//! `src/quadeval.rs`: the QuadEval fold and its Eq. (20) checks.
//!
//! The headline tests are [`in_sb_is_asymmetric`] and
//! [`the_box_is_strictly_stronger_than_the_ball`]: the paper's balanced digit
//! box `S_b = [-8, 7]` admits `-8` and rejects `+8`, while the `ℓ∞` ball
//! `‖·‖∞ ≤ CHAIN_GAMMA = 15` admits both. That single asymmetry is the whole
//! difference between `relOut` and `paperRelOut`, and a corpus that stays
//! inside the ball cannot see it.
//!
//! # Scale policy
//!
//! Split, and the split is forced by two *different* walls:
//!
//! * `in_sb`/`vec_in_sb`, `tensor_g`, `tensor_g1`, `carrier_entry` and the
//!   bounded `z` round trip are shape-generic and run here at real
//!   `RING_DEGREE`, with small ad-hoc block counts.
//! * `honest_z`, `rel_out` and `paper_rel_out` read their widths from
//!   [`params`] and cannot be run at a reduced shape. At Fig. 9 the witness
//!   `message` alone is `2^23` ring elements (~64 GiB) and `honest_z` is `2^23`
//!   ring products, so those tests are `#[ignore]`d rather than deleted --
//!   `cargo test --release -- --ignored` on a machine sized for them. Note the
//!   removal condition is a **streaming witness API**, not the multiplication
//!   champion: no `ring::mul` speed makes 64 GiB fit.

#![allow(clippy::cast_possible_wrap)]
#![allow(clippy::cast_sign_loss)]

mod support;

use hachi::commit::{l_infty_norm, vec_l_infty_norm};
use hachi::gadget::{
    balanced_gadget_decompose, bounded_z_gadget_decompose, gadget_mul, gadget_mul_z,
};
use hachi::linalg::PolyVec;
use hachi::params::{
    BLOCKS, CHAIN_GAMMA, GADGET_BASE, GADGET_DIGITS, HALF_BASE, MESSAGE_ROWS, Q, RING_DEGREE,
    SB_HI, Z_BOUND, Z_DIGITS,
};
use hachi::quadeval::{
    rlin_cols, rlin_cw, rlin_ct, rlin_cz, rlin_rows, rlin_stmt, stack, tensor_g_matrix,
    to_quad_eval_statement, unflatten, unstack, PolyEvalStatement,
    carrier, carrier_entry, in_sb, j_mul, tensor_g, tensor_g1, vec_in_sb,
};
use hachi::ring::Rq;
use support::{rq_from_u64s, show, Lcg};

/// An `Rq` whose coefficient `0` is the given *centered* integer.
fn rq_with_centered(x: i64) -> Rq {
    let v = if x >= 0 { x as u64 } else { Q - ((-x) as u64) };
    rq_from_u64s(&[v])
}

// ---------------------------------------------------------------------------
// The box, and why it is not a ball
// ---------------------------------------------------------------------------

/// The specification's box is `[-⌊b/2⌋, ⌈b/2⌉-1] = [-8, 7]` -- **asymmetric**.
/// An implementation that tested a magnitude would accept `+8`, and one that
/// tested `to_u64() <= 7` would reject every negative digit.
#[test]
fn in_sb_is_asymmetric() {
    assert!(in_sb(&rq_with_centered(-(HALF_BASE as i64))), "-8 must be in the box");
    assert!(in_sb(&rq_with_centered(SB_HI as i64)), "+7 must be in the box");
    assert!(!in_sb(&rq_with_centered(HALF_BASE as i64)), "+8 must be OUT of the box");
    assert!(
        !in_sb(&rq_with_centered(-(HALF_BASE as i64) - 1)),
        "-9 must be out of the box"
    );
    for x in -(HALF_BASE as i64)..=(SB_HI as i64) {
        assert!(in_sb(&rq_with_centered(x)), "centered {x} should be in the box");
    }
}

/// The box is strictly inside the ball, and `+8` is the witness: it passes
/// `‖·‖∞ ≤ CHAIN_GAMMA = 15` and fails `InSb 16`. This is exactly what
/// separates `rel_out` from `paper_rel_out`, isolated from their Fig. 9 widths.
#[test]
fn the_box_is_strictly_stronger_than_the_ball() {
    let plus_eight = rq_with_centered(HALF_BASE as i64);
    assert!(l_infty_norm(&plus_eight) <= CHAIN_GAMMA, "+8 is inside the ball");
    assert!(!in_sb(&plus_eight), "+8 is outside the box");

    let v = PolyVec::new(vec![rq_with_centered(-(HALF_BASE as i64)), plus_eight]);
    assert!(vec_l_infty_norm(&v) <= CHAIN_GAMMA, "the vector is inside the ball");
    assert!(!vec_in_sb(&v), "the vector must fail the box");

    // And the containment direction the spec proves (`paperRelOut_subset_relOut`
    // under `b/2 <= γ`, which is `8 <= 15` here): in the box implies in the ball.
    let mut rng = Lcg::new(0x9E11_0000_0000_0001);
    for _ in 0..32 {
        let coeffs: Vec<u64> = (0..RING_DEGREE)
            .map(|_| {
                let x = (rng.next_u64() % (GADGET_BASE)) as i64 - HALF_BASE as i64;
                if x >= 0 { x as u64 } else { Q - ((-x) as u64) }
            })
            .collect();
        let a = rq_from_u64s(&coeffs);
        if in_sb(&a) {
            assert!(l_infty_norm(&a) <= CHAIN_GAMMA, "box member outside the ball");
        }
    }
}

/// The honest balanced decomposition lands *exactly* on the box: it fills
/// `[-8, 7]`, so `paper_rel_out`'s c6 is tight on it while `rel_out`'s has
/// slack 7. That tightness is why the corpus above has to be constructed
/// rather than decomposed.
#[test]
fn the_honest_balanced_decomposition_is_in_the_box() {
    let mut rng = Lcg::new(0x9E11_0000_0000_0002);
    let x = rng.next_poly_vec(3);
    let d = balanced_gadget_decompose(&x);
    assert!(vec_in_sb(&d), "the balanced decomposition must satisfy InSb");
    assert!(vec_l_infty_norm(&d) <= CHAIN_GAMMA);
}

/// And the *unsigned* decomposition does not -- it yields digits in `{0,…,15}`,
/// which pass the ball with no slack and fail the box for every digit >= 8.
/// This is why target 2's honest path consumes target 1's balanced digits.
#[test]
fn the_unsigned_decomposition_fails_the_box() {
    let mut rng = Lcg::new(0x9E11_0000_0000_0003);
    let x = rng.next_poly_vec(3);
    let d = hachi::gadget::gadget_decompose(&x);
    assert!(
        vec_l_infty_norm(&d) <= CHAIN_GAMMA,
        "the unsigned decomposition should still pass the ball"
    );
    assert!(!vec_in_sb(&d), "the unsigned decomposition must fail the box");
}

// ---------------------------------------------------------------------------
// The gadget collapse
// ---------------------------------------------------------------------------

/// `carrierEntry` is `splitForm (gadgetMatrix …) a s`, and the Rust computes it
/// through the collapsed `gadget_mul`. Checked against the *materialized*
/// matrix at a reduced row count -- the one place `G` can be built at all.
#[test]
fn carrier_entry_agrees_with_the_materialized_matrix() {
    let rows = 2usize;
    let mut rng = Lcg::new(0x9E11_0000_0000_0004);
    let a = rng.next_poly_vec(rows);
    let s = rng.next_poly_vec(rows * GADGET_DIGITS);
    let g = hachi::gadget::gadget_matrix(rows);
    assert!(
        carrier_entry(&a, &s).equals(&g.split_form(&a, &s)),
        "the collapsed carrier entry disagrees with the materialized G"
    );
}

/// `carrier` is `carrier_entry` at every block -- one source of truth, two
/// shapes.
#[test]
fn carrier_is_carrier_entry_per_block() {
    let rows = 2usize;
    let blocks = 3usize;
    let mut rng = Lcg::new(0x9E11_0000_0000_0005);
    let a = rng.next_poly_vec(rows);
    let s: Vec<PolyVec> = (0..blocks)
        .map(|_| rng.next_poly_vec(rows * GADGET_DIGITS))
        .collect();
    let w = carrier(&a, &s);
    assert_eq!(w.len(), blocks);
    for i in 0..blocks {
        assert!(w.get(i).equals(&carrier_entry(&a, &s[i])));
    }
}

/// `tensorG1 c x = ⟨c, G x⟩`, against an independent accumulation that
/// recomposes each block by hand rather than through `gadget_mul`.
#[test]
fn tensor_g1_is_the_challenge_weighted_recomposition() {
    let blocks = 3usize;
    let mut rng = Lcg::new(0x9E11_0000_0000_0006);
    let c = rng.next_poly_vec(blocks);
    let x = rng.next_poly_vec(blocks * GADGET_DIGITS);

    // Reference: recompose block i as Σ_e b^e · x[digits·i+e], then dot with c.
    let mut expected = Rq::zero();
    for i in 0..blocks {
        let mut row = Rq::zero();
        for e in 0..GADGET_DIGITS {
            row = row.add(&x.get(GADGET_DIGITS * i + e).scalar_mul(hachi::gadget::base_pow(e)));
        }
        expected = expected.add(&c.get(i).mul(&row));
    }
    assert!(tensor_g1(&c, &x).equals(&expected));
}

/// `tensorG c x = Σᵢ cᵢ •ᵥ (G xᵢ)`, likewise -- and `•ᵥ` is a full ring
/// product per entry, not a coefficient scaling.
#[test]
fn tensor_g_is_the_blockwise_weighted_sum() {
    let rows = 2usize;
    let blocks = 3usize;
    let mut rng = Lcg::new(0x9E11_0000_0000_0007);
    let c = rng.next_poly_vec(blocks);
    let x: Vec<PolyVec> = (0..blocks)
        .map(|_| rng.next_poly_vec(rows * GADGET_DIGITS))
        .collect();

    let mut expected = PolyVec::zeros(rows);
    for i in 0..blocks {
        let recomposed = gadget_mul(rows, &x[i]);
        let mut entries = Vec::new();
        for j in 0..rows {
            entries.push(c.get(i).mul(recomposed.get(j)));
        }
        expected = expected.add(&PolyVec::new(entries));
    }
    assert!(tensor_g(rows, &c, &x).equals(&expected));
}

/// The empty sum is zero, which is what `Finset.sum` over no blocks gives.
#[test]
fn tensor_g_of_no_blocks_is_zero() {
    let rows = 2usize;
    let c = PolyVec::zeros(0);
    let x: Vec<PolyVec> = Vec::new();
    assert!(tensor_g(rows, &c, &x).equals(&PolyVec::zeros(rows)));
}

// ---------------------------------------------------------------------------
// The bounded z round trip -- conditional, and the condition is real
// ---------------------------------------------------------------------------

/// `z = J ẑ` holds for `Z_BOUND`-short inputs. The `z` side is a
/// `BoundedDigitDecomposition`, so this is the *conditional* round trip
/// (`boundedGadgetDecompose_gadgetMul_eq`), unlike the full-width gadget's.
#[test]
fn the_bounded_z_round_trip_holds_on_short_inputs() {
    let mut rng = Lcg::new(0x9E11_0000_0000_0008);
    for rows in [1usize, 2, 3] {
        // Coefficients centered within Z_BOUND.
        let mut entries = Vec::new();
        for _ in 0..rows {
            let coeffs: Vec<u64> = (0..RING_DEGREE)
                .map(|_| {
                    let mag = rng.next_u64() % (Z_BOUND + 1);
                    if rng.next_u64() % 2 == 0 { mag } else { Q - mag }
                })
                .collect();
            entries.push(rq_from_u64s(&coeffs));
        }
        let z = PolyVec::new(entries);
        for i in 0..rows {
            assert!(l_infty_norm(z.get(i)) <= Z_BOUND, "corpus is not short");
        }
        let zhat = bounded_z_gadget_decompose(&z);
        assert_eq!(zhat.len(), rows * Z_DIGITS);
        assert!(
            gadget_mul_z(rows, &zhat).equals(&z),
            "the bounded z round trip failed at rows = {rows}"
        );
        // Range is unconditional and lands in the same box.
        assert!(vec_in_sb(&zhat), "bounded z digits must satisfy InSb");
    }
}

/// And it fails outside the bound, deterministically -- `16^5 < q`, so five
/// digits cannot carry every residue. Without this the conditional round trip
/// would be indistinguishable from an unconditional one.
#[test]
fn the_bounded_z_round_trip_fails_on_long_inputs() {
    let z = PolyVec::new(vec![rq_from_u64s(&[Q / 2])]);
    assert!(l_infty_norm(z.get(0)) > Z_BOUND, "witness is not long");
    let zhat = bounded_z_gadget_decompose(&z);
    assert!(
        !gadget_mul_z(1, &zhat).equals(&z),
        "a long input round-tripped; the decomposition is not bounded"
    );
    // The range bound still holds, which is the asymmetry worth pinning.
    assert!(vec_in_sb(&zhat), "the range bound is unconditional");
}

/// `j_mul` is `gadget_mul_z` at the scheme's `n`; at that width the two agree
/// by construction, and this pins the width so a wrong `n` cannot pass.
#[test]
fn j_mul_is_gadget_mul_z_at_the_scheme_width() {
    let n = MESSAGE_ROWS * GADGET_DIGITS;
    let zhat = PolyVec::zeros(n * Z_DIGITS);
    let out = j_mul(&zhat);
    assert_eq!(out.len(), n, "j_mul must produce n = 2^m · δ entries");
    assert!(out.equals(&gadget_mul_z(n, &zhat)));
    assert_eq!(BLOCKS * GADGET_DIGITS, n, "the two widths coincide at Fig. 9");
}

// --- the polynomial-level bridge (chain row 1) -----------------------------

/// A multilinear polynomial evaluated the direct way: `Σ_k f[k]·∏_{bit j of k}
/// point[j]`, summing over all `2^n` monomials with the point given as one
/// vector. The crate never computes it this way -- it goes through the reshaped
/// matrix and two monomial bases -- so this is an independent reference for
/// what the split form is supposed to equal.
fn eval_direct(f: &[Rq], point: &[Rq]) -> Rq {
    let mut acc = Rq::zero();
    for (k, coeff) in f.iter().enumerate() {
        let mut term = coeff.copy();
        for (j, x) in point.iter().enumerate() {
            if (k >> j) & 1 == 1 {
                term = term.mul(x);
            }
        }
        acc = acc.add(&term);
    }
    acc
}

/// **The bridge's two bases reproduce the polynomial evaluation, and in the
/// right order.**
///
/// `toQuadEvalStatement` sets `avec := mb(xh)` and `bvec := mb(xl)` -- the
/// halves cross. At the pinned parameters `ML_VARS_LOW = ML_VARS_HIGH = 10`, so
/// a swap would still typecheck, still run, and quietly compute the transpose;
/// only a value test catches it. This test therefore uses **unequal** widths
/// (`nl = 2`, `nh = 3`), where a swap is caught twice over: by the value and by
/// the length.
///
/// The split form is written out here rather than taken from
/// `MlPoly::eval_split`, because that one is hard-wired to `ML_LOW_LEN` /
/// `ML_HIGH_LEN` and cannot run at a toy width -- and because a reference taken
/// from the code under test is not a reference.
#[test]
fn the_bridge_bases_reproduce_the_polynomial_evaluation() {
    let mut r = Lcg::new(0xB0DE_1DEA_5EED_5EED);
    let nl = 2usize;
    let nh = 3usize;

    let f: Vec<Rq> = (0..1 << (nl + nh)).map(|_| r.next_rq()).collect();
    let xl: Vec<Rq> = (0..nl).map(|_| r.next_rq()).collect();
    let xh: Vec<Rq> = (0..nh).map(|_| r.next_rq()).collect();

    // the reference: f at the concatenated point
    let mut point: Vec<Rq> = xl.iter().map(Rq::copy).collect();
    point.extend(xh.iter().map(Rq::copy));
    let y = eval_direct(&f, &point);

    let stmt = PolyEvalStatement::new(
        r.next_poly_vec(1),
        PolyVec::new(xl.iter().map(Rq::copy).collect()),
        PolyVec::new(xh.iter().map(Rq::copy).collect()),
        y.copy(),
    );
    let q = to_quad_eval_statement(&stmt);

    assert_eq!(q.bvec().len(), 1 << nl, "bvec must be the LOW half's basis");
    assert_eq!(q.avec().len(), 1 << nh, "avec must be the HIGH half's basis");

    // the split form, written out: entry (i, j) of the reshaped matrix is
    // coefficient `i + 2^nl · j`, rows indexed by the low half.
    let mut split = Rq::zero();
    for i in 0..1 << nl {
        for j in 0..1 << nh {
            let term = q
                .bvec()
                .get(i)
                .mul(&f[i + (1 << nl) * j])
                .mul(q.avec().get(j));
            split = split.add(&term);
        }
    }

    assert!(
        split.equals(&y),
        "the bridge's bases, fed through the split form, must reproduce f(xl ++ xh):\n  split {}\n  direct {}",
        show(&split),
        show(&y)
    );
    assert!(
        q.y().equals(stmt.y()),
        "the claim must pass through unchanged"
    );
    assert_eq!(q.u().len(), stmt.u().len(), "the commitment passes through");
}

// --- the R^lin adapter (chain row 3) --------------------------------------
//
// The mandatory toy-width oracle for the freeze exception recorded in NOTES.md
// § "Decision: the `R^lin` adapter's genesis holds the reshaped form". Genesis
// holds `Jᵀ(Gᵀa)` where the specification writes `(matMul G J).transpose *ᵥ a`,
// because that product is 320 GiB at the pinned parameters. Here the naive form
// is written out and run at `messageRows = 4, messageDigits = 2, zDigits = 2`,
// where `G·J` is `4 × 16` — so unlike target 5's exception, this oracle tests
// the *same* operation, just smaller.

/// The gadget matrix, materialized from `gadgetEntry`: column `j` of row `i` is
/// `base^(j % digits)` when `j / digits = i`, else `0`
/// (`Gadget/Core.lean:391`). This is what the crate never builds.
fn gadget_matrix_ref(rows: usize, digits: usize) -> Vec<Vec<Rq>> {
    let mut m = Vec::new();
    for i in 0..rows {
        let mut row = Vec::new();
        for j in 0..rows * digits {
            row.push(if j / digits == i {
                Rq::constant(base_pow_ref(j % digits))
            } else {
                Rq::zero()
            });
        }
        m.push(row);
    }
    m
}

/// `base^e` in `Fp`, by repeated multiplication.
fn base_pow_ref(e: usize) -> cpoly::Fp {
    let mut acc = cpoly::Fp::ONE;
    for _ in 0..e {
        acc = acc * cpoly::Fp::new(GADGET_BASE);
    }
    acc
}

/// A `PolyVec`'s entries as a slice-able `Vec`, since the newtype exposes only
/// indexed access.
fn entries_of(v: &PolyVec) -> Vec<Rq> {
    (0..v.len()).map(|i| v.get(i).copy()).collect()
}

/// A naive dense matrix product: `(A·B)[i][k] = Σ_t A[i][t]·B[t][k]`. Runs only
/// at toy sizes, which is the whole point of the exception.
fn mat_mul_ref(a: &[Vec<Rq>], b: &[Vec<Rq>]) -> Vec<Vec<Rq>> {
    let n = a.len();
    let inner = b.len();
    let cols = b[0].len();
    let mut out = Vec::new();
    for i in 0..n {
        let mut row = Vec::new();
        for k in 0..cols {
            let mut acc = Rq::zero();
            for t in 0..inner {
                acc = acc.add(&a[i][t].mul(&b[t][k]));
            }
            row.push(acc);
        }
        out.push(row);
    }
    out
}

/// `Mᵀ·v`, naively.
fn transpose_mul_ref(m: &[Vec<Rq>], v: &[Rq]) -> Vec<Rq> {
    let cols = m[0].len();
    let mut out = Vec::new();
    for j in 0..cols {
        let mut acc = Rq::zero();
        for (i, row) in m.iter().enumerate() {
            acc = acc.add(&row[j].mul(&v[i]));
        }
        out.push(acc);
    }
    out
}

/// **The exception's oracle.** `Jᵀ(Gᵀa)` — what genesis holds — equals
/// `(G·J)ᵀa` — what the specification writes — at a width where the naive
/// product can actually be formed.
///
/// If this fails, the reshape is not the identity it is claimed to be and the
/// freeze is unfaithful, which no benchmark and no digest could ever reveal.
#[test]
fn the_reshaped_c4_block_equals_the_naive_matrix_product() {
    let mut r = Lcg::new(0xC40B_10C4_0B10_0001);
    let message_rows = 4usize;
    // UNEQUAL on purpose: with messageDigits == zDigits the two transposed
    // applications commute, and swapping them is a no-op the test cannot see.
    // Found by mutation, and the third instance of that pattern today after the
    // sumcheck cube guard and the bridge's crossed point halves.
    let message_digits = 2usize;
    let z_digits = 3usize;

    let avec = PolyVec::new((0..message_rows).map(|_| r.next_rq()).collect());

    // the specification's shape: form G·J, transpose it, apply to a
    let g = gadget_matrix_ref(message_rows, message_digits);
    let j = gadget_matrix_ref(message_rows * message_digits, z_digits);
    let gj = mat_mul_ref(&g, &j);
    let naive = transpose_mul_ref(&gj, &entries_of(&avec));

    // what the crate computes: Jᵗ(Gᵗ a)
    let g_a = hachi::gadget::gadget_transpose_mul(message_rows, message_digits, &avec);
    let reshaped =
        hachi::gadget::gadget_transpose_mul(message_rows * message_digits, z_digits, &g_a);

    assert_eq!(
        reshaped.len(),
        naive.len(),
        "the reshape must produce the same length"
    );
    assert_eq!(reshaped.len(), message_rows * message_digits * z_digits);
    for k in 0..naive.len() {
        assert!(
            reshaped.get(k).equals(&naive[k]),
            "entry {k}: the reshape J^T(G^T a) must equal the naive (G*J)^T a"
        );
    }
    // and it is not vacuously zero
    assert!(
        !reshaped.get(1).is_zero() || !reshaped.get(2).is_zero(),
        "an all-zero result would make this test vacuous"
    );
}

/// `gadget_transpose_mul` is the transpose of the matrix the crate never
/// builds — checked against the materialized one.
#[test]
fn the_transposed_gadget_matches_the_materialized_transpose() {
    let mut r = Lcg::new(0x6AD6_77A5_9051_E110);
    for (rows, digits) in [(1usize, 3usize), (3, 1), (4, 2), (2, 5)] {
        let a = PolyVec::new((0..rows).map(|_| r.next_rq()).collect());
        let m = gadget_matrix_ref(rows, digits);
        let expected = transpose_mul_ref(&m, &entries_of(&a));
        let got = hachi::gadget::gadget_transpose_mul(rows, digits, &a);
        assert_eq!(got.len(), rows * digits, "rows={rows} digits={digits}");
        for k in 0..expected.len() {
            assert!(
                got.get(k).equals(&expected[k]),
                "rows={rows} digits={digits} entry {k}"
            );
        }
    }
}

/// **`tensorGMatrix c *ᵥ flatten x = tensorG c x`** — upstream's
/// `tensorGMatrix_mulVec` (`RingSwitch/Rlin.lean:141`), which is the c5
/// block-row identity. A strong oracle because the two sides are computed by
/// completely different code: a materialized matrix times a flattened vector on
/// one side, the crate's block-weighted gadget sum on the other.
#[test]
fn the_c5_block_matrix_reproduces_tensor_g() {
    let mut r = Lcg::new(0xC5B1_0CC5_B10C_0002);
    let k = 2usize;
    // `tensor_g` reaches `gadget_mul`, which is params-locked to
    // `GADGET_DIGITS`, so the comparison can only run at that digit count --
    // one more place where a frozen item's hard-wired arity narrows a test, and
    // the reason the new items take theirs as arguments.
    let digits = GADGET_DIGITS;
    let blocks = 3usize;

    let c = PolyVec::new((0..blocks).map(|_| r.next_rq()).collect());
    let x: Vec<PolyVec> = (0..blocks)
        .map(|_| PolyVec::new((0..k * digits).map(|_| r.next_rq()).collect()))
        .collect();

    let m = tensor_g_matrix(k, digits, &c);
    let flat = hachi::linalg::flatten_blocks(&x);
    let via_matrix = m.mat_vec_mul(&flat);
    let via_tensor = tensor_g(k, &c, &x);

    assert_eq!(m.rows(), k);
    assert_eq!(m.cols(), blocks * (k * digits));
    for p in 0..k {
        assert!(
            via_matrix.get(p).equals(via_tensor.get(p)),
            "row {p}: the c5 matrix must reproduce tensor_g"
        );
    }
    assert!(!via_tensor.get(0).is_zero(), "non-vacuous");
}

/// `stack` and `unstack` are inverse, both ways — upstream's
/// `flattenBlocks_unflatten` / `unflatten_flattenBlocks` lifted to the whole
/// triple. The block *order* is what this pins: a layout disagreement between
/// `stack` and the column blocks of `rlin_stmt` would make `M·ζ = y` fail for
/// honest witnesses and nothing else would notice.
#[test]
fn stack_and_unstack_are_inverse() {
    let mut r = Lcg::new(0x57AC_C0DE_57AC_C0DE);
    let blocks = 3usize;
    let message_digits = 2usize;
    let inner_width = 2usize;
    let z_len = 5usize;

    let cw = blocks * message_digits;
    let ct = blocks * inner_width;

    let resp = hachi::quadeval::QuadEvalResponse::new(
        PolyVec::new((0..cw).map(|_| r.next_rq()).collect()),
        (0..blocks)
            .map(|_| PolyVec::new((0..inner_width).map(|_| r.next_rq()).collect()))
            .collect(),
        PolyVec::new((0..z_len).map(|_| r.next_rq()).collect()),
    );

    let zeta = stack(&resp);
    assert_eq!(zeta.len(), cw + ct + z_len, "the stacked length is rlinCols");

    let back = unstack(&zeta, cw, ct, inner_width);
    assert_eq!(back.carrier_dec().len(), cw);
    assert_eq!(back.inner_dec().len(), blocks);
    assert_eq!(back.z_dec().len(), z_len);
    for i in 0..cw {
        assert!(back.carrier_dec().get(i).equals(resp.carrier_dec().get(i)), "w-hat {i}");
    }
    for b in 0..blocks {
        for w in 0..inner_width {
            assert!(
                back.inner_dec()[b].get(w).equals(resp.inner_dec()[b].get(w)),
                "t-hat block {b} entry {w}"
            );
        }
    }
    for i in 0..z_len {
        assert!(back.z_dec().get(i).equals(resp.z_dec().get(i)), "z-hat {i}");
    }

    // and the other direction: stack ∘ unstack = id on ζ
    let round = stack(&back);
    for i in 0..zeta.len() {
        assert!(round.get(i).equals(zeta.get(i)), "stack∘unstack entry {i}");
    }
}

/// `unflatten` inverts `flatten_blocks`, at a width that is not the block
/// count — so a transposed reshape cannot pass.
#[test]
fn unflatten_inverts_flatten_blocks() {
    let mut r = Lcg::new(0x0F1A_77E5_0F1A_77E1);
    let blocks = 3usize;
    let width = 5usize; // != blocks, so a transpose is caught
    let xs: Vec<PolyVec> = (0..blocks)
        .map(|_| PolyVec::new((0..width).map(|_| r.next_rq()).collect()))
        .collect();
    let flat = hachi::linalg::flatten_blocks(&xs);
    let back = unflatten(&flat, width);
    assert_eq!(back.len(), blocks);
    for b in 0..blocks {
        assert_eq!(back[b].len(), width);
        for w in 0..width {
            assert!(back[b].get(w).equals(xs[b].get(w)), "block {b} entry {w}");
        }
    }
}

/// The assembled `R^lin` system has the shape `rlinRows × rlinCols`, its `c1`
/// row block is `D` padded with zeros, and its `c4` response block is the
/// negated reshape — checked against the naive matrix product again, this time
/// through `rlin_stmt` rather than the helper directly.
// 145 lines because it asserts all five row blocks and both paddings by value.
// Splitting it would mean rebuilding the 2.2 GiB-shaped statement per part, and
// asserting fewer blocks is exactly what let three mutants live.
#[allow(clippy::too_many_lines)]
#[test]
fn the_assembled_rlin_system_has_the_specified_blocks() {
    let mut r = Lcg::new(0x810C_C50F_1700_0003);
    let blocks = 2usize;
    let message_rows = 2usize;
    let message_digits = 2usize;
    let inner_rows = 1usize;
    let inner_digits = 2usize;
    let z_digits = 3usize;
    let d_rows = 1usize;
    let outer_rows = 1usize;

    let cw = rlin_cw(blocks, message_digits);
    let ct = rlin_ct(blocks, inner_rows, inner_digits);
    let cz = rlin_cz(message_rows, message_digits, z_digits);
    let cols = rlin_cols(
        blocks,
        message_rows,
        message_digits,
        inner_rows,
        inner_digits,
        z_digits,
    );
    assert_eq!(cols, cw + (ct + cz), "rlinCols is the specification's sum");

    let pp = hachi::quadeval::PublicParamsD::new(
        hachi::commit::PublicParams::new(
            r.next_poly_matrix(inner_rows, message_rows * message_digits),
            r.next_poly_matrix(outer_rows, ct),
        ),
        r.next_poly_matrix(d_rows, cw),
    );
    let stmt = hachi::quadeval::QuadEvalStatement::new(
        r.next_poly_vec(outer_rows),
        r.next_poly_vec(message_rows),
        r.next_poly_vec(blocks),
        r.next_rq(),
    );
    let v = r.next_poly_vec(d_rows);
    let c = r.next_poly_vec(blocks);

    let out = rlin_stmt(
        &pp,
        &stmt,
        &v,
        &c,
        CHAIN_GAMMA,
        blocks,
        message_rows,
        message_digits,
        inner_rows,
        inner_digits,
        z_digits,
    );

    assert_eq!(
        out.m().rows(),
        rlin_rows(inner_rows, outer_rows, d_rows),
        "the row count is rlinRows"
    );
    assert_eq!(out.m().cols(), cols, "the column count is rlinCols");
    assert_eq!(out.yvec().len(), rlin_rows(inner_rows, outer_rows, d_rows));
    assert_eq!(out.bound(), CHAIN_GAMMA, "the bound is gamma");

    // c1 is [ D | 0 ]
    for k in 0..cw {
        assert!(
            out.m().entry(0, k).equals(pp.d_matrix().row(0).get(k)),
            "c1 carrier block entry {k} must be D"
        );
    }
    for k in cw..cols {
        assert!(out.m().entry(0, k).is_zero(), "c1 padding entry {k}");
    }

    // --- every block, by value. Found necessary by cross-review: asserting
    // only c1 and c4's response block left three mutants alive against the
    // whole 173-test suite (c2 collapsed to one column, c3/c4's carrier blocks
    // swapped, and c5's sign dropped). A block-structured matrix needs every
    // block asserted, because each one is the only place its own data appears.
    let g_r = gadget_matrix_ref(blocks, message_digits);
    let g_m = gadget_matrix_ref(message_rows, message_digits);
    let j = gadget_matrix_ref(message_rows * message_digits, z_digits);
    let gj = mat_mul_ref(&g_m, &j);

    // c2: [ 0 | B | 0 ]
    let c2 = d_rows;
    for k in 0..cw {
        assert!(out.m().entry(c2, k).is_zero(), "c2 carrier padding {k}");
    }
    for k in 0..ct {
        assert!(
            out.m().entry(c2, cw + k).equals(pp.inner().outer_matrix().row(0).get(k)),
            "c2 inner block entry {k} must be B"
        );
    }
    for k in 0..cz {
        assert!(out.m().entry(c2, cw + ct + k).is_zero(), "c2 response padding {k}");
    }

    // c3: [ (G_{2^r})^T b | 0 | 0 ] -- against bvec, not the challenge
    let c3 = d_rows + outer_rows;
    let from_bvec = transpose_mul_ref(&g_r, &entries_of(stmt.bvec()));
    for k in 0..cw {
        assert!(
            out.m().entry(c3, k).equals(&from_bvec[k]),
            "c3 carrier block entry {k} must be (G_blocks)^T bvec"
        );
    }
    for k in cw..cols {
        assert!(out.m().entry(c3, k).is_zero(), "c3 padding {k}");
    }

    // c4: [ (G_{2^r})^T c | 0 | -(G_{2^m} J)^T a ] -- against the challenge,
    // which is what distinguishes it from c3.
    let c4 = d_rows + outer_rows + 1;
    let from_challenge = transpose_mul_ref(&g_r, &entries_of(&c));
    for k in 0..cw {
        assert!(
            out.m().entry(c4, k).equals(&from_challenge[k]),
            "c4 carrier block entry {k} must be (G_blocks)^T c, not bvec"
        );
    }
    for k in 0..ct {
        assert!(out.m().entry(c4, cw + k).is_zero(), "c4 inner padding {k}");
    }
    let naive = transpose_mul_ref(&gj, &entries_of(stmt.avec()));
    for k in 0..cz {
        assert!(
            out.m().entry(c4, cw + ct + k).equals(&naive[k].neg()),
            "c4 response block entry {k} must be -(G*J)^T a"
        );
    }
    // and the two carrier blocks are genuinely different data, so the swap the
    // assertions above rule out is not ruled out vacuously.
    assert!(
        !from_bvec[0].equals(&from_challenge[0]),
        "bvec and c must differ, else c3/c4 cannot be told apart"
    );

    // c5: [ 0 | (c^T (x) G_{n_A}) | -(A J) ]
    let c5 = d_rows + outer_rows + 2;
    let g_k = gadget_matrix_ref(inner_rows, inner_digits);
    for p in 0..inner_rows {
        for k in 0..cw {
            assert!(out.m().entry(c5 + p, k).is_zero(), "c5 carrier padding {k}");
        }
        // the tensor block, from the specification's own entry formula
        for i in 0..blocks {
            for gg in 0..inner_rows * inner_digits {
                let want = c.get(i).mul(&g_k[p][gg]);
                let flat = i * (inner_rows * inner_digits) + gg;
                assert!(
                    out.m().entry(c5 + p, cw + flat).equals(&want),
                    "c5 tensor entry ({i},{gg}) must be c_i * G(p,g)"
                );
            }
        }
        // the response block: -(A J)[p], negated
        let a_row = transpose_mul_ref(&j, &entries_of(pp.inner().inner_matrix().row(p)));
        for k in 0..cz {
            assert!(
                out.m().entry(c5 + p, cw + ct + k).equals(&a_row[k].neg()),
                "c5 response entry {k} must be -(A J)[p], negated"
            );
        }
        assert!(
            !a_row[1].is_zero(),
            "the c5 response block must be nonzero, else the sign is untestable"
        );
    }

    // yvec = (v, u, y, 0, 0)
    assert!(out.yvec().get(0).equals(v.get(0)), "yvec starts with v");
    assert!(out.yvec().get(d_rows).equals(stmt.u().get(0)), "then u");
    assert!(out.yvec().get(d_rows + outer_rows).equals(stmt.y()), "then y");
    assert!(out.yvec().get(d_rows + outer_rows + 1).is_zero(), "then 0");
}

/// `rlin_row` builds the same matrix as `rlin_stmt`, row by row.
///
/// This is the oracle for Stage 6 candidate T1b's first increment. `rlin_stmt`
/// materialises `rlinRows × rlinCols` ring elements at once — 2.2 GiB at the
/// pin, memory wall W2 — while every consumer walks one row at a time. So
/// `rlin_row` exists to make the dense assembly unnecessary, and the only thing
/// worth asserting about it is that it is *the same matrix*: every row, every
/// column, compared against the dense build at a reduced shape with all six
/// dimensions distinct, so a transposed or mis-offset block cannot hide behind
/// equal widths.
///
/// Reduced, not full-const, for the reason the module doc gives: the pinned
/// shape is `5 × 57 344`, and this test is about block *placement*, which is
/// shape-generic.
#[test]
fn rlin_row_agrees_with_rlin_stmt() {
    let mut r = Lcg::new(0x5115_0000_0000_0001);

    let blocks = 2usize;
    let message_rows = 2usize;
    let message_digits = 2usize;
    let inner_rows = 1usize;
    let inner_digits = 2usize;
    let z_digits = 3usize;
    let d_rows = 1usize;
    let outer_rows = 1usize;

    let ct = rlin_ct(blocks, inner_rows, inner_digits);
    let pp = hachi::quadeval::PublicParamsD::new(
        hachi::commit::PublicParams::new(
            r.next_poly_matrix(inner_rows, message_rows * message_digits),
            r.next_poly_matrix(outer_rows, ct),
        ),
        r.next_poly_matrix(d_rows, rlin_cw(blocks, message_digits)),
    );
    let stmt = hachi::quadeval::QuadEvalStatement::new(
        r.next_poly_vec(outer_rows),
        r.next_poly_vec(message_rows),
        r.next_poly_vec(blocks),
        r.next_rq(),
    );
    let v = r.next_poly_vec(d_rows);
    let c = r.next_poly_vec(blocks);

    let dense = rlin_stmt(
        &pp, &stmt, &v, &c, CHAIN_GAMMA, blocks, message_rows, message_digits,
        inner_rows, inner_digits, z_digits,
    );

    let rows = dense.m().rows();
    let cols = dense.m().cols();
    assert!(rows > 0 && cols > 0, "the reduced shape is non-degenerate");

    let mut i = 0usize;
    while i < rows {
        let lazy = hachi::quadeval::rlin_row(
            &pp, &stmt, &c, blocks, message_rows, message_digits,
            inner_rows, inner_digits, z_digits, i,
        );
        assert_eq!(lazy.len(), cols, "row {i} has rlinCols entries");
        let mut j = 0usize;
        while j < cols {
            assert!(
                lazy.get(j).equals(dense.m().entry(i, j)),
                "row {i} column {j} disagrees with the dense assembly"
            );
            j += 1;
        }
        i += 1;
    }
}

/// `honest_z_from_raw` is `honest_z` composed with the decomposition.
///
/// The streamed form rebuilds one block's `sᵢ` per iteration instead of reading
/// it out of a 68.7 GiB table, so this is the check that the reassociation kept
/// the same sum. Both a short challenge and a dense one, because `honest_z` has
/// two branches and only the short one is the protocol path.
#[test]
fn honest_z_from_raw_agrees_with_honest_z() {
    use hachi::params::{GADGET_DIGITS, MESSAGE_ROWS, RING_DEGREE};
    let mut rng = support::Lcg::new(0x5108);
    let blocks = 2usize;
    let raw: Vec<hachi::linalg::PolyVec> =
        (0..blocks).map(|_| rng.next_poly_vec(MESSAGE_ROWS)).collect();
    let decomposed: Vec<hachi::linalg::PolyVec> =
        raw.iter().map(hachi::gadget::gadget_decompose).collect();
    assert_eq!(decomposed[0].len(), MESSAGE_ROWS * GADGET_DIGITS);

    // a protocol-valid short challenge, and a dense one for the fallback branch
    let short = {
        let mut cs = vec![0u64; RING_DEGREE];
        for k in 0..8 {
            cs[(k * 37) % RING_DEGREE] = if k % 2 == 0 { 2 } else { hachi::params::Q - 2 };
        }
        support::rq_from_u64s(&cs)
    };
    let dense = rng.next_rq();

    for c0 in [short, dense] {
        let c = hachi::linalg::PolyVec::new((0..blocks).map(|_| c0.copy()).collect());
        let want = hachi::quadeval::honest_z(&decomposed, &c);
        let got = hachi::quadeval::honest_z_from_raw(&raw, &c);
        assert_eq!(got.len(), want.len());
        for j in 0..want.len() {
            assert!(
                got.get(j).equals(want.get(j)),
                "streamed honest_z differs at column {j}"
            );
        }
    }
}

/// `carrier_from_raw` is `carrier` composed with the decomposition -- and it
/// does no gadget arithmetic at all, because `carrier_entry` recomposes what
/// the decomposition just took apart. This is the oracle for that cancellation:
/// if the round trip were not exact the two would differ, and nothing else in
/// the crate would notice.
#[test]
fn carrier_from_raw_agrees_with_carrier() {
    use hachi::params::MESSAGE_ROWS;
    let mut rng = support::Lcg::new(0x5109);
    let blocks = 3usize;
    let raw: Vec<hachi::linalg::PolyVec> =
        (0..blocks).map(|_| rng.next_poly_vec(MESSAGE_ROWS)).collect();
    let decomposed: Vec<hachi::linalg::PolyVec> =
        raw.iter().map(hachi::gadget::gadget_decompose).collect();
    let a = rng.next_poly_vec(MESSAGE_ROWS);

    let want = hachi::quadeval::carrier(&a, &decomposed);
    let got = hachi::quadeval::carrier_from_raw(&a, &raw);
    assert_eq!(got.len(), blocks);
    for i in 0..blocks {
        assert!(got.get(i).equals(want.get(i)), "streamed carrier differs at block {i}");
    }
}

/// **The compact carrier is the expanded one** (card T39).
///
/// `carrier_from_raw_32` used to call `RawVec32::expand` and hand the result
/// to the same `apply`; it now reads the `u32` words in place. The two things
/// that could go wrong are an index shift -- the compact block is one `u32`
/// per coefficient where the expanded one is one `Fp`, and the twist table is
/// indexed by the same `t` -- and a widening that picks up sign or garbage in
/// the high half. Both would show as a different carrier, so the check is the
/// direct one: the same draw down both paths.
///
/// Three blocks and the full `MESSAGE_ROWS`, which is more than one
/// `LIMB2_CHUNK` (32), so the chunk boundary is crossed rather than assumed.
#[test]
fn the_compact_carrier_equals_the_expanded_one() {
    use hachi::linalg::RawVec32;
    use hachi::params::MESSAGE_ROWS;
    let mut rng = support::Lcg::new(0x7391);
    let blocks = 3usize;
    let expanded: Vec<hachi::linalg::PolyVec> =
        (0..blocks).map(|_| rng.next_poly_vec(MESSAGE_ROWS)).collect();
    let packed: Vec<RawVec32> = expanded.iter().map(RawVec32::compact).collect();
    let a = rng.next_poly_vec(MESSAGE_ROWS);

    let want = hachi::quadeval::carrier_from_raw(&a, &expanded);
    let got = hachi::quadeval::carrier_from_raw_32(&a, &packed);
    assert_eq!(got.len(), want.len(), "the compact carrier has the same width");
    for i in 0..want.len() {
        assert!(got.get(i).equals(want.get(i)), "compact carrier differs at block {i}");
    }
}

/// **Sharing the carrier decomposition changes nothing** (candidate T28).
///
/// `honest_compute_v_from_raw_32` computed `ŵ = G⁻¹(a · raw)` internally and
/// `honest_compute_resp_from_raw_32` computed it again; at the pin that second
/// pass cost 98.7 s. Now the caller computes it once and hands it to both. The
/// two things that could go wrong are an operand mix-up (`ŵ` is the *balanced*
/// decomposition of the carrier, not the unsigned one, and the two are
/// different vectors) and an aliasing mistake in the copy the response takes.
/// So this compares the shared path against the old self-contained one, on both
/// outputs, at a width where a swapped decomposition would show.
#[test]
fn sharing_the_carrier_decomposition_leaves_v_and_the_response_unchanged() {
    use hachi::linalg::RawVec32;
    use hachi::params::{GADGET_DIGITS, MESSAGE_ROWS};
    let mut rng = support::Lcg::new(0x7283);
    let blocks = 3usize;
    let raw: Vec<RawVec32> = (0..blocks)
        .map(|_| RawVec32::compact(&rng.next_poly_vec(MESSAGE_ROWS)))
        .collect();
    let a = rng.next_poly_vec(MESSAGE_ROWS);
    let d_matrix = rng.next_poly_matrix(1, MESSAGE_ROWS * GADGET_DIGITS);
    let c = rng.next_poly_vec(blocks);
    let inner_decomp: Vec<hachi::linalg::PolyVec> =
        (0..blocks).map(|_| rng.next_poly_vec(GADGET_DIGITS)).collect();

    // the shared value, computed once
    let carrier_dec = hachi::quadeval::carrier_decomp_from_raw_32(&a, &raw);

    // `v`: through the shared value, against `carrier_commit_from_raw_32`,
    // which is the self-contained path the composed prover used before
    let v_shared = hachi::quadeval::honest_compute_v_from_decomp(&d_matrix, &carrier_dec);
    let v_alone = hachi::quadeval::carrier_commit_from_raw_32(&d_matrix, &a, &raw);
    assert_eq!(v_shared.len(), v_alone.len(), "v has the same width either way");
    for i in 0..v_alone.len() {
        assert!(v_shared.get(i).equals(v_alone.get(i)), "v differs at {i}");
    }

    // the response's carrier slot is that same vector, verbatim
    let resp = hachi::quadeval::honest_compute_resp_from_raw_32(
        &carrier_dec,
        &raw,
        &inner_decomp,
        &c,
    );
    assert_eq!(
        resp.carrier_dec().len(),
        carrier_dec.len(),
        "the response's carrier slot has the shared value's width"
    );
    for i in 0..carrier_dec.len() {
        assert!(
            resp.carrier_dec().get(i).equals(carrier_dec.get(i)),
            "the response's carrier slot differs from the shared value at {i}"
        );
    }
}

/// **The fused z pass equals the decomposed one** (Stage 6 card T43).
///
/// `honest_z_from_raw_32` no longer decomposes a block into 8192 digit ring
/// elements and multiplies each by the challenge; it reads every coefficient
/// once, splits it into its eight nibbles and scatters them into the eight
/// digit accumulators directly. Three things could go wrong, and each has an
/// input below that would show it:
///
/// * **a digit read off the wrong nibble** -- coefficients with zero nibbles
///   in chosen positions (`0x0F0F_0000`, `0x0000_00F0`, `1`, `0`, `q - 1`)
///   make a shifted or swapped digit change the sum;
/// * **a wrap handled with the wrong sign or at the wrong slot** -- challenges
///   with terms at `N - 1`, `N - 7` and `1`, so both runs of every pass are
///   non-empty and the low run is one element long for one of them;
/// * **a magnitude applied the wrong number of times** -- the whole budget in
///   one coefficient (`±16`), and a mixed draw (`+5, -3, +2, -6`).
///
/// The `ℓ₁ = 17` challenge is the control: it fails `classify_short`, takes
/// the fallback, and must still agree -- which says the fallback's own inputs
/// are untouched by the change. The dense draw is the same control at the
/// shape the acceptance test uses.
///
/// Two oracles, deliberately different: `honest_z_from_raw` on the expanded
/// blocks (the decomposed path this replaces, unchanged) and `honest_z` on the
/// decomposition itself (the spec's own shape). Two blocks, so the sum over
/// blocks is exercised and not just one block's scatter.
#[test]
fn the_fused_z_pass_equals_the_decomposed_one() {
    use hachi::linalg::RawVec32;
    use hachi::params::{MESSAGE_ROWS, Q, RING_DEGREE};
    let mut rng = support::Lcg::new(0x7431);
    let blocks = 2usize;
    let n = RING_DEGREE;

    // a random block, and one whose rows are built from words with zero nibbles
    let mut raw: Vec<hachi::linalg::PolyVec> = Vec::new();
    raw.push(rng.next_poly_vec(MESSAGE_ROWS));
    {
        let specials: [u64; 8] = [0x0F0F_0000, 0x0000_00F0, 1, 0, Q - 1, 0x1234_5678, 16, 0x8000_0000];
        let mut rows = Vec::with_capacity(MESSAGE_ROWS);
        for r in 0..MESSAGE_ROWS {
            let mut cs = vec![0u64; n];
            for k in 0..n {
                let w = specials[(k + r) % specials.len()];
                cs[k] = if r % 3 == 0 { w } else { rng.next_u64() % Q };
            }
            rows.push(support::rq_from_u64s(&cs));
        }
        raw.push(hachi::linalg::PolyVec::new(rows));
    }
    assert_eq!(raw.len(), blocks);
    let packed: Vec<RawVec32> = raw.iter().map(RawVec32::compact).collect();
    let decomposed: Vec<hachi::linalg::PolyVec> =
        raw.iter().map(hachi::gadget::gadget_decompose).collect();

    // challenges: (positions, signed magnitudes); every one but the last two is
    // protocol-valid (centred l1 <= OMEGA = 16)
    let shapes: Vec<Vec<(usize, i64)>> = vec![
        // sixteen +-1s spread so some wrap under every shift
        (0..16).map(|t| ((t * 97 + 13) % n, if t % 2 == 0 { 1 } else { -1 })).collect(),
        // the wrap edges: a one-element low run, a seven-element one, and k = 1
        vec![(n - 1, 1), (n - 7, -1), (1, 1), (0, -1)],
        // the whole budget in one coefficient, both signs
        vec![(511, 16)],
        vec![(1000, -16)],
        // mixed magnitudes
        vec![(3, 5), (700, -3), (n - 2, 2), (400, -6)],
        // the l1 = 17 control: one over the budget, so the fallback runs
        (0..17).map(|t| ((t * 61 + 5) % n, if t % 2 == 0 { 1 } else { -1 })).collect(),
    ];
    let mut cands: Vec<hachi::ring::Rq> = shapes
        .iter()
        .map(|terms| {
            let mut cs = vec![0u64; n];
            for &(at, v) in terms {
                cs[at] = if v >= 0 { v as u64 } else { Q - ((-v) as u64) };
            }
            support::rq_from_u64s(&cs)
        })
        .collect();
    // the dense control, as the acceptance test draws it
    cands.push(rng.next_rq());

    for (which, c0) in cands.iter().enumerate() {
        // two different challenges across the two blocks, so a block/challenge
        // mix-up would show
        let c1 = cands[(which + 1) % cands.len()].copy();
        let c = hachi::linalg::PolyVec::new(vec![c0.copy(), c1]);
        let got = hachi::quadeval::honest_z_from_raw_32(&packed, &c);
        let want_raw = hachi::quadeval::honest_z_from_raw(&raw, &c);
        let want_dec = hachi::quadeval::honest_z(&decomposed, &c);
        assert_eq!(got.len(), want_raw.len(), "shape {which}: width");
        for j in 0..want_raw.len() {
            assert!(
                got.get(j).equals(want_raw.get(j)),
                "shape {which}: fused z differs from the decomposed raw path at column {j}"
            );
            assert!(
                got.get(j).equals(want_dec.get(j)),
                "shape {which}: fused z differs from honest_z at column {j}"
            );
        }
    }
}
