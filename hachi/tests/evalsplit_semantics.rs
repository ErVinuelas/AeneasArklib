//! `src/evalsplit.rs` computes the multilinear evaluation split.
//!
//! The references here are written deliberately *unlike* the crate (the house
//! rule; see `ring_semantics.rs`): bit tests use `>>` and `&` where the crate
//! divides, evaluation references sum monomials directly with no matrix and no
//! basis vector, and the reshape's expected layout is spelled out entry by
//! entry. Three things in this module fail silently under a round-trip-only
//! test suite, and each gets a pinned test:
//!
//! * the reshape's **orientation** -- a transposed `to_matrix` still satisfies
//!   both round trips with a transposed `to_polynomial` (the `gadget_matrix`
//!   transposition lesson, NOTES.md § "Three mirrored operations…");
//! * the bit **endianness** -- a big-endian basis agrees with little-endian at
//!   one variable, so the pinned tests use two;
//! * the **which-half-is-which** convention -- `xl` is the first variables and
//!   the matrix rows; swapping the halves is invisible at symmetric points, so
//!   every point here is asymmetric.
//!
//! # Scale policy
//!
//! At the [NOZ26] Fig. 9 parameters a committed polynomial has
//! `ML_POLY_LEN = 2^20` ring-element coefficients (~8 GiB), and one
//! `eval_split` is ~2^20 schoolbook ring products. Every test that builds a
//! full-const polynomial is `#[ignore]`d rather than deleted: the bodies stay
//! correct at the real consts (their expectations are stated as index laws,
//! not old-shape tables) and run on demand
//! (`cargo test --release -- --ignored`) on a machine sized for them. The
//! pure index-arithmetic tests and the basis-kernel tests, which are
//! shape-generic or cheap, stay live -- including small-ad-hoc-point variants
//! of the properties whose full-const versions are ignored. This is a
//! recorded deviation from the repo habit that tests exercise the real
//! consts; see NOTES.md § "Chosen parameters" and `commit_semantics.rs`.

mod support;

use hachi::evalsplit::{
    lagrange_basis, monomial_basis, split_equiv, split_equiv_inv, to_polynomial, MlEvals, MlPoly,
};
use hachi::linalg::PolyVec;
use hachi::params::{ML_HIGH_LEN, ML_LOW_LEN, ML_POLY_LEN, ML_VARS_HIGH, ML_VARS_LOW};
use hachi::ring::Rq;
use support::{rq_from_u64s, show, Lcg};

/// Bit `j` of `i`, the way the crate does *not* compute it.
fn bit(i: usize, j: usize) -> bool {
    (i >> j) & 1 == 1
}

/// `split_equiv (x, y) = y + 2^nl · x`, checked against the little-endian bit
/// layout: the low `nl` bits of the flat index are `y` and the remaining bits
/// are `x`.
#[test]
fn split_equiv_matches_the_le_bit_layout() {
    for x in 0..ML_HIGH_LEN {
        for y in 0..ML_LOW_LEN {
            let k = split_equiv(x, y);
            assert_eq!(k, y + ML_LOW_LEN * x, "value at ({x}, {y})");
            assert_eq!(k & (ML_LOW_LEN - 1), y, "low bits at ({x}, {y})");
            assert_eq!(k >> ML_VARS_LOW, x, "high bits at ({x}, {y})");
        }
    }
}

/// The two directions invert each other over the whole index range.
#[test]
fn split_equiv_round_trips() {
    for k in 0..ML_POLY_LEN {
        let (x, y) = split_equiv_inv(k);
        assert!(x < ML_HIGH_LEN && y < ML_LOW_LEN, "bounds at {k}");
        assert_eq!(split_equiv(x, y), k, "inv then fwd at {k}");
    }
    for x in 0..ML_HIGH_LEN {
        for y in 0..ML_LOW_LEN {
            assert_eq!(split_equiv_inv(split_equiv(x, y)), (x, y));
        }
    }
}

/// At two variables the monomial basis is `[1, w₀, w₁, w₀w₁]` in little-endian
/// index order -- entry 1 is `w₀` (bit 0 = *first* variable), not `w₁`. One
/// variable cannot see endianness; this can.
#[test]
fn monomial_basis_is_the_tensor_of_the_point() {
    let mut lcg = Lcg::new(0xE5_01);
    let w0 = lcg.next_rq();
    let w1 = lcg.next_rq();
    let w = PolyVec::new(vec![w0.copy(), w1.copy()]);

    let mb = monomial_basis(&w);
    assert_eq!(mb.len(), 4);
    assert!(mb.get(0).equals(&Rq::one()), "entry 0: {}", show(mb.get(0)));
    assert!(mb.get(1).equals(&w0), "entry 1 must be w₀: {}", show(mb.get(1)));
    assert!(mb.get(2).equals(&w1), "entry 2 must be w₁: {}", show(mb.get(2)));
    assert!(
        mb.get(3).equals(&w0.mul(&w1)),
        "entry 3 must be w₀w₁: {}",
        show(mb.get(3))
    );
}

/// Candidate M's oracle: the doubling build agrees, entry by entry, with the
/// `n`-factor form the frozen baseline computed.
///
/// The oracle is spelled the way the *specification* is and the way the
/// implementation now is not -- for every index, the product of exactly `n`
/// factors selected by the bits of that index, with `1` multiplied in when a
/// bit is clear -- so it shares no loop, no index arithmetic and no allocation
/// with the function under test. Four variables, not two: the doubling build's
/// failure mode is a level whose high half lands at the wrong offset, which is
/// invisible at `n = 1` and degenerate at `n = 2`.
#[test]
fn monomial_basis_agrees_with_the_n_factor_oracle() {
    let mut lcg = Lcg::new(0xE5_07);
    let n: usize = 4;
    let pt: Vec<Rq> = (0..n).map(|_| lcg.next_rq()).collect();
    let w = PolyVec::new(pt.iter().map(Rq::copy).collect());

    let mb = monomial_basis(&w);
    assert_eq!(mb.len(), 1usize << n);
    for i in 0..(1usize << n) {
        let mut acc = Rq::one();
        for (j, wj) in pt.iter().enumerate() {
            let factor = if bit(i, j) { wj.copy() } else { Rq::one() };
            acc = acc.mul(&factor);
        }
        assert!(
            mb.get(i).equals(&acc),
            "entry {i} disagrees with the n-factor oracle: {}",
            show(mb.get(i))
        );
    }
}

/// The empty point: `monomialBasis` of a length-0 vector is `[1]`
/// (`monomialBasis_zero`), and the Lagrange basis likewise.
#[test]
fn bases_of_the_empty_point_are_one() {
    let w = PolyVec::new(vec![]);
    let mb = monomial_basis(&w);
    assert_eq!(mb.len(), 1);
    assert!(mb.get(0).equals(&Rq::one()));
    let lb = lagrange_basis(&w);
    assert_eq!(lb.len(), 1);
    assert!(lb.get(0).equals(&Rq::one()));
}

/// At two variables the Lagrange basis is
/// `[(1-w₀)(1-w₁), w₀(1-w₁), (1-w₀)w₁, w₀w₁]`, spelled out.
#[test]
fn lagrange_basis_matches_the_kernel_formula() {
    let mut lcg = Lcg::new(0xE5_02);
    let w0 = lcg.next_rq();
    let w1 = lcg.next_rq();
    let w = PolyVec::new(vec![w0.copy(), w1.copy()]);
    let c0 = Rq::one().sub(&w0); // 1 - w₀
    let c1 = Rq::one().sub(&w1); // 1 - w₁

    let lb = lagrange_basis(&w);
    assert_eq!(lb.len(), 4);
    assert!(lb.get(0).equals(&c0.mul(&c1)), "entry 0: {}", show(lb.get(0)));
    assert!(lb.get(1).equals(&w0.mul(&c1)), "entry 1: {}", show(lb.get(1)));
    assert!(lb.get(2).equals(&c0.mul(&w1)), "entry 2: {}", show(lb.get(2)));
    assert!(lb.get(3).equals(&w0.mul(&w1)), "entry 3: {}", show(lb.get(3)));
}

/// Candidate N's oracle: the ring-specialized doubling build agrees, entry by
/// entry, with the `n`-factor form the frozen baseline computed.
///
/// The oracle multiplies `n` factors per index and spells `1 - wⱼ` with a
/// subtraction from `Rq::one()`, which is what the implementation no longer
/// does: it now derives the clear-bit child as `p - p·wⱼ`. So this pins the
/// specialization `p·(1-x) = p - p·x` at the ring, not just the level offsets.
/// Four variables, for the reason given on the monomial oracle.
#[test]
fn lagrange_basis_agrees_with_the_n_factor_oracle() {
    let mut lcg = Lcg::new(0xE5_08);
    let n: usize = 4;
    let pt: Vec<Rq> = (0..n).map(|_| lcg.next_rq()).collect();
    let w = PolyVec::new(pt.iter().map(Rq::copy).collect());

    let lb = lagrange_basis(&w);
    assert_eq!(lb.len(), 1usize << n);
    for i in 0..(1usize << n) {
        let mut acc = Rq::one();
        for (j, wj) in pt.iter().enumerate() {
            let factor = if bit(i, j) {
                wj.copy()
            } else {
                Rq::one().sub(wj)
            };
            acc = acc.mul(&factor);
        }
        assert!(
            lb.get(i).equals(&acc),
            "entry {i} disagrees with the n-factor oracle: {}",
            show(lb.get(i))
        );
    }
}

/// Partition of unity: the Lagrange kernel sums to 1 over the hypercube at any
/// point -- a property of the definition the entry-by-entry test cannot state.
/// At the full variable count (`nl + nh = 20`, a 2^20-element basis).
#[test]
#[ignore = "full-const scale (a 2^20-ring-element basis, ~8 GiB); see the module doc -- run with cargo test --release -- --ignored"]
fn lagrange_basis_sums_to_one() {
    let mut lcg = Lcg::new(0xE5_03);
    let w = lcg.next_poly_vec(ML_VARS_LOW + ML_VARS_HIGH);
    let lb = lagrange_basis(&w);
    let mut sum = Rq::zero();
    for i in 0..lb.len() {
        sum = sum.add(lb.get(i));
    }
    assert!(sum.equals(&Rq::one()), "sum: {}", show(&sum));
}

/// The same partition of unity at a small ad-hoc point (`lagrange_basis` is
/// generic in the point length): the live stand-in for the ignored full-const
/// version above.
#[test]
fn lagrange_basis_sums_to_one_at_a_small_point() {
    let mut lcg = Lcg::new(0xE5_13);
    let w = lcg.next_poly_vec(4);
    let lb = lagrange_basis(&w);
    assert_eq!(lb.len(), 16);
    let mut sum = Rq::zero();
    for i in 0..lb.len() {
        sum = sum.add(lb.get(i));
    }
    assert!(sum.equals(&Rq::one()), "sum: {}", show(&sum));
}

/// The reshape's orientation, pinned entry by entry with distinguishable
/// constants: coefficient `k` lands at row `k mod 2^nl`, column `k >> nl`, so
/// entry `(i, j)` must hold coefficient `(j << nl) | i` -- the expectation is
/// the index law itself, by shift-and-mask, not the crate's `split_equiv`. A
/// transposed reshape passes both round trips; it fails here.
#[test]
#[ignore = "full-const scale (a 2^20-ring-element polynomial, ~8 GiB); see the module doc -- run with cargo test --release -- --ignored"]
fn to_matrix_places_coefficients_along_the_split() {
    let mut coeffs = Vec::new();
    for k in 0..ML_POLY_LEN {
        coeffs.push(rq_from_u64s(&[k as u64 + 1]));
    }
    let p = MlPoly::new(coeffs);
    let m = p.to_matrix();

    assert_eq!(m.rows(), ML_LOW_LEN);
    assert_eq!(m.cols(), ML_HIGH_LEN);
    for i in 0..ML_LOW_LEN {
        for j in 0..ML_HIGH_LEN {
            let want = ((j << ML_VARS_LOW) | i) as u64 + 1;
            assert_eq!(m.row(i).get(j).coeff(0).to_u64(), want, "entry ({i}, {j})");
        }
    }
}

/// `to_matrix_eval` follows the same layout (a distinct spec definition; the
/// test keeps the two bodies from drifting apart).
#[test]
#[ignore = "full-const scale (a 2^20-ring-element vector, ~8 GiB); see the module doc -- run with cargo test --release -- --ignored"]
fn to_matrix_eval_places_values_along_the_split() {
    let mut values = Vec::new();
    for k in 0..ML_POLY_LEN {
        values.push(rq_from_u64s(&[k as u64 + 1]));
    }
    let v = MlEvals::new(values);
    let m = v.to_matrix_eval();
    for i in 0..ML_LOW_LEN {
        for j in 0..ML_HIGH_LEN {
            let want = ((j << ML_VARS_LOW) | i) as u64 + 1;
            assert_eq!(m.row(i).get(j).coeff(0).to_u64(), want, "entry ({i}, {j})");
        }
    }
}

/// The two reshapes are mutually inverse on random data, both ways round.
#[test]
#[ignore = "full-const scale (two 2^20-ring-element structures, ~16 GiB); see the module doc -- run with cargo test --release -- --ignored"]
fn to_polynomial_inverts_to_matrix() {
    let mut lcg = Lcg::new(0xE5_04);

    let mut coeffs = Vec::new();
    for _ in 0..ML_POLY_LEN {
        coeffs.push(lcg.next_rq());
    }
    let p = MlPoly::new(coeffs);
    let back = to_polynomial(&p.to_matrix());
    for k in 0..ML_POLY_LEN {
        assert!(back.get(k).equals(p.get(k)), "coefficient {k}");
    }

    let m = lcg.next_poly_matrix(ML_LOW_LEN, ML_HIGH_LEN);
    let again = to_polynomial(&m).to_matrix();
    for i in 0..ML_LOW_LEN {
        for j in 0..ML_HIGH_LEN {
            assert!(again.row(i).get(j).equals(m.row(i).get(j)), "entry ({i}, {j})");
        }
    }
}

/// `evalSplit_eq_eval`, against a reference that shares nothing with the
/// implementation: the direct monomial sum `Σₖ pₖ · Π_{bit j of k} xⱼ` over
/// the concatenated point `x = xl ++ xh`, bits by shift-and-mask, no matrix,
/// no basis vector. The point halves are asymmetric so a swapped `(xl, xh)`
/// fails.
#[test]
#[ignore = "full-const scale (a 2^20-term direct sum of ring products); see the module doc -- run with cargo test --release -- --ignored"]
fn eval_split_agrees_with_a_direct_monomial_sum() {
    let mut lcg = Lcg::new(0xE5_05);
    let mut coeffs = Vec::new();
    for _ in 0..ML_POLY_LEN {
        coeffs.push(lcg.next_rq());
    }
    let p = MlPoly::new(coeffs);
    let xl = lcg.next_poly_vec(ML_VARS_LOW);
    let xh = lcg.next_poly_vec(ML_VARS_HIGH);

    // x = xl ++ xh, the spec's point.
    let mut x = Vec::new();
    for i in 0..xl.len() {
        x.push(xl.get(i).copy());
    }
    for i in 0..xh.len() {
        x.push(xh.get(i).copy());
    }

    let n = x.len();
    let mut want = Rq::zero();
    for k in 0..ML_POLY_LEN {
        let mut term = p.get(k).copy();
        for (j, xj) in x.iter().enumerate().take(n) {
            if bit(k, j) {
                term = term.mul(xj);
            }
        }
        want = want.add(&term);
    }

    let got = p.eval_split(&xl, &xh);
    assert!(got.equals(&want), "got {}, want {}", show(&got), show(&want));
}

/// `evalSplitEval_eq_eval`, same shape of reference with the Lagrange factor
/// `(bit ? xⱼ : 1 - xⱼ)` at every position.
#[test]
#[ignore = "full-const scale (a 2^20-term direct sum of ring products); see the module doc -- run with cargo test --release -- --ignored"]
fn eval_split_eval_agrees_with_a_direct_lagrange_sum() {
    let mut lcg = Lcg::new(0xE5_06);
    let mut values = Vec::new();
    for _ in 0..ML_POLY_LEN {
        values.push(lcg.next_rq());
    }
    let v = MlEvals::new(values);
    let xl = lcg.next_poly_vec(ML_VARS_LOW);
    let xh = lcg.next_poly_vec(ML_VARS_HIGH);

    let mut x = Vec::new();
    for i in 0..xl.len() {
        x.push(xl.get(i).copy());
    }
    for i in 0..xh.len() {
        x.push(xh.get(i).copy());
    }

    let n = x.len();
    let mut want = Rq::zero();
    for k in 0..ML_POLY_LEN {
        let mut term = v.get(k).copy();
        for (j, xj) in x.iter().enumerate().take(n) {
            let factor = if bit(k, j) {
                xj.copy()
            } else {
                Rq::one().sub(xj)
            };
            term = term.mul(&factor);
        }
        want = want.add(&term);
    }

    let got = v.eval_split_eval(&xl, &xh);
    assert!(got.equals(&want), "got {}, want {}", show(&got), show(&want));
}

/// The multilinear extension interpolates: at a Boolean point the split
/// evaluation returns the stored hypercube value at that vertex -- with the
/// vertex index reassembled by `split_equiv`'s own layout (low bits = `xl`).
///
/// Sampled vertices, not the full sweep: at 2^20 vertices with each
/// evaluation itself ~2^20 ring products, exhaustion is out of reach even on
/// demand. The vertices are fixed and asymmetric in both halves (0 and
/// all-ones catch a stuck evaluator; the mixed ones catch a swapped or
/// bit-reversed half).
#[test]
#[ignore = "full-const scale (a 2^20-ring-element vector, ~8 GiB, ~2^20 ring products per vertex); see the module doc -- run with cargo test --release -- --ignored"]
fn eval_split_eval_interpolates_the_hypercube() {
    let mut lcg = Lcg::new(0xE5_07);
    let mut values = Vec::new();
    for _ in 0..ML_POLY_LEN {
        values.push(lcg.next_rq());
    }
    let v = MlEvals::new(values);

    let vertices = [0usize, 1, ML_POLY_LEN - 1, 0b0000_0110_1001 % ML_POLY_LEN, (ML_POLY_LEN - 1) >> 3];
    for k in vertices {
        let mut xl = Vec::new();
        for j in 0..ML_VARS_LOW {
            xl.push(if bit(k, j) { Rq::one() } else { Rq::zero() });
        }
        let mut xh = Vec::new();
        for j in 0..ML_VARS_HIGH {
            xh.push(if bit(k, ML_VARS_LOW + j) {
                Rq::one()
            } else {
                Rq::zero()
            });
        }
        let got = v.eval_split_eval(&PolyVec::new(xl), &PolyVec::new(xh));
        assert!(got.equals(v.get(k)), "vertex {k}: got {}", show(&got));
    }
}
