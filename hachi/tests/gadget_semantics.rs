//! `src/gadget.rs`: the base-`b` digit decomposition, the gadget matrix, and the
//! two directions of the gadget algebra.
//!
//! The headline tests are [`gadget_mul_inverts_gadget_decompose`] and its
//! balanced twin [`gadget_mul_inverts_balanced_gadget_decompose`], which are the
//! specification's `IsLawfulGadgetDecomposition` (`Gadget/Core.lean:404`) at these
//! parameters, at each of the two digit maps: `G · G⁻¹(x) = x`. Everything else
//! supports them -- the digit maps, the matrix layout, and the shortness bound
//! that makes the decomposition worth doing in the first place.
//!
//! The bounded `z` digit map has no `G · G⁻¹` test and cannot have one: it is a
//! `BoundedDigitDecomposition`, so its reconstruction law is conditional on the
//! input being within [`Z_BOUND`]. Both sides of that condition are checked.

// Bounds are computed from `usize` parameters below 64 and fed to `pow`.
#![allow(clippy::cast_possible_truncation)]
// The centered view of a residue is a *signed* integer (`ZMod.valMinAbs`), and
// the independent references below compute it as one. Every value cast is
// below `q < 2^32`, so no cast here can wrap.
#![allow(clippy::cast_possible_wrap)]
// ... and back, after an explicit non-negativity check or a reduction into
// `[0, q)`. Each such cast sits one line below the guard that justifies it.
#![allow(clippy::cast_sign_loss)]

mod support;

use cpoly::Fp;
use hachi::commit::{l_infty_norm, vec_l2_norm_sq, vec_l_infty_norm};
use hachi::gadget::{
    balanced_digit_at, balanced_digit_decompose, balanced_gadget_decompose, base_pow,
    bounded_z_digit_at, digit_at, digit_decompose, gadget_decompose, gadget_matrix, gadget_mul,
};
use hachi::linalg::PolyVec;
use hachi::params::{
    BALANCED_SHIFT, BETA_SQ, GADGET_BASE, GADGET_DIGITS, GAMMA, HALF_BASE, MESSAGE_ROWS, Q,
    RING_DEGREE, Z_BALANCED_SHIFT, Z_BOUND, Z_DIGITS,
};
use hachi::ring::Rq;
use support::{rq_from_u64s, show_vec, Lcg};

/// The digits are the ordinary base-`b` digits of the *canonical representative*:
/// non-negative, each below `b`. This is the fact most likely to be assumed
/// wrongly (balanced decompositions are the norm in this literature), so it is
/// checked against an independent computation.
#[test]
fn digits_are_the_plain_base_b_digits_of_the_representative() {
    let mut rng = Lcg::new(0xDEAD_BEEF_CAFE_0001);
    for _ in 0..64 {
        let c = rng.next_fp();
        let mut rest = c.to_u64();
        for e in 0..GADGET_DIGITS {
            let expected = rest % GADGET_BASE;
            assert_eq!(
                digit_at(c, e).to_u64(),
                expected,
                "digit {e} of {} is wrong",
                c.to_u64()
            );
            assert!(digit_at(c, e).to_u64() < GADGET_BASE);
            rest /= GADGET_BASE;
        }
    }
}

/// `digit_decompose` is `digit_at` at every position -- one source of truth, two
/// shapes.
#[test]
fn digit_decompose_agrees_with_digit_at() {
    let mut rng = Lcg::new(0xDEAD_BEEF_CAFE_0002);
    for _ in 0..16 {
        let c = rng.next_fp();
        let all = digit_decompose(c);
        assert_eq!(all.len(), GADGET_DIGITS);
        for e in 0..GADGET_DIGITS {
            assert_eq!(all[e].to_u64(), digit_at(c, e).to_u64());
        }
    }
}

/// The reconstruction law `Σₑ bᵉ · digit c e = c` -- the `reconstruct` field of
/// the spec's `DigitDecomposition`, and the reason `q ≤ b^digits` is required.
/// Checked at the extremes as well as at random, since `q - 1` is where a digit
/// count one too small would fail.
#[test]
fn digits_reconstruct_the_element() {
    let mut rng = Lcg::new(0xDEAD_BEEF_CAFE_0003);
    let mut corpus = vec![Fp::ZERO, Fp::ONE, Fp::new(Q - 1), Fp::new(Q / 2)];
    for _ in 0..32 {
        corpus.push(rng.next_fp());
    }
    for c in corpus {
        let digits = digit_decompose(c);
        let mut acc = Fp::ZERO;
        for (e, d) in digits.iter().enumerate() {
            acc = acc + base_pow(e) * *d;
        }
        assert_eq!(
            acc.to_u64(),
            c.to_u64(),
            "digits of {} do not reconstruct it",
            c.to_u64()
        );
    }
}

/// `base_pow` is a power in `Z_q`, not in `u64`: it has to keep working once
/// `bᵉ` passes the modulus. At `b = 16` and `digits = 8` the in-gadget
/// exponents stay below it (`16^7 = 2^28 < q`), so the test checks the modular
/// behaviour directly at the first exponent that does not.
#[test]
fn base_pow_is_modular() {
    assert_eq!(base_pow(0).to_u64(), 1);
    assert_eq!(base_pow(1).to_u64(), GADGET_BASE);
    assert_eq!(base_pow(7).to_u64(), 1 << 28);
    // 16^8 = 2^32 = 4294967296 = Q + 99.
    assert_eq!(base_pow(8).to_u64(), 99);
    assert_eq!(base_pow(9).to_u64(), 1584);
}

/// The gadget matrix is `I_rows ⊗ [1, b, …, b^(digits-1)]`: entry `(i, j)` is
/// `b^(j mod digits)` when `j / digits = i` and zero otherwise (the spec's
/// `gadgetEntry`).
#[test]
fn gadget_matrix_has_the_tensor_layout() {
    let rows = 3;
    let g = gadget_matrix(rows);
    assert_eq!(g.rows(), rows);
    assert_eq!(g.cols(), rows * GADGET_DIGITS);

    for i in 0..rows {
        for j in 0..(rows * GADGET_DIGITS) {
            let entry = g.row(i).get(j);
            if j / GADGET_DIGITS == i {
                let expected = Rq::constant(base_pow(j % GADGET_DIGITS));
                assert!(
                    entry.equals(&expected),
                    "entry ({i}, {j}) should be the constant b^{}",
                    j % GADGET_DIGITS
                );
            } else {
                assert!(entry.is_zero(), "entry ({i}, {j}) should be zero");
            }
        }
    }
}

/// The structured product agrees with multiplying by the materialized matrix.
/// This is the specification's `gadgetMul_apply` (`Gadget/Core.lean:177`) as a
/// test: it is what licenses using `gadget_mul` wherever the spec writes
/// `Simple.commit Φ (gadgetMatrix …)`, which `derived_message` and `verify_weak`
/// both do.
#[test]
fn gadget_mul_agrees_with_the_materialized_matrix() {
    let rows = 2;
    let mut rng = Lcg::new(0xDEAD_BEEF_CAFE_0004);
    let v = rng.next_poly_vec(rows * GADGET_DIGITS);
    let direct = gadget_mul(rows, &v);
    let via_matrix = gadget_matrix(rows).mat_vec_mul(&v);
    assert!(
        direct.equals(&via_matrix),
        "structured and materialized gadget products disagree:\n  {}\n  {}",
        show_vec(&direct),
        show_vec(&via_matrix)
    );
}

/// **`G · G⁻¹(x) = x`** -- the spec's `IsLawfulGadgetDecomposition`, proved of
/// this decomposition in `gadgetDecompose_lawful`.
#[test]
fn gadget_mul_inverts_gadget_decompose() {
    let mut rng = Lcg::new(0xDEAD_BEEF_CAFE_0005);
    for rows in [1usize, 2, MESSAGE_ROWS] {
        let x = rng.next_poly_vec(rows);
        let decomposed = gadget_decompose(&x);
        assert_eq!(decomposed.len(), rows * GADGET_DIGITS);
        let recomposed = gadget_mul(rows, &decomposed);
        assert!(
            recomposed.equals(&x),
            "round trip failed at rows = {rows}:\n  in  {}\n  out {}",
            show_vec(&x),
            show_vec(&recomposed)
        );
    }
}

/// The decomposition is *short*: every entry's centered `ℓ∞` norm is at most
/// the honest digit bound `b - 1` (`gadgetDecompose_zmod_vecLInftyNorm_le`),
/// which sits strictly inside the weak-opening `GAMMA = b`. Without this the
/// round trip above would be arithmetic with no cryptographic content.
#[test]
fn the_decomposition_is_l_infty_short() {
    let mut rng = Lcg::new(0xDEAD_BEEF_CAFE_0006);
    let x = rng.next_poly_vec(MESSAGE_ROWS);
    let decomposed = gadget_decompose(&x);
    let honest = GADGET_BASE - 1;
    assert!(honest < GAMMA);
    assert!(
        vec_l_infty_norm(&decomposed) <= honest,
        "‖G⁻¹(x)‖∞ = {} exceeds b - 1 = {honest}",
        vec_l_infty_norm(&decomposed)
    );
    // Entrywise too, which is the form the spec's per-block lemma takes.
    for j in 0..decomposed.len() {
        assert!(l_infty_norm(decomposed.get(j)) <= honest);
    }
}

/// ... and `ℓ₂²`-short, by the honest bound `(rows·digits)·(deg φ)·(b-1)²`
/// (`gadgetDecompose_zmod_vecL2NormSq_le` with the honest digit bound `b - 1`,
/// NOT `GAMMA = b`), which sits far inside the weak-opening `BETA_SQ` -- the
/// verifier's slack for extracted openings, checked as such in
/// `params_semantics::beta_sq_admits_the_honest_decomposition`.
#[test]
fn the_decomposition_meets_the_l2_bound() {
    let mut rng = Lcg::new(0xDEAD_BEEF_CAFE_0007);
    let x = rng.next_poly_vec(MESSAGE_ROWS);
    let decomposed = gadget_decompose(&x);
    let honest = (MESSAGE_ROWS * GADGET_DIGITS) as u128
        * RING_DEGREE as u128
        * u128::from(GADGET_BASE - 1).pow(2);
    assert!(honest <= BETA_SQ);
    assert!(
        vec_l2_norm_sq(&decomposed) <= honest,
        "‖G⁻¹(x)‖₂² = {} exceeds {honest}",
        vec_l2_norm_sq(&decomposed)
    );
}

/// Coefficient-level layout: slot `e` of block `i` holds digit `e` of every
/// coefficient of `x[i]`. Getting the two nested indices the wrong way round
/// would still round-trip for `rows = 1`, so it is checked directly.
#[test]
fn decomposition_slots_hold_the_right_digits() {
    let x = PolyVec::new(vec![
        rq_from_u64s(&[0b1011, 0b0110]),
        rq_from_u64s(&[0b0001, 0b1111]),
    ]);
    let d = gadget_decompose(&x);
    for i in 0..2 {
        for e in 0..GADGET_DIGITS {
            let slot = d.get(GADGET_DIGITS * i + e);
            for k in 0..RING_DEGREE {
                assert_eq!(
                    slot.coeff(k).to_u64(),
                    digit_at(x.get(i).coeff(k), e).to_u64(),
                    "block {i} slot {e} coefficient {k}"
                );
            }
        }
    }
}

/// Decomposing zero gives zero, and decomposing the all-ones element gives a
/// single populated slot -- the low digit's -- which is what the layout predicts.
#[test]
fn decomposition_of_simple_inputs() {
    let z = PolyVec::zeros(2);
    let dz = gadget_decompose(&z);
    for j in 0..dz.len() {
        assert!(dz.get(j).is_zero(), "slot {j} of a zero decomposition is nonzero");
    }

    let ones = PolyVec::new(vec![Rq::one()]);
    let d = gadget_decompose(&ones);
    assert!(d.get(0).equals(&Rq::one()), "digit 0 of 1 should be 1");
    for e in 1..GADGET_DIGITS {
        assert!(d.get(e).is_zero(), "digit {e} of 1 should be 0");
    }
}

// ---------------------------------------------------------------------------
// The balanced layer
// ---------------------------------------------------------------------------
//
// The references below are written in the *specification's* shape and not the
// crate's: `Nat.digits b n` as a whole list read with `getD e 0`, rather than a
// per-index division chain; `ZMod.valMinAbs` as a signed integer, rather than
// the crate's folded `u64` magnitude; and `bᵉ` as a bit shift, rather than
// `base_pow`'s repeated modular multiplication. A bug shared with the crate
// would have to be a bug in three unrelated places at once.

/// `Nat.digits b n` -- the whole little-endian digit list, shortest form.
fn nat_digits(mut n: u64, b: u64) -> Vec<u64> {
    let mut out = Vec::new();
    while n > 0 {
        out.push(n % b);
        n /= b;
    }
    out
}

/// `List.getD e 0`.
fn get_d(v: &[u64], e: usize) -> i64 {
    if e < v.len() {
        v[e] as i64
    } else {
        0
    }
}

/// `ZMod.valMinAbs`, as the signed integer it is: the representative in
/// `(-q/2, q/2]`. Every bound in `Gadget/Norms.lean` is stated on this.
fn val_min_abs(c: Fp) -> i64 {
    let v = c.to_u64();
    if v <= Q / 2 {
        v as i64
    } else {
        v as i64 - Q as i64
    }
}

/// `bᵉ` at `b = 16` as a bit shift; exact in `u64` for every `e` the digit
/// layers use (`16^8 = 2^32`).
fn base_pow_ref(e: usize) -> i128 {
    1i128 << (4 * e)
}

/// `balancedDigit 16 8 c e`, as its centered integer value.
fn balanced_digit_ref(c: Fp, e: usize) -> i64 {
    let shifted = ((u128::from(c.to_u64()) + u128::from(BALANCED_SHIFT)) % u128::from(Q)) as u64;
    get_d(&nat_digits(shifted, GADGET_BASE), e) - HALF_BASE as i64
}

/// `boundedBalancedZmodDigit 16 5 c e`, as its centered integer value: centre
/// first, shift in `ℤ`, clamp with `Int.toNat`, then take unsigned digits.
fn bounded_z_digit_ref(c: Fp, e: usize) -> i64 {
    let shifted = val_min_abs(c) + Z_BALANCED_SHIFT as i64;
    let clamped = if shifted < 0 { 0u64 } else { shifted as u64 };
    get_d(&nat_digits(clamped, GADGET_BASE), e) - HALF_BASE as i64
}

/// Reduce a centered integer into `[0, q)`, so a reconstruction computed in `ℤ`
/// can be compared with a field element.
fn into_field(x: i128) -> u64 {
    let q = i128::from(Q);
    (((x % q) + q) % q) as u64
}

/// The balanced digit is the unsigned digit of the *field*-shifted coefficient,
/// less `⌊b/2⌋` -- the specification's three steps, checked against an
/// independent computation of each.
#[test]
fn balanced_digit_is_the_shifted_unsigned_digit_recentered() {
    let mut rng = Lcg::new(0xBA1A_0000_0000_0001);
    let mut corpus = vec![Fp::ZERO, Fp::ONE, Fp::new(Q - 1), Fp::new(Q / 2)];
    for _ in 0..48 {
        corpus.push(rng.next_fp());
    }
    for c in corpus {
        for e in 0..GADGET_DIGITS {
            assert_eq!(
                val_min_abs(balanced_digit_at(c, e)),
                balanced_digit_ref(c, e),
                "balanced digit {e} of {} is wrong",
                c.to_u64()
            );
        }
    }
}

/// The shift must be a **field** addition. A raw `u64` one is a different
/// function, and this pins a witness: `c` whose *shifted* value is exactly
/// `16^7`. The raw sum is then `16^7 + q = 16^8 + 16^7 - 99`, whose digit 7 is
/// `16 mod 16 = 0` where the specification's `(c + shift).val = 16^7` has `1`.
///
/// Note the witness has to be chosen, not guessed: at `c = q - 1` the two
/// agree, because `q - 1 + shift` and its reduction happen to share their top
/// digit. The disagreement is exactly the `c` whose shifted value sits within
/// `q`'s deficit `99` of a multiple of `16^7`.
#[test]
fn the_raw_u64_shift_would_be_a_different_function() {
    let pow7: u64 = 1 << 28; // 16^7
    let c = Fp::new(pow7 + (Q - BALANCED_SHIFT));
    let raw = c.to_u64() + BALANCED_SHIFT;
    assert!(
        raw >= 1u64 << 32,
        "the witness no longer overflows the eight-digit window"
    );
    assert_eq!(raw - Q, pow7, "the witness is not the one the doc describes");

    let top = GADGET_DIGITS - 1;
    let wrong = get_d(&nat_digits(raw, GADGET_BASE), top) - HALF_BASE as i64;
    let right = val_min_abs(balanced_digit_at(c, top));
    assert_eq!(right, balanced_digit_ref(c, top));
    assert_ne!(
        wrong, right,
        "the raw-u64 shift and the field shift agree at {}; this test has stopped \
         testing anything",
        c.to_u64()
    );
    // And the raw form breaks the box on top of being wrong: nine base-16
    // digits where the gadget reads eight.
    assert_eq!(nat_digits(raw, GADGET_BASE).len(), GADGET_DIGITS + 1);
}

/// Every balanced digit lies in the paper's box `S_b = [-⌊b/2⌋, ⌈b/2⌉-1]`,
/// i.e. `[-8, 7]` at `b = 16` -- *as a centered residue*, which is the point:
/// `-8` is the field element `q - 8`, and a range check written on `to_u64()`
/// would reject it. Unconditional in `c` (`balancedZmodDigit_valMinAbs_mem`).
#[test]
fn balanced_digits_lie_in_the_paper_box() {
    let mut rng = Lcg::new(0xBA1A_0000_0000_0002);
    let mut corpus = vec![Fp::ZERO, Fp::ONE, Fp::new(Q - 1), Fp::new(Q / 2)];
    for _ in 0..48 {
        corpus.push(rng.next_fp());
    }
    let lo = -(HALF_BASE as i64);
    let hi = (GADGET_BASE - 1 - HALF_BASE) as i64;
    for c in corpus {
        for e in 0..GADGET_DIGITS {
            let d = val_min_abs(balanced_digit_at(c, e));
            assert!(
                lo <= d && d <= hi,
                "balanced digit {e} of {} is {d}, outside [{lo}, {hi}]",
                c.to_u64()
            );
        }
    }
}

/// The reconstruction law `Σₑ bᵉ · digit c e = c`, summed over the *centered*
/// digit values in `ℤ` and reduced once at the end -- the digitwise `⌊b/2⌋`
/// subtractions sum to exactly `balancedShift` and cancel it.
#[test]
fn balanced_digits_reconstruct_the_element() {
    let mut rng = Lcg::new(0xBA1A_0000_0000_0003);
    let mut corpus = vec![Fp::ZERO, Fp::ONE, Fp::new(Q - 1), Fp::new(Q / 2)];
    for _ in 0..48 {
        corpus.push(rng.next_fp());
    }
    for c in corpus {
        let mut acc: i128 = 0;
        for e in 0..GADGET_DIGITS {
            acc += base_pow_ref(e) * i128::from(val_min_abs(balanced_digit_at(c, e)));
        }
        assert_eq!(
            into_field(acc),
            c.to_u64(),
            "the balanced digits of {} do not reconstruct it",
            c.to_u64()
        );
    }
}

/// `balanced_digit_decompose` is `balanced_digit_at` at every position.
#[test]
fn balanced_digit_decompose_agrees_with_balanced_digit_at() {
    let mut rng = Lcg::new(0xBA1A_0000_0000_0004);
    for _ in 0..16 {
        let c = rng.next_fp();
        let all = balanced_digit_decompose(c);
        assert_eq!(all.len(), GADGET_DIGITS);
        for e in 0..GADGET_DIGITS {
            assert_eq!(all[e].to_u64(), balanced_digit_at(c, e).to_u64());
        }
    }
}

/// The balanced gadget inverse is lawful: `G · G⁻¹(x) = x`, the specification's
/// `IsLawfulGadgetDecomposition` at `balancedZmodDigitDecomposition`. This is
/// the headline for the balanced layer, as
/// [`gadget_mul_inverts_gadget_decompose`] is for the unsigned one.
#[test]
fn gadget_mul_inverts_balanced_gadget_decompose() {
    let mut rng = Lcg::new(0xBA1A_0000_0000_0005);
    for rows in [1usize, 2, 3] {
        let x = rng.next_poly_vec(rows);
        let decomposed = balanced_gadget_decompose(&x);
        assert_eq!(decomposed.len(), rows * GADGET_DIGITS);
        let back = gadget_mul(rows, &decomposed);
        assert!(
            back.equals(&x),
            "G · G⁻¹ is not the identity at rows = {rows}:\n  want {}\n  got  {}",
            show_vec(&x),
            show_vec(&back)
        );
    }
}

/// Slot `e` of block `i` holds digit `e` of every coefficient of `x[i]` -- the
/// `finProdFinEquiv` layout, at the balanced digit map.
#[test]
fn balanced_decomposition_slots_hold_the_right_digits() {
    let mut rng = Lcg::new(0xBA1A_0000_0000_0006);
    let rows = 3usize;
    let x = rng.next_poly_vec(rows);
    let d = balanced_gadget_decompose(&x);
    for i in 0..rows {
        for e in 0..GADGET_DIGITS {
            let slot = d.get(GADGET_DIGITS * i + e);
            for k in 0..RING_DEGREE {
                assert_eq!(
                    val_min_abs(slot.coeff(k)),
                    balanced_digit_ref(x.get(i).coeff(k), e),
                    "slot (i={i}, e={e}) coefficient {k}"
                );
            }
        }
    }
}

/// The balanced decomposition is *shorter* than the unsigned one: radius
/// `⌊b/2⌋ = 8` against `b - 1 = 15`, which is exactly why the paper uses it and
/// why its honest `ℓ₂²` is smaller by `(15/8)²`.
#[test]
fn the_balanced_decomposition_is_shorter_than_the_unsigned_one() {
    let mut rng = Lcg::new(0xBA1A_0000_0000_0007);
    let x = rng.next_poly_vec(4);
    let bal = balanced_gadget_decompose(&x);
    let uns = gadget_decompose(&x);
    let bal_infty = vec_l_infty_norm(&bal);
    let uns_infty = vec_l_infty_norm(&uns);
    // The two radii the specification states: `⌊b/2⌋` for the balanced digits
    // (`balancedZmodDigit_natAbs_le`) and `b - 1` for the unsigned ones
    // (`zmodDigit_natAbs_le`).
    let unsigned_radius = GADGET_BASE - 1;
    assert!(
        bal_infty <= HALF_BASE,
        "the balanced decomposition is not ⌊b/2⌋-short: ‖·‖∞ = {bal_infty}"
    );
    assert!(
        uns_infty <= unsigned_radius,
        "the unsigned decomposition broke its own bound: ‖·‖∞ = {uns_infty}"
    );
    assert!(
        bal_infty < uns_infty,
        "the balanced decomposition is not strictly shorter here ({bal_infty} vs {uns_infty}); \
         with 4 rows of {RING_DEGREE} coefficients both radii should be attained"
    );
    assert!(
        vec_l2_norm_sq(&bal) < vec_l2_norm_sq(&uns),
        "the balanced ℓ₂² is not smaller"
    );
    assert!(
        vec_l2_norm_sq(&bal) <= BETA_SQ,
        "the balanced decomposition misses the verifier's ℓ₂² bound"
    );
    assert!(bal_infty <= GAMMA, "the balanced decomposition misses γ");
}

// ---------------------------------------------------------------------------
// The bounded balanced layer, for the folded witness
// ---------------------------------------------------------------------------

/// The bounded `z` digit centres *first* and shifts in `ℤ` -- the reverse of
/// the message digit's shift-then-`.val`. Checked against the spec's own
/// expression, including the `Int.toNat` clamp.
#[test]
fn bounded_z_digit_centres_before_shifting() {
    let mut rng = Lcg::new(0xB2ED_0000_0000_0001);
    let mut corpus = vec![
        Fp::ZERO,
        Fp::ONE,
        Fp::new(Q - 1),
        Fp::new(Q / 2),
        Fp::new(Z_BOUND),
        Fp::new(Q - Z_BOUND),
    ];
    for _ in 0..48 {
        corpus.push(rng.next_fp());
    }
    for c in corpus {
        for e in 0..Z_DIGITS {
            assert_eq!(
                val_min_abs(bounded_z_digit_at(c, e)),
                bounded_z_digit_ref(c, e),
                "bounded z digit {e} of {} is wrong",
                c.to_u64()
            );
        }
    }
}

/// The range is unconditional: every bounded `z` digit is in `[-8, 7]` for
/// *every* input, short or not (`boundedBalancedZmodDigit_valMinAbs_mem` takes
/// no shortness hypothesis). What shortness buys is reconstruction, not range.
#[test]
fn bounded_z_digits_lie_in_the_paper_box_unconditionally() {
    let mut rng = Lcg::new(0xB2ED_0000_0000_0002);
    let mut corpus = vec![Fp::ZERO, Fp::new(Q - 1), Fp::new(Q / 2), Fp::new(Q / 2 + 1)];
    for _ in 0..64 {
        corpus.push(rng.next_fp());
    }
    let lo = -(HALF_BASE as i64);
    let hi = (GADGET_BASE - 1 - HALF_BASE) as i64;
    for c in corpus {
        for e in 0..Z_DIGITS {
            let d = val_min_abs(bounded_z_digit_at(c, e));
            assert!(
                lo <= d && d <= hi,
                "bounded z digit {e} of {} is {d}, outside [{lo}, {hi}]",
                c.to_u64()
            );
        }
    }
}

/// Reconstruction holds on inputs within `Z_BOUND` -- including at the bound
/// itself, on both signs, which is where a `τ` one too small would fail.
#[test]
fn bounded_z_digits_reconstruct_short_elements() {
    let mut rng = Lcg::new(0xB2ED_0000_0000_0003);
    let mut corpus = vec![
        Fp::ZERO,
        Fp::ONE,
        Fp::new(Q - 1),
        Fp::new(Z_BOUND),
        Fp::new(Q - Z_BOUND),
    ];
    for _ in 0..64 {
        let v = rng.next_u64() % (2 * Z_BOUND + 1);
        // A centered value in `[-Z_BOUND, Z_BOUND]`, as a residue.
        corpus.push(if v <= Z_BOUND {
            Fp::new(v)
        } else {
            Fp::new(Q - (v - Z_BOUND))
        });
    }
    for c in corpus {
        assert!(
            val_min_abs(c).unsigned_abs() <= Z_BOUND,
            "the corpus element {} is not short",
            c.to_u64()
        );
        let mut acc: i128 = 0;
        for e in 0..Z_DIGITS {
            acc += base_pow_ref(e) * i128::from(val_min_abs(bounded_z_digit_at(c, e)));
        }
        assert_eq!(
            into_field(acc),
            c.to_u64(),
            "the {Z_DIGITS} bounded digits of {} do not reconstruct it",
            c.to_u64()
        );
    }
}

/// And it fails outside the bound, deterministically -- so the hypothesis on
/// `boundedBalancedZmodDigit_reconstruct` is not vacuous and `Z_DIGITS = 5`
/// really is a *bounded* decomposition rather than a full-width one. Five
/// base-16 digits cannot carry every residue: `16^5 < q`.
#[test]
fn bounded_z_digits_do_not_reconstruct_long_elements() {
    let capacity = i128::from(GADGET_BASE - 1 - HALF_BASE) * i128::from(69_905u64);
    assert!(
        i128::from(Z_BOUND) <= capacity,
        "Z_BOUND exceeds the balanced capacity of Z_DIGITS digits"
    );
    let c = Fp::new(Q / 2);
    assert!(
        i128::from(val_min_abs(c).unsigned_abs()) > capacity,
        "the witness is not outside the capacity"
    );
    let mut acc: i128 = 0;
    for e in 0..Z_DIGITS {
        acc += base_pow_ref(e) * i128::from(val_min_abs(bounded_z_digit_at(c, e)));
    }
    assert_ne!(
        into_field(acc),
        c.to_u64(),
        "a long element reconstructed; the bounded decomposition is not bounded"
    );
}

/// `digit_at` is still `⌊c / bᵉ⌋ mod b`, at every `e` -- including past the
/// digit count, where the specification's `getD` returns its `0` default.
///
/// The implementation is now a shift and a mask rather than a division chain,
/// and this is the oracle for that: the reference below is the division chain
/// it replaced, written out here so the two cannot drift together. `e` is taken
/// well past `GADGET_DIGITS` on purpose, because that is exactly where a bare
/// shift would be undefined and the guard is what keeps the agreement.
#[test]
fn digit_at_agrees_with_the_division_chain_at_every_index() {
    let b = hachi::params::GADGET_BASE;
    let reference = |c: u64, e: usize| -> u64 {
        let mut rest = c;
        for _ in 0..e {
            rest /= b;
        }
        rest % b
    };

    let mut rng = Lcg::new(0x6AD6_0001);
    let mut cs: Vec<u64> = vec![0, 1, b - 1, b, Q - 1, Q / 2];
    for _ in 0..64 {
        cs.push(rng.next_u64() % Q);
    }

    for &c in &cs {
        for e in 0..40usize {
            assert_eq!(
                hachi::gadget::digit_at(Fp::new(c), e).to_u64(),
                reference(c, e),
                "digit_at({c}, {e}) disagrees with the division chain"
            );
        }
    }
}
