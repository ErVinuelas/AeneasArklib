//! `src/gadget.rs`: the base-`b` digit decomposition, the gadget matrix, and the
//! two directions of the gadget algebra.
//!
//! The headline test is [`gadget_mul_inverts_gadget_decompose`], which is the
//! specification's `IsLawfulGadgetDecomposition` (`Gadget/Core.lean:152`) at these
//! parameters: `G · G⁻¹(x) = x`. Everything else supports it -- the digit map, the
//! matrix layout, and the shortness bound that makes the decomposition worth doing
//! in the first place.

// Bounds are computed from `usize` parameters below 64 and fed to `pow`.
#![allow(clippy::cast_possible_truncation)]

mod support;

use cpoly::Fp;
use hachi::commit::{l_infty_norm, vec_l2_norm_sq, vec_l_infty_norm};
use hachi::gadget::{base_pow, digit_at, digit_decompose, gadget_decompose, gadget_matrix, gadget_mul};
use hachi::linalg::PolyVec;
use hachi::params::{BETA_SQ, GADGET_BASE, GADGET_DIGITS, GAMMA, MESSAGE_ROWS, Q, RING_DEGREE};
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
/// `bᵉ` passes the modulus. At `b = 2` and `digits = 32` it does not, so the test
/// checks the modular behaviour directly at an exponent that does.
#[test]
fn base_pow_is_modular() {
    assert_eq!(base_pow(0).to_u64(), 1);
    assert_eq!(base_pow(1).to_u64(), GADGET_BASE);
    assert_eq!(base_pow(31).to_u64(), 1 << 31);
    // 2^32 = 4294967296 = Q + 99.
    assert_eq!(base_pow(32).to_u64(), 99);
    assert_eq!(base_pow(33).to_u64(), 198);
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
/// `b - 1 = GAMMA`, which is `gadgetDecompose_zmod_vecLInftyNorm_le`. Without
/// this the round trip above would be arithmetic with no cryptographic content.
#[test]
fn the_decomposition_is_l_infty_short() {
    let mut rng = Lcg::new(0xDEAD_BEEF_CAFE_0006);
    let x = rng.next_poly_vec(MESSAGE_ROWS);
    let decomposed = gadget_decompose(&x);
    assert!(
        vec_l_infty_norm(&decomposed) <= GAMMA,
        "‖G⁻¹(x)‖∞ = {} exceeds γ = {GAMMA}",
        vec_l_infty_norm(&decomposed)
    );
    // Entrywise too, which is the form the spec's per-block lemma takes.
    for j in 0..decomposed.len() {
        assert!(l_infty_norm(decomposed.get(j)) <= GAMMA);
    }
}

/// ... and `ℓ₂²`-short, by `(rows·digits)·(deg φ)·(b-1)²`, which at these
/// parameters is exactly `BETA_SQ`.
#[test]
fn the_decomposition_meets_the_l2_bound() {
    let mut rng = Lcg::new(0xDEAD_BEEF_CAFE_0007);
    let x = rng.next_poly_vec(MESSAGE_ROWS);
    let decomposed = gadget_decompose(&x);
    let bound = (MESSAGE_ROWS * GADGET_DIGITS) as u128 * RING_DEGREE as u128 * u128::from(GAMMA).pow(2);
    assert_eq!(bound, BETA_SQ);
    assert!(
        vec_l2_norm_sq(&decomposed) <= bound,
        "‖G⁻¹(x)‖₂² = {} exceeds {bound}",
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
