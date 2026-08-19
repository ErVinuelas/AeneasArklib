//! The parameters satisfy every side condition the ArkLib specification carries
//! as a hypothesis.
//!
//! `src/params.rs` fixes concrete values for `(q, α, b, digits)`, which the spec
//! leaves generic. Each generic statement comes with hypotheses -- `Fact
//! (Nat.Prime q)`, `1 < b`, `q ≤ b ^ digits` -- and an equivalence proof can only
//! instantiate it if the constants actually discharge them. Those hypotheses are
//! checked on the Lean side too, once the proofs exist; checking them here as
//! well means a bad parameter edit fails in seconds rather than at the end of a
//! Lean build.
//!
//! The dimensions and norm bounds added for the commitment layer are checked the
//! same way, and for two further reasons: `GAMMA` and `BETA_SQ` are *derived*
//! quantities written as literals (Aeneas models `const` arithmetic as fallible,
//! so a derived form would extract as a `Result`), and `KAPPA` sits on a ceiling
//! that only holds at this modulus.

// Every assertion here is *about* a constant -- that is the file's purpose, so
// clippy's "this assertion has a constant value" is the expected state and not a
// finding. The cast is to `u32` for `pow`, on values below 64.
#![allow(clippy::assertions_on_constants, clippy::cast_possible_truncation)]

use hachi::params::{
    BETA_SQ, BLOCKS, EXT_DEGREE, EXT_W, GADGET_BASE, GADGET_DIGITS, GAMMA, INNER_ROWS, KAPPA,
    MESSAGE_ROWS, OUTER_ROWS, Q, RING_DEGREE, RING_LOG_DEGREE,
};

/// `a * b mod m` without overflow, for `m < 2^32`.
///
/// Every value below is reduced mod `Q < 2^32`, so each product is `< 2^64`.
fn mul_mod(a: u64, b: u64, m: u64) -> u64 {
    (a % m) * (b % m) % m
}

fn pow_mod(mut base: u64, mut exp: u64, m: u64) -> u64 {
    let mut acc = 1u64;
    base %= m;
    while exp > 0 {
        if exp % 2 == 1 {
            acc = mul_mod(acc, base, m);
        }
        base = mul_mod(base, base, m);
        exp /= 2;
    }
    acc
}

/// `Fact (Nat.Prime q)` is an instance argument of essentially every definition in
/// `CyclotomicRing/PowTwo.lean`, so a composite `Q` would not merely weaken the
/// scheme -- no spec would instantiate at all.
///
/// Trial division is fine here: `Q < 2^32`, so this stops by 65536.
#[test]
fn q_is_prime() {
    assert!(Q > 1);
    assert!(Q % 2 == 1);
    let mut d = 3u64;
    while d * d <= Q {
        assert!(Q % d != 0, "Q is divisible by {d}");
        d += 2;
    }
}

/// `Q < 2^32` is the no-overflow argument every `u64` intermediate rests on:
/// a product of two reduced representatives is then `< 2^64`.
#[test]
fn q_fits_in_32_bits() {
    assert!(Q < 1u64 << 32);
    // And the bound is tight enough to be worth stating: this is the *largest*
    // prime below 2^32 that keeps the `- 99` shape, so there is no slack to
    // spend on a wider modulus without moving to `u128` intermediates.
    assert_eq!(Q, (1u64 << 32) - 99);
}

/// `Y^4 - W` is irreducible over `F_q` for non-square `W` exactly when
/// `q ≡ 1 mod 4`, which is what makes `Ext4` a field rather than a ring with
/// zero divisors.
#[test]
fn q_is_one_mod_four() {
    assert_eq!(Q % 4, 1);
}

/// ... and `W` really is a non-square mod `Q`, by Euler's criterion:
/// `W^((q-1)/2) = -1`.
#[test]
fn ext_w_is_a_non_square() {
    assert_eq!(pow_mod(EXT_W, (Q - 1) / 2, Q), Q - 1);
}

/// The extension is the quartic one `cpoly` proves things about.
#[test]
fn ext_degree_is_four() {
    assert_eq!(EXT_DEGREE, 4);
}

/// `RING_DEGREE` is derived from `RING_LOG_DEGREE`; they cannot drift apart.
#[test]
fn ring_degree_is_a_power_of_two() {
    assert_eq!(RING_DEGREE, 1 << RING_LOG_DEGREE);
    assert!(RING_DEGREE.is_power_of_two());
}

/// `zmodDigitDecomposition` requires `1 < b`.
#[test]
fn gadget_base_exceeds_one() {
    assert!(GADGET_BASE > 1);
}

/// `zmodDigitDecomposition` requires `q ≤ b ^ digits`, so that every residue fits
/// in `digits` base-`b` digits and the reconstruction law holds.
#[test]
fn gadget_digits_cover_the_modulus() {
    let capacity = (GADGET_BASE as u128).pow(GADGET_DIGITS as u32);
    assert!(
        u128::from(Q) <= capacity,
        "Q = {Q} exceeds b^digits = {capacity}"
    );
}

/// ... and `digits` is the *smallest* count that does, so the gadget is not
/// carrying a digit that is provably always zero. This is what pins
/// `GADGET_DIGITS` to 32 rather than merely permitting it.
#[test]
fn gadget_digits_are_minimal() {
    let one_fewer = (GADGET_BASE as u128).pow(GADGET_DIGITS as u32 - 1);
    assert!(
        u128::from(Q) > one_fewer,
        "digits could be reduced: Q = {Q} already fits in b^{} = {one_fewer}",
        GADGET_DIGITS - 1
    );
}

/// The parameter file and `cpoly`'s field agree on the modulus. If they ever
/// disagree, every proof that bridges the two layers is about two different
/// fields.
#[test]
fn q_agrees_with_the_field_layer() {
    assert_eq!(Q, cpoly::field::P);
}

/// `GAMMA` is the `ℓ∞` bound the honest decomposition meets, which
/// `Gadget/Norms.lean`'s `gadgetDecompose_zmod_vecLInftyNorm_le` proves to be
/// `b - 1`. It is a literal in `params.rs`, so nothing but this keeps it in step
/// with the base.
#[test]
fn gamma_is_the_digit_bound() {
    assert_eq!(GAMMA, GADGET_BASE - 1);
}

/// The digit bound above holds only under `b - 1 ≤ q/2` (`zmodDigit_natAbs_le`),
/// which is what stops a small *non-negative* digit from wrapping to a negative
/// centered representative.
#[test]
fn digit_bound_side_condition_holds() {
    assert!(GADGET_BASE - 1 <= Q / 2);
}

/// `BETA_SQ` is `(messageRows · messageDigits) · (deg φ) · (b-1)²`, the
/// `ℓ₂²` bound of `gadgetDecompose_zmod_vecL2NormSq_le` at these dimensions.
/// Also a literal, for the same reason as `GAMMA`.
#[test]
fn beta_sq_is_the_honest_l2_bound() {
    let expected =
        (MESSAGE_ROWS * GADGET_DIGITS) as u128 * RING_DEGREE as u128 * u128::from(GAMMA).pow(2);
    assert_eq!(BETA_SQ, expected);
}

/// `KAPPA` is capped by the Lyubashevsky-Seiler invertibility lemma
/// (`isUnit_of_l1Norm_le`), which needs `κ² < q`: that is what turns the
/// verifier's `0 < ‖c‖₁ ≤ κ` into the invertibility a weak opening actually
/// requires. `κ` is a rejection threshold, so `params.rs` takes the ceiling --
/// and both halves of that claim are checked: it is legal, and one more would
/// not be.
#[test]
fn kappa_is_the_invertibility_ceiling() {
    assert!(u128::from(KAPPA).pow(2) < u128::from(Q));
    assert!(u128::from(KAPPA + 1).pow(2) >= u128::from(Q));
}

/// The other half of that lemma's hypothesis: `q % 8 = 5`. Unlike `κ`, this is
/// not a choice -- it is a property of the Hachi prime, and without it the
/// invertibility argument (and so the meaning of the `κ` check) is gone.
#[test]
fn q_is_five_mod_eight() {
    assert_eq!(Q % 8, 5);
}

/// The honest challenge is `c = 1`, whose `ℓ₁` norm is `1`; the verifier's
/// `0 < ‖c‖₁ ≤ κ` must admit it, or nothing this crate produces would verify.
#[test]
fn the_honest_challenge_is_admissible() {
    assert!(KAPPA >= 1);
}

/// The matrix dimensions are the ones the specification's `PublicParams` shapes
/// are built from, and each has to be at least 2 for the structure it exists to
/// exercise -- more than one row, more than one block -- to be exercised at all.
#[test]
fn dimensions_are_nondegenerate() {
    assert!(MESSAGE_ROWS >= 2);
    assert!(INNER_ROWS >= 2);
    assert!(OUTER_ROWS >= 2);
    assert!(BLOCKS >= 2);
}
