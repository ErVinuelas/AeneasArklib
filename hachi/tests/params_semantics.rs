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
//! so a derived form would extract as a `Result`), and `KAPPA` has a legality
//! ceiling (`κ² < q`) that only holds at this modulus.

// Every assertion here is *about* a constant -- that is the file's purpose, so
// clippy's "this assertion has a constant value" is the expected state and not a
// finding. The cast is to `u32` for `pow`, on values below 64.
#![allow(clippy::assertions_on_constants, clippy::cast_possible_truncation)]

use hachi::params::{
    BETA_SQ, BLOCKS, EXT_DEGREE, EXT_W, GADGET_BASE, GADGET_DIGITS, GAMMA, INNER_ROWS, KAPPA,
    MESSAGE_ROWS, ML_HIGH_LEN, ML_LOW_LEN, ML_POLY_LEN, ML_VARS_HIGH, ML_VARS_LOW, OUTER_ROWS, Q,
    RING_DEGREE, RING_LOG_DEGREE,
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
    assert_eq!(Q % 2, 1);
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
/// `GADGET_DIGITS` to 8 rather than merely permitting it.
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

/// `GAMMA` is the weak-opening `ℓ∞` bound `γ̄ = b` of ArkLib's paper-parameter
/// mapping (`QuadEval/Soundness.lean`: the paper's `S_b` box relaxed to the
/// symmetric ball `‖·‖∞ ≤ b`). It is a literal in `params.rs`, so nothing but
/// this keeps it in step with the base -- and the honest decomposition's own
/// bound `b - 1` (`gadgetDecompose_zmod_vecLInftyNorm_le`) must sit strictly
/// inside it, or honest openings would need the slack they do not have.
#[test]
fn gamma_is_the_weak_opening_bound() {
    assert_eq!(GAMMA, GADGET_BASE);
    assert!(GADGET_BASE - 1 < GAMMA);
}

/// The digit bound above holds only under `b - 1 ≤ q/2` (`zmodDigit_natAbs_le`),
/// which is what stops a small *non-negative* digit from wrapping to a negative
/// centered representative.
#[test]
fn digit_bound_side_condition_holds() {
    assert!(GADGET_BASE - 1 <= Q / 2);
}

/// `BETA_SQ` is ArkLib's `quadEvalBetaSq γ b τ d m δ` at `γ := b` (Hachi
/// Lemma 8's `4·B_z`, `QuadEval/Soundness.lean`):
/// `4 · (2^m·δ) · (d · ((Σ_{u<τ} b^u) · γ)²)` with `τ = 5`, the folded-witness
/// digit count of ArkLib's `ℓ = 30` profile (ArkLib PR #847,
/// `Hachi/Params.lean`): the least `τ` whose balanced capacity
/// `(b-1-⌊b/2⌋)·Σ_{u<τ} b^u` holds the honest bound `‖z‖∞ ≤ 2ʳ·ω·⌊b/2⌋` --
/// neither [NOZ26] Fig. 9's `τ = 4` nor the full-coverage `δ = 8` (see the
/// `BETA_SQ` docstring). `τ`'s only appearance in this crate. Also a literal,
/// for the same reason as `GAMMA`.
#[test]
fn beta_sq_is_the_weak_opening_bound() {
    const TAU: u32 = 5;
    let b = u128::from(GADGET_BASE);
    // `hcap`: the honest `z` bound `2ʳ·ω·⌊b/2⌋` (r = ML_VARS_LOW, ω = KAPPA/2)
    // fits `τ` balanced digits -- and `τ` is minimal: four digits carry
    // exactly Fig. 9's `z` bound 30583, which is below it.
    let capacity = |t: u32| (b - 1 - b / 2) * (0..t).map(|u| b.pow(u)).sum::<u128>();
    let honest_z_bound: u128 =
        (1u128 << hachi::params::ML_VARS_LOW) * u128::from(hachi::params::KAPPA / 2) * (b / 2);
    assert_eq!(honest_z_bound, 131_072);
    assert!(honest_z_bound <= capacity(TAU));
    assert_eq!(capacity(TAU - 1), 30_583);
    assert!(capacity(TAU - 1) < honest_z_bound);
    // ... and it is *not* a full-width decomposition of `ℤ_q`: `b^τ < q`.
    assert!(b.pow(TAU) < u128::from(Q));
    let geom: u128 = (0..TAU).map(|u| b.pow(u)).sum();
    let z_l2_sq =
        (MESSAGE_ROWS * GADGET_DIGITS) as u128 * (RING_DEGREE as u128 * (geom * u128::from(GAMMA)).pow(2));
    assert_eq!(BETA_SQ, 4 * z_l2_sq);
}

/// ... and the honest decomposition's own `ℓ₂²` bound
/// (`gadgetDecompose_zmod_vecL2NormSq_le` at these dimensions, with the honest
/// digit bound `b - 1`) sits far inside it -- the slack is what admits the
/// protocol's *extracted* openings, and it is why no admissible challenge can
/// push an honest opening past `BETA_SQ`.
#[test]
fn beta_sq_admits_the_honest_decomposition() {
    let honest = (MESSAGE_ROWS * GADGET_DIGITS) as u128
        * RING_DEGREE as u128
        * u128::from(GADGET_BASE - 1).pow(2);
    assert_eq!(honest, 1_887_436_800);
    assert!(honest <= BETA_SQ);
}

/// `KAPPA` is capped by the Lyubashevsky-Seiler invertibility lemma
/// (`isUnit_of_l1Norm_le`), which needs `κ² < q`: that is what turns the
/// verifier's `0 < ‖c‖₁ ≤ κ` into the invertibility a weak opening actually
/// requires. `params.rs` no longer sits on that ceiling (`⌊√q⌋ = 65535`): the
/// value is the weak-opening bound `ω̄ = 2ω = 32` at [NOZ26] Fig. 9's `ω = 16`
/// (extracted openings carry challenge *differences*), so the checkable facts
/// are legality -- ArkLib Lemma 8's own `hκ : (2ω)² < q` -- and the relation
/// to `ω`.
#[test]
fn kappa_is_legal_for_invertibility() {
    // ArkLib Lemma 8's `hκ : (2ω)² < q`, at the paper's ω = 16.
    assert_eq!(KAPPA, 2 * 16);
    assert!(u128::from(KAPPA).pow(2) < u128::from(Q));
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
/// are built from. `BLOCKS` and `MESSAGE_ROWS` must be at least 2 so that the
/// per-block and per-row structure -- more than one row, more than one block --
/// is exercised at all; at [NOZ26] Fig. 9 they are 1024 and carry that duty
/// alone. The Ajtai row counts are the paper's `n_A = n_B = 1`, so for them
/// only nonzero-ness is checkable: a single Ajtai row is a legal (and the
/// paper's) shape, not a degenerate one.
#[test]
fn dimensions_are_nondegenerate() {
    assert!(MESSAGE_ROWS >= 2);
    assert!(INNER_ROWS >= 1);
    assert!(OUTER_ROWS >= 1);
    assert!(BLOCKS >= 2);
}

/// The evaluation-split shape constants are the powers of two their variable
/// counts claim, and match the consumer's shape: the reshaped matrix is
/// `blocks × messageRows` (`derivedMsgMatrix`, `QuadEval/Reduction.lean:193`),
/// so `2^nl = BLOCKS` and `2^nh = MESSAGE_ROWS`.
#[test]
fn evalsplit_shape_constants_are_consistent() {
    assert_eq!(1usize << ML_VARS_LOW, ML_LOW_LEN);
    assert_eq!(1usize << ML_VARS_HIGH, ML_HIGH_LEN);
    assert_eq!(ML_LOW_LEN * ML_HIGH_LEN, ML_POLY_LEN);
    assert_eq!(ML_LOW_LEN, BLOCKS);
    assert_eq!(ML_HIGH_LEN, MESSAGE_ROWS);
}
