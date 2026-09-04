//! The ring-switching layer: the balanced digit decomposition of a quotient
//! row.
//!
//! Reference specification:
//! `ArkLib/Commitments/Functional/Hachi/RingSwitch/RhoDigits.lean`, with the
//! reduction it feeds in `RingSwitch/Reduction.lean`.
//!
//! Ring switching sends a `Rq`-level claim down to the coefficient field by
//! writing each quotient row `ρ` as `Σ_u bᵘ · ρ_u` over balanced base-`b`
//! digits, so that the lifted witness is short enough for the Eq. (20) range
//! check. [`rho_digits`] is one such digit: the coefficientwise
//! [`crate::gadget::balanced_digit_at`], truncated at the ring dimension.
//!
//! # The digit count is the gadget's
//!
//! The specification writes it `rhoDigitCount q b = Nat.clog b q`
//! (`RhoDigits.lean:66`), consumed at `bDig := bZero` on the honest chain. At
//! these parameters `bZero = b = 16` ([`params::B_ZERO`]) and
//! `Nat.clog 16 (2^32 - 99) = 8`, because `16^7 = 268435456 < q ≤ 16^8` -- so it
//! *is* [`params::GADGET_DIGITS`] and gets no constant of its own.
//! `lean/Check.lean` § 1 proves that identity rather than naming the number
//! twice.
//!
//! # A quotient row is carried as an `Rq`
//!
//! ArkLib types `ρ` as a `CPolynomial (ZMod q)` (`LiftedWitness.ρ`), not as an
//! `Rq Φ`, so this is a choice. It is lossless at every point the honest chain
//! reaches: `rhoDigits` truncates at `Φ.φ.natDegree` by construction
//! (`RhoDigits.lean:126`), `LiftedWitness.hρ` bounds every quotient row by
//! `natDegree ≤ d - 1` (which is exactly the hypothesis `rhoDigits_reconstruct`
//! takes, `:169`), and the output is itself `d`-wide
//! (`rhoDigits_natDegree_le`, `:141`) so `Rq::from_coeffs` reads it back
//! unchanged. The `hρ` bound travels as a hypothesis on the equivalence
//! statement, alongside the `Rq` shape invariant.

use alloc::vec::Vec;
use cpoly::Fp;

use crate::gadget;
use crate::params;
use crate::ring::Rq;

// @genesis 09df61b 2026-09-04 — ringswitch::rho_digits
/// Digit `u` of a quotient row (spec: `rhoDigits Φ b ρ u`,
/// `RingSwitch/RhoDigits.lean:126`).
///
/// Mirrors ArkLib's `rhoDigits` at `b = GADGET_BASE`.
///
/// Apply [`crate::gadget::balanced_digit_at`] to every coefficient below the
/// ring dimension `d = deg φ` and truncate there, which is the spec's
/// `CPolynomial.ofFinCoeff Φ.φ.natDegree` -- and, on this side,
/// [`Rq::from_coeffs`] at the same width. The digit index `u` is the same for
/// every coefficient; the *coefficient* index is what the loop runs over.
///
/// The digit count the balanced map is taken at is `rhoDigitCount q b`, which
/// is [`params::GADGET_DIGITS`] here (module header), so this is
/// [`crate::gadget::balanced_digit_at`] with no reparameterization.
///
/// Reconstruction `Σ_u bᵘ · rho_digits(ρ, u) = ρ` is
/// `rhoDigits_reconstruct` (`:169`) and needs `ρ`'s own degree bound; each
/// digit is `⌊b/2⌋ = 8`-bounded as a centered residue unconditionally
/// (`rhoDigits_valMinAbs_natAbs_le`, `:153`), which is what makes the
/// `liftShort` range check pass at [`params::CHAIN_GAMMA`]` = 15`.
pub fn rho_digits(rho: &Rq, u: usize) -> Rq {
    let degree: usize = params::RING_DEGREE;
    let mut coeffs: Vec<Fp> = Vec::new();
    let mut k: usize = 0;
    while k < degree {
        coeffs.push(gadget::balanced_digit_at(rho.coeff(k), u));
        k += 1;
    }
    Rq::from_coeffs(&coeffs)
}
