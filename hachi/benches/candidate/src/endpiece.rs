//! The terminal checks of Hachi's nonrecursive opening.
//!
//! Reference specification:
//! `ArkLib/Commitments/Functional/Hachi/EndPiece/Reduction.lean`.
//!
//! Target 3 introduces the two shortness checks because they complete the
//! ring-switch link. Target 6 will extend this module with the terminal
//! commitment and multilinear-evaluation conjunction.

use alloc::vec::Vec;

use crate::commit::{centered_abs, vec_l_infty_norm};
use crate::params;
use crate::ringswitch::{rho_digits_at, LiftedWitness, QuotientRow};

/// Check every coefficient of every balanced quotient digit against the
/// chain's bound (spec: `rhoDigitsShortCheck`,
/// `EndPiece/Reduction.lean:111`).
///
/// Mirrors `rhoDigitsShortCheck`.
///
/// At the fixed parameters the result is always `true`, since balanced base-16
/// digits have centered magnitude at most 8 and `CHAIN_GAMMA = 15`. The loop is
/// retained as the direct translation so a future parameter change cannot
/// silently remove the verifier check.
///
/// The three nested loops are the specification's three quantifiers, in its
/// order: `∀ i` over the rows, `∀ u < δ` over the digits, `∀ k < d` over the
/// coefficients (`EndPiece/Reduction.lean:111-113`). The digit is addressed by
/// the pair `(i, u)` through [`crate::ringswitch::rho_digits_at`] because that
/// is what `rhoDigitsShortCheck` applies `rhoDigits` to. An earlier version
/// built the flat index `i * GADGET_DIGITS + u` and went through
/// `rho_digit_as_rq`, which split it back apart; that round trip is not in the
/// specification, and because `i * 8` is a checked `usize` product over an
/// `i` bounded only by `rho.len()`, it made the extracted model *fallible* --
/// forcing an `n * 8 ≤ Usize.max` hypothesis into
/// `rho_digits_short_check_spec` and, through the caller,
/// `lift_short_check_spec`. Forming no product removes the hypothesis instead
/// of assuming it away. The frozen genesis copy still has the old shape, so
/// this operation's `vs genesis` column now contains a **faithfulness repair
/// and not an optimization**; see NOTES.md § "The flat index the specification
/// does not have".
pub fn rho_digits_short_check(rho: &Vec<QuotientRow>) -> bool {
    let rows: usize = rho.len();
    let mut i: usize = 0;
    let mut short: bool = true;
    while i < rows {
        let mut u: usize = 0;
        while u < params::GADGET_DIGITS {
            let digit = rho_digits_at(rho, i, u);
            let mut k: usize = 0;
            while k < params::RING_DEGREE {
                if centered_abs(digit.coeff(k)) > params::CHAIN_GAMMA {
                    short = false;
                }
                k += 1;
            }
            u += 1;
        }
        i += 1;
    }
    short
}

/// Check the `ℓ∞` bound on `z` and the quotient-digit bound (spec:
/// `liftShortCheck`, `EndPiece/Reduction.lean:130`).
///
/// Mirrors `liftShortCheck`.
pub fn lift_short_check(w: &LiftedWitness) -> bool {
    vec_l_infty_norm(w.z()) <= params::CHAIN_GAMMA && rho_digits_short_check(w.rho())
}
