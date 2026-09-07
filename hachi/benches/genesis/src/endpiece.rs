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
use crate::ringswitch::{rho_digit_as_rq, LiftedWitness, QuotientRow};

// @genesis 240f277 2026-09-07 — endpiece::rho_digits_short_check
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
pub fn rho_digits_short_check(rho: &Vec<QuotientRow>) -> bool {
    let rows: usize = rho.len();
    let mut i: usize = 0;
    let mut short: bool = true;
    while i < rows {
        let mut u: usize = 0;
        while u < params::GADGET_DIGITS {
            let j: usize = i * params::GADGET_DIGITS + u;
            let digit = rho_digit_as_rq(rho, j);
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

// @genesis 240f277 2026-09-07 — endpiece::lift_short_check
/// Check the `ℓ∞` bound on `z` and the quotient-digit bound (spec:
/// `liftShortCheck`, `EndPiece/Reduction.lean:130`).
///
/// Mirrors `liftShortCheck`.
pub fn lift_short_check(w: &LiftedWitness) -> bool {
    vec_l_infty_norm(w.z()) <= params::CHAIN_GAMMA && rho_digits_short_check(w.rho())
}
