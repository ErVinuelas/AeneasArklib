//! The ring-switching link: quotient digits, the lifted witness, and its Ajtai
//! commitment.
//!
//! Reference specification:
//! `ArkLib/Commitments/Functional/Hachi/RingSwitch/RhoDigits.lean`, with the
//! reduction it feeds in `RingSwitch/Reduction.lean`.
//!
//! Ring switching sends a `Rq`-level claim down to the coefficient field by
//! writing each quotient row `ρ` as `Σ_u bᵘ · ρ_u` over balanced base-`b`
//! digits, so that the lifted witness is short enough for the Eq. (20) range
//! check. [`rho_digits`] is one such digit: the coefficientwise
//! [`crate::gadget::balanced_digit_at`], truncated at the ring dimension. The
//! complete lift then appends all quotient digits to the `R^lin` witness `z`
//! and commits that vector under its caller-supplied key.
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
use crate::linalg::{PolyMatrix, PolyVec};
use crate::params;
use crate::ring::Rq;

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

/// A quotient polynomial represented by its `d` coefficients.
///
/// Mirrors `Lift.LiftedWitness.ρ` at the degree bound carried by
/// `Lift.LiftedWitness.hρ` (`ProofSystem/RingSwitching/Lift/Reduction.lean:82`).
///
/// ArkLib deliberately gives quotient rows no quotient-ring multiplication.
/// Wrapping the representation keeps that distinction on the Rust side even
/// though the stored coefficient array has the same runtime shape as [`Rq`].
pub struct QuotientRow(Rq);

impl QuotientRow {
    /// Build a quotient row from little-endian coefficients, truncated and
    /// padded to the cyclotomic degree.
    pub fn new(coeffs: &Vec<Fp>) -> QuotientRow {
        QuotientRow(Rq::from_coeffs(coeffs))
    }

    /// Read coefficient `k` of the quotient polynomial.
    pub fn coeff(&self, k: usize) -> Fp {
        self.0.coeff(k)
    }

    /// Read the quotient row back as a ring element (spec: `rhoAsRq`,
    /// `RingSwitch/Reduction.lean:249`).
    ///
    /// Mirrors `rhoAsRq`.
    pub fn to_rq(&self) -> Rq {
        self.0.copy()
    }
}

/// Hachi Eq. (21)'s lifted witness: the `R^lin` witness `z` and one quotient
/// polynomial per output row (spec: `LiftedWitness`,
/// `RingSwitch/Reduction.lean:136`).
///
/// Mirrors `LiftedWitness`.
pub struct LiftedWitness {
    z: PolyVec,
    rho: Vec<QuotientRow>,
}

impl LiftedWitness {
    /// Bundle the `R^lin` witness and quotient rows.
    pub fn new(z: PolyVec, rho: Vec<QuotientRow>) -> LiftedWitness {
        LiftedWitness { z, rho }
    }

    /// The `R^lin` witness block.
    pub fn z(&self) -> &PolyVec {
        &self.z
    }

    /// The quotient rows.
    pub fn rho(&self) -> &Vec<QuotientRow> {
        &self.rho
    }
}

/// Entry `j` of the quotient-digit block (spec: `rhoDigitAsRq`,
/// `RingSwitch/Reduction.lean:256`).
///
/// Mirrors `rhoDigitAsRq`.
///
/// The flattened index is row-major: `j / GADGET_DIGITS` selects the quotient
/// row and `j % GADGET_DIGITS` selects its balanced digit.
pub fn rho_digit_as_rq(rho: &Vec<QuotientRow>, j: usize) -> Rq {
    let digits: usize = params::GADGET_DIGITS;
    let row: usize = j / digits;
    let u: usize = j % digits;
    rho_digits(&rho[row].0, u)
}

/// The vector bound by the lift commitment, `z` followed by all quotient
/// digits (spec: `liftMessage`, `RingSwitch/Reduction.lean:270`).
///
/// Mirrors `liftMessage`.
pub fn lift_message(w: &LiftedWitness) -> PolyVec {
    let z_len: usize = w.z.len();
    let rho_len: usize = w.rho.len() * params::GADGET_DIGITS;
    let mut out: Vec<Rq> = Vec::new();
    let mut i: usize = 0;
    while i < z_len {
        out.push(w.z.get(i).copy());
        i += 1;
    }
    let mut j: usize = 0;
    while j < rho_len {
        out.push(rho_digit_as_rq(&w.rho, j));
        j += 1;
    }
    PolyVec::new(out)
}

/// The concrete Ajtai lift commitment `D *ᵥ (z ‖ digits(ρ))` (spec:
/// `hachiLiftCom`, `RingSwitch/Reduction.lean:277`).
///
/// Mirrors `hachiLiftCom`.
///
/// `d_key` is the caller-supplied lift key, distinct from QuadEval's
/// `PublicParamsD::d_matrix` and expected to have `D_ROWS × LIFT_COLS` shape.
pub fn lift_commit(d_key: &PolyMatrix, w: &LiftedWitness) -> PolyVec {
    let message: PolyVec = lift_message(w);
    d_key.mat_vec_mul(&message)
}
