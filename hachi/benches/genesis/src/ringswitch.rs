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
use crate::linalg::{PolyMatrix, PolyVec};
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

// @genesis 240f277 2026-09-07 — ringswitch::QuotientRow
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
    // @genesis 240f277 2026-09-07 — ringswitch::QuotientRow::new
    /// Build a quotient row from little-endian coefficients, truncated and
    /// padded to the cyclotomic degree.
    pub fn new(coeffs: &Vec<Fp>) -> QuotientRow {
        QuotientRow(Rq::from_coeffs(coeffs))
    }

    // @genesis 240f277 2026-09-07 — ringswitch::QuotientRow::coeff
    /// Read coefficient `k` of the quotient polynomial.
    pub fn coeff(&self, k: usize) -> Fp {
        self.0.coeff(k)
    }

    // @genesis 240f277 2026-09-07 — ringswitch::QuotientRow::to_rq
    /// Read the quotient row back as a ring element (spec: `rhoAsRq`,
    /// `RingSwitch/Reduction.lean:249`).
    ///
    /// Mirrors `rhoAsRq`.
    pub fn to_rq(&self) -> Rq {
        self.0.copy()
    }
}

// @genesis 240f277 2026-09-07 — ringswitch::LiftedWitness
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
    // @genesis 240f277 2026-09-07 — ringswitch::LiftedWitness::new
    /// Bundle the `R^lin` witness and quotient rows.
    pub fn new(z: PolyVec, rho: Vec<QuotientRow>) -> LiftedWitness {
        LiftedWitness { z, rho }
    }

    // @genesis 240f277 2026-09-07 — ringswitch::LiftedWitness::z
    /// The `R^lin` witness block.
    pub fn z(&self) -> &PolyVec {
        &self.z
    }

    // @genesis 240f277 2026-09-07 — ringswitch::LiftedWitness::rho
    /// The quotient rows.
    pub fn rho(&self) -> &Vec<QuotientRow> {
        &self.rho
    }
}

// @genesis 240f277 2026-09-07 — ringswitch::rho_digit_as_rq
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

// @genesis 240f277 2026-09-07 — ringswitch::lift_message
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

// @genesis 240f277 2026-09-07 — ringswitch::lift_commit
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

// @genesis 1e57c54 2026-09-08 — ringswitch::rho_digits_at
/// The `u`-th balanced digit of quotient row `i` (spec: the
/// `rhoDigits Φ bDig (ρ i) u` of `rhoDigitsShortCheck`,
/// `EndPiece/Reduction.lean:111-113`).
///
/// Mirrors `rhoDigits` (at a row selected by index).
///
/// Addressing a digit by the pair `(i, u)` rather than by the flat index
/// [`rho_digit_as_rq`] takes is not a convenience: it is what the specification
/// does. `rhoDigitsShortCheck` quantifies `∀ i, ∀ u < δ, ∀ k < d` and applies
/// `rhoDigits` to `ρ i` directly -- there is no flat index anywhere in it. The
/// earlier translation of that check built `j = i · GADGET_DIGITS + u` and
/// handed it to [`rho_digit_as_rq`], which split it straight back into
/// `(j / δ, j % δ)`; the round trip was absent from the specification, and it
/// was the sole reason the extracted check could *fail* rather than return a
/// boolean (`i · 8` is a checked `usize` product and `i` is bounded only by the
/// vector's length). Forming no product at all is what makes
/// `rho_digits_short_check_spec` unconditional. See NOTES.md § "The flat index
/// the specification does not have".
///
/// [`rho_digit_as_rq`] keeps the flat form, because *its* specification
/// (`rhoDigitAsRq`) genuinely takes one.
pub fn rho_digits_at(rho: &Vec<QuotientRow>, i: usize, u: usize) -> Rq {
    rho_digits(&rho[i].0, u)
}

// @genesis 1e57c54 2026-09-08 — ringswitch::RlinStatement
/// Statement of Hachi's unstructured linear relation `R^lin` (spec:
/// `RlinStatement`, `RingSwitch/Rlin.lean:97`).
///
/// Mirrors `RlinStatement`.
///
/// All three fields are *public* data in the protocol's sense -- the matrix, the
/// right-hand side, and the `ℓ∞` bound the witness must meet -- which is what
/// makes the zero-check's `M̃_α` verifier-computable. `bound` is a `u64` for the
/// reason [`params::CHAIN_GAMMA`] is: the specification's `ℕ` is compared
/// against a centered coefficient magnitude, and every value in play is below
/// `q < 2^32`.
pub struct RlinStatement {
    m: PolyMatrix,
    yvec: PolyVec,
    bound: u64,
}

impl RlinStatement {
    // @genesis 1e57c54 2026-09-08 — ringswitch::RlinStatement::new
    /// Bundle the public matrix, right-hand side and norm bound.
    pub fn new(m: PolyMatrix, yvec: PolyVec, bound: u64) -> RlinStatement {
        RlinStatement { m, yvec, bound }
    }

    // @genesis 1e57c54 2026-09-08 — ringswitch::RlinStatement::m
    /// The public matrix `M ∈ Rq^{n×μ}`.
    pub fn m(&self) -> &PolyMatrix {
        &self.m
    }

    // @genesis 1e57c54 2026-09-08 — ringswitch::RlinStatement::yvec
    /// The public right-hand side `y ∈ Rq^n`.
    pub fn yvec(&self) -> &PolyVec {
        &self.yvec
    }

    // @genesis 1e57c54 2026-09-08 — ringswitch::RlinStatement::bound
    /// The public `ℓ∞`-norm bound on the witness.
    pub fn bound(&self) -> u64 {
        self.bound
    }
}

// @genesis 1e57c54 2026-09-08 — ringswitch::ext_pow
/// `x^i` in the extension field, by repeated multiplication.
///
/// The `x ^ i` of `CPolynomial.eval₂`'s fold
/// (`CompPoly/Univariate/Basic.lean:251`), recomputed per term exactly as the
/// fold writes it -- the same deliberate naivety as
/// [`crate::gadget::base_pow`], and for the same reason: the frozen baseline
/// must be the specification's shape, so that hoisting the power out of the
/// loop is a measurable optimization rather than something already spent.
fn ext_pow(x: cpoly::Ext4, i: usize) -> cpoly::Ext4 {
    let mut acc: cpoly::Ext4 = cpoly::Ext4::ONE;
    let mut t: usize = 0;
    while t < i {
        acc = acc * x;
        t += 1;
    }
    acc
}

// @genesis 1e57c54 2026-09-08 — ringswitch::c_eval_at
/// Evaluate a `Zq[X]` polynomial at a point of the extension field (spec:
/// `cEvalAt`, `RingSwitch/Reduction.lean:444`).
///
/// Mirrors `cEvalAt`.
///
/// `cEvalAt φF a p = p.eval₂ φF a`, and `eval₂` is the *sum* form --
/// `p.val.zipIdx.foldl (fun acc ⟨a, i⟩ => acc + f a * x ^ i) 0`
/// (`CompPoly/Univariate/Basic.lean:251`) -- not Horner's method, which CompPoly
/// offers separately as `eval₂Horner` and this definition does not use. So the
/// translation is the same sum, with the power recomputed per term.
///
/// This is the crate's first *mixed* evaluation: the coefficients are `Fp` and
/// the point is `cpoly::Ext4`, so each term is one `Fp`-to-`cpoly::Ext4` embedding, one
/// extension multiply and one extension add. cpoly's `UnivariatePoly::eval` is
/// not a drop-in -- its coefficients are `cpoly::Ext4` too, so using it would embed
/// the whole polynomial first and multiply in the wide field throughout.
pub fn c_eval_at(alpha: cpoly::Ext4, p: &Rq) -> cpoly::Ext4 {
    let degree: usize = params::RING_DEGREE;
    let mut acc: cpoly::Ext4 = cpoly::Ext4::ZERO;
    let mut k: usize = 0;
    while k < degree {
        acc = acc + cpoly::Ext4::from_base(p.coeff(k)) * ext_pow(alpha, k);
        k += 1;
    }
    acc
}

// @genesis 1e57c54 2026-09-08 — ringswitch::c_eval_at_modulus
/// Evaluate the cyclotomic modulus at a point of the extension field (spec:
/// `cEvalAt φF α Φ.φ`, the `φ(α)` factor of `mAlphaTilde`,
/// `ZeroCheck/Constraints.lean:519`).
///
/// Mirrors `cEvalAt` (at the modulus, which no [`Rq`] can hold).
///
/// `Φ.φ = X^d + 1` at a power-of-two cyclotomic index, so it has `d + 1`
/// coefficients and does not fit an [`Rq`], whose invariant is exactly `d` of
/// them -- hence a separate entry point rather than a call to [`c_eval_at`].
/// The body is `eval₂` over those `d + 1` coefficients, all zero but the first
/// and the last.
///
/// Deliberately naive, and expensively so: `α^d + 1` is ten squarings at
/// `d = 1024`, while this is the specification's `d + 1`-term sum with a
/// recomputed power per term. That gap is the point -- it is the largest single
/// optimization the α-side offers, and it must be *measurable*, so the baseline
/// pays it. See briefs/target-4-zero-check.md § Corrections item 3.
pub fn c_eval_at_modulus(alpha: cpoly::Ext4) -> cpoly::Ext4 {
    let degree: usize = params::RING_DEGREE;
    let mut acc: cpoly::Ext4 = cpoly::Ext4::ZERO;
    let mut k: usize = 0;
    while k <= degree {
        let coeff: Fp = if k == 0 || k == degree {
            Fp::ONE
        } else {
            Fp::ZERO
        };
        acc = acc + cpoly::Ext4::from_base(coeff) * ext_pow(alpha, k);
        k += 1;
    }
    acc
}

// ---------------------------------------------------------------------------
// The honest lift prover (spec: `RingSwitch/ComputableWitness.lean`)
// ---------------------------------------------------------------------------

// @genesis 594c984 2026-09-11 — ringswitch::long_mul
/// The unreduced product of two ring elements' canonical representatives: the
/// `2N - 1` coefficients of a polynomial in `Zq[X]` (spec: the `*` of
/// `CPolynomial (ZMod q)` inside `cRowSum`, `RingSwitch/Reduction.lean:441`).
///
/// Mirrors `CPolynomial.Raw.mul` on the canonical representatives.
///
/// This is [`Rq::mul`] **without** the negacyclic fold: `aᵢbⱼ` lands in slot
/// `i + j` and nowhere else. That is the whole difference between a product
/// in `Zq[X]` and one in `Rq`, and the reason `cRowSum` had no carrier in this
/// crate until now (NOTES.md § "Target 4 opens"): reducing here would erase
/// exactly the quotient the lift prover has to extract. Fixed width: the slot
/// count is `2N - 1 = 2047` whatever the true degree, so this is the `Raw`
/// array reading of the polynomial rather than the trimmed `CPolynomial`; the
/// two denote the same element of `Zq[X]`. `i + j ≤ 2N - 2` cannot overflow.
///
/// Private: a helper of [`c_row_sum`] alone, measured through it.
fn long_mul(a: &Rq, b: &Rq) -> Vec<Fp> {
    let n: usize = params::RING_DEGREE;
    let width: usize = 2 * n - 1;
    let mut out: Vec<Fp> = Vec::new();
    let mut k: usize = 0;
    while k < width {
        out.push(Fp::ZERO);
        k += 1;
    }
    let mut i: usize = 0;
    while i < n {
        let ai: Fp = a.coeff(i);
        let mut j: usize = 0;
        while j < n {
            let term: Fp = ai * b.coeff(j);
            let s: usize = i + j;
            out[s] = out[s] + term;
            j += 1;
        }
        i += 1;
    }
    out
}

// @genesis 594c984 2026-09-11 — ringswitch::c_row_sum
/// The `i`-th lifted row `Σⱼ Mᵢⱼ·zⱼ`, unreduced, as a polynomial in `Zq[X]`
/// with `2N - 1` coefficients (spec: `cRowSum`, `RingSwitch/Reduction.lean:439`).
///
/// Mirrors `cRowSum`.
///
/// The specification sums the `CPolynomial` products of the canonical
/// representatives; here each product is [`long_mul`] and the sum is
/// coefficientwise over the fixed width. `i < rows` and `z.len() = cols` are
/// the two fail points -- `row(i)`, `z.get(j)` -- and travel as `_spec`
/// hypotheses; the matrix's `Fin n → Fin μ → Rq Φ` type is what erases to them.
pub fn c_row_sum(s: &RlinStatement, z: &PolyVec, i: usize) -> Vec<Fp> {
    let n: usize = params::RING_DEGREE;
    let width: usize = 2 * n - 1;
    let cols: usize = s.m().cols();
    let row: &PolyVec = s.m().row(i);
    let mut acc: Vec<Fp> = Vec::new();
    let mut k: usize = 0;
    while k < width {
        acc.push(Fp::ZERO);
        k += 1;
    }
    let mut j: usize = 0;
    while j < cols {
        let prod: Vec<Fp> = long_mul(row.get(j), z.get(j));
        let mut t: usize = 0;
        while t < width {
            acc[t] = acc[t] + prod[t];
            t += 1;
        }
        j += 1;
    }
    acc
}

// @genesis 594c984 2026-09-11 — ringswitch::div_by_modulus
/// The quotient of a `Zq[X]` polynomial with `2N - 1` coefficients by the monic
/// modulus `X^N + 1` (spec: `CPolynomial.divByMonic` at `Φ.φ`,
/// `CompPoly/Univariate/Basic.lean:841`, the division `cQuotient` performs).
///
/// Mirrors `CPolynomial.divByMonic` at `Φ.φ`.
///
/// The specification's `divModByMonicAux.go` (`Univariate/Raw/Division.lean:31`)
/// peels one leading term per step: with `lc` the leading coefficient and `k`
/// the degree gap, it subtracts `lc · X^k · (X^N + 1)` from the dividend, adds
/// `lc · X^k` to the quotient, and trims. On the fixed-width carrier the
/// leading slot is `k + N` for `k` counting down from `N - 2`, and a slot that
/// holds zero is a step the specification skips by trimming -- subtracting
/// `0 · X^k · (X^N + 1)` -- so walking every slot is the same computation with
/// no-op steps made explicit. Each step reads `p[k + N]`, writes it into
/// `q[k]`, and subtracts it from `p[k]`: that subtraction is `X^N ≡ -1`, the
/// sign [`Rq::mul`] folds in and this function keeps separate. The quotient
/// has degree at most `N - 2`, so it fits a [`QuotientRow`] with its top
/// coefficient zero -- inside `LiftedWitness.hρ`'s bound `d - 1`.
///
/// `p.len() = 2N - 1` is the fail point `p[k + N]` and travels as a `_spec`
/// hypothesis. Private: a helper of [`c_quotient`] alone, measured through it.
fn div_by_modulus(p: &Vec<Fp>) -> Vec<Fp> {
    let n: usize = params::RING_DEGREE;
    let mut rem: Vec<Fp> = Vec::new();
    let mut t: usize = 0;
    while t < p.len() {
        rem.push(p[t]);
        t += 1;
    }
    let mut quot: Vec<Fp> = Vec::new();
    let mut u: usize = 0;
    while u < n {
        quot.push(Fp::ZERO);
        u += 1;
    }
    let mut k: usize = n - 1;
    while k > 0 {
        k -= 1;
        let lead: usize = k + n;
        let c: Fp = rem[lead];
        quot[k] = c;
        rem[k] = rem[k] - c;
        rem[lead] = Fp::ZERO;
    }
    quot
}

// @genesis 594c984 2026-09-11 — ringswitch::c_quotient
/// The computable honest quotient of row `i`: the lifted row defect
/// `Σⱼ Mᵢⱼ·zⱼ − yᵢ` divided by the modulus (spec: `cQuotient`,
/// `RingSwitch/ComputableWitness.lean:65`).
///
/// Mirrors `cQuotient`.
///
/// `yᵢ` enters through its canonical representative -- the specification's
/// `(s.yvec i).1` -- which has fewer than `N` coefficients, so the subtraction
/// touches the low `N` slots only. The row and column bounds are
/// [`c_row_sum`]'s; `i < yvec.len()` is the one this function adds.
pub fn c_quotient(s: &RlinStatement, z: &PolyVec, i: usize) -> QuotientRow {
    let n: usize = params::RING_DEGREE;
    let mut defect: Vec<Fp> = c_row_sum(s, z, i);
    let y: &Rq = s.yvec().get(i);
    let mut k: usize = 0;
    while k < n {
        defect[k] = defect[k] - y.coeff(k);
        k += 1;
    }
    let quot: Vec<Fp> = div_by_modulus(&defect);
    QuotientRow::new(&quot)
}

// @genesis 594c984 2026-09-11 — ringswitch::honest_lift_witness
/// The computable honest lifted witness: `z` itself and one quotient row per
/// output row (spec: `honestLiftWitnessC`, `RingSwitch/ComputableWitness.lean:89`).
///
/// Mirrors `honestLiftWitnessC`.
///
/// This is the lift prover the chain lacked: [`crate::chain::chain_open`] takes
/// the lifted witness as an input because this item did not exist (NOTES.md
/// § "The composed verifier was not a verifier"). The specification's `hd`
/// (`0 < Φ.φ.natDegree`) and `hρ` (the degree bound) are `Prop`s and erase;
/// `hd` holds at `N = 1024`, and the degree bound is what
/// [`div_by_modulus`]'s zero top coefficient delivers. `z` is copied because
/// the witness owns its block and `clone` has no model.
pub fn honest_lift_witness(s: &RlinStatement, z: &PolyVec) -> LiftedWitness {
    let rows: usize = s.m().rows();
    let mut rho: Vec<QuotientRow> = Vec::new();
    let mut i: usize = 0;
    while i < rows {
        rho.push(c_quotient(s, z, i));
        i += 1;
    }
    LiftedWitness::new(z.copy(), rho)
}
