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

// ---------------------------------------------------------------------------
// Stage 6, iteration 2 -- the fused lift commitment's row helper (candidate E).
// Frozen as a first translation the day the champion landed (2026-09-14).
// ---------------------------------------------------------------------------

// @genesis b6f0d69 2026-09-14 — ringswitch::lift_commit_row
/// One row of the lift commitment, accumulated in place over the two halves of
/// the specification's concatenation: `∑_{j<μ} D[i][j]·z[j]` then
/// `∑_{j<n·δ} D[i][μ+j]·digit(ρ, j)` (opt: `HachiEquiv.Opt.liftCommitRow`,
/// `lean/Opt.lean`; the two loops are `lift_commit.rowZLoop` and
/// `lift_commit.rowDigLoop` there).
///
/// This is the fusion of [`lift_message`] into [`lift_commit`]: the message
/// vector `z ‖ digits(ρ)` -- 57 384 ring elements, 448 MiB at the pin -- is
/// never materialized, each digit polynomial is built once per output row for
/// the column that reads it, and the operation count is exactly `mat_vec_mul`'s
/// (`μ + n·δ` products and adds per row). The digit polynomials are rebuilt per
/// output row, which is no change at the pin's `dRows = 1` and a `dRows`-fold
/// recomputation above it. No `Mirrors` line: the row is this crate's own
/// optimized variant, not an ArkLib definition.
fn lift_commit_row(d_key: &PolyMatrix, w: &LiftedWitness, i: usize) -> Rq {
    let row: &PolyVec = d_key.row(i);
    let z_len: usize = w.z().len();
    let rho_len: usize = w.rho().len() * params::GADGET_DIGITS;
    let mut acc: Rq = Rq::zero();
    let mut j: usize = 0;
    while j < z_len {
        let term: Rq = row.get(j).mul(w.z().get(j));
        acc = acc.add(&term);
        j += 1;
    }
    let mut k: usize = 0;
    while k < rho_len {
        let digit: Rq = rho_digit_as_rq(w.rho(), k);
        let term: Rq = row.get(z_len + k).mul(&digit);
        acc = acc.add(&term);
        k += 1;
    }
    acc
}

// @genesis f1ee0a1 2026-09-19 — ringswitch::long_mul_high
/// The **high half** of [`long_mul`]: coefficients `N … 2N − 2` of `a · b`,
/// which are the only ones [`div_by_modulus`] reads (Stage 6 candidate T1a).
///
/// [`long_mul`]'s body with the output loop started at `N` instead of `0`. The
/// antidiagonal `i + j = k` for `k ≥ N` is clipped on both sides — `i` runs
/// from `k + 1 − N` to `N` — so the term count is `N(N−1)/2`, exactly half of
/// the full product's `N²`, and the accumulator is the same `u128` register
/// with one reduction per output coefficient.
///
/// `N − 1` coefficients, in increasing degree: `out[t]` is coefficient
/// `N + t`.
fn long_mul_high(a: &Rq, b: &Rq) -> Vec<Fp> {
    let n: usize = params::RING_DEGREE;
    let width: usize = 2 * n - 1;
    let q: u128 = params::Q as u128;
    let mut out: Vec<Fp> = Vec::with_capacity(n);
    let mut k: usize = n;
    while k < width {
        let lo: usize = k + 1 - n;
        let mut acc: u128 = 0;
        let mut i: usize = lo;
        while i < n {
            let ai: u128 = a.coeff(i).to_u64() as u128;
            let bj: u128 = b.coeff(k - i).to_u64() as u128;
            acc = acc + ai * bj;
            i += 1;
        }
        out.push(Fp::new((acc % q) as u64));
        k += 1;
    }
    out
}

// @genesis f1ee0a1 2026-09-19 — ringswitch::c_row_sum_high
/// The high half of [`c_row_sum`]: coefficients `N … 2N − 2` of `Σⱼ Mᵢⱼ·zⱼ`
/// (Stage 6 candidate T1a).
///
/// [`c_row_sum`]'s shape with [`long_mul_high`] in place of [`long_mul`] and
/// an `N − 1`-wide accumulator in place of the `2N − 1`-wide one. The zero
/// test is candidate T1a1's and is kept for the same reason.
///
/// Private: a helper of [`c_quotient`] alone, measured through it, exactly as
/// [`div_by_modulus`] is.
fn c_row_sum_high(s: &RlinStatement, z: &PolyVec, i: usize) -> Vec<Fp> {
    let n: usize = params::RING_DEGREE;
    let cols: usize = s.m().cols();
    let row: &PolyVec = s.m().row(i);
    let mut acc: Vec<Fp> = Vec::new();
    let mut k: usize = 0;
    while k < n - 1 {
        acc.push(Fp::ZERO);
        k += 1;
    }
    let mut j: usize = 0;
    while j < cols {
        let mij: &Rq = row.get(j);
        if !mij.is_zero() {
            let prod: Vec<Fp> = long_mul_high(mij, z.get(j));
            let mut t: usize = 0;
            while t < n - 1 {
                acc[t] = acc[t] + prod[t];
                t += 1;
            }
        }
        j += 1;
    }
    acc
}

// @genesis 4a0a1c3 2026-09-21 — ringswitch::RlinBlocks
// Card W2 (2026-09-21): the `R^lin` matrix stopped being assembled. The five
// items below are first translations and are frozen here in the shape they
// landed in; the dense arm is what every earlier item was written against, so
// the baseline they are measured from is the assembled matrix's.
/// The blocks the `R^lin` matrix is assembled *from*, kept instead of the
/// assembly (wall W2).
///
/// `M` is `5 × 57 344` at the pin, which is 2.19 GiB -- and 1.25 GiB of that
/// is explicit `Rq::zero()`, because the matrix is block structured and only
/// `c4` and `c5` carry two blocks each. `ringswitch::c_row_sum` has skipped
/// those zeros since candidate T1a1; this keeps them from being built at all.
///
/// The two negated blocks are stored already negated, so that every entry can
/// be handed back as a borrow into a block and nothing is constructed per
/// call -- including the zero, of which there is exactly one.
pub struct RlinBlocks {
    d: PolyMatrix,
    bmat: PolyMatrix,
    g_b: PolyVec,
    g_c: PolyVec,
    neg_jt_g_a: PolyVec,
    tensor: PolyMatrix,
    neg_aj: PolyMatrix,
    cw: usize,
    ct: usize,
    cz: usize,
    d_rows: usize,
    b_rows: usize,
    t_rows: usize,
    zero: Rq,
}

impl RlinBlocks {
    // @genesis 4a0a1c3 2026-09-21 — ringswitch::RlinBlocks::new
    /// Bundle the blocks. The two negated ones arrive negated.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        d: PolyMatrix,
        bmat: PolyMatrix,
        g_b: PolyVec,
        g_c: PolyVec,
        neg_jt_g_a: PolyVec,
        tensor: PolyMatrix,
        neg_aj: PolyMatrix,
        cw: usize,
        ct: usize,
        cz: usize,
    ) -> RlinBlocks {
        let d_rows: usize = d.rows();
        let b_rows: usize = bmat.rows();
        let t_rows: usize = tensor.rows();
        RlinBlocks {
            d, bmat, g_b, g_c, neg_jt_g_a, tensor, neg_aj,
            cw, ct, cz, d_rows, b_rows, t_rows, zero: Rq::zero(),
        }
    }
}

// @genesis 4a0a1c3 2026-09-21 — ringswitch::RlinMat
/// The public matrix, either assembled or as the blocks it would be assembled
/// from.
///
/// `match` on a custom enum was on the extraction's unprobed list until
/// 2026-09-21; it extracts to a Lean `inductive` and a native `match`, with a
/// shared borrow out of a variant coming back as the value itself.
pub enum RlinMat {
    /// The matrix as assembled, entry by entry.
    Dense(PolyMatrix),
    /// The blocks it would have been assembled from.
    Lazy(RlinBlocks),
}

impl RlinMat {
    // @genesis 4a0a1c3 2026-09-21 — ringswitch::RlinMat::rows
    /// How many rows the matrix has.
    pub fn rows(&self) -> usize {
        match self {
            RlinMat::Dense(m) => m.rows(),
            RlinMat::Lazy(b) => b.d_rows + b.b_rows + 2 + b.t_rows,
        }
    }

    // @genesis 4a0a1c3 2026-09-21 — ringswitch::RlinMat::cols
    /// How many columns the matrix has.
    pub fn cols(&self) -> usize {
        match self {
            RlinMat::Dense(m) => m.cols(),
            RlinMat::Lazy(b) => b.cw + b.ct + b.cz,
        }
    }

    // @genesis 4a0a1c3 2026-09-21 — ringswitch::RlinMat::entry
    /// `M[i][j]`, as a borrow: the dense arm reads it, the lazy arm decides
    /// which block it falls in. Every arm returns a reference into something
    /// already held, so nothing is allocated per entry.
    pub fn entry(&self, i: usize, j: usize) -> &Rq {
        match self {
            RlinMat::Dense(m) => m.row(i).get(j),
            RlinMat::Lazy(b) => {
                if i < b.d_rows {
                    // c1: [ D | 0 | 0 ]
                    if j < b.cw { b.d.row(i).get(j) } else { &b.zero }
                } else if i < b.d_rows + b.b_rows {
                    // c2: [ 0 | B | 0 ]
                    let i2: usize = i - b.d_rows;
                    if j < b.cw {
                        &b.zero
                    } else if j < b.cw + b.ct {
                        b.bmat.row(i2).get(j - b.cw)
                    } else {
                        &b.zero
                    }
                } else if i == b.d_rows + b.b_rows {
                    // c3: [ Gᵀb | 0 | 0 ]
                    if j < b.cw { b.g_b.get(j) } else { &b.zero }
                } else if i == b.d_rows + b.b_rows + 1 {
                    // c4: [ Gᵀc | 0 | −Jᵀ(Gᵀa) ]
                    if j < b.cw {
                        b.g_c.get(j)
                    } else if j < b.cw + b.ct {
                        &b.zero
                    } else {
                        b.neg_jt_g_a.get(j - b.cw - b.ct)
                    }
                } else {
                    // c5: [ 0 | cᵀ ⊗ G | −(AJ) ]
                    let p: usize = i - b.d_rows - b.b_rows - 2;
                    if j < b.cw {
                        &b.zero
                    } else if j < b.cw + b.ct {
                        b.tensor.row(p).get(j - b.cw)
                    } else {
                        b.neg_aj.row(p).get(j - b.cw - b.ct)
                    }
                }
            }
        }
    }
}

// Frozen, but never compiled. `new_lazy` constructs `RlinMat::Lazy`, and the
// frozen `RlinStatement` above it -- stamped 1e57c54, 2026-09-08 -- declares
// `m: PolyMatrix`, a type that predates the enum. Contract point 4 (genesis
// composes with genesis) cannot be met for this item: the only frozen
// `RlinStatement` it could build is one whose field it does not fit, and
// contract point 1 forbids editing that struct to make it fit. So the text is
// frozen for provenance and `#[cfg(any())]` keeps it out of the build.
//
// Nothing measurable is lost. `new_lazy` is straight-line -- one enum wrap and
// a struct literal, no loop, no allocation -- so it sits below the bar in
// `benches/exclusions.toml`: a criterion row over it would time the
// `black_box` around it. There is no genesis time here to be compared against
// because there is no time to take. What the freeze preserves is the record
// `check-genesis` verifies against git -- a sha, a date, and text that matches
// `hachi/src` at that commit -- so that `hachi/src` still cannot grow an item
// nobody froze.
//
// The `#[cfg(any())]` belongs on this `impl` and NOT on the `fn`:
// `harness.py::_frozen_text` holds an item's attributes against git along with
// its body, so an attribute on the signature that `hachi/src` does not carry
// would fail the very check this freeze exists to satisfy.
//
// The precedent is narrow: a frozen item may go uncompiled only when a frozen
// type below it cannot express it, and only where an enclosing `impl` can
// carry the `cfg` -- `rustitems.scan` does not descend into `mod`, so a free
// function in this position has no frozen form at all and is the repo owner's
// call, not this rule's.
#[cfg(any())]
impl RlinStatement {
    // @genesis 4a0a1c3 2026-09-21 — ringswitch::RlinStatement::new_lazy
    /// Bundle the blocks instead of the assembly (wall W2).
    pub fn new_lazy(b: RlinBlocks, yvec: PolyVec, bound: u64) -> RlinStatement {
        RlinStatement { m: RlinMat::Lazy(b), yvec, bound }
    }
}


// @genesis 2db0eae 2026-09-22 — ringswitch::lift_witness_short
// Card T40 (2026-09-22): the lift commitment on the signed bounded
// Goldilocks lane, and the guard that selects it.
/// Is every coefficient of `z ‖ digits(ρ)` centred below `CHAIN_GAMMA`?
///
/// The guard on card T40's fast path, and **not** a new precondition on
/// [`lift_commit`]: when it fails the generic path runs and the answer is the
/// same, so `lift_commit_spec` keeps its statement. It is the predicate
/// `endpiece::lift_short_check` applies, written here because `endpiece`
/// depends on this module and not the other way round.
///
/// One pass over `μ + n·δ` ring elements against the row's `57 384`
/// multiplications, so its cost does not show.
pub fn lift_witness_short(w: &LiftedWitness) -> bool {
    let gamma: u64 = params::CHAIN_GAMMA;
    let z_len: usize = w.z().len();
    let rho_len: usize = w.rho().len() * params::GADGET_DIGITS;
    let deg: usize = params::RING_DEGREE;
    let mut short: bool = true;
    let mut j: usize = 0;
    while j < z_len {
        let e: &Rq = w.z().get(j);
        let mut k: usize = 0;
        while k < deg {
            if crate::commit::centered_abs(e.coeff(k)) > gamma {
                short = false;
            }
            k += 1;
        }
        j += 1;
    }
    let mut u: usize = 0;
    while u < rho_len {
        let d: Rq = rho_digit_as_rq(w.rho(), u);
        let mut k: usize = 0;
        while k < deg {
            if crate::commit::centered_abs(d.coeff(k)) > gamma {
                short = false;
            }
            k += 1;
        }
        u += 1;
    }
    short
}

// @genesis 2db0eae 2026-09-22 — ringswitch::lift_commit_row_gold
/// One row of the lift commitment on the **signed bounded Goldilocks lane**
/// (card T40).
///
/// The value [`lift_commit_row`] computes, by the route the digit path takes.
/// Where that one calls a generic [`Rq::mul`] per term -- three auxiliary
/// primes, two forward transforms and an inverse in each, then a Garner
/// reconstruction per coefficient, so nine transforms and `N` Garners for
/// every one of `57 384` terms -- this transforms the key entry and the
/// witness entry once each on **one** lane, multiply-accumulates in transform
/// space, and takes a single inverse for the whole row.
///
/// Two things make one lane enough. The witness is centred below
/// `CHAIN_GAMMA = 15`, so a term's convolution is bounded by `N · q · 15` and
/// the row's by `57 384 · N · q · 15 = 2^61.72`, inside `GOLD_P / 2`; and
/// [`crate::ntt::GOLD_SOFF`] is a multiple of `q`, so adding it per term
/// makes the accumulated value non-negative and then vanishes in the
/// reduction. No chunk loop: the whole row is one chunk, margin x2.44.
///
/// **Not a prepared path, deliberately.** `D_ROWS = 1`, so every key entry is
/// read exactly once per commitment and a prepared store would be 470 MiB
/// written to be used once. The key is transformed in the stream beside the
/// witness; both buffers and both scratches are recycled across terms in card
/// T34's discipline, so the loop allocates nothing per term.
///
/// The concatenation `z ‖ digits(ρ)` is still never built -- candidate E's
/// removal of wall W3 stands. The two segments are walked in turn into one
/// accumulator, which is sound because the transform is linear and the bound
/// above covers both segments at once.
fn lift_commit_row_gold(d_key: &PolyMatrix, w: &LiftedWitness, i: usize) -> Rq {
    let row: &PolyVec = d_key.row(i);
    let n: usize = crate::ntt::NTT_LEN;
    let deg: usize = params::RING_DEGREE;
    let qw: u64 = params::Q;
    let z_len: usize = w.z().len();
    let rho_len: usize = w.rho().len() * params::GADGET_DIGITS;
    let pt: Vec<u64> = crate::ntt::gold_psi_table(crate::ntt::GOLD_PSI);
    let it: Vec<u64> = crate::ntt::gold_psi_table(crate::ntt::GOLD_PSIINV);
    let mut acc: Vec<u64> = crate::ntt::zeros(n);
    let mut kbuf: Vec<u64> = crate::ntt::zeros(n);
    let mut ksc: Vec<u64> = crate::ntt::zeros(n);
    let mut wbuf: Vec<u64> = crate::ntt::zeros(n);
    let mut wsc: Vec<u64> = crate::ntt::zeros(n);
    let mut j: usize = 0;
    while j < z_len {
        kbuf = crate::ring::load_twisted_into(kbuf, row.get(j), &pt);
        let fk: (Vec<u64>, Vec<u64>) = crate::ntt::gold_forward(kbuf, ksc, &pt);
        wbuf = crate::ring::load_twisted_signed_into(wbuf, w.z().get(j), &pt);
        let fw: (Vec<u64>, Vec<u64>) = crate::ntt::gold_forward(wbuf, wsc, &pt);
        acc = crate::ring::mac_into_gold_off(acc, &fk.0, 0, &fw.0, n);
        kbuf = fk.0;
        ksc = fk.1;
        wbuf = fw.0;
        wsc = fw.1;
        j += 1;
    }
    let mut k: usize = 0;
    while k < rho_len {
        let digit: Rq = rho_digit_as_rq(w.rho(), k);
        kbuf = crate::ring::load_twisted_into(kbuf, row.get(z_len + k), &pt);
        let fk: (Vec<u64>, Vec<u64>) = crate::ntt::gold_forward(kbuf, ksc, &pt);
        wbuf = crate::ring::load_twisted_signed_into(wbuf, &digit, &pt);
        let fw: (Vec<u64>, Vec<u64>) = crate::ntt::gold_forward(wbuf, wsc, &pt);
        acc = crate::ring::mac_into_gold_off(acc, &fk.0, 0, &fw.0, n);
        kbuf = fk.0;
        ksc = fk.1;
        wbuf = fw.0;
        wsc = fw.1;
        k += 1;
    }
    // one offset per term, exactly as the digit path scales `GOLD_DOFF`
    let terms: u64 = (z_len + rho_len) as u64;
    let scaled: u64 = crate::ntt::gold_mul(crate::ntt::GOLD_SOFF, terms);
    let inv: (Vec<u64>, Vec<u64>) = crate::ntt::gold_inverse(acc, ksc, &it);
    let words: Vec<u64> = crate::ntt::gold_untwist_off(&inv.0, &it, scaled);
    let mut out: Vec<Fp> = Vec::with_capacity(deg);
    let mut t: usize = 0;
    while t < deg {
        out.push(Fp::new(words[t] % qw));
        t += 1;
    }
    // `Rq`'s field is private outside `ring`, and `from_coeffs` is total:
    // `out` is already `RING_DEGREE` long, so it neither pads nor truncates.
    Rq::from_coeffs(&out)
}



// @genesis 107f555 2026-09-22 — ringswitch::LIFT_GOLD_MAX
// Card T40a (2026-09-22): the width guard the proof forced.
/// The widest row the signed Goldilocks lane is exact for.
///
/// The lane accumulates the whole row in one chunk, so it is correct only
/// while twice the row's ceiling stays below `GOLD_P`:
/// `2 · T · N · q · CHAIN_GAMMA < GOLD_P` gives `T ≤ 139_810`. This is the
/// nearest power of two below that, `2^17`, which is **2.28×** the pin's
/// `LIFT_COLS = 57_384`.
///
/// It is checked at run time rather than assumed, because
/// [`lift_commit`]'s specification is generic in the witness width and its
/// only size constraint is `Usize::MAX`. Without this the fast path would
/// silently wrap for a witness wider than `139_810` -- a defect the proof
/// found and no test could, since it needs a witness 2400× the pin's width.
pub const LIFT_GOLD_MAX: usize = 131_072;
