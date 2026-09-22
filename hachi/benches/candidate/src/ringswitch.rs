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
    let mut coeffs: Vec<Fp> = Vec::with_capacity(degree);
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
///
/// Pre-sized to `μ + n·δ` (Stage 6 candidate D2; see [`crate::ring::Rq::copy`]:
/// the capacity is erased by the extraction and spares only the reallocation
/// growth of a 448 MiB vector at the pin). Since candidate E the commitment no
/// longer reads this vector; it stays as the specification's own object.
pub fn lift_message(w: &LiftedWitness) -> PolyVec {
    let z_len: usize = w.z.len();
    let rho_len: usize = w.rho.len() * params::GADGET_DIGITS;
    let total: usize = z_len + rho_len;
    let mut out: Vec<Rq> = Vec::with_capacity(total);
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

/// The concrete Ajtai lift commitment `D *ᵥ (z ‖ digits(ρ))` (spec:
/// `hachiLiftCom`, `RingSwitch/Reduction.lean:277`; opt:
/// `HachiEquiv.Opt.lift_commit.opt`, `lean/Opt.lean`).
///
/// Mirrors `hachiLiftCom`.
///
/// `d_key` is the caller-supplied lift key, distinct from QuadEval's
/// `PublicParamsD::d_matrix` and expected to have `D_ROWS × LIFT_COLS` shape.
/// Each output row is [`lift_commit_row`], so the specification's `liftMessage`
/// concatenation is never built (Stage 6 iteration 2, candidate E -- a removal
/// of the plan's memory wall W3, ≈ 1.3 GiB → ≈ 896 MiB peak at the pin, not a
/// speedup; `lift_commit.opt_eq_spec` says the result is `hachiLiftCom`'s, so
/// the `Mirrors` line above is still the truth). [`lift_message`] stays as the
/// specification's own vector for the callers that want it materialized.
pub fn lift_commit(d_key: &PolyMatrix, w: &LiftedWitness) -> PolyVec {
    let rows: usize = d_key.rows();
    let mut out: Vec<Rq> = Vec::with_capacity(rows);
    let mut i: usize = 0;
    while i < rows {
        let r: Rq = lift_commit_row(d_key, w, i);
        out.push(r);
        i += 1;
    }
    PolyVec::new(out)
}

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
    /// How many rows the matrix has.
    pub fn rows(&self) -> usize {
        match self {
            RlinMat::Dense(m) => m.rows(),
            RlinMat::Lazy(b) => b.d_rows + b.b_rows + 2 + b.t_rows,
        }
    }

    /// How many columns the matrix has.
    pub fn cols(&self) -> usize {
        match self {
            RlinMat::Dense(m) => m.cols(),
            RlinMat::Lazy(b) => b.cw + b.ct + b.cz,
        }
    }

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
///
/// Since wall W2 the matrix is an [`RlinMat`] rather than a [`PolyMatrix`]: the
/// statement is the same public data either way, and which representation it
/// holds is invisible above [`RlinMat::entry`].
pub struct RlinStatement {
    m: RlinMat,
    yvec: PolyVec,
    bound: u64,
}

impl RlinStatement {
    /// Bundle an assembled matrix, right-hand side and norm bound.
    pub fn new(m: PolyMatrix, yvec: PolyVec, bound: u64) -> RlinStatement {
        RlinStatement { m: RlinMat::Dense(m), yvec, bound }
    }

    /// Bundle the blocks instead of the assembly (wall W2).
    pub fn new_lazy(b: RlinBlocks, yvec: PolyVec, bound: u64) -> RlinStatement {
        RlinStatement { m: RlinMat::Lazy(b), yvec, bound }
    }

    /// The public matrix `M ∈ Rq^{n×μ}`, assembled or lazy.
    pub fn m(&self) -> &RlinMat {
        &self.m
    }

    /// The public right-hand side `y ∈ Rq^n`.
    pub fn yvec(&self) -> &PolyVec {
        &self.yvec
    }

    /// The public `ℓ∞`-norm bound on the witness.
    pub fn bound(&self) -> u64 {
        self.bound
    }
}

/// Evaluate a `Zq[X]` polynomial at a point of the extension field (spec:
/// `cEvalAt`, `RingSwitch/Reduction.lean:444`; opt:
/// `HachiEquiv.Opt.c_eval_at.opt`, `lean/Opt.lean`).
///
/// Mirrors `cEvalAt`.
///
/// `cEvalAt φF a p = p.eval₂ φF a`, and `eval₂` is the *sum* form
/// `∑_k φF (p.coeff k) · a^k` (`CompPoly/Univariate/Basic.lean:251`). The
/// body is that sum with the power threaded through the loop state -- `pw` is
/// `a^k` at the top of iteration `k` -- instead of recomputed per term, which
/// is `2·d` extension multiplications where the frozen baseline paid
/// `d·(d−1)/2`. The two agree by `c_eval_at.opt_eq_spec` (`lean/Opt.lean`),
/// proved against `cEvalAt` itself, so the `Mirrors` line above is still the
/// truth: the algorithm changed in Lean first, and this is its translation.
///
/// This is the crate's first *mixed* evaluation: the coefficients are `Fp` and
/// the point is `cpoly::Ext4`, so each term is one `Fp`-to-`cpoly::Ext4` embedding, one
/// extension multiply and one extension add, plus the one multiply that
/// advances the power. cpoly's `UnivariatePoly::eval` is not a drop-in -- its
/// coefficients are `cpoly::Ext4` too, so using it would embed the whole
/// polynomial first and multiply in the wide field throughout.
pub fn c_eval_at(alpha: cpoly::Ext4, p: &Rq) -> cpoly::Ext4 {
    let degree: usize = params::RING_DEGREE;
    let mut acc: cpoly::Ext4 = cpoly::Ext4::ZERO;
    let mut pw: cpoly::Ext4 = cpoly::Ext4::ONE;
    let mut k: usize = 0;
    while k < degree {
        acc = acc + cpoly::Ext4::from_base(p.coeff(k)) * pw;
        pw = pw * alpha;
        k += 1;
    }
    acc
}

/// Evaluate the cyclotomic modulus at a point of the extension field (spec:
/// `cEvalAt φF α Φ.φ`, the `φ(α)` factor of `mAlphaTilde`,
/// `ZeroCheck/Constraints.lean:519`; opt: `HachiEquiv.Opt.c_eval_at_modulus.opt`,
/// `lean/Opt.lean`).
///
/// Mirrors `cEvalAt` (at the modulus, which no [`Rq`] can hold).
///
/// `Φ.φ = X^d + 1` at a power-of-two cyclotomic index, so it has `d + 1`
/// coefficients and does not fit an [`Rq`], whose invariant is exactly `d` of
/// them -- hence a separate entry point rather than a call to [`c_eval_at`].
/// Its `eval₂` sum has exactly two non-zero terms, `1` and `α^d`, so the body
/// uses `RING_LOG_DEGREE` squarings and one addition;
/// `c_eval_at_modulus.opt_eq_spec` (`lean/Opt.lean`) proves it equal to the
/// specification's `d + 1`-term sum, which the frozen baseline computed
/// literally, with a recomputed power per term. At the checked `d = 2^10`
/// profile, ten squarings replace 1024 multiplications. The extracted loop
/// is proved directly by `ZeroCheck.c_eval_at_modulus_spec`.
pub fn c_eval_at_modulus(alpha: cpoly::Ext4) -> cpoly::Ext4 {
    let log_degree: usize = params::RING_LOG_DEGREE;
    let mut pw: cpoly::Ext4 = alpha;
    let mut k: usize = 0;
    while k < log_degree {
        pw = pw * pw;
        k += 1;
    }
    pw + cpoly::Ext4::ONE
}

// ---------------------------------------------------------------------------
// The honest lift prover (spec: `RingSwitch/ComputableWitness.lean`)
// ---------------------------------------------------------------------------

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
/// two denote the same element of `Zq[X]`.
///
/// Delayed reduction (Stage 6 candidate R), for the reason [`Rq::mul`]'s
/// candidate Q gives: every `Fp` operation reduces, so the frozen translation
/// paid a `% q` on each of the `N²` products and again on each accumulation.
/// This walks the output slot, sums its antidiagonal in `u128` unreduced, and
/// reduces once per slot -- `N²` reductions become `2N - 1`. The inner step
/// count is unchanged at `N²`; the measured 1.75× is the reduction, plus an
/// accumulator that stays in a register instead of round-tripping through
/// `out[i + j]`. Note "unreduced"
/// in this function's name has always meant *not folded by `X^N = -1`*, and
/// still does; what candidate R delays is the reduction modulo `q`, and the
/// output words are canonical representatives exactly as before.
///
/// What promoted it is the measured chain profile rather than a brief:
/// `honest_lift_witness` was 345 s of a 1 250 s run, 28% of the total and the
/// largest thing candidate Q did *not* touch, because this is a separate
/// function from the ring product (NOTES.md § "The chain, measured again").
///
/// Simpler than `Rq::mul`'s version in the one way that matters for the proof:
/// there is no negacyclic fold, so there is one accumulator and no sign split.
/// The bound is the same, `1024 · (q−1)² < 2^74` against `u128`, and equally
/// load-bearing -- one term already fills a `u64`. `k + 1` cannot overflow:
/// `k < 2N - 1 = 2047`.
///
/// Private: a helper of [`c_row_sum`] alone, measured through it.
// The narrowing cast is exact: `acc % q` is below `q < 2^32`. `Rq::mul` carries
// the same allow for the same reason.
#[allow(clippy::cast_possible_truncation)]
fn long_mul(a: &Rq, b: &Rq) -> Vec<Fp> {
    let n: usize = params::RING_DEGREE;
    let width: usize = 2 * n - 1;
    let q: u128 = params::Q as u128;
    let mut out: Vec<Fp> = Vec::with_capacity(width);
    let mut k: usize = 0;
    while k < width {
        // The antidiagonal `i + j = k`, clipped to the `N` slots each operand
        // has: `i` runs from `max(0, k + 1 − n)` up to `min(k + 1, n)`,
        // exclusive. This is the same `N²` inner steps the frozen scatter did,
        // not fewer -- the bounds are here so that walking the output does not
        // *cost* a factor two, which a guarded pass over the whole square
        // (`(2N − 1)·N` steps) would. What this loop does save per step is the
        // accumulator: `acc` stays in a register where the scatter read and
        // wrote `out[i + j]` on every term.
        let lo: usize = if k + 1 > n { k + 1 - n } else { 0 };
        let hi: usize = if k + 1 < n { k + 1 } else { n };
        let mut acc: u128 = 0;
        let mut i: usize = lo;
        while i < hi {
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
    let mut acc: Vec<Fp> = Vec::new();
    let mut k: usize = 0;
    while k < width {
        acc.push(Fp::ZERO);
        k += 1;
    }
    let mut j: usize = 0;
    while j < cols {
        // Skip the zero entries (Stage 6 candidate T1a1). `M` is block
        // structured -- `quadeval::rlin_stmt` builds c1 as `[D | 0 | 0]`, c2 as
        // `[0 | B | 0]`, c3 as `[Gᵀb | 0 | 0]` -- and at the pin
        // (`cw + ct + cz = 8192 + 8192 + 40 960`) that makes rows c1, c2 and c3
        // **86% literal `Rq::zero()`**. Without this test each of those entries
        // costs a full `long_mul`, a `2N − 1`-wide accumulation *and* a
        // `2N − 1` allocation, all to add zero.
        //
        // `Rq::is_zero` is `O(N)` against `long_mul`'s `O(N log N)`-per-prime
        // transform work, so the test costs a small fraction of what it saves
        // and is worth paying even when it fails. On the specification side the
        // skipped term is `0 · z_j = 0`, which is why this does not move
        // `c_row_sum_spec`'s statement.
        let mij: &Rq = s.m().entry(i, j);
        if !mij.is_zero() {
            let prod: Vec<Fp> = long_mul(mij, z.get(j));
            let mut t: usize = 0;
            while t < width {
                acc[t] = acc[t] + prod[t];
                t += 1;
            }
        }
        j += 1;
    }
    acc
}

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
    let mut acc: Vec<Fp> = Vec::with_capacity(n);
    let mut k: usize = 0;
    while k < n - 1 {
        acc.push(Fp::ZERO);
        k += 1;
    }
    let mut j: usize = 0;
    while j < cols {
        let mij: &Rq = s.m().entry(i, j);
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
    let mut rem: Vec<Fp> = Vec::with_capacity(p.len());
    let mut t: usize = 0;
    while t < p.len() {
        rem.push(p[t]);
        t += 1;
    }
    let mut quot: Vec<Fp> = Vec::with_capacity(n);
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
    // **The quotient IS the high half** (Stage 6 candidate T1a).
    //
    // [`div_by_modulus`] reads only `rem[k + n]` for `k` from `n − 2` down to
    // `0`; the leads run over `[n, 2n − 2]` and the only writes it makes are
    // `rem[k] -= c` at `k ≤ n − 2` and `rem[lead] = 0` at a lead it has just
    // consumed and never revisits, so every read sees the *original* word.
    // And the `y` subtraction above it touched coefficients `< n` only. So
    // `quot[k] = c_row_sum[k + n]` for `k ≤ n − 2`, and `quot[n − 1] = 0`
    // because that slot is never written.
    //
    // The low half of every `long_mul` -- half the schoolbook work -- was
    // therefore computed, reduced, accumulated over `2N − 1` slots, copied
    // into `rem`, and discarded. [`c_row_sum_high`] computes only what
    // survives; the `y` subtraction and the division loop disappear with it.
    let hi: Vec<Fp> = c_row_sum_high(s, z, i);
    let mut quot: Vec<Fp> = Vec::with_capacity(n);
    let mut k: usize = 0;
    while k < n - 1 {
        quot.push(hi[k]);
        k += 1;
    }
    // the top coefficient `div_by_modulus` never wrote
    quot.push(Fp::ZERO);
    QuotientRow::new(&quot)
}

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
    let mut rho: Vec<QuotientRow> = Vec::with_capacity(rows);
    let mut i: usize = 0;
    while i < rows {
        rho.push(c_quotient(s, z, i));
        i += 1;
    }
    LiftedWitness::new(z.copy(), rho)
}
