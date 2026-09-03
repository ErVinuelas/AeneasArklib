//! Every parameter of the scheme, in one place, as `const`s.
//!
//! The ArkLib specification is *generic*: `Rq`, the gadget and the inner-outer
//! commitment are all stated over an arbitrary modulus `q`, cyclotomic index
//! `α`, gadget base `b` and digit count `digits`, with the side conditions that
//! relate them carried as hypotheses. This crate is the opposite by design (see
//! NOTES.md § "Concrete, not generic"): there are no type parameters over the
//! ring, and the parameters live here rather than being threaded through
//! signatures. Aeneas extracts each one as a plain Lean definition, so the
//! equivalence proofs instantiate the generic ArkLib statements at exactly these
//! values.
//!
//! # Provenance of each value
//!
//! Every value below is pinned by something outside this crate: the field
//! layer (`Q`, `EXT_DEGREE`, `EXT_W`) by the `cpoly` dependency; the
//! dimensions (`RING_LOG_DEGREE`, `GADGET_BASE`/`GADGET_DIGITS`, the row,
//! block and split counts) by the Hachi paper's benchmark parameter set
//! ([NOZ26] Fig. 9, the ℓ = 30 row); and the verifier bounds (`KAPPA`,
//! `GAMMA`, `BETA_SQ`) by ArkLib's paper-parameter mapping for the
//! *weak-opening* relation (`QuadEval/Soundness.lean`, Hachi Lemma 8:
//! `(βSq, γ, κ) = (quadEvalBetaSq b b τ d m δ, b, 2ω)`) -- bounds the
//! protocol's *extracted* openings must meet, which is why each strictly
//! exceeds its honest-case value. The `ML_*` lengths are derived
//! arithmetically; the spec-side hypothesis each value has to satisfy is
//! recorded with it.
//!
//! The protocol layer's parameters (the second block below, `OMEGA` through
//! `M_ONE`) are pinned by ArkLib's own profile of the ℓ = 30 set,
//! `Hachi/Params.lean` (ArkLib PR #847, the pinned rev): `hachiTau`,
//! `honestZBound`, `params` (`γ`, `bZero`), `mu0`, `liftKeyWidth`,
//! `sumcheckWidthAtProfile`, together with the `rlin*` block widths of
//! `RingSwitch/Rlin.lean`. Two of Fig. 9's numbers are deliberately *not* the
//! spec's: `τ = 5` rather than 4 (see [`Z_DIGITS`]) and, as a consequence, the
//! `z` bound is ArkLib's proved `131072` rather than the paper's `30583` (see
//! [`Z_BOUND`]). Fig. 9's sparse-challenge weight `c = 16` has no constant here
//! at all: the specification sees a challenge only through `‖c‖₁ ≤ ω`
//! ([`OMEGA`]), the sampler is the caller's, and a bench corpus that wants
//! reference-faithful sparsity says so where it builds its challenges.
//!
//! Two honesty caveats. First, the protocol-layer *code* is still absent
//! (`lib.rs` § Status; it arrives with Stage 3 of PLAN_PROTOCOL_LAYER.md), so
//! the second block is read today only by `tests/params_semantics.rs` and
//! `lean/Check.lean` § 1 -- which is the point of landing it first: the
//! translations are written against named constants whose ArkLib ties are
//! already checked. Second, the gadget decomposition this crate's proved layer
//! implements is the **unsigned** one (`digit_at`: digits in `{0, …, 15}`),
//! which at the pinned ArkLib is `zmodDigitDecomposition` -- documented there
//! as "the building block the balanced digits are shifted from, not itself a
//! Hachi gadget inverse". The Hachi `G⁻¹` is the *balanced* decomposition
//! (digits in `[-8, 7]`, `balancedZmodDigitDecomposition`), which Stage 3's
//! target 1 promotes to the public `gadget_decompose`/`commit` names, keeping
//! `digit_at` as the primitive underneath -- exactly the spec's structure. Its
//! two constants, [`HALF_BASE`] and [`BALANCED_SHIFT`], are already below. See
//! NOTES.md § "The digits are not balanced" and § "Re-pin to ArkLib PR #847".

/// The modulus `q`: the "Hachi prime" `2^32 - 99 = 4294967197`.
///
/// **Pinned.** This is the modulus of `cpoly`'s base field `Fp`, whose Lean
/// equivalence proofs this crate builds on, so it is not a free choice here.
/// It is prime, which is what `Fact (Nat.Prime q)` demands throughout
/// `CyclotomicRing/PowTwo.lean`, and `q < 2^32`, which is the no-overflow
/// argument every `u64` intermediate in the ring layer rests on.
///
/// It is also `≡ 1 mod 4`, which is what makes `Y^4 - 2` irreducible over
/// `F_q` and so makes [`EXT_DEGREE`]/[`EXT_W`] describe a field.
pub const Q: u64 = 4_294_967_197;

/// The degree of the extension field `Ext4 = F_q[Y] / (Y^4 - W)`.
///
/// **Pinned** by `cpoly`: Hachi commits to multilinear polynomials over an
/// extension field ([NOZ26] §3), and the extension whose arithmetic is already
/// proved correct is the quartic one.
pub const EXT_DEGREE: usize = 4;

/// The constant `W` in the extension modulus `Y^4 - W`, the smallest non-square
/// mod [`Q`].
///
/// **Pinned** by `cpoly`.
pub const EXT_W: u64 = 2;

/// The cyclotomic index `α`: the commitment ring is
/// `R_q = Z_q[X] / (X^{2^α} + 1)`.
///
/// **Pinned** by [NOZ26] Fig. 9 (the ℓ = 30 parameter set): `α = 10`, the
/// degree-1024 ring of the paper's benchmark implementation. The spec
/// (`InnerOuter/Arithmetic.lean`, `hachiModulus q α`) admits any `α`, so this
/// pin is a comparability requirement rather than a spec-side one: the point of
/// matching the paper is that this crate's measurements are about the same
/// scheme the paper measured. See NOTES.md § "Chosen parameters".
pub const RING_LOG_DEGREE: usize = 10;

/// The ring degree `2^α = 1024`: the number of `Z_q` coefficients in one element
/// of `R_q`.
///
/// A literal, not `1 << RING_LOG_DEGREE`, and that is an extraction concession
/// rather than a preference: Aeneas models a shift as fallible, so the shifted
/// form extracts as `Result Std.Usize` and every Lean use of it would have to
/// bind and discharge a side condition that is plainly true. As a literal it
/// extracts as `def params.RING_DEGREE : Std.Usize := 1024#usize`.
///
/// `params_semantics::ring_degree_is_a_power_of_two` is what keeps the two in
/// step; see NOTES.md § "Aeneas surprises".
pub const RING_DEGREE: usize = 1024;

/// The gadget base `b`.
///
/// **Pinned** by [NOZ26] Fig. 9: `b = 16`, the paper's decomposition base. The
/// spec-side constraint is `1 < b` (`Gadget/Core.lean`'s
/// `zmodDigitDecomposition`, the unsigned primitive this crate's `digit_at`
/// implements; the balanced Hachi `G⁻¹` shifts it by [`BALANCED_SHIFT`] and
/// re-centres by [`HALF_BASE`]), and the shortness bounds are stated in terms
/// of it: an unsigned digit lies in `{0, …, 15}`, a balanced one in `[-8, 7]`,
/// trading digit size for digit count against the binary gadget.
pub const GADGET_BASE: u64 = 16;

/// The gadget digit count `digits`.
///
/// **Pinned** by [NOZ26] Fig. 9 (`b = 16`, 8 digits), and it still discharges
/// the spec's side condition: `zmodDigitDecomposition` needs `q ≤ b ^ digits`
/// so that every residue fits in `digits` base-`b` digits. Here
/// `16^8 = 2^32 = 4294967296 ≥ 4294967197 = q`, with 99 to spare -- so 8
/// base-16 digits are exactly enough, and 7 (`16^7 = 2^28 < q`) would not be.
///
/// The specification carries *two* digit counts, `messageDigits` and
/// `innerDigits` (`InnerOuter/Scheme.lean`), and admits different values for
/// them. Here they coincide, and not by preference: both decompositions are of
/// `Rq` elements over the same `ZMod q`, so both need `q ≤ b ^ digits`, and at
/// `b = 16` that forces 8 on each. One constant therefore serves both; see
/// NOTES.md § "One digit count, not two".
pub const GADGET_DIGITS: usize = 8;

/// The number of `R_q` rows in one message block: `messageRows` of the
/// specification.
///
/// **Pinned** by [NOZ26] Fig. 9: `2^m` at the paper's `m = 10`. This and the
/// three dimensions below are the shapes of the two Ajtai matrices, which the
/// specification leaves entirely free (`PublicParams`,
/// `InnerOuter/Scheme.lean:94`, is generic in all six); the paper's ℓ = 30 set
/// fixes them, and at this scale one message block is `1024 × 1024` `Z_q`
/// coefficients (NOTES.md § "Chosen parameters").
pub const MESSAGE_ROWS: usize = 1024;

/// The number of `R_q` rows the inner Ajtai matrix `A` produces: `innerRows`.
///
/// **Pinned** by [NOZ26] Fig. 9: the paper's `n_A = 1`. `A` is
/// `INNER_ROWS × (MESSAGE_ROWS * GADGET_DIGITS)`, i.e. `1 × 8192` here -- a
/// single Ajtai row, which is all the paper's ring dimension needs for
/// binding. The multi-row index computations this used to exercise at the old
/// toy shape are carried by [`BLOCKS`] and [`MESSAGE_ROWS`] instead.
pub const INNER_ROWS: usize = 1;

/// The number of `R_q` rows the outer Ajtai matrix `B` produces: `outerRows`.
///
/// **Pinned** by [NOZ26] Fig. 9: the paper's `n_B = 1` (see [`INNER_ROWS`]).
/// `B` is `OUTER_ROWS × (BLOCKS * (INNER_ROWS * GADGET_DIGITS))`, i.e.
/// `1 × 8192` here. The commitment is a vector of this many ring elements.
pub const OUTER_ROWS: usize = 1;

/// The number of message blocks committed together: `blocks`.
///
/// **Pinned** by [NOZ26] Fig. 9: `2^r` at the paper's `r = 10`. Exceeds 1, so
/// the per-block loop of `verify_weak` and the block flattening of
/// `commitWithDecomps` are still exercised (and then some).
pub const BLOCKS: usize = 1024;

/// The `ℓ∞` bound `γ` on the flattened inner decomposition, checked by
/// `verify_weak`.
///
/// **Pinned** by ArkLib's paper-parameter mapping for the weak-opening
/// relation, `γ̄ = b` (`QuadEval/Soundness.lean`, "Paper parameter mapping":
/// the paper's Eq. (20) checks the box `S_b` -- centered coefficients in
/// `[⌈-b/2⌉, ⌈b/2⌉-1]` -- which ArkLib's symmetric model relaxes to
/// `‖·‖∞ ≤ γ` with `γ := b`). This is a bound extracted openings must meet,
/// not the honest ceiling: this crate's honest (unsigned-digit) decomposition
/// satisfies the strictly smaller `‖t̂‖∞ ≤ b - 1 = 15` (ArkLib's generic
/// `gadgetDecompose_vecLInftyNorm_le_of_digit_le` at the unsigned digit bound,
/// `lean/Scheme.lean`'s `dd_digit_natAbs_le`), so an honest opening passes
/// with slack 1. The chain's own `ℓ∞` radius is the *different* constant
/// [`CHAIN_GAMMA`]` = 15`.
///
/// A literal `16` rather than `GADGET_BASE`, for the reason [`RING_DEGREE`]
/// is a literal (a derived form would extract through `Result`); the relation
/// to [`GADGET_BASE`] is checked in `tests/params_semantics.rs` and
/// `lean/Check.lean` § 1.
pub const GAMMA: u64 = 16;

/// The squared-`ℓ₂` bound `βSq` on the challenge-scaled message, checked by
/// `verify_weak`.
///
/// **Pinned** by ArkLib's paper-parameter mapping for the weak-opening
/// relation: `quadEvalBetaSq γ b τ d m δ` at `γ := b`
/// (`QuadEval/Soundness.lean`, Hachi Lemma 8's `βSq := 4·B_z`) --
///
/// ```text
/// 4 · (2^m · δ) · (d · ((Σ_{u<τ} b^u) · γ)²)
///   = 4 · (1024 · 8) · (1024 · (69905 · 16)²) = 41976510894886092800
/// ```
///
/// with `τ = 5`, the folded-witness digit count of ArkLib's `ℓ = 30` profile
/// (ArkLib PR #847, `Hachi/Params.lean`: `hachiTau`, and its `betaSq` is this
/// same expression) -- **not** [NOZ26] Fig. 9's `τ = 4`, and not the message
/// digit count `δ = 8`. `τ` is sized from the honest folded witness
/// `z = Σᵢ cᵢ sᵢ`, which is deterministically short, `‖z‖∞ ≤ 2ʳ·ω·⌊b/2⌋ =
/// 131072`: five balanced base-16 digits carry up to `7 · Σ_{u<5} 16^u =
/// 489335`, four carry only `30583` -- exactly Fig. 9's `z` bound, which rests
/// on a sharper statistical analysis ArkLib does not formalize. (An interim
/// `τ = 8` reading, forced while ArkLib still demanded `q ≤ b ^ zDigits` of
/// the `z`-gadget, was never committed; `BoundedDigitDecomposition` removed
/// that hypothesis -- NOTES.md § "`BETA_SQ` corrected".) `τ` enters only
/// this derived literal: the `z`-machinery itself is protocol layer and
/// absent (see `lib.rs` § Status). This is the bound on the *extracted*
/// `c̄ⱼ •ᵥ sⱼ` (a difference of two `z`-recompositions), which is why it
/// dwarfs the honest case: the honest decomposition at `c = 1` sits at
/// `(1024 · 8) · 1024 · 15² = 1887436800`, about 2.2 · 10¹⁰ times below the
/// bound. ArkLib deliberately states this as a squared-`ℓ₂` bound rather than
/// the paper's `ℓ∞`-style `β̄ = 2·b^τ` (see `quadEvalZL2SqBound`). One
/// consequence to record rather than fix: `√βSq ≈ 2^32.6` still exceeds
/// `q ≈ 2^32` (by 1.5×, where the `τ = 8` reading had 2^12.6×), so the
/// weak-binding hypothesis at this radius is not SIS-instantiable at Fig. 9's
/// toy row count -- a property of ArkLib's ball-relaxed `γ̄ = b`, not of this
/// translation (see `NOTES.md`).
///
/// A literal, for the reason [`GAMMA`] is one; the product it stands for is
/// checked in `tests/params_semantics.rs` and `lean/Check.lean` § 1.
///
/// `u128`, not `u64`, because that is the width the norm itself is computed at:
/// a single centered coefficient can be as large as `q/2`, so one squared
/// coefficient approaches `2^62` and a vector of them overflows `u64`. See
/// `commit::vec_l2_norm_sq`.
pub const BETA_SQ: u128 = 41_976_510_894_886_092_800;

/// The number of *low* (first) variables `nl` of the evaluation split: the
/// `r` of Hachi [NOZ26] §4, `PolyEvalStatement`'s `xl` half.
///
/// **Derived**, not free: the split's reshaped coefficient matrix is
/// `2^nl × 2^nh` (`Hachi/EvalSplit.lean:151`), and its consumer pins the shape
/// -- `derivedMsgMatrix` is `PolyMatrix (Rq Φ) (2^r) (2^m)`
/// (`QuadEval/Reduction.lean:193`) with `2^r = blocks`. At [`BLOCKS`]` = 1024`
/// that forces `nl = 10` -- the paper's `r` ([NOZ26] Fig. 9).
pub const ML_VARS_LOW: usize = 10;

/// The number of *high* (last) variables `nh` of the evaluation split: the
/// `m` of Hachi [NOZ26] §4, `PolyEvalStatement`'s `xh` half.
///
/// **Derived** (see [`ML_VARS_LOW`]): the matrix column count is
/// `2^nh = messageRows`, and at [`MESSAGE_ROWS`]` = 1024` that forces
/// `nh = 10` -- the paper's `m` ([NOZ26] Fig. 9). Together the split covers
/// the `ℓ - α = 30 - 10 = 20` `R_q`-variables of the ℓ = 30 set.
pub const ML_VARS_HIGH: usize = 10;

/// `2^ML_VARS_LOW = 1024`: the row count of the reshaped coefficient matrix,
/// the length of the outer monomial basis `mb(xl)`, and (by the consumer's
/// shape) equal to [`BLOCKS`].
///
/// A literal, not `1 << ML_VARS_LOW`, for the reason [`RING_DEGREE`] is a
/// literal; the relations are checked in `tests/params_semantics.rs` and
/// `lean/Check.lean` § 1.
pub const ML_LOW_LEN: usize = 1024;

/// `2^ML_VARS_HIGH = 1024`: the column count of the reshaped coefficient
/// matrix, the length of the inner monomial basis `mb(xh)`, and (by the
/// consumer's shape) equal to [`MESSAGE_ROWS`].
///
/// A literal (see [`ML_LOW_LEN`]).
pub const ML_HIGH_LEN: usize = 1024;

/// `2^(ML_VARS_LOW + ML_VARS_HIGH) = 1048576`: the coefficient count of a
/// committed multilinear polynomial, i.e. `ML_LOW_LEN * ML_HIGH_LEN`.
///
/// A literal (see [`ML_LOW_LEN`]).
pub const ML_POLY_LEN: usize = 1_048_576;

/// The `ℓ₁` bound `κ` on a challenge, checked by `verify_weak`.
///
/// **Pinned** by ArkLib's paper-parameter mapping for the weak-opening
/// relation, `κ = ω̄ = 2ω = 32` at the paper's `ω = 16` ([NOZ26] Fig. 9;
/// `QuadEval/Soundness.lean`, "Paper parameter mapping"). Not `ω` itself:
/// `ω` bounds a *sampled* challenge, but the openings the extraction produces
/// carry *differences* of two sampled challenges, and the triangle inequality
/// gives those `‖c̄‖₁ ≤ 2ω`. Well inside the legality ceiling the
/// specification needs for the challenge to be *invertible*, which is what a
/// weak opening really requires ([NOZ26] §4.1): `isUnit_of_l1Norm_le`
/// (`NormBounds/LyubashevskySeiler.lean:344`) turns `0 < ‖c‖₁ ≤ κ` into
/// `IsUnit c` provided `q % 8 = 5` and `κ² < q`. Here `q % 8 = 5` holds, and
/// `κ² = 1024 < q` with room to spare (the ceiling is `⌊√q⌋ = 65535`; this
/// crate used to sit on it, before the paper's values were adopted) -- the
/// same `(2ω)² < q` hypothesis ArkLib's Lemma 8 statement carries as `hκ`.
///
/// The challenge *sampler* the paper pairs with `ω` (c = 16 sparse
/// coefficients) lives in the protocol layer, which is out of scope here; the
/// honest challenge `c = 1` has `‖1‖₁ = 1` and passes.
pub const KAPPA: u64 = 32;

// ---------------------------------------------------------------------------
// The protocol layer: ArkLib's `ℓ = 30` profile (`Hachi/Params.lean`, PR #847)
// ---------------------------------------------------------------------------
//
// Everything below is a value the composed opening chain (`Composition.lean`,
// `Correctness.lean`, `Concrete.lean`) takes as a parameter or a dimension it
// derives from one, fixed at the profile `Hachi/Params.lean` states and proves
// facts about. Each is a literal (the reason is [`RING_DEGREE`]'s), and each
// literal's tie to its ArkLib expression is checked in `lean/Check.lean` § 1 --
// by *name* where `Params.lean` names it (`hachiTau`, `honestZBound`, `mu0`,
// `liftKeyWidth`, …), by the defining arithmetic otherwise. Literal-collision
// warning for the proofs: `16` is now `GADGET_BASE`, `GAMMA`, `B_ZERO` and
// `OMEGA`; `8` is `GADGET_DIGITS` and `HALF_BASE`; `8192` is `RLIN_CW`,
// `RLIN_CT` and `D_QUAD_COLS`; `1` is `INNER_ROWS`, `OUTER_ROWS` and `D_ROWS`.
// Rewrite hypotheses, never goals.

/// The `ℓ₁` bound `ω` on a *sampled* challenge: `ShortChallenge Φ ω`
/// (`QuadEval/Reduction.lean`), the `ω` of [NOZ26] Fig. 9.
///
/// **Pinned** by `Hachi/Params.lean`'s `hachiOmega = 16`. [`KAPPA`] is its
/// weak-opening double, `2ω`; this constant is what makes that `2 * 16` a
/// checked relation rather than a magic number. The honest folded witness's
/// bound [`Z_BOUND`] is `2ʳ · ω · ⌊b/2⌋`.
pub const OMEGA: u64 = 16;

/// The number of `R_q` rows of the Hachi short-commitment matrix `D`
/// (`PublicParamsD.dMatrix`, `QuadEval/Gadgets.lean`): `dRows`, the paper's
/// `n_D`.
///
/// **Pinned** by `Hachi/Params.lean`'s `hachiN = 1` (`n_A = n_B = n_D = 1`),
/// like [`INNER_ROWS`] and [`OUTER_ROWS`]. `D` is `D_ROWS × D_QUAD_COLS` in the
/// QuadEval link and `D_ROWS × LIFT_COLS` as the ring-switch lift key
/// (`hachiLiftCom`); the two are different matrices that happen to share a
/// height. The key itself is caller-supplied, never sampled here (NOTES.md
/// § "Keys and challenges are inputs, not constants").
pub const D_ROWS: usize = 1;

/// The zero-check range base `bZero`: the base in which the ring-switch
/// quotient block is committed as digits (`rhoDigits`, `RingSwitch/RhoDigits.lean`)
/// and the range the nested zero-check enforces on them.
///
/// **Pinned** by `Hachi/Params.lean`'s `params.bZero = 16`: the profile is
/// `HonestRangeParams.ofPinnedDigitBase b`, which sets `bZero := b`, and the
/// soundness chain hard-wires the same (`Composition.lean`). A literal `16`
/// rather than [`GADGET_BASE`] for the usual extraction reason; equality is
/// checked. Its digit count `rhoDigitCount q bZero = ⌈log₁₆ q⌉ = 8` needs no
/// constant of its own -- it *is* [`GADGET_DIGITS`], and `lean/Check.lean` § 1
/// proves that identity rather than naming the number twice.
pub const B_ZERO: u64 = 16;

/// The composed chain's `ℓ∞` radius `γ` on the lifted witness: the
/// `liftShort Φ γ bZero` bound (`RingSwitch/Reduction.lean`), and the `γ` slot of
/// every `relOut` on the honest path.
///
/// **Pinned** by `Hachi/Params.lean`'s `params.γ = 15`: completeness forces
/// `γ = bZero − 1` (`HonestChain.lean`, the honest quotient digits are
/// `⌊b/2⌋`-bounded and the range check must admit them), and
/// `ofPinnedDigitBase` realizes exactly that. **Not** [`GAMMA`]` = 16`, the
/// weak-opening `γ̄ = b` the commitment layer's `verify_weak` checks: two
/// ArkLib quantities that differ by one, and every proof that mentions either
/// must say which.
pub const CHAIN_GAMMA: u64 = 15;

/// `⌊b/2⌋ = 8`: the re-centring offset of a balanced digit, and the radius of
/// the balanced digit box `S_b = [-8, 7]` (Eq. (20)).
///
/// **Derived** from [`GADGET_BASE`] (`b / 2` in `balancedZmodDigitDecomposition`,
/// `Gadget/Core.lean`, and in `boundedBalancedZmodDigit`); a literal for the
/// usual reason. Every balanced digit is `unsigned digit − HALF_BASE`, as a
/// *field* subtraction. The honest balanced decomposition is `ℓ∞`-short at
/// radius exactly this (`balancedZmodDigit_natAbs_le`), against the chain's
/// [`CHAIN_GAMMA`]` = 15` and the weak-opening [`GAMMA`]` = 16`.
pub const HALF_BASE: u64 = 8;

/// The balanced shift `⌊b/2⌋ · (1 + b + ⋯ + b^(δ−1)) = 8 · 286331153 =
/// 2290649224 = 0x88888888`: what the message-digit balanced decomposition adds
/// to a coefficient before taking its unsigned base-`b` digits, so that
/// subtracting [`HALF_BASE`] from each lands in `[-8, 7]`.
///
/// **Derived**: `balancedShift b digits` (`Gadget/Core.lean`) at
/// `(b, digits) = (16, 8)`, i.e. `(b/2) · digitOnesValue b digits` read in
/// `ZMod q`. Strictly below [`Q`], so the `ZMod q` value is this literal with no
/// reduction step -- which is why `lean/Check.lean` § 1 can tie it as a plain
/// `ℕ` identity. The Rust must add it as a *field* element (wrapping mod `q`),
/// never as a raw `u64`: the whole point is that `c + shift` is read through
/// `.val` after reduction. On the literal-collision watchlist: it is the one
/// constant here whose value is unique.
pub const BALANCED_SHIFT: u64 = 2_290_649_224;

/// The folded-witness digit count `τ`: the number of balanced base-`b` digits
/// the response `ẑ = J⁻¹(z)` carries per coefficient (`zDigits` throughout
/// `QuadEval/`, `jMatrix Φ base n zDigits`).
///
/// **Pinned** by `Hachi/Params.lean`'s `hachiTau = 5` -- **not** [NOZ26]
/// Fig. 9's `τ = 4`, and **not** the message digit count [`GADGET_DIGITS`]` =
/// 8`. The folded witness `z = Σᵢ cᵢ sᵢ` is deterministically short
/// (`‖z‖∞ ≤ 2ʳ·ω·⌊b/2⌋ = `[`Z_BOUND`]), so its digit count is sized from that
/// bound rather than from `q`: five balanced base-16 digits carry every
/// integer up to `7 · Σ_{u<5} 16^u = 489335 ≥ 131072`, and four carry only
/// `30583 < 131072` (`tau_minimal`) -- `30583` being exactly Fig. 9's `z`
/// bound, which rests on a sharper statistical analysis ArkLib does not
/// formalize. It is *not* a full-width decomposition: `16^5 < q`
/// (`sixteen_pow_tau_lt_q`), so no `DigitDecomposition (16 : ZMod q) 5`
/// exists, and the `z` side goes through `BoundedDigitDecomposition` --
/// total and executable, reconstruction guaranteed only on inputs within
/// [`Z_BOUND`]. Consequently `Z_DIGITS ≠ GADGET_DIGITS`, and every `gadget_*`
/// function hard-wired to [`GADGET_DIGITS`] gets a `_z` sibling at this width
/// rather than a digits parameter. Also the `τ` inside [`BETA_SQ`].
pub const Z_DIGITS: usize = 5;

/// The `ℓ∞` bound the bounded `z` decomposition is sized for: `zBound` of
/// `hachiNonrecursive`, the honest `‖z‖∞ ≤ 2ʳ · ω · ⌊b/2⌋ = 2¹⁰ · 16 · 8 =
/// 131072`.
///
/// **Pinned** by `Hachi/Params.lean`'s `honestZBound = 131072`
/// (`vecLInftyNorm_honestZ_le`). Deliberately ArkLib's proved deterministic
/// bound and not Fig. 9's `30583`: the paper's number is the `τ = 4`
/// representability ceiling under a statistical analysis this development
/// does not carry (PLAN_Z_SHORTNESS.md). The two side conditions the
/// correctness theorem takes on it, `hcap : zBound ≤ balancedDigitCapacity b τ`
/// and `hzb : 2ʳ·ω·⌊b/2⌋ ≤ zBound` (the latter with equality), are checked in
/// `tests/params_semantics.rs` and `lean/Check.lean` § 1.
pub const Z_BOUND: u64 = 131_072;

/// The balanced shift of the `z` side: `⌊b/2⌋ · (1 + 16 + 16² + 16³ + 16⁴) =
/// 8 · 69905 = 559240`, added to the *centred* representative of a coefficient
/// before its five unsigned digits are taken (`boundedBalancedZmodDigit`,
/// `Gadget/Core.lean`: `Nat.digits b (valMinAbs x + ⌊b/2⌋·S).toNat`).
///
/// **Derived**: `(b/2) · digitOnesValue b τ` at `(16, 5)`
/// (`digitOnesValue_eq = 69905`). Unlike [`BALANCED_SHIFT`] this is an
/// *integer* shift of a signed centred value, not a field addition: the
/// spec centres first (`valMinAbs`), shifts in `ℤ`, and clamps a too-negative
/// result to `0` (`Int.toNat`), so a Rust implementation works on the centred
/// `i64`/`u64` representative, which `commit.rs`'s norm code already computes.
pub const Z_BALANCED_SHIFT: u64 = 559_240;

/// The carrier block width `cW = 2ʳ · messageDigits = 8192` of the Eq. (20)
/// block system: the columns holding `ŵ` (`rlinCW`, `RingSwitch/Rlin.lean`).
///
/// **Derived** from [`BLOCKS`]` · `[`GADGET_DIGITS`]; a literal for the usual
/// reason, relation checked.
pub const RLIN_CW: usize = 8192;

/// The inner block width `cT = 2ʳ · (n_A · innerDigits) = 8192`: the columns
/// holding `flatten t̂` (`rlinCT`).
///
/// **Derived** from [`BLOCKS`]` · (`[`INNER_ROWS`]` · `[`GADGET_DIGITS`]`)`.
/// Equal to [`RLIN_CW`] because `n_A = 1` and the two digit counts coincide --
/// the coincidence the reference implementation calls `reuse_mats`.
pub const RLIN_CT: usize = 8192;

/// The response block width `cZ = 2ᵐ · messageDigits · τ = 1024 · 8 · 5 =
/// 40960`: the columns holding `ẑ` (`rlinCZ`).
///
/// **Derived** from [`MESSAGE_ROWS`]` · `[`GADGET_DIGITS`]` · `[`Z_DIGITS`]. The
/// one `τ`-dependent block: it was 65536 under the full-width `τ = δ = 8`
/// reading and 32768 under the paper's `τ = 4`.
pub const RLIN_CZ: usize = 40_960;

/// The column count `μ₀` of the Eq. (20) block system, the width of the
/// stacked witness `ζ = ŵ ++ (flatten t̂ ++ ẑ)` and of the lifted witness's
/// message part: `rlinCols n_A δ δ τ m r` (`RingSwitch/Rlin.lean`).
///
/// **Pinned** by `Hachi/Params.lean`'s `mu0_eq : mu0 = 57344`
/// (`= `[`RLIN_CW`]` + (`[`RLIN_CT`]` + `[`RLIN_CZ`]`)`, with the parenthesization
/// the spec fixes). `81920` under `τ = 8`; `49152` under `τ = 4`.
pub const RLIN_COLS: usize = 57_344;

/// The row count `n₀` of the Eq. (20) block system, the stacked rows
/// `c1 ++ (c2 ++ (c3 ++ (c4 ++ c5)))`: `rlinRows n_A n_B n_D = n_D + (n_B + (1 +
/// (1 + n_A))) = 5` (`RingSwitch/Rlin.lean`).
///
/// **Derived** from [`D_ROWS`], [`OUTER_ROWS`], [`INNER_ROWS`]; also the number
/// of quotient-block rows the ring switch commits as digits, hence the `n₀` in
/// [`LIFT_COLS`] and the row count [`M_ONE`] must cover.
pub const RLIN_ROWS: usize = 5;

/// The column count of the QuadEval short-commitment matrix `D`:
/// `blocks · messageDigits = 8192`, the width of the carrier decomposition `ŵ`
/// it commits to (`PublicParamsD.dMatrix : Simple.PublicParams Φ dRows (blocks
/// * messageDigits)`, `QuadEval/Gadgets.lean`).
///
/// **Derived** from [`BLOCKS`]` · `[`GADGET_DIGITS`]. Numerically [`RLIN_CW`],
/// and deliberately a separate name: one is a matrix width, the other a block
/// offset inside `ζ`.
pub const D_QUAD_COLS: usize = 8192;

/// The width of the ring-switch lift key and the row count of the lifted
/// witness table: `μ₀ + n₀ · rhoDigitCount q bZero = 57344 + 5 · 8 = 57384`
/// (`hachiLiftCom`'s `D : PublicParams 𝓜 dRows (μ₀ + n₀ · rhoDigitCount q
/// bZero)`, `Concrete.lean`).
///
/// **Pinned** by `Hachi/Params.lean`'s `liftKeyWidth_eq : liftKeyWidth = 57384`.
/// Derived here as [`RLIN_COLS`]` + `[`RLIN_ROWS`]` · `[`GADGET_DIGITS`] (the
/// quotient digit count equals [`GADGET_DIGITS`]; see [`B_ZERO`]). `81960`
/// under `τ = 8`.
pub const LIFT_COLS: usize = 57_384;

/// The sumcheck's variable count `m₀ = M + 1 = 26`: the cube `{0,1}^m₀` the
/// digit-committed table is laid out on, hence the number of sumcheck rounds
/// and the zero-check's first block width.
///
/// **Pinned** by `Hachi/Params.lean`'s `sumcheckWidthAtProfile` /
/// `sumcheckWidthAtProfile_minimal`: the coverage hypothesis
/// `hμn : (μ₀ + n₀·δ) · d ≤ 2^(M+1)` holds at `M = 25` (`57384 · 1024 =
/// 58761216 ≤ 2²⁶`) and fails at `M = 24` (`2²⁵ = 33554432`). ArkLib carries
/// `M` free under that inequality; the profile fixes it at the least value, and
/// this constant is `M + 1` because that is what everything downstream reads
/// (`pSpecNestedZeroCheck F (M + 1) m₁`, the round count). `27` under `τ = 8`,
/// `26` under `τ = 4` as well. Every cube-shaped object is `2^M_ZERO ≈ 6.7·10⁷`
/// entries -- the second scale wall of PLAN_PROTOCOL_LAYER.md Risk 7.
pub const M_ZERO: usize = 26;

/// The nested zero-check's second block width `m₁ = 3`: the cube `{0,1}^m₁`
/// that indexes the `n₀` committed quotient rows.
///
/// **Derived**, with a recorded exception: ArkLib leaves `m₁` free under
/// `hn : n₀ ≤ 2^m₁` (`Composition.lean`) and the profile in `Hachi/Params.lean`
/// does not name it, so there is no ArkLib expression for `lean/Check.lean` § 1
/// to tie the literal to -- only the coverage inequality and its minimality
/// (`4 < 5 ≤ 8`). The one constant in this file with that status (NOTES.md
/// § "Re-pin to ArkLib PR #847", the house-discipline exception).
pub const M_ONE: usize = 3;
