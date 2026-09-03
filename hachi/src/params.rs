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
//! Two honesty caveats on "the paper's parameters". First, this is the
//! paper's *commitment and evaluation-split* parameter set only: the protocol
//! layer is absent (`lib.rs` § Status), and with it Fig. 9's matrix `D`/`n_D`,
//! the `z` bound 30583, and the sparse-challenge weight c = 16 (`τ` appears
//! solely inside `BETA_SQ`'s derived literal, at ArkLib's `τ = 5` rather than
//! Fig. 9's 4 -- see that constant). Second, the gadget
//! decomposition itself is **not** paper-faithful at `b = 16`: the paper uses
//! balanced digits in `[-8, 7]`, while the pinned ArkLib
//! (`zmodDigitDecomposition`) -- and therefore this crate -- uses unsigned
//! digits in `{0, …, 15}`, which changes honest commitment outputs and norm
//! sizes relative to the paper's implementation. See NOTES.md § "The digits
//! are not balanced" and the fix trigger recorded there (upstream ArkLib's
//! `balancedZmodDigitDecomposition`, PR #782).

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
/// `zmodDigitDecomposition`), and `Gadget/Norms.lean`'s shortness bounds are
/// stated in terms of it: each digit lies in `{0, …, 15}`, trading digit size
/// for digit count against the binary gadget.
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
/// satisfies the strictly smaller `‖t̂‖∞ ≤ b - 1 = 15`
/// (`Gadget/Norms.lean`'s `gadgetDecompose_zmod_vecLInftyNorm_le`), so an
/// honest opening passes with slack 1.
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
