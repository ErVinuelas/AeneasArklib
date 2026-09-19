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
//! the `z` bound 30583, and the sparse-challenge weight c = 16 (`τ = 4`
//! appears solely inside `BETA_SQ`'s derived literal). Second, the gadget
//! decomposition itself is **not** paper-faithful at `b = 16`: the paper uses
//! balanced digits in `[-8, 7]`, while the pinned ArkLib
//! (`zmodDigitDecomposition`) -- and therefore this crate -- uses unsigned
//! digits in `{0, …, 15}`, which changes honest commitment outputs and norm
//! sizes relative to the paper's implementation. See NOTES.md § "The digits
//! are not balanced" and the fix trigger recorded there (upstream ArkLib's
//! `balancedZmodDigitDecomposition`, PR #782).

// @genesis 4409640 2026-08-18 — params::Q
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

// @genesis 4409640 2026-08-18 — params::EXT_DEGREE
/// The degree of the extension field `Ext4 = F_q[Y] / (Y^4 - W)`.
///
/// **Pinned** by `cpoly`: Hachi commits to multilinear polynomials over an
/// extension field ([NOZ26] §3), and the extension whose arithmetic is already
/// proved correct is the quartic one.
pub const EXT_DEGREE: usize = 4;

// @genesis 4409640 2026-08-18 — params::EXT_W
/// The constant `W` in the extension modulus `Y^4 - W`, the smallest non-square
/// mod [`Q`].
///
/// **Pinned** by `cpoly`.
pub const EXT_W: u64 = 2;

// @genesis af05e6c 2026-08-28 — params::RING_LOG_DEGREE
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

// @genesis af05e6c 2026-08-28 — params::RING_DEGREE
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

// @genesis af05e6c 2026-08-28 — params::GADGET_BASE
/// The gadget base `b`.
///
/// **Pinned** by [NOZ26] Fig. 9: `b = 16`, the paper's decomposition base. The
/// spec-side constraint is `1 < b` (`Gadget/Core.lean`'s
/// `zmodDigitDecomposition`), and `Gadget/Norms.lean`'s shortness bounds are
/// stated in terms of it: each digit lies in `{0, …, 15}`, trading digit size
/// for digit count against the binary gadget.
pub const GADGET_BASE: u64 = 16;

// @genesis af05e6c 2026-08-28 — params::GADGET_DIGITS
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

// @genesis af05e6c 2026-08-28 — params::MESSAGE_ROWS
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

// @genesis af05e6c 2026-08-28 — params::INNER_ROWS
/// The number of `R_q` rows the inner Ajtai matrix `A` produces: `innerRows`.
///
/// **Pinned** by [NOZ26] Fig. 9: the paper's `n_A = 1`. `A` is
/// `INNER_ROWS × (MESSAGE_ROWS * GADGET_DIGITS)`, i.e. `1 × 8192` here -- a
/// single Ajtai row, which is all the paper's ring dimension needs for
/// binding. The multi-row index computations this used to exercise at the old
/// toy shape are carried by [`BLOCKS`] and [`MESSAGE_ROWS`] instead.
pub const INNER_ROWS: usize = 1;

// @genesis af05e6c 2026-08-28 — params::OUTER_ROWS
/// The number of `R_q` rows the outer Ajtai matrix `B` produces: `outerRows`.
///
/// **Pinned** by [NOZ26] Fig. 9: the paper's `n_B = 1` (see [`INNER_ROWS`]).
/// `B` is `OUTER_ROWS × (BLOCKS * (INNER_ROWS * GADGET_DIGITS))`, i.e.
/// `1 × 8192` here. The commitment is a vector of this many ring elements.
pub const OUTER_ROWS: usize = 1;

// @genesis af05e6c 2026-08-28 — params::BLOCKS
/// The number of message blocks committed together: `blocks`.
///
/// **Pinned** by [NOZ26] Fig. 9: `2^r` at the paper's `r = 10`. Exceeds 1, so
/// the per-block loop of `verify_weak` and the block flattening of
/// `commitWithDecomps` are still exercised (and then some).
pub const BLOCKS: usize = 1024;

// @genesis af05e6c 2026-08-28 — params::GAMMA
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

// @genesis af05e6c 2026-08-28 — params::BETA_SQ
/// The squared-`ℓ₂` bound `βSq` on the challenge-scaled message, checked by
/// `verify_weak`.
///
/// **Pinned** by ArkLib's paper-parameter mapping for the weak-opening
/// relation: `quadEvalBetaSq γ b τ d m δ` at `γ := b`
/// (`QuadEval/Soundness.lean`, Hachi Lemma 8's `βSq := 4·B_z`) --
///
/// ```text
/// 4 · (2^m · δ) · (d · ((Σ_{u<τ} b^u) · γ)²)
///   = 4 · (1024 · 8) · (1024 · (4369 · 16)²) = 163966054471565312
/// ```
///
/// with `τ = 4` the paper's `z`-decomposition digit count ([NOZ26] Fig. 9).
/// `τ` enters only this derived literal: the `z`-machinery itself is protocol
/// layer and absent (see `lib.rs` § Status). This is the bound on the
/// *extracted* `c̄ⱼ •ᵥ sⱼ` (a difference of two `z`-recompositions), which is
/// why it dwarfs the honest case: the honest decomposition at `c = 1` sits at
/// `(1024 · 8) · 1024 · 15² = 1887436800`, about 8.7 · 10⁷ times below the
/// bound. ArkLib deliberately states this as a squared-`ℓ₂` bound rather than
/// the paper's `ℓ∞`-style `β̄ = 2·b^τ` (see `quadEvalZL2SqBound`).
///
/// A literal, for the reason [`GAMMA`] is one; the product it stands for is
/// checked in `tests/params_semantics.rs` and `lean/Check.lean` § 1.
///
/// `u128`, not `u64`, because that is the width the norm itself is computed at:
/// a single centered coefficient can be as large as `q/2`, so one squared
/// coefficient approaches `2^62` and a vector of them overflows `u64`. See
/// `commit::vec_l2_norm_sq`.
pub const BETA_SQ: u128 = 163_966_054_471_565_312;

// @genesis af05e6c 2026-08-28 — params::ML_VARS_LOW
/// The number of *low* (first) variables `nl` of the evaluation split: the
/// `r` of Hachi [NOZ26] §4, `PolyEvalStatement`'s `xl` half.
///
/// **Derived**, not free: the split's reshaped coefficient matrix is
/// `2^nl × 2^nh` (`Hachi/EvalSplit.lean:151`), and its consumer pins the shape
/// -- `derivedMsgMatrix` is `PolyMatrix (Rq Φ) (2^r) (2^m)`
/// (`QuadEval/Reduction.lean:193`) with `2^r = blocks`. At [`BLOCKS`]` = 1024`
/// that forces `nl = 10` -- the paper's `r` ([NOZ26] Fig. 9).
pub const ML_VARS_LOW: usize = 10;

// @genesis af05e6c 2026-08-28 — params::ML_VARS_HIGH
/// The number of *high* (last) variables `nh` of the evaluation split: the
/// `m` of Hachi [NOZ26] §4, `PolyEvalStatement`'s `xh` half.
///
/// **Derived** (see [`ML_VARS_LOW`]): the matrix column count is
/// `2^nh = messageRows`, and at [`MESSAGE_ROWS`]` = 1024` that forces
/// `nh = 10` -- the paper's `m` ([NOZ26] Fig. 9). Together the split covers
/// the `ℓ - α = 30 - 10 = 20` `R_q`-variables of the ℓ = 30 set.
pub const ML_VARS_HIGH: usize = 10;

// @genesis af05e6c 2026-08-28 — params::ML_LOW_LEN
/// `2^ML_VARS_LOW = 1024`: the row count of the reshaped coefficient matrix,
/// the length of the outer monomial basis `mb(xl)`, and (by the consumer's
/// shape) equal to [`BLOCKS`].
///
/// A literal, not `1 << ML_VARS_LOW`, for the reason [`RING_DEGREE`] is a
/// literal; the relations are checked in `tests/params_semantics.rs` and
/// `lean/Check.lean` § 1.
pub const ML_LOW_LEN: usize = 1024;

// @genesis af05e6c 2026-08-28 — params::ML_HIGH_LEN
/// `2^ML_VARS_HIGH = 1024`: the column count of the reshaped coefficient
/// matrix, the length of the inner monomial basis `mb(xh)`, and (by the
/// consumer's shape) equal to [`MESSAGE_ROWS`].
///
/// A literal (see [`ML_LOW_LEN`]).
pub const ML_HIGH_LEN: usize = 1024;

// @genesis af05e6c 2026-08-28 — params::ML_POLY_LEN
/// `2^(ML_VARS_LOW + ML_VARS_HIGH) = 1048576`: the coefficient count of a
/// committed multilinear polynomial, i.e. `ML_LOW_LEN * ML_HIGH_LEN`.
///
/// A literal (see [`ML_LOW_LEN`]).
pub const ML_POLY_LEN: usize = 1_048_576;

// @genesis af05e6c 2026-08-28 — params::KAPPA
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

// @genesis a898de7 2026-09-04 — params::OMEGA
/// The `ℓ₁` bound `ω` on a *sampled* challenge: `ShortChallenge Φ ω`
/// (`QuadEval/Reduction.lean`), the `ω` of [NOZ26] Fig. 9.
///
/// **Pinned** by `Hachi/Params.lean`'s `hachiOmega = 16`. [`KAPPA`] is its
/// weak-opening double, `2ω`; this constant is what makes that `2 * 16` a
/// checked relation rather than a magic number. The honest folded witness's
/// bound [`Z_BOUND`] is `2ʳ · ω · ⌊b/2⌋`.
pub const OMEGA: u64 = 16;

// @genesis a898de7 2026-09-04 — params::D_ROWS
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

// @genesis a898de7 2026-09-04 — params::B_ZERO
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

// @genesis a898de7 2026-09-04 — params::CHAIN_GAMMA
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

// @genesis a898de7 2026-09-04 — params::HALF_BASE
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

// @genesis a898de7 2026-09-04 — params::BALANCED_SHIFT
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

// @genesis a898de7 2026-09-04 — params::Z_DIGITS
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

// @genesis a898de7 2026-09-04 — params::Z_BOUND
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

// @genesis a898de7 2026-09-04 — params::Z_BALANCED_SHIFT
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

// @genesis a898de7 2026-09-04 — params::RLIN_CW
/// The carrier block width `cW = 2ʳ · messageDigits = 8192` of the Eq. (20)
/// block system: the columns holding `ŵ` (`rlinCW`, `RingSwitch/Rlin.lean`).
///
/// **Derived** from [`BLOCKS`]` · `[`GADGET_DIGITS`]; a literal for the usual
/// reason, relation checked.
pub const RLIN_CW: usize = 8192;

// @genesis a898de7 2026-09-04 — params::RLIN_CT
/// The inner block width `cT = 2ʳ · (n_A · innerDigits) = 8192`: the columns
/// holding `flatten t̂` (`rlinCT`).
///
/// **Derived** from [`BLOCKS`]` · (`[`INNER_ROWS`]` · `[`GADGET_DIGITS`]`)`.
/// Equal to [`RLIN_CW`] because `n_A = 1` and the two digit counts coincide --
/// the coincidence the reference implementation calls `reuse_mats`.
pub const RLIN_CT: usize = 8192;

// @genesis a898de7 2026-09-04 — params::RLIN_CZ
/// The response block width `cZ = 2ᵐ · messageDigits · τ = 1024 · 8 · 5 =
/// 40960`: the columns holding `ẑ` (`rlinCZ`).
///
/// **Derived** from [`MESSAGE_ROWS`]` · `[`GADGET_DIGITS`]` · `[`Z_DIGITS`]. The
/// one `τ`-dependent block: it was 65536 under the full-width `τ = δ = 8`
/// reading and 32768 under the paper's `τ = 4`.
pub const RLIN_CZ: usize = 40_960;

// @genesis a898de7 2026-09-04 — params::RLIN_COLS
/// The column count `μ₀` of the Eq. (20) block system, the width of the
/// stacked witness `ζ = ŵ ++ (flatten t̂ ++ ẑ)` and of the lifted witness's
/// message part: `rlinCols n_A δ δ τ m r` (`RingSwitch/Rlin.lean`).
///
/// **Pinned** by `Hachi/Params.lean`'s `mu0_eq : mu0 = 57344`
/// (`= `[`RLIN_CW`]` + (`[`RLIN_CT`]` + `[`RLIN_CZ`]`)`, with the parenthesization
/// the spec fixes). `81920` under `τ = 8`; `49152` under `τ = 4`.
pub const RLIN_COLS: usize = 57_344;

// @genesis a898de7 2026-09-04 — params::RLIN_ROWS
/// The row count `n₀` of the Eq. (20) block system, the stacked rows
/// `c1 ++ (c2 ++ (c3 ++ (c4 ++ c5)))`: `rlinRows n_A n_B n_D = n_D + (n_B + (1 +
/// (1 + n_A))) = 5` (`RingSwitch/Rlin.lean`).
///
/// **Derived** from [`D_ROWS`], [`OUTER_ROWS`], [`INNER_ROWS`]; also the number
/// of quotient-block rows the ring switch commits as digits, hence the `n₀` in
/// [`LIFT_COLS`] and the row count [`M_ONE`] must cover.
pub const RLIN_ROWS: usize = 5;

// @genesis a898de7 2026-09-04 — params::D_QUAD_COLS
/// The column count of the QuadEval short-commitment matrix `D`:
/// `blocks · messageDigits = 8192`, the width of the carrier decomposition `ŵ`
/// it commits to (`PublicParamsD.dMatrix : Simple.PublicParams Φ dRows (blocks
/// * messageDigits)`, `QuadEval/Gadgets.lean`).
///
/// **Derived** from [`BLOCKS`]` · `[`GADGET_DIGITS`]. Numerically [`RLIN_CW`],
/// and deliberately a separate name: one is a matrix width, the other a block
/// offset inside `ζ`.
pub const D_QUAD_COLS: usize = 8192;

// @genesis a898de7 2026-09-04 — params::LIFT_COLS
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

// @genesis a898de7 2026-09-04 — params::M_ZERO
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

// @genesis a898de7 2026-09-04 — params::M_ONE
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

// @genesis b984c53 2026-09-04 — params::SB_HI
/// The upper endpoint of the paper's balanced digit box
/// `S_b = [⌈-b/2⌉, ⌈b/2⌉ - 1] = [-8, 7]` (Eq. (20)'s exact range check,
/// `InSb` in `QuadEval/Reduction.lean`).
///
/// **Derived**: `(β + 1) / 2 - 1` at `β := b = 16`, in `ℕ` division and `ℕ`
/// subtraction. A literal for the usual extraction reason -- a `const`-derived
/// truncated subtraction reaches Lean through `Result` -- and, unlike most
/// derived constants here, it also has no other spelling: `⌈b/2⌉ - 1` is not
/// `GADGET_BASE - 1 - HALF_BASE` by definition, only by arithmetic at this `b`.
///
/// The box's *lower* endpoint needs no constant of its own: it is `β / 2` at
/// `β = b`, which **is** [`HALF_BASE`]. The two are the same quantity `⌊b/2⌋`,
/// not a collision -- so `lean/Check.lean` § 1 ties the pair once and
/// `params.rs` names 8 once.
///
/// Note the box is *asymmetric*: `-8` is admissible and `+8` is not. A check
/// written on a magnitude cannot express it, which is exactly why `in_sb` has
/// to branch on the sign of the centered representative.
pub const SB_HI: u64 = 7;

// @genesis 6b228c5 2026-09-08 — params::ROUND_NODES
/// The number of Lagrange nodes a round message is sampled at: `2b + 1 = 33`,
/// one more than the per-round degree bound `roundDegZero b = 2b`
/// (`ZeroCheck/Constraints.lean:87`), which is what makes the interpolant
/// unique. The nodes themselves are `0, 1, …, 2b`, and the first two are the
/// ones `roundCheck` evaluates (`Sumcheck/Rounds.lean:100`).
///
/// **Derived** from [`GADGET_BASE`]: `2 · 16 + 1`. A literal for the usual
/// reason -- a `const` arithmetic expression is a `Result` in every Lean use of
/// it -- with the relation checked in `tests/sumcheck_semantics.rs`.
pub const ROUND_NODES: usize = 33;

// @genesis 6b228c5 2026-09-08 — params::ROUND_NODE_INV
/// The Lagrange interpolation weights for those nodes: entry `i` is
/// `(∏_{j ≠ i} (i - j))⁻¹` in `F_q`, over the nodes `0 … 2b`.
///
/// **Derived**, and precomputed because it cannot be computed here: `cpoly`
/// exposes no inversion for `Fp` or `Ext4` -- no `inv`, no `pow`, no `Div` --
/// and reimplementing the field layer is forbidden (`lib.rs` § the cpoly
/// dependency). Precomputing is also *sufficient*, which is the point: the
/// nodes are small integers, so every denominator `∏_{j≠i}(i-j)` is an integer
/// and its inverse lives in the **base** field, never in the extension. So a
/// round message is interpolated by multiplying `Ext4` values by embedded `Fp`
/// literals, and no inversion happens at runtime at any carrier.
///
/// Each entry is checked against its denominator in
/// `tests/sumcheck_semantics.rs` (`w_i · ∏_{j≠i}(i-j) = 1`), which is what
/// makes these numbers auditable rather than magic.
pub const ROUND_NODE_INV: [u64; ROUND_NODES] = [
    2_585_773_906, 3_154_578_948, 2_643_632_670,
    3_628_443_679, 2_684_811_907, 426_935_230,
    2_373_758_662, 386_683_249, 1_475_969_345,
    1_790_704_676, 1_894_333_321, 506_300_555,
    187_715_828, 2_023_881_063, 627_921_355,
    3_541_461_571, 263_728_828, 3_541_461_571,
    627_921_355, 2_023_881_063, 187_715_828,
    506_300_555, 1_894_333_321, 1_790_704_676,
    1_475_969_345, 386_683_249, 2_373_758_662,
    426_935_230, 2_684_811_907, 3_628_443_679,
    2_643_632_670, 3_154_578_948, 2_585_773_906,
];

// @genesis 2152e10 2026-09-09 — params::ROUND_NODES_ALPHA
/// The number of Lagrange nodes the **linear** round message is sampled at:
/// `roundDegAlpha + 1 = 3`, since `sumcheckPolyAlpha` is a product of two
/// multilinears and so has per-round degree `roundDegAlpha = 2`
/// (`ZeroCheck/Constraints.lean:90`). The nodes are `0, 1, 2`.
///
/// **Derived**, a literal for the reason [`ROUND_NODES`] is. Kept separate from
/// [`ROUND_NODES`] rather than reusing a prefix of it, because the
/// interpolation weights of a node *set* depend on the whole set: the weights
/// for `{0, 1, 2}` are not the first three entries of [`ROUND_NODE_INV`], which
/// belong to `{0, …, 32}`. Reusing them would be a silent wrong answer, which
/// is why the two arrays are named and tested separately.
pub const ROUND_NODES_ALPHA: usize = 3;

// @genesis 2152e10 2026-09-09 — params::ROUND_NODE_INV_ALPHA
/// The Lagrange interpolation weights for the nodes `0, 1, 2`: entry `i` is
/// `(∏_{j ≠ i} (i - j))⁻¹` in `F_q`.
///
/// **Derived**, precomputed for the reason [`ROUND_NODE_INV`] is. The
/// denominators are `(0-1)(0-2) = 2`, `(1-0)(1-2) = -1` and `(2-0)(2-1) = 2`,
/// so the entries are `2⁻¹ = (q+1)/2`, `-1 = q-1` and `2⁻¹` again — checked
/// against those denominators in `tests/sumcheck_semantics.rs` by the same
/// `w_i · ∏_{j≠i}(i-j) = 1` test that checks the range side.
pub const ROUND_NODE_INV_ALPHA: [u64; ROUND_NODES_ALPHA] =
    [2_147_483_599, 4_294_967_196, 2_147_483_599];

// @genesis 369dcae 2026-09-16 — params::RANGE_Q_COEFFS
/// The 16 coefficients of `Q(x) = ∏_{j=1}^{b−1} (x − j²)`, least significant
/// first, reduced mod [`Q`] (Stage 6 candidate T2a).
///
/// The range factor of the zero check is
/// `P_b(v) = v · ∏_{j=1}^{b−1} (v² − j²) = v · Q(v²)`, and candidate F already
/// rewrote it into that shape. `Q` is a *fixed* degree-15 polynomial once `b` is
/// pinned, so its coefficients are constants rather than something to recompute
/// per evaluation: they are the signed elementary symmetric functions of
/// `{1, 4, 9, …, 225}`, `a_k = (−1)^{15−k} e_{15−k}`, and the exact integers run
/// to 25 digits before reduction (`a_0 = −1 710 012 252 724 199 424 000 000`).
///
/// **Pinned to `GADGET_BASE = 16` and to nothing else.** Change `b` and every
/// entry here is wrong; `params_semantics::range_q_coeffs_are_the_product_form`
/// is what keeps the two in step, by rebuilding the product from `GADGET_BASE`
/// and comparing. That test is the reason this is a literal table and not a
/// `const fn`: the extraction has no `const fn`, and a literal that a test
/// checks is worth more than a computation the model cannot see.
///
/// `a_15 = 1` (the product is monic) and `a_14 = −Σ j² = −1240 ≡ q − 1240`.
pub const RANGE_Q_COEFFS: [u64; 16] = [
    3_482_634_775,
    2_503_758_464,
    2_571_177_710,
    2_088_262_913,
    1_336_916_483,
    2_390_189_385,
    593_857_483,
    4_019_711_691,
    895_573_040,
    2_269_934_483,
    1_661_002_130,
    2_173_484_420,
    4_077_588_997,
    679_644,
    4_294_965_957,
    1,
];


// @genesis dd3386a 2026-09-19 — params::SHIFT_DEG
/// The number of coefficients of `P_b`: `2b = 32`, one per degree `0 … 2b − 1`.
///
/// `P_b` has degree `2b − 1 = 31`, so a Taylor shift of it has `32`
/// coefficients — one fewer than [`ROUND_NODES`], which is `2b + 1`. The two
/// are different counts for different reasons and `params_semantics` checks
/// both against [`GADGET_BASE`].
pub const SHIFT_DEG: usize = 32;

// @genesis dd3386a 2026-09-19 — params::SHIFT_ROWS
/// The number of **nonzero** coefficients of `P_b`: `b = 16`.
///
/// `P_b(v) = v · Q(v²)` is odd, so `p_k = 0` for even `k` and the `b` nonzero
/// coefficients sit at `k = 1, 3, …, 2b − 1`. [`SHIFT_T`] stores one row per
/// such `k` rather than one per degree, which halves it.
pub const SHIFT_ROWS: usize = 16;

// @genesis dd3386a 2026-09-19 — params::SHIFT_T_LEN
/// [`SHIFT_T`]'s length, `SHIFT_ROWS · SHIFT_DEG`.
///
/// A literal for the reason [`ROUND_NODES`] is: a product is a `Result` in the
/// extracted model, so it cannot be an array length. The relation is checked by
/// `params_semantics::shift_t_is_the_binomial_table`.
pub const SHIFT_T_LEN: usize = 512;

// @genesis dd3386a 2026-09-19 — params::SHIFT_T
/// The Taylor-shift table `T[j][m] = p_{2j+1} · C(2j+1, m)`, flattened to
/// `j · SHIFT_DEG + m` (Stage 6 candidate T3).
///
/// The one fact the shifted round polynomial needs. Writing `P_b(lo + Δ·X)` in
/// `X` gives, by the binomial theorem,
///
/// ```text
///   P_b(lo + Δ X) = Σ_m Δ^m X^m · Σ_{k ≥ m} p_k · C(k, m) · lo^{k−m}
/// ```
///
/// and the inner sum is this table contracted against the powers of `lo`. Only
/// odd `k` appear because `P_b` is odd, which is why the row index is
/// `j = (k − 1) / 2` and there are [`SHIFT_ROWS`] rows and not [`SHIFT_DEG`].
/// Entries with `m > k` are never read — the `m` loop starts at `j = m / 2`,
/// and `2·(m/2) + 1 ≥ m` for every `m` — and are zero.
///
/// **Pinned to `GADGET_BASE = 16`**, exactly as [`RANGE_Q_COEFFS`] is, and for
/// the same reason: `p_{2j+1} = RANGE_Q_COEFFS[j]`.
/// `params_semantics::shift_t_is_the_binomial_table` rebuilds every entry from
/// [`RANGE_Q_COEFFS`] and Pascal's triangle and compares. The largest binomial
/// here is `C(31, 15) = 300 540 195`, well inside `Q`, so no entry needed
/// reducing before multiplication.
pub const SHIFT_T: [u64; SHIFT_T_LEN] = [
    // k = 1
    3482634775, 3482634775, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    // k = 3
    2503758464, 3216308195, 3216308195, 2503758464,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    // k = 5
    2571177710, 4265954156, 4236941115, 4236941115,
    4265954156, 2571177710, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    // k = 7
    2088262913, 1732938800, 903849203, 74759606,
    74759606, 903849203, 1732938800, 2088262913,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    // k = 9
    1336916483, 3442313953, 884354221, 631837450,
    947756175, 947756175, 631837450, 884354221,
    3442313953, 1336916483, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    // k = 11
    2390189385, 522280053, 2611400265, 3539233598,
    2783499999, 460926241, 460926241, 2783499999,
    3539233598, 2611400265, 522280053, 2390189385,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    // k = 13
    593857483, 3425180082, 3371211704, 2339519455,
    3701315039, 4085386752, 1152215139, 1152215139,
    4085386752, 3701315039, 2339519455, 3371211704,
    3425180082, 593857483, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    // k = 15
    4019711691, 166134607, 1162942249, 3607760680,
    2233347646, 2336384503, 1030662707, 2552271251,
    2552271251, 1030662707, 2336384503, 2233347646,
    3607760680, 1162942249, 166134607, 4019711691,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    // k = 17
    895573040, 2339840089, 1538851924, 3399292423,
    1160105488, 1298287390, 2596574780, 1012498085,
    191880807, 191880807, 1012498085, 2596574780,
    1298287390, 1160105488, 3399292423, 1538851924,
    2339840089, 895573040, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    // k = 19
    2269934483, 179083207, 1611748863, 543309163,
    2173236652, 2224742759, 2327754973, 2482273294,
    3723409941, 3119178640, 3119178640, 3723409941,
    2482273294, 2327754973, 2224742759, 2173236652,
    543309163, 1611748863, 179083207, 2269934483,
    0, 0, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    // k = 21
    1661002130, 521307154, 918104343, 1519693642,
    2543654192, 2635470177, 2732953275, 947794507,
    584898588, 844853516, 2731811098, 2731811098,
    844853516, 584898588, 947794507, 2732953275,
    2635470177, 2543654192, 1519693642, 918104343,
    521307154, 1661002130, 0, 0,
    0, 0, 0, 0,
    0, 0, 0, 0,
    // k = 23
    2173484420, 2745502493, 135757044, 950299308,
    456529343, 875818064, 2627454192, 2699559726,
    1104152255, 408598026, 4008010994, 832224632,
    832224632, 4008010994, 408598026, 1104152255,
    2699559726, 2627454192, 875818064, 456529343,
    950299308, 135757044, 2745502493, 2173484420,
    0, 0, 0, 0,
    0, 0, 0, 0,
    // k = 25
    4077588997, 3155479394, 3506015152, 2541302049,
    3239743277, 4157993930, 2406733908, 2851163010,
    4267633174, 1380024800, 2208039680, 3010963200,
    3512790400, 3512790400, 3010963200, 2208039680,
    1380024800, 4267633174, 2851163010, 2406733908,
    4157993930, 3239743277, 2541302049, 3506015152,
    3155479394, 4077588997, 0, 0,
    0, 0, 0, 0,
    // k = 27
    679644, 18350388, 238555044, 1987958700,
    3337817806, 3328053756, 3612929378, 2248853740,
    1327167153, 2801797323, 4184241742, 609781969,
    3676354090, 277361922, 277361922, 3676354090,
    609781969, 4184241742, 2801797323, 1327167153,
    2248853740, 3612929378, 3328053756, 3337817806,
    1987958700, 238555044, 18350388, 679644,
    0, 0, 0, 0,
    // k = 29
    4294965957, 4294931237, 4294463757, 4290436237,
    4265515957, 4147710997, 3705942397, 2359599997,
    3267674594, 466295391, 932590782, 49032370,
    73548555, 1748089340, 2611383131, 2611383131,
    1748089340, 73548555, 49032370, 932590782,
    466295391, 3267674594, 2359599997, 3705942397,
    4147710997, 4265515957, 4290436237, 4294463757,
    4294931237, 4294965957, 0, 0,
    // k = 31
    1, 31, 465, 4495,
    31465, 169911, 736281, 2629575,
    7888725, 20160075, 44352165, 84672315,
    141120525, 206253075, 265182525, 300540195,
    300540195, 265182525, 206253075, 141120525,
    84672315, 44352165, 20160075, 7888725,
    2629575, 736281, 169911, 31465,
    4495, 465, 31, 1,
];


// @genesis a52d433 2026-09-19 — params::SHORT_CHUNK
/// How many passes [`crate::ring::mul_short_add_into`] accumulates before it
/// reduces (Stage 6 candidate T33).
///
/// The short multiply adds one signed shifted copy of its operand per pass,
/// so a slot grows by at most `Q` per pass. Reducing every `SHORT_CHUNK`
/// passes keeps every slot below `(SHORT_CHUNK + 1)·Q = 1.4 × 10¹¹`, which is
/// a `u64` with eight orders of magnitude to spare — **for any description**,
/// which is the point: the alternative was a `Σ mag ≤ OMEGA` hypothesis on
/// `mul_short_add_into_spec`, a new value-level precondition.
///
/// `32 > OMEGA = 16`, so at the paper's parameters the inner reduction never
/// fires: a `classify_short` description has `Σ mag ≤ OMEGA`, and the whole
/// call is one deferred pass with a single reduction at the end. The constant
/// buys unconditional totality and costs nothing at the pin.
pub const SHORT_CHUNK: u64 = 32;
