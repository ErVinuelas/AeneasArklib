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
//! Two of the four groups below are pinned by something outside this crate; two
//! are choices this crate makes. The distinction matters when reading a proof:
//! a pinned value cannot move without breaking a dependency, while a chosen one
//! can, and the spec-side hypothesis it has to satisfy is recorded with it.

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

// @genesis 4409640 2026-08-18 — params::RING_LOG_DEGREE
/// The cyclotomic index `α`: the commitment ring is
/// `R_q = Z_q[X] / (X^{2^α} + 1)`.
///
/// **Chosen.** The spec (`InnerOuter/Arithmetic.lean`, `hachiModulus q α`) admits
/// any `α`. The ring degree `2^α` is the width of every coefficient vector in
/// this crate, so it is a performance parameter as much as a security one;
/// `α = 6` gives the degree-64 ring that the Greyhound/Hachi line of work uses.
/// See NOTES.md § "Chosen parameters" -- this is the value most likely to be
/// revised once the concrete parameter set is fixed.
pub const RING_LOG_DEGREE: usize = 6;

// @genesis 4409640 2026-08-18 — params::RING_DEGREE
/// The ring degree `2^α = 64`: the number of `Z_q` coefficients in one element of
/// `R_q`.
///
/// A literal, not `1 << RING_LOG_DEGREE`, and that is an extraction concession
/// rather than a preference: Aeneas models a shift as fallible, so the shifted
/// form extracts as `Result Std.Usize` and every Lean use of it would have to
/// bind and discharge a side condition that is plainly true. As a literal it
/// extracts as `def params.RING_DEGREE : Std.Usize := 64#usize`.
///
/// `params_semantics::ring_degree_is_a_power_of_two` is what keeps the two in
/// step; see NOTES.md § "Aeneas surprises".
pub const RING_DEGREE: usize = 64;

// @genesis 4409640 2026-08-18 — params::GADGET_BASE
/// The gadget base `b`.
///
/// **Chosen**, but constrained: `Gadget/Core.lean`'s `zmodDigitDecomposition`
/// requires `1 < b`, and `Gadget/Norms.lean`'s shortness bounds are stated in
/// terms of it. `b = 2` is the binary gadget, which gives the shortest digits
/// (each in `{0, 1}`) at the cost of the most of them.
pub const GADGET_BASE: u64 = 2;

// @genesis 4409640 2026-08-18 — params::GADGET_DIGITS
/// The gadget digit count `digits`.
///
/// **Chosen**, and it is the choice that discharges the spec's side condition:
/// `zmodDigitDecomposition` needs `q ≤ b ^ digits` so that every residue fits in
/// `digits` base-`b` digits. Here `2^32 = 4294967296 ≥ 4294967197 = q`, with 99
/// to spare -- so 32 binary digits are exactly enough, and 31 would not be.
///
/// The specification carries *two* digit counts, `messageDigits` and
/// `innerDigits` (`InnerOuter/Scheme.lean`), and admits different values for
/// them. Here they coincide, and not by preference: both decompositions are of
/// `Rq` elements over the same `ZMod q`, so both need `q ≤ b ^ digits`, and at
/// `b = 2` that forces 32 on each. One constant therefore serves both; see
/// NOTES.md § "One digit count, not two".
pub const GADGET_DIGITS: usize = 32;

// @genesis d664190 2026-08-19 — params::MESSAGE_ROWS
/// The number of `R_q` rows in one message block: `messageRows` of the
/// specification.
///
/// **Chosen.** This and the four dimensions below are the shapes of the two
/// Ajtai matrices, which the specification leaves entirely free
/// (`PublicParams`, `InnerOuter/Scheme.lean:94`, is generic in all six). They
/// are the *smallest* values that still exercise every index computation in the
/// scheme -- more than one row, more than one block, and a gadget expansion
/// wide enough to be worth flattening -- rather than a security-grade parameter
/// set, which needs [NOZ26]'s ℓ=30 table (NOTES.md § "Chosen parameters").
pub const MESSAGE_ROWS: usize = 4;

// @genesis d664190 2026-08-19 — params::INNER_ROWS
/// The number of `R_q` rows the inner Ajtai matrix `A` produces: `innerRows`.
///
/// **Chosen** (see [`MESSAGE_ROWS`]). `A` is `INNER_ROWS × (MESSAGE_ROWS *
/// GADGET_DIGITS)`, i.e. `2 × 128` here.
pub const INNER_ROWS: usize = 2;

// @genesis d664190 2026-08-19 — params::OUTER_ROWS
/// The number of `R_q` rows the outer Ajtai matrix `B` produces: `outerRows`.
///
/// **Chosen** (see [`MESSAGE_ROWS`]). `B` is `OUTER_ROWS × (BLOCKS *
/// (INNER_ROWS * GADGET_DIGITS))`, i.e. `2 × 128` here. The commitment is a
/// vector of this many ring elements.
pub const OUTER_ROWS: usize = 2;

// @genesis d664190 2026-08-19 — params::BLOCKS
/// The number of message blocks committed together: `blocks`.
///
/// **Chosen** (see [`MESSAGE_ROWS`]). Must exceed 1 for the per-block loop of
/// `verify_weak` and the block flattening of `commitWithDecomps` to be doing
/// anything.
pub const BLOCKS: usize = 2;

// @genesis d664190 2026-08-19 — params::GAMMA
/// The `ℓ∞` bound `γ` on the flattened inner decomposition, checked by
/// `verify_weak`.
///
/// **Derived**, not chosen: `Gadget/Norms.lean`'s
/// `gadgetDecompose_zmod_vecLInftyNorm_le` proves the honest decomposition
/// satisfies `‖t̂‖∞ ≤ b - 1`, and at `b = 2` that is `1`. Every digit of a
/// binary decomposition is `0` or `1`, and the centered view leaves both alone,
/// so this is exact rather than slack -- an honest opening sits on the bound.
///
/// A literal `1` rather than `GADGET_BASE - 1`, for the reason
/// [`RING_DEGREE`] is a literal: Aeneas models a `const` subtraction as
/// fallible, so the derived form would extract as `Result Std.U64` and every
/// Lean use would carry a side condition that is plainly true. The relation to
/// [`GADGET_BASE`] is checked instead, in `tests/params_semantics.rs` and
/// `lean/Check.lean` § 1.
pub const GAMMA: u64 = 1;

// @genesis d664190 2026-08-19 — params::BETA_SQ
/// The squared-`ℓ₂` bound `βSq` on the challenge-scaled message, checked by
/// `verify_weak`.
///
/// **Derived** from the same file: `gadgetDecompose_zmod_vecL2NormSq_le` bounds
/// the honest per-block decomposition by
/// `(messageRows · messageDigits) · (deg φ) · (b - 1)²`, which here is
/// `4 · 32 · 64 · 1 = 8192`. The honest challenge is `c = 1`, and scaling by it
/// changes nothing, so this is the bound the honest committer meets.
///
/// A literal, for the reason [`GAMMA`] is one; the product it stands for is
/// checked in `tests/params_semantics.rs` and `lean/Check.lean` § 1.
///
/// `u128`, not `u64`, because that is the width the norm itself is computed at:
/// a single centered coefficient can be as large as `q/2`, so one squared
/// coefficient approaches `2^62` and a vector of them overflows `u64`. See
/// `commit::vec_l2_norm_sq`.
pub const BETA_SQ: u128 = 8_192;

// @genesis d664190 2026-08-19 — params::KAPPA
/// The `ℓ₁` bound `κ` on a challenge, checked by `verify_weak`.
///
/// **Chosen at its ceiling.** The specification's only constraint on `κ` is the
/// one it needs for the challenge to be *invertible*, which is what a weak
/// opening really requires ([NOZ26] §4.1): `isUnit_of_l1Norm_le`
/// (`NormBounds/LyubashevskySeiler.lean:344`) turns `0 < ‖c‖₁ ≤ κ` into
/// `IsUnit c` provided `q % 8 = 5` and `κ² < q`. Here `q % 8 = 5` holds, and
/// `κ² < q` caps `κ` at `⌊√q⌋ = 65535`.
///
/// `κ` is a *rejection* threshold, so this is the most permissive legal value:
/// anything larger would admit challenges the invertibility lemma cannot cover.
/// The protocol layer (out of scope here -- its Lean spec is not frozen) is what
/// will lower it to the sparse challenges an actual reduction samples; the
/// honest challenge `c = 1` has `‖1‖₁ = 1` and passes either way.
pub const KAPPA: u64 = 65_535;
