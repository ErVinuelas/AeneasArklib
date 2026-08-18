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
/// **Chosen.** The spec (`InnerOuter/Arithmetic.lean`, `hachiModulus q α`) admits
/// any `α`. The ring degree `2^α` is the width of every coefficient vector in
/// this crate, so it is a performance parameter as much as a security one;
/// `α = 6` gives the degree-64 ring that the Greyhound/Hachi line of work uses.
/// See NOTES.md § "Chosen parameters" -- this is the value most likely to be
/// revised once the concrete parameter set is fixed.
pub const RING_LOG_DEGREE: usize = 6;

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

/// The gadget base `b`.
///
/// **Chosen**, but constrained: `Gadget/Core.lean`'s `zmodDigitDecomposition`
/// requires `1 < b`, and `Gadget/Norms.lean`'s shortness bounds are stated in
/// terms of it. `b = 2` is the binary gadget, which gives the shortest digits
/// (each in `{0, 1}`) at the cost of the most of them.
pub const GADGET_BASE: u64 = 2;

/// The gadget digit count `digits`.
///
/// **Chosen**, and it is the choice that discharges the spec's side condition:
/// `zmodDigitDecomposition` needs `q ≤ b ^ digits` so that every residue fits in
/// `digits` base-`b` digits. Here `2^32 = 4294967296 ≥ 4294967197 = q`, with 99
/// to spare -- so 32 binary digits are exactly enough, and 31 would not be.
pub const GADGET_DIGITS: usize = 32;
