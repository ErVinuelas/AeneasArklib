//! The base-`b` Ajtai gadget: digit decomposition, the gadget matrix `G`, and
//! its norm-reducing inverse `G⁻¹`.
//!
//! Reference specification: `ArkLib/Commitments/Functional/Hachi/Gadget/Core.lean`,
//! with the shortness bounds in `Gadget/Norms.lean`.
//!
//! `G = I_rows ⊗ [1, b, …, b^(digits-1)]` maps `rows · digits` ring elements to
//! `rows` of them, and `G⁻¹` goes back by writing each *coefficient* of each
//! entry in base `b`. Trading one ring element for `digits` elements with small
//! coefficients is what keeps an honest Ajtai opening short; the whole point of
//! the gadget is that `G · G⁻¹(x) = x` while `G⁻¹(x)` has tiny norm.
//!
//! # Two digit maps: the unsigned primitive, and the balanced gadget inverse
//!
//! [`digit_at`] is the *unsigned* base-`b` digit map, the specification's
//! `zmodDigitDecomposition` (`Gadget/Core.lean:139`):
//!
//! ```text
//! digit c e = ((Nat.digits b c.val).getD e 0 : ZMod q)
//! ```
//!
//! i.e. the ordinary base-`b` digits of the *canonical* representative
//! `c.val ∈ [0, q)`, each in `{0, …, b-1}`. At the pinned ArkLib this is
//! explicitly **not** a Hachi gadget inverse -- [NOZ26] §2.1 writes digits in
//! the balanced box `S_b`, `⌈-b/2⌉ ≤ dᵢ ≤ ⌈b/2⌉ - 1`, which unsigned digits
//! violate (at `b = 16`, `[0, 15]` against `[-8, 7]`) -- but the building block
//! the balanced digits are shifted from. Its own centered bound is `b - 1 = 15`
//! (`Gadget/Norms.lean`), under the side condition `b - 1 ≤ q/2` that stops a
//! small non-negative digit from wrapping to a negative representative.
//!
//! [`balanced_digit_at`] is the gadget inverse `G⁻¹` proper, the spec's
//! `balancedZmodDigitDecomposition` (`:174`): one **field** add of
//! [`params::BALANCED_SHIFT`], one unsigned digit read, one **field** subtract
//! of [`params::HALF_BASE`]. The shift must be a field addition and not a raw
//! `u64` one -- the raw sum can reach `6585616420 ≥ 16^8`, which has nine
//! base-16 digits where the spec's `(c + shift).val < q` has eight, and the top
//! digit would come out wrong. [`balanced_gadget_decompose`] is
//! `gadgetDecompose` at it, and that is the decomposition `Hachi.commit`
//! (`Commitment.lean:111`) and [`crate::commit::commit_balanced`] use.
//!
//! Both layers stay. `InnerOuter/Scheme.lean` is generic in the decomposition
//! (`Decomposition.ofDigits`, `:130`), so the unsigned functions are the
//! primitives the balanced ones are built from and the ones the existing
//! equivalence proofs target; the balanced ones are the paper's. See NOTES.md
//! § "The digits are not balanced".
//!
//! A balanced digit is a *residue*, not a small integer: the digit `-8` is
//! `Fp(q - 8)`. Anything that reads one as a magnitude must go through the
//! centered view ([`crate::commit::centered_abs`], the spec's `ZMod.valMinAbs`),
//! which is what every bound in `Gadget/Norms.lean` is stated on. A range check
//! written as `d.to_u64() <= 7` would silently reject every negative digit.
//!
//! # The folded witness has its own, shorter digit map
//!
//! [`bounded_z_digit_at`] is `boundedBalancedZmodDigit` (`:278`) at
//! [`params::Z_DIGITS`]` = 5`, for the folded response `ẑ`. It is not a
//! `DigitDecomposition` and cannot be: `16^5 < q`, so no five-digit
//! decomposition of *every* residue exists. It centres **first**
//! (`ZMod.valMinAbs`), shifts in `ℤ` by [`params::Z_BALANCED_SHIFT`], clamps a
//! too-negative result to `0` (`Int.toNat`), and only then takes five unsigned
//! digits -- the reverse order of the message digit's shift-then-`.val`, and an
//! integer shift of a signed value rather than a field add. Its range is
//! unconditional (the same box `[-8, 7]`); its *reconstruction* law holds only
//! for inputs within [`params::Z_BOUND`].
//!
//! # Index layout
//!
//! Slot `e` of block `i` is flat index `digits·i + e`, per `finProdFinEquiv`
//! (see [`crate::linalg`]'s module header). Both `gadget_mul` and
//! `gadget_decompose` are written directly against that layout rather than
//! against a general matrix product: the specification's `gadgetMul_apply`
//! (`Gadget/Core.lean:429`) proves the general product collapses to exactly this
//! per-block digit sum, which is what makes the direct form the honest one to
//! implement -- and `O(rows · digits)` work instead of `O(rows² · digits)`.

use alloc::vec::Vec;
use cpoly::Fp;

use crate::linalg::{PolyMatrix, PolyVec};
use crate::params;
use crate::ring::Rq;

/// The `e`-th base-`b` digit of a field element (spec:
/// `zmodDigitDecomposition.digit c e`, `Gadget/Core.lean:141`).
///
/// Mirrors ArkLib's `zmodDigitDecomposition.digit` at one `e`.
///
/// `⌊c / bᵉ⌋ mod b`, computed by repeated division so that no power of `b` is
/// ever formed -- `b^digits` can exceed the modulus, and `Nat.digits` on the spec
/// side never forms it either.
///
/// Agrees with the spec at *every* `e`, not just below the digit length: for
/// `e` past the length of `Nat.digits b c.val` the spec's `getD` returns its `0`
/// default, and so does the division here once the quotient has run out.
pub fn digit_at(c: Fp, e: usize) -> Fp {
    let b: u64 = params::GADGET_BASE;
    let mut rest: u64 = c.to_u64();
    let mut i: usize = 0;
    while i < e {
        rest = rest / b;
        i += 1;
    }
    Fp::new(rest % b)
}

/// All [`params::GADGET_DIGITS`] digits of a field element, little-endian (spec:
/// the `digit` field of `zmodDigitDecomposition` as a whole).
///
/// Mirrors ArkLib's `zmodDigitDecomposition.digit` at every `e < digits`, as
/// one vector.
///
/// The reconstruction law `Σₑ bᵉ · digit c e = c` (the `reconstruct` field of
/// `DigitDecomposition`) is what makes this a decomposition rather than an
/// arbitrary map, and it needs `q ≤ b ^ digits`; [`params::GADGET_DIGITS`]
/// records that this holds here.
pub fn digit_decompose(c: Fp) -> Vec<Fp> {
    let digits: usize = params::GADGET_DIGITS;
    let mut out: Vec<Fp> = Vec::new();
    let mut e: usize = 0;
    while e < digits {
        out.push(digit_at(c, e));
        e += 1;
    }
    out
}

/// `bᵉ` in the coefficient field.
///
/// Modular, by repeated multiplication: the spec's `base ^ e` is a power taken in
/// `ZMod q`, so a `u64` power would be a different function as soon as `bᵉ`
/// reaches the modulus.
pub fn base_pow(e: usize) -> Fp {
    let b: Fp = Fp::new(params::GADGET_BASE);
    let mut acc: Fp = Fp::ONE;
    let mut i: usize = 0;
    while i < e {
        acc = acc * b;
        i += 1;
    }
    acc
}

/// Entry `(i, j)` of the gadget matrix (spec: `gadgetEntry`,
/// `Gadget/Core.lean:391`): the ring constant `C(b^(j mod digits))` when
/// `j / digits = i`, and `0` otherwise.
///
/// Mirrors ArkLib's `gadgetEntry`.
pub fn gadget_entry(i: usize, j: usize) -> Rq {
    let digits: usize = params::GADGET_DIGITS;
    if j / digits == i {
        Rq::constant(base_pow(j % digits))
    } else {
        Rq::zero()
    }
}

/// The gadget matrix `G = I_rows ⊗ [1, b, …, b^(digits-1)]`, of shape
/// `rows × (rows · digits)` (spec: `gadgetMatrix`, `Gadget/Core.lean:395`).
///
/// Mirrors ArkLib's `gadgetMatrix`.
///
/// Materialized only where the specification materializes it: `verify_weak`
/// checks `A sᵢ = G t̂ᵢ` by passing `gadgetMatrix Φ base innerRows innerDigits`
/// to `Simple.verify`, i.e. as an ordinary Ajtai matrix. [`gadget_mul`] is the
/// structured form to use everywhere else.
pub fn gadget_matrix(rows: usize) -> PolyMatrix {
    let digits: usize = params::GADGET_DIGITS;
    let cols: usize = rows * digits;
    let mut out: Vec<PolyVec> = Vec::new();
    let mut i: usize = 0;
    while i < rows {
        let mut row: Vec<Rq> = Vec::new();
        let mut j: usize = 0;
        while j < cols {
            row.push(gadget_entry(i, j));
            j += 1;
        }
        out.push(PolyVec::new(row));
        i += 1;
    }
    PolyMatrix::new(out)
}

/// The gadget product `G · v` (spec: `gadgetMul`, `Gadget/Core.lean:399`).
///
/// Mirrors ArkLib's `gadgetMul`.
///
/// Row `i` is `Σ_{e<digits} bᵉ · v[digits·i + e]`, which is the specification's
/// `gadgetMul_apply` (`:429`) read as a definition. Multiplication by the ring
/// constant `C(bᵉ)` is coefficientwise scaling by `bᵉ`, which is the spec's
/// `constRq_mul_coeff`, so this uses [`Rq::scalar_mul`] rather than a full ring
/// product.
///
/// `v` is expected to have `rows · digits` entries.
pub fn gadget_mul(rows: usize, v: &PolyVec) -> PolyVec {
    let digits: usize = params::GADGET_DIGITS;
    let mut out: Vec<Rq> = Vec::new();
    let mut i: usize = 0;
    while i < rows {
        let mut acc: Rq = Rq::zero();
        let mut e: usize = 0;
        while e < digits {
            let scaled: Rq = v.get(digits * i + e).scalar_mul(base_pow(e));
            acc = acc.add(&scaled);
            e += 1;
        }
        out.push(acc);
        i += 1;
    }
    PolyVec::new(out)
}

/// The gadget inverse `G⁻¹` (spec: `gadgetDecompose`, `Gadget/Core.lean:518`,
/// instantiated at `zmodDigitDecomposition`).
///
/// Mirrors ArkLib's `gadgetDecompose` at `zmodDigitDecomposition`.
///
/// Slot `e` of block `i` is the ring element whose `k`-th coefficient is the
/// `e`-th digit of the `k`-th coefficient of `x[i]`. The output has
/// `x.len() · digits` entries, and `gadget_mul(x.len(), ·)` inverts it -- the
/// specification's `IsLawfulGadgetDecomposition` (`:404`), proved of this
/// decomposition in `gadgetDecompose_lawful` (`:523`).
pub fn gadget_decompose(x: &PolyVec) -> PolyVec {
    let digits: usize = params::GADGET_DIGITS;
    let degree: usize = params::RING_DEGREE;
    let rows: usize = x.len();
    let mut out: Vec<Rq> = Vec::new();
    let mut i: usize = 0;
    while i < rows {
        let mut e: usize = 0;
        while e < digits {
            let mut coeffs: Vec<Fp> = Vec::new();
            let mut k: usize = 0;
            while k < degree {
                coeffs.push(digit_at(x.get(i).coeff(k), e));
                k += 1;
            }
            out.push(Rq::from_coeffs(&coeffs));
            e += 1;
        }
        i += 1;
    }
    PolyVec::new(out)
}

// ---------------------------------------------------------------------------
// The balanced layer: the Hachi gadget inverse `G⁻¹`
// ---------------------------------------------------------------------------

/// The `e`-th *balanced* base-`b` digit of a field element (spec:
/// `balancedDigit b digits c e`, `RingSwitch/RhoDigits.lean:79`, which is by
/// `rfl` the `digit` field of `balancedZmodDigitDecomposition`,
/// `Gadget/Core.lean:174`).
///
/// Mirrors ArkLib's `balancedZmodDigitDecomposition.digit` at one `e`.
///
/// One field add of [`params::BALANCED_SHIFT`], one unsigned [`digit_at`], one
/// field subtract of [`params::HALF_BASE`] -- the spec's three steps, in the
/// spec's order. The result lies in the paper's balanced box
/// `S_b = [-8, 7]` as a *centered* residue
/// (`balancedZmodDigit_valMinAbs_mem`, `Gadget/Norms.lean:114`), so `-8` is the
/// field element `Fp(q - 8)` and not a small `u64`.
///
/// The shift is a **field** addition. A raw `u64` add would be a different
/// function: `c.to_u64() + BALANCED_SHIFT` can reach `6585616420`, which is
/// `≥ 16^8` and so has nine base-16 digits where the spec's
/// `(c + balancedShift).val < q` has eight -- the top digit, the one the gadget
/// reads at `e = 7`, would come out `0` instead of its true value. That is the
/// whole content of the specification's `hbq : b ≤ q/2` side condition
/// (`Gadget/Norms.lean:112`).
///
/// The `digits` argument of the spec enters only through `balancedShift`; it
/// does not bound `e`. As with [`digit_at`], this agrees with the spec at every
/// `e`, and the `⌊b/2⌋` box bound is the one that needs `e < digits`.
pub fn balanced_digit_at(c: Fp, e: usize) -> Fp {
    let shift: Fp = Fp::new(params::BALANCED_SHIFT);
    let half: Fp = Fp::new(params::HALF_BASE);
    digit_at(c + shift, e) - half
}

/// All [`params::GADGET_DIGITS`] balanced digits of a field element,
/// little-endian (spec: the `digit` field of `balancedZmodDigitDecomposition`
/// as a whole).
///
/// Mirrors ArkLib's `balancedZmodDigitDecomposition.digit` at every
/// `e < digits`, as one vector.
///
/// The reconstruction law `Σₑ bᵉ · digit c e = c` is inherited from the
/// unsigned decomposition at the shifted input: the digitwise subtractions of
/// `⌊b/2⌋` sum to exactly `balancedShift` and cancel it
/// (`Gadget/Core.lean:179`). It needs the same `q ≤ b ^ digits` that
/// [`digit_decompose`] does.
///
/// Deliberately re-derives the shift per digit, exactly as
/// [`digit_decompose`] re-derives each division chain: hoisting the one
/// `c + shift` out of the loop is an optimization, and the first translation
/// does not make it.
pub fn balanced_digit_decompose(c: Fp) -> Vec<Fp> {
    let digits: usize = params::GADGET_DIGITS;
    let mut out: Vec<Fp> = Vec::new();
    let mut e: usize = 0;
    while e < digits {
        out.push(balanced_digit_at(c, e));
        e += 1;
    }
    out
}

/// The Hachi gadget inverse `G⁻¹` (spec: `gadgetDecompose`,
/// `Gadget/Core.lean:518`, instantiated at `balancedZmodDigitDecomposition`).
///
/// Mirrors ArkLib's `gadgetDecompose` at `balancedZmodDigitDecomposition`.
///
/// The same shape as [`gadget_decompose`] -- slot `e` of block `i` is the ring
/// element whose `k`-th coefficient is digit `e` of coefficient `k` of `x[i]`,
/// and `gadget_mul(x.len(), ·)` inverts it by the same
/// `gadgetDecompose_lawful` (`:523`) -- but at the balanced digit map, which is
/// what makes this the decomposition [NOZ26] Eq. (20) range-checks and the one
/// `Hachi.commit` (`Commitment.lean:111`) uses.
///
/// Shorter than the unsigned form by a factor of two in `ℓ∞`: every coefficient
/// of the output is `⌊b/2⌋ = 8`-bounded as a centered residue
/// (`balancedZmodDigit_natAbs_le`, `Gadget/Norms.lean:145`) against the
/// unsigned `b - 1 = 15`.
pub fn balanced_gadget_decompose(x: &PolyVec) -> PolyVec {
    let digits: usize = params::GADGET_DIGITS;
    let degree: usize = params::RING_DEGREE;
    let rows: usize = x.len();
    let mut out: Vec<Rq> = Vec::new();
    let mut i: usize = 0;
    while i < rows {
        let mut e: usize = 0;
        while e < digits {
            let mut coeffs: Vec<Fp> = Vec::new();
            let mut k: usize = 0;
            while k < degree {
                coeffs.push(balanced_digit_at(x.get(i).coeff(k), e));
                k += 1;
            }
            out.push(Rq::from_coeffs(&coeffs));
            e += 1;
        }
        i += 1;
    }
    PolyVec::new(out)
}

// ---------------------------------------------------------------------------
// The bounded balanced layer: the folded witness `ẑ`, at `Z_DIGITS` digits
// ---------------------------------------------------------------------------

/// The `e`-th balanced base-`b` digit of a *short* field element, at the folded
/// witness width [`params::Z_DIGITS`] (spec: `boundedBalancedZmodDigit b τ x e`,
/// `Gadget/Core.lean:278`).
///
/// Mirrors ArkLib's `boundedBalancedZmodDigit` at `digits = Z_DIGITS`.
///
/// Centre first, then shift, then take unsigned digits -- the reverse of
/// [`balanced_digit_at`]'s shift-then-`.val`, and the shift is an integer one
/// rather than a field one:
///
/// ```text
/// digit x e = ((Nat.digits b (x.valMinAbs + ⌊b/2⌋·S).toNat).getD e 0 : ZMod q)
///             - (⌊b/2⌋ : ZMod q),      S = digitOnesValue b τ
/// ```
///
/// with `⌊b/2⌋·S` = [`params::Z_BALANCED_SHIFT`]. The `if` chain below is
/// `Int.toNat` of that integer sum, by the same case split
/// [`crate::commit::centered_abs`] makes: `ZMod.valMinAbs` is `v` when
/// `v ≤ q/2` and `-(q - v)` otherwise, and `Int.toNat` clamps a shift that is
/// still negative to `0`. Nothing overflows: `v < q < 2^32` and the shift is
/// below `2^20`.
///
/// **Total, but a decomposition only on short inputs.** `16^5 < q`, so no
/// `DigitDecomposition (16 : ZMod q) 5` exists and this is a
/// `BoundedDigitDecomposition` instead: the digits always lie in the box
/// `[-8, 7]` (`boundedBalancedZmodDigit_valMinAbs_mem`,
/// `Gadget/Norms.lean:165`, unconditionally), but
/// `Σₑ bᵉ · digit x e = x` holds only for `|x.valMinAbs| ≤ `
/// [`params::Z_BOUND`] (`boundedBalancedZmodDigit_reconstruct`, `:293`). The
/// honest `‖z‖∞ ≤ 2ʳ·ω·⌊b/2⌋` is exactly that bound.
pub fn bounded_z_digit_at(c: Fp, e: usize) -> Fp {
    let b: u64 = params::GADGET_BASE;
    let q: u64 = params::Q;
    let shift: u64 = params::Z_BALANCED_SHIFT;
    let half_q: u64 = q / 2;
    let v: u64 = c.to_u64();
    let shifted: u64 = if v <= half_q {
        v + shift
    } else {
        let neg: u64 = q - v;
        if neg <= shift {
            shift - neg
        } else {
            0
        }
    };
    let mut rest: u64 = shifted;
    let mut i: usize = 0;
    while i < e {
        rest = rest / b;
        i += 1;
    }
    Fp::new(rest % b) - Fp::new(params::HALF_BASE)
}

/// The gadget inverse `J⁻¹` of the folded witness, at the bounded `z`-side
/// width [`params::Z_DIGITS`] (spec: `BoundedDigitDecomposition.gadgetDecompose`,
/// `Gadget/Core.lean:544`, instantiated at
/// `boundedBalancedZmodDigitDecomposition 16 5 131072`).
///
/// Mirrors ArkLib's `BoundedDigitDecomposition.gadgetDecompose` at
/// `boundedBalancedZmodDigitDecomposition`.
///
/// The `_z` sibling [`params::Z_DIGITS`] predicts: the same triple loop as
/// [`balanced_gadget_decompose`], at `Z_DIGITS = 5` digits instead of
/// `GADGET_DIGITS = 8` and over [`bounded_z_digit_at`] instead of
/// [`balanced_digit_at`]. It is a separate function rather than a digits
/// parameter because every `gadget_*` here is hard-wired to its width, and
/// because the two digit maps are genuinely different functions -- not one
/// function at two widths.
///
/// **The round trip is conditional.** `gadget_mul_z(x.len(), ·)` inverts this
/// only when every coefficient of `x` is `Z_BOUND`-short as a centered
/// residue (`boundedGadgetDecompose_gadgetMul_eq`, `Gadget/Core.lean:553`);
/// the full-width [`gadget_decompose`] and [`balanced_gadget_decompose`] invert
/// unconditionally. That is the whole content of `τ = 5 < δ = 8`: `16^5 < q`,
/// so no five-digit decomposition of *every* residue exists. The output range
/// is unconditional either way.
pub fn bounded_z_gadget_decompose(x: &PolyVec) -> PolyVec {
    let digits: usize = params::Z_DIGITS;
    let degree: usize = params::RING_DEGREE;
    let rows: usize = x.len();
    let mut out: Vec<Rq> = Vec::new();
    let mut i: usize = 0;
    while i < rows {
        let mut e: usize = 0;
        while e < digits {
            let mut coeffs: Vec<Fp> = Vec::new();
            let mut k: usize = 0;
            while k < degree {
                coeffs.push(bounded_z_digit_at(x.get(i).coeff(k), e));
                k += 1;
            }
            out.push(Rq::from_coeffs(&coeffs));
            e += 1;
        }
        i += 1;
    }
    PolyVec::new(out)
}

/// The gadget product `J · v` at the `z`-side width (spec: `gadgetMul`,
/// `Gadget/Core.lean:399`, at `digits := zDigits`; equivalently
/// `jMatrix Φ base n zDigits *ᵥ v`, since `jMatrix` *is* `gadgetMatrix` at that
/// width -- `QuadEval/Gadgets.lean:126`).
///
/// Mirrors ArkLib's `gadgetMul` at `digits = Z_DIGITS`.
///
/// The `_z` sibling of [`gadget_mul`], and the reason it must exist in this
/// collapsed form is feasibility rather than speed: `jMatrix` at the scheme's
/// `n = MESSAGE_ROWS · GADGET_DIGITS = 8192` is `n × n·Z` ring elements, about
/// **2.5 TB** at `Z = 5`, so it is never materialized. `gadgetMul_apply`
/// (`Gadget/Core.lean:429`) proves the matrix product collapses to exactly the
/// per-block digit sum below, which is what makes this the honest
/// implementation and not an optimization.
pub fn gadget_mul_z(rows: usize, v: &PolyVec) -> PolyVec {
    let digits: usize = params::Z_DIGITS;
    let mut out: Vec<Rq> = Vec::new();
    let mut i: usize = 0;
    while i < rows {
        let mut acc: Rq = Rq::zero();
        let mut e: usize = 0;
        while e < digits {
            let scaled: Rq = v.get(digits * i + e).scalar_mul(base_pow(e));
            acc = acc.add(&scaled);
            e += 1;
        }
        out.push(acc);
        i += 1;
    }
    PolyVec::new(out)
}
