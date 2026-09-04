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
//! # The digits are non-negative, and the bound is `b - 1`
//!
//! Worth stating plainly, because it is easy to assume otherwise -- balanced
//! (signed) digit decompositions are common in this literature, and this is not
//! one. The specification's `zmodDigitDecomposition` (`Gadget/Core.lean:113`) is
//!
//! ```text
//! digit c e = ((Nat.digits b c.val).getD e 0 : ZMod q)
//! ```
//!
//! i.e. the ordinary base-`b` digits of the *canonical* representative
//! `c.val ∈ [0, q)`, each in `{0, …, b-1}`. What is centered is the norm, not the
//! digits: `Rq.lInftyNorm` measures every coefficient through `ZMod.valMinAbs`,
//! and `Gadget/Norms.lean`'s `zmodDigit_natAbs_le` then bounds each digit's
//! centered absolute value by `b - 1` -- under the side condition `b - 1 ≤ q/2`,
//! which is exactly what stops a small non-negative digit from wrapping to a
//! negative representative. At `b = 16` the digits are `{0, …, 15}` and the
//! bound is `15`. See NOTES.md § "The digits are not balanced".
//!
//! This makes the decomposition **not paper-faithful** at `b = 16`: [NOZ26]
//! uses *balanced* base-16 digits in `[-8, 7]`, so honest commitment outputs
//! and norm sizes differ from the paper's implementation (harmless at the old
//! `b = 2`, where the bounds coincide). The pinned ArkLib has only the
//! unsigned form; the fix trigger -- upstream `balancedZmodDigitDecomposition`,
//! PR #782 -- is recorded in NOTES.md § "The digits are not balanced".
//!
//! # Index layout
//!
//! Slot `e` of block `i` is flat index `digits·i + e`, per `finProdFinEquiv`
//! (see [`crate::linalg`]'s module header). Both `gadget_mul` and
//! `gadget_decompose` are written directly against that layout rather than
//! against a general matrix product: the specification's `gadgetMul_apply`
//! (`Gadget/Core.lean:177`) proves the general product collapses to exactly this
//! per-block digit sum, which is what makes the direct form the honest one to
//! implement -- and `O(rows · digits)` work instead of `O(rows² · digits)`.

use alloc::vec::Vec;
use cpoly::Fp;

use crate::linalg::{PolyMatrix, PolyVec};
use crate::params;
use crate::ring::Rq;

// @genesis d664190 2026-08-19 — gadget::digit_at
/// The `e`-th base-`b` digit of a field element (spec:
/// `zmodDigitDecomposition.digit c e`, `Gadget/Core.lean:115`).
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

// @genesis d664190 2026-08-19 — gadget::digit_decompose
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

// @genesis d664190 2026-08-19 — gadget::base_pow
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

// @genesis d664190 2026-08-19 — gadget::gadget_entry
/// Entry `(i, j)` of the gadget matrix (spec: `gadgetEntry`,
/// `Gadget/Core.lean:139`): the ring constant `C(b^(j mod digits))` when
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

// @genesis d664190 2026-08-19 — gadget::gadget_matrix
/// The gadget matrix `G = I_rows ⊗ [1, b, …, b^(digits-1)]`, of shape
/// `rows × (rows · digits)` (spec: `gadgetMatrix`, `Gadget/Core.lean:143`).
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

// @genesis d664190 2026-08-19 — gadget::gadget_mul
/// The gadget product `G · v` (spec: `gadgetMul`, `Gadget/Core.lean:147`).
///
/// Mirrors ArkLib's `gadgetMul`.
///
/// Row `i` is `Σ_{e<digits} bᵉ · v[digits·i + e]`, which is the specification's
/// `gadgetMul_apply` (`:177`) read as a definition. Multiplication by the ring
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

// @genesis d664190 2026-08-19 — gadget::gadget_decompose
/// The gadget inverse `G⁻¹` (spec: `gadgetDecompose`, `Gadget/Core.lean:207`,
/// instantiated at `zmodDigitDecomposition`).
///
/// Mirrors ArkLib's `gadgetDecompose` at `zmodDigitDecomposition`.
///
/// Slot `e` of block `i` is the ring element whose `k`-th coefficient is the
/// `e`-th digit of the `k`-th coefficient of `x[i]`. The output has
/// `x.len() · digits` entries, and `gadget_mul(x.len(), ·)` inverts it -- the
/// specification's `IsLawfulGadgetDecomposition` (`:152`), proved of this
/// decomposition in `gadgetDecompose_lawful` (`:221`).
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

// @genesis 09df61b 2026-09-04 — gadget::balanced_digit_at
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

// @genesis 09df61b 2026-09-04 — gadget::balanced_digit_decompose
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

// @genesis 09df61b 2026-09-04 — gadget::balanced_gadget_decompose
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

// @genesis 09df61b 2026-09-04 — gadget::bounded_z_digit_at
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
