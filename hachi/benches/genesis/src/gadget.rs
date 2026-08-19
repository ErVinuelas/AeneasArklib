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
//! negative representative. At `b = 2` the digits are `{0, 1}` and the bound is
//! `1`. See NOTES.md § "The digits are not balanced".
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

/// The `e`-th base-`b` digit of a field element (spec:
/// `zmodDigitDecomposition.digit c e`, `Gadget/Core.lean:115`).
///
/// `⌊c / bᵉ⌋ mod b`, computed by repeated division so that no power of `b` is
/// ever formed -- `b^digits` can exceed the modulus, and `Nat.digits` on the spec
/// side never forms it either.
///
/// Agrees with the spec at *every* `e`, not just below the digit length: for
/// `e` past the length of `Nat.digits b c.val` the spec's `getD` returns its `0`
/// default, and so does the division here once the quotient has run out.
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/gadget.rs
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
/// The reconstruction law `Σₑ bᵉ · digit c e = c` (the `reconstruct` field of
/// `DigitDecomposition`) is what makes this a decomposition rather than an
/// arbitrary map, and it needs `q ≤ b ^ digits`; [`params::GADGET_DIGITS`]
/// records that this holds here.
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/gadget.rs
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
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/gadget.rs
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
/// `Gadget/Core.lean:139`): the ring constant `C(b^(j mod digits))` when
/// `j / digits = i`, and `0` otherwise.
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/gadget.rs
pub fn gadget_entry(i: usize, j: usize) -> Rq {
    let digits: usize = params::GADGET_DIGITS;
    if j / digits == i {
        Rq::constant(base_pow(j % digits))
    } else {
        Rq::zero()
    }
}

/// The gadget matrix `G = I_rows ⊗ [1, b, …, b^(digits-1)]`, of shape
/// `rows × (rows · digits)` (spec: `gadgetMatrix`, `Gadget/Core.lean:143`).
///
/// Materialized only where the specification materializes it: `verify_weak`
/// checks `A sᵢ = G t̂ᵢ` by passing `gadgetMatrix Φ base innerRows innerDigits`
/// to `Simple.verify`, i.e. as an ordinary Ajtai matrix. [`gadget_mul`] is the
/// structured form to use everywhere else.
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/gadget.rs
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

/// The gadget product `G · v` (spec: `gadgetMul`, `Gadget/Core.lean:147`).
///
/// Row `i` is `Σ_{e<digits} bᵉ · v[digits·i + e]`, which is the specification's
/// `gadgetMul_apply` (`:177`) read as a definition. Multiplication by the ring
/// constant `C(bᵉ)` is coefficientwise scaling by `bᵉ`, which is the spec's
/// `constRq_mul_coeff`, so this uses [`Rq::scalar_mul`] rather than a full ring
/// product.
///
/// `v` is expected to have `rows · digits` entries.
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/gadget.rs
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

/// The gadget inverse `G⁻¹` (spec: `gadgetDecompose`, `Gadget/Core.lean:207`,
/// instantiated at `zmodDigitDecomposition`).
///
/// Slot `e` of block `i` is the ring element whose `k`-th coefficient is the
/// `e`-th digit of the `k`-th coefficient of `x[i]`. The output has
/// `x.len() · digits` entries, and `gadget_mul(x.len(), ·)` inverts it -- the
/// specification's `IsLawfulGadgetDecomposition` (`:152`), proved of this
/// decomposition in `gadgetDecompose_lawful` (`:221`).
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/gadget.rs
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
