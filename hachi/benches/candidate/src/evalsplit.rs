//! The multilinear evaluation split: `eval p (xl ++ xh) = mb(xl)ᵀ · M · mb(xh)`.
//!
//! Reference specification: `ArkLib/Commitments/Functional/Hachi/EvalSplit.lean`
//! (with the basis vectors from `CompPoly/Multilinear/Basic.lean`).
//!
//! This is the layer that makes Hachi a *multilinear polynomial* commitment
//! rather than a commitment to a matrix (Hachi [NOZ26] §4): the `2^(nl+nh)`
//! monomial coefficients of a polynomial are reshaped into a `2^nl × 2^nh`
//! matrix ([`MlPoly::to_matrix`]), and evaluation at a point that splits as
//! `(xl, xh)` factors as the split bilinear form
//! [`crate::linalg::PolyMatrix::split_form`] of that matrix against the
//! monomial bases of the two point halves ([`MlPoly::eval_split`];
//! `evalSplit_eq_eval`, `EvalSplit.lean:172`). The Lagrange / hypercube
//! representation gets the same treatment ([`MlEvals::eval_split_eval`]).
//!
//! | spec | here |
//! |---|---|
//! | `splitEquiv` value (`EvalSplit.lean:73`, value `:77`) | [`split_equiv`] |
//! | `splitEquiv.symm` | [`split_equiv_inv`] |
//! | `CMlPolynomial (Rq Φ) n` (`Multilinear/Basic.lean:35`) | [`MlPoly`] |
//! | `CMlPolynomialEval (Rq Φ) n` (`:43`) | [`MlEvals`] |
//! | `CMlPolynomial.monomialBasis` (`:156`) | [`monomial_basis`] |
//! | `CMlPolynomialEval.lagrangeBasis` (`:405`) | [`lagrange_basis`] |
//! | `toMatrix` (`EvalSplit.lean:150`) | [`MlPoly::to_matrix`] |
//! | `toPolynomial` (`:199`) | [`to_polynomial`] |
//! | `evalSplit` (`:166`) | [`MlPoly::eval_split`] |
//! | `toMatrixEval` (`:296`) | [`MlEvals::to_matrix_eval`] |
//! | `evalSplitEval` (`:310`) | [`MlEvals::eval_split_eval`] |
//!
//! # The instantiation, and why the field-level `cpoly` multilinear layer is
//! # not used here
//!
//! The consumer fixes the carrier: the Hachi bridge works with
//! `CMlPolynomial (Rq Φ) (r + m)` and a `2^r × 2^m` derived-message matrix
//! over `Rq` (`QuadEval/Bridge.lean:104`, `QuadEval/Reduction.lean:193`). So
//! the coefficient ring here is [`Rq`], not the field -- `cpoly`'s
//! `multilinear.rs` (over `Ext4`) is the right tool for the §3 packing layer,
//! which is protocol-side and out of scope, and the wrong carrier for this
//! one. The basis products below are `Rq` multiplications.
//!
//! # Index conventions (all little-endian)
//!
//! Bit `0` is the least significant and belongs to the *first* variable. The
//! split index is `splitEquiv (x, y) = y + 2^nl · x`: the low `nl` bits (`y`)
//! carry the first variables and index the matrix **rows**; the high `nh`
//! bits (`x`) carry the last variables and index the **columns**
//! (`EvalSplit.lean:53-57`). Note the argument swap in the reshape: entry
//! `(i, j)` of `toMatrix p` is coefficient `splitEquiv (j, i) = i + 2^nl · j`
//! (`EvalSplit.lean:151`) -- row first in the matrix, row *second* in the
//! split pair.

use alloc::vec::Vec;

use crate::linalg::{PolyMatrix, PolyVec};
use crate::params;
use crate::ring::Rq;

/// The split of a `(nl + nh)`-bit index, forward direction (spec: the value of
/// `splitEquiv`, `EvalSplit.lean:73`, `splitEquiv_val` `:77`).
///
/// Mirrors ArkLib's `splitEquiv` (the function direction).
///
/// `(x, y) ↦ y + 2^nl · x` at `2^nl = ML_LOW_LEN`: `y < 2^nl` is the low/row
/// part, `x < 2^nh` the high/column part. The spec's `Fin` bounds travel as
/// hypotheses on the equivalence statement.
pub fn split_equiv(x: usize, y: usize) -> usize {
    y + params::ML_LOW_LEN * x
}

/// The split of a `(nl + nh)`-bit index, inverse direction (spec:
/// `splitEquiv.symm`, used by `toPolynomial`, `EvalSplit.lean:199`).
///
/// Mirrors ArkLib's `splitEquiv.symm`.
///
/// `k ↦ (k / 2^nl, k % 2^nl)`: the pair is `(x, y)` in the same order as
/// [`split_equiv`] takes them -- high/column part first.
pub fn split_equiv_inv(k: usize) -> (usize, usize) {
    let x: usize = k / params::ML_LOW_LEN;
    let y: usize = k % params::ML_LOW_LEN;
    (x, y)
}

/// `2^n`, by repeated doubling (spec: the `2 ^ n` in `Vector R (2 ^ n)`).
///
/// A helper rather than `1 << n`, so the extracted model stays in plain
/// `Usize` arithmetic (see `lib.rs` § "Style notes"); the callers' concrete
/// `n` is at most `ML_VARS_LOW + ML_VARS_HIGH`, so the checked multiplication
/// is far from overflow.
// Dead since Stage 6 candidates M and N: the doubling builds of the two bases
// index nothing and form no power, so nothing in this module calls either
// helper any more. They stay rather than go, and the `allow` is the cheap half
// of that decision: both are frozen in the genesis corpus, both carry proved
// specs that `lean/Check.lean` § 4 audits (`two_pow_spec`, `test_bit_spec`), and
// charon translates every local item whether or not the crate reaches it -- so
// the model and those specs are still exactly about this code. Deleting proved
// specs is the larger and less reversible move; `zerocheck::two_pow` is a
// separate function and still has callers.
#[allow(dead_code)]
fn two_pow(n: usize) -> usize {
    let mut size: usize = 1;
    let mut t: usize = 0;
    while t < n {
        size = size * 2;
        t += 1;
    }
    size
}

/// Bit `j` of `i` (spec: `(BitVec.ofFin i).getLsb j`, i.e. `Nat.testBit`).
///
/// By repeated division, like [`crate::gadget::digit_at`]: `j` halvings, then
/// the parity of what is left. Little-endian -- bit `0` is the least
/// significant.
#[allow(dead_code)]
fn test_bit(i: usize, j: usize) -> bool {
    let mut rest: usize = i;
    let mut t: usize = 0;
    while t < j {
        rest = rest / 2;
        t += 1;
    }
    rest % 2 == 1
}

/// A multilinear polynomial over `R_q` by its `2^n` monomial coefficients,
/// little-endian (spec: `CMlPolynomial (Rq Φ) n`, `Multilinear/Basic.lean:35`).
///
/// Mirrors `CMlPolynomial` (a CompPoly definition, the carrier ArkLib's
/// split works over) at `R = Rq Φ`; the spec
/// carries the length `2^n` in the type and this carries it in the `Vec`.
/// Coefficient `i` multiplies the monomial `∏_{bit j of i set} X_j`.
pub struct MlPoly(Vec<Rq>);

/// A multilinear polynomial over `R_q` by its `2^n` values on the Boolean
/// hypercube, little-endian (spec: `CMlPolynomialEval (Rq Φ) n`,
/// `Multilinear/Basic.lean:43`).
///
/// Mirrors `CMlPolynomialEval` (CompPoly's, likewise) at `R = Rq Φ`. The same
/// carrier as [`MlPoly`] read against the Lagrange basis instead of the
/// monomial one -- two spec types, so two Rust types.
pub struct MlEvals(Vec<Rq>);

/// Monomial-basis evaluations at the point `w` (spec:
/// `CMlPolynomial.monomialBasis`, `Multilinear/Basic.lean:156`).
///
/// Mirrors `CMlPolynomial.monomialBasis` (a CompPoly definition; the ArkLib
/// split consumes it through `monomialBasis_get`).
///
/// Entry `i` of the length-`2^n` result is
/// `∏_{j < n} (if bit j of i then w[j] else 1)`.
///
/// Built one variable at a time (Stage 6 candidate M; opt:
/// `HachiEquiv.Opt.monomial_basis.opt`, `lean/Opt.lean`): the table for the
/// prefix `w₀ … wⱼ` is the table for `w₀ … wⱼ₋₁` followed by that same table
/// scaled by `wⱼ`, because bit `j` of an index below `2^j` is clear and bit `j`
/// of `2^j + r` is set. The frozen baseline recomputed each entry from all `n`
/// variables -- `2^n · n` ring products, and `n - popcount(i)` of them
/// multiplications by `Rq::one()`; this pays `2^n - 1`, which is `1023` instead
/// of `10240` at `ML_VARS_LOW = 10`.
pub fn monomial_basis(w: &PolyVec) -> PolyVec {
    let n: usize = w.len();
    let mut out: Vec<Rq> = Vec::new();
    out.push(Rq::one());
    let mut j: usize = 0;
    while j < n {
        let half: usize = out.len();
        let x: &Rq = w.get(j);
        let mut i: usize = 0;
        while i < half {
            let scaled: Rq = out[i].mul(x);
            out.push(scaled);
            i += 1;
        }
        j += 1;
    }
    PolyVec::new(out)
}

/// Lagrange-basis evaluations at the point `w` -- the multilinear equality
/// kernel `eq̃(·, w)` on the hypercube (spec: `CMlPolynomialEval.lagrangeBasis`,
/// `Multilinear/Basic.lean:405`).
///
/// Mirrors `CMlPolynomialEval.lagrangeBasis` (a CompPoly definition; the
/// ArkLib split consumes it through `lagrangeBasis_get`).
///
/// Entry `i` is `∏_{j < n} (if bit j of i then w[j] else 1 - w[j])`.
///
/// Built one variable at a time, like [`monomial_basis`] (Stage 6 candidate N;
/// opt: `HachiEquiv.Opt.lagrange_basis.opt`, `lean/Opt.lean`), and specialized
/// to the ring carrier: both children of an entry `p` are `p·(1−wⱼ)` and
/// `p·wⱼ`, and the first is spelled `p − p·wⱼ`, so the level costs **one**
/// ring multiplication and one ring subtraction per entry rather than two
/// multiplications. `Rq::sub` is `N` coefficient subtractions against
/// `Rq::mul`'s `N²` coefficient products, so at `N = 1024` the subtraction is
/// free at this ratio. The frozen baseline recomputed each entry from all `n`
/// variables -- `2^n · n` ring products, `10240` at `ML_VARS_LOW = 10`; this
/// pays `2^n - 1`, which is `1023`, and the upstream two-multiplication form
/// would have paid `2046`.
pub fn lagrange_basis(w: &PolyVec) -> PolyVec {
    let n: usize = w.len();
    let mut out: Vec<Rq> = Vec::new();
    out.push(Rq::one());
    let mut j: usize = 0;
    while j < n {
        let half: usize = out.len();
        let x: &Rq = w.get(j);
        let mut i: usize = 0;
        while i < half {
            let px: Rq = out[i].mul(x);
            let p0: Rq = out[i].sub(&px);
            out[i] = p0;
            out.push(px);
            i += 1;
        }
        j += 1;
    }
    PolyVec::new(out)
}

impl MlPoly {
    /// Wrap a coefficient vector (expected length [`params::ML_POLY_LEN`];
    /// like the ring's degree invariant, a property of construction).
    pub fn new(coeffs: Vec<Rq>) -> MlPoly {
        MlPoly(coeffs)
    }

    /// The number of coefficients.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// The `k`-th monomial coefficient.
    pub fn get(&self, k: usize) -> &Rq {
        &self.0[k]
    }

    /// Reshape the coefficient vector into the `2^nl × 2^nh` split matrix
    /// (spec: `toMatrix`, `EvalSplit.lean:150`).
    ///
    /// Mirrors ArkLib's `Hachi.toMatrix`.
    ///
    /// Entry `(i, j)` is coefficient `splitEquiv (j, i) = i + 2^nl · j` --
    /// the spec swaps the pair (row `i` is the *second* component; see the
    /// module header). Rows are indexed by the low/first variables, columns
    /// by the high/last ones.
    pub fn to_matrix(&self) -> PolyMatrix {
        let rows: usize = params::ML_LOW_LEN;
        let cols: usize = params::ML_HIGH_LEN;
        let mut out: Vec<PolyVec> = Vec::with_capacity(rows);
        let mut i: usize = 0;
        while i < rows {
            let mut row: Vec<Rq> = Vec::with_capacity(cols);
            let mut j: usize = 0;
            while j < cols {
                let k: usize = split_equiv(j, i);
                row.push(self.0[k].copy());
                j += 1;
            }
            out.push(PolyVec::new(row));
            i += 1;
        }
        PolyMatrix::new(out)
    }

    /// Evaluate via the split: the bilinear form of the reshaped matrix
    /// against the monomial bases of the two point halves (spec: `evalSplit`,
    /// `EvalSplit.lean:166`).
    ///
    /// Mirrors ArkLib's `Hachi.evalSplit`.
    ///
    /// `evalSplit_eq_eval` (`EvalSplit.lean:172`) is what makes this an
    /// evaluation: it equals `eval p (xl ++ xh)` -- `xl` the first
    /// [`params::ML_VARS_LOW`] coordinates, `xh` the last
    /// [`params::ML_VARS_HIGH`].
    pub fn eval_split(&self, xl: &PolyVec, xh: &PolyVec) -> Rq {
        let m: PolyMatrix = self.to_matrix();
        let bl: PolyVec = monomial_basis(xl);
        let bh: PolyVec = monomial_basis(xh);
        m.split_form(&bl, &bh)
    }
}

/// Read a `2^nl × 2^nh` matrix back into the coefficient vector along the
/// split -- the inverse reshape of [`MlPoly::to_matrix`] (spec:
/// `toPolynomial`, `EvalSplit.lean:199`).
///
/// Mirrors ArkLib's `Hachi.toPolynomial`.
///
/// Coefficient `k` is `M[y][x]` for `(x, y) = splitEquiv.symm k`: row
/// `y = k % 2^nl`, column `x = k / 2^nl`. The round-trip laws
/// `toMatrix_toPolynomial` / `toPolynomial_toMatrix` (`EvalSplit.lean:214,
/// 221`) are what make the two reshapes a bijection.
pub fn to_polynomial(m: &PolyMatrix) -> MlPoly {
    let len: usize = params::ML_POLY_LEN;
    let mut out: Vec<Rq> = Vec::with_capacity(len);
    let mut k: usize = 0;
    while k < len {
        let xy: (usize, usize) = split_equiv_inv(k);
        let x: usize = xy.0;
        let y: usize = xy.1;
        out.push(m.row(y).get(x).copy());
        k += 1;
    }
    MlPoly(out)
}

impl MlEvals {
    /// Wrap a hypercube-value vector (expected length
    /// [`params::ML_POLY_LEN`]; a property of construction).
    pub fn new(values: Vec<Rq>) -> MlEvals {
        MlEvals(values)
    }

    /// The number of hypercube values.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// The value at hypercube point `k` (little-endian bits).
    pub fn get(&self, k: usize) -> &Rq {
        &self.0[k]
    }

    /// Reshape the value vector into the `2^nl × 2^nh` split matrix (spec:
    /// `toMatrixEval`, `EvalSplit.lean:296`).
    ///
    /// Mirrors ArkLib's `Hachi.toMatrixEval`.
    ///
    /// The same index computation as [`MlPoly::to_matrix`] -- a distinct spec
    /// definition on a distinct spec type, so a distinct body here.
    pub fn to_matrix_eval(&self) -> PolyMatrix {
        let rows: usize = params::ML_LOW_LEN;
        let cols: usize = params::ML_HIGH_LEN;
        let mut out: Vec<PolyVec> = Vec::with_capacity(rows);
        let mut i: usize = 0;
        while i < rows {
            let mut row: Vec<Rq> = Vec::with_capacity(cols);
            let mut j: usize = 0;
            while j < cols {
                let k: usize = split_equiv(j, i);
                row.push(self.0[k].copy());
                j += 1;
            }
            out.push(PolyVec::new(row));
            i += 1;
        }
        PolyMatrix::new(out)
    }

    /// Evaluate via the split, Lagrange representation: the bilinear form of
    /// the reshaped value matrix against the Lagrange bases of the two point
    /// halves (spec: `evalSplitEval`, `EvalSplit.lean:310`).
    ///
    /// Mirrors ArkLib's `Hachi.evalSplitEval`.
    ///
    /// `evalSplitEval_eq_eval` (`EvalSplit.lean:317`) equates it with the
    /// multilinear extension's value at `xl ++ xh`.
    pub fn eval_split_eval(&self, xl: &PolyVec, xh: &PolyVec) -> Rq {
        let m: PolyMatrix = self.to_matrix_eval();
        let bl: PolyVec = lagrange_basis(xl);
        let bh: PolyVec = lagrange_basis(xh);
        m.split_form(&bl, &bh)
    }
}
