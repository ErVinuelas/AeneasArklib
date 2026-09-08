//! Hachi's nested zero-check: the table `w̃` and the range-constraint block `H₀`.
//!
//! Reference specification:
//! `ArkLib/Commitments/Functional/Hachi/ZeroCheck/Constraints.lean`.
//!
//! # What this module is
//!
//! The zero-check link states that the lifted witness is *short* without
//! sending it: the committed table `w̃` is laid out on the cube `{0,1}^m₀`, and
//! `H₀ ≡ 0` says every entry of that table is a legal base-`b` digit
//! (`rangeProduct_eq_zero_iff`, `Constraints.lean:102`). This module owns the
//! `H₀` side of the link -- the table, its multilinear extension, the range
//! factor and the constraint block. The `H_α` side (`hAlphaEvals`, `hAlpha`,
//! `alphaPublicEvals`, `zcTargetAlpha`) is *not* here: it is reached through
//! `cRowSum`, whose product of two quotient representatives is non-negacyclic
//! and grows past the ring degree, so it needs a carrier this crate does not
//! have yet. See NOTES.md § "Target 4 opens".
//!
//! # First `Ext4` consumer in the crate
//!
//! Every earlier module works over `Rq`, i.e. over `Fp`. The zero-check's
//! carrier is the *extension* field `F`, so this is the first module to import
//! `cpoly::Ext4`, and the first to hold `cpoly::MultilinearEvals` -- the
//! computable `CMlPolynomialEval F m` of `CompPoly/Multilinear/Basic.lean:47`.
//! Neither is reimplemented, per the crate's reuse rule (`lib.rs`
//! § "The field layer comes from cpoly"): `hZero` and `cWTableMle` are
//! `MultilinearEvals` values, and the Lagrange-vs-monomial split of
//! `cpoly/src/multilinear.rs` means `MultilinearEvals` (never
//! `MultilinearPoly`) is the right one -- all three ArkLib tables are the
//! Boolean-evaluation reading.
//!
//! # Arities come from the data, not from `params`
//!
//! `m₀` is an argument and `μ`, `n` are read off the witness, deliberately
//! against the crate's habit of hard-wiring `params` constants. At the pinned
//! profile `2^M_ZERO` is `2^26` entries -- 2.0 GiB as an `Ext4` table -- so a
//! `w_table` that could only be called at `M_ZERO` could not be tested or
//! benchmarked at all. The precedent is inside `evalsplit.rs`, which reads
//! `params::ML_LOW_LEN` in `to_matrix` but `w.len()` in `lagrange_basis`, and
//! it is the second form that keeps a live (non-`#[ignore]`d) test possible.
//! `d`, `b` and the quotient digit count stay `params` constants.

use alloc::vec::Vec;

use cpoly::{Ext4, Fp, MultilinearEvals};

use crate::params;
use crate::ringswitch::{rho_digit_as_rq, LiftedWitness};

/// `2^n`, by repeated doubling (spec: the `2 ^ m₀` in `CMlPolynomialEval F m₀`).
///
/// The same helper, and for the same reason, as `evalsplit`'s: a shift would
/// leave the extracted model reasoning about `<<` instead of plain `Usize`
/// arithmetic (`lib.rs` § "Style notes").
fn two_pow(n: usize) -> usize {
    let mut size: usize = 1;
    let mut t: usize = 0;
    while t < n {
        size = size * 2;
        t += 1;
    }
    size
}

/// Hachi Eq. (23)'s per-entry range factor `P_b(v) = v·∏_{j=1}^{b-1} (v−j)(v+j)`
/// (spec: `rangeProduct`, `Constraints.lean:96`).
///
/// Mirrors `rangeProduct`.
///
/// The vanishing polynomial of the symmetric range `{−(b−1), …, b−1}`, so
/// `P_b(v) = 0` says exactly that `v` is the image of an integer in that range
/// (`rangeProduct_eq_zero_iff`, `Constraints.lean:102`).
///
/// The loop runs `1 ≤ j < b` rather than `1 ≤ j ≤ b − 1`: the two index sets
/// are the same `Finset.Icc 1 (b - 1)`, but `b − 1` is never formed, so the
/// extracted model carries no subtraction to discharge (`lib.rs`
/// § "Style notes"; the same reason `params::GAMMA` is a literal).
pub fn range_product(v: Ext4) -> Ext4 {
    let base: u64 = params::GADGET_BASE;
    let mut acc: Ext4 = v;
    let mut j: u64 = 1;
    while j < base {
        let scalar: Ext4 = Ext4::from_base(Fp::new(j));
        let lo: Ext4 = v - scalar;
        let hi: Ext4 = v + scalar;
        acc = acc * lo * hi;
        j += 1;
    }
    acc
}

/// Entry `idx` of the committed table `w̃` (spec: `wTable`,
/// `Constraints.lean:140`).
///
/// Mirrors `wTable`.
///
/// The cube point is taken as its flat index. That is not a shortcut: every
/// consumer in the specification feeds `finFunctionFinEquiv.symm i` into a
/// `wTable` whose first act is to apply `finFunctionFinEquiv`, and the two
/// cancel by `Equiv.apply_symm_apply` (the simp step of `wTable_zRow`'s proof,
/// `Constraints.lean:378`), so the flat index *is* the argument every caller
/// supplies.
///
/// Two nested splits, as in the specification: the outer `idx / d`, `idx % d`
/// into (row, coefficient), then inside the quotient block a second split into
/// (quotient row, digit) -- the latter being exactly the flattening
/// [`crate::ringswitch::rho_digit_as_rq`] performs, which is why the digit
/// branch delegates to it rather than re-deriving the pair.
///
/// `μ` and `n` are read off the witness (`w.z().len()`, `w.rho().len()`),
/// matching the specification's `LiftedWitness Φ μ n` indices.
///
/// The subtraction `row − μ` is formed only under the guard that establishes
/// `μ ≤ row`, so the checked `Usize` model of it has its side condition in
/// scope (`lib.rs` § "Style notes").
///
/// The digit branch rebuilds a whole `Rq` -- `d` calls to
/// `balanced_digit_at` -- to read one coefficient out of it. That is the
/// specification's own shape (`rhoDigits` is a `CPolynomial.ofFinCoeff d`),
/// not a translation artefact, and it is deliberately kept: the `d`-factor
/// hoist is an optimization for `perf-loop`, and freezing an improved body
/// would zero that gain out of the baseline forever.
pub fn w_table(w: &LiftedWitness, idx: usize) -> Ext4 {
    let degree: usize = params::RING_DEGREE;
    let digits: usize = params::GADGET_DIGITS;
    let mu: usize = w.z().len();
    let rows: usize = w.rho().len();
    let row: usize = idx / degree;
    let col: usize = idx % degree;
    if row < mu {
        Ext4::from_base(w.z().get(row).coeff(col))
    } else if row - mu < rows * digits {
        let j: usize = row - mu;
        Ext4::from_base(rho_digit_as_rq(w.rho(), j).coeff(col))
    } else {
        Ext4::ZERO
    }
}

/// The committed table `w̃` as a multilinear extension in Lagrange form
/// (spec: `cWTableMle`, `Constraints.lean:328`).
///
/// Mirrors `cWTableMle`.
///
/// `2^m₀` entries: at the pinned `M_ZERO = 26` that is `67 108 864` `Ext4`
/// values, 2.0 GiB, which is why `m0` is an argument.
pub fn c_w_table_mle(w: &LiftedWitness, m0: usize) -> MultilinearEvals {
    let size: usize = two_pow(m0);
    let mut values: Vec<Ext4> = Vec::new();
    let mut i: usize = 0;
    while i < size {
        values.push(w_table(w, i));
        i += 1;
    }
    MultilinearEvals::from_values(values)
}

/// The evaluation claim `mle[w̃](a)` carried into the final-evaluation step
/// (spec: `wTableMleEval`, `Constraints.lean:335`).
///
/// Mirrors `wTableMleEval`.
///
/// `CMlPolynomialEval.eval` is cpoly's `MultilinearEvals::eval`, the
/// `O(m₀·2^m₀)` dot against the Lagrange basis. cpoly also carries the
/// `O(2^m₀)` `eval_mle` and the proof that the two agree
/// (`CMlPolynomialEval.eval_mle_eq_eval`, `Multilinear/Basic.lean:574`); this
/// translation takes the `eval` the specification names, and the swap is
/// `perf-loop`'s to make.
pub fn w_table_mle_eval(w: &LiftedWitness, m0: usize, a: &Vec<Ext4>) -> Ext4 {
    let table: MultilinearEvals = c_w_table_mle(w, m0);
    table.eval(a)
}

/// The range-constraint block `H₀` in Boolean-evaluation form
/// (spec: `hZero`, `Constraints.lean:204`).
///
/// Mirrors `hZero`.
///
/// Entry `x` is `P_b(w̃(x))`; the vector is the unique multilinear extension of
/// those `2^m₀` values.
pub fn h_zero(w: &LiftedWitness, m0: usize) -> MultilinearEvals {
    let size: usize = two_pow(m0);
    let mut values: Vec<Ext4> = Vec::new();
    let mut i: usize = 0;
    while i < size {
        values.push(range_product(w_table(w, i)));
        i += 1;
    }
    MultilinearEvals::from_values(values)
}

/// The zero-check's own verdict: is every entry of `H₀` zero?
/// (spec: `hZero = 0`, in the pointwise form of `hZero_eq_zero_iff`,
/// `Constraints.lean:219`).
///
/// Mirrors `hZero_eq_zero_iff`.
///
/// Runs branchless to the end rather than returning early, the shape
/// `ring::Rq::equals` and `commit`'s checks already use: the decision procedure
/// the equivalence proof mirrors is a fold over all entries, and an early
/// return would make the extracted model a different recursion.
pub fn h_zero_is_zero(w: &LiftedWitness, m0: usize) -> bool {
    let size: usize = two_pow(m0);
    let mut zero: bool = true;
    let mut i: usize = 0;
    while i < size {
        if !range_product(w_table(w, i)).is_zero() {
            zero = false;
        }
        i += 1;
    }
    zero
}

/// `α̃(ℓ) = α^ℓ`, the public column-contraction vector ([NOZ26] Eq. (22); spec:
/// `alphaTilde`, `Constraints.lean:502`).
///
/// Mirrors `alphaTilde`.
///
/// Contracting a table row's `d` coefficient entries against `α̃` evaluates the
/// corresponding `Zq[X]` polynomial at `α`. Written as the specification writes
/// it -- one power, recomputed -- the same naivety as
/// [`crate::gadget::base_pow`]. The `d`-entry power *table* is
/// `perf-loop`'s to build.
pub fn alpha_tilde(alpha: Ext4, l: usize) -> Ext4 {
    let mut acc: Ext4 = Ext4::ONE;
    let mut t: usize = 0;
    while t < l {
        acc = acc * alpha;
        t += 1;
    }
    acc
}

/// The `m₁`-cube equality weight of row `i`: `∏_j (if bit j of i then τ₁ⱼ else
/// 1 − τ₁ⱼ)` (spec: the `∏ j : Fin m₁` factor of `alphaPublicEvals`
/// (`Constraints.lean:845-847`) and `zcTargetAlpha` (`:877-879`)).
///
/// Mirrors `CMlPolynomialEval.lagrangeBasis` at one entry.
///
/// The bits of `i` are read coordinate-wise here, and that is not an
/// interchangeable choice: `STAGE2_SCOPING.md` § "Shape-list corrections" claims
/// `finFunctionFinEquiv` cancels against `.symm` in *every* consumer, which is
/// true of the `m₀`-side table constructors and **false here** -- under the
/// product the bits do not cancel (briefs/target-4-zero-check.md § Corrections
/// item 1). The bit test is `/` and `%` rather than `>>` and `&`, per `lib.rs`
/// § "Style notes".
pub fn eq_weight(tau1: &Vec<Ext4>, i: usize) -> Ext4 {
    let vars: usize = tau1.len();
    let mut acc: Ext4 = Ext4::ONE;
    let mut j: usize = 0;
    while j < vars {
        let bit: usize = (i / two_pow(j)) % 2;
        let factor: Ext4 = if bit == 1 {
            tau1[j]
        } else {
            Ext4::ONE - tau1[j]
        };
        acc = acc * factor;
        j += 1;
    }
    acc
}

/// `M̃_α(i, u)`, the public constraint matrix at `α` ([NOZ26] Eq. (22); spec:
/// `mAlphaTilde`, `Constraints.lean:517`).
///
/// Mirrors `mAlphaTilde`.
///
/// The specification's three cases, in its order:
///
/// * `u < μ` -- the `R^lin` matrix entry evaluated at `α`, `Mᵢᵤ(α)`;
/// * `μ ≤ u < μ + n·δ` and `(u − μ)/δ = i` -- `−φ(α)·b^{(u−μ)%δ}`, which places
///   the lift's `−(α^d + 1)·rᵢ(α)` term across row `i`'s `δ` digit columns;
/// * otherwise `0`.
///
/// Only public data enters (`s.M`, `Φ.φ`, `α`, `b`), which is what makes the
/// Figure 7 final check verifier-computable.
///
/// `μ` and `n` are read off the statement, and the subtraction `u − μ` is formed
/// only inside the branch whose guard establishes `μ ≤ u`.
pub fn m_alpha_tilde(s: &crate::ringswitch::RlinStatement, alpha: Ext4, i: usize, u: usize) -> Ext4 {
    let digits: usize = params::GADGET_DIGITS;
    let mu: usize = s.m().cols();
    let rows: usize = s.m().rows();
    if u < mu {
        crate::ringswitch::c_eval_at(alpha, s.m().row(i).get(u))
    } else if u < mu + rows * digits && (u - mu) / digits == i {
        let e: usize = (u - mu) % digits;
        let weight: Ext4 = Ext4::from_base(crate::gadget::base_pow(e));
        (Ext4::ZERO - crate::ringswitch::c_eval_at_modulus(alpha)) * weight
    } else {
        Ext4::ZERO
    }
}

/// The public Boolean table multiplying `mle[w̃]` in the linear-constraint
/// sumcheck (spec: `alphaPublicEvals`, `Constraints.lean:840`).
///
/// Mirrors `alphaPublicEvals`.
///
/// At the flat cube index for `(u, ℓ)` it is `α^ℓ · ∑ᵢ eq̃(τ₁, i)·M̃_α(i, u)`;
/// indices outside the encoded table are harmless padding. The cube point
/// arrives as its flat index for the reason [`w_table`]'s does.
///
/// `m₁` is `tau1.len()` and `n` is the statement's row count. The
/// `i < 2^m₁` guard is the specification's own: at the pinned `n = 5 ≤ 8 = 2^3`
/// it never fires, and it is translated rather than dropped because a parameter
/// move that broke `n ≤ 2^m₁` must not silently change what this computes.
pub fn alpha_public_evals(s: &crate::ringswitch::RlinStatement, alpha: Ext4, tau1: &Vec<Ext4>, idx: usize) -> Ext4 {
    let degree: usize = params::RING_DEGREE;
    let rows: usize = s.m().rows();
    let cube: usize = two_pow(tau1.len());
    let mut sum: Ext4 = Ext4::ZERO;
    let mut i: usize = 0;
    while i < rows {
        if i < cube {
            let weight: Ext4 = eq_weight(tau1, i);
            sum = sum + weight * m_alpha_tilde(s, alpha, i, idx / degree);
        }
        i += 1;
    }
    alpha_tilde(alpha, idx % degree) * sum
}

/// The public initial target of the linear sumcheck, `∑ᵢ eq̃(τ₁, i)·yᵢ(α)`
/// (spec: `zcTargetAlpha`, `Constraints.lean:875`).
///
/// Mirrors `zcTargetAlpha`.
///
/// The verifier computes this from the statement alone -- no witness, and no
/// cube: `n` rows, each one `m₁`-factor weight and one polynomial evaluation at
/// `α`. It is the one operation of this target that is feasible at the real
/// constants, which is why its bench row is not REDUCED.
pub fn zc_target_alpha(s: &crate::ringswitch::RlinStatement, alpha: Ext4, tau1: &Vec<Ext4>) -> Ext4 {
    let rows: usize = s.yvec().len();
    let cube: usize = two_pow(tau1.len());
    let mut sum: Ext4 = Ext4::ZERO;
    let mut i: usize = 0;
    while i < rows {
        if i < cube {
            let weight: Ext4 = eq_weight(tau1, i);
            sum = sum + weight * crate::ringswitch::c_eval_at(alpha, s.yvec().get(i));
        }
        i += 1;
    }
    sum
}
