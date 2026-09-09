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

// @genesis 32d75fa 2026-09-08 — zerocheck::two_pow
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

// @genesis 32d75fa 2026-09-08 — zerocheck::range_product
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

// @genesis 32d75fa 2026-09-08 — zerocheck::w_table
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

// @genesis 32d75fa 2026-09-08 — zerocheck::c_w_table_mle
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

// @genesis 32d75fa 2026-09-08 — zerocheck::w_table_mle_eval
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

// @genesis 32d75fa 2026-09-08 — zerocheck::h_zero
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

// @genesis 32d75fa 2026-09-08 — zerocheck::h_zero_is_zero
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

// @genesis 1e57c54 2026-09-08 — zerocheck::alpha_tilde
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

// @genesis 1e57c54 2026-09-08 — zerocheck::eq_weight
/// The `m₁`-cube equality weight of row `i`: `∏_j (if bit j of i then τ₁ⱼ else
/// 1 − τ₁ⱼ)` (spec: the `∏ j : Fin m₁` factor of `alphaPublicEvals`
/// (`Constraints.lean:845-847`) and `zcTargetAlpha` (`:877-879`)).
///
/// Mirrors `CMlPolynomialEval.lagrangeBasis` at one entry.
///
/// The bits of `i` are read coordinate-wise here, and that is not an
/// interchangeable choice: the Stage 2 scoping document § "Shape-list corrections" claims
/// `finFunctionFinEquiv` cancels against `.symm` in *every* consumer, which is
/// true of the `m₀`-side table constructors and **false here** -- under the
/// product the bits do not cancel (the target-4 brief § Corrections
/// item 1). The bit test is `/` and `%` rather than `>>` and `&`, per `lib.rs`
/// § "Style notes".
///
/// The bits are read by a **running quotient**, and that is not a
/// micro-optimization: `q` starts at `i` and is halved each iteration, so
/// `q % 2` at step `j` is exactly the specification's `finFunctionFinEquiv`
/// bit `i / 2^j % 2`, computed without ever forming `2^j`. The earlier
/// translation wrote `(i / two_pow(j)) % 2`, which materialized the power as a
/// `usize`, and that was the sole reason `eq_weight_spec` needed
/// `2 ^ m₁ ≤ Usize.max`: [`two_pow`] doubles a *checked* `usize`, so it can
/// fail, and the statement had to assume it does not. Forming no power at all
/// is what makes the statement unconditional -- the same move as
/// [`crate::ringswitch::rho_digits_at`], and cpoly's own idiom in
/// `lagrange_basis` (`multilinear.rs:169`), which this function mirrors.
pub fn eq_weight(tau1: &Vec<Ext4>, i: usize) -> Ext4 {
    let vars: usize = tau1.len();
    let mut acc: Ext4 = Ext4::ONE;
    let mut q: usize = i;
    let mut j: usize = 0;
    while j < vars {
        let bit: usize = q % 2;
        let factor: Ext4 = if bit == 1 {
            tau1[j]
        } else {
            Ext4::ONE - tau1[j]
        };
        acc = acc * factor;
        q /= 2;
        j += 1;
    }
    acc
}

// @genesis 1e57c54 2026-09-08 — zerocheck::m_alpha_tilde
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

// @genesis 1e57c54 2026-09-08 — zerocheck::alpha_public_evals
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
///
/// It is decided by [`below_two_pow`], which halves `i` and never forms the
/// cube size. An earlier version bound `cube = two_pow(tau1.len())` and
/// compared against it; that local was the only fallible arithmetic in this
/// function, and carrying it meant `2 ^ m₁ ≤ Usize.max` on the statement of a
/// function that never needs the number -- only the predicate.
pub fn alpha_public_evals(s: &crate::ringswitch::RlinStatement, alpha: Ext4, tau1: &Vec<Ext4>, idx: usize) -> Ext4 {
    let degree: usize = params::RING_DEGREE;
    let rows: usize = s.m().rows();
    let mut sum: Ext4 = Ext4::ZERO;
    let mut i: usize = 0;
    while i < rows {
        if below_two_pow(i, tau1.len()) {
            let weight: Ext4 = eq_weight(tau1, i);
            sum = sum + weight * m_alpha_tilde(s, alpha, i, idx / degree);
        }
        i += 1;
    }
    alpha_tilde(alpha, idx % degree) * sum
}

// @genesis 1e57c54 2026-09-08 — zerocheck::zc_target_alpha
/// The public initial target of the linear sumcheck, `∑ᵢ eq̃(τ₁, i)·yᵢ(α)`
/// (spec: `zcTargetAlpha`, `Constraints.lean:875`).
///
/// Mirrors `zcTargetAlpha`.
///
/// The verifier computes this from the statement alone -- no witness, and no
/// cube: `n` rows, each one `m₁`-factor weight and one polynomial evaluation at
/// `α`. It is the one operation of this target that is feasible at the real
/// constants, which is why its bench row is not REDUCED.
///
/// "No cube" is now literal. The specification's `i < 2^m₁` guard is decided
/// by [`below_two_pow`], so the cube size is never built: this function walks
/// `n` rows and forms no `usize` that can overflow, which is what keeps its
/// statement free of `2 ^ m₁ ≤ Usize.max`.
pub fn zc_target_alpha(s: &crate::ringswitch::RlinStatement, alpha: Ext4, tau1: &Vec<Ext4>) -> Ext4 {
    let rows: usize = s.yvec().len();
    let mut sum: Ext4 = Ext4::ZERO;
    let mut i: usize = 0;
    while i < rows {
        if below_two_pow(i, tau1.len()) {
            let weight: Ext4 = eq_weight(tau1, i);
            sum = sum + weight * crate::ringswitch::c_eval_at(alpha, s.yvec().get(i));
        }
        i += 1;
    }
    sum
}

// @genesis 77c7d47 2026-09-08 — zerocheck::alpha_contract
/// Eq. (22)'s public contraction of the committed table, at row `i` (spec:
/// `alphaContract` instantiated at `T = wTable`, `Constraints.lean:540`).
///
/// Mirrors `alphaContract`.
///
/// `∑_u ∑_ℓ M̃_α(i, u) · w̃(d·u + ℓ) · α̃(ℓ)` over the `μ + n·δ` table rows and
/// the `d` coefficient columns.
///
/// **Why the table is a witness and not a function.** The specification takes
/// the table as an argument, `T : (Fin m₀ → Fin 2) → F`. A function argument has
/// no translation here -- closures are outside the supported subset -- so this
/// translates the *instantiated* form, and the instantiation is not a choice:
/// `hAlphaEvals_eq_alphaDefect` (`Constraints.lean:771`) is stated at
/// `T = wTable Φ m₀ φF b w`, which is the only instantiation the chain uses.
///
/// The cube point `wTablePoint Φ m₀ b hμn u ℓ` (`:525`) is the flat index
/// `d·u + ℓ`, carrying a proof that it lies in the cube. The proof erases and
/// the arithmetic is what remains, which is exactly the argument
/// [`w_table`] already takes.
///
/// `M̃_α(i, u)` is recomputed inside the `ℓ` loop, where the specification's
/// nested sum puts it. That is deliberate and it is expensive -- one
/// `m_alpha_tilde` can reach `c_eval_at_modulus` -- but hoisting it into an
/// `n × μ` table is the brief's largest identified win on this operation
/// (briefs/target-4-zero-check.md § "The dominant term", item 4), and a
/// baseline that had already hoisted it would report that win as zero forever.
pub fn alpha_contract(
    s: &crate::ringswitch::RlinStatement,
    alpha: Ext4,
    w: &LiftedWitness,
    i: usize,
) -> Ext4 {
    let degree: usize = params::RING_DEGREE;
    let digits: usize = params::GADGET_DIGITS;
    let mu: usize = s.m().cols();
    let rows: usize = s.m().rows();
    let table_rows: usize = mu + rows * digits;
    let mut acc: Ext4 = Ext4::ZERO;
    let mut u: usize = 0;
    while u < table_rows {
        let mut l: usize = 0;
        while l < degree {
            let entry: Ext4 = m_alpha_tilde(s, alpha, i, u);
            let cell: Ext4 = w_table(w, degree * u + l);
            acc = acc + entry * cell * alpha_tilde(alpha, l);
            l += 1;
        }
        u += 1;
    }
    acc
}

// @genesis 77c7d47 2026-09-08 — zerocheck::alpha_defect
/// Eq. (22)'s per-row defect: the public contraction minus the public
/// right-hand side (spec: `alphaDefect` at `T = wTable`,
/// `Constraints.lean:549`).
///
/// Mirrors `alphaDefect`.
///
/// `H_α`'s Boolean table is exactly this at `T = w̃`, which is what
/// `alphaDefect_wTable` (`:620`) and `hAlphaEvals_eq_alphaDefect` (`:771`)
/// prove.
pub fn alpha_defect(
    s: &crate::ringswitch::RlinStatement,
    alpha: Ext4,
    w: &LiftedWitness,
    i: usize,
) -> Ext4 {
    alpha_contract(s, alpha, w, i) - crate::ringswitch::c_eval_at(alpha, s.yvec().get(i))
}

// @genesis 77c7d47 2026-09-08 — zerocheck::h_alpha_evals
/// Entry `idx` of the `H_α` constraint table (spec: `hAlphaEvals`,
/// `Constraints.lean:176`, through `hAlphaEvals_eq_alphaDefect`).
///
/// Mirrors `hAlphaEvals`.
///
/// **This is the computable route to a `noncomputable` definition, and the
/// equivalence is ArkLib's, not ours.** `hAlphaEvals` is
/// `noncomputable def`: its digit term reads `evalAt φF α (…).toPoly`, and
/// `evalAt` is noncomputable (`Transport/Eval.lean:46`). Its defect form is
/// not: `alphaDefect` is a plain `def` built from `mAlphaTilde`, `wTable`,
/// `alphaTilde` and `cEvalAt`, and `hAlphaEvals_eq_alphaDefect`
/// (`Constraints.lean:771`) **proves** the two agree, under `1 < b`,
/// `0 < d` and the coverage bound `hμn` -- all three of which hold at the
/// pinned profile, the last one being ArkLib's own `sumcheckWidthAtProfile`.
///
/// So the `_spec` for this function can be stated against `hAlphaEvals`, the
/// Eq. (22) object the protocol reasons about, and discharged by rewriting with
/// that theorem. Nothing is assumed and no weaker statement is taken.
///
/// It also means `cRowSum` -- the unreduced product of two `CPolynomial`
/// representatives, which would need a 2047-coefficient carrier this crate does
/// not have -- never appears: it occurs only in the noncomputable form.
/// See NOTES.md § "The computable route around `cRowSum`".
///
/// The `idx < n` guard is the specification's own (`:179`): the `m₁` cube is
/// padded above the `n` real rows, and padding contributes zero.
pub fn h_alpha_evals(
    s: &crate::ringswitch::RlinStatement,
    alpha: Ext4,
    w: &LiftedWitness,
    idx: usize,
) -> Ext4 {
    let rows: usize = s.yvec().len();
    if idx < rows {
        alpha_defect(s, alpha, w, idx)
    } else {
        Ext4::ZERO
    }
}

// @genesis 77c7d47 2026-09-08 — zerocheck::h_alpha
/// The `H_α` constraint block in Boolean-evaluation form (spec: `hAlpha`,
/// `Constraints.lean:213`, through the same equivalence).
///
/// Mirrors `hAlpha`.
///
/// `2^m₁` entries -- at the pinned `M_ONE = 3` that is eight, one per row of
/// the batching cube, of which `RLIN_ROWS = 5` are real and three are padding.
pub fn h_alpha(
    s: &crate::ringswitch::RlinStatement,
    alpha: Ext4,
    w: &LiftedWitness,
    m1: usize,
) -> MultilinearEvals {
    let size: usize = two_pow(m1);
    let mut values: Vec<Ext4> = Vec::new();
    let mut i: usize = 0;
    while i < size {
        values.push(h_alpha_evals(s, alpha, w, i));
        i += 1;
    }
    MultilinearEvals::from_values(values)
}

// @genesis 77c7d47 2026-09-08 — zerocheck::h_alpha_is_zero
/// The `H_α` verdict: is every entry zero? (spec: `hAlpha = 0`, in the
/// pointwise form of `hAlpha_eq_zero_iff`, `Constraints.lean:233`).
///
/// Mirrors `hAlpha_eq_zero_iff`.
///
/// Branchless to the end, as [`h_zero_is_zero`] is and for the same reason.
pub fn h_alpha_is_zero(
    s: &crate::ringswitch::RlinStatement,
    alpha: Ext4,
    w: &LiftedWitness,
    m1: usize,
) -> bool {
    let size: usize = two_pow(m1);
    let mut zero: bool = true;
    let mut i: usize = 0;
    while i < size {
        if !h_alpha_evals(s, alpha, w, i).is_zero() {
            zero = false;
        }
        i += 1;
    }
    zero
}

/// `i < 2^m`, decided by halving `i` exactly `m` times.
///
/// Mirrors `alphaPublicEvals` at its cube guard (`Constraints.lean:845`; the
/// same guard appears in `zcTargetAlpha`, `:877`).
///
/// The marker's shape matters: the scanner's regex is
/// ``Mirrors (ArkLib's)? `name` ``, so a word between `Mirrors` and the
/// backticks makes the marker **invisible** rather than wrong. This comment
/// said "Mirrors the `i < 2 ^ m₁` guard of …" for one commit, which the
/// coverage gate could not see (NOTES.md § the `evalsplit` lessons).
///
/// The *predicate*, never the bound: `i < 2^m` holds exactly when `i` shifted
/// right by `m` is zero, and halving is how this crate shifts (`lib.rs`
/// § "Style notes"). The point is that it decides the guard **for any `m`**
/// and cannot fail, where the earlier `i < two_pow(m)` had to build `2^m` as a
/// `usize` first -- a checked doubling -- which is what put
/// `2 ^ m₁ ≤ Usize.max` on the statements of both callers.
///
/// [`two_pow`] itself stays. Its remaining callers size `2^m₀`-entry tables,
/// and there the bound is not an artefact to be removed: a table that does not
/// fit in a `usize` does not fit in memory either, so the caller owes it
/// anyway.
pub fn below_two_pow(i: usize, m: usize) -> bool {
    let mut q: usize = i;
    let mut k: usize = 0;
    while k < m {
        q /= 2;
        k += 1;
    }
    q == 0
}
