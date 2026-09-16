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
use crate::ring::Rq;
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

/// Hachi Eq. (23)'s per-entry range factor `P_b(v) = v·∏_{j=1}^{b-1} (v−j)(v+j)`
/// (spec: `rangeProduct`, `Constraints.lean:96`; opt:
/// `HachiEquiv.Opt.range_product.opt`, `lean/Opt.lean`).
///
/// Mirrors `rangeProduct`.
///
/// The vanishing polynomial of the symmetric range `{−(b−1), …, b−1}`, so
/// `P_b(v) = 0` says exactly that `v` is the image of an integer in that range
/// (`rangeProduct_eq_zero_iff`, `Constraints.lean:102`).
///
/// The body folds each factor pair by `(v − j)(v + j) = v² − j²`: the square is
/// computed once and each factor is one multiplication by `v² − j²`, the `j²` a
/// base-field literal -- sixteen extension multiplications and no additions
/// where the frozen form paid thirty and fifteen (Stage 6 I5, candidate F;
/// `range_product.opt_eq_spec` says the value is `rangeProduct`'s). This is
/// ~90% of a sumcheck round's multiplications, which is why the identity is
/// worth a champion; the zero-check table builders take the same identity in
/// the base field through [`range_product_base`]. `j * j` is a `u64` product
/// below `256`, its checked-multiplication side condition immediate from
/// `j < b = 16`.
///
/// The loop runs `1 ≤ j < b` rather than `1 ≤ j ≤ b − 1`: the two index sets
/// are the same `Finset.Icc 1 (b - 1)`, but `b − 1` is never formed, so the
/// extracted model carries no subtraction to discharge (`lib.rs`
/// § "Style notes"; the same reason `params::GAMMA` is a literal).
pub fn range_product(v: Ext4) -> Ext4 {
    // `Q(x) = ∏_{j=1}^{15}(x − j²)` by Paterson–Stockmeyer with block 4, at
    // `x = v²` (Stage 6 candidate T2a; opt:
    // `HachiEquiv.Opt.range_product.opt`, `lean/Opt.lean`).
    //
    // Candidate F's form evaluated the product literally: one squaring and 15
    // general `Ext4` multiplications, one per factor. `Q`'s coefficients are
    // constants once `b` is pinned ([`params::RANGE_Q_COEFFS`]), so the same
    // value comes out of four powers of `x`, four coefficient blocks and three
    // Horner steps: **8** general multiplications and 12 base-by-extension
    // ones, which are a quarter the work each (4 base products against 16).
    let x: Ext4 = v * v;
    let x2: Ext4 = x * x;
    let x3: Ext4 = x2 * x;
    let x4: Ext4 = x2 * x2;
    // The top block `A_3`, peeled so the first Horner step is not `0 · x4`.
    let mut acc: Ext4 = Ext4::from_base(Fp::new(params::RANGE_Q_COEFFS[12]))
        + Fp::new(params::RANGE_Q_COEFFS[13]) * x
        + Fp::new(params::RANGE_Q_COEFFS[14]) * x2
        + Fp::new(params::RANGE_Q_COEFFS[15]) * x3;
    let mut i: usize = 3;
    while i > 0 {
        i -= 1;
        let b: usize = 4 * i;
        let blk: Ext4 = Ext4::from_base(Fp::new(params::RANGE_Q_COEFFS[b]))
            + Fp::new(params::RANGE_Q_COEFFS[b + 1]) * x
            + Fp::new(params::RANGE_Q_COEFFS[b + 2]) * x2
            + Fp::new(params::RANGE_Q_COEFFS[b + 3]) * x3;
        acc = acc * x4 + blk;
    }
    v * acc
}

/// The range factor computed in the base field: `P_b(c)` over `Fp`, for the
/// callers whose argument is an `Ext4::from_base` (spec: `rangeProduct` at an
/// embedded argument, through `HachiEquiv.Opt.phiF_range_product_base`; opt:
/// `HachiEquiv.Opt.range_product_base.opt`, `lean/Opt.lean`).
///
/// `φF` is a ring homomorphism, so `P_b(φF c) = φF(P_b^{Fp}(c))`: the product
/// belongs in `Fp` and the embedding happens once, at the caller. [`h_zero`]
/// and [`h_zero_is_zero`] are the two call sites (Stage 6 I5, candidate G);
/// [`range_product`] stays for the sumcheck callers, whose arguments are
/// general extension elements. The two symmetric factors are contracted as
/// `(c − j)(c + j) = c² − j²` (candidate F's shape): one squaring plus `b − 1`
/// multiplications and no additions. `j · j ≤ 225` at `b = GADGET_BASE`, so the
/// checked product's side condition is immediate and `Fp::new` never reduces.
///
/// No `Mirrors` line: this is the crate's own optimized variant, not an ArkLib
/// definition, so the coverage gate does not pair it with a row.
pub fn range_product_base(c: Fp) -> Fp {
    let base: u64 = params::GADGET_BASE;
    let c2: Fp = c * c;
    let mut acc: Fp = c;
    let mut j: u64 = 1;
    while j < base {
        let sq: u64 = j * j;
        let d: Fp = c2 - Fp::new(sq);
        acc = acc * d;
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
/// would zero that gain out of the baseline forever. That hoist landed in
/// Stage 6 iteration 1 as [`w_table_row`]; the table builders read rows through
/// it, and this entrywise reader stays as the specification's own shape.
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

/// Row `u` of the committed table `w̃`, as one [`Rq`]: the three branches of
/// `wTable` (`Constraints.lean:140`) read at the row rather than at the entry
/// (opt: `HachiEquiv.ZeroCheck.wTableRow`, the pure row function the Stage 6
/// candidate introduced -- it lives in `lean/ZeroCheck.lean` because
/// `lean/Opt.lean` imports that file, so the specs cannot cite `Opt`).
///
/// This is the `d = 1024`× hoist the [`w_table`] docstring reserves for the
/// loop: on a digit row, `w_table` rebuilt the whole `rhoDigits` polynomial --
/// 1024 digit extractions -- per entry, and this helper builds it once per row.
/// Entry `idx` of the table is coefficient `idx % d` of row `idx / d`
/// (`ZeroCheck.wTableFlat_eq_row`), which is what the three table builders
/// below stream. The `z` branch is the one that pays for the helper owning its
/// result: one `Fp` copy per entry where `w_table` read through a borrow.
///
/// No `Mirrors` line: `wTableRow` is this crate's own optimized variant, not an
/// ArkLib definition, so the coverage gate does not pair it with a row.
pub fn w_table_row(w: &LiftedWitness, u: usize) -> Rq {
    let digits: usize = params::GADGET_DIGITS;
    let mu: usize = w.z().len();
    let rows: usize = w.rho().len();
    if u < mu {
        w.z().get(u).copy()
    } else if u - mu < rows * digits {
        let j: usize = u - mu;
        rho_digit_as_rq(w.rho(), j)
    } else {
        Rq::zero()
    }
}

/// The committed table `w̃` as a plain value vector, row block by row block
/// (opt: `HachiEquiv.Opt.c_w_table_mle.opt`, `lean/Opt.lean`).
///
/// Outer loop over rows, inner loop over the `d` coefficients of the row; the
/// inner guard's second conjunct truncates the last block so that exactly
/// `2^m₀` values are produced for every `m0`, `μ`, `n` -- the same table as the
/// entrywise construction, with no hypothesis the specification lacks. `idx` is
/// the running flat index `d·u + l` of the Lean `blockLoop`'s `base + l`,
/// carried as one counter: a checked `base + d` step would have strengthened
/// the specs' `2^m₀ ≤ Usize.max` to `2^m₀ + d ≤ Usize.max`. The inner loop
/// exits only at `idx = d·u + d` or at `idx = size`, so at every outer-loop
/// entry `idx = min(d·u, size)` and the guard `idx < size` is the Lean
/// `rowLoop`'s `base < size` -- the fact the outer loop's invariant proves.
fn c_w_table_mle_values(w: &LiftedWitness, m0: usize) -> Vec<Ext4> {
    let size: usize = two_pow(m0);
    let degree: usize = params::RING_DEGREE;
    let mut values: Vec<Ext4> = Vec::with_capacity(size);
    let mut u: usize = 0;
    let mut idx: usize = 0;
    while idx < size {
        let r: Rq = w_table_row(w, u);
        let mut l: usize = 0;
        while l < degree && idx < size {
            values.push(Ext4::from_base(r.coeff(l)));
            l += 1;
            idx += 1;
        }
        u += 1;
    }
    values
}

/// The committed table `w̃` as a plain **base-field** value vector: the same
/// row-block traversal as [`c_w_table_mle_values`] with the embedding left
/// out (opt: `HachiEquiv.Opt.c_w_table_mle.opt` entrywise under `φF`,
/// `lean/Opt.lean` § "Candidate I").
///
/// Every entry of `w̃` is `φF` of a witness coefficient
/// (`Constraints.lean:146,148`), so at round 0 of the sumcheck -- before any
/// extension-field challenge has touched the table -- the table *is* this
/// vector, and [`crate::sumcheck::honest_round_messages`] computes its first
/// round on it in the base field. One `u64` per entry against four: `2^m₀`
/// words, 512 MiB at the pinned `M_ZERO = 26` where the embedded table is
/// 2.0 GiB.
pub fn c_w_table_fp(w: &LiftedWitness, m0: usize) -> Vec<Fp> {
    let size: usize = two_pow(m0);
    let degree: usize = params::RING_DEGREE;
    let mut values: Vec<Fp> = Vec::with_capacity(size);
    let mut u: usize = 0;
    let mut idx: usize = 0;
    while idx < size {
        let r: Rq = w_table_row(w, u);
        let mut l: usize = 0;
        while l < degree && idx < size {
            values.push(r.coeff(l));
            l += 1;
            idx += 1;
        }
        u += 1;
    }
    values
}

/// The committed table `w̃` as a multilinear extension in Lagrange form
/// (spec: `cWTableMle`, `Constraints.lean:328`; opt: `HachiEquiv.Opt.optEvals`
/// over `c_w_table_mle.opt`, `lean/Opt.lean`).
///
/// Mirrors `cWTableMle`.
///
/// `2^m₀` entries: at the pinned `M_ZERO = 26` that is `67 108 864` `Ext4`
/// values, 2.0 GiB, which is why `m0` is an argument. Built row by row through
/// [`c_w_table_mle_values`]; `c_w_table_mle.opt_eq_spec` says the entries are
/// the specification's, so the `Mirrors` line above is still the truth.
pub fn c_w_table_mle(w: &LiftedWitness, m0: usize) -> MultilinearEvals {
    let values: Vec<Ext4> = c_w_table_mle_values(w, m0);
    MultilinearEvals::from_values(values)
}

/// The evaluation claim `mle[w̃](a)` carried into the final-evaluation step
/// (spec: `wTableMleEval`, `Constraints.lean:335`; opt:
/// `HachiEquiv.Opt.w_table_mle_eval.opt`, `lean/Opt.lean`).
///
/// Mirrors `wTableMleEval`.
///
/// The specification names `CMlPolynomialEval.eval`, the `O(m₀·2^m₀)` dot
/// against the Lagrange basis; this body is the `O(2^m₀)` layer fold
/// `CMlPolynomialEval.evalMle`, which CompPoly proves equal
/// (`CMlPolynomialEval.eval_mle_eq_eval`, `Multilinear/Basic.lean:574`) and
/// `w_table_mle_eval.opt_eq_spec` carries to the row-built table. The fold is
/// written here rather than through `MultilinearEvals::eval_mle`, whose body
/// `clone`s its table -- an operation the extraction does not model.
/// `cpoly::multilinear::eval_mle_layer` folds variable `j` of the point.
pub fn w_table_mle_eval(w: &LiftedWitness, m0: usize, a: &Vec<Ext4>) -> Ext4 {
    let vars: usize = a.len();
    let mut cur: Vec<Ext4> = c_w_table_mle_values(w, m0);
    let mut j: usize = 0;
    while j < vars {
        cur = cpoly::multilinear::eval_mle_layer(&cur, a[j]);
        j += 1;
    }
    cur[0]
}

/// The range-constraint block `H₀` in Boolean-evaluation form
/// (spec: `hZero`, `Constraints.lean:204`; opt: `HachiEquiv.Opt.h_zero.opt2`,
/// `lean/Opt.lean` -- the row-hoisted traversal of candidate B with the range
/// factor computed in the base field by [`range_product_base`] and embedded
/// once, candidate G).
///
/// Mirrors `hZero`.
///
/// Entry `x` is `P_b(w̃(x))`; the vector is the unique multilinear extension of
/// those `2^m₀` values. Streamed row by row, as [`c_w_table_mle_values`] is,
/// with the range factor applied to each entry as it is produced.
pub fn h_zero(w: &LiftedWitness, m0: usize) -> MultilinearEvals {
    let size: usize = two_pow(m0);
    let degree: usize = params::RING_DEGREE;
    let mut values: Vec<Ext4> = Vec::with_capacity(size);
    let mut u: usize = 0;
    let mut idx: usize = 0;
    while idx < size {
        let r: Rq = w_table_row(w, u);
        let mut l: usize = 0;
        while l < degree && idx < size {
            values.push(Ext4::from_base(range_product_base(r.coeff(l))));
            l += 1;
            idx += 1;
        }
        u += 1;
    }
    MultilinearEvals::from_values(values)
}

/// The zero-check's own verdict: is every entry of `H₀` zero?
/// (spec: `hZero = 0`, in the pointwise form of `hZero_eq_zero_iff`,
/// `Constraints.lean:219`; opt: `HachiEquiv.Opt.h_zero_is_zero.opt2`,
/// `lean/Opt.lean` -- candidate B's traversal with the range factor and its
/// zero test in the base field, candidate G: `φF y = 0 ↔ y = 0`).
///
/// Mirrors `hZero_eq_zero_iff`.
///
/// Runs branchless to the end rather than returning early, the shape
/// `ring::Rq::equals` and `commit`'s checks already use: the decision procedure
/// the equivalence proof mirrors is a fold over all entries, and an early
/// return would make the extracted model a different recursion. Streamed row
/// by row like [`h_zero`].
pub fn h_zero_is_zero(w: &LiftedWitness, m0: usize) -> bool {
    let size: usize = two_pow(m0);
    let degree: usize = params::RING_DEGREE;
    let mut zero: bool = true;
    let mut u: usize = 0;
    let mut idx: usize = 0;
    while idx < size {
        let r: Rq = w_table_row(w, u);
        let mut l: usize = 0;
        while l < degree && idx < size {
            if !range_product_base(r.coeff(l)).is_zero() {
                zero = false;
            }
            l += 1;
            idx += 1;
        }
        u += 1;
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
/// [`crate::gadget::base_pow`]. The `d`-entry power *table* this docstring
/// reserved for the loop landed in Stage 6 iteration 1 as
/// [`alpha_pow_table`]; the cube traversals read `α^ℓ` through it, and this
/// entrywise reader stays as the specification's own shape.
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
///
/// The tabulated form, which hoists `φ(α)` and the `b^e` powers out of the
/// entry, is [`m_alpha_table`] (Stage 6 iteration 1); this entrywise reader
/// stays as the specification's own shape, and is what [`alpha_contract`]
/// still streams.
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
///
/// It is decided by [`below_two_pow`], which halves `i` and never forms the
/// cube size. An earlier version bound `cube = two_pow(tau1.len())` and
/// compared against it; that local was the only fallible arithmetic in this
/// function, and carrying it meant `2 ^ m₁ ≤ Usize.max` on the statement of a
/// function that never needs the number -- only the predicate.
///
/// [`crate::sumcheck::alpha_public_table`] no longer routes through this
/// function: since Stage 6 iteration 1 it builds [`alpha_pow_table`],
/// [`eq_weight_table`] and [`m_alpha_table`] once and reads them. This stays as
/// the entrywise reference the two are proved equal to, and as the `Mirrors`
/// row the coverage gate pairs with `alphaPublicEvals`.
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

/// The `d`-entry power table `[α^0, …, α^(d−1)]` (the values of `alphaTilde`,
/// `Constraints.lean:502`, tabulated; opt: `HachiEquiv.Opt.alphaPowTable`,
/// `lean/Opt.lean`, licensed entrywise by `alphaPowTable_getD`).
///
/// One multiplication per entry -- a running power -- where [`alpha_tilde`]
/// pays `ℓ` per call; the table exists so that a cube traversal reads `α^ℓ`
/// instead of recomputing it `2^m₀` times. No `Mirrors` line: the table is
/// this crate's own optimized variant, not an ArkLib definition.
pub fn alpha_pow_table(alpha: Ext4, d: usize) -> Vec<Ext4> {
    let mut out: Vec<Ext4> = Vec::with_capacity(d);
    let mut pw: Ext4 = Ext4::ONE;
    let mut l: usize = 0;
    while l < d {
        out.push(pw);
        pw = pw * alpha;
        l += 1;
    }
    out
}

/// The `n`-entry table of `m₁`-cube equality weights: entry `i` is
/// [`eq_weight`]`(τ₁, i)` under the specification's `i < 2^m₁` guard and `0`
/// above it (the `∏ j : Fin m₁` factor of `alphaPublicEvals`,
/// `Constraints.lean:845-847`; opt: `HachiEquiv.Opt.eqWeightTable`,
/// `lean/Opt.lean`, licensed by `eqWeightTable_getD`).
///
/// The guard is decided by [`below_two_pow`], as [`alpha_public_evals`] decides
/// it, so no power of two is formed. No `Mirrors` line, for the reason
/// [`alpha_pow_table`] gives.
pub fn eq_weight_table(tau1: &Vec<Ext4>, n: usize) -> Vec<Ext4> {
    let vars: usize = tau1.len();
    let mut out: Vec<Ext4> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        if below_two_pow(i, vars) {
            out.push(eq_weight(tau1, i));
        } else {
            out.push(Ext4::ZERO);
        }
        i += 1;
    }
    out
}

/// The public constraint matrix at `α`, tabulated: `n` rows of `μ + n·δ`
/// columns, entry `(i, u)` the value of [`m_alpha_tilde`]`(s, α, i, u)` (spec:
/// `mAlphaTilde`, `Constraints.lean:517`; opt: `HachiEquiv.Opt.mAlphaTable`,
/// `lean/Opt.lean`, licensed by `mAlphaTable_getD`).
///
/// `φ(α)` is evaluated once for the whole table rather than once per digit
/// column, and `b^e` is read from a `δ`-entry power table rather than
/// recomputed by [`crate::gadget::base_pow`]. Columns `u ≥ μ + n·δ` are not
/// stored: `mAlphaTilde` is `0` there (`mAlphaTilde_eq_zero_of_ge`, which
/// together with `mAlphaTable_getD_eq` is what `alpha_public_table.opt_eq_spec`
/// reads), and a caller reads them as `Ext4::ZERO`. Every row is exactly
/// `μ + n·δ` wide: a caller that guards its own column index against a
/// *separately computed* `μ + n·δ` -- as [`crate::sumcheck::alpha_public_table`]
/// does -- depends on that width for panic-freedom and not only for the value.
/// Rows of rows, as `linalg::PolyMatrix` is, and as the Lean `List (List F)` it
/// translates. No `Mirrors` line, for the reason [`alpha_pow_table`] gives.
pub fn m_alpha_table(s: &crate::ringswitch::RlinStatement, alpha: Ext4) -> Vec<Vec<Ext4>> {
    let digits: usize = params::GADGET_DIGITS;
    let mu: usize = s.m().cols();
    let rows: usize = s.m().rows();
    let cols: usize = mu + rows * digits;
    let phi_alpha: Ext4 = crate::ringswitch::c_eval_at_modulus(alpha);
    let base: Ext4 = Ext4::from_base(crate::gadget::base_pow(1));
    let bp: Vec<Ext4> = alpha_pow_table(base, digits);
    let mut out: Vec<Vec<Ext4>> = Vec::with_capacity(rows);
    let mut i: usize = 0;
    while i < rows {
        let mut row: Vec<Ext4> = Vec::with_capacity(cols);
        let mut u: usize = 0;
        while u < cols {
            if u < mu {
                row.push(crate::ringswitch::c_eval_at(alpha, s.m().row(i).get(u)));
            } else if (u - mu) / digits == i {
                let e: usize = (u - mu) % digits;
                row.push((Ext4::ZERO - phi_alpha) * bp[e]);
            } else {
                row.push(Ext4::ZERO);
            }
            u += 1;
        }
        out.push(row);
        i += 1;
    }
    out
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
/// (the target-4 brief § "The dominant term", item 4), and a
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
