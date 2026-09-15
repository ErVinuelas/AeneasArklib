//! The nested sumcheck's round machinery, in the **folded-table value form**.
//!
//! Reference specification:
//! `ArkLib/Commitments/Functional/Hachi/Sumcheck/{RoundPoly,Rounds}.lean`.
//!
//! # This module's baseline is the dense form, and that is a decision
//!
//! Everywhere else in this crate, `benches/genesis` holds the *trivial*
//! translation of the ArkLib definition, so that every later optimization is
//! measured against the specification's own shape. **Target 5 is the one
//! documented exception** (`op-genesis` § "Freezing anything other than the
//! spec's trivial translation", and NOTES.md § "Decision: target 5's genesis
//! holds the dense form").
//!
//! The reason in one line: `computableRoundPoly` (`RoundPoly.lean:246`) builds
//! its argument `H` as a `CMvPolynomial`, a sparse tree map of monomials, and
//! `cRangeProduct` leaves that map with up to `(2b+1)^{m₀}` entries -- `3.0·10^39`
//! at the pinned width, and still `3.9·10^7` at `m₀ = 5` because the blow-up is
//! in `b`, not only in `m₀`. So the naive form does not run at any width that
//! resembles the operation: its bench row would be excluded as infeasible, its
//! `case!` digest could not be computed at all, and it would carry proof debt
//! for a body that never executes.
//!
//! What follows for anyone reading a number from this module: a `vs genesis`
//! figure here measures distance from the **dense** form, never from the
//! specification's shape.
//!
//! The naive shape is not thereby unchecked. It lives in
//! `tests/sumcheck_semantics.rs` at the toy width `b = 3`, `m₀ = 5` (`7^5 =
//! 16 807` monomials), where it *does* run, and the dense form is checked
//! against it there. Same arrangement as the α side, where the unreduced
//! 2047-coefficient carrier lives in the test and nowhere in the crate.
//!
//! # What "folded-table value form" means
//!
//! The identity being translated is between *values*, and it is proved upstream:
//! `computableRoundPoly_eval` (`RoundPoly.lean:316`) says the round polynomial
//! evaluated at `T` is `hypercubeSum` of `H` with the pivot fixed to `T`, and
//! `eval_sumcheckPolyZero` (`ZeroCheck/Constraints.lean:1382`) rewrites that sum
//! into the range factor applied to the table. So instead of building `H`, the
//! prover holds the folded `w̃` table and evaluates:
//!
//! ```text
//! g_i(T) = Σ_y  eq_suffix(y) · P_b( (1 - T)·W[2y] + T·W[2y+1] )
//! ```
//!
//! for each of the `2b + 1` nodes `T`, then interpolates. The fold that produces
//! `W_{i+1}` from `W_i` is cpoly's `eval_mle_layer`, whose pairing of
//! `values[2j]`/`values[2j+1]` eliminates the low bit -- which under the
//! little-endian `finFunctionFinEquiv` is coordinate `0`, exactly the
//! coordinate `hypercubePoint` frees first (`Constraints.lean:852`). The
//! orientation is upstream's, not a choice made here.
//!
//! # What is deliberately *not* done here
//!
//! S1 and S2 of the target-5 brief are prerequisites -- nothing runs without
//! them -- and they are what this module implements. Its remaining
//! optimizations are left for `perf-loop`, so that they stay measurable against
//! this baseline:
//!
//! * `range_product` is called in its literal `(v-j)(v+j)` form, `31`
//!   multiplies. The `v² - j²` form is `16`, a 2× cut on the 94%-dominant term.
//! * the `eq̃` closed form for `finalCheck`'s first factor (`m₀` multiplies
//!   against a `2^{m₀}` sum);
//! * the tensor split of `Ã`, a 1024× cut on the verifier's dominant term;
//! * hoisting the triple `computeG`.

use alloc::vec::Vec;

use cpoly::{Ext4, Fp, UnivariatePoly};

use crate::params;

// @genesis 6b228c5 2026-09-08 — sumcheck::round_node
/// The `i`-th Lagrange node, as an element of the extension field: the integer
/// `i` embedded through `φF` (spec: the nodes of `interpolateArray`,
/// `CompPoly/Univariate/LagrangeArray.lean:48`, at `0 … 2b`).
///
/// Mirrors `CPolynomial.pointNode`.
pub fn round_node(i: usize) -> Ext4 {
    Ext4::from_base(Fp::new(i as u64))
}

// @genesis 6b228c5 2026-09-08 — sumcheck::interpolate
/// Lagrange interpolation from node values (spec: `interpolateArray`,
/// `CompPoly/Univariate/LagrangeArray.lean:48`).
///
/// Mirrors `CPolynomial.interpolateArray`.
///
/// `Σ_i y_i · w_i · ∏_{j ≠ i} (X - x_j)`, with the weights `w_i` supplied by the
/// caller rather than computed: `w_i = (∏_{j≠i}(x_i - x_j))⁻¹`, and no inversion
/// exists at either carrier (see [`params::ROUND_NODE_INV`]). Passing them in
/// keeps this function faithful to the specification's arbitrary node set
/// instead of hard-wiring `0 … 2b`, and keeps the constants auditable in one
/// place.
///
/// The basis product is built by the schoolbook shift-and-subtract the
/// specification's `interpolate` unfolds to, one node at a time.
// `vec![Ext4::ONE]` is what clippy wants for the basis seed below, and this
// crate does not use that macro anywhere the extraction sees: it expands to
// `Vec::from` over a slice, which is alloc machinery with no model, and an
// unmodelled call is an `axiom` in `lean/Generated.lean` (`lib.rs` § "Style
// notes", the same reason `Vec::is_empty` and `Vec::truncate` are avoided).
#[allow(clippy::vec_init_then_push)]
pub fn interpolate(values: &Vec<Ext4>, inv_weights: &Vec<Fp>) -> UnivariatePoly {
    let n: usize = values.len();
    let mut acc: Vec<Ext4> = Vec::new();
    let mut k: usize = 0;
    while k < n {
        acc.push(Ext4::ZERO);
        k += 1;
    }
    let mut i: usize = 0;
    while i < n {
        // basis_i = ∏_{j ≠ i} (X - x_j), built in place: multiply by (X - x_j).
        let mut basis: Vec<Ext4> = Vec::new();
        basis.push(Ext4::ONE);
        let mut j: usize = 0;
        while j < n {
            if j != i {
                let xj: Ext4 = round_node(j);
                let mut next: Vec<Ext4> = Vec::new();
                let mut t: usize = 0;
                while t < basis.len() + 1 {
                    let shifted: Ext4 = if t > 0 { basis[t - 1] } else { Ext4::ZERO };
                    let scaled: Ext4 = if t < basis.len() {
                        basis[t] * xj
                    } else {
                        Ext4::ZERO
                    };
                    next.push(shifted - scaled);
                    t += 1;
                }
                basis = next;
            }
            j += 1;
        }
        let scale: Ext4 = values[i] * Ext4::from_base(inv_weights[i]);
        let mut t: usize = 0;
        while t < basis.len() {
            acc[t] = acc[t] + basis[t] * scale;
            t += 1;
        }
        i += 1;
    }
    UnivariatePoly::from_coeffs(acc)
}

// @genesis 6b228c5 2026-09-08 — sumcheck::round_node_weights
/// The weights for the round nodes, read out of [`params::ROUND_NODE_INV`].
///
/// A `Vec` rather than the array itself because [`interpolate`] takes the
/// specification's arbitrary node set; this is the instantiation at
/// `0 … 2b`.
pub fn round_node_weights() -> Vec<Fp> {
    let n: usize = params::ROUND_NODES;
    let mut out: Vec<Fp> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        out.push(Fp::new(params::ROUND_NODE_INV[i]));
        i += 1;
    }
    out
}

// @genesis 6b228c5 2026-09-08 — sumcheck::round_value_zero
/// One node's worth of the range summand: `Σ_y eq_suffix(y) · P_b(W(T, y))`,
/// where `W(T, y) = (1 - T)·W[2y] + T·W[2y+1]` (spec: `computableRoundPoly` at
/// one node, through `computableRoundPoly_eval` (`RoundPoly.lean:316`) and
/// `eval_sumcheckPolyZero` (`ZeroCheck/Constraints.lean:1382`)).
///
/// Mirrors `computableRoundPoly` (at the `sumcheckPolyZero` summand, one node).
///
/// `w` is the folded `w̃` table of round `i`, of length `2·eq.len()`; the fold
/// pairs `2y`/`2y+1` because that is the orientation `evalMleStep` fixes
/// (`CompPoly/Multilinear/Basic.lean:467`).
pub fn round_value_zero(w: &Vec<Ext4>, eq: &Vec<Ext4>, node: Ext4) -> Ext4 {
    let half: usize = eq.len();
    let one_minus: Ext4 = Ext4::ONE - node;
    let mut acc: Ext4 = Ext4::ZERO;
    let mut y: usize = 0;
    while y < half {
        let lo: Ext4 = w[2 * y];
        let hi: Ext4 = w[2 * y + 1];
        let folded: Ext4 = one_minus * lo + node * hi;
        acc = acc + eq[y] * crate::zerocheck::range_product(folded);
        y += 1;
    }
    acc
}

// @genesis 6b228c5 2026-09-08 — sumcheck::round_values_zero
/// The whole range summand of a round message: its value at every node
/// (spec: `computableRoundPoly` at the `sumcheckPolyZero` summand).
///
/// Mirrors `computableRoundPoly`.
///
/// `2b + 1` nodes, because the summand's per-round degree is `roundDegZero b =
/// 2b` (`ZeroCheck/Constraints.lean:87`) and that many values determine it --
/// which is what `computableRoundPoly_mem_degreeLE` (`RoundPoly.lean:326`) is
/// for on the proof side.
pub fn round_values_zero(w: &Vec<Ext4>, eq: &Vec<Ext4>) -> Vec<Ext4> {
    let nodes: usize = params::ROUND_NODES;
    let mut out: Vec<Ext4> = Vec::new();
    let mut t: usize = 0;
    while t < nodes {
        out.push(round_value_zero(w, eq, round_node(t)));
        t += 1;
    }
    out
}

// @genesis 6b228c5 2026-09-08 — sumcheck::round_poly_zero
/// The range summand as a polynomial: its node values, interpolated
/// (spec: `computableRoundPoly Φ … (sumcheckPolyZero …) i cs`).
///
/// Mirrors `computableRoundPoly`.
pub fn round_poly_zero(w: &Vec<Ext4>, eq: &Vec<Ext4>) -> UnivariatePoly {
    let values: Vec<Ext4> = round_values_zero(w, eq);
    let weights: Vec<Fp> = round_node_weights();
    interpolate(&values, &weights)
}

// @genesis 2152e10 2026-09-09 — sumcheck::cube_size
/// `2^vars`, by doubling.
///
/// A local copy of `zerocheck`'s private helper of the same shape: that one is
/// private and frozen, and widening a frozen item's visibility is not an
/// append. Written as a doubling loop rather than `1 << vars` for the reason
/// [`params::ROUND_NODES`] is a literal -- a shift is a `Result` in the
/// extracted model.
fn cube_size(vars: usize) -> usize {
    let mut sz: usize = 1;
    let mut k: usize = 0;
    while k < vars {
        sz *= 2;
        k += 1;
    }
    sz
}

// @genesis 2152e10 2026-09-09 — sumcheck::eq_prefix
/// The equality kernel over the coordinates the sumcheck has already consumed:
/// `∏_{k < i} eq(τ₀ₖ, aₖ)`, where `i = challenges.len()`
/// (spec: `cEqualityPolynomial m₀ τ₀` restricted to its bound prefix,
/// `ZeroCheck/Constraints.lean:860`).
///
/// Mirrors `cEqualityPolynomial` at its bound prefix.
///
/// This is cpoly's `eq_tilde` (`multilinear.rs:248`) on a *prefix* of `tau0`,
/// and it is written out here rather than reused because reuse would need
/// `&tau0[..i]`: this crate's extracted model contains no subslice operation
/// anywhere, and introducing one for a three-line product is an extraction risk
/// for no gain. [`final_check`], which needs the kernel over *all* of `τ₀`,
/// calls cpoly's function directly.
pub fn eq_prefix(tau0: &Vec<Ext4>, challenges: &Vec<Ext4>) -> Ext4 {
    let i: usize = challenges.len();
    let mut acc: Ext4 = Ext4::ONE;
    let mut k: usize = 0;
    while k < i {
        let t: Ext4 = tau0[k];
        let a: Ext4 = challenges[k];
        acc = acc * (t * a + (Ext4::ONE - t) * (Ext4::ONE - a));
        k += 1;
    }
    acc
}

// @genesis 2152e10 2026-09-09 — sumcheck::eq_suffix_table
/// The equality kernel's hypercube table over the coordinates *after* the free
/// one: entry `y` is `∏_{k > i} eq(τ₀ₖ, y_{k-i-1})`, little-endian in `y`
/// (spec: `cEqualityPolynomial`'s trailing factors, as the table
/// `lagrangeBasis` builds).
///
/// Mirrors `lagrangeBasis` at the suffix coordinates.
///
/// Built by doubling: each coordinate is appended as the new *high* bit, and
/// the coordinates are consumed in increasing order, so `τ₀_{i+1}` ends at bit
/// `0`. That is the orientation `lagrange_basis` uses (bit `j` of the index
/// selects `point[j]`, `multilinear.rs:163`) and the one
/// [`round_value_zero`]'s fold expects, since `eval_mle_layer` folds the
/// least-significant variable (`multilinear.rs:280`).
// `vec![…]` is what clippy wants here (the empty-suffix table is the one-entry vector `[1]`), and this crate does not
// use that macro anywhere the extraction sees: see [`interpolate`].
#[allow(clippy::vec_init_then_push)]
pub fn eq_suffix_table(tau0: &Vec<Ext4>, i: usize) -> Vec<Ext4> {
    let m0: usize = tau0.len();
    let mut tab: Vec<Ext4> = Vec::new();
    tab.push(Ext4::ONE);
    let mut k: usize = i + 1;
    while k < m0 {
        let t: Ext4 = tau0[k];
        let one_minus: Ext4 = Ext4::ONE - t;
        let half: usize = tab.len();
        let mut next: Vec<Ext4> = Vec::new();
        let mut j: usize = 0;
        while j < half {
            next.push(tab[j] * one_minus);
            j += 1;
        }
        let mut j2: usize = 0;
        while j2 < half {
            next.push(tab[j2] * t);
            j2 += 1;
        }
        tab = next;
        k += 1;
    }
    tab
}

// @genesis 2152e10 2026-09-09 — sumcheck::eq_free_factor
/// The free coordinate's own equality factor, as a polynomial in the round
/// variable: `eq(t, X) = (1 - t) + (2t - 1)·X`
/// (spec: `cEqualityPolynomial`'s factor at the free coordinate).
///
/// Mirrors `cEqualityPolynomial` at its free coordinate.
///
/// Degree exactly one, which is the degree `roundDegZero b = 2b` has that
/// [`round_poly_zero`] alone does not: see the module header. `2t` is written
/// `t + t` because the extension carries no integer scalar multiplication.
// `vec![…]` is what clippy wants here (a two-coefficient polynomial), and this crate does not
// use that macro anywhere the extraction sees: see [`interpolate`].
#[allow(clippy::vec_init_then_push)]
pub fn eq_free_factor(t: Ext4) -> UnivariatePoly {
    let mut coeffs: Vec<Ext4> = Vec::new();
    coeffs.push(Ext4::ONE - t);
    coeffs.push(t + t - Ext4::ONE);
    UnivariatePoly::from_coeffs(coeffs)
}

// @genesis 2152e10 2026-09-09 — sumcheck::round_value_alpha
/// One node's worth of the linear summand: `Σ_y W(T, y) · Ã(T, y)`, both tables
/// folded at the same node (spec: `computableRoundPoly` at the
/// `sumcheckPolyAlpha` summand, one node).
///
/// Mirrors `computableRoundPoly` at the `sumcheckPolyAlpha` summand, one node.
///
/// `sumcheckPolyAlpha` is `mle[w̃] * mle[Ã]` (`Constraints.lean:868`) -- a
/// product of two multilinears and *no* equality kernel, which is why this one
/// needs no companion factor and why its per-round degree is
/// `roundDegAlpha = 2` (`:90`) rather than `2b`.
pub fn round_value_alpha(w: &Vec<Ext4>, a_tab: &Vec<Ext4>, node: Ext4) -> Ext4 {
    let half: usize = w.len() / 2;
    let one_minus: Ext4 = Ext4::ONE - node;
    let mut acc: Ext4 = Ext4::ZERO;
    let mut y: usize = 0;
    while y < half {
        let w_folded: Ext4 = one_minus * w[2 * y] + node * w[2 * y + 1];
        let a_folded: Ext4 = one_minus * a_tab[2 * y] + node * a_tab[2 * y + 1];
        acc = acc + w_folded * a_folded;
        y += 1;
    }
    acc
}

// @genesis 2152e10 2026-09-09 — sumcheck::round_values_alpha
/// The whole linear summand of a round message: its value at each of the
/// `roundDegAlpha + 1 = 3` nodes (spec: `computableRoundPoly` at the
/// `sumcheckPolyAlpha` summand).
///
/// Mirrors `computableRoundPoly` at the `sumcheckPolyAlpha` summand.
pub fn round_values_alpha(w: &Vec<Ext4>, a_tab: &Vec<Ext4>) -> Vec<Ext4> {
    let nodes: usize = params::ROUND_NODES_ALPHA;
    let mut out: Vec<Ext4> = Vec::new();
    let mut t: usize = 0;
    while t < nodes {
        out.push(round_value_alpha(w, a_tab, round_node(t)));
        t += 1;
    }
    out
}

// @genesis 2152e10 2026-09-09 — sumcheck::round_node_weights_alpha
/// The weights for the three linear-side nodes, read out of
/// [`params::ROUND_NODE_INV_ALPHA`].
///
/// Separate from [`round_node_weights`] because the weights of a node set
/// depend on the whole set, not on a prefix of it.
pub fn round_node_weights_alpha() -> Vec<Fp> {
    let n: usize = params::ROUND_NODES_ALPHA;
    let mut out: Vec<Fp> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        out.push(Fp::new(params::ROUND_NODE_INV_ALPHA[i]));
        i += 1;
    }
    out
}

// @genesis 2152e10 2026-09-09 — sumcheck::round_poly_alpha
/// The linear summand as a polynomial: its node values, interpolated
/// (spec: `computableRoundPoly Φ … (sumcheckPolyAlpha …) i cs`).
///
/// Mirrors `computableRoundPoly` at the `sumcheckPolyAlpha` summand,
/// interpolated.
pub fn round_poly_alpha(w: &Vec<Ext4>, a_tab: &Vec<Ext4>) -> UnivariatePoly {
    let values: Vec<Ext4> = round_values_alpha(w, a_tab);
    let weights: Vec<Fp> = round_node_weights_alpha();
    interpolate(&values, &weights)
}

// @genesis 2152e10 2026-09-09 — sumcheck::alpha_public_table
/// The public table `Ã` in Boolean-evaluation form: `alphaPublicEvals` at every
/// cube index (spec: `cMultilinearExtension m₀ (alphaPublicEvals …)`,
/// `ZeroCheck/Constraints.lean:871`).
///
/// Mirrors `alphaPublicEvals` as a hypercube table.
///
/// `2^m₀` entries, each one `alphaPublicEvals` call, which is the whole reason
/// the linear side's benchmark rows are REDUCED: at the pinned `m₀ = 26` this
/// table is `6.7·10⁷` extension elements. The tensor split that avoids
/// building it is strategy S6 of the target-5 brief and is `perf-loop`'s.
pub fn alpha_public_table(
    s: &crate::ringswitch::RlinStatement,
    alpha: Ext4,
    tau1: &Vec<Ext4>,
    m0: usize,
) -> Vec<Ext4> {
    let sz: usize = cube_size(m0);
    let mut out: Vec<Ext4> = Vec::new();
    let mut idx: usize = 0;
    while idx < sz {
        out.push(crate::zerocheck::alpha_public_evals(s, alpha, tau1, idx));
        idx += 1;
    }
    out
}

// @genesis 2152e10 2026-09-09 — sumcheck::NestedZeroCheckStmt
/// The zero-check statement the paired sumcheck starts from (spec:
/// `NestedZeroCheckStatement`, `ZeroCheck/Constraints.lean:1407`).
///
/// Mirrors `NestedZeroCheckStatement`.
///
/// `TCom` is instantiated at the concrete chain's commitment type, a `PolyVec`,
/// exactly as in [`crate::endpiece::WEvalStatement`]. The two direct points
/// travel as `Vec`s whose lengths are `m₀` and `m₁`; the specification's
/// `Fin m₀ → F` erases to that, and the lengths become `_spec` hypotheses
/// because Aeneas cannot see a privacy boundary.
pub struct NestedZeroCheckStmt {
    rlin: crate::ringswitch::RlinStatement,
    t: crate::linalg::PolyVec,
    alpha: Ext4,
    tau0: Vec<Ext4>,
    tau1: Vec<Ext4>,
}

impl NestedZeroCheckStmt {
    // @genesis 2152e10 2026-09-09 — sumcheck::NestedZeroCheckStmt::new
    /// Bundle the `R^lin` statement, the commitment, the ring-switching
    /// challenge and the two direct points.
    pub fn new(
        rlin: crate::ringswitch::RlinStatement,
        t: crate::linalg::PolyVec,
        alpha: Ext4,
        tau0: Vec<Ext4>,
        tau1: Vec<Ext4>,
    ) -> NestedZeroCheckStmt {
        NestedZeroCheckStmt {
            rlin,
            t,
            alpha,
            tau0,
            tau1,
        }
    }

    // @genesis 2152e10 2026-09-09 — sumcheck::NestedZeroCheckStmt::rlin
    /// The `R^lin` statement, carrying the public `M`, `yvec` and bound.
    pub fn rlin(&self) -> &crate::ringswitch::RlinStatement {
        &self.rlin
    }

    // @genesis 2152e10 2026-09-09 — sumcheck::NestedZeroCheckStmt::t
    /// The commitment to `w̃` from the lift stage.
    pub fn t(&self) -> &crate::linalg::PolyVec {
        &self.t
    }

    // @genesis 2152e10 2026-09-09 — sumcheck::NestedZeroCheckStmt::alpha
    /// The ring-switching evaluation challenge `α`.
    pub fn alpha(&self) -> Ext4 {
        self.alpha
    }

    // @genesis 2152e10 2026-09-09 — sumcheck::NestedZeroCheckStmt::tau0
    /// The direct range-polynomial evaluation point `τ₀`.
    pub fn tau0(&self) -> &Vec<Ext4> {
        &self.tau0
    }

    // @genesis 2152e10 2026-09-09 — sumcheck::NestedZeroCheckStmt::tau1
    /// The direct linear-polynomial evaluation point `τ_α`.
    pub fn tau1(&self) -> &Vec<Ext4> {
        &self.tau1
    }
}

// @genesis 2152e10 2026-09-09 — sumcheck::RoundMsg
/// A round message: the two computable univariate round polynomials
/// (spec: `RoundMsg`, `Sumcheck/Rounds.lean:65`).
///
/// Mirrors `RoundMsg`.
///
/// The specification's two `degreeLE` subtypes erase: the bounds hold by
/// construction on the prover's side ([`honest_compute_g`] interpolates
/// `2b + 1` resp. `3` nodes) and are what a verifier would re-check on the
/// wire.
pub struct RoundMsg {
    g_zero: UnivariatePoly,
    g_alpha: UnivariatePoly,
}

impl RoundMsg {
    // @genesis 2152e10 2026-09-09 — sumcheck::RoundMsg::new
    /// Pair the two round polynomials.
    pub fn new(g_zero: UnivariatePoly, g_alpha: UnivariatePoly) -> RoundMsg {
        RoundMsg { g_zero, g_alpha }
    }

    // @genesis 2152e10 2026-09-09 — sumcheck::RoundMsg::g_zero
    /// The range summand's round polynomial `g_i^{(0)}`.
    pub fn g_zero(&self) -> &UnivariatePoly {
        &self.g_zero
    }

    // @genesis 2152e10 2026-09-09 — sumcheck::RoundMsg::g_alpha
    /// The linear summand's round polynomial `g_i^{(α)}`.
    pub fn g_alpha(&self) -> &UnivariatePoly {
        &self.g_alpha
    }
}

// @genesis 2152e10 2026-09-09 — sumcheck::RoundStatement
/// The statement after `i` paired-sumcheck rounds (spec:
/// `NestedRoundStatement`, `ZeroCheck/Constraints.lean:1421`).
///
/// Mirrors `NestedRoundStatement`.
///
/// The specification's family is indexed by the round number `i`, whose only
/// computational content is the length of `challenges : Fin i → F`; here that
/// is one struct for every round and `challenges.len() == i` travels as a
/// `_spec` hypothesis. One `push` per round is the erasure of `Fin.snoc`.
pub struct RoundStatement {
    zc: NestedZeroCheckStmt,
    challenges: Vec<Ext4>,
    target_zero: Ext4,
    target_alpha: Ext4,
}

impl RoundStatement {
    // @genesis 2152e10 2026-09-09 — sumcheck::RoundStatement::new
    /// Open a round statement at the two initial targets.
    pub fn new(
        zc: NestedZeroCheckStmt,
        challenges: Vec<Ext4>,
        target_zero: Ext4,
        target_alpha: Ext4,
    ) -> RoundStatement {
        RoundStatement {
            zc,
            challenges,
            target_zero,
            target_alpha,
        }
    }

    // @genesis 2152e10 2026-09-09 — sumcheck::RoundStatement::zc
    /// The zero-check statement carrying the direct evaluation points.
    pub fn zc(&self) -> &NestedZeroCheckStmt {
        &self.zc
    }

    // @genesis 2152e10 2026-09-09 — sumcheck::RoundStatement::challenges
    /// The paired-sumcheck challenges drawn so far.
    pub fn challenges(&self) -> &Vec<Ext4> {
        &self.challenges
    }

    // @genesis 2152e10 2026-09-09 — sumcheck::RoundStatement::target_zero
    /// The current target of the range sumcheck.
    pub fn target_zero(&self) -> Ext4 {
        self.target_zero
    }

    // @genesis 2152e10 2026-09-09 — sumcheck::RoundStatement::target_alpha
    /// The current target of the linear sumcheck.
    pub fn target_alpha(&self) -> Ext4 {
        self.target_alpha
    }
}

// @genesis 2152e10 2026-09-09 — sumcheck::honest_compute_g
/// **The honest round message** (spec: `honestComputeG`,
/// `Sumcheck/Completeness.lean:74`).
///
/// Mirrors `honestComputeG`.
///
/// This is the item that mirrors `computableRoundPoly` of each summand *whole*:
/// it applies the two factors [`round_poly_zero`] leaves out -- the prefix
/// constant [`eq_prefix`] and the free coordinate's [`eq_free_factor`] -- so its
/// range component has degree `2b` and its linear component degree `2`, the
/// specification's two bounds (`ZeroCheck/Constraints.lean:87,90`).
///
/// `w_tab` and `a_tab` are the two tables folded through the `i` challenges
/// already drawn, each of length `2^{m₀-i}`; folding them is [`round_loop`]'s
/// job, and holding them rather than rebuilding `H` is this module's
/// documented dense-form decision (module header).
pub fn honest_compute_g(
    stmt: &RoundStatement,
    w_tab: &Vec<Ext4>,
    a_tab: &Vec<Ext4>,
    i: usize,
) -> RoundMsg {
    let tau0: &Vec<Ext4> = stmt.zc().tau0();
    let prefix: Ext4 = eq_prefix(tau0, stmt.challenges());
    let suffix: Vec<Ext4> = eq_suffix_table(tau0, i);
    let inner: UnivariatePoly = round_poly_zero(w_tab, &suffix);
    let free: UnivariatePoly = eq_free_factor(tau0[i]);
    let with_free: UnivariatePoly = &inner * &free;
    let g_zero: UnivariatePoly = &with_free * prefix;
    let g_alpha: UnivariatePoly = round_poly_alpha(w_tab, a_tab);
    RoundMsg { g_zero, g_alpha }
}

// @genesis 2152e10 2026-09-09 — sumcheck::round_check
/// The round check: both round polynomials sum to the current targets over
/// `{0, 1}` (spec: `roundCheck`, `Sumcheck/Rounds.lean:100`).
///
/// Mirrors `roundCheck`.
///
/// The specification is `Bool`-valued and phrased with `==`, so the translation
/// is an equality of decisions and not an implication -- a verifier that
/// accepted everything would satisfy the accepting direction alone.
pub fn round_check(stmt: &RoundStatement, g: &RoundMsg) -> bool {
    let zero_sum: Ext4 = g.g_zero().eval(Ext4::ZERO) + g.g_zero().eval(Ext4::ONE);
    let alpha_sum: Ext4 = g.g_alpha().eval(Ext4::ZERO) + g.g_alpha().eval(Ext4::ONE);
    zero_sum == stmt.target_zero() && alpha_sum == stmt.target_alpha()
}

// @genesis 2152e10 2026-09-09 — sumcheck::round_out
/// The round's output map: extend the challenge prefix by `a` and replace both
/// targets by the round polynomials' values there (spec: `roundOut`,
/// `Sumcheck/Rounds.lean:109`).
///
/// Mirrors `roundOut`.
///
/// Takes the statement by value and moves its fields into the successor, which
/// is what makes this a straight-line function in the extracted model: the
/// specification builds a new statement of the next index, and a `clone` of the
/// public data would be a trait call with no model.
pub fn round_out(stmt: RoundStatement, g: &RoundMsg, a: Ext4) -> RoundStatement {
    let target_zero: Ext4 = g.g_zero().eval(a);
    let target_alpha: Ext4 = g.g_alpha().eval(a);
    let mut challenges: Vec<Ext4> = stmt.challenges;
    challenges.push(a);
    RoundStatement {
        zc: stmt.zc,
        challenges,
        target_zero,
        target_alpha,
    }
}

// @genesis 2152e10 2026-09-09 — sumcheck::honest_compute_y
/// The honest claimed evaluation `y′ := mle[w̃](a)` (spec: `honestComputeY`,
/// `Sumcheck/FinalEval.lean:246`).
///
/// Mirrors `honestComputeY`.
///
/// Literally `wTableMleEval` at the sumcheck point, which is the whole
/// definition; it is named because the final-evaluation prover's `computeY`
/// parameter is what the completeness theorem is stated about.
pub fn honest_compute_y(
    w: &crate::ringswitch::LiftedWitness,
    m0: usize,
    challenges: &Vec<Ext4>,
) -> Ext4 {
    crate::zerocheck::w_table_mle_eval(w, m0, challenges)
}

// @genesis 2152e10 2026-09-09 — sumcheck::final_check
/// The final check, after the sumcheck has consumed every cube coordinate
/// (spec: `finalCheck`, `Sumcheck/FinalEval.lean:99`).
///
/// Mirrors `finalCheck`.
///
/// Three conjuncts in the specification's order: the range claim
/// `eq̃(τ₀, a)·P_b(y′) = target₀`, the linear claim `y′·Ã(a) = target_α`, and
/// the bound-sanity fact `bound ≤ rlin.bound`. The first factor uses cpoly's
/// `eq_tilde` over the whole of `τ₀` -- the point where [`eq_prefix`]'s prefix
/// form is not needed, since at `i = m₀` the prefix *is* the whole vector.
///
/// This is the first check in the chain that can actually reject: every earlier
/// link's verifier is a pass-through.
pub fn final_check(stmt: &RoundStatement, y_prime: Ext4, bound: u64) -> bool {
    let zc: &NestedZeroCheckStmt = stmt.zc();
    let m0: usize = zc.tau0().len();
    let eq_all: Ext4 = cpoly::multilinear::eq_tilde(zc.tau0(), stmt.challenges());
    let table: Vec<Ext4> = alpha_public_table(zc.rlin(), zc.alpha(), zc.tau1(), m0);
    let a_mle: Ext4 = cpoly::MultilinearEvals::from_values(table).eval(stmt.challenges());
    eq_all * crate::zerocheck::range_product(y_prime) == stmt.target_zero()
        && y_prime * a_mle == stmt.target_alpha()
        && bound <= zc.rlin().bound()
}

// @genesis 2152e10 2026-09-09 — sumcheck::round_loop
/// The `m₀` paired-sumcheck rounds, run honestly against a challenge list
/// (spec: `roundsReductionAux`'s computational residue,
/// `Sumcheck/Completeness.lean:347` and `Sumcheck/Rounds.lean:360`).
///
/// Mirrors `roundsReductionAux`.
///
/// `None` is the specification's `failure`: `roundVerifier` applies `roundOut`
/// on a passing `roundCheck` and fails otherwise (`Rounds.lean:113`). The two
/// tables are folded one coordinate per round with cpoly's `eval_mle_layer`,
/// the fold whose `2j`/`2j+1` pairing eliminates the least-significant variable
/// and so matches [`eq_suffix_table`]'s orientation.
pub fn round_loop(
    stmt: RoundStatement,
    w: &crate::ringswitch::LiftedWitness,
    challenges: &Vec<Ext4>,
) -> Option<RoundStatement> {
    let m0: usize = stmt.zc().tau0().len();
    let mut w_tab: Vec<Ext4> = crate::zerocheck::c_w_table_mle(w, m0).into_values();
    let mut a_tab: Vec<Ext4> = alpha_public_table(
        stmt.zc().rlin(),
        stmt.zc().alpha(),
        stmt.zc().tau1(),
        m0,
    );
    let mut current: RoundStatement = stmt;
    let mut i: usize = 0;
    while i < m0 {
        let g: RoundMsg = honest_compute_g(&current, &w_tab, &a_tab, i);
        if !round_check(&current, &g) {
            return None;
        }
        let a: Ext4 = challenges[i];
        current = round_out(current, &g, a);
        w_tab = cpoly::multilinear::eval_mle_layer(&w_tab, a);
        a_tab = cpoly::multilinear::eval_mle_layer(&a_tab, a);
        i += 1;
    }
    Some(current)
}

// @genesis eca78d0 2026-09-09 — sumcheck::nested_to_round_statement
/// The bridge into the paired sumcheck: install the empty challenge prefix and
/// the initial target pair (spec: `nestedToRoundStatement`,
/// `Sumcheck/Bridge.lean:49`).
///
/// Mirrors `nestedToRoundStatement`.
///
/// Zero-round and pure, like the other three adapter rows of
/// `Composition.lean:244`, so the statement map *is* the row -- there is no
/// check to translate.
///
/// **The range side's initial target is the literal `0`, and that is the
/// content of the row.** `H₀` must vanish identically on the cube, so the
/// range sumcheck opens at zero; the linear side opens at `zcTargetAlpha`,
/// which the verifier computes from the statement alone. Reading the two as
/// symmetric is the mistake this comment exists to prevent: one is a constant
/// the specification fixes, the other is `n` rows of work.
///
/// Takes the zero-check statement **by value** for the reason
/// [`round_out`] does: the specification builds a statement of the next index,
/// and a `clone` of the carried public data would be a trait call with no
/// extracted model. The borrow for `zc_target_alpha` ends before the move.
pub fn nested_to_round_statement(zc: NestedZeroCheckStmt) -> RoundStatement {
    let target_alpha: Ext4 = crate::zerocheck::zc_target_alpha(zc.rlin(), zc.alpha(), zc.tau1());
    RoundStatement::new(zc, Vec::new(), Ext4::ZERO, target_alpha)
}

// ---------------------------------------------------------------------------
// The rounds, split into the prover's and the verifier's halves (chain row 8)
// ---------------------------------------------------------------------------

// @genesis 821a5f8 2026-09-10 — sumcheck::honest_round_messages
/// The honest prover's side of the `m₀` paired-sumcheck rounds: the messages
/// `g₁, …, g_{m₀}` the verifier receives, computed against a challenge list
/// (spec: `roundProver`'s `sendMessage` at `computeG := honestComputeG`, one
/// per round of `roundsReductionAux`, `Sumcheck/Rounds.lean:157-171` and
/// `Sumcheck/Completeness.lean:347`).
///
/// Mirrors `roundProver` at `computeG := honestComputeG`, over every round.
///
/// [`round_loop`] is the *reduction's* honest execution -- prover and
/// verifier fused, `roundsReductionAux`'s residue -- and it returns only the
/// final statement, so a verifier cannot be handed its messages. This is the
/// prover's half on its own: the same tables, the same folds, the same
/// `round_out` threading (the prover carries the statement too,
/// `roundProver.output`), but what comes out is the wire content. The
/// verifier's half is [`round_verify_loop`]; `tests/sumcheck_semantics.rs`
/// checks that the two halves together reproduce [`round_loop`].
///
/// `challenges` must hold at least `m₀` entries; the specification's
/// `roundsSpec F b count` types that, and here it travels as a `_spec`
/// hypothesis.
pub fn honest_round_messages(
    stmt: RoundStatement,
    w: &crate::ringswitch::LiftedWitness,
    challenges: &Vec<Ext4>,
) -> Vec<RoundMsg> {
    let m0: usize = stmt.zc().tau0().len();
    let mut w_tab: Vec<Ext4> = crate::zerocheck::c_w_table_mle(w, m0).into_values();
    let mut a_tab: Vec<Ext4> = alpha_public_table(
        stmt.zc().rlin(),
        stmt.zc().alpha(),
        stmt.zc().tau1(),
        m0,
    );
    let mut current: RoundStatement = stmt;
    let mut out: Vec<RoundMsg> = Vec::new();
    let mut i: usize = 0;
    while i < m0 {
        let g: RoundMsg = honest_compute_g(&current, &w_tab, &a_tab, i);
        let a: Ext4 = challenges[i];
        current = round_out(current, &g, a);
        w_tab = cpoly::multilinear::eval_mle_layer(&w_tab, a);
        a_tab = cpoly::multilinear::eval_mle_layer(&a_tab, a);
        out.push(g);
        i += 1;
    }
    out
}

// @genesis 821a5f8 2026-09-10 — sumcheck::round_verify_loop
/// The verifier's side of the `m₀` paired-sumcheck rounds: `roundCheck` on
/// each received message, `roundOut` on a pass, `failure` on the first
/// rejection (spec: `roundVerifier`, `Sumcheck/Rounds.lean:116-123`, one per
/// round of `roundsChain`, `:402`).
///
/// Mirrors `roundVerifier`, over every round.
///
/// This is the only thing the composed verifier does in row 8. It holds no
/// witness and no table: the messages arrive over the wire, and each round
/// costs four evaluations of a univariate polynomial of degree at most `2b`.
/// The `Option` is the specification's `failure` -- `roundVerifier` fails the
/// round it rejects in, and there is no later round to run.
///
/// The specification's `RoundMsg` carries its two degree bounds as subtypes,
/// so a message of the wrong degree is not a value of the wire type at all;
/// here the bounds are the erasure recorded on [`RoundMsg`], and a
/// `_spec` hypothesis, not a runtime check. `msgs` and `challenges` must hold
/// at least `m₀` entries each, as `roundsSpec F b count` types.
pub fn round_verify_loop(
    stmt: RoundStatement,
    msgs: &Vec<RoundMsg>,
    challenges: &Vec<Ext4>,
) -> Option<RoundStatement> {
    let m0: usize = stmt.zc().tau0().len();
    let mut current: RoundStatement = stmt;
    let mut i: usize = 0;
    while i < m0 {
        let g: &RoundMsg = &msgs[i];
        if !round_check(&current, g) {
            return None;
        }
        let a: Ext4 = challenges[i];
        current = round_out(current, g, a);
        i += 1;
    }
    Some(current)
}

/// One node's worth of the range summand at round 0, the table in the base
/// field: `Σ_y P_b((1 − T)·w[2y] + T·w[2y+1]) · eq[y]` with the fold and `P_b`
/// in `Fp` (opt: `HachiEquiv.Opt.rangeSumZeroBase`, its loop
/// `rangeSumZeroBase.loop`; lemma `rangeSumZeroBase_eq` against `rangeSumZero`).
///
/// [`round_value_zero`] on the embedded table at the embedded node, computed
/// with `2 + 16` base-field multiplications per cube point plus the one scaling
/// by `eq[y]` (four), against `2 + 16 + 1` extension ones (`19` each).
pub fn round_value_zero_base(w: &Vec<Fp>, eq: &Vec<Ext4>, node: Fp) -> Ext4 {
    let half: usize = eq.len();
    let one_minus: Fp = Fp::ONE - node;
    let mut acc: Ext4 = Ext4::ZERO;
    let mut y: usize = 0;
    while y < half {
        let lo: Fp = w[2 * y];
        let hi: Fp = w[2 * y + 1];
        let folded: Fp = one_minus * lo + node * hi;
        let p: Fp = crate::zerocheck::range_product_base(folded);
        acc = acc + p * eq[y];
        y += 1;
    }
    acc
}

/// The range summand's value at every node, round 0, base-field table
/// (opt: `HachiEquiv.Opt.roundValuesZeroBase`; lemma `roundValuesZeroBase_eq`).
///
/// [`round_values_zero`] with the node passed as the base-field element
/// `Fp::new(t)` that [`round_node`] embeds: `phiF_natCast_node` says the two
/// agree.
pub fn round_values_zero_base(w: &Vec<Fp>, eq: &Vec<Ext4>) -> Vec<Ext4> {
    let nodes: usize = params::ROUND_NODES;
    let mut out: Vec<Ext4> = Vec::new();
    let mut t: usize = 0;
    while t < nodes {
        out.push(round_value_zero_base(w, eq, Fp::new(t as u64)));
        t += 1;
    }
    out
}

/// The range summand as a polynomial at round 0: [`round_values_zero_base`]
/// interpolated with the same weights [`round_poly_zero`] uses.
pub fn round_poly_zero_base(w: &Vec<Fp>, eq: &Vec<Ext4>) -> UnivariatePoly {
    let values: Vec<Ext4> = round_values_zero_base(w, eq);
    let weights: Vec<Fp> = round_node_weights();
    interpolate(&values, &weights)
}

/// One node's worth of the linear summand at round 0: the `w̃` fold in the base
/// field scaling the `Ã` fold in the extension
/// (opt: `HachiEquiv.Opt.linSumAlphaBase`; lemma `linSumAlphaBase_eq`).
///
/// [`round_value_alpha`] on the embedded table at the embedded node. `Ã`
/// carries `α` and `τ₁`, so its fold stays in `Ext4`; the product is one
/// `Fp × Ext4` scaling.
pub fn round_value_alpha_base(w: &Vec<Fp>, a_tab: &Vec<Ext4>, node: Fp) -> Ext4 {
    let half: usize = w.len() / 2;
    let one_minus: Fp = Fp::ONE - node;
    let node_ext: Ext4 = Ext4::from_base(node);
    let one_minus_ext: Ext4 = Ext4::ONE - node_ext;
    let mut acc: Ext4 = Ext4::ZERO;
    let mut y: usize = 0;
    while y < half {
        let w_folded: Fp = one_minus * w[2 * y] + node * w[2 * y + 1];
        let a_folded: Ext4 = one_minus_ext * a_tab[2 * y] + node_ext * a_tab[2 * y + 1];
        acc = acc + w_folded * a_folded;
        y += 1;
    }
    acc
}

/// The linear summand's value at its three nodes, round 0, base-field table:
/// [`round_values_alpha`] with the node as `Fp::new(t)`.
pub fn round_values_alpha_base(w: &Vec<Fp>, a_tab: &Vec<Ext4>) -> Vec<Ext4> {
    let nodes: usize = params::ROUND_NODES_ALPHA;
    let mut out: Vec<Ext4> = Vec::new();
    let mut t: usize = 0;
    while t < nodes {
        out.push(round_value_alpha_base(w, a_tab, Fp::new(t as u64)));
        t += 1;
    }
    out
}

/// The linear summand as a polynomial at round 0: [`round_values_alpha_base`]
/// interpolated with [`round_node_weights_alpha`].
pub fn round_poly_alpha_base(w: &Vec<Fp>, a_tab: &Vec<Ext4>) -> UnivariatePoly {
    let values: Vec<Ext4> = round_values_alpha_base(w, a_tab);
    let weights: Vec<Fp> = round_node_weights_alpha();
    interpolate(&values, &weights)
}

/// The one mixed layer fold: a base-field table folded at an extension-field
/// challenge, `out[j] = w[2j]·(1 − x₀) + w[2j+1]·x₀`
/// (opt: `HachiEquiv.Opt.evalMleLayerBase`; lemma `evalMleLayerBase_eq` against
/// `fold`, the conclusion `eval_mle_layer_spec` delivers).
///
/// `cpoly::multilinear::eval_mle_layer` on the embedded table: two `Fp × Ext4`
/// scalings (eight `Fp` multiplications) per output entry against two
/// extension multiplications (thirty-eight). Its output is round 1's `w̃`
/// table, an ordinary `Vec<Ext4>` from here on.
pub fn eval_mle_layer_base(values: &Vec<Fp>, x0: Ext4) -> Vec<Ext4> {
    let half: usize = values.len() / 2;
    let one_minus: Ext4 = Ext4::ONE - x0;
    let mut out: Vec<Ext4> = Vec::with_capacity(half);
    let mut j: usize = 0;
    while j < half {
        let lo: Fp = values[2 * j];
        let hi: Fp = values[2 * j + 1];
        out.push(lo * one_minus + hi * x0);
        j += 1;
    }
    out
}

/// [`honest_compute_g`] at round `0`, the `w̃` table in the base field: the same
/// two factors applied to [`round_poly_zero_base`], and [`round_poly_alpha_base`]
/// for the linear component. `i = 0` is fixed, because round 0 is the only round
/// whose table is base-field; the prefix kernel is the empty product and is
/// still computed by [`eq_prefix`] so that this body is the one above with the
/// index substituted and nothing else.
pub fn honest_compute_g_base(
    stmt: &RoundStatement,
    w_fp: &Vec<Fp>,
    a_tab: &Vec<Ext4>,
) -> RoundMsg {
    let tau0: &Vec<Ext4> = stmt.zc().tau0();
    let prefix: Ext4 = eq_prefix(tau0, stmt.challenges());
    let suffix: Vec<Ext4> = eq_suffix_table(tau0, 0);
    let inner: UnivariatePoly = round_poly_zero_base(w_fp, &suffix);
    let free: UnivariatePoly = eq_free_factor(tau0[0]);
    let with_free: UnivariatePoly = &inner * &free;
    let g_zero: UnivariatePoly = &with_free * prefix;
    let g_alpha: UnivariatePoly = round_poly_alpha_base(w_fp, a_tab);
    RoundMsg { g_zero, g_alpha }
}
