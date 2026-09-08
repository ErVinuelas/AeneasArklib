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
