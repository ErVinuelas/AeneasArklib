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
//! g_i(T) = eq̃(τ₀|<i, a) · eq(τ₀ᵢ, T) · Σ_y eq̃(τ₀|>i, y) · P_b( (1-T)·W[2y] + T·W[2y+1] )
//! ```
//!
//! for each of the `2b + 1` nodes `T`, then interpolates.
//!
//! **The three factors are applied in two different places, and that split is
//! why the degree works out.** `sumcheckPolyZero` is
//! `cEqualityPolynomial m₀ τ₀ * cRangeProduct …` (`Constraints.lean:860`), so
//! the equality kernel contributes one degree in the free coordinate and
//! `rangeProduct b v = v·∏_{j=1}^{b-1}(v-j)(v+j)` (`:96`) contributes
//! `2b - 1` — together exactly `roundDegZero b = 2b` (`:87`), which is what
//! [`params::ROUND_NODES`] is `2b + 1` for.
//!
//! [`round_value_zero`] and its callers compute **only the sum**: the suffix
//! table arrives as an argument and the free coordinate's own `eq(τ₀ᵢ, T)`
//! factor is *not* applied there, so what they return has degree `2b - 1`, not
//! `2b`. The prefix constant and the free linear factor are applied by
//! [`honest_compute_g`], which is therefore the item that mirrors
//! `computableRoundPoly (sumcheckPolyZero …)` as a whole. Reading any of the
//! three lower functions as the round polynomial itself is a mistake this
//! module made once (NOTES.md § "The dropped `eq̃` factor"). The fold that produces
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

/// The `i`-th Lagrange node, as an element of the extension field: the integer
/// `i` embedded through `φF` (spec: the nodes of `interpolateArray`,
/// `CompPoly/Univariate/LagrangeArray.lean:48`, at `0 … 2b`).
///
/// Mirrors `CPolynomial.pointNode`.
pub fn round_node(i: usize) -> Ext4 {
    Ext4::from_base(Fp::new(i as u64))
}

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

/// One node's worth of the range summand: `Σ_y eq_suffix(y) · P_b(W(T, y))`,
/// where `W(T, y) = (1 - T)·W[2y] + T·W[2y+1]` (spec: `computableRoundPoly` at
/// one node, through `computableRoundPoly_eval` (`RoundPoly.lean:316`) and
/// `eval_sumcheckPolyZero` (`ZeroCheck/Constraints.lean:1382`)).
///
/// Mirrors `computableRoundPoly` at the `sumcheckPolyZero` summand, one node,
/// **without** that summand's `cEqualityPolynomial` factor on the free
/// coordinate: this is the inner sum only, of degree `2b - 1` in `node`.
/// [`honest_compute_g`] applies the missing `eq(τ₀ᵢ, T)` and the prefix
/// constant; see the module header.
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

/// The whole range summand of a round message: its value at every node
/// (spec: `computableRoundPoly` at the `sumcheckPolyZero` summand).
///
/// Mirrors `computableRoundPoly` at the `sumcheckPolyZero` summand, less its
/// `cEqualityPolynomial` factor ([`round_value_zero`]).
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
        // [`round_value_zero`]'s body, with the node kept in the **base field**
        // (Stage 6 candidate T2c). This function knows something
        // [`round_value_zero`] cannot: its node is `Fp::new(t)`, so both fold
        // scalars are base-field elements and each product is the mixed
        // `Mul<Ext4> for Fp` impl -- four base multiplications where the quartic
        // multiply does nineteen. `round_value_zero` stays as it is because it
        // is the faithful mirror at an *arbitrary* extension node; the
        // duplication is the same one [`round_value_zero_base`] already carries
        // against it, and for the same reason.
        let node: Fp = Fp::new(t as u64);
        let one_minus: Fp = Fp::ONE - node;
        let half: usize = eq.len();
        let mut acc: Ext4 = Ext4::ZERO;
        let mut y: usize = 0;
        while y < half {
            let lo: Ext4 = w[2 * y];
            let hi: Ext4 = w[2 * y + 1];
            let folded: Ext4 = one_minus * lo + node * hi;
            acc = acc + eq[y] * crate::zerocheck::range_product(folded);
            y += 1;
        }
        out.push(acc);
        t += 1;
    }
    out
}

/// `1, x, x², …, x^{2b−1}`: the powers a Taylor shift contracts against
/// (Stage 6 candidate T3).
///
/// [`params::SHIFT_DEG`] entries, so the last is `x^{2b−1}` — the degree of
/// `P_b`. A doubling-free straight walk: each entry is the previous one times
/// `x`, which is `2b − 1` multiplications and not `2b` because the first is
/// `1`.
pub fn shift_powers(x: Ext4) -> Vec<Ext4> {
    let n: usize = params::SHIFT_DEG;
    let mut out: Vec<Ext4> = Vec::with_capacity(n);
    let mut cur: Ext4 = Ext4::ONE;
    let mut k: usize = 0;
    while k < n {
        out.push(cur);
        cur = cur * x;
        k += 1;
    }
    out
}

/// `S_m = Σ_{k ≥ m} p_k · C(k, m) · lo^{k−m}`, the inner sum of the Taylor
/// shift at coefficient `m` (Stage 6 candidate T3).
///
/// Only odd `k` contribute, because `P_b` is odd, so the loop walks the rows of
/// [`params::SHIFT_T`] rather than the degrees. It starts at `j = m / 2`, and
/// `k = 2·(m / 2) + 1 ≥ m` for every `m` — even `m` gives `k = m + 1`, odd `m`
/// gives `k = m` — so `k − m` never underflows and no entry with `m > k` is
/// ever read.
///
/// Every product here is `Fp × Ext4`, the mixed impl: four base
/// multiplications each, against nineteen for a quartic one. That is what makes
/// the ~`b²/2` terms of this sum cheaper than the `2b + 1` range-factor
/// evaluations they replace.
///
/// # Delayed reduction (Stage 6 candidate T36)
///
/// The sum is componentwise -- `Fp × Ext4` scales each coefficient and `+` adds
/// them pairwise -- so the four components never interact and each is a plain
/// integer dot product of at most [`params::SHIFT_ROWS`] terms. The `Fp`
/// arithmetic reduced mod `q` twice per component per term, once for the
/// multiply and once for the add: 8 reductions per term, ~64 per call. Here
/// each component accumulates in a `u128` and is reduced once, at the end: 4
/// per call.
///
/// **The bound, which is why this is exact and not merely usually right.**
/// Every entry of [`params::SHIFT_T`] is already below `q` (they are built
/// reduced, and `Fp::new` was a no-op on them), and every component of a
/// reduced `Ext4` is below `q`, so a term is at most `(q−1)²` and the sum of
/// at most `SHIFT_ROWS = 16` of them is at most `16·(q−1)² < 2^68`. A `u128`
/// holds it with 60 bits to spare, so no intermediate wraps and the single
/// `% q` at the end is the same residue the running reduction produced.
pub fn shift_inner(lop: &Vec<Ext4>, m: usize) -> Ext4 {
    let rows: usize = params::SHIFT_ROWS;
    let deg: usize = params::SHIFT_DEG;
    let qw: u128 = params::Q as u128;
    let mut a0: u128 = 0;
    let mut a1: u128 = 0;
    let mut a2: u128 = 0;
    let mut a3: u128 = 0;
    let mut j: usize = m / 2;
    while j < rows {
        let k: usize = 2 * j + 1;
        let c: u128 = params::SHIFT_T[j * deg + m] as u128;
        let x: Ext4 = lop[k - m];
        a0 = a0 + c * (x.c0.to_u64() as u128);
        a1 = a1 + c * (x.c1.to_u64() as u128);
        a2 = a2 + c * (x.c2.to_u64() as u128);
        a3 = a3 + c * (x.c3.to_u64() as u128);
        j += 1;
    }
    Ext4::new(
        Fp::new((a0 % qw) as u64),
        Fp::new((a1 % qw) as u64),
        Fp::new((a2 % qw) as u64),
        Fp::new((a3 % qw) as u64),
    )
}

/// One pair's contribution to the shifted coefficients: `acc[m] += e · Δ^m · S_m`
/// (Stage 6 candidate T3).
///
/// `Δ^m` is carried as a running scalar rather than a second power table,
/// because the `m` loop visits the powers in order; only `lo`'s powers are read
/// out of order (at `k − m`) and so have to be stored.
///
/// The accumulator is taken by value and written through `IndexMut`, the shape
/// `Rq::mul`'s accumulator already uses.
pub fn shift_accum(mut acc: Vec<Ext4>, lop: &Vec<Ext4>, d: Ext4, e: Ext4) -> Vec<Ext4> {
    let n: usize = params::SHIFT_DEG;
    // `e·d^m`, threaded, rather than `d^m` multiplied by `e` at every step:
    // `e · (d^m · s) = (e · d^m) · s`, so the weight rides along with the
    // power and the body drops from three full `Ext4` products to two. This
    // is the innermost loop of `round_poly_zero`, which the phase split
    // (2026-09-20) measured at 92% of `honest_compute_g` and so ~22% of the
    // whole prover; the other 8% is the alpha side, where the same reasoning
    // bought nothing.
    let mut epow: Ext4 = e;
    let mut m: usize = 0;
    while m < n {
        let s: Ext4 = shift_inner(lop, m);
        let cur: Ext4 = acc[m];
        acc[m] = cur + epow * s;
        epow = epow * d;
        m += 1;
    }
    acc
}

/// The range summand as a polynomial (spec:
/// `computableRoundPoly Φ … (sumcheckPolyZero …) i cs`).
///
/// Mirrors `computableRoundPoly` at the `sumcheckPolyZero` summand, less its
/// `cEqualityPolynomial` factor ([`round_value_zero`]).
///
/// **By Taylor shift, not by interpolation** (Stage 6 candidate T3). The fold
/// is affine in the node — `W(T, y) = lo + Δ·T` with `Δ = hi − lo` — so
/// `P_b(W(T, y))` is `P_b` shifted, and the binomial theorem gives its
/// coefficients directly:
///
/// ```text
///   Σ_y eq[y] · P_b(lo_y + Δ_y T) = Σ_m ( Σ_y eq[y] · Δ_y^m · S_m(lo_y) ) T^m
/// ```
///
/// where `S_m` is [`shift_inner`]. The `2b + 1` node evaluations and the
/// Lagrange interpolation that turned them back into coefficients both
/// disappear; what replaces them is `2b − 1` powers of `lo`, `2b − 1` of `Δ`
/// and the `b²/2` mixed products of [`shift_inner`]. Measured on the pin's
/// shapes: **−43.2%** per pair.
///
/// The output still has [`params::ROUND_NODES`] coefficients, with the last one
/// zero — `P_b` has degree `2b − 1`, so the `2b`-th coefficient of the shift is
/// zero and the `(2b+1)`-th does not exist. That length is what
/// `round_poly_zero_spec` states and it does not move.
pub fn round_poly_zero(w: &Vec<Ext4>, eq: &Vec<Ext4>) -> UnivariatePoly {
    let half: usize = eq.len();
    let n: usize = params::SHIFT_DEG;
    let mut acc: Vec<Ext4> = Vec::with_capacity(params::ROUND_NODES);
    let mut i: usize = 0;
    while i < n {
        acc.push(Ext4::ZERO);
        i += 1;
    }
    let mut y: usize = 0;
    while y < half {
        let lo: Ext4 = w[2 * y];
        let hi: Ext4 = w[2 * y + 1];
        let lop: Vec<Ext4> = shift_powers(lo);
        acc = shift_accum(acc, &lop, hi - lo, eq[y]);
        y += 1;
    }
    acc.push(Ext4::ZERO);
    UnivariatePoly::from_coeffs(acc)
}

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

/// The equality kernel over the coordinates the sumcheck has already consumed:
/// `∏_{k < i} eq(τ₀ₖ, aₖ)`, where `i = challenges.len()`
/// (spec: `cEqualityPolynomial m₀ τ₀` restricted to its bound prefix,
/// `ZeroCheck/Constraints.lean:860`).
///
/// Mirrors `cEqualityPolynomial` at its bound prefix.
///
/// This is the `i`-factor closed form of the kernel on a *prefix* of `tau0`,
/// written out here rather than through cpoly: cpoly's `eq_tilde`
/// (`multilinear.rs:248`) is `lagrange_basis(w).eval(x)` -- two `2^i` tables
/// and a dot, not a product of `i` factors -- and reusing it would also need
/// `&tau0[..i]`, a subslice this crate's extracted model contains nowhere.
/// [`final_check`] needs the kernel over *all* of `τ₀` and calls this at
/// `i = m₀` (Stage 6 candidate K; before it, it called cpoly's function and
/// paid the two `2^m₀` tables).
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

/// The linear summand as a polynomial (spec: `computableRoundPoly Φ …
/// (sumcheckPolyAlpha …) i cs`).
///
/// Mirrors `computableRoundPoly` at the `sumcheckPolyAlpha` summand.
///
/// # The coefficients directly (Stage 6 candidate T38)
///
/// The summand is a product of two *affine* folds, so it is a quadratic in `T`
/// whose coefficients are available without ever evaluating it. Per pair,
/// writing `W(T) = w₀ + T·(w₁ − w₀)` and `A(T) = a₀ + T·(a₁ − a₀)`:
///
/// ```text
/// W·A = w₀a₀ + T·[w₁a₁ − w₀a₀ − (w₁−w₀)(a₁−a₀)] + T²·(w₁−w₀)(a₁−a₀)
/// ```
///
/// -- three `Ext4` products, `p₀ = w₀a₀`, `p₁ = w₁a₁`, `p₂ = (w₁−w₀)(a₁−a₀)`,
/// and the middle coefficient is `p₁ − p₀ − p₂`. The old form evaluated at
/// three nodes, which is three folds of two products each plus a product, and
/// then ran [`interpolate`] over the results.
///
/// **This is not candidate A1**, which was rejected as noise on 2026-09-20.
/// A1 re-ordered the three-node evaluation; this removes it.
pub fn round_poly_alpha(w: &Vec<Ext4>, a_tab: &Vec<Ext4>) -> UnivariatePoly {
    let half: usize = w.len() / 2;
    let mut c0: Ext4 = Ext4::ZERO;
    let mut c1: Ext4 = Ext4::ZERO;
    let mut c2: Ext4 = Ext4::ZERO;
    let mut y: usize = 0;
    while y < half {
        let p0: Ext4 = w[2 * y] * a_tab[2 * y];
        let p1: Ext4 = w[2 * y + 1] * a_tab[2 * y + 1];
        let p2: Ext4 = (w[2 * y + 1] - w[2 * y]) * (a_tab[2 * y + 1] - a_tab[2 * y]);
        c0 = c0 + p0;
        c1 = c1 + (p1 - p0 - p2);
        c2 = c2 + p2;
        y += 1;
    }
    let mut coeffs: Vec<Ext4> = Vec::with_capacity(3);
    coeffs.push(c0);
    coeffs.push(c1);
    coeffs.push(c2);
    UnivariatePoly::from_coeffs(coeffs)
}

// ---------------------------------------------------------------------------
// Round 0 in the base field (candidate I, `lean/Opt.lean` § "Candidate I")
// ---------------------------------------------------------------------------
//
// At round 0 every entry of the `w̃` table is `φF` of a witness coefficient
// (`Constraints.lean:146,148`), every interpolation node is an embedded integer
// ([`round_node`]) and the range factor's constants are embedded integers too.
// So the zero side of the first round message is base-field arithmetic
// performed through the quartic multiply -- 19 `Fp` multiplications where one
// would do, 18 of them multiplying zeros -- and only the equality table `eq̃`
// (a function of the challenge `τ₀`) is a genuine extension element. The items
// below are the round-0 path with that arithmetic done in `Fp`: the fold and
// the range factor in the base field, one `Fp × Ext4` scaling per cube point
// (`impl Mul<Ext4> for Fp`, four `Fp` multiplications), and the one mixed layer
// fold that turns the base-field table into round 1's extension table. From
// round 1 on the challenge is a genuine `Ext4` and the items above apply
// unchanged.
//
// Each item is hachi's own variant of the item it shadows and mirrors nothing
// new: `HachiEquiv.Opt.rangeSumZeroBase_eq`, `roundValuesZeroBase_eq`,
// `evalMleLayerBase_eq` and `linSumAlphaBase_eq` say that each one computes,
// under `φF`, exactly what the extension-field item computes on the embedded
// table at the embedded node. Operand orders are the lemmas': the `Fp` factor
// on the **left** of every mixed product, which is what selects
// `Mul<Ext4> for Fp`.

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
///
/// Card T46a: on a table inside the digit alphabet `[-8, 15]` -- the honest
/// lifted witness's: balanced digits of `ŵ`, `ẑ` and `ρ` in `[-8, 7]`, the
/// unsigned digits of `t̂` in `[0, 15]` (card T46a', 2026-09-23) -- the sum regroups
/// by pair type, `Σ_y eq[y]·P(w[2y], w[2y+1]) = Σ_t b[t]·P(type t)` with
/// `b[t]` the summed `eq` weight of the pairs of type `t`, so the Taylor shift
/// runs once per type (576, padded to 1024) instead of once per pair (`2^25`
/// at the pin). The
/// per-type work is [`round_poly_zero_base_plain`] itself, on the
/// [`pair_type_table_base`] with [`bucket_pairs_base`]'s weights. Any entry
/// outside the alphabet, or a table below [`BUCKET_MIN_PAIRS0`] pairs, takes the
/// per-pair path: the function is total and its value does not depend on
/// which branch ran (rule 4).
pub fn round_poly_zero_base(w: &Vec<Fp>, eq: &Vec<Ext4>) -> UnivariatePoly {
    if eq.len() >= BUCKET_MIN_PAIRS0 {
        match bucket_pairs_base(w, eq) {
            Some(b) => round_poly_zero_base_plain(&pair_type_table_base(), &b),
            None => round_poly_zero_base_plain(w, eq),
        }
    } else {
        round_poly_zero_base_plain(w, eq)
    }
}

/// The honest round-0 alphabet's size: `[-8, 15]`, `HALF_BASE + GADGET_BASE =
/// 24` digit values -- the balanced box `S_b = [-8, 7]` and the unsigned
/// digits `[0, 15]` of the inner commitment's `t̂` (cards T46a, T46a').
pub const DIGIT_ALPHABET: usize = 24;

/// The pair-type index space of a round-0 fold: `DIGIT_ALPHABET² = 576` types
/// `24·i + j`, padded to the power of two `1024` (card T46a'). The bucketed
/// call hands the per-pair body a type table of `2 · PAIR_TYPES` entries and
/// `PAIR_TYPES` weights, and that body is specified on `2^(k+1)` and `2^k`;
/// the 448 padding types carry weight zero, so their representatives are
/// immaterial and the sum is unchanged.
pub const PAIR_TYPES: usize = 1024;

/// `q − HALF_BASE = 4 294 967 189`: the canonical word of the digit `−8`, the
/// lowest word of the box's negative half (card T46a). A literal for the
/// usual extraction reason; `tests/sumcheck_semantics.rs` ties it to `Q`.
pub const Q_MINUS_HALF: u64 = 4_294_967_189;

/// Below this many pairs the bucketed path's fixed cost -- 1024 Taylor shifts
/// and the type table -- is not repaid by the scan, and the per-pair path
/// runs (card T46a; about four times break-even).
pub const BUCKET_MIN_PAIRS0: usize = 2048;

/// The digit id of a round-0 table entry: `d + 8` for the canonical word of a
/// digit `d ∈ [-8, 15]`, and the sentinel [`DIGIT_ALPHABET`] for any other
/// word (cards T46a, T46a').
pub fn digit_id(x: Fp) -> usize {
    let v: u64 = x.to_u64();
    if v < params::GADGET_BASE {
        let id: u64 = v + params::HALF_BASE;
        id as usize
    } else if v >= Q_MINUS_HALF {
        let id: u64 = v - Q_MINUS_HALF;
        id as usize
    } else {
        DIGIT_ALPHABET
    }
}

/// The `eq` weight of every round-0 pair type: `b[24·i + j] = Σ eq[y]` over
/// the pairs `(w[2y], w[2y+1])` whose digit ids are `(i, j)` (card T46a).
/// `None` at the first entry outside the alphabet.
pub fn bucket_pairs_base(w: &Vec<Fp>, eq: &Vec<Ext4>) -> Option<Vec<Ext4>> {
    let half: usize = eq.len();
    let mut b: Vec<Ext4> = Vec::with_capacity(PAIR_TYPES);
    let mut t0: usize = 0;
    while t0 < PAIR_TYPES {
        b.push(Ext4::ZERO);
        t0 += 1;
    }
    let mut y: usize = 0;
    while y < half {
        let i: usize = digit_id(w[2 * y]);
        let j: usize = digit_id(w[2 * y + 1]);
        if i < DIGIT_ALPHABET {
            if j < DIGIT_ALPHABET {
                let t: usize = DIGIT_ALPHABET * i + j;
                let cur: Ext4 = b[t];
                b[t] = cur + eq[y];
            } else {
                return None;
            }
        } else {
            return None;
        }
        y += 1;
    }
    Some(b)
}

/// The representative table of the round-0 pair types: entry `2t` is the
/// digit of id `t / 24`, entry `2t + 1` that of id `t % 24`, each as
/// `Fp::new(id) − 8` (card T46a). Past `576` the ids exceed the alphabet and
/// the entries are padding (weight zero, see [`PAIR_TYPES`]).
pub fn pair_type_table_base() -> Vec<Fp> {
    let mut out: Vec<Fp> = Vec::with_capacity(2 * PAIR_TYPES);
    let eight: Fp = Fp::new(params::HALF_BASE);
    let mut t: usize = 0;
    while t < PAIR_TYPES {
        let hi_id: usize = t / DIGIT_ALPHABET;
        let lo_id: usize = t % DIGIT_ALPHABET;
        out.push(Fp::new(hi_id as u64) - eight);
        out.push(Fp::new(lo_id as u64) - eight);
        t += 1;
    }
    out
}

/// The range summand as a polynomial at **round 1**, from the round-0 base
/// table and the round-0 challenge: [`round_poly_zero`] on round 1's table
/// `eval_mle_layer_base(w_fp, a0)` (card T46b; spec: `rangeSumZero` at the
/// folded table, as [`round_poly_zero`]'s).
///
/// First translation: the composition, literally. Round 1's table is round
/// 0's folded at `a0`, so a round-1 pair is a function of four round-0
/// entries; card T46b buckets on that.
pub fn round_poly_zero_fold1(w_fp: &Vec<Fp>, a0: Ext4, eq: &Vec<Ext4>) -> UnivariatePoly {
    let w1: Vec<Ext4> = eval_mle_layer_base(w_fp, a0);
    round_poly_zero(&w1, eq)
}

/// [`round_poly_zero_base`] pair by pair: the function's body before card
/// T46a, unchanged, and the path it takes off the box.
pub fn round_poly_zero_base_plain(w: &Vec<Fp>, eq: &Vec<Ext4>) -> UnivariatePoly {
    // [`round_poly_zero`]'s Taylor shift, with `w̃` still in the base field
    // (Stage 6 candidate T3, round 0). Round 0 walks `2^m₀ / 2` pairs --
    // **half of every pair the protocol evaluates** -- and it is the cheap
    // half, because `lo`, `Δ` and every power of them stay in `Fp` and only
    // the final `eq[y] · c_m` crosses into `Ext4`. Measured: **−48.7%** per
    // pair, 45.0 s → 23.1 s at the pin.
    let half: usize = eq.len();
    let n: usize = params::SHIFT_DEG;
    let mut acc: Vec<Ext4> = Vec::with_capacity(params::ROUND_NODES);
    let mut i: usize = 0;
    while i < n {
        acc.push(Ext4::ZERO);
        i += 1;
    }
    let mut y: usize = 0;
    while y < half {
        let lo: Fp = w[2 * y];
        let hi: Fp = w[2 * y + 1];
        let lop: Vec<Fp> = shift_powers_base(lo);
        acc = shift_accum_base(acc, &lop, hi - lo, eq[y]);
        y += 1;
    }
    acc.push(Ext4::ZERO);
    UnivariatePoly::from_coeffs(acc)
}

/// [`shift_powers`] in the base field: `1, x, …, x^{2b−1}` as `Fp`.
pub fn shift_powers_base(x: Fp) -> Vec<Fp> {
    let n: usize = params::SHIFT_DEG;
    let mut out: Vec<Fp> = Vec::with_capacity(n);
    let mut cur: Fp = Fp::ONE;
    let mut k: usize = 0;
    while k < n {
        out.push(cur);
        cur = cur * x;
        k += 1;
    }
    out
}

/// [`shift_inner`] in the base field: every product is `Fp × Fp`.
pub fn shift_inner_base(lop: &Vec<Fp>, m: usize) -> Fp {
    let rows: usize = params::SHIFT_ROWS;
    let deg: usize = params::SHIFT_DEG;
    let mut s: Fp = Fp::ZERO;
    let mut j: usize = m / 2;
    while j < rows {
        let k: usize = 2 * j + 1;
        s = s + Fp::new(params::SHIFT_T[j * deg + m]) * lop[k - m];
        j += 1;
    }
    s
}

/// [`shift_accum`] with a base-field `lo` and `Δ`: only the final `eq[y] · c_m`
/// is a mixed product, and there is exactly one of those per coefficient.
pub fn shift_accum_base(mut acc: Vec<Ext4>, lop: &Vec<Fp>, d: Fp, e: Ext4) -> Vec<Ext4> {
    let n: usize = params::SHIFT_DEG;
    let mut dpow: Fp = Fp::ONE;
    let mut m: usize = 0;
    while m < n {
        let s: Fp = shift_inner_base(lop, m);
        let cur: Ext4 = acc[m];
        let nv: Ext4 = cur + (dpow * s) * e;
        acc[m] = nv;
        dpow = dpow * d;
        m += 1;
    }
    acc
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

/// The public table `Ã` in Boolean-evaluation form: `alphaPublicEvals` at every
/// cube index (spec: `cMultilinearExtension m₀ (alphaPublicEvals …)`,
/// `ZeroCheck/Constraints.lean:871`; opt: `HachiEquiv.Opt.alpha_public_table.opt`,
/// `lean/Opt.lean`).
///
/// Mirrors `alphaPublicEvals` as a hypercube table.
///
/// `2^m₀` entries: at the pinned `m₀ = 26` this table is `6.7·10⁷` extension
/// elements, which is why the linear side's rows are REDUCED. The body hoists
/// out of the traversal everything an entry shares with its neighbours: the
/// `d`-entry power table `α^ℓ` (`zerocheck::alpha_pow_table`), the `n`
/// equality weights (`zerocheck::eq_weight_table`) and the `n × (μ + n·δ)`
/// matrix `M̃_α(i, u)` (`zerocheck::m_alpha_table`), each built once. Entry
/// `idx` is then `pw[idx % d] · Σ_i eqw[i] · mt[i][idx / d]`, `n`
/// multiplications where the frozen entrywise form paid `n` polynomial
/// evaluations and a power loop per entry; `alpha_public_table.opt_eq_spec`
/// says the entries are the specification's, so the `Mirrors` line above is
/// still the truth. The guard `u < cols` is the translation of the Lean
/// `getD … 0` off the end of a stored row: `mAlphaTilde` is zero there, so where
/// the Lean `apRowSum` adds `eqw[i] · 0` this loop adds nothing and `sum` stays
/// `Ext4::ZERO` -- the same value, one regrouping. `cols` here must be the width
/// `zerocheck::m_alpha_table` actually built, or the index would be out of
/// range and not merely wrong. The tensor split that avoids building the table
/// at all is strategy S6 of the target-5 brief and is still `perf-loop`'s.
pub fn alpha_public_table(
    s: &crate::ringswitch::RlinStatement,
    alpha: Ext4,
    tau1: &Vec<Ext4>,
    m0: usize,
) -> Vec<Ext4> {
    let degree: usize = params::RING_DEGREE;
    let rows: usize = s.m().rows();
    let cols: usize = s.m().cols() + rows * params::GADGET_DIGITS;
    let sz: usize = cube_size(m0);
    let pw: Vec<Ext4> = crate::zerocheck::alpha_pow_table(alpha, degree);
    let eqw: Vec<Ext4> = crate::zerocheck::eq_weight_table(tau1, rows);
    let mt: Vec<Vec<Ext4>> = crate::zerocheck::m_alpha_table(s, alpha);
    let mut out: Vec<Ext4> = Vec::with_capacity(sz);
    let mut idx: usize = 0;
    while idx < sz {
        let u: usize = idx / degree;
        let l: usize = idx % degree;
        let mut sum: Ext4 = Ext4::ZERO;
        let mut i: usize = 0;
        while i < rows {
            if u < cols {
                sum = sum + eqw[i] * mt[i][u];
            }
            i += 1;
        }
        out.push(pw[l] * sum);
        idx += 1;
    }
    out
}

/// The multilinear extension of the public table `Ã` at a point, **without the
/// table** (opt: `HachiEquiv.Opt.alpha_public_mle_eval.opt`, `lean/Opt.lean`
/// § "Candidate J"; lemma `alpha_public_mle_eval.opt_eq_spec` against
/// `(cMultilinearExtension m₀ (alphaPublicEvals …)).eval`).
///
/// `alphaPublicEvals` at the flat index `idx` is `α^{idx % d} · Σᵢ eq̃(τ₁, i)·
/// M̃_α(i, idx / d)` (`Constraints.lean:840`), and the flat index is
/// little-endian in the cube coordinates, so with `d = 2^10` the table is a
/// tensor product of a function of the low `10` coordinates and a function of
/// the high `m₀ − 10`. The multilinear extension of a tensor product is the
/// product of the two extensions: `mle[Ã](a) = mle[α^ℓ](a_low) · mle[S](a_high)`
/// with `S(u) = Σᵢ eq̃(τ₁, i)·M̃_α(i, u)`. So this evaluates a `2^k`-entry table
/// and a `2^{m₀−k}`-entry one, `k = min(m₀, 10)`, each by cpoly's layer fold,
/// and multiplies -- `2^10 + 2^16` entries at the pin against the `2^26` of
/// [`alpha_public_table`] (brief 5's S4, the verifier half; wall W1's other
/// half is the prover's table). `k` is `min(m₀, log₂ d)` computed by doubling,
/// for the reason [`cube_size`] doubles: below `d` the whole cube is "low" and
/// every entry has `u = 0`.
///
/// `a` is the full sumcheck point, `m₀ = a.len()`; coordinate `j` is folded by
/// `eval_mle_layer` at layer `j`, the orientation `lagrange_basis` fixes
/// (`multilinear.rs:163`). The three tables are candidate C's
/// ([`crate::zerocheck::alpha_pow_table`], [`crate::zerocheck::eq_weight_table`],
/// [`crate::zerocheck::m_alpha_table`]) and the `u < cols` guard is
/// [`alpha_public_table`]'s: `M̃_α` is zero on the unstored columns. No
/// `Mirrors` line: this is the crate's own variant of the specification's
/// evaluation.
pub fn alpha_public_mle_eval(
    s: &crate::ringswitch::RlinStatement,
    alpha: Ext4,
    tau1: &Vec<Ext4>,
    a: &Vec<Ext4>,
) -> Ext4 {
    let degree: usize = params::RING_DEGREE;
    let m0: usize = a.len();
    let rows: usize = s.m().rows();
    let cols: usize = s.m().cols() + rows * params::GADGET_DIGITS;
    let mut k: usize = 0;
    let mut sz: usize = 1;
    while k < m0 && sz < degree {
        sz *= 2;
        k += 1;
    }
    let mut low: Vec<Ext4> = crate::zerocheck::alpha_pow_table(alpha, sz);
    let mut j: usize = 0;
    while j < k {
        low = cpoly::multilinear::eval_mle_layer(&low, a[j]);
        j += 1;
    }
    let hsz: usize = cube_size(m0 - k);
    let eqw: Vec<Ext4> = crate::zerocheck::eq_weight_table(tau1, rows);
    let mt: Vec<Vec<Ext4>> = crate::zerocheck::m_alpha_table(s, alpha);
    let mut high: Vec<Ext4> = Vec::with_capacity(hsz);
    let mut u: usize = 0;
    while u < hsz {
        let mut sum: Ext4 = Ext4::ZERO;
        let mut i: usize = 0;
        while i < rows {
            if u < cols {
                sum = sum + eqw[i] * mt[i][u];
            }
            i += 1;
        }
        high.push(sum);
        u += 1;
    }
    let mut j2: usize = k;
    while j2 < m0 {
        high = cpoly::multilinear::eval_mle_layer(&high, a[j2]);
        j2 += 1;
    }
    low[0] * high[0]
}

// ---------------------------------------------------------------------------
// The α table as two factors (candidate L, brief 5's S4, prover half; wall W1)
// ---------------------------------------------------------------------------
//
// The public table `Ã` at round 0 is the tensor product `L(idx % 2^k) ·
// H(idx / 2^k)` of a `2^k`-entry table of powers of `α` and a `2^{m₀−k}`-entry
// table of row-contracted matrix values, `k = min(m₀, 10)` (the split
// `alpha_public_mle_eval` evaluates). Folding the least-significant coordinate
// commutes with that structure: while `L` has more than one entry the fold
// acts on `L`, and once `L` is a single entry it acts on `H`. So the prover can
// carry `(low, high)` through every round and read `Ã[j]` as
// `low[j % low.len()] · high[j / low.len()]` -- one multiplication per read --
// instead of holding the `2^{m₀−i}`-entry table: `2^10 + 2^16` entries, about
// 2 MiB at the pin, where the flat table is 2 GiB. The items below are the
// α-side round pieces on the two factors; the zero side is untouched.

/// The low factor of `Ã`: the `2^k` powers of `α`, `k = min(m₀, log₂ d)` by
/// doubling, as [`alpha_public_mle_eval`] builds it (opt:
/// `HachiEquiv.Opt.alphaLowTable`, `lean/Sumcheck.lean`).
pub fn alpha_split_low(alpha: Ext4, m0: usize) -> Vec<Ext4> {
    let degree: usize = params::RING_DEGREE;
    let mut k: usize = 0;
    let mut sz: usize = 1;
    while k < m0 && sz < degree {
        sz *= 2;
        k += 1;
    }
    crate::zerocheck::alpha_pow_table(alpha, sz)
}

/// The high factor of `Ã`: entry `u < 2^{m₀−k}` is `Σᵢ eq̃(τ₁, i)·M̃_α(i, u)`,
/// zero on the unstored columns, as [`alpha_public_mle_eval`] builds it (opt:
/// `HachiEquiv.Opt.alphaHighTable`, `lean/Sumcheck.lean`).
pub fn alpha_split_high(
    s: &crate::ringswitch::RlinStatement,
    alpha: Ext4,
    tau1: &Vec<Ext4>,
    m0: usize,
) -> Vec<Ext4> {
    let degree: usize = params::RING_DEGREE;
    let rows: usize = s.m().rows();
    let cols: usize = s.m().cols() + rows * params::GADGET_DIGITS;
    let mut k: usize = 0;
    let mut sz: usize = 1;
    while k < m0 && sz < degree {
        sz *= 2;
        k += 1;
    }
    let hsz: usize = cube_size(m0 - k);
    let eqw: Vec<Ext4> = crate::zerocheck::eq_weight_table(tau1, rows);
    let mt: Vec<Vec<Ext4>> = crate::zerocheck::m_alpha_table(s, alpha);
    let mut high: Vec<Ext4> = Vec::with_capacity(hsz);
    let mut u: usize = 0;
    while u < hsz {
        let mut sum: Ext4 = Ext4::ZERO;
        let mut i: usize = 0;
        while i < rows {
            if u < cols {
                sum = sum + eqw[i] * mt[i][u];
            }
            i += 1;
        }
        high.push(sum);
        u += 1;
    }
    high
}

/// One round's fold of the two factors: the fold acts on `low` while it has
/// more than one entry and on `high` afterwards (opt:
/// `HachiEquiv.Opt.fold_tensorTable_low` / `fold_tensorTable_scalar`,
/// `lean/Opt.lean` § "Candidate L"). Takes the two tables by value and returns
/// the pair, so that the untouched factor moves rather than being copied.
pub fn alpha_split_fold(low: Vec<Ext4>, high: Vec<Ext4>, a: Ext4) -> (Vec<Ext4>, Vec<Ext4>) {
    if 1 < low.len() {
        let low1: Vec<Ext4> = cpoly::multilinear::eval_mle_layer(&low, a);
        (low1, high)
    } else {
        let high1: Vec<Ext4> = cpoly::multilinear::eval_mle_layer(&high, a);
        (low, high1)
    }
}

/// [`round_value_alpha`] with `Ã` read through its two factors: entry `j` is
/// `low[j % low.len()] · high[j / low.len()]` (opt:
/// `HachiEquiv.Opt.linSumAlpha_tensor`, `lean/Opt.lean` § "Candidate L").
pub fn round_value_alpha_split(
    w: &Vec<Ext4>,
    low: &Vec<Ext4>,
    high: &Vec<Ext4>,
    node: Ext4,
) -> Ext4 {
    let half: usize = w.len() / 2;
    let l: usize = low.len();
    let one_minus: Ext4 = Ext4::ONE - node;
    let mut acc: Ext4 = Ext4::ZERO;
    let mut y: usize = 0;
    while y < half {
        let w_folded: Ext4 = one_minus * w[2 * y] + node * w[2 * y + 1];
        let lo_a: Ext4 = low[(2 * y) % l] * high[(2 * y) / l];
        let hi_a: Ext4 = low[(2 * y + 1) % l] * high[(2 * y + 1) / l];
        let a_folded: Ext4 = one_minus * lo_a + node * hi_a;
        acc = acc + w_folded * a_folded;
        y += 1;
    }
    acc
}

/// [`round_values_alpha`] on the two factors.
pub fn round_values_alpha_split(w: &Vec<Ext4>, low: &Vec<Ext4>, high: &Vec<Ext4>) -> Vec<Ext4> {
    let nodes: usize = params::ROUND_NODES_ALPHA;
    let mut out: Vec<Ext4> = Vec::new();
    let mut t: usize = 0;
    while t < nodes {
        out.push(round_value_alpha_split(w, low, high, round_node(t)));
        t += 1;
    }
    out
}

/// [`round_poly_alpha`] on the two factors, direct coefficients and all
/// (Stage 6 candidate T38).
///
/// This is the one the pin runs: `honest_compute_g_split` calls it for every
/// round from 1 on. `Ã`'s entry `j` is `low[j % l] · high[j / l]`, so the two
/// tensor reads replace the two table reads and the quadratic identity above
/// is unchanged.
pub fn round_poly_alpha_split(w: &Vec<Ext4>, low: &Vec<Ext4>, high: &Vec<Ext4>) -> UnivariatePoly {
    let half: usize = w.len() / 2;
    let l: usize = low.len();
    let mut c0: Ext4 = Ext4::ZERO;
    let mut c1: Ext4 = Ext4::ZERO;
    let mut c2: Ext4 = Ext4::ZERO;
    let mut y: usize = 0;
    while y < half {
        let a0: Ext4 = low[(2 * y) % l] * high[(2 * y) / l];
        let a1: Ext4 = low[(2 * y + 1) % l] * high[(2 * y + 1) / l];
        let p0: Ext4 = w[2 * y] * a0;
        let p1: Ext4 = w[2 * y + 1] * a1;
        let p2: Ext4 = (w[2 * y + 1] - w[2 * y]) * (a1 - a0);
        c0 = c0 + p0;
        c1 = c1 + (p1 - p0 - p2);
        c2 = c2 + p2;
        y += 1;
    }
    let mut coeffs: Vec<Ext4> = Vec::with_capacity(3);
    coeffs.push(c0);
    coeffs.push(c1);
    coeffs.push(c2);
    UnivariatePoly::from_coeffs(coeffs)
}

/// [`round_value_alpha_base`] (round 0, base-field witness table) with `Ã`
/// read through its two factors.
pub fn round_value_alpha_base_split(
    w: &Vec<Fp>,
    low: &Vec<Ext4>,
    high: &Vec<Ext4>,
    node: Fp,
) -> Ext4 {
    let half: usize = w.len() / 2;
    let l: usize = low.len();
    let one_minus: Fp = Fp::ONE - node;
    let node_ext: Ext4 = Ext4::from_base(node);
    let one_minus_ext: Ext4 = Ext4::ONE - node_ext;
    let mut acc: Ext4 = Ext4::ZERO;
    let mut y: usize = 0;
    while y < half {
        let w_folded: Fp = one_minus * w[2 * y] + node * w[2 * y + 1];
        let lo_a: Ext4 = low[(2 * y) % l] * high[(2 * y) / l];
        let hi_a: Ext4 = low[(2 * y + 1) % l] * high[(2 * y + 1) / l];
        let a_folded: Ext4 = one_minus_ext * lo_a + node_ext * hi_a;
        acc = acc + w_folded * a_folded;
        y += 1;
    }
    acc
}

/// [`round_values_alpha_base`] on the two factors.
pub fn round_values_alpha_base_split(w: &Vec<Fp>, low: &Vec<Ext4>, high: &Vec<Ext4>) -> Vec<Ext4> {
    let nodes: usize = params::ROUND_NODES_ALPHA;
    let mut out: Vec<Ext4> = Vec::new();
    let mut t: usize = 0;
    while t < nodes {
        out.push(round_value_alpha_base_split(w, low, high, Fp::new(t as u64)));
        t += 1;
    }
    out
}

/// [`round_poly_alpha_base`] on the two factors.
pub fn round_poly_alpha_base_split(w: &Vec<Fp>, low: &Vec<Ext4>, high: &Vec<Ext4>) -> UnivariatePoly {
    let values: Vec<Ext4> = round_values_alpha_base_split(w, low, high);
    let weights: Vec<Fp> = round_node_weights_alpha();
    interpolate(&values, &weights)
}

/// The product of two univariate polynomials over `Ext4` (spec:
/// `CPolynomial.Raw.mul`, `CompPoly/Univariate/Raw/Ops.lean`).
///
/// Mirrors `CPolynomial.Raw.mul` -- schoolbook, trimmed once at the end.
///
/// This is cpoly's `impl Mul<&UnivariatePoly> for &UnivariatePoly`, written
/// here instead of called there, and the reason is the **proof surface** rather
/// than speed: the counts are identical. hachi reaches that `Mul` from exactly
/// four places, all of them `&inner * &free` in the `honest_compute_g` family,
/// where `free` is [`eq_free_factor`]'s two coefficients -- so the generic
/// schoolbook is already overkill, and any upstream change to it (upstream has
/// since put Karatsuba and `u128` leaves behind that operator) would force a
/// re-port of a proof for a product this crate never asks for. Writing it here
/// takes cpoly's generic multiplication out of the reachable extracted model,
/// which is what lets the `cpoly` pin move without breaking a proof about code
/// this repository does not own.
///
/// The body is cpoly's, verbatim to the extent hachi can be: the accumulator is
/// `vec![Ext4::ZERO; np + nq - 1]` (the *repeat* form, which the extraction
/// models with no loop of its own, so the two loops keep the loop indices the
/// ported specs are written against), the empty cases return early, and the
/// read-modify-write is spelled out rather than `+=` for the reason cpoly gives.
/// The one unavoidable difference: `UnivariatePoly`'s field is private, so the
/// result is built with [`UnivariatePoly::from_coeffs`] where cpoly names the
/// constructor -- the identity wrapper either way.
///
/// **Not** written `k`-outer like `Rq::mul`'s candidate Q. At the aspect ratio
/// this is actually called at (`np = 33`, `nq = 2`) a `k`-outer form with a full
/// inner pass would cost `34 · 33 = 1122` iterations against this scatter's `66`.
///
/// `np + nq` is a checked `usize` addition, so the spec carries
/// `np + nq ≤ usize::MAX` exactly as cpoly's did.
pub fn poly_mul(a: &UnivariatePoly, b: &UnivariatePoly) -> UnivariatePoly {
    let np: usize = a.len();
    let nq: usize = b.len();
    if np == 0 || nq == 0 {
        return UnivariatePoly::zero();
    }
    let mut out: Vec<Ext4> = alloc::vec![Ext4::ZERO; np + nq - 1];
    let mut i: usize = 0;
    while i < np {
        let mut j: usize = 0;
        while j < nq {
            let prod: Ext4 = a[i] * b[j];
            let k: usize = i + j;
            out[k] = out[k] + prod;
            j += 1;
        }
        i += 1;
    }
    UnivariatePoly::from_coeffs(out).trim()
}

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

    /// The `R^lin` statement, carrying the public `M`, `yvec` and bound.
    pub fn rlin(&self) -> &crate::ringswitch::RlinStatement {
        &self.rlin
    }

    /// The commitment to `w̃` from the lift stage.
    pub fn t(&self) -> &crate::linalg::PolyVec {
        &self.t
    }

    /// The ring-switching evaluation challenge `α`.
    pub fn alpha(&self) -> Ext4 {
        self.alpha
    }

    /// The direct range-polynomial evaluation point `τ₀`.
    pub fn tau0(&self) -> &Vec<Ext4> {
        &self.tau0
    }

    /// The direct linear-polynomial evaluation point `τ_α`.
    pub fn tau1(&self) -> &Vec<Ext4> {
        &self.tau1
    }
}

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
    /// Pair the two round polynomials.
    pub fn new(g_zero: UnivariatePoly, g_alpha: UnivariatePoly) -> RoundMsg {
        RoundMsg { g_zero, g_alpha }
    }

    /// The range summand's round polynomial `g_i^{(0)}`.
    pub fn g_zero(&self) -> &UnivariatePoly {
        &self.g_zero
    }

    /// The linear summand's round polynomial `g_i^{(α)}`.
    pub fn g_alpha(&self) -> &UnivariatePoly {
        &self.g_alpha
    }
}

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

    /// The zero-check statement carrying the direct evaluation points.
    pub fn zc(&self) -> &NestedZeroCheckStmt {
        &self.zc
    }

    /// The paired-sumcheck challenges drawn so far.
    pub fn challenges(&self) -> &Vec<Ext4> {
        &self.challenges
    }

    /// The current target of the range sumcheck.
    pub fn target_zero(&self) -> Ext4 {
        self.target_zero
    }

    /// The current target of the linear sumcheck.
    pub fn target_alpha(&self) -> Ext4 {
        self.target_alpha
    }
}

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
    let with_free: UnivariatePoly = poly_mul(&inner, &free);
    let g_zero: UnivariatePoly = &with_free * prefix;
    let g_alpha: UnivariatePoly = round_poly_alpha(w_tab, a_tab);
    RoundMsg { g_zero, g_alpha }
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
    let with_free: UnivariatePoly = poly_mul(&inner, &free);
    let g_zero: UnivariatePoly = &with_free * prefix;
    let g_alpha: UnivariatePoly = round_poly_alpha_base(w_fp, a_tab);
    RoundMsg { g_zero, g_alpha }
}

/// [`honest_compute_g`] with `Ã` carried as its two factors: the zero side is
/// the one above, the linear side is [`round_poly_alpha_split`].
pub fn honest_compute_g_split(
    stmt: &RoundStatement,
    w_tab: &Vec<Ext4>,
    low: &Vec<Ext4>,
    high: &Vec<Ext4>,
    i: usize,
) -> RoundMsg {
    let tau0: &Vec<Ext4> = stmt.zc().tau0();
    let prefix: Ext4 = eq_prefix(tau0, stmt.challenges());
    let suffix: Vec<Ext4> = eq_suffix_table(tau0, i);
    let inner: UnivariatePoly = round_poly_zero(w_tab, &suffix);
    let free: UnivariatePoly = eq_free_factor(tau0[i]);
    let with_free: UnivariatePoly = poly_mul(&inner, &free);
    let g_zero: UnivariatePoly = &with_free * prefix;
    let g_alpha: UnivariatePoly = round_poly_alpha_split(w_tab, low, high);
    RoundMsg { g_zero, g_alpha }
}

/// [`honest_compute_g_base`] with `Ã` carried as its two factors.
pub fn honest_compute_g_base_split(
    stmt: &RoundStatement,
    w_fp: &Vec<Fp>,
    low: &Vec<Ext4>,
    high: &Vec<Ext4>,
) -> RoundMsg {
    let tau0: &Vec<Ext4> = stmt.zc().tau0();
    let prefix: Ext4 = eq_prefix(tau0, stmt.challenges());
    let suffix: Vec<Ext4> = eq_suffix_table(tau0, 0);
    let inner: UnivariatePoly = round_poly_zero_base(w_fp, &suffix);
    let free: UnivariatePoly = eq_free_factor(tau0[0]);
    let with_free: UnivariatePoly = poly_mul(&inner, &free);
    let g_zero: UnivariatePoly = &with_free * prefix;
    let g_alpha: UnivariatePoly = round_poly_alpha_base_split(w_fp, low, high);
    RoundMsg { g_zero, g_alpha }
}

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

/// The final check, after the sumcheck has consumed every cube coordinate
/// (spec: `finalCheck`, `Sumcheck/FinalEval.lean:99`).
///
/// Mirrors `finalCheck`.
///
/// Three conjuncts in the specification's order: the range claim
/// `eq̃(τ₀, a)·P_b(y′) = target₀`, the linear claim `y′·Ã(a) = target_α`, and
/// the bound-sanity fact `bound ≤ rlin.bound`. The first factor is
/// [`eq_prefix`] over the whole of `τ₀`: at `i = m₀` the prefix *is* the whole
/// vector, and the prefix form is the closed form.
///
/// This is the first check in the chain that can actually reject: every earlier
/// link's verifier is a pass-through.
///
/// The linear claim's `Ã(a)` is computed by [`alpha_public_mle_eval`] -- the
/// tensor-split evaluation, two small tables and two folds -- and not by
/// building the `2^m₀` table and taking its Lagrange dot (opt:
/// `HachiEquiv.Opt.alpha_public_mle_eval.opt_eq_spec`, `lean/Opt.lean`
/// § "Candidate J"). The range claim's `eq̃(τ₀, a)` is [`eq_prefix`] over the
/// whole of `τ₀` -- the `m₀`-factor closed form -- and not cpoly's
/// `eq_tilde`, which is `lagrange_basis(τ₀).eval(a)`: two `2^m₀` bases and a
/// dot (candidate K; `eq_prefix_spec` at `i = m₀` concludes the `eqProd` the
/// old `eq_tilde` spec did, and `eq_tilde` itself has left this crate's model
/// with its callers). At the pin the two together are the difference
/// between 99 s and milliseconds, and between four 2 GiB tables and 2 MiB.
pub fn final_check(stmt: &RoundStatement, y_prime: Ext4, bound: u64) -> bool {
    let zc: &NestedZeroCheckStmt = stmt.zc();
    let eq_all: Ext4 = eq_prefix(zc.tau0(), stmt.challenges());
    let a_mle: Ext4 = alpha_public_mle_eval(zc.rlin(), zc.alpha(), zc.tau1(), stmt.challenges());
    eq_all * crate::zerocheck::range_product(y_prime) == stmt.target_zero()
        && y_prime * a_mle == stmt.target_alpha()
        && bound <= zc.rlin().bound()
}

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

// ---------------------------------------------------------------------------
// The sumcheck bridge (chain row 7)
// ---------------------------------------------------------------------------

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
///
/// Round 0 is peeled (opt: `lean/Opt.lean` § "Candidate I"): the `w̃` table is
/// built in the base field by [`crate::zerocheck::c_w_table_fp`], the first
/// message comes from [`honest_compute_g_base`], and the first fold
/// [`eval_mle_layer_base`] produces the extension table the loop from round 1
/// on consumes exactly as before. The `0 < m₀` guard is the peel's totality:
/// at `m₀ = 0` there is no round and the result is the empty list either way.
///
/// The public table `Ã` is never built: it is carried as its two tensor
/// factors `(low, high)` ([`alpha_split_low`], [`alpha_split_high`]), folded
/// by [`alpha_split_fold`] and read by the `_split` round pieces (opt:
/// `lean/Opt.lean` § "Candidate L"; wall W1: `2^10 + 2^16` entries in place
/// of `2^{m₀}`).
pub fn honest_round_messages(
    stmt: RoundStatement,
    w: &crate::ringswitch::LiftedWitness,
    challenges: &Vec<Ext4>,
) -> Vec<RoundMsg> {
    let m0: usize = stmt.zc().tau0().len();
    let mut low: Vec<Ext4> = alpha_split_low(stmt.zc().alpha(), m0);
    let mut high: Vec<Ext4> = alpha_split_high(
        stmt.zc().rlin(),
        stmt.zc().alpha(),
        stmt.zc().tau1(),
        m0,
    );
    let mut current: RoundStatement = stmt;
    let mut out: Vec<RoundMsg> = Vec::new();
    if 0 < m0 {
        let w_fp: Vec<Fp> = crate::zerocheck::c_w_table_fp(w, m0);
        let g0: RoundMsg = honest_compute_g_base_split(&current, &w_fp, &low, &high);
        let a0: Ext4 = challenges[0];
        current = round_out(current, &g0, a0);
        let mut w_tab: Vec<Ext4> = eval_mle_layer_base(&w_fp, a0);
        let folded0: (Vec<Ext4>, Vec<Ext4>) = alpha_split_fold(low, high, a0);
        low = folded0.0;
        high = folded0.1;
        out.push(g0);
        let mut i: usize = 1;
        while i < m0 {
            let g: RoundMsg = honest_compute_g_split(&current, &w_tab, &low, &high, i);
            let a: Ext4 = challenges[i];
            current = round_out(current, &g, a);
            w_tab = cpoly::multilinear::eval_mle_layer(&w_tab, a);
            let folded: (Vec<Ext4>, Vec<Ext4>) = alpha_split_fold(low, high, a);
            low = folded.0;
            high = folded.1;
            out.push(g);
            i += 1;
        }
    }
    out
}

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
