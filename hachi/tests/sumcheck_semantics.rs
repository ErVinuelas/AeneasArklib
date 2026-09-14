//! `src/sumcheck.rs`: the round message in folded-table value form.
//!
//! # What this file has to carry that others do not
//!
//! `benches/genesis` holds the **dense** form for this module, by decision
//! (NOTES.md § "Decision: target 5's genesis holds the dense form"). The
//! independent oracle a naive freeze would have provided therefore has to live
//! here instead, and these tests are that oracle rather than a supplement to it.
//!
//! Two levels, because one test cannot do both jobs:
//!
//! * **the identity** the dense form rests on -- `g(T) = eq̃(τ₀|<i,a)·eq(τ₀ᵢ,T)·Σ_y
//!   eq̃(τ₀|>i,y)·P_b(W(T,y))` is what `computableRoundPoly` computes -- checked
//!   at the toy width where
//!   the naive `CMvPolynomial` shape actually runs. Both sides are written here;
//!   the crate is not involved, because the crate's `range_product` is
//!   hard-wired to `GADGET_BASE = 16` and the naive shape needs `b = 3` to fit
//!   in memory at all (`33^5 = 3.9·10^7` monomials against `7^5 = 16 807`).
//! * **the implementation**, at the real `b = 16`: the crate's folded-table code
//!   against an independent dense computation written in a different order.
//!
//! The gap between them is stated rather than papered over: no test here runs
//! the crate's own code against the specification's naive shape, because no
//! width exists where both are possible. That is the cost of the decision, and
//! it is the reason the decision is recorded in three places.
//!
//! **A correction, 2026-09-08.** This header, the module header of
//! `src/sumcheck.rs` and the `Mirrors` lines of the three `round_*_zero`
//! functions all used to state that identity *without* its two `eq̃` factors,
//! and `round_value_is_the_eq_weighted_range_sum` below checks the crate
//! against that same incomplete formula -- so it could not have caught the
//! omission. The oracle that does is
//! `honest_compute_g_range_component_is_the_specifications_partial_sum`, which
//! builds its reference from `sumcheckPolyZero` itself. NOTES.md
//! § "The dropped eq~ factor" records how the gap arose and why no benchmark
//! or digest could have found it.

#![allow(clippy::cast_possible_truncation)]

mod support;

use cpoly::{Ext4, Fp};
use hachi::params::{GADGET_BASE, Q, ROUND_NODES, ROUND_NODE_INV};
use hachi::linalg::PolyVec;
use hachi::params::{ROUND_NODES_ALPHA, ROUND_NODE_INV_ALPHA};
use hachi::ringswitch::RlinStatement;
use hachi::ringswitch::{LiftedWitness, QuotientRow};
use hachi::sumcheck::{alpha_public_table, eq_free_factor, eq_prefix, eq_suffix_table,
                      honest_round_messages, nested_to_round_statement, round_loop,
                      round_verify_loop,
                      final_check, honest_compute_g, interpolate, round_check, round_node,
                      round_node_weights, round_out, round_poly_zero, round_value_zero,
                      round_values_zero, NestedZeroCheckStmt, RoundStatement};
use support::Lcg;

fn ext4(r: &mut Lcg) -> Ext4 {
    Ext4::new(r.next_fp(), r.next_fp(), r.next_fp(), r.next_fp())
}

/// `P_b` at an arbitrary base, as the specification writes it: `v·∏_{j=1}^{b-1}
/// (v-j)(v+j)`. Parameterised in `b`, which the crate's `range_product` is not
/// -- that is what makes the toy-width identity test below possible.
fn range_product_ref(b: u64, v: Ext4) -> Ext4 {
    let mut acc = v;
    let mut j = 1u64;
    while j < b {
        let jf = Ext4::from_base(Fp::new(j));
        acc = acc * (v - jf) * (v + jf);
        j += 1;
    }
    acc
}

// --- the constants are auditable, not magic --------------------------------

/// `ROUND_NODES = 2b + 1`: one more than the per-round degree bound
/// `roundDegZero b = 2b`, which is what makes the interpolant unique.
#[test]
fn round_node_count_is_two_b_plus_one() {
    assert_eq!(ROUND_NODES as u64, 2 * GADGET_BASE + 1);
}

/// Every interpolation weight is the inverse of its own denominator:
/// `w_i · ∏_{j≠i}(i - j) = 1` in `F_q`. This is what makes the precomputed
/// table checkable, and it is the reason those literals are allowed to exist
/// at all -- cpoly exposes no inversion, so they cannot be recomputed.
#[test]
fn interpolation_weights_invert_their_denominators() {
    let q = u128::from(Q);
    for i in 0..ROUND_NODES {
        let mut denom: u128 = 1;
        for j in 0..ROUND_NODES {
            if i != j {
                let diff = (u128::from(Q) + i as u128 - j as u128) % q;
                denom = denom * diff % q;
            }
        }
        let w = u128::from(ROUND_NODE_INV[i]);
        assert_eq!(denom * w % q, 1, "weight {i} is not the inverse of its denominator");
    }
}

// --- interpolation ---------------------------------------------------------

/// `eval_interpolateArray_at_index` (`CompPoly/Univariate/LagrangeArray.lean:79`):
/// the interpolant returns the given value at each given node. The property the
/// whole round-message representation rests on.
#[test]
fn interpolant_reproduces_its_values_at_every_node() {
    let mut r = Lcg::new(0x5A17_6001);
    let values: Vec<Ext4> = (0..ROUND_NODES).map(|_| ext4(&mut r)).collect();
    let p = interpolate(&values, &round_node_weights());
    for (i, v) in values.iter().enumerate() {
        assert_eq!(p.eval(round_node(i)), *v, "node {i}");
    }
}

/// And it is *the* interpolant, not merely one curve through the points: a
/// polynomial of degree < 33 is determined by 33 values, so interpolating the
/// values of a known polynomial must return that polynomial's own evaluations
/// everywhere -- including away from the nodes, which the previous test cannot
/// see.
#[test]
fn interpolant_agrees_off_the_nodes_with_the_polynomial_it_came_from() {
    let mut r = Lcg::new(0x5A17_6002);
    let coeffs: Vec<Ext4> = (0..ROUND_NODES).map(|_| ext4(&mut r)).collect();
    let horner = |x: Ext4| {
        let mut acc = Ext4::ZERO;
        let mut k = coeffs.len();
        while k > 0 {
            k -= 1;
            acc = acc * x + coeffs[k];
        }
        acc
    };
    let values: Vec<Ext4> = (0..ROUND_NODES).map(|i| horner(round_node(i))).collect();
    let p = interpolate(&values, &round_node_weights());
    for probe in [100u64, 12345, 4_294_967_000] {
        let x = Ext4::from_base(Fp::new(probe));
        assert_eq!(p.eval(x), horner(x), "off-node probe {probe}");
    }
}

// --- the implementation, at the real b -------------------------------------

/// The crate's folded-table value against an independent computation of the
/// same sum, accumulated in the opposite order and with the fold written out
/// separately. Pins `(1-T)·W[2y] + T·W[2y+1]` -- the pairing that eliminates
/// the low bit, which is the orientation `evalMleStep` fixes upstream.
#[test]
fn round_value_is_the_eq_weighted_range_sum() {
    let mut r = Lcg::new(0x5A17_6003);
    let half = 8usize;
    let w: Vec<Ext4> = (0..2 * half).map(|_| ext4(&mut r)).collect();
    let eq: Vec<Ext4> = (0..half).map(|_| ext4(&mut r)).collect();
    for t in [0usize, 1, 7, ROUND_NODES - 1] {
        let node = round_node(t);
        let mut expected = Ext4::ZERO;
        for y in (0..half).rev() {
            let folded = (Ext4::ONE - node) * w[2 * y] + node * w[2 * y + 1];
            expected = expected + eq[y] * range_product_ref(GADGET_BASE, folded);
        }
        assert_eq!(round_value_zero(&w, &eq, node), expected, "node {t}");
    }
}

/// `round_poly_zero` is `round_values_zero` interpolated: the polynomial's value
/// at each node is the node value the folded table produced. This is the join
/// between the two halves of the module.
#[test]
fn round_poly_evaluates_to_its_node_values() {
    let mut r = Lcg::new(0x5A17_6004);
    let half = 4usize;
    let w: Vec<Ext4> = (0..2 * half).map(|_| ext4(&mut r)).collect();
    let eq: Vec<Ext4> = (0..half).map(|_| ext4(&mut r)).collect();
    let values = round_values_zero(&w, &eq);
    let p = round_poly_zero(&w, &eq);
    for (i, v) in values.iter().enumerate() {
        assert_eq!(p.eval(round_node(i)), *v, "node {i}");
    }
}

/// A round message has degree at most `2b`, which is why `2b + 1` values
/// determine it (`computableRoundPoly_mem_degreeLE`, `RoundPoly.lean:326`). If
/// the interpolant came out with a higher degree, the representation would be
/// unsound however well it matched at the nodes.
#[test]
fn round_poly_has_degree_at_most_two_b() {
    let mut r = Lcg::new(0x5A17_6005);
    let half = 4usize;
    let w: Vec<Ext4> = (0..2 * half).map(|_| ext4(&mut r)).collect();
    let eq: Vec<Ext4> = (0..half).map(|_| ext4(&mut r)).collect();
    let p = round_poly_zero(&w, &eq).trim();
    match p.degree() {
        None => (),
        Some(d) => assert!(
            d as u64 <= 2 * GADGET_BASE,
            "degree {d} exceeds roundDegZero = {}",
            2 * GADGET_BASE
        ),
    }
}

// --- the round message as a whole, against the specification's own sum -----

/// `eq(t, x)`, written `1 - t - x + 2tx`. The crate writes the same function as
/// `t·x + (1-t)·(1-x)`; expanding it here is what makes this an independent
/// reference rather than a copy.
fn eq_ref(t: Ext4, x: Ext4) -> Ext4 {
    Ext4::ONE - t - x + (t * x + t * x)
}

/// `eq̃(tau, point)` as the product of per-coordinate factors.
fn eq_tilde_ref(tau: &[Ext4], point: &[Ext4]) -> Ext4 {
    let mut acc = Ext4::ONE;
    for k in 0..tau.len() {
        acc = acc * eq_ref(tau[k], point[k]);
    }
    acc
}

/// A multilinear extension evaluated as the Lagrange dot against the whole
/// table: `Σ_z table[z]·∏_k (bit k of z ? point[k] : 1 - point[k])`. The crate
/// reaches the same value by folding one coordinate at a time
/// (`eval_mle_layer`), so the two computations share no structure.
fn mle_ref(table: &[Ext4], point: &[Ext4]) -> Ext4 {
    let mut acc = Ext4::ZERO;
    for z in 0..table.len() {
        let mut term = table[z];
        for k in 0..point.len() {
            term = term
                * if (z >> k) & 1 == 1 {
                    point[k]
                } else {
                    Ext4::ONE - point[k]
                };
        }
        acc = acc + term;
    }
    acc
}

/// The cube point `(a₀ … a_{i-1}, T, y)`, with `y` little-endian in its bits.
fn point_at(challenges: &[Ext4], big_t: Ext4, y: usize, suffix_vars: usize) -> Vec<Ext4> {
    let mut point: Vec<Ext4> = challenges.to_vec();
    point.push(big_t);
    for k in 0..suffix_vars {
        point.push(if (y >> k) & 1 == 1 {
            Ext4::ONE
        } else {
            Ext4::ZERO
        });
    }
    point
}

/// `hypercubeSum` of `sumcheckPolyZero` with the prefix fixed to `(a, T)` --
/// i.e. the round polynomial's value at `T`, by `computableRoundPoly_eval`
/// (`RoundPoly.lean:316`). Built straight from `sumcheckPolyZero`'s definition
/// (`cEqualityPolynomial * cRangeProduct ∘ mle`, `Constraints.lean:860`), with
/// no folded table anywhere.
fn g_zero_ref(
    table: &[Ext4],
    tau0: &[Ext4],
    challenges: &[Ext4],
    i: usize,
    big_t: Ext4,
    b: u64,
) -> Ext4 {
    let suffix_vars = tau0.len() - i - 1;
    let mut acc = Ext4::ZERO;
    for y in 0..(1usize << suffix_vars) {
        let point = point_at(challenges, big_t, y, suffix_vars);
        acc = acc + eq_tilde_ref(tau0, &point) * range_product_ref(b, mle_ref(table, &point));
    }
    acc
}

/// The same for `sumcheckPolyAlpha = mle[w̃] * mle[Ã]` (`Constraints.lean:868`):
/// no equality kernel, two multilinears.
fn g_alpha_ref(
    w_table: &[Ext4],
    a_table: &[Ext4],
    challenges: &[Ext4],
    i: usize,
    m0: usize,
    big_t: Ext4,
) -> Ext4 {
    let suffix_vars = m0 - i - 1;
    let mut acc = Ext4::ZERO;
    for y in 0..(1usize << suffix_vars) {
        let point = point_at(challenges, big_t, y, suffix_vars);
        acc = acc + mle_ref(w_table, &point) * mle_ref(a_table, &point);
    }
    acc
}

/// Fold a table through the challenges already drawn, one coordinate per
/// challenge -- the crate's own prover state.
fn fold_through(table: &[Ext4], challenges: &[Ext4]) -> Vec<Ext4> {
    let mut cur = table.to_vec();
    for a in challenges {
        cur = cpoly::multilinear::eval_mle_layer(&cur, *a);
    }
    cur
}

/// A round statement whose only live fields are `τ₀`, `τ₁`, `α` and the
/// challenges: `honest_compute_g` reads nothing else, and the `R^lin` statement
/// and commitment are along for the ride.
fn round_stmt(
    seed: u64,
    tau0: Vec<Ext4>,
    tau1: Vec<Ext4>,
    alpha: Ext4,
    challenges: Vec<Ext4>,
    target_zero: Ext4,
    target_alpha: Ext4,
) -> RoundStatement {
    let mut r = Lcg::new(seed);
    let rlin = RlinStatement::new(r.next_poly_matrix(2, 2), r.next_poly_vec(2), 15);
    let t: PolyVec = r.next_poly_vec(2);
    let zc = NestedZeroCheckStmt::new(rlin, t, alpha, tau0, tau1);
    RoundStatement::new(zc, challenges, target_zero, target_alpha)
}

/// **The load-bearing test of this module.** `honest_compute_g`'s range
/// component, evaluated anywhere, is the specification's partial hypercube sum
/// of `sumcheckPolyZero` -- equality kernel included.
///
/// This is the test the previous oracle could not be: the reference here is
/// `sumcheckPolyZero`'s definition, so a missing `eq̃` factor fails it. The
/// crate's `range_product` is fixed at `b = GADGET_BASE`, which is why the
/// reference is called at that same `b` while the *width* is toy (`m₀ = 4`).
#[test]
fn honest_compute_g_range_component_is_the_specifications_partial_sum() {
    let mut r = Lcg::new(0x9E37_79B9_7F4A_7C15);
    let m0 = 4usize;
    let i = 1usize;
    let table: Vec<Ext4> = (0..1 << m0).map(|_| ext4(&mut r)).collect();
    let tau0: Vec<Ext4> = (0..m0).map(|_| ext4(&mut r)).collect();
    let tau1: Vec<Ext4> = (0..2).map(|_| ext4(&mut r)).collect();
    let alpha = ext4(&mut r);
    let challenges: Vec<Ext4> = (0..i).map(|_| ext4(&mut r)).collect();

    let w_tab = fold_through(&table, &challenges);
    let a_tab: Vec<Ext4> = (0..w_tab.len()).map(|_| ext4(&mut r)).collect();
    let stmt = round_stmt(
        1,
        tau0.clone(),
        tau1,
        alpha,
        challenges.clone(),
        Ext4::ZERO,
        Ext4::ZERO,
    );
    let g = honest_compute_g(&stmt, &w_tab, &a_tab, i);

    for t in 0..5u64 {
        let big_t = Ext4::from_base(Fp::new(t * 7 + 3));
        assert_eq!(
            g.g_zero().eval(big_t),
            g_zero_ref(&table, &tau0, &challenges, i, big_t, GADGET_BASE),
            "range component disagrees with sumcheckPolyZero's partial sum at T = {t}"
        );
    }
}

/// The linear component, against `sumcheckPolyAlpha`'s partial sum.
#[test]
fn honest_compute_g_linear_component_is_the_specifications_partial_sum() {
    let mut r = Lcg::new(0xD1B5_4A32_D192_ED03);
    let m0 = 4usize;
    let i = 2usize;
    let w_full: Vec<Ext4> = (0..1 << m0).map(|_| ext4(&mut r)).collect();
    let a_full: Vec<Ext4> = (0..1 << m0).map(|_| ext4(&mut r)).collect();
    let tau0: Vec<Ext4> = (0..m0).map(|_| ext4(&mut r)).collect();
    let tau1: Vec<Ext4> = (0..2).map(|_| ext4(&mut r)).collect();
    let alpha = ext4(&mut r);
    let challenges: Vec<Ext4> = (0..i).map(|_| ext4(&mut r)).collect();

    let w_tab = fold_through(&w_full, &challenges);
    let a_tab = fold_through(&a_full, &challenges);
    let stmt = round_stmt(
        2,
        tau0,
        tau1,
        alpha,
        challenges.clone(),
        Ext4::ZERO,
        Ext4::ZERO,
    );
    let g = honest_compute_g(&stmt, &w_tab, &a_tab, i);

    for t in 0..4u64 {
        let big_t = Ext4::from_base(Fp::new(t * 11 + 5));
        assert_eq!(
            g.g_alpha().eval(big_t),
            g_alpha_ref(&w_full, &a_full, &challenges, i, m0, big_t),
            "linear component disagrees with sumcheckPolyAlpha's partial sum at T = {t}"
        );
    }
}

/// The degrees are the specification's two bounds, and the range side's is
/// `2b` **exactly** -- which is the arithmetic statement that the equality
/// kernel's free factor is present. Without it the degree is `2b - 1`, and that
/// is precisely the defect the earlier `<= 2b` test admitted.
#[test]
fn round_message_degrees_are_two_b_and_two_exactly() {
    let mut r = Lcg::new(0x2545_F491_4F6C_DD1D);
    let m0 = 3usize;
    let i = 0usize;
    let w_full: Vec<Ext4> = (0..1 << m0).map(|_| ext4(&mut r)).collect();
    let a_full: Vec<Ext4> = (0..1 << m0).map(|_| ext4(&mut r)).collect();
    let tau0: Vec<Ext4> = (0..m0).map(|_| ext4(&mut r)).collect();
    let tau1: Vec<Ext4> = (0..2).map(|_| ext4(&mut r)).collect();
    let alpha = ext4(&mut r);
    let stmt = round_stmt(3, tau0, tau1, alpha, Vec::new(), Ext4::ZERO, Ext4::ZERO);
    let g = honest_compute_g(&stmt, &w_full, &a_full, i);

    assert_eq!(
        g.g_zero().clone().trim().degree(),
        Some((2 * GADGET_BASE) as usize),
        "the range component must have degree exactly roundDegZero = 2b"
    );
    assert_eq!(
        g.g_alpha().clone().trim().degree(),
        Some(2),
        "the linear component must have degree exactly roundDegAlpha = 2"
    );
}

// --- the two checks, in both directions ------------------------------------

/// `round_check` accepts the honest message and rejects a moved target. The
/// rejection half is the load-bearing one: a check that accepted everything
/// would satisfy the accepting direction alone.
#[test]
fn round_check_accepts_the_honest_message_and_rejects_moved_targets() {
    let mut r = Lcg::new(0x8A5C_D789_635D_2DFF);
    let m0 = 3usize;
    let w_full: Vec<Ext4> = (0..1 << m0).map(|_| ext4(&mut r)).collect();
    let a_full: Vec<Ext4> = (0..1 << m0).map(|_| ext4(&mut r)).collect();
    let tau0: Vec<Ext4> = (0..m0).map(|_| ext4(&mut r)).collect();
    let tau1: Vec<Ext4> = (0..2).map(|_| ext4(&mut r)).collect();
    let alpha = ext4(&mut r);

    let probe = round_stmt(
        4,
        tau0.clone(),
        tau1.clone(),
        alpha,
        Vec::new(),
        Ext4::ZERO,
        Ext4::ZERO,
    );
    let g = honest_compute_g(&probe, &w_full, &a_full, 0);
    let t0 = g.g_zero().eval(Ext4::ZERO) + g.g_zero().eval(Ext4::ONE);
    let ta = g.g_alpha().eval(Ext4::ZERO) + g.g_alpha().eval(Ext4::ONE);

    let good = round_stmt(4, tau0.clone(), tau1.clone(), alpha, Vec::new(), t0, ta);
    assert!(round_check(&good, &g), "the honest message must pass");

    let bad_zero = round_stmt(
        4,
        tau0.clone(),
        tau1.clone(),
        alpha,
        Vec::new(),
        t0 + Ext4::ONE,
        ta,
    );
    assert!(!round_check(&bad_zero, &g), "a moved range target must fail");

    let bad_alpha = round_stmt(4, tau0, tau1, alpha, Vec::new(), t0, ta + Ext4::ONE);
    assert!(
        !round_check(&bad_alpha, &g),
        "a moved linear target must fail"
    );
}

/// `round_out` appends the challenge and replaces both targets by the round
/// polynomials' values there -- the erasure of `Fin.snoc` plus two evaluations.
#[test]
fn round_out_extends_the_challenges_and_moves_both_targets() {
    let mut r = Lcg::new(0x1234_5678_9ABC_DEF0);
    let m0 = 3usize;
    let w_full: Vec<Ext4> = (0..1 << m0).map(|_| ext4(&mut r)).collect();
    let a_full: Vec<Ext4> = (0..1 << m0).map(|_| ext4(&mut r)).collect();
    let tau0: Vec<Ext4> = (0..m0).map(|_| ext4(&mut r)).collect();
    let tau1: Vec<Ext4> = (0..2).map(|_| ext4(&mut r)).collect();
    let alpha = ext4(&mut r);
    let a = ext4(&mut r);

    let stmt = round_stmt(
        5,
        tau0.clone(),
        tau1.clone(),
        alpha,
        Vec::new(),
        Ext4::ZERO,
        Ext4::ZERO,
    );
    let g = honest_compute_g(&stmt, &w_full, &a_full, 0);
    let next = round_out(stmt, &g, a);

    assert_eq!(next.challenges().len(), 1);
    assert_eq!(next.challenges()[0], a);
    assert_eq!(next.target_zero(), g.g_zero().eval(a));
    assert_eq!(next.target_alpha(), g.g_alpha().eval(a));
}

/// `final_check` needs all three of its conjuncts: each one is moved in turn
/// and must reject. The two claim values are computed with the independent
/// references above, so the equality halves are not checked against the crate's
/// own arithmetic; only `Ã`'s table is taken from the crate, because
/// `alphaPublicEvals` is target 4's item and has its own oracle.
#[test]
fn final_check_needs_all_three_conjuncts() {
    let mut r = Lcg::new(0xFEED_FACE_CAFE_BEEF);
    let m0 = 3usize;
    let tau0: Vec<Ext4> = (0..m0).map(|_| ext4(&mut r)).collect();
    let tau1: Vec<Ext4> = (0..2).map(|_| ext4(&mut r)).collect();
    let alpha = ext4(&mut r);
    let challenges: Vec<Ext4> = (0..m0).map(|_| ext4(&mut r)).collect();
    let y_prime = ext4(&mut r);

    let mut probe = Lcg::new(6);
    let rlin_probe = RlinStatement::new(probe.next_poly_matrix(2, 2), probe.next_poly_vec(2), 15);
    let table = alpha_public_table(&rlin_probe, alpha, &tau1, m0);
    let t0 = eq_tilde_ref(&tau0, &challenges) * range_product_ref(GADGET_BASE, y_prime);
    let ta = y_prime * mle_ref(&table, &challenges);

    let build = |tz: Ext4, tal: Ext4| {
        round_stmt(
            6,
            tau0.clone(),
            tau1.clone(),
            alpha,
            challenges.clone(),
            tz,
            tal,
        )
    };

    assert!(
        final_check(&build(t0, ta), y_prime, 15),
        "the honest claim must pass at bound = rlin.bound"
    );
    assert!(
        !final_check(&build(t0 + Ext4::ONE, ta), y_prime, 15),
        "a moved range target must fail"
    );
    assert!(
        !final_check(&build(t0, ta + Ext4::ONE), y_prime, 15),
        "a moved linear target must fail"
    );
    assert!(
        !final_check(&build(t0, ta), y_prime, 16),
        "a bound above rlin.bound must fail"
    );
}

// --- the new pieces, individually -------------------------------------------

/// The three linear-side weights invert their denominators, the same audit the
/// range side gets.
#[test]
fn linear_interpolation_weights_invert_their_denominators() {
    for i in 0..ROUND_NODES_ALPHA {
        let mut denom: u128 = 1;
        for j in 0..ROUND_NODES_ALPHA {
            if j != i {
                let d = ((i as i128 - j as i128).rem_euclid(Q as i128)) as u128;
                denom = denom * d % u128::from(Q);
            }
        }
        let prod = denom * u128::from(ROUND_NODE_INV_ALPHA[i]) % u128::from(Q);
        assert_eq!(prod, 1, "weight {i} does not invert its denominator");
    }
}

/// `eq_prefix` is the equality kernel over the drawn challenges, and
/// `eq_suffix_table` is its hypercube table over the coordinates after the free
/// one -- checked against the independent product form, and against each other
/// through the identity that the two of them plus `eq_free_factor` at a Boolean
/// point reconstruct `eq̃(τ₀, ·)` on the whole cube.
#[test]
fn the_three_equality_pieces_reconstruct_the_kernel() {
    let mut r = Lcg::new(0x0BAD_C0DE_0BAD_C0DE);
    let m0 = 4usize;
    let i = 1usize;
    let tau0: Vec<Ext4> = (0..m0).map(|_| ext4(&mut r)).collect();
    let challenges: Vec<Ext4> = (0..i).map(|_| ext4(&mut r)).collect();

    assert_eq!(
        eq_prefix(&tau0, &challenges),
        eq_tilde_ref(&tau0[..i], &challenges),
        "eq_prefix is not the kernel over the drawn challenges"
    );

    let suffix = eq_suffix_table(&tau0, i);
    let suffix_vars = m0 - i - 1;
    assert_eq!(suffix.len(), 1 << suffix_vars);
    for y in 0..suffix.len() {
        let point: Vec<Ext4> = (0..suffix_vars)
            .map(|k| {
                if (y >> k) & 1 == 1 {
                    Ext4::ONE
                } else {
                    Ext4::ZERO
                }
            })
            .collect();
        assert_eq!(
            suffix[y],
            eq_tilde_ref(&tau0[i + 1..], &point),
            "suffix table entry {y} is wrong"
        );
    }

    // eq̃(τ₀, (a, T, y)) = prefix · eq(τ₀ᵢ, T) · suffix[y], at Boolean T.
    let free = eq_free_factor(tau0[i]);
    for big_t in [Ext4::ZERO, Ext4::ONE] {
        for y in 0..suffix.len() {
            let point = point_at(&challenges, big_t, y, suffix_vars);
            assert_eq!(
                eq_prefix(&tau0, &challenges) * free.eval(big_t) * suffix[y],
                eq_tilde_ref(&tau0, &point),
                "the three pieces do not reconstruct the kernel"
            );
        }
    }
}

// --- the sumcheck bridge (chain row 7) ------------------------------------

/// `y(α)` by Horner, where the crate's `c_eval_at` is the specification's
/// *power sum* `Σ aᵢ·αⁱ` with a running power (`eval₂` is not Horner —
/// `CompPoly/Univariate/Basic.lean:251`; the power was recomputed per term in
/// genesis). Different association, same value, which is what makes it a
/// reference.
fn horner_ref(alpha: Ext4, p: &hachi::ring::Rq) -> Ext4 {
    let n = p.len();
    let mut acc = Ext4::ZERO;
    let mut k = n;
    while k > 0 {
        k -= 1;
        acc = acc * alpha + Ext4::from_base(p.coeff(k));
    }
    acc
}

/// **The bridge installs `(∅, 0, zcTargetAlpha)`.** The asymmetry is the row's
/// whole content: the range target is the literal `0` because `H₀` vanishes
/// identically, while the linear target is `n` rows of work. A translation that
/// made them symmetric — both `0`, or both computed — would pass any test that
/// only checked shapes, so this one checks the value.
#[test]
fn the_bridge_installs_zero_and_the_alpha_target() {
    let mut r = Lcg::new(0x5A17_7100);
    let n = 3usize;
    let m0 = 4usize;
    let m1 = 2usize;
    let rlin = RlinStatement::new(r.next_poly_matrix(n, 2), r.next_poly_vec(n), 15);
    let alpha = ext4(&mut r);
    let tau0: Vec<Ext4> = (0..m0).map(|_| ext4(&mut r)).collect();
    let tau1: Vec<Ext4> = (0..m1).map(|_| ext4(&mut r)).collect();

    // the reference: sum over the rows of eq~(tau1, i) * y_i(alpha)
    let mut expected = Ext4::ZERO;
    for i in 0..n {
        let mut w = Ext4::ONE;
        for j in 0..m1 {
            w = w * eq_ref(tau1[j], if (i >> j) & 1 == 1 { Ext4::ONE } else { Ext4::ZERO });
        }
        expected = expected + w * horner_ref(alpha, rlin.yvec().get(i));
    }

    let zc = NestedZeroCheckStmt::new(
        rlin,
        PolyVec::new(vec![]),
        alpha,
        tau0.clone(),
        tau1.clone(),
    );
    let st = nested_to_round_statement(zc);

    assert!(st.challenges().is_empty(), "the challenge prefix starts empty");
    assert!(
        st.target_zero().is_zero(),
        "the range target is the literal 0 -- H_0 vanishes identically"
    );
    assert_eq!(
        st.target_alpha(),
        expected,
        "the linear target is zcTargetAlpha, computed from the statement alone"
    );
    assert!(
        !st.target_alpha().is_zero(),
        "a zero alpha target here would make the asymmetry untestable"
    );
    // and the carried data survives
    assert_eq!(st.zc().tau0().len(), m0);
    assert_eq!(st.zc().tau1().len(), m1);
    assert_eq!(st.zc().alpha(), alpha);
}

// --- the rounds, split into the prover's and the verifier's halves ----------

/// A toy lifted witness whose `z` covers an `m₀`-variable cube: `w_table`
/// reads `z[idx / d]`, so at `m₀ ≤ 10` only `z[0]` is ever touched.
fn toy_witness(seed: u64) -> LiftedWitness {
    let mut r = Lcg::new(seed);
    LiftedWitness::new(r.next_poly_vec(1), (0..1).map(|_| QuotientRow::new(&Vec::new())).collect())
}

/// A round-0 statement whose two targets are the honest initial sums over the
/// witness's own tables, so that every round of an honest run passes
/// `round_check`. The targets are read off `g₁(0) + g₁(1)`, which is what the
/// sumcheck's first round asserts they are; `round_check` has its own test
/// against moved targets above.
fn honest_opening(seed: u64, w: &LiftedWitness, m0: usize) -> RoundStatement {
    let probe = round_stmt(seed, tau_of(seed, m0), tau1_of(seed), alpha_of(seed), Vec::new(),
                           Ext4::ZERO, Ext4::ZERO);
    let w_tab = hachi::zerocheck::c_w_table_mle(w, m0).into_values();
    let a_tab = alpha_public_table(probe.zc().rlin(), probe.zc().alpha(), probe.zc().tau1(), m0);
    let g = honest_compute_g(&probe, &w_tab, &a_tab, 0);
    let t0 = g.g_zero().eval(Ext4::ZERO) + g.g_zero().eval(Ext4::ONE);
    let ta = g.g_alpha().eval(Ext4::ZERO) + g.g_alpha().eval(Ext4::ONE);
    round_stmt(seed, tau_of(seed, m0), tau1_of(seed), alpha_of(seed), Vec::new(), t0, ta)
}

fn tau_of(seed: u64, m0: usize) -> Vec<Ext4> {
    let mut r = Lcg::new(seed ^ 0x7A00);
    (0..m0).map(|_| ext4(&mut r)).collect()
}

fn tau1_of(seed: u64) -> Vec<Ext4> {
    let mut r = Lcg::new(seed ^ 0x7A01);
    (0..2).map(|_| ext4(&mut r)).collect()
}

fn alpha_of(seed: u64) -> Ext4 {
    let mut r = Lcg::new(seed ^ 0xA1FA);
    ext4(&mut r)
}

/// The two halves compose to the fused reduction: the verifier's loop accepts
/// the honest prover's messages and lands on the statement `round_loop` lands
/// on -- same challenge prefix, same two targets. This is the test that lets
/// [`round_verify_loop`] stand in for `round_loop` on the verifier's path.
#[test]
fn round_verify_loop_accepts_the_honest_messages_and_agrees_with_round_loop() {
    let seed = 0x5EED_0001u64;
    let m0 = 3usize;
    let w = toy_witness(seed);
    let mut r = Lcg::new(seed ^ 0xC4);
    let challenges: Vec<Ext4> = (0..m0).map(|_| ext4(&mut r)).collect();

    let msgs = honest_round_messages(honest_opening(seed, &w, m0), &w, &challenges);
    assert_eq!(msgs.len(), m0, "one message pair per round");

    let verified = round_verify_loop(honest_opening(seed, &w, m0), &msgs, &challenges)
        .expect("the verifier must accept the honest messages");
    let fused = round_loop(honest_opening(seed, &w, m0), &w, &challenges)
        .expect("the fused reduction accepts its own honest run");

    assert_eq!(verified.challenges(), fused.challenges());
    assert_eq!(verified.target_zero(), fused.target_zero());
    assert_eq!(verified.target_alpha(), fused.target_alpha());
    assert_eq!(verified.challenges(), &challenges);
}

/// A message from another prover's run, spliced in at round `k`, is rejected
/// at round `k` and not before: the rounds before it still pass, which is what
/// shows the rejection is the message's and not the statement's.
#[test]
fn round_verify_loop_rejects_a_spliced_message_at_its_own_round() {
    let seed = 0x5EED_0002u64;
    let m0 = 4usize;
    let w = toy_witness(seed);
    let other = toy_witness(seed ^ 0xFFFF);
    let mut r = Lcg::new(seed ^ 0xC4);
    let challenges: Vec<Ext4> = (0..m0).map(|_| ext4(&mut r)).collect();

    for k in 0..m0 {
        let mut msgs = honest_round_messages(honest_opening(seed, &w, m0), &w, &challenges);
        let foreign = honest_round_messages(honest_opening(seed, &other, m0), &other, &challenges);
        msgs[k] = foreign.into_iter().nth(k).expect("the foreign run has a message at k");

        assert!(
            round_verify_loop(honest_opening(seed, &w, m0), &msgs, &challenges).is_none(),
            "a foreign message at round {k} must be rejected"
        );

        // the honest prefix still passes: truncate both lists to `k` rounds by
        // running a `k`-variable check -- the first `k` messages of the honest
        // run are the honest run of the same statement on the first `k`
        // challenges only if `k == m0`, so instead check each honest message
        // against the statement it was produced for.
        let mut current = honest_opening(seed, &w, m0);
        let honest = honest_round_messages(honest_opening(seed, &w, m0), &w, &challenges);
        for (i, g) in honest.iter().enumerate().take(k) {
            assert!(round_check(&current, g), "honest round {i} passes before the splice at {k}");
            current = round_out(current, g, challenges[i]);
        }
    }
}
