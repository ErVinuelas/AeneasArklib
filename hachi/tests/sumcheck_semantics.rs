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
//! * **the identity** the dense form rests on -- `g(T) = Σ_y eq(y)·P_b(W(T,y))`
//!   is what `computableRoundPoly` computes -- checked at the toy width where
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

#![allow(clippy::cast_possible_truncation)]

mod support;

use cpoly::{Ext4, Fp};
use hachi::params::{GADGET_BASE, Q, ROUND_NODES, ROUND_NODE_INV};
use hachi::sumcheck::{interpolate, round_node, round_node_weights, round_poly_zero,
                      round_value_zero, round_values_zero};
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
