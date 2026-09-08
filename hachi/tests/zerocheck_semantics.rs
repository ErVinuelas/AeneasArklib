//! `src/zerocheck.rs`: the committed table `w̃` and the range block `H₀`.
//!
//! The headline tests are the specification's two readback lemmas --
//! `wTable_zRow` (`ZeroCheck/Constraints.lean:378`) and `wTable_rRow` (`:394`)
//! -- and `rangeProduct_eq_zero_iff` (`:102`), which is the whole point of the
//! link: `P_b(v) = 0` exactly when `v` is the image of an integer in the
//! symmetric range `{−(b−1), …, b−1}`. `hZero_eq_zero_iff` (`:219`) is pinned
//! in both directions.
//!
//! # Scale
//!
//! REDUCED, and it has to be: `m₀` is `M_ZERO = 26` at the pinned profile, a
//! `2^26`-entry `Ext4` table (2.0 GiB). `m₀` has a *floor* of 14 at
//! `RING_DEGREE = 1024` for a witness with any quotient rows at all
//! (`2^m₀ ≥ (μ + n·δ)·d ≥ 9·1024`), so the table-shaped tests here run at
//! `μ = 1`, `n = 0`, `m₀ = 10 or 11` -- the smallest shapes in which the object
//! still exists -- and the branch-shaped tests probe individual indices, where
//! no table is materialized at all.
//!
//! The references are written in the specification's shape and not the crate's:
//! the balanced digit as `Nat.digits b` on a shifted centered representative
//! (never `rho_digits`), `eq̃(i, a)` as an explicit product over the bits of `i`
//! (never cpoly's `lagrange_basis`), and the range factor as a descending
//! product of `(v² − j²)` (never the crate's ascending `(v−j)(v+j)` pairs).

#![allow(clippy::cast_possible_wrap)]
#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::cast_sign_loss)]

mod support;

use cpoly::{Ext4, Fp, MultilinearEvals};
use hachi::linalg::PolyVec;
use hachi::params::{BALANCED_SHIFT, GADGET_BASE, GADGET_DIGITS, HALF_BASE, Q, RING_DEGREE};
use hachi::ringswitch::{LiftedWitness, QuotientRow};
use hachi::zerocheck::{c_w_table_mle, h_zero, h_zero_is_zero, range_product, w_table,
                       w_table_mle_eval};
use support::{rq_from_u64s, Lcg};

/// `φF` -- the ring map `ZMod q →+* F` the specification carries everywhere.
fn phi(c: Fp) -> Ext4 {
    Ext4::from_base(c)
}

/// The image of a *signed* integer in the extension field, as the
/// specification's `((j : ℕ) : F)` coercion composed with negation.
fn from_i64(v: i64) -> Ext4 {
    if v >= 0 {
        Ext4::from_base(Fp::new(v as u64 % Q))
    } else {
        Ext4::ZERO - Ext4::from_base(Fp::new((-v) as u64 % Q))
    }
}

/// `balancedDigit b digits c e`, written the specification's way: shift the
/// canonical representative by `balancedShift`, take `Nat.digits b` as a list,
/// read index `e` with `getD _ 0`, then subtract `⌊b/2⌋`.
///
/// Deliberately unlike `gadget::balanced_digit_at`, which divides `e` times.
fn balanced_digit(c: Fp, e: usize) -> Fp {
    let shifted = (c.to_u64() + BALANCED_SHIFT) % Q;
    let mut digits = Vec::new();
    let mut n = shifted;
    while n > 0 {
        digits.push(n % GADGET_BASE);
        n /= GADGET_BASE;
    }
    let d = if e < digits.len() { digits[e] } else { 0 };
    // `- (b/2)` in `ZMod q`.
    Fp::new((d + Q - HALF_BASE) % Q)
}

/// The range factor, as a *descending* product of `(v² − j²)` rather than the
/// crate's ascending `(v − j)·(v + j)` pairs.
fn range_product_ref(v: Ext4) -> Ext4 {
    let mut acc = v;
    let mut j = GADGET_BASE - 1;
    while j >= 1 {
        let jf = Ext4::from_base(Fp::new(j));
        acc = acc * (v * v - jf * jf);
        j -= 1;
    }
    acc
}

/// `eq̃(i, a) = ∏_j (if bit j of i then a_j else 1 - a_j)`, written as an
/// explicit bit product over the index -- the shape
/// `CMlPolynomialEval.lagrangeBasis` has in the specification.
fn eq_tilde_ref(i: usize, a: &[Ext4]) -> Ext4 {
    let mut acc = Ext4::ONE;
    for (j, aj) in a.iter().enumerate() {
        let bit = (i >> j) & 1 == 1;
        acc = acc * if bit { *aj } else { Ext4::ONE - *aj };
    }
    acc
}

/// A witness with `mu` message polynomials and `n` quotient rows.
fn witness(seed: u64, mu: usize, n: usize) -> LiftedWitness {
    let mut r = Lcg::new(seed);
    let z = r.next_poly_vec(mu);
    let mut rho = Vec::new();
    for _ in 0..n {
        let row = r.next_rq();
        let mut coeffs = Vec::new();
        for k in 0..RING_DEGREE {
            coeffs.push(row.coeff(k));
        }
        rho.push(QuotientRow::new(&coeffs));
    }
    LiftedWitness::new(z, rho)
}

// --- rangeProduct -----------------------------------------------------------

#[test]
fn range_product_matches_an_independent_product() {
    let mut r = Lcg::new(0x5A17_0001);
    for _ in 0..16 {
        let v = phi(r.next_fp());
        assert_eq!(range_product(v), range_product_ref(v));
    }
}

/// `rangeProduct_eq_zero_iff` (`Constraints.lean:102`), the forward direction:
/// every integer in the symmetric range is a root.
#[test]
fn range_product_vanishes_on_the_whole_symmetric_range() {
    let b = GADGET_BASE as i64;
    for j in -(b - 1)..b {
        let v = from_i64(j);
        assert!(range_product(v).is_zero(), "P_b should vanish at {j}");
    }
}

/// And the converse direction at the two values that matter: the first integer
/// outside the range on each side. `b − 1 = 15 = CHAIN_GAMMA` is the bound the
/// whole link is stated at, so `±b` must *not* be a root.
#[test]
fn range_product_does_not_vanish_just_outside_the_range() {
    let b = GADGET_BASE as i64;
    for j in [b, -b, b + 1, -(b + 1)] {
        assert!(!range_product(from_i64(j)).is_zero(), "P_b should not vanish at {j}");
    }
}

// --- wTable -----------------------------------------------------------------

/// `wTable_zRow` (`Constraints.lean:378`): on the message block, entry
/// `d·u + ℓ` is the `ℓ`-th coefficient of `z_u`.
#[test]
fn w_table_reads_the_message_block_coefficientwise() {
    let mu = 2;
    let w = witness(0x5A17_0002, mu, 2);
    for u in 0..mu {
        for l in [0usize, 1, 17, RING_DEGREE - 1] {
            let idx = RING_DEGREE * u + l;
            assert_eq!(w_table(&w, idx), phi(w.z().get(u).coeff(l)), "z block at ({u}, {l})");
        }
    }
}

/// `wTable_rRow` (`Constraints.lean:394`): on the quotient block, entry
/// `d·(μ + i·δ + u) + ℓ` is the `ℓ`-th coefficient of the `u`-th balanced digit
/// of quotient row `i` -- the two-level split, digit-major inside each row.
#[test]
fn w_table_reads_the_quotient_block_digit_major() {
    let (mu, n) = (2, 2);
    let w = witness(0x5A17_0003, mu, n);
    for i in 0..n {
        for u in [0usize, 3, GADGET_DIGITS - 1] {
            for l in [0usize, 5, RING_DEGREE - 1] {
                let idx = RING_DEGREE * (mu + i * GADGET_DIGITS + u) + l;
                let expected = phi(balanced_digit(w.rho()[i].coeff(l), u));
                assert_eq!(w_table(&w, idx), expected, "rho block at ({i}, {u}, {l})");
            }
        }
    }
}

/// The `else 0` branch: everything above the committed rows is the padding of
/// the cube, and the padding is zero.
#[test]
fn w_table_is_zero_above_the_committed_rows() {
    let (mu, n) = (2, 2);
    let w = witness(0x5A17_0004, mu, n);
    let first_pad = RING_DEGREE * (mu + n * GADGET_DIGITS);
    for idx in [first_pad, first_pad + 1, first_pad + 4096] {
        assert!(w_table(&w, idx).is_zero(), "padding at {idx}");
    }
}

// --- the tables -------------------------------------------------------------

/// `cWTableMle` (`:328`) is `wTable` tabulated over the flat cube index.
#[test]
fn c_w_table_mle_tabulates_w_table() {
    let w = witness(0x5A17_0005, 1, 0);
    let m0 = 11;
    let table = c_w_table_mle(&w, m0);
    assert_eq!(table.len(), 1 << m0);
    for i in 0..(1usize << m0) {
        assert_eq!(table.values()[i], w_table(&w, i), "entry {i}");
    }
}

/// `wTableMleEval` (`:335`) is `∑ᵢ w̃(i)·eq̃(i, a)`, against an `eq̃` written as
/// a bit product rather than through cpoly's Lagrange basis.
#[test]
fn w_table_mle_eval_is_the_lagrange_sum() {
    let w = witness(0x5A17_0006, 1, 0);
    let m0 = 10;
    let mut r = Lcg::new(0x5A17_0007);
    let mut a = Vec::new();
    for _ in 0..m0 {
        a.push(phi(r.next_fp()));
    }
    let mut expected = Ext4::ZERO;
    for i in 0..(1usize << m0) {
        expected = expected + w_table(&w, i) * eq_tilde_ref(i, &a);
    }
    assert_eq!(w_table_mle_eval(&w, m0, &a), expected);
}

// --- hZero ------------------------------------------------------------------

/// `hZero` (`:204`) is the range factor applied entrywise to `w̃`.
#[test]
fn h_zero_is_the_range_factor_of_the_table() {
    let w = witness(0x5A17_0008, 1, 0);
    let m0 = 10;
    let block: MultilinearEvals = h_zero(&w, m0);
    assert_eq!(block.len(), 1 << m0);
    for i in 0..(1usize << m0) {
        assert_eq!(block.values()[i], range_product(w_table(&w, i)), "entry {i}");
    }
}

/// `hZero_eq_zero_iff` (`:219`), both directions. A witness whose every
/// coefficient is already a legal digit makes `H₀ ≡ 0`; moving one single
/// coefficient one step outside the range breaks it, and nothing else does.
#[test]
fn h_zero_is_zero_exactly_when_every_coefficient_is_in_range() {
    let m0 = 10;
    let bound = GADGET_BASE - 1;

    // Every coefficient a legal digit, both signs, including the two endpoints.
    let mut coeffs = Vec::new();
    for k in 0..RING_DEGREE {
        let v = (k as u64) % (2 * bound + 1);
        coeffs.push(if v <= bound { v } else { Q - (v - bound) });
    }
    let good = LiftedWitness::new(PolyVec::new(vec![rq_from_u64s(&coeffs)]), Vec::new());
    assert!(h_zero_is_zero(&good, m0));
    for e in h_zero(&good, m0).values() {
        assert!(e.is_zero());
    }

    // One coefficient at +b, the first value outside the range.
    let mut bad_coeffs = coeffs.clone();
    bad_coeffs[7] = GADGET_BASE;
    let bad = LiftedWitness::new(PolyVec::new(vec![rq_from_u64s(&bad_coeffs)]), Vec::new());
    assert!(!h_zero_is_zero(&bad, m0));

    // And on the negative side, at -b.
    let mut bad_neg = coeffs.clone();
    bad_neg[9] = Q - GADGET_BASE;
    let bad_neg = LiftedWitness::new(PolyVec::new(vec![rq_from_u64s(&bad_neg)]), Vec::new());
    assert!(!h_zero_is_zero(&bad_neg, m0));

    // The endpoints of the scan, which is what a fencepost error in the loop
    // bound hides behind: at `m0 = 10`, `mu = 1`, `n = 0` the table is exactly
    // `z_0`'s `RING_DEGREE = 1024` coefficients, so cube index `2^m0 - 1` is
    // the last coefficient and index `0` the first. A loop that stops one short
    // -- or starts one late -- passes every other assertion in this file.
    for k in [0usize, RING_DEGREE - 1] {
        let mut edge = coeffs.clone();
        edge[k] = GADGET_BASE;
        let edge = LiftedWitness::new(PolyVec::new(vec![rq_from_u64s(&edge)]), Vec::new());
        assert!(!h_zero_is_zero(&edge, m0), "out-of-range coefficient at index {k} not seen");
        assert!(!h_zero(&edge, m0).values()[k].is_zero(), "H0 entry {k} should not vanish");
    }
}
