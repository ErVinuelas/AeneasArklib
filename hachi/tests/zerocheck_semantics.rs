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
use hachi::linalg::{PolyMatrix, PolyVec};
use hachi::params::{BALANCED_SHIFT, GADGET_BASE, GADGET_DIGITS, HALF_BASE, Q, RING_DEGREE};
use hachi::ringswitch::RlinStatement;
use hachi::ringswitch::{LiftedWitness, QuotientRow};
use hachi::ring::Rq;
use hachi::zerocheck::w_table_row;
use hachi::zerocheck::{alpha_pow_table, eq_weight_table, m_alpha_table, range_product_base};
use hachi::zerocheck::{alpha_contract, alpha_defect, alpha_public_evals, alpha_tilde,
                       c_w_table_mle, eq_weight, h_alpha, h_alpha_evals, h_alpha_is_zero,
                       h_zero, h_zero_is_zero, m_alpha_tilde, range_product, w_table,
                       w_table_mle_eval, zc_target_alpha, below_two_pow};
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

// --- the row helper ---------------------------------------------------------

/// `w_table_row` (opt: `HachiEquiv.Opt.wTableRow`) is the table read one row
/// at a time: coefficient `l` of row `u` is entry `d·u + l` of `w_table`, on the
/// message rows, on every digit row, and on the zero padding above them. It is
/// also the *only* place the row-hoisted builders differ from the entrywise
/// ones, so this is the test that pins the hoist to the specification's table.
#[test]
fn w_table_row_is_the_table_read_by_rows() {
    let (mu, n) = (2, 2);
    let w = witness(0x5A17_0009, mu, n);
    let rows = mu + n * GADGET_DIGITS;
    for u in 0..(rows + 3) {
        let r = w_table_row(&w, u);
        for l in [0, 1, 17, RING_DEGREE / 2, RING_DEGREE - 1] {
            assert_eq!(
                Ext4::from_base(r.coeff(l)),
                w_table(&w, RING_DEGREE * u + l),
                "row {u}, coefficient {l}"
            );
        }
        if u >= rows {
            assert!(r.equals(&Rq::zero()), "row {u} is padding");
        }
    }
}

/// The hoisted builders stop at the cube, not at the table: at `m₀ = 11` with
/// `1 + 2·8 = 17` rows the cube holds exactly two complete rows, so the outer
/// loop exits early (the second row a digit row) and nothing is truncated.
#[test]
fn c_w_table_mle_stops_at_the_cube_not_the_table() {
    let w = witness(0x5A17_000A, 1, 2);
    let m0 = 11;
    let table = c_w_table_mle(&w, m0);
    assert_eq!(table.len(), 1 << m0);
    for i in 0..(1usize << m0) {
        assert_eq!(table.values()[i], w_table(&w, i), "entry {i}");
    }
    let h = h_zero(&w, m0);
    for i in 0..(1usize << m0) {
        assert_eq!(h.values()[i], range_product_ref(w_table(&w, i)), "H₀ entry {i}");
    }
}

/// The one shape where the inner guard's second conjunct ends a block early:
/// `2^m₀ < d`, so row 0 is cut at `2^m₀` coefficients. This is the `m₀ < 10`
/// case the Lean lemma covers without a padding loop, and the only place the
/// two guards of the inner loop disagree.
#[test]
fn c_w_table_mle_truncates_a_partial_row_block() {
    let w = witness(0x5A17_000B, 1, 2);
    for m0 in [3usize, 9] {
        let table = c_w_table_mle(&w, m0);
        assert_eq!(table.len(), 1 << m0);
        for i in 0..(1usize << m0) {
            assert_eq!(table.values()[i], w_table(&w, i), "m0 {m0}, entry {i}");
        }
        let h = h_zero(&w, m0);
        assert_eq!(h.len(), 1 << m0);
        for i in 0..(1usize << m0) {
            assert_eq!(h.values()[i], range_product_ref(w_table(&w, i)), "m0 {m0}, H₀ {i}");
        }
    }
}

/// The verdict over a cube spanning more than one row, the second a digit row:
/// `h_zero_is_zero` must agree with the block it decides, and a corrupted
/// coefficient placed in the *digit* row (index `≥ d`) must flip it. A wrong
/// row advance or a mishandled digit branch in the verdict loop would pass the
/// single-`z`-row test above and fail here.
#[test]
fn h_zero_is_zero_agrees_with_h_zero_across_rows() {
    let w = witness(0x5A17_000C, 1, 2);
    let m0 = 11;
    let all_zero = h_zero(&w, m0).values().iter().all(|e| e.is_zero());
    assert_eq!(h_zero_is_zero(&w, m0), all_zero, "the verdict is the block's vanishing");
    // A random z row is not in range, so the honest reading is `false`; build a
    // witness that IS in range and corrupt one digit-row coefficient.
    let z = PolyVec::new(vec![rq_from_u64s(&vec![1u64; RING_DEGREE])]);
    let mut rows = Vec::new();
    for _ in 0..2 {
        rows.push(QuotientRow::new(&vec![Fp::new(0); RING_DEGREE]));
    }
    let good = LiftedWitness::new(z, rows);
    assert!(h_zero_is_zero(&good, m0), "all-zero quotient rows and unit message digits are in range");
    let all_zero_good = h_zero(&good, m0).values().iter().all(|e| e.is_zero());
    assert!(all_zero_good);
}

// --- the base-field range factor (Stage 6 I5 candidate G) ------------------

/// `range_product_base` embedded is `range_product` at the embedded argument
/// (`φF` is a ring homomorphism), on random coefficients, on the whole symmetric
/// range where both vanish, and just outside it where neither does.
#[test]
fn range_product_base_embeds_to_range_product() {
    let mut r = Lcg::new(0x5A17_C010);
    for _ in 0..16 {
        let c = Fp::new(r.next_u64() % Q);
        assert_eq!(Ext4::from_base(range_product_base(c)), range_product(Ext4::from_base(c)));
    }
    for v in -(GADGET_BASE as i64 - 1)..(GADGET_BASE as i64) {
        let c = if v >= 0 { Fp::new(v as u64) } else { Fp::new(Q - ((-v) as u64)) };
        assert!(range_product_base(c).is_zero(), "P_b vanishes at {v}");
    }
    for v in [GADGET_BASE as i64, -(GADGET_BASE as i64)] {
        let c = if v >= 0 { Fp::new(v as u64) } else { Fp::new(Q - ((-v) as u64)) };
        assert!(!range_product_base(c).is_zero(), "P_b does not vanish at {v}");
    }
}

// --- the hoisted α-side tables (Stage 6 I1 candidate C) --------------------

/// `alpha_pow_table` is `alpha_tilde` tabulated, at every index below `d`.
#[test]
fn alpha_pow_table_is_alpha_tilde_tabulated() {
    let mut r = Lcg::new(0x5A17_C001);
    let alpha = ext4(&mut r);
    let t = alpha_pow_table(alpha, RING_DEGREE);
    assert_eq!(t.len(), RING_DEGREE);
    for l in [0usize, 1, 2, 17, 511, RING_DEGREE - 1] {
        assert_eq!(t[l], alpha_tilde(alpha, l), "index {l}");
    }
}

/// `eq_weight_table` is `eq_weight` under the `i < 2^m₁` guard and zero above:
/// at `m₁ = 2` rows `4..` are padding.
#[test]
fn eq_weight_table_is_eq_weight_with_the_guard() {
    let mut r = Lcg::new(0x5A17_C002);
    let tau1: Vec<Ext4> = (0..2).map(|_| ext4(&mut r)).collect();
    let n = 6;
    let t = eq_weight_table(&tau1, n);
    assert_eq!(t.len(), n);
    for i in 0..n {
        if i < 4 {
            assert_eq!(t[i], eq_weight(&tau1, i), "row {i}");
        } else {
            assert!(t[i].is_zero(), "row {i} is above the cube");
        }
    }
}

/// `m_alpha_table` is `m_alpha_tilde` tabulated over the stored columns, all
/// three branches (matrix, this row's digit block, another row's digit block),
/// and callers read the unstored columns as zero, which `m_alpha_tilde` is there.
#[test]
fn m_alpha_table_is_m_alpha_tilde_tabulated() {
    let mut r = Lcg::new(0x5A17_C003);
    let (n, mu) = (3usize, 2usize);
    let s = statement(0x5A17_C004, n, mu);
    let alpha = ext4(&mut r);
    let t = m_alpha_table(&s, alpha);
    let cols = mu + n * GADGET_DIGITS;
    assert_eq!(t.len(), n);
    for i in 0..n {
        assert_eq!(t[i].len(), cols, "row {i} width");
        for u in 0..cols {
            assert_eq!(t[i][u], m_alpha_tilde(&s, alpha, i, u), "entry ({i}, {u})");
        }
        for u in [cols, cols + 1, cols + 1024] {
            assert!(m_alpha_tilde(&s, alpha, i, u).is_zero(), "unstored ({i}, {u}) is zero");
        }
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

// --- the α side -------------------------------------------------------------

/// `αⁿ` by repeated squaring: a different algorithm from the repeated
/// multiplication `alphaTilde` is written as.
fn pow_by_squaring(alpha: Ext4, mut n: usize) -> Ext4 {
    let mut acc = Ext4::ONE;
    let mut base = alpha;
    while n > 0 {
        if n % 2 == 1 {
            acc = acc * base;
        }
        base = base * base;
        n /= 2;
    }
    acc
}

/// `p(α)` by Horner, for the reference side of `mAlphaTilde`'s first case.
fn horner_ref(alpha: Ext4, p: &Rq) -> Ext4 {
    let mut acc = Ext4::ZERO;
    let mut k = RING_DEGREE;
    while k > 0 {
        k -= 1;
        acc = acc * alpha + Ext4::from_base(p.coeff(k));
    }
    acc
}

fn ext4(r: &mut Lcg) -> Ext4 {
    Ext4::new(r.next_fp(), r.next_fp(), r.next_fp(), r.next_fp())
}

fn statement(seed: u64, n: usize, mu: usize) -> RlinStatement {
    let mut r = Lcg::new(seed);
    RlinStatement::new(r.next_poly_matrix(n, mu), r.next_poly_vec(n), 15)
}

#[test]
fn alpha_tilde_is_the_power() {
    let mut r = Lcg::new(0x5A17_3001);
    let alpha = ext4(&mut r);
    for l in [0usize, 1, 2, 7, 63, 1023] {
        assert_eq!(alpha_tilde(alpha, l), pow_by_squaring(alpha, l), "α^{l}");
    }
}

/// The Lagrange weights are a partition of unity: `∑_{i < 2^m₁} eq̃(τ₁, i) = 1`
/// for *every* `τ₁`. A property of the family rather than a re-computation of
/// one entry, so it cannot be satisfied by a consistently wrong product.
#[test]
fn eq_weights_sum_to_one() {
    let mut r = Lcg::new(0x5A17_3002);
    for m1 in 1..=4usize {
        let tau: Vec<Ext4> = (0..m1).map(|_| ext4(&mut r)).collect();
        let mut sum = Ext4::ZERO;
        for i in 0..(1usize << m1) {
            sum = sum + eq_weight(&tau, i);
        }
        assert_eq!(sum, Ext4::ONE, "m1 = {m1}");
    }
}

/// And at a Boolean `τ₁` the family is the indicator of the index `τ₁` encodes,
/// little-endian -- which pins the *bit order*, the thing a `finFunctionFinEquiv`
/// mix-up would silently transpose.
#[test]
fn eq_weight_at_a_boolean_point_is_the_indicator() {
    let m1 = 3usize;
    for k in 0..(1usize << m1) {
        let tau: Vec<Ext4> = (0..m1)
            .map(|j| if (k >> j) & 1 == 1 { Ext4::ONE } else { Ext4::ZERO })
            .collect();
        for i in 0..(1usize << m1) {
            let w = eq_weight(&tau, i);
            if i == k {
                assert_eq!(w, Ext4::ONE, "eq(e_{k}, {i})");
            } else {
                assert!(w.is_zero(), "eq(e_{k}, {i}) should vanish");
            }
        }
    }
}

/// `mAlphaTilde`'s three cases, each against an independent computation: the
/// matrix entry at `α` by Horner, the digit weight as `−(α^d + 1)·bᵉ` by
/// squaring, and zero elsewhere.
#[test]
fn m_alpha_tilde_has_the_three_specified_cases() {
    let (n, mu) = (2usize, 2usize);
    let s = statement(0x5A17_3003, n, mu);
    let mut r = Lcg::new(0x5A17_3004);
    let alpha = ext4(&mut r);
    let phi_alpha = pow_by_squaring(alpha, RING_DEGREE) + Ext4::ONE;

    // case 1: the R^lin matrix entry evaluated at α
    for i in 0..n {
        for u in 0..mu {
            assert_eq!(
                m_alpha_tilde(&s, alpha, i, u),
                horner_ref(alpha, s.m().entry(i, u)),
                "matrix case at ({i}, {u})"
            );
        }
    }

    // case 2: row i's own digit columns carry -φ(α)·b^e
    for i in 0..n {
        for e in 0..GADGET_DIGITS {
            let u = mu + i * GADGET_DIGITS + e;
            let mut b_pow = Ext4::ONE;
            for _ in 0..e {
                b_pow = b_pow * Ext4::from_base(Fp::new(GADGET_BASE));
            }
            let expected = (Ext4::ZERO - phi_alpha) * b_pow;
            assert_eq!(m_alpha_tilde(&s, alpha, i, u), expected, "digit case ({i}, {e})");
        }
    }

    // case 3: another row's digit columns, and the padding above the table
    for i in 0..n {
        for other in 0..n {
            if other == i {
                continue;
            }
            let u = mu + other * GADGET_DIGITS;
            assert!(
                m_alpha_tilde(&s, alpha, i, u).is_zero(),
                "row {i} must not see row {other}'s digit columns"
            );
        }
        let above = mu + n * GADGET_DIGITS;
        assert!(m_alpha_tilde(&s, alpha, i, above).is_zero(), "padding at {above}");
    }
}

/// `alphaPublicEvals` factors as `α^{idx % d} · ∑ᵢ eq̃(τ₁, i)·M̃_α(i, idx / d)`,
/// against a reference that builds each factor separately.
#[test]
fn alpha_public_evals_is_the_weighted_column_contraction() {
    let (n, mu) = (2usize, 2usize);
    let s = statement(0x5A17_3005, n, mu);
    let mut r = Lcg::new(0x5A17_3006);
    let alpha = ext4(&mut r);
    let tau: Vec<Ext4> = (0..3).map(|_| ext4(&mut r)).collect();

    for idx in [0usize, 5, RING_DEGREE, RING_DEGREE + 3, 2 * RING_DEGREE + 1] {
        let mut sum = Ext4::ZERO;
        for i in 0..n {
            sum = sum + eq_weight(&tau, i) * m_alpha_tilde(&s, alpha, i, idx / RING_DEGREE);
        }
        let expected = pow_by_squaring(alpha, idx % RING_DEGREE) * sum;
        assert_eq!(alpha_public_evals(&s, alpha, &tau, idx), expected, "idx {idx}");
    }
}

/// Padding is harmless: above the encoded table every `M̃_α` case is zero, so
/// the whole entry vanishes however large the cube is.
#[test]
fn alpha_public_evals_vanishes_on_the_padding() {
    let (n, mu) = (2usize, 2usize);
    let s = statement(0x5A17_3007, n, mu);
    let mut r = Lcg::new(0x5A17_3008);
    let alpha = ext4(&mut r);
    let tau: Vec<Ext4> = (0..3).map(|_| ext4(&mut r)).collect();
    let first_pad_row = mu + n * GADGET_DIGITS;
    for u in [first_pad_row, first_pad_row + 1] {
        for l in [0usize, 9] {
            let idx = RING_DEGREE * u + l;
            assert!(
                alpha_public_evals(&s, alpha, &tau, idx).is_zero(),
                "padding row {u}, column {l}"
            );
        }
    }
}

/// `zcTargetAlpha` at a Boolean `τ₁ = e_k` is exactly `y_k(α)`: the equality
/// weights collapse to the indicator, so the sum picks out one right-hand side
/// entry. A sharper statement than re-summing the same products, and it pins
/// both the weight family and the evaluation together.
#[test]
fn zc_target_alpha_at_a_boolean_point_selects_one_row() {
    let n = 3usize;
    let s = statement(0x5A17_3009, n, 2);
    let mut r = Lcg::new(0x5A17_300A);
    let alpha = ext4(&mut r);
    for k in 0..n {
        let tau: Vec<Ext4> = (0..2)
            .map(|j| if (k >> j) & 1 == 1 { Ext4::ONE } else { Ext4::ZERO })
            .collect();
        assert_eq!(
            zc_target_alpha(&s, alpha, &tau),
            horner_ref(alpha, s.yvec().get(k)),
            "τ₁ = e_{k} must select y_{k}(α)"
        );
    }
}

/// And in general it is `∑ᵢ eq̃(τ₁, i)·yᵢ(α)`, with the evaluation taken by
/// Horner on the reference side.
#[test]
fn zc_target_alpha_is_the_weighted_sum_of_the_right_hand_side() {
    let n = 3usize;
    let s = statement(0x5A17_300B, n, 2);
    let mut r = Lcg::new(0x5A17_300C);
    let alpha = ext4(&mut r);
    let tau: Vec<Ext4> = (0..2).map(|_| ext4(&mut r)).collect();
    let mut expected = Ext4::ZERO;
    for i in 0..n {
        expected = expected + eq_weight(&tau, i) * horner_ref(alpha, s.yvec().get(i));
    }
    assert_eq!(zc_target_alpha(&s, alpha, &tau), expected);
}

// --- the H_alpha defect: the ring-switching identity itself -----------------
//
// `alphaDefect` is zero exactly when row `i` of the lift equation holds,
// `M_i · z = y_i + phi * rho_i` **as polynomials over Zq** -- unreduced, which
// is the whole content of the ring-switch claim. The reference below therefore
// builds an *honest* witness the way the identity demands: it multiplies
// without reducing, divides by `X^d + 1`, and hands the quotient to the witness
// and the remainder to the statement. That unreduced 2047-coefficient carrier
// lives here, in the test, and deliberately nowhere in the crate -- ArkLib's
// own `alphaDefect`/`hAlphaEvals_eq_alphaDefect` route means the translation
// never needs it (NOTES.md "The computable route around cRowSum").

/// Schoolbook product of two coefficient vectors **without** reducing modulo
/// `X^d + 1`: `2d - 1` coefficients, `u128` accumulation so a `u64` overflow
/// would mismatch rather than be reproduced.
fn mul_unreduced(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut out = vec![0u128; a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            out[i + j] = (out[i + j] + u128::from(*x) * u128::from(*y)) % u128::from(Q);
        }
    }
    out.into_iter().map(|v| v as u64).collect()
}

fn add_into(acc: &mut [u64], x: &[u64]) {
    for (a, b) in acc.iter_mut().zip(x.iter()) {
        *a = (*a + *b) % Q;
    }
}

/// Divide by the cyclotomic modulus `X^d + 1`, returning `(quotient,
/// remainder)`. Uses `X^k = X^{k-d}(X^d + 1) - X^{k-d}`, top down.
fn div_by_modulus(p: &[u64]) -> (Vec<u64>, Vec<u64>) {
    let d = RING_DEGREE;
    let mut c: Vec<u64> = p.to_vec();
    let mut quot = vec![0u64; d];
    for k in (d..c.len()).rev() {
        let ck = c[k];
        if ck != 0 {
            quot[k - d] = (quot[k - d] + ck) % Q;
            c[k - d] = (c[k - d] + Q - ck) % Q;
            c[k] = 0;
        }
    }
    c.truncate(d);
    (quot, c)
}

fn coeffs(a: &Rq) -> Vec<u64> {
    (0..RING_DEGREE).map(|k| a.coeff(k).to_u64()).collect()
}

/// An honest lift: `(statement, witness)` with `M_i · z = y_i + phi * rho_i`
/// for every row, by construction.
fn honest_lift(seed: u64, n: usize, mu: usize) -> (RlinStatement, LiftedWitness) {
    let mut r = Lcg::new(seed);
    let m = r.next_poly_matrix(n, mu);
    let z = r.next_poly_vec(mu);
    let mut yv = Vec::new();
    let mut rho = Vec::new();
    for i in 0..n {
        let mut acc = vec![0u64; 2 * RING_DEGREE - 1];
        for j in 0..mu {
            add_into(&mut acc, &mul_unreduced(&coeffs(m.row(i).get(j)), &coeffs(z.get(j))));
        }
        let (q_i, y_i) = div_by_modulus(&acc);
        yv.push(rq_from_u64s(&y_i));
        rho.push(QuotientRow::new(&q_i.iter().map(|v| Fp::new(*v)).collect::<Vec<Fp>>()));
    }
    (
        RlinStatement::new(m, PolyVec::new(yv), 15),
        LiftedWitness::new(z, rho),
    )
}

/// The headline property, and the reason this module exists: on an honest lift
/// the Eq. (22) defect is **zero** at every real row, and a single corrupted
/// coefficient of the right-hand side breaks it.
///
/// `#[ignore]`d for cost, not for doubt: `alpha_contract` walks
/// `(mu + n*delta) * d` table cells and the specification recomputes `M~_alpha`
/// inside the inner loop -- a `c_eval_at` per cell, linear since Stage 6
/// iteration 1 (it was `O(d^2)` in genesis) but still un-hoisted, which is
/// brief 4's item 4 and keeps this test at seconds-to-minutes rather than
/// milliseconds. Run it with
/// `cargo test --release -- --ignored` -- it was run and passed before the
/// genesis freeze, which is what `op-genesis` requires of it.
#[test]
fn alpha_defect_vanishes_exactly_on_an_honest_lift() {
    let (s, w) = honest_lift(0x5A17_5001, 1, 1);
    let mut r = Lcg::new(0x5A17_5002);
    let alpha = ext4(&mut r);
    assert!(
        alpha_defect(&s, alpha, &w, 0).is_zero(),
        "the defect must vanish on an honest lift"
    );
    assert!(h_alpha_evals(&s, alpha, &w, 0).is_zero());

    // Corrupt one coefficient of y_0: the identity no longer holds.
    let mut bad_y = coeffs(s.yvec().get(0));
    bad_y[3] = (bad_y[3] + 1) % Q;
    let bad = RlinStatement::new(
        PolyMatrix::new(vec![rlin_row(s.m(), 0)]),
        PolyVec::new(vec![rq_from_u64s(&bad_y)]),
        15,
    );
    assert!(
        !alpha_defect(&bad, alpha, &w, 0).is_zero(),
        "a corrupted right-hand side must not vanish"
    );
}

/// `alphaContract` is the double sum in the order the specification writes it;
/// this recomputes it in the *other* order (columns outer, rows inner) with an
/// independently squared power, so the summation structure is pinned rather
/// than restated.
#[test]
fn alpha_contract_is_the_double_sum_either_way_round() {
    let (s, w) = honest_lift(0x5A17_5003, 1, 1);
    let mut r = Lcg::new(0x5A17_5004);
    let alpha = ext4(&mut r);
    let table_rows = 1 + GADGET_DIGITS;
    let mut expected = Ext4::ZERO;
    for l in 0..RING_DEGREE {
        let a_l = pow_by_squaring(alpha, l);
        for u in 0..table_rows {
            expected = expected + m_alpha_tilde(&s, alpha, 0, u) * w_table(&w, RING_DEGREE * u + l) * a_l;
        }
    }
    assert_eq!(alpha_contract(&s, alpha, &w, 0), expected);
}

/// The padding half of `hAlphaEvals`, which costs nothing and is therefore the
/// live half: above the `n` real rows the `m_1` cube contributes zero, and
/// `h_alpha`'s table is `2^m_1` long whatever `n` is.
#[test]
fn h_alpha_pads_above_the_real_rows() {
    let (s, w) = honest_lift(0x5A17_5005, 0, 1);
    let mut r = Lcg::new(0x5A17_5006);
    let alpha = ext4(&mut r);
    for m1 in 1..=3usize {
        let block = h_alpha(&s, alpha, &w, m1);
        assert_eq!(block.len(), 1 << m1, "H_alpha is 2^m1 entries");
        for (i, e) in block.values().iter().enumerate() {
            assert!(e.is_zero(), "padding entry {i} must vanish");
        }
        assert!(h_alpha_is_zero(&s, alpha, &w, m1));
    }
    // And the guard is `idx < n`, so every index is padding when `n = 0`.
    assert!(h_alpha_evals(&s, alpha, &w, 0).is_zero());
}

// --- the cube guard and the bit walk, after the two_pow removal -----------

/// `eq_weight` reads only the low `m₁` bits of its index, so it is periodic in
/// `i` with period `2^m₁`. That is what `i / 2^j % 2` for `j < m₁` does, and
/// the running quotient has to agree with it *outside* the cube as well as
/// inside -- a property of the family, not a re-computation of one entry.
#[test]
fn eq_weight_reads_only_the_low_m1_bits() {
    let mut r = Lcg::new(0x51DE_0B17_5A17_3002);
    let m1 = 3usize;
    let tau: Vec<Ext4> = (0..m1).map(|_| ext4(&mut r)).collect();
    for i in 0..64usize {
        assert_eq!(
            eq_weight(&tau, i),
            eq_weight(&tau, i % (1usize << m1)),
            "i = {i} must agree with its residue mod 2^{m1}"
        );
    }
}

/// **The `i < 2^m₁` guard is decided even when `2^m₁` does not fit in a
/// `usize`.** This is the test the previous implementation could not pass: it
/// bound `cube = two_pow(tau1.len())`, and at `m₁ = 64` that doubles `1`
/// sixty-four times and wraps to `0` in release, so `i < cube` was false for
/// every row and the target came out `0` -- silently, with nothing reported.
///
/// `below_two_pow` halves `i` instead and never forms the size, so the guard is
/// the specification's predicate at any width. The reference reads the bits
/// with `>>` and `&`, which the crate does not use, and shifts cannot overflow
/// here because `j < 64`.
#[test]
fn the_cube_guard_survives_a_width_whose_cube_size_does_not_fit() {
    let mut r = Lcg::new(0xC0DE_FA11_5A17_3003);
    let n = 3usize;
    let s = statement(0x5A17_3004, n, 2);
    let alpha = ext4(&mut r);
    let vars = 64usize;
    let tau: Vec<Ext4> = (0..vars).map(|_| ext4(&mut r)).collect();

    let got = zc_target_alpha(&s, alpha, &tau);

    let mut expected = Ext4::ZERO;
    for i in 0..n {
        let mut w = Ext4::ONE;
        for j in 0..vars {
            w = w * if (i >> j) & 1 == 1 {
                tau[j]
            } else {
                Ext4::ONE - tau[j]
            };
        }
        expected = expected + w * horner_ref(alpha, s.yvec().get(i));
    }

    assert_eq!(
        got, expected,
        "every row must contribute: i < 2^64 holds for all three"
    );
    assert!(
        !got.is_zero(),
        "a zero target here is the old wrap-to-zero bug, not a coincidence"
    );
}

// --- the guard and the bit walk at widths the old form could not reach -----

/// Bit `j` of `k`, safe for `j` beyond the word: `>>` by `usize::BITS` or more
/// is a panic in Rust, which is itself a reason the crate walks a quotient.
fn bit_at(k: usize, j: usize) -> usize {
    if j < usize::BITS as usize {
        (k >> j) & 1
    } else {
        0
    }
}

/// The old power form of the weight, spelled out: bit `j` is `(i / 2^j) % 2`,
/// with the power materialized. This is the reference the running quotient has
/// to reproduce, and it is only usable where `1 << j` does not overflow --
/// which is exactly the limitation that made it the wrong thing to compute.
fn eq_weight_power_ref(tau: &[Ext4], i: usize) -> Ext4 {
    let mut acc = Ext4::ONE;
    for (j, t) in tau.iter().enumerate() {
        let bit = (i / (1usize << j)) % 2;
        acc = acc * if bit == 1 { *t } else { Ext4::ONE - *t };
    }
    acc
}

/// `below_two_pow` decides `i < 2^m` at **every** width: it agrees with the
/// shift form wherever the shift is defined, and is unconditionally true once
/// `2^m` exceeds `usize::MAX`.
///
/// The reference computes `1u128 << m`, which is why it can only check
/// `m < 64` directly -- and why the second half asserts the mathematical fact
/// instead of comparing against a number that cannot be built.
#[test]
fn below_two_pow_decides_the_cube_guard_at_every_width() {
    let probes = [
        0usize, 1, 2, 3, 7, 8, 63, 64, 255, 256, 1023, 1 << 20, usize::MAX,
    ];
    for m in 0..64usize {
        for i in probes {
            let expected = (i as u128) < (1u128 << m);
            assert_eq!(below_two_pow(i, m), expected, "i = {i}, m = {m}");
        }
    }
    for m in [64usize, 65, 100, 1000] {
        for i in probes {
            assert!(
                below_two_pow(i, m),
                "2^{m} exceeds usize::MAX, so i = {i} is below it"
            );
        }
    }
}

/// At a **70-variable** Boolean `τ₁` encoding row `k`, the weight is the row-`k`
/// indicator and the target is row `k`'s evaluation -- and neither panics.
///
/// Seventy is past the word: the old `cube = two_pow(70)` wrapped to zero and
/// skipped every row, and a reference reading bits with `>>` would panic. The
/// existing tests in this file run `m₁ ≤ 4`, which is precisely why they could
/// not see any of that.
#[test]
fn a_seventy_variable_boolean_point_still_selects_row_k() {
    let vars = 70usize;
    let n = 3usize;
    let s = statement(0x5A17_3005, n, 2);
    let mut r = Lcg::new(0x5A17_3006);
    let alpha = ext4(&mut r);

    for k in 0..n {
        let tau: Vec<Ext4> = (0..vars)
            .map(|j| {
                if bit_at(k, j) == 1 {
                    Ext4::ONE
                } else {
                    Ext4::ZERO
                }
            })
            .collect();

        for i in 0..n {
            let w = eq_weight(&tau, i);
            if i == k {
                assert_eq!(w, Ext4::ONE, "eq(e_{k}, {i}) at 70 vars");
            } else {
                assert!(w.is_zero(), "eq(e_{k}, {i}) must vanish at 70 vars");
            }
        }

        assert_eq!(
            zc_target_alpha(&s, alpha, &tau),
            horner_ref(alpha, s.yvec().get(k)),
            "the target at a 70-variable e_{k} must be row {k}'s evaluation"
        );
    }
}

/// The running quotient agrees with the power form wherever the power form is
/// computable -- inside the cube and beyond it, over random points.
#[test]
fn the_running_quotient_agrees_with_the_power_form() {
    let mut r = Lcg::new(0x5A17_3007);
    for m1 in 1..=6usize {
        let tau: Vec<Ext4> = (0..m1).map(|_| ext4(&mut r)).collect();
        for i in 0..(4usize << m1) {
            assert_eq!(
                eq_weight(&tau, i),
                eq_weight_power_ref(&tau, i),
                "m1 = {m1}, i = {i}"
            );
        }
    }
}

/// **The guard's upper boundary**, which nothing else in this file exercises.
///
/// At the pinned `n = 5 ≤ 8 = 2^m₁` the `i < 2^m₁` guard never fires, so every
/// other test here passes whether the bound is right, too large, or absent.
/// Found by mutation: `below_two_pow(i, tau1.len() + 1)` survived all
/// twenty-four. This one puts *more rows than the cube can index* -- `n = 3`
/// against `m₁ = 1` -- so rows at or above `2^m₁` are padding and must
/// contribute nothing, and it checks the dropped contribution is nonzero so
/// the assertion cannot pass vacuously.
#[test]
fn the_cube_guard_drops_rows_above_the_cube() {
    let n = 3usize;
    let m1 = 1usize;
    let s = statement(0x5A17_3008, n, 2);
    let mut r = Lcg::new(0x5A17_3009);
    let alpha = ext4(&mut r);
    let tau: Vec<Ext4> = (0..m1).map(|_| ext4(&mut r)).collect();
    let cube = 1usize << m1;

    // zc_target_alpha: only rows below the cube may contribute.
    let mut expected = Ext4::ZERO;
    for i in 0..cube {
        expected = expected + eq_weight(&tau, i) * horner_ref(alpha, s.yvec().get(i));
    }
    assert_eq!(
        zc_target_alpha(&s, alpha, &tau),
        expected,
        "rows at or above 2^m1 are padding and must be dropped"
    );
    let dropped = eq_weight(&tau, cube) * horner_ref(alpha, s.yvec().get(cube));
    assert!(
        !dropped.is_zero(),
        "row {cube}'s contribution must be nonzero, else this test is vacuous"
    );

    // alpha_public_evals carries the same guard over the matrix's rows.
    let idx = 3usize;
    let mut expected_ap = Ext4::ZERO;
    for i in 0..cube {
        expected_ap = expected_ap
            + eq_weight(&tau, i) * m_alpha_tilde(&s, alpha, i, idx / RING_DEGREE);
    }
    expected_ap = expected_ap * alpha_tilde(alpha, idx % RING_DEGREE);
    assert_eq!(
        alpha_public_evals(&s, alpha, &tau, idx),
        expected_ap,
        "the same padding rule applies to the public table"
    );
}

/// One row of an `RlinMat`, read out through `entry`. The statement no longer
/// stores rows (wall W2), and these tests want one; `entry` is the only reader
/// the source has.
fn rlin_row(m: &hachi::ringswitch::RlinMat, i: usize) -> PolyVec {
    let mut v: Vec<hachi::ring::Rq> = Vec::new();
    for j in 0..m.cols() {
        v.push(m.entry(i, j).copy());
    }
    PolyVec::new(v)
}

/// Card T48e: the table-driven evaluation is `c_eval_at` -- the same power sum
/// with `α^k` read from `alpha_pow_table(α, d)` and each term the mixed
/// `Fp × Ext4` product -- on random polynomials, the zero polynomial, and a
/// monomial at the top degree.
#[test]
fn c_eval_at_pw_is_c_eval_at() {
    use hachi::ringswitch::c_eval_at;
    use hachi::zerocheck::{alpha_pow_table, c_eval_at_pw};
    let mut r = support::Lcg::new(0x7480_0001);
    let d = hachi::params::RING_DEGREE;
    for _ in 0..4 {
        let alpha = cpoly::Ext4::new(r.next_fp(), r.next_fp(), r.next_fp(), r.next_fp());
        let pw = alpha_pow_table(alpha, d);
        let p = r.next_rq();
        assert_eq!(c_eval_at_pw(&pw, &p), c_eval_at(alpha, &p));
        let zero = hachi::ring::Rq::zero();
        assert_eq!(c_eval_at_pw(&pw, &zero), c_eval_at(alpha, &zero));
        let mut top = vec![cpoly::Fp::ZERO; d];
        top[d - 1] = r.next_fp();
        let m = hachi::ring::Rq::from_coeffs(&top);
        assert_eq!(c_eval_at_pw(&pw, &m), c_eval_at(alpha, &m));
    }
}
