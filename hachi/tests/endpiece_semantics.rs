//! `src/endpiece.rs`: the terminal statement and the end piece.
//!
//! The headline test is [`end_piece_check_decides_the_conjunction`], the
//! specification's `endPieceCheck_eq_true_iff` (`EndPiece/Reduction.lean:225`):
//! over a corpus of honest and dishonest `(stmt, w)` pairs the crate's verdict
//! is exactly `A ∧ B ∧ C` with each conjunct recomputed here independently. The
//! three reject tests around it isolate one conjunct each while the other two
//! are honest, [`end_piece_check_pins_the_z_norm_boundary`] walks `‖z‖∞` across
//! `CHAIN_GAMMA`, and the two identities `endPieceProver` / `endPieceWitness`
//! are pinned coefficientwise.
//!
//! # Scale
//!
//! REDUCED, for the same reason `zerocheck_semantics` is: conjunct C is a
//! `2^m₀`-entry table and `m₀ = M_ZERO = 26` at the pinned profile. The
//! witness fits the cube only when `(μ + n·δ)·d ≤ 2^m₀`, so `(μ, n) = (1, 0)`
//! lives at `m₀ = 10` (the table *is* `z₀`) or `11` (one half padding), and the
//! first shape with a quotient row, `(1, 1)`, needs `m₀ = 14`. That shape is
//! the path all three conjuncts' digit blocks share, and it is live here --
//! it costs seconds in debug, not minutes.
//!
//! The references are written in the specification's shape and not the
//! crate's: `w̃(i)` is read from the witness through a `Nat.digits`-style
//! balanced digit (never `w_table`), `mle[w̃](a)` is the explicit sum
//! `Σᵢ w̃(i)·eq̃(i, a)` with `eq̃` a bit product (never cpoly's Lagrange basis),
//! the commitment is an explicit row-by-message dot product over an unreduced
//! `u128` schoolbook product folded by `X^d = −1` (never `Rq::mul` /
//! `mat_vec_mul`), and `‖z‖∞` is the largest `|valMinAbs|` as a signed integer
//! (never `centered_abs`). The honest statement's `t` and `value` are built
//! from those references, so the accept case pins every conjunct against an
//! independent computation rather than against the crate's own.

// The centered view of a residue is a *signed* integer (`ZMod.valMinAbs`), and
// the references below compute it as one. Every value cast is below `q < 2^32`.
#![allow(clippy::cast_possible_wrap)]
#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::cast_sign_loss)]

mod support;

use cpoly::{Ext4, Fp};
use hachi::endpiece::{end_piece_check, end_piece_prove, end_piece_witness, WEvalStatement};
use hachi::linalg::{PolyMatrix, PolyVec};
use hachi::params::{
    BALANCED_SHIFT, CHAIN_GAMMA, D_ROWS, GADGET_BASE, GADGET_DIGITS, HALF_BASE, Q, RING_DEGREE,
};
use hachi::ringswitch::{LiftedWitness, QuotientRow};
use support::{coeffs_of, rq_from_u64s, Lcg};

// --- the references ---------------------------------------------------------

/// `φF` -- the base embedding `ZMod q →+* F`.
fn phi(c: Fp) -> Ext4 {
    Ext4::from_base(c)
}

/// `ZMod.valMinAbs`, as the signed integer it is.
fn val_min_abs(c: Fp) -> i64 {
    let v = c.to_u64();
    if v <= Q / 2 {
        v as i64
    } else {
        v as i64 - Q as i64
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
    Fp::new((d + Q - HALF_BASE) % Q)
}

/// `eq̃(i, a) = ∏_j (if bit j of i then a_j else 1 - a_j)`, as an explicit bit
/// product over the index.
fn eq_tilde_ref(i: usize, a: &[Ext4]) -> Ext4 {
    let mut acc = Ext4::ONE;
    for (j, aj) in a.iter().enumerate() {
        let bit = (i >> j) & 1 == 1;
        acc = acc * if bit { *aj } else { Ext4::ONE - *aj };
    }
    acc
}

/// `wTable` (`ZeroCheck/Constraints.lean:317`) read straight off the witness:
/// the `z` block coefficientwise, the quotient block through the independent
/// balanced digit, digit-major inside each row, and `0` above both.
fn w_tilde_ref(w: &LiftedWitness, idx: usize) -> Ext4 {
    let row = idx / RING_DEGREE;
    let col = idx % RING_DEGREE;
    let mu = w.z().len();
    if row < mu {
        return phi(w.z().get(row).coeff(col));
    }
    let j = row - mu;
    if j < w.rho().len() * GADGET_DIGITS {
        let source = &w.rho()[j / GADGET_DIGITS];
        return phi(balanced_digit(source.coeff(col), j % GADGET_DIGITS));
    }
    Ext4::ZERO
}

/// `mle[w̃](a) = Σ_{i < 2^{m₀}} w̃(i)·eq̃(i, a)`, with `m₀ = a.len()`.
fn mle_eval_ref(w: &LiftedWitness, a: &[Ext4]) -> Ext4 {
    let mut acc = Ext4::ZERO;
    for i in 0..(1usize << a.len()) {
        acc = acc + w_tilde_ref(w, i) * eq_tilde_ref(i, a);
    }
    acc
}

/// The negacyclic product in two passes: an unreduced `2d − 1`-coefficient
/// schoolbook product with `u128` accumulation, then the fold `X^d = −1`. The
/// crate folds the sign inside its double loop; a mistake in either shape shows
/// up as a mismatch rather than being reproduced.
fn mul_negacyclic_ref(a: &[u64], b: &[u64]) -> Vec<u64> {
    let d = RING_DEGREE;
    let q = u128::from(Q);
    let mut wide = vec![0u128; 2 * d - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            wide[i + j] = (wide[i + j] + u128::from(*x) * u128::from(*y)) % q;
        }
    }
    let mut out = vec![0u64; d];
    for k in 0..d {
        let high = if k + d < wide.len() { wide[k + d] } else { 0 };
        out[k] = ((wide[k] + q - high) % q) as u64;
    }
    out
}

/// Entry `j` of `liftMessage w = z ‖ digits(ρ)` as coefficient words, the
/// quotient digits through the independent balanced digit.
fn lift_message_entry_ref(w: &LiftedWitness, j: usize) -> Vec<u64> {
    let mu = w.z().len();
    if j < mu {
        return coeffs_of(w.z().get(j));
    }
    let jj = j - mu;
    let source = &w.rho()[jj / GADGET_DIGITS];
    let u = jj % GADGET_DIGITS;
    (0..RING_DEGREE)
        .map(|k| balanced_digit(source.coeff(k), u).to_u64())
        .collect()
}

/// `K.com w = D *ᵥ liftMessage w` (`hachiLiftCom`, `RingSwitch/Reduction.lean:277`)
/// as an explicit row-by-message dot product, never through `mat_vec_mul`.
fn commit_ref(d_key: &PolyMatrix, w: &LiftedWitness) -> PolyVec {
    let cols = w.z().len() + w.rho().len() * GADGET_DIGITS;
    assert_eq!(
        d_key.cols(),
        cols,
        "the key must be as wide as the lifted message"
    );
    let mut rows = Vec::new();
    for r in 0..d_key.rows() {
        let mut acc = vec![0u64; RING_DEGREE];
        for j in 0..cols {
            let prod = mul_negacyclic_ref(
                &coeffs_of(d_key.row(r).get(j)),
                &lift_message_entry_ref(w, j),
            );
            for k in 0..RING_DEGREE {
                acc[k] = (acc[k] + prod[k]) % Q;
            }
        }
        rows.push(rq_from_u64s(&acc));
    }
    PolyVec::new(rows)
}

/// `‖z‖∞` as the largest `|valMinAbs|` over every coefficient of every entry.
fn z_norm_ref(w: &LiftedWitness) -> u64 {
    let mut best = 0u64;
    for i in 0..w.z().len() {
        for k in 0..RING_DEGREE {
            best = best.max(val_min_abs(w.z().get(i).coeff(k)).unsigned_abs());
        }
    }
    best
}

/// `rhoDigitsShortCheck` (`EndPiece/Reduction.lean:111`) through the
/// independent digit. A tautology at these parameters (every balanced base-16
/// digit is `8`-bounded and `CHAIN_GAMMA = 15`), computed anyway so the
/// conjunction below is the specification's and not a shortcut.
fn digits_short_ref(w: &LiftedWitness) -> bool {
    let mut short = true;
    for row in w.rho() {
        for u in 0..GADGET_DIGITS {
            for k in 0..RING_DEGREE {
                if val_min_abs(balanced_digit(row.coeff(k), u)).unsigned_abs() > CHAIN_GAMMA {
                    short = false;
                }
            }
        }
    }
    short
}

/// Conjunct A: `K.com w == stmt.t`, compared coefficientwise as words.
fn a_ref(d_key: &PolyMatrix, stmt: &WEvalStatement, w: &LiftedWitness) -> bool {
    let com = commit_ref(d_key, w);
    if com.len() != stmt.t().len() {
        return false;
    }
    (0..com.len()).all(|i| coeffs_of(com.get(i)) == coeffs_of(stmt.t().get(i)))
}

/// Conjunct B: `liftShortCheck bound bDig w` (`EndPiece/Reduction.lean:130`).
fn b_ref(w: &LiftedWitness) -> bool {
    z_norm_ref(w) <= CHAIN_GAMMA && digits_short_ref(w)
}

/// Conjunct C: `wTableMleEval m₀ w stmt.point == stmt.value`.
fn c_ref(stmt: &WEvalStatement, w: &LiftedWitness) -> bool {
    mle_eval_ref(w, stmt.point()) == stmt.value()
}

// --- the corpus builders ----------------------------------------------------

/// A short `z`: `mu` ring elements with every centered coefficient in
/// `[−norm, norm]`, and `‖z‖∞ = norm` *exactly* -- coefficient `0` of `z₀` is
/// `+norm` and coefficient `1` is `−norm`, so both signs sit on the boundary.
fn short_z(r: &mut Lcg, mu: usize, norm: u64) -> PolyVec {
    let mut entries = Vec::new();
    for i in 0..mu {
        let mut c = Vec::new();
        for _ in 0..RING_DEGREE {
            let v = r.next_u64() % (2 * norm + 1);
            c.push(if v <= norm { v } else { Q - (v - norm) });
        }
        if i == 0 {
            c[0] = norm;
            c[1] = (Q - norm) % Q;
        }
        entries.push(rq_from_u64s(&c));
    }
    PolyVec::new(entries)
}

/// `n` quotient rows with arbitrary (full-range) coefficients: the digit block
/// is short whatever the row is, which is what conjunct B2's tautology says.
fn quotient_rows(r: &mut Lcg, n: usize) -> Vec<QuotientRow> {
    let mut rho = Vec::new();
    for _ in 0..n {
        let mut coeffs = Vec::new();
        for _ in 0..RING_DEGREE {
            coeffs.push(r.next_fp());
        }
        rho.push(QuotientRow::new(&coeffs));
    }
    rho
}

fn ext4(r: &mut Lcg) -> Ext4 {
    Ext4::new(r.next_fp(), r.next_fp(), r.next_fp(), r.next_fp())
}

/// The sumcheck point `a ∈ F^{m₀}`.
fn point(r: &mut Lcg, m0: usize) -> Vec<Ext4> {
    (0..m0).map(|_| ext4(r)).collect()
}

/// An honest `(D, stmt, w)` at the given shape: `w` has `‖z‖∞ = norm` exactly
/// and `n` arbitrary quotient rows; `stmt.t` and `stmt.value` are the
/// *reference* commitment and evaluation, so the crate is measured against
/// them and not against itself.
fn honest(
    seed: u64,
    mu: usize,
    n: usize,
    m0: usize,
    norm: u64,
) -> (PolyMatrix, WEvalStatement, LiftedWitness) {
    assert!(
        (mu + n * GADGET_DIGITS) * RING_DEGREE <= 1 << m0,
        "the witness must fit the cube"
    );
    let mut r = Lcg::new(seed);
    let w = LiftedWitness::new(short_z(&mut r, mu, norm), quotient_rows(&mut r, n));
    let d_key = r.next_poly_matrix(D_ROWS, mu + n * GADGET_DIGITS);
    let a = point(&mut r, m0);
    let t = commit_ref(&d_key, &w);
    let value = mle_eval_ref(&w, &a);
    (d_key, WEvalStatement::new(t, a, value), w)
}

/// `t` with coefficient `k` of its first entry moved by one.
fn perturb_t(t: &PolyVec, k: usize) -> PolyVec {
    let mut entries = Vec::new();
    for i in 0..t.len() {
        let mut c = coeffs_of(t.get(i));
        if i == 0 {
            c[k] = (c[k] + 1) % Q;
        }
        entries.push(rq_from_u64s(&c));
    }
    PolyVec::new(entries)
}

fn with_t(stmt: &WEvalStatement, t: PolyVec) -> WEvalStatement {
    WEvalStatement::new(t, stmt.point().clone(), stmt.value())
}

fn with_value(stmt: &WEvalStatement, value: Ext4) -> WEvalStatement {
    WEvalStatement::new(stmt.t().copy(), stmt.point().clone(), value)
}

/// Every coefficient of a witness as words, `z` entries then quotient rows.
fn witness_words(w: &LiftedWitness) -> Vec<Vec<u64>> {
    let mut out = Vec::new();
    for i in 0..w.z().len() {
        out.push(coeffs_of(w.z().get(i)));
    }
    for row in w.rho() {
        out.push((0..RING_DEGREE).map(|k| row.coeff(k).to_u64()).collect());
    }
    out
}

// --- WEvalStatement ---------------------------------------------------------

/// `WEvalStatement` (`Sumcheck/FinalEval.lean:72`): three fields, nothing
/// else, each read back as it went in.
#[test]
fn w_eval_statement_carries_its_three_fields() {
    let mut r = Lcg::new(0xE9D0_0001);
    let t = r.next_poly_vec(D_ROWS);
    let a = point(&mut r, 5);
    let value = ext4(&mut r);
    let stmt = WEvalStatement::new(t.copy(), a.clone(), value);
    assert!(stmt.t().equals(&t));
    assert_eq!(stmt.point().len(), 5, "the point's length is m₀");
    assert_eq!(*stmt.point(), a);
    assert_eq!(stmt.value(), value);
}

// --- endPieceCheck, the accept case -----------------------------------------

/// `endPieceCheck` (`EndPiece/Reduction.lean:143-147`) accepts an honest claim,
/// i.e. a pair in `relWEvalClaim` (`Sumcheck/FinalEval.lean:159-165`): the
/// commitment, the shortness and the evaluation all hold by construction, and
/// each was built by the reference and not by the crate. At `m₀ = 10` the cube
/// is exactly `z₀`; at `m₀ = 11` its upper half is the `else 0` padding.
#[test]
fn end_piece_check_accepts_an_honest_claim() {
    for (seed, m0) in [(0xE9D0_0010u64, 10usize), (0xE9D0_0011, 11)] {
        let (d_key, stmt, w) = honest(seed, 1, 0, m0, CHAIN_GAMMA);
        assert!(a_ref(&d_key, &stmt, &w) && b_ref(&w) && c_ref(&stmt, &w));
        assert!(end_piece_check(&d_key, &stmt, &w), "m₀ = {m0}");
    }
}

// --- the three conjuncts, isolated ------------------------------------------

/// Conjunct A alone: one coefficient of `t` moved by one, at the first and the
/// last position, with B and C still honest.
#[test]
fn end_piece_check_rejects_a_perturbed_commitment() {
    let (d_key, stmt, w) = honest(0xE9D0_0020, 1, 0, 10, CHAIN_GAMMA);
    for k in [0usize, 511, RING_DEGREE - 1] {
        let bad = with_t(&stmt, perturb_t(stmt.t(), k));
        assert!(
            !a_ref(&d_key, &bad, &w) && b_ref(&w) && c_ref(&bad, &w),
            "only A fails at {k}"
        );
        assert!(
            !end_piece_check(&d_key, &bad, &w),
            "t perturbed at coefficient {k}"
        );
    }
}

/// Conjunct B alone, `liftShortCheck` (`EndPiece/Reduction.lean:130`), at its
/// boundary and *through* `end_piece_check`: `‖z‖∞ ∈ {14, 15}` accepts and
/// `16` rejects, with A and C rebuilt honestly for each witness so nothing else
/// changes. `bound = CHAIN_GAMMA = 15`, not `GAMMA = 16`.
///
/// Only the `z` half of B can reject: its other half,
/// `rhoDigitsShortCheck`, is a tautology at `(bDig, bound) = (16, 15)`, since a
/// balanced base-16 digit has centered magnitude at most `8`. So honest inputs
/// test that half vacuously -- [`digits_short_ref`] is asserted alongside to
/// say so, and `ringswitch_semantics` pins the digit bound itself.
#[test]
fn end_piece_check_pins_the_z_norm_boundary() {
    for (seed, norm, accept) in [
        (0xE9D0_0030u64, CHAIN_GAMMA - 1, true),
        (0xE9D0_0031, CHAIN_GAMMA, true),
        (0xE9D0_0032, CHAIN_GAMMA + 1, false),
    ] {
        let (d_key, stmt, w) = honest(seed, 1, 0, 10, norm);
        assert_eq!(
            z_norm_ref(&w),
            norm,
            "the witness must sit exactly at ‖z‖∞ = {norm}"
        );
        assert!(
            a_ref(&d_key, &stmt, &w) && c_ref(&stmt, &w),
            "A and C stay honest at {norm}"
        );
        assert!(digits_short_ref(&w), "B2 is vacuous at these parameters");
        assert_eq!(b_ref(&w), accept);
        assert_eq!(end_piece_check(&d_key, &stmt, &w), accept, "‖z‖∞ = {norm}");
    }
}

/// Conjunct C alone: the claimed value moved by one, with A and B honest.
#[test]
fn end_piece_check_rejects_a_wrong_value() {
    let (d_key, stmt, w) = honest(0xE9D0_0040, 1, 0, 10, CHAIN_GAMMA);
    let bad = with_value(&stmt, stmt.value() + Ext4::ONE);
    assert!(
        a_ref(&d_key, &bad, &w) && b_ref(&w) && !c_ref(&bad, &w),
        "only C fails"
    );
    assert!(!end_piece_check(&d_key, &bad, &w));
}

// --- endPieceCheck_eq_true_iff ----------------------------------------------

/// One corpus entry: a name, the key, the claim, the witness, and the
/// `(A, B, C)` pattern the entry was built to hit.
type Case = (
    &'static str,
    PolyMatrix,
    WEvalStatement,
    LiftedWitness,
    (bool, bool, bool),
);

/// `endPieceCheck_eq_true_iff` (`EndPiece/Reduction.lean:225`): the verdict is
/// exactly `A ∧ B ∧ C`, each conjunct recomputed by its reference, over a
/// corpus that fails every non-empty subset of the three at least once and
/// passes twice. The expected triple is asserted too, so a corpus entry that
/// drifted onto a different pattern would be noticed rather than averaged in.
#[test]
fn end_piece_check_decides_the_conjunction() {
    let mut corpus: Vec<Case> = Vec::new();

    let (d, s, w) = honest(0xE9D0_0050, 1, 0, 10, CHAIN_GAMMA);
    corpus.push(("honest", d, s, w, (true, true, true)));

    let (d, s, w) = honest(0xE9D0_0051, 1, 0, 11, 3);
    corpus.push(("honest, padded cube", d, s, w, (true, true, true)));

    let (d, s, w) = honest(0xE9D0_0052, 1, 0, 10, CHAIN_GAMMA);
    let s = with_t(&s, perturb_t(s.t(), 17));
    corpus.push(("t perturbed", d, s, w, (false, true, true)));

    let (d, s, w) = honest(0xE9D0_0053, 1, 0, 10, CHAIN_GAMMA + 1);
    corpus.push(("z one over the bound", d, s, w, (true, false, true)));

    let (d, s, w) = honest(0xE9D0_0054, 1, 0, 10, CHAIN_GAMMA);
    let s = with_value(&s, s.value() + Ext4::ONE);
    corpus.push(("value off by one", d, s, w, (true, true, false)));

    let (d, s, w) = honest(0xE9D0_0055, 1, 0, 10, CHAIN_GAMMA + 1);
    let s = with_t(&s, perturb_t(s.t(), 0));
    corpus.push(("t perturbed, z long", d, s, w, (false, false, true)));

    let (d, s, w) = honest(0xE9D0_0056, 1, 0, 10, CHAIN_GAMMA + 1);
    let s = with_value(&s, Ext4::ZERO - s.value());
    corpus.push(("z long, value negated", d, s, w, (true, false, false)));

    // Two honest pairs with the statements swapped: `t` and `value` both belong
    // to the other witness, and `z` stays short.
    let (d1, s1, w1) = honest(0xE9D0_0057, 1, 0, 10, CHAIN_GAMMA);
    let (_, s2, w2) = honest(0xE9D0_0058, 1, 0, 10, CHAIN_GAMMA);
    corpus.push(("statements swapped", d1, s2, w1, (false, true, false)));

    // A witness with a full-range `z`, under a random key and random claims.
    let mut r = Lcg::new(0xE9D0_0059);
    let w3 = LiftedWitness::new(r.next_poly_vec(1), Vec::new());
    let s3 = WEvalStatement::new(r.next_poly_vec(D_ROWS), point(&mut r, 10), ext4(&mut r));
    corpus.push((
        "everything random",
        r.next_poly_matrix(D_ROWS, 1),
        s3,
        w3,
        (false, false, false),
    ));
    drop((s1, w2));

    for (name, d_key, stmt, w, expected) in &corpus {
        let triple = (a_ref(d_key, stmt, w), b_ref(w), c_ref(stmt, w));
        assert_eq!(
            triple, *expected,
            "{name}: the references must match the intended pattern"
        );
        let (a, b, c) = triple;
        assert_eq!(end_piece_check(d_key, stmt, w), a && b && c, "{name}");
    }
}

// --- the shape with a quotient row ------------------------------------------

/// The first shape whose witness has a digit block: `(μ, n) = (1, 1)` at
/// `m₀ = 14`, where the key is `1 × 9`, the lifted message is `z₀` followed by
/// the eight balanced digits of `ρ₀`, and the cube holds those nine ring
/// elements and `7·1024` zeros. The quotient-digit bound uses its proved fast
/// path; the remaining checks use the independent digit: the honest
/// claim accepts, and moving the claimed value or the commitment rejects.
///
/// Live rather than `#[ignore]`d: conjunct C rebuilds a `1024`-wide digit
/// vector for each of the `8192` quotient-block entries, which is seconds in
/// debug and the cost is paid once per `end_piece_check` call.
#[test]
fn end_piece_check_with_a_quotient_row() {
    let (d_key, stmt, w) = honest(0xE9D0_0060, 1, 1, 14, CHAIN_GAMMA);
    assert_eq!(d_key.cols(), 1 + GADGET_DIGITS);
    assert!(
        digits_short_ref(&w),
        "B2 is vacuous even for a full-range quotient row"
    );
    assert!(a_ref(&d_key, &stmt, &w) && b_ref(&w) && c_ref(&stmt, &w));
    assert!(
        end_piece_check(&d_key, &stmt, &w),
        "honest claim with a quotient row"
    );

    // C alone, through the digit block: the value moved by one.
    let bad_value = with_value(&stmt, stmt.value() + Ext4::ONE);
    assert!(!end_piece_check(&d_key, &bad_value, &w), "value off by one");

    // A alone, through the digit block: `t` moved by one.
    let bad_t = with_t(&stmt, perturb_t(stmt.t(), 3));
    assert!(!end_piece_check(&d_key, &bad_t, &w), "t perturbed");
}

// --- the two identities -----------------------------------------------------

/// `endPieceProver` (`EndPiece/Reduction.lean:241-252`): its one message is the
/// witness itself, every coefficient of `z` and of every quotient row intact.
#[test]
fn end_piece_prove_returns_the_witness_unchanged() {
    let mut r = Lcg::new(0xE9D0_0070);
    let w = LiftedWitness::new(short_z(&mut r, 2, CHAIN_GAMMA), quotient_rows(&mut r, 3));
    let before = witness_words(&w);
    let sent = end_piece_prove(w);
    assert_eq!(sent.z().len(), 2);
    assert_eq!(sent.rho().len(), 3);
    assert_eq!(witness_words(&sent), before);
}

/// `endPieceWitness` (`EndPiece/Reduction.lean:172-174`): the transcript's one
/// message is the witness, and the statement is ignored -- two different
/// statements read the same witness off the same message.
#[test]
fn end_piece_witness_is_the_message() {
    let mut r = Lcg::new(0xE9D0_0080);
    let w = LiftedWitness::new(short_z(&mut r, 1, CHAIN_GAMMA), quotient_rows(&mut r, 2));
    let before = witness_words(&w);
    let stmt = WEvalStatement::new(r.next_poly_vec(D_ROWS), point(&mut r, 4), ext4(&mut r));
    let other = WEvalStatement::new(r.next_poly_vec(D_ROWS), point(&mut r, 6), ext4(&mut r));

    let got = end_piece_witness(&stmt, w);
    assert_eq!(witness_words(&got), before);
    let again = end_piece_witness(&other, got);
    assert_eq!(witness_words(&again), before, "the statement plays no part");
}
