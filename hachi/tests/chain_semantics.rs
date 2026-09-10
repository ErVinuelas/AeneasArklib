//! `src/chain.rs`: the composed evaluation chain.
//!
//! # What this file can and cannot check, stated up front
//!
//! The composed chain's *acceptance* property -- an honest run verifies --
//! needs an honest transcript: a witness `w = (z, ρ)` that actually solves the
//! `R^lin` system the rows 1–3 assemble, so that the sumcheck's initial
//! targets (`0` and `zcTargetAlpha`) are the true hypercube sums and every
//! `roundCheck` passes. Producing one means the honest lift prover
//! (`honestLiftWitnessC`, the quotient rows by synthetic division), which is
//! **not translated** in this crate (`src/chain.rs` § `chain_open`), and it
//! means a cube that covers the whole table -- `hcov : (μ + n·δ)·d ≤ 2^m₀`,
//! i.e. `m₀ = 26` -- because a reduced cube truncates the sums the targets
//! are computed from. **That test is owed and is not here.** It is owed to
//! the honest lift prover first.
//!
//! What is here is the half that does not need it:
//!
//! * **the plumbing**: `chain_verify` threads rows 1–8 at a toy cube without
//!   panicking. Across those rows of index arithmetic -- flat cube indices,
//!   three column blocks, `rlinCols` boundaries -- a shape disagreement
//!   between adjacent rows is an out-of-bounds panic, not a wrong answer.
//!   Rows 9 and the end piece are reached only past an accepted round loop,
//!   so they are covered by their own modules' tests
//!   (`sumcheck_semantics.rs` § `final_check`, `endpiece_semantics.rs`) and
//!   not here.
//! * **the round loop is load-bearing**: a transcript whose messages do not
//!   sum to the targets is rejected, which is `roundVerifier`'s `failure`
//!   (`Sumcheck/Rounds.lean:123`), and the chain rejects with it.
//! * **the honest side's shapes**: `chain_open` produces the four messages at
//!   the lengths the verifier reads, with the round messages at the two degree
//!   bounds the specification types (`roundDegZero b = 2b`,
//!   `roundDegAlpha = 2`).
//!
//! The asymmetry is deliberate and worth stating: a verifier that rejects
//! everything passes every rejection test, so those tests alone prove nothing
//! about soundness -- they prove the *checks are wired*. Acceptance is what
//! proves they are not over-strict, and that is the owed half.
//!
//! # These are `#[ignore]`d, and why
//!
//! Row 2's `paper_rel_out` used to lock the shape; it is no longer on the
//! verifier's path, but row 3's `rlin_stmt` still materializes the
//! `rlinRows × rlinCols` matrix, 2.2 GiB at the pinned parameters, and
//! `alpha_public_table` reads it. So each test below costs one such matrix
//! (two for the honest-side test, sequentially), and the cube is the only
//! dimension that is reduced. Run with `cargo test --release -- --ignored`.

#![allow(clippy::cast_possible_truncation)]

mod support;

use cpoly::Ext4;
use hachi::chain::{chain_open, chain_verify};
use hachi::linalg::{PolyMatrix, PolyVec};
use hachi::params::CHAIN_GAMMA;
use hachi::quadeval::{PolyEvalStatement, PublicParamsD};
use hachi::ringswitch::{LiftedWitness, QuotientRow};
use hachi::sumcheck::RoundMsg;
use support::Lcg;

fn ext4(r: &mut Lcg) -> Ext4 {
    Ext4::new(r.next_fp(), r.next_fp(), r.next_fp(), r.next_fp())
}

/// The shape. **Only `m₀` and `m₁` are reduced.**
///
/// The `R^lin` adapter takes its dimensions as arguments, but
/// `to_quad_eval_statement` turns the two point halves into monomial bases of
/// `2^ML_VARS_LOW` and `2^ML_VARS_HIGH`, and `rlin_stmt`'s blocks are sized
/// off `pp`; keeping the real widths keeps every row at its real shape. The
/// cube stays small because it can: `w_table` reads `z[idx / d]`, so a
/// four-variable cube touches only the first row of `z` however long `z` is.
struct Shape {
    blocks: usize,
    message_rows: usize,
    message_digits: usize,
    inner_rows: usize,
    inner_digits: usize,
    z_digits: usize,
    m0: usize,
    m1: usize,
}

const TOY: Shape = Shape {
    blocks: hachi::params::BLOCKS,
    message_rows: hachi::params::MESSAGE_ROWS,
    message_digits: hachi::params::GADGET_DIGITS,
    inner_rows: hachi::params::INNER_ROWS,
    inner_digits: hachi::params::GADGET_DIGITS,
    z_digits: hachi::params::Z_DIGITS,
    m0: 4,
    m1: 1,
};

const XL_VARS: usize = hachi::params::ML_VARS_LOW;
const XH_VARS: usize = hachi::params::ML_VARS_HIGH;

/// The public data and the challenge stream: everything both parties hold.
struct Common {
    pp: PublicParamsD,
    d_key: PolyMatrix,
    poly_stmt: PolyEvalStatement,
    c: PolyVec,
    w: LiftedWitness,
    alpha: Ext4,
    tau0: Vec<Ext4>,
    tau1: Vec<Ext4>,
    challenges: Vec<Ext4>,
}

fn common(seed: u64) -> Common {
    let s = &TOY;
    let mut r = Lcg::new(seed);
    let cw = s.blocks * s.message_digits;
    let ct = s.blocks * (s.inner_rows * s.inner_digits);

    let pp = PublicParamsD::new(
        hachi::commit::PublicParams::new(
            r.next_poly_matrix(s.inner_rows, s.message_rows * s.message_digits),
            r.next_poly_matrix(1, ct),
        ),
        r.next_poly_matrix(1, cw),
    );
    let poly_stmt = PolyEvalStatement::new(
        r.next_poly_vec(1),
        r.next_poly_vec(XL_VARS),
        r.next_poly_vec(XH_VARS),
        r.next_rq(),
    );
    // A lifted witness whose `z` covers the toy cube; not a solution of the
    // `R^lin` system (see the header), so an honest run over it rejects.
    let w = LiftedWitness::new(
        r.next_poly_vec(2),
        (0..1).map(|_| QuotientRow::new(&Vec::new())).collect(),
    );
    Common {
        pp,
        d_key: r.next_poly_matrix(1, 2),
        poly_stmt,
        c: r.next_poly_vec(s.blocks),
        w,
        alpha: ext4(&mut r),
        tau0: (0..s.m0).map(|_| ext4(&mut r)).collect(),
        tau1: (0..s.m1).map(|_| ext4(&mut r)).collect(),
        challenges: (0..s.m0).map(|_| ext4(&mut r)).collect(),
    }
}

/// The prover's messages, in wire order.
struct Transcript {
    v: PolyVec,
    t: PolyVec,
    msgs: Vec<RoundMsg>,
    y_prime: Ext4,
}

/// A transcript of the right lengths whose round messages are random
/// polynomials at the two degree bounds: not honest, so the first round
/// rejects.
fn random_transcript(seed: u64, m0: usize) -> Transcript {
    let mut r = Lcg::new(seed);
    let poly = |r: &mut Lcg, deg: usize| {
        cpoly::UnivariatePoly::from_coeffs((0..=deg).map(|_| ext4(r)).collect())
    };
    Transcript {
        v: r.next_poly_vec(1),
        t: r.next_poly_vec(1),
        msgs: (0..m0)
            .map(|_| {
                let g0 = poly(&mut r, 2 * hachi::params::GADGET_BASE as usize);
                let ga = poly(&mut r, 2);
                RoundMsg::new(g0, ga)
            })
            .collect(),
        y_prime: ext4(&mut r),
    }
}

fn run(cm: &Common, tr: &Transcript) -> bool {
    let s = &TOY;
    chain_verify(
        &cm.pp,
        &cm.d_key,
        &cm.poly_stmt,
        &tr.v,
        &cm.c,
        &tr.t,
        cm.alpha,
        &cm.tau0,
        &cm.tau1,
        &tr.msgs,
        &cm.challenges,
        tr.y_prime,
        &cm.w,
        CHAIN_GAMMA,
        s.blocks,
        s.message_rows,
        s.message_digits,
        s.inner_rows,
        s.inner_digits,
        s.z_digits,
    )
}

fn open(cm: &Common, message: &Vec<PolyVec>) -> Transcript {
    let s = &TOY;
    let (v, t, msgs, y_prime) = chain_open(
        &cm.pp,
        &cm.d_key,
        &cm.poly_stmt,
        message,
        &cm.c,
        &cm.w,
        cm.alpha,
        &cm.tau0,
        &cm.tau1,
        &cm.challenges,
        CHAIN_GAMMA,
        s.blocks,
        s.message_rows,
        s.message_digits,
        s.inner_rows,
        s.inner_digits,
        s.z_digits,
    );
    Transcript { v, t, msgs, y_prime }
}

/// **The plumbing test, and the round loop's rejection in one.** Rows 1–8
/// thread through each other at the toy cube without panicking, and a
/// transcript whose messages do not sum to the targets is rejected -- random
/// polynomials essentially never satisfy `g(0) + g(1) = target`, so the first
/// round fails and the chain must be `false`.
#[test]
#[ignore = "materializes the 2.2 GiB R^lin matrix -- run with cargo test --release -- --ignored"]
fn a_transcript_whose_rounds_do_not_sum_is_rejected() {
    let cm = common(0xC0A1_0000);
    let tr = random_transcript(0xC0A1_0001, TOY.m0);
    assert!(!run(&cm, &tr), "a chain whose first round rejects must not verify");
}

/// `chain_open` produces the four messages at the shapes the verifier reads:
/// `v` with `dRows` entries, `t` with the lift key's rows, one message pair
/// per round at the specification's two degree bounds, and `y′` equal to the
/// witness table's multilinear extension at the challenge point.
#[test]
#[ignore = "materializes the 2.2 GiB R^lin matrix -- run with cargo test --release -- --ignored"]
fn chain_open_produces_the_messages_the_verifier_reads() {
    let s = &TOY;
    let cm = common(0xC0A1_0030);
    let mut r = Lcg::new(0xC0A1_0031);
    let message: Vec<PolyVec> = (0..s.blocks)
        .map(|_| r.next_poly_vec(s.message_rows * s.message_digits))
        .collect();

    let tr = open(&cm, &message);

    assert_eq!(tr.v.len(), 1, "the carrier commitment has dRows entries");
    assert_eq!(tr.t.len(), 1, "the lift commitment has the key's rows");
    assert_eq!(tr.msgs.len(), s.m0, "one message pair per round");
    let two_b = 2 * hachi::params::GADGET_BASE as usize;
    for (i, g) in tr.msgs.iter().enumerate() {
        assert!(
            g.g_zero().degree().is_none_or(|d| d <= two_b),
            "round {i}: the range message has degree at most 2b"
        );
        assert!(
            g.g_alpha().degree().is_none_or(|d| d <= 2),
            "round {i}: the linear message has degree at most 2"
        );
    }
    assert_eq!(
        tr.y_prime,
        hachi::zerocheck::w_table_mle_eval(&cm.w, s.m0, &cm.challenges),
        "y' is the table's multilinear extension at the challenge point"
    );
}

/// The honest side's messages are internally consistent -- each round's
/// message sums over `{0, 1}` to the previous round's evaluation -- even when
/// the witness is not a solution. Only the *first* target can then disagree,
/// so a chain over an honest-but-unsatisfying witness is rejected at round 1
/// and not later. That pins the rejection to the relation, not to the
/// threading.
#[test]
#[ignore = "materializes the 2.2 GiB R^lin matrix twice -- run with cargo test --release -- --ignored"]
fn an_honest_run_over_a_non_solution_is_rejected_at_the_first_round_only() {
    let s = &TOY;
    let cm = common(0xC0A1_0040);
    let mut r = Lcg::new(0xC0A1_0041);
    let message: Vec<PolyVec> = (0..s.blocks)
        .map(|_| r.next_poly_vec(s.message_rows * s.message_digits))
        .collect();
    let tr = open(&cm, &message);

    // rounds 2.. are consistent with round 1's evaluation at the challenge.
    for i in 1..s.m0 {
        let prev = &tr.msgs[i - 1];
        let g = &tr.msgs[i];
        let a = cm.challenges[i - 1];
        assert_eq!(
            g.g_zero().eval(Ext4::ZERO) + g.g_zero().eval(Ext4::ONE),
            prev.g_zero().eval(a),
            "round {i}: the range message sums to the previous evaluation"
        );
        assert_eq!(
            g.g_alpha().eval(Ext4::ZERO) + g.g_alpha().eval(Ext4::ONE),
            prev.g_alpha().eval(a),
            "round {i}: the linear message sums to the previous evaluation"
        );
    }
    // and the whole chain rejects, because the witness does not solve the
    // system the initial targets are computed from.
    assert!(!run(&cm, &tr), "an honest run over a non-solution must not verify");
}
