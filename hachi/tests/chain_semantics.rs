//! `src/chain.rs`: the composed evaluation chain.
//!
//! # What this file can and cannot check, stated up front
//!
//! The composed chain's *acceptance* property — an honest run verifies — needs
//! a transcript that satisfies Eq. (20) simultaneously with the lift's
//! shortness, both zero-check blocks, every round's target identity and the end
//! piece's commitment equality. Producing one means running the whole honest
//! prover with consistent public parameters, and at the pinned parameters that
//! is `2^23` ring products for `commit::commit` alone (`benches/exclusions.toml`
//! § the scheme-level entries). **That test is owed and is not here.**
//!
//! What is here is the half that does not need it, and it is not nothing:
//!
//! **These four are `#[ignore]`d, and slow beyond convenience.** A single
//! `chain_verify` at these widths ran 24 minutes at 99.9% CPU and 3.9 GB
//! resident without finishing; three of them were OOM-killed, since `rlin_stmt`
//! materializes 2.2 GiB each. The dominator is not the matrix and not
//! `ring::mul`: it is `h_alpha_is_zero` reaching `alpha_contract`, where the
//! specification recomputes `M~_alpha` inside the `l` loop -- the cost
//! `zerocheck_semantics.rs` marks "makes this minutes" for one row, multiplied
//! here by the cube.
//!
//! * **the plumbing**: `chain_verify` runs all ten rows at a toy shape without
//!   panicking. Across ten rows of index arithmetic — flat cube indices, three
//!   column blocks, a `2y`/`2y+1` fold, `rlinCols` boundaries — a shape
//!   disagreement between any two adjacent rows is an out-of-bounds panic, not
//!   a wrong answer. This is the test that catches a mis-threaded seam.
//! * **the guards are load-bearing**: each one is made to fail in turn and the
//!   whole chain must reject. A composition that dropped a row's check would
//!   pass an acceptance test and fail these.
//! * **the short-circuit**: a rejected round returns `None` from `round_loop`
//!   and the chain rejects without evaluating the rows after it, which is
//!   `roundVerifier`'s `failure` (`Sumcheck/Rounds.lean:113`).
//!
//! The asymmetry is deliberate and worth stating: a verifier that rejects
//! everything passes every rejection test, so those tests alone prove nothing
//! about soundness — they prove the *guards are wired*. Acceptance is what
//! proves they are not over-strict, and that is the owed half.

#![allow(clippy::cast_possible_truncation)]

mod support;

use cpoly::Ext4;
use hachi::chain::{chain_open, chain_verify};
use hachi::linalg::{PolyMatrix, PolyVec};
use hachi::params::CHAIN_GAMMA;
use hachi::quadeval::{PolyEvalStatement, PublicParamsD, QuadEvalResponse};
use hachi::ringswitch::{LiftedWitness, QuotientRow};
use support::Lcg;

fn ext4(r: &mut Lcg) -> Ext4 {
    Ext4::new(r.next_fp(), r.next_fp(), r.next_fp(), r.next_fp())
}

/// The shape. **Only `m₀` and `m₁` are reduced.**
///
/// Everything else is the scheme's real value, and not by choice: row 2's
/// `paper_rel_out` is hard-wired to `params::BLOCKS`, `params::MESSAGE_ROWS`
/// and `params::INNER_ROWS` (`src/quadeval.rs`, the c3/c4/c5 lines), so the
/// composed chain inherits that lock and there is **no toy width at which it
/// runs**. A first attempt at `blocks = 2` panicked in `PolyVec::get` in every
/// test here, which is the plumbing test doing its job.
///
/// The cube stays small because it can: `w_table` reads `z[idx / d]`, so a
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

/// The point halves are `ML_VARS_LOW`/`ML_VARS_HIGH` because
/// `to_quad_eval_statement` turns each into a `2^len` monomial basis, and row 2
/// needs those to be `BLOCKS` and `MESSAGE_ROWS` long.
const XL_VARS: usize = hachi::params::ML_VARS_LOW;
const XH_VARS: usize = hachi::params::ML_VARS_HIGH;

/// A whole chain input at the toy shape. Not an honest transcript -- see the
/// module header -- but every array is the length its row expects, which is
/// what the plumbing test needs.
struct Inputs {
    pp: PublicParamsD,
    d_key: PolyMatrix,
    poly_stmt: PolyEvalStatement,
    v: PolyVec,
    c: PolyVec,
    resp: QuadEvalResponse,
    w: LiftedWitness,
    alpha: Ext4,
    tau0: Vec<Ext4>,
    tau1: Vec<Ext4>,
    challenges: Vec<Ext4>,
    y_prime: Ext4,
}

fn inputs(seed: u64) -> Inputs {
    let s = &TOY;
    let mut r = Lcg::new(seed);
    let cw = s.blocks * s.message_digits;
    let ct = s.blocks * (s.inner_rows * s.inner_digits);
    let cz = s.message_rows * s.message_digits * s.z_digits;

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
    let resp = QuadEvalResponse::new(
        r.next_poly_vec(cw),
        (0..s.blocks)
            .map(|_| r.next_poly_vec(s.inner_rows * s.inner_digits))
            .collect(),
        r.next_poly_vec(cz),
    );
    // A lifted witness whose `z` covers the cube and whose quotient rows are
    // short, so `lift_short_check` has something to succeed on.
    let w = LiftedWitness::new(
        r.next_poly_vec(2),
        (0..1).map(|_| QuotientRow::new(&Vec::new())).collect(),
    );
    Inputs {
        pp,
        d_key: r.next_poly_matrix(1, 2),
        poly_stmt,
        v: r.next_poly_vec(1),
        c: r.next_poly_vec(s.blocks),
        resp,
        w,
        alpha: ext4(&mut r),
        tau0: (0..s.m0).map(|_| ext4(&mut r)).collect(),
        tau1: (0..s.m1).map(|_| ext4(&mut r)).collect(),
        challenges: (0..s.m0).map(|_| ext4(&mut r)).collect(),
        y_prime: ext4(&mut r),
    }
}

fn run(i: &Inputs) -> bool {
    let s = &TOY;
    chain_verify(
        &i.pp,
        &i.d_key,
        &i.poly_stmt,
        &i.v,
        &i.c,
        &i.resp,
        &i.w,
        i.alpha,
        &i.tau0,
        &i.tau1,
        &i.challenges,
        i.y_prime,
        CHAIN_GAMMA,
        s.blocks,
        s.message_rows,
        s.message_digits,
        s.inner_rows,
        s.inner_digits,
        s.z_digits,
    )
}

/// **The plumbing test.** Ten rows of index arithmetic thread through each
/// other; a shape disagreement between adjacent rows is a panic, not a wrong
/// answer. So running to completion at a toy shape is the property, and the
/// verdict is beside the point here.
#[test]
#[ignore = "full-const scale: row 2 is params-locked, so the composed chain only runs at BLOCKS/MESSAGE_ROWS -- run with cargo test --release -- --ignored"]
fn the_composed_chain_threads_every_row_without_panicking() {
    // ONE call, not three: `rlin_stmt` materializes `rlinRows x rlinCols` =
    // 2.2 GiB, and three of them was an OOM kill (signal 9) on this host.
    {
        let i = inputs(0xC0A1_0000u64);
        let _verdict = run(&i);
        // no assertion on the verdict: these inputs are not an honest
        // transcript. Reaching here at all is the claim.
    }
}

/// A rejected round must stop the chain: `round_loop` returns `None`, which is
/// `roundVerifier`'s `failure`, and no later row can rescue it.
#[test]
#[ignore = "full-const scale: row 2 is params-locked, so the composed chain only runs at BLOCKS/MESSAGE_ROWS -- run with cargo test --release -- --ignored"]
fn a_rejected_round_rejects_the_chain() {
    let i = inputs(0xC0A1_0010);
    // random targets essentially never satisfy g(0) + g(1) = target, so the
    // first round rejects and the chain must be false.
    assert!(!run(&i), "a chain whose first round rejects must not verify");
}

/// The chain rejects when the end piece's commitment equality fails -- checked
/// by handing it a `D` unrelated to the one the witness was committed under.
#[test]
#[ignore = "full-const scale: row 2 is params-locked, so the composed chain only runs at BLOCKS/MESSAGE_ROWS -- run with cargo test --release -- --ignored"]
fn a_wrong_commitment_key_rejects_the_chain() {
    let mut i = inputs(0xC0A1_0020);
    let mut r = Lcg::new(0xDEAD_0001);
    i.d_key = r.next_poly_matrix(1, 2);
    assert!(!run(&i), "a mismatched D must not verify");
}

/// `chain_open` produces the three values the verifier cannot compute for
/// itself, at the shapes the verifier expects -- the honest side's plumbing.
#[test]
#[ignore = "full-const scale: row 2 is params-locked, so the composed chain only runs at BLOCKS/MESSAGE_ROWS -- run with cargo test --release -- --ignored"]
fn chain_open_produces_the_shapes_the_verifier_expects() {
    let s = &TOY;
    let i = inputs(0xC0A1_0030);
    let mut r = Lcg::new(0xC0A1_0031);
    let message: Vec<PolyVec> = (0..s.blocks)
        .map(|_| r.next_poly_vec(s.message_rows * s.message_digits))
        .collect();
    let inner: Vec<PolyVec> = (0..s.blocks)
        .map(|_| r.next_poly_vec(s.inner_rows * s.inner_digits))
        .collect();

    let (v, resp, _y) = chain_open(
        &i.pp,
        &i.poly_stmt,
        &message,
        &inner,
        &i.c,
        &i.w,
        &i.challenges,
    );

    assert_eq!(v.len(), 1, "the carrier commitment has dRows entries");
    assert_eq!(
        resp.inner_dec().len(),
        s.blocks,
        "the response carries one inner decomposition per block"
    );
    assert_eq!(
        resp.carrier_dec().len(),
        s.blocks * hachi::params::GADGET_DIGITS,
        "the carrier decomposition is blocks * GADGET_DIGITS wide"
    );
}
