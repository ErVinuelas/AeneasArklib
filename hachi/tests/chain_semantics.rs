//! `src/chain.rs`: the composed evaluation chain.
//!
//! # What this file can and cannot check, stated up front
//!
//! The composed chain's *acceptance* property -- an honest run verifies --
//! needs an honest transcript: a witness `w = (z, ρ)` that actually solves the
//! `R^lin` system the rows 1–3 assemble, so that the sumcheck's initial
//! targets (`0` and `zcTargetAlpha`) are the true hypercube sums and every
//! `roundCheck` passes. Producing one means the honest lift prover
//! (`honestLiftWitnessC`, the quotient rows by synthetic division) -- which
//! **is** translated here as of 2026-09-11
//! (`ringswitch::honest_lift_witness`; `chain_open` still takes `w` as an
//! input rather than calling it, see `src/chain.rs` § `chain_open`) -- and it
//! means a cube that covers the whole table -- `hcov : (μ + n·δ)·d ≤ 2^m₀`,
//! i.e. `m₀ = 26` -- because a reduced cube truncates the sums the targets
//! are computed from. **That test is now here**:
//! [`the_honest_chain_verifies`], written 2026-09-11 once the honest lift
//! prover landed (`ringswitch::honest_lift_witness`). It runs at **one block**
//! and otherwise the pin -- `message_rows = 1024`, the real digit counts, and
//! `m₀ = M_ZERO = 26`, which is the least cube that covers the lifted witness
//! even at one block, since `cz = 1024 · 8 · 5 = 40 960` columns come from the
//! message rows alone. One block is not a reduction the honest side can avoid:
//! `honest_z` and the relation checks size their widths from `params`, so the
//! message rows cannot shrink, and at the pin's 1024 blocks the message alone
//! is `1024 · 8192` ring elements = **64 GiB**. (That, not the `R^lin` matrix,
//! is what killed the three toy-cube tests below on a 30 GiB machine on
//! 2026-09-11: the OOM hit at 14.8 GiB resident while the message was still
//! being drawn.) The test costs hours -- two naive `alpha_public_table`s of
//! `2^26` entries, one on each side -- and is `#[ignore]`d with that reason.
//!
//! What is here besides it is the half that does not need an honest witness:
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
use hachi::ring::Rq;
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

// --- the acceptance test ----------------------------------------------------

/// A short challenge: one ring element with coefficients in `{-1, 0, 1}`. The
/// wire's `c` is drawn from a short set so that `z = Σ cⱼ ŝⱼ` stays inside the
/// bounded decomposition's range (`Z_BOUND`); a full random `Rq` would put `z`
/// far outside it and the honest run would rightly reject.
fn ternary_rq(r: &mut Lcg) -> Rq {
    let q = hachi::params::Q;
    let mut coeffs: Vec<cpoly::Fp> = Vec::new();
    for _ in 0..hachi::params::RING_DEGREE {
        let t = r.next_u64() % 3;
        coeffs.push(cpoly::Fp::new(if t == 2 { q - 1 } else { t }));
    }
    Rq::from_coeffs(&coeffs)
}

/// The claimed value, computed the direct way: coefficient `i + 2^nl · j` of the
/// committed polynomial is entry `j` of block `i` (`quadeval_semantics.rs`'s
/// `the_bridge_bases_reproduce_the_polynomial_evaluation`: rows indexed by the
/// low half), so `f(xl ++ xh) = Σᵢ Σⱼ Mᵢⱼ · Π_{b ∈ bits(i)} xl[b] · Π_{b ∈ bits(j)} xh[b]`,
/// with the bit order of that file's `eval_direct`. Written out here rather than
/// taken from `to_quad_eval_statement`'s bases, so the bridge is under test too.
/// At one block the `xl` product is empty and this is the original single-block
/// evaluation.
fn dense_eval(blocks: &[PolyVec], xl: &PolyVec, xh: &PolyVec) -> Rq {
    let mut acc = Rq::zero();
    for (i, f) in blocks.iter().enumerate() {
        let mut block = Rq::zero();
        for j in 0..f.len() {
            let mut term = f.get(j).copy();
            for b in 0..xh.len() {
                if (j >> b) & 1 == 1 {
                    term = term.mul(xh.get(b));
                }
            }
            block = block.add(&term);
        }
        for b in 0..xl.len() {
            if (i >> b) & 1 == 1 {
                block = block.mul(xl.get(b));
            }
        }
        acc = acc.add(&block);
    }
    acc
}

/// The number of message blocks the pin-shaped runs use: `HACHI_CHAIN_BLOCKS`
/// if set (a reduced-blocks end-to-end, `PLAN_STAGE6.md` § "The fourth wall"),
/// else one block, the shape the acceptance test was written at.
fn chain_blocks_from_env() -> usize {
    match std::env::var("HACHI_CHAIN_BLOCKS") {
        Ok(v) => v.parse::<usize>().expect("HACHI_CHAIN_BLOCKS must be a positive integer"),
        Err(_) => 1,
    }
}

/// Everything the honest chain needs at the pin, built from the message up:
/// the instance the acceptance test and the profile share.
struct PinInstance {
    pp: PublicParamsD,
    d_key: PolyMatrix,
    poly_stmt: PolyEvalStatement,
    message: Vec<PolyVec>,
    c: PolyVec,
    w: LiftedWitness,
    v: PolyVec,
    alpha: Ext4,
    tau0: Vec<Ext4>,
    tau1: Vec<Ext4>,
    challenges: Vec<Ext4>,
}

/// Build the pin-shaped honest instance at `blocks` message blocks; asserts the
/// two intermediate facts (`M ζ = y`, cube coverage) and prints stage times.
#[allow(clippy::too_many_lines)]
fn pin_instance(blocks: usize, t0: &std::time::Instant) -> PinInstance {
    let mut r = Lcg::new(0xC0A1_0050);
    let message_rows = hachi::params::MESSAGE_ROWS;
    let message_digits = hachi::params::GADGET_DIGITS;
    let inner_rows = hachi::params::INNER_ROWS;
    let inner_digits = hachi::params::GADGET_DIGITS;
    let z_digits = hachi::params::Z_DIGITS;
    let m0 = hachi::params::M_ZERO;
    let m1 = hachi::params::M_ONE;
    let cw = blocks * message_digits;
    let ct = blocks * inner_rows * inner_digits;

    // public parameters, drawn
    let inner = hachi::commit::PublicParams::new(
        r.next_poly_matrix(inner_rows, message_rows * message_digits),
        r.next_poly_matrix(1, ct),
    );
    let d_matrix = r.next_poly_matrix(1, cw);

    // the message: `blocks` blocks of `message_rows` coefficients, committed
    let raw: Vec<PolyVec> = (0..blocks).map(|_| r.next_poly_vec(message_rows)).collect();
    let (u, decomp) = hachi::commit::commit(&inner, &raw);
    let message: Vec<PolyVec> = (0..blocks).map(|i| decomp.message(i).copy()).collect();
    let inner_decomp: Vec<PolyVec> = decomp.inner_decomps().iter().map(PolyVec::copy).collect();
    let pp = PublicParamsD::new(inner, d_matrix);
    eprintln!("[{:>9.1?}] committed {blocks} block(s)", t0.elapsed());

    // the claim: a true evaluation at a drawn point
    let xl = r.next_poly_vec(XL_VARS);
    let xh = r.next_poly_vec(XH_VARS);
    let y = dense_eval(&raw, &xl, &xh);
    let poly_stmt = PolyEvalStatement::new(u, xl, xh, y);
    let stmt = hachi::quadeval::to_quad_eval_statement(&poly_stmt);
    eprintln!("[{:>9.1?}] statement built", t0.elapsed());

    // the wire's challenges: one short ring element per block (`honest_z`
    // folds block `i` against `c.get(i)`; the 64-block run of 2026-09-15 found
    // this vector sized for one block)
    let c = PolyVec::new((0..blocks).map(|_| ternary_rq(&mut r)).collect());
    let alpha = ext4(&mut r);
    let tau0: Vec<Ext4> = (0..m0).map(|_| ext4(&mut r)).collect();
    let tau1: Vec<Ext4> = (0..m1).map(|_| ext4(&mut r)).collect();
    let challenges: Vec<Ext4> = (0..m0).map(|_| ext4(&mut r)).collect();

    // the honest QuadEval side: `v`, the response, its stacking
    let v = hachi::quadeval::honest_compute_v(&pp, &stmt, &message);
    eprintln!("[{:>9.1?}] honest_compute_v done", t0.elapsed());
    let resp = hachi::quadeval::honest_compute_resp(&stmt, &message, &inner_decomp, &c);
    let zeta = hachi::quadeval::stack(&resp);
    eprintln!("[{:>9.1?}] honest_compute_resp + stack done", t0.elapsed());
    let rlin = hachi::quadeval::rlin_stmt(
        &pp,
        &stmt,
        &v,
        &c,
        CHAIN_GAMMA,
        blocks,
        message_rows,
        message_digits,
        inner_rows,
        inner_digits,
        z_digits,
    );
    assert_eq!(zeta.len(), rlin.m().cols(), "the stacked witness has rlinCols entries");
    eprintln!(
        "[{:>9.1?}] R^lin statement assembled: {} x {}",
        t0.elapsed(),
        rlin.m().rows(),
        rlin.m().cols()
    );

    // relOut ⇒ rlin: the stacked honest response solves the assembled system
    assert!(
        rlin.m().mat_vec_mul(&zeta).equals(rlin.yvec()),
        "the honest stacked response must solve the assembled R^lin system"
    );
    eprintln!("[{:>9.1?}] M zeta = y holds", t0.elapsed());

    // the honest lift: `w = (zeta, rho)` by synthetic division
    let w = hachi::ringswitch::honest_lift_witness(&rlin, &zeta);
    assert_eq!(w.z().len(), zeta.len());
    assert_eq!(w.rho().len(), rlin.m().rows());
    let lift_cols = w.z().len() + w.rho().len() * hachi::params::GADGET_DIGITS;
    assert!(
        lift_cols * hachi::params::RING_DEGREE <= 1 << m0,
        "the cube must cover the lifted witness (hcov)"
    );
    let d_key = r.next_poly_matrix(1, lift_cols);
    eprintln!("[{:>9.1?}] lifted witness built, lift width {lift_cols}", t0.elapsed());

    PinInstance { pp, d_key, poly_stmt, message, c, w, v, alpha, tau0, tau1, challenges }
}


/// **The honest chain verifies.** An evaluation claim that is true, opened by
/// the honest prover over the honest lifted witness, is accepted by the
/// composed verifier -- every round check, the final check and the end piece.
///
/// The instance is built from the message up, each public value derived the
/// way its definition says, none of them drawn at random: the message block
/// `ŝ₀` and its inner decomposition `t̂₀` from `commit::commit`, the outer
/// commitment `u` with them, the claim `y` by direct evaluation, the carrier
/// commitment `v` by `honest_compute_v`, the QuadEval response and its stacking
/// `ζ` by `honest_compute_resp` and `stack`, and the lifted witness
/// `w = (ζ, ρ)` by `honest_lift_witness` against the `R^lin` statement the
/// verifier itself assembles. What *is* random is everything the wire draws:
/// the matrices `A, B, D`, the lift key, the point, the short challenge `c`,
/// `α`, `τ₀`, `τ₁` and the round challenges.
///
/// Two intermediate assertions pin where a failure would be: that `ζ` solves
/// the assembled `R^lin` system (`M ζ = y` in `R_q`, ArkLib's `relOut ⇒ rlin`
/// completeness step, which upstream carries `sorryAx`-tainted), and that the
/// prover's `v` is the one the verifier is handed.
///
/// Cost at this shape, estimated from the measured parts: `honest_lift_witness`
/// is `5 · 40 976` unreduced products (~4 min), the two `alpha_public_table`s
/// at `2^26` (~2 h each), 26 rounds of `honest_compute_g` over the folded
/// tables (~45 min), two `lift_commit`s of `41 016` products (~1 min each).
/// Peak memory is a few `2^26`-entry `Ext4` tables (2 GiB each) plus the
/// 1.6 GiB matrix.
#[test]
#[ignore = "hours: two naive 2^26 alpha_public_tables -- run with cargo test --release -- --ignored --nocapture"]
#[allow(clippy::too_many_lines)]
fn the_honest_chain_verifies() {
    use std::time::Instant;
    let t0 = Instant::now();
    let blocks = chain_blocks_from_env();
    let message_rows = hachi::params::MESSAGE_ROWS;
    let message_digits = hachi::params::GADGET_DIGITS;
    let inner_rows = hachi::params::INNER_ROWS;
    let inner_digits = hachi::params::GADGET_DIGITS;
    let z_digits = hachi::params::Z_DIGITS;
    let m0 = hachi::params::M_ZERO;
    let inst = pin_instance(blocks, &t0);

    // the honest prover
    let (v_open, t, msgs, y_prime) = chain_open(
        &inst.pp,
        &inst.d_key,
        &inst.poly_stmt,
        &inst.message,
        &inst.c,
        &inst.w,
        inst.alpha,
        &inst.tau0,
        &inst.tau1,
        &inst.challenges,
        CHAIN_GAMMA,
        blocks,
        message_rows,
        message_digits,
        inner_rows,
        inner_digits,
        z_digits,
    );
    assert!(v_open.equals(&inst.v), "the prover's v is the one the verifier is handed");
    assert_eq!(msgs.len(), m0);
    eprintln!("[{:>9.1?}] chain_open done", t0.elapsed());

    // the composed verifier accepts
    let ok = chain_verify(
        &inst.pp,
        &inst.d_key,
        &inst.poly_stmt,
        &v_open,
        &inst.c,
        &t,
        inst.alpha,
        &inst.tau0,
        &inst.tau1,
        &msgs,
        &inst.challenges,
        y_prime,
        &inst.w,
        CHAIN_GAMMA,
        blocks,
        message_rows,
        message_digits,
        inner_rows,
        inner_digits,
        z_digits,
    );
    eprintln!("[{:>9.1?}] chain_verify = {ok}", t0.elapsed());
    assert!(ok, "the honest chain must verify");
}

/// **Where the honest prover's minutes go.** The same instance as
/// [`the_honest_chain_verifies`], with `chain_open`'s composition replayed piece
/// by piece and each piece timed: the lift commitment, the `2^m₀` witness table,
/// the `2^m₀` public α table, the 26 rounds, the final claim; then the verifier
/// whole. It asserts nothing the acceptance test does not (the pieces are
/// exactly `chain_open`'s calls, in its order) and exists to tell I4
/// (`lift_commit`'s ring products) from I5 (the rounds' range factor) by
/// measurement rather than by estimate -- run it with
/// `cargo test --release -- --ignored --nocapture the_honest_chain_profile`.
#[test]
#[ignore = "tens of minutes at the pin: the honest prover replayed piece by piece for timing"]
#[allow(clippy::too_many_lines)]
fn the_honest_chain_profile() {
    use std::time::Instant;
    let t0 = Instant::now();
    let blocks = chain_blocks_from_env();
    let message_rows = hachi::params::MESSAGE_ROWS;
    let message_digits = hachi::params::GADGET_DIGITS;
    let inner_rows = hachi::params::INNER_ROWS;
    let inner_digits = hachi::params::GADGET_DIGITS;
    let z_digits = hachi::params::Z_DIGITS;
    let m0 = hachi::params::M_ZERO;
    let inst = pin_instance(blocks, &t0);
    let stmt = hachi::quadeval::to_quad_eval_statement(&inst.poly_stmt);

    let t1 = Instant::now();
    let rlin = hachi::quadeval::rlin_stmt(
        &inst.pp, &stmt, &inst.v, &inst.c, CHAIN_GAMMA, blocks, message_rows, message_digits,
        inner_rows, inner_digits, z_digits,
    );
    eprintln!("[profile] rlin_stmt (verifier assembles it too): {:.1?}", t1.elapsed());

    let t2 = Instant::now();
    let t_com: PolyVec = hachi::ringswitch::lift_commit(&inst.d_key, &inst.w);
    eprintln!("[profile] lift_commit: {:.1?}", t2.elapsed());

    let t3 = Instant::now();
    let w_tab = hachi::zerocheck::c_w_table_mle(&inst.w, m0);
    eprintln!("[profile] c_w_table_mle at 2^{m0}: {:.1?} ({} entries)", t3.elapsed(), w_tab.len());
    drop(w_tab);

    let t4 = Instant::now();
    let a_tab = hachi::sumcheck::alpha_public_table(&rlin, inst.alpha, &inst.tau1, m0);
    eprintln!("[profile] alpha_public_table at 2^{m0}: {:.1?} ({} entries)", t4.elapsed(), a_tab.len());
    drop(a_tab);

    let zc = hachi::sumcheck::NestedZeroCheckStmt::new(
        rlin,
        t_com.copy(),
        inst.alpha,
        inst.tau0.clone(),
        inst.tau1.clone(),
    );
    let opened = hachi::sumcheck::nested_to_round_statement(zc);
    let t5 = Instant::now();
    let msgs = hachi::sumcheck::honest_round_messages(opened, &inst.w, &inst.challenges);
    eprintln!(
        "[profile] honest_round_messages ({} rounds, incl. its own two tables): {:.1?}",
        msgs.len(),
        t5.elapsed()
    );

    let t6 = Instant::now();
    let y_prime = hachi::sumcheck::honest_compute_y(&inst.w, m0, &inst.challenges);
    eprintln!("[profile] honest_compute_y: {:.1?}", t6.elapsed());

    // the verifier, replayed piece by piece in `chain_verify`'s order: the
    // `R^lin` assembly, the 26 round checks, the final check (which rebuilds the
    // α table and evaluates it), the end piece (which recomputes `lift_commit`
    // and the witness evaluation); then `chain_verify` whole as the control.
    let t7 = Instant::now();
    let rlin_v = hachi::quadeval::rlin_stmt(
        &inst.pp, &stmt, &inst.v, &inst.c, CHAIN_GAMMA, blocks, message_rows, message_digits,
        inner_rows, inner_digits, z_digits,
    );
    let zc_v = hachi::sumcheck::NestedZeroCheckStmt::new(
        rlin_v, t_com.copy(), inst.alpha, inst.tau0.clone(), inst.tau1.clone(),
    );
    let opened_v = hachi::sumcheck::nested_to_round_statement(zc_v);
    eprintln!("[profile] verifier: rlin_stmt + statement thread: {:.1?}", t7.elapsed());
    let t8 = Instant::now();
    let after = hachi::sumcheck::round_verify_loop(opened_v, &msgs, &inst.challenges);
    eprintln!("[profile] verifier: round_verify_loop ({} rounds): {:.1?}", msgs.len(), t8.elapsed());
    let final_stmt = after.expect("the honest rounds must all check");
    let t9 = Instant::now();
    let c_final = hachi::sumcheck::final_check(&final_stmt, y_prime, CHAIN_GAMMA);
    eprintln!("[profile] verifier: final_check = {c_final}: {:.1?}", t9.elapsed());
    let t10 = Instant::now();
    let weval = hachi::endpiece::WEvalStatement::new(t_com.copy(), inst.challenges.clone(), y_prime);
    let c_end = hachi::endpiece::end_piece_check(&inst.d_key, &weval, &inst.w);
    eprintln!("[profile] verifier: end_piece_check = {c_end}: {:.1?}", t10.elapsed());
    assert!(c_final && c_end, "the two closing checks must accept");

    let t11 = Instant::now();
    let ok = chain_verify(
        &inst.pp, &inst.d_key, &inst.poly_stmt, &inst.v, &inst.c, &t_com, inst.alpha, &inst.tau0,
        &inst.tau1, &msgs, &inst.challenges, y_prime, &inst.w, CHAIN_GAMMA, blocks, message_rows,
        message_digits, inner_rows, inner_digits, z_digits,
    );
    eprintln!("[profile] chain_verify (whole, as the control) = {ok}: {:.1?}", t11.elapsed());
    eprintln!("[{:>9.1?}] profile done", t0.elapsed());
    assert!(ok, "the honest chain must verify");
}
