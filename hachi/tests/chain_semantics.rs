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
use hachi::linalg::{PolyMatrix, PolyVec, RawVec32};
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
        // `lift_commit_row` reads `|z| + |rho| * GADGET_DIGITS` entries of each
        // row -- 2 + 1 * 8 here -- so a width-2 key indexes out of bounds. This
        // was only ever reachable once `chain_open` stopped materializing the
        // decomposed message: before that the test was killed by the OOM killer
        // building 68.7 GiB, so the fixture's width was never exercised.
        d_key: r.next_poly_matrix(1, 2 + hachi::params::GADGET_DIGITS),
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

fn open(cm: &Common, raw: &Vec<RawVec32>) -> Transcript {
    let s = &TOY;
    // the carrier decomposition, once (candidate T28): `chain_open` takes it
    // rather than rebuilding it for `v`
    let stmt = hachi::quadeval::to_quad_eval_statement(&cm.poly_stmt);
    let carrier_dec = hachi::quadeval::carrier_decomp_from_raw_32(stmt.avec(), raw);
    let (v, t, msgs, y_prime) = chain_open(
        &cm.pp,
        &cm.d_key,
        &cm.poly_stmt,
        &carrier_dec,
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
    // the RAW width: `chain_open` decomposes internally now
    let raw: Vec<RawVec32> = (0..s.blocks)
        .map(|_| RawVec32::compact(&r.next_poly_vec(s.message_rows)))
        .collect();

    let tr = open(&cm, &raw);

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
    let raw: Vec<RawVec32> = (0..s.blocks)
        .map(|_| RawVec32::compact(&r.next_poly_vec(s.message_rows)))
        .collect();
    let tr = open(&cm, &raw);

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

/// A **protocol-valid** challenge: `ShortChallenge Φ ω` at `ω = params::OMEGA`,
/// i.e. centred `ℓ₁` norm at most 16.
///
/// What this replaces filled all `RING_DEGREE` coefficients from `{-1, 0, 1}`
/// and called itself short. Its `ℓ₁` norm is in the hundreds, so
/// `ring::classify_short` returns `None` and `honest_z` runs its **dense
/// fallback** -- a generic `Rq::mul` per entry. The profile of
/// 2026-09-18 measured `honest_compute_resp` at 3201.8 s for that reason where
/// the protocol path is ~320 s, a 13x inflation, and the two bench rows
/// (`quadeval/honest_z_short` 214 ms against `honest_z_dense` 2.84 s per block)
/// price the gap exactly.
///
/// Same shape as `benches/quadeval.rs`'s `short_challenge` so that the profile
/// and the bench rows measure the same path: `weight / mag` terms of magnitude
/// `mag` and alternating sign, spread by a stride coprime to the degree so some
/// of them wrap under any shift.
fn short_challenge_rq(index: usize, weight: u64, mag: u64) -> Rq {
    let degree = hachi::params::RING_DEGREE;
    let q = hachi::params::Q;
    assert!(weight <= hachi::params::OMEGA, "a challenge above the ω budget is not short");
    let mut coeffs: Vec<cpoly::Fp> = Vec::with_capacity(degree);
    for _ in 0..degree {
        coeffs.push(cpoly::Fp::new(0));
    }
    let terms = (weight / mag) as usize;
    for t in 0..terms {
        let at = (index * 31 + t * 97 + 13) % degree;
        let word = if t % 2 == 0 { mag } else { q - mag };
        coeffs[at] = cpoly::Fp::new(word);
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
fn dense_eval(blocks: &[RawVec32], xl: &PolyVec, xh: &PolyVec) -> Rq {
    // `y = Σᵢ wl(i) · Σⱼ Mᵢⱼ · wh(j)`, with `wl(i) = Π_{b ∈ bits(i)} xl[b]` and
    // likewise `wh`. The nested form this replaces recomputed each of those
    // products from scratch for every `(i, j)` -- `blocks · rows · popcount(j)`
    // ring multiplications, 5.2 MILLION at the pin, measured at **1860 s**,
    // more than the entire honest prover. Computing them once leaves
    // `blocks · rows` multiplications, about a fifth of that.
    //
    // The tables are the standard eq-tilde build: `2ⁿ − 1` multiplications for
    // `2ⁿ` entries. Bit order is `(k >> b) & 1`, matching `eval_direct` in
    // `quadeval_semantics.rs`, which is where this function's convention comes
    // from; an index past `2ⁿ` reads the low `n` bits, exactly as the nested
    // loop did. `dense_eval_agrees_with_the_nested_form` is the oracle.
    let eq = |x: &PolyVec| -> Vec<Rq> {
        let n = x.len();
        let mut t: Vec<Rq> = Vec::with_capacity(1usize << n);
        t.push(Rq::one());
        for b in 0..n {
            for j in 0..(1usize << b) {
                let v = t[j].mul(x.get(b));
                t.push(v);
            }
        }
        t
    };
    let wl = eq(xl);
    let wh = eq(xh);
    let low_mask = (1usize << xl.len()) - 1;
    let high_mask = (1usize << xh.len()) - 1;

    let mut acc = Rq::zero();
    for i in 0..blocks.len() {
        // one block expanded, read, and dropped: the scaffolding does not get
        // to hold the 8 GiB form the prover no longer holds either
        let f: PolyVec = blocks[i].expand();
        let mut block = Rq::zero();
        for j in 0..f.len() {
            block = block.add(&f.get(j).mul(&wh[j & high_mask]));
        }
        acc = acc.add(&block.mul(&wl[i & low_mask]));
    }
    acc
}

/// `dense_eval` still computes what the nested form computed.
///
/// The reference below *is* the old implementation, written out so the two
/// cannot drift together. Ring arithmetic here is exact, so the rewrite --
/// which only reassociates and shares products -- must agree bit for bit.
/// Several shapes, including one where the block width exceeds `2^|xh|`, which
/// is the case the index masking exists for and the pin never exercises.
#[test]
fn dense_eval_agrees_with_the_nested_form() {
    fn nested(blocks: &[PolyVec], xl: &PolyVec, xh: &PolyVec) -> Rq {
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

    let mut r = Lcg::new(0xDE5E_0001);
    // (blocks, rows, |xl|, |xh|) -- the last two straddle `rows` vs `2^|xh|`
    for &(nb, rows, nl, nh) in &[(1usize, 1usize, 1usize, 1usize), (4, 8, 2, 3),
                                 (3, 8, 2, 3), (5, 9, 3, 3), (2, 16, 1, 2)] {
        let m: Vec<PolyVec> = (0..nb).map(|_| r.next_poly_vec(rows)).collect();
        let xl = r.next_poly_vec(nl);
        let xh = r.next_poly_vec(nh);
        let want = nested(&m, &xl, &xh);
        // compacted for the call under test, so the `u32` round trip is inside
        // the comparison rather than assumed alongside it
        let mc: Vec<RawVec32> = m.iter().map(RawVec32::compact).collect();
        let got = dense_eval(&mc, &xl, &xh);
        assert!(
            got.equals(&want),
            "dense_eval disagrees at blocks={nb} rows={rows} |xl|={nl} |xh|={nh}"
        );
    }
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
    carrier_dec: PolyVec,
    c: PolyVec,
    w: LiftedWitness,
    v: PolyVec,
    alpha: Ext4,
    tau0: Vec<Ext4>,
    tau1: Vec<Ext4>,
    challenges: Vec<Ext4>,
}

/// Build the pin-shaped honest instance at `blocks` message blocks; asserts the
/// cube coverage, optionally asserts `M ζ = y`, and prints stage times.
///
/// `check_relout` gates the `M ζ = y` assertion, and only the profile passes
/// `false`. That assertion is a dense `Rq` matrix–vector multiply at the
/// assembled shape — 5 × 40 976 entries, so ~205 000 `Rq::mul` calls — and it
/// costs ~150 s at the pin, which is a sixth of a profile run spent on work the
/// protocol never does. It is a *semantics* check, it belongs to
/// `the_honest_chain_verifies`, and that test still runs it; the profile's job
/// is to time protocol phases. Recorded as owed in NOTES 2026-09-16
/// ("Correction: 144 s of the \"chain\" profile is a test assertion").
/// The kernel's own high-water mark for this process, in MiB.
///
/// `/usr/bin/time` is not installed on this machine, and a peak has to be read
/// from inside the process anyway. `VmHWM` is monotone, so a per-stage line
/// reports the high-water mark *as of* that boundary, which is what a wall
/// claim needs: the maximum over the run is the last one.
fn rss_mib(field: &str) -> u64 {
    let status = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    for line in status.lines() {
        if let Some(rest) = line.strip_prefix(field) {
            let kib: u64 = rest.trim().trim_end_matches(" kB").trim().parse().unwrap_or(0);
            return kib / 1024;
        }
    }
    0
}

/// The high-water mark: monotone, so a stage line reports the peak *as of* that
/// boundary and the last line is the peak over the run. This is the figure a
/// wall claim is made against.
fn peak_rss_mib() -> u64 {
    rss_mib("VmHWM:")
}

/// The live resident set. Reported beside the peak because the peak cannot go
/// down: without it, freeing 8 GiB is invisible in the trace.
fn live_rss_mib() -> u64 {
    rss_mib("VmRSS:")
}

#[allow(clippy::too_many_lines)]
fn pin_instance(blocks: usize, t0: &std::time::Instant, check_relout: bool) -> PinInstance {
    // Two clocks, deliberately: `t0` is cumulative, so a run that takes an hour
    // shows progress, and `last` is per stage, so a line can be *attributed*.
    // Printing only the cumulative figure here made these lines read exactly
    // like the per-stage deltas the profile body below reports -- which is how
    // 23 minutes of `dense_eval` were once read as prover time.
    // A `Cell` rather than `let mut`: the macro re-stamps it after every
    // line, and the stamp after the *last* line is a write nothing reads,
    // which `unused_assignments` rightly flags on a plain variable.
    let last = std::cell::Cell::new(std::time::Instant::now());
    macro_rules! stage {
        ($($arg:tt)*) => {{
            eprintln!("[{:>9.1?}] +{:>9.1?}  peak {:>6} live {:>6} MiB  {}",
                t0.elapsed(), last.get().elapsed(), peak_rss_mib(), live_rss_mib(),
                format_args!($($arg)*));
            last.set(std::time::Instant::now());
        }};
    }
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
    // Compacted one block at a time (T29): the `Vec<PolyVec>` form is 8 GiB at
    // the pin and is never built -- `r.next_poly_vec` output lives for exactly
    // as long as `RawVec32::compact` needs to read it.
    let raw: Vec<RawVec32> =
        (0..blocks).map(|_| RawVec32::compact(&r.next_poly_vec(message_rows))).collect();
    // the STREAMED committer: the 68.7 GiB `Decomp.message` is never built, and
    // nothing below needs it -- `honest_compute_v_from_raw` and
    // `honest_compute_resp_from_raw` both work from `raw`.
    // The claim, computed BEFORE the timed region and reported outside it.
    //
    // `dense_eval` is scaffolding: the test evaluating the message polynomial
    // itself so that the statement handed to the prover is a true one. It needs
    // only `raw`, not the commitment, so it is hoisted above the clock and the
    // stage stamp is reset after it -- it is now outside the timed region
    // rather than merely labelled inside it. Same defect class as the
    // `M zeta = y` assertion this docstring records, and now the same remedy.
    let untimed = std::time::Instant::now();
    let xl = r.next_poly_vec(XL_VARS);
    let xh = r.next_poly_vec(XH_VARS);
    let y = dense_eval(&raw, &xl, &xh);
    eprintln!(
        "[  untimed ] +{:>9.1?}  peak {:>6} live {:>6} MiB  dense_eval (SCAFFOLDING, outside the timed region)",
        untimed.elapsed(),
        peak_rss_mib(),
        live_rss_mib()
    );
    last.set(std::time::Instant::now());

    let (u, inner_decomp) = hachi::commit::commit_streamed_32(&inner, &raw);
    let pp = PublicParamsD::new(inner, d_matrix);
    stage!("committed {blocks} block(s)");

    let poly_stmt = PolyEvalStatement::new(u, xl, xh, y);
    let stmt = hachi::quadeval::to_quad_eval_statement(&poly_stmt);
    stage!("statement built");

    // the wire's challenges: one SHORT ring element per block (`honest_z` folds
    // block `i` against `c.get(i)`; the 64-block run of 2026-09-15 found this
    // vector mis-*sized* and fixed the size -- nobody checked its shortness,
    // so every profile before 2026-09-18 measured `honest_z`'s dense fallback
    // rather than the protocol path)
    let c = PolyVec::new(
        (0..blocks).map(|i| short_challenge_rq(i, hachi::params::OMEGA, 1)).collect(),
    );
    let alpha = ext4(&mut r);
    let tau0: Vec<Ext4> = (0..m0).map(|_| ext4(&mut r)).collect();
    let tau1: Vec<Ext4> = (0..m1).map(|_| ext4(&mut r)).collect();
    let challenges: Vec<Ext4> = (0..m0).map(|_| ext4(&mut r)).collect();

    // the honest QuadEval side: the carrier decomposition ONCE (candidate T28),
    // then `v = D w-hat` and the response from it, then the stacking. Before
    // T28 this stage computed the carrier three times at the pin -- here, in
    // the response, and again inside `chain_open` -- at 98.7 s each.
    let carrier_dec = hachi::quadeval::carrier_decomp_from_raw_32(stmt.avec(), &raw);
    stage!("carrier_decomp_from_raw (shared by v and the response)");
    let v = hachi::quadeval::honest_compute_v_from_decomp(pp.d_matrix(), &carrier_dec);
    stage!("honest_compute_v_from_decomp");
    let resp =
        hachi::quadeval::honest_compute_resp_from_raw_32(&carrier_dec, &raw, &inner_decomp, &c);
    let zeta = hachi::quadeval::stack(&resp);
    stage!("honest_compute_resp + stack");
    // The message is DEAD here, and this is the earliest it ever has been.
    // Its three readers are the commitment, the carrier decomposition and
    // `honest_z` -- all above -- and since candidate T28 `chain_open` takes the
    // decomposition instead of the message, so nothing below reads it either.
    // It is dropped rather than left to `pin_instance`'s scope because the
    // R^lin assembly happens in between, and 4.3 GiB of dead message underneath
    // a 3.0 GiB matrix is what set the peak.
    drop(raw);
    stage!("raw message dropped (dead from here: T28 removed its last reader)");
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
    stage!("R^lin statement assembled: {} x {}", rlin.m().rows(), rlin.m().cols());

    // relOut ⇒ rlin: the stacked honest response solves the assembled system
    if check_relout {
        assert!(
            rlin.m().mat_vec_mul(&zeta).equals(rlin.yvec()),
            "the honest stacked response must solve the assembled R^lin system"
        );
        stage!("M zeta = y holds (TEST ASSERTION, not prover work)");
    } else {
        stage!("M zeta = y SKIPPED (not prover work)");
    }

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
    stage!("lifted witness built, lift width {lift_cols}");

    PinInstance { pp, d_key, poly_stmt, carrier_dec, c, w, v, alpha, tau0, tau1, challenges }
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
    let inst = pin_instance(blocks, &t0, true);

    // the honest prover
    let (v_open, t, msgs, y_prime) = chain_open(
        &inst.pp,
        &inst.d_key,
        &inst.poly_stmt,
        &inst.carrier_dec,
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

/// The control the profile did not have.
///
/// A fixed amount of work in the **frozen** `hachi-genesis` crate, timed at the
/// start and again at the end of a profile run. It exists because every
/// cross-run profile comparison so far has had to hand-wave a systematic offset:
/// after candidate R -- which touched `long_mul` and nothing else -- every
/// untouched phase moved coherently by 8-12%, and the same thing happened again
/// after T2a (`lift_commit` 27.0 -> 30.5 s, `alpha_public_table` 12.6 -> 14.5 s).
/// Without a control there is no way to tell that offset from a real change, so
/// a phase that "moved 10%" and a machine that was 10% slower read identically.
///
/// `hachi_genesis::linalg::PolyVec::zeros` is the same choice
/// `benches/support/mod.rs` makes and for its reasons: a fixed-shape
/// allocate-and-fill at the [NOZ26] Fig. 9 block width, on no hot path, so it is
/// representative of the allocating rows without being an optimization target.
/// Taking it from the *genesis* crate is what makes it immune to candidates by
/// construction -- `make check-genesis` pins that copy to git, so it cannot drift
/// under a champion landing. (It is not immune to `Rq::zero` moving, which fills
/// it; that failure is loud, as `ring/zero`.)
///
/// Two readings per run, and both are needed: the post-T2a profile showed the
/// offset is **not one number** -- the phases around the middle of the run moved
/// +10 to +16%, while `end_piece_check` and the `chain_verify` that contains it
/// moved +29%, so it drifts *within* a run (thermal or page-cache state, at
/// minute 14 of a sustained load). The spread between the two readings is that
/// drift; their level against a previous run's is the machine's offset. Recenter
/// phase deltas by the reading nearest them before believing anything.
///
/// Sizing, measured here rather than extrapolated: 50 reps read **500.7 ms**
/// (~10 ms per call) in the 2026-09-16 pre-bump run -- far above timer noise,
/// and ~1 s added to a ~12 minute run for both readings.
///
/// Note it is *not* the same 33.4 ms that `_control/*/8192` reads, and the
/// difference is the point: the bench control is
/// `support::run(m, || PolyVec::zeros(n), d_polyvec)`, so it also digests all
/// 8192 x 1024 coefficients, which `case!` needs as its semantics oracle and
/// this does not. Same allocate-and-fill, without the digest.
fn profile_control(reps: usize) -> std::time::Duration {
    const CONTROL_N: usize = 8192; // = MESSAGE_ROWS * GADGET_DIGITS, as in benches/support
    let t = std::time::Instant::now();
    for _ in 0..reps {
        let v = hachi_genesis::linalg::PolyVec::zeros(CONTROL_N);
        std::hint::black_box(v.len());
    }
    t.elapsed()
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
    let ctl_before = profile_control(50);
    eprintln!("[profile] control (frozen genesis PolyVec::zeros x50): {ctl_before:.1?}");
    // The raw message is gone before this point, and no longer by an explicit
    // `drop`: candidate T28 gave `chain_open` the carrier decomposition instead
    // of the message, so nothing after `pin_instance` reads the message and its
    // lifetime ends inside the fixture. It used to be held live through the
    // whole profile body -- 8 GiB before T29, 4.3 after -- which is what the
    // 2026-09-18 run died of, the OOM killer taking it at 16.93 GiB inside
    // `chain_verify (whole)`, which rebuilds the R^lin matrix and both 2^26
    // tables on top of a message nobody was going to read.
    let inst = pin_instance(blocks, &t0, false);
    eprintln!(
        "[{:>9.1?}] ---------  peak {:>6} live {:>6} MiB  raw message already dead (T28)",
        t0.elapsed(),
        peak_rss_mib(),
        live_rss_mib()
    );
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
    eprintln!("[profile] chain_verify (whole) = {ok}: {:.1?}", t11.elapsed());
    let ctl_after = profile_control(50);
    eprintln!("[profile] control (frozen genesis PolyVec::zeros x50): {ctl_after:.1?}");
    eprintln!(
        "[profile] control spread within run: {:+.1}%  (recenter cross-run deltas by the level)",
        100.0 * (ctl_after.as_secs_f64() / ctl_before.as_secs_f64() - 1.0)
    );
    eprintln!("[{:>9.1?}] profile done", t0.elapsed());
    assert!(ok, "the honest chain must verify");
}

/// **Where the commitment's minutes go, per block and per coefficient**
/// (Stage 6 card 6, the instrument candidate T11's accept needs).
///
/// The commitment is 541 s at the pin, 46% of the honest prover and by a wide
/// margin the largest remaining item. Until now its split into *decomposition*
/// and *prepared product* was an inference from the `gadget/*_decompose/1024`
/// micro-row, and T11's accept rule is stated on the phase -- ≤ 5 ns per
/// coefficient, kill above 15 -- so the phase is what has to be measured.
///
/// This replays the two per-block loop bodies verbatim, from
/// `commit::commit_streamed_32` and `quadeval::honest_z_from_raw_32`, with a
/// clock around each piece. It is deliberately *outside* the crate: a timer
/// inside `commit_streamed` would extract, and nothing under `hachi/src` may
/// carry instrumentation.
///
/// "Per coefficient" counts the *input* coefficients the pass consumes, which
/// is `MESSAGE_ROWS × RING_DEGREE` per block, because that is the unit T11's
/// target is quoted in. The digit count is eight times larger.
#[test]
#[ignore = "pin-width timing, several minutes -- run with cargo test --release -- --ignored"]
fn the_commitment_and_z_pass_split_per_block() {
    use hachi::linalg::RawVec32;
    use hachi::params::{GADGET_DIGITS, INNER_ROWS, MESSAGE_ROWS, OMEGA, RING_DEGREE};
    let blocks: usize = std::env::var("HACHI_SPLIT_BLOCKS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(4);
    let mut r = Lcg::new(0xC0A1_0060);
    let coeffs_per_block: u128 = (MESSAGE_ROWS * RING_DEGREE) as u128;

    let inner = hachi::commit::PublicParams::new(
        r.next_poly_matrix(INNER_ROWS, MESSAGE_ROWS * GADGET_DIGITS),
        r.next_poly_matrix(1, blocks * INNER_ROWS * GADGET_DIGITS),
    );
    let raw: Vec<RawVec32> =
        (0..blocks).map(|_| RawVec32::compact(&r.next_poly_vec(MESSAGE_ROWS))).collect();
    let c = PolyVec::new(
        (0..blocks).map(|i| short_challenge_rq(i, OMEGA, 1)).collect(),
    );

    // ---- the commitment pass, `commit_streamed_32`'s loop body ----
    let prep = inner.inner_matrix().prepare_digits();
    let (mut t_expand, mut t_dec, mut t_apply, mut t_dec2) = (
        std::time::Duration::ZERO,
        std::time::Duration::ZERO,
        std::time::Duration::ZERO,
        std::time::Duration::ZERO,
    );
    for b in raw.iter() {
        let c0 = std::time::Instant::now();
        let block = b.expand();
        t_expand += c0.elapsed();

        let c1 = std::time::Instant::now();
        let s = hachi::gadget::gadget_decompose(&block);
        t_dec += c1.elapsed();

        let c2 = std::time::Instant::now();
        let innerv = prep.apply_digits(&s);
        t_apply += c2.elapsed();

        let c3 = std::time::Instant::now();
        let ts = hachi::gadget::gadget_decompose(&innerv);
        t_dec2 += c3.elapsed();
        std::hint::black_box(ts.len());
    }

    // ---- the z pass, `honest_z_from_raw_32`'s loop body ----
    let width = MESSAGE_ROWS * GADGET_DIGITS;
    let mut acc: Vec<Rq> = (0..width).map(|_| Rq::zero()).collect();
    let (mut z_expand, mut z_dec, mut z_mul) =
        (std::time::Duration::ZERO, std::time::Duration::ZERO, std::time::Duration::ZERO);
    let mut short_blocks = 0usize;
    for (i, b) in raw.iter().enumerate() {
        let c0 = std::time::Instant::now();
        let block = b.expand();
        z_expand += c0.elapsed();

        let c1 = std::time::Instant::now();
        let s = hachi::gadget::gadget_decompose(&block);
        z_dec += c1.elapsed();

        let c2 = std::time::Instant::now();
        match hachi::ring::classify_short(c.get(i)) {
            Some(desc) => {
                short_blocks += 1;
                for j in 0..width {
                    hachi::ring::mul_short_add_into(&desc, s.get(j), &mut acc[j]);
                }
            }
            None => {
                let scaled = s.scalar_mul(c.get(i));
                for j in 0..width {
                    acc[j] = acc[j].add(scaled.get(j));
                }
            }
        }
        z_mul += c2.elapsed();
    }
    std::hint::black_box(acc.len());

    let per = |d: std::time::Duration| -> f64 {
        d.as_nanos() as f64 / (coeffs_per_block * blocks as u128) as f64
    };
    let share = |d: std::time::Duration, tot: std::time::Duration| -> f64 {
        100.0 * d.as_secs_f64() / tot.as_secs_f64()
    };
    let commit_tot = t_expand + t_dec + t_apply + t_dec2;
    let z_tot = z_expand + z_dec + z_mul;

    eprintln!("[split] blocks = {blocks}, {coeffs_per_block} input coefficients per block");
    eprintln!("[split] --- the commitment pass (commit_streamed_32's loop body) ---");
    for (name, d) in [
        ("expand (u32 -> Rq)", t_expand),
        ("gadget_decompose (message)", t_dec),
        ("apply_digits (prepared product)", t_apply),
        ("gadget_decompose (inner)", t_dec2),
    ] {
        eprintln!(
            "[split]   {name:34} {:>9.2?}  {:>5.1}%  {:>8.2} ns/coeff",
            d,
            share(d, commit_tot),
            per(d)
        );
    }
    eprintln!("[split]   {:34} {commit_tot:>9.2?}         {:>8.2} ns/coeff", "TOTAL", per(commit_tot));
    eprintln!("[split] --- the z pass (honest_z_from_raw_32's loop body) ---");
    eprintln!("[split]   {short_blocks}/{blocks} blocks took the SHORT path");
    for (name, d) in [
        ("expand (u32 -> Rq)", z_expand),
        ("gadget_decompose (rebuild)", z_dec),
        ("short multiply + accumulate", z_mul),
    ] {
        eprintln!(
            "[split]   {name:34} {:>9.2?}  {:>5.1}%  {:>8.2} ns/coeff",
            d,
            share(d, z_tot),
            per(d)
        );
    }
    eprintln!("[split]   {:34} {z_tot:>9.2?}         {:>8.2} ns/coeff", "TOTAL", per(z_tot));
    eprintln!(
        "[split] T11 reads on `gadget_decompose`: {:.2} ns/coeff (target <= 5, kill > 15)",
        per(t_dec)
    );
}

// ---------------------------------------------------------------------------
// Card 8 / T25 Gate B: the `u32` transform, measured at the CALLER
// ---------------------------------------------------------------------------
//
// Gate A (scratchpad `probe-u32ntt`) measured the butterfly at 2.59 ns on
// `u64` and 1.82 ns on `u32` with entry asserts, −30%, correctness-checked.
// Gate B asks the only question that matters: what does that do to
// `apply_digits`, which is 94% of the commitment and 43% of the prover?
//
// This is a faithful REPLICA of the `apply_digits` path with `u32` transform
// words, living in the test rather than in `hachi/src`. That is deliberate:
// every `AuxTransform` spec is stated over `Vec Std.U64`, so retyping the
// transform layer breaks ~1186 lines of Lean the moment it lands, and
// `make build` is a hard gate. The goal's rule is that the caller-level gain
// comes first and the proof second, so the measurement is taken without
// touching the verified crate at all. `the_u32_replica_agrees_with_apply_digits`
// is what makes the replica evidence rather than decoration.

const U32_BARRETT_SCALE: u128 = 18_446_744_073_709_551_616;

#[inline]
fn r32(x: u64, p: u32, m: u64) -> u32 {
    let wide: u128 = (x as u128) * (m as u128);
    let qh: u64 = (wide / U32_BARRETT_SCALE) as u64;
    let r: u64 = x - qh * (p as u64);
    if r >= p as u64 { (r - p as u64) as u32 } else { r as u32 }
}
#[inline]
fn m32(a: u32, b: u32, p: u32, m: u64) -> u32 { r32((a as u64) * (b as u64), p, m) }
#[inline]
fn a32(a: u32, b: u32, p: u32) -> u32 { let s = a + b; if s >= p { s - p } else { s } }
#[inline]
fn s32(a: u32, b: u32, p: u32) -> u32 { if a >= b { a - b } else { a + p - b } }

fn psi_table32(psi: u64, p: u32, m: u64) -> Vec<u32> {
    let n = hachi::params::RING_DEGREE;
    let mut out = Vec::with_capacity(n);
    let mut cur: u32 = 1;
    for _ in 0..n { out.push(cur); cur = m32(cur, psi as u32, p, m); }
    out
}

fn dif32(src: &[u32], dst: &mut [u32], len: usize, tw: &[u32], p: u32, m: u64) {
    let n = hachi::params::RING_DEGREE;
    assert!(src.len() == n && dst.len() == n && tw.len() == n);
    let half = len / 2;
    let step = 2 * (n / len);
    let mut start = 0usize;
    while start < n {
        let mut j = 0usize;
        while j < half { dst[start + j] = a32(src[start + j], src[start + j + half], p); j += 1; }
        let (mut i, mut e) = (0usize, 0usize);
        while i < half {
            let d = s32(src[start + i], src[start + i + half], p);
            dst[start + half + i] = m32(d, tw[e], p, m);
            i += 1; e += step;
        }
        start += len;
    }
}

fn fwd32(mut cur: Vec<u32>, mut tmp: Vec<u32>, tw: &[u32], p: u32, m: u64) -> (Vec<u32>, Vec<u32>) {
    let mut len = hachi::params::RING_DEGREE;
    while len > 1 {
        dif32(&cur, &mut tmp, len, tw, p, m);
        std::mem::swap(&mut cur, &mut tmp);
        len /= 2;
    }
    (cur, tmp)
}

/// `prepare_digits` for one row, as `u32` forward tables under the two
/// digit-path primes.
fn prepare_row32(row: &PolyVec) -> (Vec<u32>, Vec<u32>) {
    let n = hachi::params::RING_DEGREE;
    let (p1, m1) = (hachi::ntt::AUX_P1 as u32, hachi::ntt::AUX_M1);
    let (p2, m2) = (hachi::ntt::AUX_P2 as u32, hachi::ntt::AUX_M2);
    let t1 = psi_table32(hachi::ntt::AUX_PSI1, p1, m1);
    let t2 = psi_table32(hachi::ntt::AUX_PSI2, p2, m2);
    let (mut f1, mut f2) = (Vec::new(), Vec::new());
    for j in 0..row.len() {
        for (p, m, t, out) in [(p1, m1, &t1, &mut f1), (p2, m2, &t2, &mut f2)] {
            let mut w: Vec<u32> = Vec::with_capacity(n);
            for u in 0..n { w.push(r32(row.get(j).coeff(u).to_u64(), p, m)); }
            for u in 0..n { w[u] = m32(w[u], t[u], p, m); }
            let (f, _) = fwd32(w, vec![0u32; n], t, p, m);
            out.extend_from_slice(&f);
        }
    }
    (f1, f2)
}

/// `dot_prepared_digits` over `u32` words: the same chunking, the same two
/// primes, the same Garner reconstruction.
fn dot_prepared_digits32(f1: &[u32], f2: &[u32], b: &PolyVec, n_terms: usize) -> Rq {
    let n = hachi::params::RING_DEGREE;
    let qw = hachi::params::Q;
    let (p1, m1) = (hachi::ntt::AUX_P1 as u32, hachi::ntt::AUX_M1);
    let (p2, m2) = (hachi::ntt::AUX_P2 as u32, hachi::ntt::AUX_M2);
    let t1 = psi_table32(hachi::ntt::AUX_PSI1, p1, m1);
    let t2 = psi_table32(hachi::ntt::AUX_PSI2, p2, m2);
    let mut acc = Rq::zero();
    let mut start = 0usize;
    while start < n_terms {
        let take = std::cmp::min(hachi::ring::DOT_CHUNK_D, n_terms - start);
        let end = start + take;
        let mut r = [vec![0u32; n], vec![0u32; n]];
        for (k, (p, m, t, f, doff)) in [
            (p1, m1, &t1, f1, hachi::ntt::AUX_DOFF1),
            (p2, m2, &t2, f2, hachi::ntt::AUX_DOFF2),
        ]
        .into_iter()
        .enumerate()
        {
            let mut a = vec![0u32; n];
            let mut scratch = vec![0u32; n];
            for j in start..end {
                let mut w: Vec<u32> = Vec::with_capacity(n);
                for u in 0..n { w.push(r32(b.get(j).coeff(u).to_u64(), p, m)); }
                for u in 0..n { w[u] = m32(w[u], t[u], p, m); }
                let (fb, sc) = fwd32(w, scratch, t, p, m);
                scratch = sc;
                for u in 0..n { a[u] = a32(a[u], m32(f[j * n + u], fb[u], p, m), p); }
            }
            // inverse transform + untwist, as `dot_prep_chunk_mod_p` does
            let it = {
                let inv = if k == 0 { hachi::ntt::AUX_PSIINV1 } else { hachi::ntt::AUX_PSIINV2 };
                psi_table32(inv, p, m)
            };
            let ninv = if k == 0 { hachi::ntt::AUX_NINV1 } else { hachi::ntt::AUX_NINV2 };
            let mut cur = a;
            let mut tmp = vec![0u32; n];
            let mut len = 2usize;
            while len <= n {
                // dit stage, inverse of dif at the same len
                let half = len / 2;
                let step = 2 * (n / len);
                let mut st = 0usize;
                while st < n {
                    let (mut j, mut e) = (0usize, 0usize);
                    while j < half {
                        let u = cur[st + j];
                        let v = m32(cur[st + j + half], it[e], p, m);
                        tmp[st + j] = a32(u, v, p);
                        tmp[st + j + half] = s32(u, v, p);
                        j += 1; e += step;
                    }
                    st += len;
                }
                std::mem::swap(&mut cur, &mut tmp);
                len *= 2;
            }
            // `boff` is scaled by the chunk's term count, exactly as
            // `dot_prep_chunk_mod_p` does: one offset per term was folded in.
            let scaled = m32(doff as u32, ((end - start) as u64 % p as u64) as u32, p, m);
            for u in 0..n {
                let uu = m32(cur[u], it[u], p, m);
                r[k][u] = a32(m32(uu, ninv as u32, p, m), scaled, p);
            }
        }
        let mut out: Vec<cpoly::field::Fp> = Vec::with_capacity(n);
        for t in 0..n {
            out.push(cpoly::field::Fp::new(
                hachi::ntt::garner2(r[0][t] as u64, r[1][t] as u64) % qw,
            ));
        }
        acc = acc.add(&Rq::from_coeffs(&out));
        start = end;
    }
    acc
}

/// **Gate B.** `apply_digits` with `u32` transform words, timed against the
/// `u64` path it would replace, at pin width.
#[test]
#[ignore = "pin-width timing -- run with cargo test --release -- --ignored"]
fn the_u32_transform_at_the_caller() {
    use hachi::linalg::RawVec32;
    use hachi::params::{GADGET_DIGITS, MESSAGE_ROWS, RING_DEGREE};
    let blocks: usize = std::env::var("HACHI_U32_BLOCKS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(2);
    let mut r = Lcg::new(0xC0A1_0070);
    let cols = MESSAGE_ROWS * GADGET_DIGITS;
    let a_row = r.next_poly_vec(cols);
    let am = PolyMatrix::new(vec![a_row.copy()]);
    let raw: Vec<RawVec32> =
        (0..blocks).map(|_| RawVec32::compact(&r.next_poly_vec(MESSAGE_ROWS))).collect();

    let prep64 = am.prepare_digits();
    let tp = std::time::Instant::now();
    let (f1, f2) = prepare_row32(&a_row);
    let prep32_time = tp.elapsed();

    let (mut t64, mut t32) = (std::time::Duration::ZERO, std::time::Duration::ZERO);
    let mut agree = true;
    for b in raw.iter() {
        let s = hachi::gadget::gadget_decompose(&b.expand());

        let c0 = std::time::Instant::now();
        let got64 = prep64.apply_digits(&s);
        t64 += c0.elapsed();

        let c1 = std::time::Instant::now();
        let got32 = dot_prepared_digits32(&f1, &f2, &s, cols);
        t32 += c1.elapsed();

        agree &= got64.get(0).equals(&got32);
    }
    assert!(agree, "the u32 replica computes a different product -- the timing below is meaningless");

    let coeffs = (MESSAGE_ROWS * RING_DEGREE * blocks) as f64;
    eprintln!("[u32] blocks = {blocks}, prepare (u32, once) {prep32_time:.2?}");
    eprintln!(
        "[u32] apply_digits  u64 {:>9.2?} ({:>7.2} ns/coeff)   u32 {:>9.2?} ({:>7.2} ns/coeff)   {:+.1}%",
        t64,
        t64.as_nanos() as f64 / coeffs,
        t32,
        t32.as_nanos() as f64 / coeffs,
        100.0 * (t32.as_secs_f64() / t64.as_secs_f64() - 1.0)
    );
    eprintln!("[u32] the replica agrees with apply_digits on every block: {agree}");
}

// ---------------------------------------------------------------------------
// Card 7 / T11: the decomposer kernel, prototyped before it is proved
// ---------------------------------------------------------------------------
//
// Card 6 measured `gadget_decompose` at 29.68 ns/coeff in the commitment and
// 40.34 in the z pass, against T11's target of 5 and its kill line of 15. The
// cost is structural and visible in the source: the decomposers loop e-outer,
// so `digit_at(c, e)` restarts the division chain from digit 0 every time --
// 0+1+...+7 = 28 divisions per coefficient where 8 would do -- and the
// balanced path additionally recomputes `c + shift` and subtracts `half` once
// per digit.
//
// The kernel is k-outer with a running remainder, exactly as T11's card
// specifies: shift once, `rest % 16` and `rest /= 16` eight times, and for the
// balanced path a sixteen-entry residue table in place of a field element per
// digit. These replicas are here, not in `hachi/src`, so the kill gate can be
// read before any proof is spent -- the same order that rejected card 8.

/// `(d - 8 : ZMod q)` for `d` in `0..16`: T11's item 3, as a table.
const BALANCED_DIGIT_RESIDUE: [u64; 16] = {
    let q = 4_294_967_197u64;
    let mut t = [0u64; 16];
    let mut d = 0usize;
    while d < 16 {
        t[d] = if d >= 8 { (d - 8) as u64 } else { q - (8 - d) as u64 };
        d += 1;
    }
    t
};

fn gadget_decompose_kernel(x: &PolyVec) -> PolyVec {
    let digits = hachi::params::GADGET_DIGITS;
    let degree = hachi::params::RING_DEGREE;
    let b = hachi::params::GADGET_BASE;
    let mut out: Vec<Rq> = Vec::new();
    let mut i = 0usize;
    while i < x.len() {
        let mut flat: Vec<cpoly::field::Fp> = Vec::with_capacity(digits * degree);
        let mut z = 0usize;
        while z < digits * degree { flat.push(cpoly::field::Fp::new(0)); z += 1; }
        let mut k = 0usize;
        while k < degree {
            let mut rest: u64 = x.get(i).coeff(k).to_u64();
            let mut e = 0usize;
            while e < digits {
                flat[e * degree + k] = cpoly::field::Fp::new(rest % b);
                rest /= b;
                e += 1;
            }
            k += 1;
        }
        let mut e = 0usize;
        while e < digits {
            let mut coeffs: Vec<cpoly::field::Fp> = Vec::with_capacity(degree);
            let mut k2 = 0usize;
            while k2 < degree { coeffs.push(flat[e * degree + k2]); k2 += 1; }
            out.push(Rq::from_coeffs(&coeffs));
            e += 1;
        }
        i += 1;
    }
    PolyVec::new(out)
}

fn balanced_gadget_decompose_kernel(x: &PolyVec) -> PolyVec {
    let digits = hachi::params::GADGET_DIGITS;
    let degree = hachi::params::RING_DEGREE;
    let b = hachi::params::GADGET_BASE;
    let shift = hachi::params::BALANCED_SHIFT;
    let mut out: Vec<Rq> = Vec::new();
    let mut i = 0usize;
    while i < x.len() {
        let mut flat: Vec<cpoly::field::Fp> = Vec::with_capacity(digits * degree);
        let mut z = 0usize;
        while z < digits * degree { flat.push(cpoly::field::Fp::new(0)); z += 1; }
        let mut k = 0usize;
        while k < degree {
            // shift ONCE, not once per digit
            let mut rest: u64 = (x.get(i).coeff(k) + cpoly::field::Fp::new(shift)).to_u64();
            let mut e = 0usize;
            while e < digits {
                // the balanced residue by lookup: no field element per digit
                flat[e * degree + k] =
                    cpoly::field::Fp::new(BALANCED_DIGIT_RESIDUE[(rest % b) as usize]);
                rest /= b;
                e += 1;
            }
            k += 1;
        }
        let mut e = 0usize;
        while e < digits {
            let mut coeffs: Vec<cpoly::field::Fp> = Vec::with_capacity(degree);
            let mut k2 = 0usize;
            while k2 < degree { coeffs.push(flat[e * degree + k2]); k2 += 1; }
            out.push(Rq::from_coeffs(&coeffs));
            e += 1;
        }
        i += 1;
    }
    PolyVec::new(out)
}


/// Kernel v2 for the unsigned path: keep e-outer and the output order, and
/// attack what the profile actually pays -- `Vec::new()` growing to 1024 by
/// reallocation 8192 times per row, `x.get(i)` re-indexed per digit, and
/// `digit_at`'s division chain where one shift and a mask will do.
fn gadget_decompose_kernel2(x: &PolyVec) -> PolyVec {
    let digits = hachi::params::GADGET_DIGITS;
    let degree = hachi::params::RING_DEGREE;
    let mut out: Vec<Rq> = Vec::with_capacity(x.len() * digits);
    let mut i = 0usize;
    while i < x.len() {
        let row = x.get(i); // hoisted: one index per ROW, not per digit
        let mut e = 0usize;
        while e < digits {
            let sh = 4 * e;
            let mut coeffs: Vec<cpoly::field::Fp> = Vec::with_capacity(degree);
            let mut k = 0usize;
            while k < degree {
                coeffs.push(cpoly::field::Fp::new((row.coeff(k).to_u64() >> sh) & 15));
                k += 1;
            }
            out.push(Rq::from_coeffs(&coeffs));
            e += 1;
        }
        i += 1;
    }
    PolyVec::new(out)
}

/// **T11's kill gate, read before any proof is spent.**
///
/// Warmed and repeated, because the first measurement of this lied: the same
/// function read 45.60 ns/coeff on its first call and 17.52 on its second,
/// entirely from cache and allocator warmth. Each variant is run once to warm
/// and then `reps` times, and the MINIMUM is reported -- the minimum is the
/// one statistic a cold start cannot inflate.
#[test]
#[ignore = "pin-width timing -- run with cargo test --release -- --ignored"]
fn the_decomposer_kernel_against_its_kill_gate() {
    use hachi::params::{MESSAGE_ROWS, RING_DEGREE};
    let rows: usize = std::env::var("HACHI_T11_ROWS")
        .ok().and_then(|v| v.parse().ok()).unwrap_or(MESSAGE_ROWS);
    let reps: usize = std::env::var("HACHI_T11_REPS")
        .ok().and_then(|v| v.parse().ok()).unwrap_or(7);
    let mut r = Lcg::new(0xC0A1_0080);
    let x = r.next_poly_vec(rows);
    let coeffs = (rows * RING_DEGREE) as f64;

    let mut timed = |name: &str, f: fn(&PolyVec) -> PolyVec| -> f64 {
        let warm = f(&x);
        std::hint::black_box(warm.len());
        let mut best = f64::MAX;
        for _ in 0..reps {
            let t = std::time::Instant::now();
            let got = f(&x);
            let d = t.elapsed();
            std::hint::black_box(got.len());
            best = best.min(d.as_nanos() as f64);
        }
        let ns = best / coeffs;
        eprintln!("[t11] {name:30} {ns:>7.2} ns/coeff   (best of {reps})");
        ns
    };

    // correctness first, timing second: a faster wrong answer is not a result
    for (name, f_old, f_new) in [
        ("gadget_decompose / flat-buffer kernel",
         hachi::gadget::gadget_decompose as fn(&PolyVec) -> PolyVec,
         gadget_decompose_kernel as fn(&PolyVec) -> PolyVec),
        ("gadget_decompose / kernel v2",
         hachi::gadget::gadget_decompose as fn(&PolyVec) -> PolyVec,
         gadget_decompose_kernel2 as fn(&PolyVec) -> PolyVec),
        ("balanced_gadget_decompose / kernel",
         hachi::gadget::balanced_gadget_decompose as fn(&PolyVec) -> PolyVec,
         balanced_gadget_decompose_kernel as fn(&PolyVec) -> PolyVec),
    ] {
        let want = f_old(&x);
        let got = f_new(&x);
        assert_eq!(got.len(), want.len(), "{name}: output width changed");
        for j in 0..want.len() {
            assert!(got.get(j).equals(want.get(j)), "{name}: differs at output {j}");
        }
    }

    let base_u = timed("gadget_decompose (current)", hachi::gadget::gadget_decompose);
    let k1 = timed("  flat-buffer kernel", gadget_decompose_kernel);
    let k2 = timed("  kernel v2 (shift+mask, sized)", gadget_decompose_kernel2);
    let base_b = timed("balanced (current)", hachi::gadget::balanced_gadget_decompose);
    let kb = timed("  balanced kernel (table)", balanced_gadget_decompose_kernel);

    eprintln!("[t11] unsigned: flat {:+.1}%, v2 {:+.1}%    balanced: {:+.1}%",
        100.0 * (k1 / base_u - 1.0), 100.0 * (k2 / base_u - 1.0), 100.0 * (kb / base_b - 1.0));
    eprintln!("[t11] T11's gate: target <= 5 ns/coeff, KILL if a first cut does not reach 15");
}

// ---------------------------------------------------------------------------
// Card 9 / T17 Change 3: the gather form, prototyped before it is proved
// ---------------------------------------------------------------------------
//
// Card 6 measured the short multiply at 170.88 ns/coeff and 79.8% of the z
// pass -- about 184 s at the pin, 15.5% of the prover, the largest single item
// left after `apply_digits`. `mul_short_add_into` is a SCATTER: for each
// descriptor term and each unit of magnitude it makes a full pass over the
// 1024-entry accumulator with a branchy modular add/sub and a canonical write
// per element, so at the pin's weight-16 challenges the accumulator is written
// and reduced sixteen times per coefficient.
//
// The gather walks each OUTPUT coefficient once, sums its <= 16 signed reads of
// the operand in an `i64`, and reduces once. Same finite sum, different
// schedule. The descriptor's fields are private, so it is rebuilt here exactly
// as `classify_short` builds it -- centred residue, magnitude, sign -- which
// keeps `hachi/src` untouched while the kill gate is read.

struct Desc { idx: Vec<usize>, mag: Vec<u64>, neg: Vec<bool> }

fn classify_here(a: &Rq) -> Option<Desc> {
    let n = hachi::params::RING_DEGREE;
    let q = hachi::params::Q;
    let half = q / 2;
    let budget = hachi::params::OMEGA;
    let (mut idx, mut mag, mut neg) = (Vec::new(), Vec::new(), Vec::new());
    let mut total = 0u64;
    for k in 0..n {
        let c = a.coeff(k).to_u64();
        if c != 0 {
            let m = if c <= half { c } else { q - c };
            total += m;
            if total > budget { return None; }
            idx.push(k); mag.push(m); neg.push(c > half);
        }
    }
    Some(Desc { idx, mag, neg })
}

/// The gather: one pass over the output, one reduction per coefficient.
fn mul_short_add_into_gather(d: &Desc, s: &Rq, acc: &mut Vec<i64>) {
    let n = hachi::params::RING_DEGREE;
    let terms = d.idx.len();
    let mut w = 0usize;
    while w < n {
        let mut sum: i64 = 0;
        let mut t = 0usize;
        while t < terms {
            let k = d.idx[t];
            // the unique i with (k + i) ≡ w, and whether it crossed X^N = −1
            let (i, wrapped) = if w >= k { (w - k, false) } else { (w + n - k, true) };
            let sv = s.coeff(i).to_u64() as i64;
            let c = (d.mag[t] as i64) * sv;
            sum += if d.neg[t] != wrapped { -c } else { c };
            t += 1;
        }
        acc[w] += sum;
        w += 1;
    }
}


/// The accumulator change WITHOUT the traversal change: keep the scatter's
/// sequential order, drop the modular arithmetic.
///
/// Card 9 changed both at once and rejected both when the gather lost on
/// locality. They are independent: the scatter already reads `s[i]` and writes
/// `acc[(k+i) mod n]` as `i` advances, which is the good pattern; what it pays
/// per element is a branchy modular add/sub and a canonical `Fp::new` write,
/// sixteen times per coefficient at the pin's weight-16 challenges. Here the
/// accumulator is `i64`, the magnitude multiplies once instead of driving `m`
/// passes, and the reduction happens once per coefficient at the very end.
fn mul_short_add_into_i64(d: &Desc, s: &Rq, acc: &mut Vec<i64>) {
    let n = hachi::params::RING_DEGREE;
    let terms = d.idx.len();
    let mut t = 0usize;
    while t < terms {
        let k = d.idx[t];
        let m = d.mag[t] as i64;
        let neg = d.neg[t];
        let mut i = 0usize;
        while i < n {
            let sv = s.coeff(i).to_u64() as i64;
            if sv != 0 {
                let pos = k + i;
                let (w, wrapped) = if pos >= n { (pos - n, true) } else { (pos, false) };
                let c = m * sv;
                if neg != wrapped { acc[w] -= c; } else { acc[w] += c; }
            }
            i += 1;
        }
        t += 1;
    }
}

/// **Card 9's kill gate: if the short rows move < 5%, the pass structure was
/// not the cost.** The `i64` accumulator carries across blocks, as the card's
/// strong form specifies, and is reduced to `Fp` once at the end.
#[test]
#[ignore = "pin-width timing -- run with cargo test --release -- --ignored"]
fn the_gather_form_against_its_kill_gate() {
    use hachi::linalg::RawVec32;
    use hachi::params::{GADGET_DIGITS, MESSAGE_ROWS, OMEGA, Q, RING_DEGREE};
    let blocks: usize = std::env::var("HACHI_T17_BLOCKS")
        .ok().and_then(|v| v.parse().ok()).unwrap_or(2);
    let mut r = Lcg::new(0xC0A1_0090);
    let width = MESSAGE_ROWS * GADGET_DIGITS;
    let raw: Vec<RawVec32> =
        (0..blocks).map(|_| RawVec32::compact(&r.next_poly_vec(MESSAGE_ROWS))).collect();
    let c = PolyVec::new((0..blocks).map(|i| short_challenge_rq(i, OMEGA, 1)).collect());
    let digits: Vec<PolyVec> =
        raw.iter().map(|b| hachi::gadget::gadget_decompose(&b.expand())).collect();

    // --- the scatter, as the crate has it ---
    let t0 = std::time::Instant::now();
    let mut acc_s: Vec<Rq> = (0..width).map(|_| Rq::zero()).collect();
    for (i, s) in digits.iter().enumerate() {
        let desc = hachi::ring::classify_short(c.get(i)).expect("weight-16 challenge is short");
        for j in 0..width {
            hachi::ring::mul_short_add_into(&desc, s.get(j), &mut acc_s[j]);
        }
    }
    let d_scatter = t0.elapsed();

    // --- the gather, i64 accumulators carried across blocks ---
    let t1 = std::time::Instant::now();
    let mut acc_g: Vec<Vec<i64>> = (0..width).map(|_| vec![0i64; RING_DEGREE]).collect();
    for (i, s) in digits.iter().enumerate() {
        let d = classify_here(c.get(i)).expect("weight-16 challenge is short");
        for j in 0..width {
            mul_short_add_into_gather(&d, s.get(j), &mut acc_g[j]);
        }
    }
    // one reduction per coefficient, at the end
    let q = Q as i64;
    let mut out_g: Vec<Rq> = Vec::with_capacity(width);
    for a in acc_g.iter() {
        let mut coeffs: Vec<cpoly::field::Fp> = Vec::with_capacity(RING_DEGREE);
        for &v in a.iter() {
            let m = v % q;
            coeffs.push(cpoly::field::Fp::new(if m < 0 { (m + q) as u64 } else { m as u64 }));
        }
        out_g.push(Rq::from_coeffs(&coeffs));
    }
    let d_gather = t1.elapsed();

    for j in 0..width {
        assert!(out_g[j].equals(&acc_s[j]), "the gather differs from the scatter at {j}");
    }

    // --- the scatter, with an i64 accumulator: the OTHER half of card 9 ---
    let t2 = std::time::Instant::now();
    let mut acc_i: Vec<Vec<i64>> = (0..width).map(|_| vec![0i64; RING_DEGREE]).collect();
    for (i, s) in digits.iter().enumerate() {
        let d = classify_here(c.get(i)).expect("weight-16 challenge is short");
        for j in 0..width {
            mul_short_add_into_i64(&d, s.get(j), &mut acc_i[j]);
        }
    }
    let mut out_i: Vec<Rq> = Vec::with_capacity(width);
    for a in acc_i.iter() {
        let mut coeffs: Vec<cpoly::field::Fp> = Vec::with_capacity(RING_DEGREE);
        for &v in a.iter() {
            let m = v % q;
            coeffs.push(cpoly::field::Fp::new(if m < 0 { (m + q) as u64 } else { m as u64 }));
        }
        out_i.push(Rq::from_coeffs(&coeffs));
    }
    let d_scatter_i64 = t2.elapsed();
    for j in 0..width {
        assert!(out_i[j].equals(&acc_s[j]), "the i64 scatter differs from the scatter at {j}");
    }
    eprintln!(
        "[t17] scatter+i64 {:>8.2?} ({:>6.2} ns/coeff)  {:+.1}%   <-- the accumulator alone",
        d_scatter_i64,
        d_scatter_i64.as_nanos() as f64 / (width * RING_DEGREE * blocks) as f64,
        100.0 * (d_scatter_i64.as_secs_f64() / d_scatter.as_secs_f64() - 1.0)
    );
    let coeffs = (width * RING_DEGREE * blocks) as f64;
    eprintln!(
        "[t17] scatter {:>8.2?} ({:>6.2} ns/coeff)   gather {:>8.2?} ({:>6.2} ns/coeff)   {:+.1}%",
        d_scatter, d_scatter.as_nanos() as f64 / coeffs,
        d_gather, d_gather.as_nanos() as f64 / coeffs,
        100.0 * (d_gather.as_secs_f64() / d_scatter.as_secs_f64() - 1.0)
    );
    eprintln!("[t17] the gather agrees with the scatter on all {width} outputs");
    eprintln!("[t17] kill gate: reject if the short path moves < 5%");
}

// ---------------------------------------------------------------------------
// Card 10 / T1a: the lift's high half, prototyped before it is proved
// ---------------------------------------------------------------------------
//
// The lifted witness is 70.6 s at the pin, 5.9% of the prover, and it is
// essentially all `c_row_sum`: five rows, each a sum of `long_mul`s over the
// nonzero entries of `M`, at `O(N^2)` per product.
//
// `div_by_modulus` reads ONLY the high half. Its loop is
// `quot[k] = rem[k + n]` for `k` from `n-2` down to 0; the leads run over
// `[n, 2n-2]` and the writes it makes (`rem[k] -= c`) all land below `n`, so
// the two ranges never meet. `c_quotient` subtracts `y` from the low half
// only. So the quotient IS the high half of the product sum, with no
// adjustment at all -- and the low half of every `long_mul`, which is half the
// schoolbook work, is computed and discarded.

/// `c_quotient`'s value, computing only the half of each product that survives.
fn c_quotient_high_half(m_row: &PolyVec, z: &PolyVec, cols: usize) -> Vec<cpoly::field::Fp> {
    let n = hachi::params::RING_DEGREE;
    let mut hi: Vec<cpoly::field::Fp> = vec![cpoly::field::Fp::new(0); n];
    let mut j = 0usize;
    while j < cols {
        let a = m_row.get(j);
        if !a.is_zero() {
            let b = z.get(j);
            // coefficients n ..= 2n-2 of a*b, which are quot[0 ..= n-2]
            let mut t = n;
            while t < 2 * n - 1 {
                let mut acc = cpoly::field::Fp::new(0);
                let mut u = t - n + 1; // u + v = t with both < n
                while u < n {
                    acc = acc + a.coeff(u) * b.coeff(t - u);
                    u += 1;
                }
                hi[t - n] = hi[t - n] + acc;
                t += 1;
            }
        }
        j += 1;
    }
    hi
}


/// The same value, traversed the way `long_mul` traverses: `u` ascending, `v`
/// ascending, writing only where `u + v >= n`. Same triangle, natural order.
fn c_quotient_high_half_v2(m_row: &PolyVec, z: &PolyVec, cols: usize) -> Vec<cpoly::field::Fp> {
    let n = hachi::params::RING_DEGREE;
    let mut hi: Vec<cpoly::field::Fp> = vec![cpoly::field::Fp::new(0); n];
    let mut j = 0usize;
    while j < cols {
        let a = m_row.get(j);
        if !a.is_zero() {
            let b = z.get(j);
            let mut u = 1usize; // u = 0 contributes nothing to the high half
            while u < n {
                let au = a.coeff(u);
                if au.to_u64() != 0 {
                    let mut v = n - u;
                    while v < n {
                        hi[u + v - n] = hi[u + v - n] + au * b.coeff(v);
                        v += 1;
                    }
                }
                u += 1;
            }
        }
        j += 1;
    }
    hi
}


/// The FAIR high-half prototype: `long_mul`'s own shape -- the antidiagonal
/// with a `u128` register accumulator and one reduction per output
/// coefficient -- restricted to the half that survives `div_by_modulus`.
///
/// The first two attempts here were not fair and are kept in the history as
/// the mistake they were: they accumulated in `Fp`, paying a modular reduction
/// per term, and so compared half the products with a reduction each against
/// all the products with one reduction per output. That is a comparison of
/// accumulator strategies, not of triangles.
fn c_quotient_high_half_v3(m_row: &PolyVec, z: &PolyVec, cols: usize) -> Vec<cpoly::field::Fp> {
    let n = hachi::params::RING_DEGREE;
    let q = hachi::params::Q as u128;
    let mut hi: Vec<cpoly::field::Fp> = vec![cpoly::field::Fp::new(0); n];
    let mut j = 0usize;
    while j < cols {
        let a = m_row.get(j);
        if !a.is_zero() {
            let b = z.get(j);
            let mut k = n;
            while k < 2 * n - 1 {
                let lo = k + 1 - n;
                let mut acc: u128 = 0;
                let mut i = lo;
                while i < n {
                    acc += (a.coeff(i).to_u64() as u128) * (b.coeff(k - i).to_u64() as u128);
                    i += 1;
                }
                hi[k - n] = hi[k - n] + cpoly::field::Fp::new((acc % q) as u64);
                k += 1;
            }
        }
        j += 1;
    }
    hi
}

/// **Card 10's price, measured rather than counted.**
#[test]
#[ignore = "pin-width timing -- run with cargo test --release -- --ignored"]
fn the_lift_high_half_against_the_full_product() {
    use hachi::ringswitch::{c_quotient, RlinStatement};
    let cols: usize = std::env::var("HACHI_T1_COLS")
        .ok().and_then(|v| v.parse().ok()).unwrap_or(2048);
    let mut r = Lcg::new(0xC0A1_00A0);
    // a row with the sparsity `rlin_stmt` actually produces: 43% nonzero
    let mut entries: Vec<Rq> = Vec::with_capacity(cols);
    for j in 0..cols {
        entries.push(if j % 100 < 43 { r.next_poly_vec(1).get(0).copy() } else { Rq::zero() });
    }
    let m_row = PolyVec::new(entries);
    let z = r.next_poly_vec(cols);
    let yv = PolyVec::new(vec![Rq::zero()]);
    let s = RlinStatement::new(PolyMatrix::new(vec![m_row.copy()]), yv, 15);

    let t0 = std::time::Instant::now();
    let want = c_quotient(&s, &z, 0);
    let d_full = t0.elapsed();

    let t1 = std::time::Instant::now();
    let got = c_quotient_high_half(&m_row, &z, cols);
    let d_half = t1.elapsed();

    let n = hachi::params::RING_DEGREE;
    for k in 0..n - 1 {
        assert!(
            got[k].to_u64() == want.coeff(k).to_u64(),
            "the high-half lift differs from c_quotient at {k}"
        );
    }
    let t2 = std::time::Instant::now();
    let got2 = c_quotient_high_half_v2(&m_row, &z, cols);
    let d_half2 = t2.elapsed();
    for k in 0..n - 1 {
        assert!(got2[k].to_u64() == want.coeff(k).to_u64(), "v2 differs at {k}");
    }
    let t3 = std::time::Instant::now();
    let got3 = c_quotient_high_half_v3(&m_row, &z, cols);
    let d_half3 = t3.elapsed();
    for k in 0..n - 1 {
        assert!(got3[k].to_u64() == want.coeff(k).to_u64(), "v3 differs at {k}");
    }
    eprintln!("[t1a] v3 (fair: u128 accumulator, as long_mul does) {:>8.2?} ({:+.1}%)",
        d_half3, 100.0 * (d_half3.as_secs_f64() / d_full.as_secs_f64() - 1.0));
    eprintln!(
        "[t1a] cols = {cols} (43% nonzero)   full {:>8.2?}   high half {:>8.2?} ({:+.1}%)   v2 {:>8.2?} ({:+.1}%)",
        d_full, d_half,
        100.0 * (d_half.as_secs_f64() / d_full.as_secs_f64() - 1.0),
        d_half2,
        100.0 * (d_half2.as_secs_f64() / d_full.as_secs_f64() - 1.0)
    );
    eprintln!("[t1a] the high half agrees with c_quotient on every quotient coefficient");
}

/// **The rounds, split per phase** — the one block of the prover nobody had
/// looked inside.
///
/// `honest_round_messages` is 214 s at the pin, 18% of the prover, and it was
/// deferred by instruction (the goal's 25% rule) rather than by measurement.
/// This is card 6's method applied to it: replay the loop body verbatim and
/// clock each piece. The work halves every round — round 0 walks `2^m₀`
/// entries, round 1 walks `2^(m₀−1)` — so the totals are dominated by the
/// first few, and the per-round numbers are printed for the first five.
#[test]
#[ignore = "pin-width timing, several minutes -- run with cargo test --release -- --ignored"]
fn the_rounds_split_per_phase() {
    let blocks: usize = std::env::var("HACHI_CHAIN_BLOCKS")
        .ok().and_then(|v| v.parse().ok()).unwrap_or(1024);
    let t0 = std::time::Instant::now();
    let inst = pin_instance(blocks, &t0, false);
    let stmt = hachi::quadeval::to_quad_eval_statement(&inst.poly_stmt);
    let m0 = hachi::params::M_ZERO;
    let rlin = hachi::quadeval::rlin_stmt(
        &inst.pp, &stmt, &inst.v, &inst.c, CHAIN_GAMMA, blocks,
        hachi::params::MESSAGE_ROWS, hachi::params::GADGET_DIGITS,
        hachi::params::INNER_ROWS, hachi::params::GADGET_DIGITS,
        hachi::params::Z_DIGITS,
    );
    let t = hachi::ringswitch::lift_commit(&inst.d_key, &inst.w);
    let zc = hachi::sumcheck::NestedZeroCheckStmt::new(
        rlin, t.copy(), inst.alpha, inst.tau0.clone(), inst.tau1.clone(),
    );
    let opened = hachi::sumcheck::nested_to_round_statement(zc);

    // setup, outside the loop
    let s0 = std::time::Instant::now();
    let mut low = hachi::sumcheck::alpha_split_low(opened.zc().alpha(), m0);
    let d_low = s0.elapsed();
    let s1 = std::time::Instant::now();
    let mut high = hachi::sumcheck::alpha_split_high(
        opened.zc().rlin(), opened.zc().alpha(), opened.zc().tau1(), m0);
    let d_high = s1.elapsed();
    let s2 = std::time::Instant::now();
    let w_fp = hachi::zerocheck::c_w_table_fp(&inst.w, m0);
    let d_wfp = s2.elapsed();

    let mut current = opened;
    let (mut t_g, mut t_out, mut t_mle, mut t_fold) = (
        std::time::Duration::ZERO, std::time::Duration::ZERO,
        std::time::Duration::ZERO, std::time::Duration::ZERO);

    let a0 = inst.challenges[0];
    let c0 = std::time::Instant::now();
    let g0 = hachi::sumcheck::honest_compute_g_base_split(&current, &w_fp, &low, &high);
    t_g += c0.elapsed();
    let c1 = std::time::Instant::now();
    current = hachi::sumcheck::round_out(current, &g0, a0);
    t_out += c1.elapsed();
    let c2 = std::time::Instant::now();
    let mut w_tab = hachi::sumcheck::eval_mle_layer_base(&w_fp, a0);
    t_mle += c2.elapsed();
    let c3 = std::time::Instant::now();
    let f0 = hachi::sumcheck::alpha_split_fold(low, high, a0);
    t_fold += c3.elapsed();
    low = f0.0; high = f0.1;
    eprintln!("[rounds] round  0: g {:>8.2?}  out {:>8.2?}  mle {:>8.2?}  fold {:>8.2?}",
        c0.elapsed(), c1.elapsed(), c2.elapsed(), c3.elapsed());

    for i in 1..m0 {
        let a = inst.challenges[i];
        let b0 = std::time::Instant::now();
        let g = hachi::sumcheck::honest_compute_g_split(&current, &w_tab, &low, &high, i);
        let dg = b0.elapsed(); t_g += dg;
        let b1 = std::time::Instant::now();
        current = hachi::sumcheck::round_out(current, &g, a);
        let dout = b1.elapsed(); t_out += dout;
        let b2 = std::time::Instant::now();
        w_tab = cpoly::multilinear::eval_mle_layer(&w_tab, a);
        let dmle = b2.elapsed(); t_mle += dmle;
        let b3 = std::time::Instant::now();
        let f = hachi::sumcheck::alpha_split_fold(low, high, a);
        let dfold = b3.elapsed(); t_fold += dfold;
        low = f.0; high = f.1;
        if i < 5 {
            eprintln!("[rounds] round {i:2}: g {dg:>8.2?}  out {dout:>8.2?}  mle {dmle:>8.2?}  fold {dfold:>8.2?}");
        }
    }

    let tot = t_g + t_out + t_mle + t_fold;
    eprintln!("[rounds] setup: alpha_split_low {d_low:>8.2?}  alpha_split_high {d_high:>8.2?}  c_w_table_fp {d_wfp:>8.2?}");
    for (name, d) in [("honest_compute_g", t_g), ("round_out", t_out),
                      ("eval_mle_layer", t_mle), ("alpha_split_fold", t_fold)] {
        eprintln!("[rounds]   {name:20} {:>9.2?}   {:>5.1}%", d,
            100.0 * d.as_secs_f64() / tot.as_secs_f64());
    }
    eprintln!("[rounds]   {:20} {tot:>9.2?}", "LOOP TOTAL");
}
