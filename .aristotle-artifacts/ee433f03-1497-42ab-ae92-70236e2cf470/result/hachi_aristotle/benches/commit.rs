//! Wall-clock time for the commitment itself, end to end.
//!
//! These are the only readings in the repository that correspond to something a
//! user of the scheme would wait for: `commit` (decompose, inner-commit,
//! decompose again, outer-commit), `verify_weak` (per-block norms and gadget
//! relation, then the outer product) and `verify` (`verify_weak` plus the derived
//! message check). Everything else timed here is one of their parts, present so
//! that a change in the total can be attributed.
//!
//! All three are dominated by `linalg::mat_vec_mul` and so by `ring::mul`: at
//! these dimensions a single commit does `BLOCKS · (INNER_ROWS · MESSAGE_ROWS ·
//! GADGET_DIGITS) + OUTER_ROWS · (BLOCKS · INNER_ROWS · GADGET_DIGITS)` ring
//! products. The norms are `O(coefficients)` and should be invisible next to
//! that -- if a `norm` case ever becomes comparable to `commit`, the ring product
//! got much faster or a norm got much slower.
//!
//! # Sizes
//!
//! Three families, each the dimension its operation actually loops over:
//!
//! * `RING_DEGREE = 64` for the three element-level norms, which walk one ring
//!   element's coefficients.
//! * `MESSAGE_ROWS · GADGET_DIGITS = 128` for the two vector lifts, which walk a
//!   decomposed message block.
//! * `BLOCKS = 2` for everything scheme-level. Every other dimension of those
//!   rows -- the two matrix shapes, the message width -- is taken from the
//!   variant's own `params`, because they are `A` and `B` and not knobs. The
//!   outer matrix's width is derived from the parameter (`blocks · (INNER_ROWS ·
//!   GADGET_DIGITS)`), so the shape stays consistent if the row is ever measured
//!   at a second block count.
//!
//! # Sampling
//!
//! This binary overrides `support::criterion_config`, and it is the only one that
//! does; the override and its reason sit at `criterion_group!` below.
//!
//! See `benches/support/mod.rs` for the corpus discipline, the digest oracle and
//! what the `_control` case is.

mod support;

use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};

/// One body per case, instantiated once per variant crate. Writing the variants
/// separately is how a benchmark quietly starts comparing two different
/// computations; a macro makes that impossible.
macro_rules! define_cases {
    ($modname:ident, $hachi:path) => {
        mod $modname {
            // `support::run`'s digest argument is `Fn(&R) -> u64`, so a digest of
            // a `Copy` scalar has to take it by reference. That is the bound's
            // shape, not a choice this file makes.
            #![allow(clippy::trivially_copy_pass_by_ref)]

            use std::hint::black_box;

            use $hachi as hc;

            use crate::support::{self, Mode};

            type Rq = hc::ring::Rq;
            type PolyVec = hc::linalg::PolyVec;
            type PolyMatrix = hc::linalg::PolyMatrix;
            type Decomp = hc::commit::Decomp;
            type Opening = hc::commit::Opening;
            type PublicParams = hc::commit::PublicParams;

            // -- corpus -----------------------------------------------------

            fn vec_of(seed: u64, k: usize) -> PolyVec {
                let degree = hc::params::RING_DEGREE;
                let mut entries = Vec::with_capacity(k);
                for i in 0..k {
                    entries.push(Rq::from_coeffs(&support::corpus(
                        seed.wrapping_add(i as u64 * 0x100),
                        degree,
                    )));
                }
                PolyVec::new(entries)
            }

            fn matrix_of(seed: u64, rows: usize, cols: usize) -> PolyMatrix {
                let mut out = Vec::with_capacity(rows);
                for i in 0..rows {
                    out.push(vec_of(seed.wrapping_add(i as u64 * 0x10000), cols));
                }
                PolyMatrix::new(out)
            }

            /// `A` and `B` at the scheme's shapes, for `blocks` message blocks.
            ///
            /// `A` is `INNER_ROWS × (MESSAGE_ROWS · GADGET_DIGITS)` and `B` is
            /// `OUTER_ROWS × (blocks · (INNER_ROWS · GADGET_DIGITS))`; the second
            /// width is the only one the case parameter reaches, because it is the
            /// only one that depends on the block count.
            fn public_params(blocks: usize) -> PublicParams {
                let digits = hc::params::GADGET_DIGITS;
                let inner = hc::params::INNER_ROWS;
                PublicParams::new(
                    matrix_of(0x2A00_0000, inner, hc::params::MESSAGE_ROWS * digits),
                    matrix_of(0x2B00_0000, hc::params::OUTER_ROWS, blocks * (inner * digits)),
                )
            }

            fn message(blocks: usize) -> Vec<PolyVec> {
                let rows = hc::params::MESSAGE_ROWS;
                let mut m = Vec::with_capacity(blocks);
                for b in 0..blocks {
                    m.push(vec_of(0x2C00_0000 + b as u64, rows));
                }
                m
            }

            /// One ring element of `n` coefficients, for the element-level norms.
            ///
            /// The first entry of the `0x2D00_0000` vector, which is what the
            /// vector-lift rows walk -- so the element rows and the vector rows
            /// are looking at the same numbers.
            fn single(n: usize) -> Rq {
                Rq::from_coeffs(&support::corpus(0x2D00_0000, n))
            }

            // -- digests (outside every timed region) -----------------------

            fn d_rq(a: &Rq) -> u64 {
                let n = a.len();
                let mut acc = support::mix_len(0, n);
                let mut k = 0usize;
                while k < n {
                    acc = support::mix(acc, a.coeff(k).to_u64());
                    k += 1;
                }
                acc
            }

            fn d_polyvec(v: &PolyVec) -> u64 {
                let k = v.len();
                let mut acc = support::mix_len(0, k);
                let mut i = 0usize;
                while i < k {
                    acc = support::mix(acc, d_rq(v.get(i)));
                    i += 1;
                }
                acc
            }

            fn d_polyvecs(v: &Vec<PolyVec>) -> u64 {
                let mut acc = support::mix_len(0, v.len());
                let mut i = 0usize;
                while i < v.len() {
                    acc = support::mix(acc, d_polyvec(&v[i]));
                    i += 1;
                }
                acc
            }

            /// Both halves of the decomposition, block count first. `sᵢ` and `t̂ᵢ`
            /// are folded in separate passes so a `generate_decomps` that swapped
            /// them could not collide with a correct result.
            fn d_decomp(d: &Decomp) -> u64 {
                let b = d.blocks();
                let mut acc = support::mix_len(0, b);
                let mut i = 0usize;
                while i < b {
                    acc = support::mix(acc, d_polyvec(d.message(i)));
                    i += 1;
                }
                let mut i = 0usize;
                while i < b {
                    acc = support::mix(acc, d_polyvec(d.inner_decomp(i)));
                    i += 1;
                }
                acc
            }

            fn d_commit(x: &(PolyVec, Decomp)) -> u64 {
                support::mix(d_polyvec(&x.0), d_decomp(&x.1))
            }

            fn d_u64(x: &u64) -> u64 {
                support::mix(0, *x)
            }

            fn d_u128(x: &u128) -> u64 {
                support::mix_u128(0, *x)
            }

            fn d_bool(x: &bool) -> u64 {
                support::mix(0, u64::from(*x))
            }

            // -- perfect correctness ----------------------------------------

            /// An honest opening verifies, asserted before anything is timed.
            ///
            /// Timing a verifier that rejects measures the rejection path, which
            /// is not what the case claims to measure -- and `verify_weak` has no
            /// short circuit, so a rejecting run would look plausible. Called for
            /// every variant, which is what makes it a real check that the frozen
            /// and slot copies were copied and not paraphrased.
            pub fn check() {
                let blocks = hc::params::BLOCKS;
                let pp = public_params(blocks);
                let m = message(blocks);
                let (u, _) = hc::commit::commit(&pp, &m);
                let opening = Opening::honest(hc::commit::generate_decomps(&pp, &m));
                assert!(
                    hc::commit::verify_weak(&pp, &u, &opening),
                    "an honest opening does not verify; a timing of it would be meaningless"
                );
            }

            // -- norms --------------------------------------------------------

            pub fn l1_norm(m: Mode<'_, '_>, n: usize) -> u64 {
                let a = single(n);
                support::run(m, || hc::commit::l1_norm(black_box(&a)), d_u64)
            }

            pub fn l2_norm_sq(m: Mode<'_, '_>, n: usize) -> u64 {
                let a = single(n);
                support::run(m, || hc::commit::l2_norm_sq(black_box(&a)), d_u128)
            }

            /// The element-level `ℓ∞`, reached in the scheme only through
            /// [`vec_l_infty_norm`]. A row of its own because a `max` loop and a
            /// `sum` loop are different code with different vectorization
            /// prospects, and the lift cannot tell you which of the two moved.
            pub fn l_infty_norm(m: Mode<'_, '_>, n: usize) -> u64 {
                let a = single(n);
                support::run(m, || hc::commit::l_infty_norm(black_box(&a)), d_u64)
            }

            pub fn vec_l2_norm_sq(m: Mode<'_, '_>, k: usize) -> u64 {
                let v = vec_of(0x2D00_0000, k);
                support::run(m, || hc::commit::vec_l2_norm_sq(black_box(&v)), d_u128)
            }

            pub fn vec_l_infty_norm(m: Mode<'_, '_>, k: usize) -> u64 {
                let v = vec_of(0x2D00_0000, k);
                support::run(m, || hc::commit::vec_l_infty_norm(black_box(&v)), d_u64)
            }

            // -- commit -------------------------------------------------------

            pub fn generate_decomps(m: Mode<'_, '_>, blocks: usize) -> u64 {
                let pp = public_params(blocks);
                let msg = message(blocks);
                support::run(
                    m,
                    || hc::commit::generate_decomps(black_box(&pp), black_box(&msg)),
                    d_decomp,
                )
            }

            pub fn commit_with_decomps(m: Mode<'_, '_>, blocks: usize) -> u64 {
                let pp = public_params(blocks);
                let (_, decomp) = hc::commit::commit(&pp, &message(blocks));
                support::run(
                    m,
                    || hc::commit::commit_with_decomps(black_box(&pp), black_box(&decomp)),
                    d_polyvec,
                )
            }

            pub fn derived_message(m: Mode<'_, '_>, blocks: usize) -> u64 {
                let pp = public_params(blocks);
                let (_, decomp) = hc::commit::commit(&pp, &message(blocks));
                support::run(
                    m,
                    || hc::commit::derived_message(black_box(&decomp)),
                    d_polyvecs,
                )
            }

            /// The whole committer: `generate_decomps` then
            /// `commit_with_decomps`. The two part rows above it are what a change
            /// in this one is attributed to.
            pub fn commit(m: Mode<'_, '_>, blocks: usize) -> u64 {
                let pp = public_params(blocks);
                let msg = message(blocks);
                support::run(
                    m,
                    || hc::commit::commit(black_box(&pp), black_box(&msg)),
                    d_commit,
                )
            }

            // -- verify -------------------------------------------------------

            pub fn verify_weak(m: Mode<'_, '_>, blocks: usize) -> u64 {
                let pp = public_params(blocks);
                let msg = message(blocks);
                let (u, _) = hc::commit::commit(&pp, &msg);
                let opening = Opening::honest(hc::commit::generate_decomps(&pp, &msg));
                support::run(
                    m,
                    || {
                        hc::commit::verify_weak(
                            black_box(&pp),
                            black_box(&u),
                            black_box(&opening),
                        )
                    },
                    d_bool,
                )
            }

            /// `verify_weak` plus the derived-message check, i.e. the most
            /// expensive single call in the crate. Measured on an honest opening,
            /// so it takes the accepting path all the way through -- there is no
            /// short circuit, but a rejecting input would still change which
            /// comparisons run.
            pub fn verify(m: Mode<'_, '_>, blocks: usize) -> u64 {
                let pp = public_params(blocks);
                let msg = message(blocks);
                let (u, _) = hc::commit::commit(&pp, &msg);
                let opening = Opening::honest(hc::commit::generate_decomps(&pp, &msg));
                support::run(
                    m,
                    || {
                        hc::commit::verify(
                            black_box(&pp),
                            black_box(&msg),
                            black_box(&u),
                            black_box(&opening),
                        )
                    },
                    d_bool,
                )
            }

            // -- the A/B fairness control -----------------------------------

            /// The harness's A/B fairness control. Every variant of this case runs
            /// its own compiled copy of the *same source*, so any difference the
            /// report shows for it is measurement bias -- timing order, machine
            /// drift and code layout -- and not code. See
            /// `support/mod.rs` § "The A/B fairness control" for why the body is a
            /// variant-crate operation rather than a bench-crate symbol, and for
            /// what that costs.
            pub fn control(m: Mode<'_, '_>, n: usize) -> u64 {
                support::run(m, || PolyVec::zeros(black_box(n)), d_polyvec)
            }
        }
    };
}

define_cases!(now, hachi);
define_cases!(genesis, hachi_genesis);
#[cfg(feature = "candidate")]
define_cases!(candidate, hachi_candidate);

fn commit_benches(c: &mut Criterion) {
    now::check();
    genesis::check();
    #[cfg(feature = "candidate")]
    candidate::check();

    // The run's sanity check: identical source in every variant, so anything it
    // reads is the harness disagreeing with itself. Runs first, while the machine
    // is in the same state the first real cases will see.
    bench_case!(c, "_control/commit", control, [support::CONTROL_N]);

    let degree = hachi::params::RING_DEGREE;
    let width = hachi::params::MESSAGE_ROWS * hachi::params::GADGET_DIGITS;
    let blocks = hachi::params::BLOCKS;

    // @covers commit::l1_norm
    bench_case!(c, "commit/l1_norm", l1_norm, [degree]);
    // @covers commit::l2_norm_sq
    bench_case!(c, "commit/l2_norm_sq", l2_norm_sq, [degree]);
    // @covers commit::l_infty_norm
    bench_case!(c, "commit/l_infty_norm", l_infty_norm, [degree]);
    // @covers commit::vec_l2_norm_sq
    bench_case!(c, "commit/vec_l2_norm_sq", vec_l2_norm_sq, [width]);
    // @covers commit::vec_l_infty_norm
    bench_case!(c, "commit/vec_l_infty_norm", vec_l_infty_norm, [width]);

    // @covers commit::generate_decomps
    bench_case!(c, "commit/generate_decomps", generate_decomps, [blocks]);
    // @covers commit::commit_with_decomps
    bench_case!(c, "commit/commit_with_decomps", commit_with_decomps, [blocks]);
    // @covers commit::derived_message
    bench_case!(c, "commit/derived_message", derived_message, [blocks]);
    // @covers commit::commit
    bench_case!(c, "commit/commit", commit, [blocks]);

    // @covers commit::verify_weak
    bench_case!(c, "commit/verify_weak", verify_weak, [blocks]);
    // @covers commit::verify
    bench_case!(c, "commit/verify", verify, [blocks]);
}

criterion_group! {
    // The only per-binary override of `support::criterion_config`, and it is
    // arithmetic rather than taste. Criterion samples linearly: 100 samples cost
    // `100·101/2 = 5050` executions of the routine. `commit` and `verify` are
    // milliseconds here, so 100 samples would need ~30s per variant per row and
    // the binary would run for half an hour. 50 samples is 1275 executions, which
    // fits the 10s window with the same statistics criterion's intervals assume,
    // just fewer of them.
    //
    // Nothing else changes: the warm-up and the noise threshold stay as
    // `support::criterion_config` sets them, so the only difference between this
    // binary and the other three is how many samples the estimate rests on.
    name = benches;
    config = support::criterion_config()
        .sample_size(50)
        .measurement_time(Duration::from_secs(10));
    targets = commit_benches
}
criterion_main!(benches);
