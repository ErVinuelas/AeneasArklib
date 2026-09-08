//! `src/sumcheck.rs`: the round message in folded-table value form.
//!
//! # Read a `vs genesis` figure here differently from every other binary
//!
//! `benches/genesis` holds the **dense** form for this module, by decision
//! (NOTES.md § "Decision: target 5's genesis holds the dense form"). Everywhere
//! else in this harness, `vs genesis` is distance from the specification's
//! trivial shape; **here it is distance from the dense form**, because the
//! trivial shape does not run at any width that resembles the operation. A
//! ledger row citing a number from this file has to say so.
//!
//! What is still measurable against this baseline, and deliberately left for
//! `perf-loop`: `range_product` in its literal 31-multiply form against the
//! `v² - j²` form's 16 (a 2× cut on the 94%-dominant term), the closed-form
//! `eq̃`, the tensor split of `Ã`, and hoisting the triple `computeG`.
//!
//! # Sizes
//!
//! REDUCED on the cube, real on the node count. The round-0 remaining cube is
//! `2^{m₀-1} = 2^25` points at the pinned `M_ZERO = 26`; these rows run at
//! `2^10`, which keeps the *shape* — a fold pairing `2y`/`2y+1`, then `2b+1`
//! nodes, then interpolation — while fitting a criterion iteration. The node
//! count is **not** reduced: it is `ROUND_NODES = 2b + 1 = 33`, and reducing it
//! would change which polynomial the interpolant is.

mod support;

use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};

// ---------------------------------------------------------------------------
// Sizes
// ---------------------------------------------------------------------------

/// The remaining-cube size the round rows run at: **REDUCED** from `2^25`.
/// `1024` folded pairs, so the `w̃` table is `2048` `Ext4` and the `eq̃`-suffix
/// table `1024`.
const HALF: usize = 1024;

/// One body per case, instantiated once per variant crate.
macro_rules! define_cases {
    ($modname:ident, $hachi:path) => {
        mod $modname {
            #![allow(clippy::trivially_copy_pass_by_ref)]

            use std::hint::black_box;

            use cpoly::{Ext4, Fp, UnivariatePoly};

            use $hachi as hc;

            use crate::support::{self, Mode};

            type PolyVec = hc::linalg::PolyVec;

            // -- corpus -----------------------------------------------------

            fn ext_table(seed: u64, n: usize) -> Vec<Ext4> {
                let c = support::corpus(seed, 4 * n);
                let mut out = Vec::with_capacity(n);
                let mut i = 0usize;
                while i < n {
                    out.push(Ext4::new(c[4 * i], c[4 * i + 1], c[4 * i + 2], c[4 * i + 3]));
                    i += 1;
                }
                out
            }

            // -- digests (outside every timed region) -----------------------

            fn d_ext4(v: &Ext4) -> u64 {
                let mut acc = support::mix(0, v.c0.to_u64());
                acc = support::mix(acc, v.c1.to_u64());
                acc = support::mix(acc, v.c2.to_u64());
                support::mix(acc, v.c3.to_u64())
            }

            fn d_vec(v: &Vec<Ext4>) -> u64 {
                let mut acc = support::mix_len(0, v.len());
                let mut i = 0usize;
                while i < v.len() {
                    acc = support::mix(acc, d_ext4(&v[i]));
                    i += 1;
                }
                acc
            }

            fn d_poly(p: &UnivariatePoly) -> u64 {
                let c = p.coeffs();
                let mut acc = support::mix_len(0, c.len());
                let mut i = 0usize;
                while i < c.len() {
                    acc = support::mix(acc, d_ext4(&c[i]));
                    i += 1;
                }
                acc
            }

            fn d_polyvec(v: &PolyVec) -> u64 {
                let k = v.len();
                let mut acc = support::mix_len(0, k);
                let mut i = 0usize;
                while i < k {
                    let r = v.get(i);
                    let n = r.len();
                    let mut inner = support::mix_len(0, n);
                    let mut j = 0usize;
                    while j < n {
                        inner = support::mix(inner, r.coeff(j).to_u64());
                        j += 1;
                    }
                    acc = support::mix(acc, inner);
                    i += 1;
                }
                acc
            }

            // -- the semantics this binary pins itself ----------------------

            /// Facts the digest oracle cannot supply. The load-bearing one is
            /// the interpolation property: a round message is *represented* by
            /// its node values, so if the interpolant did not reproduce them
            /// the whole representation would be unsound while every timing
            /// stayed plausible.
            pub fn check() {
                let values = ext_table(0x5A17_7000, hc::params::ROUND_NODES);
                let weights = hc::sumcheck::round_node_weights();
                let p = hc::sumcheck::interpolate(&values, &weights);
                let mut i = 0usize;
                while i < values.len() {
                    assert_eq!(
                        p.eval(hc::sumcheck::round_node(i)),
                        values[i],
                        "the interpolant must reproduce node {i}"
                    );
                    i += 1;
                }
                // And the nodes are the specification's: 0 and 1 first, because
                // those are the two `roundCheck` evaluates.
                assert_eq!(hc::sumcheck::round_node(0), Ext4::ZERO);
                assert_eq!(hc::sumcheck::round_node(1), Ext4::from_base(Fp::new(1)));
                assert_eq!(hc::params::ROUND_NODES as u64, 2 * hc::params::GADGET_BASE + 1);
            }

            // -- cases ------------------------------------------------------

            /// Lagrange interpolation at the **real** node count: `33` basis
            /// products of `32` factors each.
            pub fn interpolate(m: Mode<'_, '_>, nodes: usize) -> u64 {
                assert_eq!(nodes, hc::params::ROUND_NODES, "interpolate runs at the real node count");
                let values = ext_table(0x5A17_7001, nodes);
                let weights = hc::sumcheck::round_node_weights();
                support::run(
                    m,
                    || hc::sumcheck::interpolate(black_box(&values), black_box(&weights)),
                    d_poly,
                )
            }

            /// One node of the range summand: the fold plus `HALF`
            /// `range_product`s. The inner loop the whole target is dominated
            /// by.
            pub fn round_value_zero(m: Mode<'_, '_>, half: usize) -> u64 {
                let w = ext_table(0x5A17_7002, 2 * half);
                let eq = ext_table(0x5A17_7003, half);
                let node = hc::sumcheck::round_node(7);
                support::run(
                    m,
                    || {
                        hc::sumcheck::round_value_zero(
                            black_box(&w),
                            black_box(&eq),
                            black_box(node),
                        )
                    },
                    d_ext4,
                )
            }

            /// All `2b + 1` nodes of it: the per-round prover cost, REDUCED on
            /// the cube only.
            pub fn round_values_zero(m: Mode<'_, '_>, half: usize) -> u64 {
                let w = ext_table(0x5A17_7004, 2 * half);
                let eq = ext_table(0x5A17_7005, half);
                support::run(
                    m,
                    || hc::sumcheck::round_values_zero(black_box(&w), black_box(&eq)),
                    d_vec,
                )
            }

            /// The whole round message: node values then interpolation, which
            /// is what a round of the prover actually sends.
            pub fn round_poly_zero(m: Mode<'_, '_>, half: usize) -> u64 {
                let w = ext_table(0x5A17_7006, 2 * half);
                let eq = ext_table(0x5A17_7007, half);
                support::run(
                    m,
                    || hc::sumcheck::round_poly_zero(black_box(&w), black_box(&eq)),
                    d_poly,
                )
            }

            // -- the A/B fairness control -----------------------------------

            /// The harness's A/B fairness control, the same body as every other
            /// binary's so that the controls stay comparable with each other.
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

fn sumcheck_benches(c: &mut Criterion) {
    now::check();
    genesis::check();
    #[cfg(feature = "candidate")]
    candidate::check();

    bench_case!(c, "_control/sumcheck", control, [support::CONTROL_N]);

    // @covers sumcheck::interpolate
    bench_case!(c, "sumcheck/interpolate", interpolate, [hachi::params::ROUND_NODES]);
    // @covers sumcheck::round_value_zero
    bench_case!(c, "sumcheck/round_value_zero", round_value_zero, [HALF]);
    // @covers sumcheck::round_values_zero
    bench_case!(c, "sumcheck/round_values_zero", round_values_zero, [HALF]);
    // @covers sumcheck::round_poly_zero
    bench_case!(c, "sumcheck/round_poly_zero", round_poly_zero, [HALF]);
}

criterion_group! {
    // The same override as `benches/commit.rs` and the other heavy binaries,
    // for the averaging reason: at `HALF = 1024` the `round_values_zero` and
    // `round_poly_zero` rows are tens of milliseconds, where criterion's
    // default linear sampling would refuse the window and flip to flat samples
    // of two iterations -- and `_robust` takes the three fastest of those,
    // which is picking the three luckiest executions in the run.
    name = sumcheck_group;
    config = support::criterion_config()
        .sample_size(50)
        .measurement_time(Duration::from_secs(10));
    targets = sumcheck_benches
}
criterion_main!(sumcheck_group);
