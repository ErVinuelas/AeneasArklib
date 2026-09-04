//! Wall-clock time for the ring-switching digit layer.
//!
//! One case, and it is the whole module: [`rho_digits`] is a single coefficient
//! loop of `RING_DEGREE = 1024` balanced digits followed by one
//! `Rq::from_coeffs`. No ring product, no allocation growth beyond the two
//! coefficient vectors -- so the reading is microseconds, not milliseconds, and
//! it is dominated by the same thing the balanced gadget layer is: modular
//! reduction by `P`, five per digit in the first translation
//! (two constant `Fp::new`s, the shift add, `digit_at`'s own `Fp::new`, the
//! recentring subtract), against the unsigned path's one.
//!
//! # Size, and why the digit index is `0`
//!
//! `RING_DEGREE` is the only size there is: the loop runs over the row's
//! coefficients, and the digit index `u` is a parameter to each of them.
//! Unlike `gadget/digit_at`, the deepest index is **not** the row worth having
//! here -- the per-index division chain is `digit_at`'s cost and is already
//! measured there, while what this case is for is the coefficient loop and the
//! `Rq` construction around it. Measuring at `u = 0` keeps the division chain
//! out of the reading; a row at `u = GADGET_DIGITS - 1` would differ from this
//! one by exactly `RING_DEGREE · (digits - 1)` shifts, which `gadget/digit_at`
//! already prices.
//!
//! See `benches/support/mod.rs` for the corpus discipline, the digest oracle and
//! what the `_control` case is.

mod support;

use criterion::{criterion_group, criterion_main, Criterion};

/// One body per case, instantiated once per variant crate. Writing the variants
/// separately is how a benchmark quietly starts comparing two different
/// computations; a macro makes that impossible.
macro_rules! define_cases {
    ($modname:ident, $hachi:path) => {
        mod $modname {
            use std::hint::black_box;

            use $hachi as hc;

            use crate::support::{self, Mode};

            type Rq = hc::ring::Rq;
            type PolyVec = hc::linalg::PolyVec;

            // -- corpus -----------------------------------------------------

            /// The quotient row the case decomposes. One draw from its own
            /// stream, so every variant sees the same row.
            fn row() -> Rq {
                let degree = hc::params::RING_DEGREE;
                Rq::from_coeffs(&support::corpus(0x8047_0000_0000_0001, degree))
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

            // -- the reconstruction check -----------------------------------

            /// `Σ_u bᵘ · rho_digits(ρ, u) = ρ`, asserted before anything is
            /// timed -- the specification's `rhoDigits_reconstruct`. A timing of
            /// a digit map that does not reconstruct would be meaningless, and
            /// this is what makes it a real check that the frozen and slot
            /// copies were copied rather than paraphrased.
            pub fn check() {
                let digits = hc::params::GADGET_DIGITS;
                let rho = row();
                let mut acc = Rq::zero();
                let mut u = 0usize;
                while u < digits {
                    acc = acc.add(&hc::ringswitch::rho_digits(&rho, u).scalar_mul(
                        hc::gadget::base_pow(u),
                    ));
                    u += 1;
                }
                assert!(
                    acc.equals(&rho),
                    "the quotient digits do not reconstruct the row; a timing of them \
                     would be meaningless"
                );
            }

            // -- the case ---------------------------------------------------

            /// One digit of one quotient row: `degree` balanced digits and one
            /// `Rq::from_coeffs`. See the module doc for why the digit index is
            /// `0` and not the deepest one.
            pub fn rho_digits(m: Mode<'_, '_>, _degree: usize) -> u64 {
                let rho = row();
                support::run(
                    m,
                    || hc::ringswitch::rho_digits(black_box(&rho), black_box(0)),
                    d_rq,
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

fn ringswitch_benches(c: &mut Criterion) {
    now::check();
    genesis::check();
    #[cfg(feature = "candidate")]
    candidate::check();

    // The run's sanity check: identical source in every variant, so anything it
    // reads is the harness disagreeing with itself. Runs first, while the machine
    // is in the same state the first real cases will see.
    bench_case!(c, "_control/ringswitch", control, [support::CONTROL_N]);

    let degree = hachi::params::RING_DEGREE;

    // @covers ringswitch::rho_digits
    bench_case!(c, "ringswitch/rho_digits", rho_digits, [degree]);
}

criterion_group! {
    name = benches;
    config = support::criterion_config();
    targets = ringswitch_benches
}
criterion_main!(benches);
