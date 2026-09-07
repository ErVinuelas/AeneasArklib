//! Wall-clock time for the complete ring-switching link.
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
            type PolyMatrix = hc::linalg::PolyMatrix;
            type QuotientRow = hc::ringswitch::QuotientRow;
            type LiftedWitness = hc::ringswitch::LiftedWitness;

            // -- corpus -----------------------------------------------------

            /// The quotient row the case decomposes. One draw from its own
            /// stream, so every variant sees the same row.
            fn row() -> Rq {
                let degree = hc::params::RING_DEGREE;
                Rq::from_coeffs(&support::corpus(0x8047_0000_0000_0001, degree))
            }

            fn quotient_row(seed: u64) -> QuotientRow {
                QuotientRow::new(&support::corpus(seed, hc::params::RING_DEGREE))
            }

            fn quotient_rows(seed: u64, rows: usize) -> Vec<QuotientRow> {
                let mut out = Vec::new();
                let mut i = 0usize;
                while i < rows {
                    out.push(quotient_row(seed.wrapping_add(i as u64)));
                    i += 1;
                }
                out
            }

            fn vec_of(seed: u64, n: usize) -> PolyVec {
                let mut out = Vec::new();
                let width = hc::params::RING_DEGREE;
                let coeffs = support::corpus(seed, n * width);
                let mut i = 0usize;
                while i < n {
                    out.push(Rq::from_coeffs(&coeffs[i * width..(i + 1) * width].to_vec()));
                    i += 1;
                }
                PolyVec::new(out)
            }

            fn matrix_of(seed: u64, rows: usize, cols: usize) -> PolyMatrix {
                let mut out = Vec::new();
                let mut i = 0usize;
                while i < rows {
                    out.push(vec_of(seed.wrapping_add(i as u64), cols));
                    i += 1;
                }
                PolyMatrix::new(out)
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

            fn d_bool(b: &bool) -> u64 {
                u64::from(*b)
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

            /// `rhoAsRq`: copy the quotient polynomial's coefficient
            /// presentation into the ring carrier.
            pub fn rho_as_rq(m: Mode<'_, '_>, _degree: usize) -> u64 {
                let rho = quotient_row(0x8047_0000_0000_0010);
                support::run(m, || rho.to_rq(), d_rq)
            }

            /// One flattened `(row, digit)` entry at the real ring degree.
            pub fn rho_digit_as_rq(m: Mode<'_, '_>, rows: usize) -> u64 {
                let rho = quotient_rows(0x8047_0000_0000_0020, rows);
                let j = rows * hc::params::GADGET_DIGITS - 1;
                support::run(
                    m,
                    || hc::ringswitch::rho_digit_as_rq(black_box(&rho), black_box(j)),
                    d_rq,
                )
            }

            /// W3 REDUCED: the real `z` has 57,344 ring elements (~448 MiB)
            /// and materializing its copy makes the peak ~896 MiB. Removal
            /// condition: a fused/streaming lift commitment, not faster ring
            /// multiplication and not a smaller sumcheck cube.
            pub fn lift_message(m: Mode<'_, '_>, z_len: usize) -> u64 {
                let w = LiftedWitness::new(
                    vec_of(0x8047_0000_0000_0030, z_len),
                    quotient_rows(0x8047_0000_0000_0040, 2),
                );
                support::run(m, || hc::ringswitch::lift_message(black_box(&w)), d_polyvec)
            }

            /// W1 REDUCED: the real key is `1 × 57,384`, hence 57,384
            /// schoolbook ring products (~6.02e10 field operations). Removal
            /// condition: a sub-quadratic `ring::mul` champion.
            pub fn lift_commit(m: Mode<'_, '_>, z_len: usize) -> u64 {
                let rho_rows = 1usize;
                let width = z_len + rho_rows * hc::params::GADGET_DIGITS;
                let w = LiftedWitness::new(
                    vec_of(0x8047_0000_0000_0050, z_len),
                    quotient_rows(0x8047_0000_0000_0060, rho_rows),
                );
                let d_key = matrix_of(0x8047_0000_0000_0070, 1, width);
                support::run(
                    m,
                    || hc::ringswitch::lift_commit(black_box(&d_key), black_box(&w)),
                    d_polyvec,
                )
            }

            /// The full five-row quotient-digit check at the real constants.
            /// Its verdict is provably always true at `(16, 15)`; retaining the
            /// computation makes parameter drift observable.
            pub fn rho_digits_short_check(m: Mode<'_, '_>, rows: usize) -> u64 {
                let rho = quotient_rows(0x8047_0000_0000_0080, rows);
                support::run(
                    m,
                    || hc::endpiece::rho_digits_short_check(black_box(&rho)),
                    d_bool,
                )
            }

            /// The real 57,344-entry `z` scan. Its ~448 MiB input is built once
            /// outside the timed region; only the shortness decision is timed.
            pub fn lift_short_check(m: Mode<'_, '_>, z_len: usize) -> u64 {
                let w = LiftedWitness::new(
                    PolyVec::zeros(z_len),
                    quotient_rows(0x8047_0000_0000_0090, hc::params::RLIN_ROWS),
                );
                support::run(m, || hc::endpiece::lift_short_check(black_box(&w)), d_bool)
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
    // @covers ringswitch::QuotientRow::to_rq
    bench_case!(c, "ringswitch/rho_as_rq", rho_as_rq, [degree]);
    // @covers ringswitch::rho_digit_as_rq
    bench_case!(c, "ringswitch/rho_digit_as_rq", rho_digit_as_rq, [hachi::params::RLIN_ROWS]);
    // W3 REDUCED; see the case documentation for arithmetic and removal condition.
    // @covers ringswitch::lift_message
    bench_case!(c, "ringswitch/lift_message", lift_message, [8]);
    // W1 REDUCED; see the case documentation for arithmetic and removal condition.
    // @covers ringswitch::lift_commit
    bench_case!(c, "ringswitch/lift_commit", lift_commit, [4]);
    // @covers endpiece::rho_digits_short_check
    bench_case!(c, "endpiece/rho_digits_short_check", rho_digits_short_check, [hachi::params::RLIN_ROWS]);
    // Real constants. The 448 MiB input is constructed outside the timed region.
    // @covers endpiece::lift_short_check
    bench_case!(c, "endpiece/lift_short_check", lift_short_check, [hachi::params::RLIN_COLS]);
}

criterion_group! {
    name = benches;
    config = support::criterion_config();
    targets = ringswitch_benches
}
criterion_main!(benches);
