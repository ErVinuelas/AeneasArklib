//! Wall-clock time for the ring operations.
//!
//! `mul` is the case that matters: it is the schoolbook `O(N²)` negacyclic
//! convolution, `N = 64`, and it is where every operation above it spends its
//! time -- a matrix-vector product is `rows · cols` of these. It is also the
//! operation an NTT would replace, so this reading is the baseline any such
//! optimization has to beat *and* carry an equivalence proof for.
//!
//! # Sizes
//!
//! One size, `RING_DEGREE`, and it is not a knob: an `Rq` has exactly `N`
//! coefficients by construction (`ring`'s module header), so there is no second
//! point to measure any of these at. The parameter is carried anyway because it
//! is the length every row's output has, and `harness.py` keys a case on the
//! group plus that value -- a row whose reported size were a label rather than a
//! fact is a row nobody can compare. The three constructors that take no length
//! argument assert theirs instead of asserting nothing.
//!
//! # Allocation is part of the measurement
//!
//! Every operation here returns a freshly allocated `Rq`, and the timed region
//! includes both that allocation and the drop of that same iteration's result --
//! criterion's `Bencher::iter` is `for _ in 0..iters { black_box(routine()); }`,
//! so the value is dropped inside the loop at the end of the statement that
//! produced it. That is not an accident to be corrected: it is what a caller
//! pays, and an "optimization" that halves the arithmetic while doubling the
//! allocations has not made anything faster. Every variant pays it identically.
//!
//! Worth knowing what that costs here, because it is most of some of these rows:
//! `Rq::zero`, `Rq::constant` and every arithmetic operation build their output
//! with `Vec::new()` and `push`, so each one grows its buffer from nothing
//! through several reallocations rather than asking for `N` once. That shape is a
//! deliberate extraction concession (`src/lib.rs` § "Style notes"), and it is
//! identical in all three variants, so the comparison stays fair while the
//! magnitudes stay allocator-dominated -- which is also why `Vec::with_capacity`
//! is the first "free" optimization a candidate is likely to try, and why these
//! rows exist to price it.
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
            // `support::run`'s digest argument is `Fn(&R) -> u64`, so a digest of
            // a `Copy` scalar has to take it by reference. That is the bound's
            // shape, not a choice this file makes.
            #![allow(clippy::trivially_copy_pass_by_ref)]

            use std::hint::black_box;

            use cpoly::Fp;

            use $hachi as hc;

            use crate::support::{self, Mode};

            // -- corpus -----------------------------------------------------

            fn rq(seed: u64, n: usize) -> hc::ring::Rq {
                hc::ring::Rq::from_coeffs(&support::corpus(seed, n))
            }

            // -- digests (outside every timed region) -----------------------

            /// Length first, then every coefficient in order. The length matters
            /// because `from_coeffs` pads and truncates, so a change that
            /// produced the right coefficients and the wrong number of them must
            /// not be able to collide with a correct result.
            fn d_rq(a: &hc::ring::Rq) -> u64 {
                let n = a.len();
                let mut acc = support::mix_len(0, n);
                let mut k = 0usize;
                while k < n {
                    acc = support::mix(acc, a.coeff(k).to_u64());
                    k += 1;
                }
                acc
            }

            fn d_bool(x: &bool) -> u64 {
                support::mix(0, u64::from(*x))
            }

            /// Only the `_control` case produces one of these; `benches/linalg.rs`
            /// is where `PolyVec` is measured.
            fn d_polyvec(v: &hc::linalg::PolyVec) -> u64 {
                let k = v.len();
                let mut acc = support::mix_len(0, k);
                let mut i = 0usize;
                while i < k {
                    acc = support::mix(acc, d_rq(v.get(i)));
                    i += 1;
                }
                acc
            }

            // -- the negacyclic relation ------------------------------------

            /// `X^(N-1) · X = -1`, asserted before anything is timed.
            ///
            /// Correctness before speed: a case that computes the wrong answer
            /// must fail the run rather than be reported as a fast one. Called
            /// for every variant, which is what makes it a real check that the
            /// frozen and slot copies were copied and not paraphrased -- the
            /// digest oracle then proves they agree on the *corpus* too.
            pub fn check() {
                let n = hc::params::RING_DEGREE;
                let mut top = vec![Fp::ZERO; n];
                top[n - 1] = Fp::ONE;
                let mut x = vec![Fp::ZERO; n];
                x[1] = Fp::ONE;
                let product = hc::ring::Rq::from_coeffs(&top).mul(&hc::ring::Rq::from_coeffs(&x));
                assert!(
                    product.equals(&hc::ring::Rq::one().neg()),
                    "X^(N-1)·X is not -1"
                );
            }

            // -- construction -----------------------------------------------

            /// `Rq::zero` takes no argument, so `n` is used as what it names: the
            /// length the constructor fills.
            pub fn zero(m: Mode<'_, '_>, n: usize) -> u64 {
                assert_eq!(hc::ring::Rq::zero().len(), n, "ring/zero: wrong length");
                support::run(m, hc::ring::Rq::zero, d_rq)
            }

            /// See [`zero`]. `Rq::one` is `Rq::constant(Fp::ONE)`, so this row and
            /// `ring/constant` should track each other; they are separate rows
            /// because they are separate items with separate spec obligations.
            pub fn one(m: Mode<'_, '_>, n: usize) -> u64 {
                assert_eq!(hc::ring::Rq::one().len(), n, "ring/one: wrong length");
                support::run(m, hc::ring::Rq::one, d_rq)
            }

            pub fn constant(m: Mode<'_, '_>, n: usize) -> u64 {
                let c = support::corpus(0x1234_5678_9ABC_DEF0, n)[0];
                support::run(m, || hc::ring::Rq::constant(black_box(c)), d_rq)
            }

            pub fn from_coeffs(m: Mode<'_, '_>, n: usize) -> u64 {
                let ca = support::corpus(0x1234_5678_9ABC_DEF0, n);
                support::run(m, || hc::ring::Rq::from_coeffs(black_box(&ca)), d_rq)
            }

            // -- arithmetic --------------------------------------------------

            pub fn add(m: Mode<'_, '_>, n: usize) -> u64 {
                let a = rq(0x1234_5678_9ABC_DEF0, n);
                let b = rq(0x0FED_CBA9_8765_4321, n);
                support::run(m, || black_box(&a).add(black_box(&b)), d_rq)
            }

            pub fn sub(m: Mode<'_, '_>, n: usize) -> u64 {
                let a = rq(0x1234_5678_9ABC_DEF0, n);
                let b = rq(0x0FED_CBA9_8765_4321, n);
                support::run(m, || black_box(&a).sub(black_box(&b)), d_rq)
            }

            pub fn neg(m: Mode<'_, '_>, n: usize) -> u64 {
                let a = rq(0x1234_5678_9ABC_DEF0, n);
                support::run(m, || black_box(&a).neg(), d_rq)
            }

            pub fn scalar_mul(m: Mode<'_, '_>, n: usize) -> u64 {
                let ca = support::corpus(0x1234_5678_9ABC_DEF0, n);
                let a = hc::ring::Rq::from_coeffs(&ca);
                let scalar = ca[0];
                support::run(m, || black_box(&a).scalar_mul(black_box(scalar)), d_rq)
            }

            /// The `O(N²)` negacyclic convolution. Two seeds, never one: `a · a`
            /// is a squaring, and squaring is not what `mul` is for.
            pub fn mul(m: Mode<'_, '_>, n: usize) -> u64 {
                let a = rq(0x1234_5678_9ABC_DEF0, n);
                let b = rq(0x0FED_CBA9_8765_4321, n);
                support::run(m, || black_box(&a).mul(black_box(&b)), d_rq)
            }

            /// Equal operands on purpose. `equals` has no early exit -- it walks
            /// all `N` coefficients and accumulates a flag -- so this measures
            /// the whole loop; unequal operands would measure the same loop while
            /// making the row hostage to a future short circuit.
            pub fn equals(m: Mode<'_, '_>, n: usize) -> u64 {
                let a = rq(0x1234_5678_9ABC_DEF0, n);
                support::run(m, || black_box(&a).equals(black_box(&a)), d_bool)
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
                support::run(m, || hc::linalg::PolyVec::zeros(black_box(n)), d_polyvec)
            }
        }
    };
}

define_cases!(now, hachi);
define_cases!(genesis, hachi_genesis);
#[cfg(feature = "candidate")]
define_cases!(candidate, hachi_candidate);

fn ring_benches(c: &mut Criterion) {
    now::check();
    genesis::check();
    #[cfg(feature = "candidate")]
    candidate::check();

    // The run's sanity check: identical source in every variant, so anything it
    // reads is the harness disagreeing with itself. Runs first, while the machine
    // is in the same state the first real cases will see.
    bench_case!(c, "_control/ring", control, [support::CONTROL_N]);

    let n = hachi::params::RING_DEGREE;

    // @covers ring::Rq::zero
    bench_case!(c, "ring/zero", zero, [n]);
    // @covers ring::Rq::one
    bench_case!(c, "ring/one", one, [n]);
    // @covers ring::Rq::constant
    bench_case!(c, "ring/constant", constant, [n]);
    // @covers ring::Rq::from_coeffs
    bench_case!(c, "ring/from_coeffs", from_coeffs, [n]);

    // @covers ring::Rq::add
    bench_case!(c, "ring/add", add, [n]);
    // @covers ring::Rq::sub
    bench_case!(c, "ring/sub", sub, [n]);
    // @covers ring::Rq::neg
    bench_case!(c, "ring/neg", neg, [n]);
    // @covers ring::Rq::scalar_mul
    bench_case!(c, "ring/scalar_mul", scalar_mul, [n]);
    // @covers ring::Rq::mul
    bench_case!(c, "ring/mul", mul, [n]);
    // @covers ring::Rq::equals
    bench_case!(c, "ring/equals", equals, [n]);
}

criterion_group! {
    name = benches;
    config = support::criterion_config();
    targets = ring_benches
}
criterion_main!(benches);
