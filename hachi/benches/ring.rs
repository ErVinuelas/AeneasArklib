//! Wall-clock time for the ring operations.
//!
//! `mul` is the case that matters: it is the schoolbook `O(N²)` negacyclic
//! convolution, `N = 64`, and it is where every operation above it spends its
//! time -- a matrix-vector product is `rows · cols` of these. It is also the
//! operation an NTT would replace, so this reading is the baseline any such
//! optimization has to beat *and* carry an equivalence proof for.
//!
//! See `benches/support/mod.rs` for the corpus discipline and for what the
//! `_control` case is.

mod support;

use std::hint::black_box;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};

use support::corpus;

/// Every case of this module, for one variant (one of the three crates).
macro_rules! ring_cases {
    ($group:expr, $variant:literal, $krate:ident) => {{
        use $krate::ring::Rq;

        let ca = corpus(0x1234_5678_9ABC_DEF0, $krate::params::RING_DEGREE);
        let cb = corpus(0x0FED_CBA9_8765_4321, $krate::params::RING_DEGREE);
        let a = Rq::from_coeffs(&ca);
        let b = Rq::from_coeffs(&cb);
        let scalar = ca[0];

        // The control: `Rq::zero()` is byte-identical in all three crates, so any
        // spread here is the harness's own bias and not a property of the code.
        $group.bench_function(concat!("_control/", $variant), |bencher| {
            bencher.iter(|| black_box(Rq::zero()))
        });
        $group.bench_function(concat!("add/", $variant), |bencher| {
            bencher.iter(|| black_box(black_box(&a).add(black_box(&b))))
        });
        $group.bench_function(concat!("sub/", $variant), |bencher| {
            bencher.iter(|| black_box(black_box(&a).sub(black_box(&b))))
        });
        $group.bench_function(concat!("neg/", $variant), |bencher| {
            bencher.iter(|| black_box(black_box(&a).neg()))
        });
        $group.bench_function(concat!("scalar_mul/", $variant), |bencher| {
            bencher.iter(|| black_box(black_box(&a).scalar_mul(black_box(scalar))))
        });
        $group.bench_function(concat!("mul/", $variant), |bencher| {
            bencher.iter(|| black_box(black_box(&a).mul(black_box(&b))))
        });
        $group.bench_function(concat!("equals/", $variant), |bencher| {
            bencher.iter(|| black_box(black_box(&a).equals(black_box(&a))))
        });
        $group.bench_function(concat!("from_coeffs/", $variant), |bencher| {
            bencher.iter(|| black_box(Rq::from_coeffs(black_box(&ca))))
        });
    }};
}

fn bench_ring(c: &mut Criterion) {
    // Correctness before speed: a case that computes the wrong answer must fail
    // the run rather than be reported as a fast one. The three variants are the
    // same source, so agreeing on the negacyclic relation is a real check that
    // the frozen copies were copied and not paraphrased.
    {
        use hachi::ring::Rq;
        let n = hachi::params::RING_DEGREE;
        let mut top = vec![cpoly::Fp::ZERO; n];
        top[n - 1] = cpoly::Fp::ONE;
        let mut x = vec![cpoly::Fp::ZERO; n];
        x[1] = cpoly::Fp::ONE;
        let product = Rq::from_coeffs(&top).mul(&Rq::from_coeffs(&x));
        assert!(product.equals(&Rq::one().neg()), "X^(N-1)·X is not -1");
    }

    let mut g = c.benchmark_group("ring");
    g.measurement_time(Duration::from_secs(5));

    ring_cases!(g, "now", hachi);
    ring_cases!(g, "genesis", hachi_genesis);
    #[cfg(feature = "candidate")]
    ring_cases!(g, "cand", hachi_candidate);

    g.finish();
}

criterion_group!(benches, bench_ring);
criterion_main!(benches);
