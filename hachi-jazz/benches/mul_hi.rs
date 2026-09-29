//! Microbenchmark: the Jasmin `MULX` kernel vs. the scalar Rust idiom, on the
//! 64×64→high-64 multiply alone and inside an `aux_reduce`-shaped loop.
//!
//! This is a *sibling-crate microbenchmark*, deliberately outside hachi's
//! ledger harness: it carries no accept/reject verdict for the optimization
//! loop (only `make run-bench` rows on the crate's own bench slot do). Its one
//! job is to make the FFI call overhead visible next to the inlined idiom.
//!
//! Expected outcome, stated up front: the scalar idiom compiles to one `mulq`
//! that LLVM inlines into the caller; the Jasmin kernel is the same multiply
//! behind a `call`. The kernel should therefore *lose* here — this bench
//! documents the price of the boundary, which is what the integration
//! milestone set out to measure.

use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

fn mul_hi_ref(x: u64, y: u64) -> u64 {
    (((x as u128) * (y as u128)) >> 64) as u64
}

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn inputs(n: usize) -> Vec<(u64, u64)> {
    let mut s: u64 = 0x5EED_5EED_5EED_5EED;
    (0..n).map(|_| (splitmix64(&mut s), splitmix64(&mut s))).collect()
}

fn bench_mul_hi(c: &mut Criterion) {
    assert!(hachi_jazz::available(), "BMI2 required");
    let xs = inputs(4096);

    let mut g = c.benchmark_group("mul_hi");
    g.bench_function("rust_u128_idiom/4096", |b| {
        b.iter(|| {
            let mut acc: u64 = 0;
            for &(x, y) in &xs {
                acc = acc.wrapping_add(mul_hi_ref(black_box(x), black_box(y)));
            }
            acc
        });
    });
    g.bench_function("jasmin_mulx_ffi/4096", |b| {
        b.iter(|| {
            let mut acc: u64 = 0;
            for &(x, y) in &xs {
                acc = acc.wrapping_add(hachi_jazz::mul_hi_u64(black_box(x), black_box(y)));
            }
            acc
        });
    });
    g.finish();

    // The idiom in its real habitat: an aux_reduce-shaped Barrett reduction.
    let p = hachi::ntt::AUX_P1;
    let m = hachi::ntt::AUX_M1;
    let rs: Vec<u64> = {
        let mut s: u64 = 0xACE1_ACE1_ACE1_ACE1;
        (0..4096).map(|_| (splitmix64(&mut s) % p) * (splitmix64(&mut s) % p)).collect()
    };

    let mut g = c.benchmark_group("aux_reduce");
    g.bench_function("hachi_scalar/4096", |b| {
        b.iter(|| {
            let mut acc: u64 = 0;
            for &x in &rs {
                acc = acc.wrapping_add(hachi::ntt::aux_reduce(black_box(x), p, m));
            }
            acc
        });
    });
    g.bench_function("via_jasmin_ffi/4096", |b| {
        b.iter(|| {
            let mut acc: u64 = 0;
            for &x in &rs {
                let qh = hachi_jazz::mul_hi_u64(black_box(x), m);
                let r = x - qh * p;
                acc = acc.wrapping_add(if r >= p { r - p } else { r });
            }
            acc
        });
    });
    g.finish();
}

criterion_group!(benches, bench_mul_hi);
criterion_main!(benches);
