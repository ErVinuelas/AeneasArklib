//! Wall-clock time for the gadget algebra.
//!
//! `gadget_decompose` is the interesting one, and the case most likely to be
//! optimized first: as written it re-derives each digit from the coefficient with
//! a fresh division chain (`digit_at` divides `e` times), which is
//! `O(digits²)` per coefficient where a running quotient would be `O(digits)`.
//! That is a deliberate choice for the equivalence proof's sake -- each output
//! digit is literally the spec's `digit c e` -- and the reading here is what makes
//! the trade visible instead of assumed.
//!
//! `base_pow` inside `gadget_mul` is the same trade: recomputing `bᵉ` per slot
//! rather than carrying it, so every term is syntactically the spec's `base ^ e`.

mod support;

use std::hint::black_box;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};

use support::corpus;

macro_rules! gadget_cases {
    ($group:expr, $variant:literal, $krate:ident) => {{
        use $krate::gadget::{
            base_pow, digit_at, digit_decompose, gadget_decompose, gadget_matrix, gadget_mul,
        };
        use $krate::linalg::PolyVec;
        use $krate::params::{GADGET_DIGITS, MESSAGE_ROWS, RING_DEGREE};
        use $krate::ring::Rq;

        let vec_of = |seed: u64, k: usize| -> PolyVec {
            let mut entries = Vec::with_capacity(k);
            for i in 0..k {
                entries.push(Rq::from_coeffs(&corpus(
                    seed.wrapping_add(i as u64 * 0x100),
                    RING_DEGREE,
                )));
            }
            PolyVec::new(entries)
        };

        let x = vec_of(0x1A1A_0000_0000_0001, MESSAGE_ROWS);
        let decomposed = gadget_decompose(&x);
        let one_coeff = corpus(0x1B1B_0000_0000_0002, 1)[0];

        // Control: `base_pow(0)` is a one-line loop that never iterates, and is
        // byte-identical across the three crates.
        $group.bench_function(concat!("_control/", $variant), |bencher| {
            bencher.iter(|| black_box(base_pow(black_box(0))))
        });
        $group.bench_function(concat!("digit_at/", $variant), |bencher| {
            bencher.iter(|| {
                black_box(digit_at(
                    black_box(one_coeff),
                    black_box(GADGET_DIGITS - 1),
                ))
            })
        });
        $group.bench_function(concat!("digit_decompose/", $variant), |bencher| {
            bencher.iter(|| black_box(digit_decompose(black_box(one_coeff))))
        });
        $group.bench_function(concat!("base_pow/", $variant), |bencher| {
            bencher.iter(|| black_box(base_pow(black_box(GADGET_DIGITS - 1))))
        });
        $group.bench_function(concat!("gadget_matrix/", $variant), |bencher| {
            bencher.iter(|| black_box(gadget_matrix(black_box(MESSAGE_ROWS))))
        });
        $group.bench_function(concat!("gadget_decompose/", $variant), |bencher| {
            bencher.iter(|| black_box(gadget_decompose(black_box(&x))))
        });
        $group.bench_function(concat!("gadget_mul/", $variant), |bencher| {
            bencher.iter(|| black_box(gadget_mul(black_box(MESSAGE_ROWS), black_box(&decomposed))))
        });
    }};
}

fn bench_gadget(c: &mut Criterion) {
    // The gadget round trip, asserted before timing: `G · G⁻¹(x) = x`.
    {
        use hachi::gadget::{gadget_decompose, gadget_mul};
        use hachi::linalg::PolyVec;
        use hachi::ring::Rq;
        let x = PolyVec::new(vec![Rq::from_coeffs(&corpus(0x1234, hachi::params::RING_DEGREE))]);
        assert!(
            gadget_mul(1, &gadget_decompose(&x)).equals(&x),
            "the gadget round trip fails; a timing of it would be meaningless"
        );
    }

    let mut g = c.benchmark_group("gadget");
    g.measurement_time(Duration::from_secs(5));

    gadget_cases!(g, "now", hachi);
    gadget_cases!(g, "genesis", hachi_genesis);
    #[cfg(feature = "candidate")]
    gadget_cases!(g, "cand", hachi_candidate);

    g.finish();
}

criterion_group!(benches, bench_gadget);
criterion_main!(benches);
