//! Wall-clock time for the vector and matrix operations.
//!
//! Sizes are the scheme's own, not round numbers: the dot product is over
//! `MESSAGE_ROWS · GADGET_DIGITS = 128` entries because that is the width of the
//! inner Ajtai matrix, and the matrix is `INNER_ROWS × 128` because that is `A`.
//! A reading at a size the scheme never uses would be a reading nothing depends
//! on.
//!
//! Every case here is dominated by `ring::mul`, which is the point: if this
//! module ever shows up as a cost of its own, the loop below it got faster.

mod support;

use std::hint::black_box;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};

use support::{corpora, corpus};

macro_rules! linalg_cases {
    ($group:expr, $variant:literal, $krate:ident) => {{
        use $krate::linalg::{flatten_blocks, PolyMatrix, PolyVec};
        use $krate::params::{BLOCKS, GADGET_DIGITS, INNER_ROWS, MESSAGE_ROWS};
        use $krate::ring::Rq;

        let width = MESSAGE_ROWS * GADGET_DIGITS;
        let degree = $krate::params::RING_DEGREE;

        let vec_of = |seed: u64, k: usize| -> PolyVec {
            let mut entries = Vec::with_capacity(k);
            for i in 0..k {
                entries.push(Rq::from_coeffs(&corpus(
                    seed.wrapping_add(i as u64 * 0x100),
                    degree,
                )));
            }
            PolyVec::new(entries)
        };

        let u = vec_of(0x0A0A_0A0A_0000_0001, width);
        let v = vec_of(0x0B0B_0B0B_0000_0002, width);
        let scalar = Rq::from_coeffs(&corpus(0x0C0C_0C0C_0000_0003, degree));

        let mut rows = Vec::with_capacity(INNER_ROWS);
        for i in 0..INNER_ROWS {
            rows.push(vec_of(0x0D0D_0000_0000_0000 + i as u64, width));
        }
        let a = PolyMatrix::new(rows);

        let mut blocks = Vec::with_capacity(BLOCKS);
        for (i, _) in corpora(0x0E0E, BLOCKS, 1).iter().enumerate() {
            blocks.push(vec_of(0x0E0E_0000 + i as u64, INNER_ROWS * GADGET_DIGITS));
        }

        // Control: `PolyVec::zeros` is byte-identical across the three crates.
        $group.bench_function(concat!("_control/", $variant), |bencher| {
            bencher.iter(|| black_box(PolyVec::zeros(black_box(width))))
        });
        $group.bench_function(concat!("dot/", $variant), |bencher| {
            bencher.iter(|| black_box(black_box(&u).dot(black_box(&v))))
        });
        $group.bench_function(concat!("vec_add/", $variant), |bencher| {
            bencher.iter(|| black_box(black_box(&u).add(black_box(&v))))
        });
        $group.bench_function(concat!("scalar_vec_mul/", $variant), |bencher| {
            bencher.iter(|| black_box(black_box(&u).scalar_mul(black_box(&scalar))))
        });
        $group.bench_function(concat!("mat_vec_mul/", $variant), |bencher| {
            bencher.iter(|| black_box(black_box(&a).mat_vec_mul(black_box(&u))))
        });
        $group.bench_function(concat!("flatten_blocks/", $variant), |bencher| {
            bencher.iter(|| black_box(flatten_blocks(black_box(&blocks))))
        });
        $group.bench_function(concat!("equals/", $variant), |bencher| {
            bencher.iter(|| black_box(black_box(&u).equals(black_box(&u))))
        });
    }};
}

fn bench_linalg(c: &mut Criterion) {
    let mut g = c.benchmark_group("linalg");
    g.measurement_time(Duration::from_secs(5));

    linalg_cases!(g, "now", hachi);
    linalg_cases!(g, "genesis", hachi_genesis);
    #[cfg(feature = "candidate")]
    linalg_cases!(g, "cand", hachi_candidate);

    g.finish();
}

criterion_group!(benches, bench_linalg);
criterion_main!(benches);
