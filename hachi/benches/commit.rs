//! Wall-clock time for the commitment itself, end to end.
//!
//! These are the only two readings in the repository that correspond to something
//! a user of the scheme would wait for: `commit` (decompose, inner-commit,
//! decompose again, outer-commit) and `verify_weak` (per-block norms and gadget
//! relation, then the outer product). Everything else timed here is one of their
//! parts, present so that a change in the total can be attributed.
//!
//! Both are dominated by `linalg::mat_vec_mul` and so by `ring::mul`: at these
//! dimensions a single commit does `BLOCKS · (INNER_ROWS · MESSAGE_ROWS ·
//! GADGET_DIGITS) + OUTER_ROWS · (BLOCKS · INNER_ROWS · GADGET_DIGITS)` ring
//! products. The norms are `O(coefficients)` and should be invisible next to
//! that -- if a `norm` case ever becomes comparable to `commit`, the ring product
//! got much faster or a norm got much slower.

mod support;

use std::hint::black_box;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};

use support::corpus;

macro_rules! commit_cases {
    ($group:expr, $variant:literal, $krate:ident) => {{
        use $krate::commit::{
            commit, commit_with_decomps, derived_message, generate_decomps, l1_norm, l2_norm_sq,
            vec_l2_norm_sq, vec_l_infty_norm, Opening, PublicParams,
        };
        use $krate::linalg::{PolyMatrix, PolyVec};
        use $krate::params::{
            BLOCKS, GADGET_DIGITS, INNER_ROWS, MESSAGE_ROWS, OUTER_ROWS, RING_DEGREE,
        };
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
        let matrix_of = |seed: u64, rows: usize, cols: usize| -> PolyMatrix {
            let mut out = Vec::with_capacity(rows);
            for i in 0..rows {
                out.push(vec_of(seed.wrapping_add(i as u64 * 0x10000), cols));
            }
            PolyMatrix::new(out)
        };

        let pp = PublicParams::new(
            matrix_of(0x2A00_0000, INNER_ROWS, MESSAGE_ROWS * GADGET_DIGITS),
            matrix_of(0x2B00_0000, OUTER_ROWS, BLOCKS * (INNER_ROWS * GADGET_DIGITS)),
        );
        let mut m = Vec::with_capacity(BLOCKS);
        for b in 0..BLOCKS {
            m.push(vec_of(0x2C00_0000 + b as u64, MESSAGE_ROWS));
        }

        let (u, decomp) = commit(&pp, &m);
        let opening = Opening::honest(generate_decomps(&pp, &m));
        let long_vector = vec_of(0x2D00_0000, MESSAGE_ROWS * GADGET_DIGITS);
        let single = long_vector.get(0).copy();

        // Control: `Rq::one()` is byte-identical across the three crates.
        $group.bench_function(concat!("_control/", $variant), |bencher| {
            bencher.iter(|| black_box(Rq::one()))
        });
        $group.bench_function(concat!("l1_norm/", $variant), |bencher| {
            bencher.iter(|| black_box(l1_norm(black_box(&single))))
        });
        $group.bench_function(concat!("l2_norm_sq/", $variant), |bencher| {
            bencher.iter(|| black_box(l2_norm_sq(black_box(&single))))
        });
        $group.bench_function(concat!("vec_l2_norm_sq/", $variant), |bencher| {
            bencher.iter(|| black_box(vec_l2_norm_sq(black_box(&long_vector))))
        });
        $group.bench_function(concat!("vec_l_infty_norm/", $variant), |bencher| {
            bencher.iter(|| black_box(vec_l_infty_norm(black_box(&long_vector))))
        });
        $group.bench_function(concat!("generate_decomps/", $variant), |bencher| {
            bencher.iter(|| black_box(generate_decomps(black_box(&pp), black_box(&m))))
        });
        $group.bench_function(concat!("commit_with_decomps/", $variant), |bencher| {
            bencher.iter(|| black_box(commit_with_decomps(black_box(&pp), black_box(&decomp))))
        });
        $group.bench_function(concat!("derived_message/", $variant), |bencher| {
            bencher.iter(|| black_box(derived_message(black_box(&decomp))))
        });
        $group.bench_function(concat!("commit/", $variant), |bencher| {
            bencher.iter(|| black_box(commit(black_box(&pp), black_box(&m))))
        });
        $group.bench_function(concat!("verify_weak/", $variant), |bencher| {
            bencher.iter(|| {
                black_box($krate::commit::verify_weak(
                    black_box(&pp),
                    black_box(&u),
                    black_box(&opening),
                ))
            })
        });
    }};
}

fn bench_commit(c: &mut Criterion) {
    // Perfect correctness, asserted before timing: timing a verifier that rejects
    // measures the rejection path, which is not what the case claims to measure.
    {
        use hachi::commit::{commit, generate_decomps, verify_weak, Opening, PublicParams};
        use hachi::linalg::{PolyMatrix, PolyVec};
        use hachi::params::{BLOCKS, GADGET_DIGITS, INNER_ROWS, MESSAGE_ROWS, OUTER_ROWS};
        use hachi::ring::Rq;

        let degree = hachi::params::RING_DEGREE;
        let vec_of = |seed: u64, k: usize| -> PolyVec {
            let mut entries = Vec::with_capacity(k);
            for i in 0..k {
                entries.push(Rq::from_coeffs(&corpus(seed + i as u64 * 0x100, degree)));
            }
            PolyVec::new(entries)
        };
        let matrix_of = |seed: u64, rows: usize, cols: usize| -> PolyMatrix {
            let mut out = Vec::with_capacity(rows);
            for i in 0..rows {
                out.push(vec_of(seed + i as u64 * 0x10000, cols));
            }
            PolyMatrix::new(out)
        };
        let pp = PublicParams::new(
            matrix_of(0x2A00_0000, INNER_ROWS, MESSAGE_ROWS * GADGET_DIGITS),
            matrix_of(0x2B00_0000, OUTER_ROWS, BLOCKS * (INNER_ROWS * GADGET_DIGITS)),
        );
        let mut m = Vec::with_capacity(BLOCKS);
        for b in 0..BLOCKS {
            m.push(vec_of(0x2C00_0000 + b as u64, MESSAGE_ROWS));
        }
        let (u, _) = commit(&pp, &m);
        assert!(
            verify_weak(&pp, &u, &Opening::honest(generate_decomps(&pp, &m))),
            "an honest opening does not verify; a timing of it would be meaningless"
        );
    }

    let mut g = c.benchmark_group("commit");
    // Longer than the other groups: `commit` is milliseconds rather than
    // microseconds, so criterion needs the time to collect a sample of them.
    g.measurement_time(Duration::from_secs(10));
    g.sample_size(50);

    commit_cases!(g, "now", hachi);
    commit_cases!(g, "genesis", hachi_genesis);
    #[cfg(feature = "candidate")]
    commit_cases!(g, "cand", hachi_candidate);

    g.finish();
}

criterion_group!(benches, bench_commit);
criterion_main!(benches);
