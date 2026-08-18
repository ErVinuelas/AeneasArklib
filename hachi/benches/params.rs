//! The scaffold's benchmark: it establishes the bench target, the pinned build
//! profile and the measurement discipline, and it times the one function
//! Workstream 0 produced.
//!
//! There is no `genesis` or `candidate` variant here. Both slots are empty on
//! purpose (see `benches/genesis/src/lib.rs`): the only function in the crate is
//! a throwaway extraction probe, and freezing a throwaway into an append-only
//! baseline is the one irreversible mistake in this harness. The three-slot
//! structure -- `now` vs `genesis`, plus `candidate` under `--features candidate`
//! -- arrives with the first real module, along with the `_control` case that
//! measures the harness's own bias.
//!
//! What the discipline already is, and what real cases will inherit:
//!
//! * **Inputs are opaque to the optimizer** (`black_box`) and every output is
//!   consumed, so there is nothing to constant-fold and nothing dead to delete.
//!   A benchmark whose work the optimizer deleted reads faster, which is the
//!   direction that makes a loop believe it succeeded.
//! * **Inputs come from a seeded generator**, so a case gets byte-identical
//!   inputs on every run, on every machine, in every variant. Run-to-run
//!   comparisons are then not confounded by input variation.

use std::hint::black_box;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};

use cpoly::Fp;
use hachi::params::Q;

/// The bench corpus size. One size only: `smoke::sum` is a straight line over a
/// `Vec`, and a second size would re-measure the same straight line.
const N: usize = 1024;

/// `SplitMix64`. Chosen because it is four lines and needs no dependency; the
/// corpus has to be reproducible, not cryptographic.
struct SplitMix64(u64);

impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// `N` field elements drawn from `[1, Q)`.
///
/// Zero is excluded so that a case's *shape* cannot depend on how many zeros a
/// seed happened to produce -- the habit matters for the real operations to come
/// (Hachi's shortness checks and `trim`-like passes stop at the first non-zero
/// coefficient), and starting it here costs nothing.
fn corpus() -> Vec<Fp> {
    let mut rng = SplitMix64(0x5EED_1234_5678_9ABC);
    let mut v = Vec::with_capacity(N);
    for _ in 0..N {
        v.push(Fp::new(1 + rng.next() % (Q - 1)));
    }
    v
}

fn bench_smoke_sum(c: &mut Criterion) {
    let mut g = c.benchmark_group("smoke");
    g.measurement_time(Duration::from_secs(5));

    let v = corpus();
    // Asserted before timing: a case that computes the wrong answer must fail the
    // run rather than be reported as a fast one.
    assert_eq!(hachi::smoke::sum(&v).to_u64(), reference_sum(&v));

    g.bench_function("sum", |b| b.iter(|| black_box(hachi::smoke::sum(black_box(&v)))));
    g.finish();
}

/// An independent sum, so the assertion above checks the implementation rather
/// than agreeing with itself.
fn reference_sum(v: &[Fp]) -> u64 {
    let mut acc = 0u128;
    for x in v {
        acc += u128::from(x.to_u64());
    }
    (acc % u128::from(Q)) as u64
}

criterion_group!(benches, bench_smoke_sum);
criterion_main!(benches);
