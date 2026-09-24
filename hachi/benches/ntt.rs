//! Wall-clock time for the Goldilocks transforms of `src/ntt.rs`, measured on
//! their own rather than through a ring operation.
//!
//! One case, `ntt/gold_inverse`, card T52c's isolating row. Every other use of
//! the transforms is measured through the `ring`, `linalg`, `commit` and
//! `quadeval` rows that call them.
//!
//! # Why this is its own binary
//!
//! The row was first written as `ring/gold_inverse` in `benches/ring.rs`, and
//! card T52c's two accepting runs measured it under that name, with the `ring`
//! binary's control. `coverage --strict` then rejected the marker: a
//! `@covers ntt::…` on a `ring/…` case names one module and sits in another
//! (`harness.py` § `covered_paths`). A `ring::` marker would name an item the row
//! does not call. So the body moved here unchanged, under the name card T52c's
//! section-6 report gave it, with this binary's own `_control/ntt`.
//!
//! See `benches/support/mod.rs` for the corpus discipline, the digest oracle and
//! what the `_control` case is.

mod support;

use criterion::{criterion_group, criterion_main, Criterion};

/// One body per case, instantiated once per variant crate (`benches/ring.rs`
/// § `define_cases` has the reason).
macro_rules! define_cases {
    ($modname:ident, $hachi:path) => {
        mod $modname {
            use std::hint::black_box;

            use $hachi as hc;

            use crate::support::{self, Mode};

            /// One inverse Goldilocks transform, `ntt::gold_inverse`, on `n`
            /// canonical words with the real inverse psi table. This is the call
            /// the carrier's limbs chunk makes twice per chunk (65 536 times a
            /// carrier call at the pin), the commitment once per block, and the
            /// lift commitment once (card T52c). The input copy and the scratch
            /// allocation sit inside the closure because `gold_inverse` takes
            /// both by value: ~2 x 8 KiB against a ~10 us transform.
            pub fn gold_inverse(m: Mode<'_, '_>, n: usize) -> u64 {
                let it = hc::ntt::gold_psi_table(hc::ntt::GOLD_PSIINV);
                let words: Vec<u64> = support::corpus(0x7452_C001, n).iter().map(|f| f.to_u64()).collect();
                support::run(
                    m,
                    || hc::ntt::gold_inverse(black_box(words.clone()), black_box(vec![0u64; n]), black_box(&it)).0,
                    |v: &Vec<u64>| {
                        let mut acc = support::mix_len(0, v.len());
                        for w in v { acc = support::mix(acc, *w); }
                        acc
                    },
                )
            }

            // -- the A/B fairness control -----------------------------------

            // `d_rq` and `d_polyvec` are `benches/ring.rs`'s, verbatim, so this
            // control is that binary's control.
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

fn ntt_benches(c: &mut Criterion) {
    // The run's sanity check: identical source in every variant, so anything it
    // reads is the harness disagreeing with itself.
    bench_case!(c, "_control/ntt", control, [support::CONTROL_N]);

    let n = hachi::params::RING_DEGREE;

    // Card T52c's row: the inverse Goldilocks transform, at the ring degree.
    // @covers ntt::gold_inverse
    bench_case!(c, "ntt/gold_inverse", gold_inverse, [n]);
}

criterion_group! {
    name = benches;
    config = support::criterion_config();
    targets = ntt_benches
}
criterion_main!(benches);
