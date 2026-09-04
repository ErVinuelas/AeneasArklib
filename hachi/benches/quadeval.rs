//! Wall-clock time for the QuadEval fold's *runnable* pieces.
//!
//! Most of this module is not benchable at [NOZ26] Fig. 9, and the reason is a
//! **memory** wall rather than a multiplication one -- see
//! `benches/exclusions.toml`. The witness `message` alone is `2^23` ring
//! elements (~64 GiB), so `carrier`, `carrier_decomp`, `carrier_commit`,
//! `honest_z`, `honest_compute_v`, `honest_compute_resp`, `rel_out` and
//! `paper_rel_out` cannot run at any multiplication speed. What is left, and
//! what this file measures:
//!
//! * `in_sb` at real `RING_DEGREE` -- the coefficientwise box test, and the one
//!   function here that is neither `ring::mul`- nor memory-bound;
//! * `tensor_g`, `tensor_g1` and `carrier_entry` at **REDUCED** block/row
//!   counts, because each is `blocks` (resp. `rows`) full ring products and the
//!   scheme's 1024 of them is ~1.5 s per iteration;
//! * `j_mul` at a REDUCED `n`, for the same reason plus its `n·Z` input width.
//!
//! Every reduced size is recorded at its registration with the arithmetic that
//! forced it. See `benches/support/mod.rs` for the corpus discipline, the
//! digest oracle and what the `_control` case is.

mod support;

use criterion::{criterion_group, criterion_main, Criterion};

macro_rules! define_cases {
    ($modname:ident, $hachi:path) => {
        mod $modname {
            #![allow(clippy::trivially_copy_pass_by_ref)]

            use std::hint::black_box;

            use cpoly::Fp;

            use $hachi as hc;

            use crate::support::{self, Mode};

            type Rq = hc::ring::Rq;
            type PolyVec = hc::linalg::PolyVec;

            // -- corpus -----------------------------------------------------

            fn vec_of(seed: u64, k: usize) -> PolyVec {
                let degree = hc::params::RING_DEGREE;
                let mut entries = Vec::with_capacity(k);
                for i in 0..k {
                    entries.push(Rq::from_coeffs(&support::corpus(
                        seed.wrapping_add(i as u64 * 0x100),
                        degree,
                    )));
                }
                PolyVec::new(entries)
            }

            fn blocks_of(seed: u64, blocks: usize, width: usize) -> Vec<PolyVec> {
                let mut out = Vec::with_capacity(blocks);
                for i in 0..blocks {
                    out.push(vec_of(seed.wrapping_add(i as u64 * 0x10000), width));
                }
                out
            }

            // -- digests (outside every timed region) -----------------------

            fn d_bool(b: &bool) -> u64 {
                support::mix(0, u64::from(*b))
            }

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

            // -- the box check, asserted before anything is timed -----------

            /// The asymmetry that separates `rel_out` from `paper_rel_out`:
            /// `-8` is in the box and `+8` is not. Called for every variant,
            /// which is what makes it a real check that the frozen and slot
            /// copies were copied and not paraphrased.
            pub fn check() {
                let half = hc::params::HALF_BASE;
                let minus_eight = Rq::from_coeffs(&vec![Fp::new(hc::params::Q - half)]);
                let plus_eight = Rq::from_coeffs(&vec![Fp::new(half)]);
                assert!(
                    hc::quadeval::in_sb(&minus_eight),
                    "-8 must lie in the paper's box"
                );
                assert!(
                    !hc::quadeval::in_sb(&plus_eight),
                    "+8 must lie outside the paper's box"
                );
            }

            // -- cases ------------------------------------------------------

            /// The box test over one ring element at real `RING_DEGREE`:
            /// `degree` centered comparisons, branchless to the end.
            pub fn in_sb(m: Mode<'_, '_>, degree: usize) -> u64 {
                let a = Rq::from_coeffs(&support::corpus(0x9E11_0000_0000_0001, degree));
                support::run(m, || hc::quadeval::in_sb(black_box(&a)), d_bool)
            }

            /// The same over a vector. REDUCED width: at the scheme's
            /// `BLOCKS · GADGET_DIGITS = 8192` entries this is 8.4M centered
            /// comparisons, which measures `commit::centered_abs` in a loop
            /// rather than this function's own shape.
            pub fn vec_in_sb(m: Mode<'_, '_>, k: usize) -> u64 {
                let v = vec_of(0x9E11_0000_0000_0002, k);
                support::run(m, || hc::quadeval::vec_in_sb(black_box(&v)), d_bool)
            }

            /// `aᵀ (G s)` at a REDUCED row count: this is `rows` full ring
            /// products, so the scheme's `MESSAGE_ROWS = 1024` would be ~1.5 s
            /// per iteration.
            pub fn carrier_entry(m: Mode<'_, '_>, rows: usize) -> u64 {
                let digits = hc::params::GADGET_DIGITS;
                let a = vec_of(0x9E11_0000_0000_0003, rows);
                let s = vec_of(0x9E11_0000_0000_0004, rows * digits);
                support::run(
                    m,
                    || hc::quadeval::carrier_entry(black_box(&a), black_box(&s)),
                    d_rq,
                )
            }

            /// `⟨c, G x⟩` at a REDUCED block count, for the same arithmetic.
            pub fn tensor_g1(m: Mode<'_, '_>, blocks: usize) -> u64 {
                let digits = hc::params::GADGET_DIGITS;
                let c = vec_of(0x9E11_0000_0000_0005, blocks);
                let x = vec_of(0x9E11_0000_0000_0006, blocks * digits);
                support::run(
                    m,
                    || hc::quadeval::tensor_g1(black_box(&c), black_box(&x)),
                    d_rq,
                )
            }

            /// `Σᵢ cᵢ •ᵥ (G xᵢ)` at REDUCED block and row counts. Also the row
            /// that shows the per-block `PolyVec` allocation the `Finset.sum`
            /// of vectors pays.
            pub fn tensor_g(m: Mode<'_, '_>, blocks: usize) -> u64 {
                let digits = hc::params::GADGET_DIGITS;
                let rows = hc::params::INNER_ROWS;
                let c = vec_of(0x9E11_0000_0000_0007, blocks);
                let x = blocks_of(0x9E11_0000_0000_0008, blocks, rows * digits);
                support::run(
                    m,
                    || hc::quadeval::tensor_g(black_box(rows), black_box(&c), black_box(&x)),
                    d_polyvec,
                )
            }

            /// The A/B fairness control -- identical source in every variant.
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

fn quadeval_benches(c: &mut Criterion) {
    now::check();
    genesis::check();
    #[cfg(feature = "candidate")]
    candidate::check();

    bench_case!(c, "_control/quadeval", control, [support::CONTROL_N]);

    let degree = hachi::params::RING_DEGREE;
    // REDUCED sizes, with the arithmetic that forces each (module doc):
    // one `Rq::mul` at d = 1024 is ~1.5 ms, so `blocks` of them at the
    // scheme's 1024 is ~1.5 s per iteration.
    let reduced_blocks = 8;
    let reduced_rows = 8;
    // 8192 entries of 1024 coefficients is 8.4M comparisons; 256 keeps the row
    // about this function's own shape.
    let reduced_width = 256;

    // @covers quadeval::in_sb
    bench_case!(c, "quadeval/in_sb", in_sb, [degree]);
    // @covers quadeval::vec_in_sb
    bench_case!(c, "quadeval/vec_in_sb", vec_in_sb, [reduced_width]);
    // @covers quadeval::carrier_entry
    bench_case!(c, "quadeval/carrier_entry", carrier_entry, [reduced_rows]);
    // @covers quadeval::tensor_g1
    bench_case!(c, "quadeval/tensor_g1", tensor_g1, [reduced_blocks]);
    // @covers quadeval::tensor_g
    bench_case!(c, "quadeval/tensor_g", tensor_g, [reduced_blocks]);
}

criterion_group! {
    name = benches;
    config = support::criterion_config();
    targets = quadeval_benches
}
criterion_main!(benches);
