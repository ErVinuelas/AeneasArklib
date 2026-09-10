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
//!   function here that is neither `ring::mul`- nor memory-bound. Twice: once
//!   on the ordinary `[1, q)` corpus, which lies *outside* the box and answers
//!   `false`, and once (`in_sb_box`) on an all-inside corpus, the honest
//!   workload, so a candidate that exits early on the first outside coefficient
//!   cannot book its win on rejected inputs alone. Same pair for `vec_in_sb`.
//!   **Of those four rows only the two `vec_*` ones carry a candidate verdict**
//!   -- the single-`Rq` pair measures a branch pattern the predictor has
//!   memorized, at 5.8x below the honest per-coefficient cost (case docs, and
//!   NOTES.md § "The §4 audit of target 2's rows");
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

            /// Coefficients drawn **inside** the paper's box `[-8, 7]`: the honest
            /// workload of the box test, since the digits a balanced
            /// decomposition produces lie there by construction. Derived from the
            /// ordinary corpus so both draws share one seed discipline: the low
            /// four bits of each `[1, q)` draw pick a digit, `0..8` stays as it
            /// is and `8..16` wraps to `q - 8 .. q - 1`, i.e. `-8 .. -1`. So `-8`
            /// is reachable and `+8` is not -- the box's own asymmetry.
            fn box_coeffs(seed: u64, n: usize) -> Vec<Fp> {
                let q = hc::params::Q;
                support::corpus(seed, n)
                    .iter()
                    .map(|c| {
                        let d = c.to_u64() % 16;
                        if d < 8 {
                            Fp::new(d)
                        } else {
                            Fp::new(q - (16 - d))
                        }
                    })
                    .collect()
            }

            fn box_vec_of(seed: u64, k: usize) -> PolyVec {
                let degree = hc::params::RING_DEGREE;
                let mut entries = Vec::with_capacity(k);
                for i in 0..k {
                    entries.push(Rq::from_coeffs(&box_coeffs(
                        seed.wrapping_add(i as u64 * 0x100),
                        degree,
                    )));
                }
                PolyVec::new(entries)
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

            fn d_polymatrix(a: &hc::linalg::PolyMatrix) -> u64 {
                let r = a.rows();
                let mut acc = support::mix_len(0, r);
                let mut i = 0usize;
                while i < r {
                    acc = support::mix(acc, d_polyvec(a.row(i)));
                    i += 1;
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
                // The two corpora are what their cases claim: the ordinary draw
                // is outside the box, the box draw is inside it. Asserted here
                // so `in_sb_box` cannot quietly become a second reject-draw row.
                let degree = hc::params::RING_DEGREE;
                assert!(
                    !hc::quadeval::in_sb(&Rq::from_coeffs(&support::corpus(
                        0x9E11_0000_0000_0001,
                        degree
                    ))),
                    "the ordinary corpus must lie outside the box"
                );
                assert!(
                    hc::quadeval::in_sb(&Rq::from_coeffs(&box_coeffs(
                        0x9E11_0000_0000_0009,
                        degree
                    ))),
                    "the box corpus must lie inside the box"
                );
            }

            // -- cases ------------------------------------------------------

            /// The box test over one ring element at real `RING_DEGREE`:
            /// `degree` centered comparisons, no early exit.
            ///
            /// **This row cannot carry a candidate verdict**, for two reasons
            /// found by the §4 audit of 2026-09-07 (NOTES.md § "The §4 audit of
            /// target 2's rows"). Its corpus answers `false` (see `in_sb_box`
            /// for the honest one) *and*, more stubbornly, one ring element is
            /// the wrong shape: `in_sb`'s per-coefficient sign test compiles to
            /// a real data-dependent branch, and re-feeding the same 1024
            /// coefficients ~11M times reads 0.44 ns/coefficient against the
            /// 2.54 ns/coefficient the same machine code costs over a vector it
            /// cannot learn. A caller never sees that regime, so a candidate
            /// that changes the branch structure would read the wrong sign here.
            /// Read `vec_in_sb`/`vec_in_sb_box` instead; both rows are kept
            /// because removing one changes what the other's id means.
            pub fn in_sb(m: Mode<'_, '_>, degree: usize) -> u64 {
                let a = Rq::from_coeffs(&support::corpus(0x9E11_0000_0000_0001, degree));
                support::run(m, || hc::quadeval::in_sb(black_box(&a)), d_bool)
            }

            /// The same over a vector, and **the row that carries the verdict**
            /// for both of these functions: at 256 entries the coefficient
            /// stream is long enough that the branch predictor cannot memorize
            /// it, so this is `in_sb`'s honest per-coefficient cost (2.54 ns,
            /// against the 0.44 ns the single-`Rq` row reports).
            ///
            /// REDUCED width, and the earlier arithmetic here was wrong: the
            /// scheme's widths are `paper_rel_out`'s three, 8192 (`carrier_dec`)
            /// / 8192 (`flat`) / 40960 (`z_dec`), and 8192 would cost ~21 ms
            /// per iteration -- feasible, below this binary's own ~33 ms
            /// control. 256 is kept because it is what has been measured since
            /// the freeze and changing it changes what the row's id means;
            /// re-registering at a scheme width is a deliberate re-freeze, not
            /// an edit (`rust-bench` §1).
            pub fn vec_in_sb(m: Mode<'_, '_>, k: usize) -> u64 {
                let v = vec_of(0x9E11_0000_0000_0002, k);
                support::run(m, || hc::quadeval::vec_in_sb(black_box(&v)), d_bool)
            }

            /// The box test on an input that lies **inside** the box: the honest
            /// workload, where every coefficient passes and the function has to
            /// look at all `degree` of them. `in_sb` above draws from `[1, q)`,
            /// so each of its coefficients is outside the box with probability
            /// ≈ 1 - 3.7·10⁻⁹; on that corpus an early-exit rewrite would read as
            /// a ~1000× win that exists only for rejected inputs -- the
            /// `Rq::is_zero` trap of `rust-bench` §2.
            ///
            /// It fixes the corpus and **not** the shape: like `in_sb` it feeds
            /// one fixed ring element, so it inherits the memorized-branch
            /// regime described there and cannot carry a verdict either. The
            /// honest in-box row is `vec_in_sb_box`. Coefficients here are
            /// `0` at rate 1/16 -- `support`'s corpus never emits zero, but a
            /// balanced digit legitimately is zero, so the rule is relaxed
            /// deliberately and nothing in `in_sb` short-circuits on it.
            pub fn in_sb_box(m: Mode<'_, '_>, degree: usize) -> u64 {
                let a = Rq::from_coeffs(&box_coeffs(0x9E11_0000_0000_0009, degree));
                support::run(m, || hc::quadeval::in_sb(black_box(&a)), d_bool)
            }

            /// `vec_in_sb` on an all-inside vector, at the same REDUCED width and
            /// for the same reason as `in_sb_box` -- and, with `vec_in_sb`, one
            /// of the two rows here that can carry a verdict. The two read
            /// within 0.1% of each other (664.1 vs 664.7 µs), which is the
            /// expected answer: the box decision is computed branchlessly, so
            /// only the sign dispatch branches and it is a coin flip on either
            /// corpus.
            pub fn vec_in_sb_box(m: Mode<'_, '_>, k: usize) -> u64 {
                let v = box_vec_of(0x9E11_0000_0000_000A, k);
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

            /// The c5 block matrix of the `R^lin` adapter, materialized:
            /// `k × blocks·(k·digits)` entries, one `scalar_mul` on the gadget
            /// diagonal and a zero elsewhere. Paired with the `tensor_g` row
            /// above, since upstream's `tensorGMatrix_mulVec` says the two
            /// compute the same thing -- so the pair measures what
            /// materializing the block costs over applying it.
            pub fn tensor_g_matrix(m: Mode<'_, '_>, blocks: usize) -> u64 {
                let digits = hc::params::GADGET_DIGITS;
                let rows = hc::params::INNER_ROWS;
                let c = vec_of(0x9E11_0000_0000_000A, blocks);
                support::run(
                    m,
                    || {
                        hc::quadeval::tensor_g_matrix(
                            black_box(rows),
                            black_box(digits),
                            black_box(&c),
                        )
                    },
                    d_polymatrix,
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
    // REDUCED width. 256 entries = 262144 coefficients, ~665 µs. The scheme's
    // widths are 8192 / 8192 / 40960 (`paper_rel_out`'s three); see the case
    // doc for why the row stays at 256 and what the earlier note here got wrong.
    let reduced_width = 256;

    // @covers quadeval::in_sb
    bench_case!(c, "quadeval/in_sb", in_sb, [degree]);
    // @covers quadeval::vec_in_sb
    bench_case!(c, "quadeval/vec_in_sb", vec_in_sb, [reduced_width]);
    // The honest, all-inside workload of the same two functions (case docs).
    // @covers quadeval::in_sb
    bench_case!(c, "quadeval/in_sb_box", in_sb_box, [degree]);
    // @covers quadeval::vec_in_sb
    bench_case!(c, "quadeval/vec_in_sb_box", vec_in_sb_box, [reduced_width]);
    // @covers quadeval::carrier_entry
    bench_case!(c, "quadeval/carrier_entry", carrier_entry, [reduced_rows]);
    // @covers quadeval::tensor_g1
    bench_case!(c, "quadeval/tensor_g1", tensor_g1, [reduced_blocks]);
    // @covers quadeval::tensor_g
    bench_case!(c, "quadeval/tensor_g", tensor_g, [reduced_blocks]);
    // @covers quadeval::tensor_g_matrix
    bench_case!(c, "quadeval/tensor_g_matrix", tensor_g_matrix, [reduced_blocks]);
}

criterion_group! {
    name = benches;
    config = support::criterion_config();
    targets = quadeval_benches
}
criterion_main!(benches);
