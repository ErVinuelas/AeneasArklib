//! Wall-clock time for the ring-switching link: the quotient-digit map, the two
//! presentation changes over it, and the lifted witness the Ajtai lift commits.
//!
//! Five cases. Four run at the widths the scheme instantiates; one is
//! **REDUCED**, with its arithmetic and its removal condition recorded at the
//! case:
//!
//! | case | size | why |
//! |---|---|---|
//! | `rho_digits` | `RING_DEGREE` | real; one digit of one row |
//! | `rho_as_rq` | `RING_DEGREE` | real; a `d`-wide copy |
//! | `rho_digit_as_rq` | `RLIN_ROWS` | real row count; one flattened entry |
//! | `lift_message` | `RLIN_COLS` × `RLIN_ROWS` | real, at a measured 904 MiB peak |
//! | `lift_commit` | REDUCED (W1) | `LIFT_COLS = 57 384` schoolbook ring muls |
//!
//! From the shakeout run of 2026-09-07 -- orders of magnitude, not verdicts.
//! The machine was **not** quiet (load ~2, a browser and a music player alive)
//! and its two `_control` readings sat 2.6% apart on identical code, so nothing
//! here has been through `make run-bench` or earned a candidate column:
//! `_control/ringswitch` ~36 ms, `rho_digits` ~2.4 µs, `rho_as_rq` ~725 ns,
//! `rho_digit_as_rq` ~3.4 µs, `lift_message` ~260 ms at a measured 904 MiB peak
//! RSS, `lift_commit` ~18 ms.
//!
//! The two terminal shortness checks are **not** here. They are
//! `endpiece::*` items, so `harness.py` attributes them to a bench binary
//! named `endpiece`, and a binary is defined by its `_control`; they live in
//! `benches/endpiece.rs` with `_control/endpiece`. See that file's header
//! § "Why this is its own binary" for the failure that arrangement fixes.
//!
//! # Sizes, and the two places a size can hide
//!
//! Every size a case is measured at is registered in `ringswitch_benches`
//! below and appears in the criterion case id, and every one of them is either
//! a `params` constant or a named file-scope constant that says which `params`
//! constant it is a reduction of. That is not decoration: a reduced row whose
//! reduction is invisible is a row whose composition nobody can check, and this
//! file has already produced one.
//! `lift_message` was registered at `[8]` while its *second* dimension, the
//! quotient-row count, was a bare `2` inside the case body. At the real shape
//! that row is 57 344 `z`-copies against 40 digit extractions -- ~99.96% copy
//! by time; at `(8, 2)` it was 8 copies against 16 extractions, roughly half
//! and half. Not a smaller version of the mixture, the opposite one. Both
//! dimensions of a two-dimensional case now come from the file-scope constants
//! below, next to the `params` values they are (or are not) a reduction of.
//!
//! # Which rows are a real A/B (the §4 audit's `nm` check)
//!
//! Fat LTO merges a bench case's three variants into one function whenever the
//! inlined body no longer references a variant-distinct symbol, which a
//! *null* slot always allows -- NOTES.md § "The §4 audit of target 2's rows",
//! finding 1. Run on this binary built `--features candidate`, looking at the
//! symbol that is actually timed (`Bencher::iter::<_, &mut <variant>::<case>::
//! {closure#0}>`):
//!
//! | case | timed copies |
//! |---|---|
//! | `_control/ringswitch` | **merged** (one) |
//! | `rho_digits` | **merged** |
//! | `rho_as_rq` | **merged** |
//! | `rho_digit_as_rq` | three -- `now`, `candidate`, `genesis` |
//! | `lift_message` | three |
//! | `lift_commit` | three |
//!
//! A merged row has **no layout bias to measure**, so a null-slot sweep of it
//! reports a lower bound and its `_control` -- merged too, as every control is
//! -- cannot correct for a term it never saw. That does not make a merged row's
//! candidate verdict wrong: a real candidate is not byte-identical, so it does
//! not merge and the A/B is genuine during the pass. It makes the *floor*
//! borrowed from a null sweep optimistic for exactly those rows. Re-run the
//! check after any edit here:
//!
//! ```text
//! nm -C target/release/deps/ringswitch-* | grep 'Bencher>::iter::.*ringswitch::'
//! ```
//!
//! # Why the digit index is `0` for `rho_digits` and `GADGET_DIGITS - 1` for
//! `rho_digit_as_rq`
//!
//! The two cases want different things and deliberately disagree.
//!
//! `rho_digits` measures the **coefficient loop and the `Rq` construction**
//! around `gadget::balanced_digit_at`. The per-index division chain inside
//! `balanced_digit_at` is `gadget/digit_at`'s cost and is already priced there,
//! so `u = 0` keeps it out of the reading; a row at `u = GADGET_DIGITS - 1`
//! would differ from this one by exactly `RING_DEGREE · (digits - 1)` shifts,
//! which `gadget/digit_at` prices.
//!
//! `rho_digit_as_rq` measures the **flattening**: `j / GADGET_DIGITS` selects
//! the row and `j % GADGET_DIGITS` its digit. Here the deepest index *is* the
//! row worth having, because the deepest index is what the caller pays.
//! `endpiece::rho_digits_short_check` and `ringswitch::lift_message` both walk
//! `j` over the whole `RLIN_ROWS · GADGET_DIGITS = 40`-entry block, so
//! `u = GADGET_DIGITS - 1` is the worst entry of a loop every real consumer
//! runs to completion -- not an unrepresentative corner. Taking it at `j = 0`
//! instead would report the cheapest of the forty and call it the entry cost.
//!
//! See `benches/support/mod.rs` for the corpus discipline, the digest oracle and
//! what the `_control` case is.

mod support;

use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};

// ---------------------------------------------------------------------------
// Sizes
//
// Both dimensions of every multi-dimensional case, in one place, read from
// `hachi::params` -- and from `hachi`'s copy of it deliberately, not each
// variant's `hc::params`, so that all three variants are measured on the same
// corpus even if a candidate edits `params.rs`. (`case!`'s digest would catch a
// size change through `mix_len`, but a corpus that differs between variants is
// not something a benchmark should be *able* to express.)
//
// One-dimensional cases take their size at their registration below, which is
// where the criterion case id reads it from.
// ---------------------------------------------------------------------------

/// `lift_message`'s `z` width: **real**, `RLIN_COLS = 57 344` ring elements.
///
/// Not reduced, and the earlier `[8]` was wrong rather than merely small.
/// `lift_message` copies `z` entry by entry and then appends
/// `rho_rows · GADGET_DIGITS` freshly extracted digits, so at the real shape it
/// is `57 344` copies against `40` digit extractions: **99.93% of the entries
/// and ~99.96% of the time** is the copy (~260 ms total against 40 × the 2.4 µs
/// `ringswitch/rho_digits` row ≈ 96 µs of extraction).
///
/// At `z = 8` with two quotient rows it was 8 copies against 16 extractions --
/// call it half and half, on the same shakeout numbers. That is not a smaller
/// version of the real mixture, it is the opposite one, and it matters because
/// the fused/streaming lift this case's removal condition names is a change to
/// the **copy** half. At `(8, 2)` the copy half was barely present, so the row
/// could not have shown such a candidate winning.
///
/// The cost of the real shape is memory, not time: `z` is
/// `57 344 · RING_DEGREE` field elements (~448 MiB) and `lift_message` returns
/// a copy of it, so the case peaks at **904 MiB** (measured maximum RSS, which
/// is the derived ~896 MiB plus the binary). That is affordable here; the
/// inverted composition was not.
const LIFT_MESSAGE_Z: usize = hachi::params::RLIN_COLS;

/// `lift_message`'s quotient-row count: **real**, `RLIN_ROWS = 5`.
///
/// This is the dimension that was hidden. It was a bare `2` inside the case
/// body, invisible at the registration and absent from the case id, so the row
/// carried a second undocumented reduction on top of the registered one. If
/// this case ever has to be reduced again, reduce *both* dimensions in
/// proportion -- `z : digits` is `57 344 : 40` ≈ `1434 : 1`, so one quotient
/// row wants `z = 8 · 1434 = 11 469` -- write the ratio down, and keep both
/// numbers here.
const LIFT_MESSAGE_RHO_ROWS: usize = hachi::params::RLIN_ROWS;

/// `lift_commit`'s `z` width: **REDUCED**, from `RLIN_COLS = 57 344`.
///
/// W1. `lift_commit` performs `μ + n·δ = 57 384` schoolbook `ring::mul`s against a `D_ROWS × LIFT_COLS = 1 × 57 384` key (since I2 fused: no `lift_message` in its path) at
/// `D_ROWS × LIFT_COLS = 1 × 57 384`, i.e. `57 384` schoolbook `ring::mul`s of
/// `RING_DEGREE² = 2^20` field operations each -- minutes per criterion
/// iteration. Removal condition: a sub-quadratic `ring::mul` champion, which is
/// the same condition `exclusions.toml`'s Fig. 9 section carries.
///
/// **What survives the reduction is the composition**, which is what this row
/// is for, and it survives it comfortably. Priced against the shakeout's
/// `ring/mul` at 1.511 ms:
///
/// * real: `57 384 × 1.511 ms = 86.7 s` of `mat_vec_mul` against ~0.26 s of
///   `lift_message` -- **99.70%** multiplication;
/// * here: width `LIFT_COMMIT_Z + GADGET_DIGITS = 12`, so `12 × 1.511 ms =
///   18.13 ms` against a measured 18.16 ms total -- **99.83%**.
///
/// A candidate that speeds up ring multiplication moves this row; one that
/// speeds up the lift's copying does not, at either width. So unlike
/// `lift_message` this case is insensitive to the mixture -- only to the ring
/// product -- and reducing both dimensions hard is safe.
const LIFT_COMMIT_Z: usize = 4;

/// `lift_commit`'s quotient-row count: **REDUCED**, from `RLIN_ROWS = 5`.
///
/// One row, so the width is `LIFT_COMMIT_Z + GADGET_DIGITS`. See
/// [`LIFT_COMMIT_Z`] for the arithmetic and for why this row tolerates the
/// reduction that [`LIFT_MESSAGE_Z`] does not.
const LIFT_COMMIT_RHO_ROWS: usize = 1;

/// The honest lift prover's `R^lin` width: **REDUCED**, from `RLIN_COLS = 57 344`,
/// and **block shaped**, because a dense one measures an input the protocol
/// cannot produce.
///
/// W1 in its unreduced form. `c_row_sum` performs `μ` products of two
/// `RING_DEGREE`-coefficient polynomials **without** the negacyclic fold --
/// `2^20` field multiplications each, the same count as `ring::mul` -- so at
/// the pin one row is `57 344 × ~1.5 ms ≈ 86 s` and `honest_lift_witness` is
/// `RLIN_ROWS = 5` of them. Removal condition: a sub-quadratic `ring::mul`
/// champion whose kernel also serves the unreduced product (the `long_mul`
/// helper is `ring::mul` minus the fold). What survives the reduction is the
/// composition the row exists to price: `μ` long products, one coefficientwise
/// accumulation, one `O(N)` division per row.
///
/// # Why the shape, and not just the width
///
/// `quadeval::rlin_stmt` never emits a dense `M`. It builds c1 as `[D | 0 | 0]`,
/// c2 as `[0 | B | 0]` and c3 as `[Gᵀb | 0 | 0]`, and at the pin
/// (`cw + ct + cz = 8192 + 8192 + 40 960 = 57 344`) rows c1, c2 and c3 are
/// **86% literal `Rq::zero()`** -- the zeros are `Rq::zero()` pushes in
/// `src/quadeval.rs`, not a property of some input distribution. A dense
/// REDUCED statement therefore prices work the prover never does, and it is
/// blind to any candidate that exploits the structure: there is nothing to
/// skip, so such a candidate reads as a small loss.
///
/// `28 = 4 · 7` keeps the pin's proportions exactly (`cw : ct : cz = 1 : 1 : 5`,
/// so `4 : 4 : 20`) while keeping the dense part the size the previous dense
/// rows used: 4 dense entries and 24 zeros, 86% zeros as at the pin.
///
/// # What this replaced, and what that costs
///
/// The four-column dense cases `ringswitch/c_row_sum`, `c_quotient` and
/// `honest_lift_witness` were **retired** for these (user decision,
/// 2026-09-17). The ids changed rather than the old ones being silently
/// redefined, so the re-baseline announces itself: those rows' `vs genesis`
/// history stops here, and its last reading is the pre-bump sweep
/// `logs/runs/full-20260916-preBump.json`
/// (run `20260916T1817+0200-af4f447d`, `c_row_sum/4` and siblings).
///
/// The dense cases were **not wrong**, which is why this was a decision and not
/// a bug fix: candidate R was accepted on exactly them at −43%, and correctly,
/// because R sped up `long_mul` itself and that is structure-independent. They
/// are the right instrument for structure-independent candidates and the wrong
/// one for structure-exploiting ones, and the project chose one instrument over
/// carrying both (NOTES 2026-09-17).
const LIFT_PROVER_COLS: usize = 28;

/// One body per case, instantiated once per variant crate. Writing the variants
/// separately is how a benchmark quietly starts comparing two different
/// computations; a macro makes that impossible.
macro_rules! define_cases {
    ($modname:ident, $hachi:path) => {
        mod $modname {
            use std::hint::black_box;

            use cpoly::Ext4;

            use $hachi as hc;

            use crate::support::{self, Mode};

            type Rq = hc::ring::Rq;
            type PolyVec = hc::linalg::PolyVec;
            type PolyMatrix = hc::linalg::PolyMatrix;
            type QuotientRow = hc::ringswitch::QuotientRow;
            type LiftedWitness = hc::ringswitch::LiftedWitness;

            // -- corpus -----------------------------------------------------

            /// The quotient row the case decomposes. One draw from its own
            /// stream, so every variant sees the same row.
            fn row() -> Rq {
                let degree = hc::params::RING_DEGREE;
                Rq::from_coeffs(&support::corpus(0x8047_0000_0000_0001, degree))
            }

            fn quotient_row(seed: u64) -> QuotientRow {
                QuotientRow::new(&support::corpus(seed, hc::params::RING_DEGREE))
            }

            fn quotient_rows(seed: u64, rows: usize) -> Vec<QuotientRow> {
                let mut out = Vec::new();
                let mut i = 0usize;
                while i < rows {
                    out.push(quotient_row(seed.wrapping_add(i as u64)));
                    i += 1;
                }
                out
            }

            /// [`vec_of`] with every coefficient **centred below
            /// `CHAIN_GAMMA`** -- the shape an honest lifted witness has.
            ///
            /// `vec_of` draws from `[1, q)`, which is what the protocol never
            /// produces here: `z` is the `R^lin` witness the end piece checks
            /// for shortness, so a uniform draw is a witness every verifier
            /// rejects. That did not matter while every path cost the same;
            /// card T40 makes it decide which path runs, so the honest shape
            /// needs a corpus of its own rather than a reinterpretation of
            /// this one.
            fn short_vec_of(seed: u64, n: usize) -> PolyVec {
                let mut out = Vec::new();
                let width = hc::params::RING_DEGREE;
                let g = hc::params::CHAIN_GAMMA;
                let coeffs = support::corpus(seed, n * width);
                let mut i = 0usize;
                while i < n {
                    let mut cs = Vec::with_capacity(width);
                    let mut k = 0usize;
                    while k < width {
                        // [0, 2g] folded to the centred band {0..g} u {q-g..q-1}
                        let r = coeffs[i * width + k].to_u64() % (2 * g + 1);
                        cs.push(cpoly::Fp::new(if r <= g { r } else { hc::params::Q - (r - g) }));
                        k += 1;
                    }
                    out.push(Rq::from_coeffs(&cs));
                    i += 1;
                }
                PolyVec::new(out)
            }

            fn vec_of(seed: u64, n: usize) -> PolyVec {
                let mut out = Vec::new();
                let width = hc::params::RING_DEGREE;
                let coeffs = support::corpus(seed, n * width);
                let mut i = 0usize;
                while i < n {
                    out.push(Rq::from_coeffs(&coeffs[i * width..(i + 1) * width].to_vec()));
                    i += 1;
                }
                PolyVec::new(out)
            }

            fn matrix_of(seed: u64, rows: usize, cols: usize) -> PolyMatrix {
                let mut out = Vec::new();
                let mut i = 0usize;
                while i < rows {
                    out.push(vec_of(seed.wrapping_add(i as u64), cols));
                    i += 1;
                }
                PolyMatrix::new(out)
            }

            // -- digests (outside every timed region) -----------------------

            fn d_ext4(v: &Ext4) -> u64 {
                let mut acc = support::mix(0, v.c0.to_u64());
                acc = support::mix(acc, v.c1.to_u64());
                acc = support::mix(acc, v.c2.to_u64());
                support::mix(acc, v.c3.to_u64())
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

            // -- the reconstruction check -----------------------------------

            /// `Σ_u bᵘ · rho_digits(ρ, u) = ρ`, asserted before anything is
            /// timed -- the specification's `rhoDigits_reconstruct`. A timing of
            /// a digit map that does not reconstruct would be meaningless, and
            /// this is what makes it a real check that the frozen and slot
            /// copies were copied rather than paraphrased.
            pub fn check() {
                let digits = hc::params::GADGET_DIGITS;
                let rho = row();
                let mut acc = Rq::zero();
                let mut u = 0usize;
                while u < digits {
                    acc = acc.add(&hc::ringswitch::rho_digits(&rho, u).scalar_mul(
                        hc::gadget::base_pow(u),
                    ));
                    u += 1;
                }
                assert!(
                    acc.equals(&rho),
                    "the quotient digits do not reconstruct the row; a timing of them \
                     would be meaningless"
                );
            }

            // -- the case ---------------------------------------------------

            /// One digit of one quotient row: `degree` balanced digits and one
            /// `Rq::from_coeffs`. See the module doc for why the digit index is
            /// `0` and not the deepest one.
            ///
            /// ~2.4 µs in the shakeout, which is *just* outside the 100 ns -
            /// 2 µs band the null-slot sweep found unreliable (`rho_as_rq`
            /// below is inside it, and says what that costs). Twenty percent of
            /// clearance is not much: if a candidate makes this row faster it
            /// may well land inside the band, and the verdict on it should then
            /// be read the way `rho_as_rq`'s is.
            pub fn rho_digits(m: Mode<'_, '_>, _degree: usize) -> u64 {
                let rho = row();
                support::run(
                    m,
                    || hc::ringswitch::rho_digits(black_box(&rho), black_box(0)),
                    d_rq,
                )
            }

            /// `rhoAsRq`: copy the quotient polynomial's coefficient
            /// presentation into the ring carrier. One `Rq::copy` of
            /// `RING_DEGREE` field elements, and nothing else -- the type
            /// change is free, the copy is the whole reading.
            ///
            /// The receiver is `black_box`ed. Without it the timed closure
            /// captures a `QuotientRow` the optimizer can see the construction
            /// of, and `to_rq` is a `Vec` push loop over its coefficients:
            /// exactly the shape LLVM can hoist, narrow, or fold against a
            /// known source. Every other case in this file black-boxes its
            /// inputs (`support/mod.rs` § "the two failures a green bench run
            /// will not show you"); this one was the exception, and there was
            /// no reason for it.
            ///
            /// **This row cannot carry a candidate verdict as the harness
            /// stands.** A `d = 1024` copy read **~725 ns** in the shakeout,
            /// which is inside the 100 ns - 2 µs band where the certified
            /// null-slot sweep of 2026-09-07 measured byte-identical code
            /// producing false 5-8% verdicts after recentering (NOTES.md § "The
            /// certified null-slot sweep"; `perf-loop` § "The one rule"). The
            /// 5% floor held everywhere outside that band and does not hold
            /// inside it, so this row waits on a per-band floor or a local
            /// control. It is kept because the vs-genesis column and the
            /// digest oracle are still worth having on it.
            pub fn rho_as_rq(m: Mode<'_, '_>, _degree: usize) -> u64 {
                let rho = quotient_row(0x8047_0000_0000_0010);
                support::run(m, || black_box(&rho).to_rq(), d_rq)
            }

            /// One flattened `(row, digit)` entry at the real ring degree and
            /// the real row count.
            ///
            /// `j` is the **deepest** index of the block, `rows ·
            /// GADGET_DIGITS - 1`, so `j % GADGET_DIGITS = GADGET_DIGITS - 1`
            /// and the digit extraction pays the longest division chain
            /// `gadget::balanced_digit_at` has. That is the opposite of
            /// `rho_digits` above, which is measured at `u = 0` -- deliberately,
            /// and the module header § "Why the digit index is `0` for
            /// `rho_digits` and `GADGET_DIGITS - 1` for `rho_digit_as_rq`"
            /// is where the two choices are argued against each other. In
            /// short: `rho_digits` is measuring the coefficient loop, so the
            /// chain is noise it excludes; this case is measuring what a caller
            /// pays per block entry, and every caller (`lift_message`,
            /// `endpiece::rho_digits_short_check`) runs `j` to the end of the
            /// block, so the deepest entry is a real entry rather than a corner.
            pub fn rho_digit_as_rq(m: Mode<'_, '_>, rows: usize) -> u64 {
                let rho = quotient_rows(0x8047_0000_0000_0020, rows);
                let j = rows * hc::params::GADGET_DIGITS - 1;
                support::run(
                    m,
                    || hc::ringswitch::rho_digit_as_rq(black_box(&rho), black_box(j)),
                    d_rq,
                )
            }

            /// The lift's message vector at the **real** shape: `z` of
            /// `RLIN_COLS = 57 344` ring elements copied entry by entry, then
            /// `RLIN_ROWS · GADGET_DIGITS = 40` quotient digits extracted and
            /// appended. ~99.96% of the time is the copy, which is the mixture
            /// a caller actually sees and the one the removal condition is
            /// about: a fused/streaming lift commitment, **not** faster ring
            /// multiplication (there is no ring product here at all) and not a
            /// smaller sumcheck cube.
            ///
            /// ~448 MiB in, ~448 MiB out; measured peak RSS 904 MiB. Both
            /// dimensions come from [`crate::LIFT_MESSAGE_Z`] and
            /// [`crate::LIFT_MESSAGE_RHO_ROWS`], which is where the W3 note that
            /// used to sit here now lives -- including why the previous
            /// `(z = 8, rho_rows = 2)` reading was inverted rather than small.
            pub fn lift_message(m: Mode<'_, '_>, z_len: usize) -> u64 {
                let w = LiftedWitness::new(
                    vec_of(0x8047_0000_0000_0030, z_len),
                    quotient_rows(0x8047_0000_0000_0040, crate::LIFT_MESSAGE_RHO_ROWS),
                );
                support::run(m, || hc::ringswitch::lift_message(black_box(&w)), d_polyvec)
            }

            /// W1 REDUCED: the real key is `D_ROWS × LIFT_COLS = 1 × 57 384`,
            /// hence 57 384 schoolbook ring products (~6.02e10 field
            /// operations). Removal condition: a sub-quadratic `ring::mul`
            /// champion.
            ///
            /// Both reduced dimensions are [`crate::LIFT_COMMIT_Z`] and
            /// [`crate::LIFT_COMMIT_RHO_ROWS`], stated there against the
            /// `params` constants they cut and with the composition arithmetic
            /// that says why this row survives the cut where `lift_message`
            /// does not. The key's width is derived, not chosen: it is
            /// `LIFT_COMMIT_Z + LIFT_COMMIT_RHO_ROWS · GADGET_DIGITS`, exactly
            /// as `LIFT_COLS` is `RLIN_COLS + RLIN_ROWS · GADGET_DIGITS`.
            pub fn lift_commit(m: Mode<'_, '_>, z_len: usize) -> u64 {
                let rho_rows = crate::LIFT_COMMIT_RHO_ROWS;
                let width = z_len + rho_rows * hc::params::GADGET_DIGITS;
                let w = LiftedWitness::new(
                    vec_of(0x8047_0000_0000_0050, z_len),
                    quotient_rows(0x8047_0000_0000_0060, rho_rows),
                );
                let d_key = matrix_of(0x8047_0000_0000_0070, 1, width);
                support::run(
                    m,
                    || hc::ringswitch::lift_commit(black_box(&d_key), black_box(&w)),
                    d_polyvec,
                )
            }

            /// [`lift_commit`] on the **honest** witness shape (card T40).
            ///
            /// Same key, same widths, same digest oracle; the only difference
            /// is that `z` is centred below `CHAIN_GAMMA`, which is what the
            /// end piece requires of it. The existing `lift_commit` row keeps
            /// its uniform draw and its history, and measures the fallback.
            pub fn lift_commit_short(m: Mode<'_, '_>, z_len: usize) -> u64 {
                let rho_rows = crate::LIFT_COMMIT_RHO_ROWS;
                let width = z_len + rho_rows * hc::params::GADGET_DIGITS;
                let w = LiftedWitness::new(
                    short_vec_of(0x8047_0000_0000_0051, z_len),
                    quotient_rows(0x8047_0000_0000_0061, rho_rows),
                );
                let d_key = matrix_of(0x8047_0000_0000_0071, 1, width);
                support::run(
                    m,
                    || hc::ringswitch::lift_commit(black_box(&d_key), black_box(&w)),
                    d_polyvec,
                )
            }

            fn d_words(v: &Vec<cpoly::Fp>) -> u64 {
                let n = v.len();
                let mut acc = support::mix_len(0, n);
                let mut k = 0usize;
                while k < n {
                    acc = support::mix(acc, v[k].to_u64());
                    k += 1;
                }
                acc
            }

            fn d_witness(w: &LiftedWitness) -> u64 {
                let mut acc = d_polyvec(w.z());
                let rows = w.rho().len();
                acc = support::mix_len(acc, rows);
                let mut i = 0usize;
                while i < rows {
                    acc = support::mix(acc, d_rq(&w.rho()[i].to_rq()));
                    i += 1;
                }
                acc
            }

            /// A REDUCED statement with the **block** shape of `rlin_stmt`'s c1 row,
            /// `[D | 0 | 0]`: the first `cols / 7` entries dense, the rest
            /// `Rq::zero()`. See [`LIFT_PROVER_COLS`] for why the dense
            /// generator above cannot stand in for this.
            fn statement_blocks(seed: u64, cols: usize) -> hc::ringswitch::RlinStatement {
                let cw = cols / 7;
                let dense = vec_of(seed, cw);
                let mut row: Vec<Rq> = Vec::new();
                let mut k = 0usize;
                while k < cw {
                    row.push(dense.get(k).copy());
                    k += 1;
                }
                let mut z = 0usize;
                while z < cols - cw {
                    row.push(Rq::zero());
                    z += 1;
                }
                hc::ringswitch::RlinStatement::new(
                    PolyMatrix::new(vec![PolyVec::new(row)]),
                    vec_of(seed.wrapping_add(0x100), 1),
                    hc::params::CHAIN_GAMMA,
                )
            }

            /// [`c_row_sum`] against the block-shaped row: same composition, but
            /// 86% of the columns are zero, as at the pin.
            pub fn c_row_sum_blocks(m: Mode<'_, '_>, cols: usize) -> u64 {
                let s = statement_blocks(0x8047_0000_0000_0100, cols);
                let z = vec_of(0x8047_0000_0000_0110, cols);
                support::run(
                    m,
                    || hc::ringswitch::c_row_sum(black_box(&s), black_box(&z), black_box(0)),
                    d_words,
                )
            }

            /// `honestLiftWitnessC` at one row against the block-shaped row:
            /// one `c_quotient` plus copying `z` into the witness.
            pub fn honest_lift_witness_blocks(m: Mode<'_, '_>, cols: usize) -> u64 {
                let s = statement_blocks(0x8047_0000_0000_0140, cols);
                let z = vec_of(0x8047_0000_0000_0150, cols);
                support::run(
                    m,
                    || hc::ringswitch::honest_lift_witness(black_box(&s), black_box(&z)),
                    d_witness,
                )
            }

            /// [`c_quotient`] against the block-shaped row.
            pub fn c_quotient_blocks(m: Mode<'_, '_>, cols: usize) -> u64 {
                let s = statement_blocks(0x8047_0000_0000_0120, cols);
                let z = vec_of(0x8047_0000_0000_0130, cols);
                support::run(
                    m,
                    || hc::ringswitch::c_quotient(black_box(&s), black_box(&z), black_box(0)),
                    |r| d_rq(&r.to_rq()),
                )
            }

            /// `cEvalAt` at the **real** ring degree: `d = 1024` terms, each
            /// one `Fp`→`Ext4` embedding, one extension multiply and one add --
            /// plus the power, which the specification's `eval₂` recomputes per
            /// term (`x ^ i` inside the fold), so the row is `~d²/2` extension
            /// multiplies. That quadratic is the shape the baseline must have:
            /// hoisting the power into a running product is the first
            /// optimization this row exists to price.
            pub fn c_eval_at(m: Mode<'_, '_>, degree: usize) -> u64 {
                assert_eq!(degree, hc::params::RING_DEGREE, "c_eval_at size is the ring degree");
                let p: Rq = Rq::from_coeffs(&support::corpus(0x8047_3001, degree));
                let c = support::corpus(0x8047_3002, 4);
                let alpha = Ext4::new(c[0], c[1], c[2], c[3]);
                support::run(
                    m,
                    || hc::ringswitch::c_eval_at(black_box(alpha), black_box(&p)),
                    d_ext4,
                )
            }

            /// The same evaluation at the cyclotomic modulus `X^d + 1`, whose
            /// `d + 1` coefficients are all zero but two. Registered separately
            /// from [`c_eval_at`] because the *optimization* differs: this one
            /// collapses to `α^d + 1`, ten squarings at `d = 1024`, which is a
            /// ~50 000× cut rather than the constant factor the general
            /// evaluation admits. Pinned by
            /// `ringswitch_semantics::c_eval_at_modulus_is_alpha_to_the_d_plus_one`
            /// before any candidate touches it.
            pub fn c_eval_at_modulus(m: Mode<'_, '_>, degree: usize) -> u64 {
                assert_eq!(degree, hc::params::RING_DEGREE, "size is the ring degree");
                let c = support::corpus(0x8047_3003, 4);
                let alpha = Ext4::new(c[0], c[1], c[2], c[3]);
                support::run(
                    m,
                    || hc::ringswitch::c_eval_at_modulus(black_box(alpha)),
                    d_ext4,
                )
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
                support::run(m, || PolyVec::zeros(black_box(n)), d_polyvec)
            }
        }
    };
}

define_cases!(now, hachi);
define_cases!(genesis, hachi_genesis);
#[cfg(feature = "candidate")]
define_cases!(candidate, hachi_candidate);

fn ringswitch_benches(c: &mut Criterion) {
    now::check();
    genesis::check();
    #[cfg(feature = "candidate")]
    candidate::check();

    // The run's sanity check: identical source in every variant, so anything it
    // reads is the harness disagreeing with itself. Runs first, while the machine
    // is in the same state the first real cases will see.
    bench_case!(c, "_control/ringswitch", control, [support::CONTROL_N]);

    let degree = hachi::params::RING_DEGREE;

    // @covers ringswitch::rho_digits
    bench_case!(c, "ringswitch/rho_digits", rho_digits, [degree]);
    // Real size, but the row is inside the null-slot sweep's unreliable timing
    // band; see the case doc before reading a candidate column on it.
    // @covers ringswitch::QuotientRow::to_rq
    bench_case!(c, "ringswitch/rho_as_rq", rho_as_rq, [degree]);
    // @covers ringswitch::rho_digit_as_rq
    bench_case!(c, "ringswitch/rho_digit_as_rq", rho_digit_as_rq, [hachi::params::RLIN_ROWS]);
    // REAL shape, both dimensions: `LIFT_MESSAGE_Z` entries of `z` and
    // `LIFT_MESSAGE_RHO_ROWS` quotient rows, ~896 MiB peak. Formerly W3 REDUCED
    // at `[8]` with a hidden `rho_rows = 2`, which inverted the row's 99.7%-copy
    // mixture; see `LIFT_MESSAGE_Z`.
    // @covers ringswitch::lift_message
    bench_case!(c, "ringswitch/lift_message", lift_message, [LIFT_MESSAGE_Z]);
    // W1 REDUCED, both dimensions; see `LIFT_COMMIT_Z` for the arithmetic, the
    // removal condition, and why the composition survives this reduction.
    // @covers ringswitch::lift_commit
    bench_case!(c, "ringswitch/lift_commit", lift_commit, [LIFT_COMMIT_Z]);
    // Card T40's row: the same call on the witness shape the protocol
    // actually produces. Without it the card is invisible -- the fast path is
    // guarded on shortness and the row above draws `z` from `[1, q)`, so a
    // candidate that rewrites the short path entirely reports 0% there.
    // @covers ringswitch::lift_commit
    bench_case!(c, "ringswitch/lift_commit_short", lift_commit_short, [LIFT_COMMIT_Z]);

    // The honest lift prover, W1 REDUCED at one row of `LIFT_PROVER_COLS`
    // columns; see that constant for the arithmetic and the removal condition.
    // The lift rows, at the block shape `rlin_stmt` actually emits; the dense
    // four-column rows these replaced are described in `LIFT_PROVER_COLS`.
    // @covers ringswitch::c_row_sum
    bench_case!(c, "ringswitch/c_row_sum_blocks", c_row_sum_blocks, [LIFT_PROVER_COLS]);
    // @covers ringswitch::c_quotient
    bench_case!(c, "ringswitch/c_quotient_blocks", c_quotient_blocks, [LIFT_PROVER_COLS]);
    // @covers ringswitch::honest_lift_witness
    bench_case!(c, "ringswitch/honest_lift_witness_blocks", honest_lift_witness_blocks, [LIFT_PROVER_COLS]);

    // Both at the **real** ring degree: the mixed `Fp`-coefficient/`Ext4`-point
    // evaluation the zero-check's α side is built on. Two rows for two
    // different removal conditions -- see each case's doc.
    // @covers ringswitch::c_eval_at
    bench_case!(c, "ringswitch/c_eval_at", c_eval_at, [hachi::params::RING_DEGREE]);
    // @covers ringswitch::c_eval_at_modulus
    bench_case!(c, "ringswitch/c_eval_at_modulus", c_eval_at_modulus,
                [hachi::params::RING_DEGREE]);
}

criterion_group! {
    // A per-binary override of `support::criterion_config`, as `benches/commit.rs`
    // and `benches/endpiece.rs` also carry, and forced by one row: `lift_message`
    // at the real shape allocates and copies ~448 MiB per iteration, ~260 ms.
    // Criterion samples linearly by default, so 100 samples would cost
    // `100·101/2 = 5050` executions -- over twenty minutes per variant.
    // `SamplingMode::Auto` refuses that and flips the row to flat sampling, and
    // this override is about how many samples that flat run takes.
    //
    // Be honest about what it does and does not buy. A 260 ms row fits **one**
    // iteration per flat sample at either setting (`ceil(50 ms / 260 ms)` and
    // `ceil(200 ms / 260 ms)` are both 1; measured: 50 iterations over 50
    // samples), so the averaging argument `benches/endpiece.rs` makes does not
    // apply here -- what the override buys on this row is wall clock, ~13s per
    // variant instead of ~27s, i.e. ~40s rather than ~80s across the three
    // variants of a candidate pass, on a row that also spends seconds building
    // its 448 MiB input twice per variant.
    //
    // It does apply to `lift_commit` (~18 ms): 11 iterations per flat sample
    // here against 3 at the default. The three sub-4 µs rows stay linear
    // throughout and simply take 50 samples instead of 100, which is the same
    // trade `commit.rs` accepted and states.
    //
    // Nothing else changes: warm-up and the noise threshold stay as
    // `support::criterion_config` sets them.
    name = benches;
    config = support::criterion_config()
        .sample_size(50)
        .measurement_time(Duration::from_secs(10));
    targets = ringswitch_benches
}
criterion_main!(benches);
