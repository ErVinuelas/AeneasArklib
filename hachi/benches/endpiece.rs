//! Wall-clock time for the nonrecursive opening's two terminal shortness
//! checks, both at the real `params.rs` widths.
//!
//! Two cases, and they are the whole module:
//!
//! * `endpiece/rho_digits_short_check` -- the five-row quotient-digit check:
//!   `RLIN_ROWS · GADGET_DIGITS = 40` calls to `rho_digit_as_rq`, each one a
//!   `RING_DEGREE = 1024`-coefficient balanced-digit loop, and `40 · 1024`
//!   centered comparisons over the digits they return -- 40 960 of each. No
//!   ring product anywhere. `GADGET_BASE = 16` is a `const` power of two, so
//!   every step of `digit_at`'s division chain compiles to a shift rather than
//!   a divide; the chain is `u` steps long for digit `u` and `j` runs over all
//!   eight, so the forty entries pay `5 · 1024 · Σ_{u<8} u = 143 360` shifts
//!   between them, plus three `Fp` reductions per digit and 40 `Rq`
//!   allocations of 8 KiB.
//! * `endpiece/lift_short_check` -- the real `RLIN_COLS = 57 344`-entry `z`
//!   scan: `57 344 · 1024 ≈ 5.87e7` `centered_abs` comparisons through
//!   `commit::vec_l_infty_norm`, then the digit check above. Its ~448 MiB input
//!   is constructed once per variant, outside the timed region, and the timed
//!   region is a linear read of all of it -- memory bandwidth, not arithmetic.
//!
//! # The bands these rows sit in
//!
//! From the shakeout run of 2026-09-07, taken on a machine that was **not**
//! quiet (load ~2, a browser and a music player alive; the two controls read
//! 2.6-5.2% apart on identical code). Orders of magnitude, not verdicts -- no
//! number here has been through `make run-bench`, and the machine that produced
//! them would fail its own control check for a candidate pass:
//!
//! | case | reading | what sets it |
//! |---|---|---|
//! | `_control/endpiece` | ~37 ms | `PolyVec::zeros(8192)`, 64 MiB |
//! | `endpiece/rho_digits_short_check` | ~119 µs | 40 960 digit-and-compare steps, ~2.9 ns each |
//! | `endpiece/lift_short_check` | ~31 ms | 448 MiB read, ~14 GB/s |
//!
//! The digit check is three orders of magnitude below the other two, which is
//! why the sampling override at `criterion_group!` has to say what it does to
//! *each* of them rather than to "this binary".
//!
//! # Why this is its own binary
//!
//! `harness.py` attributes a row to a bench binary by the **module prefix of
//! its group id** (`case_binary`), and divides that binary's own `_control`
//! lean out of every candidate verdict before printing one. So a binary is
//! defined by its control, and `endpiece/*` rows can only be measured in a
//! binary that carries `_control/endpiece`.
//!
//! These two cases first landed inside `benches/ringswitch.rs`, under
//! `_control/ringswitch`. Nothing failed at bench time: the rows ran, printed
//! times, and compared against genesis -- but `case_binary` resolved them to a
//! binary named `endpiece` that had no control, so under `CANDIDATE=1` both
//! candidate verdicts read `unvalidated` and the report exited 2. A missing
//! fairness instrument that only shows up in the loop's *accept* pass is much
//! too late, so `coverage --strict` now rejects a bench file that is not one
//! binary: at least one control, every control in the file naming the same
//! binary, and every other group id prefixed with it (`harness.py`,
//! `covered_paths` → `_one_control_per_binary`).
//!
//! Splitting rather than adding a second `_control/endpiece` row to
//! `ringswitch.rs` is also the cheaper arrangement. That patch works
//! mechanically -- `case_binary` would find the lean -- but it puts a second
//! draw into the run's **worst**-pairwise-control usability veto for a binary
//! whose rows are not in that file, and it leaves `endpiece` measured under a
//! control that ran interleaved with `ringswitch`'s rows rather than its own.
//! (Note the rule is about *binaries*, not about the number of controls: two
//! controls for the **same** binary is what NOTES.md § "The §4 audit of target
//! 2's rows" proposes as the fix for recentering manufacturing a verdict, and
//! the check permits it.) And `src/endpiece.rs` says target 6 will extend this
//! module with the terminal commitment and the multilinear-evaluation
//! conjunction, which wants a file of its own regardless.
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
//! | `_control/endpiece` | **merged** (one) |
//! | `rho_digits_short_check` | **merged** |
//! | `lift_short_check` | **merged** |
//!
//! Every row in this binary merges, controls included. Both cases return a
//! `bool` through a `&`-borrowed input, so nothing variant-distinct survives
//! inlining.
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
//! nm -C target/release/deps/endpiece-* | grep 'Bencher>::iter::.*endpiece::'
//! ```
//!
//! # The void oracle, and what it means for a candidate verdict
//!
//! `endpiece::rho_digits_short_check` is a **tautology at the pinned
//! parameters**. Balanced base-`b` digits are centered-bounded by
//! `⌊b/2⌋ = 8` unconditionally (ArkLib `rhoDigits_valMinAbs_natAbs_le`,
//! `RhoDigits.lean:153`) and the bound it compares against is
//! `CHAIN_GAMMA = 15`, so **no** `Vec<QuotientRow>` this crate can construct
//! makes it answer `false`. Its digest is therefore one bit that is always the
//! same bit, and `support::case!`'s equality assertion -- the thing that
//! normally stops a semantics change being reported as a speedup -- cannot
//! discriminate the real function from `|_| true`. A candidate that deletes the
//! whole digit loop would pass the oracle *and* read as a large win.
//!
//! That is not a reason to drop the row. The optimization the void oracle fails
//! to police is a legitimate and measurable one -- fusing digit extraction into
//! the comparison instead of materializing 40 separate 8 KiB `Rq`s -- and
//! deleting the row would lose it. It is a reason to say so where a reviewer
//! looks, which is here, in the case doc, and in `check()`. **A candidate on
//! this row is a flagged proposal, not a normal candidate**: it is exactly the
//! shape `lean-opt` § "No new value-level preconditions without a gate" sends
//! to explicit user sign-off, because `{ true }` is equal to the ArkLib
//! definition only under an input condition (`bDig = 16`, `bound = 15`) that
//! the definition itself does not impose. The digest proved nothing; a human
//! reads the diff.
//!
//! `endpiece::lift_short_check` is **not** in that position: its `z` conjunct
//! rejects, so `check()` pins both directions of it, transplanted from
//! `tests/ringswitch_semantics.rs`.
//!
//! # Sampling
//!
//! This binary overrides `support::criterion_config`; the override and its
//! arithmetic sit at `criterion_group!` below.
//!
//! See `benches/support/mod.rs` for the corpus discipline, the digest oracle and
//! what the `_control` case is.

mod support;

use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};

// ---------------------------------------------------------------------------
// Sizes
//
// `lift_short_check` is two-dimensional, and the registration below can only
// carry one number, so the other one lives here rather than inside the case
// body -- the arrangement `benches/ringswitch.rs` § "Sizes" argues for, and the
// one whose absence inverted `ringswitch/lift_message`.
//
// It also has to be `hachi`'s constant rather than each variant's `hc::params`,
// and on this row that is load-bearing rather than tidy. Both cases here digest
// to a `bool`, so `case!`'s cross-variant equality carries exactly one bit: if
// the variants were built on differently sized corpora it could not tell. The
// only other cross-variant `params` guard in the harness is `support`'s `Q`
// assertion, which is deliberately narrow (see its comment).
// ---------------------------------------------------------------------------

/// The quotient-row count both cases run at: **real**, `RLIN_ROWS = 5`, the
/// number of quotient rows the ring-switch link produces (one per `R^lin`
/// output row). `endpiece/rho_digits_short_check` registers it as its size;
/// `endpiece/lift_short_check` carries it as its second dimension beside the
/// registered `RLIN_COLS`.
const RHO_ROWS: usize = hachi::params::RLIN_ROWS;

/// One body per case, instantiated once per variant crate. Writing the variants
/// separately is how a benchmark quietly starts comparing two different
/// computations; a macro makes that impossible.
macro_rules! define_cases {
    ($modname:ident, $hachi:path) => {
        mod $modname {
            // `support::run`'s digest argument is `Fn(&R) -> u64`, so a digest of
            // a `Copy` scalar has to take it by reference. That is the bound's
            // shape, not a choice this file makes.
            #![allow(clippy::trivially_copy_pass_by_ref)]

            use std::hint::black_box;

            use cpoly::Fp;

            use $hachi as hc;

            use crate::support::{self, Mode};

            type Rq = hc::ring::Rq;
            type PolyVec = hc::linalg::PolyVec;
            type QuotientRow = hc::ringswitch::QuotientRow;
            type LiftedWitness = hc::ringswitch::LiftedWitness;

            /// The arithmetic that makes `rho_digits_short_check`'s verdict a
            /// tautology, asserted at compile time in **every** variant's own
            /// `params` -- so a candidate that moved either constant would fail
            /// to build rather than quietly give the row a real oracle back.
            ///
            /// A balanced base-`b` digit is centered-bounded by `⌊b/2⌋ =
            /// HALF_BASE` for every input (ArkLib
            /// `rhoDigits_valMinAbs_natAbs_le`, `RhoDigits.lean:153`), and the
            /// check compares against `CHAIN_GAMMA`. While `HALF_BASE <=
            /// CHAIN_GAMMA` the answer is `true` for every `Vec<QuotientRow>`
            /// this crate can construct, the digest oracle on that row is void,
            /// and the module header's § "The void oracle" applies. If this ever
            /// stops holding, the check gains a false branch, the oracle becomes
            /// real, and that section can go.
            const VOID_ORACLE: () = assert!(hc::params::HALF_BASE <= hc::params::CHAIN_GAMMA);
            // The const above is evaluated whether or not anything reads it, so
            // this line is not what makes the assertion fire (checked: flipping
            // the comparison breaks the build with the line removed). It is here
            // to give `VOID_ORACLE` a use, because a named constant that exists
            // only for its const-eval side effect is `dead_code` otherwise --
            // and it is named rather than anonymous so the case doc and the
            // module header have something to point at.
            const _: () = VOID_ORACLE;

            // -- corpus -----------------------------------------------------

            fn quotient_row(seed: u64) -> QuotientRow {
                QuotientRow::new(&support::corpus(seed, hc::params::RING_DEGREE))
            }

            fn quotient_rows(seed: u64, rows: usize) -> Vec<QuotientRow> {
                let mut out = Vec::with_capacity(rows);
                let mut i = 0usize;
                while i < rows {
                    out.push(quotient_row(seed.wrapping_add(i as u64)));
                    i += 1;
                }
                out
            }

            /// The all-zero quotient row: `from_coeffs` pads to `RING_DEGREE`,
            /// so an empty coefficient list is `ρ = 0`. Used only by
            /// [`check()`], to isolate `lift_short_check`'s `z` conjunct.
            fn zero_row() -> QuotientRow {
                QuotientRow::new(&Vec::new())
            }

            /// A one-entry `z` whose only nonzero coefficient is `c`.
            fn z_of(c: u64) -> PolyVec {
                PolyVec::new(vec![Rq::from_coeffs(&vec![Fp::new(c)])])
            }

            // -- digests (outside every timed region) -----------------------

            fn d_bool(b: &bool) -> u64 {
                u64::from(*b)
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

            // -- the properties, asserted before anything is timed ----------

            /// What the digest oracle cannot check, checked here instead.
            ///
            /// `support::case!` compares one fixed input's digest across the
            /// variants, and for a `bool` row that is one bit. Both cases in
            /// this binary answer `true` on their corpora, so the oracle's whole
            /// resolution is "did it still say true" -- which `|_| true` also
            /// says. This runs for every variant and asserts a *property*
            /// instead, in the shape `ring.rs`, `gadget.rs` and `quadeval.rs`
            /// use.
            ///
            /// One of the two functions can be pinned properly and one cannot;
            /// see the module header § "The void oracle".
            pub fn check() {
                let gamma = hc::params::CHAIN_GAMMA;

                // `liftShortCheck` REJECTS through its `z` conjunct, so both
                // directions are pinnable and both are pinned -- transplanted
                // from `tests/ringswitch_semantics.rs`
                // (`lift_short_check_accepts_and_rejects_on_the_z_norm`), which
                // is the `quadeval.rs` precedent: a bench `check()` asserts the
                // property, the test suite keeps the same claim on the
                // non-benchmark path. The quotient rows are zero in both, so
                // what moves between them is only `z`.
                let accepts = LiftedWitness::new(z_of(gamma), vec![zero_row()]);
                assert!(
                    hc::endpiece::lift_short_check(&accepts),
                    "lift_short_check must accept a z sitting exactly on CHAIN_GAMMA; \
                     the bound is inclusive and an honest witness sits on it"
                );
                let rejects = LiftedWitness::new(z_of(gamma + 1), vec![zero_row()]);
                assert!(
                    !hc::endpiece::lift_short_check(&rejects),
                    "lift_short_check must reject a z one over CHAIN_GAMMA. This is the \
                     ONLY direction either check in this binary can be caught failing, \
                     so a `true` here means the row below measures nothing that has \
                     been verified"
                );

                // `rhoDigitsShortCheck`, by contrast, has NO false direction at
                // these parameters (see `VOID_ORACLE` above for the const
                // assertion that pins the arithmetic). The assertion below is
                // therefore NOT evidence that the digit loop is right --
                // `|_| true` satisfies it too, and so does a candidate that
                // deletes the loop. It is kept as a corpus tripwire: it fails
                // if a future draw stops being a valid `Vec<QuotientRow>`.
                assert!(
                    hc::endpiece::rho_digits_short_check(&quotient_rows(
                        0x8047_0000_0000_00A0,
                        crate::RHO_ROWS
                    )),
                    "the quotient-digit check must accept -- and it cannot do otherwise at \
                     (bDig, bound) = (GADGET_BASE, CHAIN_GAMMA) = (16, 15), so read this as \
                     a parameter-drift tripwire and not as a verification of the loop"
                );
            }

            // -- the cases --------------------------------------------------

            /// The full five-row quotient-digit check at the real constants:
            /// `RLIN_ROWS · GADGET_DIGITS = 40` digit extractions of
            /// `RING_DEGREE` coefficients each, and a centered comparison per
            /// coefficient returned.
            ///
            /// **The digest oracle is void on this row.** Its verdict is
            /// provably `true` for every input at `(bDig, bound) = (16, 15)`,
            /// so `case!`'s cross-variant digest equality cannot tell the real
            /// function from `|_| true`, and a candidate that deletes the digit
            /// loop entirely would read as a very large win. See the module
            /// header § "The void oracle" for why the row is kept anyway (the
            /// fused digit-extract-and-compare it exists to price is real) and
            /// for the sign-off a candidate here needs. The computation is
            /// retained in the baseline for the same reason it is retained in
            /// `src/endpiece.rs`: a parameter change must not be able to delete
            /// a verifier check silently.
            pub fn rho_digits_short_check(m: Mode<'_, '_>, rows: usize) -> u64 {
                let rho = quotient_rows(0x8047_0000_0000_0080, rows);
                support::run(
                    m,
                    || hc::endpiece::rho_digits_short_check(black_box(&rho)),
                    d_bool,
                )
            }

            /// The real `RLIN_COLS = 57 344`-entry `z` scan, plus the
            /// five-row digit check it conjoins. The ~448 MiB input is built
            /// once per variant, outside the timed region; only the shortness
            /// decision is timed. ~31 ms in the shakeout, which is 448 MiB at
            /// ~14 GB/s: this row is memory bandwidth, and the digit check it
            /// conjoins (~119 µs, benched separately above) is 0.4% of it.
            ///
            /// # Why `z` is zeros, against `support`'s no-zeros rule
            ///
            /// Because `lift_short_check` is `vec_l_infty_norm(z) <= γ &&
            /// rho_digits_short_check(ρ)`, and `&&` short-circuits. An ordinary
            /// `[1, q)` corpus has `‖z‖∞ ≈ q/2`, so the first conjunct would be
            /// `false` and the second would never run: the row would silently
            /// measure half of the function it names, and its digest would be
            /// `false` -- indistinguishable from `|_| false`. Zeros are the
            /// cheapest `z` inside the bound, which is what an honest witness
            /// looks like anyway. The assertion below is the guard: a future
            /// edit to this corpus that pushes `z` over `CHAIN_GAMMA` fails the
            /// run instead of quietly shortening the row.
            ///
            /// What the zeros cost, stated so nobody over-reads the number:
            /// `commit::centered_abs` is a compare-and-select, and on an
            /// all-zero input it takes the same branch every time. The scan
            /// still walks all `5.87e7` coefficients (neither `l_infty_norm`
            /// nor `vec_l_infty_norm` exits early -- checked in
            /// `src/commit.rs`), so nothing is skipped; but a candidate whose
            /// win comes from changing the *branch structure* of that compare
            /// would read optimistically here, the way `quadeval/in_sb` does
            /// (NOTES.md § "The §4 audit of target 2's rows").
            pub fn lift_short_check(m: Mode<'_, '_>, z_len: usize) -> u64 {
                let w = LiftedWitness::new(
                    PolyVec::zeros(z_len),
                    quotient_rows(0x8047_0000_0000_0090, crate::RHO_ROWS),
                );
                assert!(
                    hc::commit::vec_l_infty_norm(w.z()) <= hc::params::CHAIN_GAMMA,
                    "this row's `z` is over CHAIN_GAMMA, so `lift_short_check` returns on \
                     its first conjunct and the quotient-digit half is never timed. See \
                     this case's doc: the zeros are load-bearing, not a placeholder"
                );
                support::run(m, || hc::endpiece::lift_short_check(black_box(&w)), d_bool)
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

fn endpiece_benches(c: &mut Criterion) {
    now::check();
    genesis::check();
    #[cfg(feature = "candidate")]
    candidate::check();

    // The run's sanity check: identical source in every variant, so anything it
    // reads is the harness disagreeing with itself. Runs first, while the machine
    // is in the same state the first real cases will see.
    bench_case!(c, "_control/endpiece", control, [support::CONTROL_N]);

    // Every size here is the real one; neither case is REDUCED. `RHO_ROWS =
    // RLIN_ROWS = 5` is the quotient-row count the ring-switch link produces
    // (one per `R^lin` output row) -- the registered size of the first row and
    // the unregistered second dimension of the second -- and `RLIN_COLS =
    // 57 344` is the `R^lin` witness width. Both are widths the scheme
    // instantiates rather than sizes chosen here. The 448 MiB `z` is built
    // outside the timed region.
    //
    // NOTE the void oracle on the first row: its verdict is a tautology at these
    // parameters, `case!`'s digest equality proves nothing about it, and a
    // candidate touching it needs explicit sign-off. Module header § "The void
    // oracle".
    // @covers endpiece::rho_digits_short_check
    bench_case!(c, "endpiece/rho_digits_short_check", rho_digits_short_check, [RHO_ROWS]);
    // @covers endpiece::lift_short_check
    bench_case!(c, "endpiece/lift_short_check", lift_short_check,
                [hachi::params::RLIN_COLS]);
}

criterion_group! {
    // A per-binary override of `support::criterion_config`, as `benches/commit.rs`
    // and `benches/ringswitch.rs` also carry, and it is arithmetic rather than
    // taste. Criterion samples linearly by default, so 100 samples cost
    // `100·101/2 = 5050` executions of the routine; at the ~31 ms `z` scan and
    // the ~37 ms control that is over two minutes per variant, so
    // `SamplingMode::Auto` refuses it and flips both rows to *flat* sampling --
    // `sample_size` samples of `ceil(window / sample_size / met)` iterations
    // each. The override is about what that ceiling comes out at.
    //
    // At the 5s default window a flat sample of a 31 ms row is
    // `ceil(50 ms / 31 ms) = 2` iterations. At 50 samples in 10s it is
    // `ceil(200 ms / 31 ms) = 7` (measured: 350 iterations over 50 samples).
    // That matters because `harness.py`'s `_robust` takes the **three fastest**
    // qualifying samples, and under flat sampling every sample qualifies: three
    // fastest out of samples that are two executions each is close to picking
    // the three luckiest executions in the run, while a seven-iteration sample
    // is an average that contention has to beat on all seven. The 119 µs digit
    // check is nowhere near flat sampling (82k iterations fit the window); it
    // simply takes 50 samples instead of 100.
    //
    // The cost is half the samples criterion's intervals rest on, and about 5s
    // more per variant. What this file exists to produce is a cross-variant
    // delta measured back to back, which survives both.
    //
    // Nothing else changes: warm-up and the noise threshold stay as
    // `support::criterion_config` sets them.
    name = benches;
    config = support::criterion_config()
        .sample_size(50)
        .measurement_time(Duration::from_secs(10));
    targets = endpiece_benches
}
criterion_main!(benches);
