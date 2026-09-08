//! Wall-clock time for the nonrecursive opening's terminal checks: the two
//! shortness checks at the real `params.rs` widths, and the end piece itself --
//! the one REDUCED row in this binary, and the one row in the repository where
//! two different scale walls fire inside a single function.
//!
//! Three cases, and they are the whole module:
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
//! * `endpiece/end_piece_check` -- **REDUCED**: the whole `endPieceCheck`
//!   conjunction on an *accepting* input, so all three conjuncts execute --
//!   `lift_commit` and its `PolyVec::equals`, `lift_short_check`, and
//!   `w_table_mle_eval` compared against the claimed value. Registered at the
//!   cube width `m₀ = END_PIECE_M_ZERO = 14`; the two unregistered dimensions
//!   (`μ = END_PIECE_Z_COLS = 8`, `n = END_PIECE_RHO_ROWS = 1`) and the
//!   arithmetic that makes 14 the least legal `m₀` sit at the file-scope
//!   constants, and the two removal notes -- one per wall, kept separate on
//!   purpose -- sit at the case.
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
//! | `endpiece/end_piece_check` | **not yet measured** | est. 16 `ring::mul` (~24 ms at the shakeout's 1.511 ms each) + ~8.4 M balanced-digit extractions + a `14 · 2^14` `Ext4` dot -- tens of ms, an estimate |
//!
//! The digit check is three orders of magnitude below the other two measured
//! rows, and the end piece is expected to land in the same tens-of-milliseconds
//! band as the `z` scan; that spread is why the sampling override at
//! `criterion_group!` has to say what it does to *each* of them rather than to
//! "this binary".
//!
//! # Why this is its own binary
//!
//! `harness.py` attributes a row to a bench binary by the **module prefix of
//! its group id** (`case_binary`), and divides that binary's own `_control`
//! lean out of every candidate verdict before printing one. So a binary is
//! defined by its control, and `endpiece/*` rows can only be measured in a
//! binary that carries `_control/endpiece`.
//!
//! The two shortness checks first landed inside `benches/ringswitch.rs`, under
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
//! | `end_piece_check` | **not yet checked**; returns `bool` through borrowed inputs, expect merged |
//!
//! Every checked row in this binary merges, controls included. All three cases
//! return a `bool` through `&`-borrowed inputs, so nothing variant-distinct
//! survives inlining; the third row has simply not been through the check yet.
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
//! `endpiece::end_piece_check` is not in that position either, but its digest
//! is still one bit on an accepting input, and `&&` short-circuits -- so a
//! corpus edit that flipped any conjunct would silently shorten the row, and
//! `|_| true` would digest identically to the real verifier. Two guards: the
//! case asserts the accepting verdict before timing, and `check()` pins all
//! three rejecting directions at a tiny shape (`μ = 1`, `n = 0`, `m₀ = 10`) --
//! one coefficient of `t` perturbed, `‖z‖∞ = CHAIN_GAMMA + 1`, and
//! `value + 1` each reject, with the other two conjuncts held honest so the
//! failing one is the one named.
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
// `lift_short_check` is two-dimensional and `end_piece_check` is
// three-dimensional (`μ`, `n`, `m₀`, plus a key width derived from the first
// two), and the registration below can only carry one number, so the others
// live here rather than inside the case body -- the arrangement
// `benches/ringswitch.rs` § "Sizes" argues for, and the one whose absence
// inverted `ringswitch/lift_message`.
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

/// `end_piece_check`'s `z` width `μ`: **REDUCED** from `params::RLIN_COLS =
/// 57 344`. Eight `Rq`, so the message half of the lift key, of the lifted
/// message and of the `w̃` table is wide enough that neither `lift_message`'s
/// copy loop nor `w_table`'s coefficient-read branch is a single iteration --
/// and small enough that the cube it forces ([`END_PIECE_M_ZERO`]) is 2^14
/// rather than 2^26.
const END_PIECE_Z_COLS: usize = 8;

/// `end_piece_check`'s quotient-row count `n`: **REDUCED** from
/// `params::RLIN_ROWS = 5`. One row, i.e. `GADGET_DIGITS = 8` digit rows in the
/// table, so the digit block -- the part all three conjuncts rebuild from
/// scratch, each for itself -- exists and is exercised at every digit index.
/// `n ≥ 1` is load-bearing: at `n = 0` conjunct A's `rho_digit_as_rq` loop,
/// conjunct B's digit check and conjunct C's digit branch are all empty, and
/// the row would price a function this crate does not call at that shape.
const END_PIECE_RHO_ROWS: usize = 1;

/// The lift key's width at the shape above: `μ + n · GADGET_DIGITS = 8 + 8 =
/// 16`, **derived** exactly as `params::LIFT_COLS = 57 384` is
/// `RLIN_COLS + RLIN_ROWS · GADGET_DIGITS`. Also the row count of the `w̃`
/// table and the number of `ring::mul`s conjunct A performs (`D_ROWS = 1`
/// row of that width).
const END_PIECE_LIFT_COLS: usize =
    END_PIECE_Z_COLS + END_PIECE_RHO_ROWS * hachi::params::GADGET_DIGITS;

/// `end_piece_check`'s cube width `m₀`: **REDUCED** from `params::M_ZERO =
/// 26`, and the least legal value at the shape above -- which is why it is 14
/// and not something smaller, the same floor argument `benches/zerocheck.rs`
/// makes for `M_ZERO_REDUCED`. The cube has to cover the table,
/// `(μ + n·δ) · d ≤ 2^m₀` (the coverage hypothesis `hμn` behind
/// `params::M_ZERO`), and `d = RING_DEGREE = 1024` is pinned:
/// `(8 + 1·8) · 1024 = 16 384 = 2^14`, while `2^13 = 8192` is too small. Both
/// inequalities are asserted below, so moving either dimension without moving
/// this one fails the build.
///
/// A consequence worth stating: the cube is *exactly* full here, so `w_table`'s
/// `else 0` padding branch is never taken on this row. At the real constants
/// `57 384 · 1024 = 58 761 216` of `2^26 = 67 108 864` points are committed
/// rows and 12.4% are padding; that branch is one comparison, and
/// `benches/zerocheck.rs`'s `check()` pins its value.
const END_PIECE_M_ZERO: usize = 14;

const _: () = assert!(END_PIECE_LIFT_COLS * hachi::params::RING_DEGREE <= 1 << END_PIECE_M_ZERO);
const _: () =
    assert!(END_PIECE_LIFT_COLS * hachi::params::RING_DEGREE > 1 << (END_PIECE_M_ZERO - 1));

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

            use cpoly::{Ext4, Fp};

            use $hachi as hc;

            use crate::support::{self, Mode};

            type Rq = hc::ring::Rq;
            type PolyVec = hc::linalg::PolyVec;
            type PolyMatrix = hc::linalg::PolyMatrix;
            type QuotientRow = hc::ringswitch::QuotientRow;
            type LiftedWitness = hc::ringswitch::LiftedWitness;
            type WEvalStatement = hc::endpiece::WEvalStatement;

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

            /// An `n`-entry `z` that is **nonzero everywhere and inside the
            /// bound**: every coefficient is drawn from `[1, CHAIN_GAMMA]` or is
            /// the negative `q − c` of such a value, with the sign taken from a
            /// bit the magnitude does not use. So `‖z‖∞ ≤ CHAIN_GAMMA` by
            /// construction, both branches of `centered_abs` (`v ≤ q/2` and
            /// `v > q/2`) are taken, and no ring element handed to conjunct A's
            /// `ring::mul` or embedded into conjunct C's table is zero.
            ///
            /// Why not `PolyVec::zeros`, which `lift_short_check` uses and
            /// argues for: that row prices a *scan*, and zeros only cost it the
            /// branch structure of one compare. Here `z` is also half the lift
            /// key's multiplicands and half the `w̃` table. Schoolbook
            /// `ring::mul` does not short-circuit on a zero operand today, but a
            /// candidate that skipped zero coefficients would take an unearned
            /// win on eight of this row's sixteen products, and the
            /// `Ext4::from_base(0)` entries would hand the same to any
            /// zero-aware `eval`. The all-zero `z` is a degenerate input for
            /// this row in exactly the way `support`'s no-zeros rule exists to
            /// forbid, and the shortness bound is why the ordinary `[1, q)`
            /// corpus cannot be used instead.
            fn short_z(seed: u64, n: usize) -> PolyVec {
                let gamma = hc::params::CHAIN_GAMMA;
                let q = hc::params::Q;
                let degree = hc::params::RING_DEGREE;
                let mut rng = support::SplitMix64::new(seed);
                let mut out = Vec::with_capacity(n);
                let mut i = 0usize;
                while i < n {
                    let mut coeffs = Vec::with_capacity(degree);
                    let mut k = 0usize;
                    while k < degree {
                        let r = rng.next();
                        let c = 1 + r % gamma;
                        coeffs.push(Fp::new(if (r >> 63) == 0 { c } else { q - c }));
                        k += 1;
                    }
                    out.push(Rq::from_coeffs(&coeffs));
                    i += 1;
                }
                PolyVec::new(out)
            }

            /// `n` ring elements from the ordinary corpus, one block per entry.
            fn vec_of(seed: u64, n: usize) -> PolyVec {
                let width = hc::params::RING_DEGREE;
                let coeffs = support::corpus(seed, n * width);
                let mut out = Vec::with_capacity(n);
                let mut i = 0usize;
                while i < n {
                    out.push(Rq::from_coeffs(
                        &coeffs[i * width..(i + 1) * width].to_vec(),
                    ));
                    i += 1;
                }
                PolyVec::new(out)
            }

            /// A `rows × cols` lift key from the ordinary corpus, a distinct
            /// stream per row.
            fn matrix_of(seed: u64, rows: usize, cols: usize) -> PolyMatrix {
                let mut out = Vec::with_capacity(rows);
                let mut i = 0usize;
                while i < rows {
                    out.push(vec_of(seed.wrapping_add(i as u64), cols));
                    i += 1;
                }
                PolyMatrix::new(out)
            }

            /// An `m₀`-coordinate evaluation point, the sumcheck's challenge,
            /// as `benches/zerocheck.rs` builds it.
            fn point(seed: u64, m0: usize) -> Vec<Ext4> {
                let c = support::corpus(seed, 4 * m0);
                let mut out = Vec::with_capacity(m0);
                let mut j = 0usize;
                while j < m0 {
                    out.push(Ext4::new(
                        c[4 * j],
                        c[4 * j + 1],
                        c[4 * j + 2],
                        c[4 * j + 3],
                    ));
                    j += 1;
                }
                out
            }

            /// The statement an honest prover would be checked against: `t`
            /// recomputed as `lift_commit`, `value` recomputed as
            /// `w_table_mle_eval` at `m₀ = point.len()`. Both recomputations
            /// happen here, in setup, and never inside a timed region.
            fn honest_statement(
                d_key: &PolyMatrix,
                w: &LiftedWitness,
                point: Vec<Ext4>,
            ) -> WEvalStatement {
                let t = hc::ringswitch::lift_commit(d_key, w);
                let m0 = point.len();
                let value = hc::zerocheck::w_table_mle_eval(w, m0, &point);
                WEvalStatement::new(t, point, value)
            }

            /// `t` with coefficient 0 of entry 0 moved by one: the smallest
            /// change conjunct A must notice.
            fn bump_first_coeff(t: &PolyVec) -> PolyVec {
                let degree = hc::params::RING_DEGREE;
                let mut out = Vec::with_capacity(t.len());
                let mut i = 0usize;
                while i < t.len() {
                    let mut coeffs = Vec::with_capacity(degree);
                    let mut k = 0usize;
                    while k < degree {
                        coeffs.push(t.get(i).coeff(k));
                        k += 1;
                    }
                    if i == 0 {
                        coeffs[0] = coeffs[0] + Fp::ONE;
                    }
                    out.push(Rq::from_coeffs(&coeffs));
                    i += 1;
                }
                PolyVec::new(out)
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
                check_end_piece(gamma);

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

            /// `endPieceCheck_eq_true_iff` (`EndPiece/Reduction.lean:225`) in
            /// the four directions a `bool` row cannot show through its digest:
            /// the honest statement accepts, and each of the three conjuncts
            /// rejects on its own. "On its own" is the point -- in every
            /// rejecting case the other two conjuncts are held honest (the
            /// over-long `z` gets a statement recomputed *for it*), so the
            /// conjunct named is the one that failed, and `&&`'s short-circuit
            /// cannot hide which.
            ///
            /// At a tiny shape: `μ = 1`, `n = 0`, `m₀ = 10` (one table row of
            /// `d = 1024` entries fills `2^10` exactly), so this costs one
            /// `ring::mul` and a `2^10` evaluation per statement -- nothing the
            /// run would notice. The bench row itself is the guard at the
            /// benched shape: it asserts acceptance before timing.
            fn check_end_piece(gamma: u64) {
                let m0 = 10usize;
                let d_key = matrix_of(0x8047_0000_0000_00F0, hc::params::D_ROWS, 1);
                let w = LiftedWitness::new(short_z(0x8047_0000_0000_00F1, 1), Vec::new());
                let a = point(0x8047_0000_0000_00F2, m0);
                let honest = honest_statement(&d_key, &w, a.clone());
                assert!(
                    hc::endpiece::end_piece_check(&d_key, &honest, &w),
                    "end_piece_check must accept the statement an honest prover is checked \
                     against; if it does not, the row below never leaves conjunct A"
                );

                // A: one coefficient of `t` off by one.
                let wrong_t = WEvalStatement::new(
                    bump_first_coeff(honest.t()),
                    honest.point().clone(),
                    honest.value(),
                );
                assert!(
                    !hc::endpiece::end_piece_check(&d_key, &wrong_t, &w),
                    "end_piece_check must reject a `t` that differs from `lift_commit` in \
                     one coefficient (conjunct A)"
                );

                // B: `‖z‖∞ = CHAIN_GAMMA + 1`, with `t` and `value` honest for
                // THIS witness so A and C hold and only the bound fails.
                let long = LiftedWitness::new(z_of(gamma + 1), Vec::new());
                let long_stmt = honest_statement(&d_key, &long, a);
                assert!(
                    !hc::endpiece::end_piece_check(&d_key, &long_stmt, &long),
                    "end_piece_check must reject a `z` one over CHAIN_GAMMA even when its \
                     commitment and evaluation are recomputed honestly (conjunct B)"
                );

                // C: the claimed value off by one.
                let wrong_value = WEvalStatement::new(
                    honest.t().copy(),
                    honest.point().clone(),
                    honest.value() + Ext4::ONE,
                );
                assert!(
                    !hc::endpiece::end_piece_check(&d_key, &wrong_value, &w),
                    "end_piece_check must reject a claimed evaluation off by one (conjunct C)"
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

            /// The whole end piece on an accepting input -- all three conjuncts
            /// run, in the specification's order, on a witness of
            /// `μ = END_PIECE_Z_COLS = 8` message polynomials and
            /// `n = END_PIECE_RHO_ROWS = 1` quotient row, against a
            /// `D_ROWS × 16` lift key, at the registered cube width
            /// `m₀ = END_PIECE_M_ZERO = 14`. **REDUCED**, and the one row in
            /// the repository where two different scale walls fire inside a
            /// single function. The two notes are kept separate because the
            /// case is bounded below by the *larger* of the two, and the two
            /// are removed by different champions -- a single blanket note
            /// would conflate them.
            ///
            /// **W1 -- conjunct A is `lift_commit` at width `LIFT_COLS =
            /// 57 384`**: 57 384 schoolbook negacyclic products at `d = 1024`
            /// (`RING_DEGREE² = 2^20` coefficient mult-adds each, ≈ 6.0 × 10^10
            /// in all), plus ≈ 448 MiB of key and another ≈ 448 MiB of lifted
            /// message -- minutes per criterion iteration. **The forcing wall is
            /// `ring::mul`'s width** -- an accepted sub-quadratic `ring::mul`
            /// champion (NTT) removes this note. It is not `m₀`'s cube size,
            /// and nothing about `m₀` moves it.
            ///
            /// **W2 -- conjunct C is `w_table_mle_eval` at `m₀ = M_ZERO =
            /// 26`**: the hypercube has `2^26 = 67 108 864` points, so a
            /// materialized `Ext4` table is 2.0 GiB, `w_table_mle_eval` holds
            /// two of them (the table and the Lagrange basis), and every entry
            /// in the digit block rebuilds a `d`-wide digit polynomial to read
            /// one coefficient. **The forcing wall is `m₀`'s cube size, which
            /// no multiplication speedup touches**; the split / `eval_mle`
            /// rewrites remove the *allocation*, but the Θ(2^m₀) point count
            /// remains. Not a `ring::mul` wall.
            ///
            /// # The reduced shape, and why it keeps both walls honest
            ///
            /// `d = RING_DEGREE = 1024` stays real, so every one of the sixteen
            /// ring products is a full-width schoolbook product and the
            /// `idx / d`, `idx % d` splits inside `w_table` run at the real
            /// modulus. What is cut is `μ` (57 344 → 8) and `n` (5 → 1), and
            /// `m₀` then follows: `(μ + n·δ) · d = (8 + 8) · 1024 = 16 384 =
            /// 2^14`, so 14 is the least `m₀` covering the table (see
            /// [`crate::END_PIECE_M_ZERO`] for the two const assertions that
            /// pin this). Per iteration, an estimate rather than a reading:
            ///
            /// * A: `lift_message` -- 8 copies and 8 digit polynomials (8192
            ///   balanced-digit extractions) -- then `D *ᵥ ·` at `1 × 16`: 16
            ///   `ring::mul` ≈ 16 × 1.5 ms ≈ 24 ms at the shakeout's `ring/mul`,
            ///   then one `PolyVec::equals` over `D_ROWS = 1` entry.
            /// * B: `8 · 1024` `centered_abs` compares on `z` and another 8192
            ///   digit extractions -- tens of µs, cf. `rho_digits_short_check`.
            /// * C: `c_w_table_mle` at `2^14` entries, of which the 8192 on the
            ///   digit block each rebuild a 1024-digit `Rq` -- ≈ 8.4 M
            ///   balanced-digit extractions, the same 8192-entry digit block
            ///   `zerocheck/w_table_mle_eval` prices at this `m₀` -- then
            ///   `eval`'s `m₀ · 2^m₀ = 14 · 16 384 ≈ 2.3 × 10^5` `Ext4`
            ///   multiplies against the Lagrange basis.
            ///
            /// So the row is `ring::mul`-bound and digit-bound in roughly equal
            /// measure, tens of milliseconds in all, with the 2^14 `Ext4` dot a
            /// minority. That mixture is deliberate: at the real constants the
            /// two walls are both astronomically large, and a reduced row that
            /// let either term vanish would price a function shaped unlike the
            /// real one.
            ///
            /// # Why the input has to accept, and what guards it
            ///
            /// `end_piece_check` is `A && B && C`, and `&&` short-circuits. On
            /// a rejecting input the row silently prices a prefix of the
            /// function, and its digest is `false` -- indistinguishable from
            /// `|_| false`. So `t` and `value` are *recomputed from the
            /// witness* in setup ([`honest_statement`], outside the timed
            /// region), the `z` is drawn inside the bound ([`short_z`], which
            /// also says why it is not zeros), and the assertion below fails the
            /// run if a corpus edit flips any conjunct -- rather than letting the
            /// row shorten and read as a win. The digest is then one bit that is
            /// always `true`, so what the oracle cannot see is pinned in
            /// [`check()`] instead: each conjunct rejects on its own.
            pub fn end_piece_check(m: Mode<'_, '_>, m0: usize) -> u64 {
                let z_cols = crate::END_PIECE_Z_COLS;
                let rho_rows = crate::END_PIECE_RHO_ROWS;
                let width = z_cols + rho_rows * hc::params::GADGET_DIGITS;
                assert!(
                    width * hc::params::RING_DEGREE <= 1 << m0,
                    "the cube must cover the table: (mu + n*delta)*d <= 2^m0 is the coverage \
                     hypothesis behind params::M_ZERO, and a row that violates it is not a \
                     smaller end piece but an illegal one"
                );
                let w = LiftedWitness::new(
                    short_z(0x8047_0000_0000_00B0, z_cols),
                    quotient_rows(0x8047_0000_0000_00C0, rho_rows),
                );
                let d_key = matrix_of(0x8047_0000_0000_00D0, hc::params::D_ROWS, width);
                let stmt = honest_statement(&d_key, &w, point(0x8047_0000_0000_00E0, m0));
                assert!(
                    hc::commit::vec_l_infty_norm(w.z()) <= hc::params::CHAIN_GAMMA,
                    "this row's `z` is over CHAIN_GAMMA, so conjunct B fails and conjunct C \
                     is never timed; `short_z` is supposed to make this impossible"
                );
                assert!(
                    hc::endpiece::end_piece_check(&d_key, &stmt, &w),
                    "this row's input REJECTS, so `&&` short-circuits and the row prices a \
                     prefix of `end_piece_check` while digesting `false`. A corpus edit has \
                     flipped a conjunct; fix the corpus, do not silence this"
                );
                support::run(
                    m,
                    || {
                        hc::endpiece::end_piece_check(
                            black_box(&d_key),
                            black_box(&stmt),
                            black_box(&w),
                        )
                    },
                    d_bool,
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

// `harness.py`'s `BENCH_CASE` regex binds a `// @covers` marker to the
// `bench_case!(c, "<group>", <fn>,` that follows it, and it reads that call
// **one line at a time** -- so the group string and the case name must share
// the macro's first line, or `coverage --strict` reports every marker below as
// orphaned. rustfmt's `fn_call_width` heuristic would wrap each of these calls
// (their argument lists exceed 60 columns) into a form the regex cannot read.
// The registration is therefore kept in the harness's shape and rustfmt is
// told so; the case bodies above are formatted normally.
#[rustfmt::skip]
fn endpiece_benches(c: &mut Criterion) {
    now::check();
    genesis::check();
    #[cfg(feature = "candidate")]
    candidate::check();

    // The run's sanity check: identical source in every variant, so anything it
    // reads is the harness disagreeing with itself. Runs first, while the machine
    // is in the same state the first real cases will see.
    bench_case!(c, "_control/endpiece", control, [support::CONTROL_N]);

    // The two shortness checks run at the real sizes; neither is REDUCED.
    // `RHO_ROWS = RLIN_ROWS = 5` is the quotient-row count the ring-switch link
    // produces (one per `R^lin` output row) -- the registered size of the first
    // row and the unregistered second dimension of the second -- and
    // `RLIN_COLS = 57 344` is the `R^lin` witness width. Both are widths the
    // scheme instantiates rather than sizes chosen here. The 448 MiB `z` is
    // built outside the timed region.
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

    // The end piece is REDUCED on all three of its dimensions, and two
    // different walls force it -- `ring::mul`'s width on conjunct A, `m₀`'s
    // cube on conjunct C -- with two different removal conditions, stated
    // separately at the case. The registered size is `m₀ = END_PIECE_M_ZERO =
    // 14`, the least legal cube width at `μ = END_PIECE_Z_COLS = 8`, `n =
    // END_PIECE_RHO_ROWS = 1`; the other two are the unregistered dimensions
    // and live at those constants with the arithmetic.
    // @covers endpiece::end_piece_check
    bench_case!(c, "endpiece/end_piece_check", end_piece_check, [END_PIECE_M_ZERO]);
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
    // `end_piece_check` (unmeasured; estimated at tens of ms -- 16 `ring::mul`
    // ≈ 24 ms plus ~8.4 M digit extractions plus a `14 · 2^14` `Ext4` dot, see
    // the case) lands in the same band as the `z` scan and inherits the same
    // arithmetic: at, say, 60 ms a flat sample is `ceil(200 ms / 60 ms) = 4`
    // iterations under this override against `ceil(50 ms / 60 ms) = 1` at the
    // default, which is the difference between an average and a single draw.
    // If the measurement comes in far from that estimate, redo this paragraph
    // rather than the constants.
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
