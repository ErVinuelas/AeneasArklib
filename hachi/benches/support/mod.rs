//! Shared machinery for the four bench binaries: the seeded corpus, the digest
//! that keeps a measurement honest, the A/B fairness control, and the two-mode
//! runner that makes the timed code and the *verified* code the same code.
//!
//! # The two failures a green bench run will not show you
//!
//! A benchmark can measure less than it claims, because the optimizer deleted
//! work whose result nobody looked at. And it can measure the *wrong thing*,
//! because the "optimized" function no longer computes what the baseline
//! computed. Both make a number go down, which is exactly the direction that
//! makes an autonomous optimization loop believe it succeeded. So:
//!
//! * **Every case has exactly one body**, written once, and [`run`] either hands
//!   it to criterion or runs it once and digests its result. There is no separate
//!   verification copy that can drift away from the code that gets timed.
//! * **Every case ends in a digest** that depends on every output element, on its
//!   position, and on how many there are. [`case!`] computes that digest for
//!   `now`, for `genesis`, and -- under `--features candidate` -- for the slot,
//!   and asserts they are equal *before* timing anything. An "optimization" that
//!   changes an answer fails the run; it cannot be reported as a speedup.
//! * **Every input is opaque to the optimizer** ([`std::hint::black_box`]) and
//!   every output is consumed, so there is nothing to constant-fold and nothing
//!   dead to delete.
//!
//! What the oracle cannot do, stated so nobody over-reads it. It compares one
//! fixed input, so it catches a semantics change that shows up *there* and not
//! one that hides elsewhere -- and the resolution it has is the width of the
//! result. A row returning a `bool` (`ring/equals`, `linalg/equals`,
//! `commit/verify_weak`, `commit/verify`) carries one bit of it: on an accepting
//! input, `|_| true` digests identically to the real verifier. That is part of
//! why `ring.rs`, `gadget.rs` and `commit.rs` each carry a `check()` as well:
//! those assert a *property* -- the negacyclic relation, the gadget round trip,
//! that an honest opening verifies -- rather than an agreement, and they run for
//! every variant. `linalg.rs` has none, because its two `bool` rows compare a
//! vector with itself and there is no property there that `ring/equals` does not
//! already cover.
//!
//! # Three variants, one session
//!
//! Every case is measured in up to three variants -- `now` (`hachi`), `genesis`
//! (`hachi_genesis`, the frozen first translation) and, under
//! `--features candidate`, `candidate` (`hachi_candidate`, the optimization
//! loop's slot). They are measured *back to back in one criterion session*, on
//! the same machine, at the same temperature, with the same compiler, because
//! that is the only way a "vs genesis" reading is a comparison rather than a
//! recollection. Nothing is ever compared across runs.
//!
//! The variant name is a criterion `function_id` inside a group named
//! `<module>/<op>`, and it is exactly `now` / `candidate` / `genesis`:
//! `harness.py`'s `read_criterion` keys a case on the group and reads the variant
//! out of the function id, so those three names and that group shape are an
//! interface, not labels. `cmd_report` looks up `cases[case]["candidate"]` by that
//! exact spelling; a `cand` would silently drop the whole accept column.
//!
//! # What the corpus guarantees
//!
//! * **Identical inputs across variants.** Coefficients come from one
//!   `Vec<cpoly::Fp>` built by [`corpus`] and handed to all three crates. That
//!   works here and did not upstream: `hachi`, `hachi_genesis` and
//!   `hachi_candidate` all take the *same* `cpoly` at the *same* pinned `rev`
//!   (see the three `Cargo.toml`s), so `Fp` is literally one type and only the
//!   `Rq`/`PolyVec` wrappers around it are per-crate. A difference in a reading
//!   is therefore a difference in code.
//! * **Reproducibility.** Seeds are literals; no clock, no RNG crate.
//! * **No zeros.** Coefficients are drawn from `[1, Q)`. Zeros are the input on
//!   which a short-circuiting implementation looks fastest, and a corpus whose
//!   zero count depends on the seed makes two runs incomparable for a reason that
//!   has nothing to do with the code. Nothing in `hachi` short-circuits today;
//!   the rule is here so that an optimization which introduces one cannot also
//!   choose the input that flatters it.
//! * **One seed per role.** Two operands of the same operation take different
//!   seeds: `a * a` is a squaring, and squaring is not what `mul` is for.
//!
//! # The A/B fairness control
//!
//! Each bench binary carries one extra group, `_control/<binary>`, whose case
//! measures **`linalg::PolyVec::zeros(CONTROL_N)`** in every variant. It is a
//! sanity check on the *run*, not a per-case error bar, and it carries no
//! `// @covers` marker because it measures the harness rather than the crate.
//!
//! ## Why the harness benchmarks something it does not care about
//!
//! The "vs genesis" column compares two criterion benchmarks run one after the
//! other: `now` finishes completely before `genesis` starts. Anything that
//! changes about the machine across those seconds -- a core clocking up, a fan
//! spinning down, a neighbour arriving on a shared host -- lands entirely on the
//! second one and looks exactly like a code change. Code *layout* does the same
//! thing silently and permanently: the three variants are different symbols from
//! different crates, and a few bytes of alignment difference can be worth several
//! percent on a tight loop. AeneasCompPoly measured byte-identical code 28% apart
//! under `lto = "thin"` for that reason alone (`hachi/Cargo.toml`
//! § `[profile.bench]`).
//!
//! None of that can be reasoned away, so it is measured every run. `harness.py`
//! prints the worst control delta, refuses to report a run above its
//! `USABLE_BIAS_MAX`, folds the magnitude into the significance threshold, and
//! divides the *signed* candidate-side lean out of every accept-column verdict in
//! the same binary.
//!
//! ## Why the body comes from the variant crates and not from here
//!
//! There are two possible designs and they do not measure the same thing.
//!
//! * **Same symbol.** Put an integer kernel in this module and have all three
//!   variants call it. Then the timed code is one function at one address, so the
//!   control sees timing order and machine drift -- and *nothing* of layout.
//!   AeneasCompPoly's harness, which this one is a port of, is built this way.
//! * **Cross-crate.** Pick an operation whose source is byte-identical in
//!   `hachi`, `hachi_genesis` and `hachi_candidate`, and let each variant run its
//!   own separately compiled copy. Then the control is subject to exactly the
//!   layout bias the real cases are.
//!
//! This repository uses the **cross-crate** form, because `harness.py` attributes
//! the candidate slot's lean to "code layout and timing order" and then divides
//! that lean out of every candidate verdict. A control that cannot see the layout
//! half of what it is correcting for under-corrects systematically, in a fixed
//! direction, on every row -- and a correction that is wrong in a fixed direction
//! is worse than no correction, because it looks like one.
//!
//! The cost is real and is the reason this is written down: a cross-crate control
//! is only a control while the three copies agree, and every item in `hachi/src`
//! is a legitimate optimization target. `PolyVec::zeros` is the choice that
//! minimises that exposure -- it is a fixed-shape allocate-and-fill, it appears on
//! no hot path (`dot` and `gadget_mul` reach `Rq::zero` directly, never through
//! it), and it claims no `Mirrors` docstring, so it competes with no coverage
//! row. It is not immune: it fills with `Rq::zero`, which *is* benched, as
//! `ring/zero`. If a candidate rewrites `Rq::zero`, the control moves.
//!
//! That failure is loud rather than silent, and the ordering matters:
//! `harness.py` computes the bias veto from the **worst** pairwise control delta
//! *before* it prints any verdict, so a control that moved for a code reason
//! fails the whole run instead of quietly rescaling it. `ring/zero` is then the
//! row that says why. The same argument is what rules out using one of the real
//! hot operations as the control.
//!
//! ## Why it is 128 entries and not one element
//!
//! Because a control's number is the threshold every real row must clear, so it
//! has to be a row of the same kind. Two ways to get that wrong, and this
//! repository has already made the first one:
//!
//! * **Too quiet.** The controls this file replaces were `Rq::zero()` (`ring`),
//!   `Rq::one()` (`commit`) and `base_pow(0)` (`gadget`) -- single sub-microsecond
//!   calls, measured at 212 ns and 297 ns. At that scale a control is mostly
//!   timer and scheduler resolution, and it is not doing what the real rows do.
//! * **Not allocating.** Every operation `hachi` exposes takes `&self` or
//!   `&Vec<_>` and returns a freshly allocated value, so every real row pays an
//!   allocation and a drop inside the timed loop. A control over a borrowed slice
//!   would report a fraction of the spread those rows actually show.
//!
//! `PolyVec::zeros(128)` is both: 64 KiB across 128 independent `Vec` growth
//! sequences, ~28 us, which is where the polynomial rows the loop acts on live.
//!
//! **What resizing does not fix.** These are this repository's own prior
//! readings, from NOTES.md § "The first benchmark run, and what it says about the
//! harness", on an idle 4-core cloud container: the controls read 15%
//! (`ring`, 212 ns), 14% (`linalg`, 27.9 us) and 10% (`commit`, 297 ns) -- and
//! the 27.9 us one, which was already `PolyVec::zeros(128)`, was no better than
//! the 212 ns ones. So the resize makes the control *representative*; it is not a
//! fix for the floor, and that run's own diagnosis (no CPU pinning, no isolation
//! from neighbours, invisible steal time) still stands. `harness.py`'s
//! `MIN_EFFECT` note says the same thing from the other end: nothing computable
//! from inside a single run removes that residue. Any number quoted from
//! AeneasCompPoly is AeneasCompPoly's; this repository has not run its own
//! calibration sweep.

#![allow(dead_code)] // each bench file uses a different subset of this module.

use std::time::Duration;

use cpoly::Fp;
use criterion::Criterion;

/// The modulus the corpus reduces against: the Hachi prime `2^32 - 99`.
///
/// A local copy, checked below rather than trusted. The corpus reduces mod this
/// value, so a copy that disagreed with the field's would make every "field
/// element" here unreduced and every operation would be measured on an input it
/// does not promise to accept.
pub const Q: u64 = 4_294_967_197;

// The three variants are separate crates with separate `params::Q`. They agree
// today because two of them are copies, but "is a copy" is checked by
// `harness.py check-genesis`/`check-candidate` on *text*; this checks the value
// the corpus is actually generated against. A `params::Q` that drifted in one
// crate would put two different rings into one comparison, and the digest oracle
// would not catch it -- both variants see the same corpus either way.
const _: () = assert!(Q == Fp::MODULUS);
const _: () = assert!(Q == hachi::params::Q);
const _: () = assert!(Q == hachi_genesis::params::Q);
#[cfg(feature = "candidate")]
const _: () = assert!(Q == hachi_candidate::params::Q);

// ---------------------------------------------------------------------------
// Size
//
// Only the control's size lives here, and the asymmetry is deliberate. Every
// real case's size is a `params` constant read in the bench file that measures
// it -- `RING_DEGREE` in `ring.rs`, `MESSAGE_ROWS · GADGET_DIGITS` in
// `linalg.rs`, and so on -- because those are not knobs: they are the widths the
// scheme instantiates, and a reading at any other width would be a reading
// nothing depends on. The control is the one case whose size is a choice, so it
// is the one that has to be argued for.
// ---------------------------------------------------------------------------

/// The A/B fairness control's size: the width of the inner Ajtai matrix.
///
/// See the module header § "The A/B fairness control" for what the control is and
/// why it is `PolyVec::zeros`. This is the length, and the choice is a duration
/// and a footprint rather than a round number: 128 entries of `RING_DEGREE`
/// coefficients is 8192 `Fp` -- 64 KiB, 128 separate `Vec` growth sequences --
/// and NOTES.md § "The first benchmark run" measured exactly this case at
/// **27.9 us**. That is the low-microsecond band the real polynomial rows the
/// optimization loop acts on live in, and it is 130x the 212 ns the old
/// `ring`/`commit` controls ran at.
///
/// One size rather than several, because no small set of controls can cover this
/// suite: the real cases span 20 ns (`ring/equals`) to 8 ms (`commit/verify_weak`),
/// six orders of magnitude. Several controls would invite exactly the wrong
/// inference -- a per-case threshold interpolated across them and applied to rows
/// a thousand times longer than the control it came from, which reads as rigour
/// and is not. One control, one number, applied flat, is the honest shape of what
/// is known.
///
/// A literal rather than the product, so the number that appears in the criterion
/// case id (`_control/ring/128`) is readable here; the relation is checked below,
/// which is the same trade `params::RING_DEGREE` makes.
pub const CONTROL_N: usize = 128;

const _: () = assert!(CONTROL_N == hachi::params::MESSAGE_ROWS * hachi::params::GADGET_DIGITS);

// ---------------------------------------------------------------------------
// Deterministic corpus
// ---------------------------------------------------------------------------

/// `SplitMix64`, as in the scaffold's bench: four lines, no dependency.
pub struct SplitMix64(u64);

impl SplitMix64 {
    /// A generator with the given seed.
    pub fn new(seed: u64) -> SplitMix64 {
        SplitMix64(seed)
    }

    /// The next 64 bits.
    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// `n` field elements drawn from `[1, Q)`; see the module header for why zero is
/// excluded.
pub fn corpus(seed: u64, n: usize) -> Vec<Fp> {
    let mut rng = SplitMix64::new(seed);
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(Fp::new(1 + rng.next() % (Q - 1)));
    }
    v
}

// ---------------------------------------------------------------------------
// Digest
// ---------------------------------------------------------------------------

/// Fold one word into a running digest, sensitive to both value and position.
///
/// Runs **outside** every timed region -- it is applied to a finished result, not
/// per element inside the loop -- so it can afford to be a real mixing function
/// rather than an xor, which would call a reversed vector equal to its original.
/// Position sensitivity is the `rotate_left`: the fold does not commute, so
/// `mul` returning the right coefficients in the wrong slots is a different
/// digest.
pub fn mix(acc: u64, v: u64) -> u64 {
    let mut z = acc.rotate_left(17) ^ v.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Fold a length or a dimension in.
///
/// Every container digest starts with this, and it is not decoration: without it
/// a `flatten_blocks` that dropped a block, or a `gadget_decompose` that emitted
/// the wrong number of digits, could collide with a correct result. The cast is
/// confined here; `usize` cannot exceed `u64` on any target this crate builds
/// for.
pub fn mix_len(acc: u64, n: usize) -> u64 {
    mix(acc, n as u64)
}

/// Fold a `u128` in, high half first.
///
/// For the squared-`ℓ₂` norms, which are `u128` because a vector of squared
/// centered coefficients overflows `u64` (see `commit::l2_norm_sq`). Both halves
/// are folded: a digest that kept only the low 64 bits could not tell a correct
/// sum from one `2^64` larger, which is precisely the wraparound `u128` is there
/// to prevent.
pub fn mix_u128(acc: u64, v: u128) -> u64 {
    let hi = u64::try_from(v >> 64).expect("the high half of a u128 is 64 bits");
    let lo = u64::try_from(v & u128::from(u64::MAX)).expect("masked to 64 bits");
    mix(mix(acc, hi), lo)
}

// ---------------------------------------------------------------------------
// The two-mode runner
// ---------------------------------------------------------------------------

/// What a case should do with its body: time it, or run it once and digest it.
pub enum Mode<'a, 'b> {
    /// Hand the body to criterion.
    Bench(&'a mut criterion::Bencher<'b>),
    /// Run the body once and return a digest of its result.
    Digest,
}

/// Time (or digest) a body that returns its result.
///
/// `Bencher::iter` black-boxes whatever the body returns, so the result cannot be
/// optimized away; the caller's job is only to make the *inputs* opaque. The
/// returned value is dropped inside the timed loop, which is deliberate: that is
/// what a caller pays, and an "optimization" that halves the arithmetic while
/// doubling the allocations has not made anything faster.
pub fn run<R, F, D>(m: Mode<'_, '_>, mut body: F, digest: D) -> u64
where
    F: FnMut() -> R,
    D: Fn(&R) -> u64,
{
    match m {
        Mode::Bench(b) => {
            b.iter(&mut body);
            0
        }
        Mode::Digest => digest(&body()),
    }
}

/// Time (or digest) a body that writes into a caller-owned buffer.
///
/// The buffer is re-black-boxed on every iteration so the writes cannot be
/// hoisted out of the loop or elided. **No case in this crate uses it yet**, and
/// the shape that would is a per-element loop over a preallocated output --
/// `out[i] = xs[i] OP ys[i]` -- which is how a sub-nanosecond primitive is lifted
/// above the timer. Every operation `hachi` exposes already returns an owned
/// `Vec`-backed value, so [`run`] is the right runner for all of them; this is
/// here so that adding such a case does not mean re-deriving why the black_box
/// goes where it goes.
pub fn run_into<T, F, D>(m: Mode<'_, '_>, out: &mut [T], mut body: F, digest: D) -> u64
where
    F: FnMut(&mut [T]),
    D: Fn(&[T]) -> u64,
{
    match m {
        Mode::Bench(b) => {
            b.iter(|| body(std::hint::black_box(&mut *out)));
            std::hint::black_box(&*out);
            0
        }
        Mode::Digest => {
            body(out);
            digest(&*out)
        }
    }
}

/// Time (or digest) a body that consumes its input.
///
/// `iter_batched` builds the inputs and drops the outputs outside the timed
/// region (verified in criterion 0.7's `Bencher::iter_batched`), which is the
/// only correct way to measure an operation that needs a fresh owned value per
/// iteration -- timing the clone that produces it would measure the clone.
/// **No case in this crate uses it yet**: every `hachi` operation borrows its
/// operands (`&self`, `&Rq`, `&PolyVec`), so nothing here needs a fresh input.
/// It is kept because the first `self`-consuming operation to be added would
/// otherwise be measured wrong in a way that reads as a speedup.
pub fn run_batched<I, R, S, F, D>(m: Mode<'_, '_>, mut setup: S, mut body: F, digest: D) -> u64
where
    S: FnMut() -> I,
    F: FnMut(I) -> R,
    D: Fn(&R) -> u64,
{
    match m {
        Mode::Bench(b) => {
            b.iter_batched(&mut setup, &mut body, criterion::BatchSize::LargeInput);
            0
        }
        Mode::Digest => digest(&body(setup())),
    }
}

// ---------------------------------------------------------------------------
// Criterion configuration
// ---------------------------------------------------------------------------

/// The configuration `make run-bench` uses. There is exactly one; there is no
/// reduced-sampling mode, because a run that cannot be acted on is not worth the
/// minutes it still costs.
///
/// 100 samples is criterion's default and what its confidence intervals are worth
/// trusting at. The measurement window is 5s, up from criterion's 3s default.
///
/// Why 5s and not more: criterion samples *linearly*, so sample `k` runs the
/// routine `k · d` times, and a longer window buys a larger `d`. For rows near a
/// millisecond `d = 1` whatever the window, so the returns past 5s are thin and
/// the suite would double. What actually fixes the low-iteration samples is
/// discarding them, which `harness.py`'s `_robust` does.
///
/// `benches/commit.rs` overrides this, and says why at the override: its rows are
/// milliseconds, so 100 samples of linear sampling do not fit in any window worth
/// waiting for.
///
/// What more sampling does **not** fix, and what nothing inside criterion can: a
/// machine that settles into a slower state for longer than an entire
/// measurement. Criterion's statistics describe the samples it took; they cannot
/// see a bias constant across every one of them. Only the now-vs-genesis delta
/// survives that, because it lands on all variants equally -- which is why that
/// delta, and not the absolute time, is the number this harness exists to
/// produce.
pub fn criterion_config() -> Criterion {
    Criterion::default()
        .sample_size(100)
        .warm_up_time(Duration::from_millis(1000))
        .measurement_time(Duration::from_secs(5))
        .noise_threshold(0.03)
}

// ---------------------------------------------------------------------------
// The case driver
// ---------------------------------------------------------------------------

/// Measure one case in every variant, after proving they agree.
///
/// The equality assertion is the load-bearing line. `now` and `genesis` are
/// different code compiled from different crates; if they disagree on a fixed
/// input then, whatever the timings say, they are not timings of the same
/// computation and the comparison is meaningless. Failing here is much cheaper
/// than shipping a "speedup" that changed an answer.
///
/// Under `--features candidate` a third variant runs: the slot
/// (`benches/candidate`, see its `lib.rs` for the contract). It is digest-asserted
/// against `now` exactly as `genesis` is, and timed **between** `now` and
/// `genesis`: the verdict the loop acts on is candidate-vs-now, so those two run
/// closest together, while now-vs-genesis -- positions 1 and 3 only in candidate
/// runs -- keeps the `_control` cases as its witness. Every pairwise delta of a
/// control is identical code, and `harness.py` takes the worst of them all as the
/// run's threshold. Without the feature this expands to `now` then `genesis`,
/// which is what it was before the slot existed.
///
/// The three function ids are `now`, `candidate` and `genesis` verbatim:
/// `harness.py`'s `cmd_report` looks up `cases[case]["candidate"]`, so `cand`
/// would silently drop the accept column.
#[macro_export]
macro_rules! case {
    ($g:expr, $f:ident, $param:expr) => {{
        let p = $param;
        let d_now = now::$f($crate::support::Mode::Digest, p);
        let d_gen = genesis::$f($crate::support::Mode::Digest, p);
        assert_eq!(
            d_now, d_gen,
            "bench `{}` at {}: hachi and the frozen genesis snapshot compute \
             DIFFERENT results. Either the current code is wrong, or it changed \
             semantics; either way the timings below would compare two different \
             functions. Fix the code, do not silence this.",
            stringify!($f),
            p
        );
        #[cfg(feature = "candidate")]
        {
            let d_cand = candidate::$f($crate::support::Mode::Digest, p);
            assert_eq!(
                d_cand, d_now,
                "bench `{}` at {}: the candidate slot and hachi compute DIFFERENT \
                 results, so this is not an optimization, it is a semantics \
                 change. The loop must reject the candidate; do not silence this.",
                stringify!($f),
                p
            );
        }
        $g.bench_with_input(::criterion::BenchmarkId::new("now", p), &p, |b, &p| {
            now::$f($crate::support::Mode::Bench(b), p);
        });
        #[cfg(feature = "candidate")]
        $g.bench_with_input(::criterion::BenchmarkId::new("candidate", p), &p, |b, &p| {
            candidate::$f($crate::support::Mode::Bench(b), p);
        });
        $g.bench_with_input(::criterion::BenchmarkId::new("genesis", p), &p, |b, &p| {
            genesis::$f($crate::support::Mode::Bench(b), p);
        });
    }};
}

/// One criterion group per operation, one case per size.
///
/// The group name is the `<module>/<op>` pair `harness.py` keys a case on, and
/// the `// @covers <item path>` marker on the line above ties the row to the item
/// it measures -- rename deliberately, and never separate the two. A
/// `bench_case!` with no marker above it, and a marker not sitting on one, are
/// both `coverage --strict` failures; a `_control/<binary>` case is the one form
/// that must carry no marker at all, because it measures the harness rather than
/// the crate.
#[macro_export]
macro_rules! bench_case {
    ($c:expr, $name:literal, $f:ident, [$($p:expr),+ $(,)?]) => {{
        let mut g = $c.benchmark_group($name);
        $( $crate::case!(g, $f, $p); )+
        g.finish();
    }};
}
