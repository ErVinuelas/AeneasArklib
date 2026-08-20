---
name: rust-bench
description: Adding a criterion benchmark for a newly translated ArkLib operation in hachi/src — freezing its first translation into the genesis baseline, writing a case that measures the operation and nothing else, and proving that it does with adversarial review agents before any number is trusted
---

# Benchmarking a New Translation

Everything benchmark-related lives in `hachi/benches/`: the four case files,
`support/`, the frozen `genesis/` crate, the `candidate/` slot, `harness.py` and
`exclusions.toml`. Read this **before** adding a case, and read `support/mod.rs`
and `genesis/src/lib.rs` — their module docs are the design, this file is the
procedure.

Criterion wall-clock time is the *only* fitness function of this project. Every
accept/reject decision the optimization loop makes is downstream of a number
produced here. A benchmark that measures the wrong thing does not produce a
wrong decision occasionally — it produces a confidently wrong one, repeatedly,
in the direction that looks like success.

## The one rule: a benchmark is guilty until proven innocent

A bench that compiles, runs, and prints a plausible microsecond figure has
demonstrated nothing. All three of the ways it fails are silent:

* it measures **less** than it claims (the optimizer deleted work nobody looked
  at),
* it measures **more** than it claims (setup, cloning, or a second operation
  leaked into the timed region),
* it measures **something else entirely** (the wrong overload, a degenerate
  input that skips the loop).

Each of those makes a number go *down*, which is the direction an autonomous
loop reads as a win. So the bench does not exist until it has survived §4.

## Five modules, four bench targets

`MODULES` in `harness.py` is the fixed 5-tuple `params ring linalg gadget
commit`. `hachi/Cargo.toml` declares **four** `[[bench]]` targets — `ring`,
`linalg`, `gadget`, `commit`. `params.rs` is frozen into genesis and verified by
`check-genesis` like every other module, and has no bench file because all
fourteen of its items are `const`s rustc folds at compile time: a case over one
would time the `black_box` around it and nothing else. That is the
`exclusions.toml` bar, stated once by the absence of an entire target.

A **new module** is therefore five edits, not one, and four of the five fail
quietly if you skip them:

1. extend `MODULES` in `hachi/benches/harness.py` — it is a fixed tuple, and an
   unlisted module is invisible to `check-genesis`, `check-candidate` *and*
   `coverage`;
2. declare a `[[bench]]` in `hachi/Cargo.toml` — `autobenches = false`, so an
   undeclared `benches/foo.rs` is simply not built. Silence, not an error;
3. add the `pub mod` line to `hachi/benches/genesis/src/lib.rs`;
4. add it to `hachi/benches/candidate/src/lib.rs`, whose `src/` must then hold
   **exactly six files** (five modules plus `lib.rs`) — `check-candidate`
   counts;
5. add whatever corpus the module needs to `benches/support/mod.rs`.

Untraveled in this repository: all five modules were born together, before the
harness existed. Expect to amend this list the first time it happens.

## What the harness already does for you

Do not re-solve these; do not work around them.

| Guarantee | Mechanism |
|---|---|
| The timed body and the verified body are the same code | one body per case, `support::run*` either times it or digests it |
| `now` and `genesis` cannot drift apart | one case body, instantiated against `hachi` and `hachi_genesis` |
| An "optimization" that changes an answer fails loudly | `case!` digests every variant and `assert_eq!`s them **before** timing |
| The baseline is never a stale remembered number | `genesis/` is re-measured every run, in the same session |
| The frozen baseline cannot be quietly edited | `make bench-check` verifies every frozen item against its git blob |
| The three crates get symmetric codegen | `lto = "fat"`, `codegen-units = 1` (`hachi/Cargo.toml § profile.bench`) |
| Background load cannot inflate a verdict | the reported time is the mean of the three fastest *settled* samples, not criterion's slope |
| A/B bias is known, not assumed | `_control/*` runs byte-identical code as every variant, one per bench binary |
| A change under the harness's own error is not a result | a flat threshold: the worst control, floored at 5% |
| A run that fails its own self-test is thrown away | worst control > 10% → every verdict `unusable`, exit non-zero |
| Filtered-out cases cannot republish stale rows | `make run-bench` stamps the clock, `report --since` cuts on it |
| A number that survives none of this is not published | only `vs genesis` and the recentered `cand vs now` are comparisons; absolute times are not |

Two of those thresholds are **borrowed calibration**. The 5% floor
(`MIN_EFFECT`) and the 10% veto (`USABLE_BIAS_MAX`) are AeneasCompPoly's
numbers, arrived at by sweeping a full run of byte-identical code on its own
hardware; upstream records that even there 5% was a *target* rather than a
description, its worst byte-identical row reading 6.10%. This repository has not
run that sweep. What it has is worse, and it is in `NOTES.md § "The first
benchmark run, and what it says about the harness"`: on the 4-core cloud
container that produced this repo's only completed `make run-bench`, the
`_control` cases in `ring`, `linalg` and `commit` read **15%, 14% and 10%** — at
or above the veto — and two byte-identical rows read **59%** (`ring/scalar_mul`)
and **39%** (`commit/verify_weak`), i.e. worse than their own group's floor.
Read the consequence literally: on a host like that the harness's own self-test
says it cannot produce a verdict, and nothing in `harness.py` will shrink the
number. Establish a quieter host — pinned cores, no neighbours — before
believing any margin, and do not read the 5% floor as evidence that this
repository resolves 5% effects.

## 1 · Freeze the first translation

**Before** the bench, and in lockstep with the source. `benches/genesis/` is the
starting point every future measurement is scored against; its `lib.rs` contract
is worth reading rather than paraphrasing — *"Nothing here is ever edited. Not
to fix a lint, not to fix a typo, not to follow a rename in `hachi`"*, and
*"Genesis composes with genesis"*, so `vs genesis` is the cumulative improvement
over the first translation of the whole call chain.

All five modules are already frozen, and today the frozen copies are
byte-identical to `hachi/src` — so §1 is about the *next* operation, not a
backlog. The commit choreography is fixed by three mechanics and cannot be
reordered:

```bash
# 1. (agent) stage src and the VERBATIM, UNSTAMPED genesis copy together
git add hachi/src/<module>.rs hachi/benches/genesis/src/<module>.rs
# 2. (user)  commit 1 — both, one commit; the stamp will name this sha
# 3. (either) make bench-stamp   # derives `@genesis <sha> <date>` from cmt 1
# 4. (user)  commit 2 — the stamp lines alone. NEVER --amend commit 1.
# 5. make bench-check             # green before any number is taken
```

`stamp-genesis` finds the earliest commit whose `hachi/src/<module>.rs` contains
the item's text verbatim, so it cannot be talked into a wrong sha — but it also
cannot stamp text that is in no commit, which is why the source is committed
first. And it cannot be replaced by typing: `check-genesis` verifies the
attribute against git, so a hand-written placeholder such as `// @genesis (this
file's introducing commit) <date> — <path>` is not a stamp and does not pass. If
you find one, `make bench-stamp` is the fix, never an edit.

Step 4 is not tidiness. `--amend`ing commit 1 changes its sha, and the stamp
stores that sha, so the amend orphans every annotation `bench-stamp` just
derived.

**Copy, do not retype, and do not tidy.** The check is byte-exact. A reflowed
comment fails it, and rightly: the point is a guarantee that the baseline is the
original, and "I only changed a comment" is not a guarantee.

### If you discover a missing or wrong baseline late

`make bench-check` lists items in `hachi/src` with no frozen counterpart. If one
has *already been optimized* since it was written, **do not copy today's code**
— that would freeze the optimized version and silently report all its gains as
zero. Recover the original:

```bash
git log --oneline --reverse -- hachi/src/<module>.rs   # where it first appeared
git show <sha>:hachi/src/<module>.rs                   # take the ORIGINAL text
```

Paste that, then `make bench-stamp`. The stamper will confirm the sha by finding
the same text; if it names a later commit than you expected, you copied the
wrong version.

### The re-freeze carve-out, and why it is currently wide open

Genesis is append-only *because* editing it rewrites the history of every
measurement scored against it. Where there is no such measurement, there is no
history to rewrite. This repository has published none: `NOTES.md § "Benchmark
numbers from this session are not measurement-grade"` and the section that
supersedes it both say the numbers taken so far are sizing information and not a
baseline, and `logs/ledger.jsonl` starts empty. So for **every** item frozen
today, a defect caught now is honestly repairable: replace the frozen text with
the corrected first translation, re-stamp against the fixing commit, and say so
in the commit message and in `NOTES.md`. That window closes per item, the moment
a number is published against it — and it closes silently, which is why the rule
is written down here instead of being rediscovered later.

## 2 · Write the case

One body, taking `Mode` and the size parameter, instantiated against all three
crates by `case!`. Pick the runner by how the operation treats its input:

| Operation shape | Runner | Why |
|---|---|---|
| returns a value or a fresh `Rq`/`PolyVec` | `support::run` | `Bencher::iter` black-boxes the result; allocation and drop are the caller's real cost |
| per-element, result into a caller buffer | `support::run_into` | a per-element returned value would cost as much as the field op itself |
| **consumes** or mutates its input | `support::run_batched` | `iter_batched` builds inputs and drops outputs *outside* the timed region (verified in criterion 0.7's source, and 0.8's) |

`hachi`'s API makes this unusually easy to get right, and unusually easy to get
wrong in exactly one place. Every operation over the ring, vectors, matrices,
gadget and commitment takes `&self` (or `&Vec<_>`, per the `ptr_arg = "allow"`
note in `hachi/Cargo.toml`) and returns a fresh value: `run` is the correct
runner for all of them. The by-value APIs are the **constructors** —
`PolyVec::new`, `PolyMatrix::new`, `Decomp::new`, `Opening::new`,
`PublicParams::new` — which take their `Vec` or their struct by value. Benching
one of those with `run` measures the clone that feeds it, not the constructor;
they are the `run_batched` cases. `run_into` has no user in this crate today,
because nothing here writes into a caller-owned buffer; the field layer that
would want it lives in `cpoly`, not in `hachi`.

Then, non-negotiably:

* **Every input through `black_box`**, at every use inside the body. An input
  the optimizer can see through is an input it can fold the whole loop against.
* **Different corpus tags per operand.** `corpus(seed, n)` twice with one seed
  is `a + a` or `a * a`, and squaring is not what `mul` is for; `corpora`
  derives a distinct stream per block for exactly this reason. The exception is
  deliberate and must be commented: `equals(&a, &a)` is the *worst* case for
  `equals` and the right input for it.
* **Non-degenerate inputs, deliberately chosen.** The corpus draws from
  `[1, Q)` — never zero — and reads `hachi::params::Q` directly, so it cannot
  silently disagree with the field it is generating for. Ask what input would
  make the loop exit early, and note that in this crate the answer usually
  depends on an optimization that has not landed yet:
  * `Rq::equals` and `Rq::is_zero` are written **branchless** today — they set a
    flag and run the full `N` coefficients, because that is the shape the Lean
    decision-procedure proof mirrors. The obvious optimization is an early
    `return`, and the moment it lands the corpus decides the reading: a non-zero
    input makes a short-circuiting `is_zero` exit at index 0, so an `is_zero`
    case fed the ordinary corpus would report that rewrite as an `N`-fold win
    that exists only for non-zero inputs. Feed it zeros, or exclude it by name.
  * `gadget::digit_at(c, e)` divides `e` times, so its cost tracks the digit
    index and not the value — a case at a single small `e` cannot see the
    `O(digits²)` shape `gadget_decompose` inherits from it.
  * `Rq::from_coeffs` is the inverted case: it always writes `RING_DEGREE`
    coefficients whatever the input length, so no input makes it degenerate
    today — but the corpus always hands it exactly `RING_DEGREE` elements, so a
    candidate that adds an `m == n` fast path would have that path taken on
    every iteration and the general path the totality argument covers would go
    unmeasured. Add the short-input size before believing such a candidate.
* **Sizes are the scheme's parameters, and say so.** The existing cases take
  their sizes from `hachi::params` — `RING_DEGREE`, `GADGET_DIGITS`,
  `MESSAGE_ROWS`, `INNER_ROWS`, `OUTER_ROWS`, `BLOCKS` — because this crate is
  deliberately concrete: a case at any other size measures a scheme this
  repository does not implement. Add a second size only when the *shape* of the
  algorithm is what an optimization would change (an exponent cannot be seen at
  a single point), and say in the comment which shape you expect to see.
* **A `// @covers <path>` marker** directly above the `bench_case!` line, with
  the exact item path `harness.py` prints. `coverage --strict` binds marker to
  row: a path that names no item, or a marker sitting on no `bench_case!` in
  that module, fails the gate rather than silently dropping the claim.

If a mirrored item genuinely should not be benched, add it to
`benches/exclusions.toml` **with a reason that can be checked by reading it**.
The bar is "a criterion run would measure the harness, not the item" — the
`params.rs` constants are the archetype, and `Rq::len` (one `Vec::len`) and
`Rq::coeff` (one index) are the O(1)-by-inspection class. It is **not** "this is
not on the hot path".

`coverage` takes its work list from docstrings carrying a
``Mirrors `<ArkLib name>` `` line, so writing that line for the item you are
benching is part of the job (it is `lean-to-rust`'s convention, and it is what
makes the coverage claim mean anything) rather than a separate cleanup. Never
assume the gate is green: run `make bench-coverage` and read the count.

The gate *is* green as of the port that introduced it — **40 mirrored items, 32
benched, 8 excluded by name, 0 unaccounted for**, plus 3 non-mirrored items
benched as well (`ring::Rq::equals`, `linalg::PolyVec::equals` and
`gadget::base_pow`, which mirror nothing and are benched anyway; that is allowed
and often right — the two `equals` are decision procedures with no ArkLib
counterpart named in this repo, and `base_pow` is `HPow` on `ZMod q`). The 8
exclusions are the 6 mirrored `struct`s — `rustitems.benchable()` excludes
`struct` outright, so a marker on a type *always* implies an exclusion — plus
`ring::Rq::coeff` and `commit::centered_abs`, the two O(1)-by-inspection bodies.
Do not treat those counts as a target to preserve: the only invariant is
`0 UNACCOUNTED FOR`, and a new operation moves the first two numbers by
construction.

## 3 · Make it run

```bash
make bench-check                          # genesis + null slot + coverage
make run-bench BENCH='<module>/<case>'    # one case, still full rigour
```

The digest assertion in `case!` runs for **every** case in the file even under a
`BENCH=` filter, so a semantic disagreement between `hachi` and the baseline
surfaces on the first run regardless of what you filtered to.

What a filtered run does **not** validate: the `_control/*` cases do not match
the filter, so the report prints that `vs genesis` is unvalidated — the digest
oracle stands, but the timing delta carries no error bar. An accept/reject
decision takes a full `make run-bench`, never a filtered one. For a candidate
the rule is harder: a candidate row in a binary whose control did not run gets
verdict `unvalidated` and the report exits 2.

## 4 · Adversarial review — mandatory, before the case is trusted

Do **not** review your own bench by rereading it. You wrote it believing it was
right; rereading mostly re-confirms that. Spawn agents whose job is to *refute*
it, give each a different lens, and require evidence rather than opinion.

The claim under attack, stated per case:

> `<case>` measures the cost of `<item>` at size `<n>`, and nothing else.

Fan the lenses out with the Workflow tool — one agent per lens per case, verify
stage adversarial:

```js
export const meta = {
  name: 'bench-audit',
  description: 'Refute the claim that each new bench case measures what it says',
  phases: [{ title: 'Refute' }, { title: 'Adjudicate' }],
}
const LENSES = [
  { key: 'dead-work',     prompt: `...` },
  { key: 'contamination', prompt: `...` },
  { key: 'wrong-thing',   prompt: `...` },
  { key: 'fairness',      prompt: `...` },
]
const findings = await pipeline(
  CASES.flatMap(c => LENSES.map(l => ({ c, l }))),
  ({ c, l }) => agent(l.prompt.replace('$CASE', c),
                      { label: `${l.key}:${c}`, phase: 'Refute', schema: VERDICT }),
  (v, { c, l }) => v.refuted
      ? agent(`A reviewer claims ${c} is broken: ${v.evidence}. Try to show they are
               WRONG. Run the commands yourself. Default to agreeing only on evidence.`,
              { label: `adjudicate:${l.key}:${c}`, phase: 'Adjudicate', schema: VERDICT })
      : null,
)
```

Instruct every agent: **run commands, quote numbers**. "Looks fine" is not a
verdict; neither is "this could theoretically be optimized away".

### Lens A · dead work — is any of it being deleted?

* **Scaling.** Temporarily add a second size and check the ratio against the
  documented complexity: `Rq::add` is `O(N)` and doubles, `Rq::mul` is the
  schoolbook `O(N²)` negacyclic convolution and quadruples, `mat_vec_mul` is
  `rows · cols` ring multiplies. A flat curve where the complexity says
  otherwise means the work is gone or the input is degenerate.
* **First-principles floor.** Count the field operations the case must perform
  and divide by a plausible per-op cost. The only local figure to anchor on is
  the sizing table in `NOTES.md § "The first benchmark run"`: `ring/mul` at 8.51
  µs over `N² = 4096` coefficient products puts that host near 2 ns per
  multiply-and-accumulate. Treat that as an order of magnitude and re-derive it
  on your own host — the host it came from failed its own control check. A
  measured time an order of magnitude *below* the floor is proof, not suspicion.
  When you compute the floor for a gadget case, note that `GADGET_BASE` is the
  constant `2`, so `rest / b` in `digit_at` compiles to a shift; count shifts,
  not divisions.
* **Ablation.** Delete the body and confirm the time collapses; swap an input
  for a constant and confirm the time moves. If neither changes anything,
  nothing was being measured.

### Lens B · contamination — is anything extra being measured?

* Is corpus construction, `Rq::from_coeffs`, `copy`, or buffer allocation inside
  the closure rather than above it? The case bodies build their `Rq`, `PolyVec`
  and `PolyMatrix` values *once*, outside the timed region — check that yours
  do.
* Does a `run_batched` case do its cloning in `setup`, or has it leaked into the
  routine?
* Is the digest computed inside the timed region? It must not be — that is the
  entire reason `Mode` exists.
* Does the body call anything besides the item under test? Compare against the
  neighbouring case that shares most of the work: `linalg/dot` at `k` entries
  should be about `k` × `ring/mul` plus `k` × `ring/add`, and
  `gadget/gadget_matrix` should exceed `gadget/gadget_mul` because materializing
  `G` builds `rows²·digits` ring elements of which all but `rows·digits` are
  zero. If a containment relation like that inverts, one of the two is wrong —
  and read the warning in Lens D before concluding which.

### Lens C · wrong thing — right function, right inputs?

* Does the `@covers` path name the function the body actually calls? The
  same-name-different-type readings are the trap here: `Rq::equals`,
  `PolyVec::equals` and `Rq::is_zero` all wrap comparable loops, and `Rq::copy`
  and `PolyVec::copy` both exist; swapping two of them still compiles.
* Is the input degenerate in a way that skips the work (see §2)?
* Do the two operands of a binary operation come from different corpus tags —
  and where they deliberately do not (`equals`), does a comment say why?
* Is the size the one the comment claims, and is it a `params.rs` parameter?

### Lens D · fairness — is the A/B honest?

* Are all three variants generated from one case body, or has someone
  hand-written a second copy?
* If a genesis adapter exists (because the API diverged), does it do work the
  measured function should be doing? An adapter that pre-allocates for genesis
  is a rigged race.
* Did the `_control/*` rows come out near 0% in the run being used as evidence?
  Read the harness self-test block before believing any margin. It is the only
  error bar there is — everything is compared within one run, because cross-run
  comparison is worse than useless (AeneasCompPoly measured 75% and 373% drift
  on frozen code between runs, and this repository's single completed run put
  byte-identical code up to 59% apart *within* one run).
* Is the reported change larger than the printed threshold? A "win" at or below
  the A/B bias is not a win.
* Is the margin an *absolute* time or a delta? Only the delta is trustworthy —
  see "Trusting an absolute time" below.
* Does the new case make `_control/*` worse? A case that changes the binary's
  layout can move the controls; if the self-test degrades when the case is
  added, the case is the problem.

### Adjudicating

Any **confirmed** finding blocks the case; fix and re-run the audit. A
refutation that the adjudicator overturns is recorded in the case's comment so
nobody re-litigates it. If the lenses disagree and no command settles it, that
is itself a defect: the bench is not legible enough to be trusted, so make it
simpler.

## 5 · Run it for real

```bash
make run-bench                # the only mode; it wants the machine to itself
```

Serialize it. `Makefile § run-bench` says so and means it: one criterion
session at a time, repo-wide, and no `lake build` alongside it. Before
starting, check

```bash
ps -eo command | grep -c "[b]in/lean"     # someone else's Lean build?
```

and read the load average, then wait for that build rather than racing it.
This repository has already thrown away one set of numbers for exactly that
reason (`NOTES.md § "Benchmark numbers from this session are not
measurement-grade"`).

The harness stores nothing between runs and reads nothing from a previous one;
every comparison is made inside a single run. If a number needs keeping, take it
from `JSON=<path>` and keep it somewhere with a reason attached — `NOTES.md` for
the reasoning, `logs/ledger.jsonl` for a candidate verdict.

**Read the self-test block before the table.** If the A/B bias is near the size
of the effect you are looking at, you have not measured the effect. Close what
else is running and measure again — nothing inside the harness will shrink it.

## 6 · The candidate slot — the loop's within-run A/B

`perf-loop`'s accept decision needs "candidate vs current champion", and the
design above rules out every cross-run answer. So the harness carries a third
variant: `hachi/benches/candidate/`, a sibling crate like genesis (same
compilation path, same fat-LTO merge — the symmetry argument in
`benches/genesis/src/lib.rs` applies unchanged, and `candidate/src/lib.rs` says
so explicitly), timed only under

```bash
make run-bench CANDIDATE=1 BENCH='<op>|_control' JSON=<file>
```

What to know before touching it:

* **At rest it is a null candidate** —
  `src/{params,ring,linalg,gadget,commit}.rs` byte-identical to `hachi/src/`
  (`harness.py check-candidate`, part of `make bench-check`). The loop
  overwrites it inside its own worktree, benches, and discards the worktree;
  after a champion lands, the slot is re-synced in the same change. `lib.rs` is
  the slot's own documentation and is exempt, exactly like genesis's.
* **Variant order is `now`, `candidate`, `genesis`** — the accept column
  (`cand vs now`) is the tightest-spaced pair, and with the feature off the
  expansion is exactly the pre-slot macro.
* **The accept column is recentered, and that is not optional.** The candidate
  variant sits at a fixed position in every case, so `cand vs now` carries a
  *signed, systematic* layout/order lean. AeneasCompPoly's adversarial review
  (2026-08-11) is where this was found rather than foreseen: it measured **−3.6%
  to −3.8% on byte-identical code** the day the slot landed, reproduced it
  independently in every one of its bench binaries — so the lean is per
  *binary*, layout being a property of the linked binary — and computed what a
  symmetric threshold does with a signed offset: a null candidate crosses a 5%
  "faster" bar with roughly 20% probability per row, and a true +8% regression
  reads as noise. So each binary's `_control` measures its own lean in the same
  run, `report` divides it out (`cand_vs_now_adj`), and the 5% floor applies to
  the recentered value. Verdicts come from `cand_vs_now_verdict` only; the raw
  ratio is exported for transparency, never for decisions. All raw pairwise
  control magnitudes still feed the 10% run veto. The mechanism transfers; the
  numbers are upstream's, and this repository has not measured its own lean.
* **Controls are enforced for candidates, not advised**: a candidate case in a
  binary whose `_control` did not run this pass gets verdict `unvalidated` and
  the report exits 2. (For plain `vs genesis` a missing control still only
  downgrades the print.) Write the filter as `BENCH='<op>|_control'`;
  `CANDIDATE` must be exactly `1` — any other value, including `0`, disables the
  slot.
* **The report fingerprints the slot** (`candidate_slot` in the JSON: per-module
  sha, diverged-from-src list), so a number is attributable to the diff the slot
  actually held — the at-rest `check-candidate` gate cannot see inside a loop
  worktree, this can.
* **`check-candidate` pins everything that compiles**: module files byte-equal
  to `hachi/src`, exactly six files in `src/` (five modules plus `lib.rs`), no
  symlinks (a symlinked module passes any self-compare forever, and the loop's
  overwrite would write through it into the champion), and `lib.rs` +
  `Cargo.toml` byte-equal to their git-pinned content — `lib.rs` is the
  module-graph root, and one `#[path]` line there swaps out every checked byte.
* **The digest assert extends to the slot**: a candidate that computes a
  different result panics the run before any timing (`support/mod.rs`, `case!`).
  The loop's semantics tests run first; this is the last line, not the filter.
* **A default run is untouched by all of this**: the slot compiles (a path
  dependency must resolve — so a broken slot does fail the `cargo test` and
  `cargo bench` builds; `check-candidate` keeps it healthy at rest) but adds no
  timed rows, and a leftover candidate measurement from an earlier `CANDIDATE=1`
  run is cut per-variant by the required `--since`, so it can neither hide a
  case nor republish itself.

## Failure modes with teeth

**`cargo bench` handing criterion's flags to libtest.** `--benches` selects
every target with `bench = true`, which defaults true on the lib *and* on every
auto-discovered integration test. `hachi/Cargo.toml` pins `autotests = false`,
`bench = false` on the lib, and declares each of the five `[[test]]` targets —
leave that alone, and read the comment above `autotests` before touching it.

**Thin LTO making identical code 28% apart.** Already decided here, and the
reason is recorded in `hachi/Cargo.toml § profile.bench`: AeneasCompPoly
measured byte-identical code in two crates reading **28% apart** under
`lto = "thin"`, reproducibly, because thin LTO optimizes the crates in separate
modules and LLVM made different vectorization choices for the same source. Fat
LTO merges them before optimizing. The comment forbids reverting it for build
times, and the general lesson is the important part: *any* build setting that
lets the three crates be optimized differently is a correctness bug in the
fitness function. Note that this is a suspect already ruled out for this
repository's own 10–59% spread — `profile.bench` carries the fix, and the
spread is still there.

**Believing an estimator that describes the load.** Criterion's headline
`[lo mid hi]` is the regression **slope**; it and the mean describe the centre
of the sample distribution, which on a busy machine is mostly a description of
the other processes. (AeneasCompPoly's calibration run, at load average 7.75,
came out inflated 50–180% with narrow, disjoint, confident intervals.)
Contention only ever makes code look slower, so the report keeps the samples
criterion gave at least half the maximum iteration count and averages the three
fastest of those. The table therefore reads *lower* than the `cargo bench`
output above it; that is expected, not a bug.

**Measurement order looking like a speedup.** Criterion runs `now` to completion
before starting the next variant, so a warming CPU biases whatever comes second.
That is part of what `_control/*` measures. Never compare a margin against zero;
compare it against the printed threshold.

**Trusting an absolute time.** AeneasCompPoly measured two of its cases reading
**7–9× their true cost**, in a run whose control read 0.03%, printed next to
cases that strictly *contain* them — same binary, same callee, confirmed by
disassembly, correct again on a filtered rerun. It is machine/allocator state,
it persists across whole measurements, and no amount of sampling sees it: all
100 samples sat within 6% of the wrong value. It also survived consecutive
repeats, which is why a median-of-rounds made it *worse* — the median selected
the corrupted rounds. This repository's own run shows the same class of artefact
from the other side: `ring/scalar_mul` and `commit/verify_weak` read 59% and 39%
apart on byte-identical source, worse than their groups' control floors. Only a
same-run delta survives, because the artefact lands on both variants at once.
Never reason across rows, and never quote an absolute time as a result — the
sizing table in `NOTES.md` is labelled sizing information for this reason.

**Freezing an already-optimized function as "genesis".** Covered in §1. This is
the failure that cannot be detected later from the numbers alone — every gain
before the freeze silently becomes zero.

**Adding a bench file without declaring it.** `autobenches = false`, so a new
`benches/foo.rs` is simply not built until it has a `[[bench]]` entry in
`hachi/Cargo.toml`. Silence, not an error. Same shape as forgetting `MODULES`.

**A dev-dependency's MSRV breaking `cargo test`.** Cargo resolves the whole
dependency graph before it builds anything, so a dev-dependency whose
`rust-version` exceeds the active toolchain fails `cargo test` even though the
tests never link it. criterion 0.8 declares 1.86; `BENCH_TOOLCHAIN` here is
`nightly-2026-06-01`, a 1.85-era nightly, so 0.8 breaks `make test` outright.
The pin is **0.7** (declares 1.80) for that reason and no other, with
`default-features = false` to drop `plotters` and `rayon`. Before bumping it,
check `rust-version` against the oldest toolchain anyone runs `cargo test`
with, not against what the benchmarks need.

**Moving `BENCH_TOOLCHAIN`.** It is pinned to charon's own channel and checked
against `toolchain/rust-toolchain`, because a number is only comparable to
another number from the same compiler. Moving it is a re-baseline, not an
upgrade: no reading taken before the move stays comparable with one taken after.

## Invariants to keep green

* `make bench-check` passes — genesis verified against git, the candidate slot
  byte-identical to `hachi/src`, coverage complete.
* `cargo clippy --all-targets` clean under `pedantic`, benches included. The
  frozen and slot crates carry a blanket `allow(warnings, clippy::all,
  clippy::pedantic)` precisely so a lint that fires on code nobody may edit can
  never fail a build.
* `make extract` still reports `unchanged` — dev-dependencies must never reach
  `hachi/lean/Generated.lean`. (`cargo build --lib` does not build them; this is
  checked, not assumed, per `hachi/Cargo.toml`.)
* `_control/*` reads near 0%. It does not on the host in `NOTES.md § "The first
  benchmark run"`; that is a fact about the host, and the fix is the harness or
  the machine — never the interpretation.
* No claim rests on an absolute time or on comparing two rows to each other.
* Every mirrored item is benched or excluded **by name, with a reason**, and the
  item you just benched carries its `Mirrors` line.
* A new Makefile target is listed in `make help`, and in the right list. Under
  `Targets:` if someone who just cloned the repo would type it; under the
  advanced list if it exists so this loop can check or regenerate something
  mid-iteration — that is where `bench-check` and `bench-stamp` belong, and
  where a new `bench-*` almost certainly does too. One aligned line, ≤77
  characters, and it must not promise more than the target delivers; the rest
  goes in the Makefile comment above the target. Leave it unlisted only if it is
  a prerequisite nobody invokes, like `bench-toolchain`.
* Nothing about a run is persisted by the harness. Do not add a store of past
  timings without a consumer that can defend comparing across runs — the drift
  measured on frozen code, here and upstream, says none can.
* Agents stage; the user commits. The two-commit stamp dance in §1 is the only
  place in this repository where the commit boundary is load-bearing rather than
  stylistic.
