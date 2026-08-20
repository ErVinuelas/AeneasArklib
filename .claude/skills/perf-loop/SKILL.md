---
name: perf-loop
description: Orchestrating the inner optimization loop for a targeted ArkLib definition — arklib-analyze brief, lean-opt candidate fan-out, trivial translation, semantics tests, within-run candidate bench (CANDIDATE=1), accept/reject on the recentered cand-vs-now, ledger row, champion staging; use when asked to optimize a hachi operation end-to-end or to run the perf loop
---

# The Inner Performance Loop

Drives the inner optimization loop for **one target definition** (resolved by
its human dialogue or supplied by a route; choosing targets is a route/user
decision). Stages, each owned by its own skill: `arklib-analyze` → `lean-opt`
(+ the `opt-*` strategies) → `lean-to-rust` → the `rust-bench` candidate mode
→ this skill's accept rule and ledger. Aeneas is never touched per candidate;
the accepted champion owes one extraction check before landing, and the proofs
belong to the outer pass (`verify-campaign`).

The natural first target here is `hachi::ring::Rq::mul` — the schoolbook
`O(N²)` negacyclic convolution at `N = 64`. `hachi/benches/ring.rs` frames it
as "the operation an NTT would replace", whose reading is therefore "the
baseline any such optimization has to beat *and* carry an equivalence proof
for", and it is where everything above it spends its time (a `mat_vec_mul` is
`rows · cols` of these). Its source says the same thing from
the other side (`hachi/src/ring.rs` § "What is deliberately not here": no NTT,
because "an NTT is a later, bench-driven optimization and carries an
equivalence obligation of its own"). Nothing in this repository has been
measured to accept grade — see the one rule, and § "Before the first
iteration".

## Invocation

**Human invocation:** start with the bare command `/perf-loop`; do not put
parameters on the command line. Ask one question at a time: first **“Which
operation should I optimize?”**, then, for a direct invocation, **“Should
candidates come from Lean-side optimization or direct Rust optimization?”** A
route supplies the latter choice, so do not ask it again when a route calls
this skill. Resolve the answer into *both* names before benchmarking — the
ArkLib definition (the spec side) and the `hachi/src` item that mirrors it —
and confirm both, plus the candidate stage, with the user.

**Agent invocation:** bypass the dialogue with a named request:

```yaml
agent_request:
  target: <fully-qualified ArkLib definition>
  item: hachi::<module>::<path>
  candidate_stage: lean-opt | rust-direct
```

Both names are required, and that is one field more than upstream needs.
There, spec def and Rust item shared a name; here the spec side is ArkLib —
generic in `(q, α, b, digits)` and written in Mathlib's vocabulary — and the
Rust side is concrete, so the correspondence is per-item documentation (the
`(spec: …)` clause each op in `hachi/src` carries) rather than a naming rule.
The bench case id, the `@covers` marker and the swap are all keyed by the Rust
item; the proof obligation is keyed by the ArkLib one. `candidate_stage` is
required for a direct agent call and is inherited from a route composition.
Validate the packet; report missing or invalid fields to the invoking agent
instead of asking the human.

## The one rule: only a within-run measurement accepts a candidate

The accept column is the **recentered** `cand vs now` from a single
`CANDIDATE=1` run — the candidate and the champion measured in the same
criterion session, the slot's signed identical-code lean (measured by that
binary's `_control` in the same run) divided out, the 5% floor applied to what
remains. Nothing else accepts: not op counts (they only rank candidates for
benching), not Lean intuition, not a delta assembled from two runs
(AeneasCompPoly measured frozen code drifting 75% and 373% between runs when
that was tried), not the raw un-recentered ratio (upstream's adversarial
review, 2026-08-11, measured the slot's lean at −3.6% on byte-identical code
the day the slot landed, and showed that a symmetric threshold on the raw
value accepts null candidates at ~20% per row), and not a run whose report
says `unusable`. Every shortcut here converts machine noise into a
"champion", and the loop would then optimize the weather.

Both thresholds in that paragraph — the 5% floor (`MIN_EFFECT`) and the 10%
identical-code veto (`USABLE_BIAS_MAX`) — are **AeneasCompPoly's calibration**,
inherited with `harness.py`. This repository has never swept its own. What it
has measured is worse: on the host that produced its only completed
`make run-bench`, the `_control` cases read 15%, 14% and 10% and two
byte-identical rows read 59% and 39% (`NOTES.md` § "The first benchmark run,
and what it says about the harness"). The harness's own veto is what that
condition trips, and it is supposed to: a run at that bias reports
`unusable` and accepts nothing. Read the consequence literally — on such a
host this loop cannot accept a candidate at all, and the fix is a quieter
machine, not a smaller threshold.

## Before the first iteration

The accept rule needs an instrument, and the instrument is `rust-bench`'s and
`op-genesis`'s deliverable, not this skill's. Establish it rather than assume
it, once per session, and stop with a report if any of it is missing:

* `hachi/benches/harness.py` exists, and `make run-bench` stamps the clock and
  calls `harness.py report --since <stamp>` (a bare `cargo bench` produces no
  verdict at all — no recentering, no slot fingerprint, no exit 2). Check this
  first and do not assume it: `NOTES.md` § "Deferred from Workstream 0,
  deliberately" records the harness's checkers as *deferred* — what landed
  early was the part that cannot be added retroactively (both slot crates as
  siblings on the same compilation path, the `candidate` feature, the pinned
  `profile.bench`) — and says the checkers arrive with the first real module.
* `make bench-check` is green — `check-genesis` + `check-candidate` +
  `coverage --strict`. That is what says the frozen baseline is the one git
  holds and the slot is null before you fill it.
* Each bench binary has a `_control` group (`_control/<binary>`), because a
  candidate row in a binary without one gets no verdict.
* The machine is quiet, checked on the machine rather than in the repo:
  `ps -eo command | grep -c "[b]in/lean"` plus the load average.
* `hachi/benches/*.rs` are in the case shape the report keys on — one criterion
  group per case named `<module>/<op>`, variants `now` / `candidate` /
  `genesis`. A pre-harness shape (one group per module, ids `<op>/<variant>`)
  reports nothing this rule can read.

## The procedure, per iteration

1. **Brief** — `arklib-analyze` on the target.
2. **Candidates** — the route's candidate stage. Default (`route-r1`/`route-r3`):
   `lean-opt`, tiered strategy fan-out (one Opus agent per strategy,
   worktree-isolated), opt-contract enforced. Under `route-r2` the stage is
   `rust-direct`: candidates arrive as Rust diffs, skip step 3's translation,
   and their pre-bench contract is that skill's ceiling audit instead of the
   opt-contract. Either way, contract failures are already ledger rows; only
   contract-ok candidates continue.
3. **Per candidate, in its worktree**, in this order:
   * apply the translation (`lean-to-rust`) of the opt def to `hachi/src`;
   * `cargo test` — the cheap semantics filter; the module suites in
     `hachi/tests/` are written deliberately unlike the crate, so they are a
     real check and not a restatement. Failure → row `tests-failed`, drop the
     candidate;
   * copy the **five module files** over the slot, one at a time —
     `for m in params ring linalg gadget commit; do cp hachi/src/$m.rs
     hachi/benches/candidate/src/; done` — then restore the champion with
     `git restore hachi/src`. Never `cp hachi/src/*.rs`: the slot's `lib.rs` is
     its own documentation, pinned to git by `check-candidate`, and is *not* a
     copy of `hachi/src/lib.rs` (verified: at rest the five modules are
     byte-identical and `lib.rs` differs from the first line). A glob copy
     fails the gate at best and swaps the module graph at worst;
   * `make run-bench CANDIDATE=1 BENCH='<module>/<op>|_control' JSON=<file>` —
     e.g. `BENCH='ring/mul|_control'`. Keep `_control` in the filter; the
     report exits 2 with `unvalidated` verdicts if a candidate case ran in a
     binary whose control did not (enforced, not advisory). `CANDIDATE` must be
     exactly `1`.
4. **Bench discipline.** Bench runs are strictly serial — one criterion session
   on the machine at a time, loop-wide; two at once corrupt both. The rule is
   wider here than a bench-vs-bench rule: **one criterion session or one
   `lake build` at a time, repo-wide**, because `make build` on a cold Mathlib
   cache costs hours (`NOTES.md` § "The Lean side does build here, it just
   takes hours": ~2700 Mathlib modules) and saturates the cores a measurement
   needs. Exit code 2 (`unusable`, identical code measured >10% apart) → close
   what else is running and repeat once; never lower a threshold to make a run
   count.
5. **Verdict**, from the run's JSON, on the target's rows only, always via
   `cand_vs_now_verdict` (which is computed from the recentered
   `cand_vs_now_adj`, never from the raw ratio):
   * accept iff **every** measured row of the target reads `faster` — the
     rows share one lean but their noises are independent, so demanding all
     of them cuts the residual false-accept rate multiplicatively, and a
     real algorithmic win shows at every size it claims to help;
   * **a single-row target needs a second, independent `CANDIDATE=1` run, and
     both must read `faster`.** This is a local strengthening, and the reason
     is a fact about this crate: `Rq`'s degree is a `const`
     (`params::RING_DEGREE = 64`), so every `ring/*` case has exactly one row
     and the multiplicative argument above has nothing to multiply. Two
     independent within-run verdicts is strictly stronger than one and still
     never subtracts across runs — what is forbidden is *combining* two runs'
     numbers, not requiring two runs to agree;
   * mixed rows (`faster` at one size, `slower` at another) are a real
     algorithmic trade-off: reject, but surface it to the user with the
     numbers — it may deserve a size-split champion, which is a target
     decision, not a bench verdict;
   * anything else → `rejected-noise` / `rejected-slower` per the worst row.
6. **Tournament.** Multiple accepted candidates for one target: rank by
   `cand_vs_now` at the largest measured size, then confirm the winner with
   one fresh `CANDIDATE=1` run against the champion. Never chain deltas
   across candidates' separate runs.
7. **Champion landing** (accepted winner):
   * `hachi/lean/Opt.lean` def + lemma + the `#print axioms` line in
     `hachi/lean/Check.lean` § 4 — pure additions. On the **first** accepted
     champion this also creates `Opt.lean` and adds `Opt` to `roots` in
     `hachi/lakefile.lean`; `lean-opt` owns that step and its failure mode;
   * `hachi/src` swap. The item's `(spec: …)` clause keeps naming the **ArkLib**
     definition — the semantics did not change, which is exactly what
     `opt_eq_spec` says — and gains a pointer to the variant the body now is
     (`opt: HachiEquiv.Opt.Rq.mul.opt`), so the lemma chain is findable from
     the code. The type-level ``Mirrors `…` `` line on the carrier stays
     untouched: a changed carrier is a representation change, which is a gated
     proposal, not a champion. Semantics tests extended per `lean-to-rust`'s
     obligations;
   * any **new** helper fn is a first translation: freeze into genesis +
     case/exclusion, per `op-genesis` and `rust-bench` — `make bench-check`
     must be green;
   * re-sync the slot (byte-copy of the new `hachi/src` modules);
   * one extraction check in the worktree per `aeneas-extract`
     (deterministic, zero axioms, loop shapes); its result goes in the row;
   * ledger row, then **stage — never commit** (house rule): the loop ends by
     handing the user an ordered commit plan. Where stamp mechanics force it,
     interleave: content commit, then `make bench-stamp`, then a stamps-only
     commit — never `--amend` the first, since the stamp stores its sha.
   * The Rust swap + regenerated `Generated.lean` + broken `_spec`s are proof
     debt that must not reach main — prepare them as a `champion/<op>` branch
     in the commit plan. Here that debt has teeth: Aeneas names extracted
     loops **positionally**, so `Rq::mul` arrives as `ring.Rq.mul_loop0`,
     `ring.Rq.mul_loop1` and `ring.Rq.mul_loop1_loop0` (`NOTES.md` § "What the
     extraction of the four modules actually looks like"), and
     `hachi/lean/Ring.lean` proves one `_spec` per loop about exactly those
     names. A swap that changes the loop structure therefore does not weaken
     the proof, it stops it compiling — and `make build` is a hard gate, so
     the champion cannot land on main until `verify-campaign` pays the debt
     (K=1 until the ledger says otherwise) before the next target is taken up.
     Never park a `sorry` under `hachi/lean/`; Lean that is not yet proved, or
     proved but not yet audited, goes to `hachi/lean-wip/` under the rules in
     its `README.md`.
8. **Iterate** — next `lean-opt` tier on the (possibly new) champion — until
   a full round yields no accept, or the user stops the loop.

## The ledger (candidate-row schema; the file is `skill-lab`'s)

`logs/ledger.jsonl` — file conventions, ownership, the entry discipline, and the
full `kind` table live in the `skill-lab` skill; this section owns only the
candidate-verdict row. One JSON object per line per candidate verdict,
accepted or not — rejects are the cheap lessons the strategy skills grow
from. Rows without a `kind` field are this loop's candidate verdicts; any
tooling over the ledger filters on `kind` first. The file is created **empty**
by the port that added these skills: there is no champion history, no past
campaign, and no earlier verdict to compare against.

<!-- ⚠️ SYNC RULE: source of truth is skill-lab "The ledger" -->
Three duties this loop owes that discipline: append each row to the
**worktree's** `logs/ledger.jsonl` and stage it with the work it describes (a run
that lands no champion puts a ledger-only commit in its plan); mint one
`"run": "<compact ISO time with offset>-<machine id>"` per `make run-bench`
invocation and stamp it on every row copied from that report; and run
`make ledger-check` before writing the commit plan. The numbers in a row are
copies of one run's within-run deltas and are valid **only as that run's
claim**: no tooling may subtract two rows' numbers, and nothing here justifies a
cross-run comparison (the attempt that failed is documented in
`hachi/benches/genesis/src/lib.rs`).

Schema only — the numbers below are placeholders. Nothing in this repository
has been measured to accept grade (`NOTES.md` § "The first benchmark run, and
what it says about the harness").

```json
{"ts": "2026-08-20T14:03:00+02:00",
 "target": "ArkLib Mul (Rq Φ) — CyclotomicRing/Rq.lean:110",
 "item": "hachi::ring::Rq::mul",
 "op": "ring/mul",
 "strategy": "opt-algo-swap",
 "candidate": "mul.opt — karatsuba, 1 level",
 "verdict": "accepted",
 "run": "20260820T1403+0200-<machine id>",
 "rows": [{"case": "ring/mul", "cand_vs_now": -0.33,
           "cand_vs_now_adj": -0.31, "cand_vs_genesis": -0.31,
           "verdict": "faster"}],
 "cand_lean": -0.021, "slot_sha": {"ring": "1a2b3c4d5e6f"},
 "threshold": 0.05, "ab_bias": 0.021, "machine": "<id from the report>",
 "extraction": "clean",
 "pins": {"repo": "abc1234", "dirty": false,
          "arklib": "e92dc315f453db88dd7351c88e889caf0e6bf269",
          "cpoly": "583cfaff0617180764ffd849d867331af206fc5e",
          "aeneas": "nightly-2026.07.26-3a8586f",
          "bench_toolchain": "nightly-2026-06-01"},
 "notes": "champion/ring-mul branch carries the swap; Ring.lean mul_loop*_spec broken by it"}
```

`verdict` ∈ accepted · rejected-slower · rejected-noise · rejected-mixed ·
tests-failed · lemma-failed · not-translatable · no-strategy-applies ·
contract-violation · bench-unusable. `target` is the ArkLib definition as the
brief names it (`arklib-analyze` reads it from the pinned copy; do not spell an
ArkLib name from memory) and `item` is the Rust item the numbers are about.
`pins.repo` is `HEAD` (short) with `dirty` true when the skills/infra under
test are staged but uncommitted — honest provenance beats pretty provenance.
`skill@commit` pinning needs no per-skill field: every skill lives in this
repo, so `pins.repo` pins them all. Both spec-side pins belong in a row: ArkLib
is what the proof is against, and the `cpoly` rev is what the field layer — and
therefore the frozen baseline's speed — is. `slot_sha` and `cand_lean` come
from the run's report (`candidate_slot` / `cand_leans` in the JSON): the sha
ties the numbers to the diff the slot actually held, the lean records what was
divided out of the accept column.

## Failure modes with teeth

* **A `BENCH=` filter that drops `_control`.** For the accept column this is
  a hard failure — candidate verdicts read `unvalidated` and the report exits
  2 (upstream's adversarial review demonstrated the fail-open version: a stale
  30%-bias run's controls filtered away, a 20% "win" printed, exit 0). For
  plain `vs genesis` runs it still degrades to an unvalidated print, so write
  the filter correctly either way: `BENCH='<module>/<op>|_control'`.
* **Accepting on `vs genesis`, or on the raw `cand_vs_now`.** The first
  contains every *previous* champion's gain; the second contains the slot's
  signed layout lean (upstream measured −3.6% on identical code). The accept
  column is the recentered `cand_vs_now_adj` via its verdict, nothing else.
* **A landed run that forgot the restore step.** `hachi/src` still carrying a
  candidate diff, or the slot left divergent — `make bench-check`
  (`check-candidate`) is the tripwire; run it before writing the commit plan.
* **Benching a slot nobody filled.** `make run-bench CANDIDATE=1` runs
  `check-genesis` and the coverage audit but **not** `check-candidate`, and
  the report's slot witness only says which modules differ from `hachi/src` —
  which they do as soon as `src` holds the candidate, so an untouched slot
  still prints a plausible `diverged: [ring]`. The candidate column then
  measures the *champion*, every row reads ~0%, and the verdict is a silent
  false reject. Step 3's order exists for this reason: copy `src` → slot
  **first**, then `git restore hachi/src`, and confirm the slot's per-module
  sha in the report is not the champion's before reading any verdict.
* **Two loops at once, or a build beside a bench.** Worktrees isolate files,
  not the machine: a `lake build` or a second bench during a criterion session
  lands asymmetrically on the variants. Lean building and benching never
  overlap, and here a `lake build` is not a short interruption — `hachi/.lake`
  holds ~8.5 GB of built Mathlib on this checkout, and a from-scratch check is
  hours.
* **A busy machine this repo cannot see.** The serialization rule binds work
  *this* project starts; other projects on the same hardware are invisible to
  every worktree check. Upstream measured a foreign Lean build (load average
  36) driving a candidate run to an A/B bias of 64%, with rows that would have
  published −6.5% and +136% for one candidate. And "idle" has to be checked
  rather than assumed: this repository's own idle-machine run still read
  10–15% on its controls. So check the machine, not the repo, before a run —
  `ps -eo command | grep -c "[b]in/lean"` plus the load average — and when the
  competition is someone else's work, wait for it or hand the run back. Never
  free the slot by killing it, and never lower a threshold to make a contended
  run count.
* **A worktree freezes the harness at creation time.** A worktree cut before a
  harness fix benches with the old report semantics: the measurements are fine,
  the verdicts are not (upstream's first supervised run hit exactly this). If
  `hachi/benches/harness.py` changed since the worktree was cut, re-copy it
  before the accept run; a report-only rerun on the same criterion state
  (`harness.py report --since <original stamp>`) is the honest repair when it
  happens.
* **The report rides the run.** `make run-bench` benches and reports in one
  invocation; the slot fingerprint is read at *report* time, so a post-hoc
  re-report describes the slot as it is then, not as it was benched. Record
  `slot_sha` from the run's own report, and note any report-only rerun in
  the ledger row.
* **Treating the instrument's absence as a green light.** No harness, no
  `--since` stamp, no `_control`, or a `make run-bench` that only calls
  `cargo bench`: there is no accept column, and criterion's own output is not
  one. Stop at § "Before the first iteration" and report, rather than reading
  percentages out of criterion's summary.

## Invariants to keep green

* Stage, never commit — every loop run ends with staged changes and a
  written, ordered commit plan for the user.
* Every candidate that reached step 3 has a ledger row, whatever its fate.
* No champion lands without: tests green, an `accepted` row, the extraction
  check recorded, `make bench-check` green, its spec reference truthful.
* No `sorry` anywhere `hachi/lean/Check.lean` reaches, at any point in the
  loop; unproved or unaudited Lean lives in `hachi/lean-wip/`.
* At rest, the slot's five module files ≡ `hachi/src` byte-for-byte with
  `lib.rs`/`Cargo.toml` as git holds them, and `logs/ledger.jsonl` is
  append-only — a rewritten row is a falsified history.
