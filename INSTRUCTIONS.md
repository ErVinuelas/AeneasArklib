# Working with the skills in this repo

This repository turns ArkLib definitions into executable Rust that is *proved* to
compute what the definition says. Two loops do the work: an inner loop that
optimizes an operation and accepts a change only when a benchmark says it is
faster, and an outer pass that proves the optimized Rust equivalent to the
original definition. The skills in `.claude/skills/` are how that work is carried
out — each one is a written procedure an agent follows.

This file is the catalogue. The first half is for **you**, the human: the handful
of skills you would invoke to start a piece of work, and what they will ask. The
second half is a reference table of every skill, for agents to look up mid-task.
The skills themselves are the source of truth; if this file ever disagrees with
one, the skill is right and this file is a bug.

> **Where this came from, and what that means for the numbers.** The skill set is
> a port of [AeneasCompPoly](https://github.com/tobias-rothmann/AeneasCompPoly)'s,
> the sister project this repository follows in structure and method (and depends
> on for the coefficient field). The *procedures* transfer. The *measurements* in
> them mostly do not: where a threshold or a failure mode is justified by a number,
> that number was taken on AeneasCompPoly's machine and is attributed to it in the
> skill. This repository has run no measurement-grade benchmark yet — see
> [`NOTES.md`](NOTES.md) § "Benchmark numbers from this session are not
> measurement-grade" — and [`logs/ledger.jsonl`](logs/ledger.jsonl) is empty.
> Treat every borrowed number as a starting parameter awaiting a local
> calibration, never as evidence about this machine.

---

## Part 1 · The skills you invoke

### How human invocation works

Start every skill with its **bare slash command**: `/perf-loop`, not
`/perf-loop ring::Rq::mul`. The command starts a short intake: the skill asks one
direct question at a time, uses what the conversation already established, and
confirms the resolved request before it begins work. That keeps a target, route,
or trigger from silently disappearing from the request.

The fields below are questions for humans, not command-line arguments. An agent
calling another skill supplies the named `agent_request` packet from that skill's
reference entry instead; a complete packet skips the intake. An approval gate that
needs your authorization still asks you, whichever way the skill started.

### Choosing one

| You want to… | Invoke | It first asks |
|---|---|---|
| Bring an ArkLib definition into the pipeline for the first time | `/op-genesis` | Which definition should I onboard? |
| Read a definition and get a costed optimization brief | `/arklib-analyze` | (agent-facing; the target is handed in) |
| Define unproved Aeneas theorem stubs after extraction | `/aeneas-spec-author` | Which extracted operation should I specify? |
| Fill in one unproved `sorry` | `/prove-sorry` | Which theorem, or should I list the open `sorry`s? |
| Send a substantial Lean proof backlog to Aristotle | `/aristotle-prove` | Which files hold the large or genuinely hard backlog? |
| Check Aristotle sessions | `/aristotle-check` | Nothing, unless a session is active and needs a fresh key |
| Make an existing operation faster (and prove it after) | `/perf-loop` | Which operation? Then: Lean-side or direct-Rust candidates? |
| Run a supplied optimization route | `/route-r1` · `/route-r2` · `/route-r3` | Which operation should it optimize? |
| Compare routes, or two versions of a skill | `/skill-lab` | A route bake-off, or a skill A/B? |
| Run the whole pipeline unattended | `/autonomy-harness` | Default `route-r3`, or pin another route? |

### What the load-bearing ones do

**`op-genesis` — onboard a new operation.** Writes a deliberately *naive* first
translation of an ArkLib definition into `hachi/src`, tests it, extracts it, and
freezes that first version as the permanent baseline every future speed-up is
measured against. It onboards the whole dependency chain in one pass,
dependencies first. Optimizing is explicitly *not* its job: the first translation
is meant to be slow and obvious.

*What it asks of you*: the commit plan is interleaved, because a stamp records a
commit that must already exist. You commit the translation and the frozen baseline
together, `make bench-stamp` derives the stamps from that commit, you commit those
separately — never `--amend` the first, since a stamp stores its sha — and only
then can the birth benchmark run.

> All five modules (`params`, `ring`, `linalg`, `gadget`, `commit`) are **already**
> onboarded and frozen, with 81 git-verified stamps. So `op-genesis` is for the
> next operation, not for catching up.

**`perf-loop` — optimize one operation.** Generates candidates, translates them,
and measures each against the current champion inside a *single* criterion
session, accepting only what is measurably faster. Repeats until a full round of
strategies yields nothing.

- *Accept rule you can rely on*: a candidate is accepted only on the **recentered**
  `cand vs now` delta — each bench binary's own `_control` case measures the
  candidate slot's signed identical-code lean in that same run, and that lean is
  divided out before the 5% floor is applied. Nothing else accepts: not operation
  counts (they only rank candidates for benching), not a delta assembled from two
  runs, not a run the harness marked `unusable`.
- *The 5% floor is inherited.* AeneasCompPoly's own sweep of byte-identical code
  found residual noise up to 6%, so a verdict between 5% and 6% is thin *there*.
  Here the equivalent sweep has not been run, so the floor is a borrowed
  parameter. The first honest calibration is cheap and available today: the
  candidate slot is null and genesis is byte-identical to `hachi/src`, so a full
  `make run-bench` right now measures nothing but this machine's own noise, and
  every row of it must read noise.
- *It may ask*: a candidate that is only equivalent under an input condition the
  ArkLib definition does not impose needs your sign-off. It is never accepted as
  an ordinary candidate.
- *Proof debt*: every accepted champion goes to `verify-campaign` before the next
  target is taken up.

**`route-r1` / `route-r2` / `route-r3` — compose an optimization strategy.** A
route is a named composition over the stage skills, not an optimizer of its own.
It fixes which stages participate, in what order, where candidates come from, and
when benchmarking and verification happen.

| Route | How it optimizes |
|---|---|
| `route-r3` (default) | Lean-side `opt-*` pool, bench after every candidate, then verify each accepted champion |
| `route-r2` | Rust-first `rust-direct` candidates inside the Aeneas ceiling, bench-steered, then prove the extraction directly with no `opt_eq_spec` |
| `route-r1` | Lean-side `opt-*` pool to a fixpoint, one translation and one bench at the end |

A different composition is a distinct `route-<name>` skill, and its composition
stays fixed while it runs so the outcome is comparable.

**`verify-campaign` — pay the proof debt.** Takes a champion branch (or any
regenerated `Generated.lean`) to a module whose specs are proved, audited, and
ready to merge: re-extract, review the champion's Rust, re-state the specs, prove
each `sorry`, then the `hachi/lean/Check.lean` § 4 axiom audit. `main` only ever
receives a green module.

> There is real debt to point it at today, independent of any optimization:
> [`hachi/lean-wip/Scheme.lean`](hachi/lean-wip/Scheme.lean) is stated only.
> [`hachi/lean-wip/README.md`](hachi/lean-wip/README.md) says what promotion into
> the audited library requires — the procedure `RqBridge.lean` (now
> `hachi/lean/RqBridge.lean`, proved and audited) has already been through.

**`autonomy-harness` — run unattended.** Under `/loop`, each iteration picks the
next operation by headroom, runs a route end to end, proves the result, and
extends one commit plan. It halts loudly rather than degrading: on a failed proof,
on an approval gate, on anything needing a commit you have not made, when a
benchmark reads `unusable` twice running, or when the corpus is exhausted. New
operations never enter the corpus this way — that stays a deliberate `op-genesis`
decision.

### Two things every skill here obeys

**Agents stage; they never commit.** [`.claude/settings.json`](.claude/settings.json)
denies `git commit`, so this is enforced rather than trusted, and every loop run
ends by handing you an ordered commit plan.

**Only a benchmark accepts an optimization.** Not operation counts, not reasoning
about what ought to be faster. Measurements are compared only *within* one
criterion run, because a cross-run comparison inherits the difference in machine
conditions between two moments and on an ordinary desktop that dwarfs anything the
code does.

### The commands underneath

You rarely need these directly — the skills run them — but they are what the loop
runs:

```
make setup            install toolchains and dependencies (once, after cloning)
make build            check the Lean proofs; fails on any error or `sorry`
make test             run the Rust semantics tests
make extract          regenerate hachi/lean/Generated.lean from hachi/src/
make run-bench        time every operation against its frozen first translation
make bench-check      verify the frozen baseline against git, and bench coverage
make bench-stamp      re-derive the @genesis stamps after freezing a function
make bench-coverage   report which mirrored items are benched, without failing
make ledger-check     validate logs/ledger.jsonl rows and append-only history
make check-toolchain  verify the charon/aeneas pin in both directions
make clean            drop build output, keeping fetched dependencies
```

Variables: `BENCH=<regex>` to bench a subset, `JSON=<path>` for a machine-readable
report, `CANDIDATE=1` to also time the candidate slot (the A/B), and
`CHARON=`/`AENEAS=` to point `extract` at binaries kept elsewhere.

> Benchmarking needs the machine to itself. A build running alongside it — from
> this repo *or any other project* — corrupts the measurement, and another
> project's work is invisible to every check this repo can make. `make build` here
> takes hours on a cold Mathlib cache, so the two must never overlap.

### Logs

[`logs/ledger.jsonl`](logs/ledger.jsonl) is the append-only optimization and
verification ledger, and it is currently empty — see
[`logs/README.md`](logs/README.md) for the row kinds and why the ledger exists
alongside `NOTES.md`. `logs/aristotle-sessions.jsonl` is the append-only record of
asynchronous Aristotle proof sessions, created on first use.

---

## Part 2 · Every skill

Compositions and stages, in the order the pipeline runs them.

| Skill | Role | `agent_request` |
|---|---|---|
| `route-r1` · `route-r2` · `route-r3` | optimization compositions; R3 is the default | `target` |
| `autonomy-harness` | runs the loop unattended under `/loop` | `route` (optional) |
| `arklib-analyze` | targeted ArkLib definition → costed optimization brief | `target` |
| `op-genesis` | onboard a new operation; naive translation → frozen genesis | `target` |
| `lean-to-rust` | one targeted Lean definition → provably boring Rust | `target` |
| `lean-opt` | drives the Lean-side optimization stage; enforces the opt-contract | `target`, brief |
| `opt-algo-swap` · `opt-word-arith` · `opt-inplace-buffers` · `opt-tailrec-loops` · `opt-list-to-array` | the `opt-*` strategy pool | invoked by `lean-opt` |
| `rust-direct` | Rust-first candidates inside the Aeneas ceiling (route R2) | `target`, brief |
| `perf-loop` | the inner loop: candidates → bench → accept → ledger row | `target`, `candidate_stage` |
| `rust-bench` | criterion cases, the genesis freeze, and the adversarial case audit | — |
| `aeneas-extract` | runs and triages `make extract`; the supported-constructs ceiling | — |
| `aeneas-idiomatic-rust` | the idiom/axiom boundary: which Rust extracts well | — |
| `aeneas-spec-author` | states the `⦃·⦄` spec layer as typechecked `sorry` stubs | operation |
| `aeneas-equivalence-bridges` | representation relations, when the house pattern will not do | — |
| `verify-campaign` | the outer pass: scope debt → prove → audit → merge plan | `trigger`, `subject` |
| `prove-sorry` | proves one sorried theorem (or a scaffolded batch) | theorem |
| `aristotle-prove` · `aristotle-check` | asynchronous remote proof runs, and their harvest | files |
| `skill-lab` | route bake-offs and skill A/Bs; owns the ledger discipline | experiment |
| `skill-authoring` | how skills in this repo are written, vendored, and refreshed | — |

Reference material an agent consults mid-task, rather than a procedure it runs:
`aeneas-lean-core`, `aeneas-tactics-quickref`, `proof-patterns`,
`launching-proof-agents`, `verification-campaigns`, `aeneas-crypto-verification`,
`lean-lsp-mcp`. These seven are vendored verbatim from
[AeneasVerif/aeneas](https://github.com/AeneasVerif/aeneas)'s own documentation;
`skill-authoring` records the vendoring policy and how to refresh them.

`lean-lsp-mcp` additionally needs its MCP server configured before it is usable;
the `aristotle-*` pair needs an Aristotle API key, supplied per operation and
never stored.
