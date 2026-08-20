---
name: verify-campaign
description: "Agent-only outer verification stage for a champion or a regenerated extraction — scope the proof debt on the champion branch, champion idiomatic review, re-extraction and determinism check, spec repair/authoring stubs, prove-sorry runs per sorry, Check.lean audit, metered effort into a campaign ledger row, merge plan; use from a parent workflow when an accepted optimization awaits its equivalence proofs (K=1: every accepted champion), when Generated.lean regenerated for any reason (Rust edits, aeneas/charon bump) and specs broke, or when a module needs end-to-end verification"
---

# The Outer Verification Pass

Drives one **campaign**: from a champion branch (or any regenerated
`Generated.lean`) to a module whose specs are proved, audited, and ready to
merge. Stages, each owned by its own skill: the `aeneas-idiomatic-rust`
champion review → `aeneas-extract` → `aeneas-spec-author` (with
`aeneas-equivalence-bridges` on demand) → `prove-sorry` per sorry → the
`Check.lean` audit → this skill's ledger row and merge plan. The upstream
`verification-campaigns` skill is the playbook for planning and for mass
breakage (>~5 files red, from-scratch primitives); this skill is the
project-local orchestration around it. The inner optimization loop
(`perf-loop`) never proves; this pass never benches.

## Agent input

Invoke this stage only from another workflow with:

```yaml
agent_request:
  trigger: champion-accept | regeneration | from-scratch
  subject: <champion branch | generated-model path | module>
```

Validate that the subject matches the trigger. Send missing or invalid fields
back to the invoking agent. The separate approval gates for theorem weakening
and large campaign structure still apply.

## The one rule: main only ever receives a green module

A champion's Rust swap, its regenerated `Generated.lean`, and the specs it
breaks travel together on a `champion/<op>` branch (prepared by
`perf-loop`), and that branch merges only when `make build` is green, every
`_spec` under `hachi/lean/` is sorry-free, and the `Check.lean` audit passes.
No intermediate state — sorried stubs, re-pinned-but-unproved aliases, a
"temporarily red" build — is ever staged for main itself. The debt is paid
where it was incurred. Trigger cadence is **K=1**: one campaign per accepted
champion, before the next optimization target is taken up; the ledger's effort
numbers are what may later relax K, not convenience in the moment.

There is exactly one place unproved Lean may be staged: `hachi/lean-wip/`,
which is deliberately **not** a Lake root, so `make build` never looks at it
and nothing there dilutes the "no errors, no `sorry`" claim. A campaign that
cannot close ends with a *typechecked, unproved* statement in `lean-wip/` and a
`partial`/`blocked` ledger row — never with a sorried stub under `lean/`. The
promotion procedure out of `lean-wip/` (finish the proofs, move the file, add
the module to `roots` in `hachi/lakefile.lean`, `import` it from `Check.lean`,
add a `#print axioms` line per headline spec, re-run `make build`) is in
`hachi/lean-wip/README.md` and is part of closing a campaign that proved one of
those files.

## Where the debt currently sits

Untraveled repository: no campaign has run here, and `logs/ledger.jsonl` is
empty. The outstanding proof debt a campaign can be pointed at today is exactly
two files, and both are real work rather than scaffolding:

* `hachi/lean-wip/RqBridge.lean` — the lift of the proved coefficient layer to
  ArkLib's `Rq Φ`. **Proved** (26 theorems, three kernel axioms) but
  **unchecked**: promoting it per the procedure above is the shortest complete
  campaign available, and until it happens a change to `hachi/lean/Ring.lean`
  can break it silently.
* `hachi/lean-wip/Scheme.lean` — the `linalg` / `gadget` / `commit`
  obligations, **stated only** (23 `sorry`s), typechecked against the pinned
  ArkLib. `gadget_mul_spec` and `verify_weak_spec` are the two worth reading
  before proving (`lean-wip/README.md` says why: the first turns on the spec's
  own `gadgetMul_apply`, the second is an *equality* of decisions, so a
  reject-everything verifier cannot satisfy it).

Proved and audited already: `hachi/lean/Field.lean` and `hachi/lean/Ring.lean`
— nineteen headline specs, axioms exactly the three kernel ones.

## The procedure

1. **Scope the debt** (in the champion worktree/branch). Re-run extraction
   per `aeneas-extract` — the determinism check is mandatory before any
   spec work, or the whole prove stage can be spent against a flaky
   snapshot, and `--include 'cpoly::_'` must be on both runs or the field
   layer arrives as axioms. Diff `Generated.lean`; list every alias, `_spec`,
   and `Check.lean` entry affected, and classify each: *intact* / *re-pin
   only* (names re-mangled, semantics unchanged) / *stale loops* (opt
   structure changed the `*_loop` functions) / *new function*. Mass breakage
   or a from-scratch primitive → plan the file/folder structure with the
   upstream `verification-campaigns` skill before touching anything.
2. **Champion review.** One reviewer agent applies the
   `aeneas-idiomatic-rust` verdict tables to the champion's Rust, evidence
   required (candidates got only the mechanical clippy gate in the inner
   loop; the champion gets the real review). Findings that change the Rust
   send the campaign back to step 1 — the extraction must match what merges.
3. **Re-spec** per `aeneas-spec-author`: headline statements carried over
   verbatim, aliases re-derived and re-pinned, new loop specs shaped after
   the opt definition with `Foo.opt_eq_spec` splicing onto the unchanged
   right-hand side, everything delivered as typechecked `sorry` stubs. A
   representation mismatch that resists the house pattern goes through
   `aeneas-equivalence-bridges` before any relation is invented. Two local
   mechanics: the coefficient level and the `Rq Φ` level are separate files on
   purpose (`lean/Ring.lean` proves the loop invariants and totality against a
   small import surface; `lean-wip/RqBridge.lean` does the `ofFinCoeff_coeff`
   bookkeeping on top), so a spec belongs at the level where its work is; and
   the `Opt` definitions of a Lean-side champion live in `hachi/lean/Opt.lean`,
   which **does not exist yet** — the first `lean-opt` run creates it *and*
   adds `Opt` to `roots` in `hachi/lakefile.lean`. Lake builds a module only
   when a root is a prefix of its name, so an unlisted file is silently not
   built and its `sorry`s are silently not reported.
4. **Prove.** One `prove-sorry` run per sorried theorem — or one run over a
   scaffolded batch when several sorries share a decomposition (the loop
   spec + headline of one operation is the natural batch; `NOTES.md` § "Two
   things that made the proofs go through" records that once `add` was
   through, `sub`, `neg` and `scalar_mul` were mechanical, so batch them).
   Its approval gate, agent rules, and axiom hygiene apply unchanged. Machine
   discipline: Lean building and criterion benching never overlap, so a
   campaign never runs concurrently with an inner-loop bench session.
5. **Audit and close.** Full `make build` — which also fails the run on any
   `sorry` under `lean/` or any `sorryAx` in the axiom prints, so it is the
   gate and not just a compile. `Check.lean` **§ 4** prints must show axioms
   exactly `[propext, Classical.choice, Quot.sound]` for every headline spec;
   grep the touched files for
   `sorry|native_decide|axiom|implemented_by|unsafe|maxHeartbeats`; new Check
   entries for anything the campaign introduced (§ 1 for a parameter, § 2/2b
   for a model-shape assumption, § 4 for a new headline spec).
6. **Ledger row, then stage — never commit.** Append the campaign row
   (below) to the **worktree's** `logs/ledger.jsonl` so it rides the champion
   branch and enters history in the same commit as the proofs it describes
   (the entry discipline is `skill-lab`'s; `make ledger-check` gates the
   plan). Stage the branch state, and end by handing the user an ordered
   plan: the champion-branch commits, the merge to main, and any post-merge
   step the landing owes (e.g. `make bench-stamp` when the merge freezes
   new genesis items, followed by a stamps-only commit — never an `--amend`
   of the content commit, since the stamp stores its sha).

## The wall-clock shape of a campaign here

`make build` on a cold Mathlib cache takes **hours** — ArkLib and Mathlib
compile from source whenever `lake exe cache get` could not run (the cache has
no GitHub mirror; `make setup` says so and continues). Consequences that change
how a campaign is run, not just how long it takes:

* Budget the audit stage in hours, and do a full `make build` *once* per
  campaign at step 5. Iterate with `lake env lean lean/<File>.lean` on the file
  being worked, and with `lake env lean lean-wip/<File>.lean` plus the
  `LEAN_PATH` trick in `lean-wip/README.md` § "Working here" for files that
  import each other there.
* One `lake build` at a time, repo-wide. A second one does not just contend
  for cores, it makes the first slower than the sum of both.
* A campaign that has to re-extract (step 2 sent it back to step 1) pays the
  build again. Get the champion review done before the spec work, not after.

## Effort metering — the campaign's second product

The P3 questions (does `opt_eq_spec` keep proofs at trivial-translation
cost? should K stay 1? where does the trivial-grade dial sit?) are decided
by these numbers, so a campaign that forgets to meter has produced half its
value. This repository has no rows yet, so the first campaigns are the whole
evidence base. Meter **as you go** — post-hoc estimates are fiction:

* `tokens` — output tokens of the prover/verifier fleets (the Workflow
  tool's `budget.spent()` read per phase) plus a stated estimate for
  main-loop work;
* `wall_min` — wall-clock minutes per phase: scope, review, spec, prove,
  audit (the audit phase is where a cold Mathlib cache shows up);
* `retries` — prover attempts beyond the first per lemma, plus repair-agent
  escalations;
* `interventions` — approval-gate hits and any other point a human had to
  unblock the run.

The row goes in `logs/ledger.jsonl` (file conventions — append-only, one line
per event, `pins.repo` honesty — and the full `kind` table are owned by the
`skill-lab` skill; campaign rows are distinguished by `"kind": "campaign"`,
rows without a `kind` are the inner loop's). Shape only; the file is empty
until a campaign writes to it:

```json
{"kind": "campaign", "ts": "<RFC3339 local time>",
 "op": "ring/mul", "champion": "<opt name — what changed>",
 "trigger": "champion-accept",
 "specs": {"carried": 0, "repinned": 0, "new_loops": 0, "new": 0},
 "effort": {"tokens": 0, "wall_min": {"scope": 0, "review": 0, "spec": 0,
            "prove": 0, "audit": 0}, "retries": 0, "interventions": 0},
 "result": "verified",
 "axioms": "clean",
 "pins": {"repo": "<sha>", "dirty": true,
          "arklib": "e92dc315f453db88dd7351c88e889caf0e6bf269",
          "aeneas": "nightly-2026.07.26-3a8586f"},
 "notes": "…"}
```

`trigger` ∈ champion-accept · regeneration · from-scratch. `result` ∈
verified · partial · blocked — partial and blocked rows are appended too,
with the blocking lemma named in `notes`; an abandoned campaign without a
row is invisible to the K decision.

## Failure modes with teeth

* **Treating re-mangled names as broken proofs.** A regenerated extraction
  re-mangles names whenever an impl or helper shape moves; the failure is at
  the alias layer, not the semantics. Re-pin first (step 1's classification),
  or hours of proving are spent on what one `abbrev` edit fixes.
* **A module Lake never built.** Adding a file under `hachi/lean/` without
  adding it to `roots` (and importing it from `Check.lean`) produces a green
  build that checked nothing — the same trap `lean-wip/` exploits on purpose.
  Confirm the new module appears in the `make build` log.
* **Merging early.** A champion branch merged with sorried specs makes
  `make build` red for every consumer of main and turns the
  build-visible-`sorry` design into noise. Green first, merge second.
* **Benching during a campaign.** Worktrees isolate files, not the machine:
  a `lake build` landing inside someone's criterion session corrupts the
  measurements silently (the inner loop's serial rule is loop-wide, and
  campaigns count). `Makefile` § `run-bench` says the same thing from the
  other side.
* **Spec work on an unchecked extraction.** Skipping the determinism check
  and authoring against a snapshot that differs run-to-run wastes the
  entire prove stage — the check is two extractions, the prove stage is the
  expensive fleet. Dropping `--include 'cpoly::_'` is the sharper version of
  the same mistake: the specs then quantify over an uninterpreted field and
  say nothing, which is what `Check.lean` § 2 exists to catch.
* **A vacuous statement instead of a proved one.** `autoImplicit` has bitten
  this development twice: a missing `open` turns `q` into an auto-bound
  variable and the theorem becomes a claim about every natural number. Every
  file sets `autoImplicit false`; a new file must too.
* **Reconstructed effort numbers.** Numbers written at close-out from
  memory undercount retries and interventions — exactly the fields the K
  decision needs. Keep the tally in the campaign's scratchpad from step 1.

## Invariants to keep green

* Main always builds green: no `sorry` under `lean/`, no broken alias pin,
  axiom closure exactly `[propext, Classical.choice, Quot.sound]` on every
  headline spec in `Check.lean` § 4.
* Unproved Lean lives in `hachi/lean-wip/` and nowhere else; promoting a file
  out of it follows all five steps of `lean-wip/README.md`.
* Every campaign — verified, partial, or blocked — has exactly one ledger
  row with its effort block filled from a running tally.
* Stage, never commit: a campaign ends with staged changes and an ordered
  commit-and-merge plan for the user.
* A champion branch merges only after step 5 passes in full, and the merge
  plan names any post-merge obligation.
* K=1 stands until a ledger-backed decision changes it — and that decision
  updates this skill in the same session.
