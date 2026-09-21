---
name: op-genesis
description: Onboarding a new ArkLib operation into the loop — creating the naive (trivial-grade) first translation in hachi/src and freezing it into the genesis baseline; chain closure, semantics tests, extraction pass, verbatim freeze + birth bench case, and the interleaved stage-only commit plan the stamp mechanics force; use when asked to translate a new ArkLib definition, create a naive translation, onboard an operation, or put a first translation into genesis
---

# Onboarding an Operation: Naive Translation → Genesis

For a targeted ArkLib definition that has no counterpart in `hachi/src`. This is
the stage *before* `perf-loop`, whose opening two lines are

    champion ← trivial translation of the ArkLib def
    baseline ← criterion(champion)

and this skill owns them. A human dialogue resolves the target; an upstream
route supplies it. Choosing a target is not this skill's job. An orchestrator in
the `perf-loop` mold: every stage procedure lives in its own skill —
`arklib-analyze` (the brief), `lean-to-rust` (the translation), `rust-bench`
(freeze, case, audit, runs), `aeneas-extract` (the extraction pass) — this file
holds only the ordering, the artifact contract each stage hands the next, and
the two things that exist only at the composition level: the
validate-before-freeze discipline and the stage-only commit choreography.

**Nothing is pending.** All five modules — `params`, `ring`, `linalg`, `gadget`,
`commit` — are translated, frozen, and byte-identical between `hachi/src` and
`benches/genesis/src`. So every invocation of this skill is a genuinely new
definition, not a backlog item. The obvious next candidate, the protocol layer,
is deliberately absent for a reason this skill cannot fix: its ArkLib
specification still has unfilled definitional parameters, so there is nothing to
translate trivially yet. Establish that a target *is* fully defined at the
pinned rev before starting stage 1.

## Invocation

**Human invocation:** start with the bare command `/op-genesis`; do not put the
definition on the command line. Ask, first and only as needed: **"Which ArkLib
definition should I onboard?"** Resolve the name in the pinned specification
(`hachi/.lake/packages/Arklib/`, the library being `ArkLib`), ask one follow-up
only when it remains ambiguous, confirm the resolved definition, then begin the
procedure. Do not ask for optimization choices: this skill always creates the
deliberately naive baseline.

**Agent invocation:** bypass that dialogue by passing this complete named
request to the skill:

```yaml
agent_request:
  target: ArkLib.<fully-qualified-definition>
```

Validate that `target` resolves before work starts. If the packet is missing or
incomplete, return the missing field to the invoking agent; do not turn an
agent-to-agent call into a question for the human.

## The one rule: everything is validated before the freeze, because after it nothing can be repaired

`benches/genesis/` is write-once — its `lib.rs` contract reads *"Nothing here is
ever edited. Not to fix a lint, not to fix a typo, not to follow a rename in
`hachi`"*, and *"Append only"*. Two distinct mistakes become permanent at the
moment of the copy:

* **Freezing a semantics bug.** The `case!` digest oracle compares `now` against
  `genesis`, and at birth they share any bug — no signal. The bug surfaces only
  when the *fix* lands in `hachi/src`: from then on the digest assert panics the
  whole bench file, and the only way out is editing genesis. So the
  independently-written semantics tests (the house pattern in
  `hachi/tests/*_semantics.rs`: references written deliberately *unlike* the
  crate — plain convolution instead of the crate's fold, `u128` accumulation so
  a `u64` overflow mismatches instead of being reproduced, the spec's `digit c
  e` spelled out rather than a running quotient) are the *only* oracle the
  freeze gets. They go green before the copy, always.
* **Freezing anything other than the spec's trivial translation.** Genesis is
  the zero point of the fitness function; freeze an improved version and its
  gains read zero forever, undetectably (`rust-bench` §1). The thing frozen is
  the trivial-grade translation of the ArkLib definition itself — never an
  `Opt.lean` variant, never a body improved while translating. `hachi/src` is
  full of deliberately naive bodies for exactly this reason: `gadget::digit_at`
  divides `e` times so each output digit is literally the spec's `digit c e`,
  `base_pow` recomputes `bᵉ` per slot so every term is syntactically `base ^ e`,
  and `Rq::equals`/`is_zero` run branchless to the end because that is the shape
  the decision-procedure proof mirrors. Ideas that arrive during translation are
  filed for `perf-loop`, not acted on (`lean-to-rust`'s rule, applied at the
  composition level).

  **The one narrow exception, and the test for it.** The rule exists to keep
  gains *measurable*. Where a naive form cannot be measured at all, freezing it
  protects nothing and costs three things. Take the exception only when all
  three hold, and record it:

  1. the naive form cannot run at any width that still resembles the operation,
     so its bench row would be excluded as infeasible — not merely slow;
  2. therefore `case!`'s digest oracle cannot be computed on it either, so no
     bench case can be *built*, not just none registered;
  3. and being a mirrored item it would carry spec and proof debt for a body
     that never executes.

  Then freeze the optimized form, say so in `NOTES.md`, and **put the naive form
  in the tests at a toy width instead** — that is what recovers the independent
  oracle the freeze would otherwise lose, and it is not optional.

  **Travelled twice.** First for Stage 3 target 5 (the sumcheck): `(2b+1)^{m₀}` monomials is `3.9·10^7`
  already at `m₀ = 5` and `1.4·10^12` at `m₀ = 8` with `b = 16`, so only
  `b = 3, m₀ = 5` runs — a width at which the operation is no longer itself.
  What follows for readers of the ledger: a target-5 `vs genesis` figure measures
  distance from the *dense* form, never from the specification's shape.

  Stage 5's `R^lin` adapter (2026-09-09): `rlinStmt`'s c4 block is written
  `(matMul G2m J).transpose *ᵥ a`, and that product materializes at
  `1024 × 40960` `Rq` = **320 GiB** where the answer is a 320 MiB vector — a
  1024× overhead, one factor per row of `G` the contraction discards. A
  *memory* wall, so its removal condition is **not** a faster `ring::mul`.
  Frozen form: the associativity reshape `Jᵀ(Gᵀa)`, an identity rather than an
  algorithm change.

  The two instances differ in one way worth carrying. Target 5's naive form
  only runs at a width where the operation stops being itself, so its toy-width
  oracle tests something else and the gap is stated rather than closed. The
  `R^lin` naive form is dimension-parametric and runs outright at
  `2^m = 4, md = 2, zd = 2`, so its oracle is faithful — which makes the
  "arities travel as arguments" convention **load-bearing rather than
  stylistic**: hard-wiring the `params` constants into the reshaped body would
  delete the only oracle the freeze gets.

If a defect slips past both and is caught at birth — before any run has been
reported against the item — the honest repair is an immediate re-freeze: replace
the frozen text with the fixed first translation, re-stamp against the fixing
commit, and say so in the commit and in `NOTES.md`. That rewrites no measurement
history because there is none yet.

**And in this repository there is none yet for anything.** `NOTES.md §
"Benchmark numbers from this session are not measurement-grade"` and the section
that supersedes it both label every number taken so far as sizing information
rather than a baseline, and `logs/ledger.jsonl` starts empty. So the carve-out
is currently open for *every* frozen item in `benches/genesis/`, not only for
whatever this skill freezes next. It closes per item the moment a number is
published against that item, and it closes silently — which is why the rule sits
at the top of this file rather than being rediscovered later.

## The composition

1. **Brief** — `arklib-analyze` on the target. Its definition chain is the work
   list: every def in the chain missing from `hachi/src` is onboarded too,
   dependencies before dependents (one def = one fn, so a dependent's body calls
   helpers that must already exist). Defs already in `hachi/src` are reused as
   they are — calling an already-optimized champion helper is fine; that gain
   being contained in the new op's `vs genesis` is the defined meaning of that
   column (`perf-loop`). ArkLib is generic in `(q, α, b, digits)` and `hachi` is
   concrete, so the brief must also name the instantiation: which fixed
   `params.rs` values the generic statement is being pinned at. The brief's
   opt-* section is filed for later, per the one rule. Batch the whole chain
   into one pass: one commit plan, one birth run — and a run wants the machine
   to itself.
2. **Translate** — `lean-to-rust` per def, bottom-up: the enumerated moves, the
   ``Mirrors `<ArkLib name>` `` line naming the spec identifier at the pinned
   rev, house shell. The `Mirrors` line is not documentation garnish: it is the
   input `harness.py coverage` takes its work list from, so an item without one
   is an item the coverage gate cannot see. Collect the proof debt as you go —
   next item.
3. **Oracle** — extend `hachi/tests/<module>_semantics.rs` in the house pattern
   (each test states the ArkLib definition's mathematical property; the
   reference is written deliberately *unlike* the crate). `cargo test` green (66
   tests pass today, so the count only goes up), `cargo clippy --all-targets`
   clean under pedantic — before anything is frozen.
4. **Extraction pass** — `aeneas-extract`: deterministic, zero axioms, loop
   shapes, name skim. `make extract` must keep passing `--include 'cpoly::_'`,
   without which every `cpoly` item lands in `Generated.lean` as an `axiom`;
   `Check.lean` § 2 asserts the transparent form so the flag cannot be dropped
   silently, and § 2b asserts that each module arrived with the shapes the
   proofs need — a new op in an existing module usually means extending § 2b.
   Finish with the proof re-check (`make build`), since the additive
   regeneration of `Generated.lean` must not move any existing `_spec`; budget
   hours on a cold Mathlib cache, and serialize it against any bench run. This
   stage runs *before* the freeze because a ceiling failure reshapes the
   translation within the allowed moves — i.e. changes the text that would have
   been frozen. An unsupported construct that no reshape avoids is a
   stop-and-surface: the op cannot enter the loop yet.
   * Where the new obligations go: a proved coefficient-level `_spec` belongs in
     `hachi/lean/` (and a *new file* there must be added to `roots` in
     `hachi/lakefile.lean`, which has no library-named module to reach the rest
     through). Anything **not yet proved** goes to `hachi/lean-wip/` —
     `RqBridge.lean` for a ring-level lift to ArkLib's `Rq Φ`, `Scheme.lean` for
     `linalg`/`gadget`/`commit`. That directory is deliberately not a Lake root,
     so `make build`'s "no errors, no `sorry`" cannot be diluted by it. Staging
     an unproved obligation under `lean/` instead fails `make build` outright
     and puts `sorryAx` into `Check.lean` § 4's axiom audit, which must stay at
     exactly the three Lean kernel axioms.
5. **Freeze, case, slot** — `rust-bench` §1–§2 minus its git commands: copy the
   new items verbatim (copy, never retype) into
   `benches/genesis/src/<module>.rs`; a case with `@covers` per public op, a
   by-name exclusion with a checkable reason otherwise. The exclusion bar is "a
   criterion run would measure the harness, not the item": the `params.rs`
   constants are the archetype — which is why there is no `params` bench target
   at all — and `Rq::len` (one `Vec::len`) and `Rq::coeff` (one index) are the
   O(1)-by-inspection class. Then sync the candidate slot: byte-copy the changed
   `hachi/src` files over `benches/candidate/src/` — `check-candidate` pins
   slot ≡ src, so a new item breaks `make bench-check` until the copy lands.
6. **The interleaved commit plan** — next section; ends with `make bench-check`
   green.
7. **Birth run + audit** — `rust-bench` §3–§5 unchanged: the filtered shake-out
   run, the adversarial case audit, then one full `make run-bench`. **At birth
   the new op's rows must read noise**: `now` and `genesis` are byte-identical
   for it, so any significant delta is a defect in the freeze or the case (an
   adapter doing work, a degenerate input, a wrong copy), never a result. That
   the shape is achievable is upstream's evidence, not ours — AeneasCompPoly
   benched a from-scratch re-derivation digest-identical at +0.7%, inside its
   threshold. Here, "reads noise" means "inside the *printed* threshold", and
   read `NOTES.md § "The first benchmark run, and what it says about the
   harness"` before drawing any conclusion from a birth run: on the host that
   produced this repository's only completed run, byte-identical code came out
   10–59% apart and the `_control` cases sat at or above the harness's own 10%
   usability veto. On a host like that a birth run establishes that the case
   compiles, digests and scales — not that the freeze is faithful to within a
   few percent. Audit findings that change the *case* are normal post-commit
   edits; findings that change the *item* take the re-freeze carve-out above.
8. **Handoff** — the naive translation is the champion, genesis is its baseline,
   the brief already exists: the op is loop-eligible and `perf-loop` takes it
   from here. No ledger row is written — the ledger records candidate verdicts,
   and an onboarding's provenance is the `@genesis <sha> <date>` stamp itself.

## The commit choreography (stage-only)

Three enforced mechanics fix the shape; none can be worked around:

* `stamp-genesis` refuses text that is in no commit ("no commit contains this
  text verbatim") and refuses a match that exists only in the dirty working tree
  at HEAD (`harness.py`) — so a hand-typed stamp is not a stamp, and
  `check-genesis` verifies each attribute against git rather than trusting it;
* `check-genesis` fails while any live item lacks a frozen *and stamped*
  counterpart;
* `make run-bench` hard-gates on `check-genesis` — statistics cannot rescue a
  corrupted baseline — so there is no pre-commit bench number, and stages 6–7
  cannot be reordered around it.

Agent sessions in this repository stage and never commit; the user commits. So
the plan interleaves:

1. *(agent)* stage everything from stages 2–5: `hachi/src`, the semantics tests,
   the bench case and any `exclusions.toml` line, the **unstamped** genesis
   copy, the slot sync, and the Lean obligations (`lean/` if proved, `lean-wip/`
   if not, plus the `roots` edit if a new file landed under `lean/`).
2. *(user)* commit 1 — all of it, one commit: the genesis `lib.rs` contract
   wants the item added to `hachi/src` and to genesis in the same commit, and
   the stamp will name this sha.
3. *(either)* `make bench-stamp` — derives `// @genesis <sha> <date>` from
   commit 1; stage the annotations.
4. *(user)* commit 2 — the stamp lines alone. Never `--amend` commit 1 instead:
   the stamp stores commit 1's sha, and an amend changes it, orphaning every
   annotation just derived.
5. `make bench-check` green → stage 7 can run. If the session ends at step 1,
   steps 2–5 and stage 7 are the written plan's tail, in this order.

## Failure modes with teeth

* **Freezing an already-optimized body.** The one failure invisible from the
  numbers forever after — `rust-bench` §1 owns the late-recovery procedure
  (`git show` the *original* text); at the composition level the trap is
  starting stage 2 from an `Opt<Module>.lean` part or "improving while
  translating".
* **A shared semantics bug at birth.** The digest oracle is parity, not truth:
  it catches a stale or divergent *copy* (frozen ≠ src → panic on the first
  run), but a bug present in both variants sails through and detonates under the
  future fix. The stage-3 tests are the only birth oracle — which is why they
  are written against independent references, never against the code under test.
* **Forgetting the slot sync.** `make bench-check` fails on `check-candidate`
  the moment `hachi/src` gains an item the slot lacks. Byte-copy, same change,
  every time.
* **A new module, not just a new item.** `MODULES` is a fixed tuple in
  `harness.py` (`params`, `ring`, `linalg`, `gadget`, `commit`, `evalsplit`);
  a further module means extending it, both slots' `lib.rs`, a declared
  `[[bench]]` **and a declared `[[test]]`** in `hachi/Cargo.toml`
  (`autobenches = false` *and* `autotests = false`: an undeclared bench file is
  silent, and an undeclared test file silently never runs — the second one is
  the trap, because `cargo test` still exits green). Note the asymmetry that
  makes this easy to get wrong: `params.rs` is frozen and checked yet has no
  bench file. Traveled once, for `evalsplit` (the sixth module): the slot
  file-count and null-slot checks all derive from `MODULES`, so the tuple edit
  was the only `harness.py` change; the shared corpus in `benches/support/` is
  module-agnostic and needed nothing. Two more lessons from that pass: the
  ``Mirrors`` scanner's regex is `Mirrors (ArkLib's)? \`name\`` — a
  parenthetical between "Mirrors" and the backticks (e.g. for a CompPoly-owned
  name) makes the marker *invisible* to the coverage gate rather than failing
  it, so check the `coverage` count moved by exactly the number of new markers;
  and new items appended to an existing frozen genesis module go in verbatim
  (extract the block programmatically from `hachi/src`, never retype), leaving
  the module's stale frozen header comments alone.
* **Working around the run-bench gate.** A "quick number" from `cargo bench`
  before the commits exist has no genesis variant, no control, no threshold — it
  is exactly the un-validated absolute time `rust-bench` forbids reasoning from.
  The gate order is the design; wait for the commits.
* **Onboarding against a specification that is not finished.** ArkLib's protocol
  layer still carries unfilled definitional parameters, and a "trivial
  translation" of an underdetermined definition is a guess frozen into an
  append-only baseline. Stop and surface instead.

## Invariants to keep green

* What genesis receives is the trivial translation of the *spec* definition,
  tests-green and extraction-clean before the copy, byte-identical to
  `hachi/src` at commit 1.
* Chain closure: every def the target depends on exists in `hachi/src` (reused
  or onboarded) before the target itself, and the brief names the fixed
  `params.rs` values the generic ArkLib statement is instantiated at.
* Every new item carries its ``Mirrors `<ArkLib name>` `` line and is benched or
  excluded by name with a checkable reason; `make bench-check` green at the end
  of the choreography.
* The birth run's rows for the new op read noise *against the printed
  threshold*, and the case survived the `rust-bench` §4 audit before any number
  from it is believed.
* No `sorry` reaches anything `Check.lean` sees: unproved obligations live in
  `hachi/lean-wip/`, and `Check.lean` § 4 still prints exactly the three Lean
  kernel axioms.
* A new file under `hachi/lean/` is added to `roots` in `hachi/lakefile.lean`.
* The session ends with staged changes and the interleaved plan — never a
  commit.
* No ledger row for an onboarding; the `@genesis` stamp is the provenance.
