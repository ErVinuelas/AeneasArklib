---
name: skill-lab
description: Running measured experiments over the loop's skills — the route bake-off (supplied or custom route-skill arms on the same target, metered not capped), skill-version A/Bs (session-scoped variants, exactly one skill bumped per experiment), ownership of logs/ledger.jsonl and its kind-discriminated row schemas, and folding each verdict back into the responsible skill; use when comparing routes or skill versions, when appending bakeoff or ab rows, or when deciding whether ledger variance justifies an A/B
---

# The Skill Lab

The experiment layer over the loop: routes and skill versions are compared
the way candidates are — measured, within-run, with the verdict folded back
into exactly one place. Read this **before** running a bake-off arm,
starting an A/B, or writing any ledger row that is not a candidate or
campaign row. Variant mechanics (session-scoped `-v2` directories, git-only
versioning) are `skill-authoring`'s; this file owns *when* an experiment
runs and *how its result is recorded*.

## Invocation

**Human invocation:** start with `/skill-lab` alone. Ask one question at a
time: first **“Do you want a route bake-off or a skill A/B?”** For a bake-off,
ask for the target and route arms. For an A/B, ask for the skill and the exact
sentence or rule under test; do not start from a vague suspicion. Confirm the
complete experiment before creating a variant or a worktree.

**Agent invocation:** bypass the dialogue with one complete named request:

```yaml
agent_request:
  kind: bakeoff
  target: ArkLib.<fully-qualified-definition>
  arms: [route-r3, route-my-strategy]
```

```yaml
agent_request:
  kind: ab
  skill: <skill name>
  hypothesis: <exact sentence or rule under test>
  input: <fixed target or other fixed input>
```

Validate the form and return any missing field to the invoking agent instead
of asking the human.

## The one rule: an experiment varies exactly one thing

One route per arm on the same target; one skill per A/B, everything else at
HEAD. The ledger must attribute every win or loss to exactly one skill —
that is why strategies are born as their own skills — and an experiment
that varies two things produces a row that blames neither. Corollary for
routes: route skills contain no procedure, so an arm's outcome is
attributable to the composition itself; a procedure smuggled into a route
skill invalidates the arm.

## The ledger — `logs/ledger.jsonl`, owned here

File conventions: append-only at `logs/ledger.jsonl`, one JSON object per line
per event, `pins.repo` = the short base commit the work was built on (with
`dirty: true` when measured against uncommitted state). The numbers in a row
are one run's within-run claims — no tooling may subtract two rows' numbers.
AeneasCompPoly measured 75–373% drift on frozen code when cross-run comparison
was tried there; the reason the rule is kept here is stated in
`hachi/benches/genesis/src/lib.rs`, which is where the append-only baseline's
contract lives.

**What this repository's own harness can currently resolve.** NOTES.md § "The
first benchmark run" measured byte-identical crates reading up to 59% apart
*within one session* on the host it ran on, with each group's `_control` case
putting a 10–15% floor under its readings. Until that is fixed — CPU pinning,
many more samples, or interleaved rather than blocked repetitions — a "vs
genesis" or "cand vs now" number is evidence only for effects well above 50%.
An experiment run on such a host records the number *and* says so in `notes`;
a delta inside the floor is written as unresolved, never as a small win.

How rows enter history — the discipline that makes every row's provenance
resolvable and the no-cross-run rule mechanical:

* **A row rides the work it describes.** Append the row to the
  `logs/ledger.jsonl` *of the worktree the work lives in* and stage them
  together, so they enter history in the same commit and the row's introducing
  commit (git blame) contains the state it pins. Sessions here stage and the
  user commits, so the pairing is the commit plan's job to state.
  `pins.repo` alone cannot do this — a dirty pin names a base, not the state.
  Two shapes have no landing work by design and are the row's own record:
  rejected candidates and bench-only references (the `slot_sha` fingerprints
  their discarded diff). A loop run that lands no champion ends with a
  ledger-only commit in its plan.
* **Measurement rows name their criterion session.** Every candidate row
  carrying a `rows` array has a `run`, and **you never invent it**: `make
  run-bench` prints it (`run  20260820T1432+0200-721f2a18`) and `JSON=` puts it
  in the report as `"run"`. Copy that string into every row taken from that
  report. An invented id cites a run nobody can identify, which is worse than
  citing nothing.

  Its shape is `<YYYYMMDD>T<HHMM><±ZZZZ>-<8 hex>` (`harness.py § run_id`). The
  timestamp is when the *measuring* began — `make run-bench` stamps the clock
  before `cargo bench` — not when the report was printed. The digest is over what
  identifies the run rather than over its numbers: the host fingerprint (hostname,
  arch, CPU, core count, read from `/proc/cpuinfo` here), the `rustc` version, the
  source commit, and the exact set of case/variant pairs measured. So
  re-reporting unchanged criterion state reproduces the id instead of minting a
  second identity for one measurement — which matters, because a report-only
  rerun through a fixed harness is a thing that happens. Numbers from rows with
  different `run` are never compared, and that is now a rule tooling can refuse
  on rather than a sentence in `notes` hoping to be read.
* **Rows cite by `run`/`ts`, never by position.** The file merges `union`
  (`.gitattributes`), so concurrent branches append without conflict and
  committed order may interleave — "row 3" and "the row above" are
  meaningless after the first union merge.
* **`notes` hold durable facts and caveats, a few sentences (≤1200 chars).**
  The skill cleanliness rules apply verbatim: present tense, no session
  narrative, no shorthand a later reader cannot resolve. Analysis lives in the
  responsible skill or in NOTES.md; the note points there.
* **`make ledger-check` is the gate** — per-kind schema, `run` format, the
  `<module>/<op>` shape of `op`, the notes bounds, the positional-citation ban,
  and append-only against the last committed state (set-containment, since
  union merges reorder). It runs before any commit plan that touches the
  ledger. There is no exemption window: this ledger starts empty, so every row
  in it was written under this discipline and every row is checked.

Rows are discriminated by `kind`; any tooling over the ledger filters on it
first:

| `kind`      | meaning                        | schema lives in  |
|-------------|--------------------------------|------------------|
| *(absent)*  | inner-loop candidate verdict   | `perf-loop`      |
| `campaign`  | one verification campaign      | `verify-campaign`|
| `bakeoff`   | one completed bake-off arm     | here             |
| `ab`        | one settled skill A/B          | here             |

## The route bake-off

Arms are named route skills — the supplied `route-r1` / `route-r2` /
`route-r3` designs or a user-defined route — run on the **same target
definition**, each from the same genesis baseline, each in its own worktree,
each blind to the sibling arms' artifacts (an arm that reads another arm's
candidate notes is contaminated — its row says so or is not written).
Discipline:

* **Metered, not capped.** Every arm runs to its natural finish — no
  significant win left, proofs done. Effort is measured per the
  `verify-campaign` effort block (tokens, wall-clock per phase, retries,
  interventions), extended over the arm's perf stages too. Cost differences
  between arms *are* the result; a cap would amputate them.
* **Machine serialization is bake-off-wide.** One criterion session or
  `lake build` on the machine at a time across *all* arms — arms interleave
  by stage, never on the machine (`perf-loop`'s serial rule, promoted a
  level). Budget for it: `make build` here takes hours on a cold Mathlib
  cache, so a worktree that has not had `hachi/.lake` transplanted into it
  blocks every other arm while it rebuilds (`lean-opt` owns that mechanic).
* **The answer is a pair, never a scalar.** Per arm: the verified champion's
  recentered bench delta at the largest case measured, alongside the total
  effort block. No formula collapses speed and proof cost into one number —
  that trade-off is the user's to read.

One row per completed arm:

```json
{"kind": "bakeoff", "ts": "…",
 "op": "ring/mul", "arm": "route-r3",
 "target": "ArkLib.Lattices.CyclotomicModulus.Rq — the Mul instance (Rq.lean:110)",
 "champion": "Rq.mul.opt — karatsuba split of the negacyclic convolution",
 "bench": {"case": "ring/mul", "vs_genesis": -0.49,
           "claim_provenance": "accept run 20260820T1130+0200-<machine id>"},
 "effort": {"tokens": 0,
            "wall_min": {"perf": 0, "scope": 0, "review": 0, "spec": 0,
                         "prove": 0, "audit": 0},
            "retries": 0, "interventions": 0},
 "result": "verified",
 "reference": {"impl": "bench-only unrestricted Rust", "vs_genesis": null,
               "claim_provenance": "…"},
 "pins": {"repo": "…", "dirty": false, "arklib": "…", "aeneas": "…",
          "cpoly": "…", "bench_toolchain": "nightly-2026-06-01"},
 "notes": "…"}
```

`result` ∈ verified · partial · abandoned — an arm that dies (extraction
wall, unprovable champion) still gets its row; a missing arm is invisible
to the exit question. `effort` honesty: when an arm reuses work whose
effort predates metering, the row says so in `notes` and marks the
unmeterable phases `null` — a guessed number is worse than a hole. A row
carrying a measurement pins `cpoly` and `bench_toolchain` alongside `arklib`
and `aeneas`: the field layer is a `rev`-pinned dependency of both bench slots
and `BENCH_TOOLCHAIN` is the compiler both were built with, so a number is
comparable only to another taken at the same two — the same set `perf-loop`
puts on a candidate row.

`reference` is the "gap vs unrestricted Rust" anchor: an
unrestricted-but-safe Rust implementation of the same operation, measured
**through the candidate slot** in a worktree — `make run-bench CANDIDATE=1`
like any candidate, so it gets the recentered within-run delta and the digest
assert for free — then discarded with the worktree. It is never a bench case
of its own (an absolute time or a cross-row comparison would say nothing),
never enters `hachi/src`, never extracts, and is never verified. Its candidate
ledger row uses `"strategy": "reference-unrestricted"`, `"verdict":
"reference"` — nothing may cite it as a champion; it exists so a bake-off row
can state what staying inside the ceiling cost.

## Skill A/Bs

* **Trigger criterion — variance in the ledger, not curiosity.** An A/B
  runs only when rows attribute divergent outcomes to one skill: the same
  strategy skill producing accepts on one target and contract failures on
  a like target; a campaign whose retries concentrate in one stage across
  campaigns; a translation gate that keeps needing the same manual repair.
  The suspect sentence in the skill is named before the variant is written.
* **This ledger is empty, so there is no trigger yet.** A suspicion inherited
  from AeneasCompPoly is not an A/B: make the edit, attribute the reason in
  the skill, and let this repository's rows accumulate. The first honest A/B
  here is one whose divergence appears in rows written here.
* Mechanics per `skill-authoring`: variant directory beside the canonical
  one, this session only; the experiment runs both versions on the same
  fixed input (a target already in the ledger is ideal); the row records
  both outcomes; the winner is folded into the canonical directory and the
  variant deleted before the session ends.

```json
{"kind": "ab", "ts": "…", "skill": "lean-to-rust",
 "hypothesis": "…the sentence under test…",
 "input": "ArkLib.Lattices.Ajtai.gadgetMul",
 "a": {"version": "HEAD@abc1234", "outcome": "…"},
 "b": {"version": "session variant", "outcome": "…"},
 "verdict": "b-folded",
 "pins": {"repo": "…", "dirty": true},
 "notes": "…"}
```

`verdict` ∈ a-kept · b-folded · inconclusive — inconclusive rows are kept
and the variant still dies with the session.

## Fold-back — the experiment's second product

Every settled experiment amends the responsible skill in the same session:
a bake-off arm that surfaced a missing gate amends the stage skill that
lacked it; an A/B's winning text lands in the canonical directory; a
surprising ledger row grows a "failure modes" tooth where it belongs. An
experiment whose lesson stays in the ledger has produced half its value —
the same rule `prove-sorry` applies to itself.

## Invariants to keep green

* `logs/ledger.jsonl` is append-only; every row carries a valid `kind` (or
  none, for candidate verdicts), an `op` of the form `<module>/<op>` over this
  crate's modules, and honest pins.
* No experiment varies more than one thing; no arm reads a sibling arm's
  artifacts.
* No variant directory survives its session; every settled experiment has
  both its row and its fold-back edit.
* Bake-off conclusions quote the pair (speed, effort) — never a collapsed
  score — and a speed claim inside the harness's noise floor is reported as
  unresolved.
