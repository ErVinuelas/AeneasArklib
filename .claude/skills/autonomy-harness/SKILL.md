---
name: autonomy-harness
description: Running the optimization loop unattended under /loop — one iteration picks the next target by brief headroom over the genesis corpus, runs the chosen route (default route-r3) through perf-loop and its K=1 verify-campaign, appends ledger rows, and extends the ordered commit plan; halts on proof failure, approval gates, dependence on unmerged staged work, or an exhausted corpus; use when asked to run the loop autonomously, start an unattended optimization session, or put the pipeline under /loop
---

# The Autonomy Harness (/loop v1)

How the pipeline runs without a user driving each stage: a `/loop` session
in which each firing performs (or continues) **one iteration** of the loop
below. This is deliberately the supervised form — the session is watchable
and interruptible, and its gates block rather than self-approve. Scheduled
routines and CI triggers have no procedure here on purpose: they get one
only after the loop has proved itself under supervision, and the ledger
rows from these runs are that proof. `logs/ledger.jsonl` is empty, so nothing
has been proved that way yet.

## Invocation

**Human invocation:** start with `/autonomy-harness` alone. Ask: **“Use the
default `route-r3`, or pin `route-r1` or `route-r2` for this session?”** Record
the answer before the first iteration; choosing the target remains the
harness's job. A default is an explicit answer, not an unstated assumption.

**Agent invocation:** bypass the dialogue with this named request; omitting
`route` explicitly selects the default:

```yaml
agent_request:
  route: route-r1 | route-r2 | route-r3 # optional; route-r3 when omitted
```

Return an invalid route to the invoking agent rather than asking the human.

## The one rule: the loop never outruns its debt

K=1 holds inside the loop: an iteration is target → accepted champion →
**verified** champion, and the next iteration starts only if its target
does not depend on unmerged staged state. Agent sessions cannot commit
(the working style of this repository is stage-only), so every iteration
*extends one ordered commit plan* rather than landing anything; a second
iteration on the same module would build on an uncommitted foundation and is
therefore a halt, not a queue. The loop's output is verified champions plus a
commit plan the user executes — never a pile of unverified speed.

## One iteration

1. **Target selection.** Corpus = every operation with a genesis item in
   `hachi/benches/genesis` (new operations enter the corpus only through a
   user-triggered `op-genesis`, never from inside the loop). That crate today
   holds the frozen first translation of all five `hachi/src` modules;
   `params` freezes `const`s and declares no bench target, so the rankable
   operations are those of `ring`, `linalg`, `gadget` and `commit`. Exclude
   operations with an open champion branch or staged unmerged work. Rank the
   rest by algorithmic headroom from fresh `arklib-analyze` briefs — targets
   are never hardcoded. Nothing rankable → halt "corpus exhausted".
2. **Route.** Run `route-r3` on the selected target unless the user pinned
   a different route for the session. The route's own stages produce the
   candidate rows, the champion, and the campaign row.
3. **Bookkeeping.** Verify the iteration left: candidate rows for every
   benched candidate, one campaign row, `make bench-check` green, and the
   commit plan extended with this iteration's ordered steps (champion
   branch material, merge, any post-merge `make bench-stamp` followed by its
   own stamps-only commit).
4. **Report.** One user-visible summary per iteration: target, verdicts
   with numbers, campaign result, what the commit plan now contains.

## Pacing under /loop

* An iteration spans hours, and here the verification half dominates:
  `make build` takes hours on a cold Mathlib cache (README § "Usage"), so a
  single campaign can outlast a working day. /loop firings are checkpoints,
  not iterations. On each firing: if a stage is still running, `noop` with a
  long delay; if a stage just finished, advance to the next; if the iteration
  closed, start the next one at step 1.
* **Machine serialization survives autonomy**, and it is the rule most at
  risk here. One criterion session *or* one `lake build` at a time,
  repo-wide — never both, never two of either. Polling adds nothing, because
  neither can be parallelized: a second build makes the first slower than the
  sum of the two, and a build landing inside a criterion session corrupts the
  measurement silently (`Makefile` § `run-bench` says to check the machine
  before a run). An unattended run is the easiest place to violate this.
* Every timing claim comes from the run that produced it. Nothing is compared
  across runs and no number is carried between iterations: `genesis` is
  re-measured in the same criterion session every time, which is the whole
  reason that crate exists (`hachi/benches/genesis/src/lib.rs` § "Why a whole
  crate exists for this").

## Halt conditions — halt loudly, never degrade

* `verify-campaign` result ≠ `verified` → halt; the partial/blocked row and
  the blocking lemma go in the iteration report. The loop does not take a
  new target on top of unpaid debt. A statement parked in
  `hachi/lean-wip/` is unpaid debt, not a closed iteration.
* An approval gate (e.g. `prove-sorry`'s statement-weakening gate) → block
  on the user; the gate exists precisely for the unattended case and is
  never self-approved.
* Next viable target depends on unmerged staged work → halt "waiting on
  commit plan"; resumption is the user executing the plan.
* Bench verdict `unusable` twice in a row, or any sign of machine
  contention → halt; the weather is not optimized around. Read the
  `_control` spread of the run before reading anything else: `NOTES.md`
  § "The first benchmark run, and what it says about the harness" records
  that on the host used there, byte-identical crates read up to 59% apart and
  the controls put a 10–15% floor under every case, which is *above* the
  accept floor. A run whose control did not run, or whose control spread
  swamps the effect, has no verdict to report — the report exits 2 and the
  loop halts rather than promoting noise.

## Invariants to keep green

* Stage, never commit — the loop ends (or halts) with staged changes and
  one ordered commit plan covering every iteration it ran.
* No iteration starts on unpaid proof debt or unmerged same-module state.
* Every iteration is fully accounted: its candidate rows, its campaign row,
  its commit-plan extension, its one-summary report.
* One machine-heavy job at a time, and every number reported from the run
  that measured it.
* Gates block; nothing is auto-approved because nobody was watching.
