# logs/

## `ledger.jsonl`

Append-only, one JSON object per line: the machine-readable record of what the
optimization loop and the verification pass did, and what it cost.

It is **empty**, and that is the current true state of this repository. No
candidate has been benched to measurement grade and no verification campaign has
run — [`NOTES.md`](../NOTES.md) § "Benchmark numbers from this session are not
measurement-grade" is the standing record. The first row will be written by the
first `perf-loop` or `verify-campaign` run.

Two kinds of row, distinguished by the presence of `"kind": "campaign"`:

* **candidate rows** — one per benched candidate, carrying the verdict the accept
  rule produced: the recentered `cand_vs_now` per case, the per-binary
  `cand_lean` it was recentered by, the `threshold` and `ab_bias` of that run, the
  `slot_sha` fingerprint of the code the candidate slot actually held, the
  machine id, and the pins (repo sha, `cpoly` rev, aeneas tag, bench toolchain).
  A row records a measurement, so it records the conditions that make the
  measurement attributable — a delta with no run conditions beside it cannot be
  checked later, only believed.

  Every such row also carries a **`run`**, which is not invented: `make run-bench`
  prints it and `JSON=` writes it into the report, and `make ledger-check`
  enforces its shape. It is stable across a report-only rerun of unchanged
  criterion state, so one measurement never acquires two identities. Rows with
  different `run` values are never compared to each other — that is the
  no-cross-run rule, in a form tooling can refuse on.
* **campaign rows** — one per verification campaign: which specs were carried,
  re-pinned, or newly written, the metered effort (tokens, wall-clock per stage,
  retries, interventions), the result, and whether the axiom audit came back
  clean.

`make ledger-check` validates the schema and enforces append-only against the
last committed state. The row schemas, the notes discipline, and the reasoning
behind metering effort at all are owned by the `skill-lab` skill; that skill is
the source of truth and this file is a pointer.

### Why a ledger and not just prose

[`NOTES.md`](../NOTES.md) is the prose half and stays the place where reasoning,
surprises, and rejected alternatives are written down; it is much better at
"here is why this was hard" than any schema. What it cannot do is answer
"how much did the last twelve campaigns cost, and did the accept rule ever
accept something a later campaign could not prove?" — which is the question that
decides whether the loop's cadence (one campaign per accepted champion) can ever
be relaxed. That answer has to be computed over rows, so the rows exist.

## Nothing here is a timing

Criterion's own output lands under `hachi/target/criterion`, which `.gitignore`
covers, and the optional `JSON=` report is ignored at the root. No absolute time
is ever committed: an absolute time is not comparable to another run's, nor to
another row's in the same run, so keeping one invites exactly the cross-run
comparison the harness refuses to make. What a ledger row keeps is a *delta*
measured inside one criterion session, together with the conditions of that
session.
