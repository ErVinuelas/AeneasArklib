# Reproducing this campaign

The baseline is `681c7be0e432103328aab2ae263c9597d9ea96ff`. Use the exact
Rust, extractor, Lean and package pins in `contract.json`. The historical
`b6c4f69` checkpoint is not a valid comparison baseline for these changes.

## Correctness

On the final branch, provision the pinned tools/dependencies with `make setup`,
then run:

```sh
make extract
make build
cargo +nightly-2026-06-01 test --release --manifest-path hachi/Cargo.toml
RUSTUP_TOOLCHAIN=nightly-2026-06-01 make test-scale SCALE_TIMEOUT=3600
python3 scripts/test_allocation_preservation.py
python3 scripts/test_bench_candidate.py
python3 scripts/test_optimization_benchmarks.py
make bench-check bench-coverage spec-check ledger-check
```

Extraction must reproduce the committed `hachi/lean/Generated.lean` byte for byte.
The full build includes `Check.lean`; its headline closures must contain no
`sorryAx` or additional axioms. Do not infer correctness from a successful
extraction or a benchmark checksum. Scale tests are separate from the 25 timing
instruments and 17 scale-XL tests; those 42 ignored cases are not in this sweep.
The original recorded scale sweep used the host default Rust 1.96.0, a 22 GiB
virtual-address limit, and the Makefile's 1,800-second timeout per case. Seven
cases passed. The final case was deliberately interrupted after 587 seconds
(exit 143), before its timeout, to restart only that case with a longer limit.
That interrupted invocation is neither a pass nor an assertion failure.
The standalone retry uses the pinned nightly (rustc 1.98.0-nightly, 14210df0e),
the same inputs/assertions and address-space ceiling, and a 3,600-second timeout:

```sh
(ulimit -v 23068672; timeout 3600 cargo +nightly-2026-06-01 test --release \
  --manifest-path hachi/Cargo.toml --test evalsplit_semantics -- \
  --ignored --exact --test-threads=1 eval_split_eval_interpolates_the_hypercube)
```

See `scale-timeout-override.json` and the retained scale logs for the execution
history. The limits are resource ceilings, not peak-memory measurements; elapsed
times across these compilers/invocations are not performance comparisons.
For future complete sweeps, select the pinned toolchain explicitly as above and
provision sufficient time/resources for the full-size tests.

The allocation-only certificate is separately reproducible: create baseline
and candidate checkouts at the baseline revision, use the public backend URL
from this branch with the same commit pin, and apply the decompressed
`allocation-only.patch.gz` to the candidate. Build `Generated` in both checkouts.
From the candidate's `hachi` directory run:

```sh
HACHI_BASELINE_LEAN_PATH=/absolute/baseline/hachi/.lake/build/lib/lean \
  lake env lean /absolute/final-branch/scripts/CheckAllocationPreservation.lean
```

The retained compressed Generated source and `allocation-preservation.json`
identify that intermediate model. The certificate covers allocation changes
only. The terminal guard and repeated-squaring loop require the final ArkLib
proof replay, not definition-by-definition equality with the baseline.

## Runtime acceptance — required before merge

Create a fresh benchmark worktree at the baseline revision. Leave its
`hachi/src` unchanged. Copy the final branch's 13 module files (all `.rs` files
except `lib.rs`) into that worktree's `hachi/benches/candidate/src`. Preserve the
slot's pinned `lib.rs` and Cargo.toml. Copy this branch's hardened Makefile and
`hachi/benches/harness.py` into the staging worktree. Run `make bench-toolchain`
there to provision the pinned Rust benchmark toolchain. Benchmarking does not
require the baseline's Lean setup, whose original backend URL is developer-local.

On an otherwise idle host, invoke the wrapper **outside an isolated PID
namespace**, so it can see competing work:

```sh
python3 /absolute/final-branch/scripts/run_optimization_benchmarks.py \
  /absolute/benchmark-worktree --output /absolute/new-evidence-directory \
  --label current-profile \
  ring linalg gadget commit evalsplit ringswitch quadeval endpiece zerocheck sumcheck
```

Use full harness sampling, timing controls and its within-run recentered
candidate comparisons. Run serially, with no Lean builds, Rust builds, other
benchmarks or scale tests. The process monitor detects known competing builds;
it does not establish complete machine isolation. Review every operation row,
including unchanged controls, regressions and unusable rows. Keep report JSON,
execution metadata, logs and raw Criterion samples. Failed or interrupted runs
are not acceptance evidence. Parameters have no runtime body; NTT is exercised
through ring operations; composed chain rows remain explicitly excluded by the
upstream harness and require an appropriate end-to-end profiling plan.
Apply the local perf-loop acceptance rule, including the independent-run
requirement for a single-row target; a favorable isolated reading is insufficient.

The fixed-profile terminal Boolean row has no correctness oracle. The user
explicitly approved the proved shortcut; its Lean theorem, unchanged surrounding
checks and profile guard are the correctness evidence. A constant `true` digest
cannot replace that evidence.

Allocation counts can be reproduced with `scripts/check_allocations.py` against
the same baseline/candidate staging worktree. These counts are not timings or
peak memory and do not establish runtime acceptance. **Do not merge until proper
benchmarking has been completed and reviewed.**
