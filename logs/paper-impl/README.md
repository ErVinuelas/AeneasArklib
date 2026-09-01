# Reference-implementation benchmarks (the paper's `hachi-pcs`)

Measured timings of the **paper's own prototype** —
[georgeorourke/hachi-pcs](https://github.com/georgeorourke/hachi-pcs) — run on
this machine at the parameter set this repo adopted from [NOZ26] Fig. 9
(ℓ = 30). These are the numbers this crate's own benchmarks are meant to be
compared against once the paper-parameter flip (`PLAN_PAPER_PARAMS.md`) has
landed and genesis is re-frozen.

**Why absolute times live here when `logs/README.md` says "nothing here is a
timing":** that rule exists because the optimization loop's accept rule must
never compare across criterion runs. This directory is not part of that loop —
it is an *external baseline*, recorded at the user's request, with the full run
conditions written next to every number so the measurement stays attributable.
Nothing in here is ever read by the accept rule or `make ledger-check`.

## Run conditions

| Condition | Value |
|---|---|
| Reference repo | `georgeorourke/hachi-pcs` @ `6d90caca64386e506bdd5d0097f87ccb98fc0926` (2026-04-13, "Build instructions") |
| Machine | AMD Ryzen 7 8845HS laptop (16 hw threads, AVX-512), 30 GiB RAM, NVMe |
| OS | Linux 6.17.0-1032-oem |
| Toolchain (standard + stats arms) | rustc 1.89.0 stable, `cargo build --release` |
| Toolchain (AVX-512 arm) | rustc 1.98.0-nightly (2026-05-31), `--features=nightly` (tfhe-ntt nightly SIMD) |
| Key deps | tfhe-ntt 0.6.1, ark-ff 0.5.0 |
| Threading | The reference is single-threaded (no rayon); runs executed sequentially, machine otherwise lightly loaded |
| Witness | `2^ℓ` random u32 coefficients mod q, streamed from an NVMe file via mmap (the reference's own `gen_file` generator); file pages warm in page cache for every recorded run |
| Date | 2026-08-28, afternoon block (see "Reading notes" on why a morning block was discarded) |

Raw logs, witness files, and the harness live in
`~/.cache/hachi-pcs-bench/` (`run_<arm>_l<ℓ>.log`, `campaign.status`);
[`spans.json`](spans.json) in this directory is the parsed form of every run's
time-graph output. Timings are the reference's **own** `time-graph` spans (its
designed benchmark output), not external stopwatches; wall/RSS come from a
`getrusage`-based wrapper around each whole run.

## Parameters

The reference derives everything from ℓ in `src/hachi/setup.rs`. At ℓ = 30 it
is **exactly** the set this repo staged from Fig. 9:
q = 2³² − 99, α = 10 (d = 1024), b = 16, δ = 8, m = r = 10
(= `ML_VARS_HIGH`/`ML_VARS_LOW`, so `MESSAGE_ROWS = BLOCKS = 1024`),
n_A = n_B = 1, ω = k = 16. Smaller ℓ in the ladder keep α = 10 and split
m = r = (ℓ − 10)/2.

Protocol-layer constants with no counterpart in this repo (`lib.rs` § Status):
τ = `Z_DECOMP_DELTA` = 4, z-bound 30583, and the matrix D. The reference's
Prove/Verify therefore measure a *superset* of what this crate implements.

## What maps onto what

| This repo's bench case | Reference measurement | Comparability |
|---|---|---|
| `commit/commit` (BLOCKS = 1024) | `commit::commit` span (top-level, witness commit) at ℓ = 30 | Direct: same input shape (2²⁰ ring elements, d = 1024), same q, b, δ. Caveats: the reference commits via tfhe-ntt + witness streaming; ours is schoolbook, in-memory. |
| `commit/verify`, `commit/verify_weak` | `verify::verify` span | Partial: the reference's verify checks the full PCS proof (two sumchecks + reduction), ours checks a commitment opening. Reference number is an upper bound of the comparable part. |
| `ring/mul` | stats arm: `_fwd` + `_mul_acc` + `_inv` per-call | Direct per-op (NTT vs schoolbook, d = 1024). |
| `gadget/gadget_decompose` | stats arm: `poly_vec::b_decomp` per-call | Direct per-op (b = 16, δ = 8; note the reference decomposes a whole PolyVec per call, sizes vary by site). |
| `linalg/mat_vec_mul` | stats arm: `ring::mat_mul_vec` per-call | Direct in kind; matrix shapes vary by call site. |
| `evalsplit/*` | folding inside `prove::prove` (`compute_z`, `compute_y_and_w`, sumchecks) | Loose: same mathematical step (split evaluation), different decomposition of work. No prover in this repo yet. |
| — (no counterpart) | `prove::prove`, `sumcheck_proof` | Context only: this repo has no protocol layer. |

## Results — pipeline spans (standard build, stable rustc)

Time-graph spans, one run per ℓ (two independent runs at ℓ = 30). `commit` is
the top-level witness commit; the prove-internal re-commit is listed
separately. Wall covers the whole process (incl. witness generation on first
touch of a file and the `main.rs` naive evaluation check, which are not spans).

| ℓ | Commit | Prove | — of which sumchecks | Verify | wall | peak RSS |
|---|---|---|---|---|---|---|
| 20 | 0.11 s | 9.95 s | 9.64 s | 5 ms | 10.1 s | 0.32 GiB |
| 22 | 0.44 s | 20.0 s | 19.3 s | 8 ms | 20.7 s | 0.65 GiB |
| 24 | 1.69 s | 41.3 s | 39.1 s | 16 ms | 43.8 s | 1.29 GiB |
| 26 | 6.53 s | 84.5 s | 77.1 s | 28 ms | 94.1 s | 2.69 GiB |
| 28 | 23.6 s | 161.6 s | 138.8 s | 63 ms | 197 s | 5.88 GiB |
| **30** | **89.8 s** | **360.4 s** | 272.7 s | **0.138 s** | 518 s | 12.7 GiB |
| 30 (repeat) | 101.0 s | 408.1 s | 312.9 s | 0.154 s | 564 s | 13.7 GiB |

Prove-internal re-commit at ℓ = 30: 0.68 s. Run-to-run spread at ℓ = 30 is
~12% (laptop thermal envelope); treat the two ℓ = 30 rows as the honest
uncertainty band.

## Results — AVX-512 arm (nightly tfhe-ntt)

| ℓ | Commit | Prove | — of which sumchecks | Verify | wall | peak RSS |
|---|---|---|---|---|---|---|
| 24 | 1.19 s | 36.6 s | 33.6 s | 14 ms | 38.5 s | 1.31 GiB |
| 30 | 68.7 s | 428.4 s | 293.4 s | 0.149 s | 560 s | 13.8 GiB |
| 30 (repeat) | 77.6 s | 464.8 s | 311.4 s | 0.148 s | 605 s | 11.6 GiB |

AVX-512 buys ~25% on Commit (NTT-bound) and nothing on Prove — the sumchecks
are ark-ff extension-field arithmetic, which tfhe-ntt's SIMD does not touch.
The Prove totals here are *higher* than the standard arm's; the difference is
within the thermal spread on the non-NTT part, not a SIMD slowdown.

## Results — per-operation breakdown (stats build, ℓ = 24)

Per-call averages over the whole pipeline run (`total / calls`), from the
instrumented arm. Instrumentation overhead is negligible at this granularity
(the stats run's Prove matches the uninstrumented one within noise).

| Reference op (d = 1024) | per call | calls | maps to our bench case |
|---|---|---|---|
| `ring::_fwd` (forward NTT) | 7.6 µs | 147 520 | `ring/mul` (part) |
| `ring::_mul_acc` (pointwise mult-acc) | 2.1 µs | 144 384 | `ring/mul` (part) |
| `ring::_inv` (inverse NTT) | 18.6 µs | 261 | `ring/mul` (part) |
| ⇒ one negacyclic ring mul ≈ 2·fwd + mul_acc + inv | **≈ 36 µs** (amortized far lower: fwd values are cached across a mat-vec row) | — | `ring/mul` |
| `poly_vec::b_decomp` (base-16, δ = 8, whole PolyVec) | 1.73 ms | 264 | `gadget/gadget_decompose` |
| `ring::mat_mul_vec` | 5.31 ms | 261 | `linalg/mat_vec_mul` |
| `ring::chal_mul_small_poly` (sparse ω = 16 challenge mul) | 10.0 µs | 131 072 | — (no challenge layer here yet) |
| `stream::read` (mmap witness read) | 0.37 ms | 400 | — (we hold the message in memory) |
| `commit::commit` (whole, ℓ = 24) | 1.56 s | 1 | `commit/commit` at reduced shape |

At ℓ = 20 the same per-call numbers reproduce within ~10% (see `spans.json`,
`stats_l20`), so they are shape-stable and usable as per-op anchors.

## Reading notes

* **The headline comparison row.** When this repo's benches re-freeze at paper
  parameters, the direct anchor is: reference Commit at ℓ = 30 = **90–101 s**
  single-threaded on this machine (69–78 s with AVX-512). Reference
  ring-mul ≈ **tens of µs**; a schoolbook d = 1024 mul is ~N²/d ≈ 1024× the
  coefficient work of an NTT butterfly pass, so a raw gap of roughly two
  orders of magnitude on `ring/mul` (and hence on `commit/commit`) is the
  *expected starting point*, not a measurement error. This is the quantified
  version of `PLAN_PAPER_PARAMS.md` Phase 5's warning that the multiplication
  champion becomes urgent at d = 1024.
* **A morning measurement block was discarded.** The first ladder (ℓ = 20–26,
  2026-08-28 ~10:30) ran ~2× slower across the board than the afternoon block
  (power profile / thermal state of the laptop). Every number above comes from
  the afternoon block only; the morning logs are kept as
  `morning_run_std_l2*.log` in the cache dir, unused. This is exactly the
  cross-conditions comparison the ledger rules exist to prevent — the fix was
  to re-measure everything under one condition set.
* **Wall vs spans.** Wall time additionally contains witness-file generation
  (first run per file) and `main.rs`'s naive O(2^ℓ·ℓ) evaluation check —
  neither belongs to the scheme. Only the span columns are scheme cost.
* **Verify.** The reference's 0.14 s at ℓ = 30 verifies the *full* evaluation
  proof. Our `commit/verify` checks a commitment opening only; when comparing,
  expect ours to be strictly cheaper in scope. Note the reference's verify is
  polylog: it never touches the witness.
* **Memory.** Peak RSS at ℓ = 30 is ~13 GiB (dominated by the folded-witness
  sumcheck tables plus the resident mmap pages of the 4 GiB witness file).
  This machine held it with headroom; our in-memory message at the same shape
  is ~8 GiB before any commit work, which is the Phase 4 wall in a number.
* **What was NOT measured.** No multi-threaded run (the reference has no
  threading), no run at the paper's own hardware, and no criterion-style
  statistical repetition — one process per (arm, ℓ), two at ℓ = 30. For a
  delta-grade comparison of *our* code, the repo's own criterion harness
  remains the instrument; these numbers are the external anchor, good to the
  ~12% run-to-run spread stated above.
