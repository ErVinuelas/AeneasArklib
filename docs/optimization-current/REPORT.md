# Current-upstream Hachi optimisation report

**DO NOT MERGE until proper controlled benchmarking has been completed and
reviewed.** The final Rust/Lean candidate is proved against current upstream;
performance acceptance is pending. All eight ordinary scale correctness cases
passed across the original sweep and final-case retry.

This pass starts at `681c7be0e432103328aab2ae263c9597d9ea96ff`, with 360 functions
and 85 constants across 13 modules. The code checkpoint is `171f0f6e28cd8c9675b6330664346746f4c63b31`. It changes **56 function bodies in ten
modules**: 73 buffer reservations in 54 functions, the approved guarded terminal
shortcut, and ten-squaring modulus evaluation. The benchmark candidate slot is
synchronized with the final source. Ring/NTT algorithms and all constants remain
unchanged. [CHANGES.md](CHANGES.md) lists every changed function;
[inventory.json](inventory.json) records every reviewed function and constant.

## Baseline and dependency contract

[contract.json](contract.json) records repository, dependency and toolchain pins.
Rust cpoly is now `d7e26bb42feb80a1d96f904d3c14f85786751513`, ArkLib is
`d51d8bc3c22062bf21385bd15b39d390b0fe4584`, and the Lean Aeneas backend is
`6125cb9e191aa500cac5b3de4df643002818b03a`. The developer-local backend URL is
replaced with its public fork **at the same revision**. Extraction uses
`nightly-2026.07.26-3a8586f`; extraction/benchmark Rust is pinned to nightly
2026-06-01 and Lean uses 4.33.1. The baseline default tests and original scale
sweep used the host default Rust 1.96.0; final regular/reference tests and the
standalone final-scale retry use the pinned nightly (rustc 1.98.0-nightly,
14210df0e). These correctness runs are not cross-compiler performance evidence.

The historical campaign at `a81b01d` is preserved on
`codex/hachi-verified-optimizations` at `b6c4f69`; it is not this comparison's
baseline. Fifteen of its 44 reservations are already present or superseded
upstream. Its monomial-basis rewrite would regress the newer doubling algorithm,
so that rewrite was discarded. Current doubling uses `2^n - 1` products.

The historical proof-gap report is also obsolete. Ext, ZeroCheck,
QuadEvalProtocol, EndPiece, Sumcheck, Chain and LiftProver are now audited roots.
The current composed chain takes explicit challenges, a lifted witness and
well-formed transcript/dimension assumptions; it is not a sampler or a proof of
hostile-input parsing.

## Explicit terminal-fast-path approval

The user explicitly approved **“Include the proved fast path”**, followed by
**“do it, but make an explicit note of it.”** That approved path is included.

`rho_digits_short_check` returns true when q = 4,294,967,197, base = 16,
digit count = 8, half-base = 8, and the bound is at least eight
(the pinned bound is 15). ArkLib's
`rhoDigitsShort_of_half_le` proves the bound for every quotient digit, and the
unchanged `RingSwitch.rho_digits_short_check_spec` is proved against the new
extraction. The ordinary coefficient loop remains for other profiles.
`lift_short_check` still checks z's norm; commitment and evaluation checks remain
intact. Formal validation is for the pinned profile, not arbitrary future edits.

**The Boolean benchmark has no correctness oracle for this shortcut.** A true
digest cannot validate it. The Lean theorem and explicit approval justify this
change; neither constitutes a runtime measurement.

## Verification evidence

| Check | Result |
|---|---|
| Fresh baseline extraction | Byte-identical to committed baseline Generated |
| Final extraction | Repeated extraction byte-identical, including after documentation/lint edits |
| Full baseline and final Lean builds | Passed, 3,898 jobs; final branch replay also passed |
| Headline axiom audit | 585 audit entries (one axiom-free); only subsets of propext, Classical.choice, Quot.sound; no sorryAx |
| Allocation-only model preservation | 1,513 definition equations, 76 data declarations, 1,060 theorem types; 2,649 declarations total |
| Imported model foundation | 347,586 kernel declarations identical |
| Public theorem statements | Unchanged; textual audit of 1,396 theorem/lemma signatures changes only the internal modulus-loop invariant |
| Rust default suite | Baseline and final candidate: 236 passed, zero failed, 50 intentionally ignored |
| Updated independent-reference suites | 29 passed, including sequential-product modulus reference and end-piece checks |
| Larger correctness sweep | Eight cases passed: seven in the original sweep, one in a standalone retry; see execution history below |
| Verification/tooling fixtures | Six preservation fixtures, eleven slot-gate fixtures, nine benchmark-runner fixtures passed |
| Frozen benchmark items and slot | 478 intact frozen items; 13-module null candidate after promotion |
| Coverage | 156 mirrored items: 82 benched, 74 named exclusions, zero unaccounted; nine additional nonmirrored benched items |
| Textual spec references | 156/156; navigation evidence, not a proof certificate |
| Clippy | Stable 1.96.0 used because pinned nightly lacks the component; same 267 warning messages as baseline, none added |

The scale sweep passed seven cases with stable Rust. Its last case was
deliberately interrupted after 587 seconds and restarted with the pinned nightly
and a 3,600-second timeout, retaining the same assertions and 22 GiB
virtual-address ceiling. The retry passed. The original sweep therefore exits
nonzero; the combined case outcomes are recorded in [scale-results.json](scale-results.json),
with the interruption and retry retained in the evidence logs. This is not a
single green `make test-scale` invocation or a performance comparison. The
removed unused test helper appears in older logs; its cleanup was followed by a
passing 20-test reference suite.

The single local Clippy allowance documents the terminal guard's deliberate
eager, pure Boolean comparisons. Two proof-repair iterations were needed: unfold
the pinned log-degree constant, and normalize the reserved message buffer in the
sumcheck prover proof. No new axiom, sorry, unsafe library code or weakened
public specification was introduced.

The modulus loop maintains `toExt(pw) = alpha^(2^k)` with `k ≤ 10` and
decreases `10 - k`. At exit, the independently checked parameter identity
`RING_DEGREE = 2^RING_LOG_DEGREE = 1024` gives the old postcondition; adding
one matches ArkLib's evaluation of `X^1024 + 1`. Reducedness is preserved by
the existing extension-field multiplication theorem. The sequential-product
Rust reference exercises a different algorithm.

The allocation certificate applies only to the allocation-only checkpoint,
retained as `allocation-only.patch.gz` and `allocation-only.Generated.lean.gz`.
The two algorithm changes are validated by the final ArkLib replay. See
[allocation-preservation.json](allocation-preservation.json),
[final-validation.json](final-validation.json) and the retained evidence logs.
Physical allocation failure, allocator behavior and peak memory are outside the
Aeneas vector model. Existing reducedness, shape, capacity and challenge-norm
hypotheses remain required; public Rust APIs do not dynamically enforce them all.

## Current component analysis

| Component | Functions | Current implementation and applied disposition | Contract to preserve |
|---|---:|---|---|
| params | 0 | 48 constants here, plus 37 arithmetic constants in ntt/ring; retain values and lookup tables | Field/profile equalities and constant checks |
| ntt | 31 | Preallocated three-prime transforms and fused Goldilocks stages; retain upstream algorithms | Canonical residues, roots, stage lengths, reciprocal and CRT bounds |
| ring | 51 | NTT products, fused/prepared dots, limb decomposition and adaptive short multiplication; historical reservations already landed | Separate general, bounded unsigned-digit and short representations; no blanket path substitution |
| linalg | 31 | Truncating fused dot and prepared matrix paths; 11 exact row/result reservations applied | Rectangular Wf matrices; prepared carrier relations and column capacity bounds |
| gadget | 14 | Unsigned decomposition already reserves exact digit-expanded sizes; reserve remaining known buffers | Digit order, centered versus unsigned digits, conditional bounded-z reconstruction |
| commit | 28 | Goldilocks prepared inner matrix and streamed/compact paths retained; output-container reservations applied | Existing Scheme/Raw32 specifications and decomposition relations |
| evalsplit | 17 | Dynamic monomial/Lagrange doubling retained; five reshape reservations applied | Little-endian variable order, fixed matrix dimensions, 2^n representability |
| ringswitch | 30 | Lazy block matrices, streamed lifted commitment, rolling evaluations and high-only quotient reconstruction retained; buffer reservations and ten-squaring modulus evaluation applied | Rlin layout, representative-polynomial identity, dimension and arithmetic bounds |
| quadeval | 56 | Shared carrier, compact/raw paths, sparse challenges and lazy Rlin construction retained; reserve independently sized component outputs | Shape, challenge-norm and prepared-path hypotheses; full relation decisions unchanged |
| endpiece | 9 | Complete terminal decision present; approved fixed-profile shortness shortcut proved | Preserve commitment/evaluation/z-norm checks; oracle-void Boolean benchmark explicitly acknowledged |
| zerocheck | 25 | Blockwise/base-field tables, Paterson–Stockmeyer range polynomial and hoisted public factors retained; h_alpha result reservation applied | Cube layout, coverage bounds, degree/range identity and current ZeroCheck refinement |
| sumcheck | 65 | Folded/tensor-split tables, coefficient-space round construction, lazy coefficient reductions and base-field first round retained; node/temporary/message buffers reserved | Degree bounds, point lengths, tensor orientation, round decisions and failure flow |
| chain | 3 | Explicit-input computational prover/verifier composition retained; point-copy output reservation applied | Well-formed transcript, challenge norms and fixed dimension hypotheses; no sampler or hostile-input parser implied |

Thin constructors/accessors remain unchanged. Remaining empty vectors include the
fairness controls, intentionally absent transform lanes, adaptive short descriptors,
and composite-width containers without a checked total already available. An empty
vector is not by itself evidence that adding a reservation is beneficial.

The Goldilocks unsigned-digit path needs DigitWf and width at most 8192;
centered balanced digits do not meet that representation. Prepared matrices also
require their stated nonempty/dimension/capacity relations. Public Rust APIs do not
enforce all proof hypotheses dynamically. No hypothesis is removed by allocation
preservation, and no malformed-input security claim is inferred.

Further algorithmic opportunities retained for a later measured campaign: eliminate
prepared-row slice copies in general dot paths; reuse conversion/twist scratch;
reuse short-product scratch; replace suffix-table rebuilding by in-place doubling.
Each requires an explicit current-model proof and attributable measurements.
Some current comments still describe earlier stages (for example “allocation-free”
short accumulation and “PROTOTYPE” limb code); the audit follows the body and the
actual theorem roots, not those labels.


## Allocation instrumentation

Three repetitions were identical. Inputs were built before counting; output
digests are smoke checks, and the zero-check and terminal Boolean cases have no
independent correctness oracle. Counts include allocation activity reached during
each measured operation. Requested bytes are cumulative, not peak memory.

| Case | Allocations baseline → candidate | Reallocations baseline → candidate | Requested bytes baseline → candidate |
|---|---:|---:|---:|
| `ring/add/1024` | 1 → 1 | 0 → 0 | 8192 → 8192 |
| `linalg/add/8` | 9 → 9 | 0 → 0 | 65728 → 65728 |
| `linalg/copy/8` | 9 → 9 | 1 → 0 | 65824 → 65728 |
| `gadget/decompose/8` | 129 → 129 | 0 → 0 | 1050112 → 1050112 |
| `gadget/balanced_decompose/8` | 129 → 129 | 516 → 3 | 1573792 → 1051456 |
| `commit/honest_opening/8_reduced` | 9 → 9 | 1 → 0 | 65824 → 65728 |
| `evalsplit/monomial_basis/3` | 156 → 156 | 1 → 1 | 1270048 → 1270048 |
| `ringswitch/rho_digits/1024` | 2 → 2 | 8 → 0 | 24544 → 16384 |
| `quadeval/carrier/2x8` | 503 → 503 | 146 → 144 | 4243552 → 4243312 |
| `endpiece/rho_digits_short_check/1` | 16 → 0 | 64 → 0 | 196352 → 0 |
| `zerocheck/c_w_table_mle/12` | 8 → 8 | 24 → 0 | 212896 → 188416 |
| `sumcheck/round_node_weights/33` | 1 → 1 | 4 → 0 | 992 → 264 |
| `sumcheck/interpolate/33` | 1090 → 1090 | 2380 → 0 | 1452800 → 1151040 |

These are thirteen representative cases, not one isolated measurement per
changed function. The chain is covered by its functional/scale tests and Lean
proofs; it has no isolated allocation case here. The modulus change has no heap
allocation to remove. No speedup or peak-memory claim follows from this table.


## Runtime acceptance and remaining work

No controlled runtime win is claimed. The 13 allocation cases do not establish
per-function speedups. The default suite deliberately excludes 25 instrumentation
cases, eight scale correctness cases and 17 scale-XL cases; the eight ordinary
scale cases passed separately as documented above. The 42 instrumentation and
scale-XL cases were not run. Scale-XL needs a suitably provisioned host.

The benchmark gate now checks active candidate structure and unchanged timing
control dependencies. The runner refuses existing output artifacts, nonzero
exits, missing/malformed/unusable reports and detected competing work. It retains
raw samples and execution metadata. Process monitoring is a guard against known
interference, not proof of complete host isolation. No timing run is accepted
alongside Lean builds, Rust builds or scale tests.

[REPRODUCE.md](REPRODUCE.md) gives the correctness and runtime-acceptance procedure:
compare the immutable current baseline with this candidate on identical inputs,
using full sampling, timing controls, recentered within-run comparisons and
appropriate end-to-end profiling. Retain and review regressions and unusable rows.
The PR must remain draft and unmerged until that evidence is reviewed.

The lean-eq-rust-gen guidance is pinned at
`3a6b8550c142244d0ef2a3cbf2febf961e98f1dc`: `verified-rust-optimization`,
`extractable-rust`, `rust-crypto-refinement` and `lean-to-rust-hachi`, together with
the knowledge catalog, lattice comparison and benchmark contract. A remote refresh
found that local checkout three commits ahead and zero behind origin/main; it was
left unchanged. Project-local extraction and verification skills supplied the
model, axiom, timing-control and reviewer gates. Independent reviews found no
blocking source or specification-contract issue in the final changes.
