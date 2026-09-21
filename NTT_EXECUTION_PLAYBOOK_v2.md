# Autonomous Execution Playbook v2
## Verified NTT-Based `Rq::mul` for AeneasArklib

**Repository:** `ErVinuelas/AeneasArklib`  
**Primary component:** `hachi`  
**Execution model:** autonomous agent working in an isolated clone/branch with minimal human interaction  
**Objective:** replace the current schoolbook Rust implementation of `Rq::mul` with an NTT-based multiplication while preserving the existing mathematical semantics and downstream Lean theorems.

---

# 0. Mission and success condition

Implement a production Rust multiplication for Hachi's ring using a scalar auxiliary-prime NTT + CRT construction, extract it through Charon/Aeneas, prove it correct in Lean, and preserve the current theorem boundary.

Desired end state:

```text
new Rust Rq::mul
       |
       v
same HachiEquiv.Ring.mul_spec
       |
       v
same negConv semantics
       |
       v
same HachiEquiv.RqBridge.mul_spec
       |
       v
same downstream Hachi theorems
```

The implementation may change radically. The mathematical contract must not.

This document is designed for an autonomous engineering/proof agent. The agent is expected to investigate ordinary technical uncertainties independently rather than ask for routine guidance.

A failed feasibility gate is a valid and useful project outcome. Do not force the project forward merely to claim completion.

---

# 1. Repository isolation and git discipline

The work should begin from a clean clone of the current known-good repository state.

## 1.1 Record the baseline

Before editing any source file:

```sh
git status --short
git rev-parse HEAD
git branch --show-current
```

Record the full baseline SHA in:

```text
logs/ntt-execution.md
```

If that path does not exist, create it.

The repository at this SHA is the authoritative semantic and performance reference.

## 1.2 Work on an isolated branch

Create a dedicated branch, for example:

```sh
git switch -c experiment/verified-ntt-mul
```

Do not work directly on `main`.

Do not rewrite or force-push the baseline branch.

Do not amend or squash checkpoint commits during execution. The purpose of checkpoints is forensic recovery and bisectability.

## 1.3 Commit at major gates

Create commits at least at these milestones:

```text
baseline-verified
ntt-prototype
performance-gate
aeneas-vertical-slice
pure-ntt-proof
full-extracted-ntt
crt-hachi-bridge
production-switch
final-verification
```

Commit names do not need to match exactly, but each milestone must be recoverable from git history.

If a gate fails, commit the evidence/report if useful before stopping or pivoting.

## 1.4 Repository is authoritative

This playbook is a plan, not an oracle.

If repository behavior contradicts the playbook:

1. inspect the code and project instructions;
2. determine the actual invariant;
3. document the discrepancy;
4. adapt the plan while preserving the mission and non-negotiable proof contracts.

Never modify correct repository behavior merely to make the playbook literally true.

---

# 2. Autonomous operating policy

The agent should not ask for routine implementation decisions.

For ordinary uncertainty:

1. inspect the repository;
2. inspect nearby proofs and generated code;
3. inspect upstream/reference formalizations when useful;
4. choose the simplest proof-friendly design;
5. record material design decisions;
6. continue.

The agent may independently:

- create/edit Rust and Lean files;
- run extraction/build/test/benchmark commands;
- add proof helper lemmas;
- change internal implementation structure;
- replace in-place algorithms with proof-friendlier equivalents;
- choose auxiliary constants after validating them;
- refactor internal proof modules;
- abandon a failed implementation attempt and reset to a checkpoint.

The agent should request owner input only if one of these occurs:

1. the performance gate fails materially and several plausible local fixes have already been tested;
2. the Aeneas feasibility gate remains blocked after a reasonable implementation redesign;
3. preserving `Ring.mul_spec` appears to require changing `Wf`, `coeffK`, `toRq`, or the semantic role of `RqBridge`;
4. progress would require introducing a new trusted axiom or materially expanding the trusted computing base;
5. progress would require changing Hachi's cryptographic parameters;
6. repository/toolchain corruption prevents establishing a trustworthy baseline.

Otherwise, decide locally and proceed.

---

# 3. Execution log and checkpoint reports

Maintain:

```text
logs/ntt-execution.md
```

Keep it concise. Record only material facts.

At the end of every major gate, append:

```text
## Gate <name>

Status: PASS | CONDITIONAL | FAIL | PIVOT

Baseline/working commit:
<sha>

Commands/evidence:
- ...
- ...

Artifacts completed:
- ...

Key measurements:
- ...

Proof status:
- ...

Problems discovered:
- ...

Decision:
CONTINUE | REDESIGN | STOP

Reason:
...

Next action:
...
```

A STOP result is acceptable if justified by evidence.

At the end of the project, append a final handoff report using the format in Section 23.

---

# 4. Non-negotiable proof invariants

These rules override implementation convenience.

## 4.1 Preserve the multiplication contract

The final theorem must retain the existing semantic statement:

```lean
theorem mul_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b) :
    ring.Rq.mul a b
      ⦃ z => Wf z ∧ ∀ k, k < N → coeffK z k = negConv a b k ⦄
```

Do not weaken this theorem.

Do not replace `negConv` with an NTT-specific public specification.

Do not make downstream users reason about auxiliary primes, roots, transform order, or CRT.

## 4.2 Preserve the ArkLib bridge

Target:

```lean
HachiEquiv.RqBridge.mul_spec
```

should remain textually unchanged.

If imports/names force a small textual edit, the theorem statement and proof architecture must remain semantically unchanged.

A need to redesign `toRq`, `Wf`, `coeffK`, or ArkLib ring semantics is a **stop-and-reassess signal**.

## 4.3 No proof weakening

Do not:

- introduce `sorry`;
- introduce `admit`;
- introduce new arithmetic/NTT correctness axioms;
- hide implementation logic behind opaque assumptions;
- assume away overflow/runtime states that can actually occur;
- change Hachi parameters to make the proof easier;
- modify ArkLib specifications to match the implementation.

The repository's existing proof/axiom gates must stay clean.

## 4.4 V1 scope is deliberately narrow

V1 is:

> A fixed-size, scalar, three-prime, 2048-point NTT/CRT implementation of `Rq::mul` that proves the existing `Ring.mul_spec`.

V1 is not:

- SIMD;
- AVX2/NEON;
- a persistent NTT representation;
- a generic transform library;
- generic `N`;
- a public NTT API;
- a modulus change;
- an ArkLib redesign;
- a broad arithmetic rewrite;
- Montgomery arithmetic unless evidence shows it is necessary for the performance gate.

Defer optional sophistication.

---

# 5. Existing architecture to exploit

Before editing anything, inspect at least:

```text
INSTRUCTIONS.md
README.md
Makefile
hachi/Cargo.toml
hachi/src/ring.rs
hachi/src/params.rs
hachi/lean/Ring.lean
hachi/lean/RqBridge.lean
```

Also inspect nearby test and benchmark infrastructure before adding new infrastructure.

## 5.1 Existing coefficient semantics

`Ring.lean` already defines useful semantic objects, including:

```lean
negConv
wordN
posSum
negSum
```

and proofs connecting the natural sums to `negConv`.

The new NTT proof should reuse these.

Do not build a second public convolution semantics.

## 5.2 Existing ArkLib bridge

`RqBridge.lean` already proves `negConv` corresponds to multiplication in `Rq Φ`.

Therefore the new implementation proof should terminate at:

```text
new implementation = negConv
```

and reuse the existing bridge.

## 5.3 Existing bounds

The current proof already establishes natural-number bounds for delayed multiplication.

With:

```text
N = 1024
q = 4294967197
```

the exact raw coefficient bound is:

```text
N * (q - 1)^2
= 18889465051869288873984
< 2^74
```

This is the key CRT exactness range.

---

# 6. Algorithmic architecture

A direct radix-2 transform over Hachi's base field is unavailable for the required length because the modulus does not contain the necessary large power-of-two roots of unity.

Use auxiliary NTT-friendly primes.

## 6.1 Initial candidate primes

Start feasibility work with:

```text
p1 = 998244353
p2 = 1004535809
p3 = 469762049
```

Treat these as candidates until verified.

For each prime validate/prove:

```text
Nat.Prime pi
2048 ∣ (pi - 1)
chosen root has exact order 2048
inverse root is correct
2048 has the claimed modular inverse
stage roots/twiddles are correct
```

Their product is:

```text
P = 471064322751194440790966273
```

and exceeds the Hachi coefficient bound by a large margin.

If these primes create implementation/proof problems, the agent may choose different auxiliary primes provided all required properties and bounds are re-established.

## 6.2 Multiplication pipeline

For inputs `a,b` of length 1024:

1. read each coefficient as a nonnegative integer;
2. map into each auxiliary field;
3. zero-pad to length 2048;
4. forward NTT both inputs;
5. pointwise multiply;
6. inverse NTT;
7. obtain ordinary convolution coefficients modulo each auxiliary prime;
8. CRT-reconstruct each exact integer convolution coefficient;
9. for each `k < 1024`, compute the negacyclic fold:

```text
C[k] - C[1024+k]
```

10. reduce modulo Hachi's `q`;
11. construct the output `Rq`.

Because both inputs have degree `<1024`, their ordinary product has degree `<2048`; zero-padding to 2048 prevents cyclic wraparound inside the auxiliary transform.

## 6.3 Transform order

Prefer a proof-friendly scalar radix-2 architecture.

A DIF/DIT pair with a consistent bit-reversed spectral representation is a good default because it can avoid a separate bit-reversal pass.

Pointwise multiplication is compatible with the same permutation on both transformed inputs.

If another ordering yields substantially simpler Aeneas proofs, choose it and document it precisely.

## 6.4 Twiddles

Prefer:

- stage roots;
- or a deterministically generated twiddle table with a clear correctness rule.

Avoid:

- per-butterfly exponentiation;
- unexplained giant constant tables;
- opaque external code generation.

---

# 7. Verification-first Rust rules

Write V1 for Aeneas/Lean tractability.

Prefer:

- `u64` auxiliary residues;
- `u128` only where CRT/intermediate products require it;
- explicit `while` loops;
- simple indexing;
- concrete transform length;
- small helper functions;
- no unsafe code;
- no external NTT crate;
- no complex iterators/closures in the verified core;
- no unnecessary traits/generics;
- no SIMD.

For ~30-bit primes:

```text
a,b < p < 2^30
a*b < 2^60 < 2^64
```

so simple `u64` modular multiplication is viable for V1.

If a proof-friendly implementation is slightly slower than a clever one but still passes the performance gate, prefer the proof-friendly implementation.

---

# 8. Phase 0 — environment and baseline validation

## Goal

Establish that the clone is trustworthy and fully operable before changing code.

## 8.1 Environment check

Confirm availability of:

```text
git
cargo/rustup
Lean/elan/lake
python3
repository toolchain setup
Charon/Aeneas after setup
```

Use repository setup instructions rather than inventing another installation path.

If dependencies are already cached, do not unnecessarily reinstall them.

## 8.2 Baseline commands

Run the project's prescribed setup if needed:

```sh
make setup
```

Then:

```sh
make test
make extract
make build
make bench-check
```

Also run repository-specific integrity/spec checks if documented and cheap enough.

Inspect whether `make extract` unexpectedly modifies the generated model.

If a clean baseline cannot be reproduced, diagnose this before touching NTT code.

## 8.3 Record baseline

Record:

```text
baseline git SHA
Aeneas/Charon pin/version
Rust benchmark toolchain
Lean toolchain
test status
proof status
generated-model status
benchmark status
```

Run and record the existing multiplication benchmark using the repository harness.

Do not invent benchmark identifiers; discover them from the repo.

## Exit criteria

PASS only if:

- Rust tests are green;
- Lean build is green;
- no project `sorry`/`sorryAx`;
- extraction is reproducible/understood;
- benchmark baseline is recorded;
- working tree state is known.

Commit/report this milestone.

---

# 9. Phase 1 — algorithm feasibility spike

## Goal

Answer:

> Is scalar three-prime NTT/CRT multiplication sufficiently faster to justify formal verification?

Do this before expensive proof work.

Expected effort: ~3–5 days.

## 9.1 Preserve a test oracle

Keep the existing schoolbook semantics available for tests/benchmark comparison.

Git history is the ultimate reference, but a test-only local oracle is useful for differential testing.

Do not keep two production multipliers long-term.

## 9.2 Build an unverified prototype

Implement:

```text
3 auxiliary primes
2048 forward transforms
pointwise multiplication
2048 inverse transforms
CRT reconstruction
negacyclic fold
mod q
```

Do not replace production `Rq::mul` yet.

Use the repository's candidate benchmark mechanism if appropriate.

## 9.3 Correctness tests

For each auxiliary prime test:

```text
INTT(NTT(x)) = x
```

on:

- zero;
- basis vectors;
- all ones;
- maximal residues;
- alternating patterns;
- deterministic random vectors.

Test multiplication against the schoolbook oracle on:

- zero × zero;
- zero × arbitrary;
- one × arbitrary;
- monomial × monomial;
- wraparound monomials;
- all `q-1`;
- alternating coefficients;
- deterministic random inputs;
- a substantial number of differential cases.

Test CRT around:

- 0/1;
- each modulus boundary;
- pairwise product boundaries;
- the Hachi maximum convolution range.

## 9.4 Benchmark

Use the repository's benchmark harness.

Default economic target:

```text
Rq::mul speedup >= approximately 2×
```

Measure an end-to-end multiplication-heavy workload too if available.

## Gate decision

### PASS

Proceed if correctness is strong and performance is compelling.

### CONDITIONAL

For approximately 1.5–2× improvement:

- profile;
- permit a short bounded optimization attempt;
- target obvious allocation/reduction/CRT overhead;
- do not begin full proof work until benefit is convincing.

### FAIL/PIVOT

If the result is not materially faster:

- do not force the project forward;
- identify the dominant bottleneck;
- test only a bounded number of plausible alternatives;
- write a gate report.

If no credible proof-friendly route reaches worthwhile speedup, stop with evidence.

Commit the prototype/evidence.

---

# 10. Phase 2 — Aeneas vertical-slice gate

## Goal

Prove the chosen Rust implementation shape is tractable through extraction before implementing the whole verified NTT.

Expected effort: ~3–4 days.

## 10.1 Minimal verified slice

Implement production-shaped helpers:

```text
aux_add
aux_sub
aux_mul
butterfly
one complete NTT stage
small transform or miniature composition if useful
```

Use the same mutation/indexing architecture intended for the final transform.

## 10.2 Extract and inspect

Run:

```sh
make extract
```

Inspect generated Lean for:

- opacity;
- borrow/state complexity;
- unsupported constructs;
- tuple explosion;
- awkward bounds;
- difficult arithmetic translations.

## 10.3 Prove the slice

Prove:

```text
aux_add_spec
aux_sub_spec
aux_mul_spec
butterfly_spec
stage_spec
```

If useful, prove a small complete transform.

The proof target should be pure auxiliary arithmetic, not Hachi ring semantics.

## Gate decision

PASS only if:

- generated definitions are transparent enough;
- arithmetic totality is routine;
- indexing invariants are manageable;
- the stage invariant looks reusable;
- no new axioms are required.

If in-place mutation is proof-hostile, try:

1. simpler indexing;
2. simpler stage organization;
3. ping-pong/two-buffer transform;
4. internal representation redesign.

Do not weaken the public theorem.

Commit this checkpoint.

---

# 11. Phase 3 — pure auxiliary NTT mathematics

## Goal

Build a mathematical layer independent of generated Rust definitions.

Suggested logical organization:

```text
hachi/lean/NttMath/Params.lean
hachi/lean/NttMath/Arithmetic.lean
hachi/lean/NttMath/Butterfly.lean
hachi/lean/NttMath/Transform.lean
hachi/lean/NttMath/Convolution.lean
hachi/lean/NttMath/CRT.lean
```

Adapt names to repository style.

## 11.1 Parameter proofs

For each auxiliary modulus prove/check:

```text
primality
root exact order
inverse root
N inverse
stage roots/twiddles
```

## 11.2 Pure transform specification

Define exactly the transform the Rust implements.

Make explicit:

- length;
- ordering;
- stage structure;
- twiddle indexing;
- normalization;
- bit-reversal convention.

Avoid proving more generality than required.

## 11.3 Correctness

Prove sufficient forward/inverse correctness, including:

```text
INTT(NTT(a)) = a
```

for length 2048.

## 11.4 Convolution

Prove:

```text
INTT (NTT a ⊙ NTT b)
```

equals ordinary convolution modulo the auxiliary prime for zero-padded Hachi inputs.

Exploit:

```text
deg(a*b) <= 2046 < 2048
```

to eliminate cyclic wraparound.

## Exit criteria

- no `sorry`;
- complete forward/inverse theorem;
- complete convolution theorem;
- spec matches implementation architecture;
- no Hachi downstream theorem changed.

Commit this checkpoint.

---

# 12. Phase 4 — full extracted Rust NTT proof

## Goal

Connect production-shaped Rust helpers to the pure NTT theory.

Architecture:

```text
Rust helper
   |
Aeneas theorem
   |
representation bridge
   |
pure NttMath operation
```

## 12.1 Arithmetic

Prove canonicality and semantics of:

```text
aux_add
aux_sub
aux_mul
```

including overflow safety.

## 12.2 Butterfly

Prove one Rust butterfly implements the pure butterfly.

Keep this theorem local and reusable.

## 12.3 Stage

Use a loop invariant stating roughly:

- processed groups match the pure stage;
- unprocessed slots retain the input-stage value;
- residues remain canonical;
- all indices stay in range.

Avoid repeating modular identities inside the loop.

## 12.4 Full transforms

Compose stages to prove:

```text
Rust forward NTT = pure forward NTT
Rust inverse NTT = pure inverse NTT
```

Commit when the complete extracted transforms are proved.

---

# 13. Phase 5 — exact CRT reconstruction

## Goal

Turn the three modular convolution results into exact natural convolution coefficients.

## 13.1 Choose a proof-friendly reconstruction

Use `u128` where needed.

Calculate bounds for **every intermediate**, not only the final result.

If a direct CRT formula risks `u128` overflow, use staged/Garner reconstruction.

## 13.2 Pure CRT theorem

Prove:

```text
reconstruct(r1,r2,r3) < P
```

and:

```text
x < P
 ->
reconstruct(x mod p1, x mod p2, x mod p3) = x
```

## 13.3 Hachi range

Prove/reuse:

```text
ordinary convolution coefficient
 <= N * (q - 1)^2
 < P
```

Reuse current natural-sum bounds where helpful.

---

# 14. Phase 6 — connect exact convolution to existing Hachi semantics

This is a critical architectural constraint.

Do not invent a new public multiplication specification.

For every `k < N`, prove the relevant exact convolution coefficients correspond to the existing natural sums:

```text
exactConv[k] = posSum a b k N
exactConv[N+k] = negSum a b k N
```

or an equivalent formulation.

Then reuse the existing bridge lemmas:

```text
posSum_cast
negSum_cast
negConv_eq_sums
```

to prove the final coefficient equals:

```text
negConv a b k
```

The old **loop-specific** proof may become obsolete.

The old **semantic** lemmas should be retained and reused.

Commit when this bridge is complete.

---

# 15. Phase 7 — production switch

Only begin after prior gates are green.

## 15.1 Replace production `Rq::mul`

Update `hachi/src/ring.rs` to use the verified NTT/CRT pipeline.

Preserve public behavior/API.

Keep schoolbook multiplication test-only if retained at all.

## 15.2 Re-extract

Run:

```sh
make extract
```

Inspect the generated diff.

## 15.3 Re-prove `Ring.mul_spec`

The proof should conceptually be:

```text
Rust mul
 -> Rust NTT specs
 -> auxiliary convolution
 -> exact CRT
 -> posSum/negSum
 -> negConv_eq_sums
 -> existing postcondition
```

Delete implementation-specific schoolbook loop lemmas only if genuinely unused.

## 15.4 ArkLib preservation gate

Attempt the full build without editing `RqBridge.mul_spec`.

If it works unchanged, record this explicitly.

If it fails:

- distinguish import/name breakage from semantic failure;
- fix only mechanical breakage;
- stop/reassess on semantic mismatch.

Commit the production switch.

---

# 16. Phase 8 — full regression/proof campaign

Run at least:

```sh
make test
make extract
make build
make bench-check
```

Also run documented spec/coverage/axiom checks that apply.

Search changed proof code for accidental:

```text
sorry
admit
axiom
```

while distinguishing pre-existing upstream assumptions from newly introduced ones.

Run a large deterministic differential test campaign:

```text
NTT mul == schoolbook oracle
```

including edge cases.

---

# 17. Phase 9 — final benchmark campaign

Use only the repository benchmark methodology for claims.

Measure:

1. `Rq::mul`;
2. higher-level multiplication-heavy operations;
3. a representative end-to-end workflow if available.

Do not overinterpret cross-machine/cross-session raw timings.

The final verified implementation must remain materially faster than baseline.

If verification-friendly changes erase the feasibility-spike benefit, report that fact honestly.

A functional success with no worthwhile performance gain may be technically complete but should be classified as an optimization project failure.

---

# 18. Phase 10 — cleanup and maintainability

Remove:

- abandoned prototype implementations;
- duplicated constants;
- dead production schoolbook helpers;
- temporary debug output;
- duplicate proof lemmas;
- unused imports.

Document:

```text
auxiliary primes
roots
transform ordering
twiddle convention
CRT reconstruction
integer bounds
proof dependency chain
why direct base-field NTT is unavailable
```

State security scope accurately:

> The Lean/Aeneas proof establishes functional correctness. It does not, by itself, establish constant-time execution.

Review separately for:

- secret-dependent branches;
- secret-dependent memory access;
- data-dependent loop counts;
- variable-time helper functions.

---

# 19. Recommended commit/PR sequence

## 1. Baseline + feasibility

Production multiplication unchanged.

Contains:

- execution log;
- test oracle;
- prototype;
- correctness tests;
- performance evidence.

## 2. Aeneas vertical slice

Production multiplication unchanged.

Contains:

- auxiliary Rust arithmetic;
- butterfly/stage;
- extracted proof slice.

## 3. Pure NTT theory

Production multiplication unchanged.

Contains:

- parameter proofs;
- pure transform;
- inverse;
- convolution.

## 4. Full verified transforms

Production multiplication unchanged.

Contains:

- complete Rust forward/inverse;
- Aeneas proofs.

## 5. CRT + Hachi bridge

Production multiplication preferably still unchanged.

Contains:

- CRT;
- exact bounds;
- natural convolution bridge;
- `negConv` closure.

## 6. Production switch

Contains:

- new `Rq::mul`;
- new implementation proof;
- obsolete schoolbook proof cleanup;
- final docs/benchmarks.

Every intermediate commit should be as green as practical.

---

# 20. Risk register

## Scalar NTT is too slow

Discover in Phase 1. Do not sink proof effort into an economically poor implementation.

## In-place loops are proof-hostile

Discover in Phase 2. Simplify or use ping-pong buffers.

## Transform ordering becomes confusing

Document exact transform convention in the pure spec. Never leave permutation implicit.

## CRT intermediate overflow

Prove each intermediate. Switch to staged reconstruction if required.

## Generated Lean becomes fragile

Use small helpers and reusable stage proofs. Avoid gratuitous Rust abstraction.

## Root/twiddle errors

Machine-check constants and retain roundtrip tests.

## Proof compilation becomes too slow

Split modules, reduce giant simplification contexts, compose stage theorems instead of unfolding complete transforms repeatedly.

## Scope creep

Reject SIMD, persistent NTT storage, generic libraries, or unrelated refactors during V1 unless necessary to satisfy a hard gate.

## Downstream theorem churn

Treat as evidence that the abstraction boundary was violated. Fix the multiplication proof rather than patching consumers.

---

# 21. Gate summary

## Gate 0 — trustworthy baseline

Repository must start green.

## Gate 1 — algorithm economics

Prototype must be materially faster.

Default target:

```text
~2× Rq::mul speedup
```

## Gate 2 — Aeneas proof ergonomics

Butterfly/stage vertical slice must be tractable.

## Gate 3 — pure NTT math

Forward/inverse and convolution complete without `sorry`.

## Gate 4 — extracted transform correctness

Actual Rust forward/inverse refine the pure transform.

## Gate 5 — exact CRT

Range and all integer arithmetic proved.

## Gate 6 — Hachi semantics

New implementation closes to the existing `negConv`.

## Gate 7 — downstream preservation

`RqBridge.mul_spec` and downstream Hachi proofs remain valid.

## Gate 8 — verified performance

The fully verified implementation still earns the optimization.

---

# 22. Definition of done

## Rust

- [ ] Production `Rq::mul` uses NTT/CRT.
- [ ] Existing tests pass.
- [ ] NTT roundtrip tests pass.
- [ ] Differential multiplication tests pass.
- [ ] CRT boundary tests pass.
- [ ] No unjustified unsafe code.
- [ ] Test-only oracle is clearly separated from production.

## Extraction

- [ ] Final Rust extracts successfully.
- [ ] Toolchain pins remain coherent.
- [ ] Generated Lean corresponds to final Rust.

## Lean

- [ ] Auxiliary primes validated.
- [ ] Roots validated.
- [ ] Auxiliary arithmetic proved.
- [ ] Butterfly proved.
- [ ] Stage proved.
- [ ] Forward transform proved.
- [ ] Inverse transform proved.
- [ ] Convolution proved.
- [ ] CRT exactness proved.
- [ ] Integer overflow bounds proved.
- [ ] Bridge to `posSum`/`negSum` proved.
- [ ] Final result equals `negConv`.
- [ ] `Ring.mul_spec` keeps its previous semantic statement.
- [ ] `RqBridge.mul_spec` keeps its previous semantic statement.
- [ ] Downstream proofs build.
- [ ] No new `sorry`.
- [ ] No new unjustified axioms.

## Performance

- [ ] Baseline benchmark recorded.
- [ ] Prototype benchmark recorded.
- [ ] Final verified benchmark recorded.
- [ ] End-to-end effect recorded.
- [ ] Performance conclusions use repository methodology.

## Autonomous execution hygiene

- [ ] Baseline SHA recorded.
- [ ] Work occurred on isolated branch.
- [ ] Major gate commits exist.
- [ ] Gate reports exist.
- [ ] Final handoff report exists.
- [ ] Any failed/pivoted gates are documented.

---

# 23. Final handoff report

At completion, or if the project stops at a gate, append this to `logs/ntt-execution.md`:

```text
# Final NTT Project Handoff

Outcome:
COMPLETE | PARTIAL | STOPPED | PIVOT RECOMMENDED

Baseline commit:
<sha>

Final commit:
<sha>

Production algorithm:
<short description>

Theorem preservation:
- Ring.mul_spec statement unchanged: YES/NO
- RqBridge.mul_spec statement unchanged: YES/NO
- RqBridge.mul_spec proof text unchanged: YES/NO
- downstream proof regressions: <none/list>

Verification:
- make test:
- make extract:
- make build:
- sorry/axiom audit:
- other gates:

Performance:
- baseline Rq::mul:
- final Rq::mul:
- relative improvement:
- end-to-end effect:
- benchmark methodology:

Major design decisions:
- ...

Known limitations:
- ...

Deferred work:
- ...

If stopped:
- failed gate:
- evidence:
- recommended next experiment:

Files most relevant to review:
- ...

Commits most relevant to review:
- ...
```

Do not claim COMPLETE unless every definition-of-done item relevant to the project has been checked.

---

# 24. Effort model

Expected range for one strong engineer/agent already effective with Rust, Lean, Aeneas, and this repository:

```text
Phase 0 baseline                  1–2 days
Phase 1 feasibility              3–5 days
Phase 2 Aeneas vertical slice    3–4 days
Phase 3 pure NTT mathematics     6–9 days
Phase 4 extracted NTT proofs     9–14 days
Phase 5 CRT + bounds             4–7 days
Phase 6 Hachi semantic bridge    2–4 days
Phase 7 production integration   2–4 days
Phase 8–10 hardening             3–5 days
```

Base:

```text
~33–54 engineer-days
```

Planning range:

```text
P50: ~7–8 engineer-weeks
P80: ~10–12 engineer-weeks
```

Re-estimate after Gates 1 and 2 using actual evidence.

---

# 25. Reference formalizations

The strongest implementation-proof reference is Microsoft SymCrypt's verified ML-KEM NTT work using Rust → Charon → Aeneas → Lean.

Use it as a pattern for:

```text
implementation helper
 -> local step theorem
 -> representation bridge
 -> pure mathematical theorem
```

Do not blindly inherit:

- ML-KEM constants;
- Montgomery representation;
- incomplete-transform specifics;
- SIMD structure;
- assumptions tied to q=3329.

Generic Lean NTT developments may be consulted for roots of unity, inverse transforms, and Cooley–Tukey correctness.

Prefer adapting small proof ideas over adding a large dependency unless the dependency clearly reduces long-term maintenance cost.

---

# 26. Blocked-state protocol

When a proof fails:

1. classify the failure:
   - mathematical;
   - Rust shape;
   - Aeneas translation;
   - representation bridge;
   - arithmetic bound;
   - elaboration/automation;
2. reduce to the smallest failing helper;
3. prove/fix the local issue;
4. resume composition.

Do not change the public theorem because a local proof is hard.

When extraction fails:

1. simplify Rust;
2. avoid unsupported abstraction;
3. preserve behavior;
4. re-extract immediately.

When performance fails:

1. profile;
2. identify NTT arithmetic vs allocation vs CRT vs conversion vs memory traffic;
3. try only bounded proof-friendly fixes;
4. re-run the gate;
5. stop if the economics remain poor.

When stuck for a prolonged period, return to the last known-good checkpoint rather than layering speculative changes on a broken branch.

---

# 27. Final success criterion

Ideal final state:

```text
large diff: Rust multiplication implementation
substantial diff: Ring.lean implementation-specific proof
no semantic diff: Ring.mul_spec statement
no semantic diff: RqBridge.mul_spec
no downstream semantic repair
clean extraction/build
no new sorry/axioms
material benchmark improvement
```

The optimization is successful when the implementation changes substantially while the formal specification boundary does not.
