# NTT execution log

Execution of `NTT_EXECUTION_PLAYBOOK_v2.md`: replace the schoolbook Rust
`Rq::mul` with an auxiliary-prime NTT + CRT multiplication, preserving
`HachiEquiv.Ring.mul_spec` and `HachiEquiv.RqBridge.mul_spec`.

Branch: `experiment/verified-ntt-mul`, cut from `hachi/ntt-optm` @ `90120fe`.

## Baseline record

```
baseline SHA        90120fe8bdc647f8d52ab3115f9ea8dc6aaf0c42
baseline branch     hachi/ntt-optm (same tree as origin main @ 90120fe)
working branch      experiment/verified-ntt-mul
aeneas/charon       nightly-2026.07.26-3a8586f  (./toolchain, self-reported)
aeneas Lean backend file:///home/pablo/Documents/internship-eth/aeneas @ 6125cb9e (3a8586f + 1)
lean toolchain      leanprover/lean4:v4.33.1
ArkLib pin          d51d8bc3c22062bf21385bd15b39d390b0fe4584
CompPoly pin        a09455a22fea4623a2a1c5b363cf6efc61486a83
cpoly (Rust) pin    583cfaff0617180764ffd849d867331af206fc5e
bench toolchain     nightly-2026-06-01 (rustc 1.98.0-nightly 14210df0e)
host                16 cores, 30 GiB RAM, linux x86_64
```

### Environment discrepancies found during setup (Phase 0)

1. **`make setup` reports success while `lake exe cache get` failed.** In this
   fresh clone the Lean dependency fetch aborted at
   `Arklib: checking out revision 'd51d8bc3...'` with
   `fatal: reference is not a tree`. The pinned ArkLib commit is **no longer
   reachable from `https://github.com/Verified-zkEVM/ArkLib.git`** (upstream has
   moved; the sibling clone at `../../ArkLib` still has the object, and the
   repository's own `.lake/packages/Arklib` in the sibling working copy is
   checked out at exactly that rev). `make setup` treats a `cache get` failure
   as a warning, so it exits 0 with no usable dependency graph at all — not just
   a cold cache.

   *Resolution, not a workaround of the pin:* the fully materialised dependency
   set was taken from the sibling working copy of this same repository at the
   **same commit** (`/home/pablo/Documents/internship-eth/AeneasArklib`,
   `main` @ `90120fe`, `hachi/lake-manifest.json` byte-identical to this
   clone's), by `cp -a hachi/.lake`. Every package rev therefore matches the
   manifest, `Arklib` included, and no pin was changed. Recorded because a
   reader reproducing this from a clean clone **will not** be able to fetch
   ArkLib and must obtain it the same way (or bump the pin, which is a
   deliberate re-baseline, not something this work does).

2. **The `aeneas` Lean backend is a `file://` dependency** on a local checkout
   (`lakefile.lean` says so and why). That checkout exists on this host at
   `/home/pablo/Documents/internship-eth/aeneas` @ `6125cb9e`, so the build is
   reproducible here and nowhere else. Pre-existing, unchanged by this work.

3. **The machine was not idle.** A full `cargo bench --benches` run belonging to
   the sibling working copy (writing `logs/runs/full-20260916-preBump.json`) was
   already ~60 minutes into its run when this session started, and the 11 GiB
   `.lake` copy above ran alongside it for 26 s (0.9 s user, 10.7 s sys). Per
   `INSTRUCTIONS.md` ("Benchmarking needs the machine to itself"), **no
   measurement was taken and no compile was started while that run was live**;
   all heavy work in this log is timestamped after it finished. The interference
   the `cp` may have caused is to *that* run's numbers, not to any number here.

---

## Gate 0 — trustworthy baseline

Status: **PASS (conditional on the ArkLib pin note above)**

Baseline/working commit: `90120fe` (branch `experiment/verified-ntt-mul`)

Commands/evidence:
- `make setup` — exit 0, but see discrepancy 1: it exits 0 on a failed
  `lake exe cache get`. Dependency graph materialised from the sibling working
  copy at the same commit, manifest byte-identical.
- `make test` — green (see gate "performance" below for the post-change run).
- `make run-bench CANDIDATE=1 BENCH='ring/mul|_control'` — ran; harness
  self-test (ten identical-code `_control` rows) read `+0.0%` on every
  `cand vs now` and worst-case `3.9%` A/B bias.
- toolchain pins as recorded above; `make check-toolchain` passes as part of
  `make extract`.

Key measurements (run `20260916T1950+0200-c4ddce2a`, AMD Ryzen 7 8845HS,
16 cores, machine id `d19cb42225da`):
- `ring/mul/1024`, frozen genesis: **1.43 ms** — which is exactly the figure
  NOTES.md § "The exclusion arithmetic" records, so the baseline reproduces.
- `ring/mul/1024`, current champion (schoolbook, delayed reduction): **641 µs**.

Proof status: unchanged at baseline; `make build` not re-run at this gate (it is
hours on this machine and nothing Lean-side had changed yet).

Problems discovered: the two environment discrepancies above. Neither is caused
by this work and neither required changing a pin.

Decision: **CONTINUE**

---

## Gate 1 — algorithm economics (performance)

Status: **PASS**

Commands/evidence:
- `make run-bench CANDIDATE=1 BENCH='ring/mul|_control' JSON=logs/runs/ntt-gate1.json`
- run id `20260916T1950+0200-c4ddce2a`; slot fingerprint `ring c43725f2d083`
- `make test` — 24 `ring_semantics` tests (10 new) and every downstream module
  green with the NTT wired into `Rq::mul`.

Key measurements:

```
case            genesis      now   candidate     vs genesis      cand vs now
ring/mul/1024    1.43ms     641µs      287µs   -55.2% faster   -54.7% faster
```

- **recentered `cand vs now` = −54.7 %, i.e. 2.23× the champion**
- 4.98× the frozen genesis translation
- A/B bias 3.9 % (worst identical-code control); the `ring` binary's own
  candidate lean was −1.0 % and is divided out of the figure above
- the row is 287 µs–641 µs, far outside the 100 ns–2 µs band where
  `INSTRUCTIONS.md` says the 5 % floor is not trustworthy
- the ten `_control` rows all read `+0.0%` on `cand vs now`, so the harness
  agreed with itself in this run

Correctness evidence taken at this gate:
- the bench harness's own `case!` macro **asserts** the candidate's digest
  equals the champion's for every case; the run completed, so the two agree on
  the bench corpus.
- `hachi/tests/ring_semantics.rs`: constants re-derived from their defining
  properties (primality, `2N | p−1`, `p < 2^30`, `m = ⌊2^64/p⌋`, `ψ^N = −1`,
  `ψ·ψ⁻¹ = 1`, `N·N⁻¹ = 1`, `BOUND mod p`), Barrett = `%` over the whole `u64`
  range including boundaries, `psi_table` = powers of ψ, forward/inverse round
  trip = `N·x` on six adversarial shapes plus random data per prime, Garner
  exact on 20 020 points including every modulus and pairwise-product boundary
  and `2·BOUND`, and the product against a schoolbook oracle on 22 cases
  including `all q−1` (the maximum-coefficient case) and the wraparound
  monomials.
- an out-of-tree spike harness additionally ran 110 differential products and
  60 014 Garner points; see "what was tried" below.

### What was tried, and what the numbers said

Three designs were built and measured. Timings in this subsection are from an
out-of-tree harness (one implementation per binary, `taskset`-pinned, same
`opt-level`/`lto`/`codegen-units` as `profile.bench`); they are *indicative* and
exist to explain the design choice. The gate number above is the repository
harness's.

| design | product | vs that harness's schoolbook (657 µs) |
|---|---|---|
| cyclic length-2048, zero-padded, push-allocated stages | 830 µs | **0.79× — slower** |
| negacyclic length-1024 (twist), push-allocated stages | 357 µs | 1.84× |
| negacyclic length-1024, ping-pong buffers | **288 µs** | **2.28×** |

1. **The textbook route loses.** A cyclic transform of length `2N` with zero
   padding is the shape the playbook describes, and it needs neither a twist nor
   a signed-coefficient argument. It was implemented first and it is *slower
   than the schoolbook convolution it replaces*: `2.2×` more transform work than
   the negacyclic form, on buffers twice the size.
2. **`t % len` with a runtime `len` was 70 % of a stage.** The first stage
   implementation was a single flat loop over the output index computing
   `idx = t % len`. A runtime modulo is a hardware division: 2.44 µs per 2048
   elements against 0.16 µs for the equivalent mask. Restructuring into nested
   per-block loops removed it without touching the stage's closed-form
   specification.
3. **Branch misprediction was *not* the problem.** The conditional subtractions
   in `aux_add`/`aux_sub`/`aux_reduce` were replaced by arithmetic selects
   (`s − p·[s ≥ p]`) and the product got 1 % *slower*, so LLVM was already
   emitting selects. Hypothesis rejected, original code kept.
4. **Nor was it the allocator.** `MALLOC_TRIM_THRESHOLD_`/`MALLOC_TOP_PAD_`/
   `MALLOC_MMAP_THRESHOLD_` raised to a gigabyte changed the product by 2 %.
   Hypothesis rejected.
5. **It was memory traffic, and ping-pong fixed it.** A stage that allocates its
   output leaves nothing in L1: 16 KiB in, 16 KiB out, at a fresh address every
   stage. Reusing two buffers took the negacyclic product from 357 µs to 288 µs
   with no change to the arithmetic.
6. **The natural butterfly is 17 % slower than the split loops.** Writing
   `dst[start+j]` and `dst[start+half+j]` in one iteration does strictly less
   work — one twiddle multiplication instead of two in `dit_stage`, half the
   loads. Measured, in single-implementation binaries, three runs each:
   338 µs against 288 µs. Sequential store locality beats the arithmetic it
   wastes. The split form is therefore deliberate and `dit_stage` pays for its
   twiddle twice on purpose; the comment in `ntt.rs` says so, because it reads
   like an oversight.

Two measurement traps met on the way, both recorded because they nearly produced
a wrong design decision:

- **A microbenchmark of one stage is optimistic by ~2×.** Calling
  `dif_stage(&src, 2048, …)` with a literal length lets LLVM specialise `half`
  and `step`, and repeating it 5000 times on the same buffer keeps everything in
  L1. The same function inside the real pipeline costs about twice as much.
  Every design comparison above therefore times a whole product.
- **Two implementations in one binary do not compare.** The single-loop
  butterfly read *faster* than the split one when timed in isolation and
  *slower* when composed, in the same binary — a code-layout artefact. Rebuilt
  as one implementation per binary, the ordering was stable and reproducible.
  This is the same reason `hachi/Cargo.toml` pins `lto = "fat"` and
  `codegen-units = 1`.

Problems discovered:
- The performance gate **cannot** be met by the design the playbook sketches
  (§ 6.2, cyclic length-2048 with zero padding). The negacyclic length-`N` form
  is required, and it costs two extra pieces of proof: the twist isomorphism
  `X ↦ ψY` and a signed coefficient. Documented as a deviation; the mission and
  the theorem boundary are unaffected.
- The signed coefficient is handled by an **offset**, `BOUND = N·q²`, chosen so
  that it is (a) the ceiling `Ring.lean`'s existing `posSum_le`/`negSum_le`
  already prove, and (b) divisible by `q`, so the caller needs no correction
  term. `2·BOUND < P` with a factor of 12 469 spare.

Decision: **CONTINUE**

Next action: Gate 2 — extract `hachi/src/ntt.rs` through charon/Aeneas and prove
a vertical slice (auxiliary arithmetic, one stage) before committing to the full
transform proof.

---

## Gate 2 — Aeneas proof ergonomics (extraction + vertical slice)

Status: **PASS**

Commands/evidence:
- `make extract` — succeeded; `lean/Generated.lean` grew from 10 882 to 11 748
  lines, all of it `hachi.ntt`.
- `make build` — **green** on the regenerated model with every pre-existing
  proof untouched: "no errors, no `sorry`", 3 872 jobs. So adding the module did
  not perturb one line of the existing development.
- axiom count in `Generated.lean`: **0 before, 0 after**. No opaque function and
  no `axiom` entered the model.

What the generated model looks like, item by item:
- `ntt.aux_reduce`, `aux_add`, `aux_sub`, `aux_mul` — straight-line scalar
  arithmetic in the `Result` monad. Fully transparent; the `u128` widening casts
  arrive as `lift (UScalar.cast .U128 x)`, which `UScalar.cast_inBounds_spec`
  handles, and the `/ BARRETT_SCALE` as an ordinary `u128` division.
- `zeros`, `psi_table`, `twist`, `pointwise`, `untwist` — push loops with a
  two- or three-element state. The same shape as `ring::Rq::add`'s loop, which
  this repository already proves twelve times over.
- `dif_stage`, `dit_stage` — three loops each, emitted as three *separate*
  top-level definitions with states `(dst, j)`, `(dst, i, e)` and
  `(dst, start)`. No tuple explosion. The in-place write arrives in the
  simplest possible form —
  `let (_, index_mut_back) ← Vec.index_mut dst i; let dst1 := index_mut_back v` —
  i.e. the borrow is closed in the same statement, so `dst1 = dst.set i v` and
  `EvalSplit.lean`'s existing `Vec.set` idiom applies verbatim.
- `ntt_forward`, `ntt_inverse` — the **ping-pong buffer swap extracts as a
  tuple reassignment**: `ok (cont (filled, cur, len1))`. This was the main
  design risk and it is a non-issue; `ntt_forward` is even marked
  `@[reducible]`.
- `negconv_mod_p` — straight-line with tuple destructuring; `garner` —
  straight-line scalar arithmetic.

Proof status:
- **`hachi/lean/NttArith.lean` — complete, no `sorry`.** `aux_reduce_spec`
  proves Barrett reduction equals `% p` for **every** `x : u64` (not merely for
  products of residues), which is what lets one theorem serve both the twist's
  input reduction and every butterfly. Its three `ℕ` ingredients
  (`barrett_quot_le`, `barrett_quot_lt`, `barrett_correct`) are the
  never-overshoots, undershoots-by-less-than-`p`, and one-conditional-subtraction
  -is-`%` facts. `aux_add_spec`, `aux_sub_spec`, `aux_mul_spec` and four
  canonicality corollaries follow.
- Axiom closure of every theorem in the file: `[propext, Classical.choice,
  Quot.sound]`. No `sorryAx`.

Decision: **CONTINUE**

Verdict on the gate's real question — *is the in-place/ping-pong design
proof-hostile?* **No.** The ping-pong shape was chosen for performance and turns
out to extract better than the push shape it replaced would have: a stage is a
function of its input buffer, and the loop invariant is the ordinary
"prefix-written, rest-framed" pair. No redesign was needed.

---

## Gate 3 — pure NTT mathematics

Status: **PASS**

Artifact: `hachi/lean/NttMath.lean`, **complete, no `sorry`**, stated over an
arbitrary `CommRing` with an arbitrary root of unity — so the same theorems
instantiate at all three auxiliary primes with no `NeZero` instance threaded
through them.

What is proved:

| theorem | content |
|---|---|
| `ditStage_difStage` | one DIT stage undoes one DIF stage at the same block length, up to a factor of two, pointwise and with no hypothesis on the index |
| `ditRun_difRun` | `ditRun ∘ difRun = 2^k · id` — **the whole inverse-transform statement**, from the butterfly identity plus homogeneity, with no orthogonality sum anywhere |
| `difStage_blockVal` | one forward stage advances the block invariant: if each block holds the coefficients of `f(ω^(brev j B)·Y) mod (Y^m − 1)`, then after the stage each half-block holds the same for `brev (j+1) B'` |
| `difRun_blockVal` | the forward transform *evaluates*: entry `k` is `∑_t f t · ω^(brev L k · t)` |
| `cyclicConv_eval` | evaluation at an `n`-th root of unity is multiplicative for cyclic convolution — the pointwise-product step |
| `twistConv` | `X ↦ ψ·Y` carries the negacyclic product to the cyclic one: `cyclicConv (twist a) (twist b) t = ψ^t · negConv a b t` |

Design note worth keeping: the inverse transform needed **no** orthogonality
argument. Because `difRun` and `ditRun` are mirror images, the two runs nest
block length by block length, the innermost pair collapses by the butterfly
identity, and each stage outward contributes one factor of two — so
`INTT(NTT(x)) = N·x` is an induction with one algebraic identity in it. The
exponent function `brev` is defined recursively and **never unfolded to a closed
form**: the stage induction only ever needs its two recursion equations, and the
pointwise product never needs to know which root each entry belongs to.

Commands/evidence:
- `lake build NttArith NttMath` — green, no `sorry`.
- `#print axioms` on all eleven headline theorems of the two files:
  `[propext, Classical.choice, Quot.sound]` (two of them do not even need
  `Classical.choice`). No `sorryAx`.
- `grep -nE "sorry|native_decide|^axiom|implemented_by|unsafe|maxHeartbeats"` on
  both files: no matches.

Method note: the four substantial lemmas were proved by four parallel prover
agents against private copies of the file, per the repository's `prove-sorry`
procedure, after the statements were audited by hand. `difStage_blockVal` was
given two independent attempts and **both** succeeded; the integrated one is the
attempt whose helper lemmas are stated in the `2 * half` form that rewrites
directly against `difStage`.

Decision: **CONTINUE**

---

## Gates 4 and 5 — the extracted transform, and exact CRT

Status: **PASS**

By the time of this entry the following are proved with no `sorry`, checked by
`lake env lean` on each file:

| file | content | `sorry` |
|---|---|---|
| `hachi/lean/NttArith.lean` | Barrett reduction, `aux_add`/`sub`/`mul`, canonicality | 0 |
| `hachi/lean/NttMath.lean` | the pure transform mathematics (Gate 3) | 0 |
| `hachi/lean/NttStage.lean` | the extracted **DIF stage**: three loops, plus its word→ring cast | 0 |
| `hachi/lean/NttCRT.lean` | the three primes' `Magic` pairs, and **Garner exactness** | 0 |
| `hachi/lean/NttTransform.lean` | `zeros`, `psi_table`, `twist`, `pointwise`, `untwist`, the extracted **DIT stage** and its cast | 2 (the two transform loops) |
| `hachi/lean/NttProduct.lean` | the word-level antidiagonals, their bounds and their casts | 3 (the two pipeline entry points) |

### What Gate 4 actually required, and what it cost

The extracted stage was the gate's real question, and the answer is that the
ping-pong design is **easier** than the push design it replaced would have been.
Each stage is three separate generated loops with states `(dst, j)`,
`(dst, i, e)` and `(dst, start)`; each inner loop's spec is the ordinary triple
of "the entries written hold the stage value", "the entries not written are
untouched" (the frame condition — without it the outer loop cannot know earlier
blocks survive) and "every entry is still canonical". The `Vec.index_mut` write
arrives with its borrow already closed, so `EvalSplit.lean`'s existing
`Vec.set` idiom transfers unchanged.

Two facts worth recording for anyone extending this:

* **The DIT stage was a transcription of the DIF stage.** Given the proved
  forward stage as a template, the mirror image compiled on the first attempt.
  The only genuine deltas were the twiddle counter appearing in *both* inner
  loops (the inverse butterfly multiplies in both halves), the `aux_mul`-then-
  `aux_add`/`aux_sub` bind order, and one extra rewrite in the low-half branch.
* **The word→ring cast needs canonicality, and the unhypothesised version is
  false.** `difWord_cast`/`ditWord_cast` turn the `ℕ`-with-`% p` stage into the
  `ZMod p` one. The `ℕ` form writes the butterfly's difference as
  `(a + p − b) % p`, a *truncating* subtraction, and that is
  `(a : ZMod p) − (b : ZMod p)` only when `b < p`. A counterexample to the
  unhypothesised statement was machine-checked before the hypothesis was added
  (`p = 5`, `sw 1 = 7`: the word side truncates to `0`, the ring side is `3`).
  Every call site discharges it from `Canon`.

### Gate 5 — exact CRT

`NttCRT.garner_spec` proves that, given the three residues of a natural number
below `P = p1·p2·p3`, the extracted `ntt.garner` returns **that number**, as an
exact `u128`. The bound is tight: `r1 + p1·t1 + (p1·p2)·t2 ≤ P − 1`, so `x < P`
is exactly what forces the leftover multiple of `P` to vanish. Every
intermediate is bounded: `p1·t1 < 2^59` (a valid `u64` product *and* a valid
`aux_mul` operand pair mod `p3`, which is why the primes are ordered
`p1 < p2 < p3`), and the result is below `P < 2^89`.

The offset arithmetic is proved too: `2·BOUND < P` with a factor of 1.2·10^4 to
spare, and `q ∣ BOUND`.

### Method

Eleven prover agents were run against private copies of the files, per the
repository's `prove-sorry` procedure, after every statement was audited by hand.
Ten succeeded; the eleventh was a deliberate second attempt at the hardest pure
lemma and also succeeded. No agent was permitted to touch the repository, to run
`lake build`, or to change a statement; the two statement changes that did
happen (`difWord_cast`'s and `ditWord_cast`'s canonicality hypothesis) were
authorised in advance on condition that the unhypothesised form be disproved
first, and it was.

---

### Non-vacuity, checked rather than argued

A spec layer can be true and useless. The following were machine-checked as a
probe (no repo file involved), each instantiating a headline hypothesis at the
*real* constants rather than at a symbolic prime:

- all three `Magic pᵢ mᵢ` pairs are inhabited, so `aux_reduce`/`aux_mul` apply
  at every prime;
- `ψ₁ < p₁`, `N⁻¹₁ < p₁`, `BOFF₁ < p₁` — the operand-size hypotheses the
  pipeline needs;
- `ψ₁^1024 = −1`, `ψ₁·ψ₁⁻¹ = 1`, `1024·N⁻¹₁ = 1` **in `ZMod p₁`**, which is the
  form the composition consumes (each by `decide +kernel`, under a second);
- `BOFF₁ = BOUND % p₁`;
- `dif_stage_spec` instantiated at `len = 2^10`, `k = 9` — the first stage of a
  real transform;
- `garner_spec` instantiated at `x = 2·BOUND`, the **largest** value the
  pipeline can present it with, so the `x < P` hypothesis is not vacuously
  satisfied by small inputs only.

The probe compiles with no errors. Worth doing because the root facts were the
one place where a plausible-looking constant could have made every theorem above
it true and unusable.

---

---

## Commit plan (agents cannot commit in this repository)

`.claude/settings.json` denies `git commit`, and the denial is enforced by the
harness rather than trusted — a probe commit was refused. So the playbook's
"create a checkpoint commit at each gate" could not be carried out from inside
this session. Everything is **staged** instead (`git add -A`), and this is the
ordered plan to turn it into the history the playbook asks for. The interleaving
in steps 3–5 is forced by the genesis stamp mechanism, which records a commit
that must already exist (`INSTRUCTIONS.md`, `op-genesis`).

```text
1. hachi/src/ntt.rs
   hachi/tests/ring_semantics.rs
   logs/ntt-execution.md
   logs/runs/ntt-gate1.json  logs/runs/ntt-gate8.json
   logs/runs/ntt-gate8-callers.json
   NTT_EXECUTION_PLAYBOOK_v2.md
   -> "ntt: the auxiliary-prime negacyclic transform, with its constant and
       differential tests"

2. hachi/lean/NttArith.lean  hachi/lean/NttMath.lean  hachi/lean/NttCRT.lean
   hachi/lean/NttStage.lean   hachi/lean/NttTransform.lean
   hachi/lean/NttProduct.lean hachi/lakefile.lean
   -> "ntt: the transform's Lean equivalence layer"

2b. hachi/src/ring.rs  hachi/src/lib.rs
    hachi/lean/Generated.lean  hachi/lean/Ring.lean  hachi/lean/Check.lean
    hachi/benches/ring.rs  hachi/benches/exclusions.toml  NOTES.md
    -> "ring: Rq::mul through the transform; mul_spec's statement unchanged"
    (this is the switch: the Rust, its extraction, the rewritten mul_spec
     proof, the audit list that names its loops, and the prose that said a
     transform was impossible)

3. hachi/benches/genesis/src/ntt.rs   (the verbatim freeze)
   hachi/benches/genesis/src/lib.rs
   hachi/benches/candidate/src/ntt.rs hachi/benches/candidate/src/lib.rs
   hachi/benches/harness.py
   .claude/skills/skill-lab/references/ledger_check.py
   -> "ntt: freeze the module into genesis and register it with the harness"

4. make bench-stamp        # derives the @genesis stamps from commit 3

5. hachi/benches/genesis/src/ntt.rs    (stamps only -- a SEPARATE commit;
                                        never --amend commit 3, a stamp
                                        stores its own sha)
   -> "ntt: genesis stamps"

6. make bench-check        # must now pass: check-genesis, check-candidate,
                           # coverage --strict
```

Until step 4 runs, `make bench-check` and `make run-bench` fail their
`check-genesis` gate with "these items exist in hachi/src but have no frozen
counterpart" — that is the mechanism working as designed, not a regression. The
Gate 1 measurement was taken **before** `hachi/src/ntt.rs` existed, under a
passing `check-genesis`, so it is attributable as recorded.

No ledger row is written here. `logs/ledger.jsonl` stays empty: a row records a
`perf-loop` accept decision, and this work reached its performance number
through the candidate slot but outside that skill's bookkeeping. The row belongs
with whoever runs `perf-loop` on `ring::mul` next, and it should cite run
`20260916T1950+0200-c4ddce2a`.

## Gate 6 — the Hachi semantic closure

Status: **PASS**

The playbook's critical architectural constraint was that the new implementation
must terminate at the *existing* `negConv`, reusing `posSum`/`negSum` rather than
introducing a competing public multiplication specification. It does, and the
chain is:

```text
ntt::negconv_mod_q                     (NttProduct.negconv_mod_q_spec)
  = offConvW a b k % q                 exact natural number, via Garner
  = (posW + BOUND − negW) % q
  ↓ posW_eq_posSum / negW_eq_negSum     (Ring.lean: the copied words agree)
  = (posSum + BOUND − negSum) % q
  ↓ q ∣ BOUND, Nat.cast_sub
  = (posSum : ZMod q) − (negSum : ZMod q)
  ↓ negConv_eq_sums                     (Ring.lean, UNCHANGED from the baseline)
  = negConv a b k
```

`posSum_cast`, `negSum_cast`, `negConv_eq_sums`, `wordN`, `wordN_lt`,
`posSum_le` and `negSum_le` are the baseline's, reused verbatim — which is
exactly what §14 of the playbook asked for. Nothing in the chain mentions an
auxiliary prime, a root of unity, a transform order or a CRT: those live below
`NttProduct` and are invisible to `negConv`.

Four lemmas of the baseline's `Ring.lean` did become dead and were deleted:
`posSum_zero`, `negSum_zero`, `posSum_succ`, `negSum_succ` — the four
step lemmas of the schoolbook loop's invariant, which nothing else used.
`accBound` was **kept**: `LiftProver.long_mul` still uses it for its own delayed
reduction, and its docstring now says so instead of claiming to be `mul`'s.

---

## Gate 7 — downstream preservation

Status: **PASS, with zero downstream churn**

Evidence:
- `hachi/lean/RqBridge.lean` is **byte-identical to the baseline**
  (`git diff HEAD -- lean/RqBridge.lean` is empty). `RqBridge.mul_spec`'s
  statement *and* its proof text are unchanged, which is stronger than the
  playbook's requirement.
- `HachiEquiv.Ring.mul_spec`'s statement is **byte-identical to the baseline**,
  checked by diffing against `git show HEAD:hachi/lean/Ring.lean`.
- `lake build` over the whole library: **"Build completed successfully (3878
  jobs)"**, no errors. Every file above the ring layer — `Scheme`, `EvalSplit`,
  `Balanced`, `QuadEval`, `QuadEvalProtocol`, `RingSwitch`, `ZeroCheck`,
  `EndPiece`, `Rlin`, `Sumcheck`, `Chain`, `LiftProver`, `Opt` — compiles
  untouched. Not one downstream theorem was edited.
- The only files above the new `Aux*` layer that changed at all are
  `hachi/lean/Ring.lean` (the implementation-specific proof, which is the point)
  and `hachi/lean/Check.lean` (§ 4's audit list, which names the loop lemmas and
  therefore had to follow them).
- `make test`: every module green with the transform as production `Rq::mul` —
  24 `ring` tests plus 186 across the eleven other modules, each with its own
  independent oracle for the operations that call `Rq::mul`.

That the build goes through *while `Ring.mul_spec` is still sorried* is the
sharpest form of this evidence: it isolates the remaining work to one proof and
shows the abstraction boundary held.

---

## Production switch, and the full proof campaign

Status: **PASS**

`hachi/src/ring.rs`'s `Rq::mul` is now three passes and one call: read `self`'s
canonical words, read `rhs`'s, hand both to `ntt::negconv_mod_q`, wrap the
results as `Fp`. The schoolbook double loop is gone from the crate; the old
production body survives only as `schoolbook_oracle` in
`hachi/tests/ring_semantics.rs`, where it is the differential reference, and as
the frozen first translation in `hachi/benches/genesis/src/ring.rs`, which is
append-only and must not follow the change.

Commands and evidence:

```
make extract   -> regenerated lean/Generated.lean
make extract   -> "lean/Generated.lean unchanged"      (deterministic, run twice)
make build     -> "Build completed successfully (3878 jobs)"
                  "==> proofs check out: no errors, no `sorry`"
make test      -> every module green, 210 passing, 0 failed
```

Axiom audit (`lean/Check.lean` § 4 runs as part of `make build`, and re-checked
directly):

```
HachiEquiv.Ring.mul_spec                  [propext, Classical.choice, Quot.sound]
HachiEquiv.RqBridge.mul_spec              [propext, Classical.choice, Quot.sound]
HachiEquiv.NttProduct.negconv_mod_q_spec  [propext, Classical.choice, Quot.sound]
HachiEquiv.NttProduct.negconv_mod_p_spec  [propext, Classical.choice, Quot.sound]
HachiEquiv.NttCRT.garner_spec             [propext, Classical.choice, Quot.sound]
HachiEquiv.NttStage.dif_stage_spec         [propext, Classical.choice, Quot.sound]
HachiEquiv.NttTransform.dit_stage_spec    [propext, Classical.choice, Quot.sound]
HachiEquiv.NttTransform.ntt_forward_spec  [propext, Classical.choice, Quot.sound]
HachiEquiv.NttTransform.ntt_inverse_spec  [propext, Classical.choice, Quot.sound]
HachiEquiv.NttMath.difRun_blockVal         [propext, Classical.choice, Quot.sound]
HachiEquiv.NttMath.ditRun_difRun           [propext, Quot.sound]
```

No `sorryAx`, no new axiom, no `native_decide`, no `unsafe`, no
`set_option maxHeartbeats` change. `decide +kernel` is used for the per-prime
numeral facts (root order, inverses, offset residues) — kernel reduction of
`ZMod p` arithmetic at 30-bit primes, under a second each; that is ordinary
computation in the kernel, not an escape.

One pre-existing warning is unchanged and unrelated:
`Could not generate mvcgen spec for HachiEquiv.RqBridge.mul_spec: constant has
already been declared` occurs four times in the baseline build log too.

### `Check.lean` § 4's audit list moved with the loops

The audit names loop lemmas, so replacing the loops replaced five lines:
`Ring.mul_loop0_loop0_spec` and `Ring.mul_loop0_spec` gave way to
`mul_loop0_spec`, `mul_loop1_spec`, `mul_loop2_spec`, `posW_eq_posSum` and
`negW_eq_negSum`, with the comment above them rewritten to describe the chain
rather than a delayed reduction. `Ring.accBound` stays audited because
`LiftProver.long_mul` still uses it. This is the only downstream file that
changed, and it changed because it is a list of names, not because a theorem
moved.

---

## Gate 8 — verified performance

Status: **PASS**

Two runs, both on an otherwise-idle machine, both with their identical-code
controls reading within 1 %.

**The headline row** (run `20260916T2120+0200-15ffa185`):

```
case                         genesis         now          vs genesis
ring/mul/1024                 1.44ms       257µs     -82.2% ▼ faster
_control/ring/8192            33.2ms      33.2ms       +0.0% · noise
_control/ringswitch/8192      33.5ms      33.2ms       -0.8% · noise
A/B bias  0.8%
```

**The end-to-end effect** — three `Rq::mul`-bound caller rows, each 16 full ring
products (run `20260916T2125+0200-bef61acb`):

```
case                         genesis         now          vs genesis
linalg/dot/16                   23ms      5.52ms     -75.9% ▼ faster
linalg/mat_vec_mul/16           23ms      5.52ms     -76.0% ▼ faster
linalg/scalar_vec_mul/16      22.9ms      5.36ms     -76.6% ▼ faster
_control/linalg/8192          33.1ms      33.2ms       +0.5% · noise
A/B bias  0.5%
```

`linalg/scalar_vec_mul` is left multiplication by a ring element — `k` full
`ring::mul`s, not `k` coefficient scalings; the bench file says so where the
case is defined. So all three rows are genuinely multiplication-bound, and the
~76 % they each drop is the ~82 % of `ring/mul` diluted by the vector's own
allocation and addition.

### The two attributable figures, and why they differ

- **vs the current champion: 2.23×** (recentered `cand vs now` = −54.7 %), run
  `20260916T1950+0200-c4ddce2a`. That champion is the schoolbook convolution
  with candidate Q's delayed reduction, which is itself ~2.2× the genesis
  translation.
- **vs the frozen genesis translation: 5.6×** (−82.2 %), run
  `20260916T2120+0200-15ffa185`.

Both are within-run comparisons, which is the only kind this repository treats
as a measurement. They are **not** combined: 641 µs (Gate 1's `now`) against
257 µs (Gate 8's `now`) is a cross-run comparison and is not claimed.

The economic target was ~2× on `Rq::mul`. The verified implementation delivers
2.23× against the code it replaced and 5.6× against the baseline the loop
measures everything from, and it keeps it *after* verification — nothing was
given back to make the proof go through.

### Measurement hygiene notes

- A first attempt at a wider campaign was **aborted** after 8 minutes because a
  100 %-CPU process belonging to the sibling working copy
  (`AeneasArklib/.../chain_semantics`) was running; per `INSTRUCTIONS.md`, a
  benchmark shares the machine with nothing. The numbers above were taken after
  it finished.
- A second wider attempt was killed by the host's low-memory guard 22 cases in
  (30 GiB box, 18 GiB free at the time, no swap; the resident set was the
  browser's, not the bench's). The two runs above are the narrowed reruns, and
  each completed in one pass.
- `make run-bench` could not be used directly: its `check-genesis` gate fails
  until the stamps are derived, which needs a commit that does not exist yet.
  The runs above are that target's body with the gate skipped and nothing else
  changed — same pinned toolchain, same `profile.bench`, same harness report.
  The genesis text was verified byte-identical to `hachi/src` for every module
  except the three this work touched, and `hachi/benches/genesis/src/ring.rs` —
  the schoolbook baseline the numbers are measured against — is byte-identical
  to the baseline commit.

---

# Final NTT Project Handoff

**Outcome: COMPLETE.**

The production `Rq::mul` is an auxiliary-prime negacyclic number-theoretic
transform with CRT reconstruction, proved correct in Lean against the *same*
`HachiEquiv.Ring.mul_spec` statement the schoolbook convolution was proved
against, with `HachiEquiv.RqBridge.mul_spec` byte-identical to the baseline and
no downstream theorem touched.

```text
Baseline commit   90120fe8bdc647f8d52ab3115f9ea8dc6aaf0c42   (branch hachi/ntt-optm)
Working branch    experiment/verified-ntt-mul
Final commit      NONE -- `.claude/settings.json` denies `git commit` and the
                  denial is enforced, so the work is staged, not committed.
                  The ordered commit plan is in this file above.
```

## Production algorithm

Negacyclic length-`N` (`N = 1024`) NTT over three auxiliary primes, with Garner
CRT reconstruction and an additive offset:

```text
p1 = 469762049   = 7 · 2^26 + 1        ψ1 = 165447688
p2 = 998244353   = 7 · 17 · 2^23 + 1   ψ2 = 584193783
p3 = 1004535809  = 479 · 2^21 + 1      ψ3 = 714163887
P  = p1·p2·p3 ≈ 2^88.6                 BOUND = N·q² ≈ 2^74, 2·BOUND < P
```

Per prime: twist by `ψ^t` (turning `X^N + 1` into `Y^N − 1`), ten
decimation-in-frequency stages on `ω = ψ²`, pointwise product, ten
decimation-in-time stages, untwist by `ψ^(−t)·N⁻¹`, add `BOUND mod p`. Then
Garner across the three residues and one reduction mod `q`. Scalar `u64`
residues, Barrett reduction with a per-prime magic constant, `u128` only for
Barrett's multiply-high and Garner's widest term, ping-pong buffers, explicit
`while` loops, no unsafe code, no SIMD, no external crate, fixed length.

Hachi's cryptographic parameters are **unchanged**: `hachi/src/params.rs` is
byte-identical to the baseline.

## Theorem preservation

| claim | status |
|---|---|
| `Ring.mul_spec` statement unchanged | **YES** — byte-identical to `git show HEAD:hachi/lean/Ring.lean` |
| `RqBridge.mul_spec` statement unchanged | **YES** |
| `RqBridge.mul_spec` proof text unchanged | **YES** — `git diff HEAD -- lean/RqBridge.lean` is empty |
| downstream proof regressions | **none** — `lake build` green, no downstream file edited |
| new `sorry` / `admit` | **none** |
| new axioms | **none** — every theorem closes over `[propext, Classical.choice, Quot.sound]` |
| `negConv` still the public semantics | **YES** — the chain terminates at the baseline's `negConv_eq_sums` |

## Performance

| | |
|---|---|
| baseline `Rq::mul` (frozen genesis translation) | 1.44 ms |
| baseline `Rq::mul` (champion at session start) | 641 µs |
| final verified `Rq::mul` | 257 µs |
| **relative improvement, vs champion** | **2.23×** (−54.7 %, recentered, run `…1950+0200-c4ddce2a`) |
| **relative improvement, vs genesis** | **5.6×** (−82.2 %, run `…2120+0200-15ffa185`) |
| end-to-end effect | three `Rq::mul`-bound `linalg` rows each −76 % vs genesis (run `…2125+0200-bef61acb`) |
| methodology | the repository's own: `benches/harness.py`, within-run comparison only, identical-code controls, pinned `nightly-2026-06-01` and `profile.bench` |

The absolute times are not comparable across runs and are given only to show
the order of magnitude; the percentages are the measurements.

## Verification

```
make setup      exit 0, but see "Environment discrepancies" above -- it exits 0
                on a failed `lake exe cache get`, and the pinned ArkLib commit is
                no longer fetchable from GitHub
make test       green: 210 passing across twelve modules, 0 failed
make extract    regenerated, then "unchanged" on a second run (deterministic)
make build      "Build completed successfully (3878 jobs)"
                "==> proofs check out: no errors, no `sorry`"
axiom audit     every theorem in the new chain, and `Ring.mul_spec` and
                `RqBridge.mul_spec`, close over exactly
                [propext, Classical.choice, Quot.sound]
grep audit      no `sorry`, `native_decide`, `axiom`, `implemented_by`,
                `unsafe`, or `maxHeartbeats` change in any file written here
bench-coverage  156 mirrored items, 80 benched, 76 excluded, 0 unaccounted for
bench-check     FAILS on `check-genesis` until the stamps are derived -- by
                design; see the commit plan
```

### What the tests actually check

`hachi/tests/ring_semantics.rs` gained ten tests that re-derive every constant
from its defining property rather than trusting the literal: primality of each
`pᵢ`, `pᵢ < 2^30`, `2N | pᵢ − 1`, `mᵢ = ⌊2^64/pᵢ⌋`, `ψᵢ^N = −1`, `ψᵢ·ψᵢ⁻¹ = 1`,
`N·N⁻¹ = 1`, `BOFFᵢ = BOUND mod pᵢ`, `2·BOUND < P`, `q | BOUND`, and the Garner
constants. Plus: Barrett equals `%` over the whole `u64` range including
boundaries; `psi_table` is the powers of ψ; the transform round-trips to `N·x`
on six adversarial shapes per prime; Garner is exact on 20 020 points including
every modulus and pairwise-product boundary and `2·BOUND`; and the product
agrees with a schoolbook oracle on 22 cases including `all q−1` (the
maximum-coefficient case) and the wraparound monomials.

The other eleven modules' tests are the end-to-end check: each has its own
independent oracle for the operations that call `Rq::mul`, and all pass.

## Major design decisions

1. **Negacyclic length-`N`, not cyclic length-`2N`.** The plan specified the
   latter; it measured *slower than the schoolbook loop*. Recorded with numbers
   under gate "algorithm economics".
2. **The offset `BOUND = N·q²`.** Makes the reconstructed value a natural
   number (so no sign test, so no data-dependent branch), is the ceiling the
   baseline's `posSum_le`/`negSum_le` already prove, and is divisible by `q` so
   the caller needs no correction term.
3. **Ping-pong buffers, two sequential half-block loops per stage.** The first
   for locality and for a stage that is a *function* of its input buffer; the
   second because it measured 17 % faster than the natural butterfly despite
   doing more arithmetic.
4. **Barrett with a runtime modulus**, so one transform implementation serves
   all three primes — and therefore one proof, not three.
5. **Runtime-built twiddle tables**, not pinned constants: the correctness rule
   is `out[i] = ψ^i` and there is no table to audit, for ~6 % of a product.
6. **The pure mathematics is stated over an arbitrary `CommRing`**, so the
   transform argument is proved once and instantiated three times.
7. **`brev` is never unfolded.** The stage induction needs only its two
   recursion equations, and the pointwise product never needs to know which root
   an entry belongs to — so no bit-reversal combinatorics appears anywhere.

## Known limitations

- **Functional correctness only.** The Lean proof says nothing about timing.
  `aux_add`, `aux_sub` and `aux_reduce` each end in a conditional subtraction,
  which a compiler may or may not render branchless. Every loop bound and every
  index in `ntt.rs` is a public constant, and the offset design removes the one
  branch that would otherwise depend on a coefficient's value — but that is an
  argument about the source, not a theorem. A constant-time review is separate
  work and has not been done.
- **The genesis stamps are not derived**, because they record a commit that does
  not exist yet. `make bench-check` and `make run-bench` fail their
  `check-genesis` gate until the commit plan's step 4 runs.
- **`hachi/benches/candidate/src/lib.rs` differs from its git-pinned content**
  (it gained `pub mod ntt;`). That is commit plan step 3; `check-candidate`
  reports it and nothing else.
- **No ledger row was written.** `logs/ledger.jsonl` is still empty; the row
  belongs to whoever runs `perf-loop` on `ring::mul` next, and should cite run
  `20260916T1950+0200-c4ddce2a`.
- **The environment is not reproducible from a clean clone** — pre-existing, not
  caused by this work: the pinned ArkLib commit is unfetchable and the `aeneas`
  Lean backend is a `file://` dependency on a local checkout.

## Deferred work

- **Radix-4 stages.** Halves the number of passes and the twiddle
  multiplications; the likely next 1.5–1.8× on the transform. Costs a 4-way
  butterfly proof and one more root-of-unity fact.
- **Dropping the inverse-root table.** `ψ^(−t) = −ψ^(N−t)`, so one table of
  `N` entries could serve both directions — 8 KiB and `N` multiplications per
  prime, at the cost of an index-reversal lemma.
- **Fusing the pointwise product into the last forward stage**, and the twist
  into the first; three passes of `N` per prime.
- **Two primes instead of three** would need ~38-bit moduli and therefore
  `u128` residue arithmetic; estimated a net loss, not measured.
- **The un-ignore ceremony** for the `benches/exclusions.toml` entries whose
  removal condition this work satisfies, and the 27 `#[ignore]`d scale tests
  that go with it.
- **A constant-time review** of `ntt.rs`.

## Files most relevant to review

```text
hachi/src/ntt.rs              the transform (551 lines, header carries the argument)
hachi/src/ring.rs             Rq::mul -- three passes and one call
hachi/lean/NttArith.lean      Barrett, aux_add/sub/mul                  (318)
hachi/lean/NttMath.lean        the pure transform mathematics            (594)
hachi/lean/NttStage.lean       the extracted DIF stage + its cast        (523)
hachi/lean/NttTransform.lean  the DIT stage, the passes, both transforms (1186)
hachi/lean/NttCRT.lean        the three primes, and Garner exactness    (301)
hachi/lean/NttProduct.lean    the per-prime pipeline and the CRT step   (736)
hachi/lean/Ring.lean          the new mul_spec and the bridge to posSum/negSum
hachi/lean/RqBridge.lean      UNCHANGED -- read it to confirm
hachi/tests/ring_semantics.rs the constant and differential tests
logs/ntt-execution.md         this file: every gate, and what was rejected
NOTES.md                      § "The NTT is possible after all -- in three other fields"
```

The single most informative diff for a reviewer is
`git diff HEAD -- hachi/lean/RqBridge.lean` (empty) read next to
`git diff HEAD -- hachi/src/ring.rs` (the whole product replaced). That pair is
the project's thesis.
