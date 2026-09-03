# Plan: Rust generation + verification of the Hachi protocol layer, on merged ArkLib main

Status: **updated 2026-09-03 — re-pinned to ArkLib PR #847 head `d51d8bc`
(τ = 5, `BoundedDigitDecomposition`, balanced digits as *the* gadget
inverse), `make build` green after three proof-internal repairs; Decision 4
revised (⊕⊕); Stage 2's record committed (`68620ed`), its scoping tables
still to be re-based on the new pin.** Below this line the text is the
2026-09-01 revision — the parallel-track
structure below is from the 2026-08-31 evening revision, which re-grounded
the plan in a file-level audit of the pinned tree (`294b3f0b0`, then
upstream `main`'s tip) and restructured the schedule around an explicit
dependency graph. Corrections to the morning revision are marked **⟲**;
corrections from Stage 2's own audits are marked **⊕** and carry their
evidence in `STAGE2_SCOPING.md`, which is Stage 2's output document.

Where things stand: the Fig. 9 params flip is committed and stamped
(`af05e6c` + `0de99fa`); **Stage 1 is CLOSED** — commit `6f30811`, with the
extract formality clean on it (`make extract` `unchanged`, 0 axioms,
`make build` green, `Check.lean` § 4 intact); Stage 0's one live remainder
is the bench commit and the first measurement-grade bench, both USR-gated;
**Stage 2 is running** — three of its five audits are folded into
`STAGE2_SCOPING.md`, and Decisions 3 and 4 are audit-confirmed. Read the
whole file before starting any stage: the stages are ordered to make
failures attributable and each has an exit criterion.

## Context

`lib.rs` § Status records why the protocol layer (QuadEval fold, ring
switching, zero-check, sumcheck, final evaluation) is absent: its ArkLib
specification had unfilled definitional parameters, so there was nothing
stable to be equivalent *to*. The `feat/hachi-completeness` stack closed most
of that gap: #782 (merge sha `f06e28ed3`), #808 (digit decomposition,
`a39339136`), #813 (`294b3f0b0`, proof-search hotspots). This repo pins
`294b3f0b0`.

Three facts shape the schedule:

1. **The toolchain diverged at the merge — resolved the same day.** We did
   the 4.33 bump ourselves: commit `6125cb9e` ("bump to 4.33") in the sibling
   `../aeneas` checkout, one commit on top of upstream `3a8586f` — exactly
   the `AENEAS_TAG` commit the pinned extraction binaries are built from.
   Backend builds clean on v4.33.1, the regenerated `ExtractBuiltinLean.ml`
   is semantically identical to upstream's, so the pinned nightly release
   binary and the charon pin stay valid and `Generated.lean` did not
   regenerate. **Drift note (checked 2026-08-31):** upstream Aeneas `main`
   has moved 64 commits past `3a8586f` and is *still on Lean v4.31.0* — no
   upstream 4.33 release is coming soon, so our port stays load-bearing for
   the whole horizon. Two of those upstream commits bump charon: a future
   rebase would force rebuilding the extraction binaries, so the pin does
   not move casually (see Decision 2).
2. **The per-op cost is calibrated, not guessed.** `evalsplit` — a mid-size
   op — took ~2 days end-to-end (onboarded + genesis 08-26, proved 08-26,
   promoted 08-27). The whole bottom layer (5 modules, scaffold included)
   took ~10 days. Protocol links are individually comparable to `evalsplit`;
   zero-check and sumcheck are bigger (re-sized below from the audit).
3. **Recursion is not spec-stable, and it is detached.** ⟲ The audit counts
   **13** code-level sorries, not 3 (see Ground truth). The saving grace:
   `Composition.lean` does not import `Recursion/` — the composed chain ends
   at `relWEvalClaim` and closes with `endPiece`, and `Recursion/Basic.lean`'s
   own docstring says the adapters "are not currently composed into
   `Composition.lean`". The recursive tail is out of scope *and* structurally
   severable.

## Ground truth at the pin (file-level audit, 2026-08-31)

Everything below was read from the checkout at
`hachi/.lake/packages/Arklib/ArkLib/Commitments/Functional/Hachi/` (45 Lean
files) and the pinned CompPoly. These are the facts the stages below build
on; anything that contradicts them later means the pin moved.

* **Sorries: 13, in 4 files.** ⟲ `Recursion/PartialEval.lean` (6: the defs
  `partialEvalAt`, `eqWeight`, `deriveFamily`, `partialEvalExtractor` and
  the theorems `wTableMleEval_split`,
  `partialEval_coordinateWiseSpecialSoundWith`),
  `Recursion/TraceHandoff.lean` (4: `traceCheck`,
  `toNextQuadEvalStatement`, `handoffExtractor`,
  `handoff_coordinateWiseSpecialSoundWith`), `Recursion/ZBatchBridge.lean`
  (2: `hatEval`, `mem_relPartialEval_of_relHatEval`) — and **one outside
  `Recursion/`**: `Commitment.lean:199`, the recursive scheme instance's
  field `hachi.opening := sorry`, whose docstring warns the field's *type*
  will change when it lands. Two of the Recursion sorries are documented in
  their own docstrings as more than unproven: the sorry at
  `TraceHandoff.lean:238` is "not merely unproven but **false**" as stated
  (docstring at :210 — "a gap in the *design*"), and the one at
  `ZBatchBridge.lean:117` is "expected to be **unprovable** as stated"
  (:42, :105–106) — so the eventual fills will churn protocol content, not
  just proofs. Consequence: nothing we
  state may go through the `Commitment.hachi` object (Decision 1).
* **The composed chain uses balanced digits.** `HonestChain.lean:350–351`
  instantiates the message and z decompositions at
  `balancedZmodDigitDecomposition`; `Correctness.lean:384` does the same in
  the nonrecursive chain's correctness proof. Our proved commitment layer
  (`Scheme.lean`) targets the *unsigned* `zmodDigitDecomposition 16 8` —
  still present and green at the pin, because `InnerOuter/Scheme.lean` is
  decomposition-generic (`ddMsg`/`ddInner` arguments). ⟲ So #808 did not
  "resolve" the params.rs caveat by itself: it made the balanced machinery
  *available*, and the composed path *requires* it. See Decision 4.
* **No Ext4 anywhere in ArkLib's Hachi.** ⟲ The extension field enters as a
  free `φF : ZMod q →+* F` parameter; nothing in ArkLib instantiates it.
  What exists at the pin: CompPoly's `Fields/Hachi.lean` (the Hachi prime
  field, `fieldSize = 2^32 − 99` — exactly our `Q` — with a `Field`
  instance) and `Fields/Hachi/Ext4.lean` (`Ext4` with the framework `Field`
  instance via irreducibility facts). Of the Hachi chain's typeclass row on
  F: `DecidableEq` and `BEq` are provided generically on `Ext`
  (`Fields/Extension/Defs.lean:282–284`, conditional on the base field's,
  which `ZMod q` supplies); **missing at the pin: `LawfulBEq (Ext P)`**
  (likely a one-liner via the same `inferInstanceAs (… (Vector F P.d))`
  route — `Ext` is a `def`, so Vector's instances don't auto-apply) **and
  `SampleableType`** (an ArkLib/VCVio-side class, absent from CompPoly
  entirely). Choosing F is ours to do: Decision 3.
* **`scripts/HachiRuntime.lean` exists** (463 lines, in the ArkLib package):
  a *compiled, executable* honest run of the nonrecursive chain at toy
  parameters, self-described as "the executability half of the Aeneas
  extraction target: `hachiNonrecursiveConcrete` … is what the Rust
  implementation is meant to agree with". It instantiates the degenerate
  `F = ZMod q` and runs in ~6 minutes single-core at `m₀ = 5` — dominated by
  `computableRoundPoly`, independently confirming where Stage 6's second
  elephant lives. It is the single best reference for Stage 2's API mapping
  and for Stage 3's translation targets.
* **Unfilled-but-not-sorried on the honest path** (these become explicit
  inputs of the Rust API, not constants): the Ajtai lift key `D` is
  caller-supplied all the way through `Concrete.lean` (`hachiLiftCom`'s
  docstring: "a full treatment would sample it in `keygen`"); the fold
  challenge sampler is carried as an undischarged
  `[SampleableType (ShortChallenge …)]` hypothesis (`Composition.lean:196`).
  Neither blocks per-link equivalence — challenges and keys are inputs to
  public-coin verifiers — but Stage 2 must write the API consequence down.
* **Upstream `sorryAx` taint, outside Hachi:** every *composed* completeness
  theorem (`hachiNonrecursive*_perfectCorrectness`) inherits `sorryAx` from
  ArkLib's generic `Reduction.append_completeness`
  (`OracleReduction/Composition/Sequential/Append.lean`, 11 sorries, plus
  `LiftContext/Reduction.lean`). The soundness-side composition is claimed
  clean. Our obligations are equivalence-to-*definitions*, so this taints
  ArkLib's meta-theorems, not our specs — but Stage 7's write-up must state
  precisely which side of that line every claim sits on.
* **Import spine of the protocol modules** (intra-Hachi only, bottom-up):
  `Gadget/Core → Gadget/Norms → InnerOuter/* → QuadEval/Gadgets →
  QuadEval/Reduction`; `RingSwitch/RhoDigits` (needs only `Gadget/Norms`) →
  `RingSwitch/Reduction` (also pulls `Rlin → QuadEval/Reduction`) →
  `ZeroCheck/Constraints → Batch → Reduction` → `Sumcheck/{Bridge,
  RoundPoly} → Rounds → FinalEval` → {`Sumcheck/Completeness`,
  `EndPiece/Reduction`}. `EvalSplit` is a leaf feeding only
  `QuadEval/Bridge` (already onboarded). This graph is what Stage 3's
  ordering and parallel pairs are read off of.
* **Sumcheck shape (the desk check, half-answered):** the protocol
  *scaffolding* is dependently typed — `roundsSpec` and `roundsChainAux`
  are structural recursions on the round count, the latter returning a
  subtype carrying its own relation invariant; `RoundMsg` is a pair of
  degree-bounded subtypes; the round statement type changes shape each round
  (`Fin.snoc` on a `Fin i → F` prefix). None of that is what we translate.
  The *computational content* is: `computableRoundPoly`
  (`Sumcheck/RoundPoly.lean:286`, a sum over `Fin k → Fin 2` Boolean tails
  → a `0..2^k` counter loop), `roundCheck`, `finalCheck` (three `&&`/`==`
  conjuncts), `wTable`/`wTableMleEval` (`ZeroCheck/Constraints.lean:140/348`,
  a `dite` index split → a branch on `idx / d`), `hypercubeSum`, and
  `balancedDigit` via `Nat.digits`+`getD` (same proof pattern as the
  already-proved unsigned `digit_at`). Stage 2 turns this list into the
  erasure catalogue; the extraction-probe escalation stays reserved for
  constructs with no precedent (the only candidate so far: nothing — every
  shape above has one).

## Decision points (settle before the affected stage)

1. **Recursion scope** (before Stage 2) — **out of scope**, now stronger:
   13 sorries, two false-as-stated, and the tail is not even composed at the
   pin. Additional rule the audit adds: no spec may mention
   `Commitment.hachi` (its `opening` field is sorried and its *type* will
   change). Revisit only on a deliberate re-pin after `Recursion/` is
   sorry-free.
2. **Aeneas 4.33 strategy** — **settled 2026-08-31**. Two residual actions:
   (a) **publish the port** — push `6125cb9e` to a public fork (~30 min,
   user's GitHub; the lakefile then moves only the URL, keeping the rev pin
   — its comment says how). Until then the `file://` require reproduces
   only on this machine. Parallel to everything; do it whenever.
   (b) **drift policy**: upstream is 64 commits ahead with two charon bumps;
   a rebase implies rebuilding the release binaries and re-baselining the
   extraction — that is a project decision with its own verify-campaign,
   never maintenance. Trigger to even consider it: an extraction bug on a
   protocol-layer construct that upstream has fixed.
3. **The concrete extension field F** (before Stage 3's target 4) — ⊕
   **audit-confirmed 2026-09-01, and cheaper than costed**: every
   definition we translate demands only `Field F`, `BEq F`, `LawfulBEq F`
   (plus `DecidableEq F` for `roundCheck`/`roundOut`/`honestComputeG`);
   `SampleableType` is confirmed **avoidable** — it appears only in
   extractors, escape events, `coreSpecSampleable`, HonestChain/Correctness
   executions and keygen, none of which we translate. The one syntactic
   exception, `honestComputeY` (`FinalEval.lean:254`), inherits it by
   section-variable accident and has `wTableMleEval` as its body. The
   missing `LawfulBEq (Ext P)` is a *verified* one-liner: `Ext`'s BEq
   instance is literally the Vector one (`Defs.lean:284`) and Lean v4.33.1
   core ships `LawfulBEq (Vector α n)`. And φF already exists finished —
   `Ext.ofBaseRingHom` (`Extension/Bridge.lean:354–359`) with its RingHom
   laws, `Algebra` instance and coefficient lemmas proved; injectivity, the
   only extra fact any site wants, is free via `RingHom.injective`. Keep
   the `fieldSize` spelling, never the numeral. Details and the TE work
   list: `STAGE2_SCOPING.md` § Decision 3. Original recommendation, now
   ratified — **`Ext4` from CompPoly's `Fields/Hachi`**: same base
   prime (verified: `2^32 − 99`), the paper's k = 4, and the only choice
   that makes soundness non-degenerate and the protocol spans comparable to
   the reference. Cost, known exactly: provide the two instances missing at
   the pin (`LawfulBEq (Ext P)`, probably a one-liner; `SampleableType`,
   which Stage 2 audits — it may be demanded only by ArkLib's sampling
   layer, not by anything we translate) and an Ext4 bridge, RqBridge-shaped,
   relating the
   extracted `cpoly` Ext4 to CompPoly's `Ext4` (the Rust side already
   extracts — the Workstream 0 probe stands while the `cpoly` rev is
   pinned). Fallback `F = ZMod q` (HachiRuntime's choice) is **rejected for
   the deliverable** — degenerate soundness, non-comparable spans — and
   acceptable only as a temporary scaffold behind an explicit plan revision.
4. **Balanced digits: add alongside, don't flip** (before Stage 3's target
   1) — the composed chain needs `balancedZmodDigitDecomposition`; our 74
   proved specs target the unsigned instantiation. Flipping `gadget.rs`
   would invalidate them and buy a regeneration campaign for nothing.
   Instead target 1 *adds* the balanced layer the chain actually uses
   (`balancedDigit`/`balancedShift`, balanced message/z decomposition
   siblings at the `gadget.rs`/`commit.rs` seam, `rhoDigits`), keeping the
   unsigned layer as the proved bottom story. Stage 2 determines the minimal
   balanced surface (starting guesses to verify: a balanced `digit_at`
   sibling; a balanced `generate_decomps` sibling; `commit_with_decomps`
   may already be decomposition-agnostic since decomps are data). The
   params.rs:28–39 "not paper-faithful" caveat is then *superseded by a
   precise statement*: the protocol chain is balanced (paper-faithful); the
   standalone unsigned instantiation remains as the proved bottom layer.
   ⊕ **Audited 2026-09-01, all three guesses confirmed and the surface is
   smaller than feared**: `balancedDigit` is `unsigned digit ∘ (+shift) −
   b/2`, equal to the bundled `.digit` **by `rfl`**
   (`RhoDigits.lean:86–89`), so the Rust sibling is a 3-line wrapper over
   the proved `digit_at` and its spec reuses `digit_at_spec`. The one
   thing the guesses missed is the middle layer — `generate_decomps`
   hardcodes `gadget_decompose`, which hardcodes `digit_at` — so the real
   work is one mechanical `balanced_gadget_decompose` copy.
   `commit_with_decomps` is confirmed decomposition-agnostic. No existing
   spec is edited; `verify_weak_spec` needs no sibling. One new const,
   `BALANCED_SHIFT = 0x88888888`. Full surface: `STAGE2_SCOPING.md`
   § Decision 4.
   ⊕⊕ **Revised 2026-09-03 — "add alongside" stays, "don't flip" goes: the
   balanced functions become the public API.** ArkLib PR #847 (head
   `d51d8bc`, the new pin) re-labels the unsigned `zmodDigitDecomposition`
   as "the building block the balanced digits are shifted from, not itself a
   Hachi gadget inverse", renames `commitBalanced` → `commit` (the unsigned
   committer is deleted), and drops the unsigned norm lemmas
   (`zmodDigit_natAbs_le`, `gadgetDecompose_zmod_vecLInftyNorm_le`,
   `…_vecL2NormSq_le`) and `gadgetDecompose_apply`. The user's call: adapt
   to that design. So target 1 is a *promotion*, not a sibling layer: the
   balanced digit map and decomposition take the `gadget_decompose` /
   `generate_decomps` / `commit` names (matching `Hachi.commit`), and the
   proved unsigned `digit_at` becomes the primitive they are built from —
   exactly upstream's structure. The 74 specs are untouched in content
   (the unsigned instantiation still exists upstream; the three proof
   sites that cited deleted lemmas were repaired at the re-pin with a
   local `dd_digit_natAbs_le` and ArkLib's surviving `…_of_digit_le`
   forms). What the promotion costs beyond the sibling plan is a rename
   pass and re-pointing the headline `commit_spec` at the balanced
   committer; what it buys is that Stage 5's composed `commit` *is* the
   spec's `commit`, with no "which committer" footnote. The z side is
   separate again: `boundedBalancedZmodDigit` at `τ = 5` (centre, shift by
   `8·69905`, five digits) is target 1's second new function, and its
   `gadget_*` siblings at `Z_DIGITS = 5 ≠ GADGET_DIGITS = 8` are target 2's.
5. **Stage 6 budget** — by the calendar (internship end), not target
   speedup. Unchanged.
6. **Multiplication champion timing** (new) — **recommend running route-r3
   on `ring::mul` as the first perf-loop, immediately after T0**, not parked
   in Stage 6. Grounds: `benches/exclusions.toml`'s 11 scheme-level
   exclusions and the 17 `#[ignore]`d scale tests (10 in
   `commit_semantics.rs` — one fewer since the βSq correction retired the
   overlong-message witness, 7 in `evalsplit_semantics.rs`) all name "a
   sub-quadratic
   `ring::mul` champion" as their removal condition; every protocol op's
   test/bench feasibility gates on the same thing; and it is the largest
   single span gap vs the reference (≈36 µs NTT-based vs ~2–4 ms schoolbook
   at d = 1024). Candidates per the catalogue: Karatsuba/Toom or convolution
   split (`opt-algo-swap`, provable), `opt-word-arith` stacking. A radix-2
   NTT is impossible at this q (NOTES.md § "The parameters forbid a radix-2
   NTT"); the reference's multi-prime NTT is a CRT construction whose
   equivalence proof is a much bigger lift — record it as the known ceiling
   on closing the mul gap, not a candidate for this pass. Honesty note for
   later: a ~20× Karatsuba champion still leaves full-scale `commit` at
   ~minutes per criterion iteration, so the exclusions' removal condition
   will need *revising* (reduced-shape cases return, full-scale may stay
   excluded) rather than deleting — decide that when the champion's factor
   is measured, not now.

## Dependencies and parallel tracks

Resource classes — what actually serializes:

* **MX** (machine-exclusive): measurement-grade bench runs. One power/thermal
  condition set, nothing else heavy concurrently — the `logs/paper-impl`
  lesson (a discarded morning block, ~2× drift) is the rule, not an
  anecdote.
* **MH** (machine-heavy, serialize among themselves): `lake build`,
  `make extract`, `cargo test --release -- --ignored`.
* **DW** (desk work, parallelizes with everything): reading, briefs, spec
  drafting, Rust drafting, plan/docs.
* **RM** (remote): Aristotle sessions, agent fan-outs. Free parallelism.
* **USR** (user-only): every commit (`.claude/settings.json` denies
  `git commit` — enforced), plus decisions. The stamp mechanics interleave
  commits (translation+freeze commit, then stamp commit, never `--amend`),
  so each freeze is a two-touch user interaction — batch them.

The tracks, with their blocking edges:

| Track | What | Needs | Blocks | Class |
|---|---|---|---|---|
| **T0** | Stage 1 commit → extract formality → bench commit (+ `ledger_check.py` rider) → first measurement-grade bench | USR | every freeze, TM, Stage 3 births | USR+MH+MX |
| **TS2** | Stage 2 audit/briefs/desk-check (its params.rs extension lands only after T0's extract formality) | nothing — **start now** | Stage 3 order, Decisions 3–4 | DW |
| **TF** | publish the aeneas port to a public fork | USR (~30 min) | nothing (removes Risk 1 residual) | USR |
| **TM** | `ring::mul` champion, route-r3 + K=1 verify-campaign | T0 | nothing hard; relieves every scale wall | DW+MX+RM |
| **T1…T6** | Stage 3 op-genesis wave (edges below) | T0, TS2; T4+ also Decision 3 | Stage 5 | DW+MH+MX+USR |
| **TE** | Ext4 layer: missing instances + the cpoly↔CompPoly bridge | Decision 3 | T4–T6 *specs* (not their Rust drafts) | DW+RM |
| **T-proofs** | Stage 4 pipeline, one op behind genesis | each op's freeze | Stage 5 | DW+RM |

Op-genesis edges (from the import spine and the Rust seams):
**{T1 ∥ T2} → T3 → T4 → {T5 ∥ T6}.** T2's honest `zDecomp`/`carrierDecomp`
instantiate at the balanced decomposition, so T2 drafts in parallel with T1
and closes that thin seam at freeze time. T3 (`hachiLiftCom` =
`Simple.commit ∘ liftMessage`) needs T1's `rhoDigits`. T4's `wTable` needs
T3's digit block *and* F. T6 (`endPieceCheck`) needs T3's `liftShortCheck`
and T4's `wTableMleEval` but **not T5** — the end piece and the sumcheck
rounds parallelize.

What "parallel" honestly means here: one laptop, one user committing. Desk
and remote work overlap machine slots and commit batches; benches never
overlap anything. A realistic steady state is: one op's Rust being drafted
(DW), the previous op's proofs running (RM + DW), TM's next candidate
benching in a reserved MX slot, TS2/TE items filling gaps.

## Stages

### Stage 0 — Pre-merge work (done except the bench)

* **Fig. 9 stamp dance: done.** `af05e6c` + `0de99fa` (106 annotations,
  `make bench-check` green).
* **First measurement-grade local bench: the one live remainder.** The bench
  adaptations sit uncommitted (Fig. 9 sizes in `gadget.rs`/`linalg.rs`, the
  REDUCED dense-`G` and `ring::mul`-bound cases with policy notes, the
  `logs/paper-impl/` exception in `logs/README.md`); `logs/ledger.jsonl` is
  empty. Run **after** T0's toolchain commit so rows record a real sha.
  Rider: the uncommitted `ledger_check.py` MODULES sync (`evalsplit` added,
  matching `harness.py`) belongs in this bench commit, not the toolchain
  one. Whole ladder in one condition set. ~0.5–1 day.
* Extraction-ceiling probes and provisional briefs: cut (recorded in the
  previous revision; the desk check moved to Stage 2 and is now largely
  pre-answered — see Ground truth).

Exit: params flip committed and stamped (done); ledger non-empty (open).

### Stage 1 — Pin bump + toolchain re-alignment — DONE locally (uncommitted)

Budgeted 4–9 days; actual ~1 day because `Generated.lean` did not regenerate
(binaries and charon pin stayed valid). The drift bill was two Lean-side
repairs: scoped `set_option maxRecDepth 4096 in` on RqBridge's primality
instance and Scheme's three norm specs, and `verify_weak_spec`'s
`decide_eq_true`/`of_decide_eq_true` conversion (v4.33 simp re-checks
Decidable instances inside `decide`). Remaining, all mechanical (~0.5 day):

* Commit the working tree: `lakefile.lean` + `lake-manifest.json` +
  `lean-toolchain` together (the NOTES.md invariant) with the RqBridge/Scheme
  repairs, as its own commit — separate from the bench work (Risk 5).
  Optional rider while the tree is open: a NOTES.md superseding entry for
  § "Upstream aeneas, no fork" (that section's title is now false; the
  lakefile comment carries the truth, NOTES should point at it).
* Re-run `make extract` + determinism check on the committed state — the
  formality confirming `Generated.lean` is a fixpoint under the port. Do
  this **before** Stage 2's params.rs extension lands, so any diff is
  attributable to the port alone.

Exit unchanged: `lake build` green (4153 jobs — already holds), `Check.lean`
§ 4 intact, axiom-clean, extraction deterministic, all *as a commit*.

### Stage 2 — Audit + scoping (2–3 days) — IN PROGRESS

⊕ **Output document: `STAGE2_SCOPING.md`.** All five audits below are
complete and folded in as of 2026-09-01; what remains is the six
`arklib-analyze` briefs, the params.rs extension (bench-commit-gated), and
one house-discipline exception line. The five audits produced four
corrections to this plan (marked ⊕ in their sections) and one contradiction
between two audits, resolved by direct check — recorded there.

Grown from 1–2 days: the audit above answered its old questions and asked
better ones. Items, each with its consumer named:

* **Spec-stability record** → NOTES.md: the 13 sorries and the
  `Commitment.hachi` rule (Decision 1), the balanced-on-the-composed-path
  fact (Decision 4), the upstream `sorryAx` line (Stage 7's honesty
  paragraph), the D-and-sampler-as-inputs facts (the Rust API).
* **Decision 3 instance audit** → TE's work list: which of
  `BEq`/`LawfulBEq`/`DecidableEq`/`SampleableType` on `Ext4` are demanded by
  *translated* definitions vs only by ArkLib's sampling/security layer; what
  `φF` concretely is for `Ext4` (the base embedding of the extension
  framework) and whether `RingHom` facts about it are stated or ours to
  state.
* **Decision 4 minimal surface** → T1's brief: enumerate exactly which
  balanced siblings `gadget.rs`/`commit.rs` need for the composed chain
  (starting guesses in Decision 4), and which existing specs stay untouched
  (target: all 74).
* **Parameter mapping** → params.rs extension: `HonestRangeParams`'s
  `(b, γ, bZero)` and the digit counts (`messageDigits`, `zDigits`,
  `rhoDigitCount q b = Nat.clog b q`) mapped onto Fig. 9's `n_D`/matrix `D`
  shape, the `z` bound 30583, `c = 16`, `τ = 4`, plus `m₀`/`m₁` (the
  zero-check/sumcheck round split) — literal-not-derived discipline, with
  `tests/params_semantics.rs` and `Check.lean` § 1 entries. Land after T0's
  extract formality; this extension regenerates `Generated.lean`
  *additively* — gate: the diff touches only new `params.*` definitions.
  ⊕ **Audited: 16–18 new consts, values resolved.** The paper-faithful
  point is `ofPinnedDigitBase 16` = (b, γ, bZero) = **(16, 15, 16)**;
  m₀ = **27**, m₁ = **3**; μ₀ = 81920, n₀ = 5, lift width 81960.
  Three corrections the mapping forces: (i) ⊗ **there is only one τ, and
  it is `zDigits` = 8 — `BETA_SQ` included.** (This clause first read
  "τ = 4 is correct only inside the weak-opening `BETA_SQ`; do not
  reconcile them". That was wrong, and the stamped `BETA_SQ` literal was
  wrong with it.) τ is a *formal parameter* of `quadEvalBetaSq`
  (`QuadEval/Soundness.lean:106`), and every instantiation in the Hachi
  tree passes `zDigits` into that slot — none passes a literal 4;
  `hqz : q ≤ b^zDigits` is false at 4 (16⁴ = 65536 ≪ q), so τ = 4 is not
  instantiable in this formalization, and `QuadEval/Gadgets.lean:123`
  ("`zDigits = τ`") equates the names rather than preserving a separate
  paper value. Consequence: **no `TAU` const** — it would be a third name
  for 8. The corrected `BETA_SQ` is staged in the tree by a parallel
  working session, with its own NOTES.md entry.
  (ii) the chain's γ = **15** is a different quantity from the
  existing `GAMMA = 16` (weak-opening γ̄ = b) — name it `CHAIN_GAMMA`.
  (iii) **two constants have no ArkLib expression at all** (`Z_BOUND`,
  `CHALLENGE_WEIGHT` — paper/reference-impl provenance only) and two have
  no closed form (`M_ZERO`, `M_ONE` — ArkLib leaves them free under
  inequalities), so the house rule "Check.lean proves the literal equals
  the ArkLib expression" gets a recorded exception for four rows. Value
  **16** now collides five ways. Table: `STAGE2_SCOPING.md` § Parameter
  mapping.
* **API mapping from `HachiRuntime.lean`** → Stage 3/5 signatures: walk
  `hachiNonrecursiveConcrete`'s argument list and record what the Rust
  entry points take as inputs (D, challenge streams) vs read from
  `params.rs`.
* **Erasure catalogue** (the desk check, consuming the Ground-truth shape
  list) → Stage 3 briefs: per translated definition, the erasure it needs
  (subtype → vector + runtime check; `Fin k → Fin 2` sum → `0..2^k` loop;
  `Fin.snoc` → push; `Nat.digits` → running-quotient loop; `dite` index
  split → branch) and the proof precedent it maps to. Escalate to a
  throwaway probe only for a shape with no precedent — none is currently on
  the list. ⊕ **Audited, and "none" was wrong once**: `CMvPolynomial n F`
  as a *runtime value* (a `Std.ExtTreeMap` monomial dictionary) has no
  precedent anywhere in `hachi/src` or cpoly's Rust and is almost
  certainly above the ceiling. It is reached by `hypercubeSum`,
  `computableRoundPoly`, `honestComputeG`, `sumcheckPolyZero`/`Alpha` and
  both of `finalCheck`'s eval subterms. **Resolution is an opt, not a
  probe**: every runtime use is an evaluation, the factoring lemmas exist
  at the pin, and the dense-table rewrite lands on cpoly's proved MLE
  toolkit — so the Stage 6 rewrite moves forward into Stage 3 as a
  prerequisite for targets 4–5. Four smaller corrections (`roundCheck` has
  two conjuncts not three; `wTable`'s split is two-level; `honestComputeG`
  is in `Sumcheck/Completeness.lean`; the Eq. 20 checks are in
  `QuadEval/Reduction.lean`), one unlisted prerequisite (`hAlpha` is
  `noncomputable` at the pin — a computable sibling is needed first,
  bridging lemmas present), and one large win (cpoly's Ext4 + MLE toolkit
  already covers targets 4–6's evaluation needs, proved). Catalogue:
  `STAGE2_SCOPING.md` § Erasure catalogue.
* **Ordered target list + one `arklib-analyze` brief per target**, sized and
  scale-policied: each brief decides *at brief time* which semantics tests
  and bench cases run at real consts vs REDUCED vs excluded/ignored
  (extending the Fig. 9 policy the bottom layer already carries), so no
  freeze-day surprises.
* **Doc-sync list** (cheap, do during the wave): `lib.rs` § Status's "still
  has unfilled definitional parameters" sentence is stale post-merge;
  params.rs:28–39 caveat per Decision 4; `exclusions.toml`'s "19 consts"
  header when params grow; NOTES.md entries above.

Exit: ordered, dependency-closed target list with briefs and scale policies;
Decisions 3–4 settled with the user; params.rs extended, its checks green,
extraction diff params-only; NOTES.md records the audit.

### Stage 3 — Op-genesis wave (8–12 days of work, pipelined with Stage 4)

One `/op-genesis` per target. ⟲ Table re-grounded in the audit — sources,
dependency edges, and two size corrections:

| # | Target | ArkLib source (at the pin) | Rust home | Needs | Size vs `evalsplit` |
|---|---|---|---|---|---|
| 1 | balanced digit layer: `balancedDigit`/`balancedShift`, `rhoDigits`/`rhoDigitCount`, balanced message/z decompose siblings, `DigitBaseOk` side conditions | `RingSwitch/RhoDigits.lean`, `Gadget/`, `HonestChain.lean` | extends `gadget.rs` (+ `commit.rs` seam) | — | **similar** (⟲ was "smaller"; it now carries the composed chain's decomposition, Decision 4) |
| 2 | QuadEval fold link: carrier algebra (`carrierEntry/carrier/carrierDecomp/carrierCommit`, `jMatrix`, `tensorG`/`tensorG1`), `zDecomp`, `honestZ`, `honestComputeV`/`honestComputeResp`, the Eq. 20 `relOut` checks | `QuadEval/Gadgets.lean`, `QuadEval/Reduction.lean` | new `quadeval.rs` | thin seam to 1 (balanced instantiation at freeze) | similar–larger |
| 3 | ring-switch link: `liftMessage`/`rhoDigitAsRq`/`rhoAsRq`, `hachiLiftCom` (= `Simple.commit ∘ liftMessage`), `rhoDigitsShortCheck`/`liftShortCheck` | `RingSwitch/Reduction.lean`, `EndPiece/Reduction.lean:111–149` | new `ringswitch.rs` | 1 | similar |
| 4 | zero-check: `wTable`, `cWTableMle`/`wTableMleEval`, the computable `hZero`/`hAlpha` layer, `alphaPublicEvals`, `hypercubeSum`, batch checks | `ZeroCheck/Constraints.lean` (1488 lines), `Batch.lean` | new `zerocheck.rs` | 1, 3, **F** (Decision 3) | **larger** (⟲ was "similar") |
| 5 | sumcheck: `computableRoundPoly`, `roundCheck`/state advance, `finalCheck`, `honestComputeG`/`honestComputeY`, the round loop | `Sumcheck/RoundPoly.lean:286`, `Rounds.lean`, `FinalEval.lean` | new `sumcheck.rs` | 4, F | largest |
| 6 | end-piece: `endPieceCheck` (`com == t && liftShortCheck && wTableMleEval == value`), `endPieceWitness`/prover | `EndPiece/Reduction.lean` | new `endpiece.rs` | 3, 4 — **not 5** | smaller–similar |

Parallel structure: **{1 ∥ 2} → 3 → 4 → {5 ∥ 6}**, with TE (the Ext4 layer)
running beside 1–3 and landing before 4's specs. Drafting of a downstream
op's Rust may start early (DW), but nothing freezes out of dependency order.

⊕ **Stage 2 re-sizing (2026-09-01).** Edges unchanged; four size cells move.
Target 1 drops to **≈ evalsplit or less** (the balanced digit is a wrapper
over the proved `digit_at`; the bulk is one mechanical
`balanced_gadget_decompose` copy). Target 2 **loses a refactor**: zDigits =
8 = `GADGET_DIGITS`, so the params-hardwired `gadget_*` functions need no
digits parameter — its only new shape is the signed asymmetric `InSb` box
check. Target 4 **roughly holds**: it gains two prerequisites (a computable
`hAlpha` sibling, and the CMvPolynomial→dense rewrite) but cpoly's proved
MLE toolkit covers `wTableMleEval` outright. Target 5 **grows**, because
the dense rewrite it needs *to run at all* was previously booked as Stage 6
optimization — at m₀ = 27 the naive `computableRoundPoly` is not slow, it
is impossible. Net: the 8–12 day estimate survives, its internal
distribution shifts toward target 5, and one Stage 6 elephant is paid
early. Scale policies per target are fixed in `STAGE2_SCOPING.md`.

Per op, the standard op-genesis exit (naive trivial-grade translation, chain
closure, semantics tests, extraction pass, verbatim freeze + birth bench
case, interleaved stage-only commit plan) **plus the repo-specific riders
that are easy to miss**:

* MODULES sync in **both** `benches/harness.py` and
  `.claude/skills/skill-lab/references/ledger_check.py` (they must stay in
  step — the evalsplit promotion caught this late);
* `lib.rs`'s bottom-up module declaration and the `benches/genesis/` +
  `benches/candidate/` mirrors gain the module;
* the brief's scale policy is applied at freeze (which cases are REDUCED
  with a written note, which tests carry the `#[ignore = "full-const scale…"]`
  form), and `exclusions.toml`'s bar applies to anything excluded.

Calibration: 0.5–1.5 days each; zero-check +1 day (the computable layer is
wide); sumcheck +1–2 days (the erasure set is the largest).

### Stage 4 — Specs + equivalence proofs per op (10–15 days, overlapping Stage 3)

Pipelined: prove op *N* while onboarding op *N+1*; `aristotle-prove`
sessions run remotely in parallel (the machinery is warm — last session
closed 08-26, 12 sorries → 0) and `aristotle-check` folds them back in.

* `aeneas-spec-author` two-level specs per op; headline triples against the
  ArkLib definition at `params.rs`. For ops 4–6 the lift level lands on F
  through TE's bridge (the `φF` image), the way RqBridge lands Rq.
* **TE as its own proof workstream**: the missing `Ext4` instances +
  the extracted-cpoly-Ext4 ↔ CompPoly-Ext4 bridge. RqBridge-sized (~2 days),
  independent of ops 1–3, schedulable any time after Decision 3.
* Proof debt via `prove-sorry` / `launching-proof-agents`; `Check.lean` § 4
  audit line per headline spec; axiom-clean under `#print axioms`.
* Watch the literal-collision pitfall from the params flip: at these
  parameters `BLOCKS = MESSAGE_ROWS = 1024` and `GADGET_BASE = GAMMA = 16` —
  rewrite hypotheses, not goals.
* Calibration: `evalsplit` ~1 day, `RqBridge` ~2 days; ring-switch and
  sumcheck at 2–4 days each, the rest ~1–2.

Stages 3+4 combined, pipelined: **~3–4 weeks**.

Exit: every onboarded op has its headline `_spec` proved and audited; TE's
bridge proved.

### Stage 5 — Composition (~5 days)

* The target is `Composition.lean`'s composed chain as it exists at the pin
  — ending at `relWEvalClaim` + `endPiece`, Recursion detached (confirmed,
  not assumed). Rust: a composed commit → open → verify over the proved
  links, with `D` and the challenge stream as explicit inputs (the Ground
  truth facts; no invented keygen).
* Composition-level equivalence: mostly definitional over per-link specs;
  the known seam risks are the balanced-decomposition instantiation (T1)
  and the `φF` boundary at ring-switch (TE). `aeneas-equivalence-bridges`
  is the escape hatch, expected unused.
* End-to-end semantics test against the ArkLib honest chain on small inputs
  — `HachiRuntime.lean` is the spec-side executability witness for *shape*,
  but note it runs at toy parameters our const-based crate cannot adopt;
  the Rust test exercises the composed path at the smallest feasible
  shapes under the scale policy.

Exit: one composed `open`/`verify` pair, proved, with a bench case (scale
policy applies).

### Stage 6 — Optimization loop (2–4 weeks, elastic — see Decision 5)

`route-r3` per target, K = 1 verify-campaign per accepted champion, targets
by brief headroom over the genesis corpus (`autonomy-harness` once seeded).
If Decision 6 was taken, the `ring::mul` champion already landed and this
stage starts from the un-ignore/re-freeze ceremony it triggers (a dedicated
MH+MX slot: revised exclusions, reduced-shape cases returning, re-frozen
baselines — plus the honesty revision of the removal-condition wording).
The next elephants, per `logs/paper-impl/spans.json` read as a compass
only: sumcheck round polynomials (`computableRoundPoly` — the reference's
Prove-span dominator, independently confirmed by HachiRuntime's profile)
and the commit spans. Expected strategies unchanged (`opt-algo-swap`,
`opt-word-arith`, `opt-inplace-buffers`, `opt-list-to-array`).

Exit: by budget — every accepted champion proof-paid, ledger rows for every
campaign.

### Stage 7 — Comparison deliverable (2–3 days)

End-to-end ℓ = 30 runs on the same machine and witness discipline as
`logs/paper-impl/README.md`, span-for-span against the reference. The
write-up carries an explicit **claims ledger**: what is proved
(equivalence of the Rust to ArkLib's definitions, axiom-clean), what ArkLib
itself has proved about those definitions at the pin (soundness-side
composition clean; completeness-side `sorryAx`-tainted upstream), the
balanced/unsigned story per Decision 4's outcome, and which spans remain
non-comparable and why (mul-gap ceiling, `F` arithmetic differences). This
is the artifact the internship's benchmark story rests on.

## Timeline

| Stage | Duration | Status / depends on |
|---|---|---|
| 0 — pre-merge work | done except bench | ~0.5–1 day left, after T0's commit |
| 1 — toolchain re-alignment | **done locally**; commit + extract formality | ~0.5 day, USR |
| 2 — audit + scoping | 2–3 days (⟲ grew) | **starts now**, parallel to T0 |
| TM — mul champion | ~2–4 days spread opportunistically | T0; Decision 6 |
| TE — Ext4 layer | ~2–3 days | Decision 3; before target 4's specs |
| 3+4 — op-genesis + proofs, pipelined | 3–4 weeks | Stages 1–2; edges {1∥2}→3→4→{5∥6} |
| 5 — composition | ~5 days | Stages 3–4 |
| 6 — optimization loop | 2–4 weeks (elastic) | Stage 5 partially; TM changes its starting point |
| 7 — comparison deliverable | 2–3 days | Stage 6 budget spent |

**Remaining: ~6–8 weeks** from 2026-08-31 with pipelining — unchanged from
the morning revision: T1 and T4 grew, the parallel pairs {1∥2} and {5∥6} and
the TM/TE overlap absorb it. Stage 6 stays the deliberate accordion.

## Risks

1. **Aeneas port residuals** (was: the 4.33 gap, retired). (a) `file://`
   portability — fixed by TF, ~30 min. (b) Upstream drift: 64 commits, two
   charon bumps already; policy in Decision 2 — the pin moves only as a
   deliberate re-baseline.
2. **Extraction ceiling** (Stages 2/3). ⊕ **Fired once, and the answer is
   an opt rather than a probe.** The catalogue found exactly one shape with
   no in-repo precedent: `CMvPolynomial n F` as a runtime value (an
   `ExtTreeMap` monomial dictionary), reached by the sumcheck and
   zero-check polynomial layers. Because every runtime use of it is an
   *evaluation* and the pin already carries the factoring lemmas, the
   resolution is a Lean-side dense-table rewrite landing on cpoly's proved
   MLE toolkit — no tree-map ever reaches Rust. The probe escalation stays
   armed for anything else; every other entry has a precedent. The `Ext4`
   answer holds while the `cpoly` rev stays pinned.
3. **Spec churn** (Stages 2–5). Pin == main tip today; watchlist for any
   deliberate re-pin: the 12 Recursion fills (two are design changes, not
   proofs), `Commitment.hachi.opening`'s type change, the upstream
   `Append.lean` sorry fills, PR #698 (lattices subfield, additive).
   Mitigation unchanged: pinned at `294b3f0b0`, recursion out of scope.
4. **Regeneration bill** (any Rust edit from here on — T1's balanced layer
   is the first). Additive edits should produce additive `Generated.lean`
   diffs; the gate is checking exactly that per landing, and the 2–4 day
   metered verify-campaign budget remains the shape of the downside.
5. **Stamp/commit discipline across parallel tracks.** More tracks, same
   rule: toolchain commit first; nothing freezes until it's in; each freeze
   is its two-commit dance; `ledger_check.py` rides the bench commit. The
   tracks table says what each commit unblocks — batch USR interactions
   accordingly.
6. **F instance gap** — ⊕ **retired 2026-09-01.** `LawfulBEq (Ext P)` is a
   verified one-liner (`Ext`'s BEq *is* the Vector instance; core v4.33.1
   ships `LawfulBEq (Vector α n)`), and `SampleableType` is confirmed
   avoidable for every translated definition — it belongs to the sampling
   layer, exactly as hoped. What remains of TE is not an instance gap but
   the RqBridge-shaped extracted-cpoly-Ext4 ↔ CompPoly-Ext4 bridge, which
   was always its own ~2-day proof workstream.
7. **Scale walls for protocol ops** (new, certain). Every protocol op's
   full-const tests and benches hit the same Fig. 9 arithmetic that ignored
   the scheme layer; the mitigation is procedural — scale policy fixed in
   each Stage 2 brief, `exclusions.toml` bar respected, and Decision 6
   shrinking the wall early. A ~20× champion does *not* un-wall full-scale
   `commit`; only reduced shapes return. Say so wherever the removal
   condition is quoted. ⊕ **And there is now a second, independent wall:**
   m₀ = 27 makes any cube-shaped object ~1.3·10⁸ entries (a materialized
   Ext4 table is ~4 GiB), which **no multiplication champion touches**.
   Targets 4 and 5 are REDUCED-throughout for that reason, not the
   `ring::mul` one. Never conflate the two removal conditions in a policy
   note.
8. **Balanced/unsigned seam** — ⊕ **largely retired 2026-09-01.** The
   audit confirms all three minimal-surface guesses and finds
   `verify_weak_spec` needs **no** sibling (the opening is data; γ = 16
   covers both the unsigned honest bound 15 and the balanced 8). Residual:
   six `dd`-mentioning specs get additive siblings, and sibling specs must
   avoid a local `[DecidableEq (ZMod q)]` binder or unification diverges
   (`Commitment.lean:397–400`). Original framing kept below for the shape
   of the downside. The minimal-surface guess in Decision 4
   could be wrong — e.g. `verify_weak`'s norm-side conjuncts might need a
   balanced-instantiated sibling spec after all. Contained: the unsigned
   layer's 74 specs stay green regardless (nothing is edited, only added);
   the downside is T1 growing by a spec-sibling, metered under prove-sorry.
9. **Machine contention** (new, procedural). MX slots are exclusive and the
   thermal lesson is real; TM's candidate benching, birth benches, and the
   Stage 6 re-freeze ceremony all queue on the same laptop. The tracks table
   exists so the queue is chosen, not discovered.
