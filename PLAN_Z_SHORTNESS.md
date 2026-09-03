# Plan: carry the z-shortness invariant in ArkLib's Hachi formalization

Status: **draft for upstream discussion, 2026-09-02 — nothing implemented.**
Grounded in three code audits of the pinned ArkLib
(`294b3f0b0f46e1485c878a217e9de764855f5915`, 2026-08-31). Every file:line below
was verified at that pin. This is a plan for *upstream* work (Verified-zkEVM/ArkLib);
the last section records what this repo does when it lands.

## Goal

Restate the Hachi chain so the z-gadget digit count `zDigits` (the paper's τ)
is pinned by a shortness bound `B_z` on the fold `z = Σᵢ cᵢ • sᵢ` instead of by
full coverage of ℤ_q (`hqz : q ≤ b ^ zDigits`, which forces `zDigits = 8` at
`b = 16`). Payoffs, in decreasing order of importance:

1. `quadEvalBetaSq` shrinks by ≈ `b⁸ = 2³²` at τ = 4, taking `√βSq` from
   ≈ 2^44.6 (above q — weak binding trivially unsound at any dimensions) to
   ≈ 2^28.6 (below q — the Module-SIS hypothesis becomes well-formed).
2. `μ₀` (the R^lin column count, `rlinCols`, `RingSwitch/Rlin.lean:153`) loses
   half its z-block, shrinking the lift key `D`, the lifted witness, and the
   cube-cover obligations.
3. Protocol-layer z work halves and matches [NOZ26] Fig. 9's τ = 4, making a
   full implementation comparable with the paper's benchmark implementation.

## What the audits established

These seven facts shape the whole plan; each was checked in source.

**A1 — soundness is already τ-free.** `QuadEval/Soundness.lean` uses only
`hτ : 0 < zDigits`; no `hqz` appears in `Soundness/Reduction/Gadgets/Bridge`.
The QuadEval verifier is a pure pass-through (`Reduction.lean:400-406`); all
checks live in `relOut` (`:258-284`), where z exists only as the recomposition
`let z := jMatrix … *ᵥ resp.zDec`. The extracted opening's norm bound is derived
entirely from c6 (`‖ẑ‖∞ ≤ γ`) through the recomposition weight
(`gadgetMul_zmod_sub_l2NormSq_le`, `Gadget/Norms.lean:375`). **Consequence: no
new verifier check and no relation change is needed for soundness — `relOut`,
`paperRelOut`, and the entire Rlin threading stay untouched.** The paper's
explicit `‖z‖ ≤ B_z` check is, in this architecture, c6 in disguise.

**A2 — the wall is completeness.** `DigitDecomposition.reconstruct : ∀ c : R`
(`Gadget/Core.lean:95-99`) is total over ZMod q, and the completeness
hypothesis `hddZ : ∀ (x : ZMod q) (e : Fin zDigits), …natAbs ≤ γ`
(`QuadEval/Completeness.lean:161`) quantifies over every residue. At τ = 4,
`16⁴ = 65536 < q`: no such structure is inhabitable and `hddZ` is
unsatisfiable. The honest prover cannot *construct* `ẑ = J⁻¹(z)`.

**A3 — `relIn` cannot bound the honest z.** `VerifiedBlock.scaled_short`
bounds only `challengeᵢ •ᵥ sᵢ` under the opening's *own* challenge (honest:
c = 1); `relIn` puts no ℓ∞ bound on `sᵢ` itself. Deriving `‖Σ cᵢ • sᵢ‖∞ ≤ B_z`
from `relIn` is impossible. The in-repo precedent for exactly this is
`relInBox` (`Completeness.lean:186-206`): strengthen the *input relation* with
the box the upstream layer (which chose the decomposition) can establish.

**A4 — the paper's `Z_BOUND = 30583` is the τ = 4 representability ceiling,
exactly.** `balancedShift 16 4 = 8·4369 = 34952` and
`(16⁴ − 1) − 34952 = 30583`. So the paper's z-check is precisely "z is
representable in 4 balanced base-16 digits".

**A5 — the honest fold's worst case exceeds that ceiling.** With
`‖cᵢ‖₁ ≤ ω = 16`, `‖sᵢ‖∞ ≤ b/2 = 8` (balanced digits), and 2^r = 1024 blocks:
`‖z‖∞ ≤ 2^r · ω · (b/2) = 131072 > 30583`. **The paper's bound is
statistical, not worst-case** (typical ‖z‖∞ concentrates around ~10⁴ by a
back-of-envelope CLT estimate — to be confirmed against the paper's own lemma
in Phase 0). Perfect completeness at τ = 4 is therefore *impossible*; the
choice between τ = 4 (statistical completeness) and τ = 5 (worst-case, perfect
completeness) is the plan's central decision.

**A6 — one norm lemma is missing.** No `‖c·x‖∞ ≤ ‖c‖₁ · ‖x‖∞` (challenge-
scaling in ℓ∞) exists anywhere in ArkLib; only the ℓ₂² form
(`MicciancioYoung.lean:261, :325`). The negacyclic-convolution scaffolding to
prove it exists (`coeff_mul_rq_two_block`, `natAbs_conv_le`) but is
specialized to `powTwoCyclotomic`.

**A7 — most infrastructure survives untouched, and the right idioms exist.**
Free: the whole recomposition block (`Gadget/Norms.lean:274-383`), all of
`NormBounds/*`, `ModuleSIS.lean` (norm is a parameter), Lyubashevsky–Seiler.
Mechanical: the five generic `*_of_digit_le` lemmas (universal `hdd` weakens
to a bounded one; `Rq.valMinAbs_natAbs_coeff_le_of_vecLInftyNorm_le`,
`NormBounds/Basic.lean:160`, is the adapter). Idioms to copy: the proof-free
digit map `balancedDigit` (`RingSwitch/RhoDigits.lean:79`, hypotheses live on
the lemmas, not the def — its docstring is the design rationale verbatim), the
side-condition bundle `DigitBaseOk` (`RingSwitch/Reduction.lean:175`), and
`relInBox`.

## Phase 0 — pin the arithmetic and settle τ (decision gate)

Compute exactly, and check against the paper's own z-bound lemma
([NOZ26]; the reference implementation in `~/.cache/hachi-pcs-bench` shows
what its prover does on overflow — resample, abort, or nothing):

| | **Option A: τ = 4** (paper-faithful) | **Option B: τ = 5** (worst-case) |
|---|---|---|
| `B_z` | 30583 (representability ceiling) | `2^r·ω·(b/2) = 131072` (ceiling 489335 ✓) |
| honest z fits | **statistically** (needs tail bound + concrete sampler) | **always** (triangle inequality) |
| chain completeness | ε_z > 0 — perfect completeness of the composed chain is lost | perfect, unchanged shape |
| `√βSq` at γ = 16 (ball) | ≈ 2^28.6 < q (margin ≈ 10×) | ≈ 2^32.6 **> q** ✗ |
| `√βSq` at γ = 8 (box) | ≈ 2^27.6 < q (margin ≈ 21×) | ≈ 2^31.6 < q (margin ≈ 1.3×) |
| challenge distribution | must be concretely formalized | stays abstract (`ShortChallenge` subtype suffices) |
| matches Fig. 9 / reference impl | yes | no (1.25× the z work, different B_z) |

All βSq figures are √(4 · 2^m·δ · d) · (Σ_{u<τ} bᵘ) · γ at the ℓ = 30 shape —
re-derive them precisely in this phase; the γ = 8 column assumes restating the
weak-opening γ̄ from the ball relaxation (γ := b) to the paper's box S_b
(`vecInSb`, machinery exists).

**Recommendation: build Option B first — every line of it is a strict subset
of Option A** (A = B with a smaller B_z plus the statistical layer). B alone
already makes SIS non-vacuous *if* paired with the box-γ restatement; whether
that 1.3× margin satisfies the maintainers, and whether A's statistical layer
is wanted at all, is the discussion to have upstream before writing code.

**Exit criterion:** a pinned `(τ, B_z, γ-convention, completeness model)`
tuple agreed with ArkLib maintainers, recorded here.

## Phase 1 — bounded z-gadget core (`Gadget/Core.lean`, `Gadget/Norms.lean`)

Additive only; no existing definition changes.

1. Reuse `balancedDigit` (`RhoDigits.lean:79`) as the digit map — it is
   already proof-free. Add the bounded reconstruction lemma:
   `balancedDigit_reconstruct_of_natAbs_le : c.valMinAbs.natAbs ≤ B_z →
   B_z + shift-headroom side condition → ∑ e, bᵉ · balancedDigit b τ c e = c`.
   The single `hq`-consumption point to replace is
   `Nat.digits_length_le_iff … (ZMod.val_lt c) hq` (`Core.lean:118-119`) —
   substitute `(c + balancedShift b τ).val < b^τ` derived from the bound (the
   `valMinAbs_spec + omega` technique at `Norms.lean:125-131`).
2. A bounded gadget-decompose (same body as `gadgetDecompose`, driven by the
   digit map, not the structure) and its lawfulness:
   `gadgetDecomposeB_lawful_of_le : vecLInftyNorm Φ x ≤ B_z →
   gadgetMul Φ b (gadgetDecomposeB x) = x`. The existing proof bottoms out at
   per-coefficient `reconstruct` (`Core.lean:285`), so the bounded hypothesis
   threads coefficientwise via `Basic.lean:160`.
3. Bounded digit-range lemmas: instances of the existing generic
   `*_of_digit_le` family — near-zero new proof text.
4. A `ZBoundOk q b τ B_z` side-condition bundle in the `DigitBaseOk` idiom.

**Exit:** the four lemmas compile standalone; nothing else in ArkLib touched.
Size: ≈ 300–400 lines. This phase is an uncontroversial standalone PR.

## Phase 2 — the ℓ∞ challenge-scaling lemma (new, `NormBounds/`)

`Rq.lInftyNorm_mul_le : lInftyNorm Φ (c * x) ≤ l1Norm Φ c * lInftyNorm Φ x`
over the negacyclic ring (fine to state at `powTwoCyclotomic` like
Lyubashevsky–Seiler does), plus the fold corollary
`vecLInftyNorm Φ (∑ i, (c i).val •ᵥ s i) ≤ 2^r · ω · γ` from
`ShortChallenge.l1Norm_le` + `valMinAbs_natAbs_sum_le`. Genuine new analysis,
but the signed-convolution helpers exist. Also standalone-PR-able.

**Exit:** both lemmas proved; `#print axioms` clean.

## Phase 3 — QuadEval completeness rewire (`QuadEval/`)

1. `honestComputeResp` / `quadEvalReduction` gain a bounded-decomposition
   variant for the z leg (message/carrier legs keep the total structure —
   their digit counts are genuinely full-coverage).
2. `z_eq_jMatrix` gains the `‖z‖∞ ≤ B_z` hypothesis (bounded lawfulness).
3. Input-relation strengthening à la `relInBox`: add the per-block message box
   (`vecInSb b (wit.message i)` or `‖sᵢ‖∞ ≤ γ`) so the honest-fold bound
   `‖honestZ‖∞ ≤ 2^r·ω·γ ≤ B_z` (Phase 2 lemma) is derivable. New goals land
   at exactly two `refine`s: `mem_relOut_of_relIn` (`Completeness.lean:172`)
   and `mem_paperRelOut_of_relIn` (`:242`), then propagate to the five
   `quadEvalReduction_perfectCompleteness*` variants.
4. Option A only: the completeness statement weakens from perfect to
   1 − ε_z; deferred to Phase 5.

**Exit:** QuadEval link complete + sound at the pinned τ, `sorry`-free
(Option B) with the strengthened input relation.

## Phase 4 — chain rethreading (`HonestChain`, `Correctness`, `Concrete`, `Composition`, `RingSwitch`)

Mechanical but wide — this is where the τ = 8 pin actually lives:

1. Replace the z-side `hqz` at its six sites (`HonestChain.lean:336, 374, 472,
   528`; `Correctness.lean:241, 273`) with the `ZBoundOk` bundle; `hqm` (the
   message side) stays.
2. Split the `δ P` notation knot: `Correctness.lean:491-494` bakes
   `messageDigits = innerDigits = zDigits = δ P` into `μ₀`; `Concrete.lean:47-51`
   duplicates it. `zDigits` becomes its own constant. `μ₀` shrinks; the lift
   key width, `hμn`/`hcov` cube-cover hypotheses, and `nonrecursiveLiftCom`'s
   type follow (`Concrete.lean:60-115`, `Composition.lean:292`).
3. Establish the new message box at the commitment seam: `completePrefixReduction`
   builds the witness by `balancedZmodDigitDecomposition` (`HonestChain.lean:350`),
   digit bound b/2 — the box is exactly what it already guarantees.
4. Re-elaborate `Composition.lean` (`iteration`, `evaluation`) — the 6
   `quadEvalBetaSq` sites re-typecheck at the new τ automatically; widths change.
5. Verify `liftMessage_injective` (`RingSwitch/Reduction.lean:379`): its
   digit-reconstruction dependency is on the ρ digits (`bDig`, full coverage —
   untouched); the z-part of `liftMessage` is an identity append, so only
   widths change. Flagged as the sharpest re-elaboration risk; expected
   mechanical.

**Exit:** `lake build` green repo-wide at the new pin values;
`scripts/validate.sh --axioms` clean; no perfect-completeness statement lost
(Option B).

## Phase 5 — Option A only: statistical completeness

The research-grade block, and the only part with real schedule risk:

1. A concrete sampler instance for `ShortChallenge 𝓜(q,α) ω` (today: "the
   repo does not yet provide", `Composition.lean:195-199`) — presumably the
   paper's weight-c sparse distribution, as a VCVio `SampleableType`.
2. A tail bound `Pr[‖Σ cᵢ • sᵢ‖∞ > 30583] ≤ ε` over that sampler — a
   Hoeffding/Bernstein-style concentration argument over centered ZMod sums,
   bridged from Mathlib's probability library into VCVio's computational
   distributions. No precedent in ArkLib.
3. Completeness statements for the QuadEval link and the composed chain at
   error ε_z, replacing `perfectCompleteness` on the z-affected path.

**Exit:** τ = 4 chain builds with a stated, proved ε_z.

## Difficulty and time

Assume one person fluent in Lean/Mathlib and this codebase (or an agent
pipeline with human review), working on it as their main task.

| Phase | Difficulty | Estimate |
|---|---|---|
| 0 arithmetic + decision | easy (but gates everything) | 1–2 days + upstream discussion latency |
| 1 bounded gadget core | easy–moderate (idioms exist) | 3–4 days |
| 2 ℓ∞ scaling lemma | moderate (new analysis, helpers exist) | 2–5 days |
| 3 QuadEval completeness | moderate (precedented by `relInBox`) | 4–6 days |
| 4 chain rethreading | mechanical but wide; elaboration-fight risk | 5–10 days |
| 5 statistical layer (A only) | **hard** — research-grade, no precedent | 6–12 weeks |

- **Option B (τ = 5, worst-case, perfect completeness): ≈ 3–5 weeks** of
  focused work end-to-end, no new mathematics beyond one norm-lemma family.
- **Option A (τ = 4, paper-faithful): ≈ 2–4 months**, dominated by Phase 5;
  the sampler formalization and the VCVio↔Mathlib probability bridge are the
  risk items, not the gadget work.
- Calendar time adds upstream review; Phases 1–2 are additive, standalone,
  low-controversy PRs and should go first to de-risk the discussion.

## Risks

1. **Phase 5 is open-ended** — if the VCVio probability bridge fights back,
   Option A slips indefinitely; Option B is the hedge (strict subset, ships
   value alone).
2. **Option B's SIS margin is thin** (1.3× under q, and only with the box-γ
   restatement). If maintainers want the ball-γ convention kept, Option B does
   *not* fix vacuity and only Option A does. Settle in Phase 0.
3. **Elaboration cost**: `Composition.lean`/`Correctness.lean` were recently
   hotspot-optimized upstream (#813); wide re-threading may reopen build-time
   fights.
4. **Upstream direction**: the same files carry an explicit TODO list
   (knowledge-error accounting, `Commitment.extractability`, Fiat–Shamir out
   of scope) — maintainers may want the z-shortness restatement sequenced
   after those, not before.

## When it lands: consequences for this repo

A pin bump (= a project decision + verify-campaign, per NOTES.md rules):
`Z_DIGITS`/τ constants and the `BETA_SQ` literal move to the new instantiation
(direction already chosen: away from τ = 8); `Z_BOUND` and possibly the
message-box check gain ArkLib names, closing the F4 house-discipline exception
(STAGE2_SCOPING.md); if the input relation gains the message box, `verify_weak`
gains one cheap ℓ∞ check (spec change → equivalence-proof repair); the ℓ₂²
rejection branch becomes live again and
`the_l2_check_cannot_fire_at_these_dimensions` gets retired in reverse.
