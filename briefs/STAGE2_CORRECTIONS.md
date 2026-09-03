# Corrections to `STAGE2_SCOPING.md`, from the six target briefs (2026-09-01)

> **Folded into `STAGE2_SCOPING.md` on 2026-09-03** (marks ⊗⊗), after the τ
> work landed at **τ = 5** (ArkLib PR #847, not the τ = 4 § 6 anticipated nor
> the τ = 8 the tree carried). Kept as the index of evidence; § 6's
> "if `Z_DIGITS = 4` lands" arithmetic applies with 5 in place of 4:
> μ₀ = 57344, `RLIN_CZ` = 40960, m₀ = 26, and target 2's `_z` siblings return.

**Provenance.** Produced by the six `arklib-analyze` briefs in this directory,
one per Stage 3 target, all read against the pinned ArkLib rev
`294b3f0b0f46e1485c878a217e9de764855f5915`. Every item below is the brief's
finding, and **the brief carries the `file:line` evidence** — this file is an
index of what needs changing, not an independent re-verification. Cited as
`[T1]`…`[T6]` by target.

**Why this is a separate file.** `STAGE2_SCOPING.md` is being edited
concurrently by the session implementing the τ = 4 decision, and several items
below are exactly what that session is touching (`Z_DIGITS`, `M_ZERO`, F3's
τ-sensitivity). Folding these in during that work risks clobbering it. Land
this in one pass when the τ work is committed.

---

## 1. Contradictions inside the document (a side must be picked)

1. **`RHO_DIGIT_COUNT`** is listed as a new const in § "Parameter mapping" but
   as "needs no const" in the target list. **The target list is right**: it
   equals `GADGET_DIGITS`. `[T1]`
2. **Target 6's "real consts for the checks" contradicts target 3's row.**
   `endPieceCheck`'s conjunct A *is* `lift_commit` (the 81 960-wide
   `hachiLiftCom_com`), so it must inherit REDUCED. `[T6]`
3. **Module placement of `liftShortCheck` / `rhoDigitsShortCheck`.** They sit
   under target 3's scale row but are assigned to `endpiece.rs` by § "API
   mapping". The pin settles the file (`EndPiece/Reduction.lean:111,144`) —
   **API mapping is right**; target 3's row is scale policy only. `[T3][T6]`

## 2. Factual errors

4. **The naive sumcheck monomial count is `(2b+1)^m₀ = 33²⁷`, not
   `(bZero+1)^m₀ = 17²⁷`.** ArkLib's own `scripts/HachiRuntime.lean:37`
   undercounts it, contradicting that same file's proved `roundDegZero b = 2b`.
   Consequence: at `b = 16` the naive form is impossible at **every m₀ ≥ 5**,
   so its exclusion is *unconditional*, not scale-dependent — which simplifies
   the policy note. `[T5]`
5. **"No bit machinery survives" is false on the `m₁` side**
   (`Constraints.lean:858,890`). Benign — it is cpoly's `lagrange_basis` — but
   the erasure table should say so. `[T4]`
6. **Prerequisite A is smaller than scoped.** The `noncomputable` marker on
   `hAlpha`/`hAlphaEvals` has a single cause, and `cEvalAt_eq_evalAt_toPoly`
   alone repairs it; `rhoDigits_evalAt` is orthogonal. `[T4]`
7. **Prerequisite B must be *additive*.** Removing `CMvPolynomial` outright
   orphans the degree theorems at `Constraints.lean:1082,1097`. `[T4]`
8. **Target 2's "loses a refactor" needs refining**: what gets reused is
   `gadget_mul` / `gadget_decompose`, not `gadget_matrix`. `[T2]`

## 3. Missing from the document

9. **F3's value-8 collision row omits `HALF_BASE`**, which the document's own
   Decision-4 table introduces. `[T1]`
10. **The erasure catalogue lacks the `Prop`-relation → `Bool` shape**, which
    makes the corresponding `_spec` an iff rather than an equality. `[T2]`
11. **`cEvalAt` at mixed carrier is an unowned minor variant.** `[T4]`
12. **The sumcheck verifier needs an explicit degree check** that the subtype
    erasure silently drops — a correctness item, not a performance one. `[T5]`
13. **Two translation traps that cost 3× if translated literally**:
    `roundProver.output` recomputes the dominant term twice more `[T5]`, and
    `endPieceCheck`'s conjunct B2 is quadratic in `d` (41.9 M `balancedDigit`
    calls) purely from the spec's `∀i∀u∀k` nesting `[T6]`.

## 4. The walls — one is not enough, and neither is two

The document treats scale walls as `ring::mul` versus m₀'s cube. The briefs
found **five distinct walls with four different removal conditions**. Every
policy note must name which one it is:

| # | Wall | Site | Removed by |
|---|---|---|---|
| W1 | schoolbook `ring::mul` width | `lift_commit` 81 960-wide `[T3][T6]`; `relOut`'s 1×8192 mat-vecs `[T2]` | a sub-quadratic / NTT mul champion |
| W2 | m₀'s cube, `2^27` | `wTableMleEval`, `hZero` `[T4]`; the folded cube `[T5]`; conjunct C `[T6]` | **nothing in mul** — needs the dense/split rewrite |
| W3 | allocation in the lift, 640 MiB–1.3 GiB | `lift_message` `[T3]` | fusion (never materialize the concatenation) |
| W4 | 64 GiB `wit.message` at Fig. 9 | target 2's witness `[T2]` | streaming witness (no skill yet) |
| W5 | `s.M` at 3.2 GiB | target 4's second memory wall `[T4]` | the `d = 2^10` evaluation split |

Also: **`jMatrix` materialized at n = 8192 would be ~4 TB**, so collapsing it
via `gadgetMul_apply` is a feasibility requirement, not an optimization. `[T2]`

## 5. Scale-policy corrections

14. **Target 1's "real consts for bench cases" cannot cover
    `generate_decomps_balanced` / `commit_balanced`** — they are `ring::mul`-bound
    and inherit their unsigned twins' Fig. 9 exclusion. `[T1]`
15. **`lift_message` needs its own REDUCED note** citing W3, not W1. `[T3]`
16. **`liftShortCheck` at real consts carries 640 MiB resident `z`.** `[T3]`
17. **REDUCED m₀ has a floor of 14** — below that the shape stops exercising
    anything. `[T4]`
18. **Target 6 is the one target where two walls fire inside one function**
    (conjunct A = W1, removable by a mul champion; conjunct C = W2, not), so it
    needs two separate notes. `[T6]`
19. **`{1 ∥ 2}` holds for code but not for tests**: target 2's honest-path
    tests need target 1's balanced digits. `[T2]`
20. **Target 4's REDUCED-throughout policy may be revisable.** The `d = 2^10`
    evaluation split turns a 4.0 GiB table into 4.2 MiB and shrinks
    `alphaPublicEvals` ~1024×. Decide deliberately rather than inheriting. `[T4]`

## 6. For the τ session specifically

21. **τ = 4 matches the reference implementation.** The paper's prototype runs
    ℓ = 30 at τ = 4, hence **m₀ = 26**, with a measured sumcheck span of
    **272.7 s**. Stage 7's span-for-span comparison is only meaningful at the
    reference's own m₀, so τ = 4 is the right choice for the *implementation*
    parameters. `[T5]`
22. **But `zDigits = 4` has no instantiation at this pin.** `hqz : q ≤ b^zDigits`
    is discharged at `δ P` (`Correctness.lean:491,517`) and `16⁴ ≪ q`, so no
    `DigitDecomposition 16 4` over `ZMod q` exists. The z-side equivalence
    statement would become *conditional* rather than unconditional — a change
    of shape, costlier than a change of constant. `[T2][T6]`
    **The reconciliation belongs in the statement, not in the constant.**
23. **What moves if `Z_DIGITS = 4` lands**: `μ₀` 81 920 → 49 152, `m₀` 27 → 26
    (`M_ZERO`), `jMatrix` `8192 × 8192Z`, `rlinCols = 16384 + 8192Z`, and
    target 2's dropped refactor returns. Recommended shape if so: **additive
    `_z` siblings**, never re-parameterizing the four frozen `gadget_*`
    functions. `[T2][T6]`
24. **F3's value-8 row should mark only `Z_DIGITS` as τ-sensitive** —
    `GADGET_DIGITS` and `RHO_DIGIT_COUNT` are not. `[T3]`
25. **Bound-insensitivity, verified per target**: `BETA_SQ` reaches *none* of
    targets 1, 2, 3, 6 (target 3's and target 6's checks test ℓ∞ against the
    chain's `γ = bZero − 1 = 15`; target 2's `relOut` has no ℓ₂ row). The τ
    dispute is therefore about **sizes**, not about any target's bound.
    `[T1][T2][T3][T6]`

## 7. Findings outside this document's scope

26. **`hachi/src` docstring citations went stale under the pin bump**, by a
    different offset per file: `Gadget/Core.lean` +36 `[T1]`, `Vectors.lean` +6
    and `NormBounds/Basic.lean` +30 `[T3]`. A refresh pass — but it is Rust
    docstring editing, which regenerates `Generated.lean`, so it queues behind
    the τ work. Not currently on any doc-sync list.
27. **A check that cannot fail at Fig. 9 parameters**:
    `rhoDigitsShortCheck` is provably constant true
    (`rhoDigitsShortCheck_eq_true_of_digitBaseOk`), found **independently by
    two briefs** `[T3][T6]`. Both correctly declined to elide it — the
    equivalence proof must relate it to ArkLib's definition verbatim — but
    honest corpora test it vacuously, and the Stage 7 claims ledger should say
    so. Note the `verify_weak` ℓ₂² branch is a *second* such check **only at
    τ = 8**; at τ = 4 the bound is smaller and that branch can fire again.
28. **Two nearly-free wins with existing proofs**: `eval_mle_eq_eval`
    (CompPoly `Multilinear/Basic.lean:574`, already translated and proved as
    cpoly's `eval_mle_spec`) gives ~7× on target 4 with zero new proof debt
    `[T4][T6]`, and the `Fp × Ext4` product (4 Fp mults) replaces
    `Ext4 × Ext4` (16) wherever a table entry is `φF(base)` `[T6]`.
29. **The largest single algorithmic win found**: a challenge-sparse ring
    product on target 2's dominant term. `‖c‖₁ ≤ ω = 16` bounds the nonzero
    coefficients, giving `≤ ω·d` instead of `d²` field ops — about 64× — with
    no precondition needed, and the paper's prototype has exactly this
    operation. `[T2]`
