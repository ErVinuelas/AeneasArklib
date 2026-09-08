# Stage 3 target briefs

One `arklib-analyze` brief per Stage 3 target, all read against the pinned
ArkLib rev `294b3f0b0f46e1485c878a217e9de764855f5915` (what
`hachi/lake-manifest.json` records for `Arklib`). Written 2026-09-01, closing
the first of Stage 2's three remaining items (`STAGE2_SCOPING.md` §
"Remaining Stage 2 work").

Each brief carries the skill's fixed headings and cites `file:line` for every
claim; they are handed verbatim to `lean-opt` and `lean-to-rust`.

| # | Brief | Dominant cost | Largest win identified |
|---|---|---|---|
| 1 | [balanced digits](target-1-balanced-digits.md) | modular reduction, not division: 5 reductions/digit vs the unsigned path's 1 | `opt-word-arith` guarded fold, 5→~1 per digit (~1.25× floor — no complexity win) |
| 2 | [QuadEval fold](target-2-quadeval-fold.md) | `honestZ`, 2^23 ring products (~3.5 h) | challenge-sparse product, ~64× (‖c‖₁ ≤ ω = 16) |
| 3 | [ring switch](target-3-ring-switch.md) | `lift_commit`, 57 384 muls (~3 min, ~896 MiB at τ = 5) | fuse `liftMessage` into `hachiLiftCom` (never materialize the 448 MiB copy) |
| 4 | [zero check](target-4-zero-check.md) | the `2^m₀` cube at τ = 5: `2^26`, 2.08·10⁹ Ext4 mults in `hZero`, 4.0 GiB resident | `d = 2^10` split (2.0 GiB → 2.1 MiB); `eval_mle_eq_eval` ~7× at zero proof debt |
| 5 | [sumcheck](target-5-sumcheck.md) | range factor at 33 nodes over the folded cube, 1.37·10¹¹ Ext4 mults (94% of work) | folded-table value form + 33-node interpolation |
| 6 | [end piece](target-6-end-piece.md) | conjunct A = `lift_commit` (~8.6·10¹⁰ mult-adds) | hoist the 40-element digit block across all three conjuncts (41.9 M → 40 960) |

Honest floors, where the briefs computed one: target 4's is ~59 M
multiply-accumulates at τ = 5 (`R·d = 58 761 216`, the count of committed
coefficients — it was ~84 M at the τ = 8 widths); target 5's is ~1.5 h
single-threaded.

[STAGE2_CORRECTIONS.md](STAGE2_CORRECTIONS.md) — the ~29 items the briefs
found against `STAGE2_SCOPING.md` (three internal contradictions, a
miscounted monomial bound inherited from ArkLib's own `HachiRuntime.lean:37`,
**five distinct scale walls with four different removal conditions**) — was
**folded into `STAGE2_SCOPING.md` on 2026-09-03** (marks ⊗⊗) and is kept as
the index of evidence.

**Pin moved after these were written; briefs 1–4 are re-based, 5–6 are
not.** Each re-based brief carries a re-base section at the top that
must be read before the body. Brief 1 was re-based 2026-09-03 (and target 1
is onboarded as of `09df61b`/`4c146b1`); **brief 2 was re-based 2026-09-04**
— PR #847 lands squarely on it, closing its one open parameter at τ = 5 and
turning the `z` decomposition into a `BoundedDigitDecomposition` with a
conditional round trip, which makes target 1 a hard dependency rather than
the "thin seam" the plan's table records. **Brief 3 was re-based 2026-09-07**:
its definitions are unchanged, its widths move to `57344 + 40`, and three
deleted convenience lemmas are replaced by direct unfolding/composition.
**Brief 4 was re-based 2026-09-07** when target 4 opened: all fifteen definitions it
translates are byte-identical across the move, four alias theorems were deleted from
`Constraints.lean`, and the profile is now pinned by a new `Hachi/Params.lean`
(`hachiTau = 5`, `μ₀ = 57344`, `m₀ = 26`) rather than left free under `hμn` — halving
every cube-sized figure. Briefs 5–6 remain at `294b3f0b0` and must be re-based when
their target opens.

The repo now pins ArkLib PR #847's head `d51d8bc` (τ = 5 via `BoundedDigitDecomposition`; the unsigned
decomposition demoted to a building block, `commitBalanced` → `commit`;
several lemmas the briefs cite deleted). The deltas that change a target's
*shape* are in [brief 1's re-base section](target-1-balanced-digits.md)
(promotion + the bounded τ = 5 digit) and `STAGE2_SCOPING.md`'s ⊗⊗ marks
(target 2 regains `_z` siblings at `Z_DIGITS = 5`; m₀ = 26; the τ = 5
constant table). Every `file:line` in briefs 5–6 is at `294b3f0b0` and must
be re-read at `d51d8bc` when that target opens (brief 4's already were, on
2026-09-07); the numbers most affected:
μ₀ 81920 → 57344, lift width 81960 → 57384, `RLIN_CZ` 65536 → 40960,
m₀ 27 → 26, `Z_BOUND` 30583 → 131072.
