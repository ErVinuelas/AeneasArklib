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
| 3 | [ring switch](target-3-ring-switch.md) | `lift_commit`, 81 960 muls (~4 min, 1.3 GiB) | fuse `liftMessage` into `hachiLiftCom` (never materialize 640 MiB) |
| 4 | [zero check](target-4-zero-check.md) | the 2^27 cube: 3.8·10⁹ Ext4 mults, 8 GiB | `d = 2^10` split (4.0 GiB → 4.2 MiB); `eval_mle_eq_eval` ~7× at zero proof debt |
| 5 | [sumcheck](target-5-sumcheck.md) | range factor at 33 nodes over the folded cube, 1.37·10¹¹ Ext4 mults (94% of work) | folded-table value form + 33-node interpolation |
| 6 | [end piece](target-6-end-piece.md) | conjunct A = `lift_commit` (~8.6·10¹⁰ mult-adds) | hoist the 40-element digit block across all three conjuncts (41.9 M → 40 960) |

Honest floors, where the briefs computed one: target 4's is ~84 M
multiply-accumulates (the count of committed coefficients); target 5's is
~1.5 h single-threaded.

**Read [STAGE2_CORRECTIONS.md](STAGE2_CORRECTIONS.md) before acting on
`STAGE2_SCOPING.md`** — the briefs found ~29 items needing correction there,
including three internal contradictions, a miscounted monomial bound
(inherited from a bug in ArkLib's own `HachiRuntime.lean:37`), and **five
distinct scale walls with four different removal conditions** where the plan
records one.
