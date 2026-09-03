# Plan: adopt the paper's parameter set ([NOZ26] Fig. 9) while keeping the proofs green

Status: **executed 2026-08-28, then amended the same day after user review**
(all six phases; work staged, awaiting the user's commits and the two-commit
genesis stamp dance — see NOTES.md § "Superseded 2026-08-28" for the record).
Decisions 1–3 settled with the user 2026-08-28, all per the recommendations.
The review then corrected three things this plan got wrong: the verifier
bounds `(KAPPA, GAMMA, BETA_SQ)` are ArkLib's *weak-opening* triple
`(2ω, b, quadEvalBetaSq) = (32, 16, 163 966 054 471 565 312)`, not the
honest-case values in the table below; the unsigned-digit gadget is not
paper-faithful at `b = 16` (documented, fix gated on ArkLib's
`balancedZmodDigitDecomposition`); and "the paper's parameters are adopted"
was softened to the commitment/eval-split dimensions.
Originally written 2026-08-27 from an audit of the repo at commit `2a0168f`.
Read this whole file before touching anything — the phases are ordered to make
failures attributable, and each has an explicit exit criterion.

## Context

The goal is to make this repo's Hachi implementation use the *same parameters*
as the paper's benchmark implementation (Hachi paper [NOZ26], Figure 9, the
ℓ = 30 set), so that the two are comparable. The binding constraint, from the
user: **the equivalence proofs must keep working** — every headline `_spec` in
`hachi/lean/` axiom-clean under `lake build`, `Check.lean` § 4 intact.

Two facts make this tractable:

1. **The field layer already matches.** `Q = 2³² − 99 = 4294967197` and
   `EXT_DEGREE = 4` are pinned by the `cpoly` dependency *and* are exactly the
   paper's values (Fig. 9: `q`, `k`). No cpoly change is needed.
2. **The ArkLib specification is generic in every parameter** (see NOTES.md
   § "Chosen parameters"): no concrete modulus, α, base or digit count appears
   in `Commitments/Functional/Hachi/` or `Data/Lattices/`. Every proof
   instantiates a generic statement at the constants in
   `hachi/src/params.rs`, so the proof-side work is re-instantiation and
   literal repair, not re-derivation.

Self-consistency check that the target set fits this repo's structure: the
paper's ℓ = 30 at α = 10 gives μ = ℓ − α = 20 R_q-variables, and
`ML_VARS_LOW + ML_VARS_HIGH = 10 + 10 = 20`. ✔

## Target values

Diff to `hachi/src/params.rs`:

| Const | Current | Target | Side condition to re-discharge |
|---|---|---|---|
| `Q` | 4294967197 | **unchanged** | — |
| `EXT_DEGREE`, `EXT_W` | 4, 2 | **unchanged** | — |
| `RING_LOG_DEGREE` | 6 | 10 | none (spec admits any α) |
| `RING_DEGREE` | 64 | 1024 | `= 2^RING_LOG_DEGREE` (literal, checked not derived) |
| `GADGET_BASE` | 2 | 16 | `1 < b` ✔ |
| `GADGET_DIGITS` | 32 | 8 | `q ≤ 16⁸ = 2³²` ✔; minimal: `16⁷ = 2²⁸ < q` ✔ |
| `GAMMA` | 1 | 15 | `= b − 1`; `b − 1 ≤ q/2` ✔ |
| `BETA_SQ` | 8 192 | 1 887 436 800 | `= (MESSAGE_ROWS·DIGITS)·RING_DEGREE·GAMMA²`<br>`= (1024·8)·1024·15²` (literal, checked) |
| `MESSAGE_ROWS` | 4 | 1024 | `= 2^m`, paper m = 10 |
| `BLOCKS` | 2 | 1024 | `= 2^r`, paper r = 10 |
| `INNER_ROWS` | 2 | 1 | paper n_A = 1 — see Decision 2 |
| `OUTER_ROWS` | 2 | 1 | paper n_B = 1 — see Decision 2 |
| `KAPPA` | 65 535 | 16 | paper ω = 16; `κ² = 256 < q` ✔ — see Decision 1 |
| `ML_VARS_LOW` | 1 | 10 | `2^nl = BLOCKS` ✔ |
| `ML_VARS_HIGH` | 2 | 10 | `2^nh = MESSAGE_ROWS` ✔ |
| `ML_LOW_LEN` | 2 | 1024 | literal for `2^10` |
| `ML_HIGH_LEN` | 4 | 1024 | literal for `2^10` |
| `ML_POLY_LEN` | 8 | 1 048 576 | literal for `2^20` |

**No repo counterpart** (protocol layer deliberately absent, see `lib.rs`
§ Status): the paper's `n_D`/matrix `D`, τ = 4 (the `z`-decomposition
expansion), the `z` norm bound 30583, and the sparse-challenge count c = 16.
Do **not** invent constants for these; document their absence in the Phase 6
NOTES.md entry.

Remember the repo rule that derived constants are written as **literals**
(Aeneas models `const` arithmetic as fallible — a derived form extracts as
`Result`; see `params.rs` docstrings for `RING_DEGREE`, `GAMMA`, `BETA_SQ`).
The derivations are enforced by `tests/params_semantics.rs` and
`lean/Check.lean` § 1, both of which this plan updates.

## Decision points (settle with the user before Phase 1)

1. **`KAPPA = 16` vs keeping the invertibility ceiling 65 535.**
   Recommended: **16** — that is the paper's ω, which is what "same
   parameters" means. Consequence: the test
   `kappa_is_the_invertibility_ceiling` (`tests/params_semantics.rs:176`) no
   longer holds as stated (κ is no longer *at* the ceiling); rewrite it to
   assert legality only (`κ² < q`) and rename accordingly. The `KAPPA`
   docstring's "chosen at its ceiling" rationale must be rewritten too.
2. **`INNER_ROWS = OUTER_ROWS = 1`** breaks `dimensions_are_nondegenerate`
   (`tests/params_semantics.rs:200`), whose purpose was exercising multi-row
   index computations. At paper scale that duty is carried by
   `BLOCKS = MESSAGE_ROWS = 1024`. Relax the test to `≥ 1` for the two row
   counts, keep `≥ 2` for `BLOCKS`/`MESSAGE_ROWS`, and say why in the comment.
3. **Full-size tests and benches become opt-in** (Phases 4–5). At paper scale
   a single `commit` is hours of schoolbook arithmetic and the message alone
   is ~8 GiB. This deviates from the repo habit that tests exercise the real
   consts, so it needs an explicit sign-off, not a silent workaround.

## Phase 1 — Rust parameter flip (two isolated steps)

One commit per step; each ends with `cargo test` green. Two steps so that Lean
breakage in Phase 3 is attributable to one group.

### Step 1a — ring + gadget group

- [ ] `params.rs`: `RING_LOG_DEGREE = 10`, `RING_DEGREE = 1024`,
      `GADGET_BASE = 16`, `GADGET_DIGITS = 8`, `GAMMA = 15`, `KAPPA = 16`,
      and the *intermediate* `BETA_SQ` literal at old dimensions
      (`(4·8)·1024·225 = 7 372 800`) so `beta_sq_is_the_honest_l2_bound`
      stays true mid-flight.
- [ ] Update the affected `tests/params_semantics.rs` assertions:
      `gadget_digits_cover_the_modulus` / `gadget_digits_are_minimal` (hold at
      16/8, but re-read the doc comments — "pins to 32" is now "pins to 8"),
      `gamma_is_the_digit_bound` (holds), the `KAPPA` test per Decision 1.
- [ ] Rewrite stale provenance docstrings in `params.rs`:
      `RING_LOG_DEGREE` ("most likely to be revised" — it just was; now pinned
      by Fig. 9), `GADGET_BASE`/`GADGET_DIGITS` (base 16, 8 digits, Fig. 9),
      `GAMMA`, `KAPPA`.
- [ ] Fix stale comments in code: `ring.rs:285` ("both indices are below
      `N = 64`"), any other grep hit for `\b64\b` in `src/` comments.

No Rust *logic* changes: `ring::Rq::mul` reads `params::RING_DEGREE`;
`gadget::digit_at` divides by `GADGET_BASE` generically; `Fp` reduces every
product internally, so d = 1024 introduces no new overflow (the u64
no-overflow argument is per-`Fp`-operation, not per-vector).

### Step 1b — shape group

- [ ] `params.rs`: `MESSAGE_ROWS = 1024`, `BLOCKS = 1024`, `INNER_ROWS = 1`,
      `OUTER_ROWS = 1`, `ML_VARS_LOW = 10`, `ML_VARS_HIGH = 10`,
      `ML_LOW_LEN = 1024`, `ML_HIGH_LEN = 1024`, `ML_POLY_LEN = 1048576`,
      final `BETA_SQ = 1_887_436_800`.
- [ ] `dimensions_are_nondegenerate` per Decision 2;
      `evalsplit_shape_constants_are_consistent` holds as written (re-run it).
- [ ] **Feasibility gate**: `cargo test` will now hit the scale wall in
      `commit_semantics.rs` / `evalsplit_semantics.rs` (full-const-size
      messages). Apply the Phase 4 test restructuring *in this same step* so
      the tree is never red at HEAD.

## Phase 2 — re-extraction

- [ ] `make extract` under the **aeneas-extract** skill discipline: pinned
      charon+aeneas, determinism check, post-extract audits (axioms,
      whitelist transparency).
- [ ] **Gate**: `git diff hachi/lean/Generated.lean` must touch *only* the
      `params.*` definitions (constant values / their literals). Any
      body-level diff means something unexpected happened — stop and
      investigate before Phase 3.

## Phase 3 — Lean proof repair

Run as a **verify-campaign** ("Generated.lean regenerated and specs broke" is
its designed trigger). `lake build` in `hachi/` is the loop; `Check.lean` is
deliberately updated *last* so its failures enumerate what's left. Known
repair surfaces from the audit:

| File | What changes | Risk |
|---|---|---|
| `lean/Ring.lean` | `abbrev N : ℕ := 64` (line 40) → `1024`; `have hN : N = 64 := rfl` (line 721); comment text. Proofs quantify over `N` abstractly elsewhere. | Low |
| `lean/Scheme.lean` | The heavy one: `dd := zmodDigitDecomposition 2 32` (line ~690) → `16 8`; every `32`/`Fin 32`/`< 32`/`≤ 32` literal in the digit-loop specs (dozens of sites, lines ~690–870) → `8`; base literal `2` → `16`. `zmodDigitDecomposition` is generic in `b`, so this is substitution — but **audit for any step that used base-2-specific facts** (parity, `Nat` lemmas about 2) instead of `1 < b`. Also grep for any proof using `INNER_ROWS ≥ 2` / `OUTER_ROWS ≥ 2`. | Medium |
| `lean/EvalSplit.lean` | `nl`/`nh` abbrevs (lines 36–39): 1, 2 → 10, 10; the `have hlow/hhigh/hpoly` literal bridges (`2`, `4`, `8` → `1024`, `1024`, `1048576`); `norm_num` handles the new powers. | Low |
| `lean/Check.lean` § 1, § 3 | ~20 literal `example`s → new values (see Target table). § 3's "ring degree the Rust fixes is the degree ArkLib's modulus has" moves to 1024. | Low (it's the checklist) |
| `lean/RqBridge.lean`, `lean/Field.lean` | Expected untouched (α enters via `N`; field layer didn't move). They're in the build, so checked for free. | — |

- [ ] Exit criterion: `lake build` green, `Check.lean` § 4 prints every
      headline spec axiom-clean (no `sorryAx`), zero `sorry` in `lean/`,
      `lean-wip/` still empty.
- [ ] Fallback: if a Scheme.lean lemma resists mechanical repair (> a handful
      of stubborn goals), scaffold it with **prove-sorry** rather than
      hand-fighting.

## Phase 4 — Rust semantics tests at the new scale

The honest wall: at paper parameters the message is
`BLOCKS × MESSAGE_ROWS = 2²⁰` ring elements × 1024 coefficients ≈ **8 GiB**,
and one `commit` ≈ 2²³ schoolbook ring products of 2²⁰ `Fp`-ops each — hours.
The paper only reaches this scale with a multi-prime NTT and witness
streaming; this crate has neither, and a direct NTT over Z_q is impossible at
this modulus (NOTES.md § "The parameters forbid a radix-2 NTT": v₂(q−1) = 2).

Policy (per Decision 3):

- [ ] Keep on the real consts everything that stays feasible: all of
      `params_semantics.rs`, `ring_semantics.rs` (one d = 1024 mul ≈ 10⁶ ops),
      `gadget_semantics.rs`, linalg at row scale,
      `l2_norm_sq_does_not_overflow_at_the_maximum` (loops `RING_DEGREE`).
- [ ] Full-pipeline `commit_semantics.rs` / `evalsplit_semantics.rs` tests
      that build const-sized messages: mark the existing versions `#[ignore]`
      (run on demand: `cargo test -- --ignored`, release mode), and add
      shape-generic property tests over small ad-hoc matrices for the
      indexing/tamper-rejection logic they exercised.
- [ ] Record the deviation from "tests use the consts" in NOTES.md (Phase 6),
      with the arithmetic above as the justification.

## Phase 5 — benches and genesis re-freeze

Every frozen genesis baseline was measured at the old parameters and is
invalid the moment `params.rs` changes.

- [ ] Re-freeze genesis (per **rust-bench** / genesis stamp mechanics) for the
      operations that remain benchable at paper scale: `ring`, `gadget`,
      `linalg`.
- [ ] `commit`/`evalsplit` full-scale benches are unusable under schoolbook
      mul (hours per criterion iteration). `benches/exclusions.toml`'s own bar
      forbids "seemed slow" as an exclusion, so this needs an explicit user
      decision: a reduced-shape bench variant with a written note, or a
      signed-off policy exception. Do not decide this unilaterally.
- [ ] Note in the ledger that all pre-flip bench history is non-comparable
      (recentered).
- [ ] **Strong recommendation**: land the multiplication champion (the
      Karatsuba/convolution-split candidate, `opt-algo-swap`, with its proved
      `opt_eq_spec`) before or alongside this phase — at d = 1024 it is the
      difference between "benches are slow" and "benches are unusable", and
      the parameter change makes it urgent rather than optional.
- [ ] Stage only; the user commits (`.claude/settings.json` denies
      `git commit` — this is enforced, not a convention).

## Phase 6 — documentation closure

- [ ] NOTES.md: superseding entry under § "Chosen parameters" — the open
      question at NOTES.md:192 ("whoever has the paper to hand") is answered;
      record the Fig. 9 provenance of each value, the KAPPA and row-count
      decisions, and the Phase 4 test policy.
- [ ] `params.rs`: provenance rewrite — most values move from "Chosen,
      smallest that exercises the structure" to "Pinned by [NOZ26] Fig. 9".
- [ ] `lib.rs` § Status: parameter set is now the paper's; protocol layer
      (and so `n_D`, τ, `z`-bound, sparse challenges) still absent.

## Risk register

| Risk | Likelihood | Mitigation |
|---|---|---|
| Scheme.lean digit proofs used base-2-specific facts | Medium | Audit before flipping; prove-sorry fallback per lemma |
| A proof relied on `INNER_ROWS ≥ 2` | Low | Grep first; `Check.lean` catches it at build |
| Full-size tests OOM/timeout in CI | Certain | Phase 4 restructuring, decided up front (Decision 3) |
| Bench-policy conflict (exclusions bar vs infeasible commit bench) | Certain | Explicit user decision in Phase 5 |
| Extraction diff exceeds `params.*` | Low | Phase 2 gate halts everything |
| Lean numeric goals slow at 2²⁰ literals | Low | `norm_num`/`simp` handle these sizes; no `decide` on big powers |

## Effort shape

Phases 1–2: ~a day. Phase 3: the bulk (Scheme.lean literal sweep dominates).
Phases 4–5: mostly decisions plus mechanical re-freezing. Phase 6: an hour.
