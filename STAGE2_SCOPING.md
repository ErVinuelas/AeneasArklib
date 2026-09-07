# Stage 2 — audit + scoping record

Working document for Stage 2 of PLAN_PROTOCOL_LAYER.md (opened 2026-09-01).
The plan file carries the stages and decisions; this file carries Stage 2's
*outputs*: the audit results, the ordered target list with scale policies,
and the doc-sync list. Each section names its consumer, matching the plan's
item list. Sections marked ⏳ are being filled from the parallel audit
agents' reports.

> **Re-based 2026-09-03 on ArkLib PR #847 (pin `d51d8bc`).** Everything
> below was audited at `294b3f0b0`. Two things moved since: (i) the τ
> question closed — upstream decoupled the folded-witness digit count from
> δ (`BoundedDigitDecomposition`) and fixed **τ = 5** in `Hachi/Params.lean`
> (not 4, not 8; NOTES.md § "`BETA_SQ` corrected"), and (ii) upstream
> demoted the unsigned decomposition to a building block and renamed
> `commitBalanced` → `commit`, so Decision 4 is **revised** (promotion, not
> siblings — PLAN_PROTOCOL_LAYER.md Decision 4 ⊕⊕). Corrections from those
> two facts and from the six briefs (`briefs/STAGE2_CORRECTIONS.md`, now
> folded in) are marked **⊗⊗** and supersede the text they sit next to; the
> superseded text is kept where it records *why* a value was once believed.
> `file:line` citations are at `294b3f0b0` unless marked otherwise; re-read
> them at `d51d8bc` before relying on one.

Stage 2 exit criteria (from the plan): ordered, dependency-closed target
list with briefs and scale policies; Decisions 3–4 settled with the user;
params.rs extended, its checks green, extraction diff params-only; NOTES.md
records the audit.

## Status ledger

| Item | Consumer | State |
|---|---|---|
| Spec-stability record | NOTES.md | **done** — NOTES.md § "Spec stability at the pin" (Workstream 3) + the 2026-09-01 update under § "The digits are not balanced" |
| Decision 3 instance audit | TE work list | **done** — Ext4 ratified; the instance gap is one verified one-liner, SampleableType avoidable |
| Decision 4 minimal surface | target 1's brief | **done** — all three guesses confirmed, surface smaller than feared, zero spec edits |
| Parameter mapping | params.rs extension | **landed 2026-09-03** — 18 consts at τ = 5, name-bound to `Hachi/Params.lean` in `Check.lean` § 1; table below ⊗⊗ |
| API mapping (HachiRuntime walk) | Stage 3/5 signatures | **done** — argument classification, wire order, per-link signatures, S1–S7 |
| Erasure catalogue | Stage 3 briefs | **done** — one no-precedent shape found, resolved as an opt not a probe |
| Ordered target list + scale policies | Stage 3 | **done** — below |
| Per-target `arklib-analyze` briefs (6) | Stage 3 | **done 2026-09-01** — `briefs/`; their corrections folded here 2026-09-03 (⊗⊗) |
| Doc-sync list | the wave | **done** — items 4–6 rode the params landing |
| Decision 4 | target 1 | ⊗⊗ **revised 2026-09-03**: balanced = public API, unsigned = primitive (see § Decision 4) |
| Re-pin | everything | **done 2026-09-03** — `d51d8bc` (PR #847 head, draft); three proof-internal repairs, `make build` green (NOTES.md § "Re-pin to ArkLib PR #847") |

**Plan corrections produced** (all folded back into
PLAN_PROTOCOL_LAYER.md, marked ⊕): Decision 3 cheaper than costed;
Decision 4's surface confirmed and smaller; the τ/zDigits correction and
the two-gammas naming; the erasure catalogue's one no-precedent shape
(retiring the plan's "none" claim); four Stage 3 size cells; Risk 2
(fired, resolved as an opt), Risk 6 (retired), Risk 7 (second wall added),
Risk 8 (largely retired).

## Sequencing note: three commits' worth of work is in the tree

⊗ **Updated 2026-09-01 — the tree now carries three separable changes, not
one.** T0's extract formality is done (commit `6f30811`, `make extract`
`unchanged`), so the params.rs-extension gate is formally open. What is
uncommitted right now:

1. **The bench commit** (USR): `benches/gadget.rs`, `benches/linalg.rs`,
   `logs/README.md`, `logs/paper-impl/`, the `ledger_check.py` MODULES
   rider.
2. **The `BETA_SQ` correction** (a parallel working session): `params.rs`,
   `benches/candidate/src/params.rs`, `params_semantics.rs`,
   `commit_semantics.rs`, `Check.lean`, `Scheme.lean`, `lib.rs`, and a
   regenerated `Generated.lean`. This is a *fix to a stamped literal*, not
   the protocol extension — it belongs in its own commit with its own
   NOTES.md entry, and it is the one that must land before any additive
   params work, since it moves an existing value.
3. **The docs/skills sync**: `NOTES.md`, `aeneas-extract`,
   `skill-authoring`, this file, `PLAN_PROTOCOL_LAYER.md`.

Risk 5 says these stay separate. Order: `BETA_SQ` fix → bench commit →
protocol params.rs extension → gate: at that last step the
`Generated.lean` diff touches only *new* `params.*` definitions.
**Coordination hazard:** two sessions are editing this tree
simultaneously; before resuming any Rust-side work here, re-read
`params.rs` and `git status` rather than trusting a cached view.

⊗⊗ **All landed (2026-09-03), in a different order than planned:** the
bench commit went first (`60f2d69`, `39f9d5d`); the `BETA_SQ` fix landed
at **τ = 5**, not the τ = 8 the paragraph above describes (`342ebba` —
the τ = 8 value was never committed); this record (`68620ed`); the re-pin
to PR #847's head; then the params.rs extension, whose `Generated.lean`
diff was checked to be exactly the 18 new `def params.*` lines plus
`Source:` line shifts. The coordination hazard is over: one session.

## Doc-sync list

Done now (docs only, no extraction impact):

1. **NOTES.md § "Upstream aeneas, no fork"** — superseding entry added
   (2026-09-01): the local 4.33 port replaces "no fork"; lakefile comment is
   the source of truth; rebase policy per Decision 2.
2. **aeneas-extract skill** — the "upstream and unforked" paragraph replaced
   with the present-tense port record (per the skill-authoring cleanliness
   rules; the superseded narration lives in NOTES.md, not the skill).
3. **skill-authoring skill** — the vendored-suite paragraph's pin fact
   updated: Lake now fetches the port commit `6125cb9e`, which leaves
   `documentation/skills/` untouched (diff checked, empty).

⊗⊗ Done 2026-09-03, riding the params.rs landing as planned (one
regeneration, audited params-only). Items 4 and 5 were rewritten rather
than softened: the protocol layer is now "absent as code, present as
parameters", and the digit caveat states the promotion (unsigned = the
spec's building block, balanced = the gadget inverse target 1 promotes to
the public names). Original wording of the three items:

4. **`hachi/src/lib.rs` § Status** (line ~16): "specification still has
   unfilled definitional parameters" is stale post-merge — the protocol
   layer's spec is now definition-stable at the pin (Recursion excepted).
5. **`hachi/src/params.rs:28–39`** (the two honesty caveats): supersede per
   Decision 4's precise statement — the composed protocol chain is balanced
   (paper-faithful); the standalone unsigned instantiation remains as the
   proved bottom layer. The first caveat's "protocol layer is absent" also
   goes stale as the wave lands.
6. **`hachi/benches/exclusions.toml` header**: "The 19 `const`s in
   `hachi/src/params.rs`" — count goes stale when params grow; reword to not
   carry a literal count, or update the number with the extension.

## Decision 3 — instance audit (audited 2026-09-01)

Consumer: TE's work list. Headline: **F = Ext4 confirmed cheap** — the
translated layer never needs `SampleableType`, and the one missing
instance is a one-liner. (Method caveat: the Hachi tree is not fully built
at the pin, so demands were read off `variable` blocks + Lean's
auto-inclusion rule — the files' own `omit [BEq F] …` lines show the rule
is active; none of the target defs carries an `omit`.)

**Demands on F, by consumer:**

* ZeroCheck (`Constraints.lean:81–84`, Batch.lean same): `Field F, BEq F,
  LawfulBEq F` — no `DecidableEq F`, no `SampleableType F` anywhere in
  either file. `hypercubeSum` and the `c*Polynomial` helpers demand the
  F-set only (no q side).
* `computableRoundPoly` (`RoundPoly.lean:286`): `Field F, BEq F,
  LawfulBEq F` only.
* `roundCheck`/`roundOut` (`Rounds.lean:100–112`) and `honestComputeG`
  (`Completeness.lean:76`): add `DecidableEq F`. `SampleableType F` enters
  those files only *after* these defs (`Rounds.lean:184`,
  `Completeness.lean:163`).
* `finalCheck` (`FinalEval.lean:99–106`): no SampleableType. The single
  syntactic exception: `honestComputeY` (`FinalEval.lean:254`) sits after
  the file's `variable [SampleableType F]` (:175) and picks it up by
  section-variable accident — its body is exactly `wTableMleEval`, which
  is SampleableType-free. State the spec against `wTableMleEval` or pay
  the one-line instance.
* `endPieceCheck` (`EndPiece/Reduction.lean:157–161`): F-set + an explicit
  **`[BEq K.TCom]`** — the commitment carrier needs a BEq at
  instantiation, independent of F. `rhoDigitsShortCheck`/`liftShortCheck`
  don't mention F at all.
* `SampleableType` (F, `ShortChallenge`, `PublicParams`) appears **only**
  in extractors, escape events, `coreSpecSampleable`
  (`Composition.lean:200–217`), HonestChain/Correctness executions, and
  keygen — machinery we do not translate. **Verdict: avoidable.**

**φF for Ext4 exists and is finished**: `Ext.ofBaseRingHom
ext4Params.toExtensionParams : ZMod fieldSize →+* Ext4`
(`CompPoly/Fields/Extension/Bridge.lean:354–359`), with RingHom laws, simp
lemma, `Algebra` instance, and coefficient lemmas already proved.
Injectivity — the only extra fact any Hachi/RingSwitching site wants — is
free (`RingHom.injective` from a field into the `Nontrivial` Ext4).
Spelling caveat: keep the `fieldSize` spelling, never the numeral
`4294967197` (Ext4.lean itself needed a `qNum_eq` pin — the
literal-collision pitfall class).

**TE work list (final):**

| # | Item | Shape |
|---|---|---|
| 1 | `instance : LawfulBEq (Ext P) := inferInstanceAs (LawfulBEq (Vector F P.d))` in a `hachi/lean` bridge file (pin is frozen; upstreaming to CompPoly optional later) | **one-liner** — verified: `Ext`'s BEq *is* the Vector instance (`Defs.lean:284`) and v4.33.1 core provides `LawfulBEq (Vector α n)` |
| 2 | `abbrev φF4 := Ext.ofBaseRingHom …` on our side | zero work |
| 3 | `hφF` injectivity discharges at spec sites | one-liner per site |
| 4 | base-side instances at q = fieldSize (`Fact Prime` exists; `NeZero`, `BEq/LawfulBEq (ZMod q)` from core) | automatic + Check.lean audit lines |
| 5 | `Field/DecidableEq/BEq/Fintype Ext4` | all exist at the pin |
| 6 | `instance : SampleableType Ext4 := inferInstanceAs (SampleableType (Vector Hachi.Field 4))` | one-liner, **optional** — only to state specs verbatim against post-SampleableType machinery |
| 7 | `SampleableType (ShortChallenge …)` / `(PublicParams …)` | real work, needed only by untranslated machinery — **skip** (ArkLib itself flags the gap, `Composition.lean:195–199`) |
| 8 | the extracted-cpoly-Ext4 ↔ CompPoly-Ext4 bridge (RqBridge-shaped) | the actual TE proof workstream, ~2 days per the plan's calibration; unchanged by this audit |

**Planning corrections from this audit:** (a) `hAlpha`/`hAlphaEvals` are
`noncomputable` at the pin (Mathlib `evalAt` on the digit term) — the
translation targets for the α side are `alphaPublicEvals` /
`sumcheckPolyAlpha` / `zcTargetAlpha` via the computable `cEvalAt`
(`RingSwitch/Reduction.lean:451–468`, whose F-demand is `Field F` alone);
target 4's definition list is amended accordingly. (b) The Rust `Ext4`
carrier already extracts (Workstream 0 probe), so item 8 is proof work,
not extraction risk.

## Decision 4 — minimal balanced surface (audited 2026-09-01)

Consumer: target 1's brief. Headline: **smaller than the plan's re-sized
"similar to evalsplit" estimate at the core, wider at one unguessed middle
layer; total ≈ evalsplit or less.** No existing spec is edited.

**The balanced machinery is a wrapper, not a new algorithm.**
`balancedZmodDigitDecomposition.digit c e = (unsigned digit e of
(c + balancedShift).val) − ⌊b/2⌋`, all in `ZMod q` (`Gadget/Core.lean:148–164`);
`balancedShift b digits = ⌊b/2⌋·Σ b^e` (`Core.lean:133`), which at
(b=16, digits=8, q=2^32−99) evaluates to **2 290 649 224 = 0x88888888**.
`RingSwitch/RhoDigits.lean:86–89` proves `balancedDigit` equals the bundled
`.digit` **by `rfl`**, so the Norms bounds transfer for free. Digits land in
the paper's box [−8, 7]. Side conditions (`DigitBaseOk`,
`RingSwitch/Reduction.lean:175–181`) are pure `Prop` — nothing to translate.

**What the composed chain consumes** (`HonestChain.lean:348–356`,
`Correctness.lean:355–360, 384–395`): message and z decompositions balanced;
the correctness proof runs against `commitBalanced`
(`Commitment.lean:141–152` — `commit` with both decomposition slots swapped),
message and inner both balanced at δ = clog b q = 8. The quotient digits
enter via `rhoDigits` inside `liftMessage` and `rhoDigitsShortCheck` — later
targets. Nothing on the composed nonrecursive path uses the unsigned
decomposition; unsigned remnants are the recursive scaffold (banned by
Decision 1), a ball-relaxed corollary, and the bottom layer our 74 specs own.

**Rust surface (verdicts on the plan's guesses):**

| ArkLib source | New Rust |
|---|---|
| `balancedShift` | `params::BALANCED_SHIFT: u64 = 2_290_649_224` + `HALF_BASE: u64 = 8`; semantics test ties it to `8·Σ16^e mod q` |
| `balancedDigit` | `balanced_digit_at(c, e) = digit_at(c + Fp::new(BALANCED_SHIFT), e) − Fp::new(HALF_BASE)` — guess (a) confirmed, as a wrapper, no new loop |
| `gadgetDecompose` at balanced dd | `balanced_gadget_decompose` — **the unguessed real work**: `generate_decomps` hardcodes `gadget_decompose` (commit.rs:353,355) which hardcodes `digit_at` (gadget.rs:208), so the triple loop is copied with the balanced digit |
| `generateDecomps` at `ofDigits ddBal ddBal` | `generate_decomps_balanced` — guess (b) confirmed, a two-call-site copy |
| `commitBalanced` | `commit_balanced = generate_decomps_balanced` + existing `commit_with_decomps` — guess (c) confirmed: `commit_with_decomps` takes `&Decomp` as data, reused as-is |
| `rhoDigits` | one coefficient loop of `balanced_digit_at`, truncated at RING_DEGREE — its only consumers are later targets, so deferrable at zero cost |
| `rhoDigitCount` | **nothing** — equals `GADGET_DIGITS = 8` at these params (16^7 < q ≤ 16^8) |

Reused untouched: `base_pow`, `gadget_entry/matrix/mul`, `derived_message`,
`verify_weak`, `verify`, all norms, `Opening::honest`, all structs,
`flatten_blocks`.

**Spec collateral (Risk 8 resolved):** the six `dd`-mentioning specs
(`digit_at`, `digit_decompose`, `gadget_decompose` + loops, round-trip,
`generate_decomps` + loop, `commit`) get additive siblings against
`ddBal := balancedZmodDigitDecomposition 16 8 …`; `balanced_digit_at_spec`
reuses `digit_at_spec` plus two field-op steps (no new `Nat.digits`
arithmetic — the `rfl` fact above). `verify_weak_spec` needs **no** sibling
(opening is data; γ=16 covers both bounds). One bridge lemma
`Nat.clog 16 q = 8`. Traps recorded: sibling specs must not take a local
`[DecidableEq (ZMod q)]` binder (Commitment.lean:397–400 unification trap);
the Rust must do the **field** add of the shift (wrap mod q), never raw u64;
`BALANCED_SHIFT` joins the literal-collision watchlist.

⊗⊗ **Revised 2026-09-03 — promotion, not siblings.** ArkLib PR #847
(`eab7eaa32`) re-documents `zmodDigitDecomposition` as "the building block
the balanced digits are shifted from, not itself a Hachi gadget inverse",
renames `commitBalanced` → `commit` (deleting the unsigned committer), and
drops the unsigned norm lemmas (`zmodDigit_natAbs_le`,
`gadgetDecompose_zmod_vecLInftyNorm_le`, `…_l2NormSq_le`,
`…_vecL2NormSq_le`) plus `gadgetDecompose_apply`, `gadgetDecompose_eq_fun`
and `DigitDecomposition.toBounded`; `balancedDigit_valMinAbs_mem`
(`RhoDigits.lean`) is gone too. The user's call: adapt. Consequences for
the table above:

* The *names* flip. `balanced_digit_at` / `balanced_gadget_decompose` /
  `generate_decomps_balanced` / `commit_balanced` become the public
  `gadget_decompose` / `generate_decomps` / `commit` (matching the spec's
  `Hachi.commit`), and today's unsigned functions become the primitives
  they wrap — `digit_at` keeps its name (it *is* the spec's building
  block); the unsigned `gadget_decompose`/`generate_decomps`/`commit`
  survive under primitive names (`_unsigned` or module-private) because the
  74 proved specs are stated against them and `InnerOuter/Scheme.lean` is
  still decomposition-generic. Sizes unchanged from the table; one rename
  pass added; `commit_spec` re-pointed at the balanced committer becomes
  the headline.
* The unsigned layer now owns its one analytic input: `dd_digit_natAbs_le`
  in `hachi/lean/Scheme.lean` (a verbatim copy of the deleted upstream
  lemma), feeding ArkLib's surviving generic `…_of_digit_le` forms. The
  three proof sites that cited deleted lemmas were repaired at the re-pin.
* **A second digit function joins target 1.** The `z` side no longer
  instantiates `balancedZmodDigitDecomposition` at `zDigits`; it uses
  `boundedBalancedZmodDigit b τ x e =
  ((Nat.digits b (x.valMinAbs + ⌊b/2⌋·S).toNat).getD e 0) − ⌊b/2⌋`,
  `S = digitOnesValue b τ` (`Gadget/Core.lean`, PR #847) — *centre first*
  (`valMinAbs`, which `commit.rs`'s norm code already mirrors), shift in
  `ℤ` by `Z_BALANCED_SHIFT = 8·69905 = 559240`, clamp with `Int.toNat`,
  then `τ = 5` unsigned digits, minus 8. Its reconstruction law is
  conditional on `‖x‖ ≤ Z_BOUND` (`BoundedDigitDecomposition`), so its spec
  is an implication, not an equation — the `Prop`-side hypothesis travels
  on the `_spec`. Rust sketch: `bounded_z_digit_at(c, e)` over the centred
  `i64` representative. Consumers: target 2's `zDecompBounded`
  (`bddZ.gadgetDecompose`) at width `Z_DIGITS = 5`.
* `DigitBaseOk`'s "tautology" consequence
  (`rhoDigitsShortCheck_eq_true_of_digitBaseOk`) was deleted upstream as
  dead code. The check still translates verbatim (target 6); only the
  cited lemma is gone — a Stage 7 claims-ledger note, not a translation
  change.

## Parameter mapping (audited 2026-09-01)

Consumer: the params.rs extension. **Cross-validation note:** this audit
ran independently of the API walk above and reached the same values for
the two contested quantities — `zDigits = 8` (not τ = 4) and
(m₀, m₁) = (27, 3). Independent agreement, not a shared assumption.

**The paper-faithful instantiation is
`HonestRangeParams.ofPinnedDigitBase 16` = (b = 16, γ = 15, bZero = 16)**
(`HonestChain.lean:104–124, 165–175`), realized per
`hachiNonrecursive_perfectCorrectness`'s docstring
(`Correctness.lean:596–599`). Completeness forces γ = bZero − 1
(`HonestChain.lean:378`); the soundness chain hard-wires bZero = b
(`Composition.lean:286–293`). HachiRuntime's (7, 3, 2, 3) is toy
throughout — no value from it is usable.

⊗⊗ **Landed 2026-09-03 at τ = 5, 18 constants** (`hachi/src/params.rs`
§ "The protocol layer"; `tests/params_semantics.rs`, 27 tests; `Check.lean`
§ 1 `section ProtocolParams`). The table below is the *landed* one; the
audit's original τ = 8 table follows it for the record.

| Name | Type | Value | Ties to (`Check.lean` § 1) |
|---|---|---|---|
| `OMEGA` | u64 | 16 | `HachiParams.hachiOmega`; `KAPPA = 2·OMEGA` |
| `D_ROWS` | usize | 1 | `HachiParams.hachiN` (n_D) |
| `B_ZERO` | u64 | 16 | `HachiParams.params.bZero` |
| `CHAIN_GAMMA` | u64 | 15 | `HachiParams.params.γ` (= `B_ZERO − 1`, = `GAMMA − 1`) |
| `HALF_BASE` | u64 | 8 | `GADGET_BASE / 2` |
| `BALANCED_SHIFT` | u64 | 2 290 649 224 | `⌊b/2⌋ · digitOnesValue 16 8` (= `balancedShift 16 8` in ℕ, `< q`) |
| `Z_DIGITS` | usize | **5** | `HachiParams.hachiTau` |
| `Z_BOUND` | u64 | **131 072** | `HachiParams.honestZBound`; `hcap` (≤ capacity 5), `¬hcap` at 4 (= 30583), `16^5 < q` |
| `Z_BALANCED_SHIFT` | u64 | 559 240 | `⌊b/2⌋ · digitOnesValue 16 5` (`digitOnesValue_eq`) |
| `RLIN_CW` / `RLIN_CT` / `RLIN_CZ` | usize | 8192 / 8192 / **40 960** | `rlinCW 8 10`, `rlinCT 1 8 10`, `rlinCZ 8 5 10` |
| `RLIN_COLS` (μ₀) | usize | **57 344** | `HachiParams.mu0` (`mu0_eq`) |
| `RLIN_ROWS` (n₀) | usize | 5 | `rlinRows 1 1 1` |
| `D_QUAD_COLS` | usize | 8192 | `blocks · messageDigits` (`PublicParamsD.dMatrix` width) |
| `LIFT_COLS` | usize | **57 384** | `HachiParams.liftKeyWidth` (`liftKeyWidth_eq`); `rhoDigitCount q 16 = GADGET_DIGITS` proved via `clog_eq_delta` |
| `M_ZERO` (m₀ = M+1) | usize | **26** | `sumcheckWidthAtProfile{,_minimal}` at M = 25; coverage + minimality |
| `M_ONE` (m₁) | usize | 3 | **exception**: coverage `n₀ ≤ 2^m₁` + minimality only — ArkLib names no value |

Dropped from the audit's list: `RHO_DIGIT_COUNT` (contradiction 1 of the
briefs — it equals `GADGET_DIGITS`; the identity is a Check row, not a
const), `TAU` (a second name for `Z_DIGITS`), and `CHALLENGE_WEIGHT` (no
ArkLib expression *and* no consumer in translated code: the spec sees a
challenge only through `‖c‖₁ ≤ ω`; corpus sparsity is a bench-side knob,
recorded in `params.rs`'s module doc). Net: the F4 exception list shrinks
from four rows to **one** (`M_ONE`) — `Z_BOUND`, `M_ZERO` and `BETA_SQ`
gained ArkLib names in `Params.lean`, and `BETA_SQ`'s Check row is now
adjacent to the named `betaSq` (the "bonus win" below, realized).
Literal-collision watchlist at τ = 5: value 16 = `GADGET_BASE`, `GAMMA`,
`B_ZERO`, `OMEGA`; value 8 = `GADGET_DIGITS`, `HALF_BASE` (unrelated
quantities); value 8192 = `RLIN_CW`, `RLIN_CT`, `D_QUAD_COLS`; value 1 =
`INNER_ROWS`, `OUTER_ROWS`, `D_ROWS`; value 5 = `Z_DIGITS`, `RLIN_ROWS`
(new, unrelated: τ vs n₀); value 15 = `CHAIN_GAMMA` and the unsigned digit
ceiling `b − 1`. Rewrite hypotheses, never goals.

**The audit's original table (τ = 8 reading, superseded — kept for the
record of what moved):**

| Name | Value | Ties to |
|---|---|---|
| `D_ROWS` | 1 | Fig. 9 `n_D` (free var, paper pin like `INNER_ROWS`) |
| `Z_DIGITS` | 8 | `zDigits := Nat.clog b q` (`Correctness.lean:511`) |
| `RHO_DIGIT_COUNT` | 8 | `rhoDigitCount q bZero` (`RhoDigits.lean:66`) |
| `B_ZERO` | 16 | `ofPinnedDigitBase 16 .bZero`, forced = b |
| `CHAIN_GAMMA` | **15** | `P.γ = bZero − 1` — *not* the existing `GAMMA` |
| `RLIN_COLS` (μ₀) | 81920 | `rlinCols 1 8 8 8 10 10` (`Rlin.lean:153`) |
| `RLIN_ROWS` (n₀) | 5 | `rlinRows 1 1 1` (`Rlin.lean:158`) |
| `RLIN_CW/CT/CZ` | 8192 / 8192 / 65536 | `Rlin.lean:161–166` |
| `D_QUAD_COLS` | 8192 | `blocks · messageDigits` (`Gadgets.lean:70`) |
| `LIFT_COLS` | 81960 | `μ₀ + n₀·δρ` — lift key width + w̃ row count |
| `M_ZERO` (m₀) | 27 | least m₀ with `LIFT_COLS·d ≤ 2^m₀` |
| `M_ONE` (m₁) | 3 | least m₁ with `n₀ ≤ 2^m₁` |
| `OMEGA` | 16 | `ShortChallenge Φ ω`; upgrades `KAPPA`'s magic `2·16` |
| `TAU` | 4 | `quadEvalBetaSq`'s τ — moves in from a test-local const |
| `Z_BOUND` | 30583 | **no ArkLib name** — Fig. 9 / reference impl only |
| `CHALLENGE_WEIGHT` | 16 | **no ArkLib name** — sampler weight c |

**Flags:**

* **F1 — two gammas.** `CHAIN_GAMMA = 15` vs existing `GAMMA = 16`
  (weak-opening γ̄ = b). Different ArkLib quantities differing by 1; every
  Check entry must cite which. Confirms the API walk's S7 and settles the
  naming.
* **F2 — ⊗⊗ SUPERSEDED 2026-09-03: one τ, and it is 5.** The 2026-09-01
  correction below was right that τ and `zDigits` are one quantity and
  wrong about its value, because it read the value off a hypothesis
  (`hqz : q ≤ b ^ zDigits`) that PR #847 removed: the `z` gadget is a
  `BoundedDigitDecomposition` sized from the honest bound `‖z‖∞ ≤ 131072`,
  and five balanced digits (capacity 489335) is the least that fits
  (`tau_minimal`); Fig. 9's four carry exactly 30583, the paper's own `z`
  bound, under a statistical analysis ArkLib does not formalize. `BETA_SQ`
  is `41976510894886092800` = `HachiParams.betaSq`. Consequence for target
  2: `Z_DIGITS = 5 ≠ GADGET_DIGITS = 8`, so the "loses a refactor" verdict
  in § Cross-audit contradiction reverses — the `gadget_*` functions stay
  hard-wired to `GADGET_DIGITS` and the `J` side gets `_z` siblings at
  `Z_DIGITS` (additive; never re-parameterize the four frozen functions).
  Original entry:
  **τ vs zDigits — ⊗ CORRECTED 2026-09-01: there is only one τ, and
  it is `zDigits = 8`.** This entry previously said τ = 4 was correct
  *inside* the weak-opening `BETA_SQ`, with the two τ's to be reconciled by
  a comment. That is wrong, and `BETA_SQ` was wrong with it. Direct check
  of the pin: `quadEvalBetaSq`'s τ is a *formal parameter*
  (`def quadEvalBetaSq (γ b τ d m δ : ℕ)`, `QuadEval/Soundness.lean:106`),
  and **all 16 instantiations in the Hachi tree pass `zDigits` into that
  slot** — `quadEvalBetaSq γ b zDigits (deg φ) m messageDigits`, 10 in
  `QuadEval/Soundness.lean`, 6 in `Composition.lean`, none at 4 and none
  with a second τ. The three trailing arguments of the weak-opening
  relation there are `(βSq, γ, 2*ω)`, which is exactly our
  `verify_weak … 16 32` slot, so the βSq our commitment layer checks *is*
  that value. Combined with this document's own finding (S1 /
  § "Cross-audit contradiction": `Correctness.lean:509–511` sets
  `messageDigits = innerDigits = zDigits = δ P = 8`, `hqz` discharged by
  `Nat.le_pow_clog`), τ = 8 throughout. The paper's τ = 4 counts digits of
  an already-short response vector and has no home in this formalization,
  because a `DigitDecomposition` is a function on all of `ℤ_q` and must
  satisfy `q ≤ b^digits`. `BETA_SQ` was corrected to
  `704250333132185328448176128` accordingly — see NOTES.md
  § "`BETA_SQ` corrected: τ = zDigits = 8". Any protocol-layer loop over z
  digits uses 8.
* **F3 — literal collisions, complete list.** Value **16**: five names
  (`GADGET_BASE`, `GAMMA`, `B_ZERO`, `OMEGA`, `CHALLENGE_WEIGHT`). Value
  **8**: `GADGET_DIGITS`, `Z_DIGITS`, `RHO_DIGIT_COUNT`. Value **8192**:
  `RLIN_CW`, `RLIN_CT`, `D_QUAD_COLS` (this coincidence is exactly the
  reference impl's `reuse_mats = true`). Value **4**: `EXT_DEGREE` alone
  (⊗ `TAU` moved to the value-**8** row per F2 — if it is introduced at
  all it is a third name for 8, alongside `GADGET_DIGITS`/`Z_DIGITS`).
  Value **1**: `INNER_ROWS`, `OUTER_ROWS`, `D_ROWS`. Value
  **15**: `CHAIN_GAMMA` and the honest unsigned digit ceiling `b − 1`.
  Plus the existing 1024 cluster. Proof discipline: rewrite hypotheses,
  never goals.
* **F4 — ⊗⊗ reduced to one row (2026-09-03).** `Z_BOUND` is now
  `honestZBound`; `M_ZERO`'s coverage + minimality are ArkLib's own
  `sumcheckWidthAtProfile{,_minimal}`; `CHALLENGE_WEIGHT` was not
  introduced. Only `M_ONE` keeps the exception (coverage `n₀ ≤ 2^m₁` and
  minimality, no named value), recorded at the constant and in
  `Check.lean` § 1's section header. Original entry: **two constants have
  no ArkLib expression**: `Z_BOUND` and
  `CHALLENGE_WEIGHT` are paper/reference-impl provenance only, so the
  house rule's "Check.lean entry proving the literal equals the ArkLib
  expression" is *unsatisfiable* for them — their entries can only be
  arithmetic identities plus an explicit provenance comment. `M_ZERO` and
  `M_ONE` have no closed form either: ArkLib leaves them free under
  inequalities, so their entries prove coverage + minimality, not
  equality.
* **F6 — Check.lean technique** ⊗⊗ (as landed): the clog fact is
  imported, not re-proved — `HachiParams.clog_eq_delta` rewritten at the
  literals discharges `rhoDigitCount q 16 = GADGET_DIGITS`; every other
  named tie is `rw [<Params.lean>_eq]; simp [params.X]`. One import,
  `ArkLib.Commitments.Functional.Hachi.Params` (which pulls the chain).
  Original note: the clog-valued entries cannot go
  through bare `simp`/`decide` at q ≈ 4.3e9; use the
  `Nat.clog_le_iff_le_pow` + `omega` pinning pattern
  (`HachiRuntime.lean:146–150`).

**Bonus win available**: tying `BETA_SQ`'s Check entry to the *named*
`quadEvalBetaSq` for the first time (today it is an unnamed recomputation
— and that is exactly how the τ error survived review: an unnamed
recomputation agrees with itself at any τ). ⊗ Per F2 the tie is to
`quadEvalBetaSq γ b zDigits …` at `zDigits = GADGET_DIGITS`, so it needs
no new `TAU` const at all. `OMEGA` still does the same for `KAPPA`'s magic
`2 * 16`.

**Size**: params.rs +230–300 lines, params_semantics.rs +100–150,
Check.lean § 1 +50–80. Gate at landing: the `Generated.lean` diff is
solely new `def params.X : Std.UN := v#uN` lines — anything else stops
the line.

## API mapping from HachiRuntime (audited 2026-09-01)

Consumer: Stage 3/5 signatures. Source: `hachiNonrecursiveConcrete`
(`Concrete.lean:79–87`) + the HachiRuntime honest run + `Correctness.lean`'s
wire format. Full argument table and signature sketches in the audit
agent's report; the load-bearing extract:

**Inputs vs params.** Function inputs: `pp` (A, B, `pp.dMatrix`), the lift
key `d_key`, the message (`poly`/`decomp`), the query `(x, y)`, and the
challenge streams. Everything else is a params.rs const. `φF` is *not* an
argument — it is the fixed cpoly base-embedding. Challenges appear in **no**
scheme argument: the opening is a `Reduction` whose challenge oracle is
supplied at run time (`Execution.lean:196–212`) — public-coin, as assumed.
The undischarged `[SampleableType (ShortChallenge …)]` gates only the
*soundness* composition (`Composition.lean:195–201`); the honest run uses
`Inhabited` defaults.

**Wire format** (composed opening, `Correctness.lean:189–201, 508–512`):
input-adapter(0) ⧺ bridge(0) ⧺ QuadEval(2) ⧺ R^lin(0) ⧺ lift(2) ⧺ batch(0)
⧺ zero-check(m₀+m₁) ⧺ sc-bridge(0) ⧺ rounds(2m₀) ⧺ finalEval(1) ⧺
terminal(1). Only three boolean checks exist in the composed verifier —
`roundCheck`×m₀, `finalCheck`, `endPieceCheck`; rows 1–7 are pure statement
maps.

**Challenge-stream shape** (wire order): `fold : [Rq; 2^r]` (one round
carrying a vector; ℓ₁ ≤ ω lives in the *type* — Rust needs a precondition
or explicit check, since `relOut` deliberately has no challenge-norm
check), then `alpha : F`, then `tau0 : [F; m₀]`, `tau_alpha : [F; m₁]`
(separate scalar rounds), then `sumcheck : [F; m₀]` interleaved with the
`(g⁰, gᵅ)` message pairs. At Fig. 9 (n_D = 1): 1024 ring + 58 field
challenges.

**Proposed module signatures** (Stage 3): `quadeval.rs`
(`bridge_stmt`, `carrier_commit_v`, `honest_response`), `ringswitch.rs`
(`rlin_stmt`, `honest_lift_witness`, `lift_message`, `lift_commit`),
`zerocheck.rs` (`zc_target_alpha`, `w_table_mle_eval`), `sumcheck.rs`
(`round_polys`, `round_check`, `round_out`, `final_check`), `endpiece.rs`
(`lift_short_check`, `end_piece_check`); Stage 5 composed
`open`/`verify` over a `Challenges` struct + `OpeningProof {v, t, rounds,
y_prime, w}`. New params.rs consts implied: `D_ROWS`, `B_ZERO`,
`GAMMA_LIFT`, `OMEGA`, `Z_DIGITS`, `M0`, `M1`, `MU0`, `N0`,
`TABLE_WIDTH` (cross-check against the parameter-mapping audit).
⊗⊗ Landed names: `D_ROWS`, `B_ZERO`, `CHAIN_GAMMA`, `OMEGA`, `Z_DIGITS`,
`M_ZERO`, `M_ONE`, `RLIN_COLS`, `RLIN_ROWS`, `LIFT_COLS`. The composed
opening's signature also gains `hcap`/`zBound` on the spec side
(`hachiNonrecursiveOpening … (hcap : zBound ≤ balancedDigitCapacity P.b τ)`),
which the Rust discharges statically from `Z_BOUND`/`Z_DIGITS`.

**Surprises (S1–S7), each with a consequence:**

* **S1 — ⊗⊗ superseded: `zDigits` = τ = 5 (PR #847), neither δ nor Fig. 9's 4; `μ₀ = 57344`.** Original: `zDigits` = δ = 8, not the paper's τ = 4.** The scheme discharges
  `hqz : q ≤ b^zDigits` via `Nat.le_pow_clog` (`Correctness.lean:510–516`);
  τ = 4 fails it at Fig. 9 (16⁴ < q). The plan's mapping list ("τ = 4")
  maps to **8** for the composed chain; `μ₀ = 81920`. ⊗ **CORRECTED
  2026-09-01:** the final sentence of this entry used to exempt `BETA_SQ`
  ("derived with τ = 4 … belongs to the weak-opening relation only"). It
  does not — τ and `zDigits` are *one* quantity, ArkLib says so itself
  (`QuadEval/Gadgets.lean:123`: "`zDigits = τ`"), and every
  `quadEvalBetaSq` instantiation passes `zDigits` into the τ slot. So the
  8 in this entry applies to `BETA_SQ` too; it was corrected to
  `704250333132185328448176128`. See F2 for the full evidence.
* **S2 — don't copy the runtime's `m₁ = 1`.** Soundness needs
  `n₀ ≤ 2^m₁` (`Composition.lean:293`); at n_D = 1, set `M1 = 3`.
* **S3 — toy q fails `q % 8 = 5` and `(2ω)² < q`** — the runtime exercises
  the honest path only; real params satisfy both.
* **S4 — `m₀ ≈ 27` at Fig. 9, and the naive sumcheck prover is not
  runnable there at all** (`(bZero+1)^{m₀}` monomials; the toy run's
  6-minute elephant at m₀ = 5). Target 5's scale policy plans REDUCED
  cases from day one; the Stage 6 algorithm swap on `computableRoundPoly`
  is mandatory, not elective.
* **S5 — the terminal message is witness-sized**: `LiftedWitness` ≈ 335 MB
  at Fig. 9. Non-succinct by design; dominates any proof-size bench.
* **S6 — two different D matrices**: `pp.dMatrix` (Eq. 16 carrier key,
  keygen-sampled, ships inside `pp`) vs the lift key `D` (caller input,
  `dRows × (μ₀+n₀·δ)`). Rust naming keeps them apart: `pp.d_matrix` vs
  `d_key`.
* **S7 — γ collision**: params.rs `GAMMA = 16` is the weak-opening γ̄ = b;
  the composed chain's `P.γ` pins to `bZero − 1 = 15`
  (`HonestChain.lean:188–193`). Two consts, near-identical values — the
  literal-collision pitfall class. Name the new one `GAMMA_LIFT` (or
  similar) and rewrite hypotheses, not goals, in proofs. ⊗⊗ Landed as
  `CHAIN_GAMMA`.

Confirmations: lift key caller-supplied ✓; balanced digits on the composed
path ✓; `relOut` c6 is the ℓ∞ ≤ γ ball relaxation, so Rust range checks are
`‖·‖∞ ≤ γ`; `ShortChallenge`/`RoundMsg` degree bounds are subtype erasures
needing runtime checks or stated preconditions.

## Erasure catalogue (audited 2026-09-01)

Consumer: Stage 3 briefs. Per-definition table (all six targets, with
verified Lean shape, erasure, in-repo precedent and risk notes) is in the
audit report; the decision-relevant content:

### One no-precedent shape — the plan's "none" claim is wrong, once

**`CMvPolynomial n F` as a runtime value.** `Lawful n R = {p :
Std.ExtTreeMap (Vector ℕ n) R // noZeroCoef}`, with `eval`/`eval₂` as
`ExtTreeMap.foldl`. Nothing in `hachi/src` or cpoly's Rust carries a
tree-map or sparse monomial dictionary; it is almost certainly above the
Aeneas ceiling. Reached verbatim by `hypercubeSum`, `computableRoundPoly`,
`honestComputeG`, `sumcheckPolyZero`/`Alpha`, the four `c*Polynomial`
helpers, and both of `finalCheck`'s eval subterms.

**Recommended resolution: a Lean-side `Foo.opt` to dense-table forms, not
an extraction probe.** Every runtime use is an *evaluation*, and the
factoring lemmas already exist at the pin (`eval_sumcheckPolyZero`/`Alpha`
at `Constraints.lean:1414/1426`, `cMultilinearExtension_eval`,
`wTableMleEval_eq` at `:352`), so the optimization removes the type
entirely and lands on proved cpoly shapes. The naive CMvPolynomial route
is computationally absurd anyway (`cMultilinearExtension` materializes
2^m₀ Lagrange terms), so this is the same rewrite Stage 6 would demand —
it just moves to Stage 3 as a prerequisite. **This is the one place the
plan's "escalate to a probe only for a shape with no precedent — none is
currently on the list" needs amending.**

### An unlisted prerequisite step

⊗⊗ Brief 4 sharpened both prerequisites: (A) the `noncomputable` marker on
`hAlpha`/`hAlphaEvals` has a single cause and `cEvalAt_eq_evalAt_toPoly`
alone repairs it (`rhoDigits_evalAt` is orthogonal); (B) the
CMvPolynomial→dense rewrite must be **additive** — deleting the type
orphans the degree theorems at `Constraints.lean:1082,1097`. Brief 4 also
found `cEvalAt` at mixed carrier is an unowned minor variant.

**`hAlpha`/`hAlphaEvals` are `noncomputable` at the pin**
(`Constraints.lean:176, 213` — Mathlib `evalAt ∘ toPoly` in the digit
term). A computable Lean sibling is a prerequisite target 4 step the plan
does not list: swap `evalAt∘toPoly` for `cEvalAt` on `rhoDigits`
directly. The bridging lemmas (`cEvalAt_eq_evalAt_toPoly`,
`rhoDigits_evalAt`) are already in the pin, so this is a small stated
step, not research. (Independently found by the Decision 3 audit.)

### The positive the plan undersells

**Targets 4–6's field and evaluation layer already exists proved** in the
pinned cpoly dependency: Ext4, univariate Ext4 polynomials with proved
Horner `eval`, and the whole MLE toolkit — `eq_tilde`, `lagrange_basis`,
`dot`, `eval_mle`, `eval_mle_layer`. `wTableMleEval` in particular has a
direct precedent (`eval_lagrange`), not a new implementation.

### Shape-list corrections

1. `roundCheck` has **two** conjuncts, not three; `finalCheck` has the
   three (including `decide(bound ≤ rlin.bound)`).
2. `wTable`'s split is **two-level** (z rows, then digit rows with a
   further `/δ`, `%δ` sub-split), not a single `idx/d` branch. Also
   `finFunctionFinEquiv` cancels against `.symm` in every consumer, so no
   bit machinery survives — the loops are plain flat-index loops.
3. `honestComputeG` lives in `Sumcheck/Completeness.lean:76`, not in
   RoundPoly/Rounds/FinalEval.
4. The Eq. 20 checks live only in `QuadEval/Reduction.lean`
   (`relOut`:258, `paperRelOut`:335); Gadgets.lean holds only the
   `tensorG`/`tensorG1` building blocks.
5. `computableRoundPoly`'s "2^k counter loop with bit extraction" is right
   for the **outer sum only**; the summand carries the CMvPolynomial gap.

⊗⊗ From the briefs (2026-09-01, folded 2026-09-03):

6. **The naive sumcheck monomial count is `(2b+1)^m₀ = 33^m₀`, not
   `(bZero+1)^m₀`** — ArkLib's `scripts/HachiRuntime.lean:37` undercounts
   it, against that file's own `roundDegZero b = 2b`. At `b = 16` the naive
   form is impossible at *every* `m₀ ≥ 5`, so target 5's exclusion of it is
   unconditional, not scale-dependent.
7. "No bit machinery survives" is false on the `m₁` side
   (`Constraints.lean:858,890`) — benign, it is cpoly's `lagrange_basis`.
8. **A `Prop`-relation → `Bool` shape is missing from the catalogue**
   (target 2's `relOut` conjuncts): the corresponding `_spec` is an iff,
   not an equality. The bounded `z` decomposition adds a sibling shape:
   a reconstruction law *conditional* on a norm bound, so its spec carries
   the bound as a hypothesis.
9. **The sumcheck verifier needs an explicit degree check** that the
   subtype erasure silently drops (`RoundMsg`'s degree bound) — a
   correctness item, not a performance one.
10. Two translation traps that cost 3× if translated literally:
    `roundProver.output` recomputes the dominant term twice more (target
    5), and `endPieceCheck`'s conjunct B2 is quadratic in `d` (41.9 M
    `balancedDigit` calls) purely from the spec's `∀i∀u∀k` nesting (target
    6).
11. `hachi/src` docstring citations of ArkLib went stale under the pin
    bumps by a different offset per file (`Gadget/Core.lean` +36 at
    `294b3f0b0`, more at `d51d8bc`; `Vectors.lean` +6;
    `NormBounds/Basic.lean` +30). A refresh pass regenerates
    `Generated.lean`, so it rides a target landing.
12. ⊗⊗ **`ShortChallenge`'s ℓ₁ bound is erased at the Rust API — recorded
    2026-09-07, deliberately not repaired yet.** ArkLib's `relOut`
    (`QuadEval/Reduction.lean:258`) takes its challenges as
    `Fin (2^r) → ShortChallenge Φ ω`, the subtype `{c : Rq Φ // ‖c‖₁ ≤ ω}`
    (`:151`); the *type* carries the bound, which is why `relOut` has no
    norm check on `c` (`:149`). Target 2's `quadeval::rel_out` and
    `paper_rel_out` take `c: &PolyVec` unconstrained, so `‖c‖₁ ≤ ω` is a
    caller precondition the Rust type does not state, and nothing in the
    crate checks it. Decision: no `rel_out_spec` exists yet — the function
    is unrunnable at Fig. 9 (W4) and its statement needs `pp`/`D` — so the
    repair belongs where that spec is stated, Stage 5, where the composed
    verifier is the first *producer* of a challenge. There it is one of two
    forms: quantify `c : ShortChallenge Φ ω` in the statement and pass
    `c.val` to the Rust (precondition stated, API unchanged), or a
    checked-constructor newtype whose `new` decides `‖c‖₁ ≤ ω` over the
    existing `commit::l1_norm` (the brief's proposal; a newtype with no
    producer would be dead API today). Until one lands: no semantics test or
    bench feeds `rel_out` a long challenge, and none may claim to have
    exercised the bound. Ledger entry for the spec author, not a scale
    policy.

### Minor variants (precedented in shape, new in coefficient type or sign)

Plain non-negacyclic growing-degree polynomial **mul over Fp** for
`cRowSum` (cpoly's proved `mul` is at Ext4; ring.rs's is Fp but
negacyclic); the **signed asymmetric box** check for `InSb` (two u64
comparisons — `centered_abs` is the absolute-value sibling, not the
signed one); an **Ext4 power loop** for `alphaTilde`. None is
probe-level. `Nat.clog` is not translatable at all — params-literal
discipline, as already planned.

### Cross-audit contradiction, resolved by direct check — ⊗⊗ and re-resolved the other way

⊗⊗ **2026-09-03: the erasure audit's risk note was right after all,
one digit off.** `zDigits = τ = 5 ≠ GADGET_DIGITS = 8` at the new pin
(`Hachi/Params.lean`, `hachiTau`). The section below correctly showed that
at `294b3f0b0` the value was 8 *because of `hqz`*; PR #847 removed `hqz`,
and the consequence reverses: **target 2 regains the refactor**, as
additive `_z` siblings of `gadget_matrix`/`gadget_mul`/`gadget_decompose`
at `Z_DIGITS` (brief 2 item 8: the reused pieces are `gadget_mul` /
`gadget_decompose`, not `gadget_matrix`) — never a digits parameter on the
frozen four. And the `J`-side decomposition is the *bounded* one
(`zDecompBounded`, § Decision 4 ⊗⊗). The `m₀` remark also moves: at τ = 5,
`LIFT_COLS·d = 57384·1024 = 58 761 216`, `2²⁵ < that ≤ 2²⁶`, so **m₀ = 26**
(`M = 25`, `sumcheckWidthAtProfile`). The 2026-09-01 text:

The erasure audit's risk notes asserted `zDigits = τ = 4 ≠
GADGET_DIGITS = 8`, forcing a re-parameterization of the currently
params-hardwired `gadget_*` functions. **That is wrong, and the
re-parameterization is not needed.** Verified directly:
`Correctness.lean:509–511` instantiates `messageDigits`, `innerDigits`
*and* `zDigits` all at `δ P`, discharging `hqz` with
`Nat.le_pow_clog P.hb q`; and the arithmetic is decisive — `hqz : q ≤
b^zDigits` is false at (16, 4) since 16⁴ = 65536 ≪ q. The τ reading comes
from the *generic* docstring at `QuadEval/Gadgets.lean:122–123` ("in this
reduction … `zDigits = τ`"), which names the paper's symbol at the
definition site; the composed instantiation pins it to 8. Two audits
reached 8 independently from the instantiation. **Consequence: zDigits =
GADGET_DIGITS = 8, so `gadget_matrix`/`gadget_decompose` stay hardwired to
the existing consts and target 2 loses a refactor.**

(Similarly the erasure audit's incidental "m₀ ≈ 25" is superseded by the
parameter audit's explicit arithmetic: LIFT_COLS·d = 81960·1024 =
83 927 040, and 2²⁶ < that ≤ 2²⁷, so **m₀ = 27**.)

### Scale/overflow hazards at Fig. 9

All coefficient arithmetic routes through proved cpoly ops (the q < 2³²
headroom argument is already done); norms are at u64/u128 with proved
specs. The real hazards are (a) **guard-ordered Nat subtractions**
(`idx/d − μ`, `u − μ`) whose branch order must be preserved in Rust, (b)
the **2^m₀ Ext4 tables** — at m₀ = 27 a materialized table is ~4 GiB, so
target 4's scale policy must avoid materializing it even in REDUCED
cases, and (c) nothing else.

## Ordered target list + scale policies

Dependency edges unchanged: **{1 ∥ 2} → 3 → 4 → {5 ∥ 6}**, TE beside 1–3
and landing before 4's specs. Sizes below are re-estimated against the
audits; ⊕ marks a change from the plan's Stage 3 table.

| # | Target | Size | ⊕ Change from the plan |
|---|---|---|---|
| 1 | balanced digit layer | ≈ evalsplit | ⊕ core is a 3-line wrapper over the proved `digit_at` (`rfl`-equal upstream); bulk is one mechanical `balanced_gadget_decompose` copy; `rhoDigitCount` needs no const (= `GADGET_DIGITS`). ⊗⊗ **promotion, not siblings** (§ Decision 4): a rename pass, `commit_spec` re-pointed at the balanced committer; **plus a second digit map**, `boundedBalancedZmodDigit` at τ = 5 (centre → shift by `Z_BALANCED_SHIFT` → clamp → 5 digits − 8), with a conditional spec. Its two `ring::mul`-bound commit-path functions inherit the Fig. 9 exclusion (brief 1 refinement) |
| 2 | QuadEval fold | similar–larger | ⊕ ~~loses a refactor~~ ⊗⊗ **regains it**: `Z_DIGITS = 5 ≠ GADGET_DIGITS`, so `gadget_mul`/`gadget_decompose` get `_z` siblings (additive); `honestComputeResp` takes the bounded `z` decomposition (`zDecompBounded`), `jMatrix` is `8192 × 40960`. `InSb` signed-box check is a new minor variant; `relOut` conjuncts are `Prop`→`Bool` (iff specs). Its honest-path *tests* need target 1's balanced digits, so `{1 ∥ 2}` holds for code only |
| 3 | ring-switch | similar | unchanged; all shapes precedented (`flatten_blocks`, `gadget_entry`, `vec_l_infty_norm`). ⊗⊗ `lift_message` needs its own REDUCED note (W3, allocation), `liftShortCheck` at real consts carries 640 MiB resident `z`; `liftShortCheck`/`rhoDigitsShortCheck` live in `endpiece.rs` per § API mapping (the row here is scale policy only) |
| 4 | zero-check | larger | ⊕ **+2 prerequisites**: a computable `hAlpha` Lean sibling (bridging lemmas exist at the pin), and the CMvPolynomial→dense-form opt. ⊖ **offset**: cpoly's proved MLE toolkit covers `wTableMleEval` directly |
| 5 | sumcheck | largest | ⊕ the CMvPolynomial gap is *here* in force, and m₀ = 27 makes the naive form unrunnable — the dense rewrite is a Stage 3 prerequisite, not a Stage 6 option |
| 6 | end piece | smaller–similar | unchanged; every shape precedented, needs only F. ⊗⊗ conjunct A *is* `lift_commit` (57 384-wide `hachiLiftCom`), so it inherits REDUCED (W1) while conjunct C is W2 — two separate notes in one function; `rhoDigitsShortCheck` is provably constant-true at Fig. 9 (lemma deleted upstream, fact stands): translate verbatim, note it in the claims ledger |

**Net schedule read:** targets 1 and 2 each shed work; target 4 roughly
holds (two prerequisites against one large precedent win); target 5 grows,
because the dense rewrite it needs to run at all was previously booked as
Stage 6 optimization. The 8–12 day Stage 3 estimate survives, but its
*internal* distribution shifts toward target 5, and one Stage 6 elephant
is now paid earlier.

### Scale policies (fixed here, applied at each freeze)

The governing arithmetic: ⊗⊗ m₀ = **26** at τ = 5, so any 2^m₀-shaped
object is ~6.7·10⁷ entries — a materialized Ext4 table is ~2 GiB (was
~4 GiB at m₀ = 27). Full-const runs are therefore still impossible for
anything cube-shaped, independently of `ring::mul`.

⊗⊗ **Five walls, four removal conditions** (from the briefs), and every
policy note must name which one it cites:

| # | Wall | Site | Removed by |
|---|---|---|---|
| W1 | schoolbook `ring::mul` width | `lift_commit` 57 384-wide; `relOut`'s 1×8192 mat-vecs; `commit`'s `A·s` | a sub-quadratic / NTT mul champion |
| W2 | m₀'s cube, `2^26` | `wTableMleEval`, `hZero`; the folded cube; end-piece conjunct C | **nothing in mul** — the dense/split rewrite |
| W3 | allocation in the lift, ~450 MiB–1 GiB at τ = 5 | `lift_message` | fusion (never materialize the concatenation) |
| W4 | 64 GiB `wit.message` at Fig. 9 | target 2's witness | streaming witness (no skill yet) |
| W5 | `s.M` at 3.2 GiB | target 4's second memory wall | the `d = 2^10` evaluation split |

Also: `jMatrix` materialized at n = 8192 would be terabytes, so collapsing
it via `gadgetMul_apply` is a feasibility requirement. REDUCED `m₀` has a
floor of 14 (below it the shape exercises nothing). Target 4's
REDUCED-throughout policy is revisable: the `d = 2^10` split turns the
table into ~4 MiB — decide deliberately at its brief, not by inheritance.

| Target | Semantics tests | Bench cases |
|---|---|---|
| 1 | real consts (digit ops are cheap) | real consts; birth case per op |
| 2 | real consts except `carrier`/`carrierCommit` (8192-wide mat-vec under schoolbook mul) → REDUCED | REDUCED for the mat-vec cases, with the standard policy note; others real |
| 3 | real consts except `lift_commit` (81960-wide) → REDUCED | REDUCED for `lift_commit`; `liftShortCheck`/`rhoDigitsShortCheck` real |
| 4 | **REDUCED throughout** — no test may materialize a 2^m₀ table; use a small-m₀ shape and state it | REDUCED only; exclusions bar applies to any case that cannot be shrunk |
| 5 | **REDUCED throughout**, small m₀; full-const is `#[ignore]`d with the "full-const scale" form | REDUCED only; the naive form is excluded outright until the dense champion lands |
| 6 | real consts for the checks; the MLE eval REDUCED | mixed, per case |

Every REDUCED case carries a written note naming the arithmetic that
forces it, per the `exclusions.toml` bar. Note the removal condition here
is **not** the `ring::mul` champion — it is m₀'s cube size, which no
multiplication speedup touches. Say so wherever a note is written, so the
two walls are not conflated.

### Remaining Stage 2 work — ⊗⊗ none; Stage 2 exit met 2026-09-03

1. ~~One `arklib-analyze` brief per target (6)~~ — done 2026-09-01
   (`briefs/`), corrections folded here.
2. ~~The params.rs extension + riders~~ — landed 2026-09-03 at τ = 5
   against PR #847's `Hachi/Params.lean`; `Generated.lean` diff params-only;
   doc-sync items 4–6 rode it.
3. ~~A house-discipline exception line for F4~~ — the exception shrank to
   `M_ONE` and is recorded at the constant, in `Check.lean` § 1 and in
   NOTES.md.

Stage 2's exit criteria (top of file) are met: ordered, dependency-closed
target list with briefs and scale policies; Decisions 3–4 settled with the
user (4 revised); params.rs extended with checks green and the extraction
diff params-only; NOTES.md records the audit. What the briefs themselves
still owe is a re-read of their `file:line` citations at `d51d8bc` when
each target opens — the deltas that matter are summarized in
`briefs/target-1-balanced-digits.md`'s re-base section and in this file's
⊗⊗ marks. **Next: Stage 3, `/op-genesis` target 1 ∥ target 2.**
