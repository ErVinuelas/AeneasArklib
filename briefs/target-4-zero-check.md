# Brief: `ArkLib.Lattices.Ajtai.InnerOuter` zero-check link — `wTable`, `cWTableMle`/`wTableMleEval`, `hZero`/`hAlpha`, `alphaPublicEvals`, `zcTargetAlpha`, `hypercubeSum`, `relBatched` (ArkLib @ `d51d8bc3c22062bf21385bd15b39d390b0fe4584`)

Stage 3 target 4 of `PLAN_PROTOCOL_LAYER.md`, sized **larger than evalsplit** by
`STAGE2_SCOPING.md` § "Ordered target list + scale policies". Rust home: a new
`hachi/src/zerocheck.rs`. Sources read: `ZeroCheck/Constraints.lean` (1456 lines),
`ZeroCheck/Batch.lean` (302), plus the definitions they reach in
`RingSwitch/{Reduction,RhoDigits,Rlin}.lean` and `Sumcheck/FinalEval.lean`, all under
`hachi/.lake/packages/Arklib/ArkLib/Commitments/Functional/Hachi/`. Paths below are
relative to that directory unless stated otherwise; the rev is the one
`hachi/lake-manifest.json:11` records and `hachi/lakefile.lean` pins.

Dependency position: `{1 ∥ 2} → 3 → 4 → {5 ∥ 6}`, with TE landing before 4's specs
(`STAGE2_SCOPING.md` § "Ordered target list").

## Re-base from `294b3f0` to `d51d8bc` (2026-09-07)

**Every definition this target translates is byte-identical across the pin move.** Checked
mechanically rather than by eye: each declaration block was extracted from both revs and
compared — `wTable`, `cWTableMle`, `wTableMleEval`, `hZero`, `hAlpha`, `hAlphaEvals`,
`rangeProduct`, `alphaPublicEvals`, `zcTargetAlpha`, `hypercubeSum`, `cEqualityPolynomial`,
`cMultilinearExtension`, `sumcheckPolyZero`, `sumcheckPolyAlpha`, `relBatched`, and the
target-3 items this brief reaches (`cRowSum`, `cEvalAt`, `rhoDigits`, `rhoDigitCount`,
`balancedDigit`). Nothing in § "Definition chain" changes shape; only line numbers move.

**What the pin actually changed for this target.**

* **Four theorems were deleted from `Constraints.lean`** (the whole of that file's diff):
  `hZeroML_eq_zero_iff`, `hAlphaML_eq_zero_iff`, `sum_sumcheckPolyZero'` and
  `sum_sumcheckPolyAlpha'` — the last two were explicit aliases "retained for the sumcheck
  bridge", so the bridge now composes `sum_sumcheckPolyZero` / `sum_sumcheckPolyAlpha`
  directly. Target 4 translates none of them, but target 5's bridge must not cite the
  primed names.
* **The parameters this brief is instantiated at are now pinned by ArkLib itself.** A new
  `Hachi/Params.lean` fixes the profile: `hachiTau = 5` (`:90`), `mu0_eq : mu0 = 57344`
  (`:415`), `liftKeyWidth_eq : liftKeyWidth = 57384` (`:425`), and the coverage bound
  `sumcheckWidthAtProfile` at `M = 25` with `sumcheckWidthAtProfile_minimal` ruling out
  `M = 24` (`:432`, `:439`) — i.e. **`m₀ = 26`**. Where the old § "Parameters" called μ₀,
  `LIFT_COLS` and `m₀` *derived* under an inequality ArkLib left free (flag F4), they are
  now **pinned** and discharged upstream. `δρ = 8`, `n₀ = 5`, `m₁ = 3`, `b = 16`,
  `bound = 15`, `d = 1024` and `ω = 16` are unmoved.
* **Consequently every cube-sized figure halves**: `2^m₀` goes `2^27 → 2^26`
  (134 217 728 → 67 108 864 entries, 4.0 → **2.0 GiB** as an `Ext4` table), the dominant
  `wTableMleEval` term `3.76·10⁹ → 1.81·10⁹` `Ext4` mults at 4.0 GiB resident, `hZero`
  `4.16·10⁹ → 2.08·10⁹`, and naive `alphaPublicEvals` `8.3·10¹¹ → 4.1·10¹¹`. The μ₀-sized
  figures shrink by `57344/81920`: dense `s.M` 3.2 → **2.2 GiB**, the `M̃_α` hoist table
  13 → **8.8 MiB**. The `wTable` digit redundancy is *not* affected — `n·δρ·d = 40 960`
  digit entries costing `41 943 040` `balancedDigit` calls is independent of τ.
* **No conclusion of this brief is reversed by the move.** `hZero` is still the largest
  cube term (`31·2^m₀` beats `(m₀+1)·2^m₀` while `m₀ < 30`), the `d = 2^10` split is still
  a bit-boundary split (`d` did not move), Prerequisite A's `noncomputable` barrier and its
  two repair lemmas are unchanged, and the five scale walls stand.

**How the citations below were re-based.** The `file:line` in the body were remapped
mechanically from the two revs' diff hunks, and **every rewrite was verified by requiring
the old and new blobs to carry identical text at the mapped line**; a citation whose text
did not match was not rewritten. 116 moved, 77 were already correct, and the ambiguous
bare `:N` forms were resolved by hand against the declaration they name. Two classes were
deliberately left alone: citations into `CompPoly/…` and `cpoly/…` (that package's rev is
`a09455a…` at **both** ArkLib pins, so its line numbers did not move), and citations into
this repository's own `.rs`/`.md` files. Per-file shifts, for checking any citation this
brief does not carry:

| file | shift(s), old → new |
|---|---|
| `ZeroCheck/Constraints.lean` | `< 326`: 0; `< 1157`: −13; `< 1388`: −21; rest: −32 |
| `ZeroCheck/Batch.lean` | unchanged |
| `RingSwitch/Reduction.lean` | −2 from `:70`, −19 from `:287`, −24 from `:427` |
| `RingSwitch/RhoDigits.lean` | 0 below `:106`, −9 after |
| `RingSwitch/Rlin.lean` | −1 from `:38`, **−78 from `:65`** |
| `Sumcheck/FinalEval.lean` | 0 below `:135`, −8 after |
| `Gadget/Core.lean` | grows: +21 by `:109`, **+216 from `:242`**, +276 at the end |
| `Composition.lean`, `Correctness.lean` | large and non-monotone (PR #847); re-read, never shift |
| `Core/Basic.lean`, `Data/MvPolynomial/Multilinear.lean`, `Lift/Reduction.lean`, `Transport/Eval.lean` | unchanged |

---

## Definition chain

### The two objects the link is about

`relBatched` (`ZeroCheck/Batch.lean:81-88`) is a four-conjunct `Set`:
`K.com w = t ∧ hZero … = 0 ∧ hAlpha … = 0 ∧ bound ≤ rlin.bound`. Its verifier is
`ReduceClaim.verifier oSpec id` (`Batch.lean:288`) with
`batchVerifierPureForm.verify := fun stmt _ => stmt` (`Batch.lean:270-272`) — a
zero-round *statement map*, no boolean check. That matches the API walk's wire
format (`STAGE2_SCOPING.md` § "API mapping": `batch(0)`, and "only three boolean
checks exist in the composed verifier"). **Consequence for the translation: nothing
in `relBatched` is on the verifier's runtime path.** The runtime consumers of this
file are (a) `Sumcheck/FinalEval.finalCheck` (`FinalEval.lean:99-105`), which
evaluates `cEqualityPolynomial` and `cMultilinearExtension (alphaPublicEvals …)`,
(b) `honestComputeY` (`FinalEval.lean:246-248`), whose body is *exactly*
`wTableMleEval`, and (c) target 5's `hypercubeSum`/`computableRoundPoly`.

### `wTable` — notation to body

`wTable Φ m₀ φF b w : (Fin m₀ → Fin 2) → F` (`Constraints.lean:140-151`). Body,
unfolded:

1. `idx : ℕ := (finFunctionFinEquiv pt : Fin (2 ^ m₀))` (`:143`) — the little-endian
   bit decode; `d : ℕ := Φ.φ.natDegree` (`:144`).
2. `if hz : idx / d < μ` → `φF ((w.z ⟨idx / d, hz⟩).1.coeff (idx % d))` (`:145-146`).
   `w.z : Fin μ → Rq Φ` and `.1` is the canonical `CPolynomial (ZMod q)`
   representative (`LiftedWitness`, `ProofSystem/RingSwitching/Lift/Reduction.lean:80-86`,
   abbreviated at `RingSwitch/Reduction.lean:136-137`).
3. `else if hr : idx / d - μ < n * rhoDigitCount q b` →
   `φF ((rhoDigits Φ b (w.ρ ⟨(idx/d - μ)/δ, _⟩) ((idx/d - μ) % δ)).coeff (idx % d))`
   (`:147-150`), `δ := rhoDigitCount q b`.
4. `else 0` (`:151`).

**This is a two-level split, confirming `STAGE2_SCOPING.md` § "Shape-list
corrections" item 2**: an outer `idx / d`, `idx % d` split into (row, column), then
inside the quotient block a second `/δ`, `%δ` split into (quotient row, digit).
`wTable_zRow` (`:378`) and `wTable_rRow` (`:394`) are the two per-block readback
lemmas, and `wTable_rRow`'s proof (`:402-422`) is where the index algebra of the
inner split is done.

Innermost: `rhoDigits Φ b ρ u = CPolynomial.ofFinCoeff d (fun k => balancedDigit b δ (ρ.coeff k) u)`
(`RingSwitch/RhoDigits.lean:126-128`), `balancedDigit b digits c e =
((Nat.digits b (c + balancedShift b digits).val).getD e 0 : ZMod q)`
(`RhoDigits.lean:79-80`), `balancedShift` at `Gadget/Core.lean:159`. So `wTable`'s
digit branch bottoms out in target 1's `balanced_digit_at` — see § Representation for
the dependency this creates.

`δ := rhoDigitCount q b = Nat.clog b q` (`RhoDigits.lean:66`) — an `abbrev`, so it is a
params literal in Rust, never translated (`STAGE2_SCOPING.md` § "Minor variants":
"`Nat.clog` is not translatable at all").

### The two table lifts

* `cWTableMle Φ m₀ φF b w = Vector.ofFn fun i => wTable … (finFunctionFinEquiv.symm i)`
  (`:328-330`) — a `CMlPolynomialEval F m₀ = Vector F (2 ^ m₀)`
  (`CompPoly/Multilinear/Basic.lean:47`).
* `wTableMleEval … a = CMlPolynomialEval.eval (cWTableMle …) (Vector.ofFn a)`
  (`:348-350`), and `CMlPolynomialEval.eval p x = Vector.dotProduct p (lagrangeBasis x)`
  (`CompPoly/Multilinear/Basic.lean:524-525`), `lagrangeBasis w = Vector.ofFn (fun i =>
  ∏ j : Fin n, if (BitVec.ofFin i).getLsb j then w[j] else 1 - w[j])` (`:410-411`).

Note the `finFunctionFinEquiv` / `.symm` cancellation: `cWTableMle` feeds
`.symm i` into a `wTable` whose first act is to apply `finFunctionFinEquiv`, so the
composite is `Equiv.apply_symm_apply` — the same simp step `wTable_zRow`'s proof uses
(`:401`). Same for `hZero` (`:206-207`) and `hAlpha` (`:215`). Those three are flat
index loops with no bit machinery. **But see the correction in § Cost model: the
`m₁`-side weights are not.**

### `hZero` / `hAlpha`

* `hZero Φ m₀ φF b w = Vector.ofFn fun i => rangeProduct b (wTable … (finFunctionFinEquiv.symm i))`
  (`:204-207`), computable.
* `rangeProduct b v = v * ∏ j ∈ Finset.Icc 1 (b - 1), ((v - j) * (v + j))` (`:96-97`) —
  `b - 1` quadratic factors, the vanishing polynomial of `{-(b-1), …, b-1}`
  (`rangeProduct_eq_zero_iff`, `:102-116`).
* `hAlpha … = Vector.ofFn fun i => hAlphaEvals … (finFunctionFinEquiv.symm i)`
  (`:213-215`), **`noncomputable`**.
* `hAlphaEvals` (`:176-185`), **`noncomputable`**: at row `i < n`,
  `cEvalAt φF α (cRowSum Φ s w.z i) - cEvalAt φF α (s.yvec i).1
   - cEvalAt φF α Φ.φ * ∑ u : Fin δ, φF ((b : ZMod q)^u) * evalAt φF α (rhoDigits Φ b (w.ρ i) u).toPoly`;
  zero-padded above row `n`.

`cRowSum Φ s z i = ∑ j, (s.M i j).1 * (z j).1` (`RingSwitch/Reduction.lean:439-441`);
`cEvalAt φF a p = p.eval₂ φF a` (`Reduction.lean:444-445`).

### Prerequisite A — the `noncomputable` barrier: **VERIFIED, and cheaper than stated**

`hAlphaEvals` is `noncomputable def` at `Constraints.lean:176` and `hAlpha` at
`Constraints.lean:213`, exactly as `STAGE2_SCOPING.md` § "Erasure catalogue" / "An
unlisted prerequisite step" reports. The *sole* cause is the digit term's
`evalAt φF α (…).toPoly` at `Constraints.lean:184`: `evalAt` is
`noncomputable def evalAt … := Polynomial.eval₂RingHom φF a`
(`ArkLib/ProofSystem/RingSwitching/Transport/Eval.lean:46-47`). Every other
ingredient (`cEvalAt`, `cRowSum`, `rhoDigits`, `Vector.ofFn`) is computable.

The stated repair — swap `evalAt ∘ toPoly` for `cEvalAt` on `rhoDigits` directly —
and both bridging lemmas exist at the pin:

* `cEvalAt_eq_evalAt_toPoly (φF) (a) (p) : cEvalAt φF a p = evalAt φF a p.toPoly`
  (`RingSwitch/Reduction.lean:471-475`), proof `CPolynomial.eval₂_toPoly φF a p` — a
  one-liner, no side conditions beyond the omitted instances.
* `rhoDigits_evalAt` (`RingSwitch/RhoDigits.lean:191-202`): `evalAt φF α ρ.toPoly =
  ∑ u : Fin δ, φF ((b:ZMod q)^u) * evalAt φF α (rhoDigits Φ b ρ u).toPoly`, under
  `1 < b`, `0 < d` and `hρ`.

So `hAlphaEvals.c` (the computable sibling) is `hAlphaEvals` with
`evalAt φF α (rhoDigits … u).toPoly` replaced by `cEvalAt φF α (rhoDigits … u)`, and
`hAlphaEvals.c = hAlphaEvals` is `Finset.sum_congr` over
`cEvalAt_eq_evalAt_toPoly`. **This is a stated step, not research**, and it is
*smaller* than STAGE2 implies: `rhoDigits_evalAt` is not needed for the
computability repair at all (it is the *Eq. (22) identification* lemma, used at
`:763`, `:780`, `:1363` and `Batch.lean:138`, `:233`) — `cEvalAt_eq_evalAt_toPoly`
alone discharges it, term by term. Downstream: `hAlpha_eq_zero_iff` (`:237`),
`hAlphaEvals_rowPoint` (`:191`), `hAlphaEvals_eq_alphaDefect` (`:771`),
`hAlpha_eq_zero_iff_alphaDefect` (`:791`), `hAlphaML` (`:261`) and the two `Batch.lean`
bridge directions (`:108`, `:249`) all restate against the sibling by rewriting with
that one equation; none of them inspects the digit term's *form*.

Interaction with target 5: `honestComputeG` (`Sumcheck/Completeness.lean:74`, per
`STAGE2_SCOPING.md` § "Shape-list corrections" item 3) is unaffected — it does not go
through `hAlphaEvals`.

### Prerequisite B — `CMvPolynomial n F` as a runtime value: **VERIFIED, and it is an `opt-*`, not a probe**

The no-precedent shape is real. `CMvPolynomial n R = Lawful n R`
(`CompPoly/Multivariate/CMvPolynomial.lean:48`) and
`Lawful n R = {p : Unlawful n R // p.isNoZeroCoef}`
(`CompPoly/Multivariate/Lawful.lean:34-35`), with
`eval₂ f vs p = ExtTreeMap.foldl (fun s m c => f c * MonoR.evalMonomial vs m + s) 0 p.1`
(`CMvPolynomial.lean:133-135`) and `eval = eval₂ (RingHom.id _)` (`:217-218`).
A sparse `Std.ExtTreeMap` monomial dictionary has no counterpart in `hachi/src` or in
cpoly's Rust (`~/.cargo/git/checkouts/aeneascomppoly-.../583cfaf/cpoly/src/` is
`field.rs`, `univariate.rs` = `Vec<Ext4>`, `multilinear.rs` = `Vec<Ext4>`), and
STAGE2's judgement that it is above the Aeneas ceiling stands.

Reached from this target by: `cBooleanEqPolynomial` (`:830-832`),
`cMultilinearExtension` (`:835-837`), `cEqualityPolynomial` (`:840-842`),
`cRangeProduct` (`:845-847`), `sumcheckPolyZero` (`:873-876`), `sumcheckPolyAlpha`
(`:881-884`), `hypercubeSum` (`:899-900`), and — the part that makes it target 4's
problem and not only target 5's — **both eval subterms of `finalCheck`**
(`FinalEval.lean:100-104`).

The factoring lemmas that let the type be removed rather than translated all exist at
the pin, and each is `rw`-shaped:

| lemma | line | what it removes |
|---|---|---|
| `cMultilinearExtension_eval` | `:960-964` | `(cMultilinearExtension m₀ evals).eval τ = MvPolynomial.eval τ (MLE evals)` |
| `cMultilinearExtension_eval_boolean` | `:967-970` | at a Boolean point, `= evals y` |
| `cEqualityPolynomial_eval_boolean` | `:974-977` | the `eq̃` table at a Boolean point |
| `cBooleanEqPolynomial_eval` | `:950-955` | the Lagrange factor, as a product of `m₀` selections |
| `cRangeProduct_eval` | `:981-984` | `(cRangeProduct m₀ b p).eval τ = rangeProduct b (p.eval τ)` |
| `wTableMleEval_eq` | `:341-345` | `wTableMleEval … a = MvPolynomial.eval a (MLE (wTable …))` |
| `eval_sumcheckPolyZero` | `:1382-1387` | `= (cEqualityPolynomial m₀ τ₀).eval a * rangeProduct b (wTableMleEval … a)` |
| `eval_sumcheckPolyAlpha` | `:1394-1399` | `= wTableMleEval … a * (cMultilinearExtension m₀ (alphaPublicEvals …)).eval a` |

Two notes against `STAGE2_SCOPING.md`:

* the two `eval_sumcheckPoly*` citations (`:1382`/`:1394`) are exact; `wTableMleEval_eq`
  is at **`:341`**, not `:339` (`:339` is the preceding `omit` line).
* the *degree* side does **not** factor through evaluation and must keep a polynomial-
  level bridge: `fromCMvPolynomial_cMultilinearExtension` (`:1011-1016`),
  `fromCMvPolynomial_cRangeProduct` (`:1020-1029`), consumed by
  `degreeOf_sumcheckPolyZero` (`:1069-1079`) and `degreeOf_sumcheckPolyAlpha`
  (`:1084-1094`). The file says why out loud at `:989-993` ("a degree is *not*
  determined by values"). Those are `Prop`s about the erased type, so nothing is
  translated — but the dense rewrite must not be phrased as *replacing*
  `sumcheckPoly*`, only as giving them an evaluation-equal dense sibling, or the
  degree theorems (which `RoundMsg` and Lemma 11 consume) stop applying.

### The offsetting win — cpoly's proved MLE toolkit: **VERIFIED, and larger than stated**

Every piece STAGE2 § "The positive the plan undersells" names exists in Rust *with an
Aeneas equivalence proof already discharged*, in
`~/.cargo/git/checkouts/aeneascomppoly-27508bae189397f4/583cfaf/cpoly` (the crate
`hachi/Cargo.toml:75` pins by `rev = 583cfaff…`):

| Rust | Lean spec (proved) | mirrors |
|---|---|---|
| `dot` (`src/multilinear.rs:123`) | `dot_spec` (`lean/Multilinear.lean:1410-1420`) | `Vector.dotProduct` |
| `lagrange_basis` (`src/multilinear.rs:169`) | `lagrange_basis_spec` (`lean/Multilinear.lean:1341-1366`) | `CMlPolynomialEval.lagrangeBasis` |
| `MultilinearEvals::eval` (`src/multilinear.rs:530`) | `eval_lagrange_spec` (`lean/Multilinear.lean:1449-1471`) | `CMlPolynomialEval.eval` |
| `eq_tilde` (`src/multilinear.rs:248`) | `eq_tilde_spec` (`lean/Multilinear.lean:1473-1487`) | `CMlPolynomialEval.eqTilde` |
| `eval_mle_layer` (`src/multilinear.rs:280`) | `eval_mle_layer_spec` (`lean/Multilinear.lean:1721-1752`) | `CMlPolynomialEval.evalMleLayer` |
| `MultilinearEvals::eval_mle` (`src/multilinear.rs:538`) | `eval_mle_spec` (`lean/Multilinear.lean:1818-1839`) | `CMlPolynomialEval.evalMle` |

`wTableMleEval` is `CMlPolynomialEval.eval` at `m₀` (`Constraints.lean:337`), so
`MultilinearEvals::eval` + `eval_lagrange_spec` covers it **verbatim** — STAGE2's claim
holds. The undersold part: `eval_mle_spec`'s own proof closes with
`CMlPolynomialEval.eval_mle_eq_eval` (`lean/Multilinear.lean:1839`), and that theorem
(`CompPoly/Multilinear/Basic.lean:574-585`) states `evalMle p x = eval p x`
unconditionally. So the `O(m₀·2^m₀)` Lagrange-dot semantics of `wTableMleEval` may be
replaced by the `O(2^m₀)` layer fold **with the equality already proved upstream and the
Rust already written and already verified**. That is a free `m₀/2 ≈ 13×` on the single
largest computation in the target, and it needs no `Foo.opt`/`opt_eq_spec` of its own —
only a citation.

---

## Parameters

Computed at `hachi/src/params.rs` as it stands plus the Stage 2 parameter-audit
additions (`STAGE2_SCOPING.md` § "Parameter mapping"). Split per the house rule
(`NOTES.md` § "Chosen parameters"): **pinned** = forced from outside, **chosen** =
one-line diff to move, **derived** = must be re-derived if an input moves.

| symbol | ArkLib name | value | class | source |
|---|---|---|---|---|
| `q` | modulus | `2^32 − 99` | **pinned** by cpoly's `Fp` | `params.rs:51`; `cpoly/src/field.rs:56` |
| `d` | `Φ.φ.natDegree` | `1024` | **pinned** (Fig. 9 α = 10) | `params.rs:88` (`RING_DEGREE`) |
| `b` = `bZero` | digit / range base | `16` | **pinned** Fig. 9 | `params.rs:97` (`GADGET_BASE`); `B_ZERO` per § "Parameter mapping" |
| `δρ` | `rhoDigitCount q b` = `Nat.clog 16 q` | `8` | **derived** (`q ≤ b^δ`, `Nat.le_pow_clog`) | `RhoDigits.lean:66`; `RHO_DIGIT_COUNT` |
| `τ` = `zDigits` | `hachiTau` | `5` | **pinned** by `Params.lean` (PR #847) — *not* `Nat.clog b q`, see re-base | `Params.lean:90`; `Z_DIGITS` (`params.rs:423`) |
| `μ` = μ₀ | `rlinCols 1 8 8 5 10 10` | `57344` | **pinned** by `mu0_eq` | `Params.lean:411`, `:415`; `Rlin.lean:75-77`; arithmetic below |
| `n` = n₀ | `rlinRows 1 1 1` | `5` | **derived** | `Rlin.lean:80-81` |
| — | `LIFT_COLS` = `μ₀ + n₀·δρ` | `57384` | **pinned** by `liftKeyWidth_eq` | `Params.lean:421`, `:425` |
| `m₀` | least `m₀` with `(μ+n·δρ)·d ≤ 2^m₀` | **26** | **pinned** at the profile (ArkLib still carries `M` free under `hμn`, but now fixes it) | `Params.lean:432` (`sumcheckWidthAtProfile`), `:439` (`_minimal`); `Constraints.lean:437` (`hμn`) |
| `m₁` | least `m₁` with `n ≤ 2^m₁` | **3** | **derived** | `Batch.lean:109` (`hn`); § "Parameter mapping", S2 |
| `bound` | `liftShort` radius, `= b − 1` | `15` = `CHAIN_GAMMA` | **derived** from the two bridge orientations | `Batch.lean:111`, `:248`; § "Parameter mapping" F1 |
| `bDig` | `DigitBaseOk` digit base | `16` = `B_ZERO` | **pinned** = `b` | `Composition.lean:196-203` per § "Parameter mapping" |
| `ω` | `ShortChallenge Φ ω` | `16` = `OMEGA` | **pinned** Fig. 9 | § "Parameter mapping" |
| `roundDegZero b` | `2b` | `32` | **derived** | `Constraints.lean:87` |
| `roundDegAlpha` | `2` | `2` | **derived** | `Constraints.lean:90` |

Arithmetic, written out (STAGE2 § "Parameter mapping" and § "Cross-audit
contradiction" derive the same numbers; not re-derived here, only checked):

* `rlinCols 1 8 8 5 10 10 = 2^10·8 + (2^10·(1·8) + 2^10·8·5) = 8192 + 8192 + 40960 = 57344` ✓
  (`rlinCW`/`rlinCT`/`rlinCZ`, `Rlin.lean:84`, `:86`, `:88`).
* `rlinRows 1 1 1 = 1 + (1 + (1 + (1 + 1))) = 5` ✓.
* `LIFT_COLS·d = 57384 · 1024 = 58 761 216`; `2^25 = 33 554 432 < 58 761 216 ≤ 67 108 864 = 2^26`,
  so `m₀ = 26` ✓ (the same two inequalities ArkLib discharges as
  `sumcheckWidthAtProfile` / `sumcheckWidthAtProfile_minimal`). `n₀ = 5 ≤ 8 = 2^3` and `5 > 4 = 2^2`, so `m₁ = 3` ✓.

**`BETA_SQ` / τ — settled at the re-base, and the conditional above it came true.**
No numeric `BETA_SQ` is asserted here and this target still does not read it: the
zero-check's norm content is `bound` (the `liftShort` radius, `Batch.lean:111`/`:248`)
and `CHAIN_GAMMA = b − 1 = 15`, never βSq — `relBatched` (`Batch.lean:81-88`) carries
**no** norm conjunct at all, by design (`Batch.lean:20-22`: shortness is *derived* from
`H₀ ≡ 0`, not assumed). The one line of symbolic exposure is real and has now moved:
`μ₀ = rlinCols … τ …` reads the `z` digit count in the `rlinCZ` slot (`Rlin.lean:88`),
and PR #847 settled that count at **`τ = 5`**, not the `8` this brief was written at nor
the `4` it hypothesised. So `μ₀ = 8192 + 8192 + 2^10·8·5 = 57344`, `LIFT_COLS = 57384`,
`LIFT_COLS·d = 58 761 216`, and **`m₀ = 26`** — the value the old paragraph predicted for
the `τ = 4` branch, reached by a different route, so every cube-sized figure below is
halved rather than scaled by `5/8`. `δρ = Nat.clog 16 q = 8` is a *different* quantity
(the quotient digit count, `RhoDigits.lean:66`) and is unaffected, exactly as stated.
The τ that lands is not a `Nat.clog`: it is sized from `Z_BOUND = 131 072`, the honest
`‖z‖∞ ≤ 2ʳ·ω·⌊b/2⌋`, through a `BoundedDigitDecomposition` (`params.rs:405-423`;
`Params.lean:90`, `:195` `tau_minimal`).

**Two-gammas discipline (F1/S7).** This target's γ is `CHAIN_GAMMA = 15 = b − 1`, the
range-base/`liftShort` radius, **not** `params::GAMMA = 16` (the weak-opening γ̄ = b).
The coincidence is sharp and load-bearing: `rangeProduct b` at `b = 16` has exactly
`b − 1 = 15 = CHAIN_GAMMA` quadratic factors (`Constraints.lean:97`), and
`hZero_eq_zero_imp_liftShort` needs `b − 1 ≤ bound` (`:438`) while
`hZero_eq_zero_of_liftShort` needs `bound ≤ b − 1` (`Batch.lean:182`) — the two
relations coincide exactly at `bound = 15` (`Batch.lean:37-38`, `:242-244`). Every
Check.lean entry in this module must say which of the two 16/15 constants it means; per
F3 the value 15 is also the honest unsigned digit ceiling.

**Side conditions that are pure `Prop` and translate to nothing.**
`DigitBaseOk q bound bDig` is a `structure … : Prop` with three fields
(`RingSwitch/Reduction.lean:173-179`): `one_lt : 1 < bDig`, `le_half : bDig ≤ q / 2`,
`radius_le : bDig / 2 ≤ bound`. At `(q, 15, 16)`: `1 < 16` ✓, `16 ≤ 2147483598` ✓,
`8 ≤ 15` ✓. Likewise `hb : 1 < b`, `hd : 0 < Φ.φ.natDegree`, `hn : n ≤ 2^m₁`,
`hμn : (μ + n·δρ)·d ≤ 2^m₀` (`Batch.lean:109-111`) — all hypotheses, all discharged at
these constants, none of them code. `hμn` in particular does double duty as this
target's overflow certificate (§ Semantics risks).

**Instances demanded of `F`** (`Constraints.lean:81-84`, `Batch.lean:60-63`):
`Field F, BEq F, LawfulBEq F` — no `DecidableEq F`, no `SampleableType F`, no `q`-side
demand from `hypercubeSum` or the `c*Polynomial` helpers. This confirms
`STAGE2_SCOPING.md` § "Decision 3" for both files, and the one syntactic exception it
flags is also confirmed: `honestComputeY` sits at `FinalEval.lean:246`, after that
file's `variable [SampleableType F]` at `:167`, and its body is exactly
`wTableMleEval` (`:248`), which is SampleableType-free — state the spec against
`wTableMleEval` or pay the one-line instance. At `F = Ext4` the TE work list's item 1
(`LawfulBEq (Ext P)`) is the only gap, and it is a one-liner.

---

## Semantics risks

### Value ranges and overflow headroom — the *index* arithmetic, not the field arithmetic

All coefficient arithmetic routes through cpoly's proved `Fp`/`Ext4` ops, so the
`q < 2^32` headroom argument is already discharged (`STAGE2_SCOPING.md` §
"Scale/overflow hazards"; `hachi/src/params.rs:46-47`). No new width appears: `wTable`
returns `F`, `rangeProduct` is field-only, and the norms in this link are `Prop`s
(`liftShort`, `RingSwitch/Reduction.lean:209-210`), not `u128` computations. So the
headroom work here is entirely on `Usize`, and there are four obligations. Written out
at the pinned profile (`m₀ = 26`, `d = 1024`, `μ + n·δρ = 57384`):

1. **`2^m₀` must be a legal `Usize`.** `2^26 = 67 108 864 < 2^64`. A `two_pow`-style
   repeated-doubling helper (`hachi/src/evalsplit.rs:89-97`) makes each doubling a
   *checked* multiplication, so the obligation is `2^m₀ ≤ Usize.max`. cpoly already
   carries exactly this hypothesis shape: `pow2_spec (n) (hn : 2 ^ n.val ≤ Std.Usize.max)`
   (`cpoly/lean/Multilinear.lean:486`) with a `pow2_le_usize_max` helper — reuse both.
2. **`d * u + ℓ` must not overflow.** `wTableIndex` (`Constraints.lean:1164-1174`) and
   `wTablePoint` (`:525-534`) both prove `d·u + ℓ < 2^m₀` from `u < μ + n·δρ`,
   `ℓ < d` and `hμn`; the two-step chain is
   `d·u + ℓ < d·(u+1) ≤ (μ + n·δρ)·d ≤ 2^m₀`. **`hμn` is the overflow certificate**, and
   it is already a hypothesis of every consumer (`Batch.lean:110`,
   `Constraints.lean:437`, `:622`, `:794`, `:1314`). Max value at the profile:
   `1024·57383 + 1023 = 58 761 215 < 2^26`.
3. **Guard-ordered `Nat` subtractions — three of them, and the branch order is
   load-bearing.** `idx / d - μ` (`Constraints.lean:147`) is inside the `else` of
   `if hz : idx / d < μ` (`:145`), so `idx/d ≥ μ` and the `ℕ` subtraction is exact; in
   Rust the same expression on `usize` **underflows and panics** if hoisted above the
   guard. Same shape at `u - μ` in `mAlphaTilde` (`:519`, inside `else` of
   `dif hu : u < μ` at `:517`) and at `j.val - i` in `hypercubePoint` (`:853`, inside
   `else` of `if h : j.val < i`). `STAGE2_SCOPING.md` § "Scale/overflow hazards" item
   (a) names this class; the three sites are here.
4. **`b - 1` must not be formed.** `Finset.Icc 1 (b - 1)` (`:97`) at `b = GADGET_BASE`
   would extract through `Result` if written as `params::GADGET_BASE - 1`, exactly like
   `RING_DEGREE`/`GAMMA` (`params.rs:80-84`, `:162-165`). Write the loop as
   `let mut j = 1; while j < params::GADGET_BASE { … }` and no subtraction exists;
   alternatively use the `CHAIN_GAMMA = 15` literal, which *is* `b − 1` and is on the
   literal-collision watchlist (F3).

### Partiality

* **Division by `δρ` and by `d`.** `(idx/d - μ) / δρ` and `% δρ` (`:148`, `:150`) need
  `δρ > 0`; `idx / d`, `idx % d` need `d > 0`. `d > 0` is the ubiquitous `hd`
  hypothesis; `δρ > 0` is *not* a hypothesis anywhere and is instead derived on demand
  from `hr` — `Batch.lean:194-197` does exactly this (`rcases Nat.eq_zero_or_pos …; rw
  [h0, Nat.mul_zero] at hr; omega`), and `wTable_rRow` asserts it by `omega` at `:409`.
  At the pin's constants both are literals (1024, 8) so the Rust divisor is never zero,
  but the *spec-side* statement of any `_spec` must carry `0 < d` and either `0 < δρ` or
  the `hr` from which it follows.
* **`Nat.digits b` inside `balancedDigit`** (`RhoDigits.lean:79-80`) is well-founded
  recursion over an unbounded list; `hachi/src/gadget.rs:68-77` already avoids it by
  repeated division and proves agreement "at *every* `e`" (`gadget.rs:65-67`). Target 1
  owns the balanced version; target 4 inherits it.
* **`Nat.clog`** (`RhoDigits.lean:66`) is not translatable — params literal only, with
  the `Nat.clog_le_iff_le_pow` + `omega` Check.lean pattern (F6).
* **`m₀ − i` in `hypercubeSum`** (`:887`): `Fin (m₀ - i) → Fin 2`. At `i > m₀` the type
  is empty and the sum collapses — `hypercubeSum_of_le` (`:902-909`) is the lemma, and
  its docstring (`:893-901`) explains why the *unsoundness* at `m₀ < i` is why
  `Sumcheck/Rounds.lean`'s round theorem carries `i < m₀`. Target 5's problem, but the
  Rust signature target 4 hands over must not silently allow `i > m₀`.

### Exactness traps

* **`==` on `F`.** `finalCheck` (`FinalEval.lean:100-105`) uses `==` (`BEq F`) on two
  field equalities and `decide` on the bound. Per the house rule
  (`arklib-analyze` § 3, `Rq::equals`) exactly one notion of equality per type: the
  Rust must compare `Ext4` through cpoly's own `PartialEq`
  (`cpoly/src/field.rs:184`, `#[derive(… PartialEq, Eq …)]`) — coefficient-wise on
  reduced representatives — and the Lean side needs TE item 1 (`LawfulBEq (Ext P)`) for
  `==` to be the same relation.
* **`hZero … = 0` / `hAlpha … = 0` are equalities of `Vector F (2^m)`**, not of scalars.
  `hZero_eq_zero_iff` (`:219-233`) and `hAlpha_eq_zero_iff` (`:237-252`) turn each into
  a pointwise `∀ x` statement — that pointwise form is what a Rust `bool`-returning
  loop mirrors, and it is the honest translation target.
* **Degenerate sizes.** `n = 0` empties the `m₁` cube (`hAlphaEvals`'s padding branch,
  `:185`, is then everything and `hAlpha = 0` trivially); `μ = 0` empties the `z` block;
  `n < 2^m₁` is the *normal* case and the padding rows must be zero, not garbage
  (`sum_cube_rowIndexed`, `:1269-1301`, is the lemma that says both sides drop the same
  rows — and it needs **no** `n ≤ 2^m₁` hypothesis, `:1266-1268`). A REDUCED corpus with
  `n = 2^m₁` exactly would test none of the padding; see § Cost model.
* **The absent `1_{≤μ}` indicator.** `sum_sumcheckPolyZero`'s docstring
  (`:1106-1133`) records that the paper's `F_{0,τ₀}` carries a trailing indicator that
  Eq. (23)'s `H₀` does not, that the two readings are inequivalent, and that **the
  paper's own identity is false as printed**. ArkLib follows the indicator-free
  reading. A Rust `h_zero` that "helpfully" restricts the range check to the `z` rows
  would be translating the paper, not the pin. Do not re-guess this: it is decided at
  `:1115-1121`.
* **Both blocks are range-checked, but only one can fail.** Same docstring,
  `:1123-1130`: the digit rows are in range *by construction*
  (`rhoDigits_valMinAbs_natAbs_le`, `RhoDigits.lean:~168`, bounds every digit by
  `⌊b/2⌋ = 8` for an *arbitrary* quotient), so `H₀`'s substantive content is the `z`
  block. A semantics test that only perturbs a digit row cannot make `hZero ≠ 0` at an
  admissible base — perturb a `z` coefficient past `±15`.
* **Sign.** `rangeProduct`'s roots are `{0, ±1, …, ±(b−1)}` in `F`
  (`rangeProduct_eq_zero_iff`, `:102`), pulled back through the *injective* `φF` to
  centered residues (`valMinAbs_natAbs_le_of_rangeProduct_eq_zero`, `:361-373`, and its
  converse at `Batch.lean:147-162`). The docstring at `:357-360` states explicitly that
  **no anti-wraparound side condition such as `b − 1 ≤ q/2` is needed** for the
  soundness direction — do not import the `gadget.rs:27` side condition here.

---

## Cost model

Units: one `Ext4` multiply is 16 `Fp` multiplies + 3 more for the `W`-foldback + 13
`Fp` adds (`cpoly/src/field.rs:316-329`), so **≈19 `Fp` mults**; one heterogeneous
`Fp × Ext4` is **4 `Fp` mults** (`cpoly/src/field.rs:337-344`). That asymmetry is
load-bearing below, because every `wTable` entry is a `φF`-image of a base-field
coefficient. First-principles floor: the only measurement this repository has puts a
64×64 negacyclic convolution (4096 `Fp` mult-adds) at 8.51 µs
(`NOTES.md` § "The first benchmark run", `ring/mul`), i.e. ≈2 ns per `Fp` mult-add,
so ≈40 ns per `Ext4` mult and ≈8 ns per `Fp × Ext4`. That section says in terms that
these are **sizing information and not a baseline** (byte-identical crates read up to
59% apart on that host), so no percentage is predicted here — only operation counts.

### Sizes at the pinned profile

| object | entries | bytes as `Ext4` (32 B) |
|---|---|---|
| `2^m₀` cube | `2^26 = 67 108 864` | **2.0 GiB** |
| non-padding cube points, `(μ+n·δρ)·d` | `58 761 216` | 1.75 GiB |
| padding cube points | `8 347 648` | 0.25 GiB |
| `lagrangeBasis a` at `m₀` | `2^26` | **2.0 GiB** |
| `s.M` as a dense `PolyMatrix (Rq Φ) n μ` | `5 · 57 344` `Rq` = `286 720 · 1024` `Fp` | **2.2 GiB** |
| `M̃_α` hoisted (`cEvalAt α (s.M i u)`) | `5 · 57 344` `Ext4` | 8.8 MiB |
| `α^ℓ` power table, `ℓ < d` | `1024` | 32 KiB |
| `eq̃(τ₁, ·)` weights, `i < n` | `5` | 160 B |

The 2.0 GiB figure confirms `STAGE2_SCOPING.md` § "Scale/overflow hazards" item (b).
**The `s.M` row is an addition to that list** — see § "Corrections" at the end.

### Per-definition counts

Write `T := 2^m₀`, `R := μ + n·δρ` (non-padded rows), so `R·d ≤ T`.

* **`wTable` at one point** (`:140-151`): 2 `Usize` div/mod, 1–2 guards, then either
  one `Fp` coefficient read (z block) or — as written — a whole
  `rhoDigits Φ b (w.ρ i) u` construction, which is `CPolynomial.ofFinCoeff d`
  (`RhoDigits.lean:127-128`), i.e. **`d` `balancedDigit` calls to read one
  coefficient**. That is an `O(d)` recomputation per digit-block entry, redundant by a
  factor `d = 1024`: `n·δρ·d = 40 960` digit entries cost `40 960 · 1024 = 41 943 040`
  `balancedDigit` calls where `40 960` suffice. This is the single most obvious waste in
  the target and it is *inside* the spec's definition, not in the translation.
* **`cWTableMle`** (`:328-330`): `T` `wTable` calls → `T` writes, 2.0 GiB, plus the
  `d`-factor digit redundancy above.
* **`wTableMleEval`** (`:335-337`) = `dot(cWTableMle, lagrangeBasis a)`:
  `lagrangeBasis` is `T` entries each an `m₀`-fold product
  (`CompPoly/Multilinear/Basic.lean:410-411`) → `m₀·T` `Ext4` mults; `dot` adds `T`.
  **`(m₀ + 1)·T = 27 · 67 108 864 = 1.81·10⁹ Ext4 mults` ≈ 3.4·10¹⁰ `Fp` mults**, and
  4.0 GiB resident. This is the **dominant term of the target as specified**.
* **`hZero`** (`:204-207`): `T` × `rangeProduct b`. One `rangeProduct` at `b = 16` is
  `b − 1 = 15` factors, each `1` mult + `2` add/sub, plus `15` accumulating mults plus
  the leading `v·` → **31 `Ext4` mults, 30 add/sub**. `31·T = 2.08·10⁹ Ext4 mults`.
  Bigger than `wTableMleEval`, and it is the only place the range factor is applied
  per-entry (in `finalCheck` it is applied to the *scalar* `y′`, `FinalEval.lean:101` —
  31 mults total, free).
* **`hAlphaEvals` at one row** (`:176-185`, after Prerequisite A): 1 `cRowSum` (μ
  `CPolynomial` mults of degree `< d` — **the growing-degree non-negacyclic `Fp` mul
  STAGE2 § "Minor variants" flags**, `μ·d²` `Fp` mults if schoolbook, i.e.
  `57344·1024² = 6.0·10¹⁰` — dominated by target 3's concerns but reached from here),
  3 `cEvalAt` (each `d − 1` `Ext4` mults ≈ 1023), and `δρ = 8` more `cEvalAt` for the
  digit sum. **`hAlpha` over all rows: `n = 5` rows × ~11 `cEvalAt` = ~56 000 `Ext4`
  mults** — negligible beside the cube, *provided `cRowSum` is not recomputed here*
  (it is target 3's output).
* **`alphaPublicEvals` at one cube point** (`:840-849`): `alphaTilde α (idx % d)` =
  `α^ℓ` (`:502`), an `O(ℓ)` power loop as written → up to `d = 1024` `Ext4` mults; then
  `∑_{i<n}` of an `m₁`-fold product times `mAlphaTilde Φ φF b s α i (idx/d)`, and
  `mAlphaTilde`'s first branch is `cEvalAt φF α (s.M i ⟨u,_⟩).1` (`:517`) — **another
  `d − 1 = 1023` `Ext4` mults, recomputed at every cube point**. Naive total:
  `T · (d + n·(m₁ + d)) ≈ 6.71·10⁷ · 6 159 = 4.1·10¹¹ Ext4 mults`. Catastrophic, and
  the definition's own docstring names the intended fix: "the verifier's one expensive
  step (`Õ(√(2^ℓ)·λ)` by dynamic programming, §4.4)" (`:1393`) — a spec-flagged
  direction, the same status as `Core/Basic.lean:72`'s `TODO add proper NTT`.
* **`zcTargetAlpha`** (`:875-881`): `n = 5` rows × (`m₁ = 3` selection mults +
  1 `cEvalAt` over `d`) = **≈5 120 `Ext4` mults ≈ 0.2 ms**. Touches no cube. Cheap at
  *real* constants.
* **`hypercubeSum m₀ H 0`** (`:886-887`): `T` evaluations of a `CMvPolynomial`. This is
  target 5's elephant and target 4 only defines it; at `m₀ = 26` with
  `(bZero+1)^{m₀}` monomials it is not runnable at all (`STAGE2_SCOPING.md` S4).
* **`finalCheck`** (`FinalEval.lean:99-105`): two `CMvPolynomial` evals at `m₀`. After
  Prerequisite B the first is `eq̃(τ₀, a)` and the second is the MLE of
  `alphaPublicEvals` at `a` — see the two structural wins below.

### The dominant term, and what the honest floor is

**Dominant as specified: `(m₀ + 1)·2^m₀ = 1.81·10⁹ Ext4 multiplications and 4.0 GiB
resident, in `wTableMleEval`; `31·2^m₀ = 2.08·10⁹` in `hZero`; `~4.1·10¹¹` in a naive
`alphaPublicEvals`.** The honest information-theoretic floor is far lower, and three
structural facts get most of the way there:

1. **`eval_mle_eq_eval` is already proved** (`CompPoly/Multilinear/Basic.lean:574`,
   used at `cpoly/lean/Multilinear.lean:1839`): `wTableMleEval` may be computed by
   `2^m₀ + 2^{m₀-1} + … ≈ 2·2^m₀` layer steps of 2 mults each →
   `2.7·10⁸ Ext4 mults`, a **7× drop**, with zero proof debt and the Rust already
   written and verified (`cpoly/src/multilinear.rs:538`). Memory unchanged (2.0 GiB).
2. **`d = 1024 = 2^10` makes the flat index a bit-boundary split.** `wTableIndex` is
   `d·u + ℓ` (`:1187`), so bits `0..9` of `idx` are `ℓ = idx % d` and bits `10..m₀-1`
   are `u = idx / d` — literally `evalsplit::split_equiv` at `2^nl = ML_LOW_LEN = 1024`
   (`hachi/src/evalsplit.rs:66-68`), whose `nl = 10` is the same 1024
   (`params.rs:234`). Hence `mle[w̃](a) = lagB(a_low)ᵀ · W · lagB(a_high)` for the
   `R × d` coefficient matrix `W` — `EvalSplit.lean`'s `evalSplit`/`split_form`
   precedent, already translated. Cost: `2^10 + 2^16` basis entries (**2.1 MiB, not
   2.0 GiB**) plus `R·d = 5.88·10⁷` `Fp × Ext4` accumulations (`2.4·10⁸ Fp` mults) plus
   `R = 57 384` `Ext4` mults. **The 2 GiB table need never be materialized.** This is
   the honest floor: `R·d` = the number of committed `Z_q` coefficients.
3. **`alphaPublicEvals` is a tensor product across the same split.** Its value at flat
   index `idx` is `α^{idx%d} · A(idx/d)` with `A(u) = ∑_i eq̃(τ₁,i)·M̃_α(i,u)`
   (`:857-862`) — a product of a function of `ℓ` alone and a function of `u` alone. So
   its MLE at `a` factors as (low half) × (high half); the low half is
   `∑_ℓ α^ℓ ∏_j(…) = ∏_{j<10}((1-a_j) + a_j·α^{2^j})`, **10 mults**, and the high half
   is a `2^{m₀-10} = 2^16 = 65 536`-entry table — a **1024× shrink, 2 MiB instead of
   2 GiB**. Hoisting `cEvalAt α (s.M i u)` into the 8.8 MiB `M̃_α` table (see the size
   table) removes the `d`-factor recomputation and the 2.2 GiB dense `s.M` from the hot
   path at the same time. Combined: `~2.9·10^5 Ext4` mults for the whole public factor
   instead of `4.1·10¹¹`.
4. **`eq̃(τ₀, a)` collapses to `m₀` mults, but the lemma does not exist at the pin.**
   `(cEqualityPolynomial m₀ τ₀).eval a` is `∑_x eq̃(τ₀,x)·eq̃(x,a)` (by `:840-842`,
   `:973`, `:955`), which mathematically equals
   `∏_i ((1-τ₀ᵢ)(1-aᵢ) + τ₀ᵢaᵢ)` — `eqPolynomial_expanded`
   (`ArkLib/Data/MvPolynomial/Multilinear.lean:94-95`) is the right-hand side and
   `eqTilde` (`:92`) the name, **but no lemma at the pin joins them**: the only
   `MLE`↔`eqPolynomial` fact is `MLE_eval_zeroOne` (`Multilinear.lean:146-148`), which
   is the Boolean case. cpoly's `eq_tilde` (`src/multilinear.rs:248`) is also the
   `O(n·2^n)` `lagrange_basis`-then-`dot` form, not the product. So this is
   `m₀ = 26` mults versus `(m₀+1)·2^m₀` **at the cost of one new lemma** — the highest
   value-per-line item in the target, and honestly a new proof obligation rather than a
   citation.

### Bench framing

Cases in `<module>/<op>` form, as the harness thinks
(`hachi/benches/exclusions.toml` header): `zerocheck/w_table`,
`zerocheck/w_table_mle_eval`, `zerocheck/h_zero`, `zerocheck/h_alpha`,
`zerocheck/alpha_public_evals`, `zerocheck/m_alpha_tilde`,
`zerocheck/zc_target_alpha`. Plus a `zerocheck/_control` case, per the group
convention that put a 10–15% floor under every reading
(`NOTES.md` § "The first benchmark run").

**Scale policy — REDUCED throughout, and the removal condition is not `ring::mul`.**
`STAGE2_SCOPING.md` § "Scale policies" fixes REDUCED semantics tests and REDUCED-only
bench cases for this target, with the `exclusions.toml` bar applying to anything that
cannot be shrunk. Restating the reason in the form every note here must carry: **the
wall is `m₀`'s cube size — `2^26` entries, ≈2 GiB as an `Ext4` table — and no
multiplication speedup touches it.** A sub-quadratic `ring::mul` champion is the removal
condition for the `commit::generate_decomps`-class exclusions
(`hachi/benches/exclusions.toml:82-98`) and has **no bearing** on this target: `wTable`
performs no ring multiplication at all, and `wTableMleEval` is a field dot product. The
two walls must never be conflated in a note, an exclusion line, or a commit message.

Concrete REDUCED shapes (STAGE2 says "use a small-m₀ shape and state it"; here is the
statement, and note `m₀` has a **floor**):

* `d = RING_DEGREE = 1024` is a pinned const (`params.rs:88`) and `μ ≥ 1`, `n ≥ 1`,
  `δρ = 8`, so `2^m₀ ≥ (1 + 8)·1024 = 9216` ⇒ **`m₀ ≥ 14` is the floor for any shape at
  the pinned ring degree.** "Small `m₀`" cannot mean 5.
* **Primary REDUCED shape: `μ = 1`, `n = 3`, `δρ = 8`, `d = 1024` ⇒ `R = 25`,
  `R·d = 25 600`, `m₀ = 15` (`2^15 = 32 768`), `m₁ = 2` (`3 ≤ 4`).** Table `2^15`
  `Ext4` = 1 MiB; `wTableMleEval` naive ≈ `16·32 768 = 5.2·10^5 Ext4` mults ≈ 21 ms —
  benchable. Exercises: the two-level row split (1 `z` row, 24 digit rows), the cube
  zero padding (`32 768 − 25 600 = 7 168` points), the `m₁` row padding
  (`n = 3 < 4 = 2^m₁`, so `sum_cube_rowIndexed`'s dropped row is live), and the
  guard-ordered subtraction at the `μ`/digit seam.
* **Minimal variant: `μ = 1`, `n = 1` ⇒ `R = 9`, `m₀ = 14`, `m₁ = 1`** — for the
  degenerate-shape tests only; `n = 1 < 2 = 2^m₁` still pads one row.
* **`zerocheck/zc_target_alpha` runs at real constants** (`n₀ = 5`, `m₁ = 3`,
  `d = 1024`, ≈5 120 `Ext4` mults, ≈0.2 ms) because it materializes no cube table. That
  is consistent with the policy as written ("no test may materialize a `2^m₀` table")
  and worth saying, because the table row reads as blanket-REDUCED.
* `zerocheck/m_alpha_tilde` and `zerocheck/alpha_public_evals` are blocked at real
  constants by **`s.M`, not by `m₀`**: `RlinStatement.M : PolyMatrix (Rq Φ) n μ`
  (`Rlin.lean:97-99`) is `5 · 57 344` `Rq` = 2.2 GiB. REDUCED for both, with that
  arithmetic named in the note.
* Full-const bodies are kept and `#[ignore]`d with the "full-const scale" form, per
  `hachi/tests/{commit,evalsplit}_semantics.rs` (e.g.
  `evalsplit_semantics.rs:171`) — and the ignore reason must name the *cube*, not
  `ring::mul`.

---

## Strategy candidates

Highest tier first. Detail lives in the strategy skills; these are pointers with a
reason and a size.

1. **`opt-algo-swap`** — replace `CMlPolynomialEval.eval`'s Lagrange dot with the
   layer fold for `wTableMleEval`. **Zero proof debt**: `eval_mle_eq_eval` is proved
   (`CompPoly/Multilinear/Basic.lean:574`) and `MultilinearEvals::eval_mle` is written
   *and* verified (`cpoly/src/multilinear.rs:538`, `cpoly/lean/Multilinear.lean:1818`).
   `(m₀+1)·2^m₀ → ~2·2^m₀`.
2. **`opt-algo-swap`** — the `d = 2^10` **evaluation split** on `wTableMleEval` and on
   `alphaPublicEvals`' MLE: `mle[w̃](a) = lagB(a_low)ᵀ·W·lagB(a_high)`. Removes the
   `2^m₀` materialization entirely (2.0 GiB → 2.1 MiB) and lands on the already
   translated `evalsplit::eval_split_eval` / `linalg::PolyMatrix::split_form` shape
   (`hachi/src/evalsplit.rs:336-341`). Obligation: the split identity at the `F` carrier
   — `EvalSplit.lean`'s `evalSplitEval_eq_eval` is at the `Rq` carrier and the
   `hachi` translation instantiates it there (`evalsplit.rs:20-28`), so this is a
   re-instantiation at `F = Ext4`, plus `d = 2^{RING_LOG_DEGREE}`
   (`params_semantics::ring_degree_is_a_power_of_two`, cited at `params.rs:86-87`).
3. **`opt-algo-swap`** — **precomputed power tables**, the strategy's own named shape:
   `alphaTilde α ℓ` for `ℓ < d` (`:515`) hoisted to a `d`-entry table (32 KiB, 1023
   mults once, instead of up to `d` mults per cube point); `φF((b:ZMod q)^u)` for
   `u < δρ = 8` (`:532`) likewise, mirroring `gadget::base_pow`
   (`hachi/src/gadget.rs:105-114`); and the tensor collapse
   `∑_ℓ α^ℓ·eq̃ = ∏_{j<10}((1-a_j) + a_j α^{2^j})`, 10 mults for the whole low half.
4. **`opt-algo-swap`** — **hoist `cEvalAt α (s.M i u)` out of `mAlphaTilde`** into an
   `n × μ` `M̃_α` table. Kills a `d`-factor recomputation per cube point *and* drops the
   working set from `s.M`'s 2.2 GiB to 8.8 MiB. The direction is spec-flagged at
   `Constraints.lean:1393` (dynamic programming, `Õ(√(2^ℓ)·λ)`), which is the
   `Core/Basic.lean:72`-style licence to substitute.
5. **`opt-algo-swap`** — hoist `rhoDigits Φ b (w.ρ i) u` out of `wTable`: compute each
   `(row, digit)` block once as `d` coefficients instead of rebuilding `d` coefficients
   per entry (`RhoDigits.lean:127-128` inside `Constraints.lean:148`). A `d = 1024`×
   reduction on the digit block, and structurally the same move
   `gadget::gadget_decompose` already makes (`hachi/src/gadget.rs:146-166`: the `k` loop
   is innermost, one `Rq` built per `(i, e)`).
6. **`opt-algo-swap` (the eq̃ collapse; needs one new lemma)** — replace
   `(cEqualityPolynomial m₀ τ₀).eval a` by `∏_i ((1-τ₀ᵢ)(1-aᵢ) + τ₀ᵢaᵢ)`.
   `m₀ = 26` mults instead of `(m₀+1)·2^m₀`, and the `2^m₀` table disappears from
   `finalCheck`'s first conjunct. The lemma is *not* at the pin (see § Cost model item
   4); it is provable from `eqPolynomial_expanded`
   (`ArkLib/Data/MvPolynomial/Multilinear.lean:94`) plus a `Finset.prod_univ_sum`
   expansion. Highest value per line in the target; the only one of the six with real
   proof debt.
7. **`opt-inplace-buffers`** — every table here is `Vector.ofFn`/`Vec::push` over
   `2^m₀` or `R·d` entries (`:206`, `:215`, `:330`); pre-size the buffer, and fuse
   `wTable` → `rangeProduct` (`hZero`, `:206-207`) and `wTable` → `dot` accumulation so
   the table is *streamed*, never stored. This is what makes item 2's memory win real
   rather than a smaller allocation.
8. **`opt-list-to-array`** — the spec's carriers are `Vector F (2^m)` and
   `Fin (μ + n·δρ) × Fin d` `Finset.sum`s (`:543-544`, `:1254`); the `∑ u, ∑ ℓ` double
   `Finset.sum` of `alphaContract` and the `∏ i : Fin m₁` selection products
   (`:846-847`) become indexed `Vec` loops. Mechanical, and a prerequisite for the
   others to land on translatable shapes.
9. **`opt-tailrec-loops`** — `evalMleValues` is structural recursion on `n`
   (`CompPoly/Multilinear/Basic.lean:491-497`); cpoly's Rust already presents it as a
   `while` loop over layers (`cpoly/src/multilinear.rs:538-548`) with the loop spec
   proved (`eval_mle_loop1_spec`, `cpoly/lean/Multilinear.lean:1754`), so this is
   *satisfied by reuse* rather than owed.
10. **`opt-word-arith`** — thin here. The only word-level lever is the
    `Fp × Ext4` heterogeneous multiply (`cpoly/src/field.rs:337`, 4 `Fp` mults vs 19):
    every `wTable` entry is `φF` of a base-field coefficient, so the table's *entries*
    can be kept as `Fp` and only the accumulator as `Ext4`. A ~5× on the dominant
    `R·d` term of item 2, at the cost of one representation lemma
    (`φF = Ext.ofBaseRingHom`, `CompPoly/Fields/Extension/Bridge.lean:354-359`, per
    STAGE2 § "Decision 3"). No delayed reduction and no `u128` accumulator is available:
    all arithmetic is in the extension field, through cpoly's proved ops.
11. **A dense-table `CMvPolynomial` sibling** *(no skill yet — it is Prerequisite B,
    scoped as an `opt-*` candidate per `STAGE2_SCOPING.md` § "Erasure catalogue")*:
    `sumcheckPolyZero`/`sumcheckPolyAlpha`/`cMultilinearExtension`/`cEqualityPolynomial`
    get evaluation-equal dense siblings via the eight factoring lemmas tabulated in
    § Definition chain, so the `ExtTreeMap` type never reaches Rust. It must be
    *additive*: the degree theorems (`:1082`, `:1097`) are about the sparse polynomial
    and would be orphaned by a replacement.

Explicitly **not** applicable: anything aimed at `ring::mul`. This target performs no
`Rq` multiplication (the one exception, `cRowSum`'s `CPolynomial` product at
`Reduction.lean:441`, is target 3's output and is non-negacyclic, so `ring.rs`'s
product is the wrong shape for it — see § Corrections).

---

## Representation

### Reuse, not reimplementation

The hard rule (`hachi/src/lib.rs:47-52`; `arklib-analyze` § 6) applies with unusual
force here, because for the first time in this crate the carrier is the *extension*
field:

* `F = Ext4` — `cpoly::Ext4` (`cpoly/src/field.rs:185`, re-exported at
  `cpoly/src/lib.rs:84`), a named-fields `struct {c0,c1,c2,c3 : Fp}`, so the extracted
  model is straight-line. STAGE2 § "Decision 3" (b) records that the Rust `Ext4`
  already extracts (Workstream 0 probe), so this is proof work, not extraction risk.
  `hachi/src` currently imports only `cpoly::Fp` (`ring.rs:44`, `commit.rs:57`,
  `gadget.rs:50`); `zerocheck.rs` is the first `Ext4` consumer.
* `CMlPolynomialEval F m` (`CompPoly/Multilinear/Basic.lean:47`) —
  `cpoly::MultilinearEvals` (`cpoly/src/multilinear.rs`, re-exported at
  `cpoly/src/lib.rs:85`), a `Vec<Ext4>` newtype that Aeneas extracts as a
  `@[reducible]` abbreviation of `alloc.vec.Vec cpoly.field.Ext4`
  (`cpoly/src/multilinear.rs:37-40`), with `from_values`/`values`/`into_values`/`len`
  and the proved `eval`, `eval_mle`. **`hZero`, `hAlpha` and `cWTableMle` are all
  `MultilinearEvals`; do not declare a new table type.** Note the deliberate
  monomial/Lagrange type split (`cpoly/src/multilinear.rs:15-25`): these three are all
  the *Lagrange* reading, so `MultilinearEvals` and never `MultilinearPoly`.
* `lagrange_basis`, `dot`, `eq_tilde`, `eval_mle_layer` — cpoly's, at `Ext4`. The
  `Rq`-carrier duplicates in `hachi/src/evalsplit.rs:142-196` exist because that
  layer's carrier is `Rq` and the header says so explicitly
  (`evalsplit.rs:30-39`); at `F = Ext4` the reason evaporates and cpoly's must be used.

### New Rust surface in `hachi/src/zerocheck.rs`

Proposed, extending the API walk's `zerocheck.rs` sketch (`STAGE2_SCOPING.md`
§ "API mapping": `zc_target_alpha`, `w_table_mle_eval`) to the full definition list this
target owns:

| ArkLib | Rust | shape |
|---|---|---|
| `wTable` (`:140`) | `w_table(w: &LiftedWitness, m0: usize, pt_idx: usize) -> Ext4` | two-level index split; guard-ordered `-` |
| `cWTableMle` (`:341`) | `c_w_table_mle(w, m0) -> MultilinearEvals` | `two_pow(m0)`-counter loop |
| `wTableMleEval` (`:348`) | `w_table_mle_eval(w, m0, a: &[Ext4]) -> Ext4` | delegates to `MultilinearEvals::eval` (then `eval_mle`) |
| `rangeProduct` (`:96`) | `range_product(v: Ext4) -> Ext4` | `1..GADGET_BASE` loop, no `b-1` |
| `hZero` (`:204`) | `h_zero(w, m0) -> MultilinearEvals` + `h_zero_is_zero(...) -> bool` | the `= 0` form is the pointwise loop of `:219-233` |
| `hAlphaEvals` (`:176`, computable sibling) | `h_alpha_evals(s, alpha, w, m1, pt_idx) -> Ext4` | Prerequisite A |
| `hAlpha` (`:213`, computable sibling) | `h_alpha(...) -> MultilinearEvals` + `h_alpha_is_zero` | |
| `alphaTilde` (`:515`) | `alpha_powers(alpha, len) -> Vec<Ext4>` | table, not a per-call power |
| `mAlphaTilde` (`:528`) | `m_alpha_tilde(s, alpha, i, u) -> Ext4` / hoisted `m_alpha_table` | three-case branch; `u - μ` guard-ordered |
| `alphaPublicEvals` (`:853`) | `alpha_public_evals(s, alpha, tau1, m0, m1, pt_idx) -> Ext4` | reads `eq̃(τ₁,·)` from `lagrange_basis(tau1)` |
| `zcTargetAlpha` (`:888`) | `zc_target_alpha(s, alpha, tau1, m1) -> Ext4` | real-const feasible |
| `NestedZeroCheckStatement` (`:1439-1450`) | `struct` with named fields `rlin, t, alpha, tau0, tau_alpha` | small fixed shape ⇒ named-fields struct |
| `NestedRoundStatement` (`:1453-1462`) | `struct { zc, challenges, target0, target_alpha }` | ditto |

`cEvalAt` (`Reduction.lean:444`) and `cRowSum` (`:439`) are **target 3's** items but are
consumed here; see § Corrections.

### Arities must come from arguments, not from `params::M_ZERO`

This is the one place this target must break the crate's params-hardwiring habit, and
there is precedent for both sides *inside one file*: `evalsplit::to_matrix` reads
`params::ML_LOW_LEN` (`evalsplit.rs:225`) while `evalsplit::lagrange_basis` reads
`w.len()` (`evalsplit.rs:175`) — and it is exactly the second form that lets
`lagrange_basis_sums_to_one_at_a_small_point` (`hachi/tests/evalsplit_semantics.rs:120-133`)
be a *live* test where its full-const sibling is `#[ignore]`d. **A `w_table` that reads
`m₀` from a const cannot be tested at all under the REDUCED policy**, because the only
shape it would ever have is the 4 GiB one. So: `m₀`, `m₁`, `μ`, `n` travel as arguments
or are read off the data; `d`, `b`, `δρ` stay `params` consts. Bonus: the `_spec`
statements are then the generic ArkLib statements at arbitrary `m₀`/`m₁`, which is
strictly stronger than an instantiation at `M_ZERO`.

### Shape invariants that must travel as hypotheses

Aeneas cannot see a Rust privacy boundary, so each invariant is also a hypothesis on
every `_spec` (`Wf` in `hachi/lean/Ring.lean`; `arklib-analyze` § 6):

* `cWTableMle`/`hZero` length `= 2^m₀`; `hAlpha` length `= 2^m₁` — cpoly's
  `VecReduced` + `p.val.length = 2 ^ n` pair is the established form
  (`cpoly/lean/Multilinear.lean:1819-1821`), and `hpl`/`hwl` are its names.
* `a.len() = m₀` for the evaluation point (`hwl` in the same specs).
* `2^m₀ ≤ Usize.max` (`pow2_le_usize_max`, `cpoly/lean/Multilinear.lean:~471`).
* `hμn : (μ + n·δρ)·d ≤ 2^m₀` and `hd : 0 < d` — carried by every ArkLib consumer
  (`Batch.lean:110`, `:109`) and doubling as the `Usize` overflow certificate.
* `w.ρ`'s degree bound `hρ` (`Lift/Reduction.lean:86`), which is what makes
  `rhoDigits`' truncation at `d` lossless (`RhoDigits.lean:118-122`).

### Upstream dependencies this target un-defers

* **`rho_digits`** — Decision 4's table calls it "one coefficient loop of
  `balanced_digit_at`, truncated at RING_DEGREE — its only consumers are later targets,
  so deferrable at zero cost" (`STAGE2_SCOPING.md` § "Decision 4"). **Target 4 is that
  consumer**: `wTable`'s digit branch (`Constraints.lean:148`) is `rhoDigits`. It must
  land with target 1 or at the head of target 4.
* **`balanced_digit_at`** and `params::BALANCED_SHIFT`/`HALF_BASE` — target 1.
* **`c_eval_at`, `c_row_sum`** — nominally target 3 (they live in
  `RingSwitch/Reduction.lean:439-445`) but absent from target 3's row; see § Corrections.
* **TE item 1**, `LawfulBEq (Ext P)`, before any `==`-bearing spec here
  (`STAGE2_SCOPING.md` § "Decision 3", TE work list).

---

## Corrections to `STAGE2_SCOPING.md`

Each with the evidence from the pin. None of them changes the target's ordering or its
"larger than evalsplit" sizing.

1. **§ "Shape-list corrections" item 2 is half wrong.** It says
   "`finFunctionFinEquiv` cancels against `.symm` in every consumer, so no bit machinery
   survives — the loops are plain flat-index loops." True for the `m₀`-side table
   constructors (`hZero` `:206-207`, `hAlpha` `:215`, `cWTableMle` `:330` all feed
   `.symm i` straight into a `finFunctionFinEquiv`, cancelled by
   `Equiv.apply_symm_apply` as at `:388`). **False for the `m₁`-side `eq̃` weights**:
   `alphaPublicEvals` (`:845-847`) and `zcTargetAlpha` (`:877-879`) both compute
   `∏ j : Fin m₁, if (finFunctionFinEquiv.symm ⟨(i:ℕ), hi⟩) j = 1 then τ₁ j else 1 - τ₁ j`
   — the bits of `i` are *read coordinate-wise* under a product and do **not** cancel.
   Benign, because that product is exactly entry `i` of
   `CMlPolynomialEval.lagrangeBasis τ₁` (`CompPoly/Multilinear/Basic.lean:410-411`) and
   cpoly's `lagrange_basis` + `lagrangeBasis_getElem'`
   (`cpoly/src/multilinear.rs:169`, `cpoly/lean/Multilinear.lean:414-417`, with the
   `BitVec.ofFin`↔`Nat.testBit` bridge at `:400`) already implement and prove it. But
   the claim as written would send the translation looking for a flat-index loop where a
   bit loop is required, and would miss a free reuse.
2. **§ "Scale/overflow hazards at Fig. 9" lists one memory wall; there are two.**
   Item (b) is the `2^m₀` `Ext4` table (≈4 GiB) ✓. The second is
   `RlinStatement.M : PolyMatrix (Rq Φ) n μ` (`Rlin.lean:97-99`), which at
   `(n₀, μ₀) = (5, 57 344)` is `286 720` `Rq` = `2.94·10^8` `Fp` words = **2.2 GiB**, and
   it is what actually blocks `mAlphaTilde`/`alphaPublicEvals` at real constants. It is
   equally independent of `ring::mul`. Consequence: the `exclusions.toml` note for those
   two cases must name `s.M`'s size, not `m₀`'s.
3. **§ "Minor variants" omits `cEvalAt` at a mixed carrier.** `cEvalAt φF a p` evaluates
   a `CPolynomial (ZMod q)` — `Fp` coefficients — at a point in `F = Ext4`
   (`Reduction.lean:444-445`). cpoly's `UnivariatePoly` is `Vec<Ext4>`
   (`cpoly/src/univariate.rs:57`) and its `eval` takes `x: Ext4` over `Ext4`
   coefficients (`:194`), so there is **no drop-in**: a mixed Horner
   (`acc = acc*α + Ext4::from_base(c_k)`, `d-1` `Ext4` mults) is a new minor variant, in
   the same class as the `cRowSum` `Fp` mul the section does list. It is reached from
   target 4 four times (`:517`, `:519`'s sibling branch, `:552`, `:880`) and is also
   absent from target 3's "all shapes precedented" row — so today no target owns it.
   Cheap (a `while` loop) but it should be assigned. Special case worth exploiting:
   `cEvalAt φF α Φ.φ` is `α^d + 1` at `Φ.φ = X^d + 1`, i.e. 10 squarings, not 1023 mults.
4. **§ "Erasure catalogue" understates the offsetting win.** It credits cpoly with
   `wTableMleEval` "via `eval_lagrange`" ✓ — but `CMlPolynomialEval.eval_mle_eq_eval`
   (`CompPoly/Multilinear/Basic.lean:574`) makes the `O(2^m₀)` `evalMle` *provably equal*
   to that `O(m₀·2^m₀)` dot, and `MultilinearEvals::eval_mle` is written and verified
   (`cpoly/src/multilinear.rs:538`, `cpoly/lean/Multilinear.lean:1818-1839`). So the
   headline algorithmic win on the target's dominant term arrives with **zero proof
   debt**, which is a stronger statement than "has a direct precedent".
5. **Prerequisite A is smaller than described.** § "An unlisted prerequisite step" names
   two bridging lemmas; only `cEvalAt_eq_evalAt_toPoly`
   (`Reduction.lean:471-475`) is needed for the computability repair.
   `rhoDigits_evalAt` (`RhoDigits.lean:191`) is the *Eq. (22) identification* lemma
   (used at `:763`, `:780`, `:1363`, `Batch.lean:138`, `:233`) and is orthogonal. Both
   exist at the pin, as claimed.
6. **§ "Scale policies", row 4, needs two riders.** (a) `m₀` has a floor of **14** at
   the pinned `RING_DEGREE = 1024` (since `2^m₀ ≥ (μ + n·δρ)·d ≥ 9·1024`), so
   "small-m₀ shape" is bounded below and the stated shape should say so; (b)
   `zc_target_alpha` materializes no cube and runs at real constants, so
   "REDUCED throughout" should read "REDUCED for every cube- or `M`-shaped case".
7. **Minor:** `wTableMleEval_eq` is at `Constraints.lean:341`, not `:339` (`:339` is the
   preceding `omit`). The other two cited lines (`:1382`, `:1394`) are exact.
