# Brief: the Hachi sumcheck link — `ArkLib.Lattices.Ajtai.InnerOuter.computableRoundPoly`, `roundCheck`/`roundOut`, `honestComputeG`, `finalCheck`, `honestComputeY`, and the `m₀`-round loop (ArkLib @ `294b3f0b0f46e1485c878a217e9de764855f5915`)

Target handed in by Stage 2 (`STAGE2_SCOPING.md` § "Ordered target list + scale
policies", row 5: *sumcheck — largest*). Rust home: a new `hachi/src/sumcheck.rs`.
Read from the pinned copy only; **rev** is the one `hachi/lake-manifest.json`
records for `Arklib`, `294b3f0b0f46e1485c878a217e9de764855f5915` — *not* the
`e92dc31` the `arklib-analyze` skill text still quotes. Citation root for every
`file:line` below is `hachi/.lake/packages/Arklib/ArkLib/Commitments/Functional/Hachi/`
unless the path says otherwise; `Sumcheck/…` and `ZeroCheck/…` are relative to it.
CompPoly citations are rooted at `hachi/.lake/packages/CompPoly/`, Mathlib at
`hachi/.lake/packages/mathlib/`, and the Rust field layer at
`AeneasCompPoly/cpoly/src/` (the `cpoly` git dependency, rev
`583cfaff0617180764ffd849d867331af206fc5e`, `hachi/Cargo.toml:75`).

## Confirmations and corrections to `STAGE2_SCOPING.md`

Everything this brief consumes from Stage 2 was re-checked against the pin. Six
confirmations and two corrections.

**Confirmed, verbatim:**

1. *Shape-list correction 1* — `roundCheck` has **two** conjuncts
   (`Sumcheck/Rounds.lean:100-104`); `finalCheck` has **three**, the third being
   `decide (bound ≤ stmt.zc.rlin.bound)` (`Sumcheck/FinalEval.lean:99-106`).
2. *Shape-list correction 3* — `honestComputeG` is at
   `Sumcheck/Completeness.lean:76`, not in `RoundPoly`/`Rounds`/`FinalEval`.
3. *Shape-list correction 5* — `computableRoundPoly`'s outer sum is a genuine
   `2^k` counter loop (`∑ y : Fin (M + 1 - (i+1)) → Fin 2`,
   `Sumcheck/RoundPoly.lean:288`); the *summand* `H.eval₂ CPolynomial.CHom …`
   (`:289`) carries the whole CMvPolynomial gap.
4. *Shape-list correction 2, `finFunctionFinEquiv` half* — the equivalence
   cancels against `.symm` in every consumer, so no bit machinery survives:
   `wTable` applies `finFunctionFinEquiv pt` (`ZeroCheck/Constraints.lean:143`)
   and `hZero`/`cWTableMle` feed it `finFunctionFinEquiv.symm i`
   (`:207`, `:343`). It is little-endian —
   `finFunctionFinEquiv f = ∑ i, f i · m^i`
   (`Mathlib/Algebra/BigOperators/Fin.lean:610`, `finFunctionFinEquiv_apply`) —
   which is what makes the sumcheck's fold on coordinate `0` the same thing as
   cpoly's `values[2j] / values[2j+1]` pairing (see § Strategy candidates, S1).
5. *Decision 3 — instance audit* — `computableRoundPoly`'s variable block is
   `[Field F] [BEq F] [LawfulBEq F]` and nothing else
   (`Sumcheck/RoundPoly.lean:107`, no `omit` on the target defs);
   `roundCheck`/`roundOut`/`roundProver` add `[DecidableEq F]`
   (`Sumcheck/Rounds.lean:93`); `honestComputeG` likewise
   (`Sumcheck/Completeness.lean:63`); `finalCheck` needs neither
   (`Sumcheck/FinalEval.lean:84`). `honestComputeY` sits after the file's
   `variable [SampleableType F]` (`:175`) and picks it up by section-variable
   accident, its body being exactly `wTableMleEval Φ m₀ φF b w stmt.challenges`
   (`:254-256`) — so specs state against `wTableMleEval` or pay the one-line
   instance, exactly as audited.
6. *Scale/overflow hazard (a)* — the guard-ordered `Nat` subtractions are real
   and in `wTable`: `idx / d - μ` under the guard `¬ (idx / d < μ)`
   (`ZeroCheck/Constraints.lean:145-150`).

**Correction 1 — the naive monomial count is `(2·bZero + 1)^{m₀}`, not
`(bZero + 1)^{m₀}`.** The figure Stage 2 carries (target-5 row, and S4) comes
from ArkLib's own `HachiRuntime.lean:36-38`: "`sumcheckPolyZero` is a product of
`bZero` copies of an `m₀`-variate multilinear extension, so it carries up to
`(bZero + 1)^m₀` monomials". That undercounts. `cRangeProduct m₀ b p =
p * ∏_{j ∈ Icc 1 (b-1)} ((p - C j) * (p + C j))`
(`ZeroCheck/Constraints.lean:845-847`) is `1 + 2(b-1) = 2b - 1` copies of `p`,
and `sumcheckPolyZero` multiplies by one further multilinear factor
`cEqualityPolynomial` (`:873-876`), so it is a product of `2b` multilinear
factors with per-variable degree `≤ 2b`. ArkLib proves exactly that itself:
`degreeOf_rangeProduct_le … ≤ 2 * b - 1` (`:1055-1059`) and
`degreeOf_sumcheckPolyZero … ≤ roundDegZero b` with `roundDegZero b = 2 * b`
(`:1082-1084`, `:87`). The dense monomial bound is therefore `(2b+1)^{m₀}`. At
Fig. 9 (`b = bZero = 16`, `m₀ = 27`) that is `33^27 ≈ 1.0·10^41`, against the
docstring's `17^27 ≈ 1.7·10^33` — eight orders of magnitude larger. The error
runs *toward* Stage 2's conclusion, so nothing downstream flips; but the number
in the target-5 row should read `33^27`, and the round message's degree bound is
`2b = 32` with soundness arity `k = max (2b) 2 + 1 = 33`
(`Sumcheck/Rounds.lean:189-191`).

**Correction 2 — "the naive form is impossible at `m₀ = 27`" is true but too
weak: at `b = 16` the naive form is impossible at *every* usable `m₀`, so the
naive-form exclusion is not an `m₀` condition alone.** `(2b+1)^{m₀}` at `b = 16`
is `3.9·10^7` already at `m₀ = 5` and `1.4·10^12` at `m₀ = 8`. The toy run that
finishes in six minutes does so at `b = bZero = 3` *and* `m₀ = 5`
(`scripts/HachiRuntime.lean:97` `MM := 4`, `:111` `bZero := 3`, `:30`), where the
bound is `7^5 = 16 807`. Consequence for the scale policy: a REDUCED case cannot
rescue the naive form by shrinking `m₀` while keeping `GADGET_BASE = 16`; it would
have to shrink `b` as well, at which point it is no longer measuring the operation
at anything like its shape. This *strengthens* Stage 2's "the naive form is
excluded outright until the dense champion lands" — the exclusion is
unconditional, not scale-dependent.

## Definition chain

### A. The seven items that actually compute

The target is a link, not a definition, so the first job is to separate the code
from the certificate machinery. These are the only definitions in the link with
computational content:

| # | Item | `file:line` | Computes |
|---|---|---|---|
| 1 | `computableRoundPoly` | `Sumcheck/RoundPoly.lean:286` | the round message polynomial, as a `CPolynomial F` |
| 2 | `honestComputeG` | `Sumcheck/Completeness.lean:76` | the pair `(g⁰, gᵅ) : RoundMsg F b`, = item 1 at the two summands |
| 3 | `roundCheck` | `Sumcheck/Rounds.lean:100` | `Bool`: `g(0) + g(1) == target` for both components |
| 4 | `roundOut` | `Sumcheck/Rounds.lean:110` | the round-`(i+1)` statement: `Fin.snoc` the challenge, retarget by `g(a)` |
| 5 | `finalCheck` | `Sumcheck/FinalEval.lean:99` | `Bool`: the two closing target equations plus the bound-sanity conjunct |
| 6 | `honestComputeY` | `Sumcheck/FinalEval.lean:254` | `y′ = mle[w̃](a)`, body exactly `wTableMleEval` |
| 7 | the round loop | `Sumcheck/Rounds.lean:367-398` (soundness) / `Sumcheck/Completeness.lean:349-369` (honest) | `m₀` iterations of 2+4, threading the statement |

`hypercubeSum` (`ZeroCheck/Constraints.lean:899`) is *not* on this list: in the
link it appears only inside `nestedRoundRel` (`:1475-1486`), which is a
`Set`/`Prop`. Nothing in the protocol ever evaluates it; the prover's `g` and the
verifier's checks are what stand in for it. (Its saturation lemma
`hypercubeSum_of_le` at `:915` is the reason `finalCheck` reads plain evaluations.)

### B. `computableRoundPoly` — notation to body

    computableRoundPoly H i cs
      = ∑ y : Fin (M + 1 - (i+1)) → Fin 2,
          H.eval₂ CPolynomial.CHom (freeVariableAssignment i cs y)   -- RoundPoly.lean:286-289

* `∑` is `Finset.sum` over `Fintype (Fin k → Fin 2)`, i.e. a `2^(M-i)`-term sum
  in the ring `CPolynomial F`; `+` resolves through
  `CPolynomial`'s `Add` → `Raw.add` = pad-and-`zipWith` then `trim`
  (`CompPoly/Univariate/Raw/Ops.lean:55,61`).
* `freeVariableAssignment i cs y = Fin.insertNth i CPolynomial.X (fun j =>
  CPolynomial.C (roundAssignment i cs y j))` (`RoundPoly.lean:273-275`), with
  `roundAssignment i cs y = Fin.append cs (fun k => ((y k : ℕ) : F)) ∘ Fin.cast _`
  (`:266-268`): the challenge prefix, then the Boolean tail, cast into `Fin M`.
* `CPolynomial.CHom` is `CPolynomial.C` bundled as a `RingHom`
  (`RoundPoly.lean:80-87`); it is deliberately computable, and the *proof*-side
  sibling `toPolyRingHom` (`:93`) is the noncomputable one.
* `CMvPolynomial.eval₂ f vs p = ExtTreeMap.foldl (fun s m c => f c *
  MonoR.evalMonomial vs m + s) 0 p.1`
  (`CompPoly/Multivariate/CMvPolynomial.lean:133-135`), with
  `evalMonomial vs m = ∏ᵢ (vs i) ^ m.get i`
  (`CompPoly/Multivariate/CMvMonomial.lean:204-205`). So one monomial costs
  `m₀` exponentiations **in `CPolynomial F`** — cheap only because all but the
  pivot slot are constants and the pivot is `X^e` (`mulPowX`,
  `CompPoly/Univariate/Raw/Ops.lean:95`).
* The carrier is the load-bearing part: `CMvPolynomial n R = Lawful n R =
  {p : Unlawful n R // p.isNoZeroCoef}` (`CompPoly/Multivariate/Lawful.lean:35-36`),
  `Unlawful n R = Std.ExtTreeMap (CMvMonomial n) R compare`
  (`CompPoly/Multivariate/Unlawful.lean:37`), `CMvMonomial n = Vector ℕ n`
  (`CompPoly/Multivariate/CMvMonomial.lean:35`). A sparse tree-map of dense
  exponent vectors. Multiplication is the double fold
  `p₁.foldl (fun p m₁ c₁ => (p₂.foldl …) + p)`
  (`CompPoly/Multivariate/Unlawful.lean:188-191`), i.e. `|p₁|·|p₂|` inserts.
* `H` itself is one of two things. `sumcheckPolyZero Φ m₀ φF b τ₀ w =
  cEqualityPolynomial m₀ τ₀ * cRangeProduct m₀ b (cMultilinearExtension m₀
  (wTable Φ m₀ φF b w))` (`ZeroCheck/Constraints.lean:873-876`), and
  `sumcheckPolyAlpha … = cMultilinearExtension m₀ (wTable …) *
  cMultilinearExtension m₀ (alphaPublicEvals …)` (`:881-884`), where
  `cMultilinearExtension m₀ evals = ∑ x : Fin m₀ → Fin 2, C (evals x) *
  cBooleanEqPolynomial m₀ x` (`:835-837`) and
  `cBooleanEqPolynomial m₀ x = ∏ᵢ (if x i = 1 then X i else 1 - X i)`
  (`:830-832`). Both `H`s are therefore built by a `2^{m₀}`-term sum of
  `m₀`-factor tree-map products, before `cRangeProduct` multiplies `2b - 1` more
  times. **The infeasibility bites at `H`'s construction, before
  `computableRoundPoly` runs a single outer-sum iteration.**
* The two specifications the translation must reproduce are values, not shapes:
  `computableRoundPoly_eval` (`RoundPoly.lean:356-360`) — `(crp H i cs).eval T =
  hypercubeSum (M+1) H (i+1) (Fin.snoc cs T)` — and
  `computableRoundPoly_mem_degreeLE` (`:366-370`), specialized at the two
  summands by `:406` and `:417`. `computableRoundPoly_toPoly` (`:345`) is the
  bridge both are transported along, and is proof-side only.

### C. `roundCheck`, `roundOut`, the loop

* `roundCheck stmt g = (g.1.1.eval 0 + g.1.1.eval 1 == stmt.target₀) &&
  (g.2.1.eval 0 + g.2.1.eval 1 == stmt.targetα)` (`Sumcheck/Rounds.lean:100-104`).
  `==` is `BEq F`; `beq_iff_eq` needs `LawfulBEq F`. `.1.1` peels the
  `degreeLE` subtype. `CPolynomial.eval x p = p.val.zipIdx.foldl (fun acc (a,i)
  => acc + a * x^i) 0` (`CompPoly/Univariate/Basic.lean:246-247`) — note *not*
  Horner; `evalHorner` exists beside it (`:263`).
* `roundOut stmt g a = ⟨stmt.zc, Fin.snoc stmt.challenges a, g.1.1.eval a,
  g.2.1.eval a⟩` (`Sumcheck/Rounds.lean:110-112`). The output type is
  `NestedRoundStatement … (i+1)`, whose `challenges : Fin i → F` field
  (`ZeroCheck/Constraints.lean:1453-1462`) is one wider — this is the shape change
  per round.
* `roundVerifier` is `if roundCheck … then pure (roundOut …) else failure`
  (`Sumcheck/Rounds.lean:116-123`); the guard and verdict are carried as
  computable data by `roundVerifierGuardedForm` (`:134-140`) with `verify_eq` by
  `rfl`.
* `roundProver` (`:164-182`) is the honest prover shell: `PrvState` at three
  indices, `sendMessage ⟨0,_⟩` emits `computeG st.1 st.2`, `receiveChallenge
  ⟨1,_⟩` stores `c`, and `output` rebuilds the statement. **`output` re-evaluates
  `computeG stmt wit` twice more** (`:181-182`), so a literal transcription runs
  the dominant computation three times per round; see § Cost model.
* Wire format: `pSpecScalar (RoundMsg F b) F` per round, concatenated by
  `roundsSpec : (count : ℕ) → ProtocolSpec (2 * count)` with
  `roundsSpec (count+1) = roundsSpec count ++ₚ pSpecScalar …`
  (`Sumcheck/Rounds.lean:71-73`) — 2 slots per round, `2m₀ = 54` at Fig. 9,
  matching Stage 2's § "API mapping" wire count.
* `RoundMsg F b = ↥(CPolynomial.degreeLE (roundDegZero b : ℕ)) ×
  ↥(CPolynomial.degreeLE (roundDegAlpha : ℕ))` (`:65-67`), with
  `degreeLE n = {p | p.val.degreeBound ≤ n}`
  (`CompPoly/Univariate/Linear.lean:47`).

### D. `finalCheck`, `honestComputeY`

    finalCheck … stmt y'
      = ((cEqualityPolynomial m₀ stmt.zc.τ₀).eval stmt.challenges
            * rangeProduct b y' == stmt.target₀)
        && (y' * (cMultilinearExtension m₀ (alphaPublicEvals Φ m₀ m₁ φF b
              stmt.zc.rlin stmt.zc.α stmt.zc.τα)).eval stmt.challenges
            == stmt.targetα)
        && decide (bound ≤ stmt.zc.rlin.bound)          -- FinalEval.lean:99-106

Three conjuncts. `rangeProduct b v = v * ∏_{j ∈ Icc 1 (b-1)} ((v - j) * (v + j))`
(`ZeroCheck/Constraints.lean:96-97`) — `2b - 1 = 31` field multiplications at
`b = 16`. The two polynomial evaluations are `CMvPolynomial.eval` at the
`m₀`-point `stmt.challenges`, i.e. `eval₂ (RingHom.id _)`
(`CompPoly/Multivariate/CMvPolynomial.lean:217-218`) over `2^{m₀}`-monomial
multilinear objects. `alphaPublicEvals` itself is
`alphaTilde α (idx % d) * ∑ᵢ (∏ⱼ eq-select(τ₁)) * mAlphaTilde Φ φF b s α i (idx / d)`
(`:853-862`), a *product of a column factor and a row factor* under the flat
index's `div`/`mod` split — the structure the `Õ(√(2^ℓ)·λ)` dynamic-programming
remark of §4.4 points at (`:1425`), and `wTableIndex_div_mod` (`:1207`) already
proves that split.

`honestComputeY φF stmt w = wTableMleEval Φ m₀ φF b w stmt.challenges`
(`FinalEval.lean:254-256`), and `wTableMleEval φF b w a =
CMlPolynomialEval.eval (cWTableMle Φ m₀ φF b w) (Vector.ofFn a)`
(`ZeroCheck/Constraints.lean:348-350`), with `cWTableMle = Vector.ofFn fun i =>
wTable … (finFunctionFinEquiv.symm i)` (`:341-343`). `CMlPolynomialEval R n =
Vector R (2 ^ n)` (`CompPoly/Multilinear/Basic.lean:47`) and
`CMlPolynomialEval.eval p x = Vector.dotProduct p (lagrangeBasis x)` (`:524`) —
which **materializes a `2^{m₀}`-entry Lagrange table**
(`lagrangeBasis`, `:410-411`). The layered sibling `evalMle`
(`:499`, via `evalMleStep`/`evalMleLayer` `:467`/`:475`) does the same in halving
tables and is the shape to translate; `evalMle_succ` (`:512`) is the recursion
lemma.

`finalEvalVerifier` is again `if finalCheck … then pure ⟨t, a, y'⟩ else failure`
(`FinalEval.lean:110-117`), guard-as-data at `:128-133`. The step has no
challenge round (`IsEmpty (pSpecFinalEval F).ChallengeIdx`, `:55`) and is
`ProverOnly` (`:65`), so the honest run is one `pure`
(`finalEvalProver_run_support`, `:320-341`).

### E. Scaffolding versus computational content — the explicit split

**Not translated (dependently-typed certificate scaffolding).** None of these has
a Rust counterpart; they are the interactive-reduction framework's bookkeeping and
the soundness argument's carrier.

| Scaffolding | `file:line` | Why it is not code |
|---|---|---|
| `roundsSpec` | `Sumcheck/Rounds.lean:71-73` | structural recursion on the round count producing a *type* (`ProtocolSpec (2*count)`); the Rust loop is `for i in 0..M0` and the wire order is fixed by the `OpeningProof` field order |
| `roundsSpecSampleable` | `:78-85` | instance recursion; challenges are caller-supplied in Rust (Stage 2 § "API mapping": public-coin, oracle at run time) |
| `roundsChainAux` | `:367-398` | returns a **subtype** `{P : EscapeGCWSSPackage … // P.relIn = … ∧ P.relOut = …}` — the relation invariant rides along because the endpoints are definitional only per instance. Pure proof plumbing |
| `roundsChain` + `_relIn`/`_relOut` | `:409-438` | re-pins the seams so downstream composes by `rfl`; zero computational content |
| `roundVerifier`/`roundPackage`/`roundEsc`/`roundExtractor` | `:116`, `:327`, `:198`, `:215` | the `Verifier`/`EscapeGCWSSPackage` wrappers, the escape event and the tree extractor. The *guard* and the *verdict* inside them are items 3 and 4 and **are** translated |
| `roundProver`/`roundReduction`/`roundsReduction(Aux)` | `:164`, `Completeness.lean:168`, `:349`, `:363` | the `Prover` record and the honest-chain fold. The *body* of `sendMessage`/`output` is items 2 and 4 |
| `finalEvalVerifier`/`Prover`/`Package`/`Extractor` | `FinalEval.lean:110,147,419,179` | same pattern |
| `NestedRoundStatement … i`'s dependence on `i` | `ZeroCheck/Constraints.lean:1453-1462` | the `challenges : Fin i → F` field grows by `Fin.snoc` each round; erased to one `Vec<Ext4>` that is `push`ed |
| `RoundMsg`'s two `degreeLE` subtypes | `Sumcheck/Rounds.lean:65-67` | subtype erasure; the bound becomes a runtime check or a stated precondition |
| `hρ` field of `LiftedWitness` | `ProofSystem/RingSwitching/Lift/Reduction.lean:86` | a `Prop`; travels as a `Wf`-style hypothesis on each `_spec` |
| `nestedRoundRel`, `relWEvalClaim`, `liftShort` | `ZeroCheck/Constraints.lean:1475`, `FinalEval.lean:167` | `Set`/`Prop`; never evaluated |

**Translated, with erasure and in-repo precedent.** This is the whole of
`hachi/src/sumcheck.rs`.

| Computational piece | Erasure | In-repo precedent |
|---|---|---|
| outer sum `∑ y : Fin k → Fin 2` (`RoundPoly.lean:288`) | `while j < two_pow(k)` counter loop over the flat index | `evalsplit::monomial_basis`/`lagrange_basis` (`hachi/src/evalsplit.rs:142,174`), `two_pow` (`:89`) |
| `H.eval₂ CHom (insertNth i X (C ∘ s))` (`:289`) | **no precedent — this is the CMvPolynomial gap.** Replaced, not translated: see § Strategy candidates S1/S2 | — |
| `CPolynomial F` (the message) | `Vec<Ext4>` newtype, coefficients low-to-high, length `≤ 2b+1` by construction | `ring::Rq` is the same shape at fixed length (`hachi/src/ring.rs:54`); cpoly's `UnivariatePoly` is the variable-length one |
| `CPolynomial.eval` at `0`, `1`, `a` (`Basic.lean:246`) | index/`Horner` loop; at `0` and `1` it degenerates (see § Semantics risks) | `linalg::PolyVec::dot` (`hachi/src/linalg.rs:188`) is the same fold shape |
| `Fin.snoc stmt.challenges a` (`Rounds.lean:112`) | `challenges.push(a)` on a `Vec<Ext4>` pre-sized to `M0` | `evalsplit::to_polynomial`'s push loop (`hachi/src/evalsplit.rs:271`) |
| `Bool` conjunction of `==` checks (`:103-104`, `FinalEval.lean:101-106`) | `&&` of `Ext4` equality (derived `PartialEq`, `cpoly/src/field.rs:184`) and a `u64` `<=` | `commit::verify_weak` is exactly this shape (`hachi/src/commit.rs`) |
| `rangeProduct b v` (`Constraints.lean:96`) | `while j < GADGET_BASE - 1` product loop over `Ext4` | `gadget::base_pow` (`hachi/src/gadget.rs:105`) — the same "exactly `n` factors, even when trivial" convention |
| `cEqualityPolynomial.eval a` (`FinalEval.lean:101`) | `m₀`-factor product loop (after S3) | `evalsplit::lagrange_basis`'s inner product loop (`hachi/src/evalsplit.rs:182-194`) |
| `wTableMleEval` / `honestComputeY` (`Constraints.lean:348`) | halving-table fold, `evalMleLayer` shape | `cpoly::multilinear::eval_mle_layer` (`cpoly/src/multilinear.rs:280`) — **already written, already extraction-clean** |
| `wTable` (`Constraints.lean:140-151`) | two-level guarded index split: `idx/d < μ`, else `idx/d - μ < n·δ` with a further `/δ`, `%δ` | `evalsplit::split_equiv_inv` (`hachi/src/evalsplit.rs:77`), `commit::flatten_blocks` (`hachi/src/linalg.rs:274`) |
| `alphaPublicEvals` table (`Constraints.lean:853`) | row/column tensor split (S4) then two folds | `linalg::PolyMatrix::split_form` (`hachi/src/linalg.rs:258`) is the same bilinear shape |
| the `m₀`-round loop (`Rounds.lean:367`) | one `while i < M0` over a mutable statement struct | `commit::generate_decomps`' triple loop |

## Parameters

Computed at `hachi/src/params.rs` as it stands today (re-read at the start of this
brief; a second session is editing the same tree, per `STAGE2_SCOPING.md`
§ "Sequencing note").

**Pinned** (outside this crate's choice):

| Const | Value | Pin |
|---|---|---|
| `Q` | `2^32 - 99 = 4 294 967 197` | `cpoly`'s `Fp` (`params.rs:41-51`; `cpoly/src/field.rs:56`) |
| `EXT_DEGREE` | `4` | `cpoly`'s `Ext4` (`params.rs:58`) |
| `RING_DEGREE` | `1024` (`α = 10`) | [NOZ26] Fig. 9, ℓ = 30 (`params.rs:75-88`) |
| `GADGET_BASE` | `16` | Fig. 9 (`params.rs:97`) |
| `GADGET_DIGITS` | `8` | Fig. 9, and forced by `q ≤ b^digits` (`params.rs:113`) |
| `MESSAGE_ROWS` = `BLOCKS` | `1024` (`2^m`, `2^r`, `m = r = 10`) | Fig. 9 (`params.rs:124,147`) |
| `INNER_ROWS` = `OUTER_ROWS` | `1` (`n_A = n_B = 1`) | Fig. 9 (`params.rs:133,140`) |
| `GAMMA` | `16` | weak-opening `γ̄ = b` (`params.rs:166`) — **not** the chain's `γ` |
| `KAPPA` | `32` | `2ω` at `ω = 16` (`params.rs:268`) |
| `ML_VARS_LOW` = `ML_VARS_HIGH` | `10` | derived from `BLOCKS`/`MESSAGE_ROWS` (`params.rs:216,225`) |

**Chosen** (Stage 2 additions, paper pins with no spec constraint):
`D_ROWS = 1` (Fig. 9 `n_D`), `B_ZERO = 16`, `OMEGA = 16`,
`CHALLENGE_WEIGHT = 16`, `Z_BOUND = 30583` — `STAGE2_SCOPING.md`
§ "Parameter mapping". Of these, only `B_ZERO` is used by this target.

**Derived** — the numbers this brief's cost model is a claim *about*. All from
`STAGE2_SCOPING.md` § "Parameter mapping"; each re-checked against the pin here.

| Quantity | Value | Derivation, re-verified |
|---|---|---|
| `Z_DIGITS` (`zDigits`, `τ`) | **8** | `zDigits := Nat.clog b q` (`Correctness.lean:511`, `hqz` by `Nat.le_pow_clog` at `:510-516`); `16^7 < q ≤ 16^8` |
| `RHO_DIGIT_COUNT` (`δρ`) | **8** | `rhoDigitCount q b = Nat.clog b q` (`RingSwitch/RhoDigits.lean:66`) |
| `CHAIN_GAMMA` (`P.γ`) | **15** | `ofPinnedDigitBase 16` sets `γ := b - 1` (`HonestChain.lean:165-175`), pinned by `pinned_of_soundness_orientations` (`:188-193`) |
| `B_ZERO` (`P.bZero`) | **16** | `ofPinnedDigitBase` sets `bZero := b` (`HonestChain.lean:167`) |
| `RLIN_COLS` (`μ₀`) | **81 920** | `rlinCols 1 8 8 8 10 10 = 2^10·8 + (2^10·(1·8) + 2^10·8·8) = 8192 + 8192 + 65536` (`RingSwitch/Rlin.lean:153`) |
| `RLIN_ROWS` (`n₀`) | **5** | `rlinRows 1 1 1 = 1 + (1 + (1 + (1 + 1)))` (`Rlin.lean:158`) |
| `LIFT_COLS` | **81 960** | `μ₀ + n₀·δρ = 81920 + 40` |
| table entries | **83 927 040** | `LIFT_COLS · d = 81960 · 1024` |
| **`M_ZERO` (`m₀`)** | **27** | least `m₀` with `(μ₀ + n₀·δρ)·d ≤ 2^{m₀}` — the `hcov`/`hμn` hypothesis (`Composition.lean:292`, `Constraints.lean:538`). `2^26 = 67 108 864 < 83 927 040 ≤ 2^27 = 134 217 728` |
| **`M_ONE` (`m₁`)** | **3** | least `m₁` with `n₀ ≤ 2^{m₁}` — `hn` (`Composition.lean:293`); `5 ≤ 8` |
| the sumcheck's `b` | **16** | `roundsChain 𝓜(q,α) m₀ m₁ γ b b …` (`Composition.lean:326`) instantiated at `liftShort Φ P.γ P.bZero` (`Correctness.lean:502,254`), so `(bound, bDig, b) = (15, 16, 16)` |
| `roundDegZero b` | **32** | `2 * b` (`ZeroCheck/Constraints.lean:87`) |
| `roundDegAlpha` | **2** | `ZeroCheck/Constraints.lean:90` |
| soundness arity `k` | **33** | `max (roundDegZero b) roundDegAlpha + 1` (`Sumcheck/Rounds.lean:255`) |
| challenge count | 1024 ring + **58** field | `m₀ + m₁ + 1 + m₀ = 27 + 3 + 1 + 27` — matches Stage 2 § "API mapping" |

**The `BETA_SQ`/τ contest, and how it reaches this target.** `BETA_SQ` is not read
anywhere in the sumcheck link, so the contested literal itself is
symbolic here; the tree currently shows the `τ = 8` value
`704 250 333 132 185 328 448 176 128` (`params.rs:206`), and the user has chosen
`4` with another agent implementing. **But `τ` and `zDigits` are the same formal
slot** (`QuadEval/Gadgets.lean:123`: "`zDigits = τ`"), and `zDigits` *does* reach
this brief, through `rlinCZ = 2^m · messageDigits · zDigits` (`Rlin.lean:166`) →
`μ₀` → `m₀`. Concretely: at `zDigits = 4`, `μ₀ = 49 152`, `LIFT_COLS = 49 172`,
table entries `= 50 352 128 ≤ 2^26`, so **`m₀` would be 26, not 27** — halving
every count in § Cost model. That resolution is not available in this
formalization: `hqz : q ≤ b ^ zDigits` is discharged by `Nat.le_pow_clog`
(`Correctness.lean:510-516`) and is *false* at `(16, 4)` since `16^4 = 65 536 ≪ q`.
So this brief is computed at `zDigits = 8`, `m₀ = 27`, and the one-line
consequence is: **if the contest resolves by moving `zDigits` rather than by
scoping `τ` to `BETA_SQ` alone, `m₀` must be re-derived and every number below
halves.** Nothing else in the link touches it.

## Semantics risks

### The CMvPolynomial gap is a semantics risk before it is a performance one

`STAGE2_SCOPING.md` § "Erasure catalogue" records this as the one no-precedent
shape, "here in force", and that is confirmed: `CMvPolynomial n F` is reached
verbatim by `computableRoundPoly`'s argument (`RoundPoly.lean:286`),
`honestComputeG`'s two `sumcheckPoly*` calls (`Completeness.lean:79-86`), and both
of `finalCheck`'s eval subterms (`FinalEval.lean:101-104`). Nothing in
`hachi/src` or in `cpoly/src` carries a tree map or a sparse monomial dictionary,
and Stage 2's judgement that `Std.ExtTreeMap` is "almost certainly above the
Aeneas ceiling" stands unchallenged by anything found here.

The reason it is a *semantics* risk and not merely a slow path: the naive form
does not compute a wrong answer, it fails to terminate at any usable scale
(§ Cost model, and Correction 2 above), so a semantics test written against it
cannot be made to pass. There is therefore **no honest naive-grade translation of
this target**. This is the sense in which Stage 2's "Stage 3 prerequisite, not a
Stage 6 option" is exact: the dense rewrite is not an optimization of a working
translation, it is a precondition for having one. The `op-genesis` "verbatim
freeze + birth bench case" step has to be taken against the dense form.

Mitigating, and it is the whole reason the rewrite is tractable: **every runtime
use of a `CMvPolynomial` in this link is an *evaluation*, and the factoring
lemmas are already proved at the pin** — `eval_sumcheckPolyZero`
(`Constraints.lean:1414-1419`), `eval_sumcheckPolyAlpha` (`:1426-1431`),
`cMultilinearExtension_eval` (`:973-977`), `cRangeProduct_eval` (`:994-997`),
`wTableMleEval_eq` (`:354-358`), `computableRoundPoly_eval`
(`RoundPoly.lean:356-360`). So the type can be removed rather than modelled.

### Value ranges and overflow headroom

All coefficient arithmetic in this target is `Ext4`, and every `Ext4` operation
is `cpoly`'s, whose headroom argument is already discharged there:
`Fp::mul` is `Fp((self.0 * rhs.0) % P)` and is sound because
`(P-1)^2 < 2^64` with `P < 2^32` (`cpoly/src/field.rs`, `impl Mul for Fp`);
`Ext4::mul` is the schoolbook `t0..t6` with the `Y^4 = W` fold
(`cpoly/src/field.rs:306-330`), so every intermediate is an `Fp` and inherits the
same bound. **Reusing that layer rather than reimplementing is the hard rule**
(`hachi/src/lib.rs:47-52`), and here it is also the entire overflow story: no new
width appears. Written out: one `Ext4` product is 19 `Fp` multiplications
(16 schoolbook `tᵏ` terms plus the three `W * t₄₋₆` folds) and 9 `Fp` additions,
each of which stays below `2^64` by the `Fp` bound.

Two places where an integer *not* in `Ext4` appears, and both need the
`params.rs` literal discipline:

* the cube sizes. `two_pow(m₀ - i - 1)` at `m₀ = 27` is `2^26`, and a
  `usize` index into a table of `2^27` `Ext4` is fine on 64-bit; but the
  *literal* discipline applies — `M0` must be the literal `27`, never
  `1 << M0_LOG` or `ML_VARS_LOW + 17`, for the reason `RING_DEGREE` is the
  literal `1024` (`params.rs:80-88`): Aeneas models a shift or a `const`
  subtraction as fallible, and every Lean use would bind and discharge a
  `Result`. Likewise `roundDegZero` must not be written `2 * GADGET_BASE`.
* `bound ≤ stmt.zc.rlin.bound` in `finalCheck`'s third conjunct
  (`FinalEval.lean:106`) is a `ℕ` comparison of two `R^lin` bound parameters, i.e.
  `CHAIN_GAMMA = 15` against a statement field. `u64` compare, no arithmetic, no
  headroom question. Note it is *carried by the input relation*, not assumed
  (`finalCheck_honestComputeY`'s docstring, `FinalEval.lean:394-402`).

### Partiality

* **`Nat` subtraction with a guard order that must be preserved.** `wTable`
  (`Constraints.lean:145-150`) computes `idx / d - μ` only under `¬ (idx / d < μ)`,
  and then `(idx / d - μ) / δρ` and `(idx / d - μ) % δρ` under
  `idx / d - μ < n * δρ`. Two levels, in that order — Stage 2 § "Scale/overflow
  hazards" item (a), confirmed. Reordering the branches in Rust changes the
  extracted model's `Usize` subtraction obligations from trivially-true to
  false.
* **`m₀ - i - 1` in the outer sum's arity** (`RoundPoly.lean:288`,
  `M + 1 - ((i : ℕ) + 1)`). Total in Lean only because the whole layer is stated
  at arity `M + 1` and `i : Fin (M + 1)`; that framing is deliberate
  (`RoundPoly.lean:110-115`). In Rust the loop bound is `M0 - i - 1` under
  `i < M0`, which is a stated precondition, not an inferable fact.
* **`Fin i → F` prefix and `Fin.snoc`.** `Fin.snoc` is total; the risk is the
  *representation* choice: a `Vec<Ext4>` whose length is `i` is an invariant
  Aeneas cannot see (no privacy boundary), so it travels as a hypothesis on each
  `_spec` in the `Wf` style of `hachi/lean/Ring.lean`.
* **No division and no well-founded recursion** anywhere in the seven items —
  `roundsChainAux`/`roundsReductionAux` are structural on `count`, and they are
  scaffolding. This is the one partiality box the target leaves empty.

### Exactness traps

* **`==` on `F`.** `roundCheck` and `finalCheck` branch on field equality
  (`Rounds.lean:103-104`, `FinalEval.lean:101-105`) and the passing case unpacks
  by `beq_iff_eq`, i.e. needs `LawfulBEq F`. In Rust that must be *one* notion of
  equality per type, as `Rq::equals` already enforces by comparing through
  `Fp::to_u64` (`hachi/src/ring.rs:157`); the `Ext4` `PartialEq` is derived
  (`cpoly/src/field.rs:184`) and is the one to use. The `LawfulBEq (Ext P)`
  instance is Stage 2's TE work-list item 1, a verified one-liner.
* **`eval 0` and `eval 1` are not general evaluations.** With
  `CPolynomial.eval x p = Σ aᵢ xⁱ` (`Basic.lean:246`), `eval 0 = a₀` (since
  `0^0 = 1`) and `eval 1 = Σ aᵢ`. A translation that calls a general `eval`
  at `0` and `1` is correct but pays `2·(2b+1)` powers for what is one array read
  and one array sum. Cheap either way (the verifier side), but the *spec* must be
  stated against `eval`, so the fast form is an `opt_eq_spec` obligation, not a
  free rewrite.
* **The two load-bearing side conditions.** `i < m₀` and `0 < b` carry both the
  round's soundness (`round_coordinateWiseSpecialSoundWithEscape`'s docstring,
  `Rounds.lean:239-249`) and its typing. `i < m₀` is real: at `m₀ ≤ i` the sum has
  saturated (`hypercubeSum_of_le`, `Constraints.lean:915`) and the guard yields
  `2·hypercubeSum = target`, false over any `F` of characteristic `≠ 2`. `0 < b` is
  real: at `b = 0` the range factor is `P₀(v) = v` of degree 1, overflowing
  `roundDegZero 0 = 0`. Both are `const`-true at Fig. 9 (`27` rounds, `b = 16`),
  so a corpus that never approaches them tests nothing — the loop must be
  exercised at `i = m₀ - 1` (the last round, where the outer sum is a single
  term) and the `b = 1` boundary should appear in a semantics test.
* **Degree-bound subtype erasure.** `RoundMsg`'s two `degreeLE` components
  (`Rounds.lean:65-67`) erase to unconstrained coefficient vectors. Stage 2
  § "API mapping" confirmations already record that `ShortChallenge`/`RoundMsg`
  degree bounds "are subtype erasures needing runtime checks or stated
  preconditions"; for the *honest* prover the bound is a theorem
  (`computableRoundPoly_sumcheckPolyZero_mem_degreeLE`, `RoundPoly.lean:406`), so
  a stated precondition suffices on the prover side. On the **verifier** side it
  is not: `roundCheck`/`roundOut` consume a message from the wire, and a
  degree-`33` `g⁰` would break the soundness argument's
  `Polynomial.eq_of_natDegree_lt_card_of_eval_eq` step (`Rounds.lean:283`,
  `:291`). So the Rust verifier needs an explicit `g.len() <= 2*B + 1` check.
  This is the same shape as `relOut`'s deliberately-absent challenge-norm check
  that Stage 2 flagged for the challenge stream.
* **`decide (bound ≤ …)` is a third conjunct, not two.** Confirmed
  (`FinalEval.lean:106`), and it is the one conjunct with no polynomial in it —
  easy to drop by inattention when transcribing.

### One risk that is proof-side, not translation-side

`roundsReduction_perfectCompleteness` and `sumcheckReduction_perfectCompleteness`
go through the still-`sorry` `Reduction.append_completeness` and therefore depend
on `sorryAx` (`Sumcheck/Basic.lean:95-102`, `Completeness.lean:37-46`). The
*per-round* result `roundReduction_perfectCompleteness` is axiom-clean, as is
`finalEvalReduction_perfectCompleteness` (`FinalEval.lean:403`). Consequence for
this target: equivalence specs should be stated per link (round `i`, final eval)
against the axiom-clean statements, and never against the folded ones, or the
`Check.lean` axiom audit will report `sorryAx` inherited from ArkLib's framework
rather than from anything in `hachi`.

## Cost model

Unit throughout: one **`Ext4` multiplication = 19 `Fp` multiplications + 9 `Fp`
additions** (`cpoly/src/field.rs:306-330`, counted above). `Ext4` addition is 4
`Fp` additions. Ring multiplications (`ring::mul`) do **not** appear in this
target at all — this is the first target whose cost is not `ring::mul` in a loop,
which matters for every policy note below.

### The naive form: two independent walls, both unpassable

1. **Constructing `H`.** `cMultilinearExtension m₀ (wTable …)`
   (`Constraints.lean:835-837`) is a `2^{m₀}`-term sum whose terms are
   `m₀`-factor `CMvPolynomial` products (`cBooleanEqPolynomial`, `:830-832`), and
   `CMvPolynomial` multiplication is the `|p₁|·|p₂|` tree-map double fold
   (`CompPoly/Multivariate/Unlawful.lean:188-191`). At `m₀ = 27` that is
   `2^27 = 134 217 728` terms × `27` products over maps growing to `2^27`
   monomials. `cRangeProduct` (`:845-847`) then multiplies `2b - 1 = 31` further
   times, at which point the operand carries up to `(2b+1)^{m₀} = 33^27 ≈
   1.0·10^41` monomials of `Vector ℕ 27` keys.
2. **Evaluating it.** `computableRoundPoly`'s outer sum is `2^{m₀-i-1}` terms
   (`RoundPoly.lean:288`) — `2^26 = 67 108 864` in round 0 — and each term is one
   `CMvPolynomial.eval₂` fold over all of `H`'s monomials
   (`CompPoly/Multivariate/CMvPolynomial.lean:133-135`), each monomial costing
   `m₀` `CPolynomial` powers (`CMvMonomial.lean:204-205`), of which one is an
   `X^e` array shift (`Raw/Ops.lean:95`) and `m₀ - 1` are constant powers.

Wall 1 alone settles it, and it settles it before the loop starts. `33^27`
monomials at 27 × 8 bytes of key alone is `10^43` bytes. Per Correction 2, this
is unconditional at `b = 16`: even `m₀ = 5` gives `3.9·10^7` monomials, `m₀ = 8`
gives `1.4·10^12`. **The naive form is excluded outright, and the removal
condition is `m₀`'s cube size, not the `ring::mul` champion** — no multiplication
speedup, ring or field, moves either wall.

### The dense form: the real cost model, and the dominant term

Take the value-level route (§ Strategy candidates S1–S3): per round `i`, hold the
folded `w̃` table `W_i` of `2^{m₀-i}` `Ext4`, the folded `eq̃`-suffix table of
`2^{m₀-i-1}`, and the folded `Ã` table; produce the `2b+1 = 33` values of
`g_i^{(0)}` and the `3` values of `g_i^{(α)}`, then interpolate.

Per round `i`, per remaining-cube point `y` (there are `2^{m₀-i-1}`):

| Work | `Ext4` mults |
|---|---|
| `W_i(T, y)` for the 33 nodes `T`, each `(1-T)·lo + T·hi` | 33 (one per node; `lo`,`hi` read once) |
| `rangeProduct b (·)` at each node — `2b - 1 = 31` factors (`Constraints.lean:96`) | 33 × 31 = 1023 |
| multiply by `eq̃`-suffix and accumulate | 33 |
| the `α` summand: `W_i(T,y) · Ã_i(T,y)` at 3 nodes | 3 |
| **subtotal** | **≈ 1092, dominated by the `1023`** |

Summed over the loop, `Σ_{i<m₀} 2^{m₀-i-1} = 2^{m₀} - 1`, so the whole prover is

    ≈ (2^{m₀} - 1) · (2b+1)(2b-1)
      = 134 217 727 · 33 · 31
      ≈ 1.37 · 10^11 Ext4 multiplications
      ≈ 2.6  · 10^12 Fp multiplications.

**The dominant term is the range factor `P_b` evaluated at `2b+1` nodes over the
folded cube: `(2b+1)(2b-1) = 1023` of the ≈1092 `Ext4` mults per cube point,
i.e. 94%.** The `α` summand, at `roundDegAlpha = 2`, is 0.3% of it. Everything
else — the folds themselves (`2·2^{m₀-i}` per layer, `≈ 2^{m₀+1}` total),
the interpolations (`m₀ · 33²`), the verifier's `roundCheck`s — is below the
noise floor of that number.

First-principles floor: at `Fp::mul` = one `u64` multiply plus one `% P` with a
compile-time constant modulus (multiply-high/shift/subtract, call it ~5 cycles),
one `Ext4` mult is ~150 cycles ≈ 40 ns at 4 GHz, so `1.37·10^11` mults is
**≈ 5.5·10^3 s ≈ 1.5 hours single-threaded**, before any allocation cost. Per the
`rust-bench` discipline this is a floor from operation counts, not a predicted
runtime.

**External anchor, and it is unusually good here.** The paper's own prototype
(`logs/paper-impl/README.md`) measures, at exactly this parameter set (ℓ = 30,
`q = 2^32 - 99`, `α = 10`, `b = 16`, `δ = 8`, `m = r = 10`, `ω = 16`), a **Prove
of 360.4 s of which sumchecks are 272.7 s** (standard arm; 293–311 s on the
AVX-512 arm — "AVX-512 buys … nothing on Prove — the sumchecks are ark-ff
extension-field arithmetic"). Two comparability caveats, both in our
disfavour-by-a-factor: the reference runs at `τ = Z_DECOMP_DELTA = 4`
(`logs/paper-impl/README.md`, "Protocol-layer constants"), hence `μ₀ = 49 152`,
`LIFT_COLS·d = 50 352 128 ≤ 2^26`, i.e. **`m₀ = 26` — half our cube**; and its
field layer is ark-ff Montgomery, not `% P`. So 272.7 s is a *lower* bound on
what a good implementation of this step costs at Fig. 9, and my `1.5 h` floor is
~20× it at 2× the cube — consistent, and consistent in the direction that says
the gap is field-arithmetic and algorithmic, not a modelling error.

### Memory, which is the second wall

| Object | At Fig. 9 |
|---|---|
| round-0 fold table, `2^{m₀}` `Ext4` at 16 B | **2 048 MiB** |
| same, if `w̃`'s base-field origin is kept as `Fp` until layer 1 | 1 024 MiB |
| `Ã` fold table, same shape | another 2 048 MiB (unless S4 lands) |
| `LiftedWitness.z` alone, `μ₀ · d` `Fp` at 8 B (`Lift/Reduction.lean:82`) | **640 MiB** |
| reference implementation's measured peak RSS at ℓ = 30 | **~13 GiB**, "dominated by the folded-witness sumcheck tables" |

Stage 2's § "Scale/overflow hazards" item (b) says target 4's policy "must avoid
materializing [a `2^{m₀}` table] even in REDUCED cases". For target 5 the fold
table is *not* avoidable — folding is the algorithm — so the policy is different
in kind: the table is intrinsic, and its size is exactly why full-const is out.

### The transcription trap: `roundProver.output` triples the dominant cost

`roundProver` computes `computeG st.1 st.2` in `sendMessage`
(`Rounds.lean:175`) and then **twice more** in `output` (`:181-182`), once per
component. A literal 1:1 translation therefore runs the 94%-dominant computation
three times per round — a 3× regression built into the reference shape. The fix is
semantics-preserving and provable by `rfl`: `output`'s four fields are exactly
`roundOut stmt (computeG stmt wit) c`, so a `let`-bound message (or reuse of the
one already sent, which is in the prover state) is the same value. Flagging it
here because it is invisible unless the two definitions are read together.

### Verifier side

Cheap, and worth stating so it is not optimized by mistake. `roundCheck` is
4 evaluations at `0`/`1` — degenerating to one coefficient read and one
coefficient sum each (§ Semantics risks) — so ≈ `4·(2b+1) = 132` `Ext4`
additions per round, 27 rounds. `roundOut` is 2 general evaluations of degree
32 and 2. `finalCheck` is `rangeProduct` (31 mults) plus **two `2^{m₀}`-sized
polynomial evaluations** (`FinalEval.lean:101-104`): `cEqualityPolynomial.eval a`
and `cMultilinearExtension (alphaPublicEvals …).eval a`. Those two are the whole
verifier cost, they are both dense-rewrite obligations of their own (S3, S4), and
after S3/S4 the verifier is `O(m₀)` plus one `2^{m₀-log₂ d}`-entry row fold — the
`Õ(√(2^ℓ)·λ)` claim of §4.4 (`Constraints.lean:1425`) in a shape we can actually
translate.

### REDUCED sizing, and the bench cases

Dense-form prover cost `(2^{m₀} - 1)·1023` `Ext4` mults, at `b = 16` (so the
degree, and hence the operation *shape*, is the real one):

| `m₀` | `Ext4` mults | floor @40 ns | verdict |
|---|---|---|---|
| 8 | 2.6·10^5 | ~10 ms | good criterion size |
| 10 | 1.0·10^6 | ~42 ms | **recommended REDUCED point** |
| 12 | 4.2·10^6 | ~170 ms | fine |
| 14 | 1.7·10^7 | ~0.7 s | upper end |
| 16 | 6.7·10^7 | ~2.7 s | too slow for criterion defaults |
| 27 | 1.4·10^11 | ~1.5 h | full const — impossible |

Proposed cases, all `sumcheck/<op>` (the group name the harness thinks in), all
**REDUCED**, per `STAGE2_SCOPING.md` § "Scale policies" row 5:

* `sumcheck/round_polys` — one round's `honestComputeG` at `m₀ = 10`, `i = 0`
  (the largest round). The birth case, and the one the ledger will steer on.
* `sumcheck/round_check` — `roundCheck` at real `b = 16`; cheap, real consts.
* `sumcheck/round_out` — `roundOut`; cheap, real consts.
* `sumcheck/final_check` — `finalCheck` at `m₀ = 10`; REDUCED because of the two
  cube-sized evaluations.
* `sumcheck/w_table_mle_eval` — `honestComputeY` at `m₀ = 10`; REDUCED, same
  reason. (If target 4 also benches `wTableMleEval`, one owner, not two.)
* `sumcheck/round_loop` — the `m₀`-round loop end to end at `m₀ = 10`; this is
  the case that catches a per-round allocation regression the single-round case
  hides.
* full-const variants: `#[ignore]`d, carrying the "full-const scale" form.

**The policy note every one of these cases must carry, in these words or
equivalent:** *REDUCED because `m₀ = 27` at [NOZ26] Fig. 9 makes any cube-shaped
object `2^{27} ≈ 1.3·10^8` entries — a materialized `Ext4` table is ~2 GiB and the
prover is ~1.4·10^11 `Ext4` multiplications. The removal condition is `m₀`'s cube
size, **not** the `ring::mul` champion: this operation performs no ring
multiplications at all, so no multiplication speedup — ring or field — changes
it.* And separately, for the naive `CMvPolynomial` form: *excluded outright, not
reduced; at `b = 16` there is no `m₀ ≥ 5` at which it runs, so there is no
REDUCED point to shrink to.*

### What allocates

* `computableRoundPoly`'s `+` in `CPolynomial`: `Raw.add` pads both operands and
  `zipWith`s, then `trim` (`Raw/Ops.lean:55,61`) — a fresh array per outer-sum
  term. `2^{m₀-i-1}` allocations per round in the naive shape; zero in the dense
  shape (accumulate into 33 scalars).
* `cpoly::multilinear::eval_mle_layer` builds its output with `Vec::new()` +
  `push` (`cpoly/src/multilinear.rs:280-296`) — no `with_capacity`. At `2^26`
  pushes that is ~26 reallocations and a 2× peak; `opt-inplace-buffers` territory,
  but note it is *`cpoly`'s* code, so a change there is a dependency change, not a
  `hachi/src` edit. The `hachi/src/sumcheck.rs` fold can pre-size its own buffers.
* `Fin.snoc` on the challenge prefix → one `push` per round on a `Vec` pre-sized
  to `M0`; negligible.
* `rangeProduct`'s `Finset.prod` over `Icc 1 (b-1)` is scalar; no allocation.

## Strategy candidates

Ordered by the size of the wall each removes. S1–S3 are prerequisites, not
optimizations — nothing runs without them.

* **S1 — `opt-algo-swap`: replace `computableRoundPoly` by the folded-table
  value form.** Compute the `2b+1` values `g_i^{(0)}(T) = Σ_y eq̃-suffix(y) ·
  P_b(W_i(T,y))` from a folded `w̃` table, then interpolate. Justified by
  `computableRoundPoly_eval` (`RoundPoly.lean:356`) + `eval_sumcheckPolyZero`
  (`Constraints.lean:1414`) + `hypercubeSum` (`:899`), so the identity is between
  *values*; the polynomial-level `opt_eq_spec` closes by
  `Polynomial.eq_of_natDegree_lt_card_of_eval_eq` against
  `computableRoundPoly_mem_degreeLE` (`RoundPoly.lean:366`) and Mathlib's
  `Lagrange.degree_interpolate_lt` (`Mathlib/LinearAlgebra/Lagrange.lean:336`) —
  **the same proof pattern already used at `Rounds.lean:283-293`**. The
  interpolation is computable and proved: `CPolynomial` `interpolateArray` /
  `eval_interpolateArray_at_index`
  (`CompPoly/Univariate/LagrangeArray.lean:48,79`). The fold step is
  `evalMleLayer` (`CompPoly/Multilinear/Basic.lean:475`) with `evalMle_succ`
  (`:512`) as its recursion lemma, and the orientation is already right:
  `evalMleStep` pairs `values[2j]`/`values[2j+1]` (`:467-471`), i.e. eliminates
  the low bit, which under little-endian `finFunctionFinEquiv`
  (`Mathlib/Algebra/BigOperators/Fin.lean:610`) is coordinate `0` — exactly the
  coordinate `hypercubePoint` frees first (`Constraints.lean:865-866`).
* **S2 — `opt-algo-swap`: the same for `wTableMleEval`/`honestComputeY`.**
  `CMlPolynomialEval.eval` materializes a `2^{m₀}` Lagrange table
  (`CompPoly/Multilinear/Basic.lean:524`, `:410`); `evalMle` (`:499`) does it in
  halving layers with no full table. And once S1 holds the folded table `W_{m₀}`
  *is* `mle[w̃](a)`, so `honestComputeY` is free — a shared-subexpression win
  across the link, not a separate computation.
* **S3 — `opt-algo-swap`: closed-form `eq̃` for `finalCheck`'s first factor.**
  `(cEqualityPolynomial m₀ τ₀).eval a` is a `2^{m₀}` sum as written
  (`FinalEval.lean:101` → `Constraints.lean:840` → `:835`), but it is
  `eq̃(τ₀, a) = ∏ᵢ ((1-τ₀ᵢ)(1-aᵢ) + τ₀ᵢaᵢ)`, i.e. `m₀ = 27` multiplications. The
  lemma chain is short and every link exists: `cMultilinearExtension_eval`
  (`Constraints.lean:973`) to Mathlib's `MLE`, `eval_eqPolynomial_boolean`
  (`:938`) to recognize the table as `eq̃(x,τ₀)`, `eqPolynomial_symm`
  (`Data/MvPolynomial/Multilinear.lean:97`), `eqPolynomial_mem_restrictDegree`
  (`:184`) with `MLEEquiv` (`:307`) to collapse `MLE` of a multilinear function,
  and `eqPolynomial_expanded` (`:94`) for the product form.
* **S4 — `opt-algo-swap`: tensor-split `Ã`, the verifier's expensive step.**
  `alphaPublicEvals x = alphaTilde α (idx % d) · Σᵢ eq̃(τ₁,i)·M̃_α(i, idx / d)`
  (`Constraints.lean:853-862`) is a product of a function of the *low* `log₂ d =
  10` index bits and a function of the *high* `m₀ - 10 = 17` bits, and the split
  is exactly `wTableIndex_div_mod` (`:1207`). So its MLE factorizes: the column
  factor `MLE(α^ℓ)(a_low) = ∏_{j<10} ((1-a_j) + a_j·α^{2^j})` is 10 mults (a
  geometric-sequence MLE), and the row factor is a `2^{17} = 131 072`-entry fold
  instead of `2^{27}`. That is a **1024× reduction** on the verifier's dominant
  term and is the concrete content of the `Õ(√(2^ℓ)·λ)` dynamic-programming
  remark at `:1425`. `α^{2^j}` needs an `Ext4` power loop — Stage 2's
  § "Minor variants" already lists one for `alphaTilde`.
* **S5 — `opt-algo-swap`: `P_b` via `v²`.** `rangeProduct b v = v·∏_{j=1}^{b-1}
  ((v-j)(v+j)) = v·∏_{j=1}^{b-1}(v² - j²)` (`Constraints.lean:96-97`). One
  squaring plus `b-1 = 15` multiplications = 16, against the literal form's
  `2(b-1) + 1 = 31`. A **2× cut on the 94%-dominant term** — the single largest
  win available after S1. The `j²` constants are compile-time (`params.rs`
  literal discipline, one `const` array or a `while`-computed table). `opt_eq_spec`
  is `ring`-level algebra over `Finset.prod`.
* **S6 — `opt-inplace-buffers`: hoist the triple `computeG`.** `roundProver.output`
  recomputes the round message twice (`Rounds.lean:181-182`); a `let`-bound
  message makes `output = roundOut stmt g c`, provable by `rfl`. 3× → 1× on the
  dominant term. Also: pre-size every fold buffer to `2^{m₀-i-1}` rather than
  growing it (`cpoly`'s `eval_mle_layer` grows, `cpoly/src/multilinear.rs:283`),
  and fuse the "fold `W`" and "evaluate the 33 nodes" passes so the folded table
  is read once.
* **S7 — `opt-word-arith`: keep layer 0 in the base field.** `w̃`'s entries are
  `φF`-images of `ZMod q` coefficients (`Constraints.lean:146,148`), i.e. `Ext4`
  with `c1 = c2 = c3 = 0`. `Ext4 × Ext4::from_base` is 4 `Fp` mults, not 19, and
  the layer-0 table is `2^{m₀}` entries — the largest one. ~5× on the biggest
  fold layer and a 2× cut on peak memory (`Fp` at 8 B vs `Ext4` at 16 B). The
  headroom argument is `cpoly`'s, unchanged.
* **S8 — `opt-list-to-array`: the `Fin`-function and `Finset.sum` shapes.**
  `∑ y : Fin k → Fin 2` (`RoundPoly.lean:288`), `∏ j ∈ Icc 1 (b-1)`
  (`Constraints.lean:97`), `Vector.ofFn` in `cWTableMle` (`:343`) and
  `Fin.append`/`Fin.cast` in `roundAssignment` (`RoundPoly.lean:268`) all become
  flat-indexed `Vec` loops. Precedent: `evalsplit.rs`'s `two_pow`/`test_bit`
  counter loops (`hachi/src/evalsplit.rs:89,104`) — and note Stage 2's
  observation that `finFunctionFinEquiv` cancels against `.symm`, so *no bit
  machinery survives* and `test_bit` may not even be needed for the fold (only
  for `wTable`'s index split, which is `/` and `%`).
* **S9 — `opt-tailrec-loops`: the round loop.** `roundsReductionAux`/`roundsChainAux`
  are structural recursions on `count` (`Completeness.lean:349`,
  `Rounds.lean:367`); the computational residue is a `while i < M0` accumulator
  over a mutable statement struct. Low value (27 iterations), listed because the
  loop shape is what the Lean loop invariants are written about.
* **S10 — one free node from the round check `(no skill yet)`.** `roundCheck`
  asserts `g(0) + g(1) = target` (`Rounds.lean:103`), so the prover can compute
  `2b` of the `2b+1` values and solve for the last. ~3% of the dominant term;
  named because it is the standard sumcheck-prover trick and costs nothing but a
  lemma, and because no `opt-*` skill covers "derive one value from the
  verifier's own identity".

**Explicitly not applicable:** anything about `ring::mul` or the NTT
(`CyclotomicRing/Core/Basic.lean:72`'s `TODO add proper NTT multiplication here`,
and `hachi/src/ring.rs` § "What is deliberately not here"). This target performs
no `Rq` multiplications; its arithmetic is `Ext4`. Keeping the two straight is the
whole point of repeating the removal condition in every policy note.

## Representation

**Rust home:** a new `hachi/src/sumcheck.rs`, added to `lib.rs`'s strict bottom-up
layering (`hachi/src/lib.rs:43-45`) *above* `evalsplit` — it uses `ring`,
`linalg` and the `cpoly` field layer, and nothing reaches back up. Stage 2
§ "API mapping" already proposed the module and its four entry points
(`round_polys`, `round_check`, `round_out`, `final_check`); add `honest_compute_y`
and `round_loop` per § A above.

**The field layer is `cpoly`'s, and this is the first `hachi` module whose
coefficient type is `Ext4` rather than `Fp`.** `Ext4` is a four-named-field
`Copy` struct (`cpoly/src/field.rs:185-195`) chosen precisely so "every extension
operation [is] straight-line in the extracted model: no bounds checks, no loops".
Stage 2's Decision-3 audit records that the Rust `Ext4` carrier already extracts
(Workstream 0 probe) and that the remaining work is the
extracted-`cpoly`-`Ext4` ↔ CompPoly-`Ext4` bridge (TE item 8), i.e. proof work,
not extraction risk. **Reusing it rather than reimplementing is a hard project
rule** (`hachi/src/lib.rs:47-52`).

**And `cpoly` already ships, in extraction-clean Rust, most of what the dense
form needs** — this is the "positive the plan undersells" (Stage 2 § "Erasure
catalogue"), and it is true on the Rust side too, not only in Lean:

| Needed | Already in `cpoly` | Mirrors |
|---|---|---|
| the fold step | `eval_mle_layer` (`cpoly/src/multilinear.rs:280`) | `CMlPolynomialEval.evalMleLayer` (`CompPoly/Multilinear/Basic.lean:475`) |
| `eq̃`-suffix table | `lagrange_basis` (`multilinear.rs:169`) | `lagrangeBasis` (`:410`) |
| `eq̃` at a point | `eq_tilde` (`multilinear.rs:248`) | `eqTilde` (`:531`) |
| the cube-sized dot product | `dot` (`multilinear.rs:123`) | `Vector.dotProduct` |
| the hypercube-table carrier | `MultilinearEvals(Vec<Ext4>)` (`multilinear.rs:487`) | `CMlPolynomialEval R n = Vector R (2^n)` (`:47`) |

So the new code in `hachi/src/sumcheck.rs` is: the two summands' value form, the
`33`-node interpolation, `wTable`'s index split, `rangeProduct`, the two checks,
the statement advance, and the loop. Nothing else.

**Proposed carriers**, following the reasoning pattern of the existing ones
(`hachi/src/lib.rs`, `hachi/src/evalsplit.rs:114-130`): small fixed dimension →
named-fields struct so the extracted model is straight-line; dynamic length →
`Vec` newtype whose constructor establishes the shape invariant, which must also
travel as a hypothesis on each `_spec` because Aeneas cannot see a Rust privacy
boundary (`Wf` in `hachi/lean/Ring.lean`).

* `UniPoly(Vec<Ext4>)` — the round-message polynomial, coefficients low-to-high,
  length `≤ 2*B_ZERO + 1` by construction. Mirrors `CPolynomial F`
  (`CompPoly/Univariate/Basic.lean:58`, an `Array` subtype). One `Vec` newtype,
  two constructors (`from_values` after interpolation, `from_coeffs`), and the
  degree bound as the shape invariant. Note `CPolynomial`'s invariant is
  *canonicity* (no trailing zeros, `Trim`), which is a second invariant to state
  and the reason `Rq` could get away with a plain fixed length and this cannot.
* `RoundMsg { g_zero: UniPoly, g_alpha: UniPoly }` — a two-field struct, since
  `RoundMsg F b` is a pair (`Sumcheck/Rounds.lean:65-67`). The two `degreeLE`
  subtypes erase; the bounds become `UniPoly`'s invariant on the prover side and
  an explicit length check on the verifier side (§ Semantics risks).
* `RoundStatement { zc: NestedZeroCheckStmt, challenges: Vec<Ext4>, target_zero:
  Ext4, target_alpha: Ext4 }` — mirrors `NestedRoundStatement`
  (`ZeroCheck/Constraints.lean:1453-1462`). The `i`-indexing of `challenges :
  Fin i → F` erases to the `Vec`'s length, which travels as `challenges.len() ==
  i` on each `_spec`. One struct for all rounds, not a family.
* `MleTable(Vec<Ext4>)` — the folded `w̃` table. Could be `cpoly`'s
  `MultilinearEvals` directly (`cpoly/src/multilinear.rs:487`); prefer that, per
  the reuse rule, and add only what is missing.
* `LiftedWit { z: PolyVec, rho: Vec<Rq> }` — mirrors `LiftedWitness`
  (`ProofSystem/RingSwitching/Lift/Reduction.lean:80-86`): `z : Fin μ → S` at
  `μ = μ₀ = 81 920`, `ρ : Fin n → CPolynomial R` at `n = n₀ = 5` with the
  degree-`≤ d-1` bound. The `hρ` field is a `Prop` and erases; the bound becomes
  `rho[i].len() <= RING_DEGREE` as a construction invariant plus a `_spec`
  hypothesis. This carrier is shared with targets 3 and 4 and should be owned by
  whichever lands first — it is `640 MiB` at Fig. 9 for `z` alone, which is by
  itself a reason the semantics tests are REDUCED.
* `WEvalStatement { t: TCom, point: Vec<Ext4>, value: Ext4 }` — mirrors
  `WEvalStatement` (`Sumcheck/FinalEval.lean:72-78`), the link's output.

**New `params.rs` consts this target needs** (all from Stage 2's audited table,
all as literals per the extraction-concession discipline of `params.rs:80-88`):
`M_ZERO = 27`, `M_ONE = 3`, `B_ZERO = 16`, `CHAIN_GAMMA = 15`,
`RLIN_COLS = 81920`, `RLIN_ROWS = 5`, `RHO_DIGIT_COUNT = 8`, `Z_DIGITS = 8`,
plus the round degrees. Two literal-collision hazards from Stage 2 § F3 bite
here specifically: value **16** is now five names (`GADGET_BASE`, `GAMMA`,
`B_ZERO`, `OMEGA`, `CHALLENGE_WEIGHT`) and the sumcheck reads `B_ZERO`; value
**15** is `CHAIN_GAMMA` *and* the honest unsigned digit ceiling `b - 1`, and the
sumcheck's `bound` slot is `CHAIN_GAMMA` (`Composition.lean:326`,
`Correctness.lean:254`). `roundDegZero b = 32` is a sixth name for a sixth
value but collides with nothing. Proof discipline, per Stage 2: **rewrite
hypotheses, never goals.**

**Spec-statement notes.** State against `wTableMleEval` rather than
`honestComputeY` (Decision 3, to avoid the accidental `SampleableType`); state
per-link against the axiom-clean `roundReduction_perfectCompleteness` /
`finalEvalReduction_perfectCompleteness` rather than the folded statements
(§ Semantics risks, last item); and state the round-polynomial spec against
`computableRoundPoly_eval` and `computableRoundPoly_mem_degreeLE`
(`RoundPoly.lean:356,366`) — the two facts the round check and the round output
map are the *only* consumers of (`:353-355`), so the `CPolynomial` identity
`computableRoundPoly_toPoly` never has to appear in a `hachi` spec at all.
