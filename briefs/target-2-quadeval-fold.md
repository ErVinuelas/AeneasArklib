# Brief: `ArkLib.Lattices.Hachi` QuadEval fold — `carrier*`/`jMatrix`/`zDecomp`/`tensorG*`/`honest*`/`relOut`       (ArkLib @ `294b3f0b0f46e1485c878a217e9de764855f5915`)

Stage 2 target 2 of `PLAN_PROTOCOL_LAYER.md`; scale policies and the audit
tables this brief consumes are `STAGE2_SCOPING.md` §§ "Erasure catalogue",
"Ordered target list + scale policies", "Parameter mapping", "API mapping from
HachiRuntime". Rev confirmed at `hachi/lake-manifest.json:8` and
`hachi/lakefile.lean:42`.

**Citation paths.** `H/…` = `hachi/.lake/packages/Arklib/ArkLib/Commitments/Functional/Hachi/…`;
`D/…` = `hachi/.lake/packages/Arklib/ArkLib/Data/Lattices/…`;
`A/…` = `hachi/.lake/packages/Arklib/ArkLib/Commitments/Ordinary/Ajtai/…`.
Everything else is a repo-relative path.

**Rust home:** a new `hachi/src/quadeval.rs`.

**The brief's one open parameter is `Z_DIGITS`** (ArkLib's `zDigits`, the
paper's τ). Every width below is written in terms of it; the two readings and
exactly what differs are in § Parameters. No numeric `BETA_SQ` is asserted
anywhere in this brief, and § Semantics risks records why that value is not on
this target's code path at all.

## Definition chain

Surface names, in dependency order, with the body each one really has after the
`PolyVec`/`Matrix`/`Finset.sum`/subtype layers.

**Shared substrate** (all four of these are already translated; the chain stops
at them):

* `PolyVec P k := Fin k → P`, `PolyMatrix P rows cols := Matrix (Fin rows) (Fin cols) P` — `D/Vectors.lean:45,48`.
* `dot u v = (List.ofFn fun i => u i * v i).sum` — `D/Vectors.lean:83-84`; `u ⬝ᵥ v` notation `:101`. Note the *List* sum (right-nested), which `hachi/src/linalg.rs:180-183` records as a left fold plus an associativity argument.
* `matVecMul A v = fun i => dot (A i) v` — `D/Vectors.lean:87-89`; `*ᵥ` `:100`. `scalarVecMul c v = fun i => c * v i` — `:97-98`; `•ᵥ` `:102`.
* `splitForm M u v = u ⬝ᵥ (M *ᵥ v)` — `D/Vectors.lean:197-198`.
* `PolyVec.flattenBlocks xs j = xs (finProdFinEquiv.symm j).1 …` — `D/Vectors.lean:55-57`; flat index is `e + width·i` (`H/Gadget/Core.lean:202`), i.e. plain concatenation (`hachi/src/linalg.rs:36-44`).
* `a * b : Rq Φ` → `Mul (Rq Φ)` (`D/CyclotomicRing/Rq.lean:110`) → `Rq.mk Φ (a.1 * b.1)` → `Φ.reduce = modByMonic Φ.φ` (`D/CyclotomicRing/Core/Basic.lean:67`); Rust `Rq::mul` folds the `X^N ≡ −1` sign into a schoolbook convolution (`hachi/src/ring.rs:274-312`).
* `Simple.commit Φ A s = A *ᵥ s` — `A/Simple/Scheme.lean:38-40`; `Simple.PublicParams rows cols` is just `PolyMatrix (Rq Φ) rows cols` (`:29`), `Commitment rows = PolyVec (Rq Φ) rows` (`:35`).
* `gadgetEntry base i j = if j/digits = i then constRq (base^(j%digits)) else 0` — `H/Gadget/Core.lean:175-176`; `gadgetMatrix base rows digits = fun i j => gadgetEntry …` — `:179-180`; `gadgetMul base v = gadgetMatrix … *ᵥ v` — `:183-185`.
* **`gadgetMul_apply`** — `H/Gadget/Core.lean:213-216`: `gadgetMul base v i = ∑ e : Fin digits, constRq (base^e) * v (finProdFinEquiv (i,e))`. This collapse is *load-bearing for feasibility*, not an optimization (see § Cost model), and it is already how `hachi/src/gadget.rs:168-184` is written.
* `gadgetDecompose dd x j = Rq.ofFinCoeff Φ Φ.φ.natDegree (fun k => dd.digit ((x …).1.coeff k) …)` — `H/Gadget/Core.lean:243-246`; `ofFinCoeff` `D/CyclotomicRing/Rq.lean:269`; lawfulness `gadgetDecompose_lawful` `H/Gadget/Core.lean:257-259`.
* `DigitDecomposition base digits` is a *structure* with fields `digit : R → Fin digits → R` and `reconstruct : ∀ c, ∑ e, base^e · digit c e = c` — `H/Gadget/Core.lean:95-99`. Its two `ZMod q` instances are `zmodDigitDecomposition b digits hb hq` (`:113-115`, unsigned digits of `c.val`) and `balancedZmodDigitDecomposition` (`:148-152`, target 1's), **both requiring `hq : q ≤ b ^ digits`**.

**The target proper.**

1. `carrierEntry Φ base a s = splitForm (gadgetMatrix Φ base messageRows messageDigits) a s` — `H/QuadEval/Gadgets.lean:81-83`. Unfolded: `dot a (G_{2^m,δ} *ᵥ s)`, `G` of shape `messageRows × (messageRows·messageDigits)`.
2. `carrier Φ base a s = fun i => carrierEntry Φ base a (s i)` — `H/QuadEval/Gadgets.lean:86-88`; result `PolyVec (Rq Φ) blocks`.
3. `carrierDecomp Φ ddCarrier a s = gadgetDecompose Φ ddCarrier (carrier Φ base a s)` — `H/QuadEval/Gadgets.lean:94-98`; width `blocks * messageDigits`. `base` is **implicit, pinned by `ddCarrier`** (`:93`). Roundtrip `carrier_eq_gadget` `:101-106`.
4. `carrierCommit Φ D ddCarrier a s = Simple.commit Φ D (carrierDecomp …)` — `H/QuadEval/Gadgets.lean:109-114`; `D : Simple.PublicParams Φ dRows (blocks * messageDigits)`, carried by `PublicParamsD` (`:66-70`), which `extends InnerOuter.PublicParams` (`H/InnerOuter/Scheme.lean:94-99`).
5. `jMatrix Φ base n zDigits = gadgetMatrix Φ base n zDigits` — `H/QuadEval/Gadgets.lean:125-126`. **It is literally the gadget matrix**, at `n = messageRows * messageDigits` and `digits := zDigits` (docstring `:122-123`, which is also where the string "`zDigits = τ`" comes from).
6. `zDecomp Φ ddZ z = gadgetDecompose Φ ddZ z` — `H/QuadEval/Gadgets.lean:132-134`; width `n * zDigits`. Roundtrip `z_eq_jMatrix` `:137-140`.
7. `tensorG Φ base k digits c x = ∑ i : Fin blocks, (c i) •ᵥ (gadgetMatrix Φ base k digits *ᵥ x i)` — `H/QuadEval/Gadgets.lean:151-153`. A `Finset.sum` **of vectors** (`Pi` addition), instantiated at `k = innerRows`, `digits = innerDigits` by c5.
8. `tensorG1 Φ base digits c x = dot c (gadgetMatrix Φ base blocks digits *ᵥ x)` — `H/QuadEval/Gadgets.lean:188-190`. A scalar; `x = ŵ` is the flat `blocks·digits` carrier decomposition.
9. `honestZ Φ wit c = ∑ i : Fin (2^r), (c i).val •ᵥ wit.message i` — `H/QuadEval/Reduction.lean:487-489`. `wit.message i : PolyVec (Rq Φ) (2^m * messageDigits)`, from `Decomp.message` (`H/InnerOuter/Scheme.lean:107`). `(c i).val = Subtype.val` (`H/QuadEval/Reduction.lean:166`). **Every `•ᵥ` entry here is a full ring product** (`D/Vectors.lean:97-98`), not a constant scaling.
10. `honestComputeV Φ pp ddCarrier stmt wit = Hachi.carrierCommit Φ pp.dMatrix ddCarrier stmt.avec wit.message` — `H/QuadEval/Reduction.lean:474-482`.
11. `honestComputeResp` — `H/QuadEval/Reduction.lean:494-503`: `carrierDec := carrierDecomp Φ ddCarrier stmt.avec wit.message`, `innerDec := wit.innerDecomp` (pass-through), `zDec := zDecomp Φ ddZ (honestZ Φ wit c)`.
12. `relOut Φ pp base ω γ` — `H/QuadEval/Reduction.lean:258-284`. A **`Set` of `Prop`s**, not a `Bool`. With `c := fun i => (chals i).val` and `z := jMatrix Φ base ((2^m)*messageDigits) zDigits *ᵥ resp.zDec` (`:266-268`):
    * c1 `Simple.commit Φ pp.dMatrix resp.carrierDec = v` (`:270`)
    * c2 `Simple.commit Φ pp.outerMatrix (flattenBlocks resp.innerDec) = stmt.u` (`:272`)
    * c3 `dot stmt.bvec (gadgetMatrix Φ base (2^r) messageDigits *ᵥ resp.carrierDec) = stmt.y` (`:274`)
    * c4 `tensorG1 Φ base messageDigits c resp.carrierDec = dot stmt.avec (gadgetMatrix Φ base (2^m) messageDigits *ᵥ z)` (`:276-277`)
    * c5 `tensorG Φ base innerRows innerDigits c resp.innerDec = pp.innerMatrix *ᵥ z` (`:279-280`)
    * c6 three `vecLInftyNorm … ≤ γ`, on `carrierDec`, `flattenBlocks innerDec`, `zDec` (`:282-284`).
    `vecLInftyNorm z = sup_i Rq.lInftyNorm (z i)`, `Rq.lInftyNorm a = sup over Finset.range Φ.φ.natDegree of (a.1.coeff k).valMinAbs.natAbs` — `D/CyclotomicRing/NormBounds/Basic.lean:125-126, 117-118`. **No challenge-norm check and no `‖z‖₂²` check** — deliberate, `H/QuadEval/Reduction.lean:149-152, 254-256`.
13. `InSb Φ β a = ∀ k, k < Φ.φ.natDegree → −((β/2 : ℕ) : ℤ) ≤ (a.1.coeff k).valMinAbs ∧ (a.1.coeff k).valMinAbs ≤ (((β+1)/2 : ℕ) : ℤ) − 1` — `H/QuadEval/Reduction.lean:297-300`; `vecInSb` `:303`; `paperRelOut` = `relOut` with c6 replaced by three `vecInSb` (`:335-357`); containment `paperRelOut_subset_relOut` under `b/2 ≤ γ` (`:367-376`), via `lInftyNorm_le_of_InSb` `:308-313`.
14. Adjacent, **not** in this target (relIn side, already covered by `commit::verify_weak`): `relIn` `H/QuadEval/Reduction.lean:382-388`, `evalConsistency` `:206-208`, `derivedMsgMatrix` `:200-202`, `dShort` `:212-213`, `quadEvalSISSet` `:224-232`. The protocol objects `verifier`/`prover`/`quadEvalReduction` (`:400-406, 426-459, 513-528`) are Stage 5's, not Stage 3's.

**How the composed chain instantiates all of it** (this is what fixes the
parameters below): `H/HonestChain.lean:349-351` appends
`quadEvalReduction (zDigits := zDigits) Φ pp (balancedZmodDigitDecomposition P.b messageDigits P.hb hqm) (balancedZmodDigitDecomposition P.b zDigits P.hb hqz)`,
under `hqm : q ≤ P.b ^ messageDigits` and `hqz : q ≤ P.b ^ zDigits`
(`:336`); `H/Correctness.lean:501-516` closes both with
`Nat.le_pow_clog P.hb q` at `zDigits := δ P` where `δ P := Nat.clog P.b q`
(`H/Correctness.lean:491`). So on the composed path **both** decompositions are
balanced (confirming `STAGE2_SCOPING.md` § Decision 4) and `zDigits` is `clog`.

## Parameters

Values from `hachi/src/params.rs`, with the pinned/chosen/derived split carried
as that file records it. `d := RING_DEGREE`, `δ := GADGET_DIGITS`,
`n := 2^m · δ = MESSAGE_ROWS · GADGET_DIGITS = 8192`, `Z := Z_DIGITS`.

| ArkLib | value here | provenance |
|---|---|---|
| `q` | `Q = 2^32 − 99` | **pinned** by cpoly's `Fp` (`params.rs:41-51`) |
| `α`, `deg φ = d` | `RING_LOG_DEGREE = 10`, `RING_DEGREE = 1024` | **pinned** by [NOZ26] Fig. 9 (`params.rs:66-88`); a literal, not `1 << α`, per the extraction concession at `:80-84` |
| `base = b` | `GADGET_BASE = 16` | **pinned** Fig. 9; spec side needs only `1 < b` (`params.rs:90-97`) |
| `messageDigits = innerDigits = δ` | `GADGET_DIGITS = 8` | **pinned** Fig. 9 **and forced** by `q ≤ b^digits` — `16^8 = 2^32 ≥ q`, `16^7 < q` (`params.rs:99-113`) |
| `messageRows = 2^m` | `MESSAGE_ROWS = 1024` | **pinned** Fig. 9; `PublicParams` is generic in all six shapes (`H/InnerOuter/Scheme.lean:94`) |
| `blocks = 2^r` | `BLOCKS = 1024` | **pinned** Fig. 9 (`params.rs:142-147`) |
| `innerRows = n_A`, `outerRows = n_B` | `INNER_ROWS = OUTER_ROWS = 1` | **pinned** Fig. 9 (`params.rs:126-140`) |
| `m`, `r` | `ML_VARS_HIGH = ML_VARS_LOW = 10` | **derived** from the consumer's shape (`params.rs:208-225`) |
| `κ = 2ω` | `KAPPA = 32` | **pinned** by ArkLib's weak-opening mapping (`params.rs:249-268`) ⇒ `ω = 16` |
| `γ` of `verify_weak` (γ̄ = b) | `GAMMA = 16` | **pinned** by the same mapping (`params.rs:150-166`) |
| `dRows = n_D` | `D_ROWS = 1` (new) | **chosen/paper-pinned**: `dRows` is a bare `Nat` on `PublicParamsD` (`H/QuadEval/Gadgets.lean:67,70`), spec-unconstrained; `STAGE2_SCOPING.md` § Parameter mapping |
| `blocks·messageDigits` (D's width) | `D_QUAD_COLS = 8192` (new) | **derived** from the two above (`H/QuadEval/Gadgets.lean:70`) |
| `ω` of `ShortChallenge` | `OMEGA = 16` (new) | **derived** from `KAPPA = 2ω`; retires `KAPPA`'s magic `2·16` (`STAGE2_SCOPING.md` § Parameter mapping, "Bonus win") |
| `γ` of `relOut` c6 | `CHAIN_GAMMA = 15` (new) | **derived**: on the composed path `P.γ = P.bZero − 1` at `ofPinnedDigitBase b` (`H/HonestChain.lean:165-175`), and `pinned_of_soundness_orientations` (`:188-193`) forces it |
| `zDigits = τ` | **`Z_DIGITS` — OPEN** | see below |
| `βSq` | **contested; not on this target's path** | `relOut` carries no `ℓ₂` check at all (`H/QuadEval/Reduction.lean:255`); βSq enters only `relIn` → `VerifiedOpening` (`:387`), i.e. the *existing* `commit::verify_weak` slot |

### ⚠ The single open parameter: `Z_DIGITS`

`Z` is the only parameter this target's shapes depend on that is not settled.
Written symbolically, the widths it drives are:

| object | width / shape | source |
|---|---|---|
| `zDecomp` output, `QuadEvalResponse.zDec` | `n · Z = 8192·Z` ring elements | `H/QuadEval/Gadgets.lean:133`; `H/QuadEval/Reduction.lean:105` |
| `jMatrix Φ base n Z` | `n × (n·Z)` = `8192 × 8192Z` | `H/QuadEval/Gadgets.lean:125` |
| `z = J *ᵥ ẑ` | `n = 8192` (independent of `Z`) | `H/QuadEval/Reduction.lean:267-268` |
| `rlinCZ` (target 3) | `2^m · δ · Z = 8192·Z` | `H/RingSwitch/Rlin.lean:166` |
| `rlinCols = μ₀` (target 3) | `2^r·δ + (2^r·(n_A·innerDigits) + 8192·Z)` = `16384 + 8192Z` | `H/RingSwitch/Rlin.lean:153` |

**Reading A — `Z = 8` (the composed chain).** `zDigits` is instantiated at
`δ P = Nat.clog P.b q` and `hqz : q ≤ P.b ^ zDigits` is discharged by
`Nat.le_pow_clog` (`H/HonestChain.lean:336, 350-351`; `H/Correctness.lean:511,
516`); at `b = 16` that is 8, the same minimality that pins `GADGET_DIGITS`.
Every one of the 16 `quadEvalBetaSq` instantiations in the tree passes
`zDigits` into the formal τ slot (`def quadEvalBetaSq (γ b τ d m δ : ℕ)`,
`H/QuadEval/Soundness.lean:106`; call sites `:355, 490, 557, 596, 628` and
`Composition.lean`), which is the evidence `STAGE2_SCOPING.md` § "Parameter
mapping" F2 and § "Cross-audit contradiction" rest on. Verified here: it holds
exactly as recorded.

**Reading B — `Z = 4` (the paper, the reference implementation, the user's
choice).** Fig. 9's τ = 4; the paper's own prototype names it
`Z_DECOMP_DELTA = 4` (`logs/paper-impl/README.md:48`); and ArkLib itself makes
the identification in the definition-site docstring, "in this reduction … and
`zDigits = τ`" (`H/QuadEval/Gadgets.lean:122-123`).

**What differs, exactly:**

1. **Constructibility of `ddZ`.** `DigitDecomposition` demands
   `reconstruct : ∀ c : R, ∑ e, base^e · digit c e = c` (`H/Gadget/Core.lean:95-99`),
   and both `ZMod q` instances require `hq : q ≤ b^digits`
   (`:113, 148`). At `(16, 4)`, `16^4 = 65536 ≪ q`, so **no ArkLib
   `DigitDecomposition (16 : ZMod q) 4` exists at this pin.** Consequence for
   this target: at `Z = 8` the z-side equivalence statement is the
   unconditional `z_decompose … = gadgetDecompose Φ ddZ z`; at `Z = 4` the Rust
   function is not the translation of any constructible `zDecomp` instance, and
   its spec must become conditional (a hypothesis of the shape "`z`'s
   coefficients are below `b^4`", true of honest already-short `z` and false in
   general) or be stated against a new local digit-decomposition definition.
   **This is a statement-shape change, not a constant change, and it is the
   costliest half of the choice.**
2. **The refactor.** `Z = 8 = GADGET_DIGITS` makes the J side pure reuse:
   `jMatrix` *is* `gadgetMatrix` and `zDecomp` *is* `gadgetDecompose`, so
   `hachi/src/gadget.rs`'s functions apply at their hardwired consts. At
   `Z = 4` they do not — see the audit-claim check in § Representation.
3. **Memory and time of the z side.** `ẑ` is `8192·Z` ring elements of `d` `Fp`
   = `8 KiB` each (`Fp := Std.U64`, `hachi/lean/Generated.lean:29`), so
   **512 MiB at `Z = 8`, 256 MiB at `Z = 4`**; `zDecomp`'s digit work is
   `n·d·Z(Z+1)/2` division steps (`digit_at` divides `e` times,
   `hachi/src/gadget.rs:68-77`) = `3.0·10^8` vs `8.4·10^7`; the J recompose
   inside `relOut` is `n·Z` scalar multiplies = 65536 vs 32768.
4. **Downstream parameters** (targets 3–5, stated in `STAGE2_SCOPING.md`
   § Parameter mapping at `Z = 8`): `RLIN_CZ` 65536 → 32768; `μ₀ = 16384 +
   8192Z` 81920 → 49152; `LIFT_COLS = μ₀ + n₀·δρ` (n₀ = `rlinRows 1 1 1` = 5,
   `H/RingSwitch/Rlin.lean:158`) 81960 → 49192; and hence
   **`M_ZERO` 27 → 26**, since `49192·1024 = 50 372 608 ∈ (2^25, 2^26]`. If
   `Z = 4` lands, those four rows of that table need re-deriving.
5. **`BETA_SQ`'s literal** moves with τ through `quadEvalBetaSq`
   (`H/QuadEval/Soundness.lean:106` → `zRecomposeL2SqBound γ b τ d cols =
   cols · (d · ((∑_{u<τ} b^u)·γ)²)`, `D/CyclotomicRing/NormBounds/Basic.lean:387-388`).
   **It does not reach this target's code**: `relOut`/`paperRelOut` have no
   `ℓ₂` row (`H/QuadEval/Reduction.lean:255`), so nothing in `quadeval.rs` reads
   `BETA_SQ`. The value belongs to `relIn`/`verify_weak`, already implemented.

**What does *not* differ:** the whole ŵ/t̂ half — `carrier*`, `tensorG`,
`tensorG1`, c1, c2, c3, and c6's first two balls — runs at
`messageDigits = innerDigits = δ = 8` and is insensitive to `Z`. So a change of
`Z` re-shapes roughly one third of this target and none of the rest.

**Literal-collision watch** (`STAGE2_SCOPING.md` F3): at `Z = 8` the value 8
names `GADGET_DIGITS`, `Z_DIGITS`, `RHO_DIGIT_COUNT` *and* the `InSb` lower
endpoint `⌊b/2⌋`; the value 16 names `GADGET_BASE`, `GAMMA`, `B_ZERO`, `OMEGA`,
`CHALLENGE_WEIGHT`; 8192 names `RLIN_CW`, `RLIN_CT`, `D_QUAD_COLS` *and* `n`.
Rewrite hypotheses, never goals.

## Semantics risks

**Ranges and overflow headroom.** No new width appears in this target; the
arithmetic in numbers:

* Coefficients stay in `Red u := u.val < q` (`hachi/lean/Field.lean:63`), `q < 2^32`. One `Fp` product is `< (q−1)² < 2^64`, one sum `< 2^33` — the base case already stated in `hachi/lean/Field.lean` header.
* `Rq::mul`'s accumulator adds `d = 1024` products *after* reduction, per `hachi/src/ring.rs:294-311`; the existing spec covers it. A *delayed-reduction* variant (§ Strategy candidates) would accumulate `1024·(q−1)² < 2^74 < 2^128` in `u128` — comfortable, and `16·(q−1)² < 2^68` for the sparse variant.
* c6's norms reuse `commit::vec_l_infty_norm`/`l_infty_norm`/`centered_abs` unchanged (`hachi/src/commit.rs:174-186, 115-127, 79-88`): each centered value `≤ q/2 < 2^31`, compared against `γ`, so `u64` throughout and no sum is taken. **No `u128` is needed anywhere in this target** — the `u128` in the crate exists for `vec_l2_norm_sq`, which `relOut` does not call.
* `in_sb`'s two comparisons are on `v = c.to_u64() < q` and `q − v`; the subtraction is checked in the Aeneas model, so `Red c` is its precondition — the *same* obligation `centered_abs` already discharges (`hachi/src/commit.rs:79-88`).
* **Index arithmetic is checked.** `finProdFinEquiv (i,e) = e + width·i` becomes `digits * i + e` in Rust (`hachi/src/gadget.rs:176, 208`), a checked `usize` multiply in the extracted model. Largest flat index in this target is `n·Z − 1 = 8192Z − 1` (65535 at `Z = 8`) — trivially inside `usize`, but the bound still travels as a hypothesis on each `_spec`.

**Partiality.**

* `Nat.clog` is not translatable — `Z_DIGITS` must be a params literal with a `Check.lean` entry, using the `Nat.clog_le_iff_le_pow` + `omega` pattern rather than `simp`/`decide` at `q ≈ 4.3·10^9` (`STAGE2_SCOPING.md` F6).
* `InSb`'s endpoints `(β+1)/2 − 1` and `β/2` are **`Nat` divisions and a truncated `Nat` subtraction** (`H/QuadEval/Reduction.lean:299-300`). Do **not** compute them in Rust from `β`: a `const`-derived subtraction extracts through `Result` (the reason `RING_DEGREE` is the literal `1024` and `GAMMA` the literal `16`, `hachi/src/params.rs:80-84, 162-165`). Introduce two literals — `SB_HI = 7` (`= (16+1)/2 − 1`) and `SB_LO = 8` (`= 16/2`) — each with its `params_semantics.rs` + `Check.lean` § 1 tie.
* `DigitDecomposition.reconstruct` is the totality condition behind the whole z side; see the `Z = 4` item in § Parameters.
* Nothing here uses well-founded recursion or `ℕ` subtraction on a runtime value.

**Exactness traps.**

* **Five equalities.** c1–c5 are `=` on `Rq`/commitment vectors. They must all go through `Rq::equals`/`PolyVec::equals` (`hachi/src/ring.rs:157`, `hachi/src/linalg.rs:111`) so exactly one notion of equality exists per type; `Simple.verify` on the spec side is `decide (commit … = c)` (`A/Simple/Scheme.lean:46-49`).
* **`relOut` is a `Prop`, and `verify_weak` was a `Bool`.** `relOut`/`paperRelOut` are `Set … ` of conjunctions (`H/QuadEval/Reduction.lean:264, 341`), whereas the already-translated `InnerOuter.verify_weak` is `Bool` (`H/InnerOuter/Scheme.lean:194-205`). So the Rust `rel_out : … -> bool` is a *decision procedure* and its equivalence statement is an **iff**, not an equality of Bools. This shape is not in `STAGE2_SCOPING.md` § "Erasure catalogue"; it is low-risk (every conjunct is decidable: `Rq` equality is canonical, the norms are `ℕ`) but it changes the `_spec` shape, so the spec author must be told. `InSb` is the one conjunct with no `Decidable` instance stated at the pin — it is a bounded `∀` over `k < deg φ` with decidable body, so the instance is a one-liner on our side, or the iff can be proved directly against the loop.
* **c6's γ is `CHAIN_GAMMA = 15`, not `params::GAMMA = 16`.** `H/HonestChain.lean:165-175, 188-193` pins the composed chain's `P.γ = bZero − 1`; `params::GAMMA` is the weak-opening `γ̄ = b` (`hachi/src/params.rs:150-166`). Two constants one apart, on two different relations — `STAGE2_SCOPING.md` S7/F1. Every `Check.lean` entry must say which.
* **The box is tight, the ball is not.** With balanced digits the honest decomposition's centered coefficients fill `[−8, 7]` exactly (`balancedZmodDigit_valMinAbs_mem`, `H/Gadget/Norms.lean:109`; and `balancedZmodDigitDecomposition`'s own docstring, `H/Gadget/Core.lean:139-141`), so `paperRelOut`'s `vecInSb 16` sits *on* the honest values while `relOut`'s `‖·‖∞ ≤ 15` has slack 7. A corpus inside the ball tests nothing. The semantics corpus must therefore contain coefficients at `−8` (in the box, magnitude 8 > 7 — the asymmetry) and at `+8` (**outside** the box, inside the ball ≤ 15): that single pair is what separates `rel_out` from `paper_rel_out`.
* **`paper_rel_out` is false on the current unsigned honest path.** Today's `gadget_decompose` yields digits in `{0,…,15}` (`hachi/src/gadget.rs:13-30`), which fails `InSb 16` for every digit ≥ 8 while passing `‖·‖∞ ≤ 15` exactly (no slack). So target 2's *honest-acceptance* tests on the `paperRelOut` side consume target 1's `balanced_gadget_decompose`. See the corrections at the end.
* `paperRelOut_subset_relOut` needs `b/2 ≤ γ` (`H/QuadEval/Reduction.lean:369`): `8 ≤ 15` ✓ (and `8 ≤ 16` ✓), so the containment is available at either γ.
* `ShortChallenge Φ ω = {c : Rq Φ // Rq.l1Norm Φ c ≤ ω}` (`H/QuadEval/Reduction.lean:151-152`) — a **subtype erasure**. `relOut` deliberately has no challenge-norm check (`:149-152`), so the bound exists only in the type: Rust needs a checked constructor or an explicit precondition (`STAGE2_SCOPING.md` § API mapping, "Confirmations"). The honest challenge `c = 1` has `‖1‖₁ = 1` and passes.
* `honestComputeV` is evaluated **twice** and `carrierDecomp` recomputed a **third** time by the prover skeleton (`H/QuadEval/Reduction.lean:453` `sendMessage`, `:458-459` `output` calls `computeV` again *and* `computeResp`). That is spec-faithful and computationally 3× the carrier cost; the sharing is a Stage 5 API decision, not a per-function optimization (see § Strategy candidates).

## Cost model

Units. One `Rq::mul` at `d = 1024` is `2^20` `Fp` mult-adds; the repo's own
figures are **~2–4 ms** (`hachi/benches/exclusions.toml:85-89`) and the only
measurement at this degree is **12.3 s for 8192 of them ⇒ ≈1.5 ms each**
(`hachi/benches/linalg.rs:11-13`, 2026-08-31). `Rq::scalar_mul` is `d` `Fp`
mults, i.e. `1/1024` of a mul (`hachi/src/ring.rs:263-272`); `digit_at` is `e`
divisions by the compile-time constant 16 (`hachi/src/gadget.rs:68-77`);
`centered_abs` is O(1). Per the harness rules these are *sizing*, never a
baseline (`NOTES.md` § "The first benchmark run…", § "The 5% accept floor…").

**Ring-multiplication counts at Fig. 9** (`2^m = 2^r = 1024`, `δ = 8`,
`n_A = n_B = dRows = 1`, `n = 8192`):

| definition | `Rq::mul` | `Rq::scalar_mul` | wall @1.5 ms/mul |
|---|---|---|---|
| `carrierEntry` (per block) | `2^m` = 1 024 | `2^m·δ` = 8 192 | ~1.5 s |
| `carrier` | `2^r·2^m` = **2^20** | `2^r·2^m·δ` = 2^23 | ~26 min |
| `carrierDecomp` | 0 | 0 | `2^r·δ·d`≈2^23 digit steps, on top of `carrier` |
| `carrierCommit` = `honestComputeV` | `2^20 + dRows·(2^r·δ)` = 2^20 + 8 192 | ″ | ~26 min |
| **`honestZ`** | `2^r · n` = **2^23** | 0 | **~3.5 h** |
| `zDecomp` | 0 | 0 | `n·d·Z(Z+1)/2` digit steps; output `n·Z` |
| `honestComputeResp` | `2^20 + 2^23` | | ~3.9 h |
| `tensorG1` (c4 LHS) | `2^r` = 1 024 | `2^r·δ` = 8 192 | ~1.5 s |
| `tensorG` (c5 LHS) | `2^r·n_A` = 1 024 | `2^r·n_A·innerDigits` = 8 192 | ~1.5 s |
| `relOut` c1 (`D ŵ`) | `dRows·(2^r·δ)` = 8 192 | 0 | ~12 s |
| `relOut` c2 (`B flatten t̂`) | `n_B·(2^r·n_A·innerDigits)` = 8 192 | 0 | ~12 s |
| `relOut` c3 | `2^r` = 1 024 | 8 192 | ~1.5 s |
| `relOut` c4 RHS (`aᵀ G z`, incl. `z = J ẑ`) | `2^m` = 1 024 | `n·Z + 2^m·δ` | ~1.5 s |
| `relOut` c5 RHS (`A z`) | `n_A·n` = 8 192 | 0 | ~12 s |
| `relOut` c6 | 0 | 0 | `(2·8192 + n·Z)·d` `centered_abs` ≈ 8.4·10^7 |
| **`relOut` total** | **28 672** | ≈ 24 576 + `n·Z` | **~43 s** |

**What dominates.**

1. **`honestZ` is the headline**: `2^r · n = 2^23` full ring products, because
   `scalarVecMul` multiplies by a *ring element* (`D/Vectors.lean:97-98`), not
   by a constant. That is the same `2^23` order as the already-excluded
   `commit::commit` (`hachi/benches/exclusions.toml:110-113`, "~2^23 ring
   muls") — hours per
   iteration. Everything else in the target is at most `2^20`.
2. **Within `relOut`, the three `1 × 8192` mat-vecs (c1, c2, c5-RHS) are 24 576
   of the 28 672 muls = 86%.** c3/c4/c6 and both tensor sums are rounding error
   beside them. Optimizing `relOut` means optimizing an 8192-wide mat-vec, i.e.
   `ring::mul`, i.e. the champion the whole repo is waiting for.
3. **The gadget collapse is mandatory, not optional.** Materializing
   `gadgetMatrix Φ base (2^m) δ` is `2^m × 2^m·δ = 2^23` ring elements ≈ 64 GiB
   (the arithmetic already recorded at `hachi/benches/gadget.rs:26-32`), and
   materializing `jMatrix Φ base n Z` is `n × n·Z = 2^26·Z` elements ≈ **4 TB at
   `Z = 8`**. Both must be `gadget_mul` (the `gadgetMul_apply` form,
   `H/Gadget/Core.lean:213-216`), which turns `rows·cols` products into
   `rows·digits` constant scalings. This is why the `Rq::mul` column above is
   `2^m` and not `2^23` for `carrierEntry`.
4. **A second, independent wall: RAM.** `Fp = u64` (`hachi/lean/Generated.lean:29`)
   ⇒ one `Rq` is 8 KiB. Then `wit.message : PolyVec (PolyVec (Rq) 8192) 1024` is
   `2^23` ring elements = **64 GiB** — larger than this machine's 30 GiB, and 8×
   `NOTES.md`'s "~8 GiB in-memory message" (which is the *undecomposed* `m`).
   `ẑ` is `8192·Z` × 8 KiB = 512 MiB at `Z = 8`; `ŵ` and `flatten t̂` are 64 MiB
   each. So `carrier`, `carrierDecomp`, `carrierCommit`, `honestZ`,
   `honestComputeV`, `honestComputeResp` are **not runnable at real `BLOCKS`
   at any multiplication speed** — the removal condition is a blockwise/streaming
   witness API, not the mul champion. Per `STAGE2_SCOPING.md`'s instruction, say
   so wherever the note is written so the walls are not conflated.

**Allocation.** Every loop in the crate's precedent style pushes into a fresh
`Vec` (`hachi/src/gadget.rs:200-216`, `hachi/src/linalg.rs:238-247`). At this
target's widths that matters: `zDecomp` grows a `Vec<Rq>` to `8192·Z` entries
(512 MiB at `Z = 8`) by `push`, and `tensorG` is a `Finset.sum` of vectors —
one freshly allocated `PolyVec` per block, 1024 of them, all but the last dead.

**Bench cases and scale policy** (fixed by `STAGE2_SCOPING.md`
§ "Scale policies", refined by the two walls above). Proposed
`quadeval/<op>` cases:

| case | scale | the note it must carry |
|---|---|---|
| `quadeval/carrier_entry` | REDUCED (`messageRows`) | `2^m` ring muls per call ≈1.5 s at real consts |
| `quadeval/carrier` | **REDUCED** (blocks *and* rows) | 2^20 ring muls (~26 min/iter) — the `eval_split` class (`exclusions.toml:139-143`) — **and** a 64 GiB `wit.message`; two independent walls |
| `quadeval/carrier_decomp` | REDUCED (blocks) | dominated by `carrier`; its own work is `2^r·δ·d` digit steps |
| `quadeval/carrier_commit` | **REDUCED** | `carrier` + an 8192-wide `D ŵ` mat-vec (~12 s) |
| `quadeval/z_decompose` | **REDUCED** (n) — *added by this brief* | no ring muls, but `n·Z` × 8 KiB = 512 MiB of output per iteration at `Z = 8`, plus `n·d·Z(Z+1)/2` digit steps. Allocation-bound, not mul-bound; the removal condition is neither the mul champion nor `m₀` |
| `quadeval/honest_z` | **REDUCED** (blocks) — *added by this brief* | `2^r·n = 2^23` ring muls (~3.5 h) **and** the 64 GiB witness |
| `quadeval/tensor_g`, `quadeval/tensor_g1` | REDUCED (blocks) | `2^r` ring muls (~1.5 s) each |
| `quadeval/rel_out`, `quadeval/paper_rel_out` | **REDUCED** | 28 672 ring muls (~43 s), 86% in three 8192-wide mat-vecs |
| `quadeval/in_sb`, `quadeval/vec_in_sb` | **real consts** | pure `u64` comparisons over `d`/`cols·d` coefficients; same class as `commit/l_infty_norm` |
| `quadeval/honest_compute_v`, `quadeval/honest_compute_resp` | **REDUCED** | strictly more than `carrier_commit` + `honest_z`; both walls |

Semantics tests: real consts for `in_sb`/`vec_in_sb`/`jMatrix`-collapse
roundtrips and the small algebraic identities; REDUCED for
`carrier`/`carrierCommit` (as `STAGE2_SCOPING.md` fixes) **and** for
`honestZ`/`honestComputeResp`/`zDecomp`, each with the arithmetic named above.

## Strategy candidates

* **`opt-algo-swap` — a challenge-sparse ring product. The headline.** `ShortChallenge` carries `‖c‖₁ ≤ ω = 16` in the type (`H/QuadEval/Reduction.lean:151-152, 170`), and a centered coefficient of magnitude ≥ 1 costs at least 1 of that budget, so a challenge has **≤ 16 nonzero coefficients out of 1024**. A skip-the-zero-multiplier convolution costs `≤ ω·d = 2^14` `Fp` ops instead of `d² = 2^20` — a **64× cut on `honestZ`'s `2^23` products**, and on `tensorG`/`tensorG1`/c4/c5's `c_i •ᵥ ·`. Correctness needs no precondition at all (dropping `0 · x` terms is unconditionally equal); the `ℓ₁` bound only justifies the *speed* claim. The reference implementation has exactly this operation (`ring::chal_mul_small_poly`, 10.0 µs vs ≈36 µs for a full NTT mul, 131 072 calls — `logs/paper-impl/README.md:111`). **Bench caveat:** the win is data-dependent, so the corpus must use genuinely ω-sparse challenges or the case measures the dense path.
* **`opt-algo-swap` — never materialize `G` or `J`.** Route every `gadgetMatrix … *ᵥ ·` through the `gadgetMul_apply` collapse (`H/Gadget/Core.lean:213-216`). Not a speed choice: the dense forms are 64 GiB and ~4 TB (§ Cost model item 3). Precedent and prior art already in the crate (`hachi/src/gadget.rs:39-47, 168-184`).
* **`opt-algo-swap` — running-quotient digit extraction.** `digit_at` re-divides from scratch per digit, making any decomposition `O(digits²)` per coefficient where a carried quotient is `O(digits)` (`hachi/benches/gadget.rs:3-9` states the trade). `zDecomp` is the largest consumer in the repo (`n·d` coefficients); the fix belongs to target 1's `digit_at`, and this target is the reason to prioritise it.
* **`opt-inplace-buffers` — pre-sized buffers and pass fusion.** (a) `ẑ`'s length `n·Z` is const-known: pre-size instead of `push`-growing 512 MiB. (b) `w := G_{2^r,δ} *ᵥ ŵ` is computed **twice** inside `relOut` — once in c3 (`H/QuadEval/Reduction.lean:274`) and once inside `tensorG1` for c4 (`:276` → `H/QuadEval/Gadgets.lean:190`); one shared pass saves 8192 scalar multiplies and a 64 MiB allocation. (c) `tensorG`'s `Finset.sum` of vectors allocates one `PolyVec` per block; accumulate into one buffer.
* **`opt-list-to-array`.** `dot` is `(List.ofFn …).sum` (`D/Vectors.lean:83-84`) and both tensor sums are `Finset.sum`s over `Fin blocks` of *vectors* (`H/QuadEval/Gadgets.lean:153`) — the exact List/`Fin`-function/per-element-allocation shape this skill exists for, at `blocks = 1024`.
* **`opt-tailrec-loops`.** The `Finset.sum`s of `honestZ`, `tensorG`, `tensorG1` and the `dot`s beneath them are structural sums; a tail-recursive accumulator lands 1:1 on the counter `while` loops the rest of the crate uses.
* **`opt-word-arith`.** Two places: a `u128` delayed-reduction accumulator inside the (sparse or dense) convolution — headroom written out in § Semantics risks, `2^74` and `2^68` against `2^128`; and `in_sb`/`vec_in_sb` as two `u64` comparisons per coefficient with an early exit, no signed arithmetic and no `valMinAbs` materialization. Representation changes (Montgomery/Barrett) touch the `cpoly` dependency and are gated, per that skill.
* **`(no skill yet)` — cross-round sharing of `ŵ` at the protocol seam.** The prover skeleton evaluates `honestComputeV` twice and recomputes `carrierDecomp` a third time (`H/QuadEval/Reduction.lean:453, 458-459`), i.e. 3 × 2^20 ring muls. No `opt-*` skill covers sharing *across* functions; the closest is `opt-inplace-buffers`' pass fusion, and the honest resolution is a Stage 5 API that computes `ŵ` once and passes it, keeping the per-function translations 1:1 with the spec.
* **`(no skill yet)` — blockwise/streaming witness.** The 64 GiB `wit.message` is a data-structure wall no arithmetic optimization touches (§ Cost model item 4); the reference implementation solves it by mmap streaming (`logs/paper-impl/README.md:28, 112`). Recording it as the removal condition for this target's REDUCED cases, distinct from both the `ring::mul` champion and `m₀`'s cube size.
* Where the specification itself flags a direction: `D/CyclotomicRing/Core/Basic.lean:72` carries `TODO add proper NTT multiplication here`, and `hachi/src/ring.rs` § "What is deliberately not here" records that the schoolbook product is deliberate and that an NTT carries its own equivalence obligation.

## Representation

**Reused unchanged** (the whole substrate is already translated): `Rq`
(`hachi/src/ring.rs:54`), `PolyVec`/`PolyMatrix`/`flatten_blocks`/`dot`/
`mat_vec_mul`/`scalar_mul`/`split_form` (`hachi/src/linalg.rs:55, 66, 274, 188,
238, 165, 258`), `gadget_mul`/`gadget_decompose`/`gadget_entry`/`base_pow`
(`hachi/src/gadget.rs:168, 196, 121, 105`), `vec_l_infty_norm`/`l_infty_norm`/
`centered_abs` (`hachi/src/commit.rs:174, 115, 79`), `Decomp` and `Opening`
(`hachi/src/commit.rs:229, 271` — `Opening` *is* `QuadEvalWitness`,
`H/QuadEval/Reduction.lean:117-119`), `PublicParams`
(`hachi/src/commit.rs:200`). `Fp`/`Ext4` come from `cpoly` and are never
reimplemented (`hachi/src/lib.rs`, README § "The field layer comes from cpoly");
no `Ext4` is needed in this target at all.

**New carriers**, each following the reasoning pattern of an existing one:

| ArkLib | Rust proposal | pattern / precedent |
|---|---|---|
| `PublicParamsD` (`H/QuadEval/Gadgets.lean:66-70`), a structure `extends` | `struct PublicParamsD { pp: PublicParams, d_matrix: PolyMatrix }` | ArkLib's `Opening extends Decomp` is already rendered as a named field (`hachi/src/commit.rs:271-283`) — same erasure, verbatim |
| `QuadEvalStatement` (`H/QuadEval/Reduction.lean:84-93`) | `struct QuadEvalStatement { u: PolyVec, avec: PolyVec, bvec: PolyVec, y: Rq }` | small fixed arity → named-fields struct, straight-line extracted model |
| `QuadEvalResponse` (`:98-105`) | `struct QuadEvalResponse { carrier_dec: PolyVec, inner_dec: Vec<PolyVec>, z_dec: PolyVec }` | ditto; `inner_dec` stays blocked because c2/c5 flatten it (`:272, 279`) |
| `ShortChallenge Φ ω` subtype (`:151-152`) | `struct ShortChallenge(Rq)` + a checked constructor returning `Option`, and `val(&self) -> &Rq` | dynamic-shape newtype whose constructor establishes the invariant; Aeneas cannot see Rust privacy, so the invariant must also travel as a hypothesis on each `_spec` — exactly `Wf` (`hachi/lean/Ring.lean:53`) and `WfVec`/`WfMat` (`hachi/lean/Scheme.lean:57, 68`). The Lean-side invariant is `l1_norm c ≤ OMEGA`, discharged from `ShortChallenge.l1Norm_le` (`H/QuadEval/Reduction.lean:170`) |
| `InSb`/`vecInSb` (`:297-303`) | `in_sb(a: &Rq) -> bool`, `vec_in_sb(v: &PolyVec) -> bool` at the params box | see the audit-claim check below |

**Function surface** (extending `STAGE2_SCOPING.md` § API mapping's
`quadeval.rs` sketch of `bridge_stmt`/`carrier_commit_v`/`honest_response`):
`carrier_entry`, `carrier`, `carrier_decomp`, `carrier_commit`, `j_matrix` (or
its collapsed `j_mul`), `z_decompose`, `tensor_g`, `tensor_g1`, `honest_z`,
`honest_compute_v`, `honest_compute_resp`, `rel_out`, `paper_rel_out`, `in_sb`,
`vec_in_sb`. `d_short` (`:212-213`) and `quad_eval_sis_set` (`:224-232`) are
soundness vocabulary and are not translated.

### The two audit claims, checked against the pin

**Claim 1 — "target 2 loses a refactor, because `zDigits = 8 = GADGET_DIGITS`
lets `gadget_matrix`/`gadget_decompose` stay hardwired"
(`STAGE2_SCOPING.md` § "Cross-audit contradiction", § "Ordered target list").
HOLDS, with one refinement and one conditional.**

* Mechanism confirmed: `jMatrix Φ base n zDigits` **is** `gadgetMatrix Φ base n zDigits` by definition (`H/QuadEval/Gadgets.lean:125-126`) and `zDecomp Φ ddZ` **is** `gadgetDecompose Φ ddZ` (`:132-134`). On the Rust side `digit_at` depends only on `GADGET_BASE` (`hachi/src/gadget.rs:69`), while `gadget_entry`, `gadget_matrix`, `gadget_mul` and `gadget_decompose` each read `params::GADGET_DIGITS` (`:122, 140, 169, 197`). At `Z = 8` those reads are correct for the J side too, so nothing is re-parameterized. **True.**
* Refinement: what is reusable is `gadget_mul` and `gadget_decompose`, **not** `gadget_matrix` — at `n = 8192` the dense `J` is ~4 TB (§ Cost model item 3). The saved refactor is on the two structured functions.
* Conditional, as instructed: **if `Z_DIGITS = 4` the refactor comes back.** Four frozen functions would need an explicit `digits: usize` argument, which regenerates `Generated.lean` and restates the six `dd`-mentioning specs `STAGE2_SCOPING.md` § "Decision 4 — Spec collateral" enumerates (`digit_at`, `digit_decompose`, `gadget_decompose` + loops, round-trip, `generate_decomps` + loop, `commit`), plus their bench rows. **Recommendation: additive `_z` siblings hardwiring `Z_DIGITS` instead** (`j_entry`/`j_matrix`/`j_mul`/`z_decompose`), which is the same additive-copy precedent Decision 4 chose for `balanced_gadget_decompose`/`generate_decomps_balanced` and restates no existing spec. Note `rows` is already a runtime argument of `gadget_matrix`/`gadget_mul`, so the parameterized route is mechanically trivial — the cost is entirely regeneration and spec churn, not difficulty.

**Claim 2 — "`InSb` needs a new signed asymmetric box check (two `u64`
comparisons, `centered_abs` being the absolute-value sibling rather than the
signed one)" (`STAGE2_SCOPING.md` § "Minor variants"). HOLDS, and can be
sharpened: no signed arithmetic is needed at all.**

`InSb β a` asks, per coefficient, `−(β/2) ≤ valMinAbs ≤ (β+1)/2 − 1`
(`H/QuadEval/Reduction.lean:297-300`) — at `β = b = 16` the box `[−8, 7]`, which
is **asymmetric**, whereas `centered_abs` returns `|valMinAbs|` and discards the
sign (`hachi/src/commit.rs:79-88`). The asymmetry is not expressible through
`centered_abs` alone: `−8` is in the box with magnitude 8, `+8` is out of the box
with the same magnitude. But `centered_abs`'s own branch is the sign test, so the
check is that branch with two different constants — on `v = c.to_u64()`,

```
in_sb(c) := if v <= Q/2 { v <= SB_HI } else { Q - v <= SB_LO }
```

with `SB_HI = 7`, `SB_LO = 8` as params literals (see § Semantics risks on why
they are literals and not `(β+1)/2 − 1`). Two `u64` comparisons per coefficient,
no `i64`, no `valMinAbs` materialization. `vec_in_sb` is the entrywise `∀`, and
`vecInSb_flattenBlocks` (`:326-329`) means the flattened form needs no separate
implementation. Cost is the `commit::l_infty_norm` class — real consts, cheap.

### Corrections to `STAGE2_SCOPING.md`

1. **§ "Scale policies", target 2 row is incomplete and one label is wrong.** (a) `carrier` is *not* "an 8192-wide mat-vec": the 8192-wide mat-vecs are `carrierCommit`'s `D ŵ` and `relOut`'s c1/c2/c5-RHS (8 192 muls, ~12 s each); `carrier` is `2^r·2^m = 2^20` muls (~26 min), the `evalsplit::eval_split` class. (b) **`honestZ`, `honestComputeResp` and `honestComputeV` are missing from the REDUCED list and are the target's worst cases** — `2^23` ring muls, ~3.5 h. (c) `zDecomp` also needs REDUCED, for an *allocation* reason (512 MiB of output at `Z = 8`) with no ring multiplication in it at all.
2. **A second removal condition exists, and it is neither the mul champion nor `m₀`.** `wit.message` at Fig. 9 is `2^23` ring elements × 8 KiB = **64 GiB** (`Fp = Std.U64`, `hachi/lean/Generated.lean:29`), against a 30 GiB machine; that is 8× `NOTES.md`'s "~8 GiB in-memory message", which counts the undecomposed `m`. So the honest-side cases are unrunnable at real `BLOCKS` at *any* multiplication speed, and their REDUCED notes must name the witness-streaming API as the removal condition. § "Scale policies" already insists the walls not be conflated; this is a third wall to keep apart.
3. **§ "Erasure catalogue" has no entry for the `Prop`-relation → `Bool` decision-procedure erasure.** `relOut`/`paperRelOut` are `Set`s of `Prop`s (`H/QuadEval/Reduction.lean:264, 341`) while the translated `verify_weak` was already `Bool` (`H/InnerOuter/Scheme.lean:194`). Low risk, but it makes the `_spec` an iff rather than an equality, and `InSb` is the one conjunct with no `Decidable` instance at the pin.
4. **§ "Ordered target list": the `{1 ∥ 2}` edge is right for code, but target 2's honest-path *tests* consume target 1.** The composed chain hands `quadEvalReduction` two *balanced* decompositions (`H/HonestChain.lean:350-351`), and `paper_rel_out` is outright false on today's unsigned digits (which fill `{0,…,15}`, `hachi/src/gadget.rs:13-30`, failing `InSb 16` from digit 8 up). Parallel development is fine; the honest-acceptance semantics tests are not, until target 1 lands.
5. **§ "Parameter mapping" is stated at `Z_DIGITS = 8` throughout, and four rows move if `Z = 4` is adopted**: `RLIN_CZ` 65536 → 32768, `RLIN_COLS`/μ₀ 81920 → 49152, `LIFT_COLS` 81960 → 49192, `M_ZERO` **27 → 26**. The F2/S1 evidence for `Z = 8` reproduces exactly as recorded (all `quadEvalBetaSq` sites pass `zDigits`; `hqz` closed by `Nat.le_pow_clog`); the countervailing facts for `Z = 4` are ArkLib's own definition-site docstring (`H/QuadEval/Gadgets.lean:122-123`) and the paper prototype's `Z_DECOMP_DELTA = 4` (`logs/paper-impl/README.md:48`). The decision is the user's; this brief is written so that only the widths marked `Z` move with it.
