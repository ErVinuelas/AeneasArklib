# Brief: `ArkLib.Lattices.Ajtai.InnerOuter.endPieceCheck` / `endPieceWitness` / `endPieceProver`   (ArkLib @ `294b3f0b0f46e1485c878a217e9de764855f5915`)

Target 6 of the protocol-layer wave (`STAGE2_SCOPING.md` § "Ordered target list +
scale policies": *end piece*, `smaller–similar`, "every shape precedented, needs
only F"). Rust home: a new `hachi/src/endpiece.rs`
(`STAGE2_SCOPING.md` § "API mapping from HachiRuntime": `endpiece.rs`
(`lift_short_check`, `end_piece_check`)).

Paths below are relative to `hachi/.lake/packages/Arklib/ArkLib/` unless the
prefix says otherwise; the Hachi subtree is abbreviated
`H/ = Commitments/Functional/Hachi/`. The rev is the one
`hachi/lake-manifest.json:8` records for `Arklib`.

---

## Definition chain

**The surface object.** Three conjuncts, one `Bool`:

```lean
def endPieceCheck (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    [BEq K.TCom] (φF : ZMod q →+* F)
    (stmt : WEvalStatement K.TCom F m₀) (w : LiftedWitness Φ μ n) : Bool :=
  (K.com w == stmt.t) && liftShortCheck Φ bound bDig w &&
    (wTableMleEval Φ m₀ φF b w stmt.point == stmt.value)
```
`H/EndPiece/Reduction.lean:157–161`. It decides `relWEvalClaim` exactly
(`endPieceCheck_eq_true_iff`, `:248–260`), and it is the *single* decision
procedure of the closing link: the guarded soundness verifier guards on it
(`endPieceVerifier`, `:164–169`; `endPieceVerifierGuardedForm`, `:176–182`) and
the nonrecursive scheme's terminal verifier *returns* it
(`terminalVerifier`, `H/Correctness.lean:112–114`;
`terminalVerifier_verify_eq_endPieceCheck`, `:121–125`). One Rust function
therefore serves both shapes.

`&&` is `Bool.and` on total functions, so conjunct order is semantically free
(and Rust's short-circuit `&&` is faithful) — see § Strategy candidates for why
reordering buys nothing on the path a bench measures.

### Conjunct A — `K.com w == stmt.t`

* `K : LiftCom W Short` = `CoordinateWise.BindingCommitment W Short`
  (`H/RingSwitch/Reduction.lean:217–218`); `K.com`/`K.TCom` are fields.
* At the composed chain, `K = hachiLiftCom Φ bound bDig D`
  (`H/RingSwitch/Reduction.lean:281–286`), with
  `TCom = CarrierCom Φ dRows = Simple.Commitment Φ dRows = PolyVec (Rq Φ) dRows`
  (`hachiLiftCom_TCom`, `:291–294`; `CarrierCom`, `H/QuadEval/Reduction.lean:68`;
  `Simple.Commitment`, `Commitments/Ordinary/Ajtai/Simple/Scheme.lean:34`) and
  `com w = Simple.commit Φ D (liftMessage Φ bDig w)`
  (`hachiLiftCom_com`, `:297–300`).
* `Simple.commit Φ A s = A *ᵥ s`
  (`Commitments/Ordinary/Ajtai/Simple/Scheme.lean:38–40`) →
  `matVecMul A v = fun i => dot (A i) v` (`Data/Lattices/Vectors.lean:87–89`) →
  `dot u v = (List.ofFn fun i => u i * v i).sum` (`:83–85`).
* `*` on `Rq Φ` → `instance : Mul (Rq Φ) := ⟨fun a b => Rq.mk Φ (a.1 * b.1)⟩`
  (`Data/Lattices/CyclotomicRing/Rq.lean:110`) → `Rq.mk Φ p = ⟨Φ.reduce p, _⟩`
  (`:96`) → `reduce p = p.modByMonic Φ.φ`
  (`Data/Lattices/CyclotomicRing/Core/Basic.lean:67`), the inner product being
  CompPoly's `CPolynomial` multiplication. **This is the same chain the existing
  `hachi/src/ring.rs:286` (`Rq::mul`) and `hachi/src/linalg.rs:238`
  (`PolyMatrix::mat_vec_mul`) already translate.**
* `liftMessage b w = Fin.append w.z (rhoDigitAsRq Φ b w.ρ)`
  (`H/RingSwitch/Reduction.lean:273–275`), width `μ + n·δρ` with
  `δρ = rhoDigitCount q b = Nat.clog b q` (`H/RingSwitch/RhoDigits.lean:66`).
  Digit-block entry `j` is
  `rhoAsRq Φ (rhoDigits Φ b (ρ (j / δρ)) (j % δρ))`
  (`rhoDigitAsRq`, `:259–261`; `finProdFinEquiv.symm j = (j.divNat, j.modNat)`,
  Mathlib `Mathlib/Logic/Equiv/Fin/Basic.lean:343), and
  `rhoAsRq p = Rq.ofFinCoeff Φ (deg φ) p.coeff` (`:252–253`).
* `==` on `TCom` is the `[BEq K.TCom]` instance argument — the one extra
  instance the Decision-3 audit flagged (`STAGE2_SCOPING.md` § "Decision 3":
  "`endPieceCheck` … F-set + an explicit `[BEq K.TCom]`"). Confirmed
  first-hand at `H/EndPiece/Reduction.lean:158`. At the concrete `K` the carrier
  is `PolyVec (Rq Φ) dRows`, so it is `hachi/src/linalg.rs:111`
  (`PolyVec::equals`) — no new equality notion.

### Conjunct B — `liftShortCheck Φ bound bDig w`

```lean
def liftShortCheck (w : LiftedWitness Φ μ n) : Bool :=
  decide (vecLInftyNorm Φ w.z ≤ bound) && rhoDigitsShortCheck Φ bound bDig w.ρ
```
`H/EndPiece/Reduction.lean:144–145`, deciding `liftShort` exactly
(`liftShortCheck_eq_true_iff`, `:149–152`;
`liftShort bound bDig w = vecLInftyNorm Φ w.z ≤ bound ∧ RhoDigitsShort Φ bound bDig w.ρ`,
`H/RingSwitch/Reduction.lean:211–212`).

* `vecLInftyNorm z = (univ : Finset (Fin cols)).sup (fun i => Rq.lInftyNorm Φ (z i))`
  and `Rq.lInftyNorm a = (Finset.range (deg φ)).sup (fun k => (a.1.coeff k).valMinAbs.natAbs)`
  (`Data/Lattices/CyclotomicRing/NormBounds/Basic.lean:125–126` and `:117–118`).
  Precedents: `hachi/src/commit.rs:174` (`vec_l_infty_norm`), `:115`
  (`l_infty_norm`), `:79` (`centered_abs`).
* `rhoDigitsShortCheck ρ = decide (∀ i, ∀ u < rhoDigitCount q bDig, ∀ k < (deg φ), ((rhoDigits Φ bDig (ρ i) u).coeff k).valMinAbs.natAbs ≤ bound)`
  (`H/EndPiece/Reduction.lean:111–113`); it decides `RhoDigitsShort`
  (`H/RingSwitch/Reduction.lean:159–161`) exactly, the `k ≥ deg φ` tail being
  discharged by `rhoDigits`' own truncation (`rhoDigitsShortCheck_eq_true_iff`,
  `:118–127`, via `rhoDigits_coeff`, `H/RingSwitch/RhoDigits.lean:141–143`).
* `rhoDigits b ρ u = CPolynomial.ofFinCoeff (deg φ) (fun k => balancedDigit b (rhoDigitCount q b) (ρ.coeff k) u)`
  (`H/RingSwitch/RhoDigits.lean:135–137`), and
  `balancedDigit b digits c e = ((Nat.digits b (c + balancedShift b digits).val).getD e 0 : ZMod q) − (b/2 : ZMod q)`
  (`:79–81`), definitionally the bundled decomposition's digit field
  (`balancedDigit_eq_digit`, `:86–89`, by `rfl`), with
  `balancedShift b digits = ⌊b/2⌋·Σ b^e` (`H/Gadget/Core.lean:133`). This is
  target 1's layer; `STAGE2_SCOPING.md` § "Decision 4" already fixes the Rust
  shape (`balanced_digit_at`, `BALANCED_SHIFT = 2_290_649_224`, `HALF_BASE = 8`)
  and the trap: the shift must be added in the **field**, never as a raw `u64`.

### Conjunct C — `wTableMleEval Φ m₀ φF b w stmt.point == stmt.value`

* `wTableMleEval φF b w a = CMlPolynomialEval.eval (cWTableMle Φ m₀ φF b w) (Vector.ofFn a)`
  (`H/ZeroCheck/Constraints.lean:348–351`), with
  `cWTableMle = Vector.ofFn fun i => wTable Φ m₀ φF b w (finFunctionFinEquiv.symm i)`
  (`:341–343`).
* `CMlPolynomialEval R n := Vector R (2^n)` and
  `eval p x = Vector.dotProduct p (lagrangeBasis x)`
  (`hachi/.lake/packages/CompPoly/CompPoly/Multilinear/Basic.lean:47` and
  `:524–525`), `lagrangeBasis w = Vector.ofFn fun i => ∏ j, if (BitVec.ofFin i).getLsb j then w[j] else 1 - w[j]`
  (`:410–411`). So conjunct C is a **`2^m₀`-long dot product against a
  `2^m₀`-long Lagrange basis** — Θ(m₀·2^m₀) field mults as written.
* `wTable` is a pure function of the flat cube index
  (`H/ZeroCheck/Constraints.lean:140–151`):
  `idx = finFunctionFinEquiv pt`, `d = deg φ`;
  `idx/d < μ` → `φF ((w.z ⟨idx/d⟩).1.coeff (idx % d))`;
  else `idx/d − μ < n·δρ` → `φF ((rhoDigits Φ b (w.ρ ⟨(idx/d−μ)/δρ⟩) ((idx/d−μ)%δρ)).coeff (idx % d))`;
  else `0`. Its two block lemmas are `wTable_zRow` (`:391`) and `wTable_rRow`
  (`:407`), and the flat index of block entry `(u, ℓ)` is `d·u + ℓ`
  (`wTableIndex`, `:1185–1196`; `wTableIndex_div_mod`, `:1207`).
* `finFunctionFinEquiv` is **little-endian**: `f ↦ ∑ i, f i · m^i`, inverse
  `a ↦ a / m^b % m` (Mathlib `Mathlib/Algebra/BigOperators/Fin.lean:580–598`).
  With `m = 2` this makes cube coordinates `0..9` the coefficient index
  `k = idx % d` (at `d = 2^10`) and coordinates `10..m₀−1` the committed-vector
  row `u = idx / d`.
* **The load-bearing structural fact** (needed by the § Strategy candidates
  split): column `u` of the `2^d × 2^(m₀−10)` reshaping of `cWTableMle` is
  exactly `φF` applied coefficient-wise to `liftMessage Φ b w u`, and `0` for
  `u ≥ μ + n·δρ`. Two halves, both read from the pin: the `z` half is
  `wTable_zRow` (`:391`) against `Fin.append_left` in `liftMessage`
  (`H/RingSwitch/Reduction.lean:273–275`); the digit half is `wTable_rRow`
  (`:407`) against `rhoDigitAsRq` (`:259–261`), whose `finProdFinEquiv.symm`
  split is `(j / δρ, j % δρ)` — the *same* `/δρ`, `%δρ` split `wTable` performs
  at `:148–150`. ArkLib states the agreement itself at `:255–258` ("the same
  flattening the gadget matrix uses … exactly as `wTable`'s widened quotient
  rows read it"). Verified, not assumed.
* `φF : ZMod q →+* F` is *not* a Rust argument — it is the fixed cpoly base
  embedding (`STAGE2_SCOPING.md` § "API mapping"), `Ext4::from_base`
  (`cpoly/src/field.rs:231`, spec `ext_from_base_spec`,
  `cpoly/lean/Field.lean:629`), i.e. ArkLib's
  `Ext.ofBaseRingHom ext4Params.toExtensionParams`
  (`CompPoly/Fields/Extension/Bridge.lean:354–359`, per
  `STAGE2_SCOPING.md` § "Decision 3").

### The prover and the extractor — both identities

`endPieceProver.sendMessage ⟨0,_⟩ = fun w => pure (w, w)` and
`output = fun _ => pure ((), ())` (`H/EndPiece/Reduction.lean:264–275`);
`endPieceWitness _stmt tr = tr 0` (`:195–197`); `endPieceExtractor` is
`endPieceWitness` on the tree's unique path (`:202–208`). The honest-run
characterization is a single `pure` (`endPieceProver_run_support`, `:297–315`).
**The prover half of this target has no arithmetic content**: `end_piece_prove`
is a move/clone of the `LiftedWitness`, and the wire format is one `P_to_V`
message (`pSpecEndPiece`, `:86–87`). All the cost is in the verifier.

---

## Parameters

`ArkLib` pins none of these; `hachi` pins all of them as `const`s
(`hachi/src/params.rs`). The brief is computed at:

| Constant | Value | Status | Source |
|---|---|---|---|
| `Q` | `2^32 − 99 = 4294967197` | **pinned** by the `cpoly` `Fp` | `params.rs:51` |
| `EXT_DEGREE` | 4 | **pinned** by cpoly's `Ext4` | `params.rs:58` |
| `RING_DEGREE` (`d = deg φ`) | 1024 (α = 10) | **chosen** (Fig. 9) | `params.rs:88` |
| `GADGET_BASE` (`b`) | 16 | **chosen** (Fig. 9) | `params.rs:97` |
| `GADGET_DIGITS` | 8 | **derived**: least `δ` with `q ≤ 16^δ` | `params.rs:113` |
| `MESSAGE_ROWS` = `BLOCKS` | 1024 | **chosen** (`2^m`, `2^r`) | `params.rs:124`, `:147` |
| `INNER_ROWS` = `OUTER_ROWS` | 1 | **chosen** (Fig. 9 `n_A = n_B = 1`) | `params.rs:133`, `:140` |
| `ML_VARS_LOW` = `ML_VARS_HIGH` | 10 | **derived** from `BLOCKS` | `params.rs:216`, `:225` |
| `GAMMA` (γ̄ = b, weak opening) | 16 | **derived** | `params.rs:166` |
| `KAPPA` | 32 | **derived** (`2ω`) | `params.rs:268` |
| `BETA_SQ` | **contested — see below** | derived | `params.rs:206` |

New Stage-2 constants this target consumes (values from
`STAGE2_SCOPING.md` § "Parameter mapping"; not yet in `params.rs` — the
extension is gated behind the bench commit per that file's sequencing note):

| Name | Value | Ties to |
|---|---|---|
| `D_ROWS` (`dRows`) | 1 | Fig. 9 `n_D`, a free var of `hachiLiftCom` (`H/RingSwitch/Reduction.lean:281–283`) |
| `B_ZERO` (`bZero`) | 16 | `ofPinnedDigitBase 16 .bZero = b` (`H/HonestChain.lean:165–175`) |
| `CHAIN_GAMMA` (`P.γ`) | **15** | `ofPinnedDigitBase 16 .γ = b − 1` (`H/HonestChain.lean:167`); pinned by `pinned_of_soundness_orientations` (`:188–194`) |
| `RHO_DIGIT_COUNT` (`δρ`) | 8 | `rhoDigitCount q bZero = Nat.clog 16 q` (`H/RingSwitch/RhoDigits.lean:66`) |
| `RLIN_ROWS` (`n₀`) | 5 | `rlinRows 1 1 1 = dRows + (outerRows + (1 + (1 + innerRows)))` (`H/RingSwitch/Rlin.lean:158–159`) |
| `RLIN_COLS` (`μ₀`) | 81920 | `rlinCols 1 8 8 zDigits 10 10 = 2^r·8 + (2^r·8 + 2^m·8·zDigits)` (`H/RingSwitch/Rlin.lean:152–153`) — **τ-dependent** |
| `LIFT_COLS` (`μ₀ + n₀·δρ`) | 81960 | `liftMessage` width (`H/RingSwitch/Reduction.lean:273–275`) |
| `M_ZERO` (`m₀`) | 27 | least `m₀` with `LIFT_COLS·d ≤ 2^m₀` — the hypothesis `hμn` at `H/Correctness.lean:277`, `:537` |
| `M_ONE` (`m₁`) | 3 | `n₀ ≤ 2^m₁` (`H/Composition.lean:293`) — not used by this target |

### What the composed chain feeds `endPieceCheck` — read off the pin

`H/Correctness.lean:254`:

```lean
(nonrecursiveTerminalReduction (oSpec := oSpec) Φ (M + 1) P.γ P.bZero P.bZero K φF)
```

so at the composed instantiation **`m₀ = M + 1`, `bound = P.γ`, `bDig = P.bZero`,
`b = P.bZero`** — note the third numeric slot is `bZero`, not `P.b` (they
coincide at `ofPinnedDigitBase`, but the spec text is `bZero`). With
`P = HonestRangeParams.ofPinnedDigitBase 16` (`H/HonestChain.lean:165–175`,
realized per `hachiNonrecursive_perfectCorrectness`) that is:

* **`bound = 15`** (`CHAIN_GAMMA`), **`bDig = b = 16`** (`B_ZERO`),
  **`m₀ = 27`** (`M_ZERO`), **`μ = μ₀ = 81920`**, **`n = n₀ = 5`**,
  **`dRows = 1`**, **`δρ = 8`**.
* `liftShort Φ P.γ P.bZero` is the `Short` predicate of `K`
  (`H/Correctness.lean:497`, `:568`), so `bound`/`bDig` are not independently
  choosable at the Rust API: they are the commitment's own indices.

Also decisive, and read first-hand: `hachiNonrecursiveOpening`
(`H/Correctness.lean:500–518`) hard-wires
`messageDigits = innerDigits = zDigits = δ P`, where
`δ P = Nat.clog P.b q` (`local notation`, `:491`) — i.e. **8**. `zDigits` is not
a free knob of the composed scheme.

### `BETA_SQ` / τ — contested, and how it touches this target

`BETA_SQ` and τ are under concurrent revision (the tree presently shows the
τ = 8 value at `params.rs:206`; a τ = 4 reading is the user's choice and the
paper's, `logs/paper-impl/README.md` § "Parameters": the reference impl's own
`Z_DECOMP_DELTA = 4`). This brief therefore asserts **no numeric `BETA_SQ`**.
For target 6 the situation is unusually clean:

1. **No conjunct of `endPieceCheck` uses `BETA_SQ`, or any ℓ₂ bound at all.**
   Conjunct A uses no bound. Conjunct B uses `bound = P.γ = bZero − 1` in *both*
   halves: the centered **ℓ∞** bound on `z`
   (`H/EndPiece/Reduction.lean:145`, first factor) and the same `bound` as a
   per-coefficient centered-absolute-value bound on the quotient digits
   (`:112–113`). Conjunct C uses no bound. `βSq` enters the chain only through
   `relPolyEval`/`verify_weak` (`H/Correctness.lean:282`,
   `hachi/src/commit.rs` `verify_weak`), which is a *different* link.
   ⇒ **The end piece is bound-insensitive to the τ dispute.**
2. **τ does reach this target — as a size, through `zDigits`.** τ occupies the
   `zDigits` slot of `rlinCZ = 2^m · messageDigits · zDigits`
   (`H/RingSwitch/Rlin.lean:166`), hence of `μ₀`:
   * τ = 8: `μ₀ = 8192 + (8192 + 65536) = 81920`, `LIFT_COLS = 81960`,
     `LIFT_COLS·d = 83 927 040`, so `m₀ = 27` (`2^26 < … ≤ 2^27`).
   * τ = 4: `μ₀ = 8192 + (8192 + 32768) = 49152`, `LIFT_COLS = 49192`,
     `LIFT_COLS·d = 50 372 608`, so `m₀ = 26` (`2^25 < … ≤ 2^26`).

   So the τ = 4 reading would shrink conjuncts A and B by **1.67×** and conjunct
   C's table by **2×**. Nothing else moves.
3. **The τ = 4 reading is not instantiable for `zDigits` at the pin.**
   `nonrecursiveOpeningReduction` demands `hqz : q ≤ P.b ^ zDigits`
   (`H/Correctness.lean:242`) and the composed def discharges it with
   `Nat.le_pow_clog P.hb q` at `zDigits = δ P` (`:517`); at `(16, 4)`,
   `16^4 = 65536 ≪ q`, so `hqz` is false. ArkLib's own generic docstring names
   the paper symbol (`H/QuadEval/Gadgets.lean:122–123`, "`zDigits = τ`"), which
   is where the τ = 4 reading comes from, but the *instantiation* pins 8.
   ⇒ Whichever way `BETA_SQ` lands, **this target should be sized at
   `zDigits = 8` (`m₀ = 27`, `LIFT_COLS = 81960`)**, and the τ = 4 branch is
   worth carrying only as a sensitivity note, not a second parameter set.

---

## Semantics risks

### Value ranges and overflow headroom

Aeneas models every `+`/`*`/index as checked, and a triple
`m ⦃ r => post r ⦄` already asserts `∃ r, m = ok r`
(`hachi/lean/Field.lean`, header § "What a spec says"), so each of the following
is a proof obligation, written out in numbers.

* **Coefficient arithmetic (conjunct A).** `Red u` is `u.val < q`, `q < 2^32`;
  a sum of two reduced words is `< 2^33` and a product `≤ (q−1)^2 < 2^64`. The
  negacyclic accumulation in `Rq::mul` is the existing, proved chain
  (`hachi/src/ring.rs:286`), reused verbatim by `mat_vec_mul`
  (`hachi/src/linalg.rs:238`). **No new width appears in conjunct A.**
* **Norms (conjunct B).** `centered_abs` returns a `u64` `< q/2 < 2^31`
  (`hachi/src/commit.rs:79`); `l_infty_norm`/`vec_l_infty_norm` are `Finset.sup`
  → a running `max`, so no accumulation and **no overflow at any width**
  (contrast `vec_l2_norm_sq`, which needed `u128` — that argument is *not*
  needed here, and a `u128` here would be cargo-culted). The comparison is
  `≤ bound = 15` in `u64`.
* **Balanced digits (conjunct B).** `balanced_digit_at` is
  `digit_at(c + Fp::new(BALANCED_SHIFT), e) − Fp::new(HALF_BASE)` — both
  operations in the field (mod-`q` wrap), never on raw `u64`
  (`STAGE2_SCOPING.md` § "Decision 4", recorded trap). `BALANCED_SHIFT`
  = `2 290 649 224` < `q`, so `Fp::new` is a no-op reduction; the field add can
  wrap and must.
* **`Ext4` arithmetic (conjunct C).** All proved in the pinned cpoly:
  `ext_add_spec` / `ext_mul_spec` / `ext_smul_spec` / `ext_eq_spec` at
  `cpoly/lean/Field.lean:454`, `:513`, `:572`, `:695`. `Ext4` is four `Fp`
  (`cpoly/src/field.rs:185–194`) = 32 bytes; `Ext4 × Ext4` is 16 `Fp` mults
  + 3 `W`-scalings (`:315–329`), `Fp × Ext4` is **4** `Fp` mults (`:332–344`).
  **No new headroom argument is owed by this target.**
* **Index width (conjunct C).** `2^m₀ = 2^27 = 134 217 728` and
  `LIFT_COLS·d = 83 927 040` both fit `usize` with 37 bits to spare; cpoly's
  specs carry the `2^n ≤ usize::MAX` side condition explicitly
  (`pow2_spec`, `cpoly/lean/Multilinear.lean:486`; `table_len`'s own contract,
  `cpoly/src/multilinear.rs:100–109`). At τ = 4 (`m₀ = 26`) the same holds.
  **Memory, not width, is the binding constraint** — see § Cost model.

### Partiality

* **`Nat.clog` is not translatable.** `rhoDigitCount q b = Nat.clog b q`
  (`H/RingSwitch/RhoDigits.lean:66`) becomes the literal
  `RHO_DIGIT_COUNT = 8`, with a `Check.lean` entry via the
  `Nat.clog_le_iff_le_pow` + `omega` pattern (`STAGE2_SCOPING.md` § F6). Same
  for `M_ZERO`/`M_ONE`, which ArkLib leaves free under inequalities (§ F4).
* **Guard-ordered `Nat` subtractions.** `wTable` computes `idx/d − μ` *inside*
  the `else` branch of `if hz : idx/d < μ`
  (`H/ZeroCheck/Constraints.lean:145–150`). In `ℕ` the subtraction truncates;
  in Rust it is checked. **The branch order must be preserved literally** —
  this is hazard (a) of `STAGE2_SCOPING.md` § "Scale/overflow hazards".
  Same for `(idx/d − μ)/δρ` and `(idx/d − μ) % δρ`.
* **Erased `Fin` proofs.** `⟨(idx/d − μ)/δρ, Nat.div_lt_of_lt_mul …⟩`
  (`:148–150`) and `wTableIndex`'s bound proof (`:1183–1194`) are erased; the
  Rust index needs the guard that discharges them, or the shape invariant of
  the carrier does.
* **Derived-looking constants.** As with `RING_DEGREE` being the literal `1024`
  rather than `1 << RING_LOG_DEGREE` (`params.rs:88`), `HALF_BASE` must be the
  literal `8`, not `GADGET_BASE / 2`, and `CHAIN_GAMMA` the literal `15`, not
  `B_ZERO − 1`: a derived form is a `Result` in every Lean use.
* **`hρ` is a subtype field, not a check.** `LiftedWitness.hρ : ∀ i, (ρ i).toPoly.natDegree ≤ d − 1`
  (`ProofSystem/RingSwitching/Lift/Reduction.lean:80–88`). It is erased in Rust
  and must travel as a hypothesis on each `_spec` — the `Wf` pattern of
  `hachi/lean/Ring.lean`. See § Representation for why this one is free.

### Exactness traps

* **Conjunct B2 always passes at these parameters.** `DigitBaseOk q bound bDig`
  (`H/RingSwitch/Reduction.lean:175–181`) holds at `(q, 15, 16)`:
  `1 < 16`; `16 ≤ q/2 = 2 147 483 598`; `16/2 = 8 ≤ 15`. Hence
  `rhoDigitsShortCheck_eq_true_of_digitBaseOk`
  (`H/EndPiece/Reduction.lean:138–141`) makes conjunct B2 **unconditionally
  `true`** — the pin says so in its own docstring (`:130–137`: "at the chain's
  parameters `liftShortCheck` is effectively the `z`-norm check alone").
  Consequences: (i) the check still has to *run* and pay its full cost, since
  there is no violation to exit on; (ii) **a semantics-test corpus that only
  exercises honest witnesses tests conjunct B2 vacuously** — negative cases must
  be built by hand from a `ρ` whose *digits* were tampered with post hoc, which
  no honest path produces. Say so in the test file; do not report B2 as
  "covered" on honest inputs alone.
* **The ℓ∞ bound is tight-ish, and the interesting side is B1.** Honest
  balanced digits land in `[−8, 7]` (`balancedDigit_valMinAbs_mem`,
  `H/RingSwitch/RhoDigits.lean:108–115`), i.e. 8 against a bound of 15 — slack
  7. The `z` half has no such guarantee: `bound = 15` on `vecLInftyNorm w.z` is
  a real constraint that an honest lift must be shown to meet, and a corpus
  sitting comfortably inside it tests nothing (`NOTES.md`
  § "The dimensions and the norm bounds"). Put the boundary cases at
  `‖z‖∞ ∈ {14, 15, 16}`.
* **Two notions of "gamma", one apart.** `CHAIN_GAMMA = 15` (this target's
  `bound`) vs `params.rs:166`'s `GAMMA = 16` (the weak-opening γ̄ = b). Flag F1
  / S7 of `STAGE2_SCOPING.md`; every proof step must rewrite *hypotheses*, never
  goals, and every `Check.lean` line must say which quantity it means.
* **Literal collisions this target walks into** (`STAGE2_SCOPING.md` § F3):
  value **16** — `GADGET_BASE`, `GAMMA`, `B_ZERO`, `OMEGA`, `CHALLENGE_WEIGHT`;
  value **8** — `GADGET_DIGITS`, `Z_DIGITS`, `RHO_DIGIT_COUNT`, `HALF_BASE`;
  value **1** — `INNER_ROWS`, `OUTER_ROWS`, `D_ROWS`; value **15** —
  `CHAIN_GAMMA` and the unsigned digit ceiling `b − 1`. Conjunct B uses
  `bound = 15` and `bDig = 16` *adjacently*, which is exactly where an off-by-one
  substitution would typecheck and be wrong.
* **Equality.** Conjunct A compares `PolyVec`s (`PolyVec::equals`,
  `hachi/src/linalg.rs:111`, through `Rq::equals`, `hachi/src/ring.rs:157`,
  through `Fp::to_u64`); conjunct C compares `Ext4` (`ext_eq_spec`,
  `cpoly/lean/Field.lean:695`, written out coefficient-wise at
  `cpoly/src/field.rs:246–248`). Exactly one notion of equality per type; do not
  add a third.
* **Degenerate sizes.** `dRows = 1` makes conjunct A a *single* dot product, so
  the `PolyMatrix` row loop runs once — a shape where an off-by-one in the row
  loop is invisible. `Finset.sup` over an empty range is `0`, which an empty
  Rust loop reproduces (`hachi/src/commit.rs:113–115`); at `μ = 81920 > 0` and
  `n = 5 > 0` no empty case arises on the composed path, but the standalone
  Rust function will be called at reduced shapes where it might.

---

## Cost model

Op counts at the parameters above (`m₀ = 27`, `μ = 81920`, `n = 5`, `δρ = 8`,
`d = 1024`, `dRows = 1`), stated per bench case (`<module>/<op>`). Following
`NOTES.md` § "The first benchmark run, and what it says about the harness", these
are operation counts with first-principles floors, **never predicted
percentages**; the external anchors are `logs/paper-impl/README.md`
§ "per-operation breakdown", whose own caveats apply.

### `endpiece/end_piece_check` — conjunct A (`com == t`) dominates

* `liftMessage`: `n·δρ = 40` calls to `rhoDigits`, each `d = 1024`
  `balancedDigit` evaluations ⇒ **40 960** digit extractions. Negligible.
* `Simple.commit`: one `matVecMul` at `1 × 81960` ⇒ **81 960 `Rq::mul` +
  81 959 `Rq::add`**. Schoolbook negacyclic at `d = 1024`
  (`hachi/src/ring.rs:286`) is `d^2 = 1 048 576` coefficient mult-adds each ⇒
  **≈ 8.59 × 10^10 coefficient mult-adds**.
* Floor: our own `ring/mul` anchor at the *old* `d = 64` read ≈ 8.5 µs for
  `64^2 = 4096` coefficient ops (`NOTES.md` § "The first benchmark run"), i.e.
  ≈ 2 ns per coefficient op ⇒ this conjunct alone floors around
  **10^2 seconds** at `d = 1024`. The reference impl's NTT anchor for the same
  algebra is ≈ 36 µs per `d = 1024` mul unamortized and 5.31 ms per
  `ring::mat_mul_vec` call (`logs/paper-impl/README.md`), which is the quantified
  version of `PLAN_PAPER_PARAMS.md` Phase 5's warning.
* Allocation: `D` is `1 × 81960` `Rq` = **≈ 640 MiB**, and `liftMessage` is
  another 81 960 `Rq` = **≈ 640 MiB**. Both are unavoidable at real consts.
* **Dominant term of the whole target, by three orders of magnitude.**

### conjunct B1 (`‖z‖∞ ≤ bound`)

`μ·d = 81 920 × 1024 = 83 886 080` `centered_abs` + compare, no allocation
beyond the accumulator. Sub-second; invisible beside conjunct A.

### conjunct B2 (`rhoDigitsShortCheck`) — quadratic in `d` as literally written

The spec's quantifier nesting is `∀ i, ∀ u, ∀ k`, with
`rhoDigits Φ bDig (ρ i) u` *inside* the `k` loop
(`H/EndPiece/Reduction.lean:112–113`). A literal translation therefore calls
`rhoDigits` `n·δρ·d = 5 × 8 × 1024 = 40 960` times, each building a `d`-wide
polynomial ⇒ **41 943 040 `balancedDigit` evaluations**, each of which is a
`Nat.digits 16` expansion (`H/RingSwitch/RhoDigits.lean:79–81`) ≈ 8 divmods ⇒
≈ **3.4 × 10^8 divmods**. Hoisting `rhoDigits` out of the `k` loop takes that to
`n·δρ = 40` calls / 40 960 digit evaluations; extracting all `δρ` digits of one
coefficient in a single running-quotient pass takes it to `n·d = 5 120` digit
expansions. **A ≈ 8 192× reduction that changes no semantics** — see § Strategy
candidates. This is *not* a `ring::mul` wall and *not* an `m₀` wall; it is a
loop-nesting artefact of the spec's `decide`.

### conjunct C (`wTableMleEval`) — the `m₀` cube

Three distinct costs, worth separating because they have different removal
conditions:

1. **Materializing `cWTableMle`** (`H/ZeroCheck/Constraints.lean:342–345`):
   `2^m₀ = 134 217 728` `Ext4` = **≈ 4.29 GB**, and each entry re-derives
   `rhoDigits` from scratch in the digit range
   (`wTable`, `:147–150`) ⇒ up to `2^m₀ × d ≈ 1.4 × 10^11` `balancedDigit`
   evaluations. **This is not slow, it is not runnable.** Removing it is a
   precondition for the target existing at all, not an optimization.
2. **`lagrangeBasis`** (`CompPoly/Multilinear/Basic.lean:410–411`):
   `m₀ · 2^m₀ ≈ 3.6 × 10^9` `Ext4` mults + a second 4.29 GB vector.
3. **The dot product** (`:524–525`): `2^m₀ ≈ 1.34 × 10^8` `Ext4` mults
   (16 `Fp` mults each ⇒ ≈ 2.1 × 10^9 `Fp` mults) + as many adds.

With the two rewrites named below (layer folding, and the 10/17 split) conjunct C
lands at ≈ `LIFT_COLS·d + 2^(m₀−10) ≈ 8.4 × 10^7` **base×extension** products
(4 `Fp` mults each ⇒ ≈ 3.4 × 10^8 `Fp` mults) with a **4 MB** high basis and an
**8 KB** low basis, and never allocates a `2^m₀` object.

### `endpiece/end_piece_prove`, `endpiece/end_piece_witness`

O(1) — a move of the `LiftedWitness` (`H/EndPiece/Reduction.lean:264–275`,
`:195–197`). Worth a birth bench case only as a control; the interesting number
is that it is a control.

### Scale policy, and which wall forces each REDUCED case

`STAGE2_SCOPING.md` § "Scale policies", target 6 row: *"real consts for the
checks; the MLE eval REDUCED — bench cases mixed, per case."* Applied per
conjunct, with the note each REDUCED case must carry:

| Case | Policy | Note the case must carry |
|---|---|---|
| `endpiece/end_piece_prove` | real consts | — (O(1)) |
| `endpiece/lift_short_check` (B1+B2) | **real consts** | — 83.9 M `centered_abs` + 5 120 digit expansions after the fusion; runnable |
| `endpiece/end_piece_check` conjunct A (`lift_commit`) | **REDUCED** | *"81 960 schoolbook negacyclic products at `d = 1024` (≈ 8.6 × 10^10 coefficient mult-adds) plus ≈ 1.3 GiB of key and message. **The forcing wall is `ring::mul`'s width** — an accepted multiplication champion (NTT) removes this note. It is not `m₀`'s cube size."* |
| `endpiece/w_table_mle_eval` (conjunct C) | **REDUCED** | *"`m₀ = 27`, so the hypercube has 1.34 × 10^8 points and a materialized `Ext4` table is ≈ 4.29 GB. **The forcing wall is `m₀`'s cube size, which no multiplication speedup touches**; the split rewrite removes the *allocation* but the Θ(2^m₀) point count remains. Not a `ring::mul` wall."* |
| `endpiece/end_piece_check` (whole) | **REDUCED** | both notes above, verbatim and separately — the case is bounded below by the max of the two, and the two are removed by different champions |

Reduced shape recommendation, so the two walls stay visible and distinct:
keep `d = 1024` and shrink `μ₀`/`n₀` (e.g. `μ = 16`, `n = 2`, `δρ = 8`,
`m₀ = 15`) — that keeps the `ring::mul` width honest per-product while making
the cube tractable, and it keeps the `/d`, `%d` split at the real `d` so the
guard-ordered `Nat` subtractions are exercised at their real modulus.

### Correction to `STAGE2_SCOPING.md` § "Ordered target list + scale policies"

**Target 6's row — "real consts for the checks" — is inconsistent with target
3's row for one conjunct.** Conjunct A of `endPieceCheck` *is* `lift_commit`:
`K.com w = Simple.commit Φ D (liftMessage Φ bDig w)` at width
`μ₀ + n₀·δρ = 81960` (`hachiLiftCom_com`,
`H/RingSwitch/Reduction.lean:297–300`), which target 3's own row already marks
`REDUCED` ("real consts except `lift_commit` (81960-wide) → REDUCED"). The two
rows must agree: **conjunct A inherits target 3's REDUCED policy**, and only
`liftShortCheck` and the O(1) prover stay at real consts. The table above is the
repaired reading. The `m₀`-vs-`ring::mul` distinction the same section insists on
is what makes this matter: target 6 is the one target where **both** walls fire
in a single function, and a single blanket note would conflate them.

---

## Strategy candidates

Pointers only; the strategies live in their skills. Ranked by the op counts
above.

* **`opt-inplace-buffers` — hoist `rhoDigits` out of the `k` loop, and compute
  the digit block once for all three conjuncts.** The spec evaluates
  `rhoDigits Φ bDig (ρ i) u` once per `(i, u, k)`
  (`H/EndPiece/Reduction.lean:112–113`) and again inside `liftMessage`
  (`H/RingSwitch/Reduction.lean:259–261`) and again inside `wTable`
  (`H/ZeroCheck/Constraints.lean:147–150`) — three independent recomputations of
  the same `n·δρ = 40` polynomials. One pre-sized `n·δρ` buffer, filled once,
  serves conjuncts A, B2 and C. Highest ratio of win to risk in this brief
  (41.9 M → 40 960 digit evaluations on B2 alone, and it is what makes C's naive
  form stop being astronomically wasteful).
* **`opt-algo-swap` (a) — `eval` → `evalMle` for conjunct C.**
  `CMlPolynomialEval.evalMle` folds one variable per layer
  (`CompPoly/Multilinear/Basic.lean:491–500`) at Θ(2^m₀) instead of
  `eval`'s Θ(m₀·2^m₀), and **the equality is already proved at the pin**:
  `CMlPolynomialEval.eval_mle_eq_eval` (`:573–585`). It is already translated
  and proved on the Rust side too: `MultilinearEvals::eval_mle`
  (`cpoly/src/multilinear.rs:538–546`) with `eval_mle_spec`
  (`cpoly/lean/Multilinear.lean:1819–1840`, which cites exactly that lemma).
  A free ≈ 27× on the basis work, and it deletes the second 4.29 GB vector.
* **`opt-algo-swap` (b) — the 10/17 split, so the `2^m₀` table is never
  materialized.** `m₀ = 27 = 10 + 17`, `d = 2^10`, and
  `finFunctionFinEquiv` is little-endian
  (Mathlib `Mathlib/Algebra/BigOperators/Fin.lean:580–598`), so cube coordinates
  `0..9` are the coefficient index and `10..26` the committed-vector row. ArkLib
  proves the factorization generically in the coefficient ring and in
  `(nl, nh)`: `evalSplitEval` (`H/EvalSplit.lean:310–313`) and
  `evalSplitEval_eq_eval` (`:317`), on top of `lagrangeBasis_split` (`:300`).
  Combined with the structural fact established in § Definition chain (column
  `u` of the reshaped table is `φF`-applied `liftMessage w u`, zero past
  `LIFT_COLS`), conjunct C becomes: one `2^10` low basis (8 KB), one `2^17` high
  basis (4 MB), one streaming pass over the `LIFT_COLS × d` coefficients — the
  zero tail costing nothing. **In-repo Rust precedent exists**:
  `MlEvals::eval_split_eval` (`hachi/src/evalsplit.rs:336–341`),
  `split_form` (`hachi/src/linalg.rs:258`), `lagrange_basis`
  (`hachi/src/evalsplit.rs:174`), `split_equiv`/`split_equiv_inv` (`:66`, `:77`)
  — this is the `evalsplit` target's own shape at `Ext4` instead of `Rq`. This
  is the strategy that makes conjunct C runnable at real `m₀`; it does **not**
  remove the Θ(2^m₀) lower bound on the outer basis (2^17 here after the split),
  which is why the case stays REDUCED.
* **`opt-algo-swap` (c) — running-quotient digit extraction.**
  `balancedDigit` recomputes a whole `Nat.digits 16` expansion for a single digit
  index (`H/RingSwitch/RhoDigits.lean:79–81`). All `δρ = 8` digits of one
  coefficient in one pass is the named example of that skill; 40 960 → 5 120
  expansions on B2. Shares the target-1 layer, so coordinate with it rather than
  duplicating.
* **`opt-word-arith` — base×extension products in conjunct C.** Every table
  entry is `φF(c)` for a base-field `c` (`wTable`,
  `H/ZeroCheck/Constraints.lean:146`, `:148–150`), so the inner products are
  `Fp × Ext4` (4 `Fp` mults, `cpoly/src/field.rs:332–344`, spec
  `ext_smul_spec`, `cpoly/lean/Field.lean:572`) rather than `Ext4 × Ext4`
  (16 `Fp` mults + 3 `W`-scalings, `:315–329`). A 4× on ≈ 8.4 × 10^7 products,
  for free, using an already-proved cpoly primitive — do not re-embed into
  `Ext4` first.
* **`opt-list-to-array` — the `List` shapes on conjunct A's path.**
  `dot` is `(List.ofFn fun i => u i * v i).sum`
  (`Data/Lattices/Vectors.lean:83–85`), `liftMessage` is a `Fin.append`
  (`H/RingSwitch/Reduction.lean:275`), and `rhoDigits` is
  `CPolynomial.ofFinCoeff` (`H/RingSwitch/RhoDigits.lean:135–137`). At width
  81 960 the intermediate list is 640 MiB of per-element allocation.
  `hachi/src/linalg.rs:188` (`PolyVec::dot`) already carries the indexed-loop
  form for this exact shape, so the win here is at the *new* `liftMessage`
  buffer rather than at `dot` itself.
* **NTT for `Rq::mul` — `(no skill yet)`, and it belongs to the ring target,
  not here.** The pin flags the direction itself
  (`Data/Lattices/CyclotomicRing/Core/Basic.lean:72`: "TODO add proper NTT
  multiplication here, not just reduce-after-CPolynomial-mul"), and
  `hachi/src/ring.rs` § "What is deliberately not here" (`:37`) records that the
  schoolbook product is deliberate and that an NTT carries an equivalence
  obligation of its own. **Recorded here only because target 6 is the single
  largest consumer of `ring::mul` width in the protocol layer** (81 960
  products in one function call, tied with target 3's `lift_commit` because it
  *is* that product), so this target's `com` conjunct is the case that will move
  most when that champion lands.
* **Not worth a candidate: reordering the conjuncts.** `Bool.and` on total
  functions is commutative, so `B && C && A` is provably equal to the spec's
  order and would short-circuit the 8.6 × 10^10-op conjunct on a *rejecting*
  input. But every bench case and every honest semantics test runs the
  *accepting* path, where all three conjuncts execute regardless. Named here so
  the fan-out does not spend an agent on it.

---

## Representation

**Existing types this slots into** — every shape is precedented, confirming
`STAGE2_SCOPING.md`'s "every shape precedented, needs only F":

| ArkLib | Rust | Precedent |
|---|---|---|
| `PolyVec (Rq Φ) k`, `PolyMatrix` | `PolyVec`, `PolyMatrix` | `hachi/src/linalg.rs:55`, `:66` |
| `Simple.commit Φ D ·` | `PolyMatrix::mat_vec_mul` | `hachi/src/linalg.rs:238` |
| `TCom = CarrierCom Φ dRows`, `==` | `PolyVec` + `PolyVec::equals` | `hachi/src/linalg.rs:111` |
| `vecLInftyNorm`, `Rq.lInftyNorm`, `valMinAbs.natAbs` | `vec_l_infty_norm`, `l_infty_norm`, `centered_abs` | `hachi/src/commit.rs:174`, `:115`, `:79` |
| `balancedDigit`, `rhoDigits` | target 1's `balanced_digit_at` + a `d`-wide coefficient loop | `hachi/src/gadget.rs:68` (`digit_at`), `:196` (the triple-loop shape) |
| `F`, `φF`, `CMlPolynomialEval F m₀`, `eval`/`evalMle`, `lagrangeBasis` | `Ext4`, `Ext4::from_base`, `MultilinearEvals`, `eval`/`eval_mle`, `lagrange_basis` | `cpoly/src/field.rs:185`, `:231`; `cpoly/src/multilinear.rs:487`, `:530`, `:538`, `:169` — **taken from `cpoly`, never reimplemented** (`hachi/src/lib.rs`, README § "The field layer comes from cpoly") |
| the split evaluation | `MlEvals::eval_split_eval`, `split_form` | `hachi/src/evalsplit.rs:336`, `hachi/src/linalg.rs:258` |

**One new carrier, and it is cheap: `LiftedWitness`.**
`Lift.LiftedWitness R S d μ n` is `⟨z : Fin μ → S, ρ : Fin n → CPolynomial R, hρ : ∀ i, (ρ i).toPoly.natDegree ≤ d − 1⟩`
(`ProofSystem/RingSwitching/Lift/Reduction.lean:80–88`), at
`S = Rq Φ`, `R = ZMod q`, `d = deg φ`
(`H/RingSwitch/Reduction.lean:138–139`). Proposal, per the reasoning pattern of
the existing carriers (small fixed arity → named-fields struct; dynamic length →
`Vec` newtype whose constructor establishes the shape invariant):

```rust
pub struct LiftedWitness { z: PolyVec, rho: PolyVec }   // len(z) = μ, len(rho) = n
```

Both fields are `PolyVec`, i.e. **no genuinely new carrier at all**. The `ρ`
choice is the load-bearing one: `hρ` bounds each row by `natDegree ≤ d − 1`,
which is exactly the degree range of a reduced `Rq Φ` representative
(`Rq.natDegree_val_toPoly_lt'`, used at `H/RingSwitch/Reduction.lean:124–126`),
and ArkLib itself reads the rows back and forth with
`rhoAsRq p = Rq.ofFinCoeff Φ (deg φ) p.coeff` — "a change of presentation, not a
reduction" (`:249–253`). So representing `ρ` as `Rq` is faithful for every use
inside `endPieceCheck` (all of which read `.coeff k` for `k < d`, or truncate at
`d`: `rhoDigits`, `H/RingSwitch/RhoDigits.lean:135–137`, and
`rhoDigitsShortCheck`'s `k < Φ.φ.natDegree`, `H/EndPiece/Reduction.lean:112`),
and `hρ` becomes the `Wf`-style shape invariant rather than a new bridge. The
Aeneas privacy caveat applies: the invariant must also travel as a hypothesis on
each `_spec` (`Wf` in `hachi/lean/Ring.lean`).

```rust
pub struct WEvalStatement { t: PolyVec, point: Vec<Ext4>, value: Ext4 }  // len(point) = m₀
```
`WEvalStatement` is a three-field record with no sumcheck data
(`H/Sumcheck/FinalEval.lean:72–78`) — small fixed arity, so a named-fields
struct, straight-line in the extracted model.

### Dependencies and API surface

* **Needs target 3's `liftShortCheck` and target 4's `wTableMleEval`; does *not*
  need target 5.** Confirmed against the pin: `endPieceCheck`
  (`H/EndPiece/Reduction.lean:157–161`) mentions `K.com`, `liftShortCheck`
  (`:144`) and `wTableMleEval` (`H/ZeroCheck/Constraints.lean:348`) and nothing
  from `H/Sumcheck/Rounds.lean` or `RoundPoly.lean`; the statement it consumes
  carries only `(t, point, value)` (`H/Sumcheck/FinalEval.lean:72–78`). **The end
  piece and the sumcheck rounds parallelize** — the `{5 ∥ 6}` edge of
  `STAGE2_SCOPING.md`'s dependency graph is real, and target 5's CMvPolynomial
  problem does not block this one. Nor does target 4's: `wTableMleEval` is on
  the `CMlPolynomialEval` (dense `Vector`) side, not the
  `CMvPolynomial`/`ExtTreeMap` side that § "Erasure catalogue" flags as the one
  no-precedent shape — that shape is reached by `hypercubeSum`,
  `computableRoundPoly`, `honestComputeG` and `finalCheck`'s subterms, none of
  which this target touches.
* **`D` (the lift key) and the challenge point are function inputs, not
  constants.** `hachiLiftCom` takes
  `D : Simple.PublicParams Φ dRows (μ + n·rhoDigitCount q bDig)` as a parameter
  (`H/RingSwitch/Reduction.lean:281–283`) and the composed scheme takes `K`
  itself as a parameter (`H/Correctness.lean:497`, `:568`); `stmt.point` is the
  sumcheck challenge point, arriving on the wire. **Invent no keygen.** Keep the
  `S6` naming discipline: this is `d_key`, distinct from `pp.d_matrix`
  (the Eq. 16 carrier key) — `STAGE2_SCOPING.md` § "Surprises", S6.
* Proposed signatures (matching `STAGE2_SCOPING.md` § "API mapping"):
  ```rust
  pub fn rho_digits_short_check(rho: &PolyVec) -> bool;
  pub fn lift_short_check(w: &LiftedWitness) -> bool;
  pub fn w_table_mle_eval(w: &LiftedWitness, point: &[Ext4]) -> Ext4;
  pub fn end_piece_check(d_key: &PolyMatrix, stmt: &WEvalStatement, w: &LiftedWitness) -> bool;
  pub fn end_piece_prove(w: LiftedWitness) -> LiftedWitness;   // the identity message
  ```
  `bound`, `bDig`, `b`, `m₀`, `μ`, `n`, `δρ` are all `params.rs` consts at the
  composed instantiation (`H/Correctness.lean:254`), so they are not arguments;
  `w_table_mle_eval` may live in `zerocheck.rs` if target 4 lands it first
  (`STAGE2_SCOPING.md` § "API mapping" puts `w_table_mle_eval` there) — in that
  case `endpiece.rs` calls it.

### Correction: where `liftShortCheck` lives

`STAGE2_SCOPING.md` is internally inconsistent about the module for
`liftShortCheck`/`rhoDigitsShortCheck`: § "Scale policies" lists them under
**target 3** ("`liftShortCheck`/`rhoDigitsShortCheck` real"), while § "API
mapping from HachiRuntime" assigns them to **`endpiece.rs`**
(`endpiece.rs` (`lift_short_check`, `end_piece_check`)). The pin settles the
file: both definitions are in `H/EndPiece/Reduction.lean` (`:111`, `:144`), not
in `H/RingSwitch/`. Recommended reading: the API mapping is right about the
*module* (`endpiece.rs`, mirroring the ArkLib file), and target 3's row should be
read as a *scale policy* for those two cases only — whichever target lands them
first, they land in `endpiece.rs`. This is a naming/ownership fix, not a
resizing: target 6 stays `smaller–similar`.
