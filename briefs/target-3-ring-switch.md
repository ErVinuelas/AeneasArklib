# Brief: `ArkLib.Lattices.Ajtai.InnerOuter.{rhoAsRq, rhoDigitAsRq, liftMessage, hachiLiftCom, rhoDigitsShortCheck, liftShortCheck}`  (ArkLib @ `294b3f0b0f46e1485c878a217e9de764855f5915`)

Stage 3 target **3**, the ring-switching link. Rust home: a new `hachi/src/ringswitch.rs`.
Every `file:line` below is in `hachi/.lake/packages/Arklib/ArkLib/` at the rev above, which
is the rev `hachi/lake-manifest.json` records for `Arklib` (`lake-manifest.json:8`). Consumes
`STAGE2_SCOPING.md` §§ "Erasure catalogue", "Ordered target list + scale policies",
"Parameter mapping", "API mapping from HachiRuntime"; corrections to that file are marked ⊗.

Sources: `Commitments/Functional/Hachi/RingSwitch/Reduction.lean:252–300` (the three carriers
plus the commitment), `Commitments/Functional/Hachi/EndPiece/Reduction.lean:111–145` (the two
short checks), with `RingSwitch/RhoDigits.lean` supplying `rhoDigits`/`rhoDigitCount`.

---

## Definition chain

**1. `rhoAsRq` — a quotient row read back as a ring element.** `RingSwitch/Reduction.lean:252`

```
rhoAsRq Φ p = Rq.ofFinCoeff Φ Φ.φ.natDegree p.coeff
```

Unfolds to `Rq.mk Φ (CPolynomial.ofFinCoeff N c)` (`Data/Lattices/CyclotomicRing/Rq.lean:269`),
i.e. `⟨Φ.reduce (∑ k ∈ range N, monomial k (c k)), _⟩` — `Rq.mk` at `Rq.lean:96`,
`Φ.reduce p = p.modByMonic Φ.φ` at `CyclotomicRing/Core/Basic.lean:67`,
`CPolynomial.ofFinCoeff N c = ∑ k ∈ range N, monomial k (c k)` at
`ToCompPoly/Univariate/Basic.lean:294`. **The `reduce` is provably a no-op here**:
`Rq.ofFinCoeff_coeff` (`Rq.lean:271`) discharges it from `N ≤ deg φ`, which holds with
equality (`N = Φ.φ.natDegree`). ArkLib's own docstring calls this "a change of presentation,
not a reduction" (`Reduction.lean:249–250`).

**2. `rhoDigitAsRq` — entry `j` of the quotient block.** `RingSwitch/Reduction.lean:259–261`

```
rhoDigitAsRq Φ b ρ j = rhoAsRq Φ (rhoDigits Φ b (ρ (finProdFinEquiv.symm j).1)
                                              ((finProdFinEquiv.symm j).2 : ℕ))
```

with `rhoDigits Φ b ρ u = CPolynomial.ofFinCoeff Φ.φ.natDegree (fun k => balancedDigit b
(rhoDigitCount q b) (ρ.coeff k) u)` (`RingSwitch/RhoDigits.lean:135–136`),
`balancedDigit b digits c e = ((Nat.digits b (c + balancedShift b digits).val).getD e 0 : ZMod q)
− ((b/2 : ℕ) : ZMod q)` (`RhoDigits.lean:79–81`), and
`rhoDigitCount q b = Nat.clog b q` (`RhoDigits.lean:66`).

The flat index splits digit-major within each row: `j ↦ (j / δ, j % δ)`, "the same flattening
the gadget matrix uses (`gadgetEntry_finProdFinEquiv`)" (`Reduction.lean:255–258`), which is
exactly the layout `PolyVec.flattenBlocks` uses (`Data/Lattices/Vectors.lean:55–57`) and which
`hachi/src/gadget.rs:41` already implements as flat index `digits·i + e`.

**The two `ofFinCoeff` layers collapse.** Composing 1 and 2, and rewriting with
`rhoDigits_coeff` (`RhoDigits.lean:141–144`) and `Rq.ofFinCoeff_coeff` (`Rq.lean:271`):

```
(rhoDigitAsRq Φ b ρ j).1.coeff k = if k < d then balancedDigit b δ ((ρ (j/δ)).coeff k) (j%δ) else 0
```

so the whole of 1+2 is **one `d`-iteration loop of `balanced_digit_at`**, with no intermediate
polynomial. Both rewrite lemmas are already proved at the pin; nothing has to be invented.

**3. `liftMessage` — the committed vector.** `RingSwitch/Reduction.lean:273–275`

```
liftMessage Φ b w = Fin.append w.z (rhoDigitAsRq Φ b w.ρ)
    : PolyVec (Rq Φ) (μ + n * rhoDigitCount q b)
```

`Fin.append` is concatenation; `Fin.append_left`/`_right` (used at `Reduction.lean:337, 341`)
are the two projection lemmas. `w : LiftedWitness Φ μ n` is
`Lift.LiftedWitness (ZMod q) (Rq Φ) Φ.φ.natDegree μ n` (`Reduction.lean:138–139`), a structure
`⟨z : Fin μ → Rq Φ, ρ : Fin n → CPolynomial (ZMod q), hρ : ∀ i, (ρ i).toPoly.natDegree ≤ d − 1⟩`
(`ProofSystem/RingSwitching/Lift/Reduction.lean:80–86`).

**4. `hachiLiftCom` — the Ajtai lift commitment.** `RingSwitch/Reduction.lean:281–285`

```
(hachiLiftCom Φ bound bDig D).TCom = Simple.Commitment Φ dRows
(hachiLiftCom Φ bound bDig D).com w = Simple.commit Φ D (liftMessage Φ bDig w)
```

`Simple.commit Φ A s = A *ᵥ s` (`Commitments/Ordinary/Ajtai/Simple/Scheme.lean:38–40`);
`matVecMul A v = fun i => dot (A i) v` (`Data/Lattices/Vectors.lean:87–88`);
`dot u v = (List.ofFn fun i => u i * v i).sum` (`Vectors.lean:83–84`); and `*` on `Rq Φ` is
`Mul (Rq Φ)` = `Rq.mk Φ (a.1 * b.1)` (`Rq.lean:110`) = `Φ.reduce (a.1 * b.1)`
(`Rq.lean:96`, `Core/Basic.lean:67`) — the CompPoly `CPolynomial` product followed by
`modByMonic`, i.e. the schoolbook negacyclic convolution `hachi/src/ring.rs:286` implements.
Two `rfl` unfolding lemmas exist and should be used rather than re-derived:
`hachiLiftCom_TCom` (`Reduction.lean:291–293`, `TCom = CarrierCom Φ dRows`) and
`hachiLiftCom_com` (`Reduction.lean:297–300`).

Instantiated for the chain by `nonrecursiveLiftCom P D = hachiLiftCom 𝓜(q,α) P.γ P.bZero D`
(`Hachi/Concrete.lean:59–62`), i.e. `bound := P.γ`, `bDig := P.bZero`.

**5. `rhoDigitsShortCheck`.** `EndPiece/Reduction.lean:111–113`

```
rhoDigitsShortCheck Φ bound bDig ρ =
  decide (∀ i, ∀ u < rhoDigitCount q bDig, ∀ k < Φ.φ.natDegree,
            ((rhoDigits Φ bDig (ρ i) u).coeff k).valMinAbs.natAbs ≤ bound)
```

Decides `RhoDigitsShort` (`RingSwitch/Reduction.lean:161–163`) exactly
(`rhoDigitsShortCheck_eq_true_iff`, `EndPiece/Reduction.lean:118–127`); the `k ≥ d` tail is
discharged by `rhoDigits_coeff`'s truncation. `valMinAbs.natAbs` is the centered absolute
value — the spec of `hachi/src/commit.rs:75–88`'s `centered_abs`.

**6. `liftShortCheck`.** `EndPiece/Reduction.lean:144–145`

```
liftShortCheck Φ bound bDig w =
  decide (vecLInftyNorm Φ w.z ≤ bound) && rhoDigitsShortCheck Φ bound bDig w.ρ
```

`vecLInftyNorm Φ z = (univ : Finset (Fin cols)).sup (fun i => Rq.lInftyNorm Φ (z i))` and
`Rq.lInftyNorm a = (range Φ.φ.natDegree).sup (fun k => (a.1.coeff k).valMinAbs.natAbs)`
(`Data/Lattices/CyclotomicRing/NormBounds/Basic.lean:125–126` and `:117–118`). Decides
`liftShort Φ bound bDig w = vecLInftyNorm Φ w.z ≤ bound ∧ RhoDigitsShort Φ bound bDig w.ρ`
(`RingSwitch/Reduction.lean:211–212`) exactly (`liftShortCheck_eq_true_iff`,
`EndPiece/Reduction.lean:149–152`).

**Consumer, for context only.** `endPieceCheck` (`EndPiece/Reduction.lean:157–161`) is
`(K.com w == stmt.t) && liftShortCheck … && (wTableMleEval … == stmt.value)`; the `==` is the
explicit `[BEq K.TCom]` binder that `STAGE2_SCOPING.md` § "Decision 3" flagged. `wTableMleEval`
is target 6's, not this one's.

### Which bound each check uses — asked for explicitly

| Check | Bound it tests | Kind | Value in the chain |
|---|---|---|---|
| `liftShortCheck` conjunct 1 | `bound` = `P.γ` (`Concrete.lean:62`) | `ℓ∞` over `Rq` coefficients | `CHAIN_GAMMA` = `bZero − 1` = **15** |
| `liftShortCheck` conjunct 2 = `rhoDigitsShortCheck` | the same `bound` = `P.γ` | `ℓ∞` over centered digit coefficients | **15** |
| — | — | — | — |
| *not reached:* `BETA_SQ` | squared-`ℓ₂`, weak-opening relation only | `commit::verify_weak` | see § Parameters |
| *not reached:* `params.rs GAMMA = 16` | weak-opening `γ̄ = b` | `commit::verify_weak` | see § Parameters |

`P.γ = P.bZero − 1` is forced (`HonestChain.pinned_of_soundness_orientations`,
`HonestChain.lean:186–193`) and realized at `ofPinnedDigitBase b`, which sets
`γ := b − 1`, `bZero := b` (`HonestChain.lean:169–180`). So at Fig. 9's `b = 16`,
**bound = 15 and bDig = 16**. Neither check touches a squared-`ℓ₂` bound at all.

---

## Parameters

The brief is computed at `hachi/src/params.rs` as it stands, plus the four new consts this
target needs. Split per `NOTES.md` § "Chosen parameters" and `STAGE2_SCOPING.md`
§ "Parameter mapping".

**Existing (`hachi/src/params.rs`)**

| Const | Value | Split | Role here |
|---|---|---|---|
| `Q` | `2^32 − 99` = 4 294 967 197 | **pinned** (cpoly `Fp`, `params.rs:41–51`) | modulus; `q < 2^32` is the headroom base |
| `RING_LOG_DEGREE` / `RING_DEGREE` | 10 / 1024 (α = 10, `d = deg φ`) | **pinned** ([NOZ26] Fig. 9, `params.rs:66–88`) | width of every digit block and of `Rq` |
| `GADGET_BASE` | 16 | **pinned** (`params.rs:90–97`) | `= P.b = P.bZero` at `ofPinnedDigitBase 16` |
| `GADGET_DIGITS` | 8 | **pinned**, and `q ≤ b^8` forces ≥ 8 (`params.rs:99–113`) | `= δ P = messageDigits = innerDigits` |
| `MESSAGE_ROWS`, `BLOCKS` | 1024, 1024 (`2^m`, `2^r`, m = r = 10) | **pinned** (`params.rs:114–147`) | enter `μ₀` |
| `INNER_ROWS`, `OUTER_ROWS` | 1, 1 (`n_A`, `n_B`) | **pinned** (`params.rs:126–140`) | enter `μ₀`, `n₀` |
| `ML_VARS_LOW`/`_HIGH` | 10 / 10 | **derived** (`params.rs:208–225`) | the `m`, `r` of `rlinCols` |

**New, this target's (from `STAGE2_SCOPING.md` § "Parameter mapping"; verified against the pin)**

| Const | Value | Split | Derivation, verified |
|---|---|---|---|
| `D_ROWS` (`dRows`) | 1 | **pinned** (Fig. 9 `n_D`, free in ArkLib) | `dRows` is a free `{dRows : ℕ}` at `Reduction.lean:281` |
| `RHO_DIGIT_COUNT` (`δρ`) | **8** | **derived** | `rhoDigitCount q bZero = Nat.clog 16 q` (`RhoDigits.lean:66`); `16^7 = 268 435 456 < q ≤ 16^8 = 4 294 967 296` |
| `RLIN_COLS` (`μ₀`) | **81 920** | **derived** | `rlinCols 1 8 8 8 10 10 = 2^10·8 + (2^10·(1·8) + 2^10·8·8) = 8192 + 8192 + 65 536` (`RingSwitch/Rlin.lean:153–154`, notation at `Concrete.lean:48–50`) |
| `RLIN_ROWS` (`n₀`) | **5** | **derived** | `rlinRows 1 1 1 = 1 + (1 + (1 + (1 + 1)))` (`Rlin.lean:158–159`, notation at `Concrete.lean:51`) |
| `LIFT_COLS` | **81 960** | **derived** | `μ₀ + n₀·δρ = 81 920 + 5·8`; the width at `Reduction.lean:282` / `Concrete.lean:60` |
| `CHAIN_GAMMA` (`P.γ`) | **15** | **derived** | `γ = bZero − 1` (`HonestChain.lean:169–180, 186–193`) |
| `B_ZERO` (`P.bZero`) | 16 | **derived** = `b` | `ofPinnedDigitBase` sets `bZero := b` (`HonestChain.lean:171`) |

`BALANCED_SHIFT = 2 290 649 224` and `HALF_BASE = 8` are **target 1's**
(`STAGE2_SCOPING.md` § "Decision 4", verified there against `Gadget/Core.lean:133, 148–164`);
this target consumes `balanced_digit_at` and adds nothing to the digit layer.

### `BETA_SQ` and its exponent τ — contested, and **this target does not reach it**

`BETA_SQ` is written **symbolically** here: it is `quadEvalBetaSq γ b τ d m δ`
(`QuadEval/Soundness.lean:106`, a formal-parameter τ), a **squared-`ℓ₂`** bound belonging to the
*weak-opening* relation and checked only by `commit::verify_weak`. The user has chosen τ = 4; a
parallel session is implementing that; the tree at the time of writing shows the τ = 8 literal
(`hachi/src/params.rs:168–206`). No number is asserted here, and none is needed: as the table
in § Definition chain shows, **`liftShortCheck` and `rhoDigitsShortCheck` test `ℓ∞ ≤ P.γ = 15`,
not `βSq`, and not `params.rs`'s `GAMMA = 16` either** (that is the weak-opening `γ̄ = b`,
`params.rs:149–166`; `STAGE2_SCOPING.md` F1/S7's two-gammas flag applies verbatim). So the
contested value **does not reach this target's semantics**, and the equivalence proofs for all
six definitions can be written today without waiting on it.

One indirect line, as requested. τ enters this target only as `zDigits` inside
`rlinCZ messageDigits zDigits m = 2^m · messageDigits · zDigits` (`Rlin.lean:166`), hence in
`μ₀` and so in `LIFT_COLS` — the width of `D` and of `liftMessage`:

* **τ = zDigits = 8** (the tree's reading, and the one the pin forces on the composed path —
  `Correctness.lean:509–516` instantiates `messageDigits = innerDigits = zDigits = δ P` and
  discharges `hqz : q ≤ b^zDigits` by `Nat.le_pow_clog`, which **fails at 4** since
  `16^4 = 65 536 ≪ q`): `μ₀ = 81 920`, `LIFT_COLS = 81 960`.
* **If τ = 4 were adopted as `zDigits`**: `μ₀ = 8192 + 8192 + 1024·8·4 = 49 152`,
  `LIFT_COLS = 49 192` — a 40% narrower lift key. Same order of magnitude, **same REDUCED
  verdict** for `lift_commit`, no change to any semantics claim in this brief.
* **If τ = 4 is adopted only inside the weak-opening `BETA_SQ` literal** (a
  `verify_weak`-local reading): this target is **entirely untouched**.

`δρ = rhoDigitCount q bZero = Nat.clog 16 q = 8` is a **different quantity** from `zDigits`
(quotient digits vs response digits) that happens to equal 8 too, so the `n₀·δρ = 40` tail of
`LIFT_COLS` is fixed regardless of the τ outcome. ⊗ Add this pair to
`STAGE2_SCOPING.md` F3's value-**8** collision row, which currently lists
`GADGET_DIGITS`/`Z_DIGITS`/`RHO_DIGIT_COUNT` without noting that `Z_DIGITS` is the *only*
τ-sensitive one of the three.

### `D` is a caller input, not a constant, and there is no keygen to invent

Verified at the pin, three places:

* `hachiLiftCom` takes `(D : Simple.PublicParams Φ dRows (μ + n * rhoDigitCount q bDig))` as an
  explicit argument (`Reduction.lean:281–282`).
* Its section note **"Why the lift needs its own key"** explains that `pp.dMatrix` is the wrong
  width — `PublicParamsD.dMatrix` has `blocks * messageDigits = rlinCW` columns, the carrier
  slice `ŵ` alone — and closes: *"So the key is taken as a parameter at the matching width; a
  full treatment would sample it in `keygen` alongside `D`, which needs a new `PublicParamsD`
  field."* (`Reduction.lean:235–246`.)
* It stays an explicit argument **all the way through `Concrete.lean`**: `nonrecursiveLiftCom`
  (`Concrete.lean:60`), `hachiNonrecursiveConcrete` (`Concrete.lean:84`), and even the
  correctness corollary (`Concrete.lean:113`) each take `D` as a parameter. `keygen`
  (`Correctness.lean:509–511`) samples `pp` and never `D`.
  `moduleSIS_relation_of_mem_Collision`'s ⚠ Scope note says it outright: *"`D` is a parameter
  of `hachiLiftCom` — `keygen` does not sample it alongside the inner-outer commitment's own
  key"* (`Reduction.lean:421–425`).

**Consequence for the Rust signature.** `D` is an argument of `lift_commit`, never a `params.rs`
const and never something `ringswitch.rs` samples:

```rust
/// spec: `hachiLiftCom … D |>.com w`, `RingSwitch/Reduction.lean:281`
pub fn lift_commit(d_key: &PolyMatrix, w: &LiftedWitness) -> PolyVec
```

with the shape invariant `d_key.rows() == params::D_ROWS && d_key.cols() == params::LIFT_COLS`
travelling as a hypothesis on the `_spec` (the `Wf` pattern of `hachi/lean/Ring.lean`), exactly
as `STAGE2_SCOPING.md` S6 prescribes: **`pp.d_matrix`** (the Eq. 16 carrier key, keygen-sampled,
`RLIN_CW = 8192` wide) and **`d_key`** (this one, `D_ROWS × LIFT_COLS = 1 × 81 960`) are two
different objects and must keep two different names. ✓ S6 confirmed against the pin. No `keygen`
is added to this crate by this target.

---

## Semantics risks

### No new width is introduced

Every accumulation in this target is already-reduced-`Rq` arithmetic or a bounded comparison:

* `Fp` is `Fp(u64)` (`cpoly/src/field.rs:72`) with `Red u := u.val < q`, `q < 2^32`
  (`hachi/lean/Field.lean` header § "What a spec says"). The commit's inner loop is
  `Rq::mul` then `Rq::add` (`hachi/src/linalg.rs:197–198`), and `Rq::add` reduces, so the
  accumulator never grows: the existing bound — a product of two reduced words is at most
  `(q−1)^2 < 2^64`, a sum of two below `2^33` — carries over unchanged. **`lift_commit` needs
  no new headroom argument.**
* `centered_abs` returns `≤ q/2 = 2 147 483 598 < 2^31` (`hachi/src/commit.rs:75–88`).
  `l_infty_norm`/`vec_l_infty_norm` are **maxima, not sums** (`commit.rs:115–127, 174–186`), so
  no accumulation and no overflow at any vector length — which is why `liftShortCheck` can be
  `u64` where `vec_l2_norm_sq` had to be `u128`. Both comparisons are against `bound = 15`.
* `balanced_digit_at` is a field add of `BALANCED_SHIFT`, a `digit_at` (repeated `/16` on a
  word `< q`, then `% 16`), and a field sub of `HALF_BASE` — all inside `q`. Target 1 owns the
  headroom argument; the trap it records applies here too: **the shift must be a field add
  (mod q), never a raw `u64` add** (`STAGE2_SCOPING.md` § "Decision 4", Traps).
* Index arithmetic: `δ·i + u ≤ 39`, `μ₀ + j ≤ 81 959`, `LIFT_COLS · d = 83 927 040`. All
  comfortably inside `usize`; the last is the quantity that pins `m₀ = 27`
  (`2^26 = 67 108 864 < 83 927 040 ≤ 2^27`, `STAGE2_SCOPING.md:247`) ✓.

### The reduction that must **not** happen

`rhoAsRq` is `Rq.ofFinCoeff`, whose unfolding contains `Φ.reduce = modByMonic Φ.φ`
(`Rq.lean:96`, `Core/Basic.lean:67`). A translation that performs a reduction would be *wrong*
in cost and merely equal in value. The licence to skip it is `Rq.ofFinCoeff_coeff`
(`Rq.lean:271–280`), whose side condition `(N : WithBot ℕ) ≤ Φ.φ.toPoly.degree` holds with
equality at `N = Φ.φ.natDegree` — and `hachi/lean/RqBridge.lean:112` (`N_le_degree`) has
already proved precisely that instance. So the obligation is discharged by an existing lemma,
not by an assumption; state it, do not assume it.

### `rhoDigitsShortCheck` is provably constant `true` at these constants

`DigitBaseOk q bound bDig` (`RingSwitch/Reduction.lean:172–181`) holds at
`(q, 15, 16)`: `one_lt : 1 < 16` ✓, `le_half : 16 ≤ q/2 = 2 147 483 598` ✓,
`radius_le : 16/2 = 8 ≤ 15` ✓. Therefore
`rhoDigitsShortCheck_eq_true_of_digitBaseOk` (`EndPiece/Reduction.lean:138–141`) applies, and
ArkLib states the consequence itself: *"**The digit conjunct of `liftShortCheck` always passes**
at an admissible digit base … So at the chain's parameters `liftShortCheck` is effectively the
`z`-norm check alone."* (`EndPiece/Reduction.lean:130–137.)

This is the sharpest exactness trap on this target, and it is stronger than the usual
"a corpus inside the bound tests nothing" (`arklib-analyze` § 3): the bound
`⌊bDig/2⌋ = 8 ≤ 15 = bound` holds **for an arbitrary `ρ`, with no shortness hypothesis at all**
(`rhoDigitsShort_of_half_le`, `Reduction.lean:190–195`), so **no input whatsoever — honest or
adversarial — can make `rho_digits_short_check` return `false` at Fig. 9 constants.** The
`false` branch of that conjunct is unreachable at real consts. Three consequences to write down
rather than paper over:

1. Its semantics test can only pin the `true` verdict and the *computation*; it must say so.
   Exercising the `false` path needs an inadmissible base (`bDig > 2·bound + 1`), which a
   consts-hardwired Rust cannot express — so it is a **REDUCED-instantiation test only**, or a
   Lean-level check.
2. `liftShortCheck`'s `false` path is reachable — via the `z` conjunct — so the composed check
   is still testable in both directions. Test the *pair*, not the digit conjunct alone.
3. It makes "just return `true`" a valid `Foo.opt` at these constants. It is nonetheless the
   wrong champion; see § Strategy candidates, candidate 6.

### Partiality and erasure

* `rhoDigitCount q b = Nat.clog b q` (`RhoDigits.lean:66`) is **not translatable**
  (`STAGE2_SCOPING.md` § "Minor variants") → the `RHO_DIGIT_COUNT = 8` literal, with its
  Check.lean entry through the `Nat.clog_le_iff_le_pow` + `omega` pattern rather than
  `simp`/`decide` at `q ≈ 4.3·10^9` (`STAGE2_SCOPING.md` F6).
* `finProdFinEquiv.symm j` needs `n · δρ > 0`; at `5 · 8 = 40` ✓. Its `.symm` **does not**
  cancel against a `finProdFinEquiv` here (unlike `wTable`'s consumers,
  `STAGE2_SCOPING.md` § "Shape-list corrections" 2) — it is a genuine `j ↦ (j/δ, j%δ)` split,
  and the Rust must do that division. Precedented: `gadget_entry` already does
  `j / digits` / `j % digits` (`hachi/src/gadget.rs:121–128`).
* `Fin.append` erases to concatenation; the `Fin μ`/`Fin (n·δ)` case split becomes an
  `if j < MU0` in the fused form. `Fin.append_left`/`_right` are the proof handles
  (`Reduction.lean:337, 341`; `RingSwitch/Rlin.lean:96–100, 125–138` shows the house style for
  append-splitting a `matVecMul`, in the *row* direction — the *column* analogue is what
  candidate 1 needs and is not at the pin).
* **`hρ` is not needed by this target.** `LiftedWitness.hρ`
  (`ProofSystem/RingSwitching/Lift/Reduction.lean:85–86`) is a proof field; every definition
  here truncates at `deg φ` on its own (`rhoDigits` by `ofFinCoeff`, `rhoAsRq` by
  `ofFinCoeff_coeff`, `Rq.lInftyNorm` by `range Φ.φ.natDegree`), so none of the six `_spec`s
  needs `hρ` as a hypothesis. It becomes the **representation invariant** of the Rust `ρ`
  carrier instead (see § Representation); it *is* needed by `rhoDigits_reconstruct`
  (`RhoDigits.lean:178–179`), i.e. by targets 4 and 6, not here.
* `Rq::equals` / `PolyVec::equals` (`hachi/src/ring.rs:157`, `linalg.rs:111`) route through
  `Fp::to_u64` so exactly one notion of equality exists per type; `endPieceCheck`'s
  `[BEq K.TCom]` binder lands on that. `hachiLiftCom_TCom` says `TCom = CarrierCom Φ dRows`
  **by `rfl`** (`Reduction.lean:291–293`), so the commitment is a `PolyVec` of `D_ROWS = 1` ring
  elements and `PolyVec::equals` is the whole of it — no new `BEq`.

### The recompute trap in `rhoDigitsShortCheck`

The spec's quantifier order is `(i, u, k)` with `rhoDigits Φ bDig (ρ i) u` **inside** the `∀ k`
(`EndPiece/Reduction.lean:112–113`). A literal-looking translation that writes
`centered_abs(rho_digit(rho.get(i), u).coeff(k))` inside the `k` loop rebuilds a whole
1024-wide digit row per coefficient: `n₀·δρ·d·d = 41 943 040` digit-row builds,
`≈ 4.3·10^10` digit evaluations — **1024× the necessary work**, and it would silently pass every
semantics test. Hoisting the row out of the `k` loop is the trivial-grade form; the fused form
(candidate 3) removes the row entirely.

---

## Cost model

Notation, all fixed by § Parameters: `d = 1024`, `μ₀ = 81 920`, `n₀ = 5`, `δρ = 8`,
`LIFT_COLS = 81 960`, `dRows = 1`, `Fp = 8 bytes` (`cpoly/src/field.rs:72`).

The house's own arithmetic for the dominant term is already written down and is used verbatim
rather than re-derived: *"one schoolbook `ring::mul` at `RING_DEGREE = 1024` is `2^20` field
operations (~2–4 ms) … anything that multiplies through the inner matrix `A` (`1 × 8192`) pays
≥ 8192 ring muls (~tens of seconds)"* — `hachi/benches/exclusions.toml:85–89`. The only
in-repo measurement (`NOTES.md` § "The first benchmark run…", `ring/mul` ≈ 8.51 µs at the old
`N = 64`) is sizing information at a superseded shape and is **not** a baseline; the external
anchor in `logs/paper-impl/README.md` (reference NTT ring-mul ≈ 36 µs at `d = 1024`,
`ring::mat_mul_vec` ≈ 5.31 ms per call) is likewise an anchor, not a target. No percentage is
predicted below.

| Op (`<module>/<case>`) | Ring muls | Ring adds | `balanced_digit_at` | `centered_abs` | Peak `Fp` bytes | Dominant term |
|---|---|---|---|---|---|---|
| `ringswitch/rho_digit_as_rq` (one entry) | 0 | 0 | `d` = 1 024 | 0 | 8 KiB | the digit loop |
| `ringswitch/lift_message` | 0 | 0 | `n₀·δρ·d` = 40 960 | 0 | ~1.3 GiB in + out | **`Rq::copy` of the `z` block** |
| `ringswitch/lift_commit` | `dRows·LIFT_COLS` = **81 960** | 81 960 | 40 960 | 0 | ~1.3 GiB (`d_key` + message) | **`ring::mul`** |
| `ringswitch/rho_digits_short_check` | 0 | 0 | `n₀·δρ·d` = 40 960 | 40 960 | 8 KiB scratch | the digit loop |
| `ringswitch/lift_short_check` | 0 | 0 | 40 960 | `μ₀·d` = **83 886 080** | 640 MiB (`z`, resident) | the `z` scan |

**`lift_commit` is the whole target's cost.** 81 960 ring muls × `2^20` coefficient
mult-and-reduce = **8.59·10^10** field operations. Scaling `exclusions.toml:88`'s own anchor
(8192 muls ≈ 25 s) linearly gives **≈ 250 s ≈ 4 min per criterion iteration**; the ~2–4 ms/mul
figure in the same comment brackets it at 165–330 s. Ten samples is ~40–55 minutes for one
case. Everything else in the table is ≤ 100 ms and invisible beside it — the norms literally
so, as the skill's cost-model guidance predicts.

**A second, independent wall: allocation width.** `d_key` at `1 × 81 960` is
`81 960 · 1024 · 8 B = 671 416 320 B ≈ 640 MiB`; `liftMessage`'s output is the same;
`w.z` alone is `81 920 · 1024 · 8 = 671 088 640 B = 640 MiB` exactly. So one `lift_commit` call
needs **≈ 1.3 GiB resident** before any multiplication, and `lift_message` is
640 MiB of `memcpy` producing a second 640 MiB. This is not a `ring::mul` cost and no
multiplication champion removes it.

### Scale policy (fixed by `STAGE2_SCOPING.md` § "Scale policies", row 3, with one refinement)

`STAGE2_SCOPING.md:539` reads: *semantics tests* "real consts except `lift_commit` (81960-wide)
→ REDUCED"; *bench cases* "REDUCED for `lift_commit`; `liftShortCheck`/`rhoDigitsShortCheck`
real". Applied, with the mandatory written note per case:

| Case | Policy | Note the case must carry, and the removal condition |
|---|---|---|
| `ringswitch/lift_commit` | **REDUCED** | *"`dRows × LIFT_COLS = 1 × 81 960` schoolbook `ring::mul`s at `d = 1024` — `8.59·10^10` field ops, ≈ 4 min/iteration by `exclusions.toml`'s own 8192-mul ≈ 25 s anchor — plus ≈ 1.3 GiB of `Fp` for `d_key` and the message. **Removal condition: a sub-quadratic `ring::mul` champion landing** (the `exclusions.toml` Fig. 9 policy exception). This is a width-driven wall and the multiplication champion **does** remove it — unlike targets 4/5's `m₀ = 27` cube wall, which no multiplication speedup touches (`STAGE2_SCOPING.md:544–548`). Do not conflate the two."* |
| `ringswitch/lift_message` | ⊗ **REDUCED for the bench**, real consts for the semantics test | *"640 MiB `memcpy` of the `z` block into a second 640 MiB vector, ≈ 1.3 GiB peak; a criterion run measures the allocator, not the operation. **Removal condition: a streaming/in-place `lift_commit` champion (candidate 1) that removes the materialized concatenation — NOT the `ring::mul` champion, and NOT `m₀`.** A third, distinct wall: memory, not multiplication."* |
| `ringswitch/rho_digit_as_rq` | real consts | one 1024-iteration digit loop; birth case per `rust-bench` |
| `ringswitch/rho_digits_short_check` | real consts | 40 960 digit evaluations, ≈ tens of µs–low ms. Test must record that the verdict is **provably constant `true`** at these consts (§ Semantics risks) |
| `ringswitch/lift_short_check` | real consts | ⊗ 83 886 080 `centered_abs` ≈ 100 ms and **640 MiB of `z` resident**: feasible, but the input must be built once *outside* the timed region (`iter_batched`-style setup), or the case measures construction |

⊗ **Two refinements to `STAGE2_SCOPING.md:539`**, offered as strengthenings rather than
contradictions: (a) the row names only `lift_commit` as width-driven, but the *same* 81 960
width makes `lift_message` a 1.3 GiB allocation-bound case whose removal condition is a
*different* champion — so target 3 has **three** walls (`ring::mul` width, allocation width,
and no `m₀` wall at all), and the scale-policy paragraph's warning against conflating walls
needs the third name; (b) `liftShortCheck` at real consts is feasible but carries 640 MiB of
resident `z`, which the row does not mention and which a bench author will otherwise put inside
the timed region.

---

## Strategy candidates

Pointers only; the strategies live in their skills.

1. **`opt-inplace-buffers` — fuse `liftMessage` into `hachiLiftCom`, never materialize the
   concatenation.** `liftMessage` produces an output the size of its input (81 960 `Rq`,
   640 MiB) that `hachiLiftCom` consumes exactly once (`Reduction.lean:285`). Split the single
   `dot` of length 81 960 into `∑_{j<μ₀} D[i][j]·z[j] + ∑_{j<n₀δρ} D[i][μ₀+j]·rhoDigitAsRq…`,
   accumulating in place: kills 640 MiB of `memcpy` and 640 MiB of peak. Proof handles:
   `hachiLiftCom_com` (`Reduction.lean:297–300`), `dot`/`matVecMul` unfolding
   (`Vectors.lean:83–88`), `Fin.append_left`/`_right` and `Fin.sum_univ_add`; the row-direction
   precedent `matVecMul_append_rows` is at `Rlin.lean:125–138`, the column analogue is not at
   the pin and is this candidate's lemma. **Top candidate**, and the removal condition for
   `lift_message`'s bench note.
2. **`opt-inplace-buffers` — collapse the two `ofFinCoeff` layers in `rhoDigitAsRq`.** `rhoDigits`
   builds a `CPolynomial` by `ofFinCoeff` (`RhoDigits.lean:135`, itself a 1024-term monomial
   sum, `ToCompPoly/Univariate/Basic.lean:294`) which `rhoAsRq` then re-reads coefficientwise
   through a second `ofFinCoeff` plus a provably-vacuous `reduce`. One `d`-loop suffices.
   Both rewrite lemmas already exist: `rhoDigits_coeff` (`RhoDigits.lean:141–144`) and
   `Rq.ofFinCoeff_coeff` (`Rq.lean:271`). Cheap, certain, and it is what makes the Rust body
   trivial-grade.
3. **`opt-inplace-buffers` — the same fusion inside `rhoDigitsShortCheck`.** The check needs a
   digit *coefficient*, `balancedDigit b δρ ((ρ i).coeff k) u`, not a digit *polynomial*; the
   spec's quantifier nesting invites a 1024× recompute (§ Semantics risks). Same two lemmas as
   candidate 2. Note for Stage 5, not for this target: on the honest path `lift_message` and
   `rho_digits_short_check` compute the **same** 40 digit rows, so a shared precompute is
   available at the composed layer.
4. **`opt-algo-swap` — early-exit `vecLInftyNorm ≤ bound`.** `liftShortCheck` computes a full
   `Finset.sup` over `μ₀·d = 83 886 080` centered coefficients and *then* compares
   (`NormBounds/Basic.lean:117–126`). The `Bool` is unchanged by a scan that returns `false` on
   the first coefficient exceeding `bound = 15`. Wins on the rejecting path only — honest
   inputs still pay the full scan — so low priority, but it is the only algorithmic content in
   the checks.
5. **`opt-word-arith` — test the bound on the raw word.** `centered_abs(c) ≤ 15` is
   `c ≤ 15 ∨ c ≥ q − 15` on the `u64` (`commit.rs:75–88`'s two branches collapse against a
   comparison), removing a branch and a subtraction from an 83.9 M-iteration loop. No new
   width, no representation change — `Fp`/`Ext4` stay cpoly's
   (`hachi/src/lib.rs`, README § "The field layer comes from cpoly").
6. **(no skill yet) — dead-branch elision, and why it should be *declined*.** At these consts
   `rhoDigitsShortCheck` is provably `fun _ => true`
   (`rhoDigitsShortCheck_eq_true_of_digitBaseOk`, `EndPiece/Reduction.lean:138–141`), so
   `Foo.opt := true` with a proved `opt_eq_spec` is a legitimate, and maximal, optimization —
   it deletes 40 960 digit evaluations. **Do not offer it as a champion without explicit user
   sign-off**: it removes a range check from the verifier, and any later parameter move
   (`bZero > 2·γ + 1`, or `γ < ⌊bZero/2⌋`) breaks the theorem that licensed it while the code
   keeps saying `true`. Recommended instead: keep the loop and record the identity as a
   `lean/Check.lean` line, where a parameter move fails loudly.
7. **`opt-algo-swap` on `ring::mul` — not this target's work, but its gate.** 81 960 of the
   81 960 muls in `lift_commit` are `hachi/src/ring.rs:286`'s schoolbook convolution. The
   specification flags the direction itself: `CyclotomicRing/Core/Basic.lean:72` carries
   *"TODO add proper NTT multiplication here"*, and `hachi/src/ring.rs:37–41` records that the
   schoolbook form is deliberate and that an NTT carries an equivalence obligation of its own.
   Target 3's `lift_commit` bench case is gated on that champion; nothing in `ringswitch.rs`
   should try to pay it locally.

**Not applicable, and why** (so no agent spends effort there): `opt-tailrec-loops` — no
structural or non-tail recursion appears anywhere in the six definitions; the only recursion is
the `List.ofFn … |>.sum` inside `dot`, and `opt-list-to-array` is **already paid** by the
existing `PolyVec::dot` accumulator loop, whose docstring records the List-vs-fold discrepancy
and the commutativity/associativity argument the `_spec` needs
(`hachi/src/linalg.rs:176–202`). Reuse it; do not re-open it.

---

## Representation

### Precedents — the audit's claim, verified

`STAGE2_SCOPING.md:516` says target 3 is "unchanged; all shapes precedented (`flatten_blocks`,
`gadget_entry`, `vec_l_infty_norm`)". **Verified, and the mapping is tighter than the audit
claims:**

| ArkLib shape | Rust precedent | Verified |
|---|---|---|
| `finProdFinEquiv.symm j` → `(j/δ, j%δ)` | `gadget_entry` (`hachi/src/gadget.rs:121–128`: `j / digits == i`, `base_pow(j % digits)`); layout stated at `gadget.rs:41` | ✓ same flattening ArkLib names at `Reduction.lean:257` (`gadgetEntry_finProdFinEquiv`) |
| block-major concatenation | `flatten_blocks` (`hachi/src/linalg.rs:274–288`) | ✓ shape-identical; note `liftMessage` is `Fin.append` (two *unequal* widths, 81 920 + 40), not `flattenBlocks` (equal widths), so it is `flatten_blocks`'s shape, not its call |
| `vecLInftyNorm Φ w.z ≤ bound` | `vec_l_infty_norm` (`hachi/src/commit.rs:174–186`) + `l_infty_norm` (`:115–127`) + `centered_abs` (`:75–88`) | ✓ **reused verbatim**, zero new code for `liftShortCheck`'s first conjunct |
| `Rq.ofFinCoeff Φ (deg φ) c` | `Rq::from_coeffs` (`hachi/src/ring.rs:110–124`), spec-cited at `Rq.lean:269` with `from_coeffs_spec` already proved (`hachi/lean/RqBridge.lean:335`) | ✓ |
| `Simple.commit Φ D s = D *ᵥ s` | `PolyMatrix::mat_vec_mul` (`hachi/src/linalg.rs:238–247`), which already cites `Ajtai/Simple/Scheme.lean:38` as *the Ajtai commitment itself* | ✓ **reused verbatim** |
| `balancedDigit` | target 1's `balanced_digit_at` (`STAGE2_SCOPING.md` § "Decision 4") | dependency edge 1 → 3, as the ordered list has it |

So the only genuinely new Rust is: one `d`-loop (`rho_digit_as_rq`), one concatenation
(`lift_message`), one `mat_vec_mul` call (`lift_commit`), and two `&&`-joined loops (the checks).
That is why `≈ evalsplit` is the right size, and neither audit moved it.

### `rhoAsRq` costs **zero** Rust code

`hachi/lean/RqBridge.lean:108` defines the representation function as
`toRq (v : ring.Rq) : Rq Φ := Rq.ofFinCoeff Φ N (coeffK v)` — which is, character for
character, `rhoAsRq`'s body at `N = Φ.φ.natDegree` (`Reduction.lean:252–253`), with
`N_le_degree` (`RqBridge.lean:112`) already proving its side condition. So if a Rust quotient row
is a coefficient array of width `RING_DEGREE`, **`rhoAsRq` *is* the existing rep function** and
there is nothing to translate: the `_spec` for `rho_digit_as_rq` states
`toRq (rho_digit_as_rq …) = rhoDigitAsRq Φ …` and the `rhoAsRq` layer discharges by
`rfl`-plus-`ofFinCoeff_coeff`. Confirms and sharpens ArkLib's own "a change of presentation,
not a reduction" (`Reduction.lean:249–250`).

### The one new carrier: the quotient row

`ρ : Fin n → CPolynomial (ZMod q)` with `hρ : natDegree ≤ d − 1`
(`ProofSystem/RingSwitching/Lift/Reduction.lean:82–86`). `CPolynomial` is *not* `Rq`: no
quotient identification. But every use in this target truncates at `deg φ`, so a width-`d`
coefficient array is a faithful carrier for exactly the `hρ`-satisfying subset. Following the
reasoning pattern of the existing carriers (`arklib-analyze` § 6): dynamic length → `Vec`
newtype whose constructor establishes the shape invariant, and the invariant travels as a
hypothesis on each `_spec` (the `Wf` pattern, `hachi/lean/Ring.lean`).

```rust
/// A quotient row: `d` coefficients of `ZMod q`, little-endian.
/// spec: `CPolynomial (ZMod q)` restricted by `LiftedWitness.hρ`
/// (`ProofSystem/RingSwitching/Lift/Reduction.lean:85`).
pub struct QuotientRow(Vec<Fp>);        // invariant: len() == params::RING_DEGREE

/// spec: `LiftedWitness Φ μ n`, `RingSwitch/Reduction.lean:138`.
/// `hρ` is a proof field: erased here, carried as the `QuotientRow` invariant.
pub struct LiftedWitness { z: PolyVec, rho: Vec<QuotientRow> }
```

**Recommendation, with the trade-off stated.** `QuotientRow` and `ring::Rq` have identical
runtime layout, and reusing `Rq` outright would make `rho_digit_as_rq`'s body one line and
`rhoAsRq` literally `toRq`. The reason not to: `Rq` carries the quotient-ring `Mul`, and a
`QuotientRow` has no ring structure in the spec — reusing `Rq` invites a `Rq::mul` on a
quotient row, which is meaningless. Take the newtype, and give it a `to_rq()` whose spec is
`rhoAsRq`. If a probe later shows the extra newtype costs extraction anything, `Rq` is the
fallback and the fallback is *sound for this target* (all six definitions truncate).

Everything else slots into existing types: `PolyVec`/`PolyMatrix` (`hachi/src/linalg.rs:55, 66`)
for `z`, `d_key`, `liftMessage` and the commitment; `Fp`/`Ext4` **from `cpoly`, never
reimplemented** (`hachi/src/lib.rs`, README § "The field layer comes from cpoly"). `Ext4` does
not appear in this target at all — none of the six definitions mentions `F`
(`STAGE2_SCOPING.md` § "Decision 3": *"`rhoDigitsShortCheck`/`liftShortCheck` don't mention `F`
at all"* ✓ verified: `EndPiece/Reduction.lean:111, 144` take no `F` argument), so target 3 does
**not** wait on the TE Ext4 bridge.

### ⊗ Module placement — a discrepancy to settle before writing files

`STAGE2_SCOPING.md:353–358` assigns `lift_message`/`lift_commit` to `ringswitch.rs` and
`lift_short_check` to **`endpiece.rs`** (with `end_piece_check`). This target hands all six to
`ringswitch.rs`, which matches the *source* files' own split only partially: the two checks live
in `EndPiece/Reduction.lean`, the four carriers in `RingSwitch/Reduction.lean`. Both placements
are defensible; the checks' dependency runs the other way (they call `rho_digits`, which is
`ringswitch.rs`'s). **Recommendation:** put `rho_digits`, `rho_digit_as_rq`, `lift_message`,
`lift_commit` **and** `lift_short_check`/`rho_digits_short_check` in `ringswitch.rs` (this
target, one file, one freeze), and have target 6's `endpiece.rs` *call* `lift_short_check`
rather than define it — keeping each Rust item's `Mirrors` line in the module that owns its
spec's dependency, and keeping target 6 to `end_piece_check` + `wTableMleEval`. Flagged rather
than decided: it changes two rows of the API-mapping table.

### ⊗ A staleness correction that affects every citation an agent copies

`hachi/src`'s spec citations were written against the previous pin (`e92dc31`) and are
**systematically stale for two files** at `294b3f0b`, by a constant offset. Names still resolve;
line numbers do not:

| Cited in `hachi/src` | Actual at this pin |
|---|---|
| `Vectors.lean:39` `PolyVec`, `:42` `PolyMatrix`, `:49` `flattenBlocks`, `:77` `dot`, `:81` `matVecMul`, `:91` `scalarVecMul` | `:45`, `:48`, `:55`, `:83`, `:87`, `:97` — **uniformly +6** |
| `Vectors.lean:178` `splitForm` | `:197` |
| `NormBounds/Basic.lean:78` `l2NormSq`, `:82` `l1Norm`, `:87` `lInftyNorm`, `:91` `vecL2NormSq`, `:95` `vecLInftyNorm` | `:108`, `:113`, `:117`, `:121`, `:125` — **uniformly +30** |

`Rq.lean` and `Ajtai/Simple/Scheme.lean` citations (`Rq.lean:269` `ofFinCoeff`, `:260`
`coeffHom`, `Scheme.lean:38` `commit`) are **still accurate**. New `ringswitch.rs` docstrings
must cite the numbers in this brief, not the numbers next door; and a follow-up pass over
`linalg.rs`/`commit.rs` citations is owed (a docstring edit moves `Generated.lean`, so it rides
the params.rs landing per `STAGE2_SCOPING.md` § "Doc-sync list").
