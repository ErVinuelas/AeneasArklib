# Brief: the balanced digit layer — `balancedDigit` / `balancedShift`, `rhoDigits` / `rhoDigitCount`, the balanced message and `z` decomposition siblings, `DigitBaseOk` (ArkLib @ `294b3f0b0f46e1485c878a217e9de764855f5915`; ⊗⊗ re-based 2026-09-03 on PR #847 `d51d8bc` — see the first section)

Stage 2 target 1. Read from the pinned copy `hachi/.lake/packages/Arklib/ArkLib/…`
at the rev `hachi/lake-manifest.json` records for `Arklib`
(`hachi/lake-manifest.json:6–8`). Every path below is relative to
`hachi/.lake/packages/Arklib/ArkLib/Commitments/Functional/Hachi/` unless it
names another root.

Builds on `STAGE2_SCOPING.md` §§ "Decision 4 — minimal balanced surface",
"Parameter mapping", "Erasure catalogue", "Ordered target list + scale
policies". Where this brief corrects that document, the paragraph is marked
**⊗ correction**.

---

## ⊗⊗ Re-based 2026-09-03 on ArkLib PR #847 (pin `d51d8bc`) — read this first

Everything below was read at `294b3f0b0`; the pin moved to PR #847's head
before this target opened, and four things change. `file:line` citations
below are at the old pin — re-read each at `d51d8bc` before relying on it
(`Gadget/Core.lean` in particular grew a 200-line bounded-digit block and
lost the per-`dd` `gadgetDecompose_apply`).

**1. The target is a promotion, not a sibling layer (Decision 4 revised).**
Upstream re-documents `zmodDigitDecomposition` as "the building block the
balanced digits are shifted from, not itself a Hachi gadget inverse",
renames `commitBalanced` → `commit` (the unsigned committer is deleted), and
drops the unsigned norm lemmas (`zmodDigit_natAbs_le`,
`gadgetDecompose_zmod_vecLInftyNorm_le`, `…_l2NormSq_le`, `…_vecL2NormSq_le`)
and `gadgetDecompose_apply` / `gadgetDecompose_eq_fun`; `RhoDigits.lean`'s
`balancedDigit_valMinAbs_mem` is gone too (its content lives in
`Gadget/Norms.lean`'s `balancedZmodDigit_valMinAbs_mem`). The user's call:
adapt. So the *public* names go to the balanced functions —
`gadget_decompose`, `generate_decomps`, `commit` mirror
`balancedZmodDigitDecomposition`-at-δ and `Hachi.commit` — and today's
unsigned functions become the primitives underneath (`digit_at` keeps its
name: it *is* the spec's building block; the unsigned
`gadget_decompose`/`generate_decomps`/`commit` survive under primitive names
because the 74 proved specs are stated against them and
`InnerOuter/Scheme.lean` stays decomposition-generic). Every "sibling" in
§ Representation's signature table is therefore the *promoted* function;
the work is the same plus a rename pass and re-pointing `commit_spec` at
the balanced committer as the headline. The proved unsigned layer now owns
its one analytic input, `dd_digit_natAbs_le` (`hachi/lean/Scheme.lean`, a
verbatim copy of the deleted upstream lemma) feeding ArkLib's surviving
generic `gadgetDecompose_*_of_digit_le` — reuse that pattern for the
balanced specs (`balancedZmodDigit_natAbs_le` is the upstream input there).

**2. A second digit function, for the `z` side at τ = 5.** The chain's `z`
decomposition is no longer `balancedZmodDigitDecomposition` at `zDigits`;
it is `boundedBalancedZmodDigitDecomposition b τ zBound` with

```
boundedBalancedZmodDigit b τ x e
  = (((Nat.digits b (x.valMinAbs + ((b/2 : ℕ) : ℤ) * (digitOnesValue b τ : ℤ)).toNat)
        .getD e 0 : ℕ) : ZMod q) - ((b/2 : ℕ) : ZMod q)        Gadget/Core.lean (PR #847)
```

— *centre first* (`valMinAbs`, which `commit::centered_abs` already mirrors),
shift in `ℤ` by `Z_BALANCED_SHIFT = 8 · 69905 = 559240`, clamp with
`Int.toNat`, then `τ = 5` unsigned digits, each minus 8. The order is the
*reverse* of the message digit's shift-then-`.val`, and the shift is an
integer shift of a signed value, not a field add. Its reconstruction law
is conditional — `x.valMinAbs.natAbs ≤ zBound → Σ bᵉ·digit = x`
(`BoundedDigitDecomposition.reconstruct_of_bound`) — so the `_spec` for
its round-trip carries the bound as a hypothesis (a new shape for the
erasure catalogue: conditional reconstruction). Its range is unconditional
(`boundedBalancedZmodDigit_valMinAbs_mem`, box `[-8, 7]`). Rust sketch
`bounded_z_digit_at(c: Fp, e: usize) -> Fp` over the centred `i64`
representative; its `gadget_*` consumers at width `Z_DIGITS = 5` are
target 2's (`zDecompBounded = bddZ.gadgetDecompose`), not this target's.
Cost: one `valMinAbs` (a compare and a subtract) per coefficient, then the
same digit loop at 5 digits; a `Nat.digits` of a value `< 16^5` — no new
width. Scale: real consts throughout, like the rest of the digit layer.

**3. The contested-`BETA_SQ` paragraph in § Semantics risks is settled.**
τ = 5, `BETA_SQ = 41976510894886092800` (`342ebba`); the claim that this
target is insensitive to it stands (honest balanced `ℓ₂² = 536870912` is
eleven orders of magnitude below it). "Write specs against `GADGET_DIGITS`
for loop bounds" still holds for the message side; the `z` side's loop
bound is `Z_DIGITS`.

**4. Constants landed (params.rs, 2026-09-03), so § Parameters' "new
constants this target needs" is done:** `HALF_BASE = 8`, `BALANCED_SHIFT =
2290649224` as specified, plus `Z_DIGITS = 5`, `Z_BOUND = 131072`,
`Z_BALANCED_SHIFT = 559240`, `B_ZERO = 16`, `CHAIN_GAMMA = 15`, and the
dimension block. `Check.lean` § 1 ties `BALANCED_SHIFT` to
`⌊b/2⌋ · digitOnesValue 16 8` and `Z_BALANCED_SHIFT` to `digitOnesValue_eq`;
`rhoDigitCount q 16 = GADGET_DIGITS` is proved there once via
`HachiParams.clog_eq_delta` (the bridge lemma § Parameters asks for).
`rhoDigitsShortCheck_eq_true_of_digitBaseOk` was deleted upstream as dead
code; the tautology it stated is still true and still worth a claims-ledger
note when target 6 translates the check verbatim.

**Unchanged:** the definition chain's *shape* (balanced message digit = one
field add, one unsigned digit read, one field subtract; `rfl`-equal to the
bundled `.digit`), the cost model, the strategy ranking, the representation
choices, the `hbq : b ≤ q/2` anti-wraparound trap, the "raw-`u64` shift is
wrong" arithmetic, and the scale policy with its `commit`-path refinement.

---

## Definition chain

Four separate chains, all bottoming out in one `Nat.digits` read.

**1. The coefficient-level balanced digit.**

```
balancedZmodDigitDecomposition b digits hb hq            Gadget/Core.lean:148
  : DigitDecomposition (R := ZMod q) (b : ZMod q) digits
  .digit c e = (zmodDigitDecomposition b digits hb hq).digit
                 (c + balancedShift b digits) e
               - ((b / 2 : ℕ) : ZMod q)                  Gadget/Core.lean:150–152
  .reconstruct                                            Gadget/Core.lean:153–164
```

with

```
zmodDigitDecomposition …  .digit c e
  = ((Nat.digits b c.val).getD (e : ℕ) 0 : ZMod q)        Gadget/Core.lean:115
balancedShift b digits
  = ((b / 2 : ℕ) : ZMod q) * ∑ e : Fin digits, (b : ZMod q) ^ (e : ℕ)
                                                          Gadget/Core.lean:133–134
```

The proof-free repackaging the rest of the chain actually uses:

```
balancedDigit b digits c e
  = (((Nat.digits b (c + balancedShift b digits).val).getD e 0 : ℕ) : ZMod q)
    - ((b / 2 : ℕ) : ZMod q)                              RingSwitch/RhoDigits.lean:79–81
balancedDigit_eq_digit … := rfl                           RingSwitch/RhoDigits.lean:86–89
```

So the surface syntax `balancedDigit b digits c e` unfolds to: one **field**
add of a constant, one base-`b` `getD` digit read of the canonical
representative, one **field** subtract of a constant. The `digits` argument
enters *only* through `balancedShift` — it does not bound `e`, and the bound
lemmas carry `he : e < digits` separately (`RhoDigits.lean:101, 109`).

**2. The polynomial-level quotient digits.**

```
rhoDigitCount q b = Nat.clog b q                          RingSwitch/RhoDigits.lean:66
rhoDigits Φ b ρ u
  = CPolynomial.ofFinCoeff Φ.φ.natDegree
      (fun k => balancedDigit b (rhoDigitCount q b) (ρ.coeff k) u)
                                                          RingSwitch/RhoDigits.lean:135–136
rhoDigits_coeff : (rhoDigits Φ b ρ u).coeff k
  = if k < Φ.φ.natDegree then balancedDigit … else 0       RingSwitch/RhoDigits.lean:141–143
```

i.e. one coefficient loop of `balancedDigit`, truncated at the ring dimension.
Its consumers: `rhoAsRq` (`RingSwitch/Reduction.lean:252–253`, `Rq.ofFinCoeff`
at `deg φ`), `rhoDigitAsRq` (`:259–261`, flattening `(row, digit)` through
`finProdFinEquiv`), `liftMessage` (`:273–275`, `Fin.append w.z
(rhoDigitAsRq …)`), and the decidable range check `rhoDigitsShortCheck`
(`EndPiece/Reduction.lean:111–113`) / `liftShortCheck` (`:144`).

**3. The message and `z` gadget siblings.** The gadget inverse is generic in
the decomposition:

```
gadgetDecompose Φ dd x j
  = Rq.ofFinCoeff Φ Φ.φ.natDegree
      (fun k => dd.digit ((x (finProdFinEquiv.symm j).1).1.coeff k)
                         (finProdFinEquiv.symm j).2)        Gadget/Core.lean:243–246
Decomposition.ofDigits ddMsg ddInner
  = { message := gadgetDecompose Φ ddMsg
      inner   := gadgetDecompose Φ ddInner }                InnerOuter/Scheme.lean:131–136
generateDecomps decomp pp m
  = { message := fun i => decomp.message (m i)
      innerDecomp := fun i =>
        decomp.inner (Simple.commit Φ pp.innerMatrix (ss i)) } InnerOuter/Scheme.lean:157–163
```

so the balanced path is *the same functions at a different `dd`*:

```
commitBalanced b hb pp p
  = let decomps := generateDecomps Φ
        (Decomposition.ofDigits Φ
          (balancedZmodDigitDecomposition b (Nat.clog b q) hb (Nat.le_pow_clog hb q))
          (balancedZmodDigitDecomposition b (Nat.clog b q) hb (Nat.le_pow_clog hb q)))
        pp.toPublicParams (Hachi.toMatrix p)
    (commitWithDecomps Φ pp.toPublicParams decomps, decomps)   Commitment.lean:141–152
```

versus `commit` at `zmodDigitDecomposition` (`Commitment.lean:113–124`);
`commitBalanced_fst`/`_snd` are `rfl` (`Commitment.lean:374–395`). The `z`
half is the second decomposition slot of `quadEvalReduction`:

```
completePrefixReduction … (quadEvalReduction … Φ pp
  (balancedZmodDigitDecomposition P.b messageDigits P.hb hqm)
  (balancedZmodDigitDecomposition P.b zDigits   P.hb hqz)) …   HonestChain.lean:333–358
```

**4. The side conditions.** `DigitBaseOk q bound bDig` is a three-field
`Prop` structure — `one_lt : 1 < bDig`, `le_half : bDig ≤ q / 2`,
`radius_le : bDig / 2 ≤ bound` (`RingSwitch/Reduction.lean:175–181`) —
supplied at the chain's parameters by `HonestRangeParams.digitBaseOk`
(`HonestChain.lean:211`) and `digitBaseOk_range` (`:216`). Pure `Prop`:
nothing to translate, and its only computational consequence is that the digit
conjunct of `liftShortCheck` is a tautology
(`rhoDigitsShortCheck_eq_true_of_digitBaseOk`, `EndPiece/Reduction.lean:138–141`).

**Rust chain to extend.** `gadget::digit_at` (`hachi/src/gadget.rs:68–77`) →
`gadget::gadget_decompose` (`:196–217`, `digit_at` hardcoded at `:208`) →
`commit::generate_decomps` (`hachi/src/commit.rs:347–359`, `gadget_decompose`
hardcoded at `:353` and `:355`) → `commit::commit_with_decomps` (`:366–369`)
→ `commit::commit` (`:378–382`). `Rq::from_coeffs` (`hachi/src/ring.rs:110–123`)
is the `Rq.ofFinCoeff` end of the chain; `Rq::coeff` (`:132–137`) the other.

**⊗ correction — `hachi/src/gadget.rs`'s spec citations are stale at this
pin.** The module cites `Gadget/Core.lean:139` for `gadgetEntry` (actual
`:175`), `:143` for `gadgetMatrix` (`:179`), `:147` for `gadgetMul` (`:183`),
`:152` for `IsLawfulGadgetDecomposition` (`:188`), `:177` for `gadgetMul_apply`
(`:213`), `:207` for `gadgetDecompose` (`:243`), `:221` for
`gadgetDecompose_lawful` (`:257`) — all off by exactly 36 lines, which is the
`balancedShift` + `balancedZmodDigitDecomposition` block inserted at
`Gadget/Core.lean:130–165`. The two citations *below* the insertion
(`zmodDigitDecomposition` `:113`, its `.digit` `:115`) are still correct, and
every `InnerOuter/Scheme.lean` citation in `commit.rs` (`:131`, `:157`,
`:166`, `:194`) is still correct. Any file touched for this target should have
its `Gadget/Core.lean` line numbers re-based; this is a docstring edit and so
moves `Generated.lean` (`NOTES.md` § "An Aeneas surprise"), so it rides a
regeneration rather than going in alone.

---

## Parameters

Values from `hachi/src/params.rs`, pinned/chosen/derived split carried per
constant. `q` is the Hachi prime, `b` the gadget base, `d = deg φ` the ring
degree, `δ` the digit count.

| Constant | Value | Provenance | Spec-side obligation it discharges |
|---|---|---|---|
| `Q` | `2^32 − 99 = 4294967197` | **pinned** by `cpoly`'s `Fp` (`params.rs:41–51`; `cpoly/src/field.rs:56`) | `Fact (Nat.Prime q)`, `q < 2^32` |
| `RING_LOG_DEGREE` / `RING_DEGREE` | `10` / `1024` (α = 10, d = 2^α) | **pinned** by [NOZ26] Fig. 9, ℓ = 30 (`params.rs:66–88`) | `0 < Φ.φ.natDegree` (`RhoDigits.lean:178`), `1 ≤ deg φ` (`Gadget/Core.lean:257`) |
| `GADGET_BASE` | `16` | **pinned** by Fig. 9 (`params.rs:90–97`) | `hb : 1 < b` (`Gadget/Core.lean:148`); `hbq : b ≤ q/2` for the *balanced* bounds — 16 ≤ 2147483598 ✓ (`Gadget/Norms.lean:110`) |
| `GADGET_DIGITS` | `8` | **pinned** by Fig. 9, and forced: `16^7 = 2^28 < q ≤ 16^8 = 2^32` (`params.rs:99–113`) | `hq : q ≤ b ^ digits` (`Gadget/Core.lean:148`) |
| `MESSAGE_ROWS` = `BLOCKS` | `1024` each | **pinned** by Fig. 9 `2^m` / `2^r` (`params.rs:115–147`) | `PublicParams` shapes, free in the spec |
| `INNER_ROWS` = `OUTER_ROWS` | `1` each | **pinned** by Fig. 9 `n_A = n_B = 1` (`params.rs:126–140`) | as above |
| `GAMMA` | `16` (weak-opening γ̄ = b) | **pinned** by ArkLib's paper-parameter mapping (`params.rs:149–166`) | covers the balanced digit radius `⌊b/2⌋ = 8` ✓ |
| `KAPPA` | `32` (= 2ω) | **pinned** (`params.rs:249–268`) | untouched by this target |
| `ML_VARS_LOW` = `ML_VARS_HIGH` | `10` each | **derived** (`params.rs:207–225`) | untouched by this target |
| `BETA_SQ` | *symbolic:* `quadEvalBetaSq γ b τ d m δ` at `γ := b` (`QuadEval/Soundness.lean:106`) | **derived**, and its exponent `τ` is **contested** — see below | untouched by this target (see § Semantics risks) |

**New constants this target needs.** Two, both literals for the reason
`RING_DEGREE` and `GAMMA` are literals (a derived form extracts through
`Result` — `params.rs:80–84, 162–165`):

| Name | Value | Provenance | Ties to |
|---|---|---|---|
| `BALANCED_SHIFT: u64` | `2_290_649_224` (`= 0x88888888`) | **derived** | `balancedShift 16 8` (`Gadget/Core.lean:133–134`): `⌊16/2⌋ · Σ_{e<8} 16^e = 8 · 286331153 = 2290649224`. Strictly below `Q`, so its `ZMod q` image is the literal itself and the Check entry is an ℕ identity with no reduction step |
| `HALF_BASE: u64` | `8` | **derived** | `(b / 2 : ℕ)` at `b = 16` (`Gadget/Core.lean:152`, `RhoDigits.lean:81`) |

`Σ_{e<8} 16^e = (16^8 − 1)/15 = 286331153 = 0x11111111`, the same factor
`params.rs:177` already carries inside `BETA_SQ`'s derivation.

**`rhoDigitCount` needs no constant — confirmed, and the reason is sharper
than Stage 2 states.** All four digit counts on the composed nonrecursive path
are one number:

* `rhoDigitCount q b = Nat.clog b q` (`RhoDigits.lean:66`), consumed at
  `bDig := P.bZero` (`HonestChain.lean:377`, `Composition.lean:292`);
* `HonestRangeParams.ofPinnedDigitBase 16` gives `(b, γ, bZero) = (16, 15, 16)`
  (`HonestChain.lean:165–175`), so `bZero = b = 16`;
* `hachiNonrecursiveOpening` instantiates `messageDigits := δ P`,
  `innerDigits := δ P` **and** `zDigits := δ P`, discharging both `hqm` and
  `hqz` with `Nat.le_pow_clog P.hb q` (`Correctness.lean:500–517`), where
  `δ P = Nat.clog (HonestRangeParams.b P) q` (`Correctness.lean:491`,
  `Concrete.lean:47`);
* `Nat.clog 16 (2^32 − 99) = 8` because `16^7 = 268435456 < q ≤ 16^8`.

So `messageDigits = innerDigits = zDigits = rhoDigitCount q bZero = 8 =
GADGET_DIGITS`, one literal, one bridge lemma. That lemma cannot go through
bare `simp`/`decide` at `q ≈ 4.3·10^9`; the pattern is
`Nat.clog_le_iff_le_pow` + `omega`, worked at
`hachi/.lake/packages/Arklib/scripts/HachiRuntime.lean:146–150` (note the
`scripts/` root, not `ArkLib/`).

**⊗ correction — `STAGE2_SCOPING.md` contradicts itself on
`RHO_DIGIT_COUNT`.** § "Parameter mapping" lists `RHO_DIGIT_COUNT | 8 |
rhoDigitCount q bZero` as a new params row (and F3 puts it in the value-8
literal-collision cluster), while § "Ordered target list" row 1 says
"`rhoDigitCount` needs no const (= `GADGET_DIGITS`)". The second reading is
right on the arithmetic above; adopting it removes one member of the value-8
collision cluster. Recommendation: **no `RHO_DIGIT_COUNT`**, reuse
`GADGET_DIGITS`, and put the `Nat.clog 16 q = 8` identity in Check.lean § 1
once, cited from both the `GADGET_DIGITS` and the `rhoDigits` entries.

**⊗ addition to F3 (literal collisions).** F3's value-**8** list is
`GADGET_DIGITS`, `Z_DIGITS`, `RHO_DIGIT_COUNT`. `HALF_BASE = 8` — introduced
by § "Decision 4"'s own Rust table — is missing from it. With the
`RHO_DIGIT_COUNT` removal above, the value-8 cluster becomes
`GADGET_DIGITS`, `HALF_BASE` (and `Z_DIGITS`, if it is introduced at all
rather than sharing `GADGET_DIGITS` per the same argument). `HALF_BASE` and
`GADGET_DIGITS` are *unrelated* quantities that collide at these parameters
(`⌊b/2⌋` vs `⌈log_b q⌉`), which is the dangerous shape: rewrite hypotheses,
never goals.

`BALANCED_SHIFT` also joins the watchlist for a different reason: it depends on
the digit count (`balancedShift b digits`, `Gadget/Core.lean:133`), so the
single constant is valid only while all four counts coincide at 8. If
`NOTES.md` § "One digit count, not two"'s "To revisit" ever fires, this
constant splits per count.

---

## Semantics risks

**Value ranges — no new width, and the balanced form is strictly shorter.**
Every value stays inside `Fp` (`cpoly`'s `u64` newtype reduced mod
`P = 4294967197`, `cpoly/src/field.rs:72–91`):

* the field add of the shift: `c.to_u64() ≤ q−1 = 4294967196` and
  `BALANCED_SHIFT = 2290649224`, so the raw sum is at most `6585616420 < 2^64`
  — no `u64` overflow, and `Fp::add` reduces it (`cpoly/src/field.rs:107–114`);
* the field sub of `HALF_BASE`: `Fp::sub` is `(a + P − b) % P ≤ (P−1) + P <
  2^64` (`cpoly/src/field.rs:116–123`);
* the digit read: `rest / 16` and `rest % 16` on a `u64 < q`, so every
  intermediate is `< 2^32`.

Norms: a balanced digit's centered absolute value is `≤ ⌊b/2⌋ = 8`
(`Gadget/Norms.lean:140–144`, ball form; `:109–114`, the exact box
`[−⌊b/2⌋, ⌈b/2⌉−1] = [−8, 7]`), against the unsigned form's `b − 1 = 15`
(`Gadget/Norms.lean:71–73`). So at `MESSAGE_ROWS · GADGET_DIGITS = 8192`
entries of `RING_DEGREE = 1024` coefficients each, the honest `ℓ₂²` of a
balanced message decomposition is `8192 · 1024 · 8² = 536870912`, against the
unsigned `8192 · 1024 · 15² = 1887436800` (the figure `params.rs:191` records).
Both fit `u64` comfortably; `commit::vec_l2_norm_sq`'s `u128`
(`hachi/src/commit.rs:159`) is unchanged and unchallenged. `‖·‖∞ = 8 ≤ GAMMA
= 16` and `≤ CHAIN_GAMMA = 15`, so **`verify_weak` needs no balanced sibling**
— Stage 2's claim, confirmed on both bounds.

**The raw-`u64` shift is wrong, not merely unidiomatic.** Stage 2 flags that
the shift add must be a *field* add; here is the arithmetic. The raw sum can
reach `6585616420`, and `16^8 = 4294967296 ≤ 6585616420 < 16^9`, so
`Nat.digits 16` of the raw sum has **9** entries where the spec's
`(c + balancedShift).val < q` has at most 8. Digit 7 — the top digit the
gadget actually reads — would then be `⌊6585616420/16^7⌋ mod 16 = 24 mod 16 =
8`, and the balanced digit `8 − 8 = 0` instead of the true value; and the box
bound `[−8, 7]` fails outright because the digit is no longer `< b` at the
top position. Anti-wraparound is the whole content of the `hbq : b ≤ q/2`
hypothesis (`Gadget/Norms.lean:107–108` spells this out).

**A balanced digit is a residue, not a small integer.** The digit `−8` is
represented as `Fp(q − 8) = Fp(4294967189)`. Anything that reads a digit as a
magnitude must go through the centered view — `commit::centered_abs`
(`hachi/src/commit.rs:79–88`), which mirrors `ZMod.valMinAbs`, and which
`vec_l_infty_norm` (`:174`) already uses. A range check written as
`d.to_u64() <= 7` would silently reject every negative digit. The spec side
says the same thing in its own vocabulary: every bound in `Gadget/Norms.lean`
and `RhoDigits.lean` is stated on `.valMinAbs.natAbs`, never on `.val`.

**Partiality.** Aeneas models `/`, `%`, `+`, `*` and indexing as fallible.
Three consequences, all with precedents: (a) `HALF_BASE` must be the literal
`8`, never `params::GADGET_BASE / 2`, exactly as `GAMMA` is `16` and not
`GADGET_BASE` (`params.rs:162–165`); (b) `Fp::new(BALANCED_SHIFT)` is a `%`
and so a `Result` bind per call — a reason to hoist it, see § Cost model; (c)
`digit_at`'s `rest / b` is already discharged at a literal base by the
existing `digit_at_loop_spec` (`hachi/lean/Scheme.lean:695`), and the balanced
sibling reuses it verbatim.

**Exactness / degenerate cases.**

* The bound lemmas need `he : e < digits` (`RhoDigits.lean:101, 109`);
  `digit_at_spec` already carries `he : e.val < 8`
  (`hachi/lean/Scheme.lean:722`). `balanced_digit_at` at `e ≥ 8` is *defined*
  but outside the proved box.
* The two derived bounds `GAMMA` and `BETA_SQ` are documented as tight for an
  *extracted* opening (`NOTES.md` § "The dimensions and the norm bounds"), but
  the balanced honest case sits at half the unsigned radius, i.e. deeper
  inside both. A corpus of balanced decompositions therefore exercises the
  norm checks *less* than the unsigned corpus does; a semantics test that
  wants to see a bound bite must construct the vector, not decompose one.
* `NOTES.md` § "The digits are not balanced" (updated 2026-09-01) settles the
  adoption shape: the balanced layer is **added alongside** the unsigned one
  and `gadget.rs` is never flipped, because `InnerOuter/Scheme.lean` is
  decomposition-generic (`:131–136`). The 74 proved specs keep targeting
  `zmodDigitDecomposition 16 8` (`hachi/lean/Scheme.lean:690`).
* Proof-side trap, from Stage 2 and confirmed: sibling specs must take **no**
  local `[DecidableEq (ZMod q)]` binder, or the committer's decomposition and
  the generic lemma carry different instances and unification diverges — the
  pin states this itself at `Commitment.lean:396–400`.
* `balancedDigit`'s body (`RhoDigits.lean:79–81`) inlines the `Nat.digits …
  getD` expression rather than mentioning `zmodDigitDecomposition`. There is
  no named simp lemma for `balancedDigit = unsigned digit of (c+shift) − ⌊b/2⌋`;
  the route is `balancedDigit_eq_digit` (`rfl`, `:86–89`) followed by
  `simp only [balancedZmodDigitDecomposition, zmodDigitDecomposition]`, which
  is exactly what `Gadget/Norms.lean:116` does.

**The contested `BETA_SQ`/τ, in one line, and why this target is insensitive
to it.** The pin instantiates the composed chain's *structural* digit count at
`zDigits = δ P = Nat.clog 16 q = 8` and discharges `hqz : q ≤ b ^ zDigits` by
`Nat.le_pow_clog` (`Correctness.lean:500–517`; `16^4 = 65536 < q`, so a
balanced `z`-decomposition at 4 digits is not constructible at all), whereas
the *contested* τ is the third formal argument of the soundness bound
`quadEvalBetaSq (γ b τ d m δ : ℕ)` (`QuadEval/Soundness.lean:106`) — a
number in a norm ceiling, not a loop count. The two readings differ only in
that literal: the working tree currently carries the τ = 8 value
(`params.rs:206`, per `STAGE2_SCOPING.md` F2 and `NOTES.md`
§ "`BETA_SQ` corrected"), while the user has chosen τ = 4, the reference
implementation's `Z_DECOMP_DELTA` (`logs/paper-impl/README.md:48`). Target 1
reads neither: the honest balanced `ℓ₂²` of `536870912` is eight orders of
magnitude below **both** candidate ceilings, so no balanced-layer op, test or
bench case changes with the outcome. Write specs against `GADGET_DIGITS` for
loop bounds and never against `BETA_SQ`'s τ.

---

## Cost model

Bench vocabulary: `<module>/<op>` cases, `gadget/*` and `commit/*`.

**The dominant term is *modular reduction by `P`*, not division by `b`.**
`GADGET_BASE = 16` reaches `digit_at` as `let b: u64 = params::GADGET_BASE`
(`hachi/src/gadget.rs:69`), a compile-time constant power of two, so `rest / b`
and `rest % b` (`:73, 76`) are a shift and a mask. `Fp`'s `% P`
(`cpoly/src/field.rs:85–89, 107–123`) is a reduction by a non-power-of-two
constant — a multiply-shift sequence, several times the cost of a shift. Count
`% P` per digit:

| form | `% P` per digit | `/16`,`%16` per digit |
|---|---|---|
| unsigned `digit_at` today | 1 (`Fp::new(rest % b)`) | `e` shifts + 1 mask |
| naive balanced wrapper `digit_at(c + Fp::new(SHIFT), e) − Fp::new(HALF)` | **5** (2 × `Fp::new` const, `Fp::add`, `digit_at`'s `Fp::new`, `Fp::sub`) | same |
| constants hoisted, shift-add once per coefficient | 2 | same |
| + digit folded in `u64` before one `Fp::new` | ~1.1 (8 digits share one shift-add) | same |

Per **coefficient** (all 8 digits): unsigned 8 reductions and 28 shifts
(`Σ_{e<8} e`); naive balanced **40** reductions and 28 shifts; hoisted 18 and
28; fully folded ~10 and 8. So the naive wrapper is roughly **5× the
modular-reduction work** of the unsigned digit path it copies, and the
achievable floor is ~1.25×.

**Whole-op counts at real consts.**

* `gadget::balanced_digit_at(c, e)`: `O(e)` shifts, 5 reductions. Bench at
  `e = GADGET_DIGITS − 1 = 7`, the deepest index, per the existing `digit_at`
  precedent and its stated reason (`hachi/benches/gadget.rs:166–169`).
* `gadget::balanced_gadget_decompose(x)` at `rows = MESSAGE_ROWS = 1024`:
  `rows · digits · degree = 1024 · 8 · 1024 = 8388608` balanced digits;
  `rows · degree · Σ_{e<8} e = 29360128` shifts and (naive) ~41.9 M reductions.
  Allocation: `8192` output slots, each building a `Vec<Fp>` by 1024 `push`es
  and then **copying it again** inside `Rq::from_coeffs`
  (`hachi/src/ring.rs:110–123`) → `16384` `Vec<Fp>` allocations and ~134 MiB
  of coefficient traffic per call, plus the ~11 doubling reallocations each
  `Vec::new()`-then-push chain pays.
* `ringswitch::rho_digits(ρ, u)`: one coefficient loop, `RING_DEGREE = 1024`
  balanced digits, one `Rq` built. Cheap; the same double-copy applies.
* `commit::generate_decomps_balanced` and `commit::commit_balanced`: **not
  digit-bound.** Per block they pay one `A · s` of `INNER_ROWS ×
  (MESSAGE_ROWS · GADGET_DIGITS) = 1 × 8192` ring muls, ~25 s at `d = 1024`
  schoolbook, and there are `BLOCKS = 1024` blocks
  (`hachi/benches/exclusions.toml:94–99`). The digit layer is a few percent of
  that.

**Floors and anchors, not predictions.** The only in-repo `gadget_decompose`
reading is `82.2 µs` at the *retired* toy shape (4 rows × 32 digits, `d = 64`
— 8192 digits, 126976 shifts), `NOTES.md` § "The first benchmark run", and the
same section says plainly these are sizing information and not a baseline,
because byte-identical crates read up to 59% apart on that host (see also
`NOTES.md` § "Benchmark numbers from this session are not measurement-grade").
Scaled by digit count alone that shape suggests ~10 ns/digit for the naive
division-chain form, hence ~80 ms for `balanced_gadget_decompose` at
`rows = 1024`; the module doc's independent expectation for the same shape is
"~tens of ms" (`hachi/benches/gadget.rs:22–24`). The **external** anchor is
better here than usual: the paper's own implementation uses balanced base-16
δ = 8 digits, and its `poly_vec::b_decomp` measures **1.73 ms per call** at
ℓ = 24 (`logs/paper-impl/README.md:109`) — comparability caveat recorded in the
same file (`:58`): the reference decomposes a whole `PolyVec` per call and the
sizes vary by call site, so this is an order-of-magnitude anchor, not a
per-digit rate.

**Proof-side cost, for scheduling.** The unsigned `gadget_decompose` costs
three loop specs plus a headline — `gadget_decompose_coeff_loop_spec`
(`hachi/lean/Scheme.lean:1229`), `_digit_loop_spec` (`:1287`),
`_outer_loop_spec` (`:1350`), `gadget_decompose_spec` (`:1416`) — roughly 190
lines of loop invariant. The balanced sibling is that scaffold at `ddBal`
instead of `dd` (`:690`), plus `balanced_digit_at_spec` = `digit_at_spec`
(`:722`) followed by two field steps, per Stage 2. `generate_decomps_spec`
(`:2054`) and its loop (`:1964`) get the same treatment.

---

## Strategy candidates

Highest expected win first. Pointers only; the strategies live in their skills.

* **`opt-word-arith` — the balanced-digit conditional-subtract fold.** The
  headline. Fold `u − ⌊b/2⌋` in `u64` under a guard (`u ≥ 8 ? Fp::new(u − 8) :
  Fp::new(Q − (8 − u))`; every branch value is `< Q`, so `Fp::new` is exact)
  and hoist the two constant `Fp::new`s, replacing 5 reductions per digit with
  ~1. Both branches are provably `Fp::new(u) − Fp::new(8)` because `u < 16 <
  Q`, so the lemma is two-case arithmetic. Note the hard constraint the skill
  already carries: `Fp` comes from `cpoly` and is never reimplemented
  (`hachi/src/lib.rs`, README § "The field layer comes from cpoly"), so the
  shift **add** must stay `Fp`'s `+` — the raw-`u64` route is wrong on the
  numbers above, not just impolite. (The rule is stated at
  `hachi/src/lib.rs:47–53`: "Reusing them rather than reimplementing is a hard
  rule of this project.")
* **`opt-inplace-buffers` — hoist the shift out of the digit loop, and stop
  copying the coefficient vector.** Two independent wins in the triple loop:
  (a) compute `c + shift` once per *coefficient* rather than once per
  (coefficient, digit), which requires inverting the `(e, k)` nesting so the 8
  output coefficient buffers are filled in parallel — 8× fewer field adds; (b)
  pre-size the coefficient buffer to `RING_DEGREE` and build the `Rq` from it
  directly, removing `Rq::from_coeffs`'s second full copy
  (`hachi/src/ring.rs:110–123`) and the push-growth reallocations: 16384 → 8192
  allocations, ~134 → ~67 MiB per `balanced_gadget_decompose` call.
* **`opt-algo-swap` — running-quotient digit extraction.** `Σ_{e<8} e = 28`
  shift-chains per coefficient become 8. The specification's own bench header
  advertises exactly this trade (`hachi/benches/gadget.rs:4–6`: "`O(digits²)`
  per coefficient where a running quotient would be `O(digits)`"). Ranked
  third rather than first *at these parameters only*: `b = 16` is a power of
  two so the eliminated operations are shifts, not hardware divisions. It is
  worth doing anyway because it is the natural carrier for the two wins above
  (a single pass per coefficient makes the hoisted shift-add and the parallel
  buffers fall out), and because it is the win that survives a base change.
* **`opt-list-to-array` — applies to the *Lean* statement of any candidate,
  not to the Rust.** `gadgetDecompose` is a `Fin (rows·digits) → Rq Φ` and
  `rhoDigits` is `CPolynomial.ofFinCoeff` over a `fun k => …`
  (`Gadget/Core.lean:243–246`, `RhoDigits.lean:135–136`); a `Foo.opt` variant
  has to be an indexed `Vec` loop for the translation to stay trivial. No new
  win in the Rust, which is already indexed loops with no `List` and no append
  chain.
* **`opt-tailrec-loops` — not applicable, recorded so it is not re-guessed.**
  The only non-structural recursion in the chain is Mathlib's `Nat.digits`
  (well-founded), and the Rust never mirrors it: `digit_at` is already a
  counter loop and `digit_at_spec` bridges the two
  (`hachi/src/gadget.rs:68–77`, `hachi/lean/Scheme.lean:722–740`).
* **Sharing the shifted coefficient across the message *and* inner
  decompositions — *(no skill yet)*.** `generateDecomps` decomposes `m i` and
  then `A · s i` (`InnerOuter/Scheme.lean:157–163`); the two inputs are
  unrelated, so there is nothing to share. Recorded as a *rejected*
  direction so it is not proposed later.
* **Not a candidate: NTT / `ring::mul`.** The digit layer contains no ring
  product. `commit_balanced`'s cost is `ring::mul`
  (`hachi/benches/exclusions.toml:94–99`), and that champion is target-2+
  business — `ArkLib/Data/Lattices/CyclotomicRing/Core/Basic.lean:71–73`'s
  `TODO add proper NTT multiplication here` and `hachi/src/ring.rs`
  § "What is deliberately not here" own it.

---

## Representation

**No new carrier.** Every value the target produces is an `Fp`, an `Rq` or a
`PolyVec`, all existing:

* `Fp` and `Ext4` are taken from the `cpoly` dependency and never
  reimplemented — a hard project rule (`hachi/src/lib.rs:47–53`).
  `Fp::new`, `to_u64`, `Add`, `Sub`, `Mul`, `Neg`,
  `ZERO`, `ONE` are the whole surface (`cpoly/src/field.rs:72–160`); there is
  no `const fn` constructor, which is why `BALANCED_SHIFT` reaches the field
  through `Fp::new` and why hoisting it matters.
* `Rq` is a `Vec<Fp>` newtype of exactly `RING_DEGREE` coefficients by
  construction (`hachi/src/ring.rs:54–137`), matching `Rq.ofFinCoeff Φ
  Φ.φ.natDegree` — which is precisely the shape both `gadgetDecompose`
  (`Gadget/Core.lean:245`) and `rhoAsRq` (`RingSwitch/Reduction.lean:252–253`)
  build. `Wf` (`hachi/lean/Ring.lean:53`) and `WfVec`
  (`hachi/lean/Scheme.lean:57`, used at `:1416`) carry the shape invariant as a
  hypothesis on each `_spec`, since Aeneas cannot see the Rust privacy
  boundary.
* `PolyVec` / `PolyMatrix` (`hachi/src/linalg.rs:55–91, 207`) for the block
  layer. The flat index layout is already the specification's:
  `finProdFinEquiv (i, e)` has value `e + digits · i`
  (`Gadget/Core.lean:202`), which is `digits · i + e`, which is what
  `gadget.rs` § "Index layout" (`:39–47`) and `gadget_mul`/`gadget_decompose`
  implement, and which `rhoDigitAsRq` reuses verbatim for the quotient block
  ("row `j / δ` and digit `j % δ` — the same flattening the gadget matrix
  uses", `RingSwitch/Reduction.lean:255–258`). **No new index arithmetic.**

**Proposed signatures**, mirroring the existing ones one-for-one:

```rust
// gadget.rs — extends the module, does not modify digit_at/gadget_decompose
pub fn balanced_digit_at(c: Fp, e: usize) -> Fp;              // spec: balancedDigit 16 8 c e
pub fn balanced_digit_decompose(c: Fp) -> Vec<Fp>;            // optional; the shared-shift carrier
pub fn balanced_gadget_decompose(x: &PolyVec) -> PolyVec;     // spec: gadgetDecompose Φ ddBal
// commit.rs — the seam
pub fn generate_decomps_balanced(pp: &PublicParams, m: &Vec<PolyVec>) -> Decomp;
pub fn commit_balanced(pp: &PublicParams, m: &Vec<PolyVec>) -> (PolyVec, Decomp);
// ringswitch.rs (new module, or gadget.rs until target 3 opens it)
pub fn rho_digits(rho: &Rq, u: usize) -> Rq;                  // spec: rhoAsRq ∘ rhoDigits Φ 16
```

`commit_with_decomps` (`hachi/src/commit.rs:366–369`) is reused **unchanged**:
it takes `&Decomp` as data, and `commitBalanced` differs from `commit` only in
the decomposition slots (`Commitment.lean:141–152` vs `:113–124`). Likewise
`base_pow`, `gadget_entry`, `gadget_matrix`, `gadget_mul`, `derived_message`,
`verify_weak`, `verify`, all norms, `Opening::honest`, `flatten_blocks` and
every struct — Stage 2's reuse list, confirmed against the pin.

**A quotient row is representable as `Rq`.** ArkLib types `ρ` as
`CPolynomial (ZMod q)` (`LiftedWitness.ρ`,
`ProofSystem/RingSwitching/Lift/Reduction.lean:80–86`), not as `Rq Φ`, so this
is a choice and not a given. It is sound and pre-justified at the pin:
`rhoDigits` truncates at `Φ.φ.natDegree` by construction
(`RhoDigits.lean:135–136, 141–143`), so the coefficients an `Rq` would drop
are ones `rhoDigits` discards anyway; the truncation is lossless because
`LiftedWitness.hρ` bounds every row by `natDegree ≤ d − 1`
(`RhoDigits.lean:126–129`, and `rhoDigits_reconstruct` takes exactly that
hypothesis, `:178–179`); and the output is itself `d`-wide
(`rhoDigits_natDegree_le`, `:150–153`), so `Rq::from_coeffs` reads it back
losslessly — the same argument the pin makes for `Rq.ofFinCoeff`
(`:149–150`). The `hρ` bound must travel as a hypothesis on the `_spec`,
alongside `Wf`.

**Nothing to translate for the side conditions.** `DigitBaseOk`
(`RingSwitch/Reduction.lean:175–181`), `RhoDigitsShort` (`:159–161`) and
`liftShort` (`:211`) are `Prop`s. Their decidable counterparts
`rhoDigitsShortCheck` / `liftShortCheck` (`EndPiece/Reduction.lean:111–113,
144`) *are* runtime code, but they belong to target 6, and at these parameters
the digit conjunct is a tautology
(`rhoDigitsShortCheck_eq_true_of_digitBaseOk`, `:138–141`) — worth carrying
forward as a note, since a Rust `liftShortCheck` that recomputes it is doing
provably redundant work.

---

## Scale policy (fixed at Stage 2, with one refinement)

`STAGE2_SCOPING.md` § "Scale policies", row 1: **real consts for both
semantics tests and bench cases; birth case per op** (digit ops are cheap).
Confirmed for the digit layer proper —
`balanced_digit_at`, `balanced_digit_decompose`, `balanced_gadget_decompose`
(at `rows = MESSAGE_ROWS = 1024`, mirroring the existing
`gadget/gadget_decompose` registration, `hachi/benches/gadget.rs:291–292`) and
`rho_digits` — all of which are coefficientwise and land in the tens of
milliseconds or below.

**⊗ refinement.** The row cannot be applied to the two commit-path siblings §
"Decision 4"'s own table introduces. `generate_decomps_balanced` and
`commit_balanced` are `ring::mul`-bound, not digit-bound: per block one
`A · s` of 8192 ring muls (~25 s at `d = 1024` schoolbook), `BLOCKS = 1024`
blocks. Their unsigned twins are already excluded for exactly this reason
(`hachi/benches/exclusions.toml:94–99, 110–113`), so the siblings inherit the
**Fig. 9 policy exception verbatim**, with the same removal condition (a
sub-quadratic `ring::mul` champion) and the same `#[ignore]`d full-const test
route. Real-const *semantics tests* still apply to the digit layer; a
`commit_balanced` round-trip test must be REDUCED or `#[ignore]`d, naming the
8192-ring-mul arithmetic that forces it, per the `exclusions.toml` bar.
