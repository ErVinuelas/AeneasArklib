/-
The **base-field layer** of the equivalence: the extracted `cpoly.field.Fp`
operations (see `Generated.lean`) against arithmetic in `ZMod q`.

This is the bottom of the development. Every operation above it — the ring, the
gadget, the commitment — computes coefficientwise through these four impls, so
their specs are what discharge the no-overflow side conditions everywhere else.

## Why these proofs are here rather than imported

`cpoly` proves exactly these theorems in its own `lean/Field.lean`, and reusing
them was the intended plan. It is not available: those proofs are stated against
`CompPoly.Extension.Ext Hachi.ext4Params`, which exists only in CompPoly's Lean
v4.32.0 tree, while this development is pinned to v4.31.0 because ArkLib is, and
one Lake package cannot have both. NOTES.md § "What the cpoly dependency does
*not* buy: its Lean proofs" records the cost; this file is that cost, paid. The
proofs follow cpoly's, restated against `ZMod q` directly.

## What a spec says

Aeneas's triple `m ⦃ r => post r ⦄` is `Aeneas.Std.spec m post`, a
weakest-precondition predicate that already implies `∃ r, m = ok r`. So each
theorem below carries two claims, and the first is not decoration:

1. **totality** — the operation returns `ok`; no `u64` intermediate overflows;
2. **agreement** — its result maps, under `toK`, to the `ZMod q` operation.

`Red u` (`u.val < q`) is what makes the first half true, and it is the whole
no-overflow argument: `q < 2^32`, so a sum of two reduced words is below `2^33`
and a product below `2^64`, with room to spare. Rust maintains it by construction
— `Fp`'s inner `u64` is private and `Fp::new` reduces — but Aeneas cannot see a
privacy boundary, so it travels as a hypothesis.

The specs are `@[step]`, which is what lets the layers above walk through generated
code without naming them.
-/
import Generated
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.Field

/-! ## The modulus -/

/-- The modulus `q = 2^32 - 99`, the Hachi prime. An `abbrev` so that `ZMod q`
unfolds to `Fin q` and its `CommRing` instance is found by synthesis.

Primality is not needed here and so not assumed: the field *operations* are
modular arithmetic, and `ZMod q` is a commutative ring whatever `q` is. Primality
is what makes `ZMod q` a field, which the layers above need (`Rq` is stated over a
`Field`) and `lean/Check.lean` § 1 checks. -/
abbrev q : ℕ := 4294967197

/-- The base-field element a word represents. -/
def toK (u : cpoly.field.Fp) : ZMod q := (u.val : ZMod q)

/-- Representation invariant: the word is reduced mod `q`. Maintained by every
operation below, and required to discharge their no-overflow obligations. -/
def Red (u : cpoly.field.Fp) : Prop := u.val < q

/-- The generated modulus word has value `q`. It is `irreducible`, so this is the
way in, and it is `scalar_tac_simps` so that the arithmetic side conditions in the
generated code can use it. -/
@[simp, scalar_tac_simps]
theorem cpoly_P_val : (cpoly.field.P).val = q := by simp only [cpoly.field.P]; decide

/-- This crate's own `Q` is the same modulus. If these two ever disagree, every
proof bridging the layers is about two different fields. -/
@[simp, scalar_tac_simps]
theorem params_Q_val : (params.Q).val = q := by simp only [params.Q]; decide

@[simp, scalar_tac_simps]
theorem cpoly_Fp_ZERO_val : (cpoly.field.Fp.ZERO).val = 0 := by
  simp only [cpoly.field.Fp.ZERO]; decide

@[simp, scalar_tac_simps]
theorem cpoly_Fp_ONE_val : (cpoly.field.Fp.ONE).val = 1 := by
  simp only [cpoly.field.Fp.ONE]; decide

@[simp] theorem toK_zero : toK cpoly.field.Fp.ZERO = 0 := by
  simp only [toK, cpoly_Fp_ZERO_val, Nat.cast_zero]

@[simp] theorem toK_one : toK cpoly.field.Fp.ONE = 1 := by
  simp only [toK, cpoly_Fp_ONE_val, Nat.cast_one]

theorem Red_zero : Red cpoly.field.Fp.ZERO := by
  simp only [Red, cpoly_Fp_ZERO_val]; decide

theorem Red_one : Red cpoly.field.Fp.ONE := by
  simp only [Red, cpoly_Fp_ONE_val]; decide

/-- `m >>= ok` is `m`. Aeneas ends a `do` block this way whenever the Rust tail
expression is a local it has just bound, which is most of them, and the shape
blocks `spec_mono` from seeing the last call as the whole body. -/
@[simp] theorem bind_ok_id {α : Type} (m : Result α) : (do let x ← m; ok x) = m := by
  cases m <;> rfl

/-! ## The operator impls -/

/-- `impl Add for Fp`. **A conditional subtraction, not a `%`** since the
2026-09-16 cpoly bump: `a + b < 2q < 2^33` for reduced operands, so one subtract
suffices and the division is gone. `Red` is what rules out the second subtract,
and `↑q = 0` in `ZMod q` is what makes the branch invisible on the
specification side. -/
@[step]
theorem fp_add_spec (a b : cpoly.field.Fp) (ha : Red a) (hb : Red b) :
    cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add a b
      ⦃ c => Red c ∧ toK c = toK a + toK b ⦄ := by
  unfold Red at ha hb
  rw [cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add]
  step as ⟨sum, hsum⟩
  by_cases hge : sum ≥ cpoly.field.P
  · rw [if_pos hge]
    have hgev : q ≤ sum.val := by rw [← cpoly_P_val]; scalar_tac
    step as ⟨c, hc⟩
    refine ⟨?_, ?_⟩
    · unfold Red; rw [hc, cpoly_P_val]; omega
    · simp only [toK, hc, cpoly_P_val, hsum]
      rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self]
      ring
  · rw [if_neg hge, WP.spec_ok]
    refine ⟨?_, ?_⟩
    · unfold Red
      have hlt : sum.val < (cpoly.field.P).val := by scalar_tac
      rw [cpoly_P_val] at hlt; exact hlt
    · simp only [toK, hsum, Nat.cast_add]

/-- `impl Mul for Fp`. The generated `a * b` is a *checked* `U64` product; it
succeeds because `q < 2^32` forces `a * b ≤ (q-1)^2 < 2^64`. -/
@[step]
theorem fp_mul_spec (a b : cpoly.field.Fp) (ha : Red a) (hb : Red b) :
    cpoly.field.Fp.Insts.CoreOpsArithMulFpFp.mul a b
      ⦃ c => Red c ∧ toK c = toK a * toK b ⦄ := by
  unfold Red at ha hb
  rw [cpoly.field.Fp.Insts.CoreOpsArithMulFpFp.mul]
  step as ⟨i, hi⟩
  step as ⟨c, hc⟩
  refine ⟨?_, ?_⟩
  · unfold Red; rw [hc, cpoly_P_val]; exact Nat.mod_lt _ (by decide)
  · simp only [toK, hc, cpoly_P_val, ZMod.natCast_mod, hi, Nat.cast_mul]

/-- `impl Sub for Fp`. The Rust adds `q` before subtracting, which is what keeps
the `u64` from going negative; `↑q = 0` in `ZMod q` is what makes that invisible
on the specification side. -/
@[step]
theorem fp_sub_spec (a b : cpoly.field.Fp) (ha : Red a) (hb : Red b) :
    cpoly.field.Fp.Insts.CoreOpsArithSubFpFp.sub a b
      ⦃ c => Red c ∧ toK c = toK a - toK b ⦄ := by
  unfold Red at ha hb
  rw [cpoly.field.Fp.Insts.CoreOpsArithSubFpFp.sub]
  by_cases hge : a ≥ b
  · rw [if_pos hge]
    have hgev : b.val ≤ a.val := by scalar_tac
    step as ⟨c, hc⟩
    refine ⟨?_, ?_⟩
    · unfold Red; omega
    · simp only [toK, hc]
      rw [Nat.cast_sub hgev]
  · rw [if_neg hge]
    have hlt : a.val < b.val := by scalar_tac
    step as ⟨i, hi⟩          -- i = a + q
    step as ⟨c, hc⟩          -- c = i - b
    refine ⟨?_, ?_⟩
    · unfold Red; rw [hc, hi, cpoly_P_val]; omega
    · simp only [toK, hc, hi, cpoly_P_val]
      rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self]
      ring

/-- `impl Neg for Fp`. Since the 2026-09-16 cpoly bump this **branches on zero**
rather than reducing: the old body computed `(q - a) % q`, where the outer `%`
was what sent `0` to `0` instead of to `q`. The branch does the same job without
a division, and `a = 0` is now a case of the proof rather than a consequence of
the arithmetic. -/
@[step]
theorem fp_neg_spec (a : cpoly.field.Fp) (ha : Red a) :
    cpoly.field.Fp.Insts.CoreOpsArithNegFp.neg a ⦃ c => Red c ∧ toK c = - toK a ⦄ := by
  unfold Red at ha
  rw [cpoly.field.Fp.Insts.CoreOpsArithNegFp.neg]
  by_cases hz : a = 0#u64
  · rw [if_pos hz, WP.spec_ok]
    refine ⟨?_, ?_⟩
    · unfold Red; decide
    · rw [hz]; simp [toK]
  · rw [if_neg hz]
    have hpos : 0 < a.val := by
      rcases Nat.eq_zero_or_pos a.val with h | h
      · exact absurd (by scalar_tac : a = 0#u64) hz
      · exact h
    step as ⟨c, hc⟩          -- c = q - a
    refine ⟨?_, ?_⟩
    · unfold Red; rw [hc, cpoly_P_val]; omega
    · have hai : a.val ≤ q := by scalar_tac
      simp only [toK, hc, cpoly_P_val]
      rw [Nat.cast_sub hai, ZMod.natCast_self]
      ring

/-! ## The two-word accumulator and its reduction

New with the 2026-09-16 cpoly bump. `Ext4::mul` no longer reduces after every
base multiplication: it accumulates sixteen unreduced products into four
two-word `(low, high)` pairs and reduces each pair once. These are the specs
that layer needs.

They are **transcribed** from AeneasCompPoly's own `cpoly/lean/Field.lean` at
`d7e26bb` rather than imported, and the reason is concrete: that package is on
Lean/Mathlib **v4.32.0** on its own aeneas fork, this one is on **v4.33.1**, and
one Lake build cannot hold both toolchains.

`wideK` is the field image of such a pair, and the constant `9801` is the whole
trick: `q = 2^32 - 99`, so `2^32 ≡ 99` and `2^64 ≡ 99² = 9801 (mod q)`. The high
word therefore folds down by a *multiplication* instead of a division, which is
what makes deferring the reduction worth anything. The `≤ 5` and `≤ 7` carry
bounds are what keep the fold inside one `u64`; the caller threads them along
the accumulator chain. -/

/-- A product of two reduced representatives is a *checked* `u64` product:
`q < 2^32` forces `(q-1)² < 2^64`. The accumulator relies on this before it
starts preserving carries by hand. -/
theorem red_mul_fits_u64 (x y : cpoly.field.Fp) (hx : Red x) (hy : Red y) :
    x.val * y.val ≤ Std.U64.max := by
  unfold Red at hx hy
  have h : x.val * y.val ≤ (q - 1) * (q - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hmax : (q - 1) * (q - 1) ≤ Std.U64.max := by
    simp only [Std.U64.max, Std.U64.numBits]; norm_num
  omega

/-- The field image of one machine-word carry. -/
def carryK (b : Bool) : ZMod q := if b then 1 else 0

/-- The field image of the two-word integer an accumulator represents:
`high · 2^64 + low`, with `2^64` already folded to `9801`. -/
def wideK (acc : Std.U64 × Std.U64) : ZMod q :=
  ((acc.2.val : ℕ) : ZMod q) * 9801 + ((acc.1.val : ℕ) : ZMod q)

/-- `2^64 ≡ 9801 (mod q)`, which is `(2^32)² ≡ 99²` composed with
`q = 2^32 − 99`. This is the only arithmetic fact the whole layer rests on. -/
@[simp] theorem u64_size_toK : ((Std.U64.size : ℕ) : ZMod q) = 9801 := by
  have hsz : (Std.U64.size : ℕ) = 18446744073709551616 := by
    simp only [Std.U64.size, Std.U64.numBits]; norm_num
  rw [hsz]
  decide

/-- `overflowing_add` preserves the represented integer, reading its boolean
carry as `0` or `1` scaled by `2^64 ≡ 9801`. -/
theorem overflowing_add_toK (x y : Std.U64) :
    (((core.num.U64.overflowing_add x y).1.val : ℕ) : ZMod q) +
        carryK ((core.num.U64.overflowing_add x y).2) * 9801 =
      ((x.val : ℕ) : ZMod q) + ((y.val : ℕ) : ZMod q) := by
  have h := core.num.U64.overflowing_add_eq x y
  dsimp only at h
  by_cases hov : x.val + y.val > Std.UScalar.max .U64
  · rw [if_pos hov] at h
    obtain ⟨hval, hcarry⟩ := h
    rw [hcarry]
    have hK := congrArg (fun n : ℕ => (n : ZMod q)) hval
    simpa [carryK, u64_size_toK] using hK
  · rw [if_neg hov] at h
    obtain ⟨hval, hcarry⟩ := h
    rw [hcarry]
    have hK := congrArg (fun n : ℕ => (n : ZMod q)) hval
    simpa [carryK] using hK

/-- Adding one raw product preserves the accumulator's field image. The `u64`
low word is allowed to **wrap**; its carry is recorded in the high word, which
is why the spec is about `wideK` and not about either word alone. -/
@[step]
theorem add_product_spec (acc : Std.U64 × Std.U64) (a b : cpoly.field.Fp)
    (ha : Red a) (hb : Red b) (hacc : acc.2.val ≤ 5) :
    cpoly.field.add_product acc a b ⦃ out =>
      out.2.val ≤ acc.2.val + 1 ∧ wideK out = wideK acc + toK a * toK b ⦄ := by
  rw [cpoly.field.add_product]
  apply spec_bind (Std.U64.mul_spec (red_mul_fits_u64 a b ha hb))
  intro product hproduct
  simp only [lift]
  simp
  apply spec_bind (Std.U64.add_spec (by
    change acc.2.val + (core.convert.num.FromU64Bool.from
      (core.num.U64.overflowing_add acc.1 product).2).val ≤ Std.U64.max
    simp only [core.convert.num.FromU64Bool.from]
    split <;> norm_num [Std.U64.max_eq] at hacc ⊢ <;> omega))
  intro high hhigh
  simp only [spec_ok]
  simp only [wideK]
  change high.val = acc.2.val +
      (core.convert.num.FromU64Bool.from
        (core.num.U64.overflowing_add acc.1 product).2).val at hhigh
  have hcarry :
      (core.convert.num.FromU64Bool.from
        (core.num.U64.overflowing_add acc.1 product).2).val =
        if (core.num.U64.overflowing_add acc.1 product).2 then 1 else 0 := by
    cases (core.num.U64.overflowing_add acc.1 product).2 <;>
      simp [core.convert.num.FromU64Bool.from, Std.UScalar.val]
  constructor
  · rw [hhigh, hcarry]
    split <;> omega
  · change (((high.val : ℕ) : ZMod q) * 9801 +
      (((core.num.U64.overflowing_add acc.1 product).1.val : ℕ) : ZMod q)) = _
    rw [hhigh, hcarry]
    have hcarryK :
        ((if (core.num.U64.overflowing_add acc.1 product).2 then 1 else 0 : ℕ) : ZMod q) =
          carryK (core.num.U64.overflowing_add acc.1 product).2 := by
      simp [carryK]
    have hproductK : ((product.val : ℕ) : ZMod q) = toK a * toK b := by
      rw [hproduct]; unfold toK; norm_cast
    rw [Nat.cast_add, hcarryK, ← hproductK]
    have hoverflow := overflowing_add_toK acc.1 product
    linear_combination hoverflow

/-- Adding twice one raw reduced-coefficient product preserves the field image
of the accumulator.  This is the `2 * aᵢbⱼ` wrap contribution in `Ext4::mul` -- the factor that used to be a
multiplication by the constant `W = 2`, and is now folded into the accumulator,
which is why `cpoly.field.W` no longer appears in the extracted model at all. -/
@[step]
theorem add_double_product_spec (acc : Std.U64 × Std.U64) (a b : cpoly.field.Fp)
    (ha : Red a) (hb : Red b) (hacc : acc.2.val ≤ 5) :
    cpoly.field.add_double_product acc a b ⦃ out =>
      out.2.val ≤ acc.2.val + 2 ∧ wideK out = wideK acc + 2 * toK a * toK b ⦄ := by
  rw [cpoly.field.add_double_product]
  apply spec_bind (Std.U64.mul_spec (red_mul_fits_u64 a b ha hb))
  intro product hproduct
  simp only [lift]
  simp
  change (do
    let high0 ← acc.2 + core.convert.num.FromU64Bool.from
      (core.num.U64.overflowing_add acc.1 product).2
    let high1 ← high0 + core.convert.num.FromU64Bool.from
      (core.num.U64.overflowing_add (core.num.U64.overflowing_add acc.1 product).1 product).2
    ok ((core.num.U64.overflowing_add (core.num.U64.overflowing_add acc.1 product).1 product).1,
      high1)) ⦃ out => out.2.val ≤ acc.2.val + 2 ∧
        wideK out = wideK acc + 2 * toK a * toK b ⦄
  apply spec_bind (Std.U64.add_spec (by
    simp only [core.convert.num.FromU64Bool.from]
    split <;> norm_num [Std.U64.max_eq] at hacc ⊢ <;> omega))
  intro high0 hhigh0
  apply spec_bind (Std.U64.add_spec (by
    have hcarry0 : (core.convert.num.FromU64Bool.from
      (core.num.U64.overflowing_add acc.1 product).2).val ≤ 1 := by
      cases (core.num.U64.overflowing_add acc.1 product).2 <;>
        simp [core.convert.num.FromU64Bool.from, Std.UScalar.val]
    have : high0.val ≤ acc.2.val + 1 := by
      rw [hhigh0]
      omega
    simp only [core.convert.num.FromU64Bool.from]
    split <;> norm_num [Std.U64.max_eq] at hacc ⊢ <;> omega))
  intro high1 hhigh1
  simp only [spec_ok]
  have hcarry0 : (core.convert.num.FromU64Bool.from
      (core.num.U64.overflowing_add acc.1 product).2).val =
      if (core.num.U64.overflowing_add acc.1 product).2 then 1 else 0 := by
    cases (core.num.U64.overflowing_add acc.1 product).2 <;>
      simp [core.convert.num.FromU64Bool.from, Std.UScalar.val]
  have hcarry1 : (core.convert.num.FromU64Bool.from
      (core.num.U64.overflowing_add
        (core.num.U64.overflowing_add acc.1 product).1 product).2).val =
      if (core.num.U64.overflowing_add
        (core.num.U64.overflowing_add acc.1 product).1 product).2 then 1 else 0 := by
    cases (core.num.U64.overflowing_add
      (core.num.U64.overflowing_add acc.1 product).1 product).2 <;>
      simp [core.convert.num.FromU64Bool.from, Std.UScalar.val]
  constructor
  · rw [hhigh1, hhigh0, hcarry0, hcarry1]
    split <;> split <;> omega
  · simp only [wideK]
    change (((high1.val : ℕ) : ZMod q) * 9801 +
      (((core.num.U64.overflowing_add
        (core.num.U64.overflowing_add acc.1 product).1 product).1.val : ℕ) : ZMod q)) = _
    change high0.val = acc.2.val +
      (core.convert.num.FromU64Bool.from
        (core.num.U64.overflowing_add acc.1 product).2).val at hhigh0
    change high1.val = high0.val +
      (core.convert.num.FromU64Bool.from
        (core.num.U64.overflowing_add
          (core.num.U64.overflowing_add acc.1 product).1 product).2).val at hhigh1
    rw [hhigh1, hhigh0, hcarry0, hcarry1]
    have hcarry0K :
        ((if (core.num.U64.overflowing_add acc.1 product).2 then 1 else 0 : ℕ) : ZMod q) =
          carryK (core.num.U64.overflowing_add acc.1 product).2 := by
      simp [carryK]
    have hcarry1K :
        ((if (core.num.U64.overflowing_add
          (core.num.U64.overflowing_add acc.1 product).1 product).2 then 1 else 0 : ℕ) : ZMod q) =
          carryK (core.num.U64.overflowing_add
            (core.num.U64.overflowing_add acc.1 product).1 product).2 := by
      simp [carryK]
    have hproductK : ((product.val : ℕ) : ZMod q) = toK a * toK b := by
      rw [hproduct]
      unfold toK
      norm_cast
    simp only [Nat.cast_add]
    rw [hcarry0K, hcarry1K]
    have hoverflow0 := overflowing_add_toK acc.1 product
    have hoverflow1 := overflowing_add_toK
      (core.num.U64.overflowing_add acc.1 product).1 product
    linear_combination hoverflow0 + hoverflow1 + 2 * hproductK

/-- The two-word reduction, and the reason deferring reductions pays: it turns
`high · 2^64 + low` into a canonical representative with **two multiplications by
a small constant and one conditional subtraction**, where the old body paid a
`u64` division per base multiplication.

`2^32 ≡ 99` and `2^64 ≡ 9801 (mod q)`, so `low` folds at 32 bits twice and
`high` enters scaled by `9801`. The `high.val ≤ 7` contract is what keeps every
intermediate inside one `u64`; `ext_mul_spec` below discharges it from the carry
bounds its sixteen accumulator steps carry along. -/
@[step]
theorem reduce_wide_spec (low high : Std.U64) (hhigh : high.val ≤ 7) :
    cpoly.field.reduce_wide low high ⦃ out =>
      Red out ∧ toK out = wideK (low, high) ⦄ := by
  rw [cpoly.field.reduce_wide]
  rw [cpoly.field.reduce_wide.LIMB]
  step as ⟨limb, hlimb⟩
  norm_num [U64.size, U64.numBits] at hlimb
  have hshift : ((1 <<< 32 : Nat) % 18446744073709551616) = 4294967296 := by
    decide
  rw [hshift] at hlimb
  step as ⟨r0, hr0⟩
  step as ⟨q0, hq0⟩
  step as ⟨x0, hx0⟩
  step as ⟨s0, hs0⟩
  step as ⟨x1, hx1⟩
  step as ⟨folded_once, hfolded_once⟩
  step as ⟨r1, hr1⟩
  step as ⟨q1, hq1⟩
  step as ⟨x2, hx2⟩
  step as ⟨folded_twice, hfolded_twice⟩
  have hdecomp0 : r0.val + 4294967296 * q0.val = low.val := by
    rw [hr0, hq0, hlimb]
    exact Nat.mod_add_div low.val 4294967296
  have hdecomp1 : r1.val + 4294967296 * q1.val = folded_once.val := by
    rw [hr1, hq1, hlimb]
    exact Nat.mod_add_div folded_once.val 4294967296
  have hL : ((4294967296 : Nat) : ZMod q) = (99 : ZMod q) := by
    have hP : q = 4294967197 := rfl
    apply (ZMod.natCast_eq_natCast_iff' 4294967296 99 q).2
    rw [hP]
  have hdecomp0K' := congrArg (fun n : Nat => (n : ZMod q)) hdecomp0
  have hdecomp0K : (r0.val : ZMod q) + ((4294967296 : Nat) : ZMod q) * (q0.val : ZMod q) = (low.val : ZMod q) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using hdecomp0K'
  have hdecomp1K' := congrArg (fun n : Nat => (n : ZMod q)) hdecomp1
  have hdecomp1K : (r1.val : ZMod q) + ((4294967296 : Nat) : ZMod q) * (q1.val : ZMod q) = (folded_once.val : ZMod q) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using hdecomp1K'
  have htwiceK' := congrArg (fun n : Nat => (n : ZMod q)) hfolded_twice
  have htwiceK : (folded_twice.val : ZMod q) = (r1.val : ZMod q) + (x2.val : ZMod q) := by
    simpa only [Nat.cast_add] using htwiceK'
  have honceK' := congrArg (fun n : Nat => (n : ZMod q)) hfolded_once
  have honceK : (folded_once.val : ZMod q) = (s0.val : ZMod q) + (x1.val : ZMod q) := by
    simpa only [Nat.cast_add] using honceK'
  have hs0K' := congrArg (fun n : Nat => (n : ZMod q)) hs0
  have hs0K : (s0.val : ZMod q) = (r0.val : ZMod q) + (x0.val : ZMod q) := by
    simpa only [Nat.cast_add] using hs0K'
  have hx0K' := congrArg (fun n : Nat => (n : ZMod q)) hx0
  have hx0K : (x0.val : ZMod q) = ((99 : Nat) : ZMod q) * (q0.val : ZMod q) := by
    simpa only [Nat.cast_mul] using hx0K'
  have hx1K' := congrArg (fun n : Nat => (n : ZMod q)) hx1
  have hx1K : (x1.val : ZMod q) = ((9801 : Nat) : ZMod q) * (high.val : ZMod q) := by
    simpa only [Nat.cast_mul] using hx1K'
  have hx2K' := congrArg (fun n : Nat => (n : ZMod q)) hx2
  have hx2K : (x2.val : ZMod q) = ((99 : Nat) : ZMod q) * (q1.val : ZMod q) := by
    simpa only [Nat.cast_mul] using hx2K'
  have hfoldedK : (folded_twice.val : ZMod q) = wideK (low, high) := by
    calc
      (folded_twice.val : ZMod q) = (r1.val : ZMod q) + ((99 : Nat) : ZMod q) * (q1.val : ZMod q) := by
        rw [htwiceK, hx2K]
      _ = (r1.val : ZMod q) + ((4294967296 : Nat) : ZMod q) * (q1.val : ZMod q) := by
        rw [hL]
        norm_num
      _ = (folded_once.val : ZMod q) := hdecomp1K
      _ = (r0.val : ZMod q) + ((99 : Nat) : ZMod q) * (q0.val : ZMod q) +
        ((9801 : Nat) : ZMod q) * (high.val : ZMod q) := by
        rw [honceK, hs0K, hx0K, hx1K]
      _ = (low.val : ZMod q) + ((9801 : Nat) : ZMod q) * (high.val : ZMod q) := by
        rw [hL] at hdecomp0K
        linear_combination hdecomp0K
      _ = wideK (low, high) := by
        simp only [wideK]
        ring
  have hlow : low.val < 18446744073709551616 := by
    have hlow' := low.hBounds
    norm_num [UScalarTy.U64_numBits_eq] at hlow'
    exact hlow'
  have hq0 : q0.val < 4294967296 := by
    rw [hq0, hlimb]
    apply (Nat.div_lt_iff_lt_mul (by norm_num)).2
    norm_num
    exact hlow
  have hr0 : r0.val < 4294967296 := by
    rw [hr0, hlimb]
    exact Nat.mod_lt _ (by norm_num)
  have hs0 : s0.val < 429496729600 := by
    rw [hs0, hx0]
    omega
  have hx1 : x1.val ≤ 68607 := by
    rw [hx1]
    omega
  have hfolded_once : folded_once.val < 433791696896 := by
    rw [hfolded_once]
    omega
  have hq1 : q1.val < 101 := by
    rw [hq1, hlimb]
    apply (Nat.div_lt_iff_lt_mul (by norm_num)).2
    norm_num
    exact hfolded_once
  have hr1 : r1.val < 4294967296 := by
    rw [hr1, hlimb]
    exact Nat.mod_lt _ (by norm_num)
  have hfolded_twice : folded_twice.val < 4294977196 := by
    rw [hfolded_twice, hx2]
    omega
  have hP : q = 4294967197 := rfl
  have htwice_twoP : folded_twice.val < 2 * q := by
    rw [hP]
    omega
  by_cases hP_le : q ≤ folded_twice.val
  · have hif : folded_twice ≥ cpoly.field.P := by
      simpa [cpoly_P_val] using hP_le
    rw [if_pos hif]
    -- the subtraction's side condition is discharged by `step` itself here; the
    -- 4.32 original needed an explicit `simpa … using hP_le` bullet for it.
    step as ⟨out, hout⟩
    refine ⟨?_, ?_⟩
    · unfold Red
      rw [hout, cpoly_P_val, hP] at *
      omega
    · have hp_le : cpoly.field.P.val ≤ folded_twice.val := by
        simpa [cpoly_P_val] using hP_le
      unfold toK
      rw [hout, Nat.cast_sub hp_le, cpoly_P_val, ZMod.natCast_self]
      simpa using hfoldedK
  · have hif : ¬ folded_twice ≥ cpoly.field.P := by
      intro h
      apply hP_le
      simpa [cpoly_P_val] using h
    rw [if_neg hif]
    refine ⟨?_, hfoldedK⟩
    unfold Red
    simpa [cpoly_P_val] using Nat.lt_of_not_ge hP_le

/-! ## Construction and observation

`Fp::new` and `Fp::to_u64` are the boundary of the representation: the first is
the only way an arbitrary word enters the field, and the second is how this crate
compares field elements (`Rq::equals` goes through it rather than through a derived
`PartialEq`, so that there is one notion of equality per type). -/

/-- `Fp::new` — reduces, so its result satisfies `Red` for *any* input word. This
is the theorem that makes `Red` an invariant of construction rather than an
assumption: nothing outside this boundary can produce an unreduced `Fp`. -/
@[step]
theorem fp_new_spec (v : Std.U64) :
    cpoly.field.Fp.new v ⦃ c => Red c ∧ toK c = (v.val : ZMod q) ⦄ := by
  rw [cpoly.field.Fp.new]
  step as ⟨c, hc⟩
  refine ⟨?_, ?_⟩
  · unfold Red; rw [hc, cpoly_P_val]; exact Nat.mod_lt _ (by decide)
  · simp only [toK, hc, cpoly_P_val, ZMod.natCast_mod]

/-- `Fp::to_u64` — the canonical representative. Total, and injective on reduced
words, which is what licenses comparing two `Fp`s by comparing their words:
`toK a = toK b ↔ a.val = b.val` for reduced `a`, `b`. -/
theorem toK_inj_of_Red {a b : cpoly.field.Fp} (ha : Red a) (hb : Red b) :
    toK a = toK b ↔ a.val = b.val := by
  unfold Red at ha hb
  constructor
  · intro h
    have := (ZMod.natCast_eq_natCast_iff' a.val b.val q).mp h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · intro h; unfold toK; rw [h]

end HachiEquiv.Field
