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

/-- `impl Add for Fp`. -/
@[step]
theorem fp_add_spec (a b : cpoly.field.Fp) (ha : Red a) (hb : Red b) :
    cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add a b
      ⦃ c => Red c ∧ toK c = toK a + toK b ⦄ := by
  unfold Red at ha hb
  rw [cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add]
  step as ⟨i, hi⟩
  step as ⟨c, hc⟩
  refine ⟨?_, ?_⟩
  · unfold Red; rw [hc, cpoly_P_val]; exact Nat.mod_lt _ (by decide)
  · simp only [toK, hc, cpoly_P_val, ZMod.natCast_mod, hi, Nat.cast_add]

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
  step as ⟨i, hi⟩          -- i = a + q
  step as ⟨j, hj⟩          -- j = i - b
  step as ⟨c, hc⟩          -- c = j % q
  refine ⟨?_, ?_⟩
  · unfold Red; rw [hc, cpoly_P_val]; exact Nat.mod_lt _ (by decide)
  · have hbi : b.val ≤ a.val + q := by scalar_tac
    simp only [toK, hc, cpoly_P_val, ZMod.natCast_mod, hj, hi]
    rw [Nat.cast_sub hbi, Nat.cast_add, ZMod.natCast_self]
    ring

/-- `impl Neg for Fp`. The outer `% q` is what sends `0` to `0` rather than to
`q`. -/
@[step]
theorem fp_neg_spec (a : cpoly.field.Fp) (ha : Red a) :
    cpoly.field.Fp.Insts.CoreOpsArithNegFp.neg a ⦃ c => Red c ∧ toK c = - toK a ⦄ := by
  unfold Red at ha
  rw [cpoly.field.Fp.Insts.CoreOpsArithNegFp.neg]
  step as ⟨i, hi⟩          -- i = q - a
  step as ⟨c, hc⟩          -- c = i % q
  refine ⟨?_, ?_⟩
  · unfold Red; rw [hc, cpoly_P_val]; exact Nat.mod_lt _ (by decide)
  · have hai : a.val ≤ q := by scalar_tac
    simp only [toK, hc, cpoly_P_val, ZMod.natCast_mod, hi]
    rw [Nat.cast_sub hai, ZMod.natCast_self]
    ring

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
