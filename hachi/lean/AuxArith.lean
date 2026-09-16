/-
The **auxiliary modular arithmetic** of `hachi.ntt`: Barrett reduction, and
addition, subtraction and multiplication modulo a runtime prime.

This is the bottom of the transform layer, and it plays the role `Field.lean`
plays for `Fp`: every loop above computes through these four operations, so
their specs are what discharge the no-overflow side conditions everywhere else.

## Why the modulus is a variable

`hachi::ntt` runs the same transform at three different primes, and passes the
prime (and its Barrett magic) as arguments rather than monomorphising. So the
theorems here are stated for an arbitrary `(p, m)` satisfying [`Magic`], and
`AuxNTT.lean` instantiates them three times. The alternative -- three copies of
the code with the modulus as a literal -- would be three copies of every proof
above this file too.

## What a spec says

Aeneas's triple already implies `∃ r, m = ok r`, so each theorem carries two
claims:

1. **totality** -- no `u64` or `u128` intermediate overflows and no division by
   zero;
2. **agreement** -- the result is the corresponding `ℕ` operation mod `p`.

The statements stay in `ℕ` rather than moving to `ZMod p`: at this level every
operation *is* a `%`, the modulus is a variable, and a `ZMod p` statement would
need a `NeZero p` instance threaded through three primes for no gain. The move
to `ZMod p` happens one layer up, where the ring structure is what the transform
argument needs.
-/
import Generated
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.AuxArith

/-! ## The Barrett precondition

`Magic p m` is everything `ntt::aux_reduce` needs of its modulus and magic
constant. `p < 2^32` is what keeps `a * b` inside a `u64` one layer up, and it is
also (with `2 ≤ p`) what keeps `x * m` inside a `u128`: `m = ⌊2^64/p⌋ ≤ 2^63`.
-/

/-- The contract between a modulus and its Barrett magic constant. -/
structure Magic (p m : Std.U64) : Prop where
  /-- `p` is at least `2`: `p = 1` would put `2^64` in `m`, which is not a `u64`,
  and `p = 0` would make the reduction meaningless. -/
  two_le : 2 ≤ p.val
  /-- `p < 2^32`, the bound that keeps a product of two residues in a `u64`. -/
  lt_pow : p.val < 2 ^ 32
  /-- `m` is the Barrett magic: `⌊2^64 / p⌋`. -/
  magic : m.val = 2 ^ 64 / p.val

theorem Magic.pos {p m : Std.U64} (h : Magic p m) : 0 < p.val :=
  Nat.lt_of_lt_of_le Nat.zero_lt_two h.two_le

/-! ## The three `ℕ` facts behind the reduction

The quotient estimate `qh = ⌊x·m / 2^64⌋` is either `⌊x/p⌋` or one less than it,
so one conditional subtraction finishes the job. Split into the three statements
the Aeneas proof actually uses: the estimate never overshoots (so the `u64`
subtraction is total), it undershoots by less than one `p` (so one correction
suffices), and the correction lands on `x % p`.
-/

/-- The Barrett quotient never overshoots, which is what makes `x - qh·p` total.

`qh·2^64 ≤ x·m` because `qh` is a floor, and `m·p ≤ 2^64` because `m` is one
too; multiplying the first by `p` and the second by `x` meets in the middle. -/
theorem barrett_quot_le (x p m : ℕ) (hm : m = 2 ^ 64 / p) :
    (x * m / 2 ^ 64) * p ≤ x := by
  have hmp : m * p ≤ 2 ^ 64 := by rw [hm]; exact Nat.div_mul_le_self _ _
  have hq : (x * m / 2 ^ 64) * 2 ^ 64 ≤ x * m := Nat.div_mul_le_self _ _
  have key : (x * m / 2 ^ 64) * p * 2 ^ 64 ≤ x * 2 ^ 64 := by
    calc (x * m / 2 ^ 64) * p * 2 ^ 64
        = ((x * m / 2 ^ 64) * 2 ^ 64) * p := by ring
      _ ≤ (x * m) * p := Nat.mul_le_mul_right _ hq
      _ = x * (m * p) := by ring
      _ ≤ x * 2 ^ 64 := Nat.mul_le_mul_left _ hmp
  exact Nat.le_of_mul_le_mul_right key (by positivity)

/-- The Barrett quotient undershoots by less than one `p`, which is what makes a
*single* conditional subtraction enough.

`x·m < (qh+1)·2^64` because `qh` is a floor, and `2^64 = m·p + s` with `s < p`,
so `x·2^64 = (x·m)·p + x·s` and the `x·s` term is itself below `2^64·p`. -/
theorem barrett_quot_lt (x p m : ℕ) (hp : 0 < p) (hm : m = 2 ^ 64 / p)
    (hx : x < 2 ^ 64) : x < (x * m / 2 ^ 64) * p + 2 * p := by
  set qh := x * m / 2 ^ 64 with hqh
  have hsplit : 2 ^ 64 = m * p + 2 ^ 64 % p := by
    rw [hm]; exact (Nat.div_add_mod' (2 ^ 64) p).symm
  have hs : 2 ^ 64 % p < p := Nat.mod_lt _ hp
  have hxm : x * m < 2 ^ 64 * (qh + 1) := by
    have hdm : 2 ^ 64 * (x * m / 2 ^ 64) + (x * m) % 2 ^ 64 = x * m :=
      Nat.div_add_mod (x * m) (2 ^ 64)
    have hlt : (x * m) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by positivity)
    rw [hqh]
    omega
  have hxs : x * (2 ^ 64 % p) < 2 ^ 64 * p := Nat.mul_lt_mul'' hx hs
  have key : x * 2 ^ 64 < (qh * p + 2 * p) * 2 ^ 64 := by
    calc x * 2 ^ 64 = x * (m * p + 2 ^ 64 % p) := by rw [← hsplit]
      _ = (x * m) * p + x * (2 ^ 64 % p) := by ring
      _ < (2 ^ 64 * (qh + 1)) * p + 2 ^ 64 * p :=
          Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_of_lt hxm)) hxs
      _ = (qh * p + 2 * p) * 2 ^ 64 := by ring
  exact Nat.lt_of_mul_lt_mul_right key

/-- With the two bounds in hand, one conditional subtraction *is* `% p`. -/
theorem barrett_correct (x p qh : ℕ) (hle : qh * p ≤ x)
    (hlt : x < qh * p + 2 * p) :
    (if p ≤ x - qh * p then x - qh * p - p else x - qh * p) = x % p := by
  have hx : x = qh * p + (x - qh * p) := (Nat.add_sub_cancel' hle).symm
  have hmod : x % p = (x - qh * p) % p := by
    conv_lhs => rw [hx]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  have hr2 : x - qh * p < 2 * p := by omega
  by_cases hc : p ≤ x - qh * p
  · rw [if_pos hc, hmod]
    have hsmall : x - qh * p - p < p := by omega
    rw [Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt hsmall]
  · rw [if_neg hc, hmod, Nat.mod_eq_of_lt (by omega)]

/-! ## `ntt::aux_reduce` -/

@[simp, scalar_tac_simps]
theorem BARRETT_SCALE_val : (ntt.BARRETT_SCALE).val = 2 ^ 64 := by
  simp only [ntt.BARRETT_SCALE]; decide

/-- `aux_reduce x p m` is `x % p`, for **every** `u64` `x`.

No upper bound on `x` beyond its type: the undershoot argument only ever needs
`x < 2^64`, which is what `x : U64` already says. That is what lets `twist` feed
it a word below `q` and a butterfly feed it a product of two residues, with one
theorem covering both. -/
@[step]
theorem aux_reduce_spec (x p m : Std.U64) (h : Magic p m) :
    ntt.aux_reduce x p m ⦃ r => r.val = x.val % p.val ⦄ := by
  have hp : 0 < p.val := h.pos
  have hmle : m.val ≤ 2 ^ 63 := by
    rw [h.magic]
    calc 2 ^ 64 / p.val ≤ 2 ^ 64 / 2 := Nat.div_le_div_left h.two_le (by norm_num)
      _ = 2 ^ 63 := by norm_num
  rw [ntt.aux_reduce]
  -- the two widening casts
  have hcx : lift (UScalar.cast .U128 x) ⦃ y => y.val = x.val ⦄ :=
    UScalar.cast_inBounds_spec .U128 x (by scalar_tac)
  step with hcx as ⟨xw, hxw⟩
  have hcm : lift (UScalar.cast .U128 m) ⦃ y => y.val = m.val ⦄ :=
    UScalar.cast_inBounds_spec .U128 m (by scalar_tac)
  step with hcm as ⟨mw, hmw⟩
  -- `x * m ≤ (2^64 - 1) * 2^63 < 2^128`
  have hprod : xw.val * mw.val ≤ Std.U128.max := by
    have hxlt : x.val < 2 ^ 64 := by scalar_tac
    have h1 : xw.val * mw.val ≤ 2 ^ 64 * 2 ^ 63 := by
      rw [hxw, hmw]; exact Nat.mul_le_mul (Nat.le_of_lt hxlt) hmle
    have h2 : (2 : ℕ) ^ 64 * 2 ^ 63 ≤ Std.U128.max := by
      simp only [Std.U128.max, Std.U128.numBits]; norm_num
    omega
  step as ⟨wide, hwide⟩
  step as ⟨i2, hi2⟩
  -- `qh = ⌊x·m / 2^64⌋ < 2^64`, so the narrowing cast is exact
  have hqhv : i2.val = x.val * m.val / 2 ^ 64 := by
    rw [hi2, hwide, hxw, hmw, BARRETT_SCALE_val]
  have hqhlt : i2.val < 2 ^ 64 := by
    rw [hqhv]
    calc x.val * m.val / 2 ^ 64 ≤ x.val * m.val / 2 ^ 64 := Nat.le_refl _
      _ < 2 ^ 64 := by
          have h1 : x.val * m.val ≤ 2 ^ 64 * 2 ^ 63 := by
            have hxlt : x.val < 2 ^ 64 := by scalar_tac
            exact Nat.mul_le_mul (Nat.le_of_lt hxlt) hmle
          calc x.val * m.val / 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 63 / 2 ^ 64 :=
                Nat.div_le_div_right h1
            _ = 2 ^ 63 := by norm_num
            _ < 2 ^ 64 := by norm_num
  have hcq : lift (UScalar.cast .U64 i2) ⦃ y => y.val = i2.val ⦄ :=
    UScalar.cast_inBounds_spec .U64 i2 (by
      simp only [UScalar.max, UScalarTy.numBits]
      omega)
  step with hcq as ⟨qh, hqh⟩
  -- `qh·p ≤ x < 2^64`
  have hqp : qh.val * p.val ≤ x.val := by
    rw [hqh, hqhv]; exact barrett_quot_le _ _ _ h.magic
  have hmul : qh.val * p.val ≤ UScalar.max UScalarTy.U64 := by
    have : x.val ≤ UScalar.max UScalarTy.U64 := by scalar_tac
    omega
  step as ⟨i3, hi3⟩
  have hsub : i3.val ≤ x.val := by rw [hi3]; exact hqp
  step as ⟨r, hr⟩
  have hrv : r.val = x.val - qh.val * p.val := by rw [hr, hi3]
  have hlt : x.val < qh.val * p.val + 2 * p.val := by
    rw [hqh, hqhv]
    exact barrett_quot_lt _ _ _ hp h.magic (by scalar_tac)
  -- the conditional subtraction
  by_cases hc : r >= p
  · rw [if_pos hc]
    have hcv : p.val ≤ r.val := by scalar_tac
    step as ⟨z, hz⟩
    rw [hz, hrv]
    have := barrett_correct x.val p.val qh.val hqp hlt
    rwa [if_pos (by rw [← hrv]; exact hcv)] at this
  · rw [if_neg hc, WP.spec_ok]
    have hcv : ¬ (p.val ≤ r.val) := by scalar_tac
    have := barrett_correct x.val p.val qh.val hqp hlt
    rw [if_neg (by rw [← hrv]; exact hcv)] at this
    rw [← this, hrv]

/-! ## `ntt::aux_add`, `ntt::aux_sub`, `ntt::aux_mul`

All three take residues below `p` and return one. The statements are in the
`% p` form rather than as `< p` plus an equation, because that is what the
transform proofs rewrite with; canonicality comes out as a corollary.
-/

/-- `aux_add a b p` is `(a + b) % p` when both operands are below `p`. -/
@[step]
theorem aux_add_spec (a b p : Std.U64) (hp : p.val < 2 ^ 32)
    (ha : a.val < p.val) (hb : b.val < p.val) :
    ntt.aux_add a b p ⦃ r => r.val = (a.val + b.val) % p.val ⦄ := by
  rw [ntt.aux_add]
  have hbnd : a.val + b.val ≤ UScalar.max UScalarTy.U64 := by
    simp only [UScalar.max, UScalarTy.numBits]; omega
  step as ⟨s, hs⟩
  have hsv : s.val = a.val + b.val := hs
  by_cases hc : s >= p
  · rw [if_pos hc]
    have hcv : p.val ≤ s.val := by scalar_tac
    step as ⟨z, hz⟩
    rw [hz, hsv, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg hc, WP.spec_ok]
    have hcv : s.val < p.val := by scalar_tac
    rw [hsv, Nat.mod_eq_of_lt (by omega)]

/-- `aux_sub a b p` is `(a + p − b) % p` when both operands are below `p`.

Stated with the `a + p − b` numerator rather than as a `ZMod p` subtraction for
the same reason `Field.lean`'s `fp_sub_spec` adds `q` first: that is what the
Rust does to keep the `u64` from going negative. -/
@[step]
theorem aux_sub_spec (a b p : Std.U64) (hp : p.val < 2 ^ 32)
    (ha : a.val < p.val) (hb : b.val < p.val) :
    ntt.aux_sub a b p ⦃ r => r.val = (a.val + p.val - b.val) % p.val ⦄ := by
  rw [ntt.aux_sub]
  by_cases hc : a >= b
  · rw [if_pos hc]
    have hcv : b.val ≤ a.val := by scalar_tac
    step as ⟨z, hz⟩
    rw [hz]
    have : a.val + p.val - b.val = (a.val - b.val) + p.val := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg hc]
    have hcv : a.val < b.val := by scalar_tac
    have hbnd : a.val + p.val ≤ UScalar.max UScalarTy.U64 := by
      simp only [UScalar.max, UScalarTy.numBits]; omega
    step as ⟨i, hi⟩
    have hle : b.val ≤ i.val := by rw [hi]; omega
    step as ⟨z, hz⟩
    rw [hz, hi, Nat.mod_eq_of_lt (by omega)]

/-- `aux_mul a b p m` is `(a · b) % p` when both operands are below `p < 2^32`:
the product is then below `2^64` and [`aux_reduce_spec`] applies to it. -/
@[step]
theorem aux_mul_spec (a b p m : Std.U64) (h : Magic p m)
    (ha : a.val < p.val) (hb : b.val < p.val) :
    ntt.aux_mul a b p m ⦃ r => r.val = (a.val * b.val) % p.val ⦄ := by
  rw [ntt.aux_mul]
  have hbnd : a.val * b.val ≤ UScalar.max UScalarTy.U64 := by
    have hlt : p.val < 2 ^ 32 := h.lt_pow
    have : a.val * b.val ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    simp only [UScalar.max, UScalarTy.numBits]
    omega
  step as ⟨i, hi⟩
  step with aux_reduce_spec i p m h as ⟨r, hr⟩
  rw [hr, hi]

/-! ## Canonicality

Every result above is below `p`, which is the invariant the transform's buffers
carry. `Nat.mod_lt` says it once; these three are the form the loop proofs use.
-/

theorem aux_add_lt (a b p : Std.U64) (hp : p.val < 2 ^ 32)
    (ha : a.val < p.val) (hb : b.val < p.val) :
    ntt.aux_add a b p ⦃ r => r.val = (a.val + b.val) % p.val ∧ r.val < p.val ⦄ := by
  apply spec_mono (aux_add_spec a b p hp ha hb)
  intro r hr
  exact ⟨hr, by rw [hr]; exact Nat.mod_lt _ (by omega)⟩

theorem aux_sub_lt (a b p : Std.U64) (hp : p.val < 2 ^ 32)
    (ha : a.val < p.val) (hb : b.val < p.val) :
    ntt.aux_sub a b p
      ⦃ r => r.val = (a.val + p.val - b.val) % p.val ∧ r.val < p.val ⦄ := by
  apply spec_mono (aux_sub_spec a b p hp ha hb)
  intro r hr
  exact ⟨hr, by rw [hr]; exact Nat.mod_lt _ (by omega)⟩

theorem aux_mul_lt (a b p m : Std.U64) (h : Magic p m)
    (ha : a.val < p.val) (hb : b.val < p.val) :
    ntt.aux_mul a b p m
      ⦃ r => r.val = (a.val * b.val) % p.val ∧ r.val < p.val ⦄ := by
  apply spec_mono (aux_mul_spec a b p m h ha hb)
  intro r hr
  exact ⟨hr, by rw [hr]; exact Nat.mod_lt _ (by omega)⟩

theorem aux_reduce_lt (x p m : Std.U64) (h : Magic p m) :
    ntt.aux_reduce x p m ⦃ r => r.val = x.val % p.val ∧ r.val < p.val ⦄ := by
  apply spec_mono (aux_reduce_spec x p m h)
  intro r hr
  exact ⟨hr, by rw [hr]; exact Nat.mod_lt _ h.pos⟩

end HachiEquiv.AuxArith
