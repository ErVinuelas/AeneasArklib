/-
The **Goldilocks lane**: modular arithmetic at `p = 2^64 − 2^32 + 1`
(candidate T27).

This is the bottom of a *second* transform layer, and it plays the role
`NttArith.lean` plays for the three 30-bit auxiliary primes. It exists because
of one number: a digit-path dot has one operand below `GADGET_BASE`, so its
whole `8192`-term product is bounded by `1.081·10^18` against this prime's
`1.845·10^19`. One lane covers what two 30-bit primes need two lanes and four
chunks for — and with one lane there is no CRT step at all.

## Why this is not `NttArith` with a different constant

`NttArith`'s theorems are stated for an arbitrary `(p, m)` satisfying `Magic`,
and `Magic` **requires `p < 2^32`** — its own docstring says that is what keeps
a product of two residues inside a `u64`. Goldilocks products need a `u128`, so
the existing layer cannot be instantiated here and the arithmetic starts again.

What it does not need is Barrett. `2^64 ≡ 2^32 − 1 (mod p)` is *exact*, so
[`gold_reduce_spec`] has no floor, no magic constant and no error term to
bound — the reduction is two shifts, a mask, one multiply and two modular
operations, and its proof is correspondingly shorter than `aux_reduce_spec`'s.

## The one tight bound

`gold_reduce` finishes with a *single* conditional subtract, which is only
enough if its sum stays below `2p`. It does, with a margin of **two**:
`t ≤ 2^64 − 1` and `m ≤ (2^32 − 1)^2`, so `t + m ≤ 2^65 − 2^33 = 2p − 2`.
That is why [`gold_reduce_spec`] needs no precondition at all — it is exact for
every `u128` — and why [`gold_add_bounded`] is stated with `< 2 * GP` rather
than at two reduced operands: the reduction's own call sites do not have
reduced operands, and demanding them would be a lie about the code.
-/
import Generated
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.GoldArith

/-- The Goldilocks prime, as a natural number. -/
abbrev GP : ℕ := 18446744069414584321

theorem GP_eq : GP = 2 ^ 64 - 2 ^ 32 + 1 := by norm_num

theorem GOLD_P_val : (ntt.GOLD_P).val = GP := by
  simp only [ntt.GOLD_P]; decide +kernel

theorem GP_lt : GP < 2 ^ 64 := by norm_num

/-- The bound that makes one conditional subtract enough, with its margin of
two spelled out. -/
theorem two_GP_bound : (2 ^ 64 - 1) + (2 ^ 32 - 1) * (2 ^ 32 - 1) + 2 = 2 * GP := by
  norm_num

/-! ## Addition and subtraction -/

/-- `gold_add` is correct whenever the *sum* is below `2 · p` — which is what
its callers can offer, since `gold_reduce` feeds it operands that are not
themselves reduced. -/
theorem gold_add_bounded (a b : Std.U64) (h : a.val + b.val < 2 * GP) :
    ntt.gold_add a b ⦃ r => r.val = (a.val + b.val) % GP ⦄ := by
  have hGP : GP = 18446744069414584321 := rfl
  have ha64 : a.val < 2 ^ 64 := by scalar_tac
  have hb64 : b.val < 2 ^ 64 := by scalar_tac
  rw [ntt.gold_add]
  have hca : lift (UScalar.cast .U128 a) ⦃ y => y.val = a.val ⦄ :=
    UScalar.cast_inBounds_spec .U128 a (by scalar_tac)
  step with hca as ⟨aw, haw⟩
  have hcb : lift (UScalar.cast .U128 b) ⦃ y => y.val = b.val ⦄ :=
    UScalar.cast_inBounds_spec .U128 b (by scalar_tac)
  step with hcb as ⟨bw, hbw⟩
  have hsum : aw.val + bw.val ≤ Std.U128.max := by
    rw [haw, hbw]
    have : (2 : ℕ) ^ 64 + 2 ^ 64 ≤ Std.U128.max := by
      simp only [Std.U128.max, Std.U128.numBits]; norm_num
    omega
  step as ⟨s, hs⟩
  have hcp : lift (UScalar.cast .U128 ntt.GOLD_P) ⦃ y => y.val = GP ⦄ :=
    spec_mono (UScalar.cast_inBounds_spec .U128 ntt.GOLD_P (by scalar_tac))
      (fun y hy => by rw [hy, GOLD_P_val])
  step with hcp as ⟨p, hp⟩
  have hsv : s.val = a.val + b.val := by rw [hs, haw, hbw]
  by_cases hge : s ≥ p
  · rw [if_pos hge]
    have hgev : GP ≤ s.val := by rw [← hp]; scalar_tac
    rw [hsv] at hgev
    step as ⟨d, hd⟩
    have hdv : d.val = a.val + b.val - GP := by rw [hd, hsv, hp]
    simp only [UScalar.cast_val_eq, UScalarTy.numBits, hdv]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_sub_mod hgev,
      Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg hge]
    have hltv : s.val < GP := by rw [← hp]; scalar_tac
    rw [hsv] at hltv
    rw [WP.spec_ok]
    simp only [UScalar.cast_val_eq, UScalarTy.numBits, hsv]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- `gold_add` at two reduced operands, the form every caller above the
reduction uses. -/
@[step]
theorem gold_add_spec (a b : Std.U64) (ha : a.val < GP) (hb : b.val < GP) :
    ntt.gold_add a b ⦃ r => r.val = (a.val + b.val) % GP ∧ r.val < GP ⦄ := by
  apply spec_mono (gold_add_bounded a b (by omega))
  intro r hr
  exact ⟨hr, by rw [hr]; exact Nat.mod_lt _ (by norm_num)⟩

/-- `gold_sub`, at a reduced subtrahend. The minuend need not be reduced: the
reduction subtracts a value below `2^32` from an arbitrary `u64` word. -/
theorem gold_sub_bounded (a b : Std.U64) (hb : b.val < GP) :
    ntt.gold_sub a b ⦃ r => (b.val ≤ a.val ∧ r.val = a.val - b.val)
                          ∨ (a.val < b.val ∧ r.val = a.val + GP - b.val) ⦄ := by
  have hGP : GP = 18446744069414584321 := rfl
  have ha64 : a.val < 2 ^ 64 := by scalar_tac
  have hb64 : b.val < 2 ^ 64 := by scalar_tac
  rw [ntt.gold_sub]
  by_cases hge : a ≥ b
  · rw [if_pos hge]
    have hgev : b.val ≤ a.val := by scalar_tac
    step as ⟨d, hd⟩
    exact Or.inl ⟨hgev, by rw [hd]⟩
  · rw [if_neg hge]
    have hltv : a.val < b.val := by scalar_tac
    have hca : lift (UScalar.cast .U128 a) ⦃ y => y.val = a.val ⦄ :=
      UScalar.cast_inBounds_spec .U128 a (by scalar_tac)
    step with hca as ⟨aw, haw⟩
    have hcp : lift (UScalar.cast .U128 ntt.GOLD_P) ⦃ y => y.val = GP ⦄ :=
      spec_mono (UScalar.cast_inBounds_spec .U128 ntt.GOLD_P (by scalar_tac))
        (fun y hy => by rw [hy, GOLD_P_val])
    step with hcp as ⟨p, hp⟩
    have hs1 : aw.val + p.val ≤ Std.U128.max := by
      rw [haw, hp]
      have : (2 : ℕ) ^ 64 + 18446744069414584321 ≤ Std.U128.max := by
        simp only [Std.U128.max, Std.U128.numBits]; norm_num
      omega
    step as ⟨s, hs⟩
    have hcb : lift (UScalar.cast .U128 b) ⦃ y => y.val = b.val ⦄ :=
      UScalar.cast_inBounds_spec .U128 b (by scalar_tac)
    step with hcb as ⟨bw, hbw⟩
    have hsv : s.val = a.val + GP := by rw [hs, haw, hp]
    have hle : bw.val ≤ s.val := by rw [hbw, hsv]; omega
    step as ⟨d, hd⟩
    have hdv : d.val = a.val + GP - b.val := by rw [hd, hsv, hbw]
    simp only [UScalar.cast_val_eq, UScalarTy.numBits, hdv]
    exact Or.inr ⟨hltv, Nat.mod_eq_of_lt (by omega)⟩

/-- `gold_sub` at two reduced operands. -/
@[step]
theorem gold_sub_spec (a b : Std.U64) (ha : a.val < GP) (hb : b.val < GP) :
    ntt.gold_sub a b ⦃ r => r.val = (a.val + GP - b.val) % GP ∧ r.val < GP ⦄ := by
  have hGP : GP = 18446744069414584321 := rfl
  apply spec_mono (gold_sub_bounded a b hb)
  rintro r (⟨hge, hr⟩ | ⟨hlt, hr⟩)
  · refine ⟨?_, by omega⟩
    rw [hr]
    have hre : a.val + GP - b.val = (a.val - b.val) + GP := by omega
    rw [hre, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · refine ⟨?_, by omega⟩
    rw [hr, Nat.mod_eq_of_lt (by omega)]

/-! ## The reduction

`2^64 ≡ 2^32 − 1 (mod p)` is exact, so with `x = hi·2^64 + lo` and
`hi = a·2^32 + b` the value folds to `lo − a + b·(2^32 − 1)`. Two ℕ identities
carry the whole proof, one per branch of the subtraction, and both are exact —
there is no error term because there is no Barrett:

```text
a ≤ lo :  x      = (t + m) + a·(2^96 + 1) + b·p
lo < a :  x + p  = (t + m) + a·(2^96 + 1) + b·p
```

and `2^96 + 1 = p · (2^32 + 1)`, so both correction terms are multiples of `p`.
-/

/-- A narrowing cast is truncation, and `lift` is `ok`: the cast is total and
its value is the residue. -/
theorem cast_trunc_spec {src : UScalarTy} (tgt : UScalarTy) (x : UScalar src) :
    lift (UScalar.cast tgt x) ⦃ y => y.val = x.val % 2 ^ tgt.numBits ⦄ := by
  rw [Std.lift, WP.spec_ok]
  exact UScalar.cast_val_eq tgt x

/-- `2^96 + 1` is `p · (2^32 + 1)`: the fact that makes the fold exact. -/
theorem pow96_succ : 2 ^ 96 + 1 = GP * 4294967297 := by norm_num

-- The 2^96 and 2^128 literals want more than the default recursion depth.
set_option maxRecDepth 8192 in
/-- **`gold_reduce` is `% p`, for every `u128`, with no precondition.**

The absence of a precondition is the tight part: `gold_reduce` ends in a single
conditional subtract, and that is enough only because `t ≤ 2^64 − 1` and
`m ≤ (2^32 − 1)^2` give `t + m ≤ 2p − 2`. The margin is two. -/
@[step]
theorem gold_reduce_spec (x : Std.U128) :
    ntt.gold_reduce x ⦃ r => r.val = x.val % GP ∧ r.val < GP ⦄ := by
  have hGP : GP = 18446744069414584321 := rfl
  have hx : x.val < 2 ^ 128 := by scalar_tac
  rw [ntt.gold_reduce]
  -- lo = x mod 2^64
  step with cast_trunc_spec .U64 x as ⟨lo, hlo⟩
  simp only [UScalarTy.numBits] at hlo
  -- hi = x / 2^64
  step as ⟨sh, hsh⟩
  step with cast_trunc_spec .U64 sh as ⟨hi, hhi⟩
  simp only [UScalarTy.numBits] at hhi
  rw [hsh, Nat.shiftRight_eq_div_pow] at hhi
  have hdlt : x.val / 2 ^ 64 < 2 ^ 64 := by
    apply Nat.div_lt_of_lt_mul
    rw [show (2 : ℕ) ^ 64 * 2 ^ 64 = 2 ^ 128 by ring]
    exact hx
  rw [Nat.mod_eq_of_lt hdlt] at hhi
  -- a = hi / 2^32, b = hi mod 2^32
  step as ⟨a, ha⟩
  step as ⟨b, hb⟩
  rw [Nat.shiftRight_eq_div_pow] at ha
  have hmask : ((4294967295#u64 : Std.U64)).val = 2 ^ 32 - 1 := by decide +kernel
  rw [UScalar.val_and, hmask, Nat.and_two_pow_sub_one_eq_mod] at hb
  have hhi64 : hi.val < 2 ^ 64 := by rw [hhi]; exact hdlt
  have ha32 : a.val < 4294967296 := by
    rw [ha]
    rw [show (2 : ℕ) ^ 32 = 4294967296 by norm_num]
    apply Nat.div_lt_of_lt_mul
    rw [show (2 : ℕ) ^ 64 = 4294967296 * 4294967296 by norm_num] at hhi64
    omega
  have hb32 : b.val < 4294967296 := by
    rw [hb]; exact Nat.mod_lt _ (by norm_num)
  -- m = b · (2^32 − 1), exact because b < 2^32 puts the product below 2^64
  step as ⟨m, hm⟩
  have hmv : m.val = b.val * 4294967295 := by
    rw [hm, core.num.U64.wrapping_mul, UScalar.wrapping_mul_val_eq, hmask]
    simp only [UScalar.size, UScalarTy.numBits]
    rw [show (2 : ℕ) ^ 32 - 1 = 4294967295 by norm_num,
      show (2 : ℕ) ^ 64 = 18446744073709551616 by norm_num,
      Nat.mod_eq_of_lt (by omega)]
  -- the two decompositions, in numerals so the arithmetic stays linear
  have hsplit : hi.val = a.val * 4294967296 + b.val := by
    have h2 := Nat.div_add_mod hi.val (2 ^ 32)
    rw [← ha, ← hb, show (2 : ℕ) ^ 32 = 4294967296 by norm_num] at h2
    omega
  have hxd : x.val = a.val * 79228162514264337593543950336
                   + b.val * 18446744073709551616 + lo.val := by
    have h1 := Nat.div_add_mod x.val (2 ^ 64)
    rw [← hhi, ← hlo, show (2 : ℕ) ^ 64 = 18446744073709551616 by norm_num] at h1
    have hprod : hi.val * 18446744073709551616
        = a.val * 79228162514264337593543950336 + b.val * 18446744073709551616 := by
      rw [hsplit]; ring
    omega
  have hlo64 : lo.val < 18446744073709551616 := by
    rw [hlo, show (2 : ℕ) ^ 64 = 18446744073709551616 by norm_num]
    exact Nat.mod_lt _ (by norm_num)
  -- t = lo − a, in one of the two shapes
  have haGP : a.val < GP := by omega
  step with gold_sub_bounded lo a haGP as ⟨t, ht⟩
  have hmle : m.val ≤ 18446744065119617025 := by rw [hmv]; omega
  have hsum : t.val + m.val < 2 * GP := by
    rcases ht with ⟨_, hte⟩ | ⟨_, hte⟩ <;> rw [hte] <;> omega
  apply spec_mono (gold_add_bounded t m hsum)
  intro r hr
  refine ⟨?_, by rw [hr]; exact Nat.mod_lt _ (by norm_num)⟩
  rw [hr]
  -- `2^96 + 1 = p·(2^32 + 1)`, so both correction terms are multiples of p
  rcases ht with ⟨hle, hte⟩ | ⟨hlt, hte⟩
  · have hid : x.val = (t.val + m.val) + GP * (a.val * 4294967297 + b.val) := by
      rw [hte, hmv, hxd, hGP]; ring_nf; omega
    rw [hid, Nat.add_mul_mod_self_left]
  · have hid : x.val + GP = (t.val + m.val) + GP * (a.val * 4294967297 + b.val) := by
      rw [hte, hmv, hxd, hGP]; ring_nf; omega
    have heq : (t.val + m.val) % GP = (x.val + GP) % GP := by
      rw [hid, Nat.add_mul_mod_self_left]
    rw [heq, Nat.add_mod_right]

/-- **`gold_mul` is `· * · mod p`, for any two words.** The product of two
residues needs a `u128` — which is exactly what `Magic`'s `p < 2^32` exists to
avoid, and therefore exactly why this lane cannot reuse `NttArith`.
No precondition: it inherits that from [`gold_reduce_spec`], so a caller
holding unreduced words gets the right answer too. -/
@[step]
theorem gold_mul_spec (a b : Std.U64) :
    ntt.gold_mul a b ⦃ r => r.val = (a.val * b.val) % GP ∧ r.val < GP ⦄ := by
  rw [ntt.gold_mul]
  have hca : lift (UScalar.cast .U128 a) ⦃ y => y.val = a.val ⦄ :=
    UScalar.cast_inBounds_spec .U128 a (by scalar_tac)
  step with hca as ⟨aw, haw⟩
  have hcb : lift (UScalar.cast .U128 b) ⦃ y => y.val = b.val ⦄ :=
    UScalar.cast_inBounds_spec .U128 b (by scalar_tac)
  step with hcb as ⟨bw, hbw⟩
  have ha64 : a.val < 2 ^ 64 := by scalar_tac
  have hb64 : b.val < 2 ^ 64 := by scalar_tac
  have hprod : aw.val * bw.val ≤ Std.U128.max := by
    rw [haw, hbw]
    have h1 : a.val * b.val ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : ((2 : ℕ) ^ 64 - 1) * (2 ^ 64 - 1) ≤ Std.U128.max := by
      simp only [Std.U128.max, Std.U128.numBits]; norm_num
    omega
  step as ⟨w, hw⟩
  have hwv : w.val = a.val * b.val := by rw [hw, haw, hbw]
  apply spec_mono (gold_reduce_spec w)
  intro r hr
  exact ⟨by rw [hr.1, hwv], hr.2⟩


end HachiEquiv.GoldArith
