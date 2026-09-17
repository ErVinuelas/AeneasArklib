/-
The **three auxiliary primes** and the exactness of `hachi.ntt`'s CRT
reconstruction.

Two things live here. First, the prime-specific constants: each `(pᵢ, mᵢ)` pair
shown to satisfy `AuxArith.Magic`, each root shown to have exact order `2N`, and
each `NINVᵢ`/`BOFFᵢ` shown to be what it claims. All of it by `decide` or
`norm_num` on numerals -- these are closed arithmetic facts about 30-bit
integers, so there is nothing to prove beyond naming them.

Second, [`garner_spec`]: the reconstruction returns the *exact* natural number
below `P = p1·p2·p3`, given its three residues. That is the theorem the whole
construction rests on, because it is what turns "correct modulo three primes"
into "correct as an integer", and it is why `ntt.rs` can offset by `N·q²` and
have the answer come out right mod `q`.
-/
import AuxArith
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.AuxCRT

open HachiEquiv.AuxArith

/-! ## The constants -/

abbrev p1 : ℕ := 469762049
abbrev p2 : ℕ := 998244353
abbrev p3 : ℕ := 1004535809

/-- `P = p1·p2·p3`, the CRT modulus: `471 064 322 751 194 440 790 966 273`. -/
abbrev P : ℕ := p1 * p2 * p3

@[simp, scalar_tac_simps] theorem AUX_P1_val : (ntt.AUX_P1).val = p1 := by
  simp only [ntt.AUX_P1]; decide
@[simp, scalar_tac_simps] theorem AUX_P2_val : (ntt.AUX_P2).val = p2 := by
  simp only [ntt.AUX_P2]; decide
@[simp, scalar_tac_simps] theorem AUX_P3_val : (ntt.AUX_P3).val = p3 := by
  simp only [ntt.AUX_P3]; decide
@[simp, scalar_tac_simps] theorem AUX_M1_val : (ntt.AUX_M1).val = 39268272336 := by
  simp only [ntt.AUX_M1]; decide
@[simp, scalar_tac_simps] theorem AUX_M2_val : (ntt.AUX_M2).val = 18479187002 := by
  simp only [ntt.AUX_M2]; decide
@[simp, scalar_tac_simps] theorem AUX_M3_val : (ntt.AUX_M3).val = 18363450967 := by
  simp only [ntt.AUX_M3]; decide
@[simp, scalar_tac_simps] theorem GARNER_P12_val : (ntt.GARNER_P12).val = p1 * p2 := by
  simp only [ntt.GARNER_P12]; decide
@[simp, scalar_tac_simps] theorem GARNER_INV1_val : (ntt.GARNER_INV1).val = 554580198 := by
  simp only [ntt.GARNER_INV1]; decide
@[simp, scalar_tac_simps] theorem GARNER_INV12_val : (ntt.GARNER_INV12).val = 395249030 := by
  simp only [ntt.GARNER_INV12]; decide

/-! ### The three `Magic` pairs

`Magic p m` is `2 ≤ p`, `p < 2^32` and `m = ⌊2^64/p⌋`; the last is the only one
with any content, and it is a division of numerals. -/

theorem magic1 : Magic ntt.AUX_P1 ntt.AUX_M1 := by
  refine ⟨?_, ?_, ?_⟩
  · show 2 ≤ (ntt.AUX_P1).val
    rw [AUX_P1_val]; norm_num [p1]
  · show (ntt.AUX_P1).val < 2 ^ 32
    rw [AUX_P1_val]; norm_num [p1]
  · rw [AUX_M1_val, AUX_P1_val]; norm_num [p1]

theorem magic2 : Magic ntt.AUX_P2 ntt.AUX_M2 := by
  refine ⟨?_, ?_, ?_⟩
  · show 2 ≤ (ntt.AUX_P2).val
    rw [AUX_P2_val]; norm_num [p2]
  · show (ntt.AUX_P2).val < 2 ^ 32
    rw [AUX_P2_val]; norm_num [p2]
  · rw [AUX_M2_val, AUX_P2_val]; norm_num [p2]

theorem magic3 : Magic ntt.AUX_P3 ntt.AUX_M3 := by
  refine ⟨?_, ?_, ?_⟩
  · show 2 ≤ (ntt.AUX_P3).val
    rw [AUX_P3_val]; norm_num [p3]
  · show (ntt.AUX_P3).val < 2 ^ 32
    rw [AUX_P3_val]; norm_num [p3]
  · rw [AUX_M3_val, AUX_P3_val]; norm_num [p3]

/-! ### The primes are ordered and the inverses are inverses

The ordering `p1 < p2 < p3` is what lets `garner` skip two reductions: `r1 < p1`
is already reduced mod `p2` and mod `p3`, and `t1 < p2` is already reduced mod
`p3`. -/

theorem p_ordered : p1 < p2 ∧ p2 < p3 := by constructor <;> norm_num

theorem inv1_spec : p1 * 554580198 % p2 = 1 := by norm_num

theorem inv12_spec : (p1 * p2) % p3 * 395249030 % p3 = 1 := by norm_num

/-! ## Exactness of the reconstruction

```text
t1 = (r2 − r1) · p1⁻¹                 mod p2
t2 = (r3 − r1 − p1·t1) · (p1·p2)⁻¹    mod p3
x  = r1 + p1·t1 + (p1·p2)·t2
```

The argument, in one paragraph. Write `x` for the natural number whose residues
are given. From `r1 = x % p1` we get `x = r1 + p1·u`; reducing mod `p2` and
multiplying by `p1⁻¹` identifies `t1 = u % p2`, so `u = t1 + p2·v` and
`x = r1 + p1·t1 + (p1·p2)·v`; reducing *that* mod `p3` and multiplying by
`(p1·p2)⁻¹` identifies `t2 = v % p3`, so `x = r1 + p1·t1 + (p1·p2)·t2 + P·w`.
Finally `r1 + p1·t1 + (p1·p2)·t2 ≤ (p1−1) + p1(p2−1) + p1p2(p3−1) = P − 1 < P`,
so `x < P` forces `w = 0`.

The totality half is the `u128` bookkeeping: `p1·t1 < 2^59` (so it is a valid
`u64` product and a valid `aux_mul` operand pair mod `p3`), and the final sum is
below `P < 2^89`.
-/

/-- Every `u64` widens into a `u128`. Stated once so the five casts in
`garner` need no `scalar_tac` in a context full of 27-digit numerals. -/
theorem u64_le_u128_max (v : Std.U64) : v.val ≤ UScalar.max UScalarTy.U128 := by
  have h := Std.U64.le_max v
  have h2 : UScalar.max UScalarTy.U128 = 340282366920938463463374607431768211455 := by
    simp only [UScalar.max, UScalarTy.numBits]; norm_num
  omega

/-! ### The generic Garner step

`t1` and `t2` are computed by the same three-line pattern: a difference taken
mod `n`, then a multiplication by the stored inverse, again mod `n`. What makes
that pattern *identify a digit* is stated once, for an arbitrary modulus: if the
difference `A` agrees with `c·y` mod `n` once a common summand `e` is cancelled,
and `k` inverts `c` mod `n`, then the pattern returns `y % n`. -/
theorem garner_generic (n c k y A e : ℕ) (hn : 1 < n)
    (hinv : c * k % n = 1)
    (hcancel : (A + e) % n = (c * y + e) % n) :
    A % n * k % n = y % n := by
  have hA : A ≡ c * y [MOD n] := Nat.ModEq.add_right_cancel' e hcancel
  have hck : c * k ≡ 1 [MOD n] := by
    show c * k % n = 1 % n
    rw [hinv, Nat.mod_eq_of_lt hn]
  calc A % n * k % n
      = A * k % n := (Nat.mod_modEq A n).mul_right k
    _ = c * y * k % n := hA.mul_right k
    _ = y * (c * k) % n := by rw [show c * y * k = y * (c * k) from by ring]
    _ = y * 1 % n := hck.mul_left y
    _ = y % n := by rw [Nat.mul_one]

/-- The inverse of `p1·p2` mod `p3`, in the unreduced form `garner_generic`
wants. -/
theorem inv12_spec' : p1 * p2 * 395249030 % p3 = 1 := by norm_num

/-- `P` as a literal, for `omega`. -/
theorem P_val : P = 471064322751194440790966273 := by norm_num [P, p1, p2, p3]

/-- **Garner reconstruction is exact.** Given the three residues of a natural
number below `P`, `ntt.garner` returns that number. -/
theorem garner_spec (r1 r2 r3 : Std.U64) (x : ℕ) (hx : x < P)
    (h1 : r1.val = x % p1) (h2 : r2.val = x % p2) (h3 : r3.val = x % p3) :
    ntt.garner r1 r2 r3 ⦃ z => z.val = x ⦄ := by
  have np1 : (p1 : ℕ) = 469762049 := rfl
  have np2 : (p2 : ℕ) = 998244353 := rfl
  have np3 : (p3 : ℕ) = 1004535809 := rfl
  -- the three residues are canonical
  have hr1lt : r1.val < p1 := by rw [h1]; exact Nat.mod_lt _ (by norm_num)
  have hr2lt : r2.val < p2 := by rw [h2]; exact Nat.mod_lt _ (by norm_num)
  have hr3lt : r3.val < p3 := by rw [h3]; exact Nat.mod_lt _ (by norm_num)
  have hr1p2 : r1.val < p2 := by omega
  have hr1p3 : r1.val < p3 := by omega
  -- `x = r1 + p1·q1`
  obtain ⟨q1, hq1⟩ : ∃ q, x = r1.val + p1 * q :=
    ⟨x / p1, by rw [h1]; exact (Nat.mod_add_div x p1).symm⟩
  rw [ntt.garner]
  -- `d1 = (r2 + p2 − r1) % p2`
  step with aux_sub_lt r2 r1 ntt.AUX_P2 (by rw [AUX_P2_val]; norm_num)
      (by rw [AUX_P2_val]; exact hr2lt) (by rw [AUX_P2_val]; exact hr1p2)
    as ⟨d1, hd1, hd1lt⟩
  rw [AUX_P2_val] at hd1 hd1lt
  -- `t1 = d1 · p1⁻¹ % p2`
  step with aux_mul_lt d1 ntt.GARNER_INV1 ntt.AUX_P2 ntt.AUX_M2 magic2
      (by rw [AUX_P2_val]; exact hd1lt)
      (by rw [AUX_P2_val, GARNER_INV1_val]; norm_num)
    as ⟨t1, ht1, ht1lt⟩
  rw [AUX_P2_val, GARNER_INV1_val] at ht1
  rw [AUX_P2_val] at ht1lt
  -- and `t1` is the second digit of `x`
  have ht1eq : t1.val = q1 % p2 := by
    rw [ht1, hd1]
    refine garner_generic p2 p1 554580198 q1 (r2.val + p2 - r1.val) r1.val
      (by norm_num) inv1_spec ?_
    have hA : r2.val + p2 - r1.val + r1.val = r2.val + p2 := by omega
    have hsum : p1 * q1 + r1.val = x := by omega
    rw [hA, hsum, Nat.add_mod_right, h2]
    exact Nat.mod_mod_of_dvd x (dvd_refl p2)
  obtain ⟨v, hv⟩ : ∃ v, q1 = t1.val + p2 * v :=
    ⟨q1 / p2, by rw [ht1eq]; exact (Nat.mod_add_div q1 p2).symm⟩
  have hx2 : x = r1.val + p1 * t1.val + p1 * p2 * v := by rw [hq1, hv]; ring
  -- `i = p1·t1 % p3`
  step with aux_mul_lt ntt.AUX_P1 t1 ntt.AUX_P3 ntt.AUX_M3 magic3
      (by rw [AUX_P1_val, AUX_P3_val]; norm_num)
      (by rw [AUX_P3_val]; omega)
    as ⟨i, hi, hilt⟩
  rw [AUX_P1_val, AUX_P3_val] at hi
  rw [AUX_P3_val] at hilt
  -- `partial1 = (r1 + i) % p3`
  step with aux_add_lt r1 i ntt.AUX_P3 (by rw [AUX_P3_val]; norm_num)
      (by rw [AUX_P3_val]; exact hr1p3) (by rw [AUX_P3_val]; exact hilt)
    as ⟨pa, hpa, hpalt⟩
  rw [AUX_P3_val] at hpa hpalt
  -- `d2 = (r3 + p3 − partial1) % p3`
  step with aux_sub_lt r3 pa ntt.AUX_P3 (by rw [AUX_P3_val]; norm_num)
      (by rw [AUX_P3_val]; exact hr3lt) (by rw [AUX_P3_val]; exact hpalt)
    as ⟨d2, hd2, hd2lt⟩
  rw [AUX_P3_val] at hd2 hd2lt
  -- `t2 = d2 · (p1p2)⁻¹ % p3`
  step with aux_mul_lt d2 ntt.GARNER_INV12 ntt.AUX_P3 ntt.AUX_M3 magic3
      (by rw [AUX_P3_val]; exact hd2lt)
      (by rw [AUX_P3_val, GARNER_INV12_val]; norm_num)
    as ⟨t2, ht2, ht2lt⟩
  rw [AUX_P3_val, GARNER_INV12_val] at ht2
  rw [AUX_P3_val] at ht2lt
  -- and `t2` is the third digit of `x`
  have ht2eq : t2.val = v % p3 := by
    rw [ht2, hd2]
    refine garner_generic p3 (p1 * p2) 395249030 v (r3.val + p3 - pa.val) pa.val
      (by norm_num) inv12_spec' ?_
    have hA : r3.val + p3 - pa.val + pa.val = r3.val + p3 := by omega
    have hpaeq : pa.val ≡ r1.val + p1 * t1.val [MOD p3] := by
      calc pa.val ≡ r1.val + i.val [MOD p3] := by rw [hpa]; exact Nat.mod_modEq _ _
        _ ≡ r1.val + p1 * t1.val [MOD p3] := by
            rw [hi]; exact (Nat.mod_modEq _ _).add_left r1.val
    have hrhs : (p1 * p2 * v + pa.val) % p3 = x % p3 := by
      calc (p1 * p2 * v + pa.val) % p3
          = (p1 * p2 * v + (r1.val + p1 * t1.val)) % p3 := hpaeq.add_left _
        _ = x % p3 := by
            rw [show p1 * p2 * v + (r1.val + p1 * t1.val) = x from by rw [hx2]; ring]
    rw [hA, hrhs, Nat.add_mod_right, h3]
    exact Nat.mod_mod_of_dvd x (dvd_refl p3)
  obtain ⟨w, hw⟩ : ∃ w, v = t2.val + p3 * w :=
    ⟨v / p3, by rw [ht2eq]; exact (Nat.mod_add_div v p3).symm⟩
  have hx3 : x = r1.val + p1 * t1.val + p1 * p2 * t2.val + p1 * p2 * p3 * w := by
    rw [hx2, hw]; ring
  -- the three digits fit under `P`, so the leftover `w` vanishes
  have e1 : p1 * t1.val ≤ 468937312198197248 := by
    have hle := Nat.mul_le_mul (Nat.le_refl p1) (show t1.val ≤ 998244352 by omega)
    have hn1 : p1 * 998244352 = 468937312198197248 := by norm_num [p1]
    omega
  have e2 : p1 * p2 * t2.val ≤ 471064322282257128123006976 := by
    have hle := Nat.mul_le_mul (Nat.le_refl (p1 * p2))
      (show t2.val ≤ 1004535808 by omega)
    have hn2 : p1 * p2 * 1004535808 = 471064322282257128123006976 := by
      norm_num [p1, p2]
    omega
  have n3 : p1 * p2 * p3 = 471064322751194440790966273 := by norm_num [p1, p2, p3]
  rw [n3] at hx3
  rw [P_val] at hx
  have hxfin : x = r1.val + p1 * t1.val + p1 * p2 * t2.val := by omega
  -- the `u128` reconstruction
  have hc1 : lift (UScalar.cast .U128 r1) ⦃ y => y.val = r1.val ⦄ :=
    UScalar.cast_inBounds_spec .U128 r1 (u64_le_u128_max r1)
  step with hc1 as ⟨i1, hi1⟩
  have hc2 : lift (UScalar.cast .U128 ntt.AUX_P1) ⦃ y => y.val = (ntt.AUX_P1).val ⦄ :=
    UScalar.cast_inBounds_spec .U128 ntt.AUX_P1 (u64_le_u128_max _)
  step with hc2 as ⟨i2, hi2⟩
  rw [AUX_P1_val] at hi2
  have hc3 : lift (UScalar.cast .U128 t1) ⦃ y => y.val = t1.val ⦄ :=
    UScalar.cast_inBounds_spec .U128 t1 (u64_le_u128_max t1)
  step with hc3 as ⟨i3, hi3⟩
  have hmax : (471064322751194440790966273 : ℕ) ≤ Std.U128.max := by
    simp only [Std.U128.max, Std.U128.numBits]; norm_num
  have hprod1 : i2.val * i3.val ≤ Std.U128.max := by rw [hi2, hi3]; omega
  step as ⟨i4, hi4⟩
  have hsum1 : i1.val + i4.val ≤ Std.U128.max := by
    rw [hi1, hi4, hi2, hi3]; omega
  step as ⟨i5, hi5⟩
  have hc6 : lift (UScalar.cast .U128 ntt.GARNER_P12)
      ⦃ y => y.val = (ntt.GARNER_P12).val ⦄ :=
    UScalar.cast_inBounds_spec .U128 ntt.GARNER_P12 (u64_le_u128_max _)
  step with hc6 as ⟨i6, hi6⟩
  rw [GARNER_P12_val] at hi6
  have hc7 : lift (UScalar.cast .U128 t2) ⦃ y => y.val = t2.val ⦄ :=
    UScalar.cast_inBounds_spec .U128 t2 (u64_le_u128_max t2)
  step with hc7 as ⟨i7, hi7⟩
  have hprod2 : i6.val * i7.val ≤ Std.U128.max := by rw [hi6, hi7]; omega
  step as ⟨i8, hi8⟩
  have hsum2 : i5.val + i8.val ≤ Std.U128.max := by
    rw [hi5, hi1, hi4, hi2, hi3, hi8, hi6, hi7]; omega
  step as ⟨z, hz⟩
  rw [hz, hi5, hi8, hi1, hi4, hi2, hi3, hi6, hi7, hxfin]

/-- The bound the transform's offset has to respect, and the fact that makes the
reconstruction exact for it: the offset convolution coefficient
`W = posSum + N·q² − negSum` lies in `[0, 2·N·q²]`, and `2·N·q² < P`. -/
theorem two_bound_lt_P : 2 * (1024 * (4294967197 * 4294967197)) < P := by norm_num

/-- And the offset vanishes mod `q`, which is why the caller needs no correction
term. -/
theorem bound_mod_q : 1024 * (4294967197 * 4294967197) % 4294967197 = 0 := by norm_num

/-! ## Two primes, for a digit-bounded operand

A generic ring product needs all three primes: its exact convolution coefficient
can reach `N·q²`, and even one term of that does not fit `p1·p2`. A product in
which one operand's coefficients are gadget *digits* has an exact coefficient
below `N·q·16`, which is `2^46` rather than `2^73` -- so thousands of terms fit
two primes, and the third transform is pure waste.

This section is the arithmetic of that: the radix, the fit, and the two-residue
reconstruction. The transforms themselves are untouched; `dot_prep_chunk_mod_p`
is already generic in the prime and the offset. -/

/-- `p1 · p2`, the two-prime radix. A `u64`, unlike `P`. -/
abbrev P12 : ℕ := p1 * p2

/-- `P12` as a literal, for `omega`. -/
theorem P12_val : P12 = 468937312667959297 := by norm_num [P12, p1, p2]

/-- **Two-prime Garner reconstruction is exact.** Given the two residues of a
natural number below `p1 · p2`, `ntt.garner2` returns that number.

This is `garner_spec`'s first stage and nothing more, and it is sound only under
the much tighter `hx`: two primes identify a 59-bit range, not an 89-bit one.
There is no third digit to compute precisely *because* `x < p1·p2` forces the
quotient `q1` below `p2`, which is the step below that has no analogue in
`garner_spec`. -/
theorem garner2_spec (r1 r2 : Std.U64) (x : ℕ) (hx : x < P12)
    (h1 : r1.val = x % p1) (h2 : r2.val = x % p2) :
    ntt.garner2 r1 r2 ⦃ z => z.val = x ⦄ := by
  have np1 : (p1 : ℕ) = 469762049 := rfl
  have np2 : (p2 : ℕ) = 998244353 := rfl
  have hr1lt : r1.val < p1 := by rw [h1]; exact Nat.mod_lt _ (by norm_num)
  have hr2lt : r2.val < p2 := by rw [h2]; exact Nat.mod_lt _ (by norm_num)
  have hr1p2 : r1.val < p2 := by omega
  obtain ⟨q1, hq1⟩ : ∃ q, x = r1.val + p1 * q :=
    ⟨x / p1, by rw [h1]; exact (Nat.mod_add_div x p1).symm⟩
  -- the two-prime fit, used twice: it is what leaves no third digit
  have hq1lt : q1 < p2 := by
    by_contra hge
    have hmul : p1 * p2 ≤ p1 * q1 := Nat.mul_le_mul_left p1 (by omega)
    simp only [P12] at hx
    omega
  rw [ntt.garner2]
  step with aux_sub_lt r2 r1 ntt.AUX_P2 (by rw [AUX_P2_val]; norm_num)
      (by rw [AUX_P2_val]; exact hr2lt) (by rw [AUX_P2_val]; exact hr1p2)
    as ⟨d1, hd1, hd1lt⟩
  rw [AUX_P2_val] at hd1 hd1lt
  step with aux_mul_lt d1 ntt.GARNER_INV1 ntt.AUX_P2 ntt.AUX_M2 magic2
      (by rw [AUX_P2_val]; exact hd1lt)
      (by rw [AUX_P2_val, GARNER_INV1_val]; norm_num)
    as ⟨t1, ht1, ht1lt⟩
  rw [AUX_P2_val, GARNER_INV1_val] at ht1
  rw [AUX_P2_val] at ht1lt
  have ht1eq : t1.val = q1 := by
    rw [ht1, hd1]
    rw [show q1 = q1 % p2 from (Nat.mod_eq_of_lt hq1lt).symm]
    refine garner_generic p2 p1 554580198 q1 (r2.val + p2 - r1.val) r1.val
      (by norm_num) inv1_spec ?_
    have hA : r2.val + p2 - r1.val + r1.val = r2.val + p2 := by omega
    have hsum : p1 * q1 + r1.val = x := by omega
    rw [hA, hsum, Nat.add_mod_right, h2]
    exact Nat.mod_mod_of_dvd x (dvd_refl p2)
  -- `r1 + p1·t1` is `x`, and it fits a `u64` because it is below `p1·p2 < 2^59`
  step as ⟨i, hi⟩
  step as ⟨z, hz⟩
  rw [hz, hi, AUX_P1_val, ht1eq, hq1]

end HachiEquiv.AuxCRT

