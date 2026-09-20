/-
The Taylor-shift round polynomial (Stage 6 candidate T3)

`round_poly_zero` used to evaluate the range summand at `2b + 1 = 33` nodes and
Lagrange-interpolate the result back into coefficients. It now writes the
coefficients down directly, because the multilinear fold is **affine** in the
node:

```text
  W(T, y) = (1 − T)·lo_y + T·hi_y = lo_y + Δ_y·T,     Δ_y = hi_y − lo_y
```

so `P_b(W(T, y))` is `P_b` Taylor-shifted, and the binomial theorem gives its
coefficients in one pass:

```text
  P_b(lo + Δ T) = Σ_m Δ^m T^m · Σ_{k ≥ m} p_k · C(k, m) · lo^{k−m}
```

Two things make the inner sum cheap. `P_b` is **odd**, so only `b` of the `2b`
coefficients `p_k` are nonzero and the inner sum runs over `k = 2j + 1`; and
`p_k · C(k, m)` is a *constant*, so every product in it is `Fp × Ext4` — four
base multiplications, against nineteen for a quartic one. That table is
`params::SHIFT_T`.

This file is the algebra and the four loop specs. The headline,
`round_poly_zero_spec`, stays in `lean/Sumcheck.lean` where it always was, and
its **statement does not move**: 33 coefficients, reduced, and the interpolant
evaluates to `rangeSumZero` everywhere. Only the proof changes, from a Lagrange
uniqueness argument to this one.

## What the table is

`SHIFT_T[j · SHIFT_DEG + m] = p_{2j+1} · C(2j+1, m) mod q`, with
`p_{2j+1} = RANGE_Q_COEFFS[j]`, and `0` where `m > 2j + 1`. `st_val` below is
that claim, checked by `decide +kernel` over all 512 entries at once — a
computation in `ℕ`, so a wrong entry fails its own decision and cannot be
absorbed by the algebra. `params_semantics.rs`'s
`shift_t_is_the_binomial_table` is the same claim on the Rust side.
-/
import ZeroCheck
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum

set_option linter.style.longLine false
set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly CompPoly.CPolynomial CompPoly.Extension ArkLib.Lattices
open ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.AuxShift

open HachiEquiv.Field HachiEquiv.Ext HachiEquiv.Ring HachiEquiv.ZeroCheck

/-! ## 1. The table -/

/-- `SHIFT_T`'s length. -/
@[simp] theorem shift_t_length : params.SHIFT_T.val.length = 512 := by decide +kernel

@[simp] theorem shift_deg_val : (params.SHIFT_DEG).val = 32 := by
  simp only [params.SHIFT_DEG]; decide

@[simp] theorem shift_rows_val : (params.SHIFT_ROWS).val = 16 := by
  simp only [params.SHIFT_ROWS]; decide

/-- **The 512 entries, in one decision.** Every entry of `SHIFT_T` is
`RANGE_Q_COEFFS[j] · C(2j+1, m)` reduced, or zero past the degree. -/
theorem st_nat (j : ℕ) (hj : j < 16) (m : ℕ) (hm : m < 32) :
    (params.SHIFT_T.val.getD (j * 32 + m) 0#u64).val
      = if m ≤ 2 * j + 1
        then (params.RANGE_Q_COEFFS.val.getD j 0#u64).val * Nat.choose (2 * j + 1) m % q
        else 0 := by
  revert hj hm
  revert m
  revert j
  have h : ∀ j < 16, ∀ m < 32,
      (params.SHIFT_T.val.getD (j * 32 + m) 0#u64).val
        = if m ≤ 2 * j + 1
          then (params.RANGE_Q_COEFFS.val.getD j 0#u64).val * Nat.choose (2 * j + 1) m % q
          else 0 := by decide +kernel
  intro j m hj hm
  exact h j hj m hm

/-- Entry `(j, m)` of the table as an element of `F`: the whole interface
between the Rust table and the algebra below, exactly as [`rc`] is for
`RANGE_Q_COEFFS`. -/
def st (j m : ℕ) : F := ((params.SHIFT_T.val.getD (j * 32 + m) 0#u64).val : ℕ)

/-- The bridge from what `Array.index_usize_spec` hands back to the `getD` that
[`st`] is written with. -/
theorem st_of_index (i : ℕ) (h : i < params.SHIFT_T.val.length) (j m : ℕ)
    (hi : i = j * 32 + m) :
    ((params.SHIFT_T.val[i].val : ℕ) : F) = st j m := by
  subst hi
  rw [st, List.getD_eq_getElem (l := params.SHIFT_T.val) (d := 0#u64) h]

/-- **The algebraic reading of the table.** In `F`, entry `(j, m)` is
`p_{2j+1} · C(2j+1, m)` — the reduction mod `q` vanishes because `F` has
characteristic `q` through `φF`. -/
theorem st_eq (j : ℕ) (hj : j < 16) (m : ℕ) (hm : m ≤ 2 * j + 1) (hm32 : m < 32) :
    st j m = rc j * ((Nat.choose (2 * j + 1) m : ℕ) : F) := by
  rw [st, st_nat j hj m hm32, if_pos hm, rc]
  push_cast
  rw [← map_natCast phiF, ← map_natCast phiF, ← map_natCast phiF, ← map_mul]
  congr 1
  push_cast
  rw [ZMod.natCast_mod]
  push_cast
  ring

/-- Past the degree the entry is zero, which is what lets the `m` loop start at
`j = m / 2` without ever reading one. -/
theorem st_zero (j : ℕ) (hj : j < 16) (m : ℕ) (hm : 2 * j + 1 < m) (hm32 : m < 32) :
    st j m = 0 := by
  rw [st, st_nat j hj m hm32, if_neg (by omega)]
  simp

-- Sealed once its two readings are proved: every use below goes through
-- `st_eq` or `st_zero`, and `whnf` must never walk the 512 literals.
attribute [irreducible] st

/-! ## 2. The algebra: `P_b` in coefficient form, and its Taylor shift -/

/-- `P_b` in **coefficient** form: `rangeProduct 16 v = Σ_{j<16} p_{2j+1} · v^{2j+1}`.

[`rangeQ_sq_eq_rangeProduct`] says `rangeProduct 16 v = v · Q(v²)` and `rangeQ`
is `Q` in coefficient form; distributing the leading `v` over the sum and
folding `(v²)^j · v = v^{2j+1}` is the whole content. It is also the precise
sense in which `P_b` is odd: the sum has no even power in it. -/
theorem rangeProduct_eq_sum (v : F) :
    ArkLib.Lattices.Ajtai.InnerOuter.rangeProduct 16 v = ∑ j ∈ Finset.range 16, rc j * v ^ (2 * j + 1) := by
  rw [← rangeQ_sq_eq_rangeProduct, rangeQ, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show v * v = v ^ 2 by ring, ← pow_mul, show 2 * j + 1 = 2 * j + 1 from rfl, pow_succ]
  ring

/-- Coefficient `m` of the Taylor shift, in the shape the code computes it:
`Δ^m · Σ_{j ≥ m/2} T[j][m] · lo^{2j+1−m}`.

The lower limit is `m / 2` and not `⌈(m−1)/2⌉` because those are the same
number: for even `m` the first odd `k ≥ m` is `m + 1 = 2·(m/2) + 1`, and for odd
`m` it is `m = 2·(m/2) + 1`. That is the one index fact the Rust and the proof
share, and it is why `k − m` never underflows. -/
def shiftCoeff (lo d : F) (m : ℕ) : F :=
  d ^ m * ∑ j ∈ Finset.Ico (m / 2) 16, st j m * lo ^ (2 * j + 1 - m)

set_option maxHeartbeats 1000000 in
/-- The terms the lower limit drops are zero: below `m / 2` the exponent
`2j+1−m` would underflow, and the table entry is zero there because `m` exceeds
the row's degree. So the sum may be taken over all of `range 16`. -/
theorem shiftCoeff_range (lo d : F) (m : ℕ) (hm : m < 32) :
    shiftCoeff lo d m
      = d ^ m * ∑ j ∈ Finset.range 16,
          rc j * ((Nat.choose (2 * j + 1) m : ℕ) : F) * lo ^ (2 * j + 1 - m) := by
  rw [shiftCoeff]
  refine congrArg (fun t => d ^ m * t) ?_
  have hfun : ∀ j ∈ Finset.Ico (m / 2) 16,
      st j m * lo ^ (2 * j + 1 - m)
        = rc j * ((Nat.choose (2 * j + 1) m : ℕ) : F) * lo ^ (2 * j + 1 - m) := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    rw [st_eq j hj.2 m (by omega) hm]
  rw [Finset.sum_congr rfl hfun]
  refine Finset.sum_subset (fun j hj => ?_) (fun j hjt hj => ?_)
  · simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢
    exact hj.2
  · simp only [Finset.mem_range] at hjt
    simp only [Finset.mem_Ico, not_and, not_lt] at hj
    have hj2 : 2 * j + 1 < m := by
      have := hj
      omega
    rw [Nat.choose_eq_zero_of_lt hj2]
    simp

set_option maxHeartbeats 2000000 in
/-- **The Taylor shift.** `P_b` at an affine argument, in coefficient form.

`rangeProduct 16 (lo + d·T) = Σ_{m<32} shiftCoeff lo d m · T^m`. The proof is
[`rangeProduct_eq_sum`], then `add_pow` on each `(lo + d·T)^{2j+1}`, then a sum
swap. The outer range is `32` because `P_b` has degree `2b − 1 = 31`; the
binomial coefficients cut every term with `m > 2j + 1`, which is the same
cutting [`shiftCoeff_range`] performs from the other side. -/
theorem rangeProduct_shift (lo d T : F) :
    ArkLib.Lattices.Ajtai.InnerOuter.rangeProduct 16 (lo + d * T)
      = ∑ m ∈ Finset.range 32, shiftCoeff lo d m * T ^ m := by
  rw [rangeProduct_eq_sum]
  have hterm : ∀ j ∈ Finset.range 16,
      rc j * (lo + d * T) ^ (2 * j + 1)
        = ∑ m ∈ Finset.range 32,
            (rc j * ((Nat.choose (2 * j + 1) m : ℕ) : F) * lo ^ (2 * j + 1 - m))
              * (d ^ m * T ^ m) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [add_comm lo (d * T), add_pow, Finset.mul_sum]
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : 2 * j + 1 + 1 ≤ 32)]
    have hhigh : ∑ m ∈ Finset.Ico (2 * j + 1 + 1) 32,
        (rc j * ((Nat.choose (2 * j + 1) m : ℕ) : F) * lo ^ (2 * j + 1 - m))
          * (d ^ m * T ^ m) = 0 := by
      refine Finset.sum_eq_zero (fun m hm => ?_)
      have : 2 * j + 1 < m := by simp only [Finset.mem_Ico] at hm; omega
      rw [Nat.choose_eq_zero_of_lt this]
      simp
    rw [hhigh, add_zero]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    simp only [Finset.mem_range] at hm
    rw [mul_pow]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  simp only [Finset.mem_range] at hm
  rw [shiftCoeff_range lo d m hm, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring


/-! ## 3. The loops

Four, and the first three are the new items: `shift_powers`, `shift_inner` and
`shift_accum`. The fourth pair is `round_poly_zero`'s own zero-fill and pair
loops, which changed shape with its body.
-/

/-- `shift_powers x` is `1, x, …, x^31`. -/
theorem shift_powers_loop_spec (x : cpoly.field.Ext4) (hx : Reduced x)
    (out : alloc.vec.Vec cpoly.field.Ext4) (cur : cpoly.field.Ext4) (k : Std.Usize)
    (hk : k.val ≤ 32) (hlen : out.val.length = k.val) (hred : VecReduced out)
    (hcr : Reduced cur) (hcv : toExt cur = toExt x ^ k.val)
    (hov : ∀ e, e < k.val → toExt (out.val.getD e cpoly.field.Ext4.ZERO) = toExt x ^ e) :
    sumcheck.shift_powers_loop x params.SHIFT_DEG out cur k
      ⦃ z => z.val.length = 32 ∧ VecReduced z ∧
          ∀ e, e < 32 → toExt (z.val.getD e cpoly.field.Ext4.ZERO) = toExt x ^ e ⦄ := by
  rw [sumcheck.shift_powers_loop]
  apply loop.spec_decr_nat (fun r => 32 - r.2.2.val)
    (fun r => r.2.2.val ≤ 32 ∧ r.1.val.length = r.2.2.val ∧ VecReduced r.1
      ∧ Reduced r.2.1 ∧ toExt r.2.1 = toExt x ^ r.2.2.val
      ∧ ∀ e, e < r.2.2.val → toExt (r.1.val.getD e cpoly.field.Ext4.ZERO) = toExt x ^ e)
  · rintro ⟨o, c, kk⟩ ⟨hkk, hol, hor, hcr1, hcv1, hov1⟩
    dsimp only at hkk hol hor hcr1 hcv1 hov1
    simp only [sumcheck.shift_powers_loop.body]
    by_cases hlt : kk < params.SHIFT_DEG
    · rw [if_pos hlt]
      have hklt : kk.val < 32 := by have := shift_deg_val; scalar_tac
      have hmax : o.val.length < Std.Usize.max := by rw [hol]; scalar_tac
      step as ⟨o1, ho1⟩
      step with ext_mul_spec c x hcr1 hx as ⟨c1, hc1r, hc1v⟩
      step as ⟨kk1, hkk1⟩
      refine ⟨by scalar_tac, ?_, ?_, hc1r, ?_, ?_, by scalar_tac⟩
      · rw [ho1, hkk1, List.length_append, hol]; simp
      · intro a ha
        rw [ho1] at ha
        rcases List.mem_append.mp ha with h | h
        · exact hor a h
        · rw [List.mem_singleton.mp h]; exact hcr1
      · rw [hc1v, hcv1, hkk1, pow_succ]
      · intro e he
        rw [hkk1] at he
        rcases Nat.lt_or_ge e kk.val with helt | hege
        · rw [ho1, HachiEquiv.AuxGoldTransform.getD_append_lt' _ _ _ (by omega)]
          exact hov1 e helt
        · have heq : e = o.val.length := by omega
          rw [heq, ho1, HachiEquiv.AuxGoldTransform.getD_append_eq', hol, hcv1]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : kk.val = 32 := by have := shift_deg_val; scalar_tac
      exact ⟨by rw [hol, heq], hor, fun e he => hov1 e (by rw [heq]; exact he)⟩
  · exact ⟨hk, hlen, hred, hcr, hcv, hov⟩

/-- **`shift_powers`.** -/
theorem shift_powers_spec (x : cpoly.field.Ext4) (hx : Reduced x) :
    sumcheck.shift_powers x
      ⦃ z => z.val.length = 32 ∧ VecReduced z ∧
          ∀ e, e < 32 → toExt (z.val.getD e cpoly.field.Ext4.ZERO) = toExt x ^ e ⦄ := by
  rw [sumcheck.shift_powers]
  simp only [alloc.vec.Vec.with_capacity]
  exact shift_powers_loop_spec x hx (alloc.vec.Vec.new cpoly.field.Ext4)
    cpoly.field.Ext4.ONE 0#usize (by simp) (by simp) (by intro a ha; simp at ha)
    reduced_ONE (by simp) (by intro e he; simp at he)


/-- The `j` loop of `shift_inner`: the running sum is the table contracted
against the powers of `lo`, from `m / 2` up. -/
theorem shift_inner_loop_spec (lop : alloc.vec.Vec cpoly.field.Ext4)
    (m rows deg : Std.Usize) (s : cpoly.field.Ext4) (j : Std.Usize) (X : F)
    (hrows : rows.val = 16) (hdeg : deg.val = 32) (hm : m.val < 32)
    (hlen : lop.val.length = 32) (hlr : VecReduced lop)
    (hv : ∀ e, e < 32 → toExt (lop.val.getD e cpoly.field.Ext4.ZERO) = X ^ e)
    (hj0 : m.val / 2 ≤ j.val) (hj : j.val ≤ 16) (hsr : Reduced s)
    (hsv : toExt s
      = ∑ j' ∈ Finset.Ico (m.val / 2) j.val, st j' m.val * X ^ (2 * j' + 1 - m.val)) :
    sumcheck.shift_inner_loop lop m rows deg s j
      ⦃ z => Reduced z ∧ toExt z
          = ∑ j' ∈ Finset.Ico (m.val / 2) 16, st j' m.val * X ^ (2 * j' + 1 - m.val) ⦄ := by
  rw [sumcheck.shift_inner_loop]
  apply loop.spec_decr_nat (fun r => 16 - r.2.val)
    (fun r => m.val / 2 ≤ r.2.val ∧ r.2.val ≤ 16 ∧ Reduced r.1
      ∧ toExt r.1 = ∑ j' ∈ Finset.Ico (m.val / 2) r.2.val,
          st j' m.val * X ^ (2 * j' + 1 - m.val))
  · rintro ⟨ss, jj⟩ ⟨hj0', hjb, hsr', hsv'⟩
    dsimp only at hj0' hjb hsr' hsv'
    simp only [sumcheck.shift_inner_loop.body]
    by_cases hlt : jj < rows
    · rw [if_pos hlt]
      have hjlt : jj.val < 16 := by scalar_tac
      -- `k = 2j + 1 ≥ m`, which is what makes `k - m` total
      have hkm : m.val ≤ 2 * jj.val + 1 := by omega
      step as ⟨i, hi⟩
      step as ⟨k, hk⟩
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = jj.val * 32 + m.val := by rw [hi2, hi1, hdeg]
      have hi2b : i2.val < params.SHIFT_T.val.length := by
        rw [hi2v, shift_t_length]; omega
      step as ⟨i3, hi3⟩
      step with HachiEquiv.Field.fp_new_spec i3 as ⟨f, hRf, hfv⟩
      step as ⟨i4, hi4⟩
      have hi4v : i4.val = 2 * jj.val + 1 - m.val := by rw [hi4, hk, hi]
      have hi4b : i4.val < lop.val.length := by rw [hi4v, hlen]; omega
      step as ⟨e, he⟩
      have hRe : Reduced e := hlr _ (by rw [he]; exact List.getElem_mem hi4b)
      have hev : toExt e = X ^ (2 * jj.val + 1 - m.val) := by
        rw [he, ← hi4v, ← List.getD_eq_getElem (l := lop.val) (d := cpoly.field.Ext4.ZERO) hi4b]
        exact hv i4.val (by rw [hlen] at hi4b; exact hi4b)
      step with HachiEquiv.Ext.fp_ext_mul_spec f e hRf hRe as ⟨e1, hRe1, he1v⟩
      step with HachiEquiv.Ext.ext_add_spec ss e1 hsr' hRe1 as ⟨s1, hRs1, hs1v⟩
      step as ⟨jj1, hjj1⟩
      refine ⟨by omega, by omega, hRs1, ?_, by omega⟩
      have hterm : toExt e1 = st jj.val m.val * X ^ (2 * jj.val + 1 - m.val) := by
        rw [he1v, hev, hfv, hi3, ofBase_natCast,
          st_of_index i2.val hi2b jj.val m.val hi2v]
      rw [hs1v, hsv', hterm, hjj1,
        Finset.sum_Ico_succ_top (by omega : m.val / 2 ≤ jj.val)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = 16 := by scalar_tac
      exact ⟨hsr', by rw [hsv', heq]⟩
  · exact ⟨hj0, hj, hsr, hsv⟩

/-- **`shift_inner`** is `S_m`: the table's row contraction against the powers
of `lo`. -/
theorem shift_inner_spec (lop : alloc.vec.Vec cpoly.field.Ext4) (m : Std.Usize) (X : F)
    (hm : m.val < 32) (hlen : lop.val.length = 32) (hlr : VecReduced lop)
    (hv : ∀ e, e < 32 → toExt (lop.val.getD e cpoly.field.Ext4.ZERO) = X ^ e) :
    sumcheck.shift_inner lop m
      ⦃ z => Reduced z ∧ toExt z
          = ∑ j' ∈ Finset.Ico (m.val / 2) 16, st j' m.val * X ^ (2 * j' + 1 - m.val) ⦄ := by
  rw [sumcheck.shift_inner]
  step as ⟨j, hj⟩
  have hjv : j.val = m.val / 2 := by rw [hj]
  exact shift_inner_loop_spec lop m params.SHIFT_ROWS params.SHIFT_DEG
    cpoly.field.Ext4.ZERO j X shift_rows_val shift_deg_val hm hlen hlr hv
    (by omega) (by omega) HachiEquiv.Ext.reduced_ZERO
    (by rw [HachiEquiv.Ext.toExt_ZERO, hjv]; simp)


/-- The `m` loop of `shift_accum`: coefficient `m` gains `e · Δ^m · S_m`, and
`Δ^m` is the running scalar. -/
theorem shift_accum_loop_spec (acc lop : alloc.vec.Vec cpoly.field.Ext4)
    (d e : cpoly.field.Ext4) (n : Std.Usize) (dpow : cpoly.field.Ext4) (m : Std.Usize)
    (X : F) (acc0 : ℕ → F)
    (hn : n.val = 32) (hm : m.val ≤ 32)
    (hlen : lop.val.length = 32) (hlr : VecReduced lop)
    (hv : ∀ t, t < 32 → toExt (lop.val.getD t cpoly.field.Ext4.ZERO) = X ^ t)
    (hdr : Reduced d) (her : Reduced e)
    (halen : acc.val.length = 32) (har : VecReduced acc)
    (hdpr : Reduced dpow) (hdpv : toExt dpow = toExt e * toExt d ^ m.val)
    (hav : ∀ t, t < 32 → toExt (acc.val.getD t cpoly.field.Ext4.ZERO)
      = acc0 t + (if t < m.val then toExt e * shiftCoeff X (toExt d) t else 0)) :
    sumcheck.shift_accum_loop acc lop d n dpow m
      ⦃ z => z.val.length = 32 ∧ VecReduced z ∧
          ∀ t, t < 32 → toExt (z.val.getD t cpoly.field.Ext4.ZERO)
            = acc0 t + toExt e * shiftCoeff X (toExt d) t ⦄ := by
  rw [sumcheck.shift_accum_loop]
  apply loop.spec_decr_nat (fun r => 32 - r.2.2.val)
    (fun r => r.2.2.val ≤ 32 ∧ r.1.val.length = 32 ∧ VecReduced r.1
      ∧ Reduced r.2.1 ∧ toExt r.2.1 = toExt e * toExt d ^ r.2.2.val
      ∧ ∀ t, t < 32 → toExt (r.1.val.getD t cpoly.field.Ext4.ZERO)
          = acc0 t + (if t < r.2.2.val then toExt e * shiftCoeff X (toExt d) t else 0))
  · rintro ⟨a, dp, mm⟩ ⟨hmm, hal, har', hdpr', hdpv', hav'⟩
    dsimp only at hmm hal har' hdpr' hdpv' hav'
    simp only [sumcheck.shift_accum_loop.body]
    by_cases hlt : mm < n
    · rw [if_pos hlt]
      have hmlt : mm.val < 32 := by rw [← hn]; scalar_tac
      step with shift_inner_spec lop mm X hmlt hlen hlr hv as ⟨sv, hRsv, hsvv⟩
      have hab : mm.val < a.val.length := by rw [hal]; exact hmlt
      step as ⟨e1, he1⟩
      have hRe1 : Reduced e1 := har' _ (by rw [he1]; exact List.getElem_mem hab)
      have he1v : toExt e1 = acc0 mm.val + 0 := by
        rw [he1, ← List.getD_eq_getElem (l := a.val) (d := cpoly.field.Ext4.ZERO) hab,
          hav' mm.val hmlt, if_neg (by omega)]
      step with HachiEquiv.Ext.ext_mul_spec dp sv hdpr' hRsv as ⟨e3, hRe3, he3v⟩
      step with HachiEquiv.Ext.ext_add_spec e1 e3 hRe1 hRe3 as ⟨e4, hRe4, he4v⟩
      step as ⟨elem, back, helem, hback⟩
      step with HachiEquiv.Ext.ext_mul_spec dp d hdpr' hdr as ⟨dp1, hRdp1, hdp1v⟩
      step as ⟨mm1, hmm1⟩
      have hset : back e4 = a.set mm e4 := by rw [hback]
      have he4val : toExt e4 = acc0 mm.val + toExt e * shiftCoeff X (toExt d) mm.val := by
        rw [he4v, he1v, he3v, hsvv, hdpv', shiftCoeff]
        ring
      refine ⟨by omega, ?_, ?_, hRdp1, ?_, ?_, by omega⟩
      · rw [hset, alloc.vec.Vec.set_val_eq, List.length_set, hal]
      · intro y hy
        rw [hset, alloc.vec.Vec.set_val_eq] at hy
        rcases List.mem_or_eq_of_mem_set hy with h | h
        · exact har' y h
        · rw [h]; exact hRe4
      · rw [hdp1v, hdpv', hmm1, pow_succ]; ring
      · intro t ht
        rw [hset, alloc.vec.Vec.set_val_eq, hmm1]
        rcases eq_or_ne t mm.val with rfl | hne
        · rw [List.getD_eq_getElem _ _ (by rw [List.length_set, hal]; exact ht),
            List.getElem_set_self, he4val, if_pos (by omega)]
        · rw [List.getD_eq_getElem _ _ (by rw [List.length_set, hal]; exact ht),
            List.getElem_set_ne (by omega),
            ← List.getD_eq_getElem (l := a.val) (d := cpoly.field.Ext4.ZERO) (by rw [hal]; exact ht),
            hav' t ht]
          by_cases hc : t < mm.val
          · rw [if_pos hc, if_pos (by omega)]
          · rw [if_neg hc, if_neg (by omega)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : mm.val = 32 := by rw [← hn]; scalar_tac
      refine ⟨hal, har', fun t ht => ?_⟩
      rw [hav' t ht, if_pos (by omega)]
  · exact ⟨hm, halen, har, hdpr, hdpv, hav⟩

/-- **`shift_accum`**: one pair's contribution to the 32 shifted coefficients. -/
theorem shift_accum_spec (acc lop : alloc.vec.Vec cpoly.field.Ext4)
    (d e : cpoly.field.Ext4) (X : F) (acc0 : ℕ → F)
    (hlen : lop.val.length = 32) (hlr : VecReduced lop)
    (hv : ∀ t, t < 32 → toExt (lop.val.getD t cpoly.field.Ext4.ZERO) = X ^ t)
    (hdr : Reduced d) (her : Reduced e)
    (halen : acc.val.length = 32) (har : VecReduced acc)
    (hav : ∀ t, t < 32 → toExt (acc.val.getD t cpoly.field.Ext4.ZERO) = acc0 t) :
    sumcheck.shift_accum acc lop d e
      ⦃ z => z.val.length = 32 ∧ VecReduced z ∧
          ∀ t, t < 32 → toExt (z.val.getD t cpoly.field.Ext4.ZERO)
            = acc0 t + toExt e * shiftCoeff X (toExt d) t ⦄ := by
  rw [sumcheck.shift_accum]
  exact shift_accum_loop_spec acc lop d e params.SHIFT_DEG e 0#usize
    X acc0 shift_deg_val (by simp) hlen hlr hv hdr her halen har
    her (by simp)
    (by intro t ht; rw [hav t ht, if_neg (by simp)]; ring)


/-! ## 4. `round_poly_zero`'s own two loops -/

/-- The zero-fill: `SHIFT_DEG` zero coefficients. -/
theorem zero_fill_spec (n : Std.Usize) (acc : alloc.vec.Vec cpoly.field.Ext4)
    (i : Std.Usize) (hn : n.val = 32) (hi : i.val ≤ 32)
    (hlen : acc.val.length = i.val) (har : VecReduced acc)
    (hav : ∀ t, t < i.val → toExt (acc.val.getD t cpoly.field.Ext4.ZERO) = 0) :
    sumcheck.round_poly_zero_loop0 n acc i
      ⦃ z => z.val.length = 32 ∧ VecReduced z ∧
          ∀ t, t < 32 → toExt (z.val.getD t cpoly.field.Ext4.ZERO) = 0 ⦄ := by
  rw [sumcheck.round_poly_zero_loop0]
  apply loop.spec_decr_nat (fun r => 32 - r.2.val)
    (fun r => r.2.val ≤ 32 ∧ r.1.val.length = r.2.val ∧ VecReduced r.1
      ∧ ∀ t, t < r.2.val → toExt (r.1.val.getD t cpoly.field.Ext4.ZERO) = 0)
  · rintro ⟨a, ii⟩ ⟨hii, hal, har', hav'⟩
    dsimp only at hii hal har' hav'
    simp only [sumcheck.round_poly_zero_loop0.body]
    by_cases hlt : ii < n
    · rw [if_pos hlt]
      have hilt : ii.val < 32 := by rw [← hn]; scalar_tac
      have hmax : a.val.length < Std.Usize.max := by rw [hal]; scalar_tac
      step as ⟨a1, ha1⟩
      step as ⟨ii1, hii1⟩
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · rw [ha1, hii1, List.length_append, hal]; simp
      · intro y hy
        rw [ha1] at hy
        rcases List.mem_append.mp hy with h | h
        · exact har' y h
        · rw [List.mem_singleton.mp h]; exact HachiEquiv.Ext.reduced_ZERO
      · intro t ht
        rw [hii1] at ht
        rcases Nat.lt_or_ge t ii.val with hc | hc
        · rw [ha1, HachiEquiv.AuxGoldTransform.getD_append_lt' _ _ _ (by omega)]
          exact hav' t hc
        · have heq : t = a.val.length := by omega
          rw [heq, ha1, HachiEquiv.AuxGoldTransform.getD_append_eq']
          exact HachiEquiv.Ext.toExt_ZERO
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ii.val = 32 := by rw [← hn]; scalar_tac
      exact ⟨by rw [hal, heq], har', fun t ht => hav' t (by rw [heq]; exact ht)⟩
  · exact ⟨hi, hlen, har, hav⟩

/-- The `lo`/`Δ` of pair `y`, as elements of `F`. -/
def loF (w : alloc.vec.Vec cpoly.field.Ext4) (y : ℕ) : F :=
  toExt (w.val.getD (2 * y) cpoly.field.Ext4.ZERO)

/-- `Δ_y = hi_y − lo_y`. -/
def dF (w : alloc.vec.Vec cpoly.field.Ext4) (y : ℕ) : F :=
  toExt (w.val.getD (2 * y + 1) cpoly.field.Ext4.ZERO) - loF w y

/-- `eq[y]`, as an element of `F`. -/
def eqF (eq : alloc.vec.Vec cpoly.field.Ext4) (y : ℕ) : F :=
  toExt (eq.val.getD y cpoly.field.Ext4.ZERO)

/-- The pair loop: after `y` pairs, coefficient `t` is the partial sum
`Σ_{y' < y} eq[y'] · shiftCoeff lo_{y'} Δ_{y'} t`. -/
theorem pair_loop_spec (w eq : alloc.vec.Vec cpoly.field.Ext4) (half : Std.Usize)
    (acc : alloc.vec.Vec cpoly.field.Ext4) (y : Std.Usize)
    (hhalf : half.val = eq.val.length) (hwl : w.val.length = 2 * eq.val.length)
    (hwr : VecReduced w) (her : VecReduced eq)
    (hy : y.val ≤ half.val) (halen : acc.val.length = 32) (har : VecReduced acc)
    (hav : ∀ t, t < 32 → toExt (acc.val.getD t cpoly.field.Ext4.ZERO)
      = ∑ y' ∈ Finset.range y.val, eqF eq y' * shiftCoeff (loF w y') (dF w y') t) :
    sumcheck.round_poly_zero_loop1 w eq half acc y
      ⦃ z => z.val.length = 32 ∧ VecReduced z ∧
          ∀ t, t < 32 → toExt (z.val.getD t cpoly.field.Ext4.ZERO)
            = ∑ y' ∈ Finset.range half.val,
                eqF eq y' * shiftCoeff (loF w y') (dF w y') t ⦄ := by
  rw [sumcheck.round_poly_zero_loop1]
  apply loop.spec_decr_nat (fun r => half.val - r.2.val)
    (fun r => r.2.val ≤ half.val ∧ r.1.val.length = 32 ∧ VecReduced r.1
      ∧ ∀ t, t < 32 → toExt (r.1.val.getD t cpoly.field.Ext4.ZERO)
          = ∑ y' ∈ Finset.range r.2.val, eqF eq y' * shiftCoeff (loF w y') (dF w y') t)
  · rintro ⟨a, yy⟩ ⟨hyy, hal, har', hav'⟩
    dsimp only at hyy hal har' hav'
    simp only [sumcheck.round_poly_zero_loop1.body]
    by_cases hlt : yy < half
    · rw [if_pos hlt]
      have hylt : yy.val < eq.val.length := by rw [← hhalf]; scalar_tac
      have hb0 : 2 * yy.val < w.val.length := by rw [hwl]; omega
      have hb1 : 2 * yy.val + 1 < w.val.length := by rw [hwl]; omega
      step as ⟨i, hi⟩
      step as ⟨lo, hlo⟩
      have hlob : i.val < w.val.length := by rw [hi]; exact hb0
      have hRlo : Reduced lo := hwr _ (by rw [hlo]; exact List.getElem_mem hlob)
      have hlov : toExt lo = loF w yy.val := by
        rw [hlo, loF, ← hi,
          ← List.getD_eq_getElem (l := w.val) (d := cpoly.field.Ext4.ZERO) hlob]
      step as ⟨i1, hi1⟩
      step as ⟨hiw, hhiw⟩
      have hhib : i1.val < w.val.length := by rw [hi1, hi]; exact hb1
      have hRhi : Reduced hiw := hwr _ (by rw [hhiw]; exact List.getElem_mem hhib)
      have hhiv : toExt hiw = toExt (w.val.getD (2 * yy.val + 1) cpoly.field.Ext4.ZERO) := by
        rw [hhiw, ← List.getD_eq_getElem (l := w.val) (d := cpoly.field.Ext4.ZERO) hhib,
          hi1, hi]
      step with shift_powers_spec lo hRlo as ⟨lop, hlopl, hlopr, hlopv⟩
      step with HachiEquiv.Ext.ext_sub_spec hiw lo hRhi hRlo as ⟨dd, hRdd, hddv⟩
      have hddval : toExt dd = dF w yy.val := by rw [hddv, hhiv, hlov, dF]
      step as ⟨ev, hev⟩
      have hRev : Reduced ev := her _ (by rw [hev]; exact List.getElem_mem hylt)
      have hevv : toExt ev = eqF eq yy.val := by
        rw [hev, eqF, ← List.getD_eq_getElem (l := eq.val) (d := cpoly.field.Ext4.ZERO) hylt]
      step with shift_accum_spec a lop dd ev (loF w yy.val)
        (fun t => ∑ y' ∈ Finset.range yy.val, eqF eq y' * shiftCoeff (loF w y') (dF w y') t)
        hlopl hlopr (by intro t ht; rw [hlopv t ht, hlov]) hRdd hRev hal har' hav'
        as ⟨a1, ha1l, ha1r, ha1v⟩
      step as ⟨yy1, hyy1⟩
      refine ⟨by omega, ha1l, ha1r, ?_, by omega⟩
      intro t ht
      rw [ha1v t ht, hyy1, Finset.sum_range_succ, hevv, hddval]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : yy.val = half.val := by scalar_tac
      exact ⟨hal, har', fun t ht => by rw [hav' t ht, heq]⟩
  · exact ⟨hy, halen, har, hav⟩


/-- `Usize.max` is at least `2^32 - 1`; a local copy, as `AuxShort` has. -/
private theorem usize_max_ge4' : (4294967295 : ℕ) ≤ Std.Usize.max := by
  rw [Std.Usize.max_def]
  rcases System.Platform.numBits_eq with h | h <;> simp [Std.Usize.numBits, h]

/-! ## 5. The base-field path: round 0 (Stage 6 candidate T3, round 0)

Round 0 walks `2^(m₀−1)` pairs -- **half of every pair the protocol
evaluates** -- with `w̃` still in the base field, so `lo`, `Δ` and all their
powers stay in `ZMod q` and only the final `eq[y] · c_m` crosses into the
extension. The algebra is the same shift; the only new content is that the
coefficient is computed in `ZMod q` and embedded, and `phiF` is a ring
homomorphism, so [`shiftCoeffK_phi`] moves it across in one line. -/

/-- [`st`] in the base field. -/
def stK (j m : ℕ) : ZMod q := ((params.SHIFT_T.val.getD (j * 32 + m) 0#u64).val : ℕ)

theorem stK_phi (j m : ℕ) : phiF (stK j m) = st j m := by
  rw [stK, st, phiF_apply, ofBase_natCast]

/-- [`shiftCoeff`] in the base field. -/
def shiftCoeffK (lo d : ZMod q) (m : ℕ) : ZMod q :=
  d ^ m * ∑ j ∈ Finset.Ico (m / 2) 16, stK j m * lo ^ (2 * j + 1 - m)

theorem shiftCoeffK_phi (lo d : ZMod q) (m : ℕ) :
    phiF (shiftCoeffK lo d m) = shiftCoeff (phiF lo) (phiF d) m := by
  rw [shiftCoeffK, shiftCoeff, map_mul, map_pow, map_sum]
  refine congrArg (fun t => phiF d ^ m * t) (Finset.sum_congr rfl (fun j _ => ?_))
  rw [map_mul, map_pow, stK_phi]

/-- **`shift_powers_base`.** -/
theorem shift_powers_base_loop_spec (x : cpoly.field.Fp) (hx : Red x)
    (out : alloc.vec.Vec cpoly.field.Fp) (cur : cpoly.field.Fp) (k : Std.Usize)
    (hk : k.val ≤ 32) (hlen : out.val.length = k.val) (hred : ∀ a ∈ out.val, Red a)
    (hcr : Red cur) (hcv : toK cur = toK x ^ k.val)
    (hov : ∀ e, e < k.val → coeffK out e = toK x ^ e) :
    sumcheck.shift_powers_base_loop x params.SHIFT_DEG out cur k
      ⦃ z => z.val.length = 32 ∧ (∀ a ∈ z.val, Red a) ∧
          ∀ e, e < 32 → coeffK z e = toK x ^ e ⦄ := by
  rw [sumcheck.shift_powers_base_loop]
  apply loop.spec_decr_nat (fun r => 32 - r.2.2.val)
    (fun r => r.2.2.val ≤ 32 ∧ r.1.val.length = r.2.2.val ∧ (∀ a ∈ r.1.val, Red a)
      ∧ Red r.2.1 ∧ toK r.2.1 = toK x ^ r.2.2.val
      ∧ ∀ e, e < r.2.2.val → coeffK r.1 e = toK x ^ e)
  · rintro ⟨o, c, kk⟩ ⟨hkk, hol, hor, hcr1, hcv1, hov1⟩
    dsimp only at hkk hol hor hcr1 hcv1 hov1
    simp only [sumcheck.shift_powers_base_loop.body]
    by_cases hlt : kk < params.SHIFT_DEG
    · rw [if_pos hlt]
      have hklt : kk.val < 32 := by have := shift_deg_val; scalar_tac
      have hmax : o.val.length < Std.Usize.max := by
        rw [hol]
        have h2 := usize_max_ge4'
        omega
      step as ⟨o1, ho1⟩
      step with HachiEquiv.Field.fp_mul_spec c x hcr1 hx as ⟨c1, hc1r, hc1v⟩
      step as ⟨kk1, hkk1⟩
      refine ⟨by omega, ?_, ?_, hc1r, ?_, ?_, by omega⟩
      · rw [ho1, hkk1, List.length_append, hol]; simp
      · intro a ha
        rw [ho1] at ha
        rcases List.mem_append.mp ha with h | h
        · exact hor a h
        · rw [List.mem_singleton.mp h]; exact hcr1
      · rw [hc1v, hcv1, hkk1, pow_succ]
      · intro e he
        rw [hkk1] at he
        rcases Nat.lt_or_ge e kk.val with helt | hege
        · unfold coeffK
          rw [ho1, HachiEquiv.AuxGoldTransform.getD_append_lt' _ _ _ (by omega)]
          exact hov1 e helt
        · have heq : e = o.val.length := by omega
          unfold coeffK
          rw [heq, ho1, HachiEquiv.AuxGoldTransform.getD_append_eq', hol]
          exact hcv1
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : kk.val = 32 := by have := shift_deg_val; scalar_tac
      exact ⟨by rw [hol, heq], hor, fun e he => hov1 e (by rw [heq]; exact he)⟩
  · exact ⟨hk, hlen, hred, hcr, hcv, hov⟩

theorem shift_powers_base_spec (x : cpoly.field.Fp) (hx : Red x) :
    sumcheck.shift_powers_base x
      ⦃ z => z.val.length = 32 ∧ (∀ a ∈ z.val, Red a) ∧
          ∀ e, e < 32 → coeffK z e = toK x ^ e ⦄ := by
  rw [sumcheck.shift_powers_base]
  simp only [alloc.vec.Vec.with_capacity]
  exact shift_powers_base_loop_spec x hx (alloc.vec.Vec.new cpoly.field.Fp)
    cpoly.field.Fp.ONE 0#usize (by simp) (by simp) (by intro a ha; simp at ha)
    HachiEquiv.Field.Red_one (by simp [HachiEquiv.Field.toK_one])
    (by intro e he; simp at he)

/-- **`shift_inner_base`** is `S_m` in `ZMod q`. -/
theorem shift_inner_base_loop_spec (lop : alloc.vec.Vec cpoly.field.Fp)
    (m rows deg : Std.Usize) (acc : cpoly.field.Fp) (j : Std.Usize) (X : ZMod q)
    (hrows : rows.val = 16) (hdeg : deg.val = 32) (hm : m.val < 32)
    (hlen : lop.val.length = 32) (hlr : ∀ a ∈ lop.val, Red a)
    (hv : ∀ e, e < 32 → coeffK lop e = X ^ e)
    (hj0 : m.val / 2 ≤ j.val) (hj : j.val ≤ 16) (har : Red acc)
    (hav : toK acc = ∑ j' ∈ Finset.Ico (m.val / 2) j.val,
             stK j' m.val * X ^ (2 * j' + 1 - m.val)) :
    sumcheck.shift_inner_base_loop lop m rows deg acc j
      ⦃ z => Red z ∧ toK z
          = ∑ j' ∈ Finset.Ico (m.val / 2) 16, stK j' m.val * X ^ (2 * j' + 1 - m.val) ⦄ := by
  rw [sumcheck.shift_inner_base_loop]
  apply loop.spec_decr_nat (fun r => 16 - r.2.val)
    (fun r => m.val / 2 ≤ r.2.val ∧ r.2.val ≤ 16 ∧ Red r.1
      ∧ toK r.1 = ∑ j' ∈ Finset.Ico (m.val / 2) r.2.val,
          stK j' m.val * X ^ (2 * j' + 1 - m.val))
  · rintro ⟨ss, jj⟩ ⟨hj0', hjb, hsr, hsv⟩
    dsimp only at hj0' hjb hsr hsv
    simp only [sumcheck.shift_inner_base_loop.body]
    by_cases hlt : jj < rows
    · rw [if_pos hlt]
      have hjlt : jj.val < 16 := by scalar_tac
      have hkm : m.val ≤ 2 * jj.val + 1 := by omega
      step as ⟨i, hi⟩
      step as ⟨k, hk⟩
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = jj.val * 32 + m.val := by rw [hi2, hi1, hdeg]
      have hi2b : i2.val < params.SHIFT_T.val.length := by
        rw [hi2v, shift_t_length]; omega
      step as ⟨i3, hi3⟩
      step with HachiEquiv.Field.fp_new_spec i3 as ⟨f, hRf, hfv⟩
      step as ⟨i4, hi4⟩
      have hi4v : i4.val = 2 * jj.val + 1 - m.val := by rw [hi4, hk, hi]
      have hi4b : i4.val < lop.val.length := by rw [hi4v, hlen]; omega
      step as ⟨e, he⟩
      have hRe : Red e := hlr _ (by rw [he]; exact List.getElem_mem hi4b)
      have hev : toK e = X ^ (2 * jj.val + 1 - m.val) := by
        rw [he, ← hi4v, ← coeffK_of_lt hi4b]
        exact hv i4.val (by rw [hlen] at hi4b; exact hi4b)
      step with HachiEquiv.Field.fp_mul_spec f e hRf hRe as ⟨e1, hRe1, he1v⟩
      step with HachiEquiv.Field.fp_add_spec ss e1 hsr hRe1 as ⟨s1, hRs1, hs1v⟩
      step as ⟨jj1, hjj1⟩
      refine ⟨by omega, by omega, hRs1, ?_, by omega⟩
      have hterm : toK e1 = stK jj.val m.val * X ^ (2 * jj.val + 1 - m.val) := by
        rw [he1v, hev, hfv, hi3, stK]
        congr 2
        rw [← hi2v, List.getD_eq_getElem _ _ hi2b]
      rw [hs1v, hsv, hterm, hjj1,
        Finset.sum_Ico_succ_top (by omega : m.val / 2 ≤ jj.val)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = 16 := by scalar_tac
      exact ⟨hsr, by rw [hsv, heq]⟩
  · exact ⟨hj0, hj, har, hav⟩

theorem shift_inner_base_spec (lop : alloc.vec.Vec cpoly.field.Fp) (m : Std.Usize)
    (X : ZMod q) (hm : m.val < 32) (hlen : lop.val.length = 32)
    (hlr : ∀ a ∈ lop.val, Red a)
    (hv : ∀ e, e < 32 → coeffK lop e = X ^ e) :
    sumcheck.shift_inner_base lop m
      ⦃ z => Red z ∧ toK z
          = ∑ j' ∈ Finset.Ico (m.val / 2) 16, stK j' m.val * X ^ (2 * j' + 1 - m.val) ⦄ := by
  rw [sumcheck.shift_inner_base]
  step as ⟨j, hj⟩
  have hjv : j.val = m.val / 2 := by rw [hj]
  exact shift_inner_base_loop_spec lop m params.SHIFT_ROWS params.SHIFT_DEG
    cpoly.field.Fp.ZERO j X shift_rows_val shift_deg_val hm hlen hlr hv
    (by omega) (by omega) HachiEquiv.Field.Red_zero
    (by rw [HachiEquiv.Field.toK_zero, hjv]; simp)


/-- **`shift_accum_base`**: one pair's contribution, with the base-field
coefficient embedded exactly once per slot. -/
theorem shift_accum_base_loop_spec (acc : alloc.vec.Vec cpoly.field.Ext4)
    (lop : alloc.vec.Vec cpoly.field.Fp) (d : cpoly.field.Fp) (e : cpoly.field.Ext4)
    (n : Std.Usize) (dpow : cpoly.field.Fp) (m : Std.Usize)
    (X : ZMod q) (acc0 : ℕ → F)
    (hn : n.val = 32) (hm : m.val ≤ 32)
    (hlen : lop.val.length = 32) (hlr : ∀ a ∈ lop.val, Red a)
    (hv : ∀ t, t < 32 → coeffK lop t = X ^ t)
    (hdr : Red d) (her : Reduced e)
    (halen : acc.val.length = 32) (har : VecReduced acc)
    (hdpr : Red dpow) (hdpv : toK dpow = toK d ^ m.val)
    (hav : ∀ t, t < 32 → toExt (acc.val.getD t cpoly.field.Ext4.ZERO)
      = acc0 t + (if t < m.val then phiF (shiftCoeffK X (toK d) t) * toExt e else 0)) :
    sumcheck.shift_accum_base_loop acc lop d e n dpow m
      ⦃ z => z.val.length = 32 ∧ VecReduced z ∧
          ∀ t, t < 32 → toExt (z.val.getD t cpoly.field.Ext4.ZERO)
            = acc0 t + phiF (shiftCoeffK X (toK d) t) * toExt e ⦄ := by
  rw [sumcheck.shift_accum_base_loop]
  apply loop.spec_decr_nat (fun r => 32 - r.2.2.val)
    (fun r => r.2.2.val ≤ 32 ∧ r.1.val.length = 32 ∧ VecReduced r.1
      ∧ Red r.2.1 ∧ toK r.2.1 = toK d ^ r.2.2.val
      ∧ ∀ t, t < 32 → toExt (r.1.val.getD t cpoly.field.Ext4.ZERO)
          = acc0 t + (if t < r.2.2.val then phiF (shiftCoeffK X (toK d) t) * toExt e else 0))
  · rintro ⟨a, dp, mm⟩ ⟨hmm, hal, har', hdpr', hdpv', hav'⟩
    dsimp only at hmm hal har' hdpr' hdpv' hav'
    simp only [sumcheck.shift_accum_base_loop.body]
    by_cases hlt : mm < n
    · rw [if_pos hlt]
      have hmlt : mm.val < 32 := by rw [← hn]; scalar_tac
      step with shift_inner_base_spec lop mm X hmlt hlen hlr hv as ⟨sv, hRsv, hsvv⟩
      have hab : mm.val < a.val.length := by rw [hal]; exact hmlt
      step as ⟨cur, hcur⟩
      have hRcur : Reduced cur := har' _ (by rw [hcur]; exact List.getElem_mem hab)
      have hcurv : toExt cur = acc0 mm.val + 0 := by
        rw [hcur, ← List.getD_eq_getElem (l := a.val) (d := cpoly.field.Ext4.ZERO) hab,
          hav' mm.val hmlt, if_neg (by omega)]
      step with HachiEquiv.Field.fp_mul_spec dp sv hdpr' hRsv as ⟨f, hRf, hfv⟩
      step with HachiEquiv.Ext.fp_ext_mul_spec f e hRf her as ⟨e1, hRe1, he1v⟩
      step with HachiEquiv.Ext.ext_add_spec cur e1 hRcur hRe1 as ⟨nv, hRnv, hnvv⟩
      step as ⟨xa, back, hxa, hback⟩
      step with HachiEquiv.Field.fp_mul_spec dp d hdpr' hdr as ⟨dp1, hRdp1, hdp1v⟩
      step as ⟨mm1, hmm1⟩
      have hset : back nv = a.set mm nv := by rw [hback]
      have hnvval : toExt nv = acc0 mm.val + phiF (shiftCoeffK X (toK d) mm.val) * toExt e := by
        have hfval : toK f = shiftCoeffK X (toK d) mm.val := by
          rw [hfv, hdpv', hsvv, shiftCoeffK]
        rw [hnvv, hcurv, add_zero, he1v, hfval, phiF_apply]
      refine ⟨by omega, ?_, ?_, hRdp1, ?_, ?_, by omega⟩
      · rw [hset, alloc.vec.Vec.set_val_eq, List.length_set, hal]
      · intro y hy
        rw [hset, alloc.vec.Vec.set_val_eq] at hy
        rcases List.mem_or_eq_of_mem_set hy with h | h
        · exact har' y h
        · rw [h]; exact hRnv
      · rw [hdp1v, hdpv', hmm1, pow_succ]
      · intro t ht
        rw [hset, alloc.vec.Vec.set_val_eq, hmm1]
        rcases eq_or_ne t mm.val with rfl | hne
        · rw [List.getD_eq_getElem _ _ (by rw [List.length_set, hal]; exact ht),
            List.getElem_set_self, hnvval, if_pos (by omega)]
        · rw [List.getD_eq_getElem _ _ (by rw [List.length_set, hal]; exact ht),
            List.getElem_set_ne (by omega),
            ← List.getD_eq_getElem (l := a.val) (d := cpoly.field.Ext4.ZERO)
              (by rw [hal]; exact ht),
            hav' t ht]
          by_cases hc : t < mm.val
          · rw [if_pos hc, if_pos (by omega)]
          · rw [if_neg hc, if_neg (by omega)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : mm.val = 32 := by rw [← hn]; scalar_tac
      exact ⟨hal, har', fun t ht => by rw [hav' t ht, if_pos (by omega)]⟩
  · exact ⟨hm, halen, har, hdpr, hdpv, hav⟩

theorem shift_accum_base_spec (acc : alloc.vec.Vec cpoly.field.Ext4)
    (lop : alloc.vec.Vec cpoly.field.Fp) (d : cpoly.field.Fp) (e : cpoly.field.Ext4)
    (X : ZMod q) (acc0 : ℕ → F)
    (hlen : lop.val.length = 32) (hlr : ∀ a ∈ lop.val, Red a)
    (hv : ∀ t, t < 32 → coeffK lop t = X ^ t)
    (hdr : Red d) (her : Reduced e)
    (halen : acc.val.length = 32) (har : VecReduced acc)
    (hav : ∀ t, t < 32 → toExt (acc.val.getD t cpoly.field.Ext4.ZERO) = acc0 t) :
    sumcheck.shift_accum_base acc lop d e
      ⦃ z => z.val.length = 32 ∧ VecReduced z ∧
          ∀ t, t < 32 → toExt (z.val.getD t cpoly.field.Ext4.ZERO)
            = acc0 t + phiF (shiftCoeffK X (toK d) t) * toExt e ⦄ := by
  rw [sumcheck.shift_accum_base]
  exact shift_accum_base_loop_spec acc lop d e params.SHIFT_DEG cpoly.field.Fp.ONE
    0#usize X acc0 shift_deg_val (by simp) hlen hlr hv hdr her halen har
    HachiEquiv.Field.Red_one (by simp [HachiEquiv.Field.toK_one])
    (by intro t ht; rw [hav t ht, if_neg (by simp)]; ring)

/-! ### `round_poly_zero_base`'s own two loops -/

theorem zero_fill_base_spec (n : Std.Usize) (acc : alloc.vec.Vec cpoly.field.Ext4)
    (i : Std.Usize) (hn : n.val = 32) (hi : i.val ≤ 32)
    (hlen : acc.val.length = i.val) (har : VecReduced acc)
    (hav : ∀ t, t < i.val → toExt (acc.val.getD t cpoly.field.Ext4.ZERO) = 0) :
    sumcheck.round_poly_zero_base_loop0 n acc i
      ⦃ z => z.val.length = 32 ∧ VecReduced z ∧
          ∀ t, t < 32 → toExt (z.val.getD t cpoly.field.Ext4.ZERO) = 0 ⦄ := by
  rw [sumcheck.round_poly_zero_base_loop0]
  apply loop.spec_decr_nat (fun r => 32 - r.2.val)
    (fun r => r.2.val ≤ 32 ∧ r.1.val.length = r.2.val ∧ VecReduced r.1
      ∧ ∀ t, t < r.2.val → toExt (r.1.val.getD t cpoly.field.Ext4.ZERO) = 0)
  · rintro ⟨a, ii⟩ ⟨hii, hal, har', hav'⟩
    dsimp only at hii hal har' hav'
    simp only [sumcheck.round_poly_zero_base_loop0.body]
    by_cases hlt : ii < n
    · rw [if_pos hlt]
      have hilt : ii.val < 32 := by rw [← hn]; scalar_tac
      have hmax : a.val.length < Std.Usize.max := by
        rw [hal]; have := usize_max_ge4'; omega
      step as ⟨a1, ha1⟩
      step as ⟨ii1, hii1⟩
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · rw [ha1, hii1, List.length_append, hal]; simp
      · intro y hy
        rw [ha1] at hy
        rcases List.mem_append.mp hy with h | h
        · exact har' y h
        · rw [List.mem_singleton.mp h]; exact HachiEquiv.Ext.reduced_ZERO
      · intro t ht
        rw [hii1] at ht
        rcases Nat.lt_or_ge t ii.val with hc | hc
        · rw [ha1, HachiEquiv.AuxGoldTransform.getD_append_lt' _ _ _ (by omega)]
          exact hav' t hc
        · have heq : t = a.val.length := by omega
          rw [heq, ha1, HachiEquiv.AuxGoldTransform.getD_append_eq']
          exact HachiEquiv.Ext.toExt_ZERO
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ii.val = 32 := by rw [← hn]; scalar_tac
      exact ⟨by rw [hal, heq], har', fun t ht => hav' t (by rw [heq]; exact ht)⟩
  · exact ⟨hi, hlen, har, hav⟩

/-- `lo`, `Δ` and `eq[y]` for the base path. -/
def loK (w : alloc.vec.Vec cpoly.field.Fp) (y : ℕ) : ZMod q := coeffK w (2 * y)
def dK (w : alloc.vec.Vec cpoly.field.Fp) (y : ℕ) : ZMod q := coeffK w (2 * y + 1) - loK w y

theorem pair_loop_base_spec (w : alloc.vec.Vec cpoly.field.Fp)
    (eq : alloc.vec.Vec cpoly.field.Ext4) (half : Std.Usize)
    (acc : alloc.vec.Vec cpoly.field.Ext4) (y : Std.Usize)
    (hhalf : half.val = eq.val.length) (hwl : w.val.length = 2 * eq.val.length)
    (hwr : ∀ a ∈ w.val, Red a) (her : VecReduced eq)
    (hy : y.val ≤ half.val) (halen : acc.val.length = 32) (har : VecReduced acc)
    (hav : ∀ t, t < 32 → toExt (acc.val.getD t cpoly.field.Ext4.ZERO)
      = ∑ y' ∈ Finset.range y.val,
          phiF (shiftCoeffK (loK w y') (dK w y') t) * eqF eq y') :
    sumcheck.round_poly_zero_base_loop1 w eq half acc y
      ⦃ z => z.val.length = 32 ∧ VecReduced z ∧
          ∀ t, t < 32 → toExt (z.val.getD t cpoly.field.Ext4.ZERO)
            = ∑ y' ∈ Finset.range half.val,
                phiF (shiftCoeffK (loK w y') (dK w y') t) * eqF eq y' ⦄ := by
  rw [sumcheck.round_poly_zero_base_loop1]
  apply loop.spec_decr_nat (fun r => half.val - r.2.val)
    (fun r => r.2.val ≤ half.val ∧ r.1.val.length = 32 ∧ VecReduced r.1
      ∧ ∀ t, t < 32 → toExt (r.1.val.getD t cpoly.field.Ext4.ZERO)
          = ∑ y' ∈ Finset.range r.2.val,
              phiF (shiftCoeffK (loK w y') (dK w y') t) * eqF eq y')
  · rintro ⟨a, yy⟩ ⟨hyy, hal, har', hav'⟩
    dsimp only at hyy hal har' hav'
    simp only [sumcheck.round_poly_zero_base_loop1.body]
    by_cases hlt : yy < half
    · rw [if_pos hlt]
      have hylt : yy.val < eq.val.length := by rw [← hhalf]; scalar_tac
      have hb0 : 2 * yy.val < w.val.length := by rw [hwl]; omega
      have hb1 : 2 * yy.val + 1 < w.val.length := by rw [hwl]; omega
      step as ⟨i, hi⟩
      step as ⟨lo, hlo⟩
      have hlob : i.val < w.val.length := by rw [hi]; exact hb0
      have hRlo : Red lo := hwr _ (by rw [hlo]; exact List.getElem_mem hlob)
      have hlov : toK lo = loK w yy.val := by
        rw [hlo, loK, ← hi, ← coeffK_of_lt hlob]
      step as ⟨i1, hi1⟩
      step as ⟨hiw, hhiw⟩
      have hhib : i1.val < w.val.length := by rw [hi1, hi]; exact hb1
      have hRhi : Red hiw := hwr _ (by rw [hhiw]; exact List.getElem_mem hhib)
      have hhiv : toK hiw = coeffK w (2 * yy.val + 1) := by
        rw [hhiw, ← coeffK_of_lt hhib, hi1, hi]
      step with shift_powers_base_spec lo hRlo as ⟨lop, hlopl, hlopr, hlopv⟩
      step with HachiEquiv.Field.fp_sub_spec hiw lo hRhi hRlo as ⟨dd, hRdd, hddv⟩
      have hddval : toK dd = dK w yy.val := by rw [hddv, hhiv, hlov, dK]
      step as ⟨ev, hev⟩
      have hRev : Reduced ev := her _ (by rw [hev]; exact List.getElem_mem hylt)
      have hevv : toExt ev = eqF eq yy.val := by
        rw [hev, eqF, ← List.getD_eq_getElem (l := eq.val) (d := cpoly.field.Ext4.ZERO) hylt]
      step with shift_accum_base_spec a lop dd ev (loK w yy.val)
        (fun t => ∑ y' ∈ Finset.range yy.val,
          phiF (shiftCoeffK (loK w y') (dK w y') t) * eqF eq y')
        hlopl hlopr (by intro t ht; rw [hlopv t ht, hlov]) hRdd hRev hal har' hav'
        as ⟨a1, ha1l, ha1r, ha1v⟩
      step as ⟨yy1, hyy1⟩
      refine ⟨by omega, ha1l, ha1r, ?_, by omega⟩
      intro t ht
      rw [ha1v t ht, hyy1, Finset.sum_range_succ, hevv, hddval]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : yy.val = half.val := by scalar_tac
      exact ⟨hal, har', fun t ht => by rw [hav' t ht, heq]⟩
  · exact ⟨hy, halen, har, hav⟩


end HachiEquiv.AuxShift
