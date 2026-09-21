/-
The **ring layer**, at the level of coefficients: the extracted `hachi.ring.*`
operations shown total, length-preserving, and coefficientwise equal to arithmetic
in `ZMod q`.

## Why this file stops short of `Rq Φ`

The equivalence this repository is about is with ArkLib's `CyclotomicModulus.Rq Φ`,
and that statement needs one more step than what is here. This file proves the part
that is *work*: the loop invariants, the totality of every `u64` intermediate, and
the coefficient semantics of each operation. Lifting a coefficient statement to an
element of `Rq Φ` is then bookkeeping through ArkLib's `ofFinCoeff_coeff` and
`Subtype.ext`, and it lives in `lean/RqBridge.lean` with the rest of the
`Rq Φ`-level statements.

The split is deliberate: this half is checkable against a much smaller import
surface (`Generated` and `Field`, no ArkLib at all), which is what lets it be
audited now rather than when the whole `Rq Φ` bridge is finished.

## The representation

A coefficient vector is well-formed (`Wf`) when it has exactly `N = 2^α` entries
and every entry is a reduced word. `coeffK v k` reads coefficient `k` as an element
of `ZMod q`, and is `0` past the end — which matches both the Rust (`Rq::coeff`
returns `Fp::ZERO` there) and ArkLib (`coeff_eq_zero_of_natDegree_le`), so the
statements below can be quantified over all `k` rather than only over `k < N`.
-/
import Generated
import Field
import NttProduct

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi
open HachiEquiv.Field

namespace HachiEquiv.Ring

/-- The ring degree `N = 2^α = 1024`: the number of coefficients in one element. -/
abbrev N : ℕ := 1024

/-- The extracted `RING_DEGREE` is `N`. `params.RING_DEGREE` is `irreducible`, so
this is the way in, and it is what every loop bound below is rewritten with. -/
@[simp, scalar_tac_simps]
theorem params_RING_DEGREE_val : (params.RING_DEGREE).val = N := by
  simp only [params.RING_DEGREE]; decide

/-- Coefficient `k` of a vector, as a field element; `0` past the end. -/
def coeffK (v : alloc.vec.Vec cpoly.field.Fp) (k : ℕ) : ZMod q :=
  toK (v.val.getD k cpoly.field.Fp.ZERO)

/-- Representation invariant: exactly `N` entries, all reduced. -/
def Wf (v : ring.Rq) : Prop := v.val.length = N ∧ ∀ u ∈ v.val, Red u

theorem coeffK_of_ge {v : alloc.vec.Vec cpoly.field.Fp} {k : ℕ} (hk : v.val.length ≤ k) :
    coeffK v k = 0 := by
  unfold coeffK
  rw [List.getD_eq_default _ _ hk, toK_zero]

theorem coeffK_of_lt {v : alloc.vec.Vec cpoly.field.Fp} {k : ℕ} (hk : k < v.val.length) :
    coeffK v k = toK v.val[k] := by
  unfold coeffK
  rw [List.getD_eq_getElem _ _ hk]

/-- The entries of a well-formed vector are reduced, in the `getElem` form the loop
proofs need. -/
theorem Red_getElem {v : ring.Rq} (hv : ∀ u ∈ v.val, Red u) {k : ℕ}
    (hk : k < v.val.length) : Red v.val[k] :=
  hv _ (List.getElem_mem hk)

/-! ## `Rq::zero` -/

theorem zero_loop_spec (n : Std.Usize) (out : alloc.vec.Vec cpoly.field.Fp) (i : Std.Usize)
    (hi : i.val ≤ n.val) (hout : out.val = List.replicate i.val cpoly.field.Fp.ZERO) :
    ring.Rq.zero_loop n out i
      ⦃ z => z.val = List.replicate n.val cpoly.field.Fp.ZERO ⦄ := by
  rw [ring.Rq.zero_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val = List.replicate s.2.val cpoly.field.Fp.ZERO)
  · rintro ⟨o1, i1⟩ ⟨hi1, ho1⟩
    -- The invariant arrives phrased in projections of the state pair; reduce them
    -- before anything tries to rewrite with it.
    dsimp only at hi1 ho1
    simp only [ring.Rq.zero_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hlen : o1.val.length = i1.val := by rw [ho1, List.length_replicate]
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [ho2, hi2, ho1, List.replicate_succ']
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      show o1.val = List.replicate n.val cpoly.field.Fp.ZERO
      have heq : i1.val = n.val := by scalar_tac
      rw [ho1, heq]
  · exact ⟨hi, hout⟩

/-- `Rq::zero` — the all-zero coefficient vector: well-formed, and every
coefficient is `0`. -/
theorem zero_spec : ring.Rq.zero ⦃ z => Wf z ∧ ∀ k, coeffK z k = 0 ⦄ := by
  rw [ring.Rq.zero]
  simp only [bind_ok_id]
  apply spec_mono (zero_loop_spec params.RING_DEGREE (alloc.vec.Vec.new cpoly.field.Fp)
    0#usize (by simp) (by simp))
  intro z hz
  -- Every entry read out of the result is `Fp::ZERO`, whether the index is in
  -- range or not: in range because the vector is a `replicate`, out of range
  -- because `getD`'s default is the same value.
  have hread : ∀ k, z.val.getD k cpoly.field.Fp.ZERO = cpoly.field.Fp.ZERO := by
    intro k
    rw [hz]
    by_cases hk : k < (List.replicate ((params.RING_DEGREE).val) cpoly.field.Fp.ZERO).length
    · rw [List.getD_eq_getElem _ _ hk, List.getElem_replicate]
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hk)]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hz, List.length_replicate, params_RING_DEGREE_val]
  · intro u hu
    rw [hz] at hu
    rw [List.eq_of_mem_replicate hu]
    exact Red_zero
  · intro k
    unfold coeffK
    rw [hread k]
    exact toK_zero

/-! ## Reading a coefficient out of a pushed vector

Every operation below is a `push` loop, so every one of them needs the same two
facts about `out.val ++ [x]`: the coefficients below the old length are unchanged,
and the coefficient at the old length is the pushed word. -/

theorem coeffK_append_lt {v : alloc.vec.Vec cpoly.field.Fp} {x : cpoly.field.Fp}
    {w : alloc.vec.Vec cpoly.field.Fp} (hw : w.val = v.val ++ [x])
    {k : ℕ} (hk : k < v.val.length) : coeffK w k = coeffK v k := by
  unfold coeffK
  rw [hw, List.getD_eq_getElem _ _ (by simp [List.length_append]; omega),
    List.getD_eq_getElem _ _ hk, List.getElem_append_left hk]

theorem coeffK_append_eq {v : alloc.vec.Vec cpoly.field.Fp} {x : cpoly.field.Fp}
    {w : alloc.vec.Vec cpoly.field.Fp} (hw : w.val = v.val ++ [x]) :
    coeffK w v.val.length = toK x := by
  unfold coeffK
  rw [hw, List.getD_eq_getElem _ _ (by simp [List.length_append]),
    List.getElem_append_right (Nat.le_refl _)]
  simp

/-! ## `Rq::add`

The loop's state is `(rhs, out, i)` -- Aeneas threads the borrowed `rhs` through it
-- so the invariant has to say that the first component never moves, as well as the
two facts about `out` that matter: its length is the counter, and its coefficients
so far are the pointwise sums. -/

theorem add_loop_spec (v : alloc.vec.Vec cpoly.field.Fp) (rhs : ring.Rq) (n : Std.Usize)
    (out : alloc.vec.Vec cpoly.field.Fp) (i : Std.Usize)
    (hnv : n.val ≤ v.val.length) (hnr : n.val ≤ rhs.val.length)
    (hv : ∀ u ∈ v.val, Red u) (hr : ∀ u ∈ rhs.val, Red u)
    (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hred : ∀ u ∈ out.val, Red u)
    (hcoef : ∀ k, k < i.val → coeffK out k = coeffK v k + coeffK rhs k) :
    ring.Rq.add_loop v rhs n out i
      ⦃ z => z.val.length = n.val ∧ (∀ u ∈ z.val, Red u) ∧
        ∀ k, k < n.val → coeffK z k = coeffK v k + coeffK rhs k ⦄ := by
  rw [ring.Rq.add_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.2.val)
    (fun s => s.1 = rhs ∧ s.2.2.val ≤ n.val ∧ s.2.1.val.length = s.2.2.val ∧
      (∀ u ∈ s.2.1.val, Red u) ∧
      ∀ k, k < s.2.2.val → coeffK s.2.1 k = coeffK v k + coeffK rhs k)
  · rintro ⟨r1, o1, i1⟩ ⟨hr1, hi1, hlen1, hred1, hcoef1⟩
    dsimp only at hr1 hi1 hlen1 hred1 hcoef1
    subst hr1
    simp only [ring.Rq.add_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hiv : i1.val < v.val.length := by scalar_tac
      have hir : i1.val < r1.val.length := by scalar_tac
      step as ⟨a, ha⟩
      have hRa : Red a := ha ▸ hv _ (List.getElem_mem hiv)
      step as ⟨b, hb⟩
      have hRb : Red b := hb ▸ hr _ (List.getElem_mem hir)
      step as ⟨c, hRc, hc⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      -- The invariant's `s.1 = rhs` conjunct is already discharged for the new
      -- state (it is `r1 = r1` after the `subst`), so the goal is the remaining
      -- four components plus the measure.
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hred1 u h
        · rw [List.mem_singleton.mp h]; exact hRc
      · intro k hk
        rw [hi2] at hk
        rcases Nat.lt_or_ge k i1.val with hklt | hkge
        · rw [coeffK_append_lt ho2 (by omega), hcoef1 k hklt]
        · have hkeq : k = o1.val.length := by omega
          rw [hkeq, coeffK_append_eq ho2, hc, hlen1, coeffK_of_lt hiv,
            coeffK_of_lt hir, ha, hb]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hred1, by rw [← heq]; exact hcoef1⟩
  · exact ⟨rfl, hi, hlen, hred, hcoef⟩

/-- `Rq::add` — coefficientwise addition, total, length-preserving.

The `Wf` hypotheses are what make it total: they give `Red` on every word the loop
reads, which is what discharges the `u64` no-overflow obligation inside
`Fp::add`. -/
theorem add_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b) :
    ring.Rq.add a b
      ⦃ z => Wf z ∧ ∀ k, k < N → coeffK z k = coeffK a k + coeffK b k ⦄ := by
  obtain ⟨halen, hared⟩ := ha
  obtain ⟨hblen, hbred⟩ := hb
  rw [ring.Rq.add]
  simp only [bind_ok_id]
  apply spec_mono (add_loop_spec a b (alloc.vec.Vec.len a)
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize
    (by simp) (by simp [halen, hblen]) hared hbred (by simp)
    (by simp) (by intro u hu; simp at hu) (by intro k hk; simp at hk))
  rintro z ⟨hzlen, hzred, hzcoef⟩
  have hn : (alloc.vec.Vec.len a).val = N := by simp [halen]
  refine ⟨⟨?_, hzred⟩, ?_⟩
  · rw [hzlen, hn]
  · intro k hk
    exact hzcoef k (by rw [hn]; exact hk)

/-! ## `Rq::sub`

The same loop as `add` with `Fp::sub` in place of `Fp::add`; the state is `(rhs,
out, i)` for the same reason. -/

theorem sub_loop_spec (v : alloc.vec.Vec cpoly.field.Fp) (rhs : ring.Rq) (n : Std.Usize)
    (out : alloc.vec.Vec cpoly.field.Fp) (i : Std.Usize)
    (hnv : n.val ≤ v.val.length) (hnr : n.val ≤ rhs.val.length)
    (hv : ∀ u ∈ v.val, Red u) (hr : ∀ u ∈ rhs.val, Red u)
    (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hred : ∀ u ∈ out.val, Red u)
    (hcoef : ∀ k, k < i.val → coeffK out k = coeffK v k - coeffK rhs k) :
    ring.Rq.sub_loop v rhs n out i
      ⦃ z => z.val.length = n.val ∧ (∀ u ∈ z.val, Red u) ∧
        ∀ k, k < n.val → coeffK z k = coeffK v k - coeffK rhs k ⦄ := by
  rw [ring.Rq.sub_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.2.val)
    (fun s => s.1 = rhs ∧ s.2.2.val ≤ n.val ∧ s.2.1.val.length = s.2.2.val ∧
      (∀ u ∈ s.2.1.val, Red u) ∧
      ∀ k, k < s.2.2.val → coeffK s.2.1 k = coeffK v k - coeffK rhs k)
  · rintro ⟨r1, o1, i1⟩ ⟨hr1, hi1, hlen1, hred1, hcoef1⟩
    dsimp only at hr1 hi1 hlen1 hred1 hcoef1
    subst hr1
    simp only [ring.Rq.sub_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hiv : i1.val < v.val.length := by scalar_tac
      have hir : i1.val < r1.val.length := by scalar_tac
      step as ⟨a, ha⟩
      have hRa : Red a := ha ▸ hv _ (List.getElem_mem hiv)
      step as ⟨b, hb⟩
      have hRb : Red b := hb ▸ hr _ (List.getElem_mem hir)
      step as ⟨c, hRc, hc⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hred1 u h
        · rw [List.mem_singleton.mp h]; exact hRc
      · intro k hk
        rw [hi2] at hk
        rcases Nat.lt_or_ge k i1.val with hklt | hkge
        · rw [coeffK_append_lt ho2 (by omega), hcoef1 k hklt]
        · have hkeq : k = o1.val.length := by omega
          rw [hkeq, coeffK_append_eq ho2, hc, hlen1, coeffK_of_lt hiv,
            coeffK_of_lt hir, ha, hb]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hred1, by rw [← heq]; exact hcoef1⟩
  · exact ⟨rfl, hi, hlen, hred, hcoef⟩

/-- `Rq::sub` — coefficientwise subtraction, total, length-preserving. -/
theorem sub_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b) :
    ring.Rq.sub a b
      ⦃ z => Wf z ∧ ∀ k, k < N → coeffK z k = coeffK a k - coeffK b k ⦄ := by
  obtain ⟨halen, hared⟩ := ha
  obtain ⟨hblen, hbred⟩ := hb
  rw [ring.Rq.sub]
  simp only [bind_ok_id]
  apply spec_mono (sub_loop_spec a b (alloc.vec.Vec.len a)
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize
    (by simp) (by simp [halen, hblen]) hared hbred (by simp)
    (by simp) (by intro u hu; simp at hu) (by intro k hk; simp at hk))
  rintro z ⟨hzlen, hzred, hzcoef⟩
  have hn : (alloc.vec.Vec.len a).val = N := by simp [halen]
  refine ⟨⟨?_, hzred⟩, ?_⟩
  · rw [hzlen, hn]
  · intro k hk
    exact hzcoef k (by rw [hn]; exact hk)

/-! ## `Rq::neg` and `Rq::scalar_mul`

One input rather than two, so the loop state is just `(out, i)`. -/

theorem neg_loop_spec (v : alloc.vec.Vec cpoly.field.Fp) (n : Std.Usize)
    (out : alloc.vec.Vec cpoly.field.Fp) (i : Std.Usize)
    (hnv : n.val ≤ v.val.length) (hv : ∀ u ∈ v.val, Red u)
    (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hred : ∀ u ∈ out.val, Red u)
    (hcoef : ∀ k, k < i.val → coeffK out k = - coeffK v k) :
    ring.Rq.neg_loop v n out i
      ⦃ z => z.val.length = n.val ∧ (∀ u ∈ z.val, Red u) ∧
        ∀ k, k < n.val → coeffK z k = - coeffK v k ⦄ := by
  rw [ring.Rq.neg_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧
      (∀ u ∈ s.1.val, Red u) ∧
      ∀ k, k < s.2.val → coeffK s.1 k = - coeffK v k)
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hred1, hcoef1⟩
    dsimp only at hi1 hlen1 hred1 hcoef1
    simp only [ring.Rq.neg_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hiv : i1.val < v.val.length := by scalar_tac
      step as ⟨a, ha⟩
      have hRa : Red a := ha ▸ hv _ (List.getElem_mem hiv)
      step as ⟨c, hRc, hc⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hred1 u h
        · rw [List.mem_singleton.mp h]; exact hRc
      · intro k hk
        rw [hi2] at hk
        rcases Nat.lt_or_ge k i1.val with hklt | hkge
        · rw [coeffK_append_lt ho2 (by omega), hcoef1 k hklt]
        · have hkeq : k = o1.val.length := by omega
          rw [hkeq, coeffK_append_eq ho2, hc, hlen1, coeffK_of_lt hiv, ha]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hred1, by rw [← heq]; exact hcoef1⟩
  · exact ⟨hi, hlen, hred, hcoef⟩

/-- `Rq::neg` — coefficientwise negation. -/
theorem neg_spec (a : ring.Rq) (ha : Wf a) :
    ring.Rq.neg a ⦃ z => Wf z ∧ ∀ k, k < N → coeffK z k = - coeffK a k ⦄ := by
  obtain ⟨halen, hared⟩ := ha
  rw [ring.Rq.neg]
  simp only [bind_ok_id]
  apply spec_mono (neg_loop_spec a (alloc.vec.Vec.len a)
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize
    (by simp) hared (by simp) (by simp) (by intro u hu; simp at hu)
    (by intro k hk; simp at hk))
  rintro z ⟨hzlen, hzred, hzcoef⟩
  have hn : (alloc.vec.Vec.len a).val = N := by simp [halen]
  refine ⟨⟨?_, hzred⟩, ?_⟩
  · rw [hzlen, hn]
  · intro k hk
    exact hzcoef k (by rw [hn]; exact hk)

theorem scalar_mul_loop_spec (v : alloc.vec.Vec cpoly.field.Fp) (c : cpoly.field.Fp)
    (n : Std.Usize) (out : alloc.vec.Vec cpoly.field.Fp) (i : Std.Usize)
    (hnv : n.val ≤ v.val.length) (hv : ∀ u ∈ v.val, Red u) (hc : Red c)
    (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hred : ∀ u ∈ out.val, Red u)
    (hcoef : ∀ k, k < i.val → coeffK out k = toK c * coeffK v k) :
    ring.Rq.scalar_mul_loop v c n out i
      ⦃ z => z.val.length = n.val ∧ (∀ u ∈ z.val, Red u) ∧
        ∀ k, k < n.val → coeffK z k = toK c * coeffK v k ⦄ := by
  rw [ring.Rq.scalar_mul_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧
      (∀ u ∈ s.1.val, Red u) ∧
      ∀ k, k < s.2.val → coeffK s.1 k = toK c * coeffK v k)
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hred1, hcoef1⟩
    dsimp only at hi1 hlen1 hred1 hcoef1
    simp only [ring.Rq.scalar_mul_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hiv : i1.val < v.val.length := by scalar_tac
      step as ⟨a, ha⟩
      have hRa : Red a := ha ▸ hv _ (List.getElem_mem hiv)
      step as ⟨d, hRd, hd⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hred1 u h
        · rw [List.mem_singleton.mp h]; exact hRd
      · intro k hk
        rw [hi2] at hk
        rcases Nat.lt_or_ge k i1.val with hklt | hkge
        · rw [coeffK_append_lt ho2 (by omega), hcoef1 k hklt]
        · have hkeq : k = o1.val.length := by omega
          rw [hkeq, coeffK_append_eq ho2, hd, hlen1, coeffK_of_lt hiv, ha]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hred1, by rw [← heq]; exact hcoef1⟩
  · exact ⟨hi, hlen, hred, hcoef⟩

/-- `Rq::scalar_mul` — coefficientwise scaling by a field element.

This is the operation the gadget product is built from: multiplication by the ring
constant `C(bᵉ)`, whose coefficientwise action is ArkLib's `constRq_mul_coeff`. -/
theorem scalar_mul_spec (a : ring.Rq) (c : cpoly.field.Fp) (ha : Wf a) (hc : Red c) :
    ring.Rq.scalar_mul a c
      ⦃ z => Wf z ∧ ∀ k, k < N → coeffK z k = toK c * coeffK a k ⦄ := by
  obtain ⟨halen, hared⟩ := ha
  rw [ring.Rq.scalar_mul]
  simp only [bind_ok_id]
  apply spec_mono (scalar_mul_loop_spec a c (alloc.vec.Vec.len a)
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize
    (by simp) hared hc (by simp) (by simp) (by intro u hu; simp at hu)
    (by intro k hk; simp at hk))
  rintro z ⟨hzlen, hzred, hzcoef⟩
  have hn : (alloc.vec.Vec.len a).val = N := by simp [halen]
  refine ⟨⟨?_, hzred⟩, ?_⟩
  · rw [hzlen, hn]
  · intro k hk
    exact hzcoef k (by rw [hn]; exact hk)


/-- `Fp::to_u64` is the identity on the representation (`Fp := U64`); no `@[step]`
lemma is registered for it, so a loop body that reads a word needs it spelled
out. Public since 2026-09-16: `LiftProver.lean`'s `long_mul` needs the same fact,
and one shared lemma beats two copies. -/
theorem to_u64_id (f : cpoly.field.Fp) :
    cpoly.field.Fp.to_u64 f ⦃ x => x = f ⦄ := by
  rw [cpoly.field.Fp.to_u64, WP.spec_ok]

/-! ## `Rq::mul`

The negacyclic product, and the only operation here that walks the *output*
coefficient rather than the input pair. Term `aᵢbⱼ` belongs to slot `k` with a
`+` when `i + j = k` and with a `−` when `i + j = N + k`, because `X^N ≡ -1`;
re-indexed by the output, that is `j = k − i` for `i ≤ k` and `j = N + k − i`
for `i > k`, which is the `if i <= k` of the Rust. `negConv` is the closed form
the completed pass reaches -- written with `Finset.antidiagonal` because that is
the shape `Polynomial.coeff_mul` produces, which is what the `Rq Φ` bridge needs.

Stage 6 candidate Q made the reduction lazy: the two antidiagonals are summed in
`u128` **without** reducing, and `% q` is paid once per slot rather than on every
one of the `N²` products (each `Fp` operation reduces). So the proof has a shape
the earlier schoolbook did not need -- the accumulators are *naturals*, `posSum`
and `negSum`, and the bridge to `ZMod q` is `Nat.cast` being a ring hom, applied
once at the end. Totality needs two things: every word read is below `q` (the
`Red` invariant), which bounds a term by `q * q`; and `N` such terms fit a
`u128`, which `accBound` is. -/

/-- Coefficient `k` of the negacyclic product: the `k`-th antidiagonal of the raw
product minus its `(N + k)`-th, which is `(a * b) mod (X^N + 1)` written out. -/
def negConv (a b : ring.Rq) (k : ℕ) : ZMod q :=
  (∑ p ∈ Finset.antidiagonal k, coeffK a p.1 * coeffK b p.2)
    - ∑ p ∈ Finset.antidiagonal (N + k), coeffK a p.1 * coeffK b p.2

/-- Overwriting one entry with a reduced word keeps every entry reduced. -/
theorem Red_set {v : alloc.vec.Vec cpoly.field.Fp} {t : Std.Usize} {x : cpoly.field.Fp}
    (hv : ∀ u ∈ v.val, Red u) (hx : Red x) : ∀ u ∈ (v.set t x).val, Red u := by
  intro u hu
  rw [alloc.vec.Vec.set_val_eq] at hu
  rcases List.mem_or_eq_of_mem_set hu with h | h
  · exact hv u h
  · rw [h]; exact hx

/-! ### The accumulators, as naturals

`wordN` is `coeffK` before the cast, and the two sums are exactly what the inner
loop holds after `m` steps. Keeping them in `ℕ` is the point: the Rust does not
reduce until the slot is finished, so neither does the invariant. -/

/-- The word at index `t`, as a natural number -- `coeffK` before the cast. -/
def wordN (v : alloc.vec.Vec cpoly.field.Fp) (t : ℕ) : ℕ :=
  (v.val.getD t cpoly.field.Fp.ZERO).val

theorem coeffK_eq_cast_wordN (v : alloc.vec.Vec cpoly.field.Fp) (t : ℕ) :
    coeffK v t = ((wordN v t : ℕ) : ZMod q) := rfl

/-- Every word a well-formed `Rq` can be read at is below `q`: in range by the
`Red` invariant, out of range because the default is `Fp.ZERO`. -/
theorem wordN_lt {v : ring.Rq} (hv : Wf v) (t : ℕ) : wordN v t < q := by
  unfold wordN
  by_cases ht : t < v.val.length
  · rw [List.getD_eq_getElem _ _ ht]
    exact hv.2 _ (List.getElem_mem ht)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Red_zero

/-- The `+` accumulator after `m` inner steps of slot `k`. -/
def posSum (a b : ring.Rq) (k m : ℕ) : ℕ :=
  ∑ t ∈ Finset.range m, if t ≤ k then wordN a t * wordN b (k - t) else 0

/-- The `−` accumulator after `m` inner steps of slot `k`. -/
def negSum (a b : ring.Rq) (k m : ℕ) : ℕ :=
  ∑ t ∈ Finset.range m, if t ≤ k then 0 else wordN a t * wordN b (N + k - t)

/-- Each term is below `q * q`, so `m` of them are below `m * (q * q)`. -/
theorem posSum_le {a b : ring.Rq} (ha : Wf a) (hb : Wf b) (k m : ℕ) :
    posSum a b k m ≤ m * (q * q) := by
  unfold posSum
  calc ∑ t ∈ Finset.range m, (if t ≤ k then wordN a t * wordN b (k - t) else 0)
      ≤ ∑ _t ∈ Finset.range m, q * q := by
        refine Finset.sum_le_sum (fun t _ => ?_)
        by_cases h : t ≤ k
        · rw [if_pos h]
          exact Nat.mul_le_mul (Nat.le_of_lt (wordN_lt ha t)) (Nat.le_of_lt (wordN_lt hb _))
        · rw [if_neg h]; exact Nat.zero_le _
    _ = m * (q * q) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem negSum_le {a b : ring.Rq} (ha : Wf a) (hb : Wf b) (k m : ℕ) :
    negSum a b k m ≤ m * (q * q) := by
  unfold negSum
  calc ∑ t ∈ Finset.range m, (if t ≤ k then 0 else wordN a t * wordN b (N + k - t))
      ≤ ∑ _t ∈ Finset.range m, q * q := by
        refine Finset.sum_le_sum (fun t _ => ?_)
        by_cases h : t ≤ k
        · rw [if_pos h]; exact Nat.zero_le _
        · rw [if_neg h]
          exact Nat.mul_le_mul (Nat.le_of_lt (wordN_lt ha t)) (Nat.le_of_lt (wordN_lt hb _))
    _ = m * (q * q) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The ceiling that makes a delayed reduction sound: `N` terms of at most
`q * q` each, against `u128`. `1024 · (2^32 − 99)² < 2^74`, so there are 54 bits
to spare -- and a `u64` accumulator would already overflow on one term.

`Rq::mul` no longer needs it (its accumulation happens in `ntt`, in `ZMod p`),
but `LiftProver.long_mul` does, and it opens this namespace to get it. It stays
here because this is where the two operands' bound lives. -/
theorem accBound : N * (q * q) < Std.U128.max := by
  simp only [N, q, Std.U128.max, Std.U128.numBits]
  norm_num

/-! ### From the natural sums to `negConv` -/

theorem posSum_cast {a b : ring.Rq} (_ha : Wf a) (_hb : Wf b) {k : ℕ} (hk : k < N) :
    ((posSum a b k N : ℕ) : ZMod q)
      = ∑ p ∈ Finset.antidiagonal k, coeffK a p.1 * coeffK b p.2 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeffK a i * coeffK b j) k]
  unfold posSum
  push_cast
  rw [← Finset.sum_subset (s₁ := Finset.range (k + 1)) (s₂ := Finset.range N)
    (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
    (by
      intro x _ hx
      simp only [Finset.mem_range] at hx
      rw [if_neg (by omega)])]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  simp only [Finset.mem_range] at ht
  rw [if_pos (by omega), coeffK_eq_cast_wordN, coeffK_eq_cast_wordN]

theorem negSum_cast {a b : ring.Rq} (ha : Wf a) (hb : Wf b) {k : ℕ} (hk : k < N) :
    ((negSum a b k N : ℕ) : ZMod q)
      = ∑ p ∈ Finset.antidiagonal (N + k), coeffK a p.1 * coeffK b p.2 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeffK a i * coeffK b j) (N + k)]
  -- Outside `k < t < N` the summand vanishes: `coeffK a` above `N`, `coeffK b`
  -- because `N + k - t ≥ N` once `t ≤ k`.
  have hzero : ∀ t, N ≤ t → coeffK a t * coeffK b (N + k - t) = 0 := by
    intro t ht
    rw [coeffK_of_ge (by rw [ha.1]; exact ht), zero_mul]
  have hzero' : ∀ t, t ≤ k → coeffK a t * coeffK b (N + k - t) = 0 := by
    intro t ht
    rw [coeffK_of_ge (v := b) (k := N + k - t) (by rw [hb.1]; omega), mul_zero]
  rw [Finset.sum_congr rfl (g := fun t =>
        if t ≤ k then 0 else coeffK a t * coeffK b (N + k - t))
      (fun t ht => by
        simp only [Finset.mem_range] at ht
        by_cases h : t ≤ k
        · rw [if_pos h, hzero' t h]
        · rw [if_neg h])]
  unfold negSum
  push_cast
  rw [← Finset.sum_subset (s₁ := Finset.range N) (s₂ := Finset.range (N + k + 1))
    (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
    (by
      intro x _ hx
      simp only [Finset.mem_range] at hx
      rw [if_neg (by omega), hzero x (by omega)])]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  by_cases h : t ≤ k
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, coeffK_eq_cast_wordN, coeffK_eq_cast_wordN]

/-- The closed form the finished slot reaches: reducing the two natural sums once
each and subtracting in `Fp` is `negConv`. -/
theorem negConv_eq_sums {a b : ring.Rq} (ha : Wf a) (hb : Wf b) {k : ℕ} (hk : k < N) :
    ((posSum a b k N : ℕ) : ZMod q) - ((negSum a b k N : ℕ) : ZMod q) = negConv a b k := by
  rw [posSum_cast ha hb hk, negSum_cast ha hb hk, negConv]

/-- Reading a word in range. -/
theorem wordN_of_lt {v : alloc.vec.Vec cpoly.field.Fp} {t : ℕ} (ht : t < v.val.length) :
    wordN v t = (v.val[t]).val := by
  unfold wordN; rw [List.getD_eq_getElem _ _ ht]

/-! ### The three loops, and the bridge to `NttProduct`

`Rq::mul` is three passes and one call: read `self`'s words, read `rhs`'s words,
hand both to `ntt::negconv_mod_q`, and wrap what comes back as `Fp`. So the loop
proofs here are three push loops of exactly the shape `add_loop_spec` has, and
the content of the multiplication theorem lives one layer down, in
`NttProduct.negconv_mod_q_spec`.

What joins the two layers is that `NttProduct`'s `posW`/`negW` -- the same two
antidiagonals, over a `u64` buffer instead of over an `Rq` -- agree with
`posSum`/`negSum` once the extraction loops have copied the words. After that
`negConv_eq_sums` closes the proof exactly as it did for the schoolbook, which
is why the headline statement below is the one it always was.

The offset is invisible here. `NttProduct.BOUND` is `N · q²`, a multiple of `q`,
so `negconv_mod_q` hands back the coefficient itself and there is no correction
term to carry through `coeffK`. -/

/-- Reading below the join, and reading the appended entry. `HachiEquiv.Scheme` has
the same two lemmas, but `Scheme` is *downstream* of this file (via `RqBridge`), so
they cannot be shared in this direction; the names are primed to keep the two from
shadowing each other where both are in scope. -/
private theorem getD_append_lt' {α : Type} (l : List α) (x d : α) {j : ℕ}
    (hj : j < l.length) : (l ++ [x]).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hj,
    List.getElem_append_left hj]

private theorem getD_append_eq' {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
  simp

/-- `mul`'s first loop: `self`'s canonical words, copied into a `u64` buffer.
The `Red` half of `Wf` is what makes every word below `q`, which is
`negconv_mod_q`'s precondition. -/
theorem mul_loop0_spec (a : ring.Rq) (n : Std.Usize) (aw : alloc.vec.Vec Std.U64)
    (i : Std.Usize) (ha : Wf a) (hn : n.val = N) (hi : i.val ≤ n.val)
    (hlen : aw.val.length = i.val) (hred : ∀ u ∈ aw.val, u.val < q)
    (hval : ∀ t, t < i.val → NttStage.wordAt aw t = wordN a t) :
    ring.Rq.mul_loop0 a n aw i
      ⦃ z => NttStage.Canon q z ∧ ∀ t, t < N → NttStage.wordAt z t = wordN a t ⦄ := by
  rw [ring.Rq.mul_loop0]
  apply loop.spec_decr_nat (fun s => n.val - s.2.2.val)
    (fun s => s.1 = a ∧ s.2.2.val ≤ n.val ∧ s.2.1.val.length = s.2.2.val ∧
      (∀ u ∈ s.2.1.val, u.val < q) ∧
      ∀ t, t < s.2.2.val → NttStage.wordAt s.2.1 t = wordN a t)
  · rintro ⟨s1, o1, i1⟩ ⟨h1, h2, h3, h4, h5⟩
    dsimp only at h1 h2 h3 h4 h5
    subst h1
    simp only [ring.Rq.mul_loop0.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hia : i1.val < s1.val.length := by rw [ha.1, ← hn]; scalar_tac
      step as ⟨f, hf⟩
      step with to_u64_id f as ⟨w, hw⟩
      have hRw : w.val < q := by rw [hw, hf]; exact ha.2 _ (List.getElem_mem hia)
      have hwv : w.val = wordN s1 i1.val := by rw [hw, hf, wordN_of_lt hia]
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, h3]; simp
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact h4 u h
        · rw [List.mem_singleton.mp h]; exact hRw
      · intro t ht
        rw [hi2] at ht
        simp only [NttStage.wordAt] at h5 ⊢
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt' _ _ _ (by omega)]
          exact h5 t htlt
        · have hteq : t = o1.val.length := by omega
          rw [hteq, ho2, getD_append_eq', h3, hwv]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      refine ⟨⟨?_, h4⟩, ?_⟩
      · rw [h3, heq, hn]
      · intro t ht
        exact h5 t (by omega)
  · exact ⟨rfl, hi, hlen, hred, hval⟩

/-- `mul`'s second loop: the same for `rhs`. Separate in the extraction because
it is a separate Rust loop, and separate here for the same reason. -/
theorem mul_loop1_spec (b : ring.Rq) (n : Std.Usize) (bw : alloc.vec.Vec Std.U64)
    (j : Std.Usize) (hb : Wf b) (hn : n.val = N) (hj : j.val ≤ n.val)
    (hlen : bw.val.length = j.val) (hred : ∀ u ∈ bw.val, u.val < q)
    (hval : ∀ t, t < j.val → NttStage.wordAt bw t = wordN b t) :
    ring.Rq.mul_loop1 b n bw j
      ⦃ z => NttStage.Canon q z ∧ ∀ t, t < N → NttStage.wordAt z t = wordN b t ⦄ := by
  rw [ring.Rq.mul_loop1]
  apply loop.spec_decr_nat (fun s => n.val - s.2.2.val)
    (fun s => s.1 = b ∧ s.2.2.val ≤ n.val ∧ s.2.1.val.length = s.2.2.val ∧
      (∀ u ∈ s.2.1.val, u.val < q) ∧
      ∀ t, t < s.2.2.val → NttStage.wordAt s.2.1 t = wordN b t)
  · rintro ⟨s1, o1, j1⟩ ⟨h1, h2, h3, h4, h5⟩
    dsimp only at h1 h2 h3 h4 h5
    subst h1
    simp only [ring.Rq.mul_loop1.body]
    by_cases hlt : j1 < n
    · rw [if_pos hlt]
      have hjb : j1.val < s1.val.length := by rw [hb.1, ← hn]; scalar_tac
      step as ⟨f, hf⟩
      step with to_u64_id f as ⟨w, hw⟩
      have hRw : w.val < q := by rw [hw, hf]; exact hb.2 _ (List.getElem_mem hjb)
      have hwv : w.val = wordN s1 j1.val := by rw [hw, hf, wordN_of_lt hjb]
      step as ⟨o2, ho2⟩
      step as ⟨j2, hj2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hj2, List.length_append, h3]; simp
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact h4 u h
        · rw [List.mem_singleton.mp h]; exact hRw
      · intro t ht
        rw [hj2] at ht
        simp only [NttStage.wordAt] at h5 ⊢
        rcases Nat.lt_or_ge t j1.val with htlt | htge
        · rw [ho2, getD_append_lt' _ _ _ (by omega)]
          exact h5 t htlt
        · have hteq : t = o1.val.length := by omega
          rw [hteq, ho2, getD_append_eq', h3, hwv]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : j1.val = n.val := by scalar_tac
      refine ⟨⟨?_, h4⟩, ?_⟩
      · rw [h3, heq, hn]
      · intro t ht
        exact h5 t (by omega)
  · exact ⟨rfl, hj, hlen, hred, hval⟩

/-- `mul`'s third loop: wrap the transform's words back up as `Fp`. `Fp::new`
reduces, so the result is `Red` whatever the input word was -- but the words are
already below `q`, so the wrap is the identity on the representation. -/
theorem mul_loop2_spec (n : Std.Usize) (cw : alloc.vec.Vec Std.U64)
    (out : alloc.vec.Vec cpoly.field.Fp) (k : Std.Usize)
    (hn : n.val = N) (hcw : cw.val.length = N) (hk : k.val ≤ n.val)
    (hlen : out.val.length = k.val) (hred : ∀ u ∈ out.val, Red u)
    (hval : ∀ t, t < k.val → coeffK out t = ((NttStage.wordAt cw t : ℕ) : ZMod q)) :
    ring.Rq.mul_loop2 n cw out k
      ⦃ z => Wf z ∧ ∀ t, t < N → coeffK z t = ((NttStage.wordAt cw t : ℕ) : ZMod q) ⦄ := by
  rw [ring.Rq.mul_loop2]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧
      (∀ u ∈ s.1.val, Red u) ∧
      ∀ t, t < s.2.val → coeffK s.1 t = ((NttStage.wordAt cw t : ℕ) : ZMod q))
  · rintro ⟨o1, k1⟩ ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4
    simp only [ring.Rq.mul_loop2.body]
    by_cases hlt : k1 < n
    · rw [if_pos hlt]
      have hkc : k1.val < cw.val.length := by rw [hcw, ← hn]; scalar_tac
      step as ⟨w, hw⟩
      have hwv : w.val = NttStage.wordAt cw k1.val := by
        rw [hw, NttStage.wordAt_of_lt hkc]
      step as ⟨f, hRf, hf⟩
      step as ⟨o2, ho2⟩
      step as ⟨k2, hk2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hk2, List.length_append, h2]; simp
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact h3 u h
        · rw [List.mem_singleton.mp h]; exact hRf
      · intro t ht
        rw [hk2] at ht
        rcases Nat.lt_or_ge t k1.val with htlt | htge
        · rw [coeffK_append_lt ho2 (by omega)]
          exact h4 t htlt
        · have hteq : t = o1.val.length := by omega
          rw [hteq, coeffK_append_eq ho2, hf, hwv, h2]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = n.val := by scalar_tac
      refine ⟨⟨?_, h3⟩, ?_⟩
      · rw [h2, heq, hn]
      · intro t ht
        exact h4 t (by omega)
  · exact ⟨hk, hlen, hred, hval⟩

/-- The `+` antidiagonal over the copied words is the `+` antidiagonal over the
operands. Both sums run over `Finset.range N` with the same guard, so this is a
`Finset.sum_congr` once the copies are known to agree -- and they are known to
agree only below `N`, which is all either sum reads. -/
theorem posW_eq_posSum (a b : ring.Rq) (aw bw : alloc.vec.Vec Std.U64)
    (haw : ∀ t, t < N → NttStage.wordAt aw t = wordN a t)
    (hbw : ∀ t, t < N → NttStage.wordAt bw t = wordN b t)
    (k : ℕ) (hk : k < N) :
    NttProduct.posW aw bw k N = posSum a b k N := by
  unfold NttProduct.posW posSum
  refine Finset.sum_congr rfl (fun t ht => ?_)
  simp only [Finset.mem_range] at ht
  by_cases h : t ≤ k
  · rw [if_pos h, if_pos h, haw t ht, hbw (k - t) (by omega)]
  · rw [if_neg h, if_neg h]

/-- The `−` antidiagonal, likewise. Its `b` index is `N + k − t` for `t > k`,
which lies in `[k+1, N−1]`, so it too reads only below `N`. -/
theorem negW_eq_negSum (a b : ring.Rq) (aw bw : alloc.vec.Vec Std.U64)
    (haw : ∀ t, t < N → NttStage.wordAt aw t = wordN a t)
    (hbw : ∀ t, t < N → NttStage.wordAt bw t = wordN b t)
    (k : ℕ) (hk : k < N) :
    NttProduct.negW aw bw k N = negSum a b k N := by
  unfold NttProduct.negW negSum
  refine Finset.sum_congr rfl (fun t ht => ?_)
  simp only [Finset.mem_range] at ht
  by_cases h : t ≤ k
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, haw t ht]
    -- `N + k − t` with `k < t < N` lies in `[k+1, N−1]`, so it too is below `N`.
    have hkN : k < N := hk
    have hNN : NttStage.N = N := rfl
    have hidx : NttStage.N + k - t < N := by omega
    exact congrArg (fun x => wordN a t * x) (hbw _ hidx)

/-- `Rq::mul` -- the negacyclic product: total, length-preserving, and
coefficientwise `negConv`.

**The statement is the schoolbook convolution's, verbatim.** That is the point of
the whole `Aux*` development: the implementation is now an auxiliary-prime
negacyclic transform with CRT reconstruction, and the specification did not move
with it. `RqBridge.mul_spec` is unchanged too, and so is every proof above it. -/
theorem mul_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b) :
    ring.Rq.mul a b ⦃ z => Wf z ∧ ∀ k, k < N → coeffK z k = negConv a b k ⦄ := by
  rw [ring.Rq.mul]
  simp only [alloc.vec.Vec.with_capacity]
  step with mul_loop0_spec a params.RING_DEGREE (alloc.vec.Vec.new Std.U64) 0#usize
    ha params_RING_DEGREE_val (by simp) (by simp) (by intro u hu; simp at hu)
    (by intro t ht; simp at ht) as ⟨aw1, hacan, haw⟩
  step with mul_loop1_spec b params.RING_DEGREE (alloc.vec.Vec.new Std.U64) 0#usize
    hb params_RING_DEGREE_val (by simp) (by simp) (by intro u hu; simp at hu)
    (by intro t ht; simp at ht) as ⟨bw1, hbcan, hbw⟩
  have hqa : ∀ t, NttStage.wordAt aw1 t < NttProduct.q :=
    fun t => NttStage.wordAt_lt hacan (by norm_num [q]) t
  have hqb : ∀ t, NttStage.wordAt bw1 t < NttProduct.q :=
    fun t => NttStage.wordAt_lt hbcan (by norm_num [q]) t
  step with NttProduct.negconv_mod_q_spec aw1 bw1 hacan.1 hbcan.1 hqa hqb
    as ⟨cw, hcwlen, hcwred, hcwval⟩
  step with mul_loop2_spec params.RING_DEGREE cw (alloc.vec.Vec.new cpoly.field.Fp) 0#usize
    params_RING_DEGREE_val hcwlen (by simp) (by simp) (by intro u hu; simp at hu)
    (by intro t ht; simp at ht) as ⟨z, hzwf, hzval⟩
  refine ⟨hzwf, ?_⟩
  intro k hk
  -- the finished word, as the offset natural it is
  have hzk := hzval k hk
  rw [hcwval k hk] at hzk
  have hmod : ((NttProduct.offConvW aw1 bw1 k % NttProduct.q : ℕ) : ZMod q)
      = ((NttProduct.offConvW aw1 bw1 k : ℕ) : ZMod q) := ZMod.natCast_mod _ _
  -- the offset is a multiple of `q`, so it is invisible after the cast
  have hB : ((NttProduct.BOUND : ℕ) : ZMod q) = 0 := by
    have h1024 : (NttProduct.BOUND : ℕ) = 1024 * (q * q) := rfl
    rw [h1024]
    push_cast
    simp
  have hnb : NttProduct.negW aw1 bw1 k N
      ≤ NttProduct.posW aw1 bw1 k N + NttProduct.BOUND :=
    Nat.le_trans (NttProduct.negW_le_bound aw1 bw1 hqa hqb k) (Nat.le_add_left _ _)
  have hcast : ((NttProduct.offConvW aw1 bw1 k : ℕ) : ZMod q)
      = ((NttProduct.posW aw1 bw1 k N : ℕ) : ZMod q)
        - ((NttProduct.negW aw1 bw1 k N : ℕ) : ZMod q) := by
    have hoff : (NttProduct.offConvW aw1 bw1 k : ℕ)
        = NttProduct.posW aw1 bw1 k N + NttProduct.BOUND
          - NttProduct.negW aw1 bw1 k N := rfl
    rw [hoff, Nat.cast_sub hnb, Nat.cast_add, hB, add_zero]
  rw [hzk, hmod, hcast, posW_eq_posSum a b aw1 bw1 haw hbw k hk,
    negW_eq_negSum a b aw1 bw1 haw hbw k hk]
  exact negConv_eq_sums ha hb hk

/-! ## Construction and observation

The six arithmetic operations above are the ring structure; these seven are how an
element is built, read and compared. All of them are `push`/read loops of the same shape
as `zero_loop` and `add_loop` -- none uses the `Vec.set` accumulator that made `mul` hard
-- so what is worth attention here is the *statements* rather than the proofs:

* `from_coeffs_spec` is quantified over an arbitrary input length, because that is where
  its totality lives: the loop truncates at `N` and zero-pads below it, and neither
  branch may be assumed away. `coeffK` being `0` past the end of a vector is what lets
  both branches land on the same `coeffK v k`.
* `coeff_spec` needs no loop and no length hypothesis beyond `Wf`: the Rust bounds-checks
  and returns `Fp::ZERO` out of range, which is exactly `coeffK`'s own convention.
* `equals_spec` and `is_zero_spec` are `↔`, not implications. The rejection direction is
  the half a wrong implementation would satisfy -- an `equals` that always answered
  `false` proves the forward direction of both -- and it is the half `Simple.verify`
  depends on. The Rust compares through `Fp::to_u64`, so the content of these two is
  `toK_inj_of_Red`: on *reduced* words, equality of words is equality in `ZMod q`. Drop
  `Red` and the theorems are false, not merely unprovable.
-/

/-! ## `Rq::constant` and `Rq::one` -/

theorem constant_loop_spec (c : cpoly.field.Fp) (n : Std.Usize)
    (out : alloc.vec.Vec cpoly.field.Fp) (i : Std.Usize)
    (hc : Red c) (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hred : ∀ u ∈ out.val, Red u)
    (hcoef : ∀ k, k < i.val → coeffK out k = if k = 0 then toK c else 0) :
    ring.Rq.constant_loop c n out i
      ⦃ z => z.val.length = n.val ∧ (∀ u ∈ z.val, Red u) ∧
        ∀ k, k < n.val → coeffK z k = if k = 0 then toK c else 0 ⦄ := by
  rw [ring.Rq.constant_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧
      (∀ u ∈ s.1.val, Red u) ∧
      ∀ k, k < s.2.val → coeffK s.1 k = if k = 0 then toK c else 0)
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hred1, hcoef1⟩
    dsimp only at hi1 hlen1 hred1 hcoef1
    simp only [ring.Rq.constant_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      by_cases h0 : i1 = 0#usize
      · -- slot `0`: the pushed word is `c` itself.
        rw [if_pos h0]
        have hi1v : i1.val = 0 := by scalar_tac
        step as ⟨o2, ho2⟩
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
        · rw [ho2, hi2, List.length_append, hlen1]; simp
        · intro u hu
          rw [ho2] at hu
          rcases List.mem_append.mp hu with h | h
          · exact hred1 u h
          · rw [List.mem_singleton.mp h]; exact hc
        · intro k hk
          rw [hi2, hi1v] at hk
          have hk0 : k = 0 := by omega
          subst hk0
          rw [if_pos rfl]
          have hcc := coeffK_append_eq ho2
          rw [hlen1, hi1v] at hcc
          exact hcc
        · scalar_tac
      · -- every later slot: the pushed word is `Fp::ZERO`.
        rw [if_neg h0]
        have hi1v : i1.val ≠ 0 := by scalar_tac
        step as ⟨o2, ho2⟩
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
        · rw [ho2, hi2, List.length_append, hlen1]; simp
        · intro u hu
          rw [ho2] at hu
          rcases List.mem_append.mp hu with h | h
          · exact hred1 u h
          · rw [List.mem_singleton.mp h]; exact Red_zero
        · intro k hk
          rw [hi2] at hk
          rcases Nat.lt_or_ge k i1.val with hklt | hkge
          · rw [coeffK_append_lt ho2 (by omega), hcoef1 k hklt]
          · have hkeq : k = o1.val.length := by omega
            rw [hkeq, coeffK_append_eq ho2, toK_zero, if_neg (by omega)]
        · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hred1, by rw [← heq]; exact hcoef1⟩
  · exact ⟨hi, hlen, hred, hcoef⟩

theorem constant_spec (c : cpoly.field.Fp) (hc : Red c) :
    ring.Rq.constant c
      ⦃ z => Wf z ∧ ∀ k, k < N → coeffK z k = if k = 0 then toK c else 0 ⦄ := by
  rw [ring.Rq.constant]
  simp only [bind_ok_id]
  apply spec_mono (constant_loop_spec c params.RING_DEGREE
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize hc (by simp) (by simp)
    (by intro u hu; simp at hu) (by intro k hk; simp at hk))
  rintro z ⟨hzlen, hzred, hzcoef⟩
  refine ⟨⟨?_, hzred⟩, ?_⟩
  · rw [hzlen, params_RING_DEGREE_val]
  · intro k hk
    exact hzcoef k (by rw [params_RING_DEGREE_val]; exact hk)

theorem one_spec :
    ring.Rq.one ⦃ z => Wf z ∧ ∀ k, k < N → coeffK z k = if k = 0 then 1 else 0 ⦄ := by
  rw [ring.Rq.one]
  apply spec_mono (constant_spec cpoly.field.Fp.ONE Red_one)
  rintro z ⟨hz, hzcoef⟩
  refine ⟨hz, ?_⟩
  intro k hk
  rw [hzcoef k hk, toK_one]


/-! ## `Rq::from_coeffs` -/

theorem from_coeffs_loop_spec (v : alloc.vec.Vec cpoly.field.Fp) (n : Std.Usize)
    (m : Std.Usize) (out : alloc.vec.Vec cpoly.field.Fp) (i : Std.Usize)
    (hm : m.val = v.val.length) (hv : ∀ u ∈ v.val, Red u)
    (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hred : ∀ u ∈ out.val, Red u)
    (hcoef : ∀ k, k < i.val → coeffK out k = coeffK v k) :
    ring.Rq.from_coeffs_loop v n m out i
      ⦃ z => z.val.length = n.val ∧ (∀ u ∈ z.val, Red u) ∧
        ∀ k, k < n.val → coeffK z k = coeffK v k ⦄ := by
  rw [ring.Rq.from_coeffs_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧
      (∀ u ∈ s.1.val, Red u) ∧
      ∀ k, k < s.2.val → coeffK s.1 k = coeffK v k)
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hred1, hcoef1⟩
    dsimp only at hi1 hlen1 hred1 hcoef1
    simp only [ring.Rq.from_coeffs_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      by_cases hltm : i1 < m
      · rw [if_pos hltm]
        have hiv : i1.val < v.val.length := by scalar_tac
        step as ⟨f, hf⟩
        have hRf : Red f := hf ▸ hv _ (List.getElem_mem hiv)
        step as ⟨o2, ho2⟩
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
        · rw [ho2, hi2, List.length_append, hlen1]; simp
        · intro u hu
          rw [ho2] at hu
          rcases List.mem_append.mp hu with h | h
          · exact hred1 u h
          · rw [List.mem_singleton.mp h]; exact hRf
        · intro k hk
          rw [hi2] at hk
          rcases Nat.lt_or_ge k i1.val with hklt | hkge
          · rw [coeffK_append_lt ho2 (by omega), hcoef1 k hklt]
          · have hkeq : k = o1.val.length := by omega
            rw [hkeq, coeffK_append_eq ho2, hlen1, coeffK_of_lt hiv, hf]
        · scalar_tac
      · rw [if_neg hltm]
        have hgev : v.val.length ≤ i1.val := by scalar_tac
        step as ⟨o2, ho2⟩
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
        · rw [ho2, hi2, List.length_append, hlen1]; simp
        · intro u hu
          rw [ho2] at hu
          rcases List.mem_append.mp hu with h | h
          · exact hred1 u h
          · rw [List.mem_singleton.mp h]; exact Red_zero
        · intro k hk
          rw [hi2] at hk
          rcases Nat.lt_or_ge k i1.val with hklt | hkge
          · rw [coeffK_append_lt ho2 (by omega), hcoef1 k hklt]
          · have hkeq : k = o1.val.length := by omega
            rw [hkeq, coeffK_append_eq ho2, hlen1, toK_zero,
              coeffK_of_ge hgev]
        · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      rw [heq] at hlen1 hcoef1
      exact ⟨hlen1, hred1, hcoef1⟩
  · exact ⟨hi, hlen, hred, hcoef⟩

theorem from_coeffs_spec (v : ring.Rq) (hv : ∀ u ∈ v.val, Red u) :
    ring.Rq.from_coeffs v ⦃ z => Wf z ∧ ∀ k, k < N → coeffK z k = coeffK v k ⦄ := by
  rw [ring.Rq.from_coeffs]
  simp only [bind_ok_id]
  apply spec_mono (from_coeffs_loop_spec v params.RING_DEGREE (alloc.vec.Vec.len v)
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize
    (by simp) hv (by simp) (by simp) (by intro u hu; simp at hu)
    (by intro k hk; simp at hk))
  rintro z ⟨hzlen, hzred, hzcoef⟩
  refine ⟨⟨?_, hzred⟩, ?_⟩
  · rw [hzlen, params_RING_DEGREE_val]
  · intro k hk
    exact hzcoef k (by rw [params_RING_DEGREE_val]; exact hk)

theorem coeff_spec (v : ring.Rq) (k : Std.Usize) (hv : Wf v) :
    ring.Rq.coeff v k ⦃ c => Red c ∧ toK c = coeffK v k.val ⦄ := by
  obtain ⟨hlen, hred⟩ := hv
  rw [ring.Rq.coeff]
  by_cases hlt : k < alloc.vec.Vec.len v
  · rw [if_pos hlt]
    have hkb : k.val < v.val.length := by scalar_tac
    step as ⟨c, hc⟩
    exact ⟨hc ▸ Red_getElem hred hkb, by rw [hc, coeffK_of_lt hkb]⟩
  · rw [if_neg hlt, WP.spec_ok]
    have hkb : v.val.length ≤ k.val := by scalar_tac
    exact ⟨Red_zero, by rw [toK_zero, coeffK_of_ge hkb]⟩

theorem equals_loop_spec (v w : alloc.vec.Vec cpoly.field.Fp) (n : Std.Usize)
    (i : Std.Usize) (same : Bool)
    (hnv : n.val ≤ v.val.length) (hnw : n.val ≤ w.val.length)
    (hv : ∀ u ∈ v.val, Red u) (hw : ∀ u ∈ w.val, Red u)
    (hi : i.val ≤ n.val)
    (hinv : same = true ↔ ∀ k, k < i.val → coeffK v k = coeffK w k) :
    ring.Rq.equals_loop v w n i same
      ⦃ r => r = true ↔ ∀ k, k < n.val → coeffK v k = coeffK w k ⦄ := by
  rw [ring.Rq.equals_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.1.val)
    (fun s => s.1.val ≤ n.val ∧
      (s.2 = true ↔ ∀ k, k < s.1.val → coeffK v k = coeffK w k))
  · rintro ⟨i1, s1⟩ ⟨hi1, hs1⟩
    dsimp only at hi1 hs1
    simp only [ring.Rq.equals_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hiv : i1.val < v.val.length := by scalar_tac
      have hiw : i1.val < w.val.length := by scalar_tac
      step as ⟨a, ha⟩
      simp only [cpoly.field.Fp.to_u64]
      step as ⟨b, hb⟩
      have hRa : Red a := ha ▸ hv _ (List.getElem_mem hiv)
      have hRb : Red b := hb ▸ hw _ (List.getElem_mem hiw)
      have hcv : coeffK v i1.val = toK a := by rw [coeffK_of_lt hiv, ha]
      have hcw : coeffK w i1.val = toK b := by rw [coeffK_of_lt hiw, hb]
      split
      · -- the two words differ: the flag is set to `false`, and it stays correct
        -- because coefficient `i1` is a genuine witness of inequality.
        next hcond =>
        simp only [bne_iff_ne, ne_eq] at hcond
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        simp only [Bool.false_eq_true, false_iff]
        intro hall
        apply hcond
        apply Std.UScalar.eq_imp
        rw [← toK_inj_of_Red hRa hRb, ← hcv, ← hcw]
        exact hall i1.val (by omega)
      · -- the two words agree: the flag is unchanged, and the range it certifies
        -- grows by the one index just checked.
        next hcond =>
        simp only [bne_iff_ne, ne_eq, not_not] at hcond
        step as ⟨i2, hi2⟩
        have heq : coeffK v i1.val = coeffK w i1.val := by rw [hcv, hcw, hcond]
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        constructor
        · intro hs k hk
          rw [hi2] at hk
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
          · exact hs1.mp hs k hk'
          · rw [hk']; exact heq
        · intro hall
          exact hs1.mpr (fun k hk => hall k (by scalar_tac))
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      rw [heq] at hs1
      exact hs1
  · exact ⟨hi, hinv⟩

theorem equals_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b) :
    ring.Rq.equals a b ⦃ r => r = true ↔ ∀ k, k < N → coeffK a k = coeffK b k ⦄ := by
  obtain ⟨halen, hared⟩ := ha
  obtain ⟨hblen, hbred⟩ := hb
  rw [ring.Rq.equals]
  have hn : (alloc.vec.Vec.len a).val = N := by simp [halen]
  have hm : (alloc.vec.Vec.len b).val = N := by simp [hblen]
  -- Under `Wf` both vectors have length `N`, so the early `return false` is dead.
  have hlen : alloc.vec.Vec.len a = alloc.vec.Vec.len b :=
    Std.UScalar.eq_imp _ _ (by rw [hn, hm])
  rw [if_neg (by simp [hlen])]
  apply spec_mono (equals_loop_spec a b (alloc.vec.Vec.len a) 0#usize true
    (by simp) (by simp [halen, hblen]) hared hbred (by simp) (by simp))
  intro r hr
  rw [hn] at hr
  exact hr

/-- A coefficient of a vector vanishes in `ZMod q` exactly when its word is the zero
word — the step that turns the Rust's `to_u64() != 0` test into a statement about
`coeffK`. Injectivity of `toK` on reduced words is what makes it an `↔`. -/
private theorem coeffK_eq_zero_iff {v : alloc.vec.Vec cpoly.field.Fp} {k : ℕ}
    (hk : k < v.val.length) (hred : Red v.val[k]) :
    coeffK v k = 0 ↔ (v.val[k]).val = 0 := by
  rw [coeffK_of_lt hk, ← toK_zero, toK_inj_of_Red hred Red_zero, cpoly_Fp_ZERO_val]

theorem is_zero_loop_spec (v : alloc.vec.Vec cpoly.field.Fp) (n : Std.Usize)
    (i : Std.Usize) (zero : Bool)
    (hnv : n.val ≤ v.val.length) (hv : ∀ u ∈ v.val, Red u)
    (hi : i.val ≤ n.val)
    (hinv : zero = true ↔ ∀ k, k < i.val → coeffK v k = 0) :
    ring.Rq.is_zero_loop v n i zero
      ⦃ r => r = true ↔ ∀ k, k < n.val → coeffK v k = 0 ⦄ := by
  rw [ring.Rq.is_zero_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.1.val)
    (fun s => s.1.val ≤ n.val ∧ (s.2 = true ↔ ∀ k, k < s.1.val → coeffK v k = 0))
  · rintro ⟨i1, z1⟩ ⟨hi1, hz1⟩
    dsimp only at hi1 hz1
    simp only [ring.Rq.is_zero_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hiv : i1.val < v.val.length := by scalar_tac
      have hRv : Red v.val[i1.val] := hv _ (List.getElem_mem hiv)
      have hzi : coeffK v i1.val = 0 ↔ (v.val[i1.val]).val = 0 :=
        coeffK_eq_zero_iff hiv hRv
      step as ⟨f, hf⟩
      step with to_u64_id f as ⟨w, hw⟩
      by_cases hbne : (w != 0#u64) = true
      · -- the word read is nonzero: the flag drops to `false`, and it must, because
        -- coefficient `i1` is the witness that not all of them vanish.
        rw [if_pos hbne]
        have hwne : w.val ≠ 0 := by scalar_tac
        have hfne : (v.val[i1.val]).val ≠ 0 := by rw [← hf, ← hw]; exact hwne
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        constructor
        · intro h; simp at h
        · intro h
          exact absurd (hzi.mp (h i1.val (by scalar_tac))) hfne
      · -- the word read is zero: the flag is unchanged, and the range it certifies
        -- grows by the one index just checked.
        rw [if_neg hbne]
        have hw0 : w.val = 0 := by
          simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hbne; scalar_tac
        have hf0 : (v.val[i1.val]).val = 0 := by rw [← hf, ← hw]; exact hw0
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hi2]
        constructor
        · intro h k hk
          rcases Nat.lt_or_ge k i1.val with hk1 | hk2
          · exact hz1.mp h k hk1
          · have hke : k = i1.val := by omega
            rw [hke]; exact hzi.mpr hf0
        · intro h
          exact hz1.mpr (fun k hk => h k (by omega))
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      rw [heq] at hz1
      exact hz1
  · exact ⟨hi, hinv⟩

/-- `Rq::is_zero` — the all-coefficients-zero test, total, and exactly the predicate
it is supposed to decide. No length guard in the Rust: the loop runs over `self`'s own
length, which `Wf` pins to `N`. -/
theorem is_zero_spec (a : ring.Rq) (ha : Wf a) :
    ring.Rq.is_zero a ⦃ r => r = true ↔ ∀ k, k < N → coeffK a k = 0 ⦄ := by
  obtain ⟨halen, hared⟩ := ha
  rw [ring.Rq.is_zero]
  have hn : (alloc.vec.Vec.len a).val = N := by simp [halen]
  apply spec_mono (is_zero_loop_spec a (alloc.vec.Vec.len a) 0#usize true
    (by simp) hared (by simp) (by simp))
  intro r hr
  rw [hn] at hr
  exact hr

theorem copy_loop_spec (v : alloc.vec.Vec cpoly.field.Fp) (n : Std.Usize)
    (out : alloc.vec.Vec cpoly.field.Fp) (i : Std.Usize)
    (hnv : n.val ≤ v.val.length) (hv : ∀ u ∈ v.val, Red u)
    (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hred : ∀ u ∈ out.val, Red u)
    (hcoef : ∀ k, k < i.val → coeffK out k = coeffK v k) :
    ring.Rq.copy_loop v n out i
      ⦃ z => z.val.length = n.val ∧ (∀ u ∈ z.val, Red u) ∧
        ∀ k, k < n.val → coeffK z k = coeffK v k ⦄ := by
  rw [ring.Rq.copy_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧
      (∀ u ∈ s.1.val, Red u) ∧
      ∀ k, k < s.2.val → coeffK s.1 k = coeffK v k)
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hred1, hcoef1⟩
    dsimp only at hi1 hlen1 hred1 hcoef1
    simp only [ring.Rq.copy_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hiv : i1.val < v.val.length := by scalar_tac
      step as ⟨a, ha⟩
      have hRa : Red a := ha ▸ hv _ (List.getElem_mem hiv)
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hred1 u h
        · rw [List.mem_singleton.mp h]; exact hRa
      · intro k hk
        rw [hi2] at hk
        rcases Nat.lt_or_ge k i1.val with hklt | hkge
        · rw [coeffK_append_lt ho2 (by omega), hcoef1 k hklt]
        · have hkeq : k = o1.val.length := by omega
          rw [hkeq, coeffK_append_eq ho2, hlen1, coeffK_of_lt hiv, ha]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hred1, by rw [← heq]; exact hcoef1⟩
  · exact ⟨hi, hlen, hred, hcoef⟩

theorem copy_spec (a : ring.Rq) (ha : Wf a) :
    ring.Rq.copy a ⦃ z => Wf z ∧ ∀ k, k < N → coeffK z k = coeffK a k ⦄ := by
  obtain ⟨halen, hared⟩ := ha
  rw [ring.Rq.copy]
  simp only [bind_ok_id]
  apply spec_mono (copy_loop_spec a (alloc.vec.Vec.len a)
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize
    (by simp) hared (by simp) (by simp) (by intro u hu; simp at hu)
    (by intro k hk; simp at hk))
  rintro z ⟨hzlen, hzred, hzcoef⟩
  have hn : (alloc.vec.Vec.len a).val = N := by simp [halen]
  refine ⟨⟨?_, hzred⟩, ?_⟩
  · rw [hzlen, hn]
  · intro k hk
    exact hzcoef k (by rw [hn]; exact hk)

end HachiEquiv.Ring
