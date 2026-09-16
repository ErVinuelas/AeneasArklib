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
lemma is registered for it, so the loop body needs it spelled out. -/
private theorem to_u64_id (f : cpoly.field.Fp) :
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

theorem posSum_zero (a b : ring.Rq) (k : ℕ) : posSum a b k 0 = 0 := by
  simp [posSum]

theorem negSum_zero (a b : ring.Rq) (k : ℕ) : negSum a b k 0 = 0 := by
  simp [negSum]

theorem posSum_succ (a b : ring.Rq) (k m : ℕ) :
    posSum a b k (m + 1)
      = posSum a b k m + (if m ≤ k then wordN a m * wordN b (k - m) else 0) :=
  Finset.sum_range_succ _ _

theorem negSum_succ (a b : ring.Rq) (k m : ℕ) :
    negSum a b k (m + 1)
      = negSum a b k m + (if m ≤ k then 0 else wordN a m * wordN b (N + k - m)) :=
  Finset.sum_range_succ _ _

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

/-- The ceiling that makes the delayed reduction sound: `N` terms of at most
`q * q` each, against `u128`. `1024 · (2^32 − 99)² < 2^74`, so there are 54 bits
to spare -- and a `u64` accumulator would already overflow on one term. -/
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

/-! ### The two loops

The inner loop is the one with content: its state carries both accumulators and
the two operands (Aeneas threads the shared borrows, so the state is a 5-tuple
`(self, rhs, pos, neg, i)` and the two operands come back unchanged). Each step
adds one term to exactly one accumulator, and the no-overflow obligation on the
checked `u128` `+` is discharged from `posSum_le`/`negSum_le` against
`accBound`. -/

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

theorem mul_loop0_loop0_spec (a b : ring.Rq) (n k : Std.Usize) (pos neg : Std.U128)
    (i : Std.Usize) (ha : Wf a) (hb : Wf b) (hn : n.val = N) (hk : k.val < N)
    (hi : i.val ≤ n.val)
    (hpos : pos.val = posSum a b k.val i.val)
    (hneg : neg.val = negSum a b k.val i.val) :
    ring.Rq.mul_loop0_loop0 a b n k pos neg i
      ⦃ z => z.1 = a ∧ z.2.1 = b ∧ z.2.2.1.val = posSum a b k.val N
             ∧ z.2.2.2.val = negSum a b k.val N ⦄ := by
  rw [ring.Rq.mul_loop0_loop0]
  apply loop.spec_decr_nat (fun s => n.val - s.2.2.2.2.val)
    (fun s => s.1 = a ∧ s.2.1 = b ∧ s.2.2.2.2.val ≤ n.val
      ∧ s.2.2.1.val = posSum a b k.val s.2.2.2.2.val
      ∧ s.2.2.2.1.val = negSum a b k.val s.2.2.2.2.val)
  · rintro ⟨s1, s2, sp, sn, si⟩ ⟨h1, h2, hsi, hsp, hsn⟩
    dsimp only at h1 h2 hsi hsp hsn
    simp only [ring.Rq.mul_loop0_loop0.body]
    by_cases hlt : si < n
    · rw [if_pos hlt]
      have hsiN : si.val < N := by rw [← hn]; scalar_tac
      have hs1len : s1.val.length = N := by rw [h1]; exact ha.1
      have hs2len : s2.val.length = N := by rw [h2]; exact hb.1
      have hterm : ∀ u : ℕ, wordN a si.val * wordN b u ≤ q * q :=
        fun u => Nat.mul_le_mul (Nat.le_of_lt (wordN_lt ha _)) (Nat.le_of_lt (wordN_lt hb u))
      have hstep : (si.val + 1) * (q * q) ≤ N * (q * q) :=
        Nat.mul_le_mul_right _ (by omega)
      step as ⟨f, hf⟩
      step with to_u64_id f as ⟨w, hw⟩
      have haiv : w.val = wordN a si.val := by
        rw [hw, hf, ← wordN_of_lt (v := s1) (t := si.val) (by omega), h1]
      have hcast : lift (UScalar.cast .U128 w) ⦃ y => y.val = w.val ⦄ :=
        UScalar.cast_inBounds_spec .U128 w (by scalar_tac)
      step with hcast as ⟨ai, hai⟩
      by_cases hle : si ≤ k
      · rw [if_pos hle]
        step as ⟨d, hd⟩
        step as ⟨g, hg⟩
        step with to_u64_id g as ⟨w2, hw2⟩
        have hbjv : w2.val = wordN b (k.val - si.val) := by
          rw [hw2, hg, ← wordN_of_lt (v := s2) (t := d.val) (by omega), h2, hd]
        have hcast2 : lift (UScalar.cast .U128 w2) ⦃ y => y.val = w2.val ⦄ :=
          UScalar.cast_inBounds_spec .U128 w2 (by scalar_tac)
        step with hcast2 as ⟨bj, hbj⟩
        have hbnd : sp.val + ai.val * bj.val ≤ Std.U128.max := by
          have hacc := accBound
          have hprod : ai.val * bj.val ≤ q * q := by
            rw [hai, hbj, haiv, hbjv]; exact hterm _
          have hposle : sp.val ≤ si.val * (q * q) := by
            rw [hsp]; exact posSum_le ha hb _ _
          calc sp.val + ai.val * bj.val ≤ si.val * (q * q) + q * q :=
                Nat.add_le_add hposle hprod
            _ = (si.val + 1) * (q * q) := by ring
            _ ≤ N * (q * q) := hstep
            _ ≤ Std.U128.max := Nat.le_of_lt hacc
        step as ⟨t, ht⟩
        step as ⟨sp2, hsp2⟩
        step as ⟨si2, hsi2⟩
        refine ⟨h1, h2, by scalar_tac, ?_, ?_, by scalar_tac⟩
        · rw [hsp2, ht, hai, hbj, haiv, hbjv, hsp, hsi2, posSum_succ,
            if_pos (by scalar_tac)]
        · rw [hsn, hsi2, negSum_succ, if_pos (by scalar_tac), Nat.add_zero]
      · rw [if_neg hle]
        have hgt : k.val < si.val := by scalar_tac
        step as ⟨d1, hd1⟩
        step as ⟨d, hd⟩
        step as ⟨g, hg⟩
        step with to_u64_id g as ⟨w2, hw2⟩
        have hbjv : w2.val = wordN b (N + k.val - si.val) := by
          have hdlt : d.val < s2.val.length := by rw [hs2len]; scalar_tac
          rw [hw2, hg, ← wordN_of_lt (v := s2) (t := d.val) hdlt, h2, hd, hd1]
          congr 1
          scalar_tac
        have hcast2 : lift (UScalar.cast .U128 w2) ⦃ y => y.val = w2.val ⦄ :=
          UScalar.cast_inBounds_spec .U128 w2 (by scalar_tac)
        step with hcast2 as ⟨bj, hbj⟩
        have hbnd : sn.val + ai.val * bj.val ≤ Std.U128.max := by
          have hacc := accBound
          have hprod : ai.val * bj.val ≤ q * q := by
            rw [hai, hbj, haiv, hbjv]; exact hterm _
          have hnegle : sn.val ≤ si.val * (q * q) := by
            rw [hsn]; exact negSum_le ha hb _ _
          calc sn.val + ai.val * bj.val ≤ si.val * (q * q) + q * q :=
                Nat.add_le_add hnegle hprod
            _ = (si.val + 1) * (q * q) := by ring
            _ ≤ N * (q * q) := hstep
            _ ≤ Std.U128.max := Nat.le_of_lt hacc
        step as ⟨t, ht⟩
        step as ⟨sn2, hsn2⟩
        step as ⟨si2, hsi2⟩
        refine ⟨h1, h2, by scalar_tac, ?_, ?_, by scalar_tac⟩
        · rw [hsp, hsi2, posSum_succ, if_neg (by scalar_tac), Nat.add_zero]
        · rw [hsn2, ht, hai, hbj, haiv, hbjv, hsn, hsi2, negSum_succ,
            if_neg (by scalar_tac)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : si.val = N := by rw [← hn]; scalar_tac
      exact ⟨h1, h2, by rw [hsp, heq], by rw [hsn, heq]⟩
  · exact ⟨rfl, rfl, hi, hpos, hneg⟩

theorem mul_loop0_spec (a b : ring.Rq) (n : Std.Usize) (qw : Std.U128)
    (out : alloc.vec.Vec cpoly.field.Fp) (k : Std.Usize)
    (ha : Wf a) (hb : Wf b) (hn : n.val = N) (hq : qw.val = q)
    (hk : k.val ≤ n.val) (hlen : out.val.length = k.val)
    (hred : ∀ u ∈ out.val, Red u)
    (hval : ∀ t, t < k.val → coeffK out t = negConv a b t) :
    ring.Rq.mul_loop0 a b n qw out k
      ⦃ z => z.val.length = N ∧ (∀ u ∈ z.val, Red u)
             ∧ ∀ t, t < N → coeffK z t = negConv a b t ⦄ := by
  rw [ring.Rq.mul_loop0]
  apply loop.spec_decr_nat (fun s => n.val - s.2.2.2.val)
    (fun s => s.1 = a ∧ s.2.1 = b ∧ s.2.2.2.val ≤ n.val
      ∧ s.2.2.1.val.length = s.2.2.2.val ∧ (∀ u ∈ s.2.2.1.val, Red u)
      ∧ ∀ t, t < s.2.2.2.val → coeffK s.2.2.1 t = negConv a b t)
  · rintro ⟨s1, s2, so, sk⟩ ⟨h1, h2, hsk, hlen1, hred1, hval1⟩
    dsimp only at h1 h2 hsk hlen1 hred1 hval1
    simp only [ring.Rq.mul_loop0.body]
    by_cases hlt : sk < n
    · rw [if_pos hlt]
      have hskN : sk.val < N := by rw [← hn]; scalar_tac
      have hqpos : 0 < q := by norm_num [q]
      step with mul_loop0_loop0_spec s1 s2 n sk 0#u128 0#u128 0#usize
        (by rw [h1]; exact ha) (by rw [h2]; exact hb) hn hskN
        (by simp) (by simp [posSum_zero]) (by simp [negSum_zero]) as ⟨r1, r2, rp, rn, hr1, hr2, hrp, hrn⟩
      have hr1a : r1 = a := hr1.trans h1
      have hr2b : r2 = b := hr2.trans h2
      have hrp' : rp.val = posSum a b sk.val N := by rw [hrp, h1, h2]
      have hrn' : rn.val = negSum a b sk.val N := by rw [hrn, h1, h2]
      step as ⟨mp, hmp⟩
      have hcast : lift (UScalar.cast .U64 mp) ⦃ y => y.val = mp.val ⦄ :=
        UScalar.cast_inBounds_spec .U64 mp (by
          rw [hmp, hq]
          have hb1 : rp.val % q < q := Nat.mod_lt _ hqpos
          have hb2 : q ≤ UScalar.max UScalarTy.U64 := by
            simp only [q, UScalar.max, UScalarTy.numBits]; norm_num
          omega)
      step with hcast as ⟨pw, hpw⟩
      step as ⟨pf, hRpf, hpf⟩
      step as ⟨mn, hmn⟩
      have hcast2 : lift (UScalar.cast .U64 mn) ⦃ y => y.val = mn.val ⦄ :=
        UScalar.cast_inBounds_spec .U64 mn (by
          rw [hmn, hq]
          have hb1 : rn.val % q < q := Nat.mod_lt _ hqpos
          have hb2 : q ≤ UScalar.max UScalarTy.U64 := by
            simp only [q, UScalar.max, UScalarTy.numBits]; norm_num
          omega)
      step with hcast2 as ⟨nw, hnw⟩
      step as ⟨nf, hRnf, hnf⟩
      step with fp_sub_spec pf nf hRpf hRnf as ⟨dd, hRd, hdd⟩
      step as ⟨so2, hso2⟩
      step as ⟨sk2, hsk2⟩
      refine ⟨hr1a, hr2b, by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
      · rw [hso2, hsk2, List.length_append, hlen1]; simp
      · intro u hu
        rw [hso2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hred1 u h
        · rw [List.mem_singleton.mp h]; exact hRd
      · intro t ht
        rw [hsk2] at ht
        rcases Nat.lt_or_ge t sk.val with htlt | htge
        · rw [coeffK, hso2, getD_append_lt' _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : t = so.val.length := by omega
          rw [coeffK, hteq, hso2, getD_append_eq' _ _ _, hdd, hpf, hnf, hpw, hnw, hmp, hmn,
            hq, hrp', hrn', ZMod.natCast_mod, ZMod.natCast_mod, hlen1]
          exact negConv_eq_sums ha hb hskN
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : sk.val = N := by rw [← hn]; scalar_tac
      exact ⟨by rw [hlen1, heq], hred1, by
        intro t ht; exact hval1 t (by rw [heq]; exact ht)⟩
  · exact ⟨rfl, rfl, hk, hlen, hred, hval⟩

/-- `Rq::mul` -- the negacyclic product: total, length-preserving, and coefficientwise
`negConv`. The statement is candidate Q's predecessor's, verbatim: the reduction moved,
the semantics did not. -/
theorem mul_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b) :
    ring.Rq.mul a b ⦃ z => Wf z ∧ ∀ k, k < N → coeffK z k = negConv a b k ⦄ := by
  rw [ring.Rq.mul]
  have hcast : lift (UScalar.cast .U128 params.Q) ⦃ y => y.val = (params.Q).val ⦄ :=
    UScalar.cast_inBounds_spec .U128 params.Q (by rw [params_Q_val]; norm_num [q, U128.max, U128.numBits])
  step with hcast as ⟨qw, hqw⟩
  simp only [alloc.vec.Vec.with_capacity]
  step with mul_loop0_spec a b params.RING_DEGREE qw
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize ha hb params_RING_DEGREE_val
    (by rw [hqw]; exact params_Q_val) (by simp [params_RING_DEGREE_val]) (by simp)
    (by intro u hu; simp at hu) (by intro t ht; simp at ht)
    as ⟨z, hlen, hred, hvals⟩
  exact ⟨⟨hlen, hred⟩, hvals⟩

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
