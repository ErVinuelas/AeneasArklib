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
`Subtype.ext`, and it lives in `lean-wip/Ring.lean` with the rest of the
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

/-- The ring degree `N = 2^α = 64`: the number of coefficients in one element. -/
abbrev N : ℕ := 64

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

end HachiEquiv.Ring
