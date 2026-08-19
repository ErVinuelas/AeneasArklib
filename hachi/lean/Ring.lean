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
`Subtype.ext`, and it lives in `lean-wip/RqBridge.lean` with the rest of the
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


/-! ## `Rq::mul`

The negacyclic product, and the only operation here whose loop writes *into* the
accumulator instead of pushing onto it. The Rust folds the wraparound in as it goes: the
term `aᵢbⱼ` is added to slot `i + j` when that is below `N`, and subtracted from slot
`i + j - N` otherwise, because `X^N ≡ -1`. `contrib` is that rule as a function,
`rowsSum` is what the accumulator holds after a whole number of rows, and `negConv` is
the closed form the completed pass reaches -- written with `Finset.antidiagonal` because
that is the shape `Polynomial.coeff_mul` produces, which is what the `Rq Φ` bridge needs.

Totality is the usual argument (`Red` on every word the loop reads) plus one fact the
other operations do not need: `i + j` is a *checked* `Usize` addition, and it cannot
overflow because both indices are below `N = 64`. -/

/-- The signed contribution of the term `u * bⱼ` to slot `k`, when `u` is the `i`-th
coefficient of the left factor: `+` when `i + j = k`, `−` when `i + j = N + k`, and
nothing otherwise. -/
def contrib (u : ZMod q) (b : ring.Rq) (i j k : ℕ) : ZMod q :=
  if i + j = k then u * coeffK b j
  else if i + j = N + k then -(u * coeffK b j)
  else 0

/-- Slot `k` of the accumulator once the first `m` rows of the schoolbook pass are done. -/
def rowsSum (a b : ring.Rq) (m k : ℕ) : ZMod q :=
  ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range N, contrib (coeffK a i) b i j k

/-- Coefficient `k` of the negacyclic product: the `k`-th antidiagonal of the raw product
minus its `(N + k)`-th, which is `(a * b) mod (X^N + 1)` written out. -/
def negConv (a b : ring.Rq) (k : ℕ) : ZMod q :=
  (∑ p ∈ Finset.antidiagonal k, coeffK a p.1 * coeffK b p.2)
    - ∑ p ∈ Finset.antidiagonal (N + k), coeffK a p.1 * coeffK b p.2

/-- Reading a coefficient out of a `Vec.set`. The `push` loops above never need this; the
convolution's inner loop does nothing else. -/
theorem coeffK_set {v : alloc.vec.Vec cpoly.field.Fp} {t : Std.Usize} {x : cpoly.field.Fp}
    (ht : t.val < v.val.length) (k : ℕ) :
    coeffK (v.set t x) k = if k = t.val then toK x else coeffK v k := by
  unfold coeffK
  rw [alloc.vec.Vec.set_val_eq]
  by_cases hk : k < v.val.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ hk,
      List.getElem_set]
    by_cases he : k = t.val
    · rw [if_pos he.symm, if_pos he]
    · rw [if_neg (fun h => he h.symm), if_neg he]
  · have hk' : ¬ k = t.val := by omega
    rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hk),
      List.getD_eq_default _ _ (Nat.le_of_not_lt hk), if_neg hk']

/-- Overwriting one entry with a reduced word keeps every entry reduced. -/
theorem Red_set {v : alloc.vec.Vec cpoly.field.Fp} {t : Std.Usize} {x : cpoly.field.Fp}
    (hv : ∀ u ∈ v.val, Red u) (hx : Red x) : ∀ u ∈ (v.set t x).val, Red u := by
  intro u hu
  rw [alloc.vec.Vec.set_val_eq] at hu
  rcases List.mem_or_eq_of_mem_set hu with h | h
  · exact hv u h
  · rw [h]; exact hx

/-- The pass that allocates the accumulator is literally `Rq::zero`'s loop -- Aeneas
extracts the two `while` bodies to definitionally equal terms. -/
theorem mul_loop0_spec (n : Std.Usize) (out : alloc.vec.Vec cpoly.field.Fp) (i : Std.Usize)
    (hi : i.val ≤ n.val) (hout : out.val = List.replicate i.val cpoly.field.Fp.ZERO) :
    ring.Rq.mul_loop0 n out i
      ⦃ z => z.val = List.replicate n.val cpoly.field.Fp.ZERO ⦄ :=
  zero_loop_spec n out i hi hout

/-- The inner (`j`) pass, for the row of the left factor whose coefficient is `x`. `acc` is
whatever the rows already processed contributed; the invariant adds one `contrib` per
iteration, and the two branches of the `if` are the two branches of `contrib`. -/
theorem mul_loop1_loop0_spec (b : ring.Rq) (n : Std.Usize)
    (out : alloc.vec.Vec cpoly.field.Fp) (i : Std.Usize) (x : cpoly.field.Fp)
    (j : Std.Usize) (acc : ℕ → ZMod q)
    (hn : n.val = N) (hb : Wf b) (hx : Red x) (hi : i.val < N) (hj : j.val ≤ N)
    (hlen : out.val.length = N) (hred : ∀ u ∈ out.val, Red u)
    (hcoef : ∀ k, k < N → coeffK out k
      = acc k + ∑ j' ∈ Finset.range j.val, contrib (toK x) b i.val j' k) :
    ring.Rq.mul_loop1_loop0 b n out i x j
      ⦃ r => r.1 = b ∧ r.2.val.length = N ∧ (∀ u ∈ r.2.val, Red u) ∧
        ∀ k, k < N → coeffK r.2 k
          = acc k + ∑ j' ∈ Finset.range N, contrib (toK x) b i.val j' k ⦄ := by
  obtain ⟨hblen, hbred⟩ := hb
  rw [ring.Rq.mul_loop1_loop0]
  apply loop.spec_decr_nat (fun s => n.val - s.2.2.val)
    (fun s => s.1 = b ∧ s.2.2.val ≤ N ∧ s.2.1.val.length = N ∧
      (∀ u ∈ s.2.1.val, Red u) ∧
      ∀ k, k < N → coeffK s.2.1 k
        = acc k + ∑ j' ∈ Finset.range s.2.2.val, contrib (toK x) b i.val j' k)
  · rintro ⟨r1, o1, j1⟩ ⟨hr1, hj1, hlen1, hred1, hcoef1⟩
    dsimp only at hr1 hj1 hlen1 hred1 hcoef1
    subst hr1
    simp only [ring.Rq.mul_loop1_loop0.body]
    by_cases hlt : j1 < n
    · rw [if_pos hlt]
      have hjn : j1.val < N := by scalar_tac
      have hjb : j1.val < r1.val.length := by scalar_tac
      step as ⟨f, hf⟩
      have hRf : Red f := hf ▸ hbred _ (List.getElem_mem hjb)
      step as ⟨term, hRterm, hterm⟩
      step as ⟨s, hs⟩
      by_cases hsn : s < n
      · -- `i + j` lands in slot `s = i + j` with a `+`.
        rw [if_pos hsn]
        have hsv : s.val = i.val + j1.val := by scalar_tac
        have hsN : s.val < N := by scalar_tac
        have hsb : s.val < o1.val.length := by scalar_tac
        step as ⟨f1, hf1⟩
        have hRf1 : Red f1 := hf1 ▸ hred1 _ (List.getElem_mem hsb)
        step as ⟨f2, hRf2, hf2⟩
        step as ⟨y, hy1, hy2⟩
        obtain ⟨y1, y2⟩ := y
        dsimp only at hy1 hy2 ⊢
        rw [hy2]
        step as ⟨j2, hj2⟩
        refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
        · rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen1
        · exact Red_set hred1 hRf2
        · intro k hk
          rw [coeffK_set hsb k, hj2, Finset.sum_range_succ]
          by_cases hke : k = s.val
          · subst hke
            have hcond : i.val + j1.val = s.val := by omega
            have hc1 : contrib (toK x) r1 i.val j1.val s.val = toK x * toK f := by
              unfold contrib
              rw [if_pos hcond, coeffK_of_lt hjb, hf]
            have ho : coeffK o1 s.val = toK f1 := by rw [coeffK_of_lt hsb, hf1]
            rw [if_pos rfl, hc1, hf2, hterm, ← ho, hcoef1 _ hk]
            ring
          · have h1 : ¬ (i.val + j1.val = k) := by omega
            have h2 : ¬ (i.val + j1.val = N + k) := by omega
            have hc0 : contrib (toK x) r1 i.val j1.val k = 0 := by
              unfold contrib
              rw [if_neg h1, if_neg h2]
            rw [if_neg hke, hc0, hcoef1 k hk, add_zero]
        · scalar_tac
      · -- `X^N = -1`: the term lands in slot `t = i + j - N` with a `-`.
        rw [if_neg hsn]
        have hsv : s.val = i.val + j1.val := by scalar_tac
        have hsge : n.val ≤ s.val := by scalar_tac
        step as ⟨t, ht⟩
        have htv : t.val = i.val + j1.val - N := by scalar_tac
        have htb : t.val < o1.val.length := by scalar_tac
        step as ⟨f1, hf1⟩
        have hRf1 : Red f1 := hf1 ▸ hred1 _ (List.getElem_mem htb)
        step as ⟨f2, hRf2, hf2⟩
        step as ⟨y, hy1, hy2⟩
        obtain ⟨y1, y2⟩ := y
        dsimp only at hy1 hy2 ⊢
        rw [hy2]
        step as ⟨j2, hj2⟩
        refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
        · rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen1
        · exact Red_set hred1 hRf2
        · intro k hk
          rw [coeffK_set htb k, hj2, Finset.sum_range_succ]
          by_cases hke : k = t.val
          · subst hke
            have hcond1 : ¬ (i.val + j1.val = t.val) := by omega
            have hcond2 : i.val + j1.val = N + t.val := by omega
            have hc1 : contrib (toK x) r1 i.val j1.val t.val = -(toK x * toK f) := by
              unfold contrib
              rw [if_neg hcond1, if_pos hcond2, coeffK_of_lt hjb, hf]
            have ho : coeffK o1 t.val = toK f1 := by rw [coeffK_of_lt htb, hf1]
            rw [if_pos rfl, hc1, hf2, hterm, ← ho, hcoef1 _ hk]
            ring
          · have h1 : ¬ (i.val + j1.val = k) := by omega
            have h2 : ¬ (i.val + j1.val = N + k) := by omega
            have hc0 : contrib (toK x) r1 i.val j1.val k = 0 := by
              unfold contrib
              rw [if_neg h1, if_neg h2]
            rw [if_neg hke, hc0, hcoef1 k hk, add_zero]
        · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : j1.val = N := by scalar_tac
      rw [heq] at hcoef1
      exact ⟨rfl, hlen1, hred1, hcoef1⟩
  · exact ⟨rfl, hj, hlen, hred, hcoef⟩

/-- One more row of the schoolbook pass. -/
private theorem rowsSum_succ (a b : ring.Rq) (m k : ℕ) :
    rowsSum a b (m + 1) k
      = rowsSum a b m k + ∑ j ∈ Finset.range N, contrib (coeffK a m) b m j k := by
  unfold rowsSum
  exact Finset.sum_range_succ _ _

theorem mul_loop1_spec (a b : ring.Rq) (n : Std.Usize)
    (out : alloc.vec.Vec cpoly.field.Fp) (i : Std.Usize)
    (hn : n.val = N) (ha : Wf a) (hb : Wf b) (hi : i.val ≤ N)
    (hlen : out.val.length = N) (hred : ∀ u ∈ out.val, Red u)
    (hcoef : ∀ k, k < N → coeffK out k = rowsSum a b i.val k) :
    ring.Rq.mul_loop1 a b n out i
      ⦃ z => z.val.length = N ∧ (∀ u ∈ z.val, Red u) ∧
        ∀ k, k < N → coeffK z k = rowsSum a b N k ⦄ := by
  obtain ⟨halen, hared⟩ := ha
  obtain ⟨hblen, hbred⟩ := hb
  rw [ring.Rq.mul_loop1]
  apply loop.spec_decr_nat (fun s => N - s.2.2.2.val)
    (fun s => s.1 = a ∧ s.2.1 = b ∧ s.2.2.2.val ≤ N ∧ s.2.2.1.val.length = N ∧
      (∀ u ∈ s.2.2.1.val, Red u) ∧
      ∀ k, k < N → coeffK s.2.2.1 k = rowsSum a b s.2.2.2.val k)
  · rintro ⟨a1, b1, o1, i1⟩ ⟨ha1, hb1, hi1, hlen1, hred1, hcoef1⟩
    dsimp only at ha1 hb1 hi1 hlen1 hred1 hcoef1
    subst ha1; subst hb1
    simp only [ring.Rq.mul_loop1.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hia : i1.val < a1.val.length := by scalar_tac
      step as ⟨x, hx⟩
      have hRx : Red x := hx ▸ hared _ (List.getElem_mem hia)
      have hxk : toK x = coeffK a1 i1.val := by rw [coeffK_of_lt hia, hx]
      step with mul_loop1_loop0_spec b1 n o1 i1 x 0#usize (rowsSum a1 b1 i1.val)
          hn ⟨hblen, hbred⟩ hRx (by scalar_tac) (by simp) hlen1 hred1
          (by intro k hk; rw [hcoef1 k hk]; simp)
        as ⟨rb, o2, hrb, hlen2, hred2, hcoef2⟩
      step as ⟨i2, hi2⟩
      refine ⟨hrb, by scalar_tac, hlen2, hred2, ?_, by scalar_tac⟩
      intro k hk
      rw [hi2, hcoef2 k hk, hxk, rowsSum_succ]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = N := by scalar_tac
      exact ⟨hlen1, hred1, by intro k hk; rw [hcoef1 k hk, heq]⟩
  · exact ⟨rfl, rfl, hi, hlen, hred, hcoef⟩

/-- A doubly-indexed sum restricted to one antidiagonal is that antidiagonal's sum, when
the summand vanishes outside the `N × N` block. The step from the loops' `range N × range N`
bookkeeping to the form `Polynomial.coeff_mul` speaks. -/
theorem sum_block_eq_antidiagonal (A : ℕ → ℕ → ZMod q)
    (hAi : ∀ i j, N ≤ i → A i j = 0) (hAj : ∀ i j, N ≤ j → A i j = 0) (m : ℕ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, if i + j = m then A i j else 0)
      = ∑ p ∈ Finset.antidiagonal m, A p.1 p.2 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ A m]
  -- Collapse the inner sum: at most `j = m - i` survives, and it is `0` once `m - i ≥ N`.
  have key : ∀ i : ℕ, (∑ j ∈ Finset.range N, if i + j = m then A i j else 0)
      = if i ≤ m then A i (m - i) else 0 := by
    intro i
    by_cases him : i ≤ m
    · rw [if_pos him]
      by_cases hmi : m - i < N
      · rw [Finset.sum_eq_single (m - i)]
        · rw [if_pos (by omega)]
        · intro j _ hj; rw [if_neg (by omega)]
        · intro h; exact absurd (Finset.mem_range.mpr hmi) h
      · rw [hAj i (m - i) (by omega)]
        refine Finset.sum_eq_zero ?_
        intro j hj
        rw [Finset.mem_range] at hj
        rw [if_neg (by omega)]
    · rw [if_neg him]
      refine Finset.sum_eq_zero ?_
      intro j _
      rw [if_neg (by omega)]
  simp only [key]
  -- Both sides are now sums of the same guarded summand, over `range N` and `range (m+1)`.
  have hrhs : (∑ i ∈ Finset.range m.succ, A i (m - i))
      = ∑ i ∈ Finset.range m.succ, (if i ≤ m then A i (m - i) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Finset.mem_range] at hi
    rw [if_pos (by omega)]
  rw [hrhs]
  rcases le_total (m + 1) N with h | h
  · refine (Finset.sum_subset (Finset.range_subset_range.mpr h) ?_).symm
    intro i hi hni
    rw [Finset.mem_range] at hi
    rw [Finset.mem_range] at hni
    rw [if_neg (by omega)]
  · refine Finset.sum_subset (Finset.range_subset_range.mpr h) ?_
    intro i hi hni
    rw [Finset.mem_range] at hi
    rw [Finset.mem_range] at hni
    rw [if_pos (by omega)]
    exact hAi i (m - i) (by omega)

/-- The two branches of `contrib` are mutually exclusive (`N > 0`, so `k ≠ N + k`),
so the three-way `if` is a difference of two one-sided indicators. This is the form
`sum_block_eq_antidiagonal` consumes. -/
private theorem contrib_eq_sub (u : ZMod q) (b : ring.Rq) (i j k : ℕ) :
    contrib u b i j k
      = (if i + j = k then u * coeffK b j else 0)
        - (if i + j = N + k then u * coeffK b j else 0) := by
  have hN : N = 64 := rfl
  unfold contrib
  split_ifs with h₁ h₂ h₃ <;> first | omega | ring

theorem rowsSum_full (a b : ring.Rq) (ha : Wf a) (hb : Wf b) (k : ℕ) :
    rowsSum a b N k = negConv a b k := by
  obtain ⟨halen, -⟩ := ha
  obtain ⟨hblen, -⟩ := hb
  -- The summand vanishes outside the `N × N` block, because `coeffK` is `0` past
  -- the end of a vector and both vectors have length exactly `N`.
  have hAi : ∀ i j : ℕ, N ≤ i → coeffK a i * coeffK b j = 0 := by
    intro i j hi
    rw [coeffK_of_ge (show a.val.length ≤ i by omega), zero_mul]
  have hAj : ∀ i j : ℕ, N ≤ j → coeffK a i * coeffK b j = 0 := by
    intro i j hj
    rw [coeffK_of_ge (show b.val.length ≤ j by omega), mul_zero]
  have key : ∀ m : ℕ,
      (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          if i + j = m then coeffK a i * coeffK b j else 0)
        = ∑ p ∈ Finset.antidiagonal m, coeffK a p.1 * coeffK b p.2 :=
    sum_block_eq_antidiagonal (fun i j => coeffK a i * coeffK b j) hAi hAj
  unfold rowsSum negConv
  calc ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, contrib (coeffK a i) b i j k
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          ((if i + j = k then coeffK a i * coeffK b j else 0)
            - (if i + j = N + k then coeffK a i * coeffK b j else 0)) := by
        simp only [contrib_eq_sub]
    _ = (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            if i + j = k then coeffK a i * coeffK b j else 0)
          - ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            if i + j = N + k then coeffK a i * coeffK b j else 0 := by
        simp only [Finset.sum_sub_distrib]
    _ = _ := by rw [key k, key (N + k)]

/-- `Rq::mul` -- the negacyclic product: total, length-preserving, and coefficientwise
`negConv`, the `k`-th antidiagonal of the raw product minus its `(N + k)`-th.

`lean-wip/RqBridge.lean` is what turns that into the statement about ArkLib's
`Mul (Rq Φ)`; the reduction the specification performs with `modByMonic` is exactly the
minus sign the Rust folds in as it goes. -/
theorem mul_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b) :
    ring.Rq.mul a b ⦃ z => Wf z ∧ ∀ k, k < N → coeffK z k = negConv a b k ⦄ := by
  rw [ring.Rq.mul]
  simp only [bind_ok_id]
  apply spec_bind (mul_loop0_spec params.RING_DEGREE (alloc.vec.Vec.new cpoly.field.Fp)
    0#usize (by simp) (by simp))
  intro out hout
  -- The zeroing pass leaves a `replicate`, so every read is `Fp::ZERO`, in range or not.
  have hread : ∀ k, out.val.getD k cpoly.field.Fp.ZERO = cpoly.field.Fp.ZERO := by
    intro k
    rw [hout]
    by_cases hk : k < (List.replicate ((params.RING_DEGREE).val) cpoly.field.Fp.ZERO).length
    · rw [List.getD_eq_getElem _ _ hk, List.getElem_replicate]
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hk)]
  have hlen : out.val.length = N := by
    rw [hout, List.length_replicate, params_RING_DEGREE_val]
  have hred : ∀ u ∈ out.val, Red u := by
    intro u hu
    rw [hout] at hu
    rw [List.eq_of_mem_replicate hu]
    exact Red_zero
  have hcoef : ∀ k, k < N → coeffK out k = rowsSum a b (0#usize).val k := by
    intro k _
    have h0 : coeffK out k = 0 := by unfold coeffK; rw [hread k]; exact toK_zero
    rw [h0]
    simp [rowsSum]
  apply spec_mono (mul_loop1_spec a b params.RING_DEGREE out 0#usize
    params_RING_DEGREE_val ha hb (by simp) hlen hred hcoef)
  rintro z ⟨hzlen, hzred, hzcoef⟩
  refine ⟨⟨hzlen, hzred⟩, ?_⟩
  intro k hk
  rw [hzcoef k hk, rowsSum_full a b ha hb k]

end HachiEquiv.Ring
