/-
The **upper layers** of the equivalence: linear algebra, the gadget, and the
inner-outer commitment. Statements only, on the bridge from `Ring.lean`.

Unchecked, and outside the audited library; see `lean-wip/README.md`.

## Why the statements are the deliverable

Each theorem below fixes what the corresponding Rust function has to mean, in the
specification's own vocabulary, before any proof exists. That is worth having on
its own: it is where a mistranslation shows up. Two of them earn their place
already, because writing them down is what settled a design question in the Rust:

* `gadget_mul_spec` states agreement with `gadgetMul`, which is
  `gadgetMatrix *ᵥ v` — a *matrix* product. The Rust computes the per-block digit
  sum instead. Those are equal by the specification's own `gadgetMul_apply`, which
  is therefore not an optimization note but a load-bearing step of this proof.
* `verify_weak_spec` is an *equality of decisions*, not an implication. A verifier
  that rejected everything would satisfy `verify_weak = true → (the spec's checks
  hold)`; only the equality says the two accept the same openings, and only that
  form makes the rejection paths part of the claim.

## The composition order

`linalg` over `Ring`, `gadget` over both, `commit` over all three — the same
layering as `src/`. Each layer's specs are stated so that the layer above can
`step` through them without unfolding anything: that is why the `Wf` predicates
below are conjunctions of a shape condition and an entrywise one, and why the
gadget statements are about `Φ.φ.natDegree` where the Rust says `RING_DEGREE`
(they are equal by `Ring.phi_natDegree`, and using the spec's spelling keeps the
rewrite out of the upper layers).
-/
import RqBridge
import ArkLib.Commitments.Functional.Hachi.InnerOuter.Scheme
import ArkLib.Commitments.Functional.Hachi.Gadget.Norms

-- On, for the reason `lean/Check.lean` gives at length: with `autoImplicit` an
-- unknown identifier in a binder becomes an implicitly bound variable, so a missing
-- `open` turns a statement about `q` into a statement about *any* natural number --
-- which is how a spec silently becomes vacuous.
set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.Scheme

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge

/-! ## Vectors and matrices -/

/-- A vector of the extracted model is well-formed when it has the expected length
and every entry is. -/
def WfVec (k : ℕ) (v : linalg.PolyVec) : Prop :=
  v.val.length = k ∧ ∀ x ∈ v.val, Wf x

/-- The `PolyVec` an extracted vector represents. `Fin`-indexed, as the
specification's containers are; out-of-range indices cannot occur, so the
function is total by construction. -/
def toVec {k : ℕ} (v : linalg.PolyVec) : PolyVec (Rq Φ) k :=
  fun i => toRq (v.val.getD i.val (alloc.vec.Vec.new cpoly.field.Fp))

/-- A matrix is well-formed when it has the expected number of rows and each row is
a well-formed vector of the expected width. -/
def WfMat (rows cols : ℕ) (a : linalg.PolyMatrix) : Prop :=
  a.val.length = rows ∧ ∀ r ∈ a.val, WfVec cols r

/-- The `PolyMatrix` an extracted matrix represents. -/
def toMat {rows cols : ℕ} (a : linalg.PolyMatrix) : PolyMatrix (Rq Φ) rows cols :=
  fun i j => (toVec (k := cols) (a.val.getD i.val (alloc.vec.Vec.new ring.Rq))) j

/-! ### Working with extracted vectors

The loop proofs below all have the same shape: an accumulator vector is grown one
entry at a time, and the invariant says that its length is the counter and that each
entry already written is the intended one. The four lemmas here are what that
invariant is stated and stepped with. -/

attribute [local step] HachiEquiv.RqBridge.add_spec HachiEquiv.RqBridge.sub_spec
  HachiEquiv.RqBridge.mul_spec HachiEquiv.RqBridge.zero_spec HachiEquiv.RqBridge.one_spec
  HachiEquiv.RqBridge.constant_spec HachiEquiv.RqBridge.scalar_mul_spec
  HachiEquiv.RqBridge.copy_spec HachiEquiv.RqBridge.from_coeffs_spec
  HachiEquiv.RqBridge.coeff_spec

/-- Reading below the end of a pushed-to list is reading the list before the push. -/
theorem getD_append_lt {α : Type} (l : List α) (x d : α) {j : ℕ} (hj : j < l.length) :
    (l ++ [x]).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hj,
    List.getElem_append_left hj]

/-- Reading at the end of a pushed-to list is reading the pushed element. -/
theorem getD_append_eq {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
  simp

/-- Every in-range entry of a well-formed vector is a well-formed ring element. -/
theorem wf_getD {k : ℕ} {v : linalg.PolyVec} (hv : WfVec k v) {j : ℕ} (hj : j < k) :
    Wf (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) := by
  obtain ⟨hlen, hwf⟩ := hv
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact hwf _ (List.getElem_mem _)

/-- Two extracted vectors that agree entrywise below `k` represent the same `PolyVec`. -/
theorem toVec_ext {k : ℕ} {v w : linalg.PolyVec}
    (h : ∀ j, j < k → v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)
      = w.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) :
    toVec (k := k) v = toVec (k := k) w := by
  funext i
  simp only [toVec, h i.val i.isLt]

/-- The loop of `PolyVec::dot`: the accumulator is the partial sum over the indices
already visited. -/
theorem dot_loop_spec {k : ℕ} (u v : linalg.PolyVec) (n : Std.Usize)
    (acc : ring.Rq) (i : Std.Usize)
    (hu : WfVec k u) (hv : WfVec k v) (hn : n.val = k)
    (hi : i.val ≤ n.val) (hacc : Wf acc)
    (hval : toRq acc = ∑ j ∈ Finset.range i.val,
      toRq (u.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        * toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))) :
    linalg.PolyVec.dot_loop u v n acc i
      ⦃ z => Wf z ∧ toRq z = ∑ j ∈ Finset.range k,
        toRq (u.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          * toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [linalg.PolyVec.dot_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ Wf s.1 ∧
      toRq s.1 = ∑ j ∈ Finset.range s.2.val,
        toRq (u.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          * toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨a1, i1⟩ ⟨hi1, hacc1, hval1⟩
    dsimp only at hi1 hacc1 hval1
    simp only [linalg.PolyVec.dot_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hiu : i1.val < u.val.length := by rw [hu.1]; scalar_tac
      have hiv : i1.val < v.val.length := by rw [hv.1]; scalar_tac
      step as ⟨a, ha⟩
      have hWa : Wf a := by rw [ha]; exact hu.2 _ (List.getElem_mem hiu)
      step as ⟨b, hb⟩
      have hWb : Wf b := by rw [hb]; exact hv.2 _ (List.getElem_mem hiv)
      step as ⟨t, hWt, ht⟩
      step as ⟨a2, hWa2, ha2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, hWa2, ?_, ?_⟩
      · rw [ha2, hval1, ht, hi2, Finset.sum_range_succ,
          List.getD_eq_getElem _ _ hiu, List.getD_eq_getElem _ _ hiv, ha, hb]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨hacc1, by rw [hval1, heq, hn]⟩
  · exact ⟨hi, hacc, hval⟩

/-- `PolyVec::dot` — ArkLib's `dot`.

The two are not syntactically the same sum: the specification is
`(List.ofFn fun i => u i * v i).sum`, which is right-nested and ends in `0`, while
the Rust accumulates from the left. They agree because `Rq Φ` is a commutative
monoid under `+`, and `dot_eq_sum` is the bridge to the `Finset.sum` form the rest
of the specification uses. Equal lengths are a hypothesis: the Rust takes the
shorter of the two, which makes it total, and the specification's version is only
defined when they match. -/
theorem dot_spec {k : ℕ} (u v : linalg.PolyVec) (hu : WfVec k u) (hv : WfVec k v) :
    linalg.PolyVec.dot u v
      ⦃ z => Wf z ∧ toRq z = ArkLib.Lattices.dot (toVec (k := k) u) (toVec (k := k) v) ⦄ := by
  rw [linalg.PolyVec.dot]
  have hlen : (alloc.vec.Vec.len u).val = k := by simp [hu.1]
  have hlen' : (alloc.vec.Vec.len v).val = k := by simp [hv.1]
  simp only [if_pos (by scalar_tac : alloc.vec.Vec.len u ≤ alloc.vec.Vec.len v)]
  step as ⟨z0, hz0wf, hz0⟩
  apply spec_mono (dot_loop_spec u v (alloc.vec.Vec.len u) z0 0#usize hu hv hlen
    (by simp) hz0wf (by simp [hz0]))
  rintro z ⟨hzwf, hzval⟩
  refine ⟨hzwf, ?_⟩
  rw [hzval, ArkLib.Lattices.dot_eq_sum]
  exact (Fin.sum_univ_eq_sum_range
    (fun j => toRq (u.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
      * toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))) k).symm

/-- The loop of `PolyVec::add`: the accumulator holds the entrywise sums already
computed, and its length is the counter. -/
theorem vec_add_loop_spec {k : ℕ} (u rhs : linalg.PolyVec) (n : Std.Usize)
    (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hu : WfVec k u) (hv : WfVec k rhs) (hn : n.val = k)
    (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hwf : ∀ z ∈ out.val, Wf z)
    (hval : ∀ j, j < i.val →
      toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (u.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          + toRq (rhs.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))) :
    linalg.PolyVec.add_loop u rhs n out i
      ⦃ z => z.val.length = k ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < k → toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq (u.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
            + toRq (rhs.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [linalg.PolyVec.add_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.2.val)
    (fun s => s.1 = rhs ∧ s.2.2.val ≤ n.val ∧ s.2.1.val.length = s.2.2.val ∧
      (∀ y ∈ s.2.1.val, Wf y) ∧
      ∀ j, j < s.2.2.val → toRq (s.2.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (u.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          + toRq (rhs.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨r1, o1, i1⟩ ⟨hr1, hi1, hlen1, hwf1, hval1⟩
    dsimp only at hr1 hi1 hlen1 hwf1 hval1
    subst hr1
    simp only [linalg.PolyVec.add_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hiu : i1.val < u.val.length := by rw [hu.1]; scalar_tac
      have hir : i1.val < r1.val.length := by rw [hv.1]; scalar_tac
      step as ⟨a, ha⟩
      step as ⟨b, hb⟩
      have hWa : Wf a := by rw [ha]; exact hu.2 _ (List.getElem_mem hiu)
      have hWb : Wf b := by rw [hb]; exact hv.2 _ (List.getElem_mem hir)
      step as ⟨c, hWc, hc⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWc
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 j hjlt]
        · have hjeq : j = o1.val.length := by omega
          rw [hjeq, ho2, getD_append_eq, hc, hlen1,
            List.getD_eq_getElem _ _ hiu, List.getD_eq_getElem _ _ hir, ha, hb]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq, hn], hwf1, by intro j hj; exact hval1 j (by omega)⟩
  · exact ⟨rfl, hi, hlen, hwf, hval⟩

/-- `PolyVec::add` — the `Pi` instance. -/
theorem vec_add_spec {k : ℕ} (u v : linalg.PolyVec) (hu : WfVec k u) (hv : WfVec k v) :
    linalg.PolyVec.add u v
      ⦃ z => WfVec k z ∧ toVec (k := k) z = toVec (k := k) u + toVec (k := k) v ⦄ := by
  rw [linalg.PolyVec.add]
  simp only [bind_ok_id]
  apply spec_mono (vec_add_loop_spec u v (alloc.vec.Vec.len u)
    (alloc.vec.Vec.new ring.Rq) 0#usize hu hv (by simp [hu.1]) (by simp)
    (by simp) (by intro y hy; simp at hy) (by intro j hj; simp at hj))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i
  simp only [toVec, Pi.add_apply]
  exact hzval i.val i.isLt

/-- The loop of `PolyVec::sub`; the same invariant as `vec_add_loop_spec` with a
difference in place of the sum. -/
theorem vec_sub_loop_spec {k : ℕ} (u rhs : linalg.PolyVec) (n : Std.Usize)
    (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hu : WfVec k u) (hv : WfVec k rhs) (hn : n.val = k)
    (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hwf : ∀ z ∈ out.val, Wf z)
    (hval : ∀ j, j < i.val →
      toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (u.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          - toRq (rhs.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))) :
    linalg.PolyVec.sub_loop u rhs n out i
      ⦃ z => z.val.length = k ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < k → toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq (u.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
            - toRq (rhs.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [linalg.PolyVec.sub_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.2.val)
    (fun s => s.1 = rhs ∧ s.2.2.val ≤ n.val ∧ s.2.1.val.length = s.2.2.val ∧
      (∀ y ∈ s.2.1.val, Wf y) ∧
      ∀ j, j < s.2.2.val → toRq (s.2.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (u.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          - toRq (rhs.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨r1, o1, i1⟩ ⟨hr1, hi1, hlen1, hwf1, hval1⟩
    dsimp only at hr1 hi1 hlen1 hwf1 hval1
    subst hr1
    simp only [linalg.PolyVec.sub_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hiu : i1.val < u.val.length := by rw [hu.1]; scalar_tac
      have hir : i1.val < r1.val.length := by rw [hv.1]; scalar_tac
      step as ⟨a, ha⟩
      step as ⟨b, hb⟩
      have hWa : Wf a := by rw [ha]; exact hu.2 _ (List.getElem_mem hiu)
      have hWb : Wf b := by rw [hb]; exact hv.2 _ (List.getElem_mem hir)
      step as ⟨c, hWc, hc⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWc
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 j hjlt]
        · have hjeq : j = o1.val.length := by omega
          rw [hjeq, ho2, getD_append_eq, hc, hlen1,
            List.getD_eq_getElem _ _ hiu, List.getD_eq_getElem _ _ hir, ha, hb]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq, hn], hwf1, by intro j hj; exact hval1 j (by omega)⟩
  · exact ⟨rfl, hi, hlen, hwf, hval⟩

/-- `PolyVec::sub` — the `Pi` instance; the vector whose norm `sub_l2NormSq_le`
bounds. -/
theorem vec_sub_spec {k : ℕ} (u v : linalg.PolyVec) (hu : WfVec k u) (hv : WfVec k v) :
    linalg.PolyVec.sub u v
      ⦃ z => WfVec k z ∧ toVec (k := k) z = toVec (k := k) u - toVec (k := k) v ⦄ := by
  rw [linalg.PolyVec.sub]
  simp only [bind_ok_id]
  apply spec_mono (vec_sub_loop_spec u v (alloc.vec.Vec.len u)
    (alloc.vec.Vec.new ring.Rq) 0#usize hu hv (by simp [hu.1]) (by simp)
    (by simp) (by intro y hy; simp at hy) (by intro j hj; simp at hj))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i
  simp only [toVec, Pi.sub_apply]
  exact hzval i.val i.isLt

/-- The loop of `PolyVec::scalar_mul`: each entry written is `c` times the
corresponding entry of the input. -/
theorem scalar_vec_mul_loop_spec {k : ℕ} (v : linalg.PolyVec) (c : ring.Rq) (n : Std.Usize)
    (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hc : Wf c) (hv : WfVec k v) (hn : n.val = k)
    (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hwf : ∀ z ∈ out.val, Wf z)
    (hval : ∀ j, j < i.val →
      toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq c * toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))) :
    linalg.PolyVec.scalar_mul_loop v c n out i
      ⦃ z => z.val.length = k ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < k → toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq c * toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [linalg.PolyVec.scalar_mul_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      ∀ j, j < s.2.val → toRq (s.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq c * toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [linalg.PolyVec.scalar_mul_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hiv : i1.val < v.val.length := by rw [hv.1]; scalar_tac
      step as ⟨a, ha⟩
      have hWa : Wf a := by rw [ha]; exact hv.2 _ (List.getElem_mem hiv)
      step as ⟨b, hWb, hb⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWb
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 j hjlt]
        · have hjeq : j = o1.val.length := by omega
          rw [hjeq, ho2, getD_append_eq, hb, hlen1, List.getD_eq_getElem _ _ hiv, ha]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq, hn], hwf1, by intro j hj; exact hval1 j (by omega)⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- `PolyVec::scalar_mul` — ArkLib's `scalarVecMul`, the `cᵢ •ᵥ sᵢ` of the weak
verifier. -/
theorem scalar_vec_mul_spec {k : ℕ} (c : ring.Rq) (v : linalg.PolyVec)
    (hc : Wf c) (hv : WfVec k v) :
    linalg.PolyVec.scalar_mul v c
      ⦃ z => WfVec k z ∧ toVec (k := k) z = ArkLib.Lattices.scalarVecMul (toRq c)
        (toVec (k := k) v) ⦄ := by
  rw [linalg.PolyVec.scalar_mul]
  simp only [bind_ok_id]
  apply spec_mono (scalar_vec_mul_loop_spec v c (alloc.vec.Vec.len v)
    (alloc.vec.Vec.new ring.Rq) 0#usize hc hv (by simp [hv.1]) (by simp)
    (by simp) (by intro y hy; simp at hy) (by intro j hj; simp at hj))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i
  simp only [toVec, scalarVecMul]
  exact hzval i.val i.isLt

/-- Rows of a well-formed matrix are well-formed vectors. -/
theorem wfMat_row {rows cols : ℕ} {a : linalg.PolyMatrix} (ha : WfMat rows cols a)
    {j : ℕ} (hj : j < rows) :
    WfVec cols (a.val.getD j (alloc.vec.Vec.new ring.Rq)) := by
  obtain ⟨hlen, hrow⟩ := ha
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact hrow _ (List.getElem_mem _)

/-- The row a represented matrix has at `i` is the represented row. -/
theorem toMat_apply {rows cols : ℕ} (a : linalg.PolyMatrix) (i : Fin rows) :
    toMat (rows := rows) (cols := cols) a i
      = toVec (k := cols) (a.val.getD i.val (alloc.vec.Vec.new ring.Rq)) := rfl

/-- The loop of `PolyMatrix::mat_vec_mul`: entry `j` already written is the dot
product of row `j` with the input vector. -/
theorem mat_vec_mul_loop_spec {rows cols : ℕ} (a : linalg.PolyMatrix) (v : linalg.PolyVec)
    (n : Std.Usize) (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (ha : WfMat rows cols a) (hv : WfVec cols v) (hn : n.val = rows)
    (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hwf : ∀ z ∈ out.val, Wf z)
    (hval : ∀ j, j < i.val →
      toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ArkLib.Lattices.dot (toVec (k := cols) (a.val.getD j (alloc.vec.Vec.new ring.Rq)))
            (toVec (k := cols) v)) :
    linalg.PolyMatrix.mat_vec_mul_loop a v n out i
      ⦃ z => z.val.length = rows ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < rows → toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          = ArkLib.Lattices.dot (toVec (k := cols) (a.val.getD j (alloc.vec.Vec.new ring.Rq)))
              (toVec (k := cols) v) ⦄ := by
  rw [linalg.PolyMatrix.mat_vec_mul_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ j, j < s.2.val → toRq (s.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ArkLib.Lattices.dot (toVec (k := cols) (a.val.getD j (alloc.vec.Vec.new ring.Rq)))
            (toVec (k := cols) v))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [linalg.PolyMatrix.mat_vec_mul_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hia : i1.val < a.val.length := by rw [ha.1]; scalar_tac
      step as ⟨pv, hpv⟩
      have hWpv : WfVec cols pv := by
        rw [hpv]; exact ha.2 _ (List.getElem_mem hia)
      have hdot := dot_spec (k := cols) pv v hWpv hv
      step with hdot as ⟨r, hWr, hr⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 j hjlt]
        · have hjeq : j = o1.val.length := by omega
          rw [hjeq, ho2, getD_append_eq, hr, hlen1, List.getD_eq_getElem _ _ hia, hpv]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq, hn], hwf1, by intro j hj; exact hval1 j (by omega)⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- `PolyMatrix::mat_vec_mul` — ArkLib's `matVecMul`, and so the Ajtai commitment
itself: `Simple.commit Φ A s = A *ᵥ s`. -/
theorem mat_vec_mul_spec {rows cols : ℕ} (a : linalg.PolyMatrix) (v : linalg.PolyVec)
    (ha : WfMat rows cols a) (hv : WfVec cols v) :
    linalg.PolyMatrix.mat_vec_mul a v
      ⦃ z => WfVec rows z ∧ toVec (k := rows) z
        = ArkLib.Lattices.matVecMul (toMat (rows := rows) (cols := cols) a)
            (toVec (k := cols) v) ⦄ := by
  rw [linalg.PolyMatrix.mat_vec_mul]
  simp only [bind_ok_id]
  apply spec_mono (mat_vec_mul_loop_spec a v (alloc.vec.Vec.len a)
    (alloc.vec.Vec.new ring.Rq) 0#usize ha hv (by simp [ha.1]) (by simp)
    (by simp) (by intro y hy; simp at hy) (by intro j hj; simp at hj))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i
  rw [ArkLib.Lattices.matVecMul_apply, toMat_apply]
  exact hzval i.val i.isLt

/-- The inner loop of `flatten_blocks`: it appends the `width` entries of block `i`,
and every entry written so far — old or new — is the block-major entry it should be. -/
theorem flatten_blocks_inner_loop_spec {blocks width : ℕ} (xs : alloc.vec.Vec linalg.PolyVec)
    (out : alloc.vec.Vec ring.Rq) (i : Std.Usize) (wd : Std.Usize) (w : Std.Usize)
    (hxs : xs.val.length = blocks ∧ ∀ x ∈ xs.val, WfVec width x)
    (hsize : blocks * width ≤ Usize.max)
    (hi : i.val < blocks) (hwd : wd.val = width) (hw : w.val ≤ width)
    (hlen : out.val.length = i.val * width + w.val)
    (hwf : ∀ z ∈ out.val, Wf z)
    (hval : ∀ j, j < out.val.length →
      toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq ((xs.val.getD (j / width) (alloc.vec.Vec.new ring.Rq)).val.getD (j % width)
            (alloc.vec.Vec.new cpoly.field.Fp))) :
    linalg.flatten_blocks_loop0_loop0 xs out i wd w
      ⦃ z => z.val.length = i.val * width + width ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < z.val.length →
          toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
            = toRq ((xs.val.getD (j / width) (alloc.vec.Vec.new ring.Rq)).val.getD (j % width)
                (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [linalg.flatten_blocks_loop0_loop0]
  apply loop.spec_decr_nat (fun s => wd.val - s.2.val)
    (fun s => s.2.val ≤ width ∧ s.1.val.length = i.val * width + s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      ∀ j, j < s.1.val.length →
        toRq (s.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq ((xs.val.getD (j / width) (alloc.vec.Vec.new ring.Rq)).val.getD (j % width)
              (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, w1⟩ ⟨hw1, hlen1, hwf1, hval1⟩
    dsimp only at hw1 hlen1 hwf1 hval1
    simp only [linalg.flatten_blocks_loop0_loop0.body]
    by_cases hlt : w1 < wd
    · rw [if_pos hlt]
      have hwlt : w1.val < width := by rw [← hwd]; scalar_tac
      have hixs : i.val < xs.val.length := by rw [hxs.1]; exact hi
      step as ⟨pv, hpv⟩
      have hWpv : WfVec width pv := by
        rw [hpv]; exact hxs.2 _ (List.getElem_mem hixs)
      have hpvlen : w1.val < pv.val.length := by rw [hWpv.1]; exact hwlt
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hWpv.2 _ (List.getElem_mem hpvlen)
      step as ⟨r1, hWr1, hr1⟩
      have hbound : o1.val.length < Usize.max := by
        have h1 : (i.val + 1) * width ≤ blocks * width :=
          Nat.mul_le_mul_right width (by omega)
        have h2 : i.val * width + width = (i.val + 1) * width := by ring
        omega
      step as ⟨o2, ho2⟩
      step as ⟨w2, hw2⟩
      have hlen2 : o2.val.length = i.val * width + w1.val + 1 := by
        rw [ho2, List.length_append, hlen1]; simp
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · rw [hlen2, hw2]; omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · refine ⟨?_, ?_⟩
        · intro j hj
          rw [hlen2] at hj
          rcases Nat.lt_or_ge j o1.val.length with hjlt | hjge
          · rw [ho2, getD_append_lt _ _ _ hjlt]
            exact hval1 j hjlt
          · have hjeq : j = o1.val.length := by omega
            have hw0 : 0 < width := Nat.lt_of_le_of_lt (Nat.zero_le _) hwlt
            have hcomm : i.val * width + w1.val = w1.val + width * i.val := by ring
            have hdiv : (i.val * width + w1.val) / width = i.val := by
              rw [hcomm, Nat.add_mul_div_left _ _ hw0, Nat.div_eq_of_lt hwlt, Nat.zero_add]
            have hmod : (i.val * width + w1.val) % width = w1.val := by
              rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hwlt]
            rw [hjeq, ho2, getD_append_eq, hr1, hr, hlen1, hdiv, hmod,
              List.getD_eq_getElem _ _ hixs, ← hpv, List.getD_eq_getElem _ _ hpvlen]
        · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : w1.val = width := by
        have : wd.val ≤ w1.val := by scalar_tac
        omega
      exact ⟨by rw [hlen1, heq], hwf1, hval1⟩
  · exact ⟨hw, hlen, hwf, hval⟩

/-- The outer loop of `flatten_blocks`. -/
theorem flatten_blocks_outer_loop_spec {blocks width : ℕ} (xs : alloc.vec.Vec linalg.PolyVec)
    (nblocks : Std.Usize) (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hxs : xs.val.length = blocks ∧ ∀ x ∈ xs.val, WfVec width x)
    (hsize : blocks * width ≤ Usize.max)
    (hnb : nblocks.val = blocks) (hi : i.val ≤ blocks)
    (hlen : out.val.length = i.val * width)
    (hwf : ∀ z ∈ out.val, Wf z)
    (hval : ∀ j, j < out.val.length →
      toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq ((xs.val.getD (j / width) (alloc.vec.Vec.new ring.Rq)).val.getD (j % width)
            (alloc.vec.Vec.new cpoly.field.Fp))) :
    linalg.flatten_blocks_loop0 xs nblocks out i
      ⦃ z => z.val.length = blocks * width ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < z.val.length →
          toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
            = toRq ((xs.val.getD (j / width) (alloc.vec.Vec.new ring.Rq)).val.getD (j % width)
                (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [linalg.flatten_blocks_loop0]
  apply loop.spec_decr_nat (fun s => nblocks.val - s.2.val)
    (fun s => s.2.val ≤ blocks ∧ s.1.val.length = s.2.val * width ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      ∀ j, j < s.1.val.length →
        toRq (s.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq ((xs.val.getD (j / width) (alloc.vec.Vec.new ring.Rq)).val.getD (j % width)
              (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [linalg.flatten_blocks_loop0.body]
    by_cases hlt : i1 < nblocks
    · rw [if_pos hlt]
      have hilt : i1.val < blocks := by rw [← hnb]; scalar_tac
      have hixs : i1.val < xs.val.length := by rw [hxs.1]; exact hilt
      step as ⟨pv, hpv⟩
      have hWpv : WfVec width pv := by
        rw [hpv]; exact hxs.2 _ (List.getElem_mem hixs)
      simp only [linalg.PolyVec.len]
      have hwdw : (alloc.vec.Vec.len pv).val = width := by simpa using hWpv.1
      have hinner := flatten_blocks_inner_loop_spec (blocks := blocks) (width := width)
        xs o1 i1 (alloc.vec.Vec.len pv) 0#usize hxs hsize hilt hwdw (by simp)
        (by simp [hlen1]) hwf1 hval1
      step with hinner as ⟨o2, hlen2, hwf2, hval2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [hlen2, hi2]; ring
      · exact hwf2
      · exact hval2
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = blocks := by
        have : nblocks.val ≤ i1.val := by scalar_tac
        omega
      exact ⟨by rw [hlen1, heq], hwf1, hval1⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/- The original statement of `flatten_blocks_spec`, kept for the record:

theorem flatten_blocks_spec {blocks width : ℕ} (xs : alloc.vec.Vec linalg.PolyVec)
    (hxs : xs.val.length = blocks ∧ ∀ x ∈ xs.val, WfVec width x) :
    linalg.flatten_blocks xs
      ⦃ z => WfVec (blocks * width) z ∧ toVec (k := blocks * width) z
        = PolyVec.flattenBlocks (fun i : Fin blocks =>
            toVec (k := width) (xs.val.getD i.val (alloc.vec.Vec.new ring.Rq))) ⦄

It is *false* in this model: the flattened output has length `blocks * width`, and
`alloc.vec.Vec` carries the invariant `length ≤ Usize.max`, so the final `push`
can fail (`alloc.vec.Vec.push` returns `fail` on a full vector). The hypotheses
`xs.val.length = blocks` and `∀ x ∈ xs.val, WfVec width x` only bound `blocks` and
`width` separately by `Usize.max`, which does not bound their product. The
hypothesis `hsize : blocks * width ≤ Usize.max` below repairs it; on the concrete
dimensions this crate uses it is discharged by `decide`. -/

/-- `flatten_blocks` — ArkLib's `PolyVec.flattenBlocks`.

*Statement modified*: the hypothesis `hsize : blocks * width ≤ Usize.max` was added,
because the output vector has `blocks * width` entries and `alloc.vec.Vec` only
admits lengths up to `Usize.max`; without it the extracted code can fail on the
final `push`. See the comment above.

The content of this one is the index convention: `finProdFinEquiv (i, w)` is
`w + width · i`, so the flattening is block-major, and the Rust's concatenation is
that. Getting it transposed would leave every other statement here true and the
composition wrong, which is why it is stated against `flattenBlocks` directly
rather than against a hand-written index formula. -/
theorem flatten_blocks_spec {blocks width : ℕ} (xs : alloc.vec.Vec linalg.PolyVec)
    (hsize : blocks * width ≤ Usize.max)
    (hxs : xs.val.length = blocks ∧ ∀ x ∈ xs.val, WfVec width x) :
    linalg.flatten_blocks xs
      ⦃ z => WfVec (blocks * width) z ∧ toVec (k := blocks * width) z
        = PolyVec.flattenBlocks (fun i : Fin blocks =>
            toVec (k := width) (xs.val.getD i.val (alloc.vec.Vec.new ring.Rq))) ⦄ := by
  rw [linalg.flatten_blocks]
  simp only [bind_ok_id]
  apply spec_mono (flatten_blocks_outer_loop_spec xs (alloc.vec.Vec.len xs)
    (alloc.vec.Vec.new ring.Rq) 0#usize hxs hsize (by simp [hxs.1]) (by simp)
    (by simp) (by intro y hy; simp at hy) (by intro j hj; simp at hj))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext j
  have hj : j.val < z.val.length := by rw [hzlen]; exact j.isLt
  simp only [toVec, PolyVec.flattenBlocks, finProdFinEquiv_symm_apply, Fin.divNat, Fin.modNat]
  exact hzval j.val hj

/-! ## The gadget

The specification's digit decomposition is
`zmodDigitDecomposition b digits hb hq`, whose `digit c e` is
`((Nat.digits b c.val).getD e 0 : ZMod q)` — the ordinary base-`b` digits of the
canonical representative, *not* a balanced decomposition. `digit_at_spec` is
where that becomes a proof obligation, and it is the one genuinely arithmetic
statement in this file: the Rust divides `e` times and takes a remainder, and the
specification indexes into `Nat.digits`. The missing lemma is
`(Nat.digits b n).getD e 0 = n / b ^ e % b`, by induction on `e` with
`Nat.digits_def`. -/

/-- The instantiated digit decomposition at this crate's parameters. Its two side
conditions are `1 < b` and `q ≤ b ^ digits`, which `lean/Check.lean` § 1 checks of
the extracted constants. -/
def dd : DigitDecomposition (R := ZMod q) (2 : ZMod q) 32 :=
  zmodDigitDecomposition 2 32 (by norm_num) (by norm_num)

/-- The loop of `gadget::digit_at`: after `i` halvings the remaining word is
`c / 2ⁱ`. -/
theorem digit_at_loop_spec (e : Std.Usize) (rest : Std.U64) (i : Std.Usize) (c0 : ℕ)
    (hi : i.val ≤ e.val) (hrest : rest.val = c0 / 2 ^ i.val) :
    gadget.digit_at_loop e params.GADGET_BASE rest i
      ⦃ z => z.val = c0 / 2 ^ e.val ⦄ := by
  have hb : (params.GADGET_BASE).val = 2 := by simp [params.GADGET_BASE]
  rw [gadget.digit_at_loop]
  apply loop.spec_decr_nat (fun s => e.val - s.2.val)
    (fun s => s.2.val ≤ e.val ∧ s.1.val = c0 / 2 ^ s.2.val)
  · rintro ⟨r1, i1⟩ ⟨hi1, hval1⟩
    dsimp only at hi1 hval1
    simp only [gadget.digit_at_loop.body]
    by_cases hlt : i1 < e
    · rw [if_pos hlt]
      step as ⟨r2, hr2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [hr2, hval1, hb, hi2, Nat.div_div_eq_div_mul, ← pow_succ]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = e.val := by scalar_tac
      rw [hval1, heq]
  · exact ⟨hi, hrest⟩

/-- `gadget::digit_at` — the specification's `digit c e`, at every `e`: past the
length of `Nat.digits b c.val` the specification's `getD` returns its default and
the Rust's quotient has run out, so both are `0`. -/
theorem digit_at_spec (c : cpoly.field.Fp) (e : Std.Usize) (hc : Red c) (he : e.val < 32) :
    gadget.digit_at c e ⦃ d => Red d ∧ toK d = dd.digit (toK c) ⟨e.val, he⟩ ⦄ := by
  have hb : (params.GADGET_BASE).val = 2 := by simp [params.GADGET_BASE]
  have hcv : (toK c).val = c.val := by
    simp only [toK, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hc
  rw [gadget.digit_at]
  simp only [cpoly.field.Fp.to_u64]
  show (do
      let rest1 ← gadget.digit_at_loop e params.GADGET_BASE c 0#usize
      let i ← rest1 % params.GADGET_BASE
      cpoly.field.Fp.new i) ⦃ d => Red d ∧ toK d = dd.digit (toK c) ⟨e.val, he⟩ ⦄
  step with digit_at_loop_spec e c 0#usize c.val (by simp) (by simp) as ⟨r, hr⟩
  step as ⟨m, hm⟩
  step as ⟨d, hRd, hd⟩
  refine ⟨hRd, ?_⟩
  rw [hd, dd, zmodDigitDecomposition]
  dsimp only
  rw [hcv, Nat.getD_digits _ _ (by norm_num), hm, hr, hb]

/-- The loop of `gadget::base_pow`: the accumulator is `bⁱ` after `i` turns. -/
theorem base_pow_loop_spec (e : Std.Usize) (b : cpoly.field.Fp) (acc : cpoly.field.Fp)
    (i : Std.Usize) (hb : Red b) (hbv : toK b = (2 : ZMod q)) (hacc : Red acc)
    (hi : i.val ≤ e.val) (hval : toK acc = (2 : ZMod q) ^ i.val) :
    gadget.base_pow_loop e b acc i
      ⦃ p => Red p ∧ toK p = (2 : ZMod q) ^ e.val ⦄ := by
  rw [gadget.base_pow_loop]
  apply loop.spec_decr_nat (fun s => e.val - s.2.val)
    (fun s => s.2.val ≤ e.val ∧ Red s.1 ∧ toK s.1 = (2 : ZMod q) ^ s.2.val)
  · rintro ⟨a1, i1⟩ ⟨hi1, hR1, hval1⟩
    dsimp only at hi1 hR1 hval1
    simp only [gadget.base_pow_loop.body]
    by_cases hlt : i1 < e
    · rw [if_pos hlt]
      step as ⟨a2, hR2, ha2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, hR2, ?_, ?_⟩
      · rw [ha2, hval1, hbv, hi2, pow_succ]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = e.val := by scalar_tac
      exact ⟨hR1, by rw [hval1, heq]⟩
  · exact ⟨hi, hacc, hval⟩

/-- `gadget::base_pow` — `bᵉ` in `ZMod q`, not in `u64`: the specification's
exponent lives in the coefficient ring, and `b ^ e` passes the modulus at
`e = 32`. -/
theorem base_pow_spec (e : Std.Usize) :
    gadget.base_pow e ⦃ p => Red p ∧ toK p = (2 : ZMod q) ^ e.val ⦄ := by
  rw [gadget.base_pow]
  step as ⟨b, hRb, hb⟩
  have hbv : toK b = (2 : ZMod q) := by
    rw [hb]; simp [params.GADGET_BASE]
  exact base_pow_loop_spec e b cpoly.field.Fp.ONE 0#usize hRb hbv Red_one
    (by simp) (by simp)

/-- `gadget::gadget_entry` — ArkLib's `gadgetEntry`. -/
theorem gadget_entry_spec (i j : Std.Usize) :
    gadget.gadget_entry i j
      ⦃ z => Wf z ∧ ∀ (rows : ℕ) (hi : i.val < rows) (hj : j.val < rows * 32),
          toRq z = gadgetEntry Φ (2 : ZMod q) (rows := rows) (digits := 32)
            ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⦄ := by
  have hd : (params.GADGET_DIGITS).val = 32 := by simp [params.GADGET_DIGITS]
  rw [gadget.gadget_entry]
  step as ⟨i1, hi1⟩
  by_cases heq : i1 = i
  · rw [if_pos heq]
    step as ⟨j2, hj2⟩
    step with base_pow_spec j2 as ⟨f, hRf, hf⟩
    step as ⟨z, hWz, hz⟩
    refine ⟨hWz, ?_⟩
    intro rows hi hj
    have hcond : j.val / 32 = i.val := by rw [← hd, ← hi1, heq]
    rw [hz, hf, hj2, hd, gadgetEntry, if_pos hcond]
  · rw [if_neg heq]
    step as ⟨z, hWz, hz⟩
    refine ⟨hWz, ?_⟩
    intro rows hi hj
    have hcond : ¬ (j.val / 32 = i.val) := by
      intro h
      apply heq
      have : i1.val = i.val := by rw [hi1, hd, h]
      scalar_tac
    rw [hz, gadgetEntry, if_neg hcond]

/-- The inner loop of `gadget::gadget_mul`: the accumulator is the base-weighted sum
over the digit slots of block `i` already visited. -/
theorem gadget_mul_inner_loop_spec {rows : ℕ} (v : linalg.PolyVec) (dg : Std.Usize)
    (i : Std.Usize) (acc : ring.Rq) (e : Std.Usize)
    (hv : WfVec (rows * 32) v) (hdg : dg.val = 32) (hi : i.val < rows)
    (hacc : Wf acc) (he : e.val ≤ 32)
    (hval : toRq acc = ∑ t ∈ Finset.range e.val, Rq.constRq Φ ((2 : ZMod q) ^ t)
      * toRq (v.val.getD (t + 32 * i.val) (alloc.vec.Vec.new cpoly.field.Fp))) :
    gadget.gadget_mul_loop0_loop0 v dg i acc e
      ⦃ z => Wf z ∧ toRq z = ∑ t ∈ Finset.range 32, Rq.constRq Φ ((2 : ZMod q) ^ t)
        * toRq (v.val.getD (t + 32 * i.val) (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  have hvlen : rows * 32 ≤ Usize.max := by rw [← hv.1]; exact v.property
  have hib : 32 * i.val + 32 ≤ Usize.max := by
    have h1 : (i.val + 1) * 32 ≤ rows * 32 := Nat.mul_le_mul_right 32 (by omega)
    have h2 : (i.val + 1) * 32 = 32 * i.val + 32 := by ring
    omega
  rw [gadget.gadget_mul_loop0_loop0]
  apply loop.spec_decr_nat (fun s => dg.val - s.2.val)
    (fun s => s.2.val ≤ 32 ∧ Wf s.1 ∧
      toRq s.1 = ∑ t ∈ Finset.range s.2.val, Rq.constRq Φ ((2 : ZMod q) ^ t)
        * toRq (v.val.getD (t + 32 * i.val) (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨a1, e1⟩ ⟨he1, hW1, hval1⟩
    dsimp only at he1 hW1 hval1
    simp only [gadget.gadget_mul_loop0_loop0.body]
    by_cases hlt : e1 < dg
    · rw [if_pos hlt]
      have helt : e1.val < 32 := by rw [← hdg]; scalar_tac
      step as ⟨p, hp⟩
      step as ⟨p2, hp2⟩
      have hidx : p2.val = e1.val + 32 * i.val := by rw [hp2, hp, hdg]; ring
      have hlen : p2.val < v.val.length := by
        rw [hv.1, hidx]
        have : (i.val + 1) * 32 ≤ rows * 32 := Nat.mul_le_mul_right 32 (by omega)
        have h2 : (i.val + 1) * 32 = 32 * i.val + 32 := by ring
        omega
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hv.2 _ (List.getElem_mem hlen)
      step with base_pow_spec e1 as ⟨f, hRf, hf⟩
      step as ⟨scaled, hWs, hs⟩
      step as ⟨a2, hWa2, ha2⟩
      step as ⟨e2, he2⟩
      refine ⟨by scalar_tac, hWa2, ?_, ?_⟩
      · rw [ha2, hs, hf, hr, hval1, he2, Finset.sum_range_succ,
          ← List.getD_eq_getElem _ _ hlen, hidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : e1.val = 32 := by rw [← hdg]; scalar_tac
      exact ⟨hW1, by rw [hval1, heq]⟩
  · exact ⟨he, hacc, hval⟩

/-- The outer loop of `gadget::gadget_mul`: one accumulated row per block. -/
theorem gadget_mul_outer_loop_spec {rows : ℕ} (r : Std.Usize) (v : linalg.PolyVec)
    (dg : Std.Usize) (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hv : WfVec (rows * 32) v) (hdg : dg.val = 32) (hr : r.val = rows)
    (hi : i.val ≤ rows) (hlen : out.val.length = i.val)
    (hwf : ∀ z ∈ out.val, Wf z)
    (hval : ∀ j, j < i.val →
      toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ∑ t ∈ Finset.range 32, Rq.constRq Φ ((2 : ZMod q) ^ t)
            * toRq (v.val.getD (t + 32 * j) (alloc.vec.Vec.new cpoly.field.Fp))) :
    gadget.gadget_mul_loop0 r v dg out i
      ⦃ z => z.val.length = rows ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < rows → toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          = ∑ t ∈ Finset.range 32, Rq.constRq Φ ((2 : ZMod q) ^ t)
              * toRq (v.val.getD (t + 32 * j) (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [gadget.gadget_mul_loop0]
  apply loop.spec_decr_nat (fun s => r.val - s.2.val)
    (fun s => s.2.val ≤ rows ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ j, j < s.2.val → toRq (s.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ∑ t ∈ Finset.range 32, Rq.constRq Φ ((2 : ZMod q) ^ t)
            * toRq (v.val.getD (t + 32 * j) (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [gadget.gadget_mul_loop0.body]
    by_cases hlt : i1 < r
    · rw [if_pos hlt]
      have hilt : i1.val < rows := by rw [← hr]; scalar_tac
      step as ⟨z0, hWz0, hz0⟩
      have hinner := gadget_mul_inner_loop_spec (rows := rows) v dg i1 z0 0#usize
        hv hdg hilt hWz0 (by simp) (by simp [hz0])
      step with hinner as ⟨a1, hWa1, ha1⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWa1
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 j hjlt]
        · have hjeq : j = o1.val.length := by omega
          rw [hjeq, ho2, getD_append_eq, ha1, hlen1]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = rows := by rw [← hr]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, by intro j hj; exact hval1 j (by omega)⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- `gadget::gadget_mul` — ArkLib's `gadgetMul`, i.e. `gadgetMatrix *ᵥ v`.

The Rust computes the per-block digit sum directly. The bridge is the
specification's `gadgetMul_apply`: row `i` of the matrix product *is*
`Σ_{e} constRq (bᵉ) * v (finProdFinEquiv (i, e))`. -/
theorem gadget_mul_spec {rows : ℕ} (r : Std.Usize) (v : linalg.PolyVec)
    (hr : r.val = rows) (hv : WfVec (rows * 32) v) :
    gadget.gadget_mul r v
      ⦃ z => WfVec rows z ∧ toVec (k := rows) z
        = gadgetMul Φ (2 : ZMod q) (toVec (k := rows * 32) v) ⦄ := by
  have hdg : (params.GADGET_DIGITS).val = 32 := by simp [params.GADGET_DIGITS]
  rw [gadget.gadget_mul]
  simp only [linalg.PolyVec.new, bind_ok_id]
  apply spec_mono (gadget_mul_outer_loop_spec r v params.GADGET_DIGITS
    (alloc.vec.Vec.new ring.Rq) 0#usize hv hdg hr (by simp) (by simp)
    (by intro y hy; simp at hy) (by intro j hj; simp at hj))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i
  rw [gadgetMul_apply Φ (2 : ZMod q) (by norm_num)]
  simp only [toVec]
  rw [hzval i.val i.isLt]
  have hfp : ∀ x : Fin 32,
      ((finProdFinEquiv (i, x) : Fin (rows * 32)) : ℕ) = x.val + 32 * i.val := fun _ => rfl
  simp only [hfp]
  rw [Fin.sum_univ_eq_sum_range (fun t => Rq.constRq Φ ((2 : ZMod q) ^ t)
    * toRq (v.val.getD (t + 32 * i.val) (alloc.vec.Vec.new cpoly.field.Fp))) 32]

/-- `gadget::gadget_decompose` — ArkLib's `gadgetDecompose` at `dd`. -/
theorem gadget_decompose_spec {rows : ℕ} (x : linalg.PolyVec) (hx : WfVec rows x) :
    gadget.gadget_decompose x
      ⦃ z => WfVec (rows * 32) z ∧ toVec (k := rows * 32) z
        = gadgetDecompose Φ dd (toVec (k := rows) x) ⦄ := by
  sorry

/-- **The gadget is lawful**, as a statement about the *Rust*: the extracted
`gadget_mul` inverts the extracted `gadget_decompose`. A corollary of the two
specs above and the specification's `gadgetDecompose_lawful`, and the property the
scheme's correctness rests on. Worth stating separately because it is the one
claim about this layer a reader can check against the test suite
(`tests/gadget_semantics.rs::gadget_mul_inverts_gadget_decompose`). -/
theorem gadget_round_trip {rows : ℕ} (r : Std.Usize) (x : linalg.PolyVec)
    (hr : r.val = rows) (hx : WfVec rows x) :
    (do let d ← gadget.gadget_decompose x; gadget.gadget_mul r d)
      ⦃ z => WfVec rows z ∧ toVec (k := rows) z = toVec (k := rows) x ⦄ := by
  sorry

/-! ## The centered norms

The specification measures every coefficient through `ZMod.valMinAbs`, which sends
a residue to its representative in `(-q/2, q/2]`; `commit::centered_abs` folds the
upper half of `[0, q)` down instead. The two agree because `q` is odd, and that is
`centered_abs_spec`.

The `ℓ₂²` statements are about `Std.U128` for a reason that is part of the claim:
the specification sums in `ℕ`, which cannot overflow, and a `u64` accumulator
would *fail* in this model on inputs the verifier is supposed to reject. -/

/-- `commit::centered_abs` — `(c.valMinAbs).natAbs`. -/
theorem centered_abs_spec (c : cpoly.field.Fp) (hc : Red c) :
    commit.centered_abs c ⦃ n => n.val = (toK c).valMinAbs.natAbs ⦄ := by
  have hcv : (toK c).val = c.val := by
    simp only [toK, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hc
  have hmin : (toK c).valMinAbs
      = if c.val ≤ q / 2 then (c.val : ℤ) else (c.val : ℤ) - (q : ℤ) := by
    rw [ZMod.valMinAbs_def_pos, hcv]
  rw [commit.centered_abs]
  step as ⟨half, hhalf⟩
  show (if c ≤ half then ok c else params.Q - c) ⦃ n => n.val = (toK c).valMinAbs.natAbs ⦄
  by_cases hle : c ≤ half
  · rw [if_pos hle, WP.spec_ok]
    have hcle : c.val ≤ q / 2 := by scalar_tac
    rw [hmin, if_pos hcle]
    simp
  · rw [if_neg hle]
    step as ⟨r, hr⟩
    · simp only [params_Q_val]
      exact le_of_lt hc
    · have hcgt : ¬ c.val ≤ q / 2 := by scalar_tac
      rw [hmin, if_neg hcgt, hr]
      have hq : c.val ≤ q := le_of_lt hc
      simp only [params_Q_val]
      omega

/-- Every centered representative is at most `q / 2`, so a partial sum of `m` of them
is at most `m · (q / 2)`. The bound that keeps the `u64` accumulators of the norms
from overflowing. -/
theorem valMinAbs_sum_le (a : Rq Φ) (m : ℕ) :
    ∑ k ∈ Finset.range m, ((a.1.coeff k).valMinAbs.natAbs) ≤ m * (q / 2) := by
  have h := Finset.sum_le_card_nsmul (Finset.range m)
    (fun k => ((a.1.coeff k).valMinAbs.natAbs)) (q / 2)
    (fun x _ => ZMod.natAbs_valMinAbs_le _)
  simpa [Finset.card_range, mul_comm] using h

/-- The loop of `commit::l1_norm`: the accumulator is the partial sum of the centered
absolute values of the coefficients already visited. -/
theorem l1_norm_loop_spec (a : ring.Rq) (n : Std.Usize) (acc : Std.U64) (k : Std.Usize)
    (ha : Wf a) (hn : n.val = N) (hk : k.val ≤ n.val)
    (hacc : acc.val = ∑ j ∈ Finset.range k.val, ((toRq a).1.coeff j).valMinAbs.natAbs) :
    commit.l1_norm_loop a n acc k
      ⦃ z => z.val = ∑ j ∈ Finset.range N, ((toRq a).1.coeff j).valMinAbs.natAbs ⦄ := by
  rw [commit.l1_norm_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧
      s.1.val = ∑ j ∈ Finset.range s.2.val, ((toRq a).1.coeff j).valMinAbs.natAbs)
  · rintro ⟨a1, k1⟩ ⟨hk1, hval1⟩
    dsimp only at hk1 hval1
    simp only [commit.l1_norm_loop.body]
    by_cases hlt : k1 < n
    · rw [if_pos hlt]
      step as ⟨f, hRf, hf⟩
      step with centered_abs_spec f hRf as ⟨i, hi⟩
      have hbi : i.val ≤ q / 2 := by rw [hi]; exact ZMod.natAbs_valMinAbs_le _
      have hba : a1.val ≤ N * (q / 2) := by
        rw [hval1]
        exact le_trans (valMinAbs_sum_le (toRq a) k1.val)
          (Nat.mul_le_mul_right _ (by omega))
      step as ⟨a2, ha2⟩
      step as ⟨k2, hk2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [ha2, hval1, hi, hf, hk2, Finset.sum_range_succ]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = N := by rw [← hn]; scalar_tac
      rw [hval1, heq]
  · exact ⟨hk, hacc⟩

/-- `commit::l1_norm` — ArkLib's `Rq.l1Norm`. -/
theorem l1_norm_spec (a : ring.Rq) (ha : Wf a) :
    commit.l1_norm a ⦃ n => n.val = Rq.l1Norm Φ (toRq a) ⦄ := by
  rw [commit.l1_norm]
  apply spec_mono (l1_norm_loop_spec a params.RING_DEGREE 0#u64 0#usize ha
    (by simp [params_RING_DEGREE_val]) (by simp) (by simp))
  intro z hz
  rw [hz, Rq.l1Norm, phi_natDegree]

/-- The loop of `commit::l_infty_norm`: the running maximum is the supremum over the
coefficients already visited. -/
theorem l_infty_norm_loop_spec (a : ring.Rq) (n : Std.Usize) (best : Std.U64) (k : Std.Usize)
    (ha : Wf a) (hn : n.val = N) (hk : k.val ≤ n.val)
    (hbest : best.val
      = (Finset.range k.val).sup (fun j => ((toRq a).1.coeff j).valMinAbs.natAbs)) :
    commit.l_infty_norm_loop a n best k
      ⦃ z => z.val
        = (Finset.range N).sup (fun j => ((toRq a).1.coeff j).valMinAbs.natAbs) ⦄ := by
  rw [commit.l_infty_norm_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val
      = (Finset.range s.2.val).sup (fun j => ((toRq a).1.coeff j).valMinAbs.natAbs))
  · rintro ⟨b1, k1⟩ ⟨hk1, hval1⟩
    dsimp only at hk1 hval1
    simp only [commit.l_infty_norm_loop.body]
    by_cases hlt : k1 < n
    · rw [if_pos hlt]
      step as ⟨f, hRf, hf⟩
      step with centered_abs_spec f hRf as ⟨x, hx⟩
      have hite : (if x > b1 then ok x else ok b1)
          ⦃ z => z.val = max x.val b1.val ⦄ := by
        by_cases hgt : x > b1
        · rw [if_pos hgt, WP.spec_ok]
          have : b1.val ≤ x.val := by scalar_tac
          omega
        · rw [if_neg hgt, WP.spec_ok]
          have : x.val ≤ b1.val := by scalar_tac
          omega
      step with hite as ⟨b2, hb2⟩
      step as ⟨k2, hk2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [hk2, Finset.range_add_one, Finset.sup_insert, hb2, hval1, hx, hf]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = N := by rw [← hn]; scalar_tac
      rw [hval1, heq]
  · exact ⟨hk, hbest⟩

/-- `commit::l_infty_norm` — ArkLib's `Rq.lInftyNorm`. The Rust's running maximum
over an empty range is `0`, which is what the specification's `Finset.sup` gives
there too. -/
theorem l_infty_norm_spec (a : ring.Rq) (ha : Wf a) :
    commit.l_infty_norm a ⦃ n => n.val = Rq.lInftyNorm Φ (toRq a) ⦄ := by
  rw [commit.l_infty_norm]
  apply spec_mono (l_infty_norm_loop_spec a params.RING_DEGREE 0#u64 0#usize ha
    (by simp [params_RING_DEGREE_val]) (by simp) (by simp))
  intro z hz
  rw [hz, Rq.lInftyNorm, phi_natDegree]

/-- The squared analogue of `valMinAbs_sum_le`, for the `u128` accumulator of
`l2_norm_sq`. -/
theorem valMinAbs_sq_sum_le (a : Rq Φ) (m : ℕ) :
    ∑ k ∈ Finset.range m, ((a.1.coeff k).valMinAbs.natAbs) ^ 2 ≤ m * (q / 2) ^ 2 := by
  have h := Finset.sum_le_card_nsmul (Finset.range m)
    (fun k => ((a.1.coeff k).valMinAbs.natAbs) ^ 2) ((q / 2) ^ 2)
    (fun x _ => Nat.pow_le_pow_left (ZMod.natAbs_valMinAbs_le _) 2)
  simpa [Finset.card_range, mul_comm] using h

/-- The loop of `commit::l2_norm_sq`. -/
theorem l2_norm_sq_loop_spec (a : ring.Rq) (n : Std.Usize) (acc : Std.U128) (k : Std.Usize)
    (ha : Wf a) (hn : n.val = N) (hk : k.val ≤ n.val)
    (hacc : acc.val = ∑ j ∈ Finset.range k.val, ((toRq a).1.coeff j).valMinAbs.natAbs ^ 2) :
    commit.l2_norm_sq_loop a n acc k
      ⦃ z => z.val = ∑ j ∈ Finset.range N, ((toRq a).1.coeff j).valMinAbs.natAbs ^ 2 ⦄ := by
  rw [commit.l2_norm_sq_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧
      s.1.val = ∑ j ∈ Finset.range s.2.val, ((toRq a).1.coeff j).valMinAbs.natAbs ^ 2)
  · rintro ⟨a1, k1⟩ ⟨hk1, hval1⟩
    dsimp only at hk1 hval1
    simp only [commit.l2_norm_sq_loop.body]
    by_cases hlt : k1 < n
    · rw [if_pos hlt]
      step as ⟨f, hRf, hf⟩
      step with centered_abs_spec f hRf as ⟨i, hi⟩
      have hbi : i.val ≤ q / 2 := by rw [hi]; exact ZMod.natAbs_valMinAbs_le _
      have hba : a1.val ≤ N * (q / 2) ^ 2 := by
        rw [hval1]
        exact le_trans (valMinAbs_sq_sum_le (toRq a) k1.val)
          (Nat.mul_le_mul_right _ (by omega))
      have hcast : lift (UScalar.cast .U128 i) ⦃ y => y.val = i.val ⦄ :=
        UScalar.cast_inBounds_spec .U128 i (by scalar_tac)
      step with hcast as ⟨x, hx⟩
      step as ⟨y, hy⟩
      step as ⟨a2, ha2⟩
      step as ⟨k2, hk2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [ha2, hy, hx, hval1, hi, hf, hk2, Finset.sum_range_succ, sq]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = N := by rw [← hn]; scalar_tac
      rw [hval1, heq]
  · exact ⟨hk, hacc⟩

/-- `commit::l2_norm_sq` — ArkLib's `Rq.l2NormSq`, and total: `u128` is wide
enough for `N · (q/2)²`. -/
theorem l2_norm_sq_spec (a : ring.Rq) (ha : Wf a) :
    commit.l2_norm_sq a ⦃ n => n.val = Rq.l2NormSq Φ (toRq a) ⦄ := by
  rw [commit.l2_norm_sq]
  apply spec_mono (l2_norm_sq_loop_spec a params.RING_DEGREE 0#u128 0#usize ha
    (by simp [params_RING_DEGREE_val]) (by simp) (by simp))
  intro z hz
  rw [hz, Rq.l2NormSq, phi_natDegree]

/-- The `ℓ₂²` norm of a single ring element never exceeds `N · (q/2)²`. -/
theorem l2NormSq_le (x : Rq Φ) : Rq.l2NormSq Φ x ≤ N * (q / 2) ^ 2 := by
  rw [Rq.l2NormSq, phi_natDegree]
  exact valMinAbs_sq_sum_le x N

/-- The partial sums of the entrywise `ℓ₂²` norms of a vector, bounded entry by entry.
What keeps the `u128` accumulator of `vec_l2_norm_sq` inside its range. -/
theorem vec_l2NormSq_sum_le (v : linalg.PolyVec) (m : ℕ) :
    ∑ j ∈ Finset.range m,
        Rq.l2NormSq Φ (toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))
      ≤ m * (N * (q / 2) ^ 2) := by
  have h := Finset.sum_le_card_nsmul (Finset.range m)
    (fun j => Rq.l2NormSq Φ (toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))))
    (N * (q / 2) ^ 2) (fun x _ => l2NormSq_le _)
  simpa [Finset.card_range, mul_comm] using h

/-- The loop of `commit::vec_l2_norm_sq`. -/
theorem vec_l2_norm_sq_loop_spec {k : ℕ} (v : linalg.PolyVec) (n : Std.Usize)
    (acc : Std.U128) (i : Std.Usize) (hv : WfVec k v)
    (hsize : k * (N * (q / 2) ^ 2) ≤ U128.max)
    (hn : n.val = k) (hi : i.val ≤ n.val)
    (hacc : acc.val = ∑ j ∈ Finset.range i.val,
      Rq.l2NormSq Φ (toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))) :
    commit.vec_l2_norm_sq_loop v n acc i
      ⦃ z => z.val = ∑ j ∈ Finset.range k,
        Rq.l2NormSq Φ (toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))) ⦄ := by
  rw [commit.vec_l2_norm_sq_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val = ∑ j ∈ Finset.range s.2.val,
      Rq.l2NormSq Φ (toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))))
  · rintro ⟨a1, i1⟩ ⟨hi1, hval1⟩
    dsimp only at hi1 hval1
    simp only [commit.vec_l2_norm_sq_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hilt : i1.val < v.val.length := by rw [hv.1, ← hn]; scalar_tac
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hv.2 _ (List.getElem_mem hilt)
      step with l2_norm_sq_spec r hWr as ⟨x, hx⟩
      have hbx : x.val ≤ N * (q / 2) ^ 2 := by rw [hx]; exact l2NormSq_le _
      have hba : a1.val ≤ i1.val * (N * (q / 2) ^ 2) := by
        rw [hval1]; exact vec_l2NormSq_sum_le v i1.val
      have hbnd : a1.val + x.val ≤ U128.max := by
        have h1 : (i1.val + 1) * (N * (q / 2) ^ 2) ≤ k * (N * (q / 2) ^ 2) :=
          Nat.mul_le_mul_right _ (by rw [← hn]; scalar_tac)
        have h2 : (i1.val + 1) * (N * (q / 2) ^ 2)
            = i1.val * (N * (q / 2) ^ 2) + (N * (q / 2) ^ 2) := by ring
        omega
      step as ⟨a2, ha2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [ha2, hval1, hx, hr, hi2, Finset.sum_range_succ,
          List.getD_eq_getElem _ _ hilt]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = k := by rw [← hn]; scalar_tac
      rw [hval1, heq]
  · exact ⟨hi, hacc⟩

/- The original statement of `vec_l2_norm_sq_spec`, kept for the record:

theorem vec_l2_norm_sq_spec {k : ℕ} (v : linalg.PolyVec) (hv : WfVec k v) :
    commit.vec_l2_norm_sq v ⦃ n => n.val = vecL2NormSq Φ (toVec (k := k) v) ⦄

It is *false* in this model, for the reason its own docstring gives in reverse: the
accumulator is a `u128`, and while that is wide enough for one ring element's
`ℓ₂²` norm (`N · (q/2)² < 2^68`), a `PolyVec` in this model may have up to
`Usize.max` entries, and `Usize.max · N · (q/2)²` exceeds `U128.max` when `usize`
is 64 bits. The hypothesis `hsize` below is exactly the absence of that overflow;
at the concrete dimensions of the crate it is a numeral inequality. -/

/-- `commit::vec_l2_norm_sq` — ArkLib's `vecL2NormSq`.

*Statement modified*: the hypothesis `hsize : k * (N * (q / 2) ^ 2) ≤ U128.max` was
added, since for a vector with more than about `2^60` entries the `u128`
accumulator can overflow. See the comment above. -/
theorem vec_l2_norm_sq_spec {k : ℕ} (v : linalg.PolyVec) (hv : WfVec k v)
    (hsize : k * (N * (q / 2) ^ 2) ≤ U128.max) :
    commit.vec_l2_norm_sq v ⦃ n => n.val = vecL2NormSq Φ (toVec (k := k) v) ⦄ := by
  rw [commit.vec_l2_norm_sq]
  simp only [linalg.PolyVec.len]
  apply spec_mono (vec_l2_norm_sq_loop_spec v (alloc.vec.Vec.len v) 0#u128 0#usize hv
    hsize (by simpa using hv.1) (by simp) (by simp))
  intro z hz
  rw [hz, vecL2NormSq]
  simp only [toVec]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => Rq.l2NormSq Φ (toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))) k]

/-- A supremum over `Finset.range k` is the supremum over `Fin k` of the same
function: the shape the vector norms are stated in, on the two sides. -/
theorem sup_range_eq_sup_univ {k : ℕ} (f : ℕ → ℕ) :
    (Finset.range k).sup f = Finset.univ.sup (fun i : Fin k => f i.val) := by
  apply le_antisymm
  · refine Finset.sup_le fun j hj => ?_
    exact Finset.le_sup (f := fun i : Fin k => f i.val)
      (Finset.mem_univ (⟨j, Finset.mem_range.mp hj⟩ : Fin k))
  · exact Finset.sup_le fun i _ => Finset.le_sup (Finset.mem_range.mpr i.isLt)

/-- The loop of `commit::vec_l_infty_norm`. -/
theorem vec_l_infty_norm_loop_spec {k : ℕ} (v : linalg.PolyVec) (n : Std.Usize)
    (best : Std.U64) (i : Std.Usize) (hv : WfVec k v) (hn : n.val = k) (hi : i.val ≤ n.val)
    (hbest : best.val = (Finset.range i.val).sup
      (fun j => Rq.lInftyNorm Φ (toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))))) :
    commit.vec_l_infty_norm_loop v n best i
      ⦃ z => z.val = (Finset.range k).sup
        (fun j => Rq.lInftyNorm Φ (toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))) ⦄ := by
  rw [commit.vec_l_infty_norm_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val = (Finset.range s.2.val).sup
      (fun j => Rq.lInftyNorm Φ (toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))))
  · rintro ⟨b1, i1⟩ ⟨hi1, hval1⟩
    dsimp only at hi1 hval1
    simp only [commit.vec_l_infty_norm_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hilt : i1.val < v.val.length := by rw [hv.1, ← hn]; scalar_tac
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hv.2 _ (List.getElem_mem hilt)
      step with l_infty_norm_spec r hWr as ⟨x, hx⟩
      have hite : (if x > b1 then ok x else ok b1)
          ⦃ z => z.val = max x.val b1.val ⦄ := by
        by_cases hgt : x > b1
        · rw [if_pos hgt, WP.spec_ok]
          have : b1.val ≤ x.val := by scalar_tac
          omega
        · rw [if_neg hgt, WP.spec_ok]
          have : x.val ≤ b1.val := by scalar_tac
          omega
      step with hite as ⟨b2, hb2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [hi2, Finset.range_add_one, Finset.sup_insert, hb2, hval1, hx, hr,
          List.getD_eq_getElem _ _ hilt]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = k := by rw [← hn]; scalar_tac
      rw [hval1, heq]
  · exact ⟨hi, hbest⟩

/-- `commit::vec_l_infty_norm` — ArkLib's `vecLInftyNorm`, the `‖t̂‖∞ ≤ γ` of the
weak verifier. -/
theorem vec_l_infty_norm_spec {k : ℕ} (v : linalg.PolyVec) (hv : WfVec k v) :
    commit.vec_l_infty_norm v ⦃ n => n.val = vecLInftyNorm Φ (toVec (k := k) v) ⦄ := by
  rw [commit.vec_l_infty_norm]
  simp only [linalg.PolyVec.len]
  apply spec_mono (vec_l_infty_norm_loop_spec v (alloc.vec.Vec.len v) 0#u64 0#usize hv
    (by simpa using hv.1) (by simp) (by simp))
  intro z hz
  rw [hz, vecLInftyNorm, sup_range_eq_sup_univ]
  rfl

/-! ## The commitment

The specification's scheme is generic in six dimensions; these statements fix them
at `params.rs`'s values. `WfParams` and `WfDecomp` are the shape conditions that
make the two sides comparable at all -- the extracted structures carry `Vec`s
whose lengths nothing in the type system pins. -/

/-- Shape invariant of the public parameters: the two Ajtai matrices are of the
shapes `PublicParams` fixes. -/
def WfParams (pp : commit.PublicParams) : Prop :=
  WfMat 2 (4 * 32) pp.inner_matrix ∧ WfMat 2 (2 * (2 * 32)) pp.outer_matrix

/-- Shape invariant of the decomposition data. -/
def WfDecomp (d : commit.Decomp) : Prop :=
  (d.message.val.length = 2 ∧ ∀ s ∈ d.message.val, WfVec (4 * 32) s) ∧
  (d.inner_decomp.val.length = 2 ∧ ∀ t ∈ d.inner_decomp.val, WfVec (2 * 32) t)

/-- The specification's public parameters that an extracted `PublicParams`
represents. -/
def toParams (pp : commit.PublicParams) : InnerOuter.PublicParams Φ 2 4 32 2 2 32 where
  innerMatrix := toMat (rows := 2) (cols := 4 * 32) pp.inner_matrix
  outerMatrix := toMat (rows := 2) (cols := 2 * (2 * 32)) pp.outer_matrix

/-- The specification's decomposition data that an extracted `Decomp` represents. -/
def toDecompSpec (d : commit.Decomp) : InnerOuter.Decomp Φ 2 4 32 2 32 where
  message := fun i => toVec (k := 4 * 32) (d.message.val.getD i.val
    (alloc.vec.Vec.new ring.Rq))
  innerDecomp := fun i => toVec (k := 2 * 32) (d.inner_decomp.val.getD i.val
    (alloc.vec.Vec.new ring.Rq))

/-- The specification's weak opening that an extracted `Opening` represents. -/
def toOpening (o : commit.Opening) : InnerOuter.Opening Φ 2 4 32 2 32 where
  toDecomp := toDecompSpec o.decomp
  challenge := toVec (k := 2) o.challenge

/-- `commit::generate_decomps` — ArkLib's `generateDecomps` at
`Decomposition.ofDigits dd dd`: per block `sᵢ = G⁻¹(mᵢ)` and `t̂ᵢ = G⁻¹(A sᵢ)`.

Both halves matter. The shape half (`WfDecomp`) is what the layer above needs to
apply anything; the agreement half is what makes it the specification's
decomposition and not merely a decomposition of the right shape. -/
theorem generate_decomps_spec (pp : commit.PublicParams) (m : alloc.vec.Vec linalg.PolyVec)
    (hpp : WfParams pp) (hm : m.val.length = 2 ∧ ∀ x ∈ m.val, WfVec 4 x) :
    commit.generate_decomps pp m
      ⦃ d => WfDecomp d ∧ toDecompSpec d
        = InnerOuter.generateDecomps Φ (InnerOuter.Decomposition.ofDigits Φ dd dd)
            (toParams pp)
            (fun i : Fin 2 => toVec (k := 4) (m.val.getD i.val
              (alloc.vec.Vec.new ring.Rq))) ⦄ := by
  sorry

/-- `commit::derived_message` — ArkLib's `derivedMessage`, `mᵢ = G · sᵢ`
([NOZ26] Eq. (13)): the message a weak opening does not store but determines. -/
theorem derived_message_spec (d : commit.Decomp) (hd : WfDecomp d) :
    commit.derived_message d
      ⦃ out => (out.val.length = 2 ∧ ∀ x ∈ out.val, WfVec 4 x) ∧
        (fun i : Fin 2 => toVec (k := 4) (out.val.getD i.val (alloc.vec.Vec.new ring.Rq)))
          = InnerOuter.derivedMessage Φ (2 : ZMod q) (toDecompSpec d) ⦄ := by
  sorry

/-- `commit::commit_with_decomps` — ArkLib's `commitWithDecomps`,
`u = B · flatten(t̂)`. -/
theorem commit_with_decomps_spec (pp : commit.PublicParams) (d : commit.Decomp)
    (hpp : WfParams pp) (hd : WfDecomp d) :
    commit.commit_with_decomps pp d
      ⦃ u => WfVec 2 u ∧ toVec (k := 2) u
        = InnerOuter.commitWithDecomps Φ (toParams pp) (toDecompSpec d) ⦄ := by
  sorry

/-- `commit::verify_weak` — ArkLib's `verify_weak`, as an equality of *decisions*.

An equality of `Bool`s, not an implication: an implication in the accepting
direction is satisfied by a verifier that rejects everything, and that is exactly
the failure a correctness test cannot see. The specification's `verify_weak` is
itself `Bool`-valued (a `&&` of `List.all` over eagerly-`decide`d propositions),
which is why no `decide` appears on either side.

The three bounds are `params.rs`'s: `βSq = 8192`, `γ = 1`, `κ = 65535`. They are
the numbers `lean/Check.lean` § 1 ties to the extracted constants, so this
statement and the Rust cannot disagree about them without that audit failing. -/
theorem verify_weak_spec (pp : commit.PublicParams) (u : linalg.PolyVec)
    (o : commit.Opening) (hpp : WfParams pp) (hu : WfVec 2 u) (ho : WfDecomp o.decomp) :
    commit.verify_weak pp u o
      ⦃ r => r = InnerOuter.verify_weak Φ (2 : ZMod q) 8192 1 65535
        (toParams pp) (toVec (k := 2) u) (toOpening o) ⦄ := by
  sorry

/-- **Perfect correctness of the extracted scheme**: an honest commitment and its
honest opening verify. The computational content of ArkLib's
`InnerOuter.Correctness.perfectlyCorrect`, and the statement the test
`tests/commit_semantics.rs::honest_commitments_verify` checks by example.

Stated as a single `do` block rather than as three composed specs because that is
what the honest committer actually runs, and because the challenge the honest
committer supplies (`cᵢ = 1`) is part of the claim: it is admissible only because
`‖1‖₁ = 1` sits inside `0 < ‖c‖₁ ≤ κ`, which is a fact about `params.rs`'s `κ`
and not about the scheme. -/
theorem honest_verifies (pp : commit.PublicParams) (m : alloc.vec.Vec linalg.PolyVec)
    (hpp : WfParams pp) (hm : m.val.length = 2 ∧ ∀ x ∈ m.val, WfVec 4 x) :
    (do
      let (u, d) ← commit.commit pp m
      let o ← commit.Opening.honest d
      commit.verify_weak pp u o) ⦃ r => r = true ⦄ := by
  sorry

end HachiEquiv.Scheme
