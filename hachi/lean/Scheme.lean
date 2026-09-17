/-
The **upper layers** of the equivalence: linear algebra, the gadget, and the
inner-outer commitment. Proved, on the bridge from `Ring.lean`, and part of the
audited library -- `lean/Check.lean` § 4 prints the axiom dependencies of every
headline spec below, so a `sorry` here is a `make build` failure.

## Why the statements are the deliverable

Each theorem below fixes what the corresponding Rust function has to mean, in the
specification's own vocabulary. That was worth having before any proof existed --
it is where a mistranslation shows up -- and it is still what the proofs are worth:
a proof is only as strong as the statement it closes. Two of them earn their place
on the statement alone, because writing them down is what settled a design question
in the Rust:

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

theorem dot_spec {k : ℕ} (u v : linalg.PolyVec) (hu : WfVec k u) (hv : WfVec k v) :
    linalg.PolyVec.dot u v
      ⦃ z => Wf z ∧ toRq z = ArkLib.Lattices.dot (toVec (k := k) u) (toVec (k := k) v) ⦄ := by
  rw [linalg.PolyVec.dot]
  have hlen : (alloc.vec.Vec.len u).val = k := by simp [hu.1]
  have hlen' : (alloc.vec.Vec.len v).val = k := by simp [hv.1]
  simp only [if_pos (by scalar_tac : alloc.vec.Vec.len u ≤ alloc.vec.Vec.len v)]
  -- `dot` now delegates to `ring::dot_fused`, whose statement this one is
  apply spec_mono (HachiEquiv.RqBridge.dot_fused_spec u v (alloc.vec.Vec.len u)
    (by
      intro j hj
      rw [hlen] at hj
      rw [List.getD_eq_getElem _ _ (by rw [hu.1]; exact hj)]
      exact hu.2 _ (List.getElem_mem _))
    (by
      intro j hj
      rw [hlen] at hj
      rw [List.getD_eq_getElem _ _ (by rw [hv.1]; exact hj)]
      exact hv.2 _ (List.getElem_mem _))
    (by rw [hlen, hu.1]) (by rw [hlen, hv.1]))
  rintro z ⟨hzwf, hzval⟩
  refine ⟨hzwf, ?_⟩
  rw [hzval, hlen, ArkLib.Lattices.dot_eq_sum]
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

/-! ### The prepared matrix-vector product

`PolyMatrix::prepare` forward-transforms every entry of a matrix once;
`PreparedMatrix::apply` then only multiplies pointwise and inverts. The value is
unchanged -- `apply_spec` below concludes *exactly* what `mat_vec_mul_spec`
concludes, so no caller's specification moves -- and what changes is that a row's
twist and forward transform are paid once for the whole matrix instead of once
per matrix-vector product.

`mat_vec_mul` itself is deliberately **not** rewired: the prepared tables are
`rows * cols * 3 * N * 8` bytes, which is 192 MiB for the Ajtai matrix `A`
(1 x 8192) but 4.8 GiB for `rlin_stmt`'s `M` (5 x 40976). The choice is per
caller, and `hachi/src/linalg.rs` records it at `PolyMatrix::prepare`. -/

/-- A `usize` holds at least `2 ^ 32 - 1`. `Usize.max` is platform-dependent in
the Aeneas model, so a concrete bound has to come from somewhere; this is the
same fact `Sumcheck.usize_max_ge` states, restated here because that file sits
above this one in the import graph. -/
theorem usize_max_ge' : 4294967295 ≤ Usize.max := by
  rw [Usize.max_def]
  rcases System.Platform.numBits_eq with h | h <;> simp [Usize.numBits, h]

/-- `ring::dot_prepared` at the specification level: the same `ArkLib` dot product
`dot_spec` computes, for a left operand supplied in prepared form. -/
theorem dot_prep_spec {k : ℕ} (prep : ring.PreparedVec) (u v : linalg.PolyVec)
    (nU : Std.Usize) (hn : nU.val = k) (hu : WfVec k u) (hv : WfVec k v)
    (hprep : PrepRow k prep u) :
    ring.dot_prepared prep v nU
      ⦃ z => Wf z ∧ toRq z
        = ArkLib.Lattices.dot (toVec (k := k) u) (toVec (k := k) v) ⦄ := by
  apply spec_mono (HachiEquiv.RqBridge.dot_prepared_spec prep u v nU
    (by intro j hj; rw [hn] at hj; exact wf_getD hu hj)
    (by intro j hj; rw [hn] at hj; exact wf_getD hv hj)
    (by rw [hn, hu.1]) (by rw [hn, hv.1]) (by rw [hn]; exact hprep))
  rintro z ⟨hzwf, hzval⟩
  refine ⟨hzwf, ?_⟩
  rw [hzval, hn, ArkLib.Lattices.dot_eq_sum]
  exact (Fin.sum_univ_eq_sum_range
    (fun j => toRq (u.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
      * toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))) k).symm

/-- `pm` is the prepared form of `m`: the same shape, and every row prepared. -/
def WfPrep (rows cols : ℕ) (pm : linalg.PreparedMatrix) (m : linalg.PolyMatrix) : Prop :=
  pm.cols.val = cols ∧ pm.rows.val.length = rows
  ∧ ∀ i, i < rows → PrepRow cols (pm.rows.val.getD i prepJunk)
      (m.val.getD i (alloc.vec.Vec.new ring.Rq))

/-- `PolyMatrix::cols` reads the width off row 0, so it answers for a matrix that
has one. (The `rows = 0` case returns 0 and is not used: a prepared matrix with no
rows prepares nothing.) -/
theorem cols_spec {rows cols : ℕ} (m : linalg.PolyMatrix) (ha : WfMat rows cols m)
    (hrows : 0 < rows) : linalg.PolyMatrix.cols m ⦃ c => c.val = cols ⦄ := by
  have hlen : (alloc.vec.Vec.len m).val = rows := by simp [ha.1]
  have h0 : (0 : ℕ) < m.val.length := by rw [ha.1]; exact hrows
  rw [linalg.PolyMatrix.cols]
  simp only [if_neg (by scalar_tac : ¬ (alloc.vec.Vec.len m = 0#usize))]
  step as ⟨pv, hpv⟩
  rw [linalg.PolyVec.len, WP.spec_ok]
  have hW : WfVec cols pv := by rw [hpv]; exact ha.2 _ (List.getElem_mem h0)
  simp [hW.1]

/-- The loop of `PolyMatrix::prepare`: after `i` rows the table holds `i` prepared
rows, each the prepared form of the matrix row at the same index. -/
theorem prepare_loop_spec {rows cols : ℕ} (m : linalg.PolyMatrix)
    (n c : Std.Usize) (rws : alloc.vec.Vec ring.PreparedVec) (i : Std.Usize)
    (ha : WfMat rows cols m) (hn : n.val = rows) (hc : c.val = cols)
    (hmax : cols * N ≤ Std.Usize.max)
    (hi : i.val ≤ n.val) (hlen : rws.val.length = i.val)
    (hval : ∀ u, u < i.val → PrepRow cols (rws.val.getD u prepJunk)
      (m.val.getD u (alloc.vec.Vec.new ring.Rq))) :
    linalg.PolyMatrix.prepare_loop m n c rws i
      ⦃ z => z.val.length = rows ∧ ∀ u, u < rows →
          PrepRow cols (z.val.getD u prepJunk)
            (m.val.getD u (alloc.vec.Vec.new ring.Rq)) ⦄ := by
  rw [linalg.PolyMatrix.prepare_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val
      ∧ ∀ u, u < s.2.val → PrepRow cols (s.1.val.getD u prepJunk)
          (m.val.getD u (alloc.vec.Vec.new ring.Rq)))
  · rintro ⟨r1, i1⟩ ⟨hi1, hlen1, hval1⟩
    dsimp only at hi1 hlen1 hval1
    simp only [linalg.PolyMatrix.prepare_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have him : i1.val < m.val.length := by rw [ha.1, ← hn]; scalar_tac
      step as ⟨pv, hpv⟩
      have hWpv : WfVec cols pv := by rw [hpv]; exact ha.2 _ (List.getElem_mem him)
      have hmi : m.val.getD i1.val (alloc.vec.Vec.new ring.Rq) = pv := by
        rw [hpv]; exact List.getD_eq_getElem _ _ him
      step with HachiEquiv.AuxFused.prepare_vec_spec pv c
        (by intro u hu; rw [hc] at hu; exact wf_getD hWpv hu)
        (by rw [hc, hWpv.1]) (by rw [hc]; exact hmax) as ⟨p, hpl, hp1, hp2, hp3⟩
      step as ⟨r2, hr2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · rw [hr2, hi2, List.length_append, hlen1]; simp
      · intro u hu
        rw [hi2] at hu
        rcases Nat.lt_or_ge u i1.val with hult | huge
        · rw [hr2, getD_append_lt _ _ _ (by omega)]
          exact hval1 u hult
        · have hueq : u = r1.val.length := by omega
          rw [hueq, hr2, getD_append_eq, hlen1, hmi]
          refine ⟨by rw [hpl]; exact hc, ?_, ?_, ?_⟩
          · rw [← hc]; exact hp1
          · rw [← hc]; exact hp2
          · rw [← hc]; exact hp3
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq, hn], by intro u hu; exact hval1 u (by rw [heq, hn]; exact hu)⟩
  · exact ⟨hi, hlen, hval⟩

/-- `PolyMatrix::prepare` — the prepared form of the matrix it is given. -/
theorem prepare_spec {rows cols : ℕ} (m : linalg.PolyMatrix)
    (ha : WfMat rows cols m) (hrows : 0 < rows) (hmax : cols * N ≤ Std.Usize.max) :
    linalg.PolyMatrix.prepare m ⦃ z => WfPrep rows cols z m ⦄ := by
  rw [linalg.PolyMatrix.prepare]
  step with cols_spec m ha hrows as ⟨c, hc⟩
  step with prepare_loop_spec m (alloc.vec.Vec.len m) c
    (alloc.vec.Vec.new ring.PreparedVec) 0#usize ha (by simp [ha.1]) hc hmax
    (by simp) (by simp) (by intro u hu; simp at hu) as ⟨rws, hrl, hrv⟩
  exact ⟨hc, hrl, hrv⟩

/-- The loop of `PreparedMatrix::apply`: entry `j` already written is the dot
product of matrix row `j` with the input vector — the very invariant
`mat_vec_mul_loop_spec` carries. -/
theorem apply_loop_spec {rows cols : ℕ} (pm : linalg.PreparedMatrix)
    (m : linalg.PolyMatrix) (v : linalg.PolyVec) (n w : Std.Usize)
    (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (ha : WfMat rows cols m) (hv : WfVec cols v) (hp : WfPrep rows cols pm m)
    (hn : n.val = rows) (hw : w.val = cols)
    (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hwf : ∀ z ∈ out.val, Wf z)
    (hval : ∀ j, j < i.val →
      toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ArkLib.Lattices.dot (toVec (k := cols) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))
            (toVec (k := cols) v)) :
    linalg.PreparedMatrix.apply_loop pm.rows v n w out i
      ⦃ z => z.val.length = rows ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < rows → toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          = ArkLib.Lattices.dot (toVec (k := cols) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))
              (toVec (k := cols) v) ⦄ := by
  rw [linalg.PreparedMatrix.apply_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ j, j < s.2.val → toRq (s.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ArkLib.Lattices.dot (toVec (k := cols) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))
            (toVec (k := cols) v))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [linalg.PreparedMatrix.apply_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hip : i1.val < pm.rows.val.length := by rw [hp.2.1, ← hn]; scalar_tac
      have him : i1.val < m.val.length := by rw [ha.1, ← hn]; scalar_tac
      step as ⟨pv, hpv⟩
      have hprow : PrepRow cols pv (m.val.getD i1.val (alloc.vec.Vec.new ring.Rq)) := by
        have := hp.2.2 i1.val (by rw [← hn]; scalar_tac)
        rwa [List.getD_eq_getElem _ _ hip, ← hpv] at this
      have hWrow : WfVec cols (m.val.getD i1.val (alloc.vec.Vec.new ring.Rq)) := by
        rw [List.getD_eq_getElem _ _ him]; exact ha.2 _ (List.getElem_mem him)
      step with dot_prep_spec (k := cols) pv
        (m.val.getD i1.val (alloc.vec.Vec.new ring.Rq)) v w hw hWrow hv hprow
        as ⟨r, hWr, hr⟩
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
          rw [hjeq, ho2, getD_append_eq, hr, hlen1]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq, hn], hwf1, by intro j hj; exact hval1 j (by rw [heq, hn]; exact hj)⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- **`PreparedMatrix::apply` = `PolyMatrix::mat_vec_mul`.** The conclusion is
`mat_vec_mul_spec`'s, word for word: ArkLib's `matVecMul` of the matrix the
prepared form was built from. -/
theorem apply_spec {rows cols : ℕ} (pm : linalg.PreparedMatrix)
    (m : linalg.PolyMatrix) (v : linalg.PolyVec)
    (ha : WfMat rows cols m) (hv : WfVec cols v) (hp : WfPrep rows cols pm m) :
    linalg.PreparedMatrix.apply pm v
      ⦃ z => WfVec rows z ∧ toVec (k := rows) z
        = ArkLib.Lattices.matVecMul (toMat (rows := rows) (cols := cols) m)
            (toVec (k := cols) v) ⦄ := by
  rw [linalg.PreparedMatrix.apply]
  have hvl : (alloc.vec.Vec.len v).val = cols := by simp [hv.1]
  have hcl : pm.cols.val = cols := hp.1
  simp only [if_pos (by scalar_tac : pm.cols ≤ alloc.vec.Vec.len v), bind_ok_id]
  apply spec_mono (apply_loop_spec pm m v (alloc.vec.Vec.len pm.rows) pm.cols
    (alloc.vec.Vec.new ring.Rq) 0#usize ha hv hp (by simp [hp.2.1]) hcl
    (by simp) (by simp) (by intro y hy; simp at hy) (by intro j hj; simp at hj))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i
  rw [ArkLib.Lattices.matVecMul_apply, toMat_apply]
  exact hzval i.val i.isLt

/-! ### The two-prime prepared matrix

The same value again, under two primes rather than three, for a vector of gadget
digits. `apply_digits_spec`'s conclusion is once more `mat_vec_mul_spec`'s word
for word; what it carries extra is `DigitVec`, and that is the one precondition
in this file that a caller can violate without the compiler noticing. It is
discharged at `generate_decomps` by `gadget_decompose_digit_words`. -/

/-- `ring::dot_prepared_digits` at the specification level. -/
theorem dot_prep_digits_spec {k : ℕ} (prep : ring.PreparedVec) (u v : linalg.PolyVec)
    (nU : Std.Usize) (hn : nU.val = k) (hu : WfVec k u) (hv : WfVec k v)
    (hvd : DigitVec k v) (hprep : PrepRow2 k prep u) :
    ring.dot_prepared_digits prep v nU
      ⦃ z => Wf z ∧ toRq z
        = ArkLib.Lattices.dot (toVec (k := k) u) (toVec (k := k) v) ⦄ := by
  apply spec_mono (HachiEquiv.RqBridge.dot_prepared_digits_spec prep u v nU
    (by intro j hj; rw [hn] at hj; exact wf_getD hu hj)
    (by intro j hj; rw [hn] at hj; exact wf_getD hv hj)
    (by rw [hn]; exact hvd)
    (by rw [hn, hu.1]) (by rw [hn, hv.1]) (by rw [hn]; exact hprep))
  rintro z ⟨hzwf, hzval⟩
  refine ⟨hzwf, ?_⟩
  rw [hzval, hn, ArkLib.Lattices.dot_eq_sum]
  exact (Fin.sum_univ_eq_sum_range
    (fun j => toRq (u.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
      * toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))) k).symm

/-- `pm` is the two-prime prepared form of `m`. -/
def WfPrep2 (rows cols : ℕ) (pm : linalg.PreparedMatrix) (m : linalg.PolyMatrix) : Prop :=
  pm.cols.val = cols ∧ pm.rows.val.length = rows
  ∧ ∀ i, i < rows → PrepRow2 cols (pm.rows.val.getD i prepJunk)
      (m.val.getD i (alloc.vec.Vec.new ring.Rq))

/-- The loop of `PolyMatrix::prepare_digits`. -/
theorem prepare_digits_loop_spec {rows cols : ℕ} (m : linalg.PolyMatrix)
    (n c : Std.Usize) (rws : alloc.vec.Vec ring.PreparedVec) (i : Std.Usize)
    (ha : WfMat rows cols m) (hn : n.val = rows) (hc : c.val = cols)
    (hmax : cols * N ≤ Std.Usize.max)
    (hi : i.val ≤ n.val) (hlen : rws.val.length = i.val)
    (hval : ∀ u, u < i.val → PrepRow2 cols (rws.val.getD u prepJunk)
      (m.val.getD u (alloc.vec.Vec.new ring.Rq))) :
    linalg.PolyMatrix.prepare_digits_loop m n c rws i
      ⦃ z => z.val.length = rows ∧ ∀ u, u < rows →
          PrepRow2 cols (z.val.getD u prepJunk)
            (m.val.getD u (alloc.vec.Vec.new ring.Rq)) ⦄ := by
  rw [linalg.PolyMatrix.prepare_digits_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val
      ∧ ∀ u, u < s.2.val → PrepRow2 cols (s.1.val.getD u prepJunk)
          (m.val.getD u (alloc.vec.Vec.new ring.Rq)))
  · rintro ⟨r1, i1⟩ ⟨hi1, hlen1, hval1⟩
    dsimp only at hi1 hlen1 hval1
    simp only [linalg.PolyMatrix.prepare_digits_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have him : i1.val < m.val.length := by rw [ha.1, ← hn]; scalar_tac
      step as ⟨pv, hpv⟩
      have hWpv : WfVec cols pv := by rw [hpv]; exact ha.2 _ (List.getElem_mem him)
      have hmi : m.val.getD i1.val (alloc.vec.Vec.new ring.Rq) = pv := by
        rw [hpv]; exact List.getD_eq_getElem _ _ him
      step with HachiEquiv.AuxFused.prepare_vec_two_spec pv c
        (by intro u hu; rw [hc] at hu; exact wf_getD hWpv hu)
        (by rw [hc, hWpv.1]) (by rw [hc]; exact hmax) as ⟨p, hpl, hp1, hp2⟩
      step as ⟨r2, hr2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · rw [hr2, hi2, List.length_append, hlen1]; simp
      · intro u hu
        rw [hi2] at hu
        rcases Nat.lt_or_ge u i1.val with hult | huge
        · rw [hr2, getD_append_lt _ _ _ (by omega)]
          exact hval1 u hult
        · have hueq : u = r1.val.length := by omega
          rw [hueq, hr2, getD_append_eq, hlen1, hmi]
          refine ⟨by rw [hpl]; exact hc, ?_, ?_⟩
          · rw [← hc]; exact hp1
          · rw [← hc]; exact hp2
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq, hn], by intro u hu; exact hval1 u (by rw [heq, hn]; exact hu)⟩
  · exact ⟨hi, hlen, hval⟩

/-- `PolyMatrix::prepare_digits` — the two-prime prepared form. -/
theorem prepare_digits_spec {rows cols : ℕ} (m : linalg.PolyMatrix)
    (ha : WfMat rows cols m) (hrows : 0 < rows) (hmax : cols * N ≤ Std.Usize.max) :
    linalg.PolyMatrix.prepare_digits m ⦃ z => WfPrep2 rows cols z m ⦄ := by
  rw [linalg.PolyMatrix.prepare_digits]
  step with cols_spec m ha hrows as ⟨c, hc⟩
  step with prepare_digits_loop_spec m (alloc.vec.Vec.len m) c
    (alloc.vec.Vec.new ring.PreparedVec) 0#usize ha (by simp [ha.1]) hc hmax
    (by simp) (by simp) (by intro u hu; simp at hu) as ⟨rws, hrl, hrv⟩
  exact ⟨hc, hrl, hrv⟩

/-- The loop of `PreparedMatrix::apply_digits`. -/
theorem apply_digits_loop_spec {rows cols : ℕ} (pm : linalg.PreparedMatrix)
    (m : linalg.PolyMatrix) (v : linalg.PolyVec) (n w : Std.Usize)
    (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (ha : WfMat rows cols m) (hv : WfVec cols v) (hvd : DigitVec cols v)
    (hp : WfPrep2 rows cols pm m)
    (hn : n.val = rows) (hw : w.val = cols)
    (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hwf : ∀ z ∈ out.val, Wf z)
    (hval : ∀ j, j < i.val →
      toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ArkLib.Lattices.dot (toVec (k := cols) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))
            (toVec (k := cols) v)) :
    linalg.PreparedMatrix.apply_digits_loop pm.rows v n w out i
      ⦃ z => z.val.length = rows ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < rows → toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          = ArkLib.Lattices.dot (toVec (k := cols) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))
              (toVec (k := cols) v) ⦄ := by
  rw [linalg.PreparedMatrix.apply_digits_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ j, j < s.2.val → toRq (s.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ArkLib.Lattices.dot (toVec (k := cols) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))
            (toVec (k := cols) v))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [linalg.PreparedMatrix.apply_digits_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hip : i1.val < pm.rows.val.length := by rw [hp.2.1, ← hn]; scalar_tac
      have him : i1.val < m.val.length := by rw [ha.1, ← hn]; scalar_tac
      step as ⟨pv, hpv⟩
      have hprow : PrepRow2 cols pv (m.val.getD i1.val (alloc.vec.Vec.new ring.Rq)) := by
        have := hp.2.2 i1.val (by rw [← hn]; scalar_tac)
        rwa [List.getD_eq_getElem _ _ hip, ← hpv] at this
      have hWrow : WfVec cols (m.val.getD i1.val (alloc.vec.Vec.new ring.Rq)) := by
        rw [List.getD_eq_getElem _ _ him]; exact ha.2 _ (List.getElem_mem him)
      step with dot_prep_digits_spec (k := cols) pv
        (m.val.getD i1.val (alloc.vec.Vec.new ring.Rq)) v w hw hWrow hv hvd hprow
        as ⟨r, hWr, hr⟩
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
          rw [hjeq, ho2, getD_append_eq, hr, hlen1]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq, hn], hwf1, by intro j hj; exact hval1 j (by rw [heq, hn]; exact hj)⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- **`PreparedMatrix::apply_digits` = `PolyMatrix::mat_vec_mul`**, for a vector
of gadget digits. The conclusion is `mat_vec_mul_spec`'s and `apply_spec`'s, word
for word; only the hypotheses differ. -/
theorem apply_digits_spec {rows cols : ℕ} (pm : linalg.PreparedMatrix)
    (m : linalg.PolyMatrix) (v : linalg.PolyVec)
    (ha : WfMat rows cols m) (hv : WfVec cols v) (hvd : DigitVec cols v)
    (hp : WfPrep2 rows cols pm m) :
    linalg.PreparedMatrix.apply_digits pm v
      ⦃ z => WfVec rows z ∧ toVec (k := rows) z
        = ArkLib.Lattices.matVecMul (toMat (rows := rows) (cols := cols) m)
            (toVec (k := cols) v) ⦄ := by
  rw [linalg.PreparedMatrix.apply_digits]
  have hvl : (alloc.vec.Vec.len v).val = cols := by simp [hv.1]
  have hcl : pm.cols.val = cols := hp.1
  simp only [if_pos (by scalar_tac : pm.cols ≤ alloc.vec.Vec.len v), bind_ok_id]
  apply spec_mono (apply_digits_loop_spec pm m v (alloc.vec.Vec.len pm.rows) pm.cols
    (alloc.vec.Vec.new ring.Rq) 0#usize ha hv hvd hp (by simp [hp.2.1]) hcl
    (by simp) (by simp) (by intro y hy; simp at hy) (by intro j hj; simp at hj))
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
def dd : DigitDecomposition (R := ZMod q) (16 : ZMod q) 8 :=
  zmodDigitDecomposition 16 8 (by norm_num) (by norm_num)

/-- **The unsigned digit bound**: each digit of `dd`, as a centered residue, has
absolute value at most `b - 1 = 15` (the digit is a natural number `< 16 ≤ q/2`,
so it does not wrap to a negative representative). This was ArkLib's
`zmodDigit_natAbs_le` until PR #847 made the *balanced* digits the Hachi gadget
inverse and dropped the unsigned norm lemmas; the proved unsigned layer here
keeps it as the single analytic input to its shortness bounds, fed to ArkLib's
surviving generic `gadgetDecompose_*_of_digit_le` forms. -/
theorem dd_digit_natAbs_le (c : ZMod q) (e : Fin 8) :
    (dd.digit c e).valMinAbs.natAbs ≤ 15 := by
  simp only [dd, zmodDigitDecomposition]
  set d := (Nat.digits 16 c.val).getD (e : ℕ) 0 with hd
  have hdb : d < 16 := by
    rcases lt_or_ge (e : ℕ) (Nat.digits 16 c.val).length with hlt | hge
    · rw [hd, List.getD_eq_getElem _ _ hlt]
      exact Nat.digits_lt_base (by norm_num) (List.getElem_mem _)
    · rw [hd, List.getD_eq_default _ _ hge]; omega
  rw [ZMod.valMinAbs_natCast_of_le_half (by show d ≤ 4294967197 / 2; omega)]
  simp only [Int.natAbs_natCast]
  omega

/-! ### The digit bound, at the word level

The two-prime bounded dot is correct only for an operand whose *words* are below
the gadget base, so somebody has to say so about `gadget_decompose`'s output.
Nothing existing does: `digit_at_spec` says `Red d`, which is `< q`, and
`gadget_decompose_spec` says the result represents `gadgetDecompose Φ dd`, which
is a statement about `Rq`s and not about their `u64` representatives.

Both facts below are *derived* rather than proved by a second induction over the
three loops of `gadget_decompose`: ArkLib's `gadgetDecompose_coeff` says each
coefficient of the result is a digit, and `dd_digit_val_lt` says a digit's
canonical value is below the base. `AuxCode.spec_and` is what lets the caller
have this and `gadget_decompose_spec` at once, with neither statement moving. -/
/-- **The unsigned digit bound, on the canonical value.** `dd`'s digits are
natural numbers below the base, so they do not wrap: `val`, not just
`valMinAbs.natAbs`, is below 16.

The sibling `dd_digit_natAbs_le` is the *centered* bound, which is what the
shortness arguments want; this one is what an integer bound on a `u64` word
wants, and the two are genuinely different statements -- a centered bound of 15
also admits `val = q − 15`. -/
theorem dd_digit_val_lt (c : ZMod q) (e : Fin 8) : (dd.digit c e).val < 16 := by
  simp only [dd, zmodDigitDecomposition]
  set d := (Nat.digits 16 c.val).getD (e : ℕ) 0 with hd
  have hdb : d < 16 := by
    rcases lt_or_ge (e : ℕ) (Nat.digits 16 c.val).length with hlt | hge
    · rw [hd, List.getD_eq_getElem _ _ hlt]
      exact Nat.digits_lt_base (by norm_num) (List.getElem_mem _)
    · rw [hd, List.getD_eq_default _ _ hge]; omega
  rw [ZMod.val_natCast]
  exact lt_of_le_of_lt (Nat.mod_le _ _) hdb

/-- The loop of `gadget::digit_at`: after `i` divisions by 16 the remaining
word is `c / 16ⁱ`. -/
theorem digit_at_loop_spec (e : Std.Usize) (rest : Std.U64) (i : Std.Usize) (c0 : ℕ)
    (hi : i.val ≤ e.val) (hrest : rest.val = c0 / 16 ^ i.val) :
    gadget.digit_at_loop e params.GADGET_BASE rest i
      ⦃ z => z.val = c0 / 16 ^ e.val ⦄ := by
  have hb : (params.GADGET_BASE).val = 16 := by simp [params.GADGET_BASE]
  rw [gadget.digit_at_loop]
  apply loop.spec_decr_nat (fun s => e.val - s.2.val)
    (fun s => s.2.val ≤ e.val ∧ s.1.val = c0 / 16 ^ s.2.val)
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
theorem digit_at_spec (c : cpoly.field.Fp) (e : Std.Usize) (hc : Red c) (he : e.val < 8) :
    gadget.digit_at c e ⦃ d => Red d ∧ toK d = dd.digit (toK c) ⟨e.val, he⟩ ⦄ := by
  have hb : (params.GADGET_BASE).val = 16 := by simp [params.GADGET_BASE]
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

/-- `gadget::digit_at` returns a word below the base. -/
theorem digit_at_lt_base (c : cpoly.field.Fp) (e : Std.Usize) (hc : Red c) (he : e.val < 8) :
    gadget.digit_at c e ⦃ d => d.val < 16 ⦄ := by
  apply spec_mono (digit_at_spec c e hc he)
  rintro d ⟨hRd, hd⟩
  have hv : (toK d).val = d.val := by
    simp only [toK, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hRd
  rw [← hv, hd]
  exact dd_digit_val_lt (toK c) ⟨e.val, he⟩

/-! ### `gadget::digit_decompose`

`digit_at` at every position, which is the whole of the claim: the Rust runs the
same divide-by-16 loop 8 times over, and the specification's `dd.digit` indexes
`Nat.digits 16 c.val`. `digit_at_spec` is the per-position statement; this is the
vector of them, and the reason it earns a statement of its own is that a reader
cannot otherwise tell whether the *order* agrees -- slot `e` has to be digit `e`,
least-significant first, and a reversed accumulation would leave `digit_at_spec`
true and this false.

The representation is `Ring.coeffK`, not a new function: the output is an
`alloc.vec.Vec cpoly.field.Fp`, which is exactly `coeffK`'s domain.

Hypotheses: `Red c` only. The fail-point walk closes without a value bound --
`gadget::digit_at` is total (its loop just divides `e` times; the `e.val < 8` of
`digit_at_spec` feeds the `Fin 8` index of its postcondition, not a fail point,
and the loop guard `e < digits` supplies it at `digits = GADGET_DIGITS = 8`);
the 8 `Vec.push`es are bounded by a numeral; and `e + 1#usize` is under the
guard. -/

/-- The loop of `gadget::digit_decompose`: after `e` turns the accumulator holds
digits `0 … e-1`, in order. -/
theorem digit_decompose_loop_spec (c : cpoly.field.Fp) (digits : Std.Usize)
    (out : alloc.vec.Vec cpoly.field.Fp) (e : Std.Usize)
    (hc : Red c) (hdig : digits.val = 8) (he : e.val ≤ 8)
    (hlen : out.val.length = e.val) (hred : ∀ u ∈ out.val, Red u)
    (hval : ∀ (t : ℕ) (ht : t < 8), t < e.val →
      coeffK out t = dd.digit (toK c) ⟨t, ht⟩) :
    gadget.digit_decompose_loop c digits out e
      ⦃ z => z.val.length = 8 ∧ (∀ u ∈ z.val, Red u) ∧
        ∀ (t : ℕ) (ht : t < 8), coeffK z t = dd.digit (toK c) ⟨t, ht⟩ ⦄ := by
  rw [gadget.digit_decompose_loop]
  apply loop.spec_decr_nat (fun s => digits.val - s.2.val)
    (fun s => s.2.val ≤ 8 ∧ s.1.val.length = s.2.val ∧ (∀ u ∈ s.1.val, Red u) ∧
      ∀ (t : ℕ) (ht : t < 8), t < s.2.val →
        coeffK s.1 t = dd.digit (toK c) ⟨t, ht⟩)
  · rintro ⟨o1, e1⟩ ⟨he1, hlen1, hred1, hval1⟩
    dsimp only at he1 hlen1 hred1 hval1
    simp only [gadget.digit_decompose_loop.body]
    by_cases hlt : e1 < digits
    · rw [if_pos hlt]
      have he1lt : e1.val < 8 := by rw [← hdig]; scalar_tac
      step with digit_at_spec c e1 hc he1lt as ⟨f, hRf, hf⟩
      have hcap : o1.val.length < Usize.max := by rw [hlen1]; scalar_tac
      step as ⟨o2, ho2⟩
      step as ⟨e2, he2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, he2, List.length_append, hlen1]; simp
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hred1 u h
        · rw [List.mem_singleton.mp h]; exact hRf
      · intro t ht htlt
        rw [he2] at htlt
        rcases Nat.lt_or_ge t e1.val with h | h
        · rw [coeffK_append_lt ho2 (by omega : t < o1.val.length)]
          exact hval1 t ht h
        · have hteq : t = e1.val := by omega
          subst hteq
          conv_lhs => rw [← hlen1]
          rw [coeffK_append_eq ho2]
          exact hf
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : e1.val = 8 := by scalar_tac
      refine ⟨by rw [hlen1, heq], hred1, ?_⟩
      intro t ht
      exact hval1 t ht (by omega)
  · exact ⟨he, hlen, hred, hval⟩

/-- `gadget::digit_decompose` — ArkLib's `zmodDigitDecomposition.digit` at every
`e < digits`, as a vector: slot `e` is digit `e` of `c`'s canonical
representative, least-significant first. -/
theorem digit_decompose_spec (c : cpoly.field.Fp) (hc : Red c) :
    gadget.digit_decompose c
      ⦃ z => z.val.length = 8 ∧ (∀ u ∈ z.val, Red u) ∧
        ∀ e : Fin 8, coeffK z e.val = dd.digit (toK c) e ⦄ := by
  simp only [gadget.digit_decompose]
  apply spec_mono (digit_decompose_loop_spec c params.GADGET_DIGITS
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize hc (by simp [params.GADGET_DIGITS])
    (by simp) (by simp) (by intro u hu; simp at hu) (by intro t ht h; simp at h))
  rintro z ⟨h1, h2, h3⟩
  exact ⟨h1, h2, fun e => h3 e.val e.isLt⟩

/-- The loop of `gadget::base_pow`: the accumulator is `bⁱ` after `i` turns. -/
theorem base_pow_loop_spec (e : Std.Usize) (b : cpoly.field.Fp) (acc : cpoly.field.Fp)
    (i : Std.Usize) (hb : Red b) (hbv : toK b = (16 : ZMod q)) (hacc : Red acc)
    (hi : i.val ≤ e.val) (hval : toK acc = (16 : ZMod q) ^ i.val) :
    gadget.base_pow_loop e b acc i
      ⦃ p => Red p ∧ toK p = (16 : ZMod q) ^ e.val ⦄ := by
  rw [gadget.base_pow_loop]
  apply loop.spec_decr_nat (fun s => e.val - s.2.val)
    (fun s => s.2.val ≤ e.val ∧ Red s.1 ∧ toK s.1 = (16 : ZMod q) ^ s.2.val)
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
`e = 8`. -/
theorem base_pow_spec (e : Std.Usize) :
    gadget.base_pow e ⦃ p => Red p ∧ toK p = (16 : ZMod q) ^ e.val ⦄ := by
  rw [gadget.base_pow]
  step as ⟨b, hRb, hb⟩
  have hbv : toK b = (16 : ZMod q) := by
    rw [hb]; simp [params.GADGET_BASE]
  exact base_pow_loop_spec e b cpoly.field.Fp.ONE 0#usize hRb hbv Red_one
    (by simp) (by simp)

/-- `gadget::gadget_entry` — ArkLib's `gadgetEntry`. -/
theorem gadget_entry_spec (i j : Std.Usize) :
    gadget.gadget_entry i j
      ⦃ z => Wf z ∧ ∀ (rows : ℕ) (hi : i.val < rows) (hj : j.val < rows * 8),
          toRq z = gadgetEntry Φ (16 : ZMod q) (rows := rows) (digits := 8)
            ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⦄ := by
  have hd : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  rw [gadget.gadget_entry]
  step as ⟨i1, hi1⟩
  by_cases heq : i1 = i
  · rw [if_pos heq]
    step as ⟨j2, hj2⟩
    step with base_pow_spec j2 as ⟨f, hRf, hf⟩
    step as ⟨z, hWz, hz⟩
    refine ⟨hWz, ?_⟩
    intro rows hi hj
    have hcond : j.val / 8 = i.val := by rw [← hd, ← hi1, heq]
    rw [hz, hf, hj2, hd, gadgetEntry, if_pos hcond]
  · rw [if_neg heq]
    step as ⟨z, hWz, hz⟩
    refine ⟨hWz, ?_⟩
    intro rows hi hj
    have hcond : ¬ (j.val / 8 = i.val) := by
      intro h
      apply heq
      have : i1.val = i.val := by rw [hi1, hd, h]
      scalar_tac
    rw [hz, gadgetEntry, if_neg hcond]

/-! ### `gadget::gadget_matrix`

The materialized gadget matrix `G = I_rows ⊗ [1, 16, …, 16⁷]`. `gadget_mul` is the
map `v ↦ G *ᵥ v` computed without building `G`, and `gadget_mul_spec` below
proves that against `gadgetMul`; this states that the *materialized* matrix is
`gadgetMatrix` itself. Both are needed and neither implies the other: the
`gadget_mul` route could agree with `gadgetMul` while `gadget_matrix` built a
transposed or misaligned `G`, and before this statement
`tests/gadget_semantics.rs`'s `gadget_matrix_has_the_tensor_layout` and the
`via_matrix` cross-check were the only things pinning it.

Hypotheses: `hmax : rows * 8 ≤ Usize.max` is earned. The fail point is the first
line of the extracted body, `let cols ← rows * params.GADGET_DIGITS` -- a checked
`Usize` multiplication, and `r`'s own carrier invariant bounds `rows` but not
`8 * rows`. It is minimal: with it, the outer `Vec.push` (`rows` entries) and the
inner one (`cols` entries, and `cols` is a `Usize`) are both bounded, and
`gadget_entry` is total. -/

/-- The inner loop of `gadget::gadget_matrix`: row `i` is filled left to right
with the gadget entries of that row. -/
theorem gadget_matrix_loop0_loop0_spec {rows : ℕ} (cols i : Std.Usize)
    (row : alloc.vec.Vec ring.Rq) (j : Std.Usize)
    (hi : i.val < rows) (hcols : cols.val = rows * 8)
    (hj : j.val ≤ rows * 8) (hlen : row.val.length = j.val)
    (hwf : ∀ x ∈ row.val, Wf x)
    (hval : ∀ (t : ℕ) (ht : t < rows * 8), t < j.val →
      toRq (row.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        = gadgetEntry Φ (16 : ZMod q) (rows := rows) (digits := 8) ⟨i.val, hi⟩ ⟨t, ht⟩) :
    gadget.gadget_matrix_loop0_loop0 cols i row j
      ⦃ z => z.val.length = rows * 8 ∧ (∀ x ∈ z.val, Wf x) ∧
        ∀ (t : ℕ) (ht : t < rows * 8),
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = gadgetEntry Φ (16 : ZMod q) (rows := rows) (digits := 8)
                ⟨i.val, hi⟩ ⟨t, ht⟩ ⦄ := by
  rw [gadget.gadget_matrix_loop0_loop0]
  apply loop.spec_decr_nat (fun s => cols.val - s.2.val)
    (fun s => s.2.val ≤ rows * 8 ∧ s.1.val.length = s.2.val ∧
      (∀ x ∈ s.1.val, Wf x) ∧
      ∀ (t : ℕ) (ht : t < rows * 8), t < s.2.val →
        toRq (s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          = gadgetEntry Φ (16 : ZMod q) (rows := rows) (digits := 8) ⟨i.val, hi⟩ ⟨t, ht⟩)
  · rintro ⟨row1, j1⟩ ⟨hj1, hlen1, hwf1, hval1⟩
    dsimp only at hj1 hlen1 hwf1 hval1
    simp only [gadget.gadget_matrix_loop0_loop0.body]
    by_cases hlt : j1 < cols
    · rw [if_pos hlt]
      have hj1lt : j1.val < rows * 8 := by rw [← hcols]; scalar_tac
      have hcap : row1.val.length < Usize.max := by rw [hlen1]; scalar_tac
      step with gadget_entry_spec i j1 as ⟨z, hWz, hz⟩
      step as ⟨row2, hrow2⟩
      step as ⟨j2, hj2⟩
      have hget : row2.val.getD j1.val (alloc.vec.Vec.new cpoly.field.Fp) = z := by
        rw [hrow2, ← hlen1]; exact getD_append_eq _ _ _
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [hrow2, hj2, List.length_append, hlen1]; simp
      · intro x hx
        rw [hrow2] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hwf1 x h
        · rw [List.mem_singleton.mp h]; exact hWz
      · intro t ht htlt
        rw [hj2] at htlt
        rcases Nat.lt_or_ge t j1.val with hlow | hhigh
        · rw [hrow2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t ht hlow
        · have hteq : t = j1.val := by omega
          subst hteq
          rw [hget]
          exact hz rows hi hj1lt
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : j1.val = rows * 8 := by rw [← hcols]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, fun t ht => hval1 t ht (by omega)⟩
  · exact ⟨hj, hlen, hwf, hval⟩

/-- The outer loop of `gadget::gadget_matrix`: the accumulator holds the rows of
`gadgetMatrix` already built. -/
theorem gadget_matrix_loop0_spec {rows : ℕ} (r cols : Std.Usize)
    (out : alloc.vec.Vec linalg.PolyVec) (i : Std.Usize)
    (hr : r.val = rows) (hcols : cols.val = rows * 8) (hi : i.val ≤ rows)
    (hlen : out.val.length = i.val)
    (hwf : ∀ y ∈ out.val, WfVec (rows * 8) y)
    (hval : ∀ (s : ℕ) (hs : s < rows), s < i.val →
      toVec (k := rows * 8) (out.val.getD s (alloc.vec.Vec.new ring.Rq))
        = gadgetMatrix Φ (16 : ZMod q) rows 8 ⟨s, hs⟩) :
    gadget.gadget_matrix_loop0 r cols out i
      ⦃ z => z.val.length = rows ∧ (∀ y ∈ z.val, WfVec (rows * 8) y) ∧
        ∀ (s : ℕ) (hs : s < rows),
          toVec (k := rows * 8) (z.val.getD s (alloc.vec.Vec.new ring.Rq))
            = gadgetMatrix Φ (16 : ZMod q) rows 8 ⟨s, hs⟩ ⦄ := by
  rw [gadget.gadget_matrix_loop0]
  apply loop.spec_decr_nat (fun s => r.val - s.2.val)
    (fun s => s.2.val ≤ rows ∧ s.1.val.length = s.2.val ∧
      (∀ y ∈ s.1.val, WfVec (rows * 8) y) ∧
      (∀ (t : ℕ) (ht : t < rows), t < s.2.val →
        toVec (k := rows * 8) (s.1.val.getD t (alloc.vec.Vec.new ring.Rq))
          = gadgetMatrix Φ (16 : ZMod q) rows 8 ⟨t, ht⟩))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [gadget.gadget_matrix_loop0.body]
    by_cases hlt : i1 < r
    · rw [if_pos hlt]
      have hi1lt : i1.val < rows := by rw [← hr]; scalar_tac
      step with gadget_matrix_loop0_loop0_spec (rows := rows) cols i1
        (alloc.vec.Vec.new ring.Rq) 0#usize hi1lt hcols (by simp) (by simp)
        (by intro x hx; simp at hx) (by intro t ht h; simp at h)
        as ⟨z, hzlen, hzwf, hzval⟩
      simp only [linalg.PolyVec.new]
      have hcap : o1.val.length < Usize.max := by rw [hlen1]; scalar_tac
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      have hrow : toVec (k := rows * 8) z
          = gadgetMatrix Φ (16 : ZMod q) rows 8 ⟨i1.val, hi1lt⟩ := by
        funext t
        show toRq (z.val.getD t.val (alloc.vec.Vec.new cpoly.field.Fp))
          = gadgetEntry Φ (16 : ZMod q) (rows := rows) (digits := 8) ⟨i1.val, hi1lt⟩ t
        exact hzval t.val t.isLt
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact ⟨hzlen, hzwf⟩
      · intro t ht h
        rw [hi2] at h
        rcases Nat.lt_or_ge t i1.val with hjlt | hjge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 t ht hjlt]
        · have hget : (o1.val ++ [z]).getD t (alloc.vec.Vec.new ring.Rq) = z := by
            rw [show t = o1.val.length from by omega]
            exact getD_append_eq _ _ _
          have hfin : (⟨t, ht⟩ : Fin rows) = ⟨i1.val, hi1lt⟩ := by
            simp only [Fin.mk.injEq]; omega
          rw [ho2, hget, hfin]
          exact hrow
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = rows := by rw [← hr] at hi1 ⊢; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, fun t ht => hval1 t ht (by omega)⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- `gadget::gadget_matrix` — ArkLib's `gadgetMatrix` at base `2` and 8 digits:
the materialized `G = I_rows ⊗ [1, 16, …, 16⁷]`.

`hmax` is the capacity side condition of the column count; see the section note
for the fail point it discharges. -/
theorem gadget_matrix_spec {rows : ℕ} (r : Std.Usize) (hr : r.val = rows)
    (hmax : rows * 8 ≤ Usize.max) :
    gadget.gadget_matrix r
      ⦃ a => WfMat rows (rows * 8) a ∧
        toMat (rows := rows) (cols := rows * 8) a
          = gadgetMatrix Φ (16 : ZMod q) rows 8 ⦄ := by
  rw [gadget.gadget_matrix]
  have hgd : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  have hfit : r.val * (params.GADGET_DIGITS).val ≤ Usize.max := by rw [hgd, hr]; exact hmax
  step as ⟨cols, hcols⟩
  have hcols32 : cols.val = rows * 8 := by rw [hcols, hgd, hr]
  step with gadget_matrix_loop0_spec (rows := rows) r cols
    (alloc.vec.Vec.new linalg.PolyVec) 0#usize hr hcols32 (by simp) (by simp)
    (by intro y hy; simp at hy) (by intro s hs h; simp at h)
    as ⟨z, hzlen, hzwf, hzval⟩
  simp only [linalg.PolyMatrix.new, WP.spec_ok]
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i
  rw [toMat_apply]
  exact hzval i.val i.isLt

/-- The inner loop of `gadget::gadget_mul`: the accumulator is the base-weighted sum
over the digit slots of block `i` already visited. -/
theorem gadget_mul_inner_loop_spec {rows : ℕ} (v : linalg.PolyVec) (dg : Std.Usize)
    (i : Std.Usize) (acc : ring.Rq) (e : Std.Usize)
    (hv : WfVec (rows * 8) v) (hdg : dg.val = 8) (hi : i.val < rows)
    (hacc : Wf acc) (he : e.val ≤ 8)
    (hval : toRq acc = ∑ t ∈ Finset.range e.val, Rq.constRq Φ ((16 : ZMod q) ^ t)
      * toRq (v.val.getD (t + 8 * i.val) (alloc.vec.Vec.new cpoly.field.Fp))) :
    gadget.gadget_mul_loop0_loop0 v dg i acc e
      ⦃ z => Wf z ∧ toRq z = ∑ t ∈ Finset.range 8, Rq.constRq Φ ((16 : ZMod q) ^ t)
        * toRq (v.val.getD (t + 8 * i.val) (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  have hvlen : rows * 8 ≤ Usize.max := by rw [← hv.1]; exact v.property
  have hib : 8 * i.val + 8 ≤ Usize.max := by
    have h1 : (i.val + 1) * 8 ≤ rows * 8 := Nat.mul_le_mul_right 8 (by omega)
    have h2 : (i.val + 1) * 8 = 8 * i.val + 8 := by ring
    omega
  rw [gadget.gadget_mul_loop0_loop0]
  apply loop.spec_decr_nat (fun s => dg.val - s.2.val)
    (fun s => s.2.val ≤ 8 ∧ Wf s.1 ∧
      toRq s.1 = ∑ t ∈ Finset.range s.2.val, Rq.constRq Φ ((16 : ZMod q) ^ t)
        * toRq (v.val.getD (t + 8 * i.val) (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨a1, e1⟩ ⟨he1, hW1, hval1⟩
    dsimp only at he1 hW1 hval1
    simp only [gadget.gadget_mul_loop0_loop0.body]
    by_cases hlt : e1 < dg
    · rw [if_pos hlt]
      have helt : e1.val < 8 := by rw [← hdg]; scalar_tac
      step as ⟨p, hp⟩
      step as ⟨p2, hp2⟩
      have hidx : p2.val = e1.val + 8 * i.val := by rw [hp2, hp, hdg]; ring
      have hlen : p2.val < v.val.length := by
        rw [hv.1, hidx]
        have : (i.val + 1) * 8 ≤ rows * 8 := Nat.mul_le_mul_right 8 (by omega)
        have h2 : (i.val + 1) * 8 = 8 * i.val + 8 := by ring
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
      have heq : e1.val = 8 := by rw [← hdg]; scalar_tac
      exact ⟨hW1, by rw [hval1, heq]⟩
  · exact ⟨he, hacc, hval⟩

/-- The outer loop of `gadget::gadget_mul`: one accumulated row per block. -/
theorem gadget_mul_outer_loop_spec {rows : ℕ} (r : Std.Usize) (v : linalg.PolyVec)
    (dg : Std.Usize) (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hv : WfVec (rows * 8) v) (hdg : dg.val = 8) (hr : r.val = rows)
    (hi : i.val ≤ rows) (hlen : out.val.length = i.val)
    (hwf : ∀ z ∈ out.val, Wf z)
    (hval : ∀ j, j < i.val →
      toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ∑ t ∈ Finset.range 8, Rq.constRq Φ ((16 : ZMod q) ^ t)
            * toRq (v.val.getD (t + 8 * j) (alloc.vec.Vec.new cpoly.field.Fp))) :
    gadget.gadget_mul_loop0 r v dg out i
      ⦃ z => z.val.length = rows ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < rows → toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          = ∑ t ∈ Finset.range 8, Rq.constRq Φ ((16 : ZMod q) ^ t)
              * toRq (v.val.getD (t + 8 * j) (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [gadget.gadget_mul_loop0]
  apply loop.spec_decr_nat (fun s => r.val - s.2.val)
    (fun s => s.2.val ≤ rows ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ j, j < s.2.val → toRq (s.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ∑ t ∈ Finset.range 8, Rq.constRq Φ ((16 : ZMod q) ^ t)
            * toRq (v.val.getD (t + 8 * j) (alloc.vec.Vec.new cpoly.field.Fp)))
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
    (hr : r.val = rows) (hv : WfVec (rows * 8) v) :
    gadget.gadget_mul r v
      ⦃ z => WfVec rows z ∧ toVec (k := rows) z
        = gadgetMul Φ (16 : ZMod q) (toVec (k := rows * 8) v) ⦄ := by
  have hdg : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  rw [gadget.gadget_mul]
  simp only [linalg.PolyVec.new, bind_ok_id]
  apply spec_mono (gadget_mul_outer_loop_spec r v params.GADGET_DIGITS
    (alloc.vec.Vec.new ring.Rq) 0#usize hv hdg hr (by simp) (by simp)
    (by intro y hy; simp at hy) (by intro j hj; simp at hj))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i
  rw [gadgetMul_apply Φ (16 : ZMod q) (by norm_num)]
  simp only [toVec]
  rw [hzval i.val i.isLt]
  have hfp : ∀ x : Fin 8,
      ((finProdFinEquiv (i, x) : Fin (rows * 8)) : ℕ) = x.val + 8 * i.val := fun _ => rfl
  simp only [hfp]
  rw [Fin.sum_univ_eq_sum_range (fun t => Rq.constRq Φ ((16 : ZMod q) ^ t)
    * toRq (v.val.getD (t + 8 * i.val) (alloc.vec.Vec.new cpoly.field.Fp))) 8]

/-! ### `gadget::gadget_decompose`

The Rust writes block `i`, digit slot `e` at the flat index `8 * i + e`, which is
exactly `finProdFinEquiv (i, e)`; `digitBlock` names the ring element it writes
there. The three loop specs below are the three nested `for`s, from the inside out. -/

/-- The specification's digit map at an unbounded exponent. `dd.digit c ⟨e, _⟩` is
`digitK c e` definitionally (`dd_digit_eq`), which is what lets the loop invariants
below range over `ℕ` rather than over `Fin 8`. -/
def digitK (c : ZMod q) (e : ℕ) : ZMod q := (((Nat.digits 16 c.val).getD e 0 : ℕ) : ZMod q)

theorem dd_digit_eq (c : ZMod q) (e : Fin 8) : dd.digit c e = digitK c e.val := rfl

/-- Two `ofFinCoeff`s at width `N` agree as soon as their coefficient functions do
below `N`. -/
theorem ofFinCoeff_congr {f g : ℕ → ZMod q} (h : ∀ t < N, f t = g t) :
    Rq.ofFinCoeff Φ N f = Rq.ofFinCoeff Φ N g := by
  apply Subtype.ext
  rw [CompPoly.CPolynomial.eq_iff_coeff]
  intro t
  rw [Rq.ofFinCoeff_coeff Φ _ N_le_degree, Rq.ofFinCoeff_coeff Φ _ N_le_degree]
  by_cases ht : t < N
  · rw [if_pos ht, if_pos ht, h t ht]
  · rw [if_neg ht, if_neg ht]

/-- The ring element `gadget::gadget_decompose` writes at the flat index `8 * i + e`:
digit `e` of every coefficient of block `i`. -/
def digitBlock (x : linalg.PolyVec) (i e : ℕ) : Rq Φ :=
  Rq.ofFinCoeff Φ N (fun t =>
    digitK ((toRq (x.val.getD i (alloc.vec.Vec.new cpoly.field.Fp))).1.coeff t) e)

/-- The innermost loop of `gadget::gadget_decompose`: `coeffs` collects digit `e` of
the first `k` coefficients of block `i`. -/
theorem gadget_decompose_coeff_loop_spec {rows : ℕ} (x : linalg.PolyVec)
    (degree i e : Std.Usize) (coeffs : alloc.vec.Vec cpoly.field.Fp) (k : Std.Usize)
    (hx : WfVec rows x) (hdeg : degree.val = N) (hi : i.val < rows) (he : e.val < 8)
    (hk : k.val ≤ N) (hlen : coeffs.val.length = k.val)
    (hred : ∀ u ∈ coeffs.val, Red u)
    (hval : ∀ t < k.val, coeffK coeffs t
      = digitK ((toRq (x.val.getD i.val (alloc.vec.Vec.new cpoly.field.Fp))).1.coeff t) e.val) :
    gadget.gadget_decompose_loop0_loop0_loop0 x degree i e coeffs k
      ⦃ z => z.val.length = N ∧ (∀ u ∈ z.val, Red u) ∧ ∀ t < N, coeffK z t
        = digitK ((toRq (x.val.getD i.val
            (alloc.vec.Vec.new cpoly.field.Fp))).1.coeff t) e.val ⦄ := by
  have hilt : i.val < x.val.length := by rw [hx.1]; exact hi
  have hxi : x.val.getD i.val (alloc.vec.Vec.new cpoly.field.Fp) = x.val[i.val] :=
    List.getD_eq_getElem _ _ hilt
  have hWx : Wf x.val[i.val] := hx.2 _ (List.getElem_mem hilt)
  rw [gadget.gadget_decompose_loop0_loop0_loop0]
  apply loop.spec_decr_nat (fun s => degree.val - s.2.val)
    (fun s => s.2.val ≤ N ∧ s.1.val.length = s.2.val ∧ (∀ u ∈ s.1.val, Red u) ∧
      ∀ t < s.2.val, coeffK s.1 t
        = digitK ((toRq (x.val.getD i.val
            (alloc.vec.Vec.new cpoly.field.Fp))).1.coeff t) e.val)
  · rintro ⟨c1, k1⟩ ⟨hk1, hlen1, hred1, hval1⟩
    dsimp only at hk1 hlen1 hred1 hval1
    simp only [gadget.gadget_decompose_loop0_loop0_loop0.body]
    by_cases hlt : k1 < degree
    · rw [if_pos hlt]
      have hkN : k1.val < N := by rw [← hdeg]; scalar_tac
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hWx
      step with RqBridge.coeff_spec r k1 hWr as ⟨f, hRf, hf⟩
      step with digit_at_spec f e hRf he as ⟨g, hRg, hg⟩
      step as ⟨c2, hc2⟩
      step as ⟨k2, hk2⟩
      refine ⟨by omega, ?_, ?_, ?_, ?_⟩
      · rw [hc2, hk2, List.length_append, hlen1]; simp
      · intro u hu
        rw [hc2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hred1 u h
        · rw [List.mem_singleton.mp h]; exact hRg
      · intro t ht
        rw [hk2] at ht
        rcases Nat.lt_or_ge t k1.val with htlt | htge
        · rw [coeffK_append_lt hc2 (by omega), hval1 t htlt]
        · have hteq : t = k1.val := by omega
          have hpush : coeffK c2 k1.val = toK g := by
            rw [← hlen1]; exact coeffK_append_eq hc2
          rw [hteq, hpush, hg, dd_digit_eq, hf, hr, ← hxi]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = N := by rw [← hdeg] at hk1 ⊢; scalar_tac
      refine ⟨by rw [hlen1, heq], hred1, ?_⟩
      rw [← heq]; exact hval1
  · exact ⟨hk, hlen, hred, hval⟩

/-- The middle loop of `gadget::gadget_decompose`: one digit block of row `i` per turn. -/
theorem gadget_decompose_digit_loop_spec {rows : ℕ} (x : linalg.PolyVec)
    (digits degree i : Std.Usize) (out : alloc.vec.Vec ring.Rq) (e : Std.Usize)
    (hx : WfVec rows x) (hmax : 8 * rows ≤ Usize.max)
    (hdig : digits.val = 8) (hdeg : degree.val = N) (hi : i.val < rows)
    (he : e.val ≤ 8) (hlen : out.val.length = 8 * i.val + e.val)
    (hwf : ∀ y ∈ out.val, Wf y)
    (hval : ∀ i' e' : ℕ, e' < 8 → 8 * i' + e' < 8 * i.val + e.val →
      toRq (out.val.getD (8 * i' + e') (alloc.vec.Vec.new cpoly.field.Fp))
        = digitBlock x i' e') :
    gadget.gadget_decompose_loop0_loop0 x digits degree out i e
      ⦃ z => z.val.length = 8 * i.val + 8 ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ i' e' : ℕ, e' < 8 → 8 * i' + e' < 8 * i.val + 8 →
          toRq (z.val.getD (8 * i' + e') (alloc.vec.Vec.new cpoly.field.Fp))
            = digitBlock x i' e' ⦄ := by
  have hmaxb : 8 * i.val + 8 ≤ Usize.max := by
    have h1 : 8 * (i.val + 1) ≤ 8 * rows := Nat.mul_le_mul_left 8 (by omega)
    omega
  rw [gadget.gadget_decompose_loop0_loop0]
  apply loop.spec_decr_nat (fun s => digits.val - s.2.val)
    (fun s => s.2.val ≤ 8 ∧ s.1.val.length = 8 * i.val + s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ i' e' : ℕ, e' < 8 → 8 * i' + e' < 8 * i.val + s.2.val →
        toRq (s.1.val.getD (8 * i' + e') (alloc.vec.Vec.new cpoly.field.Fp))
          = digitBlock x i' e')
  · rintro ⟨o1, e1⟩ ⟨he1, hlen1, hwf1, hval1⟩
    dsimp only at he1 hlen1 hwf1 hval1
    simp only [gadget.gadget_decompose_loop0_loop0.body]
    by_cases hlt : e1 < digits
    · rw [if_pos hlt]
      have helt : e1.val < 8 := by rw [← hdig]; scalar_tac
      have hinner := gadget_decompose_coeff_loop_spec x degree i e1
        (alloc.vec.Vec.new cpoly.field.Fp) 0#usize hx hdeg hi helt (by simp) (by simp)
        (by intro u hu; simp at hu) (by intro t ht; simp at ht)
      step with hinner as ⟨cs, hcslen, hcsred, hcsval⟩
      step with RqBridge.from_coeffs_spec cs hcsred as ⟨rr, hWrr, hrr⟩
      step as ⟨o2, ho2⟩
      step as ⟨e2, he2⟩
      have hblock : toRq rr = digitBlock x i.val e1.val := by
        rw [hrr, digitBlock]
        exact ofFinCoeff_congr (fun t ht => hcsval t ht)
      refine ⟨by omega, ?_, ?_, ?_, ?_⟩
      · rw [ho2, he2, List.length_append, hlen1]; simp; omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWrr
      · intro i' e' he' hb
        rw [he2] at hb
        rcases Nat.lt_or_ge (8 * i' + e') (8 * i.val + e1.val) with hjlt | hjge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 i' e' he' hjlt]
        · have hi'e : i' = i.val ∧ e' = e1.val := by omega
          obtain ⟨hii, hee⟩ := hi'e
          have hidx : 8 * i' + e' = o1.val.length := by omega
          rw [hidx, ho2, getD_append_eq, hblock, hii, hee]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : e1.val = 8 := by rw [← hdig] at he1 ⊢; scalar_tac
      rw [heq] at hlen1 hval1
      exact ⟨hlen1, hwf1, hval1⟩
  · exact ⟨he, hlen, hwf, hval⟩

/-- The outer loop of `gadget::gadget_decompose`: one block of `8` digit slots per row. -/
theorem gadget_decompose_outer_loop_spec {rows : ℕ} (x : linalg.PolyVec)
    (digits degree r : Std.Usize) (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hx : WfVec rows x) (hmax : 8 * rows ≤ Usize.max)
    (hdig : digits.val = 8) (hdeg : degree.val = N) (hr : r.val = rows)
    (hi : i.val ≤ rows) (hlen : out.val.length = 8 * i.val)
    (hwf : ∀ y ∈ out.val, Wf y)
    (hval : ∀ i' e' : ℕ, e' < 8 → 8 * i' + e' < 8 * i.val →
      toRq (out.val.getD (8 * i' + e') (alloc.vec.Vec.new cpoly.field.Fp))
        = digitBlock x i' e') :
    gadget.gadget_decompose_loop0 x digits degree r out i
      ⦃ z => z.val.length = 8 * rows ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ i' e' : ℕ, e' < 8 → 8 * i' + e' < 8 * rows →
          toRq (z.val.getD (8 * i' + e') (alloc.vec.Vec.new cpoly.field.Fp))
            = digitBlock x i' e' ⦄ := by
  rw [gadget.gadget_decompose_loop0]
  apply loop.spec_decr_nat (fun s => r.val - s.2.val)
    (fun s => s.2.val ≤ rows ∧ s.1.val.length = 8 * s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ i' e' : ℕ, e' < 8 → 8 * i' + e' < 8 * s.2.val →
        toRq (s.1.val.getD (8 * i' + e') (alloc.vec.Vec.new cpoly.field.Fp))
          = digitBlock x i' e')
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [gadget.gadget_decompose_loop0.body]
    by_cases hlt : i1 < r
    · rw [if_pos hlt]
      have hilt : i1.val < rows := by rw [← hr]; scalar_tac
      have hmid := gadget_decompose_digit_loop_spec x digits degree i1 o1 0#usize
        hx hmax hdig hdeg hilt (by simp) (by simpa using hlen1) hwf1
        (by simpa using hval1)
      step with hmid as ⟨o2, hlen2, hwf2, hval2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by omega, ?_, ?_, ?_, ?_⟩
      · rw [hi2, hlen2]; ring
      · exact hwf2
      · intro i' e' he' hb
        rw [hi2] at hb
        exact hval2 i' e' he' (by omega)
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = rows := by rw [← hr] at hi1 ⊢; scalar_tac
      rw [heq] at hlen1 hval1
      exact ⟨hlen1, hwf1, hval1⟩
  · exact ⟨hi, hlen, hwf, hval⟩

-- The statement as it was first written here,
--
--     theorem gadget_decompose_spec {rows : ℕ} (x : linalg.PolyVec) (hx : WfVec rows x) :
--       gadget.gadget_decompose x
--         ⦃ z => WfVec (rows * 8) z ∧ toVec (k := rows * 8) z
--           = gadgetDecompose Φ dd (toVec (k := rows) x) ⦄
--
-- is *false*, and the proof below is what shows why: the Rust grows `out` with
-- `Vec::push`, whose extracted model fails once the vector has `Usize.max` entries,
-- so `gadget_decompose` diverges from `ok` as soon as `8 * rows` exceeds that. The
-- input `x` only bounds `rows` itself (`rows ≤ Usize.max`, from `x`'s own carrier
-- invariant), never `8 * rows`. Note that the missing bound is exactly what the
-- postcondition asserts anyway -- `WfVec (rows * 8) z` forces `z`'s length, hence
-- `8 * rows`, below `Usize.max` -- so adding it as a hypothesis weakens nothing
-- that the conclusion did not already carry.

/-- `gadget::gadget_decompose` — ArkLib's `gadgetDecompose` at `dd`.

`hmax` is the capacity side condition of the output vector: the Rust pushes
`8 * rows` ring elements into a `Vec`, which the extracted model only permits below
`Usize.max`. Every use in this file supplies it at a numeral. -/
theorem gadget_decompose_spec {rows : ℕ} (x : linalg.PolyVec) (hx : WfVec rows x)
    (hmax : 8 * rows ≤ Usize.max) :
    gadget.gadget_decompose x
      ⦃ z => WfVec (rows * 8) z ∧ toVec (k := rows * 8) z
        = gadgetDecompose Φ dd (toVec (k := rows) x) ⦄ := by
  have hdig : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  have hdeg : (params.RING_DEGREE).val = N := by simp
  rw [gadget.gadget_decompose]
  simp only [linalg.PolyVec.len, linalg.PolyVec.new, bind_ok_id]
  apply spec_mono (gadget_decompose_outer_loop_spec x params.GADGET_DIGITS
    params.RING_DEGREE (alloc.vec.Vec.len x) (alloc.vec.Vec.new ring.Rq) 0#usize
    hx hmax hdig hdeg (by simpa using hx.1) (by simp) (by simp)
    (by intro y hy; simp at hy) (by intro i' e' _ hb; simp at hb))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨by rw [hzlen]; ring, hzwf⟩, ?_⟩
  funext m
  have hm : m.val < rows * 8 := m.isLt
  have he'lt : m.val % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hi'lt : m.val / 8 < rows := by omega
  have hsplit : 8 * (m.val / 8) + m.val % 8 = m.val := by omega
  have hfp : (finProdFinEquiv (⟨m.val / 8, hi'lt⟩, ⟨m.val % 8, he'lt⟩) : Fin (rows * 8))
      = m := by
    apply Fin.ext
    show m.val % 8 + 8 * (m.val / 8) = m.val
    omega
  -- `gadgetDecompose Φ dd` is `gadgetDecomposeFun Φ dd.digit` by definition
  -- (ArkLib PR #847 folded the per-`dd` `gadgetDecompose_apply` into it).
  have hgd : gadgetDecompose Φ dd (toVec (k := rows) x)
      (finProdFinEquiv (⟨m.val / 8, hi'lt⟩, ⟨m.val % 8, he'lt⟩))
      = Rq.ofFinCoeff Φ Φ.φ.natDegree
          (fun k => dd.digit ((toVec (k := rows) x ⟨m.val / 8, hi'lt⟩).1.coeff k)
            ⟨m.val % 8, he'lt⟩) :=
    gadgetDecomposeFun_apply Φ dd.digit (toVec (k := rows) x) _ _
  rw [hfp] at hgd
  rw [hgd]
  simp only [toVec]
  have hz := hzval (m.val / 8) (m.val % 8) he'lt (by omega)
  rw [hsplit] at hz
  rw [hz, digitBlock, RqBridge.phi_natDegree]
  rfl

/-- **Every word `gadget_decompose` writes is below the base.**

The precondition of `PreparedMatrix::apply_digits`, and the one thing about the
unsigned decomposition that nothing above says: `digit_at_spec` gives `Red`,
which is `< q`, and `gadget_decompose_spec` speaks about `Rq`s rather than about
their `u64` representatives.

Derived from `gadget_decompose_spec` rather than proved by a second induction
over its three loops -- the represented block *is* `dd.digit` of the input
coefficient, and `dd_digit_val_lt` bounds that. A separate theorem rather than a
conjunct, because `gadget_decompose_spec` is audited by name and its three call
sites do not need this; `AuxCode.spec_and` puts the two together where they are
both wanted. -/
theorem gadget_decompose_digit_words {rows : ℕ} (x : linalg.PolyVec) (hx : WfVec rows x)
    (hmax : 8 * rows ≤ Usize.max) :
    gadget.gadget_decompose x
      ⦃ z => ∀ y ∈ z.val, ∀ w ∈ y.val, w.val < 16 ⦄ := by
  apply spec_mono (gadget_decompose_spec x hx hmax)
  rintro z ⟨hWz, hzval⟩
  intro y hy w hw
  obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hy
  obtain ⟨t, ht, htw⟩ := List.getElem_of_mem hw
  have hjr : j < rows * 8 := by rw [← hWz.1]; exact hj
  have hWy : Wf y := hWz.2 y hy
  have htN : t < N := by rw [← hWy.1]; exact ht
  have hred : w.val < q := hWy.2 w hw
  have hyd : z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp) = y := by
    rw [List.getD_eq_getElem _ _ hj, hjy]
  -- the block index, split exactly as `gadget_decompose_spec` splits it
  have he'lt : j % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hi'lt : j / 8 < rows := by omega
  have hfp : (finProdFinEquiv (⟨j / 8, hi'lt⟩, ⟨j % 8, he'lt⟩) : Fin (rows * 8))
      = ⟨j, hjr⟩ := by
    apply Fin.ext
    show j % 8 + 8 * (j / 8) = j
    omega
  have hgd : gadgetDecompose Φ dd (toVec (k := rows) x) ⟨j, hjr⟩
      = Rq.ofFinCoeff Φ Φ.φ.natDegree
          (fun k => dd.digit ((toVec (k := rows) x ⟨j / 8, hi'lt⟩).1.coeff k)
            ⟨j % 8, he'lt⟩) := by
    rw [← hfp]
    exact gadgetDecomposeFun_apply Φ dd.digit (toVec (k := rows) x) _ _
  -- so the word is a digit, and a digit's canonical value is below the base
  have hcoeff : coeffK y t
      = dd.digit ((toVec (k := rows) x ⟨j / 8, hi'lt⟩).1.coeff t) ⟨j % 8, he'lt⟩ := by
    have h1 : (toVec (k := rows * 8) z ⟨j, hjr⟩).1.coeff t = coeffK y t := by
      simp only [toVec]
      rw [hyd, toRq_coeff_eq_coeffK hWy]
    rw [← h1, hzval, hgd, Rq.ofFinCoeff_coeff Φ _ (Rq.phi_natDegree_le_degree Φ) t,
      if_pos (by rw [RqBridge.phi_natDegree]; exact htN)]
  have hlt := dd_digit_val_lt
    ((toVec (k := rows) x ⟨j / 8, hi'lt⟩).1.coeff t) ⟨j % 8, he'lt⟩
  rw [← hcoeff] at hlt
  have hwv : coeffK y t = ((w.val : ℕ) : ZMod q) := by
    simp only [coeffK, toK]
    rw [List.getD_eq_getElem _ _ ht, htw]
  rw [hwv, ZMod.val_natCast, Nat.mod_eq_of_lt hred] at hlt
  exact hlt

/-- **The gadget is lawful**, as a statement about the *Rust*: the extracted
`gadget_mul` inverts the extracted `gadget_decompose`. A corollary of the two
specs above and the specification's `gadgetDecompose_lawful`, and the property the
scheme's correctness rests on. Worth stating separately because it is the one
claim about this layer a reader can check against the test suite
(`tests/gadget_semantics.rs::gadget_mul_inverts_gadget_decompose`).

`hmax` is the capacity side condition inherited from `gadget_decompose_spec`; see the
note there for why it cannot be dropped. -/
theorem gadget_round_trip {rows : ℕ} (r : Std.Usize) (x : linalg.PolyVec)
    (hr : r.val = rows) (hx : WfVec rows x) (hmax : 8 * rows ≤ Usize.max) :
    (do let d ← gadget.gadget_decompose x; gadget.gadget_mul r d)
      ⦃ z => WfVec rows z ∧ toVec (k := rows) z = toVec (k := rows) x ⦄ := by
  step with gadget_decompose_spec x hx hmax as ⟨d, hWd, hd⟩
  apply spec_mono (gadget_mul_spec r d hr hWd)
  rintro z ⟨hWz, hz⟩
  refine ⟨hWz, ?_⟩
  rw [hz, hd]
  exact gadgetDecompose_lawful Φ (rows := rows) (by norm_num)
    (by rw [RqBridge.phi_natDegree]; norm_num) dd (toVec (k := rows) x)

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

-- The v4.33 kernel replays this proof (and the two sibling norm specs below)
-- deeper than the default recursion limit; the bumps are scoped per declaration.
set_option maxRecDepth 4096 in
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

set_option maxRecDepth 4096 in
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

set_option maxRecDepth 4096 in
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

/-! ### Deciding equality of vectors

`verify_weak` is an equality of *decisions*, so the two equality checks the Rust makes
(`A sᵢ = G t̂ᵢ` and `B t̂ = u`) have to be matched by the specification's `Simple.verify`,
which is a `decide`. `poly_vec_equals_spec` is the `↔` that lets them be. -/

/-- Two extracted vectors represent the same `PolyVec` exactly when they agree
entrywise below `k`. -/
theorem toVec_eq_iff {k : ℕ} (v w : linalg.PolyVec) :
    toVec (k := k) v = toVec (k := k) w
      ↔ ∀ j < k, toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (w.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) := by
  constructor
  · intro h j hj
    exact congrFun h ⟨j, hj⟩
  · intro h
    funext i
    exact h i.val i.isLt

/-- The loop of `PolyVec::equals`. -/
theorem poly_vec_equals_loop_spec {k : ℕ} (v w : linalg.PolyVec) (n i : Std.Usize) (same : Bool)
    (hv : WfVec k v) (hw : WfVec k w) (hn : n.val = k) (hi : i.val ≤ k)
    (hsame : same = true ↔ ∀ j < i.val, toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
      = toRq (w.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))) :
    linalg.PolyVec.equals_loop v w n i same
      ⦃ r => r = true ↔ ∀ j < k, toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (w.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [linalg.PolyVec.equals_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.1.val)
    (fun s => s.1.val ≤ k ∧ (s.2 = true ↔ ∀ j < s.1.val,
      toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (w.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))))
  · rintro ⟨i1, s1⟩ ⟨hi1, hs1⟩
    dsimp only at hi1 hs1
    simp only [linalg.PolyVec.equals_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hilt : i1.val < k := by rw [← hn]; scalar_tac
      have hvlt : i1.val < v.val.length := by rw [hv.1]; exact hilt
      have hwlt : i1.val < w.val.length := by rw [hw.1]; exact hilt
      step as ⟨r, hr⟩
      step as ⟨r1, hr1⟩
      have hWr : Wf r := by rw [hr]; exact hv.2 _ (List.getElem_mem hvlt)
      have hWr1 : Wf r1 := by rw [hr1]; exact hw.2 _ (List.getElem_mem hwlt)
      step with RqBridge.equals_spec r r1 hWr hWr1 as ⟨b, hb⟩
      have hite : (if b then ok s1 else ok (false : Bool)) ⦃ z => z = (s1 && b) ⦄ := by
        cases b
        · rw [if_neg (by simp), WP.spec_ok]; simp
        · rw [if_pos (by simp), WP.spec_ok]; simp
      step with hite as ⟨s2, hs2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by omega, ?_, ?_⟩
      · rw [hs2, hi2, Bool.and_eq_true, hs1, hb, hr, hr1]
        constructor
        · rintro ⟨h1, h2⟩ j hj
          rcases Nat.lt_or_ge j i1.val with h | h
          · exact h1 j h
          · have hje : j = i1.val := by omega
            subst hje
            rw [List.getD_eq_getElem _ _ hvlt, List.getD_eq_getElem _ _ hwlt]
            exact h2
        · intro h
          refine ⟨fun j hj => h j (by omega), ?_⟩
          have h2 := h i1.val (by omega)
          rwa [List.getD_eq_getElem _ _ hvlt, List.getD_eq_getElem _ _ hwlt] at h2
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = k := by rw [← hn] at hi1 ⊢; scalar_tac
      rw [← heq]; exact hs1
  · exact ⟨hi, hsame⟩

/-- `PolyVec::equals` — decides equality of the represented vectors.

An `↔`, for the same reason `Rq::equals` is one: the specification's `Simple.verify`
is a `decide`, so only a two-way statement makes the *rejecting* runs of the Rust
part of the claim. -/
theorem poly_vec_equals_spec {k : ℕ} (v w : linalg.PolyVec) (hv : WfVec k v) (hw : WfVec k w) :
    linalg.PolyVec.equals v w
      ⦃ r => r = true ↔ toVec (k := k) v = toVec (k := k) w ⦄ := by
  have h1 : (alloc.vec.Vec.len v).val = k := by simpa using hv.1
  have h2 : (alloc.vec.Vec.len w).val = k := by simpa using hw.1
  rw [linalg.PolyVec.equals]
  have hne : (alloc.vec.Vec.len v != alloc.vec.Vec.len w) = false := by
    simp only [bne_eq_false_iff_eq]
    scalar_tac
  rw [hne, if_neg (by simp)]
  apply spec_mono (poly_vec_equals_loop_spec v w (alloc.vec.Vec.len v) 0#usize true
    hv hw h1 (by simp) (by simp))
  intro r hr
  rw [hr, toVec_eq_iff]

/-! ## The commitment

The specification's scheme is generic in six dimensions; these statements fix them
at `params.rs`'s values. `WfParams` and `WfDecomp` are the shape conditions that
make the two sides comparable at all -- the extracted structures carry `Vec`s
whose lengths nothing in the type system pins. -/

/-- Shape invariant of the public parameters: the two Ajtai matrices are of the
shapes `PublicParams` fixes. -/
def WfParams (pp : commit.PublicParams) : Prop :=
  WfMat 1 (1024 * 8) pp.inner_matrix ∧ WfMat 1 (1024 * (1 * 8)) pp.outer_matrix

/-- Shape invariant of the decomposition data. -/
def WfDecomp (d : commit.Decomp) : Prop :=
  (d.message.val.length = 1024 ∧ ∀ s ∈ d.message.val, WfVec (1024 * 8) s) ∧
  (d.inner_decomp.val.length = 1024 ∧ ∀ t ∈ d.inner_decomp.val, WfVec (1 * 8) t)

/-- The specification's public parameters that an extracted `PublicParams`
represents. -/
def toParams (pp : commit.PublicParams) : InnerOuter.PublicParams Φ 1 1024 8 1 1024 8 where
  innerMatrix := toMat (rows := 1) (cols := 1024 * 8) pp.inner_matrix
  outerMatrix := toMat (rows := 1) (cols := 1024 * (1 * 8)) pp.outer_matrix

/-- The specification's decomposition data that an extracted `Decomp` represents. -/
def toDecompSpec (d : commit.Decomp) : InnerOuter.Decomp Φ 1 1024 8 1024 8 where
  message := fun i => toVec (k := 1024 * 8) (d.message.val.getD i.val
    (alloc.vec.Vec.new ring.Rq))
  innerDecomp := fun i => toVec (k := 1 * 8) (d.inner_decomp.val.getD i.val
    (alloc.vec.Vec.new ring.Rq))

/-- The specification's weak opening that an extracted `Opening` represents. -/
def toOpening (o : commit.Opening) : InnerOuter.Opening Φ 1 1024 8 1024 8 where
  toDecomp := toDecompSpec o.decomp
  challenge := toVec (k := 1024) o.challenge

/-- `commit::generate_decomps` — ArkLib's `generateDecomps` at
`Decomposition.ofDigits dd dd`: per block `sᵢ = G⁻¹(mᵢ)` and `t̂ᵢ = G⁻¹(A sᵢ)`.

Both halves matter. The shape half (`WfDecomp`) is what the layer above needs to
apply anything; the agreement half is what makes it the specification's
decomposition and not merely a decomposition of the right shape. -/
theorem generate_decomps_loop_spec (pp : commit.PublicParams)
    (m : alloc.vec.Vec linalg.PolyVec) (blocks : Std.Usize)
    (prep : linalg.PreparedMatrix)
    (ss ts : alloc.vec.Vec linalg.PolyVec) (i : Std.Usize)
    (hpp : WfParams pp) (hprep : WfPrep2 1 (1024 * 8) prep pp.inner_matrix)
    (hm : m.val.length = 1024 ∧ ∀ x ∈ m.val, WfVec 1024 x)
    (hb : blocks.val = 1024) (hi : i.val ≤ 1024)
    (hss : ss.val.length = i.val) (hts : ts.val.length = i.val)
    (hWss : ∀ y ∈ ss.val, WfVec (1024 * 8) y) (hWts : ∀ y ∈ ts.val, WfVec (1 * 8) y)
    (hvss : ∀ j < i.val, toVec (k := 1024 * 8) (ss.val.getD j (alloc.vec.Vec.new ring.Rq))
      = gadgetDecompose Φ dd (toVec (k := 1024) (m.val.getD j (alloc.vec.Vec.new ring.Rq))))
    (hvts : ∀ j < i.val, toVec (k := 1 * 8) (ts.val.getD j (alloc.vec.Vec.new ring.Rq))
      = gadgetDecompose Φ dd (ArkLib.Lattices.matVecMul
          (toMat (rows := 1) (cols := 1024 * 8) pp.inner_matrix)
          (gadgetDecompose Φ dd
            (toVec (k := 1024) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))))) :
    commit.generate_decomps_loop m blocks prep ss ts i
      ⦃ r => r.1.val.length = 1024 ∧ r.2.val.length = 1024 ∧
        (∀ y ∈ r.1.val, WfVec (1024 * 8) y) ∧ (∀ y ∈ r.2.val, WfVec (1 * 8) y) ∧
        (∀ j < 1024, toVec (k := 1024 * 8) (r.1.val.getD j (alloc.vec.Vec.new ring.Rq))
          = gadgetDecompose Φ dd
              (toVec (k := 1024) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))) ∧
        (∀ j < 1024, toVec (k := 1 * 8) (r.2.val.getD j (alloc.vec.Vec.new ring.Rq))
          = gadgetDecompose Φ dd (ArkLib.Lattices.matVecMul
              (toMat (rows := 1) (cols := 1024 * 8) pp.inner_matrix)
              (gadgetDecompose Φ dd
                (toVec (k := 1024) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))))) ⦄ := by
  rw [commit.generate_decomps_loop]
  apply loop.spec_decr_nat (fun s => blocks.val - s.2.2.val)
    (fun s => s.2.2.val ≤ 1024 ∧ s.1.val.length = s.2.2.val ∧ s.2.1.val.length = s.2.2.val ∧
      (∀ y ∈ s.1.val, WfVec (1024 * 8) y) ∧ (∀ y ∈ s.2.1.val, WfVec (1 * 8) y) ∧
      (∀ j < s.2.2.val, toVec (k := 1024 * 8) (s.1.val.getD j (alloc.vec.Vec.new ring.Rq))
        = gadgetDecompose Φ dd
            (toVec (k := 1024) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))) ∧
      (∀ j < s.2.2.val, toVec (k := 1 * 8) (s.2.1.val.getD j (alloc.vec.Vec.new ring.Rq))
        = gadgetDecompose Φ dd (ArkLib.Lattices.matVecMul
            (toMat (rows := 1) (cols := 1024 * 8) pp.inner_matrix)
            (gadgetDecompose Φ dd
              (toVec (k := 1024) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))))))
  · rintro ⟨s1, t1, i1⟩ ⟨hi1, hs1, ht1, hWs1, hWt1, hvs1, hvt1⟩
    dsimp only at hi1 hs1 ht1 hWs1 hWt1 hvs1 hvt1
    simp only [commit.generate_decomps_loop.body]
    by_cases hlt : i1 < blocks
    · rw [if_pos hlt]
      have hilt : i1.val < m.val.length := by rw [hm.1, ← hb]; scalar_tac
      step as ⟨pv, hpv⟩
      have hWpv : WfVec 1024 pv := by rw [hpv]; exact hm.2 _ (List.getElem_mem hilt)
      -- the value spec and the digit bound at once: `apply_digits` needs both,
      -- and neither theorem changes to provide it
      step with HachiEquiv.AuxCode.spec_and
        (gadget_decompose_spec (rows := 1024) pv hWpv (by scalar_tac))
        (gadget_decompose_digit_words (rows := 1024) pv hWpv (by scalar_tac))
        as ⟨s, hWs, hs, hsd⟩
      have hsdv : DigitVec (1024 * 8) s := by
        intro u hu
        refine HachiEquiv.AuxFused.digitWf_of_mem (fun w hw => hsd _ ?_ w hw)
        rw [List.getD_eq_getElem _ _ (by rw [hWs.1]; exact hu)]
        exact List.getElem_mem _
      step with apply_digits_spec (rows := 1) (cols := 1024 * 8) prep pp.inner_matrix s
        hpp.1 hWs hsdv hprep as ⟨inner, hWinner, hinner⟩
      step with gadget_decompose_spec (rows := 1) inner hWinner (by scalar_tac)
        as ⟨t, hWt, ht⟩
      step as ⟨t2, ht2⟩
      step as ⟨s2, hs2⟩
      step as ⟨i2, hi2⟩
      have hmi : m.val.getD i1.val (alloc.vec.Vec.new ring.Rq) = pv := by
        rw [hpv]; exact List.getD_eq_getElem _ _ hilt
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hs2, hi2, List.length_append, hs1]; simp
      · rw [ht2, hi2, List.length_append, ht1]; simp
      · intro y hy
        rw [hs2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hWs1 y h
        · rw [List.mem_singleton.mp h]; exact hWs
      · intro y hy
        rw [ht2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hWt1 y h
        · rw [List.mem_singleton.mp h]; exact hWt
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [hs2, getD_append_lt _ _ _ (by omega), hvs1 j hjlt]
        · have hjeq : j = s1.val.length := by omega
          rw [hjeq, hs2, getD_append_eq, hs, hs1, hmi]
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [ht2, getD_append_lt _ _ _ (by omega), hvt1 j hjlt]
        · have hjeq : j = t1.val.length := by omega
          rw [hjeq, ht2, getD_append_eq, ht, hinner, hs, ht1, hmi]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = 1024 := by rw [← hb] at hi1 ⊢; scalar_tac
      rw [heq] at hs1 ht1 hvs1 hvt1
      exact ⟨hs1, ht1, hWs1, hWt1, hvs1, hvt1⟩
  · exact ⟨hi, hss, hts, hWss, hWts, hvss, hvts⟩

/-- `commit::generate_decomps` — see the docstring above. -/
theorem generate_decomps_spec (pp : commit.PublicParams) (m : alloc.vec.Vec linalg.PolyVec)
    (hpp : WfParams pp) (hm : m.val.length = 1024 ∧ ∀ x ∈ m.val, WfVec 1024 x) :
    commit.generate_decomps pp m
      ⦃ d => WfDecomp d ∧ toDecompSpec d
        = InnerOuter.generateDecomps Φ (InnerOuter.Decomposition.ofDigits Φ dd dd)
            (toParams pp)
            (fun i : Fin 1024 => toVec (k := 1024) (m.val.getD i.val
              (alloc.vec.Vec.new ring.Rq))) ⦄ := by
  rw [commit.generate_decomps]
  simp only [commit.Decomp.new, commit.PublicParams.impl.inner_matrix]
  -- the one prepared matrix, hoisted above the block loop: 192 MiB paid once
  step with prepare_digits_spec (rows := 1) (cols := 1024 * 8) pp.inner_matrix hpp.1
    (by norm_num) (by have h := usize_max_ge'; norm_num [N]; omega) as ⟨prep, hprep⟩
  step with generate_decomps_loop_spec pp m (alloc.vec.Vec.len m) prep
    (alloc.vec.Vec.new linalg.PolyVec) (alloc.vec.Vec.new linalg.PolyVec) 0#usize
    hpp hprep hm (by simpa using hm.1) (by simp) (by simp) (by simp)
    (by intro y hy; simp at hy) (by intro y hy; simp at hy)
    (by intro j hj; simp at hj) (by intro j hj; simp at hj)
    as ⟨ss, ts, hsl, htl, hWs, hWt, hvs, hvt⟩
  refine ⟨⟨⟨hsl, hWs⟩, ⟨htl, hWt⟩⟩, ?_⟩
  show (toDecompSpec ⟨ss, ts⟩ : InnerOuter.Decomp Φ 1 1024 8 1024 8) = _
  simp only [toDecompSpec, InnerOuter.generateDecomps, InnerOuter.Decomposition.ofDigits,
    InnerOuter.Decomp.mk.injEq]
  constructor
  · funext i; exact hvs i.val i.isLt
  · funext i; exact hvt i.val i.isLt

/-- The loop of `commit::derived_message`: one gadget product per block. -/
theorem derived_message_loop_spec (d : commit.Decomp) (blocks : Std.Usize)
    (out : alloc.vec.Vec linalg.PolyVec) (i : Std.Usize)
    (hd : WfDecomp d) (hb : blocks.val = 1024) (hi : i.val ≤ 1024)
    (hlen : out.val.length = i.val) (hwf : ∀ y ∈ out.val, WfVec 1024 y)
    (hval : ∀ j < i.val, toVec (k := 1024) (out.val.getD j (alloc.vec.Vec.new ring.Rq))
      = gadgetMul Φ (16 : ZMod q)
          (toVec (k := 1024 * 8) (d.message.val.getD j (alloc.vec.Vec.new ring.Rq)))) :
    commit.derived_message_loop d blocks params.MESSAGE_ROWS out i
      ⦃ z => z.val.length = 1024 ∧ (∀ y ∈ z.val, WfVec 1024 y) ∧
        ∀ j < 1024, toVec (k := 1024) (z.val.getD j (alloc.vec.Vec.new ring.Rq))
          = gadgetMul Φ (16 : ZMod q)
              (toVec (k := 1024 * 8) (d.message.val.getD j (alloc.vec.Vec.new ring.Rq))) ⦄ := by
  have hmr : (params.MESSAGE_ROWS).val = 1024 := by simp [params.MESSAGE_ROWS]
  rw [commit.derived_message_loop]
  apply loop.spec_decr_nat (fun s => blocks.val - s.2.val)
    (fun s => s.2.val ≤ 1024 ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, WfVec 1024 y) ∧
      ∀ j < s.2.val, toVec (k := 1024) (s.1.val.getD j (alloc.vec.Vec.new ring.Rq))
        = gadgetMul Φ (16 : ZMod q)
            (toVec (k := 1024 * 8) (d.message.val.getD j (alloc.vec.Vec.new ring.Rq))))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [commit.derived_message_loop.body]
    by_cases hlt : i1 < blocks
    · rw [if_pos hlt]
      have hilt : i1.val < d.message.val.length := by rw [hd.1.1, ← hb]; scalar_tac
      simp only [commit.Decomp.impl.message]
      step as ⟨pv, hpv⟩
      have hWpv : WfVec (1024 * 8) pv := by
        rw [hpv]; exact hd.1.2 _ (List.getElem_mem hilt)
      step with gadget_mul_spec (rows := 1024) params.MESSAGE_ROWS pv hmr hWpv as ⟨pv1, hW1, h1⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hW1
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 j hjlt]
        · have hjeq : j = o1.val.length := by omega
          rw [hjeq, ho2, getD_append_eq, h1, hpv, hlen1,
            ← List.getD_eq_getElem _ _ hilt]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = 1024 := by rw [← hb] at hi1 ⊢; scalar_tac
      rw [heq] at hlen1 hval1
      exact ⟨hlen1, hwf1, hval1⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- `commit::derived_message` — ArkLib's `derivedMessage`, `mᵢ = G · sᵢ`
([NOZ26] Eq. (13)): the message a weak opening does not store but determines. -/
theorem derived_message_spec (d : commit.Decomp) (hd : WfDecomp d) :
    commit.derived_message d
      ⦃ out => (out.val.length = 1024 ∧ ∀ x ∈ out.val, WfVec 1024 x) ∧
        (fun i : Fin 1024 => toVec (k := 1024) (out.val.getD i.val (alloc.vec.Vec.new ring.Rq)))
          = InnerOuter.derivedMessage Φ (16 : ZMod q) (toDecompSpec d) ⦄ := by
  rw [commit.derived_message]
  simp only [commit.Decomp.blocks]
  apply spec_mono (derived_message_loop_spec d (alloc.vec.Vec.len d.message)
    (alloc.vec.Vec.new linalg.PolyVec) 0#usize hd (by simpa using hd.1.1) (by simp)
    (by simp) (by intro y hy; simp at hy) (by intro j hj; simp at hj))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i
  exact hzval i.val i.isLt

/-- `commit::commit_with_decomps` — ArkLib's `commitWithDecomps`,
`u = B · flatten(t̂)`. -/
theorem commit_with_decomps_spec (pp : commit.PublicParams) (d : commit.Decomp)
    (hpp : WfParams pp) (hd : WfDecomp d) :
    commit.commit_with_decomps pp d
      ⦃ u => WfVec 1 u ∧ toVec (k := 1) u
        = InnerOuter.commitWithDecomps Φ (toParams pp) (toDecompSpec d) ⦄ := by
  rw [commit.commit_with_decomps]
  simp only [commit.Decomp.inner_decomps, commit.PublicParams.impl.outer_matrix]
  step with flatten_blocks_spec (blocks := 1024) (width := 1 * 8) d.inner_decomp
    (by scalar_tac) hd.2 as ⟨flat, hWflat, hflat⟩
  apply spec_mono (mat_vec_mul_spec (rows := 1) (cols := 1024 * (1 * 8))
    pp.outer_matrix flat hpp.2 hWflat)
  rintro u ⟨hWu, hu⟩
  refine ⟨hWu, ?_⟩
  rw [hu, hflat]
  rfl

/-! ### The weak verifier

`verify_weak` accumulates a `Bool` through a chain of `if … then false else …`
guards; the two lemmas below are what each of those links is, and `BlockVerifies`
names the per-block conjunction the loop is deciding. -/

/-- A rejecting guard: `if c then false else x` accepts exactly when `c` fails and
`x` already accepted. -/
theorem ite_false_spec {c : Prop} [Decidable c] (x : Bool) :
    (if c then (ok false : Result Bool) else ok x) ⦃ z => z = true ↔ (¬ c ∧ x = true) ⦄ := by
  by_cases h : c
  · rw [if_pos h, WP.spec_ok]; simp [h]
  · rw [if_neg h, WP.spec_ok]; simp [h]

/-- The dual guard: `if c then x else false` accepts exactly when `c` holds and `x`
already accepted. -/
theorem ite_true_spec {c : Prop} [Decidable c] (x : Bool) :
    (if c then (ok x : Result Bool) else ok false) ⦃ z => z = true ↔ (c ∧ x = true) ⦄ := by
  by_cases h : c
  · rw [if_pos h, WP.spec_ok]; simp [h]
  · rw [if_neg h, WP.spec_ok]; simp [h]

/-- The per-block checks of `verify_weak` at block `j`, in the specification's
vocabulary: the challenge is nonzero and `ℓ₁`-short, the scaled message is
`ℓ₂²`-short, and the inner gadget relation `A sⱼ = G t̂ⱼ` holds. -/
def BlockVerifies (pp : commit.PublicParams) (o : commit.Opening) (j : ℕ) : Prop :=
  0 < Rq.l1Norm Φ (toRq (o.challenge.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))) ∧
  Rq.l1Norm Φ (toRq (o.challenge.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))) ≤ 32 ∧
  vecL2NormSq Φ (ArkLib.Lattices.scalarVecMul
      (toRq (o.challenge.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))
      (toVec (k := 1024 * 8) (o.decomp.message.val.getD j (alloc.vec.Vec.new ring.Rq)))) ≤ 41976510894886092800 ∧
  gadgetMul Φ (16 : ZMod q)
      (toVec (k := 1 * 8) (o.decomp.inner_decomp.val.getD j (alloc.vec.Vec.new ring.Rq)))
    = ArkLib.Lattices.matVecMul (toMat (rows := 1) (cols := 1024 * 8) pp.inner_matrix)
      (toVec (k := 1024 * 8) (o.decomp.message.val.getD j (alloc.vec.Vec.new ring.Rq)))

/-- The `ℓ₂²` accumulator of `vec_l2_norm_sq` cannot overflow at the crate's message
width: `128 · N · (q/2)² < 2¹²⁸`. -/
theorem l2_norm_sq_message_fits : (1024 * 8) * (N * (q / 2) ^ 2) ≤ U128.max := by
  norm_num [U128.max, U128.numBits]

/-- The loop of `commit::verify_weak`: the accumulated `Bool` decides exactly the
per-block checks at the blocks already visited. -/
theorem verify_weak_loop_spec (pp : commit.PublicParams) (o : commit.Opening)
    (blocks : Std.Usize) (ok1 : Bool) (i : Std.Usize)
    (hpp : WfParams pp) (hoc : WfVec 1024 o.challenge) (ho : WfDecomp o.decomp)
    (hb : blocks.val = 1024) (hi : i.val ≤ 1024)
    (hok : ok1 = true ↔ ∀ j < i.val, BlockVerifies pp o j) :
    commit.verify_weak_loop pp o o.decomp blocks ok1 i
      ⦃ r => r = true ↔ ∀ j < 1024, BlockVerifies pp o j ⦄ := by
  have hir : (params.INNER_ROWS).val = 1 := by simp [params.INNER_ROWS]
  have hk : (params.KAPPA).val = 32 := by simp [params.KAPPA]
  have hbs : (params.BETA_SQ).val = 41976510894886092800 := by simp [params.BETA_SQ]
  rw [commit.verify_weak_loop]
  apply loop.spec_decr_nat (fun s => blocks.val - s.2.val)
    (fun s => s.2.val ≤ 1024 ∧ (s.1 = true ↔ ∀ j < s.2.val, BlockVerifies pp o j))
  · rintro ⟨b1, i1⟩ ⟨hi1, hb1⟩
    dsimp only at hi1 hb1
    simp only [commit.verify_weak_loop.body]
    by_cases hlt : i1 < blocks
    · rw [if_pos hlt]
      have hilt : i1.val < 1024 := by rw [← hb]; scalar_tac
      have hclt : i1.val < o.challenge.val.length := by rw [hoc.1]; exact hilt
      have hmlt : i1.val < o.decomp.message.val.length := by rw [ho.1.1]; exact hilt
      have hdlt : i1.val < o.decomp.inner_decomp.val.length := by rw [ho.2.1]; exact hilt
      simp only [commit.Opening.impl.challenge, linalg.PolyVec.get,
        commit.Decomp.impl.message, commit.Decomp.impl.inner_decomp,
        commit.PublicParams.impl.inner_matrix]
      step as ⟨c, hc⟩
      have hWc : Wf c := by rw [hc]; exact hoc.2 _ (List.getElem_mem hclt)
      step with l1_norm_spec c hWc as ⟨cl1, hcl1⟩
      step with ite_false_spec (c := (cl1 = 0#u64)) b1 as ⟨ok2, hok2⟩
      step with ite_false_spec (c := (cl1 > params.KAPPA)) ok2 as ⟨ok3, hok3⟩
      step as ⟨pv, hpv⟩
      have hWpv : WfVec (1024 * 8) pv := by rw [hpv]; exact ho.1.2 _ (List.getElem_mem hmlt)
      step with scalar_vec_mul_spec (k := 1024 * 8) c pv hWc hWpv as ⟨scaled, hWsc, hsc⟩
      step with vec_l2_norm_sq_spec (k := 1024 * 8) scaled hWsc l2_norm_sq_message_fits
        as ⟨n2, hn2⟩
      step with ite_false_spec (c := (n2 > params.BETA_SQ)) ok3 as ⟨ok4, hok4⟩
      step with mat_vec_mul_spec (rows := 1) (cols := 1024 * 8) pp.inner_matrix pv hpp.1 hWpv
        as ⟨inn, hWinn, hinn⟩
      step as ⟨pv1, hpv1⟩
      have hWpv1 : WfVec (1 * 8) pv1 := by rw [hpv1]; exact ho.2.2 _ (List.getElem_mem hdlt)
      step with gadget_mul_spec (rows := 1) params.INNER_ROWS pv1 hir hWpv1
        as ⟨recomp, hWrec, hrec⟩
      step with poly_vec_equals_spec (k := 1) recomp inn hWrec hWinn as ⟨bb, hbb⟩
      step with ite_true_spec (c := (bb = true)) ok4 as ⟨ok5, hok5⟩
      step as ⟨i2, hi2⟩
      have hcg : c = o.challenge.val.getD i1.val (alloc.vec.Vec.new cpoly.field.Fp) := by
        rw [hc, List.getD_eq_getElem _ _ hclt]
      have hpvg : pv = o.decomp.message.val.getD i1.val (alloc.vec.Vec.new ring.Rq) := by
        rw [hpv, List.getD_eq_getElem _ _ hmlt]
      have hpv1g : pv1 = o.decomp.inner_decomp.val.getD i1.val (alloc.vec.Vec.new ring.Rq) := by
        rw [hpv1, List.getD_eq_getElem _ _ hdlt]
      have hBV : BlockVerifies pp o i1.val ↔
          (0 < cl1.val ∧ cl1.val ≤ 32 ∧ n2.val ≤ 41976510894886092800 ∧ bb = true) := by
        rw [BlockVerifies, ← hcg, ← hpvg, ← hpv1g, ← hcl1, ← hsc, ← hn2, ← hrec, ← hinn, ← hbb]
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [hi2, hok5, hok4, hok3, hok2, hb1]
        constructor
        · rintro ⟨h4, h3, h2, h1, hprev⟩ j hj
          rcases Nat.lt_or_ge j i1.val with h | h
          · exact hprev j h
          · have hje : j = i1.val := by omega
            subst hje
            exact hBV.mpr ⟨by scalar_tac, by scalar_tac, by scalar_tac, h4⟩
        · intro h
          obtain ⟨g1, g2, g3, g4⟩ := hBV.mp (h i1.val (by omega))
          exact ⟨g4, by scalar_tac, by scalar_tac, by scalar_tac, fun j hj => h j (by omega)⟩
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = 1024 := by rw [← hb] at hi1 ⊢; scalar_tac
      rw [heq] at hb1; exact hb1
  · exact ⟨hi, hok⟩

/- The original statement of `verify_weak_spec`, kept for the record:

theorem verify_weak_spec (pp : commit.PublicParams) (u : linalg.PolyVec)
    (o : commit.Opening) (hpp : WfParams pp) (hu : WfVec 1 u) (ho : WfDecomp o.decomp) :
    commit.verify_weak pp u o
      ⦃ r => r = InnerOuter.verify_weak Φ (16 : ZMod q) 41976510894886092800 16 32
        (toParams pp) (toVec (k := 1) u) (toOpening o) ⦄

It is *false* in this model: `WfParams`, `WfVec 1 u` and `WfDecomp o.decomp` say
nothing at all about `o.challenge`, yet the extracted loop reads
`opening.challenge[i]` for `i < 1024` (`alloc.vec.Vec.index`, which *fails* out of
range) and then takes its `ℓ₁` norm (`commit::l1_norm`, whose specification needs a
well-formed ring element). With, say, an empty `challenge` the left-hand side is
`fail`, so no postcondition holds of it. The hypothesis `hoc : WfVec 1024 o.challenge`
below is exactly the shape condition the `Opening` type does not carry. -/

/-- `commit::verify_weak` — ArkLib's `verify_weak`, as an equality of *decisions*.

An equality of `Bool`s, not an implication: an implication in the accepting
direction is satisfied by a verifier that rejects everything, and that is exactly
the failure a correctness test cannot see. The specification's `verify_weak` is
itself `Bool`-valued (a `&&` of `List.all` over eagerly-`decide`d propositions),
which is why no `decide` appears on either side.

The three bounds are `params.rs`'s: `βSq = 41976510894886092800`, `γ = 16`,
`κ = 32`. They are the numbers `lean/Check.lean` § 1 ties to the extracted
constants, so this statement and the Rust cannot disagree about them without that
audit failing.

*Statement modified*: the hypothesis `hoc : WfVec 1024 o.challenge` was added, since
the verifier indexes and norms the challenge vector and nothing else in the
hypotheses bounds it. See the comment above. -/
theorem verify_weak_spec (pp : commit.PublicParams) (u : linalg.PolyVec)
    (o : commit.Opening) (hpp : WfParams pp) (hu : WfVec 1 u) (hoc : WfVec 1024 o.challenge)
    (ho : WfDecomp o.decomp) :
    commit.verify_weak pp u o
      ⦃ r => r = InnerOuter.verify_weak Φ (16 : ZMod q) 41976510894886092800 16 32
        (toParams pp) (toVec (k := 1) u) (toOpening o) ⦄ := by
  have hg : (params.GAMMA).val = 16 := by simp [params.GAMMA]
  rw [commit.verify_weak]
  simp only [commit.Opening.impl.decomp, commit.Decomp.blocks, commit.Decomp.inner_decomps,
    commit.PublicParams.impl.outer_matrix]
  step with verify_weak_loop_spec pp o (alloc.vec.Vec.len o.decomp.message) true 0#usize
    hpp hoc ho (by simpa using ho.1.1) (by simp) (by simp) as ⟨okA, hokA⟩
  step with flatten_blocks_spec (blocks := 1024) (width := 1 * 8) o.decomp.inner_decomp
    (by scalar_tac) ho.2 as ⟨flat, hWflat, hflat⟩
  step with vec_l_infty_norm_spec (k := 1024 * (1 * 8)) flat hWflat as ⟨ninf, hninf⟩
  step with ite_false_spec (c := (ninf > params.GAMMA)) okA as ⟨okB, hokB⟩
  step with mat_vec_mul_spec (rows := 1) (cols := 1024 * (1 * 8)) pp.outer_matrix flat hpp.2 hWflat
    as ⟨outer, hWouter, houter⟩
  step with poly_vec_equals_spec (k := 1) outer u hWouter hu as ⟨bb, hbb⟩
  apply spec_mono (ite_true_spec (c := (bb = true)) okB)
  intro r hr
  have hgam : (¬ ninf > params.GAMMA) ↔ vecLInftyNorm Φ (toVec (k := 1024 * (1 * 8)) flat) ≤ 16 := by
    constructor <;> intro h <;> scalar_tac
  rw [Bool.eq_iff_iff, hr, hokB, hokA, hbb, houter, hgam, hflat, InnerOuter.verify_weak]
  -- `decide_eq_true_eq` is deliberately absent from this simp set: at v4.33 simp
  -- re-checks the `Decidable` instance inside each `decide` against what synthesis
  -- returns here, and rejects the vector-equality instances baked into ArkLib's
  -- `verify_weak` (this file's `BEq (ZMod q)` layer diverts synthesis). The
  -- `decide P = true` conjuncts are instead converted term-level below, where
  -- plain defeq applies.
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    Simple.verify, Simple.commit, forall_const, toOpening, toParams, toDecompSpec]
  have hch : ∀ x : Fin 1024, toVec (k := 1024) o.challenge x
      = toRq (o.challenge.val.getD x.val (alloc.vec.Vec.new cpoly.field.Fp)) := fun _ => rfl
  simp only [hch, BlockVerifies, gadgetMul, Fin.forall_iff]
  constructor
  · rintro ⟨hX, hY, hZ⟩
    refine ⟨⟨fun j hj => ?_, decide_eq_true hY⟩, decide_eq_true hX⟩
    obtain ⟨a, b, c, d⟩ := hZ j hj
    exact ⟨⟨⟨decide_eq_true a, decide_eq_true b⟩, decide_eq_true c⟩, decide_eq_true d⟩
  · rintro ⟨⟨hW, hY⟩, hX⟩
    refine ⟨of_decide_eq_true hX, of_decide_eq_true hY, fun j hj => ?_⟩
    obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := hW j hj
    exact ⟨of_decide_eq_true a, of_decide_eq_true b, of_decide_eq_true c, of_decide_eq_true d⟩

/-! ### The honest committer -/

/-- `commit::commit` — decompose, then outer-commit. -/
theorem commit_spec (pp : commit.PublicParams) (m : alloc.vec.Vec linalg.PolyVec)
    (hpp : WfParams pp) (hm : m.val.length = 1024 ∧ ∀ x ∈ m.val, WfVec 1024 x) :
    commit.commit pp m
      ⦃ z => WfVec 1 z.1 ∧ WfDecomp z.2 ∧
        toDecompSpec z.2 = InnerOuter.generateDecomps Φ
            (InnerOuter.Decomposition.ofDigits Φ dd dd) (toParams pp)
            (fun i : Fin 1024 => toVec (k := 1024) (m.val.getD i.val (alloc.vec.Vec.new ring.Rq))) ∧
        toVec (k := 1) z.1
          = InnerOuter.commitWithDecomps Φ (toParams pp) (toDecompSpec z.2) ⦄ := by
  rw [commit.commit]
  step with generate_decomps_spec pp m hpp hm as ⟨d, hWd, hdspec⟩
  step with commit_with_decomps_spec pp d hpp hWd as ⟨u, hWu, huspec⟩
  exact ⟨hWu, hWd, hdspec, huspec⟩

/-- The loop of `Opening::honest`: it pushes `blocks` copies of `1`. -/
theorem honest_loop_spec (blocks : Std.Usize) (ones : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hb : blocks.val = 1024) (hi : i.val ≤ 1024) (hlen : ones.val.length = i.val)
    (hwf : ∀ x ∈ ones.val, Wf x)
    (hval : ∀ j < i.val, toRq (ones.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) = 1) :
    commit.Opening.honest_loop blocks ones i
      ⦃ z => WfVec 1024 z ∧
        ∀ j < 1024, toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) = 1 ⦄ := by
  rw [commit.Opening.honest_loop]
  apply loop.spec_decr_nat (fun s => blocks.val - s.2.val)
    (fun s => s.2.val ≤ 1024 ∧ s.1.val.length = s.2.val ∧ (∀ x ∈ s.1.val, Wf x) ∧
      ∀ j < s.2.val, toRq (s.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) = 1)
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [commit.Opening.honest_loop.body]
    by_cases hlt : i1 < blocks
    · rw [if_pos hlt]
      have hcap : o1.val.length < Usize.max := by rw [hlen1]; scalar_tac
      step as ⟨r, hWr, hr⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro x hx
        rw [ho2] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hwf1 x h
        · rw [List.mem_singleton.mp h]; exact hWr
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with h | h
        · rw [ho2, getD_append_lt _ _ _ (by omega)]; exact hval1 j h
        · have hje : j = o1.val.length := by omega
          rw [hje, ho2, getD_append_eq]; exact hr
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = 1024 := by rw [← hb] at hi1 ⊢; scalar_tac
      rw [heq] at hlen1 hval1
      exact ⟨⟨hlen1, hwf1⟩, hval1⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- `Opening::honest` — the committer's weak opening: its decomposition data unchanged,
with the trivial challenge `cᵢ = 1` in every block. -/
theorem honest_spec (d : commit.Decomp) (hd : WfDecomp d) :
    commit.Opening.honest d
      ⦃ o => o.decomp = d ∧ WfVec 1024 o.challenge ∧
        toVec (k := 1024) o.challenge = (fun _ => 1 : PolyVec (Rq Φ) 1024) ⦄ := by
  rw [commit.Opening.honest]
  simp only [commit.Decomp.blocks, linalg.PolyVec.new]
  step with honest_loop_spec (alloc.vec.Vec.len d.message) (alloc.vec.Vec.new ring.Rq) 0#usize
    (by simpa using hd.1.1) (by simp) (by simp) (by intro x hx; simp at hx)
    (by intro j hj; simp at hj) as ⟨z, hWz, hzv⟩
  exact ⟨hWz, by funext i; exact hzv i.val i.isLt⟩

/-- The specification side of perfect correctness: at the trivial challenge `cᵢ = 1`,
the honest decompositions pass every check of `verify_weak`.

The two shortness bounds sit strictly inside `params.rs`'s weak-opening values:
with base `16` the honest decomposition has
`‖sᵢ‖₂² ≤ (1024·8)·(deg φ)·(16-1)² = 1887436800 ≤ 41976510894886092800 = βSq`
(the extracted-opening bound `quadEvalBetaSq`, which dwarfs the honest case by
design) and `‖t̂‖∞ ≤ 16 - 1 = 15 ≤ 16 = γ` (the weak-opening `γ̄ = b`). -/
theorem verify_weak_honest (P : InnerOuter.PublicParams Φ 1 1024 8 1 1024 8)
    (M : InnerOuter.Message Φ 1024 1024) (O : InnerOuter.Opening Φ 1 1024 8 1024 8)
    (U : InnerOuter.Commitment Φ 1)
    (hD : O.toDecomp
      = InnerOuter.generateDecomps Φ (InnerOuter.Decomposition.ofDigits Φ dd dd) P M)
    (hc : O.challenge = (fun _ => 1 : PolyVec (Rq Φ) 1024))
    (hU : U = InnerOuter.commitWithDecomps Φ P O.toDecomp) :
    InnerOuter.verify_weak Φ (16 : ZMod q) 41976510894886092800 16 32 P U O = true := by
  have hdeg : 1 ≤ Φ.φ.natDegree := by rw [RqBridge.phi_natDegree]; norm_num
  have hlaw : ∀ x : PolyVec (Rq Φ) 1,
      gadgetMul Φ (16 : ZMod q) (gadgetDecompose Φ dd x) = x :=
    gadgetDecompose_lawful Φ (by norm_num) hdeg dd
  simp only [InnerOuter.verify_weak, Bool.and_eq_true, hc, hU]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro i _
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [Rq.l1Norm_one Φ hdeg]; norm_num
    · rw [Rq.l1Norm_one Φ hdeg]; norm_num
    · have hone : (1 : Rq Φ) •ᵥ O.message i = O.message i := by funext j; simp
      rw [hone]
      have hb := gadgetDecompose_vecL2NormSq_le_of_digit_le Φ dd dd_digit_natAbs_le (M i)
      refine le_trans (le_of_eq ?_) (le_trans hb (by rw [RqBridge.phi_natDegree]; norm_num))
      rw [hD]
      rfl
    · simp only [Simple.verify, Simple.commit, decide_eq_true_eq, hD]
      exact hlaw _
  · rw [decide_eq_true_eq]
    refine vecLInftyNorm_flattenBlocks_le Φ _ (fun i => ?_)
    have hb := gadgetDecompose_vecLInftyNorm_le_of_digit_le Φ dd dd_digit_natAbs_le
      (Simple.commit Φ P.innerMatrix (gadgetDecompose Φ dd (M i)))
    -- The honest bound is `b - 1 = 15`; the weak-opening `γ = b = 16` admits it
    -- with slack 1, hence the extra `le_trans` step.
    refine le_trans (le_of_eq ?_) (le_trans (by simpa using hb) (by norm_num))
    rw [hD]
    rfl
  · simp [Simple.verify, InnerOuter.commitWithDecomps]

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
    (hpp : WfParams pp) (hm : m.val.length = 1024 ∧ ∀ x ∈ m.val, WfVec 1024 x) :
    (do
      let (u, d) ← commit.commit pp m
      let o ← commit.Opening.honest d
      commit.verify_weak pp u o) ⦃ r => r = true ⦄ := by
  step with commit_spec pp m hpp hm as ⟨u, d, hWu, hWd, hdspec, huspec⟩
  step with honest_spec d hWd as ⟨o, hod, hWoc, hocv⟩
  apply spec_mono (verify_weak_spec pp u o hpp hWu hWoc (by rw [hod]; exact hWd))
  intro r hr
  rw [hr]
  refine verify_weak_honest (toParams pp)
    (fun i : Fin 1024 => toVec (k := 1024) (m.val.getD i.val (alloc.vec.Vec.new ring.Rq)))
    (toOpening o) _ ?_ hocv ?_
  · show toDecompSpec o.decomp = _
    rw [hod]; exact hdspec
  · show toVec (k := 1) u = InnerOuter.commitWithDecomps Φ (toParams pp) (toDecompSpec o.decomp)
    rw [hod]; exact huspec

/-! ### `commit::verify` — the full verifier

The scheme's full verifier: the claimed message must be the one the opening
determines (`derivedMessage opening.toDecomp = m`), *and* the weak checks must
pass. `honest_verifies` above reaches only `verify_weak`, so this is the
top-level API of `commit.rs` — the one function in the crate a caller would
actually invoke.

**Why `verify_spec` does not name the bundled scheme.** The ArkLib name here is
a structure *field*: `InnerOuter.commitmentScheme`'s `verify`. The bundle
carries two `SampleableType` instance arguments that its `setup` field needs
and its `verify` field does not, and no instance exists at these types (the
elaborator: `failed to synthesize SampleableType (Simple.PublicParams Φ ?rows
(?cols * 8))`). Taking the two as instance binders of `verify_spec` would not
make the theorem vacuous — the `verify` field never mentions them, so the
bundled statement is the same claim and is dischargeable from `verify_spec`'s
own proof term. What it would make the theorem is *unusable*: with binders no
caller can ever eliminate it, because no instance exists to supply. So the
postcondition names the two ArkLib definitions the `verify` field is built
from — `InnerOuter.derivedMessage` and `InnerOuter.verify_weak` — in the
field's own `List.finRange` / `decide` / `&&` shape, so a reader can diff it
line-for-line against `InnerOuter/Scheme.lean`. It implies the bundled form
outright and becomes it the moment ArkLib gains the instances. The cost,
recorded in `NOTES.md` as well: alone among the headline specs, this one does
not move automatically if ArkLib restructures `commitmentScheme.verify`.

**Hypotheses, and none of them is new** — but three of them are load-bearing
for the *truth* of the equality, not only for totality. `hpp`, `hoc` and `ho`
are exactly `verify_weak_spec`'s side conditions, inherited because the body
calls `verify_weak` on every path. The other three each have a falsifying
witness without them, all of the same shape: the representation functions are
`Fin`-indexed, so `toVec (k := 1024)` and `toVec (k := 1)` are blind to entries a
too-long carrier hides and pad a too-short one with zeros, while the extracted
`PolyVec::equals` rejects on the raw length test — so the two sides can decide
differently. `hm.1` (a longer or shorter `m` flips the outer length test),
`hm.2` (a block of the wrong inner width flips `equals` inside the loop), and
`hu` (a longer `u` flips `verify_weak`'s final outer-commitment comparison).
Without any one of them the equality of decisions is false, not merely
unprovable. -/

/-- The loop of `commit::verify`: the accumulated `Bool` decides exactly whether
the derived and claimed message blocks agree at the blocks already visited. -/
theorem verify_loop_spec (m derived : alloc.vec.Vec linalg.PolyVec)
    (blocks : Std.Usize) (ok1 : Bool) (i : Std.Usize)
    (hm : m.val.length = 1024 ∧ ∀ x ∈ m.val, WfVec 1024 x)
    (hd : derived.val.length = 1024 ∧ ∀ x ∈ derived.val, WfVec 1024 x)
    (hb : blocks.val = 1024) (hi : i.val ≤ 1024)
    (hok : ok1 = true ↔ ∀ j < i.val,
      toVec (k := 1024) (derived.val.getD j (alloc.vec.Vec.new ring.Rq))
        = toVec (k := 1024) (m.val.getD j (alloc.vec.Vec.new ring.Rq))) :
    commit.verify_loop m derived blocks ok1 i
      ⦃ r => r = true ↔ ∀ j < 1024,
        toVec (k := 1024) (derived.val.getD j (alloc.vec.Vec.new ring.Rq))
          = toVec (k := 1024) (m.val.getD j (alloc.vec.Vec.new ring.Rq)) ⦄ := by
  rw [commit.verify_loop]
  apply loop.spec_decr_nat (fun s => blocks.val - s.2.val)
    (fun s => s.2.val ≤ 1024 ∧ (s.1 = true ↔ ∀ j < s.2.val,
      toVec (k := 1024) (derived.val.getD j (alloc.vec.Vec.new ring.Rq))
        = toVec (k := 1024) (m.val.getD j (alloc.vec.Vec.new ring.Rq))))
  · rintro ⟨b1, i1⟩ ⟨hi1, hb1⟩
    dsimp only at hi1 hb1
    simp only [commit.verify_loop.body]
    by_cases hlt : i1 < blocks
    · rw [if_pos hlt]
      have hilt : i1.val < 1024 := by rw [← hb]; scalar_tac
      have hdlt : i1.val < derived.val.length := by rw [hd.1]; exact hilt
      have hmlt : i1.val < m.val.length := by rw [hm.1]; exact hilt
      step as ⟨pv, hpv⟩
      step as ⟨pv1, hpv1⟩
      have hWpv : WfVec 1024 pv := by rw [hpv]; exact hd.2 _ (List.getElem_mem hdlt)
      have hWpv1 : WfVec 1024 pv1 := by rw [hpv1]; exact hm.2 _ (List.getElem_mem hmlt)
      step with poly_vec_equals_spec (k := 1024) pv pv1 hWpv hWpv1 as ⟨bb, hbb⟩
      have hite : (if bb then ok b1 else ok (false : Bool)) ⦃ z => z = (b1 && bb) ⦄ := by
        cases bb
        · rw [if_neg (by simp), WP.spec_ok]; simp
        · rw [if_pos (by simp), WP.spec_ok]; simp
      step with hite as ⟨b2, hb2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by omega, ?_, ?_⟩
      · rw [hb2, hi2, Bool.and_eq_true, hb1, hbb, hpv, hpv1]
        constructor
        · rintro ⟨h1, h2⟩ j hj
          rcases Nat.lt_or_ge j i1.val with h | h
          · exact h1 j h
          · have hje : j = i1.val := by omega
            subst hje
            rw [List.getD_eq_getElem _ _ hdlt, List.getD_eq_getElem _ _ hmlt]
            exact h2
        · intro h
          refine ⟨fun j hj => h j (by omega), ?_⟩
          have h2 := h i1.val (by omega)
          rwa [List.getD_eq_getElem _ _ hdlt, List.getD_eq_getElem _ _ hmlt] at h2
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = 1024 := by rw [← hb] at hi1 ⊢; scalar_tac
      rw [heq] at hb1; exact hb1
  · exact ⟨hi, hok⟩

/-- `commit::verify` — ArkLib's `InnerOuter.commitmentScheme.verify`, as an
equality of *decisions*.

The right-hand side is the `verify` field's own body at this crate's parameters
(`base = 16`, `βSq = 41976510894886092800`, `γ = 16`, `κ = 32`), naming
`InnerOuter.derivedMessage` and `InnerOuter.verify_weak` rather than the bundled
`commitmentScheme`; the section note above records why the bundle cannot be
mentioned here and what that costs. -/
theorem verify_spec (pp : commit.PublicParams) (m : alloc.vec.Vec linalg.PolyVec)
    (u : linalg.PolyVec) (o : commit.Opening)
    (hpp : WfParams pp) (hm : m.val.length = 1024 ∧ ∀ x ∈ m.val, WfVec 1024 x)
    (hu : WfVec 1 u) (hoc : WfVec 1024 o.challenge) (ho : WfDecomp o.decomp) :
    commit.verify pp m u o
      ⦃ r => r = ((List.finRange 1024).all (fun i =>
                    decide (InnerOuter.derivedMessage Φ (16 : ZMod q) (toOpening o).toDecomp i
                      = toVec (k := 1024) (m.val.getD i.val (alloc.vec.Vec.new ring.Rq))))
                  && InnerOuter.verify_weak Φ (16 : ZMod q) 41976510894886092800 16 32
                      (toParams pp) (toVec (k := 1) u) (toOpening o)) ⦄ := by
  have hlm : m.val.length = 1024 := hm.1
  rw [commit.verify]
  simp only [commit.Opening.impl.decomp]
  step with derived_message_spec o.decomp ho as ⟨derived, hdlen, hdwf, hder⟩
  have hWder : derived.val.length = 1024 ∧ ∀ x ∈ derived.val, WfVec 1024 x := ⟨hdlen, hdwf⟩
  have hld : derived.val.length = 1024 := hdlen
  have h1 : (alloc.vec.Vec.len derived).val = 1024 := by simpa using hld
  have h2 : (alloc.vec.Vec.len m).val = 1024 := by simpa using hlm
  have hne : (alloc.vec.Vec.len derived != alloc.vec.Vec.len m) = false := by
    simp only [bne_eq_false_iff_eq]
    scalar_tac
  rw [hne, if_neg (by simp)]
  step with verify_loop_spec m derived (alloc.vec.Vec.len m) true 0#usize hm hWder
    h2 (by simp) (by simp) as ⟨ok1, hok1⟩
  step with verify_weak_spec pp u o hpp hu hoc ho as ⟨b, hb⟩
  have hite : (if b then ok ok1 else ok (false : Bool)) ⦃ z => z = (ok1 && b) ⦄ := by
    cases b
    · rw [if_neg (by simp), WP.spec_ok]; simp
    · rw [if_pos (by simp), WP.spec_ok]; simp
  apply spec_mono hite
  intro r hr
  have hder' : ∀ i : Fin 1024,
      InnerOuter.derivedMessage Φ (16 : ZMod q) (toOpening o).toDecomp i
        = toVec (k := 1024) (derived.val.getD i.val (alloc.vec.Vec.new ring.Rq)) :=
    fun i => (congrFun hder i).symm
  have hA : ok1 = ((List.finRange 1024).all (fun i =>
      decide (InnerOuter.derivedMessage Φ (16 : ZMod q) (toOpening o).toDecomp i
        = toVec (k := 1024) (m.val.getD i.val (alloc.vec.Vec.new ring.Rq))))) := by
    rw [Bool.eq_iff_iff, hok1, List.all_eq_true]
    simp only [List.mem_finRange, decide_eq_true_eq, forall_const]
    constructor
    · intro h i
      exact (hder' i).trans (h i.val i.isLt)
    · intro h j hj
      exact (hder' ⟨j, hj⟩).symm.trans (h ⟨j, hj⟩)
  rw [hr, hb, hA]

/-- **Perfect correctness at the crate's top-level API**: an honest commitment
and its honest opening pass `commit::verify` itself -- the derived-message check
included -- not only `verify_weak`. `honest_verifies` above reaches `verify_weak`
because `verify` had no spec when it was proved; with `verify_spec` in hand this
is the composition a caller actually runs. The message half closes by
`gadgetDecompose_lawful`: the honest committer's blocks are `sᵢ = G⁻¹(mᵢ)`, so
the derived message `G · sᵢ` is `mᵢ` back. -/
theorem honest_verifies_full (pp : commit.PublicParams)
    (m : alloc.vec.Vec linalg.PolyVec)
    (hpp : WfParams pp) (hm : m.val.length = 1024 ∧ ∀ x ∈ m.val, WfVec 1024 x) :
    (do
      let (u, d) ← commit.commit pp m
      let o ← commit.Opening.honest d
      commit.verify pp m u o) ⦃ r => r = true ⦄ := by
  step with commit_spec pp m hpp hm as ⟨u, d, hWu, hWd, hdspec, huspec⟩
  step with honest_spec d hWd as ⟨o, hod, hWoc, hocv⟩
  apply spec_mono (verify_spec pp m u o hpp hm hWu hWoc (by rw [hod]; exact hWd))
  intro r hr
  have hdeg : 1 ≤ Φ.φ.natDegree := by rw [RqBridge.phi_natDegree]; norm_num
  have hlaw : ∀ x : PolyVec (Rq Φ) 1024,
      gadgetMul Φ (16 : ZMod q) (gadgetDecompose Φ dd x) = x :=
    gadgetDecompose_lawful Φ (by norm_num) hdeg dd
  rw [hr, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    intro i _
    rw [decide_eq_true_eq]
    show InnerOuter.derivedMessage Φ (16 : ZMod q) (toDecompSpec o.decomp) i = _
    rw [hod, hdspec]
    exact hlaw _
  · exact verify_weak_honest (toParams pp)
      (fun i : Fin 1024 => toVec (k := 1024) (m.val.getD i.val (alloc.vec.Vec.new ring.Rq)))
      (toOpening o) _
      (by show toDecompSpec o.decomp = _; rw [hod]; exact hdspec) hocv
      (by
        show toVec (k := 1) u
          = InnerOuter.commitWithDecomps Φ (toParams pp) (toDecompSpec o.decomp)
        rw [hod]; exact huspec)

end HachiEquiv.Scheme
