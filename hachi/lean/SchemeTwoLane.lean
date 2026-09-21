/-
The **linalg layer of the two-lane general path** (candidate G2).

`PolyMatrix::prepare_ga` and `PreparedMatrixGA::apply_ga` are
`PolyMatrix::prepare` and `PreparedMatrix::apply` with a two-lane store, so
this file is `Scheme.lean`'s three-lane block with the lane count changed and
nothing else. In particular the *statements* are the three-lane ones: the
prepared product is `matVecMul` either way, which is the whole claim of the
card at this level.

It lives in its own file rather than inside `Scheme.lean` because the trunk
was mid-refactor when it was written; the natural home is beside `apply_spec`
once that settles.
-/
import Scheme
import RingTwoLane

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.SchemeTwoLane

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge
open HachiEquiv.Scheme HachiEquiv.RingTwoLane HachiEquiv.RingFused

/-- [`RqBridge.PrepRow`] for the two-lane store. -/
def PrepRowGA (cols : ℕ) (p : ring.PreparedVecGA) (a : linalg.PolyVec) : Prop :=
  p.len.val = cols
  ∧ PrepAtGV p.fwd_g a cols
  ∧ PrepAt p.fwd_a a cols ntt.AUX_P1 ntt.AUX_PSI1

/-- The `getD` default for a `PreparedVecGA` slot; never read. -/
def prepJunkGA : ring.PreparedVecGA :=
  { len := 0#usize, fwd_g := alloc.vec.Vec.new Std.U64,
    fwd_a := alloc.vec.Vec.new Std.U64 }

/-- **`ring::dot_prepared_ga` at the `Rq` level.** `RqBridge.dot_prepared_spec`
with two lanes. -/
theorem dot_prepared_ga_rq_spec (prep : ring.PreparedVecGA)
    (a b : alloc.vec.Vec ring.Rq) (nU : Std.Usize)
    (haw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (han : nU.val ≤ a.val.length) (hbn : nU.val ≤ b.val.length)
    (hprep : PrepRowGA nU.val prep a) :
    ring.dot_prepared_ga prep b nU
      ⦃ z => HachiEquiv.Ring.Wf z ∧ toRq z = ∑ u ∈ Finset.range nU.val,
          toRq (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
            * toRq (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  obtain ⟨-, hpg, hpa⟩ := hprep
  apply spec_mono (dot_prepared_ga_spec prep a b nU haw hbw han hbn hpg hpa)
  rintro z ⟨hzwf, hzval⟩
  exact ⟨hzwf, dot_sum_toRq a b nU haw hbw z hzval⟩

/-- [`Scheme.dot_prep_spec`] for the two-lane store. -/
theorem dot_prep_ga_spec {k : ℕ} (prep : ring.PreparedVecGA) (u v : linalg.PolyVec)
    (nU : Std.Usize) (hn : nU.val = k) (hu : WfVec k u) (hv : WfVec k v)
    (hprep : PrepRowGA k prep u) :
    ring.dot_prepared_ga prep v nU
      ⦃ z => Wf z ∧ toRq z
        = ArkLib.Lattices.dot (toVec (k := k) u) (toVec (k := k) v) ⦄ := by
  apply spec_mono (dot_prepared_ga_rq_spec prep u v nU
    (by intro j hj; rw [hn] at hj; exact wf_getD hu hj)
    (by intro j hj; rw [hn] at hj; exact wf_getD hv hj)
    (by rw [hn, hu.1]) (by rw [hn, hv.1]) (by rw [hn]; exact hprep))
  rintro z ⟨hzwf, hzval⟩
  refine ⟨hzwf, ?_⟩
  rw [hzval, hn, ArkLib.Lattices.dot_eq_sum]
  exact (Fin.sum_univ_eq_sum_range
    (fun j => toRq (u.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
      * toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))) k).symm

/-- [`Scheme.WfPrep`] for the two-lane store. -/
def WfPrepGA (rows cols : ℕ) (pm : linalg.PreparedMatrixGA)
    (m : linalg.PolyMatrix) : Prop :=
  pm.cols.val = cols ∧ pm.rows.val.length = rows
  ∧ ∀ i, i < rows → PrepRowGA cols (pm.rows.val.getD i prepJunkGA)
      (m.val.getD i (alloc.vec.Vec.new ring.Rq))

theorem prepare_ga_loop_spec {rows cols : ℕ} (m : linalg.PolyMatrix)
    (n c : Std.Usize) (rws : alloc.vec.Vec ring.PreparedVecGA) (i : Std.Usize)
    (ha : WfMat rows cols m) (hn : n.val = rows) (hc : c.val = cols)
    (hmax : cols * N ≤ Std.Usize.max)
    (hi : i.val ≤ n.val) (hlen : rws.val.length = i.val)
    (hval : ∀ u, u < i.val → PrepRowGA cols (rws.val.getD u prepJunkGA)
      (m.val.getD u (alloc.vec.Vec.new ring.Rq))) :
    linalg.PolyMatrix.prepare_ga_loop m n c rws i
      ⦃ z => z.val.length = rows ∧ ∀ u, u < rows →
          PrepRowGA cols (z.val.getD u prepJunkGA)
            (m.val.getD u (alloc.vec.Vec.new ring.Rq)) ⦄ := by
  rw [linalg.PolyMatrix.prepare_ga_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val
      ∧ ∀ u, u < s.2.val → PrepRowGA cols (s.1.val.getD u prepJunkGA)
          (m.val.getD u (alloc.vec.Vec.new ring.Rq)))
  · rintro ⟨r1, i1⟩ ⟨hi1, hlen1, hval1⟩
    dsimp only at hi1 hlen1 hval1
    simp only [linalg.PolyMatrix.prepare_ga_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have him : i1.val < m.val.length := by rw [ha.1, ← hn]; scalar_tac
      step as ⟨pv, hpv⟩
      have hWpv : WfVec cols pv := by rw [hpv]; exact ha.2 _ (List.getElem_mem him)
      have hmi : m.val.getD i1.val (alloc.vec.Vec.new ring.Rq) = pv := by
        rw [hpv]; exact List.getD_eq_getElem _ _ him
      step with prepare_vec_ga_spec pv c
        (by intro u hu; rw [hc] at hu; exact wf_getD hWpv hu)
        (by rw [hc, hWpv.1]) (by rw [hc]; exact hmax) as ⟨p, hpl, hpg, hpa⟩
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
          · rw [← hc]; exact hpg
          · rw [← hc]; exact hpa
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq, hn], by intro u hu; exact hval1 u (by rw [heq, hn]; exact hu)⟩
  · exact ⟨hi, hlen, hval⟩

/-- `PolyMatrix::prepare` — the prepared form of the matrix it is given. -/
theorem prepare_ga_spec {rows cols : ℕ} (m : linalg.PolyMatrix)
    (ha : WfMat rows cols m) (hrows : 0 < rows) (hmax : cols * N ≤ Std.Usize.max) :
    linalg.PolyMatrix.prepare_ga m ⦃ z => WfPrepGA rows cols z m ⦄ := by
  rw [linalg.PolyMatrix.prepare_ga]
  step with cols_spec m ha hrows as ⟨c, hc⟩
  step with prepare_ga_loop_spec m (alloc.vec.Vec.len m) c
    (alloc.vec.Vec.new ring.PreparedVecGA) 0#usize ha (by simp [ha.1]) hc hmax
    (by simp) (by simp) (by intro u hu; simp at hu) as ⟨rws, hrl, hrv⟩
  exact ⟨hc, hrl, hrv⟩

/-- The loop of `PreparedMatrix::apply`: entry `j` already written is the dot
product of matrix row `j` with the input vector — the very invariant
`mat_vec_mul_loop_spec` carries. -/
theorem apply_ga_loop_spec {rows cols : ℕ} (pm : linalg.PreparedMatrixGA)
    (m : linalg.PolyMatrix) (v : linalg.PolyVec) (n w : Std.Usize)
    (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (ha : WfMat rows cols m) (hv : WfVec cols v) (hp : WfPrepGA rows cols pm m)
    (hn : n.val = rows) (hw : w.val = cols)
    (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hwf : ∀ z ∈ out.val, Wf z)
    (hval : ∀ j, j < i.val →
      toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ArkLib.Lattices.dot (toVec (k := cols) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))
            (toVec (k := cols) v)) :
    linalg.PreparedMatrixGA.apply_ga_loop pm.rows v n w out i
      ⦃ z => z.val.length = rows ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < rows → toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          = ArkLib.Lattices.dot (toVec (k := cols) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))
              (toVec (k := cols) v) ⦄ := by
  rw [linalg.PreparedMatrixGA.apply_ga_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ j, j < s.2.val → toRq (s.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ArkLib.Lattices.dot (toVec (k := cols) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))
            (toVec (k := cols) v))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [linalg.PreparedMatrixGA.apply_ga_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hip : i1.val < pm.rows.val.length := by rw [hp.2.1, ← hn]; scalar_tac
      have him : i1.val < m.val.length := by rw [ha.1, ← hn]; scalar_tac
      step as ⟨pv, hpv⟩
      have hprow : PrepRowGA cols pv (m.val.getD i1.val (alloc.vec.Vec.new ring.Rq)) := by
        have := hp.2.2 i1.val (by rw [← hn]; scalar_tac)
        rwa [List.getD_eq_getElem _ _ hip, ← hpv] at this
      have hWrow : WfVec cols (m.val.getD i1.val (alloc.vec.Vec.new ring.Rq)) := by
        rw [List.getD_eq_getElem _ _ him]; exact ha.2 _ (List.getElem_mem him)
      step with dot_prep_ga_spec (k := cols) pv
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

end HachiEquiv.SchemeTwoLane
