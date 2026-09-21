/-
The **linalg layer of the 16-bit limb carrier path** (card T35).

`PolyMatrix::prepare_limbs2` and `PreparedMatrixL2::apply_limbs2` are
`PolyMatrix::prepare` and `PreparedMatrix::apply` with a two-limb store, so
this file is `SchemeTwoLane.lean`'s block with the store changed and nothing
else. The *statements* are again the original ones -- the prepared product is
`matVecMul` whichever store computes it, which is the whole claim of the card
at this level.

The one structural difference from `SchemeTwoLane.lean` is that a prepared row
here does not name the limbs it was split into: `prepare_vec_limbs2` produces
them internally and `dot_prepared_limbs2` consumes them, so [`PrepRowL2`]
quantifies over them existentially and the row spec re-opens the pair.
-/
import Scheme
import RingLimb

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.SchemeLimb

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge
open HachiEquiv.Scheme HachiEquiv.RingLimb HachiEquiv.RingFused

/-- [`RqBridge.PrepRow`] for the two-limb store. The limbs are existential:
they exist inside `prepare_vec_limbs2` and are read again inside
`dot_prepared_limbs2`, and nothing between the two ever names them. -/
def PrepRowL2 (cols : ℕ) (p : ring.PreparedVecL2) (a : linalg.PolyVec) : Prop :=
  p.len.val = cols
  ∧ ∃ a0 a1, LimbsOf a a0 a1 cols
      ∧ PrepAtLimb p.f0 a0 cols ∧ PrepAtLimb p.f1 a1 cols

/-- The `getD` default for a `PreparedVecL2` slot; never read. -/
def prepJunkL2 : ring.PreparedVecL2 :=
  { len := 0#usize, f0 := alloc.vec.Vec.new Std.U64,
    f1 := alloc.vec.Vec.new Std.U64 }

/-- **`ring::dot_prepared_limbs2` at the `Rq` level.**
`RqBridge.dot_prepared_spec` with the limb store. -/
theorem dot_prepared_limbs2_rq_spec (prep : ring.PreparedVecL2)
    (a b : alloc.vec.Vec ring.Rq) (nU : Std.Usize)
    (haw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbn : nU.val ≤ b.val.length)
    (hprep : PrepRowL2 nU.val prep a) :
    ring.dot_prepared_limbs2 prep b nU
      ⦃ z => HachiEquiv.Ring.Wf z ∧ toRq z = ∑ u ∈ Finset.range nU.val,
          toRq (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
            * toRq (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  obtain ⟨-, a0, a1, hl, hp0, hp1⟩ := hprep
  apply spec_mono (dot_prepared_limbs2_spec prep a a0 a1 b nU hbw hbn hl hp0 hp1)
  rintro z ⟨hzwf, hzval⟩
  exact ⟨hzwf, dot_sum_toRq a b nU haw hbw z hzval⟩

/-- [`Scheme.dot_prep_spec`] for the two-limb store. -/
theorem dot_prep_limbs2_spec {k : ℕ} (prep : ring.PreparedVecL2)
    (u v : linalg.PolyVec) (nU : Std.Usize) (hn : nU.val = k)
    (hu : WfVec k u) (hv : WfVec k v) (hprep : PrepRowL2 k prep u) :
    ring.dot_prepared_limbs2 prep v nU
      ⦃ z => Wf z ∧ toRq z
        = ArkLib.Lattices.dot (toVec (k := k) u) (toVec (k := k) v) ⦄ := by
  apply spec_mono (dot_prepared_limbs2_rq_spec prep u v nU
    (by intro j hj; rw [hn] at hj; exact wf_getD hu hj)
    (by intro j hj; rw [hn] at hj; exact wf_getD hv hj)
    (by rw [hn, hv.1]) (by rw [hn]; exact hprep))
  rintro z ⟨hzwf, hzval⟩
  refine ⟨hzwf, ?_⟩
  rw [hzval, hn, ArkLib.Lattices.dot_eq_sum]
  exact (Fin.sum_univ_eq_sum_range
    (fun j => toRq (u.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
      * toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))) k).symm

/-- [`Scheme.WfPrep`] for the two-limb store. -/
def WfPrepL2 (rows cols : ℕ) (pm : linalg.PreparedMatrixL2)
    (m : linalg.PolyMatrix) : Prop :=
  pm.cols.val = cols ∧ pm.rows.val.length = rows
  ∧ ∀ i, i < rows → PrepRowL2 cols (pm.rows.val.getD i prepJunkL2)
      (m.val.getD i (alloc.vec.Vec.new ring.Rq))

theorem prepare_limbs2_loop_spec {rows cols : ℕ} (m : linalg.PolyMatrix)
    (n c : Std.Usize) (rws : alloc.vec.Vec ring.PreparedVecL2) (i : Std.Usize)
    (ha : WfMat rows cols m) (hn : n.val = rows) (hc : c.val = cols)
    (hmax : cols * N ≤ Std.Usize.max)
    (hi : i.val ≤ n.val) (hlen : rws.val.length = i.val)
    (hval : ∀ u, u < i.val → PrepRowL2 cols (rws.val.getD u prepJunkL2)
      (m.val.getD u (alloc.vec.Vec.new ring.Rq))) :
    linalg.PolyMatrix.prepare_limbs2_loop m n c rws i
      ⦃ z => z.val.length = rows ∧ ∀ u, u < rows →
          PrepRowL2 cols (z.val.getD u prepJunkL2)
            (m.val.getD u (alloc.vec.Vec.new ring.Rq)) ⦄ := by
  rw [linalg.PolyMatrix.prepare_limbs2_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val
      ∧ ∀ u, u < s.2.val → PrepRowL2 cols (s.1.val.getD u prepJunkL2)
          (m.val.getD u (alloc.vec.Vec.new ring.Rq)))
  · rintro ⟨r1, i1⟩ ⟨hi1, hlen1, hval1⟩
    dsimp only at hi1 hlen1 hval1
    simp only [linalg.PolyMatrix.prepare_limbs2_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have him : i1.val < m.val.length := by rw [ha.1, ← hn]; scalar_tac
      step as ⟨pv, hpv⟩
      have hWpv : WfVec cols pv := by rw [hpv]; exact ha.2 _ (List.getElem_mem him)
      have hmi : m.val.getD i1.val (alloc.vec.Vec.new ring.Rq) = pv := by
        rw [hpv]; exact List.getD_eq_getElem _ _ him
      step with prepare_vec_limbs2_spec pv c
        (by intro u hu; rw [hc] at hu; exact wf_getD hWpv hu)
        (by rw [hc, hWpv.1]) (by rw [hc]; exact hmax)
        as ⟨p, hpl, a0, a1, hpl0, hpl1, hpl2⟩
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
          refine ⟨by rw [hpl]; exact hc, a0, a1, ?_, ?_, ?_⟩
          · rw [← hc]; exact hpl0
          · rw [← hc]; exact hpl1
          · rw [← hc]; exact hpl2
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq, hn], by intro u hu; exact hval1 u (by rw [heq, hn]; exact hu)⟩
  · exact ⟨hi, hlen, hval⟩

/-- `PolyMatrix::prepare_limbs2` — the prepared form of the matrix it is
given. -/
theorem prepare_limbs2_spec {rows cols : ℕ} (m : linalg.PolyMatrix)
    (ha : WfMat rows cols m) (hrows : 0 < rows) (hmax : cols * N ≤ Std.Usize.max) :
    linalg.PolyMatrix.prepare_limbs2 m ⦃ z => WfPrepL2 rows cols z m ⦄ := by
  rw [linalg.PolyMatrix.prepare_limbs2]
  simp only [alloc.vec.Vec.with_capacity]
  step with cols_spec m ha hrows as ⟨c, hc⟩
  step with prepare_limbs2_loop_spec m (alloc.vec.Vec.len m) c
    (alloc.vec.Vec.new ring.PreparedVecL2) 0#usize ha (by simp [ha.1]) hc hmax
    (by simp) (by simp) (by intro u hu; simp at hu) as ⟨rws, hrl, hrv⟩
  exact ⟨hc, hrl, hrv⟩

/-- The loop of `PreparedMatrixL2::apply_limbs2`: entry `j` already written is
the dot product of matrix row `j` with the input vector — the very invariant
`mat_vec_mul_loop_spec` carries. -/
theorem apply_limbs2_loop_spec {rows cols : ℕ} (pm : linalg.PreparedMatrixL2)
    (m : linalg.PolyMatrix) (v : linalg.PolyVec) (n w : Std.Usize)
    (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (ha : WfMat rows cols m) (hv : WfVec cols v) (hp : WfPrepL2 rows cols pm m)
    (hn : n.val = rows) (hw : w.val = cols)
    (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hwf : ∀ z ∈ out.val, Wf z)
    (hval : ∀ j, j < i.val →
      toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ArkLib.Lattices.dot (toVec (k := cols) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))
            (toVec (k := cols) v)) :
    linalg.PreparedMatrixL2.apply_limbs2_loop pm.rows v n w out i
      ⦃ z => z.val.length = rows ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < rows → toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          = ArkLib.Lattices.dot (toVec (k := cols) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))
              (toVec (k := cols) v) ⦄ := by
  rw [linalg.PreparedMatrixL2.apply_limbs2_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ j, j < s.2.val → toRq (s.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ArkLib.Lattices.dot (toVec (k := cols) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))
            (toVec (k := cols) v))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [linalg.PreparedMatrixL2.apply_limbs2_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hip : i1.val < pm.rows.val.length := by rw [hp.2.1, ← hn]; scalar_tac
      have him : i1.val < m.val.length := by rw [ha.1, ← hn]; scalar_tac
      step as ⟨pv, hpv⟩
      have hprow : PrepRowL2 cols pv (m.val.getD i1.val (alloc.vec.Vec.new ring.Rq)) := by
        have := hp.2.2 i1.val (by rw [← hn]; scalar_tac)
        rwa [List.getD_eq_getElem _ _ hip, ← hpv] at this
      have hWrow : WfVec cols (m.val.getD i1.val (alloc.vec.Vec.new ring.Rq)) := by
        rw [List.getD_eq_getElem _ _ him]; exact ha.2 _ (List.getElem_mem him)
      step with dot_prep_limbs2_spec (k := cols) pv
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

theorem apply_limbs2_spec {rows cols : ℕ} (pm : linalg.PreparedMatrixL2)
    (m : linalg.PolyMatrix) (v : linalg.PolyVec)
    (ha : WfMat rows cols m) (hv : WfVec cols v) (hp : WfPrepL2 rows cols pm m) :
    linalg.PreparedMatrixL2.apply_limbs2 pm v
      ⦃ z => WfVec rows z ∧ toVec (k := rows) z
        = ArkLib.Lattices.matVecMul (toMat (rows := rows) (cols := cols) m)
            (toVec (k := cols) v) ⦄ := by
  rw [linalg.PreparedMatrixL2.apply_limbs2]
  have hvl : (alloc.vec.Vec.len v).val = cols := by simp [hv.1]
  have hcl : pm.cols.val = cols := hp.1
  simp only [if_pos (by scalar_tac : pm.cols ≤ alloc.vec.Vec.len v), bind_ok_id,
    alloc.vec.Vec.with_capacity]
  apply spec_mono (apply_limbs2_loop_spec pm m v (alloc.vec.Vec.len pm.rows) pm.cols
    (alloc.vec.Vec.new ring.Rq) 0#usize ha hv hp (by simp [hp.2.1]) hcl
    (by simp) (by simp) (by intro y hy; simp at hy) (by intro j hj; simp at hj))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i
  rw [ArkLib.Lattices.matVecMul_apply, toMat_apply]
  exact hzval i.val i.isLt

end HachiEquiv.SchemeLimb
