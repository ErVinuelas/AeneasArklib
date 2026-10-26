/-
The **row level of the two-lane general path** (candidate G2): one prepared row
`ring::dot_prepared_ga` against `Rq`, stated as `Scheme.lean`'s three-lane row
is. The matrix-level wrapper (`PreparedMatrixGA`) was removed once card T35's
limb carrier replaced this path; `SchemeLimb.lean` reuses the row shape.
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

end HachiEquiv.SchemeTwoLane
