/-
The full ring-switch link: statements only, not proofs.

Staged here rather than in `lean/` because the obligations below are not yet
proved. The file is rebased on ArkLib `d51d8bc`: `Z_DIGITS = 5` makes
`RLIN_COLS = 57344`, while the quotient digit count remains `clog 16 q = 8`.
The deleted convenience lemmas `hachiLiftCom_TCom`, `hachiLiftCom_com`, and
`rhoDigitsShortCheck_eq_true_of_digitBaseOk` are deliberately not referenced.

`ShortChallenge` erasure does not enter any definition below: this link receives
no challenge. The missing `ℓ₁ ≤ ω` precondition remains a composition-level
obligation when the verifier first consumes the fold challenge.
-/

import QuadEval
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Reduction
import ArkLib.Commitments.Functional.Hachi.EndPiece.Reduction

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.RingSwitch

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme

theorem rhoDigitCount_eq : InnerOuter.rhoDigitCount q 16 = 8 := by
  have h := InnerOuter.HachiParams.clog_eq_delta
  simp only [InnerOuter.HachiParams.hachiB, InnerOuter.HachiParams.hachiQ,
    InnerOuter.HachiParams.hachiDelta] at h
  simpa [InnerOuter.rhoDigitCount, q] using h

/-- The raw quotient polynomial represented by a `QuotientRow`. -/
def toQuotientRow (v : ringswitch.QuotientRow) : CPolynomial (ZMod q) :=
  CPolynomial.ofFinCoeff N (coeffK v)

/-- A vector of raw quotient rows is well-formed at length `n`. -/
def WfRho (n : ℕ) (rho : alloc.vec.Vec ringswitch.QuotientRow) : Prop :=
  rho.val.length = n ∧ ∀ x ∈ rho.val, Wf x

/-- The specification-side quotient-row family represented by a Rust vector. -/
def toRho {n : ℕ} (rho : alloc.vec.Vec ringswitch.QuotientRow) :
    Fin n → CPolynomial (ZMod q) :=
  fun i => toQuotientRow (rho.val.getD i.val (alloc.vec.Vec.new cpoly.field.Fp))

/-- Relation between the extracted pair and ArkLib's proof-carrying witness. -/
def RepLiftedWitness {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) : Prop :=
  WfVec μ w.z ∧ WfRho n w.rho ∧
    toVec (k := μ) w.z = sw.z ∧ toRho (n := n) w.rho = sw.ρ

/-- `QuotientRow::to_rq` is ArkLib's `rhoAsRq`: a presentation change, not a
cyclotomic reduction. -/
theorem rho_as_rq_spec (rho : ringswitch.QuotientRow) (hrho : Wf rho) :
    ringswitch.QuotientRow.to_rq rho
      ⦃ out => Wf out ∧ toRq out = InnerOuter.rhoAsRq Φ (toQuotientRow rho) ⦄ := by
  sorry

/-- The flat index is split as quotient row `j / 8` and digit `j % 8`. -/
theorem rho_digit_as_rq_spec {n : ℕ} (rho : alloc.vec.Vec ringswitch.QuotientRow)
    (j : Std.Usize) (hrho : WfRho n rho) (hj : j.val < n * 8) :
    ringswitch.rho_digit_as_rq rho j
      ⦃ out => Wf out ∧ toRq out =
        InnerOuter.rhoDigitAsRq Φ 16 (toRho (n := n) rho)
          ⟨j.val, by rw [rhoDigitCount_eq]; exact hj⟩ ⦄ := by
  sorry

/-- `lift_message` is `Fin.append z (rhoDigitAsRq …)`. -/
theorem lift_message_spec {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (hw : RepLiftedWitness w sw)
    (hmax : μ + n * 8 ≤ Usize.max) :
    ringswitch.lift_message w
      ⦃ out => WfVec (μ + n * 8) out ∧ toVec (k := μ + n * 8) out =
        InnerOuter.liftMessage Φ 16 sw ⦄ := by
  sorry

/-- `lift_commit` is the concrete Ajtai commitment map at `(bound,bDig) =
(15,16)`. -/
theorem lift_commit_spec {dRows μ n : ℕ} (dKey : linalg.PolyMatrix)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (hD : WfMat dRows (μ + n * 8) dKey) (hw : RepLiftedWitness w sw)
    (hmax : μ + n * 8 ≤ Usize.max) :
    ringswitch.lift_commit dKey w
      ⦃ out => WfVec dRows out ∧ toVec (k := dRows) out =
        (InnerOuter.hachiLiftCom Φ 15 16
          (toMat (rows := dRows) (cols := μ + n * 8) dKey)).com sw ⦄ := by
  sorry

/-- The Rust boolean decides the quotient-digit half of `liftShort`. -/
theorem rho_digits_short_check_spec {n : ℕ}
    (rho : alloc.vec.Vec ringswitch.QuotientRow) (hrho : WfRho n rho) :
    endpiece.rho_digits_short_check rho
      ⦃ b => (b = true ↔ InnerOuter.RhoDigitsShort Φ 15 16 (toRho (n := n) rho)) ⦄ := by
  sorry

/-- The Rust boolean decides `liftShort` at the concrete chain parameters. -/
theorem lift_short_check_spec {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (hw : RepLiftedWitness w sw) :
    endpiece.lift_short_check w
      ⦃ b => (b = true ↔ InnerOuter.liftShort Φ 15 16 sw) ⦄ := by
  sorry

end HachiEquiv.RingSwitch
