/-
Target 6's end piece: **statements only**.

Four obligations, none proved here. Split out of `ZeroCheck.lean` rather than
bundled with it: the convention in `lean/` is one file per `hachi/src` module
(`Field`, `Ring`, `RqBridge`, `Scheme`, `EvalSplit`, `Balanced`, `QuadEval`,
`RingSwitch`), and bundling would also force the two targets to be promoted
together, which they should not be -- target 4's obligations are independent of
target 6's.

The cost of the split is a second `LEAN_PATH` hop: this file imports
`ZeroCheck.lean`, which imports `Ext.lean`, and `lake build` produces no
`.olean` for anything under `lean-wip/`. The chain is

```sh
cd hachi
lake env lean -o /tmp/wiplean/Ext.olean       lean-wip/Ext.lean
LEAN_PATH="$(lake env printenv LEAN_PATH):/tmp/wiplean" \
  lake env lean -o /tmp/wiplean/ZeroCheck.olean lean-wip/ZeroCheck.lean
LEAN_PATH="$(lake env printenv LEAN_PATH):/tmp/wiplean" \
  lake env lean lean-wip/EndPiece.lean
```

and the promotion order it forces is `Ext` -> `ZeroCheck` -> `EndPiece`.

`end_piece_check` is where the two walls of the whole scheme meet in one
function -- conjunct A is `lift_commit`'s `LIFT_COLS` ring products, conjunct C
is the `2^m0` cube -- and they are removed by different champions, which is why
`hachi/benches/endpiece.rs` states them as separate rows.
-/

import ZeroCheck

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly CompPoly.Extension CompPoly.Extension.Ext ArkLib.Lattices
open ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.EndPiece

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme
open HachiEquiv.RingSwitch HachiEquiv.Ext HachiEquiv.ZeroCheck

/-- `PartialEq for Ext4` decides equality of the represented elements.

The crate's derived comparison is four `Fp` word comparisons
(`CoreCmpPartialEqExt4.eq`), so reducedness is what makes it sound, exactly as
in `Ext.lean`'s `ext_is_zero_spec`. Local to this file: `end_piece_check` is the
only caller of it in the audited surface. -/
theorem ext_eq_spec (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    cpoly.field.Ext4.Insts.CoreCmpPartialEqExt4.eq a b
      ⦃ r => (r = true ↔ toExt a = toExt b) ⦄ := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hb
  have hfp : ∀ (x y : cpoly.field.Fp), Red x → Red y →
      ((x = y) ↔ toK x = toK y) := by
    intro x y hx hy
    rw [toK_inj_of_Red hx hy]
    constructor
    · intro h; rw [h]
    · intro h; scalar_tac
  rw [cpoly.field.Ext4.Insts.CoreCmpPartialEqExt4.eq, toExt_eq_iff]
  simp only [cpoly.field.Fp.Insts.CoreCmpPartialEqFp.eq, bind_tc_ok]
  by_cases h0 : a.c0 = b.c0
  · rw [if_pos (by simpa using h0)]
    by_cases h1 : a.c1 = b.c1
    · rw [if_pos (by simpa using h1)]
      by_cases h2 : a.c2 = b.c2
      · rw [if_pos (by simpa using h2)]
        simp only [WP.spec_ok, decide_eq_true_eq]
        rw [hfp a.c0 b.c0 ha0 hb0] at h0
        rw [hfp a.c1 b.c1 ha1 hb1] at h1
        rw [hfp a.c2 b.c2 ha2 hb2] at h2
        rw [hfp a.c3 b.c3 ha3 hb3]
        exact ⟨fun h => ⟨h0, h1, h2, h⟩, fun h => h.2.2.2⟩
      · rw [if_neg (by simpa using h2), WP.spec_ok]
        rw [hfp a.c2 b.c2 ha2 hb2] at h2
        simp only [Bool.false_eq_true, false_iff, not_and]
        exact fun _ _ h => absurd h h2
    · rw [if_neg (by simpa using h1), WP.spec_ok]
      rw [hfp a.c1 b.c1 ha1 hb1] at h1
      simp only [Bool.false_eq_true, false_iff, not_and]
      exact fun _ h => absurd h h1
  · rw [if_neg (by simpa using h0), WP.spec_ok]
    rw [hfp a.c0 b.c0 ha0 hb0] at h0
    simp only [Bool.false_eq_true, false_iff, not_and]
    exact fun h => absurd h h0

/-- The end-piece statement's constructor preserves the relation. -/
theorem WEvalStatement_new_spec {dRows m₀ : ℕ} (t : linalg.PolyVec)
    (point : alloc.vec.Vec cpoly.field.Ext4) (value : cpoly.field.Ext4)
    (ws : InnerOuter.WEvalStatement (PolyVec (Rq Φ) dRows) F m₀)
    (hWt : WfVec dRows t) (hWp : WfPoint m₀ point) (hWv : Reduced value)
    (ht : toVec (k := dRows) t = ws.t)
    (hp : toPoint (m := m₀) point = ws.point) (hv : toExt value = ws.value) :
    endpiece.WEvalStatement.new t point value
      ⦃ out => RepWEval (dRows := dRows) (m₀ := m₀) out ws ⦄ := by
  rw [endpiece.WEvalStatement.new, WP.spec_ok]
  exact ⟨hWt, hWp, hWv, ht, hp, hv⟩

/-- `end_piece_check` **decides** `endPieceCheck` (`EndPiece/Reduction.lean:143`):
the three conjuncts, in the specification's order and with its short-circuit.

The `BEq`/`LawfulBEq` on the commitment carrier are instance *hypotheses*, which
is ArkLib's own convention for this definition (`Composition.lean:287`,
`Correctness.lean:100` both take them rather than providing them): `K.TCom` here
is `PolyVec (Rq Φ) dRows`, a function type, so there is no instance to find.
`LawfulBEq` is the load-bearing half -- it ties `==` to `=`, without which the
statement would be about an arbitrary relation. The Rust side compares with
`PolyVec::equals`, which is `Rq::equals` pointwise through `Fp::to_u64`, i.e.
the crate's single notion of equality per type (`Check.lean` § 2). -/
theorem end_piece_check_spec {dRows μ n m₀ : ℕ} (dKey : linalg.PolyMatrix)
    [BEq (InnerOuter.hachiLiftCom Φ 15 16
      (toMat (rows := dRows) (cols := μ + n * 8) dKey)).TCom]
    [LawfulBEq (InnerOuter.hachiLiftCom Φ 15 16
      (toMat (rows := dRows) (cols := μ + n * 8) dKey)).TCom]
    (stmt : endpiece.WEvalStatement)
    (ws : InnerOuter.WEvalStatement (PolyVec (Rq Φ) dRows) F m₀)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (hD : WfMat dRows (μ + n * 8) dKey) (hstmt : RepWEval (dRows := dRows) (m₀ := m₀) stmt ws)
    (hw : RepLiftedWitness w sw) (hmax : μ + n * 8 ≤ Usize.max)
    (hm0 : 2 ^ m₀ ≤ Usize.max) :
    endpiece.end_piece_check dKey stmt w
      ⦃ b => (b = true ↔
        InnerOuter.endPieceCheck Φ m₀ 15 16 16
          (InnerOuter.hachiLiftCom Φ 15 16
            (toMat (rows := dRows) (cols := μ + n * 8) dKey)) phiF ws sw = true) ⦄ := by
  rename_i hbeqK hlawK
  obtain ⟨hWt, hWp, hWv, hteq, hpeq, hveq⟩ := hstmt
  have hlenv : (alloc.vec.Vec.len stmt.point).val = m₀ := by simpa using hWp.1
  subst hlenv
  rw [endpiece.end_piece_check]
  simp only [endpiece.WEvalStatement.impl.point, endpiece.WEvalStatement.impl.t,
    endpiece.WEvalStatement.impl.value, bind_tc_ok]
  step with lift_commit_spec (dRows := dRows) (μ := μ) (n := n) dKey w sw hD hw hmax
    as ⟨com, hWcom, hcom⟩
  step with poly_vec_equals_spec (k := dRows) com stmt.t hWcom hWt as ⟨bcom, hbcom⟩
  have hlawF : LawfulBEq F := inferInstanceAs (LawfulBEq (Vector K Hachi.ext4Params.d))
  simp only [InnerOuter.endPieceCheck]
  have hA : (((InnerOuter.hachiLiftCom Φ 15 16
      (toMat (rows := dRows) (cols := μ + n * 8) dKey)).com sw == ws.t) = true) ↔ bcom = true := by
    constructor
    · intro h
      exact hbcom.mpr (by rw [hcom, hteq]; exact @eq_of_beq _ hbeqK hlawK _ _ h)
    · intro h
      have h2 := hbcom.mp h
      rw [hcom, hteq] at h2
      rw [h2]
      exact @beq_self_eq_true _ hbeqK (@LawfulBEq.toReflBEq _ hbeqK hlawK) _
  by_cases hbt : bcom = true
  · rw [if_pos hbt]
    step with lift_short_check_spec w sw hw as ⟨bshort, hbshort⟩
    have hB : (InnerOuter.liftShortCheck Φ 15 16 sw = true) ↔ bshort = true := by
      rw [InnerOuter.liftShortCheck_eq_true_iff, hbshort]
    by_cases hst : bshort = true
    · rw [if_pos hst]
      step with w_table_mle_eval_spec (μ := μ) (n := n) w sw (alloc.vec.Vec.len stmt.point)
        stmt.point hw hWp hm0 hmax as ⟨e, hRe, he⟩
      apply spec_mono (ext_eq_spec e stmt.value hRe hWv)
      intro r hr
      rw [hr, he, hpeq, hveq]
      simp [hA.mpr hbt, hB.mpr hst]
    · rw [if_neg hst, WP.spec_ok]
      have hBfalse : InnerOuter.liftShortCheck Φ 15 16 sw = false := by
        rcases Bool.eq_false_or_eq_true (InnerOuter.liftShortCheck Φ 15 16 sw) with h | h
        · exact absurd (hB.mp h) hst
        · exact h
      simp [hBfalse]
  · rw [if_neg hbt, WP.spec_ok]
    have hAfalse : ((InnerOuter.hachiLiftCom Φ 15 16
        (toMat (rows := dRows) (cols := μ + n * 8) dKey)).com sw == ws.t) = false := by
      rcases Bool.eq_false_or_eq_true ((InnerOuter.hachiLiftCom Φ 15 16
        (toMat (rows := dRows) (cols := μ + n * 8) dKey)).com sw == ws.t) with h | h
      · exact absurd (hA.mp h) hbt
      · exact h
    simp [hAfalse]

/-- `end_piece_prove` is the honest prover's single message: the identity
(`endPieceProver`, `EndPiece/Reduction.lean:241`). -/
theorem end_piece_prove_spec {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (hw : RepLiftedWitness w sw) :
    endpiece.end_piece_prove w
      ⦃ out => RepLiftedWitness out sw ⦄ := by
  rw [endpiece.end_piece_prove, WP.spec_ok]
  exact hw

/-- `end_piece_witness` is the witness read off the one-round transcript: the
message itself (`endPieceWitness`, `EndPiece/Reduction.lean:172`).

`hstmt` turned out to be unnecessary and is kept because the statement is the
one this file was staged with: the extracted function ignores its statement
argument, so nothing about the statement's representation is needed. -/
theorem end_piece_witness_spec {dRows m₀ μ n : ℕ} (stmt : endpiece.WEvalStatement)
    (ws : InnerOuter.WEvalStatement (PolyVec (Rq Φ) dRows) F m₀)
    (message : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (hstmt : RepWEval (dRows := dRows) (m₀ := m₀) stmt ws)
    (hw : RepLiftedWitness message sw) :
    endpiece.end_piece_witness stmt message
      ⦃ out => RepLiftedWitness out sw ⦄ := by
  rw [endpiece.end_piece_witness, WP.spec_ok]
  exact hw

end HachiEquiv.EndPiece
