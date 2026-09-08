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

/-- The end-piece statement's constructor preserves the relation. -/
theorem WEvalStatement_new_spec {dRows m₀ : ℕ} (t : linalg.PolyVec)
    (point : alloc.vec.Vec cpoly.field.Ext4) (value : cpoly.field.Ext4)
    (ws : InnerOuter.WEvalStatement (PolyVec (Rq Φ) dRows) F m₀)
    (hWt : WfVec dRows t) (hWp : WfPoint m₀ point) (hWv : Reduced value)
    (ht : toVec (k := dRows) t = ws.t)
    (hp : toPoint (m := m₀) point = ws.point) (hv : toExt value = ws.value) :
    endpiece.WEvalStatement.new t point value
      ⦃ out => RepWEval (dRows := dRows) (m₀ := m₀) out ws ⦄ := by
  sorry

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
  sorry

/-- `end_piece_prove` is the honest prover's single message: the identity
(`endPieceProver`, `EndPiece/Reduction.lean:241`). -/
theorem end_piece_prove_spec {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (hw : RepLiftedWitness w sw) :
    endpiece.end_piece_prove w
      ⦃ out => RepLiftedWitness out sw ⦄ := by
  sorry

/-- `end_piece_witness` is the witness read off the one-round transcript: the
message itself (`endPieceWitness`, `EndPiece/Reduction.lean:172`). -/
theorem end_piece_witness_spec {dRows m₀ μ n : ℕ} (stmt : endpiece.WEvalStatement)
    (ws : InnerOuter.WEvalStatement (PolyVec (Rq Φ) dRows) F m₀)
    (message : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (hstmt : RepWEval (dRows := dRows) (m₀ := m₀) stmt ws)
    (hw : RepLiftedWitness message sw) :
    endpiece.end_piece_witness stmt message
      ⦃ out => RepLiftedWitness out sw ⦄ := by
  sorry

end HachiEquiv.EndPiece
