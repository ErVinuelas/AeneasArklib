/-
The **QuadEval fold**: statements only, not proofs.

Staged here rather than in `lean/` because nothing below is proved — see
`lean-wip/README.md`.

It imports `Balanced`, which is legitimate now and was not when this file was
written: `lean-wip/Balanced.lean` was out with an Aristotle session then, and
`lake build` produces no `.olean` for anything in this directory, so a wip file
cannot import another wip file. `Balanced.lean` was proved and promoted to
`lean/` on 2026-09-04, so `ddBal` and `bddZ` come from there and the duplicates
that stood in for them are gone.

## The shape that is new here

Every `_spec` in `lean/Scheme.lean` is an *equality*: the extracted function
returns a value, and the spec says which. Four of the statements below are
**iffs** instead, and that is forced by the specification rather than chosen:
`InSb`, `vecInSb`, `relOut` and `paperRelOut` are `Prop`s — `relOut` is a `Set`
of conjunctions (`QuadEval/Reduction.lean:258`) — while the Rust returns a
`Bool`. So the obligation is "the decision procedure decides the proposition",
not "two values agree". `commit.verify_weak` is the contrasting case: ArkLib
states *that* one as a `Bool`, so its spec is an equality.

This shape is not in `STAGE2_SCOPING.md`'s erasure catalogue. It is low-risk —
every conjunct is decidable, `Rq` equality being canonical and the norms `ℕ` —
but it changes what the proof has to produce.

## Proof notes

`in_sb_spec` is the one genuinely new arithmetic obligation and the one worth
reading twice. The box is **asymmetric**: `-⌊b/2⌋` is admissible and `+⌊b/2⌋`
is not, so the Rust branches on the sign of the centered representative rather
than testing a magnitude. The missing lemma is that branch against
`ZMod.valMinAbs`, which is the same case split `commit::centered_abs` already
carries — but used two-sidedly, where `centered_abs` collapses to a magnitude.
A proof that reaches for `centered_abs` alone cannot close it.

`carrier_entry_spec` needs `gadgetMul_apply` (`Gadget/Core.lean:429`) as a
*load-bearing* step, not a rewrite of convenience: the Rust computes the
collapsed per-block digit sum where `splitForm` is a matrix product, and the
matrix in question is ~64 GiB, so the two are equal only through that lemma.
The same applies to `j_mul` at the `z` width, where the matrix is ~2.5 TB.

`bounded_z_gadget_decompose`'s round trip is **conditional** — that is the whole
content of `τ = 5 < δ = 8` — so `gadget_mul_z_inverts_spec` carries the
shortness hypothesis. Its *range* is unconditional; do not merge the two.

**No local `[DecidableEq (ZMod q)]` binder** in any statement below, for the
reason `Commitment.lean` states itself.
-/

import Scheme
import Balanced
import ArkLib.Commitments.Functional.Hachi.QuadEval.Gadgets
import ArkLib.Commitments.Functional.Hachi.QuadEval.Reduction
import ArkLib.Commitments.Functional.Hachi.Params

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.QuadEval

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme
open HachiEquiv.Balanced (ddBal bddZ)

/-! ## The `z`-side gadget siblings -/

/-- `gadget::bounded_z_gadget_decompose` — ArkLib's
`BoundedDigitDecomposition.gadgetDecompose` at `bddZ`. The same triple loop as
the full-width gadget, at `τ = 5` over the bounded digit map. -/
theorem bounded_z_gadget_decompose_spec {rows : ℕ} (x : linalg.PolyVec)
    (hx : WfVec rows x) (hmax : 5 * rows ≤ Usize.max) :
    gadget.bounded_z_gadget_decompose x
      ⦃ z => WfVec (rows * 5) z ∧ toVec (k := rows * 5) z
        = bddZ.gadgetDecompose Φ (toVec (k := rows) x) ⦄ := by
  sorry

/-- `gadget::gadget_mul_z` — ArkLib's `gadgetMul` at `digits = 5`, equivalently
`jMatrix Φ 16 rows 5 *ᵥ ·`. Collapsed: the Rust computes the per-block digit
sum, and `gadgetMul_apply` is what makes that the matrix product. -/
theorem gadget_mul_z_spec (rows : Std.Usize) (v : linalg.PolyVec)
    (hv : WfVec (rows.val * 5) v) (hmax : 5 * rows.val ≤ Usize.max) :
    gadget.gadget_mul_z rows v
      ⦃ z => WfVec rows.val z ∧ toVec (k := rows.val) z
        = gadgetMul Φ (16 : ZMod q) (toVec (k := rows.val * 5) v) ⦄ := by
  sorry

/-- **The conditional round trip** `J · J⁻¹(z) = z`, on `Z_BOUND`-short input —
`boundedGadgetDecompose_gadgetMul_eq` read on the extracted pair. The hypothesis
is the whole content of `τ = 5 < δ`: without it the statement is false, and the
full-width gadget's counterpart needs no such hypothesis. -/
theorem gadget_mul_z_inverts_spec (rows : Std.Usize) (x : linalg.PolyVec)
    (hx : WfVec rows.val x) (hmax : 5 * rows.val ≤ Usize.max)
    (hshort : ∀ i : Fin rows.val, ∀ k < N,
      (((toVec (k := rows.val) x) i).1.coeff k).valMinAbs.natAbs ≤ 131072) :
    (do
      let z ← gadget.bounded_z_gadget_decompose x
      gadget.gadget_mul_z rows z)
      ⦃ y => WfVec rows.val y ∧ toVec (k := rows.val) y = toVec (k := rows.val) x ⦄ := by
  sorry

/-! ## The carrier algebra -/

/-- `quadeval::carrier_entry` — ArkLib's `carrierEntry`, i.e.
`splitForm (gadgetMatrix …) a s`. The Rust never materializes the gadget matrix
(~64 GiB at these parameters), so the equality runs through `gadgetMul_apply`. -/
theorem carrier_entry_spec {rows : ℕ} (a s : linalg.PolyVec)
    (ha : WfVec rows a) (hs : WfVec (rows * 8) s) (hmax : 8 * rows ≤ Usize.max) :
    quadeval.carrier_entry a s
      ⦃ w => Wf w ∧ toRq w
        = Hachi.carrierEntry Φ (16 : ZMod q) (toVec (k := rows) a)
            (toVec (k := rows * 8) s) ⦄ := by
  sorry

/-- `quadeval::tensor_g1` — ArkLib's `tensorG1`, the Eq. (20) row-4 left side. -/
theorem tensor_g1_spec {blocks : ℕ} (c x : linalg.PolyVec)
    (hc : WfVec blocks c) (hx : WfVec (blocks * 8) x) (hmax : 8 * blocks ≤ Usize.max) :
    quadeval.tensor_g1 c x
      ⦃ y => Wf y ∧ toRq y
        = Hachi.tensorG1 Φ (16 : ZMod q) 8 (toVec (k := blocks) c)
            (toVec (k := blocks * 8) x) ⦄ := by
  sorry

/-! ## The box, and why these are iffs -/

/-- `quadeval::in_sb` **decides** ArkLib's `InSb` at `β = 16`.

An iff, not an equality: `InSb` is a `Prop` (`QuadEval/Reduction.lean:297`).
The box `[-⌊b/2⌋, ⌈b/2⌉-1] = [-8, 7]` is asymmetric, so the proof splits on the
sign of `valMinAbs` — see the file header. -/
theorem in_sb_spec (a : ring.Rq) (ha : Wf a) :
    quadeval.in_sb a ⦃ b => (b = true ↔ InnerOuter.InSb Φ 16 (toRq a)) ⦄ := by
  sorry

/-- `quadeval::vec_in_sb` decides `vecInSb`. Branchless to the end, so the loop
invariant is "no entry so far has failed" rather than an early exit. -/
theorem vec_in_sb_spec {cols : ℕ} (v : linalg.PolyVec) (hv : WfVec cols v) :
    quadeval.vec_in_sb v
      ⦃ b => (b = true ↔ InnerOuter.vecInSb Φ 16 (toVec (k := cols) v)) ⦄ := by
  sorry

/-- **The box is strictly stronger than the ball.** `paperRelOut ⊆ relOut` under
`b/2 ≤ γ` (`paperRelOut_subset_relOut`, `:367`), which is `8 ≤ 15` here. Stated
on the extracted pair because it is what the semantics tests witness and what a
future `rel_out` optimization must not break. -/
theorem paper_rel_out_implies_rel_out_spec {cols : ℕ} (v : linalg.PolyVec)
    (hv : WfVec cols v) :
    (do
      let b ← quadeval.vec_in_sb v
      ok b)
      ⦃ b => b = true →
        vecLInftyNorm Φ (toVec (k := cols) v) ≤ 15 ⦄ := by
  sorry

end HachiEquiv.QuadEval
