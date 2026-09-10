/-
Stage 5's composed evaluation chain (`hachi/src/chain.rs`): **statements only**.

Two obligations, both mirroring `evaluation` (`Composition.lean:283`) — one at
its verifier, one at its honest prover — and both compositions of specs that
already exist: nine promoted links and the staged `Sumcheck.lean`. Nothing new
is computed here; what is new is the *thread*, and that thread is the content.

# What `evaluation` is, and what these statements are against

`evaluation` is an `EscapeGCWSSPackage`: a soundness certificate carrying
provers, verifiers, extractors and escape events over a `ProbComp`. None of
that has an Aeneas model, and `chain.rs` § "What this module is" scopes the
translation to the chain's **computational residue**. So the right-hand sides
here are not `evaluation` itself but two plain definitions built from the link
definitions `evaluation` composes:

* `chainStart` — rows 1 to 7 as one statement map: `toQuadEvalStatement`
  (bridge), `rlinStmt` (the `R^lin` adapter), the `NestedZeroCheckStatement`
  the lift and zero-check rows adjoin `(t, α, τ₀, τ_α)` to (`batch` is `id`),
  and `nestedToRoundStatement` (the sumcheck bridge). Row 2, QuadEval, is a
  pass-through of the message `v` and the challenge `c`.
* `chainVerdict` — the **three** boolean decisions the composed verifier
  actually runs, in the specification's own short-circuit order: `roundCheck`
  once per round through `verifyRounds` (`roundVerifier`, `Rounds.lean:116`),
  then `finalCheck` (`FinalEval.lean:99`) and `endPieceCheck`
  (`EndPiece/Reduction.lean`) as the conjunction their `GuardedForm`s name.

Eq. (20), the lift's shortness and the two zero-check blocks appear in neither,
and that is faithful: they are *relations* the soundness theorems quantify
over, not checks any verifier evaluates (`chain.rs` § "What the verifier
checks, and what it does not").

# Conventions

Instantiated where the reps it consumes are: the QuadEval carriers
(`RepParamsD`, `RepStmt`, `RepPolyEval`) and the `R^lin` adapter pin the
inner/outer dimensions and `nR = rlinRows 1 1 1`, `μR = rlinCols 1 8 8 5 10 10`;
the sumcheck arities `m₀ = M + 1`, `m₁` and the lift key's `dRows` stay
generic, as in `Sumcheck.lean` and `EndPiece.lean`. `TCom` is the lift
commitment at key `d_key`, `hachiLiftCom Φ 15 16 (toMat d_key)`, as
`lift_commit_spec` and `end_piece_check_spec` have it; the `BEq`/`LawfulBEq`
instance hypotheses on it are `end_piece_check_spec`'s.

The hypotheses are the union of the links' representation invariants plus the
two value bounds they earn: `2 ^ m₀ ≤ Usize.max` (tables) and the lift key's
width `μR + nR·8 ≤ Usize.max`, which at the pin is a concrete `57 384` and is a
helper lemma rather than a hypothesis.

# Staging

This imports `Sumcheck`, itself staged, so validating it needs the `LEAN_PATH`
detour of `lean-wip/README.md` § "Working here", and the Aristotle helper's
plain validation cannot integrate a return for it until `Sumcheck.lean` is
promoted. Both statements are compositions of proved or stated specs and are
expected to be proved locally, not by Aristotle.
-/
import Rlin
import Sumcheck

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly CompPoly.Extension ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.Chain

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme
open HachiEquiv.RingSwitch HachiEquiv.Ext HachiEquiv.ZeroCheck HachiEquiv.EndPiece
open HachiEquiv.Balanced HachiEquiv.QuadEvalProtocol HachiEquiv.Rlin HachiEquiv.Sumcheck

/-- The `R^lin` system's row count at the pin, `rlinRows 1 1 1 = 5`. -/
abbrev nR : ℕ := InnerOuter.rlinRows 1 1 1

/-- The `R^lin` system's column count at the pin, `rlinCols 1 8 8 5 10 10 = 57 344`. -/
abbrev μR : ℕ := InnerOuter.rlinCols 1 8 8 5 10 10

/-- The lift key's width fits a `usize`: `57 344 + 5 · 8`. What
`lift_commit_spec`, `end_piece_check_spec` and the table specs ask for as
`hmax`, discharged once here rather than carried as a hypothesis. -/
theorem rlin_dims_fit : μR + nR * 8 ≤ Usize.max := by
  sorry

/-! ## `copy_point` -/

/-- The loop of `copy_point`: the prefix pushed so far is the prefix of `p`. -/
theorem copy_point_loop_spec (p out : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize)
    (hi : i.val ≤ p.val.length) (hout : out.val = p.val.take i.val) :
    chain.copy_point_loop p out i ⦃ z => z.val = p.val ⦄ := by
  sorry

/-- `copy_point` returns the same words. Total: every push is bounded by `p`'s
own length. -/
theorem copy_point_spec (p : alloc.vec.Vec cpoly.field.Ext4) :
    chain.copy_point p ⦃ z => z.val = p.val ⦄ := by
  sorry

/-! ## The statement thread and the verdict -/

/-- Rows 1 to 7 of the composed chain as one statement map: the bridge, the
`R^lin` adapter, the nested zero-check statement the lift and zero-check rows
adjoin `(t, α, τ₀, τ_α)` to, and the sumcheck bridge. Row 2 passes `v` and the
challenges `c` through. -/
def chainStart {M m₁ dRows : ℕ}
    (sp : Hachi.PublicParamsD Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (ps : InnerOuter.PolyEvalStatement Φ 1 8 1 8 1 10 10)
    (v : PolyVec (Rq Φ) 1) (chals : Fin (2 ^ 10) → InnerOuter.ShortChallenge Φ 16) (γ : ℕ)
    (t : PolyVec (Rq Φ) dRows) (α : F) (τ₀ : Fin (M + 1) → F) (τα : Fin m₁ → F) :
    InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F nR μR (M + 1) m₁ 0 :=
  InnerOuter.nestedToRoundStatement Φ (M + 1) m₁ phiF
    ⟨InnerOuter.rlinStmt (zDigits := 5) Φ sp (16 : ZMod q) 16 γ
        (InnerOuter.toQuadEvalStatement Φ ps, v, chals), t, α, τ₀, τα⟩

/-- The composed verifier's decision: `roundCheck` per round (`verifyRounds`,
`none` at the first rejection), then `finalCheck` and `endPieceCheck` on what
the prover sent. `γ` is both `rlinStmt`'s bound and `finalCheck`'s; the lift
commitment scheme is `hachiLiftCom` at the extracted key, as `end_piece_check_spec`
has it. -/
def chainVerdict {M m₁ dRows : ℕ} (d_key : linalg.PolyMatrix)
    [BEq (InnerOuter.hachiLiftCom Φ 15 16
      (toMat (rows := dRows) (cols := μR + nR * 8) d_key)).TCom]
    [LawfulBEq (InnerOuter.hachiLiftCom Φ 15 16
      (toMat (rows := dRows) (cols := μR + nR * 8) d_key)).TCom]
    (s0 : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F nR μR (M + 1) m₁ 0)
    (gs : Fin (M + 1) → InnerOuter.RoundMsg F 16) (cs : Fin (M + 1) → F) (γ : ℕ)
    (t : PolyVec (Rq Φ) dRows) (y' : F) (sw : InnerOuter.LiftedWitness Φ μR nR) : Bool :=
  match verifyRounds s0 gs cs (M + 1) le_rfl with
  | none => false
  | some sm =>
    InnerOuter.finalCheck Φ (M + 1) m₁ γ 16 phiF sm y' &&
      InnerOuter.endPieceCheck Φ (M + 1) 15 16 16
        (InnerOuter.hachiLiftCom Φ 15 16 (toMat (rows := dRows) (cols := μR + nR * 8) d_key))
        phiF (⟨t, cs, y'⟩ : InnerOuter.WEvalStatement (PolyVec (Rq Φ) dRows) F (M + 1)) sw

/-! ## The two rows -/

/-- `chain_verify` computes the composed verifier's verdict (spec: `evaluation`
at its verifier, `Composition.lean:283`): the thread `chainStart` on the public
inputs, the wire messages `(v, t, msgs, y′, w)` and the challenges
`(c, α, τ₀, τ_α, cs)`, then `chainVerdict`. An equality of decisions, so both
directions of every check are carried.

Hypotheses are the links' invariants: the QuadEval carriers, the `ℓ₁` bound
`toChals` needs on `c`, the wire lengths (`msgs`, `challenges`, `tau0` at `m₀`,
`tau1` at `m₁`) that the specification's transcript types and that erase to
`Vec`s here, the lift key's shape, and the six dimension arguments pinned as
`rlin_stmt_spec` pins them. `2 ^ m₀ ≤ Usize.max` is `final_check`'s and
`end_piece_check`'s. -/
theorem chain_verify_spec {M m₁ dRows : ℕ}
    (pp : quadeval.PublicParamsD) (d_key : linalg.PolyMatrix)
    (poly_stmt : quadeval.PolyEvalStatement) (v c t : linalg.PolyVec)
    (alpha : cpoly.field.Ext4) (tau0 tau1 : alloc.vec.Vec cpoly.field.Ext4)
    (msgs : alloc.vec.Vec sumcheck.RoundMsg) (challenges : alloc.vec.Vec cpoly.field.Ext4)
    (y_prime : cpoly.field.Ext4) (w : ringswitch.LiftedWitness) (gamma : Std.U64)
    (b mr md ir idg zd : Std.Usize)
    [BEq (InnerOuter.hachiLiftCom Φ 15 16
      (toMat (rows := dRows) (cols := μR + nR * 8) d_key)).TCom]
    [LawfulBEq (InnerOuter.hachiLiftCom Φ 15 16
      (toMat (rows := dRows) (cols := μR + nR * 8) d_key)).TCom]
    (sp : Hachi.PublicParamsD Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (ps : InnerOuter.PolyEvalStatement Φ 1 8 1 8 1 10 10)
    (gs : Fin (M + 1) → InnerOuter.RoundMsg F 16)
    (sw : InnerOuter.LiftedWitness Φ μR nR)
    (hpp : RepParamsD pp sp) (hps : RepPolyEval poly_stmt ps)
    (hv : WfVec 1 v) (hc : WfVec (2 ^ 10) c)
    (hcn : ∀ i : Fin (2 ^ 10), Rq.l1Norm Φ (toVec (k := 2 ^ 10) c i) ≤ 16)
    (ht : WfVec dRows t) (ha : Reduced alpha)
    (h0 : WfPoint (M + 1) tau0) (h1 : WfPoint m₁ tau1)
    (hg : RepMsgs (m₀ := M + 1) msgs gs) (hch : WfPoint (M + 1) challenges)
    (hy : Reduced y_prime) (hw : RepLiftedWitness w sw)
    (hD : WfMat dRows (μR + nR * 8) d_key) (hm0 : 2 ^ (M + 1) ≤ Usize.max)
    (hb : b.val = 2 ^ 10) (hmr : mr.val = 2 ^ 10) (hmd : md.val = 8)
    (hir : ir.val = 1) (hidg : idg.val = 8) (hzd : zd.val = 5) :
    chain.chain_verify pp d_key poly_stmt v c t alpha tau0 tau1 msgs challenges y_prime w
        gamma b mr md ir idg zd
      ⦃ out => out = chainVerdict (dRows := dRows) d_key
        (chainStart sp ps (toVec (k := 1) v) (toChals c hcn) gamma.val
          (toVec (k := dRows) t) (toExt alpha) (toPoint (m := M + 1) tau0)
          (toPoint (m := m₁) tau1))
        gs (toPoint (m := M + 1) challenges) gamma.val (toVec (k := dRows) t)
        (toExt y_prime) sw ⦄ := by
  sorry

/-- `chain_open` computes the honest prover's wire content (spec: `evaluation`
at its honest prover — `honestComputeV`, `hachiLiftCom`'s `com`,
`honestComputeG` per round and `wTableMleEval`, `Composition.lean:283`):
`v` is the carrier commitment, `t` the lift commitment, the `m₀` messages are
`honestComputeG` along `honestRounds` from the thread `chainStart` at the
honest `v` and `t`, and `y′` is the witness MLE at the challenges. The lifted
witness is an input, not an output (`chain.rs` § the lifted witness).

Hypotheses are `honest_compute_v_spec`'s (`wo`, the opening the message
represents), `lift_commit_spec`'s, `honest_round_messages_spec`'s and
`honest_compute_y_spec`'s, with the width bound discharged by `rlin_dims_fit`. -/
theorem chain_open_spec {M m₁ dRows : ℕ}
    (pp : quadeval.PublicParamsD) (d_key : linalg.PolyMatrix)
    (poly_stmt : quadeval.PolyEvalStatement) (message : alloc.vec.Vec linalg.PolyVec)
    (c : linalg.PolyVec) (w : ringswitch.LiftedWitness) (alpha : cpoly.field.Ext4)
    (tau0 tau1 challenges : alloc.vec.Vec cpoly.field.Ext4) (gamma : Std.U64)
    (b mr md ir idg zd : Std.Usize)
    (sp : Hachi.PublicParamsD Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (ps : InnerOuter.PolyEvalStatement Φ 1 8 1 8 1 10 10)
    (wo : InnerOuter.Opening Φ 1 (2 ^ 10) 8 (2 ^ 10) 8)
    (sw : InnerOuter.LiftedWitness Φ μR nR)
    (hpp : RepParamsD pp sp) (hps : RepPolyEval poly_stmt ps)
    (hm : toBlocks (blocks := 2 ^ 10) (width := 2 ^ 10 * 8) message = wo.message)
    (hWm : WfBlocks (2 ^ 10) (2 ^ 10 * 8) message)
    (hc : WfVec (2 ^ 10) c)
    (hcn : ∀ i : Fin (2 ^ 10), Rq.l1Norm Φ (toVec (k := 2 ^ 10) c i) ≤ 16)
    (hw : RepLiftedWitness w sw) (ha : Reduced alpha)
    (h0 : WfPoint (M + 1) tau0) (h1 : WfPoint m₁ tau1) (hch : WfPoint (M + 1) challenges)
    (hD : WfMat dRows (μR + nR * 8) d_key) (hm0 : 2 ^ (M + 1) ≤ Usize.max)
    (hb : b.val = 2 ^ 10) (hmr : mr.val = 2 ^ 10) (hmd : md.val = 8)
    (hir : ir.val = 1) (hidg : idg.val = 8) (hzd : zd.val = 5) :
    chain.chain_open pp d_key poly_stmt message c w alpha tau0 tau1 challenges gamma
        b mr md ir idg zd
      ⦃ out =>
        let ss := InnerOuter.toQuadEvalStatement Φ ps
        let vS := InnerOuter.honestComputeV Φ sp ddBal ss wo
        let K := InnerOuter.hachiLiftCom Φ 15 16
          (toMat (rows := dRows) (cols := μR + nR * 8) d_key)
        let s0 := chainStart sp ps vS (toChals c hcn) gamma.val (K.com sw) (toExt alpha)
          (toPoint (m := M + 1) tau0) (toPoint (m := m₁) tau1)
        WfVec 1 out.1 ∧ toVec (k := 1) out.1 = vS ∧
        WfVec dRows out.2.1 ∧ toVec (k := dRows) out.2.1 = K.com sw ∧
        RepMsgs (m₀ := M + 1) out.2.2.1 (fun k =>
          InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF k.val k.isLt
            (honestRounds s0 sw (toPoint (m := M + 1) challenges) k.val k.isLt.le) sw) ∧
        Reduced out.2.2.2 ∧
        toExt out.2.2.2 =
          InnerOuter.wTableMleEval Φ (M + 1) phiF 16 sw (toPoint (m := M + 1) challenges) ⦄ := by
  sorry

end HachiEquiv.Chain
