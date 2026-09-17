/-
Stage 5's composed evaluation chain (`hachi/src/chain.rs`), **proved locally**.

Two obligations, both mirroring `evaluation` (`Composition.lean:283`) — one at
its verifier, one at its honest prover — and both compositions of specs that
already exist: nine promoted links and the staged `Sumcheck.lean`. Nothing new
is computed here; what is new is the *thread*, and that thread is the content.
Both proofs are `step` chains through the link specs, one `rcases` on the
verifier's `Option`, and nothing else. They are complete in this file and,
since `Sumcheck.lean`'s last obligations closed on 2026-09-11, kernel-clean:
the two headline closures print exactly the three Lean kernel axioms.

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

# Promotion

Promoted from `lean-wip/` on 2026-09-11, behind `Sumcheck.lean`, which it
imports. Both statements are compositions of proved specs and were proved
locally, not by Aristotle.
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
  have h := usize_max_ge
  norm_num [μR, nR, InnerOuter.rlinCols, InnerOuter.rlinRows]
  omega

/-! ## `copy_point`, and carrying a point through a copy -/

/-- Two vectors with the same words are the same point. -/
theorem toPoint_of_val_eq {m : ℕ} {a b : alloc.vec.Vec cpoly.field.Ext4} (h : a.val = b.val) :
    toPoint (m := m) a = toPoint (m := m) b := by
  funext j; simp only [toPoint, h]

/-- Well-formedness transfers along equal words. -/
theorem wfPoint_of_val_eq {m : ℕ} {a b : alloc.vec.Vec cpoly.field.Ext4} (h : a.val = b.val)
    (hb : WfPoint m b) : WfPoint m a := by
  refine ⟨by rw [h]; exact hb.1, ?_⟩
  intro x hx; rw [h] at hx; exact hb.2 x hx

/-- The loop of `copy_point`: the prefix pushed so far is the prefix of `p`. -/
theorem copy_point_loop_spec (p out : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize)
    (hi : i.val ≤ p.val.length) (hout : out.val = p.val.take i.val) :
    chain.copy_point_loop p out i ⦃ z => z.val = p.val ⦄ := by
  rw [chain.copy_point_loop]
  apply loop.spec_decr_nat (fun s => p.val.length - s.2.val)
    (fun s => s.2.val ≤ p.val.length ∧ s.1.val = p.val.take s.2.val)
  · rintro ⟨out1, i1⟩ hinv
    obtain ⟨hi1, hout1⟩ : i1.val ≤ p.val.length ∧ out1.val = p.val.take i1.val := hinv
    simp only [chain.copy_point_loop.body]
    by_cases hlt : i1 < alloc.vec.Vec.len p
    · rw [if_pos hlt]
      have hlt' : i1.val < p.val.length := by scalar_tac
      have hlen1 : out1.val.length = i1.val := by
        rw [hout1, List.length_take]; omega
      step as ⟨e, he⟩
      step as ⟨out2, hout2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hout2, hi2, hout1, he]
      exact List.take_concat_get' _ _ hlt'
    · rw [if_neg hlt]
      have heq : i1.val = p.val.length := by scalar_tac
      simp only [WP.spec_ok]
      rw [hout1, heq, List.take_length]
  · exact ⟨hi, hout⟩

/-- `copy_point` returns the same words. Total: every push is bounded by `p`'s
own length. -/
theorem copy_point_spec (p : alloc.vec.Vec cpoly.field.Ext4) :
    chain.copy_point p ⦃ z => z.val = p.val ⦄ := by
  rw [chain.copy_point]
  exact copy_point_loop_spec p (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by simp) (by simp)

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
  rw [chain.chain_verify]
  step with to_quad_eval_statement_spec poly_stmt ps hps as ⟨stmt, hstmt⟩
  step with rlin_stmt_spec pp stmt v c gamma b mr md ir idg zd sp
    (InnerOuter.toQuadEvalStatement Φ ps) hpp hstmt hv hc hcn hb hmr hmd hir hidg hzd
    as ⟨rlin, hrlin⟩
  step with poly_vec_copy_spec (k := dRows) t ht as ⟨pv, hpvW, hpv⟩
  step with copy_point_spec tau0 as ⟨v1, hv1⟩
  step with copy_point_spec tau1 as ⟨v2, hv2⟩
  step with NestedZeroCheckStmt_new_spec (n := nR) (μ := μR) (m₀ := M + 1) (m₁ := m₁)
    (dRows := dRows) rlin pv alpha v1 v2
    ⟨InnerOuter.rlinStmt (zDigits := 5) Φ sp (16 : ZMod q) 16 gamma.val
        (InnerOuter.toQuadEvalStatement Φ ps, toVec (k := 1) v, toChals c hcn),
      toVec (k := dRows) t, toExt alpha, toPoint (m := M + 1) tau0, toPoint (m := m₁) tau1⟩
    hrlin hpvW ha (wfPoint_of_val_eq hv1 h0) (wfPoint_of_val_eq hv2 h1) hpv rfl
    (toPoint_of_val_eq hv1) (toPoint_of_val_eq hv2) as ⟨zc, hzc⟩
  step with nested_to_round_statement_spec (n := nR) (μ := μR) (m₀ := M + 1) (m₁ := m₁)
    (dRows := dRows) zc _ hzc as ⟨opened, hopened⟩
  set s0 := chainStart sp ps (toVec (k := 1) v) (toChals c hcn) gamma.val
    (toVec (k := dRows) t) (toExt alpha) (toPoint (m := M + 1) tau0)
    (toPoint (m := m₁) tau1) with hs0
  have hopened' : RepRoundStmt (n := nR) (μ := μR) (m₀ := M + 1) (m₁ := m₁) (i := 0)
      (dRows := dRows) opened s0 := hopened
  step with round_verify_loop_spec (n := nR) (μ := μR) (m₀ := M + 1) (m₁ := m₁)
    (dRows := dRows) opened msgs challenges s0 gs hopened' hg hch as ⟨after, hafter⟩
  rcases hver : verifyRounds s0 gs (toPoint (m := M + 1) challenges) (M + 1) le_rfl with _ | s'
  · rw [hver] at hafter
    simp only at hafter
    rcases after with _ | s2
    · simp only [WP.spec_ok, chainVerdict, hver]
    · exact absurd hafter (by simp)
  · rw [hver] at hafter
    obtain ⟨s, hs_eq, hsrep⟩ := hafter
    rcases after with _ | s2
    · cases hs_eq
    have hs2 : s2 = s := Option.some.inj hs_eq
    subst hs2
    simp only
    step with final_check_spec (n := nR) (μ := μR) (m₀ := M + 1) (m₁ := m₁) (dRows := dRows)
      s2 y_prime gamma s' hsrep hy hm0 rlin_dims_fit as ⟨c_final, hcf⟩
    step with copy_point_spec challenges as ⟨v3, hv3⟩
    step with WEvalStatement_new_spec (dRows := dRows) (m₀ := M + 1) pv v3 y_prime
      ⟨toVec (k := dRows) t, toPoint (m := M + 1) challenges, toExt y_prime⟩
      hpvW (wfPoint_of_val_eq hv3 hch) hy hpv (toPoint_of_val_eq hv3) rfl as ⟨weval, hweval⟩
    step with end_piece_check_spec (dRows := dRows) (μ := μR) (n := nR) (m₀ := M + 1) d_key weval
      ⟨toVec (k := dRows) t, toPoint (m := M + 1) challenges, toExt y_prime⟩ w sw hD hweval hw
      rlin_dims_fit hm0 as ⟨c_end, hce⟩
    by_cases hcft : c_final = true
    · rw [if_pos hcft]
      simp only [WP.spec_ok, chainVerdict, hver]
      rw [← hcf, hcft, Bool.true_and]
      exact Bool.eq_iff_iff.mpr hce
    · rw [if_neg hcft]
      have hcff : c_final = false := by simpa using hcft
      simp only [WP.spec_ok, chainVerdict, hver]
      rw [← hcf, hcff, Bool.false_and]

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
    (poly_stmt : quadeval.PolyEvalStatement) (raw : alloc.vec.Vec linalg.PolyVec)
    (c : linalg.PolyVec) (w : ringswitch.LiftedWitness) (alpha : cpoly.field.Ext4)
    (tau0 tau1 challenges : alloc.vec.Vec cpoly.field.Ext4) (gamma : Std.U64)
    (b mr md ir idg zd : Std.Usize)
    (sp : Hachi.PublicParamsD Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (ps : InnerOuter.PolyEvalStatement Φ 1 8 1 8 1 10 10)
    (wo : InnerOuter.Opening Φ 1 (2 ^ 10) 8 (2 ^ 10) 8)
    (sw : InnerOuter.LiftedWitness Φ μR nR)
    (hpp : RepParamsD pp sp) (hps : RepPolyEval poly_stmt ps)
    -- the RAW blocks now: `chain_open` decomposes internally, so the honest
    -- prover never holds `Decomp.message`
    (hm : (fun i : Fin (2 ^ 10) => gadgetDecompose Φ Scheme.dd
            (toVec (k := 2 ^ 10) (raw.val.getD i.val (alloc.vec.Vec.new ring.Rq))))
          = wo.message)
    (hWm : WfBlocks (2 ^ 10) (2 ^ 10) raw)
    (hc : WfVec (2 ^ 10) c)
    (hcn : ∀ i : Fin (2 ^ 10), Rq.l1Norm Φ (toVec (k := 2 ^ 10) c i) ≤ 16)
    (hw : RepLiftedWitness w sw) (ha : Reduced alpha)
    (h0 : WfPoint (M + 1) tau0) (h1 : WfPoint m₁ tau1) (hch : WfPoint (M + 1) challenges)
    (hD : WfMat dRows (μR + nR * 8) d_key) (hm0 : 2 ^ (M + 1) ≤ Usize.max)
    (hb : b.val = 2 ^ 10) (hmr : mr.val = 2 ^ 10) (hmd : md.val = 8)
    (hir : ir.val = 1) (hidg : idg.val = 8) (hzd : zd.val = 5) :
    chain.chain_open pp d_key poly_stmt raw c w alpha tau0 tau1 challenges gamma
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
  have hm0v : (alloc.vec.Vec.len tau0).val = M + 1 := by simpa using h0.1
  rw [chain.chain_open]
  step with to_quad_eval_statement_spec poly_stmt ps hps as ⟨stmt, hstmt⟩
  step with honest_compute_v_from_raw_spec pp stmt raw sp
    (InnerOuter.toQuadEvalStatement Φ ps) wo hpp hstmt hm hWm as ⟨v, hvW, hvV⟩
  step with rlin_stmt_spec pp stmt v c gamma b mr md ir idg zd sp
    (InnerOuter.toQuadEvalStatement Φ ps) hpp hstmt hvW hc hcn hb hmr hmd hir hidg hzd
    as ⟨rlin, hrlin⟩
  rw [hvV] at hrlin
  step with lift_commit_spec (dRows := dRows) (μ := μR) (n := nR) d_key w sw hD hw rlin_dims_fit
    as ⟨t, htW, htV⟩
  step with poly_vec_copy_spec (k := dRows) t htW as ⟨pv, hpvW, hpv⟩
  step with copy_point_spec tau0 as ⟨v1, hv1⟩
  step with copy_point_spec tau1 as ⟨v2, hv2⟩
  step with NestedZeroCheckStmt_new_spec (n := nR) (μ := μR) (m₀ := M + 1) (m₁ := m₁)
    (dRows := dRows) rlin pv alpha v1 v2
    ⟨InnerOuter.rlinStmt (zDigits := 5) Φ sp (16 : ZMod q) 16 gamma.val
        (InnerOuter.toQuadEvalStatement Φ ps,
          InnerOuter.honestComputeV Φ sp ddBal (InnerOuter.toQuadEvalStatement Φ ps) wo,
          toChals c hcn),
      toVec (k := dRows) t, toExt alpha, toPoint (m := M + 1) tau0, toPoint (m := m₁) tau1⟩
    hrlin hpvW ha (wfPoint_of_val_eq hv1 h0) (wfPoint_of_val_eq hv2 h1) hpv rfl
    (toPoint_of_val_eq hv1) (toPoint_of_val_eq hv2) as ⟨zc, hzc⟩
  step with nested_to_round_statement_spec (n := nR) (μ := μR) (m₀ := M + 1) (m₁ := m₁)
    (dRows := dRows) zc _ hzc as ⟨opened, hopened⟩
  rw [htV] at hopened
  have hopened' : RepRoundStmt (n := nR) (μ := μR) (m₀ := M + 1) (m₁ := m₁) (i := 0)
      (dRows := dRows) opened
      (chainStart sp ps
        (InnerOuter.honestComputeV Φ sp ddBal (InnerOuter.toQuadEvalStatement Φ ps) wo)
        (toChals c hcn) gamma.val
        ((InnerOuter.hachiLiftCom Φ 15 16
          (toMat (rows := dRows) (cols := μR + nR * 8) d_key)).com sw)
        (toExt alpha) (toPoint (m := M + 1) tau0) (toPoint (m := m₁) tau1)) := hopened
  step with honest_round_messages_spec (n := nR) (μ := μR) (M := M) (m₁ := m₁) (dRows := dRows)
    opened w challenges _ sw hopened' hw hch hm0 rlin_dims_fit as ⟨msgs, hmlen, hmsgs⟩
  step with honest_compute_y_spec (μ := μR) (n := nR) w (alloc.vec.Vec.len tau0) challenges sw hw
    (by rw [hm0v]; exact hch) (by rw [hm0v]; exact hm0) rlin_dims_fit as ⟨y', hyR, hyv⟩
  rw [hm0v] at hyv
  exact ⟨hvW, hvV, htW, htV, ⟨hmlen, fun k => hmsgs k.val k.isLt⟩, hyR, hyv⟩

end HachiEquiv.Chain
