/-
Target 2's QuadEval **protocol layer**: statements only.

Eleven obligations, none proved here. They are the debt `make spec-check`
found on 2026-09-08: the QuadEval fold's arithmetic was proved and promoted
(`lean/QuadEval.lean`, Aristotle session `14b9bf77`), but eleven of the
module's items -- its three carriers, the honest prover's three functions, the
two gadget-level helpers and the two output relations -- carry `Mirrors` lines
and had no `_spec` anywhere. `coverage` asked "is it measured" and answered
yes; nothing asked "is it stated". This file is the answer to the second
question for `quadeval`.

# What this file rests on, and why it is staged rather than promoted

It imports the promoted `QuadEval.lean`, which is legal here (a wip file may
import a promoted file -- `lean-wip/README.md` § "Working here") and which is
what supplies the whole representation kit: `toVec`/`WfVec`, `toMat`/`WfMat`,
`toParams`/`WfParams`, `toOpening`, `toRq`/`Wf`, and the two digit maps `ddBal`
(full width, base 16, 8 digits) and `bddZ` (bounded, base 16, `τ = 5`,
`zBound = 131072`). Nothing new is needed at the ring level; what is new is the
four representations below.

Because it imports only promoted files, this one needs **no `LEAN_PATH`
detour**:

```sh
cd hachi
lake build
lake env lean lean-wip/QuadEvalProtocol.lean
```

# The four conventions this file follows

**Carriers are related, not converted.** `RepParamsD`, `RepStmt` and `RepResp`
are `Prop`-valued relations between an extracted struct and the specification's
structure, in the shape `RepRlin` established in `ZeroCheck.lean`, and each
carrier gets one `new_spec` saying its constructor preserves the relation. No
accessor specs: that is the precedent from `RlinStatement`, whose `m`/`yvec`/
`bound` projections are consumed through the relation rather than through
theorems of their own.

**The challenge vector's rep carries a proof.** `ShortChallenge Φ ω` is the
subtype `{c : Rq Φ // ‖c‖₁ ≤ ω}` (`QuadEval/Reduction.lean:151`), so a plain
`PolyVec` cannot be converted into `Fin (2^r) → ShortChallenge Φ ω` without the
`ℓ₁` bound. `toChals` therefore takes that bound as an argument, and it appears
as a hypothesis on the two relation specs. This is not a weakening: ArkLib's
`relOut` checks no challenge norm *precisely because the type carries it*
(`:148-150`), so the extracted verifier -- which also checks none -- is faithful
only against challenges that are short, and the hypothesis is where that says
so.

**Decisions are stated as equalities of decisions.** `relOut` and `paperRelOut`
are `Set`s of `Prop`s and `quadeval::rel_out`/`paper_rel_out` return `Bool`, so
both obligations are **iffs**. A verifier that rejected everything would satisfy
an implication in one direction, and `paperRelOut ⊆ relOut` (`:361`) means the
two are not interchangeable: `paper_rel_out` is the strictly stronger check.

**The instantiation is the one `params.rs` fixes**, and it is written out here
once: `innerRows = 1`, `messageRows = 2^10 = 1024`, `messageDigits = 8`,
`outerRows = 1`, `blocks = 2^10`, `innerDigits = 8`, `dRows = 1`,
`zDigits = 5`, `zBound = 131072`, `base = 16`, `ω = 16` (`params::OMEGA`),
`γ = 15` (`params::CHAIN_GAMMA`) and the paper's box `β = 16`
(`params::GADGET_BASE`, whose box `[-8, 7]` is `lean/QuadEval.lean`'s
`InBoxK`). Two of those collide in value and must not be confused in a proof:
`ω = 16` is the challenge `ℓ₁` bound while `β = 16` is the digit box, and
`γ = 15` is the `ℓ∞` ball. Stage 2 § F3's rule applies -- rewrite hypotheses,
never goals.
-/
import QuadEval

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi
open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme
open HachiEquiv.Balanced (ddBal bddZ)

namespace HachiEquiv.QuadEvalProtocol

/-! ## The representation layer

Four additions. Everything else comes from `Scheme.lean` through the promoted
`QuadEval.lean`. -/

/-- A `Vec<PolyVec>` read as ArkLib's per-block vector-of-vectors. The pattern
is `toDecompSpec`'s (`lean/Scheme.lean:1973`): out-of-range blocks read as the
empty vector, which `WfBlocks` rules out wherever it matters. -/
def toBlocks {blocks width : ℕ} (v : alloc.vec.Vec linalg.PolyVec) :
    PolyVec (PolyVec (Rq Φ) width) blocks :=
  fun i => toVec (k := width) (v.val.getD i.val (alloc.vec.Vec.new ring.Rq))

/-- Shape invariant of a block vector: the block count, and every block of the
declared width. -/
def WfBlocks (blocks width : ℕ) (v : alloc.vec.Vec linalg.PolyVec) : Prop :=
  v.val.length = blocks ∧ ∀ x ∈ v.val, WfVec width x

/-- The challenge vector read as ArkLib's short challenges. The `ℓ₁` bound is an
argument because `ShortChallenge` is a subtype and the extracted `PolyVec`
carries no proof; see the header. -/
def toChals (c : linalg.PolyVec)
    (hc : ∀ i : Fin (2 ^ 10), Rq.l1Norm Φ (toVec (k := 2 ^ 10) c i) ≤ 16) :
    Fin (2 ^ 10) → InnerOuter.ShortChallenge Φ 16 :=
  fun i => ⟨toVec (k := 2 ^ 10) c i, hc i⟩

/-- Relation between the extracted commitment key and ArkLib's `PublicParamsD`
(`QuadEval/Gadgets.lean:67`): the inner-outer pair through `toParams`, plus the
Hachi short-commitment matrix `D` of Eq. (16). -/
def RepParamsD (pp : quadeval.PublicParamsD)
    (sp : Hachi.PublicParamsD Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1) : Prop :=
  WfParams pp.inner ∧ WfMat 1 (2 ^ 10 * 8) pp.d_matrix ∧
    toParams pp.inner = sp.toPublicParams ∧
    toMat (rows := 1) (cols := 2 ^ 10 * 8) pp.d_matrix = sp.dMatrix

/-- Relation between the extracted input statement and ArkLib's
`QuadEvalStatement` (`QuadEval/Reduction.lean:84`). -/
def RepStmt (s : quadeval.QuadEvalStatement)
    (ss : InnerOuter.QuadEvalStatement Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1) : Prop :=
  WfVec 1 s.u ∧ WfVec (2 ^ 10) s.avec ∧ WfVec (2 ^ 10) s.bvec ∧ Wf s.y ∧
    toVec (k := 1) s.u = ss.u ∧
    toVec (k := 2 ^ 10) s.avec = ss.avec ∧
    toVec (k := 2 ^ 10) s.bvec = ss.bvec ∧
    toRq s.y = ss.y

/-- Relation between the extracted response triple and ArkLib's
`QuadEvalResponse` (`QuadEval/Reduction.lean:98`), at `zDigits = τ = 5`. -/
def RepResp (r : quadeval.QuadEvalResponse)
    (sr : InnerOuter.QuadEvalResponse Φ 1 (2 ^ 10) 8 (2 ^ 10) 8 5) : Prop :=
  WfVec (2 ^ 10 * 8) r.carrier_dec ∧ WfBlocks (2 ^ 10) (1 * 8) r.inner_dec ∧
    WfVec (2 ^ 10 * 8 * 5) r.z_dec ∧
    toVec (k := 2 ^ 10 * 8) r.carrier_dec = sr.carrierDec ∧
    toBlocks (blocks := 2 ^ 10) (width := 1 * 8) r.inner_dec = sr.innerDec ∧
    toVec (k := 2 ^ 10 * 8 * 5) r.z_dec = sr.zDec

/-! ## The three carriers -/

/-- The commitment key's constructor preserves the relation. -/
theorem PublicParamsD_new_spec (inner : commit.PublicParams) (d_matrix : linalg.PolyMatrix)
    (sp : Hachi.PublicParamsD Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (hi : toParams inner = sp.toPublicParams)
    (hd : toMat (rows := 1) (cols := 2 ^ 10 * 8) d_matrix = sp.dMatrix)
    (hWi : WfParams inner) (hWd : WfMat 1 (2 ^ 10 * 8) d_matrix) :
    quadeval.PublicParamsD.new inner d_matrix
      ⦃ out => RepParamsD out sp ⦄ := by
  sorry

/-- The input statement's constructor preserves the relation. -/
theorem QuadEvalStatement_new_spec (u avec bvec : linalg.PolyVec) (y : ring.Rq)
    (ss : InnerOuter.QuadEvalStatement Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (hu : toVec (k := 1) u = ss.u) (ha : toVec (k := 2 ^ 10) avec = ss.avec)
    (hb : toVec (k := 2 ^ 10) bvec = ss.bvec) (hy : toRq y = ss.y)
    (hWu : WfVec 1 u) (hWa : WfVec (2 ^ 10) avec) (hWb : WfVec (2 ^ 10) bvec) (hWy : Wf y) :
    quadeval.QuadEvalStatement.new u avec bvec y
      ⦃ out => RepStmt out ss ⦄ := by
  sorry

/-- The response triple's constructor preserves the relation. -/
theorem QuadEvalResponse_new_spec (carrier_dec : linalg.PolyVec)
    (inner_dec : alloc.vec.Vec linalg.PolyVec) (z_dec : linalg.PolyVec)
    (sr : InnerOuter.QuadEvalResponse Φ 1 (2 ^ 10) 8 (2 ^ 10) 8 5)
    (hc : toVec (k := 2 ^ 10 * 8) carrier_dec = sr.carrierDec)
    (hi : toBlocks (blocks := 2 ^ 10) (width := 1 * 8) inner_dec = sr.innerDec)
    (hz : toVec (k := 2 ^ 10 * 8 * 5) z_dec = sr.zDec)
    (hWc : WfVec (2 ^ 10 * 8) carrier_dec) (hWi : WfBlocks (2 ^ 10) (1 * 8) inner_dec)
    (hWz : WfVec (2 ^ 10 * 8 * 5) z_dec) :
    quadeval.QuadEvalResponse.new carrier_dec inner_dec z_dec
      ⦃ out => RepResp out sr ⦄ := by
  sorry

/-! ## The two gadget-level helpers -/

/-- `carrier_decomp` computes `carrierDecomp` at the balanced digit map: the
carrier `wᵢ = aᵀ G sᵢ` of Eq. (16), gadget-decomposed block-major
(`QuadEval/Gadgets.lean:95`).

Full width by design -- carrier coefficients are arbitrary residues, so this is
`ddBal`'s `8` digits and not the `z` side's bounded `5`. -/
theorem carrier_decomp_spec (a : linalg.PolyVec) (s : alloc.vec.Vec linalg.PolyVec)
    (hWa : WfVec (2 ^ 10) a) (hWs : WfBlocks (2 ^ 10) (2 ^ 10 * 8) s) :
    quadeval.carrier_decomp a s
      ⦃ out => WfVec (2 ^ 10 * 8) out ∧
        toVec (k := 2 ^ 10 * 8) out
          = Hachi.carrierDecomp Φ ddBal (toVec (k := 2 ^ 10) a)
              (toBlocks (blocks := 2 ^ 10) (width := 2 ^ 10 * 8) s) ⦄ := by
  sorry

/-- `carrier_commit` computes `carrierCommit`, the honest round-0 message
`v = D ŵ` (`QuadEval/Gadgets.lean:110`; `Simple.commit Φ D x` is `D *ᵥ x`). -/
theorem carrier_commit_spec (d_matrix : linalg.PolyMatrix) (a : linalg.PolyVec)
    (s : alloc.vec.Vec linalg.PolyVec)
    (hWd : WfMat 1 (2 ^ 10 * 8) d_matrix) (hWa : WfVec (2 ^ 10) a)
    (hWs : WfBlocks (2 ^ 10) (2 ^ 10 * 8) s) :
    quadeval.carrier_commit d_matrix a s
      ⦃ out => WfVec 1 out ∧
        toVec (k := 1) out
          = Hachi.carrierCommit Φ (toMat (rows := 1) (cols := 2 ^ 10 * 8) d_matrix) ddBal
              (toVec (k := 2 ^ 10) a)
              (toBlocks (blocks := 2 ^ 10) (width := 2 ^ 10 * 8) s) ⦄ := by
  sorry

/-- `j_mul` computes `jMatrix *ᵥ ẑ`, the verifier's reconstruction `z = J ẑ` of
Eq. (20) (`QuadEval/Gadgets.lean:126`).

`jMatrix` is `gadgetMatrix Φ base n zDigits` at `n = messageRows·messageDigits`
and `zDigits = τ = 5`, and the extracted function never materializes it: it goes
through `gadget::gadget_mul_z`, whose own spec (`lean/QuadEval.lean:414`) is
what this composes with. At these parameters the matrix would be ~2.5 TB. -/
theorem j_mul_spec (z_dec : linalg.PolyVec) (hWz : WfVec (2 ^ 10 * 8 * 5) z_dec) :
    quadeval.j_mul z_dec
      ⦃ out => WfVec (2 ^ 10 * 8) out ∧
        toVec (k := 2 ^ 10 * 8) out
          = Hachi.jMatrix Φ (16 : ZMod q) (2 ^ 10 * 8) 5
              *ᵥ toVec (k := 2 ^ 10 * 8 * 5) z_dec ⦄ := by
  sorry

/-! ## The honest prover -/

/-- `honest_z` computes `honestZ`, the challenge-weighted fold
`z = Σᵢ cᵢ sᵢ` of Eq. (19) (`QuadEval/Reduction.lean:515`).

The specification reads the message blocks off a `QuadEvalWitness`; the
extracted function takes them directly, so `hm` is what ties the two together.
`hc` is the challenge subtype's own bound (header). -/
theorem honest_z_spec (message : alloc.vec.Vec linalg.PolyVec) (c : linalg.PolyVec)
    (wo : InnerOuter.Opening Φ 1 (2 ^ 10) 8 (2 ^ 10) 8)
    (hc : ∀ i : Fin (2 ^ 10), Rq.l1Norm Φ (toVec (k := 2 ^ 10) c i) ≤ 16)
    (hm : toBlocks (blocks := 2 ^ 10) (width := 2 ^ 10 * 8) message = wo.message)
    (hWm : WfBlocks (2 ^ 10) (2 ^ 10 * 8) message) (hWc : WfVec (2 ^ 10) c) :
    quadeval.honest_z message c
      ⦃ out => WfVec (2 ^ 10 * 8) out ∧
        toVec (k := 2 ^ 10 * 8) out = InnerOuter.honestZ Φ wo (toChals c hc) ⦄ := by
  sorry

/-- `honest_compute_v` computes `honestComputeV`, the prover's round-0 message
`v = D ŵ` (`QuadEval/Reduction.lean:502`). -/
theorem honest_compute_v_spec (pp : quadeval.PublicParamsD) (stmt : quadeval.QuadEvalStatement)
    (message : alloc.vec.Vec linalg.PolyVec)
    (sp : Hachi.PublicParamsD Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (ss : InnerOuter.QuadEvalStatement Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (wo : InnerOuter.Opening Φ 1 (2 ^ 10) 8 (2 ^ 10) 8)
    (hpp : RepParamsD pp sp) (hst : RepStmt stmt ss)
    (hm : toBlocks (blocks := 2 ^ 10) (width := 2 ^ 10 * 8) message = wo.message)
    (hWm : WfBlocks (2 ^ 10) (2 ^ 10 * 8) message) :
    quadeval.honest_compute_v pp stmt message
      ⦃ out => WfVec 1 out ∧
        toVec (k := 1) out = InnerOuter.honestComputeV Φ sp ddBal ss wo ⦄ := by
  sorry

/-- `honest_compute_resp` computes `honestComputeResp`, the honest output witness
`(ŵ, t̂, ẑ)` of Eq. (20) (`QuadEval/Reduction.lean:531`).

The two digit maps differ in kind and that is the point: `ddBal` decomposes the
carrier at full width, `bddZ` decomposes `z` at the honest shortness bound
`τ = 5 < δ = 8`, which is what ArkLib PR #847 settled. `t̂` is a pass-through of
the witness's own inner decompositions. -/
theorem honest_compute_resp_spec (stmt : quadeval.QuadEvalStatement)
    (message inner_decomp : alloc.vec.Vec linalg.PolyVec) (c : linalg.PolyVec)
    (ss : InnerOuter.QuadEvalStatement Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (wo : InnerOuter.Opening Φ 1 (2 ^ 10) 8 (2 ^ 10) 8)
    (hc : ∀ i : Fin (2 ^ 10), Rq.l1Norm Φ (toVec (k := 2 ^ 10) c i) ≤ 16)
    (hst : RepStmt stmt ss)
    (hm : toBlocks (blocks := 2 ^ 10) (width := 2 ^ 10 * 8) message = wo.message)
    (hi : toBlocks (blocks := 2 ^ 10) (width := 1 * 8) inner_decomp = wo.innerDecomp)
    (hWm : WfBlocks (2 ^ 10) (2 ^ 10 * 8) message)
    (hWi : WfBlocks (2 ^ 10) (1 * 8) inner_decomp) (hWc : WfVec (2 ^ 10) c) :
    quadeval.honest_compute_resp stmt message inner_decomp c
      ⦃ out => RepResp out
        (InnerOuter.honestComputeResp Φ ddBal bddZ ss wo (toChals c hc)) ⦄ := by
  sorry

/-! ## The two output relations

Both are decision procedures for specification `Set`s, so both are iffs. -/

/-- `rel_out` decides `relOut`, the Eq. (20) checks with the `ℓ∞` **ball** range
condition at `γ = 15` (`QuadEval/Reduction.lean:258`). -/
theorem rel_out_spec (pp : quadeval.PublicParamsD) (stmt : quadeval.QuadEvalStatement)
    (v c : linalg.PolyVec) (resp : quadeval.QuadEvalResponse)
    (sp : Hachi.PublicParamsD Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (ss : InnerOuter.QuadEvalStatement Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (sr : InnerOuter.QuadEvalResponse Φ 1 (2 ^ 10) 8 (2 ^ 10) 8 5)
    (hc : ∀ i : Fin (2 ^ 10), Rq.l1Norm Φ (toVec (k := 2 ^ 10) c i) ≤ 16)
    (hpp : RepParamsD pp sp) (hst : RepStmt stmt ss) (hre : RepResp resp sr)
    (hWv : WfVec 1 v) (hWc : WfVec (2 ^ 10) c) :
    quadeval.rel_out pp stmt v c resp
      ⦃ out => out = true ↔
        ((ss, toVec (k := 1) v, toChals c hc), sr)
          ∈ InnerOuter.relOut (zDigits := 5) Φ sp (16 : ZMod q) 16 15 ⦄ := by
  sorry

/-- `paper_rel_out` decides `paperRelOut`, the same checks with the paper's exact
`S_β` **box** at `β = 16` (`QuadEval/Reduction.lean:335`).

Strictly the stronger of the two: `paperRelOut ⊆ relOut` holds under
`β / 2 ≤ γ` (`paperRelOut_subset_relOut`, `:361`), which here is `8 ≤ 15`. The
containment is ArkLib's theorem, not an obligation of this file; what is owed
here is that the extracted `Bool` decides the box relation. -/
theorem paper_rel_out_spec (pp : quadeval.PublicParamsD) (stmt : quadeval.QuadEvalStatement)
    (v c : linalg.PolyVec) (resp : quadeval.QuadEvalResponse)
    (sp : Hachi.PublicParamsD Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (ss : InnerOuter.QuadEvalStatement Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (sr : InnerOuter.QuadEvalResponse Φ 1 (2 ^ 10) 8 (2 ^ 10) 8 5)
    (hc : ∀ i : Fin (2 ^ 10), Rq.l1Norm Φ (toVec (k := 2 ^ 10) c i) ≤ 16)
    (hpp : RepParamsD pp sp) (hst : RepStmt stmt ss) (hre : RepResp resp sr)
    (hWv : WfVec 1 v) (hWc : WfVec (2 ^ 10) c) :
    quadeval.paper_rel_out pp stmt v c resp
      ⦃ out => out = true ↔
        ((ss, toVec (k := 1) v, toChals c hc), sr)
          ∈ InnerOuter.paperRelOut (zDigits := 5) Φ sp (16 : ZMod q) 16 16 ⦄ := by
  sorry

end HachiEquiv.QuadEvalProtocol
