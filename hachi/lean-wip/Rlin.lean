/-
Stage 5's `R^lin` adapter (chain row 3): **statements only**.

Thirteen statements. The four `usize` dimension specs (`rlin_cw`, `rlin_ct`,
`rlin_cz`, `rlin_rows`) are proved in place -- three `step`s and a
`scalar_tac` each; the other nine are `sorry` stubs for the prover. They
cover the adapter that turns
QuadEval's five differently-shaped Eq. (20) checks into the single unstructured
linear claim `M·ζ = y` the ring-switching layer consumes: the dimension
abbrevs, the two reshapes, the witness maps, the c5 block matrix, the
transposed gadget application every block goes through, and the assembly
itself. `quadeval::PolyEvalStatement`/`to_quad_eval_statement` — chain row 1,
the polynomial-level bridge — ride along here because they are the same seam
read from the other end.

# What a reader must know before believing `rlin_stmt_spec`

`benches/genesis` holds the **reshaped** c4 block for this item, by decision
(NOTES.md § "Decision: the `R^lin` adapter's genesis holds the reshaped form").
The specification writes c4's `ẑ` block as `(matMul G_{2^m} J).transpose *ᵥ a`;
that product is `1024 × 40960` `Rq` = 320 GiB at the pinned parameters where
the answer is a 320 MiB vector, so there is no width at which the naive form
runs. **The statement below is still against the specification's form** —
`rlinStmt` itself — because that is the one rule: the right-hand side is the
ArkLib definition, and the proof is what has to bridge the associativity. That
bridge is `Matrix.transpose_mul`/`mulVec_mulVec` shaped and is the interesting
part of the obligation, not a footnote.

# Conventions

Every dimension is an argument in the *Rust*. Nine of the thirteen statements
are correspondingly generic; the other four — `stack`, `unstack`,
`to_quad_eval_statement`, `rlin_stmt` — are **instantiated at the pinned
dimensions**, because the carrier relations they consume
(`RepParamsD`/`RepStmt`/`RepResp`, in the promoted `QuadEvalProtocol.lean`) are
themselves instantiated. Which convention a statement can use is decided by the
reps it touches, not by preference. (An earlier version of this paragraph
claimed all thirteen were generic, which a reviewer reading only the header
would have believed.) The
`≤ Usize.max` hypotheses on the dimension specs are earned: each of those
functions forms a checked `usize` product, and a caller who cannot supply the
bound could not hold the vector it sizes either — "implied by representability,
invisible to the `Vec` model", the phrasing `lean/ZeroCheck.lean` settled on.

It imports only promoted files (`QuadEvalProtocol` for the three QuadEval
carriers' relations, `ZeroCheck` for `RepRlin`), so it needs **no `LEAN_PATH`
detour**:

```sh
cd hachi
lake build
lake env lean lean-wip/Rlin.lean
```
-/
import QuadEvalProtocol
import ZeroCheck

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.Rlin

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme
open HachiEquiv.QuadEvalProtocol HachiEquiv.ZeroCheck

/-! ## The transposed gadget application -/

/-- `gadget_transpose_mul` computes `Gᵗ·a`, the transposed gadget matrix
applied to a vector — the operation c3, c4 and c5 of `rlinStmt` all go through.

`gadgetEntry` is `base^(j % digits)` when `j / digits = i` and `0` otherwise
(`Gadget/Core.lean:391`), so the transpose has one nonzero per row and the
extracted loop is a scale with no sum. Materializing `G` is what this avoids:
`G_{2^r}` alone is `1024 × 8192` `Rq` = 64 GiB. -/
theorem gadget_transpose_mul_spec {rows digits : ℕ} (r d : Std.Usize)
    (a : linalg.PolyVec) (ha : WfVec rows a)
    (hr : r.val = rows) (hd : d.val = digits)
    (hfit : rows * digits ≤ Usize.max) :
    gadget.gadget_transpose_mul r d a
      ⦃ out => WfVec (rows * digits) out ∧
        toVec (k := rows * digits) out
          = (gadgetMatrix Φ (16 : ZMod q) rows digits).transpose *ᵥ toVec (k := rows) a ⦄ := by
  sorry

/-! ## The `rlinCols` layout -/

/-- `rlin_cw` computes `rlinCW = 2^r · messageDigits`, the `ŵ` column block
(`RingSwitch/Rlin.lean:84`). `blocks` is `2^r` already expanded, so no power is
formed; the bound is the checked product's. -/
theorem rlin_cw_spec {blocks messageDigits : ℕ} (b md : Std.Usize)
    (hb : b.val = blocks) (hmd : md.val = messageDigits)
    (hfit : blocks * messageDigits ≤ Usize.max) :
    quadeval.rlin_cw b md ⦃ out => out.val = blocks * messageDigits ⦄ := by
  rw [quadeval.rlin_cw]
  step as ⟨p, hp⟩
  scalar_tac

/-- `rlin_ct` computes `rlinCT = 2^r · (innerRows · innerDigits)` (`:86`). -/
theorem rlin_ct_spec {blocks innerRows innerDigits : ℕ} (b ir idg : Std.Usize)
    (hb : b.val = blocks) (hir : ir.val = innerRows) (hidg : idg.val = innerDigits)
    (hinner : innerRows * innerDigits ≤ Usize.max)
    (hfit : blocks * (innerRows * innerDigits) ≤ Usize.max) :
    quadeval.rlin_ct b ir idg
      ⦃ out => out.val = blocks * (innerRows * innerDigits) ⦄ := by
  rw [quadeval.rlin_ct]
  have h1 : ir.val * idg.val ≤ Usize.max := by rw [hir, hidg]; exact hinner
  step as ⟨i, hi⟩
  have hiv : i.val = innerRows * innerDigits := by rw [hi, hir, hidg]
  have h2 : b.val * i.val ≤ Usize.max := by rw [hb, hiv]; exact hfit
  step as ⟨p, hp⟩
  scalar_tac

/-- `rlin_cz` computes `rlinCZ = 2^m · messageDigits · zDigits` (`:88`). -/
theorem rlin_cz_spec {messageRows messageDigits zDigits : ℕ} (mr md zd : Std.Usize)
    (hmr : mr.val = messageRows) (hmd : md.val = messageDigits) (hzd : zd.val = zDigits)
    (hinner : messageRows * messageDigits ≤ Usize.max)
    (hfit : messageRows * messageDigits * zDigits ≤ Usize.max) :
    quadeval.rlin_cz mr md zd
      ⦃ out => out.val = messageRows * messageDigits * zDigits ⦄ := by
  rw [quadeval.rlin_cz]
  have h1 : mr.val * md.val ≤ Usize.max := by rw [hmr, hmd]; exact hinner
  step as ⟨i, hi⟩
  have hiv : i.val = messageRows * messageDigits := by rw [hi, hmr, hmd]
  have h2 : i.val * zd.val ≤ Usize.max := by rw [hiv, hzd]; exact hfit
  step as ⟨p, hp⟩
  scalar_tac

/-- `rlin_cols` computes `rlinCols` (`:75`), in the specification's own
parenthesisation — which that definition fixes deliberately ("Associativity
fixed once, here"), so the statement mirrors it rather than normalising.

The four inner bounds are the fail points of the three width calls this
function makes (`rlin_ct`'s `ir * idg`, `rlin_cz`'s `mr * md` and its outer
product, `rlin_ct`'s outer product), each a checked `usize` multiplication that
the final sum's bound `hfit` does not imply — at `blocks = 0` the sum is `0`
while `ir * idg` can still overflow. -/
theorem rlin_cols_spec {blocks messageRows messageDigits innerRows innerDigits zDigits : ℕ}
    (b mr md ir idg zd : Std.Usize)
    (hb : b.val = blocks) (hmr : mr.val = messageRows) (hmd : md.val = messageDigits)
    (hir : ir.val = innerRows) (hidg : idg.val = innerDigits) (hzd : zd.val = zDigits)
    (hinnerT : innerRows * innerDigits ≤ Usize.max)
    (hinnerZ : messageRows * messageDigits ≤ Usize.max)
    (hct : blocks * (innerRows * innerDigits) ≤ Usize.max)
    (hcz : messageRows * messageDigits * zDigits ≤ Usize.max)
    (hfit : blocks * messageDigits
      + (blocks * (innerRows * innerDigits) + messageRows * messageDigits * zDigits)
      ≤ Usize.max) :
    quadeval.rlin_cols b mr md ir idg zd
      ⦃ out => out.val = blocks * messageDigits
        + (blocks * (innerRows * innerDigits) + messageRows * messageDigits * zDigits) ⦄ := by
  sorry

/-- `rlin_rows` computes `rlinRows = dRows + (outerRows + (1 + (1 + innerRows)))`
(`:80`), the `c1 ++ (c2 ++ (c3 ++ (c4 ++ c5)))` row count. -/
theorem rlin_rows_spec {innerRows outerRows dRows : ℕ} (ir or dr : Std.Usize)
    (hir : ir.val = innerRows) (hor : or.val = outerRows) (hdr : dr.val = dRows)
    (hfit : dRows + (outerRows + (1 + (1 + innerRows))) ≤ Usize.max) :
    quadeval.rlin_rows ir or dr
      ⦃ out => out.val = dRows + (outerRows + (1 + (1 + innerRows))) ⦄ := by
  rw [quadeval.rlin_rows]
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  step as ⟨p, hp⟩
  scalar_tac

/-! ## The two reshapes -/

/-- `unflatten` inverts `flattenBlocks` (`RingSwitch/Rlin.lean:113`): entry `w`
of block `i` is entry `width·i + w` of the input.

`0 < width` is not decoration. At `width = 0` the hypothesis `WfVec (blocks *
width) v` forces `v` empty, the extracted loop's guard `base < total` never
fires, and `out` comes back empty — while the postcondition asserts
`WfBlocks blocks 0 out`, i.e. `out.val.length = blocks`, which is satisfiable
at `blocks = 5`. Nothing else in the hypotheses determines `blocks`, which is
what lets the counterexample in. Found by cross-review. -/
theorem unflatten_spec {blocks width : ℕ} (v : linalg.PolyVec) (w : Std.Usize)
    (hv : WfVec (blocks * width) v) (hw : w.val = width) (hpos : 0 < width) :
    quadeval.unflatten v w
      ⦃ out => WfBlocks blocks width out ∧
        toBlocks (blocks := blocks) (width := width) out
          = InnerOuter.unflatten (P := Rq Φ) (toVec (k := blocks * width) v) ⦄ := by
  sorry

/-- `tensor_g_matrix` computes `tensorGMatrix`, the c5 block `(cᵀ ⊗ G_k)`
(`:132`). Materialized — `relRlin` applies it — but its entries come from the
gadget's structure, never from a materialized `G`. -/
theorem tensor_g_matrix_spec {k digits blocks : ℕ} (kk dd : Std.Usize) (c : linalg.PolyVec)
    (hk : kk.val = k) (hd : dd.val = digits) (hc : WfVec blocks c)
    (hfit : blocks * (k * digits) ≤ Usize.max) :
    quadeval.tensor_g_matrix kk dd c
      ⦃ out => WfMat k (blocks * (k * digits)) out ∧
        toMat (rows := k) (cols := blocks * (k * digits)) out
          = InnerOuter.tensorGMatrix Φ (16 : ZMod q) k digits blocks (toVec (k := blocks) c) ⦄ := by
  sorry

/-! ## The witness maps -/

/-- `stack` computes `stack`, the adapter's witness map
`ζ = ŵ ++ (flatten t̂ ++ ẑ)` (`:158`). -/
theorem stack_spec (resp : quadeval.QuadEvalResponse)
    (sr : InnerOuter.QuadEvalResponse Φ 1 (2 ^ 10) 8 (2 ^ 10) 8 5)
    (hre : RepResp resp sr) :
    quadeval.stack resp
      ⦃ out => WfVec (InnerOuter.rlinCols 1 8 8 5 10 10) out ∧
        toVec (k := InnerOuter.rlinCols 1 8 8 5 10 10) out = InnerOuter.stack Φ sr ⦄ := by
  sorry

/-- `unstack` computes `unstack` (`:166`), inverse to `stack`. The three widths
are arguments because nothing in `ζ` records where the boundaries are — the
specification recovers them from type indices, which erase. -/
theorem unstack_spec (zeta : linalg.PolyVec) (cw ct innerWidth : Std.Usize)
    (hz : WfVec (InnerOuter.rlinCols 1 8 8 5 10 10) zeta)
    (hcw : cw.val = InnerOuter.rlinCW 8 10)
    (hct : ct.val = InnerOuter.rlinCT 1 8 10)
    (hiw : innerWidth.val = 1 * 8) :
    quadeval.unstack zeta cw ct innerWidth
      ⦃ out => RepResp out
        (InnerOuter.unstack Φ (toVec (k := InnerOuter.rlinCols 1 8 8 5 10 10) zeta)) ⦄ := by
  sorry

/-! ## The polynomial-level bridge (chain row 1) -/

/-- Relation between the extracted polynomial-level statement and ArkLib's
`PolyEvalStatement` (`QuadEval/Bridge.lean:108`). The point travels pre-split as
`(xl, xh)`, which is the specification's own choice — it "avoids `take`/`drop`
casts" — and the halves are `Vector`s there against `PolyVec`s here. -/
def RepPolyEval {innerRows messageDigits outerRows innerDigits dRows m r : ℕ}
    (s : quadeval.PolyEvalStatement)
    (ps : InnerOuter.PolyEvalStatement Φ innerRows messageDigits outerRows innerDigits dRows m r) :
    Prop :=
  WfVec outerRows s.u ∧ WfVec r s.xl ∧ WfVec m s.xh ∧ Wf s.y ∧
    toVec (k := outerRows) s.u = ps.u ∧
    Vector.ofFn (toVec (k := r) s.xl) = ps.xl ∧
    Vector.ofFn (toVec (k := m) s.xh) = ps.xh ∧
    toRq s.y = ps.y

/-- The polynomial-level statement's constructor preserves the relation. -/
theorem PolyEvalStatement_new_spec
    {innerRows messageDigits outerRows innerDigits dRows m r : ℕ}
    (u xl xh : linalg.PolyVec) (y : ring.Rq)
    (ps : InnerOuter.PolyEvalStatement Φ innerRows messageDigits outerRows innerDigits dRows m r)
    (hu : toVec (k := outerRows) u = ps.u)
    (hxl : Vector.ofFn (toVec (k := r) xl) = ps.xl)
    (hxh : Vector.ofFn (toVec (k := m) xh) = ps.xh)
    (hy : toRq y = ps.y)
    (hWu : WfVec outerRows u) (hWxl : WfVec r xl) (hWxh : WfVec m xh) (hWy : Wf y) :
    quadeval.PolyEvalStatement.new u xl xh y
      ⦃ out => RepPolyEval out ps ⦄ := by
  sorry

/-- `to_quad_eval_statement` computes `toQuadEvalStatement`
(`QuadEval/Bridge.lean:124`): the Eq. (12) bases are the monomial tensor bases
of the two point halves.

**The halves cross**, and that is the row's whole content: `avec := mb(xh)` (the
*high* half, indexing columns) and `bvec := mb(xl)` (the *low* half, indexing
rows). At this crate's parameters `ML_VARS_LOW = ML_VARS_HIGH = 10`, so a swap
typechecks, runs, and computes the transpose — which is why the semantics test
uses unequal toy widths and why this statement pins the two separately. -/
theorem to_quad_eval_statement_spec (s : quadeval.PolyEvalStatement)
    (ps : InnerOuter.PolyEvalStatement Φ 1 8 1 8 1 10 10)
    (hs : RepPolyEval s ps) :
    quadeval.to_quad_eval_statement s
      ⦃ out => RepStmt out (InnerOuter.toQuadEvalStatement Φ ps) ⦄ := by
  sorry

/-! ## The assembly -/

/-- `rlin_stmt` computes `rlinStmt`, the Eq. (20) block matrix and right-hand
side (`RingSwitch/Rlin.lean:205`).

**The obligation this file exists for**, and the one whose proof is not
bookkeeping. The right-hand side is the specification's `rlinStmt`, whose c4
block is written `(matMul G_{2^m} J).transpose *ᵥ a`; the extracted code
computes `Jᵀ(Gᵀa)` instead, because the product is 320 GiB at these
parameters (NOTES.md § "Decision: the `R^lin` adapter's genesis holds the
reshaped form"). Proving them equal is an associativity argument, and the route is **not** the
one first recorded here. `ArkLib.Lattices.matMul` is standalone —
`fun i k => dot (M i) (fun j => N j k)` (`Data/Lattices/Vectors.lean:93`),
deliberately so "it stays computable" — **not** Mathlib's `Matrix.mul`, so
`Matrix.transpose_mul` does not apply, and no
`(matMul M N)ᵀ = matMul Nᵀ Mᵀ` exists anywhere in ArkLib. What does exist is
`matVecMul_matMul : matMul M N *ᵥ v = M *ᵥ (N *ᵥ v)` (`:184`), for the
*untransposed* product, and `splitForm_transpose` (`:241`).

So the bridge is an index computation, not a named rewrite: `PolyMatrix` *is* a
`Matrix`, so `Matrix.transpose_apply` gives `(matMul G J)ᵀ i k = matMul G J k i`,
and from there `matMul_apply`, `dot_eq_sum`, `Finset.sum_comm` and the gadget's
single-nonzero column structure. Recorded because the first version of this
note would have sent a prover after two lemmas that do not fire. The freeze is faithful only if this theorem holds,
and no benchmark or digest can substitute for it. -/
theorem rlin_stmt_spec
    (pp : quadeval.PublicParamsD) (stmt : quadeval.QuadEvalStatement)
    (v c : linalg.PolyVec) (gamma : Std.U64) (b mr md ir idg zd : Std.Usize)
    (sp : Hachi.PublicParamsD Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (ss : InnerOuter.QuadEvalStatement Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (hpp : RepParamsD pp sp) (hst : RepStmt stmt ss)
    (hv : WfVec 1 v) (hc : WfVec (2 ^ 10) c)
    (hcn : ∀ i : Fin (2 ^ 10), Rq.l1Norm Φ (toVec (k := 2 ^ 10) c i) ≤ 16)
    (hb : b.val = 2 ^ 10) (hmr : mr.val = 2 ^ 10) (hmd : md.val = 8)
    (hir : ir.val = 1) (hidg : idg.val = 8) (hzd : zd.val = 5) :
    quadeval.rlin_stmt pp stmt v c gamma b mr md ir idg zd
      ⦃ out => RepRlin
        (n := InnerOuter.rlinRows 1 1 1) (μ := InnerOuter.rlinCols 1 8 8 5 10 10) out
        (InnerOuter.rlinStmt (zDigits := 5) Φ sp (16 : ZMod q) 16 gamma.val
          (ss, toVec (k := 1) v, toChals c hcn)) ⦄ := by
  sorry

end HachiEquiv.Rlin
