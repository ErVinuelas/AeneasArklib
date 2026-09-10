/-
Stage 5's `R^lin` adapter (chain row 3), **proved**.

Thirteen headline specs, all audited by `Check.lean` § 4. The four `usize`
dimension specs (`rlin_cw`, `rlin_ct`, `rlin_cz`, `rlin_rows`) were proved in
place when the file was stated; the other nine were discharged by Aristotle
session `4d70f965` (2026-09-10, nine obligations to zero, every headline
statement byte-identical to the submitted baseline -- the file gained
forty-one helper and loop lemmas and no hypothesis). They cover the adapter
that turns
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

It imports `QuadEvalProtocol` for the three QuadEval carriers' relations and
`ZeroCheck` for `RepRlin`. Promoted from `lean-wip/` on 2026-09-10; the
proofs here are re-checked by every `make build`, and a `sorry` in this file
is a build failure.
-/
import QuadEvalProtocol
import ZeroCheck
-- `EvalSplit` is a promoted file too (`lean/EvalSplit.lean`); the polynomial-level
-- bridge below is stated about its `monomial_basis` reading, so its spec is needed
-- here. It adds no `LEAN_PATH` detour: it is part of the built library.
import EvalSplit

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

/-- The ring element `gadget_transpose_mul` writes at the flat output index `t`:
the single nonzero of column `t` of `G`, times the matching entry of `a`. -/
def gtmVal (digits : ℕ) (a : linalg.PolyVec) (t : ℕ) : Rq Φ :=
  Rq.constRq Φ ((16 : ZMod q) ^ (t % digits))
    * toRq (a.val.getD (t / digits) (alloc.vec.Vec.new cpoly.field.Fp))

/-- The inner loop of `gadget_transpose_mul`: the `digits` slots of block `i` are
filled with `a i` scaled by the successive powers of the base. -/
theorem gadget_transpose_mul_inner_loop_spec {rows digits : ℕ} (d : Std.Usize)
    (a : linalg.PolyVec) (out : alloc.vec.Vec ring.Rq) (i e : Std.Usize)
    (ha : WfVec rows a) (hd : d.val = digits) (hi : i.val < rows)
    (hfit : rows * digits ≤ Usize.max)
    (he : e.val ≤ digits) (hlen : out.val.length = digits * i.val + e.val)
    (hwf : ∀ y ∈ out.val, Wf y)
    (hval : ∀ t, t < digits * i.val + e.val →
      toRq (out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = gtmVal digits a t) :
    gadget.gadget_transpose_mul_loop0_loop0 d a out i e
      ⦃ z => z.val.length = digits * i.val + digits ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ t, t < digits * i.val + digits →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = gtmVal digits a t ⦄ := by
  have hfit' : digits * rows ≤ Usize.max := by rw [Nat.mul_comm]; exact hfit
  have hblock : digits * i.val + digits ≤ digits * rows := by
    have : digits * (i.val + 1) ≤ digits * rows := Nat.mul_le_mul_left _ hi
    omega
  rw [gadget.gadget_transpose_mul_loop0_loop0]
  apply loop.spec_decr_nat (fun s => d.val - s.2.val)
    (fun s => s.2.val ≤ digits ∧ s.1.val.length = digits * i.val + s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      ∀ t, t < digits * i.val + s.2.val →
        toRq (s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = gtmVal digits a t)
  · rintro ⟨o1, e1⟩ ⟨he1, hlen1, hwf1, hval1⟩
    dsimp only at he1 hlen1 hwf1 hval1
    simp only [gadget.gadget_transpose_mul_loop0_loop0.body]
    by_cases hlt : e1 < d
    · rw [if_pos hlt]
      have he1lt : e1.val < digits := by rw [← hd]; scalar_tac
      have hia : i.val < a.val.length := by rw [ha.1]; exact hi
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact ha.2 _ (List.getElem_mem hia)
      step with HachiEquiv.Scheme.base_pow_spec e1 as ⟨f, hRf, hf⟩
      step with RqBridge.scalar_mul_spec r f hWr hRf as ⟨r1, hWr1, hr1⟩
      have hcap : o1.val.length < Usize.max := by rw [hlen1]; omega
      step as ⟨o2, ho2⟩
      step as ⟨e2, he2⟩
      have hentry : toRq r1 = gtmVal digits a (digits * i.val + e1.val) := by
        have hdiv : (digits * i.val + e1.val) / digits = i.val := by
          rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega : 0 < digits),
            Nat.div_eq_of_lt he1lt, Nat.zero_add]
        have hmod : (digits * i.val + e1.val) % digits = e1.val := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt he1lt]
        rw [gtmVal, hdiv, hmod, hr1, hf, hr, List.getD_eq_getElem _ _ hia]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, he2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [he2] at ht
        rcases Nat.lt_or_ge t (digits * i.val + e1.val) with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = o1.val.length := by rw [hlen1]; omega
          rw [hteq, ho2, getD_append_eq, hentry, hlen1]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : e1.val = digits := by rw [← hd]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · exact ⟨he, hlen, hwf, hval⟩

/-- The outer loop of `gadget_transpose_mul`: the first `i` blocks are written. -/
theorem gadget_transpose_mul_outer_loop_spec {rows digits : ℕ} (r d : Std.Usize)
    (a : linalg.PolyVec) (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (ha : WfVec rows a) (hr : r.val = rows) (hd : d.val = digits)
    (hfit : rows * digits ≤ Usize.max)
    (hi : i.val ≤ rows) (hlen : out.val.length = digits * i.val)
    (hwf : ∀ y ∈ out.val, Wf y)
    (hval : ∀ t, t < digits * i.val →
      toRq (out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = gtmVal digits a t) :
    gadget.gadget_transpose_mul_loop0 r d a out i
      ⦃ z => z.val.length = rows * digits ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ t, t < rows * digits →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = gtmVal digits a t ⦄ := by
  rw [gadget.gadget_transpose_mul_loop0]
  apply loop.spec_decr_nat (fun s => r.val - s.2.val)
    (fun s => s.2.val ≤ rows ∧ s.1.val.length = digits * s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      ∀ t, t < digits * s.2.val →
        toRq (s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = gtmVal digits a t)
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [gadget.gadget_transpose_mul_loop0.body]
    by_cases hlt : i1 < r
    · rw [if_pos hlt]
      have hi1lt : i1.val < rows := by rw [← hr]; scalar_tac
      step with gadget_transpose_mul_inner_loop_spec d a o1 i1 0#usize ha hd hi1lt hfit
        (by simp) (by simp [hlen1]) hwf1 (by simpa using hval1) as ⟨o2, hlen2, hwf2, hval2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [hlen2, hi2]; ring_nf
      · exact hwf2
      · intro t ht
        rw [hi2] at ht
        exact hval2 t (by omega)
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = rows := by rw [← hr]; scalar_tac
      refine ⟨by rw [hlen1, heq, Nat.mul_comm], hwf1, ?_⟩
      intro t ht
      exact hval1 t (by rw [heq, Nat.mul_comm]; exact ht)
  · exact ⟨hi, hlen, hwf, hval⟩

/-- The entry `gtmVal` is the entry of `Gᵀ·a`: column `j` of `G` has its single
nonzero in row `j / digits`. -/
theorem gtmVal_eq_transpose_apply {rows digits : ℕ} (a : linalg.PolyVec)
    (j : Fin (rows * digits)) :
    gtmVal digits a j.val
      = ((gadgetMatrix Φ (16 : ZMod q) rows digits).transpose *ᵥ toVec (k := rows) a) j := by
  have hdpos : 0 < digits := by
    rcases Nat.eq_zero_or_pos digits with h | h
    · exact absurd j.isLt (by simp [h])
    · exact h
  have hdivlt : j.val / digits < rows :=
    Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le j.isLt (le_of_eq (Nat.mul_comm rows digits)))
  rw [matVecMul_apply, dot_eq_sum]
  rw [Finset.sum_eq_single (⟨j.val / digits, hdivlt⟩ : Fin rows)]
  · simp only [Matrix.transpose_apply, gadgetMatrix, gadgetEntry, if_true, gtmVal, toVec]
  · intro b _ hb
    have hne : ¬ (j.val / digits = b.val) := by
      intro h; exact hb (Fin.ext h.symm)
    simp only [Matrix.transpose_apply, gadgetMatrix, gadgetEntry, if_neg hne, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `gadget_transpose_mul` entrywise, in the `gtmVal` vocabulary: the form the
`c5` row loop consumes, where the flat index is an `ℕ` rather than a `Fin`. -/
theorem gadget_transpose_mul_entry_spec {rows digits : ℕ} (r d : Std.Usize)
    (a : linalg.PolyVec) (ha : WfVec rows a)
    (hr : r.val = rows) (hd : d.val = digits)
    (hfit : rows * digits ≤ Usize.max) :
    gadget.gadget_transpose_mul r d a
      ⦃ out => WfVec (rows * digits) out ∧
        ∀ t, t < rows * digits →
          toRq (out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = gtmVal digits a t ⦄ := by
  rw [gadget.gadget_transpose_mul]
  step with gadget_transpose_mul_outer_loop_spec r d a (alloc.vec.Vec.new ring.Rq) 0#usize
    ha hr hd hfit (by simp) (by simp) (by intro y hy; simp at hy) (by intro t ht; simp at ht)
    as ⟨z, hzlen, hzwf, hzval⟩
  simp only [linalg.PolyVec.new, WP.spec_ok]
  exact ⟨⟨hzlen, hzwf⟩, hzval⟩

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
  rw [gadget.gadget_transpose_mul]
  step with gadget_transpose_mul_outer_loop_spec r d a (alloc.vec.Vec.new ring.Rq) 0#usize
    ha hr hd hfit (by simp) (by simp) (by intro y hy; simp at hy) (by intro t ht; simp at ht)
    as ⟨z, hzlen, hzwf, hzval⟩
  simp only [linalg.PolyVec.new, WP.spec_ok]
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext j
  simp only [toVec]
  rw [hzval j.val j.isLt]
  exact gtmVal_eq_transpose_apply a j


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
  rw [quadeval.rlin_cols]
  have hcw : blocks * messageDigits ≤ Usize.max := by omega
  step with rlin_cw_spec b md hb hmd hcw as ⟨i, hi⟩
  step with rlin_ct_spec b ir idg hb hir hidg hinnerT hct as ⟨i1, hi1⟩
  step with rlin_cz_spec mr md zd hmr hmd hzd hinnerZ hcz as ⟨i2, hi2⟩
  have h3 : i1.val + i2.val ≤ Usize.max := by rw [hi1, hi2]; omega
  step as ⟨i3, hi3⟩
  have h4 : i.val + i3.val ≤ Usize.max := by rw [hi, hi3, hi1, hi2]; exact hfit
  step as ⟨p, hp⟩
  scalar_tac

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

/-- The inner loop of `unflatten`: block starting at `base` is copied out of `v`. -/
theorem unflatten_inner_loop_spec {blocks width : ℕ} (v : linalg.PolyVec) (w base : Std.Usize)
    (block : alloc.vec.Vec ring.Rq) (wi : Std.Usize)
    (hv : WfVec (blocks * width) v) (hw : w.val = width)
    (hbase : base.val + width ≤ blocks * width)
    (hwi : wi.val ≤ width) (hlen : block.val.length = wi.val)
    (hwf : ∀ y ∈ block.val, Wf y)
    (hval : ∀ t, t < wi.val →
      toRq (block.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (v.val.getD (base.val + t) (alloc.vec.Vec.new cpoly.field.Fp))) :
    quadeval.unflatten_loop0_loop0 v w base block wi
      ⦃ z => z.val.length = width ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ t, t < width →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = toRq (v.val.getD (base.val + t) (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  have hvlen : v.val.length = blocks * width := hv.1
  have hcap : blocks * width ≤ Usize.max := by rw [← hvlen]; exact v.property
  rw [quadeval.unflatten_loop0_loop0]
  apply loop.spec_decr_nat (fun s => w.val - s.2.val)
    (fun s => s.2.val ≤ width ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ t, t < s.2.val →
        toRq (s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq (v.val.getD (base.val + t) (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨b1, w1⟩ ⟨hw1, hlen1, hwf1, hval1⟩
    dsimp only at hw1 hlen1 hwf1 hval1
    simp only [quadeval.unflatten_loop0_loop0.body]
    by_cases hlt : w1 < w
    · rw [if_pos hlt]
      have hw1lt : w1.val < width := by rw [← hw]; scalar_tac
      have hsum : base.val + w1.val ≤ Usize.max := by omega
      step as ⟨i, hi⟩
      have hiv : i.val = base.val + w1.val := by rw [hi]
      have hidx : i.val < v.val.length := by rw [hvlen, hiv]; omega
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hv.2 _ (List.getElem_mem hidx)
      step with RqBridge.copy_spec r hWr as ⟨r1, hWr1, hr1⟩
      have hcap2 : b1.val.length < Usize.max := by rw [hlen1]; omega
      step as ⟨b2, hb2⟩
      step as ⟨w2, hw2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [hb2, hw2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
      · intro y hy
        rw [hb2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [hw2] at ht
        rcases Nat.lt_or_ge t w1.val with htlt | htge
        · rw [hb2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = b1.val.length := by rw [hlen1]; omega
          rw [hteq, hb2, getD_append_eq, hr1, hr, hlen1, ← hiv,
            List.getD_eq_getElem _ _ hidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : w1.val = width := by rw [← hw]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · exact ⟨hwi, hlen, hwf, hval⟩

/-- The outer loop of `unflatten`: the blocks below `base` are already written. -/
theorem unflatten_outer_loop_spec {blocks width : ℕ} (v : linalg.PolyVec) (w total : Std.Usize)
    (out : alloc.vec.Vec linalg.PolyVec) (base : Std.Usize)
    (hv : WfVec (blocks * width) v) (hw : w.val = width) (hpos : 0 < width)
    (htotal : total.val = blocks * width)
    (hbase : base.val = width * out.val.length) (hnb : out.val.length ≤ blocks)
    (hwf : ∀ x ∈ out.val, WfVec width x)
    (hval : ∀ n, n < out.val.length → ∀ t, t < width →
      toRq ((out.val.getD n (alloc.vec.Vec.new ring.Rq)).val.getD t
          (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (v.val.getD (width * n + t) (alloc.vec.Vec.new cpoly.field.Fp))) :
    quadeval.unflatten_loop0 v w total out base
      ⦃ z => z.val.length = blocks ∧ (∀ x ∈ z.val, WfVec width x) ∧
        ∀ n, n < blocks → ∀ t, t < width →
          toRq ((z.val.getD n (alloc.vec.Vec.new ring.Rq)).val.getD t
              (alloc.vec.Vec.new cpoly.field.Fp))
            = toRq (v.val.getD (width * n + t) (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  have hvlen : v.val.length = blocks * width := hv.1
  have hcap : blocks * width ≤ Usize.max := by rw [← hvlen]; exact v.property
  rw [quadeval.unflatten_loop0]
  apply loop.spec_decr_nat (fun s => total.val - s.2.val)
    (fun s => s.2.val = width * s.1.val.length ∧ s.1.val.length ≤ blocks ∧
      (∀ x ∈ s.1.val, WfVec width x) ∧
      ∀ n, n < s.1.val.length → ∀ t, t < width →
        toRq ((s.1.val.getD n (alloc.vec.Vec.new ring.Rq)).val.getD t
            (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq (v.val.getD (width * n + t) (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, base1⟩ ⟨hbase1, hnb1, hwf1, hval1⟩
    dsimp only at hbase1 hnb1 hwf1 hval1
    simp only [quadeval.unflatten_loop0.body]
    by_cases hlt : base1 < total
    · rw [if_pos hlt]
      have hlen1lt : o1.val.length < blocks := by
        by_contra hcon
        have : o1.val.length = blocks := by omega
        have : total.val ≤ base1.val := by rw [htotal, hbase1, this, Nat.mul_comm]
        scalar_tac
      have hbfit : base1.val + width ≤ blocks * width := by
        rw [hbase1]
        calc width * o1.val.length + width = width * (o1.val.length + 1) := by ring
          _ ≤ width * blocks := Nat.mul_le_mul_left _ hlen1lt
          _ = blocks * width := Nat.mul_comm _ _
      step with unflatten_inner_loop_spec v w base1 (alloc.vec.Vec.new ring.Rq) 0#usize
        hv hw hbfit (by simp) (by simp) (by intro y hy; simp at hy)
        (by intro t ht; simp at ht) as ⟨blk, hblen, hbwf, hbval⟩
      simp only [linalg.PolyVec.new]
      have hcap2 : o1.val.length < Usize.max := by
        have : blocks ≤ blocks * width := Nat.le_mul_of_pos_right _ hpos
        omega
      step as ⟨o2, ho2⟩
      have hsum : base1.val + w.val ≤ Usize.max := by rw [hw]; omega
      step as ⟨base2, hbase2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hbase2, ho2, List.length_append, hbase1, hw]
        simp only [List.length_cons, List.length_nil]
        ring
      · rw [ho2, List.length_append]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro x hx
        rw [ho2] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hwf1 x h
        · rw [List.mem_singleton.mp h]; exact ⟨hblen, hbwf⟩
      · intro n hn t ht
        rw [ho2, List.length_append] at hn
        simp only [List.length_cons, List.length_nil] at hn
        rcases Nat.lt_or_ge n o1.val.length with hnlt | hnge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 n hnlt t ht
        · have hneq : n = o1.val.length := by omega
          rw [hneq, ho2, getD_append_eq, hbval t ht, hbase1]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : o1.val.length = blocks := by
        have hge : total.val ≤ base1.val := by scalar_tac
        rw [htotal, hbase1] at hge
        by_contra hcon
        have hcon2 : o1.val.length + 1 ≤ blocks := by omega
        have hmul := Nat.mul_le_mul_left width hcon2
        have hexp : width * (o1.val.length + 1) = width * o1.val.length + width := by ring
        have hcomm : blocks * width = width * blocks := Nat.mul_comm _ _
        omega
      exact ⟨heq, hwf1, by rw [← heq]; exact hval1⟩
  · exact ⟨hbase, hnb, hwf, hval⟩

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
  rw [quadeval.unflatten]
  simp only [linalg.PolyVec.len]
  apply spec_mono (unflatten_outer_loop_spec v w (alloc.vec.Vec.len v)
    (alloc.vec.Vec.new linalg.PolyVec) 0#usize hv hw hpos (by simpa using hv.1)
    (by simp) (by simp) (by intro x hx; simp at hx) (by intro n hn; simp at hn))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i j
  have hfp : ((finProdFinEquiv (i, j) : Fin (blocks * width)) : ℕ) = j.val + width * i.val := rfl
  simp only [toBlocks, toVec, InnerOuter.unflatten, hfp]
  rw [hzval i.val i.isLt j.val j.isLt, Nat.add_comm]

/-- The entry `tensor_g_matrix` writes in row `p` at the flat column index `t`:
the block index is `t / (k · digits)` and the gadget column is `t % (k · digits)`. -/
def tgmVal (k digits : ℕ) (c : linalg.PolyVec) (p t : ℕ) : Rq Φ :=
  if (t % (k * digits)) / digits = p then
    Rq.constRq Φ ((16 : ZMod q) ^ ((t % (k * digits)) % digits))
      * toRq (c.val.getD (t / (k * digits)) (alloc.vec.Vec.new cpoly.field.Fp))
  else 0

/-- The flat column index of block `i`, gadget row `e`, digit slot `f` is in range. -/
theorem tgm_index_lt {k digits blocks i e f : ℕ} (hi : i < blocks) (he : e < k) (hf : f < digits) :
    i * (k * digits) + (e * digits + f) < blocks * (k * digits) := by
  have h1 : e * digits + f < k * digits := by
    calc e * digits + f < e * digits + digits := by omega
      _ = (e + 1) * digits := by ring
      _ ≤ k * digits := Nat.mul_le_mul_right _ he
  have h2 : (i + 1) * (k * digits) ≤ blocks * (k * digits) := Nat.mul_le_mul_right _ hi
  have h3 : (i + 1) * (k * digits) = i * (k * digits) + k * digits := by ring
  omega

/-- The value written at the flat column index of block `i`, gadget row `e`, digit
slot `f`. -/
theorem tgmVal_index {k digits : ℕ} (c : linalg.PolyVec) (p : ℕ) {i e f : ℕ}
    (he : e < k) (hf : f < digits) :
    tgmVal k digits c p (i * (k * digits) + (e * digits + f))
      = if e = p then
          Rq.constRq Φ ((16 : ZMod q) ^ f)
            * toRq (c.val.getD i (alloc.vec.Vec.new cpoly.field.Fp))
        else 0 := by
  have hcol : e * digits + f < k * digits := by
    calc e * digits + f < e * digits + digits := by omega
      _ = (e + 1) * digits := by ring
      _ ≤ k * digits := Nat.mul_le_mul_right _ he
  have hdpos : 0 < digits := by omega
  have hkd : 0 < k * digits := Nat.mul_pos (by omega) hdpos
  have hsplit : i * (k * digits) + (e * digits + f) = (e * digits + f) + (k * digits) * i := by
    ring
  have hcolsplit : e * digits + f = f + digits * e := by ring
  have hmod : (i * (k * digits) + (e * digits + f)) % (k * digits) = e * digits + f := by
    rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcol]
  have hdiv : (i * (k * digits) + (e * digits + f)) / (k * digits) = i := by
    rw [hsplit, Nat.add_mul_div_left _ _ hkd, Nat.div_eq_of_lt hcol, Nat.zero_add]
  have hcdiv : (e * digits + f) / digits = e := by
    rw [hcolsplit, Nat.add_mul_div_left _ _ hdpos, Nat.div_eq_of_lt hf, Nat.zero_add]
  have hcmod : (e * digits + f) % digits = f := by
    rw [hcolsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hf]
  rw [tgmVal, hmod, hdiv, hcdiv, hcmod]

/-- The innermost loop of `tensor_g_matrix`: the `digits` slots of gadget row `e`
of block `i`. -/
theorem tensor_g_matrix_digit_loop_spec {k digits blocks : ℕ} (dd : Std.Usize)
    (c : linalg.PolyVec) (p : Std.Usize) (row : alloc.vec.Vec ring.Rq) (i e f : Std.Usize)
    (hc : WfVec blocks c) (hd : dd.val = digits) (hi : i.val < blocks) (he : e.val < k)
    (hfit : blocks * (k * digits) ≤ Usize.max)
    (hf : f.val ≤ digits)
    (hlen : row.val.length = i.val * (k * digits) + (e.val * digits + f.val))
    (hwf : ∀ y ∈ row.val, Wf y)
    (hval : ∀ t, t < row.val.length →
      toRq (row.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = tgmVal k digits c p.val t) :
    quadeval.tensor_g_matrix_loop0_loop0_loop0_loop0 dd c p row i e f
      ⦃ z => z.val.length = i.val * (k * digits) + (e.val * digits + digits) ∧
        (∀ y ∈ z.val, Wf y) ∧
        ∀ t, t < z.val.length →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = tgmVal k digits c p.val t ⦄ := by
  rw [quadeval.tensor_g_matrix_loop0_loop0_loop0_loop0]
  apply loop.spec_decr_nat (fun s => dd.val - s.2.val)
    (fun s => s.2.val ≤ digits ∧
      s.1.val.length = i.val * (k * digits) + (e.val * digits + s.2.val) ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      ∀ t, t < s.1.val.length →
        toRq (s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = tgmVal k digits c p.val t)
  · rintro ⟨r1, f1⟩ ⟨hf1, hlen1, hwf1, hval1⟩
    dsimp only at hf1 hlen1 hwf1 hval1
    simp only [quadeval.tensor_g_matrix_loop0_loop0_loop0_loop0.body]
    by_cases hlt : f1 < dd
    · rw [if_pos hlt]
      have hf1lt : f1.val < digits := by rw [← hd]; scalar_tac
      have hidxlt : r1.val.length < blocks * (k * digits) := by
        rw [hlen1]; exact tgm_index_lt hi he hf1lt
      have hcap : r1.val.length < Usize.max := by omega
      have hentry :
          (if e = p then
            (do
              let r ← linalg.PolyVec.get c i
              let fp ← gadget.base_pow f1
              ring.Rq.scalar_mul r fp)
            else ring.Rq.zero)
            ⦃ entry => Wf entry ∧
              toRq entry = tgmVal k digits c p.val r1.val.length ⦄ := by
        by_cases hep : e = p
        · rw [if_pos hep]
          have hia : i.val < c.val.length := by rw [hc.1]; exact hi
          simp only [linalg.PolyVec.get]
          step as ⟨r, hr⟩
          have hWr : Wf r := by rw [hr]; exact hc.2 _ (List.getElem_mem hia)
          step with HachiEquiv.Scheme.base_pow_spec f1 as ⟨fp, hRfp, hfp⟩
          apply spec_mono (RqBridge.scalar_mul_spec r fp hWr hRfp)
          rintro entry ⟨hWentry, hentryv⟩
          refine ⟨hWentry, ?_⟩
          have hepv : e.val = p.val := by rw [hep]
          rw [hentryv, hfp, hr, ← List.getD_eq_getElem _ _ hia, hlen1,
            tgmVal_index c p.val he hf1lt, if_pos hepv]
        · rw [if_neg hep]
          apply spec_mono RqBridge.zero_spec
          rintro entry ⟨hWentry, hentryv⟩
          refine ⟨hWentry, ?_⟩
          have hepv : ¬ (e.val = p.val) := by
            intro h; exact hep (by scalar_tac)
          rw [hentryv, hlen1, tgmVal_index c p.val he hf1lt, if_neg hepv]
      step with hentry as ⟨entry, hWentry, hentryval⟩
      step as ⟨r2, hr2⟩
      step as ⟨f2, hf2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [hr2, hf2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [hr2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWentry
      · intro t ht
        rw [hr2, List.length_append] at ht
        simp only [List.length_cons, List.length_nil] at ht
        rcases Nat.lt_or_ge t r1.val.length with htlt | htge
        · rw [hr2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : t = r1.val.length := by omega
          rw [hteq, hr2, getD_append_eq, hentryval]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : f1.val = digits := by rw [← hd]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hval1⟩
  · exact ⟨hf, hlen, hwf, hval⟩

/-- The `e`-loop of `tensor_g_matrix`: the `k` gadget rows of block `i`. -/
theorem tensor_g_matrix_row_loop_spec {k digits blocks : ℕ} (kk dd : Std.Usize)
    (c : linalg.PolyVec) (p : Std.Usize) (row : alloc.vec.Vec ring.Rq) (i e : Std.Usize)
    (hc : WfVec blocks c) (hk : kk.val = k) (hd : dd.val = digits) (hi : i.val < blocks)
    (hfit : blocks * (k * digits) ≤ Usize.max)
    (he : e.val ≤ k) (hlen : row.val.length = i.val * (k * digits) + e.val * digits)
    (hwf : ∀ y ∈ row.val, Wf y)
    (hval : ∀ t, t < row.val.length →
      toRq (row.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = tgmVal k digits c p.val t) :
    quadeval.tensor_g_matrix_loop0_loop0_loop0 kk dd c p row i e
      ⦃ z => z.val.length = i.val * (k * digits) + k * digits ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ t, t < z.val.length →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = tgmVal k digits c p.val t ⦄ := by
  rw [quadeval.tensor_g_matrix_loop0_loop0_loop0]
  apply loop.spec_decr_nat (fun s => kk.val - s.2.val)
    (fun s => s.2.val ≤ k ∧ s.1.val.length = i.val * (k * digits) + s.2.val * digits ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      ∀ t, t < s.1.val.length →
        toRq (s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = tgmVal k digits c p.val t)
  · rintro ⟨r1, e1⟩ ⟨he1, hlen1, hwf1, hval1⟩
    dsimp only at he1 hlen1 hwf1 hval1
    simp only [quadeval.tensor_g_matrix_loop0_loop0_loop0.body]
    by_cases hlt : e1 < kk
    · rw [if_pos hlt]
      have he1lt : e1.val < k := by rw [← hk]; scalar_tac
      step with tensor_g_matrix_digit_loop_spec dd c p r1 i e1 0#usize hc hd hi he1lt hfit
        (by simp) (by simp [hlen1]) hwf1 hval1 as ⟨r2, hlen2, hwf2, hval2⟩
      step as ⟨e2, he2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [hlen2, he2]; ring
      · exact hwf2
      · exact hval2
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : e1.val = k := by rw [← hk]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hval1⟩
  · exact ⟨he, hlen, hwf, hval⟩

/-- The block loop of `tensor_g_matrix`: row `p` is filled block by block. -/
theorem tensor_g_matrix_block_loop_spec {k digits blocks : ℕ} (kk dd : Std.Usize)
    (c : linalg.PolyVec) (bl : Std.Usize) (p : Std.Usize) (row : alloc.vec.Vec ring.Rq)
    (i : Std.Usize)
    (hc : WfVec blocks c) (hk : kk.val = k) (hd : dd.val = digits) (hbl : bl.val = blocks)
    (hfit : blocks * (k * digits) ≤ Usize.max)
    (hi : i.val ≤ blocks) (hlen : row.val.length = i.val * (k * digits))
    (hwf : ∀ y ∈ row.val, Wf y)
    (hval : ∀ t, t < row.val.length →
      toRq (row.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = tgmVal k digits c p.val t) :
    quadeval.tensor_g_matrix_loop0_loop0 kk dd c bl p row i
      ⦃ z => z.val.length = blocks * (k * digits) ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ t, t < z.val.length →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = tgmVal k digits c p.val t ⦄ := by
  rw [quadeval.tensor_g_matrix_loop0_loop0]
  apply loop.spec_decr_nat (fun s => bl.val - s.2.val)
    (fun s => s.2.val ≤ blocks ∧ s.1.val.length = s.2.val * (k * digits) ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      ∀ t, t < s.1.val.length →
        toRq (s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = tgmVal k digits c p.val t)
  · rintro ⟨r1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [quadeval.tensor_g_matrix_loop0_loop0.body]
    by_cases hlt : i1 < bl
    · rw [if_pos hlt]
      have hi1lt : i1.val < blocks := by rw [← hbl]; scalar_tac
      step with tensor_g_matrix_row_loop_spec kk dd c p r1 i1 0#usize hc hk hd hi1lt hfit
        (by simp) (by simp [hlen1]) hwf1 hval1 as ⟨r2, hlen2, hwf2, hval2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [hlen2, hi2]; ring
      · exact hwf2
      · exact hval2
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = blocks := by rw [← hbl]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hval1⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- The row loop of `tensor_g_matrix`: the `k` rows of the matrix. -/
theorem tensor_g_matrix_outer_loop_spec {k digits blocks : ℕ} (kk dd : Std.Usize)
    (c : linalg.PolyVec) (bl : Std.Usize) (rows : alloc.vec.Vec linalg.PolyVec) (p : Std.Usize)
    (hc : WfVec blocks c) (hk : kk.val = k) (hd : dd.val = digits) (hbl : bl.val = blocks)
    (hfit : blocks * (k * digits) ≤ Usize.max)
    (hp : p.val ≤ k) (hlen : rows.val.length = p.val)
    (hwf : ∀ x ∈ rows.val, WfVec (blocks * (k * digits)) x)
    (hval : ∀ s, s < p.val → ∀ t, t < blocks * (k * digits) →
      toRq ((rows.val.getD s (alloc.vec.Vec.new ring.Rq)).val.getD t
          (alloc.vec.Vec.new cpoly.field.Fp))
        = tgmVal k digits c s t) :
    quadeval.tensor_g_matrix_loop0 kk dd c bl rows p
      ⦃ z => z.val.length = k ∧ (∀ x ∈ z.val, WfVec (blocks * (k * digits)) x) ∧
        ∀ s, s < k → ∀ t, t < blocks * (k * digits) →
          toRq ((z.val.getD s (alloc.vec.Vec.new ring.Rq)).val.getD t
              (alloc.vec.Vec.new cpoly.field.Fp))
            = tgmVal k digits c s t ⦄ := by
  rw [quadeval.tensor_g_matrix_loop0]
  apply loop.spec_decr_nat (fun s => kk.val - s.2.val)
    (fun st => st.2.val ≤ k ∧ st.1.val.length = st.2.val ∧
      (∀ x ∈ st.1.val, WfVec (blocks * (k * digits)) x) ∧
      ∀ s, s < st.2.val → ∀ t, t < blocks * (k * digits) →
        toRq ((st.1.val.getD s (alloc.vec.Vec.new ring.Rq)).val.getD t
            (alloc.vec.Vec.new cpoly.field.Fp))
          = tgmVal k digits c s t)
  · rintro ⟨o1, p1⟩ ⟨hp1, hlen1, hwf1, hval1⟩
    dsimp only at hp1 hlen1 hwf1 hval1
    simp only [quadeval.tensor_g_matrix_loop0.body]
    by_cases hlt : p1 < kk
    · rw [if_pos hlt]
      have hp1lt : p1.val < k := by rw [← hk]; scalar_tac
      step with tensor_g_matrix_block_loop_spec kk dd c bl p1 (alloc.vec.Vec.new ring.Rq) 0#usize
        hc hk hd hbl hfit (by simp) (by simp) (by intro y hy; simp at hy)
        (by intro t ht; simp at ht) as ⟨r2, hlen2, hwf2, hval2⟩
      simp only [linalg.PolyVec.new]
      have hcap : o1.val.length < Usize.max := by
        have : k ≤ Usize.max := by scalar_tac
        omega
      step as ⟨o2, ho2⟩
      step as ⟨p2, hp2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hp2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
      · intro x hx
        rw [ho2] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hwf1 x h
        · rw [List.mem_singleton.mp h]; exact ⟨hlen2, hwf2⟩
      · intro s hs t ht
        rw [hp2] at hs
        rcases Nat.lt_or_ge s p1.val with hslt | hsge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 s hslt t ht
        · have hseq : s = o1.val.length := by rw [hlen1]; omega
          rw [hseq, ho2, getD_append_eq, hlen1]
          exact hval2 t (by rw [hlen2]; exact ht)
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : p1.val = k := by rw [← hk]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1,
        fun s hs t ht => hval1 s (by rw [heq]; exact hs) t ht⟩
  · exact ⟨hp, hlen, hwf, hval⟩

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
  rw [quadeval.tensor_g_matrix]
  simp only [linalg.PolyVec.len]
  step with tensor_g_matrix_outer_loop_spec kk dd c (alloc.vec.Vec.len c)
    (alloc.vec.Vec.new linalg.PolyVec) 0#usize hc hk hd (by simpa using hc.1) hfit
    (by simp) (by simp) (by intro x hx; simp at hx) (by intro s hs; simp at hs)
    as ⟨z, hzlen, hzwf, hzval⟩
  simp only [linalg.PolyMatrix.new, WP.spec_ok]
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i j
  simp only [toMat, toVec]
  rw [hzval i.val i.isLt j.val j.isLt]
  simp only [InnerOuter.tensorGMatrix, finProdFinEquiv_symm_apply, Fin.divNat, Fin.modNat,
    gadgetMatrix, gadgetEntry, toVec, tgmVal]
  split_ifs with h
  · rw [mul_comm]
  · rw [mul_zero]

/-! ## The witness maps -/

/-- The carrier loop of `stack`: `resp.carrierDec` is appended to the accumulator. -/
theorem stack_carrier_loop_spec {n : ℕ} (resp : quadeval.QuadEvalResponse)
    (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hcd : WfVec n resp.carrier_dec) (hcap : out.val.length + n ≤ Usize.max)
    (hi : i.val ≤ n) (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.stack_loop0 resp out i
      ⦃ z => z.val.length = out.val.length + (n - i.val) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length →
          z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
            = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < n - i.val →
          toRq (z.val.getD (out.val.length + t) (alloc.vec.Vec.new cpoly.field.Fp))
            = toRq (resp.carrier_dec.val.getD (i.val + t)
                (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [quadeval.stack_loop0]
  apply loop.spec_decr_nat (fun s => n - s.2.val)
    (fun s => s.2.val ≤ n ∧ s.1.val.length = out.val.length + (s.2.val - i.val) ∧
      i.val ≤ s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length →
        s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val - i.val →
        toRq (s.1.val.getD (out.val.length + t) (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq (resp.carrier_dec.val.getD (i.val + t) (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hge1, hwf1, hpre1, hval1⟩
    dsimp only at hi1 hlen1 hge1 hwf1 hpre1 hval1
    simp only [quadeval.stack_loop0.body, quadeval.QuadEvalResponse.impl.carrier_dec,
      linalg.PolyVec.len, bind_tc_ok]
    have hcdlen : resp.carrier_dec.val.length = n := hcd.1
    have hnnv : (alloc.vec.Vec.len resp.carrier_dec).val = n := by simpa using hcdlen
    by_cases hlt : i1 < alloc.vec.Vec.len resp.carrier_dec
    · rw [if_pos hlt]
      have hi1lt : i1.val < n := by rw [← hnnv]; scalar_tac
      have hidx : i1.val < resp.carrier_dec.val.length := by rw [hcdlen]; exact hi1lt
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hcd.2 _ (List.getElem_mem hidx)
      step with RqBridge.copy_spec r hWr as ⟨r1, hWr1, hr1⟩
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · scalar_tac
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t (i1.val - i.val) with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hidxeq : i.val + t = i1.val := by omega
          rw [hteq, ho2, getD_append_eq, hr1, hr, hidxeq,
            ← List.getD_eq_getElem _ _ hidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n := by rw [← hnnv]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, by rw [← heq]; exact hval1⟩
  · refine ⟨hi, ?_, le_refl _, hwf, ?_, ?_⟩
    · dsimp only; omega
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; exact absurd ht (by omega)

/-- The middle loop of `stack`: the flattened inner blocks are appended. -/
theorem stack_flat_loop_spec {n : ℕ} (flat : linalg.PolyVec)
    (out : alloc.vec.Vec ring.Rq) (j : Std.Usize)
    (hfl : WfVec n flat) (hcap : out.val.length + n ≤ Usize.max)
    (hj : j.val ≤ n) (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.stack_loop1 flat out j
      ⦃ z => z.val.length = out.val.length + (n - j.val) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length →
          z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
            = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < n - j.val →
          toRq (z.val.getD (out.val.length + t) (alloc.vec.Vec.new cpoly.field.Fp))
            = toRq (flat.val.getD (j.val + t) (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [quadeval.stack_loop1]
  apply loop.spec_decr_nat (fun s => n - s.2.val)
    (fun s => s.2.val ≤ n ∧ s.1.val.length = out.val.length + (s.2.val - j.val) ∧
      j.val ≤ s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length →
        s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val - j.val →
        toRq (s.1.val.getD (out.val.length + t) (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq (flat.val.getD (j.val + t) (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, j1⟩ ⟨hj1, hlen1, hge1, hwf1, hpre1, hval1⟩
    dsimp only at hj1 hlen1 hge1 hwf1 hpre1 hval1
    simp only [quadeval.stack_loop1.body, linalg.PolyVec.len, bind_tc_ok]
    have hfllen : flat.val.length = n := hfl.1
    have hnnv : (alloc.vec.Vec.len flat).val = n := by simpa using hfllen
    by_cases hlt : j1 < alloc.vec.Vec.len flat
    · rw [if_pos hlt]
      have hj1lt : j1.val < n := by rw [← hnnv]; scalar_tac
      have hidx : j1.val < flat.val.length := by rw [hfllen]; exact hj1lt
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hfl.2 _ (List.getElem_mem hidx)
      step with RqBridge.copy_spec r hWr as ⟨r1, hWr1, hr1⟩
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨j2, hj2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hj2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · scalar_tac
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hj2] at ht
        rcases Nat.lt_or_ge t (j1.val - j.val) with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hidxeq : j.val + t = j1.val := by omega
          rw [hteq, ho2, getD_append_eq, hr1, hr, hidxeq,
            ← List.getD_eq_getElem _ _ hidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : j1.val = n := by rw [← hnnv]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, by rw [← heq]; exact hval1⟩
  · refine ⟨hj, ?_, le_refl _, hwf, ?_, ?_⟩
    · dsimp only; omega
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; exact absurd ht (by omega)

/-- The `z` loop of `stack`: `resp.zDec` is appended. -/
theorem stack_z_loop_spec {n : ℕ} (resp : quadeval.QuadEvalResponse)
    (out : alloc.vec.Vec ring.Rq) (kk : Std.Usize)
    (hzd : WfVec n resp.z_dec) (hcap : out.val.length + n ≤ Usize.max)
    (hk : kk.val ≤ n) (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.stack_loop2 resp out kk
      ⦃ z => z.val.length = out.val.length + (n - kk.val) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length →
          z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
            = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < n - kk.val →
          toRq (z.val.getD (out.val.length + t) (alloc.vec.Vec.new cpoly.field.Fp))
            = toRq (resp.z_dec.val.getD (kk.val + t) (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [quadeval.stack_loop2]
  apply loop.spec_decr_nat (fun s => n - s.2.val)
    (fun s => s.2.val ≤ n ∧ s.1.val.length = out.val.length + (s.2.val - kk.val) ∧
      kk.val ≤ s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length →
        s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val - kk.val →
        toRq (s.1.val.getD (out.val.length + t) (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq (resp.z_dec.val.getD (kk.val + t) (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, k1⟩ ⟨hk1, hlen1, hge1, hwf1, hpre1, hval1⟩
    dsimp only at hk1 hlen1 hge1 hwf1 hpre1 hval1
    simp only [quadeval.stack_loop2.body, quadeval.QuadEvalResponse.impl.z_dec,
      linalg.PolyVec.len, bind_tc_ok]
    have hzdlen : resp.z_dec.val.length = n := hzd.1
    have hnnv : (alloc.vec.Vec.len resp.z_dec).val = n := by simpa using hzdlen
    by_cases hlt : k1 < alloc.vec.Vec.len resp.z_dec
    · rw [if_pos hlt]
      have hk1lt : k1.val < n := by rw [← hnnv]; scalar_tac
      have hidx : k1.val < resp.z_dec.val.length := by rw [hzdlen]; exact hk1lt
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hzd.2 _ (List.getElem_mem hidx)
      step with RqBridge.copy_spec r hWr as ⟨r1, hWr1, hr1⟩
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨k2, hk2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hk2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · scalar_tac
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hk2] at ht
        rcases Nat.lt_or_ge t (k1.val - kk.val) with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hidxeq : kk.val + t = k1.val := by omega
          rw [hteq, ho2, getD_append_eq, hr1, hr, hidxeq,
            ← List.getD_eq_getElem _ _ hidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = n := by rw [← hnnv]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, by rw [← heq]; exact hval1⟩
  · refine ⟨hk, ?_, le_refl _, hwf, ?_, ?_⟩
    · dsimp only; omega
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; exact absurd ht (by omega)

/-- `stack` computes `stack`, the adapter's witness map
`ζ = ŵ ++ (flatten t̂ ++ ẑ)` (`:158`). -/
theorem stack_spec (resp : quadeval.QuadEvalResponse)
    (sr : InnerOuter.QuadEvalResponse Φ 1 (2 ^ 10) 8 (2 ^ 10) 8 5)
    (hre : RepResp resp sr) :
    quadeval.stack resp
      ⦃ out => WfVec (InnerOuter.rlinCols 1 8 8 5 10 10) out ∧
        toVec (k := InnerOuter.rlinCols 1 8 8 5 10 10) out = InnerOuter.stack Φ sr ⦄ := by
  obtain ⟨hWc, hWi, hWz, hcv, hiv, hzv⟩ := hre
  rw [quadeval.stack]
  simp only [quadeval.QuadEvalResponse.impl.inner_dec]
  step with HachiEquiv.Scheme.flatten_blocks_spec (blocks := 2 ^ 10) (width := 1 * 8)
    resp.inner_dec (by scalar_tac) hWi as ⟨flat, hWflat, hflat⟩
  step with stack_carrier_loop_spec (n := 2 ^ 10 * 8) resp (alloc.vec.Vec.new ring.Rq) 0#usize
    hWc (by simp; scalar_tac) (by simp) (by intro y hy; simp at hy)
    as ⟨o1, hlen1, hwf1, _, hval1⟩
  simp only [alloc.vec.Vec.new, List.length_nil, Nat.zero_add, Nat.sub_zero] at hlen1 hval1
  step with stack_flat_loop_spec (n := 2 ^ 10 * (1 * 8)) flat o1 0#usize hWflat
    (by rw [hlen1]; scalar_tac) (by simp) hwf1 as ⟨o2, hlen2, hwf2, hpre2, hval2⟩
  step with stack_z_loop_spec (n := 2 ^ 10 * 8 * 5) resp o2 0#usize hWz
    (by rw [hlen2, hlen1]; scalar_tac) (by simp) hwf2 as ⟨o3, hlen3, hwf3, hpre3, hval3⟩
  simp only [Nat.sub_zero] at hlen2 hlen3
  simp only [linalg.PolyVec.new, WP.spec_ok]
  have hlen3' : o3.val.length = InnerOuter.rlinCols 1 8 8 5 10 10 := by
    rw [hlen3, hlen2, hlen1]; norm_num [InnerOuter.rlinCols]
  refine ⟨⟨hlen3', hwf3⟩, ?_⟩
  have hflat' : toVec (k := 2 ^ 10 * (1 * 8)) flat = PolyVec.flattenBlocks sr.innerDec := by
    rw [hflat, ← hiv]; rfl
  funext j
  simp only [toVec, InnerOuter.stack]
  refine Fin.addCases (fun a => ?_) (fun a => ?_) j
  · rw [Fin.append_left]
    rw [Fin.val_castAdd, hpre3 a.val (by rw [hlen2, hlen1]; omega),
      hpre2 a.val (by rw [hlen1]; omega), hval1 a.val a.isLt]
    have ha' := congrFun hcv a
    simp only [toVec] at ha'
    exact ha'
  · rw [Fin.append_right]
    refine Fin.addCases (fun b => ?_) (fun b => ?_) a
    · rw [Fin.append_left]
      have h2 := hval2 b.val (by omega)
      simp only [Nat.zero_add] at h2
      rw [hlen1] at h2
      rw [Fin.val_natAdd, Fin.val_castAdd, hpre3 _ (by rw [hlen2, hlen1]; omega), h2]
      have hb' := congrFun hflat' b
      simp only [toVec] at hb'
      exact hb'
    · rw [Fin.append_right]
      have h3 := hval3 b.val (by omega)
      simp only [Nat.zero_add] at h3
      rw [hlen2, hlen1] at h3
      rw [Fin.val_natAdd, Fin.val_natAdd,
        show 2 ^ 10 * 8 + (2 ^ 10 * (1 * 8) + b.val)
            = 2 ^ 10 * 8 + 2 ^ 10 * (1 * 8) + b.val from by ring, h3]
      have hb' := congrFun hzv b
      simp only [toVec] at hb'
      exact hb'

/-- The head loop of `unstack`: the first `cw` entries of `ζ`. -/
theorem unstack_head_loop_spec {mu : ℕ} (zeta : linalg.PolyVec) (cw : Std.Usize)
    (carrier : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hz : WfVec mu zeta) (hcw : cw.val ≤ mu) (hi : i.val ≤ cw.val)
    (hlen : carrier.val.length = i.val) (hwf : ∀ y ∈ carrier.val, Wf y)
    (hval : ∀ t, t < i.val →
      toRq (carrier.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (zeta.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))) :
    quadeval.unstack_loop0 zeta cw carrier i
      ⦃ z => z.val.length = cw.val ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ t, t < cw.val →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = toRq (zeta.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  have hzlen : zeta.val.length = mu := hz.1
  have hcap : mu ≤ Usize.max := by rw [← hzlen]; exact zeta.property
  rw [quadeval.unstack_loop0]
  apply loop.spec_decr_nat (fun s => cw.val - s.2.val)
    (fun s => s.2.val ≤ cw.val ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ t, t < s.2.val →
        toRq (s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq (zeta.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨c1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [quadeval.unstack_loop0.body]
    by_cases hlt : i1 < cw
    · rw [if_pos hlt]
      have hi1lt : i1.val < cw.val := by scalar_tac
      have hidx : i1.val < zeta.val.length := by rw [hzlen]; omega
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hz.2 _ (List.getElem_mem hidx)
      step with RqBridge.copy_spec r hWr as ⟨r1, hWr1, hr1⟩
      have hcap1 : c1.val.length < Usize.max := by rw [hlen1]; omega
      step as ⟨c2, hc2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [hc2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
      · intro y hy
        rw [hc2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [hc2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : t = c1.val.length := by rw [hlen1]; omega
          rw [hteq, hc2, getD_append_eq, hr1, hr, hlen1, ← List.getD_eq_getElem _ _ hidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = cw.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- The middle loop of `unstack`: the `ct` entries of `ζ` after the first `cw`. -/
theorem unstack_mid_loop_spec {mu : ℕ} (zeta : linalg.PolyVec) (cw ct : Std.Usize)
    (middle : alloc.vec.Vec ring.Rq) (j : Std.Usize)
    (hz : WfVec mu zeta) (hsum : cw.val + ct.val ≤ mu) (hj : j.val ≤ ct.val)
    (hlen : middle.val.length = j.val) (hwf : ∀ y ∈ middle.val, Wf y)
    (hval : ∀ t, t < j.val →
      toRq (middle.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (zeta.val.getD (cw.val + t) (alloc.vec.Vec.new cpoly.field.Fp))) :
    quadeval.unstack_loop1 zeta cw ct middle j
      ⦃ z => z.val.length = ct.val ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ t, t < ct.val →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = toRq (zeta.val.getD (cw.val + t) (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  have hzlen : zeta.val.length = mu := hz.1
  have hcap : mu ≤ Usize.max := by rw [← hzlen]; exact zeta.property
  rw [quadeval.unstack_loop1]
  apply loop.spec_decr_nat (fun s => ct.val - s.2.val)
    (fun s => s.2.val ≤ ct.val ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ t, t < s.2.val →
        toRq (s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq (zeta.val.getD (cw.val + t) (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨m1, j1⟩ ⟨hj1, hlen1, hwf1, hval1⟩
    dsimp only at hj1 hlen1 hwf1 hval1
    simp only [quadeval.unstack_loop1.body]
    by_cases hlt : j1 < ct
    · rw [if_pos hlt]
      have hj1lt : j1.val < ct.val := by scalar_tac
      have hsumfit : cw.val + j1.val ≤ Usize.max := by omega
      step as ⟨idx, hidxv⟩
      have hidxval : idx.val = cw.val + j1.val := by rw [hidxv]
      have hidx : idx.val < zeta.val.length := by rw [hzlen, hidxval]; omega
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hz.2 _ (List.getElem_mem hidx)
      step with RqBridge.copy_spec r hWr as ⟨r1, hWr1, hr1⟩
      have hcap1 : m1.val.length < Usize.max := by rw [hlen1]; omega
      step as ⟨m2, hm2⟩
      step as ⟨j2, hj2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [hm2, hj2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
      · intro y hy
        rw [hm2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [hj2] at ht
        rcases Nat.lt_or_ge t j1.val with htlt | htge
        · rw [hm2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : t = m1.val.length := by rw [hlen1]; omega
          rw [hteq, hm2, getD_append_eq, hr1, hr, hlen1, ← hidxval,
            List.getD_eq_getElem _ _ hidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : j1.val = ct.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · exact ⟨hj, hlen, hwf, hval⟩

/-- The tail loop of `unstack`: everything from index `cw + ct` on. -/
theorem unstack_tail_loop_spec {mu : ℕ} (zeta : linalg.PolyVec) (kk : Std.Usize)
    (zv : alloc.vec.Vec ring.Rq) (k : Std.Usize)
    (hz : WfVec mu zeta) (hk : kk.val ≤ k.val) (hkm : k.val ≤ mu)
    (hlen : zv.val.length = k.val - kk.val) (hwf : ∀ y ∈ zv.val, Wf y)
    (hval : ∀ t, t < k.val - kk.val →
      toRq (zv.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (zeta.val.getD (kk.val + t) (alloc.vec.Vec.new cpoly.field.Fp))) :
    quadeval.unstack_loop2 zeta zv k
      ⦃ z => z.val.length = mu - kk.val ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ t, t < mu - kk.val →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = toRq (zeta.val.getD (kk.val + t) (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  have hzlen : zeta.val.length = mu := hz.1
  have hcap : mu ≤ Usize.max := by rw [← hzlen]; exact zeta.property
  have hlenv : (alloc.vec.Vec.len zeta).val = mu := by simpa using hzlen
  rw [quadeval.unstack_loop2]
  apply loop.spec_decr_nat (fun s => mu - s.2.val)
    (fun s => s.2.val ≤ mu ∧ kk.val ≤ s.2.val ∧ s.1.val.length = s.2.val - kk.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      ∀ t, t < s.2.val - kk.val →
        toRq (s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq (zeta.val.getD (kk.val + t) (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨z1, k1⟩ ⟨hk1, hge1, hlen1, hwf1, hval1⟩
    dsimp only at hk1 hge1 hlen1 hwf1 hval1
    simp only [quadeval.unstack_loop2.body, linalg.PolyVec.len, bind_tc_ok]
    by_cases hlt : k1 < alloc.vec.Vec.len zeta
    · rw [if_pos hlt]
      have hk1lt : k1.val < mu := by rw [← hlenv]; scalar_tac
      have hidx : k1.val < zeta.val.length := by rw [hzlen]; exact hk1lt
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hz.2 _ (List.getElem_mem hidx)
      step with RqBridge.copy_spec r hWr as ⟨r1, hWr1, hr1⟩
      have hcap1 : z1.val.length < Usize.max := by rw [hlen1]; omega
      step as ⟨z2, hz2⟩
      step as ⟨k2, hk2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · scalar_tac
      · rw [hz2, hk2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [hz2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [hk2] at ht
        rcases Nat.lt_or_ge t (k1.val - kk.val) with htlt | htge
        · rw [hz2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : t = z1.val.length := by rw [hlen1]; omega
          have hidxeq : kk.val + (k1.val - kk.val) = k1.val := by omega
          rw [hteq, hz2, getD_append_eq, hr1, hr, hlen1, hidxeq,
            List.getD_eq_getElem _ _ hidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = mu := by rw [← hlenv]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · exact ⟨hkm, hk, hlen, hwf, hval⟩

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
  have hzlen : zeta.val.length = InnerOuter.rlinCols 1 8 8 5 10 10 := hz.1
  have hmu : InnerOuter.rlinCols 1 8 8 5 10 10 ≤ Usize.max := by
    rw [← hzlen]; exact zeta.property
  have hcwv : cw.val = 2 ^ 10 * 8 := hcw
  have hctv : ct.val = 2 ^ 10 * (1 * 8) := hct
  rw [quadeval.unstack]
  step with unstack_head_loop_spec (mu := InnerOuter.rlinCols 1 8 8 5 10 10) zeta cw
    (alloc.vec.Vec.new ring.Rq) 0#usize hz (by rw [hcwv]; norm_num [InnerOuter.rlinCols])
    (by simp) (by simp) (by intro y hy; simp at hy) (by intro t ht; simp at ht)
    as ⟨carrier, hclen, hcwf, hcval⟩
  step with unstack_mid_loop_spec (mu := InnerOuter.rlinCols 1 8 8 5 10 10) zeta cw ct
    (alloc.vec.Vec.new ring.Rq) 0#usize hz
    (by rw [hcwv, hctv]; norm_num [InnerOuter.rlinCols])
    (by simp) (by simp) (by intro y hy; simp at hy) (by intro t ht; simp at ht)
    as ⟨middle, hmlen, hmwf, hmval⟩
  have hsumfit : cw.val + ct.val ≤ Usize.max := by
    rw [hcwv, hctv]; norm_num [InnerOuter.rlinCols] at hmu ⊢; omega
  step as ⟨kk, hkk⟩
  have hkkv : kk.val = 2 ^ 10 * 8 + 2 ^ 10 * (1 * 8) := by rw [hkk, hcwv, hctv]
  step with unstack_tail_loop_spec (mu := InnerOuter.rlinCols 1 8 8 5 10 10) zeta kk
    (alloc.vec.Vec.new ring.Rq) kk hz
    (le_refl _) (by rw [hkkv]; norm_num [InnerOuter.rlinCols]) (by simp)
    (by intro y hy; simp at hy) (by intro t ht; simp at ht)
    as ⟨zv, hzvlen, hzvwf, hzvval⟩
  simp only [linalg.PolyVec.new, bind_tc_ok]
  step with unflatten_spec (blocks := 2 ^ 10) (width := 1 * 8) middle innerWidth
    ⟨by rw [hmlen, hctv], hmwf⟩ hiw (by norm_num) as ⟨v, hvwf, hvval⟩
  have hzvlen' : zv.val.length = 2 ^ 10 * 8 * 5 := by
    rw [hzvlen, hkkv]; norm_num [InnerOuter.rlinCols]
  refine HachiEquiv.QuadEvalProtocol.QuadEvalResponse_new_spec carrier v zv _ ?_ ?_ ?_
    ⟨by rw [hclen, hcwv], hcwf⟩ hvwf ⟨hzvlen', hzvwf⟩
  · funext i
    simp only [toVec, InnerOuter.unstack]
    rw [hcval i.val (by rw [hcwv]; exact i.isLt), Fin.val_castAdd]
  · have hmid : toVec (k := 2 ^ 10 * (1 * 8)) middle
        = fun k => toVec (k := InnerOuter.rlinCols 1 8 8 5 10 10) zeta
            (Fin.natAdd (InnerOuter.rlinCW 8 10) (Fin.castAdd (InnerOuter.rlinCZ 8 5 10) k)) := by
      funext i
      simp only [toVec]
      rw [hmval i.val (by rw [hctv]; exact i.isLt), Fin.val_natAdd, Fin.val_castAdd, hcwv]
    rw [hvval]
    exact congrArg (InnerOuter.unflatten (P := Rq Φ) (blocks := 2 ^ 10) (width := 1 * 8)) hmid
  · funext i
    have hb : i.val < InnerOuter.rlinCols 1 8 8 5 10 10 - kk.val := by
      have hi := i.isLt
      rw [hkkv]
      norm_num [InnerOuter.rlinCols] at hi ⊢
      omega
    have hi3 := hzvval i.val hb
    rw [hkkv, show 2 ^ 10 * 8 + 2 ^ 10 * (1 * 8) + i.val
        = 2 ^ 10 * 8 + (2 ^ 10 * (1 * 8) + i.val) from by ring] at hi3
    simp only [toVec, InnerOuter.unstack]
    rw [Fin.val_natAdd, Fin.val_natAdd]
    exact hi3

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
  rw [quadeval.PolyEvalStatement.new, WP.spec_ok]
  exact ⟨hWu, hWxl, hWxh, hWy, hu, hxl, hxh, hy⟩

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
  obtain ⟨hWu, hWxl, hWxh, hWy, hu, hxl, hxh, hy⟩ := hs
  rw [quadeval.to_quad_eval_statement]
  simp only [quadeval.PolyEvalStatement.impl.xh, quadeval.PolyEvalStatement.impl.xl,
    quadeval.PolyEvalStatement.impl.u, quadeval.PolyEvalStatement.impl.y]
  step with HachiEquiv.EvalSplit.monomial_basis_spec (n := 10) s.xh hWxh (by scalar_tac)
    as ⟨avec, hWa, ha⟩
  step with HachiEquiv.EvalSplit.monomial_basis_spec (n := 10) s.xl hWxl (by scalar_tac)
    as ⟨bvec, hWb, hb⟩
  step with HachiEquiv.QuadEvalProtocol.poly_vec_copy_spec (k := 1) s.u hWu as ⟨u', hWu', hu'⟩
  step with RqBridge.copy_spec s.y hWy as ⟨y', hWy', hy'⟩
  apply HachiEquiv.QuadEvalProtocol.QuadEvalStatement_new_spec u' avec bvec y'
    (InnerOuter.toQuadEvalStatement Φ ps) (by rw [hu', hu]; rfl) ?_ ?_ (by rw [hy', hy]; rfl)
    hWu' hWa hWb hWy'
  · rw [ha]
    show (CMlPolynomial.monomialBasis (HachiEquiv.EvalSplit.toVector (n := 10) s.xh)).get = _
    rw [HachiEquiv.EvalSplit.toVector, hxh]
    rfl
  · rw [hb]
    show (CMlPolynomial.monomialBasis (HachiEquiv.EvalSplit.toVector (n := 10) s.xl)).get = _
    rw [HachiEquiv.EvalSplit.toVector, hxl]
    rfl

/-! ## The assembly -/

/-! ### The row loops of `rlin_stmt`

Each of the eighteen extracted loops appends one block of a row (or of the
right-hand side) to an accumulator; the specs below all have the same shape:
the accumulator's prefix is untouched and the new entries are the block. -/

theorem rlin_c1_zeros_loop_spec (ct cz : Std.Usize) (out : alloc.vec.Vec ring.Rq)
    (hsum : ct.val + cz.val ≤ Usize.max)
    (hcap : out.val.length + (ct.val + cz.val) ≤ Usize.max) (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.rlin_stmt_loop0_loop1 ct cz out 0#usize
      ⦃ z => z.val.length = out.val.length + (ct.val + cz.val) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length → z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < ct.val + cz.val → toRq (z.val.getD (out.val.length + t)
            (alloc.vec.Vec.new cpoly.field.Fp)) = 0 ⦄ := by
  rw [quadeval.rlin_stmt_loop0_loop1]
  apply loop.spec_decr_nat (fun s => ct.val + cz.val - s.2.val)
    (fun s => s.2.val ≤ ct.val + cz.val ∧ s.1.val.length = out.val.length + s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length → s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
        = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val → toRq (s.1.val.getD (out.val.length + t)
          (alloc.vec.Vec.new cpoly.field.Fp)) = 0)
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hpre1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hpre1 hval1
    simp only [quadeval.rlin_stmt_loop0_loop1.body]
    step as ⟨nn, hnn⟩
    have hnnv : nn.val = ct.val + cz.val := by rw [hnn]
    by_cases hlt : i1 < nn
    · rw [if_pos hlt]
      have hilt : i1.val < ct.val + cz.val := by rw [← hnnv]; scalar_tac
      step with RqBridge.zero_spec as ⟨r1, hWr1, hr1⟩
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hteq2 : t = i1.val := by omega
          rw [hteq, ho2, getD_append_eq]
          exact hr1
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = ct.val + cz.val := by rw [← hnnv]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · refine ⟨?_, ?_, hwf, ?_, ?_⟩
    · dsimp only; simp
    · dsimp only; simp
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; simp at ht

theorem rlin_c2_zeros_cw_loop_spec (cw : Std.Usize) (out : alloc.vec.Vec ring.Rq)
    (hcap : out.val.length + cw.val ≤ Usize.max) (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.rlin_stmt_loop1_loop0 cw out 0#usize
      ⦃ z => z.val.length = out.val.length + (cw.val) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length → z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < cw.val → toRq (z.val.getD (out.val.length + t)
            (alloc.vec.Vec.new cpoly.field.Fp)) = 0 ⦄ := by
  rw [quadeval.rlin_stmt_loop1_loop0]
  apply loop.spec_decr_nat (fun s => cw.val - s.2.val)
    (fun s => s.2.val ≤ cw.val ∧ s.1.val.length = out.val.length + s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length → s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
        = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val → toRq (s.1.val.getD (out.val.length + t)
          (alloc.vec.Vec.new cpoly.field.Fp)) = 0)
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hpre1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hpre1 hval1
    simp only [quadeval.rlin_stmt_loop1_loop0.body]
    by_cases hlt : i1 < cw
    · rw [if_pos hlt]
      have hilt : i1.val < cw.val := by scalar_tac
      step with RqBridge.zero_spec as ⟨r1, hWr1, hr1⟩
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hteq2 : t = i1.val := by omega
          rw [hteq, ho2, getD_append_eq]
          exact hr1
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = cw.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · refine ⟨?_, ?_, hwf, ?_, ?_⟩
    · dsimp only; simp
    · dsimp only; simp
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; simp at ht

theorem rlin_c2_zeros_cz_loop_spec (cz : Std.Usize) (out : alloc.vec.Vec ring.Rq)
    (hcap : out.val.length + cz.val ≤ Usize.max) (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.rlin_stmt_loop1_loop2 cz out 0#usize
      ⦃ z => z.val.length = out.val.length + (cz.val) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length → z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < cz.val → toRq (z.val.getD (out.val.length + t)
            (alloc.vec.Vec.new cpoly.field.Fp)) = 0 ⦄ := by
  rw [quadeval.rlin_stmt_loop1_loop2]
  apply loop.spec_decr_nat (fun s => cz.val - s.2.val)
    (fun s => s.2.val ≤ cz.val ∧ s.1.val.length = out.val.length + s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length → s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
        = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val → toRq (s.1.val.getD (out.val.length + t)
          (alloc.vec.Vec.new cpoly.field.Fp)) = 0)
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hpre1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hpre1 hval1
    simp only [quadeval.rlin_stmt_loop1_loop2.body]
    by_cases hlt : i1 < cz
    · rw [if_pos hlt]
      have hilt : i1.val < cz.val := by scalar_tac
      step with RqBridge.zero_spec as ⟨r1, hWr1, hr1⟩
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hteq2 : t = i1.val := by omega
          rw [hteq, ho2, getD_append_eq]
          exact hr1
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = cz.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · refine ⟨?_, ?_, hwf, ?_, ?_⟩
    · dsimp only; simp
    · dsimp only; simp
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; simp at ht

theorem rlin_c3_zeros_loop_spec (ct cz : Std.Usize) (out : alloc.vec.Vec ring.Rq)
    (hsum : ct.val + cz.val ≤ Usize.max)
    (hcap : out.val.length + (ct.val + cz.val) ≤ Usize.max) (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.rlin_stmt_loop3 ct cz out 0#usize
      ⦃ z => z.val.length = out.val.length + (ct.val + cz.val) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length → z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < ct.val + cz.val → toRq (z.val.getD (out.val.length + t)
            (alloc.vec.Vec.new cpoly.field.Fp)) = 0 ⦄ := by
  rw [quadeval.rlin_stmt_loop3]
  apply loop.spec_decr_nat (fun s => ct.val + cz.val - s.2.val)
    (fun s => s.2.val ≤ ct.val + cz.val ∧ s.1.val.length = out.val.length + s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length → s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
        = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val → toRq (s.1.val.getD (out.val.length + t)
          (alloc.vec.Vec.new cpoly.field.Fp)) = 0)
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hpre1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hpre1 hval1
    simp only [quadeval.rlin_stmt_loop3.body]
    step as ⟨nn, hnn⟩
    have hnnv : nn.val = ct.val + cz.val := by rw [hnn]
    by_cases hlt : i1 < nn
    · rw [if_pos hlt]
      have hilt : i1.val < ct.val + cz.val := by rw [← hnnv]; scalar_tac
      step with RqBridge.zero_spec as ⟨r1, hWr1, hr1⟩
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hteq2 : t = i1.val := by omega
          rw [hteq, ho2, getD_append_eq]
          exact hr1
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = ct.val + cz.val := by rw [← hnnv]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · refine ⟨?_, ?_, hwf, ?_, ?_⟩
    · dsimp only; simp
    · dsimp only; simp
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; simp at ht

theorem rlin_c4_zeros_ct_loop_spec (ct : Std.Usize) (out : alloc.vec.Vec ring.Rq)
    (hcap : out.val.length + ct.val ≤ Usize.max) (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.rlin_stmt_loop5 ct out 0#usize
      ⦃ z => z.val.length = out.val.length + (ct.val) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length → z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < ct.val → toRq (z.val.getD (out.val.length + t)
            (alloc.vec.Vec.new cpoly.field.Fp)) = 0 ⦄ := by
  rw [quadeval.rlin_stmt_loop5]
  apply loop.spec_decr_nat (fun s => ct.val - s.2.val)
    (fun s => s.2.val ≤ ct.val ∧ s.1.val.length = out.val.length + s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length → s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
        = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val → toRq (s.1.val.getD (out.val.length + t)
          (alloc.vec.Vec.new cpoly.field.Fp)) = 0)
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hpre1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hpre1 hval1
    simp only [quadeval.rlin_stmt_loop5.body]
    by_cases hlt : i1 < ct
    · rw [if_pos hlt]
      have hilt : i1.val < ct.val := by scalar_tac
      step with RqBridge.zero_spec as ⟨r1, hWr1, hr1⟩
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hteq2 : t = i1.val := by omega
          rw [hteq, ho2, getD_append_eq]
          exact hr1
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = ct.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · refine ⟨?_, ?_, hwf, ?_, ?_⟩
    · dsimp only; simp
    · dsimp only; simp
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; simp at ht

theorem rlin_c5_zeros_cw_loop_spec (cw : Std.Usize) (out : alloc.vec.Vec ring.Rq)
    (hcap : out.val.length + cw.val ≤ Usize.max) (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.rlin_stmt_loop7_loop0 cw out 0#usize
      ⦃ z => z.val.length = out.val.length + (cw.val) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length → z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < cw.val → toRq (z.val.getD (out.val.length + t)
            (alloc.vec.Vec.new cpoly.field.Fp)) = 0 ⦄ := by
  rw [quadeval.rlin_stmt_loop7_loop0]
  apply loop.spec_decr_nat (fun s => cw.val - s.2.val)
    (fun s => s.2.val ≤ cw.val ∧ s.1.val.length = out.val.length + s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length → s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
        = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val → toRq (s.1.val.getD (out.val.length + t)
          (alloc.vec.Vec.new cpoly.field.Fp)) = 0)
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hpre1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hpre1 hval1
    simp only [quadeval.rlin_stmt_loop7_loop0.body]
    by_cases hlt : i1 < cw
    · rw [if_pos hlt]
      have hilt : i1.val < cw.val := by scalar_tac
      step with RqBridge.zero_spec as ⟨r1, hWr1, hr1⟩
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hteq2 : t = i1.val := by omega
          rw [hteq, ho2, getD_append_eq]
          exact hr1
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = cw.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · refine ⟨?_, ?_, hwf, ?_, ?_⟩
    · dsimp only; simp
    · dsimp only; simp
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; simp at ht

theorem rlin_c3_gb_loop_spec {n : ℕ} (cw : Std.Usize) (g_b : linalg.PolyVec)
    (out : alloc.vec.Vec ring.Rq)
    (hg : WfVec n g_b) (hcw : cw.val ≤ n)
    (hcap : out.val.length + cw.val ≤ Usize.max) (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.rlin_stmt_loop2 cw g_b out 0#usize
      ⦃ z => z.val.length = out.val.length + (cw.val) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length → z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < cw.val → toRq (z.val.getD (out.val.length + t)
            (alloc.vec.Vec.new cpoly.field.Fp)) = toRq (g_b.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [quadeval.rlin_stmt_loop2]
  apply loop.spec_decr_nat (fun s => cw.val - s.2.val)
    (fun s => s.2.val ≤ cw.val ∧ s.1.val.length = out.val.length + s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length → s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
        = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val → toRq (s.1.val.getD (out.val.length + t)
          (alloc.vec.Vec.new cpoly.field.Fp)) = toRq (g_b.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hpre1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hpre1 hval1
    simp only [quadeval.rlin_stmt_loop2.body]
    by_cases hlt : i1 < cw
    · rw [if_pos hlt]
      have hilt : i1.val < cw.val := by scalar_tac
      have hidx : i1.val < g_b.val.length := by rw [hg.1]; omega
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hg.2 _ (List.getElem_mem hidx)
      step with RqBridge.copy_spec r hWr as ⟨r1, hWr1, hr1⟩
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hteq2 : t = i1.val := by omega
          rw [hteq, ho2, getD_append_eq, hteq2, hr1, hr,
            ← List.getD_eq_getElem _ _ hidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = cw.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · refine ⟨?_, ?_, hwf, ?_, ?_⟩
    · dsimp only; simp
    · dsimp only; simp
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; simp at ht

theorem rlin_c4_gc_loop_spec {n : ℕ} (cw : Std.Usize) (g_c : linalg.PolyVec)
    (out : alloc.vec.Vec ring.Rq)
    (hg : WfVec n g_c) (hcw : cw.val ≤ n)
    (hcap : out.val.length + cw.val ≤ Usize.max) (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.rlin_stmt_loop4 cw g_c out 0#usize
      ⦃ z => z.val.length = out.val.length + (cw.val) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length → z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < cw.val → toRq (z.val.getD (out.val.length + t)
            (alloc.vec.Vec.new cpoly.field.Fp)) = toRq (g_c.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [quadeval.rlin_stmt_loop4]
  apply loop.spec_decr_nat (fun s => cw.val - s.2.val)
    (fun s => s.2.val ≤ cw.val ∧ s.1.val.length = out.val.length + s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length → s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
        = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val → toRq (s.1.val.getD (out.val.length + t)
          (alloc.vec.Vec.new cpoly.field.Fp)) = toRq (g_c.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hpre1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hpre1 hval1
    simp only [quadeval.rlin_stmt_loop4.body]
    by_cases hlt : i1 < cw
    · rw [if_pos hlt]
      have hilt : i1.val < cw.val := by scalar_tac
      have hidx : i1.val < g_c.val.length := by rw [hg.1]; omega
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hg.2 _ (List.getElem_mem hidx)
      step with RqBridge.copy_spec r hWr as ⟨r1, hWr1, hr1⟩
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hteq2 : t = i1.val := by omega
          rw [hteq, ho2, getD_append_eq, hteq2, hr1, hr,
            ← List.getD_eq_getElem _ _ hidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = cw.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · refine ⟨?_, ?_, hwf, ?_, ?_⟩
    · dsimp only; simp
    · dsimp only; simp
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; simp at ht

theorem rlin_c4_neg_loop_spec {n : ℕ} (cz : Std.Usize) (jt_g_a : linalg.PolyVec)
    (out : alloc.vec.Vec ring.Rq)
    (hj : WfVec n jt_g_a) (hcz : cz.val ≤ n)
    (hcap : out.val.length + cz.val ≤ Usize.max) (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.rlin_stmt_loop6 cz jt_g_a out 0#usize
      ⦃ z => z.val.length = out.val.length + (cz.val) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length → z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < cz.val → toRq (z.val.getD (out.val.length + t)
            (alloc.vec.Vec.new cpoly.field.Fp)) = - toRq (jt_g_a.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [quadeval.rlin_stmt_loop6]
  apply loop.spec_decr_nat (fun s => cz.val - s.2.val)
    (fun s => s.2.val ≤ cz.val ∧ s.1.val.length = out.val.length + s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length → s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
        = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val → toRq (s.1.val.getD (out.val.length + t)
          (alloc.vec.Vec.new cpoly.field.Fp)) = - toRq (jt_g_a.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hpre1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hpre1 hval1
    simp only [quadeval.rlin_stmt_loop6.body]
    by_cases hlt : i1 < cz
    · rw [if_pos hlt]
      have hilt : i1.val < cz.val := by scalar_tac
      have hidx : i1.val < jt_g_a.val.length := by rw [hj.1]; omega
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hj.2 _ (List.getElem_mem hidx)
      step with RqBridge.neg_spec r hWr as ⟨r1, hWr1, hr1⟩
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hteq2 : t = i1.val := by omega
          rw [hteq, ho2, getD_append_eq, hteq2, hr1, hr,
            ← List.getD_eq_getElem _ _ hidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = cz.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · refine ⟨?_, ?_, hwf, ?_, ?_⟩
    · dsimp only; simp
    · dsimp only; simp
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; simp at ht

theorem rlin_c5_neg_loop_spec {n : ℕ} (cz : Std.Usize) (aj : linalg.PolyVec)
    (out : alloc.vec.Vec ring.Rq)
    (ha : WfVec n aj) (hcz : cz.val ≤ n)
    (hcap : out.val.length + cz.val ≤ Usize.max) (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.rlin_stmt_loop7_loop2 cz out aj 0#usize
      ⦃ z => z.val.length = out.val.length + (cz.val) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length → z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < cz.val → toRq (z.val.getD (out.val.length + t)
            (alloc.vec.Vec.new cpoly.field.Fp)) = - toRq (aj.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [quadeval.rlin_stmt_loop7_loop2]
  apply loop.spec_decr_nat (fun s => cz.val - s.2.val)
    (fun s => s.2.val ≤ cz.val ∧ s.1.val.length = out.val.length + s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length → s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
        = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val → toRq (s.1.val.getD (out.val.length + t)
          (alloc.vec.Vec.new cpoly.field.Fp)) = - toRq (aj.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hpre1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hpre1 hval1
    simp only [quadeval.rlin_stmt_loop7_loop2.body]
    by_cases hlt : i1 < cz
    · rw [if_pos hlt]
      have hilt : i1.val < cz.val := by scalar_tac
      have hidx : i1.val < aj.val.length := by rw [ha.1]; omega
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact ha.2 _ (List.getElem_mem hidx)
      step with RqBridge.neg_spec r hWr as ⟨r1, hWr1, hr1⟩
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hteq2 : t = i1.val := by omega
          rw [hteq, ho2, getD_append_eq, hteq2, hr1, hr,
            ← List.getD_eq_getElem _ _ hidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = cz.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · refine ⟨?_, ?_, hwf, ?_, ?_⟩
    · dsimp only; simp
    · dsimp only; simp
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; simp at ht



theorem rlin_c1_row_loop_spec {rows cols : ℕ} (pp : quadeval.PublicParamsD) (cw i : Std.Usize)
    (out : alloc.vec.Vec ring.Rq)
    (hd : WfMat rows cols pp.d_matrix) (hi : i.val < rows) (hcw : cw.val ≤ cols)
    (hcap : out.val.length + cw.val ≤ Usize.max) (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.rlin_stmt_loop0_loop0 pp cw i out 0#usize
      ⦃ z => z.val.length = out.val.length + (cw.val) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length → z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < cw.val → toRq (z.val.getD (out.val.length + t)
            (alloc.vec.Vec.new cpoly.field.Fp)) = toRq ((pp.d_matrix.val.getD i.val (alloc.vec.Vec.new ring.Rq)).val.getD t
          (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [quadeval.rlin_stmt_loop0_loop0]
  apply loop.spec_decr_nat (fun s => cw.val - s.2.val)
    (fun s => s.2.val ≤ cw.val ∧ s.1.val.length = out.val.length + s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length → s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
        = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val → toRq (s.1.val.getD (out.val.length + t)
          (alloc.vec.Vec.new cpoly.field.Fp)) = toRq ((pp.d_matrix.val.getD i.val (alloc.vec.Vec.new ring.Rq)).val.getD t
          (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hpre1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hpre1 hval1
    simp only [quadeval.rlin_stmt_loop0_loop0.body]
    by_cases hlt : i1 < cw
    · rw [if_pos hlt]
      have hilt : i1.val < cw.val := by scalar_tac
      have hrowidx : i.val < pp.d_matrix.val.length := by rw [hd.1]; exact hi
      simp only [quadeval.PublicParamsD.impl.d_matrix, linalg.PolyMatrix.row,
        linalg.PolyVec.get, bind_tc_ok]
      step as ⟨pv, hpv⟩
      have hWpv : WfVec cols pv := by rw [hpv]; exact hd.2 _ (List.getElem_mem hrowidx)
      have hidx : i1.val < pv.val.length := by rw [hWpv.1]; omega
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hWpv.2 _ (List.getElem_mem hidx)
      step with RqBridge.copy_spec r hWr as ⟨r1, hWr1, hr1⟩
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hteq2 : t = i1.val := by omega
          rw [hteq, ho2, getD_append_eq, hteq2, hr1, hr,
            ← List.getD_eq_getElem _ _ hidx, hpv, ← List.getD_eq_getElem _ _ hrowidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = cw.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · refine ⟨?_, ?_, hwf, ?_, ?_⟩
    · dsimp only; simp
    · dsimp only; simp
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; simp at ht

theorem rlin_c2_row_loop_spec {rows cols : ℕ} (pp : quadeval.PublicParamsD) (ct i2 : Std.Usize)
    (out : alloc.vec.Vec ring.Rq)
    (ho : WfMat rows cols pp.inner.outer_matrix) (hi : i2.val < rows) (hct : ct.val ≤ cols)
    (hcap : out.val.length + ct.val ≤ Usize.max) (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.rlin_stmt_loop1_loop1 pp ct i2 out 0#usize
      ⦃ z => z.val.length = out.val.length + (ct.val) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length → z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < ct.val → toRq (z.val.getD (out.val.length + t)
            (alloc.vec.Vec.new cpoly.field.Fp)) = toRq ((pp.inner.outer_matrix.val.getD i2.val (alloc.vec.Vec.new ring.Rq)).val.getD t
          (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [quadeval.rlin_stmt_loop1_loop1]
  apply loop.spec_decr_nat (fun s => ct.val - s.2.val)
    (fun s => s.2.val ≤ ct.val ∧ s.1.val.length = out.val.length + s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length → s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
        = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val → toRq (s.1.val.getD (out.val.length + t)
          (alloc.vec.Vec.new cpoly.field.Fp)) = toRq ((pp.inner.outer_matrix.val.getD i2.val (alloc.vec.Vec.new ring.Rq)).val.getD t
          (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hpre1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hpre1 hval1
    simp only [quadeval.rlin_stmt_loop1_loop1.body]
    by_cases hlt : i1 < ct
    · rw [if_pos hlt]
      have hilt : i1.val < ct.val := by scalar_tac
      have hrowidx : i2.val < pp.inner.outer_matrix.val.length := by rw [ho.1]; exact hi
      simp only [quadeval.PublicParamsD.impl.inner, commit.PublicParams.impl.outer_matrix,
        linalg.PolyMatrix.row, linalg.PolyVec.get, bind_tc_ok]
      step as ⟨pv, hpv⟩
      have hWpv : WfVec cols pv := by rw [hpv]; exact ho.2 _ (List.getElem_mem hrowidx)
      have hidx : i1.val < pv.val.length := by rw [hWpv.1]; omega
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hWpv.2 _ (List.getElem_mem hidx)
      step with RqBridge.copy_spec r hWr as ⟨r1, hWr1, hr1⟩
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hteq2 : t = i1.val := by omega
          rw [hteq, ho2, getD_append_eq, hteq2, hr1, hr,
            ← List.getD_eq_getElem _ _ hidx, hpv, ← List.getD_eq_getElem _ _ hrowidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = ct.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · refine ⟨?_, ?_, hwf, ?_, ?_⟩
    · dsimp only; simp
    · dsimp only; simp
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; simp at ht

theorem rlin_c5_tensor_loop_spec {rows cols : ℕ} (ct p : Std.Usize) (tensor : linalg.PolyMatrix)
    (out : alloc.vec.Vec ring.Rq)
    (ht : WfMat rows cols tensor) (hp : p.val < rows) (hct : ct.val ≤ cols)
    (hcap : out.val.length + ct.val ≤ Usize.max) (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.rlin_stmt_loop7_loop1 ct tensor p out 0#usize
      ⦃ z => z.val.length = out.val.length + (ct.val) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length → z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < ct.val → toRq (z.val.getD (out.val.length + t)
            (alloc.vec.Vec.new cpoly.field.Fp)) = toRq ((tensor.val.getD p.val (alloc.vec.Vec.new ring.Rq)).val.getD t
          (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [quadeval.rlin_stmt_loop7_loop1]
  apply loop.spec_decr_nat (fun s => ct.val - s.2.val)
    (fun s => s.2.val ≤ ct.val ∧ s.1.val.length = out.val.length + s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length → s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
        = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val → toRq (s.1.val.getD (out.val.length + t)
          (alloc.vec.Vec.new cpoly.field.Fp)) = toRq ((tensor.val.getD p.val (alloc.vec.Vec.new ring.Rq)).val.getD t
          (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hpre1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hpre1 hval1
    simp only [quadeval.rlin_stmt_loop7_loop1.body]
    by_cases hlt : i1 < ct
    · rw [if_pos hlt]
      have hilt : i1.val < ct.val := by scalar_tac
      have hrowidx : p.val < tensor.val.length := by rw [ht.1]; exact hp
      simp only [linalg.PolyMatrix.row, linalg.PolyVec.get]
      step as ⟨pv, hpv⟩
      have hWpv : WfVec cols pv := by rw [hpv]; exact ht.2 _ (List.getElem_mem hrowidx)
      have hidx : i1.val < pv.val.length := by rw [hWpv.1]; omega
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hWpv.2 _ (List.getElem_mem hidx)
      step with RqBridge.copy_spec r hWr as ⟨r1, hWr1, hr1⟩
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hteq2 : t = i1.val := by omega
          rw [hteq, ho2, getD_append_eq, hteq2, hr1, hr,
            ← List.getD_eq_getElem _ _ hidx, hpv, ← List.getD_eq_getElem _ _ hrowidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = ct.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · refine ⟨?_, ?_, hwf, ?_, ?_⟩
    · dsimp only; simp
    · dsimp only; simp
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; simp at ht

theorem rlin_y_v_loop_spec {n : ℕ} (v : linalg.PolyVec) (out : alloc.vec.Vec ring.Rq)
    (hv : WfVec n v) (hcap : out.val.length + n ≤ Usize.max) (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.rlin_stmt_loop8 v out 0#usize
      ⦃ z => z.val.length = out.val.length + (n) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length → z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < n → toRq (z.val.getD (out.val.length + t)
            (alloc.vec.Vec.new cpoly.field.Fp)) = toRq (v.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [quadeval.rlin_stmt_loop8]
  apply loop.spec_decr_nat (fun s => n - s.2.val)
    (fun s => s.2.val ≤ n ∧ s.1.val.length = out.val.length + s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length → s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
        = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val → toRq (s.1.val.getD (out.val.length + t)
          (alloc.vec.Vec.new cpoly.field.Fp)) = toRq (v.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hpre1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hpre1 hval1
    simp only [quadeval.rlin_stmt_loop8.body]
    have hnv : (alloc.vec.Vec.len v).val = n := by simpa using hv.1
    simp only [linalg.PolyVec.len, bind_tc_ok]
    by_cases hlt : i1 < alloc.vec.Vec.len v
    · rw [if_pos hlt]
      have hilt : i1.val < n := by rw [← hnv]; scalar_tac
      have hidx : i1.val < v.val.length := by rw [hv.1]; omega
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hv.2 _ (List.getElem_mem hidx)
      step with RqBridge.copy_spec r hWr as ⟨r1, hWr1, hr1⟩
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hteq2 : t = i1.val := by omega
          rw [hteq, ho2, getD_append_eq, hteq2, hr1, hr,
            ← List.getD_eq_getElem _ _ hidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n := by rw [← hnv]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · refine ⟨?_, ?_, hwf, ?_, ?_⟩
    · dsimp only; simp
    · dsimp only; simp
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; simp at ht

theorem rlin_y_u_loop_spec {n : ℕ} (stmt : quadeval.QuadEvalStatement) (out : alloc.vec.Vec ring.Rq)
    (hu : WfVec n stmt.u) (hcap : out.val.length + n ≤ Usize.max) (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.rlin_stmt_loop9 stmt out 0#usize
      ⦃ z => z.val.length = out.val.length + (n) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length → z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < n → toRq (z.val.getD (out.val.length + t)
            (alloc.vec.Vec.new cpoly.field.Fp)) = toRq (stmt.u.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [quadeval.rlin_stmt_loop9]
  apply loop.spec_decr_nat (fun s => n - s.2.val)
    (fun s => s.2.val ≤ n ∧ s.1.val.length = out.val.length + s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length → s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
        = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val → toRq (s.1.val.getD (out.val.length + t)
          (alloc.vec.Vec.new cpoly.field.Fp)) = toRq (stmt.u.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hpre1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hpre1 hval1
    simp only [quadeval.rlin_stmt_loop9.body]
    have hnv : (alloc.vec.Vec.len stmt.u).val = n := by simpa using hu.1
    simp only [quadeval.QuadEvalStatement.impl.u, linalg.PolyVec.len, bind_tc_ok]
    by_cases hlt : i1 < alloc.vec.Vec.len stmt.u
    · rw [if_pos hlt]
      have hilt : i1.val < n := by rw [← hnv]; scalar_tac
      have hidx : i1.val < stmt.u.val.length := by rw [hu.1]; omega
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hu.2 _ (List.getElem_mem hidx)
      step with RqBridge.copy_spec r hWr as ⟨r1, hWr1, hr1⟩
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hteq2 : t = i1.val := by omega
          rw [hteq, ho2, getD_append_eq, hteq2, hr1, hr,
            ← List.getD_eq_getElem _ _ hidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n := by rw [← hnv]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · refine ⟨?_, ?_, hwf, ?_, ?_⟩
    · dsimp only; simp
    · dsimp only; simp
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; simp at ht

theorem rlin_y_repeat_loop_spec (r : ring.Rq) (innerRows : Std.Usize) (out : alloc.vec.Vec ring.Rq)
    (hWr : Wf r) (hcap : out.val.length + innerRows.val ≤ Usize.max)
    (hwf : ∀ y ∈ out.val, Wf y) :
    quadeval.rlin_stmt_loop10 r innerRows out 0#usize
      ⦃ z => z.val.length = out.val.length + (innerRows.val) ∧ (∀ y ∈ z.val, Wf y) ∧
        (∀ t, t < out.val.length → z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
        ∀ t, t < innerRows.val → toRq (z.val.getD (out.val.length + t)
            (alloc.vec.Vec.new cpoly.field.Fp)) = toRq r ⦄ := by
  rw [quadeval.rlin_stmt_loop10]
  apply loop.spec_decr_nat (fun s => innerRows.val - s.2.val)
    (fun s => s.2.val ≤ innerRows.val ∧ s.1.val.length = out.val.length + s.2.val ∧
      (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t, t < out.val.length → s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
        = out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ∧
      ∀ t, t < s.2.val → toRq (s.1.val.getD (out.val.length + t)
          (alloc.vec.Vec.new cpoly.field.Fp)) = toRq r)
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hpre1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hpre1 hval1
    simp only [quadeval.rlin_stmt_loop10.body]
    by_cases hlt : i1 < innerRows
    · rw [if_pos hlt]
      have hilt : i1.val < innerRows.val := by scalar_tac
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 t ht
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 t htlt
        · have hteq : out.val.length + t = o1.val.length := by omega
          have hteq2 : t = i1.val := by omega
          rw [hteq, ho2, getD_append_eq]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = innerRows.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · refine ⟨?_, ?_, hwf, ?_, ?_⟩
    · dsimp only; simp
    · dsimp only; simp
    · dsimp only; intro t _; rfl
    · dsimp only; intro t ht; simp at ht


/-- The `c1` row loop: `dRows` rows of `[ D | 0 ]`. -/
theorem rlin_c1_outer_loop_spec {rows cols : ℕ} (pp : quadeval.PublicParamsD)
    (cw ct cz : Std.Usize) (out : alloc.vec.Vec linalg.PolyVec) (i : Std.Usize)
    (hd : WfMat rows cols pp.d_matrix) (hcw : cw.val ≤ cols)
    (hsum : ct.val + cz.val ≤ Usize.max)
    (hwidth : cw.val + (ct.val + cz.val) ≤ Usize.max)
    (hi : i.val ≤ rows) (hlen : out.val.length = i.val)
    (hwf : ∀ x ∈ out.val, WfVec (cw.val + (ct.val + cz.val)) x)
    (hval : ∀ u, u < i.val → ∀ t, t < cw.val + (ct.val + cz.val) →
      toRq ((out.val.getD u (alloc.vec.Vec.new ring.Rq)).val.getD t
          (alloc.vec.Vec.new cpoly.field.Fp))
        = if t < cw.val then
            toRq ((pp.d_matrix.val.getD u (alloc.vec.Vec.new ring.Rq)).val.getD t
              (alloc.vec.Vec.new cpoly.field.Fp))
          else 0) :
    quadeval.rlin_stmt_loop0 pp cw ct cz out i
      ⦃ z => z.val.length = rows ∧ (∀ x ∈ z.val, WfVec (cw.val + (ct.val + cz.val)) x) ∧
        ∀ u, u < rows → ∀ t, t < cw.val + (ct.val + cz.val) →
          toRq ((z.val.getD u (alloc.vec.Vec.new ring.Rq)).val.getD t
              (alloc.vec.Vec.new cpoly.field.Fp))
            = if t < cw.val then
                toRq ((pp.d_matrix.val.getD u (alloc.vec.Vec.new ring.Rq)).val.getD t
                  (alloc.vec.Vec.new cpoly.field.Fp))
              else 0 ⦄ := by
  have hdrows : pp.d_matrix.val.length = rows := hd.1
  have hrowscap : rows ≤ Usize.max := by rw [← hdrows]; exact pp.d_matrix.property
  rw [quadeval.rlin_stmt_loop0]
  apply loop.spec_decr_nat (fun s => rows - s.2.val)
    (fun s => s.2.val ≤ rows ∧ s.1.val.length = s.2.val ∧
      (∀ x ∈ s.1.val, WfVec (cw.val + (ct.val + cz.val)) x) ∧
      ∀ u, u < s.2.val → ∀ t, t < cw.val + (ct.val + cz.val) →
        toRq ((s.1.val.getD u (alloc.vec.Vec.new ring.Rq)).val.getD t
            (alloc.vec.Vec.new cpoly.field.Fp))
          = if t < cw.val then
              toRq ((pp.d_matrix.val.getD u (alloc.vec.Vec.new ring.Rq)).val.getD t
                (alloc.vec.Vec.new cpoly.field.Fp))
            else 0)
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [quadeval.rlin_stmt_loop0.body, quadeval.PublicParamsD.impl.d_matrix,
      linalg.PolyMatrix.rows, bind_tc_ok]
    have hnr : (alloc.vec.Vec.len pp.d_matrix).val = rows := by simpa using hdrows
    by_cases hlt : i1 < alloc.vec.Vec.len pp.d_matrix
    · rw [if_pos hlt]
      have hi1lt : i1.val < rows := by rw [← hnr]; scalar_tac
      step with rlin_c1_row_loop_spec pp cw i1 (alloc.vec.Vec.new ring.Rq) hd hi1lt hcw
        (by simp; omega) (by intro y hy; simp at hy) as ⟨row, hrlen, hrwf, _, hrval⟩
      simp only [alloc.vec.Vec.new, List.length_nil, Nat.zero_add] at hrlen hrval
      step with rlin_c1_zeros_loop_spec ct cz row hsum (by rw [hrlen]; exact hwidth) hrwf
        as ⟨row1, h1len, h1wf, h1pre, h1val⟩
      rw [hrlen] at h1len h1val
      simp only [linalg.PolyVec.new]
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      have hrowval : ∀ t, t < cw.val + (ct.val + cz.val) →
          toRq (row1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = if t < cw.val then
                toRq ((pp.d_matrix.val.getD i1.val (alloc.vec.Vec.new ring.Rq)).val.getD t
                  (alloc.vec.Vec.new cpoly.field.Fp))
              else 0 := by
        intro t ht
        by_cases hlt2 : t < cw.val
        · rw [if_pos hlt2, h1pre t (by rw [hrlen]; omega), hrval t hlt2]
        · rw [if_neg hlt2]
          have h := h1val (t - cw.val) (by omega)
          rw [show cw.val + (t - cw.val) = t from by omega] at h
          exact h
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro x hx
        rw [ho2] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hwf1 x h
        · rw [List.mem_singleton.mp h]; exact ⟨h1len, h1wf⟩
      · intro u hu t ht
        rw [hi2] at hu
        rcases Nat.lt_or_ge u i1.val with hult | huge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 u hult t ht
        · have hueq : u = o1.val.length := by omega
          rw [hueq, ho2, getD_append_eq, hlen1]
          exact hrowval t ht
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = rows := by rw [← hnr]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, fun u hu t ht => hval1 u (by rw [heq]; exact hu) t ht⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- The `c2` row loop: `outerRows` rows of `[ 0 | B | 0 ]`. -/
theorem rlin_c2_outer_loop_spec {rows cols : ℕ} (pp : quadeval.PublicParamsD)
    (cw ct cz : Std.Usize) (out : alloc.vec.Vec linalg.PolyVec)
    (ho : WfMat rows cols pp.inner.outer_matrix) (hct : ct.val ≤ cols)
    (hwidth : cw.val + (ct.val + cz.val) ≤ Usize.max)
    (hcap : out.val.length + rows ≤ Usize.max)
    (hwf : ∀ x ∈ out.val, WfVec (cw.val + (ct.val + cz.val)) x) :
    quadeval.rlin_stmt_loop1 pp cw ct cz out 0#usize
      ⦃ z => z.val.length = out.val.length + rows ∧
        (∀ x ∈ z.val, WfVec (cw.val + (ct.val + cz.val)) x) ∧
        (∀ u, u < out.val.length →
          z.val.getD u (alloc.vec.Vec.new ring.Rq)
            = out.val.getD u (alloc.vec.Vec.new ring.Rq)) ∧
        ∀ u, u < rows → ∀ t, t < cw.val + (ct.val + cz.val) →
          toRq ((z.val.getD (out.val.length + u) (alloc.vec.Vec.new ring.Rq)).val.getD t
              (alloc.vec.Vec.new cpoly.field.Fp))
            = if t < cw.val then 0
              else if t < cw.val + ct.val then
                toRq ((pp.inner.outer_matrix.val.getD u (alloc.vec.Vec.new ring.Rq)).val.getD
                  (t - cw.val) (alloc.vec.Vec.new cpoly.field.Fp))
              else 0 ⦄ := by
  have horows : pp.inner.outer_matrix.val.length = rows := ho.1
  rw [quadeval.rlin_stmt_loop1]
  apply loop.spec_decr_nat (fun s => rows - s.2.val)
    (fun s => s.2.val ≤ rows ∧ s.1.val.length = out.val.length + s.2.val ∧
      (∀ x ∈ s.1.val, WfVec (cw.val + (ct.val + cz.val)) x) ∧
      (∀ u, u < out.val.length →
        s.1.val.getD u (alloc.vec.Vec.new ring.Rq)
          = out.val.getD u (alloc.vec.Vec.new ring.Rq)) ∧
      ∀ u, u < s.2.val → ∀ t, t < cw.val + (ct.val + cz.val) →
        toRq ((s.1.val.getD (out.val.length + u) (alloc.vec.Vec.new ring.Rq)).val.getD t
            (alloc.vec.Vec.new cpoly.field.Fp))
          = if t < cw.val then 0
            else if t < cw.val + ct.val then
              toRq ((pp.inner.outer_matrix.val.getD u (alloc.vec.Vec.new ring.Rq)).val.getD
                (t - cw.val) (alloc.vec.Vec.new cpoly.field.Fp))
            else 0)
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hpre1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hpre1 hval1
    simp only [quadeval.rlin_stmt_loop1.body, quadeval.PublicParamsD.impl.inner,
      commit.PublicParams.impl.outer_matrix, linalg.PolyMatrix.rows, bind_tc_ok]
    have hnr : (alloc.vec.Vec.len pp.inner.outer_matrix).val = rows := by simpa using horows
    by_cases hlt : i1 < alloc.vec.Vec.len pp.inner.outer_matrix
    · rw [if_pos hlt]
      have hi1lt : i1.val < rows := by rw [← hnr]; scalar_tac
      step with rlin_c2_zeros_cw_loop_spec cw (alloc.vec.Vec.new ring.Rq)
        (by simp; omega) (by intro y hy; simp at hy) as ⟨rowa, halen, hawf, _, haval⟩
      simp only [alloc.vec.Vec.new, List.length_nil, Nat.zero_add] at halen haval
      step with rlin_c2_row_loop_spec pp ct i1 rowa ho hi1lt hct
        (by rw [halen]; omega) hawf as ⟨rowb, hblen, hbwf, hbpre, hbval⟩
      rw [halen] at hblen hbval
      step with rlin_c2_zeros_cz_loop_spec cz rowb (by rw [hblen]; omega) hbwf
        as ⟨rowc, hclen, hcwf, hcpre, hcval⟩
      rw [hblen] at hclen hcval
      simp only [linalg.PolyVec.new]
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      have hrowval : ∀ t, t < cw.val + (ct.val + cz.val) →
          toRq (rowc.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = if t < cw.val then 0
              else if t < cw.val + ct.val then
                toRq ((pp.inner.outer_matrix.val.getD i1.val
                  (alloc.vec.Vec.new ring.Rq)).val.getD (t - cw.val)
                  (alloc.vec.Vec.new cpoly.field.Fp))
              else 0 := by
        intro t ht
        by_cases hlt2 : t < cw.val
        · rw [if_pos hlt2, hcpre t (by rw [hblen]; omega),
            hbpre t (by rw [halen]; omega), haval t hlt2]
        · rw [if_neg hlt2]
          by_cases hlt3 : t < cw.val + ct.val
          · rw [if_pos hlt3, hcpre t (by rw [hblen]; omega)]
            have h := hbval (t - cw.val) (by omega)
            rw [show cw.val + (t - cw.val) = t from by omega] at h
            exact h
          · rw [if_neg hlt3]
            have h := hcval (t - (cw.val + ct.val)) (by omega)
            rw [show cw.val + ct.val + (t - (cw.val + ct.val)) = t from by omega] at h
            exact h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro x hx
        rw [ho2] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hwf1 x h
        · rw [List.mem_singleton.mp h]
          exact ⟨by rw [hclen]; ring, hcwf⟩
      · intro u hu
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 u hu
      · intro u hu t ht
        rw [hi2] at hu
        rcases Nat.lt_or_ge u i1.val with hult | huge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 u hult t ht
        · have hueq : u = i1.val := by omega
          subst hueq
          rw [← hlen1, ho2, getD_append_eq]
          exact hrowval t ht
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = rows := by rw [← hnr]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1,
        fun u hu t ht => hval1 u (by rw [heq]; exact hu) t ht⟩
  · refine ⟨by scalar_tac, by scalar_tac, hwf, fun u _ => rfl, ?_⟩
    intro u hu
    exact absurd hu (by scalar_tac)

/-- The `c5` row loop: `innerRows` rows of `[ 0 | (cᵀ ⊗ G) | −(A J) ]`, the last
block computed as `Jᵀ` applied to the row of `A`. -/
theorem rlin_c5_outer_loop_spec {rowsT colsT rowsA zd : ℕ} (pp : quadeval.PublicParamsD)
    (innerRowsU zDigits cw ct cz innerCols : Std.Usize) (tensor : linalg.PolyMatrix)
    (out : alloc.vec.Vec linalg.PolyVec)
    (ht : WfMat rowsT colsT tensor) (hct : ct.val ≤ colsT) (hpT : innerRowsU.val ≤ rowsT)
    (hA : WfMat rowsA innerCols.val pp.inner.inner_matrix) (hpA : innerRowsU.val ≤ rowsA)
    (hzd : zDigits.val = zd) (hfit : innerCols.val * zd ≤ Usize.max)
    (hcz : cz.val ≤ innerCols.val * zd)
    (hwidth : cw.val + (ct.val + cz.val) ≤ Usize.max)
    (hcap : out.val.length + innerRowsU.val ≤ Usize.max)
    (hwf : ∀ x ∈ out.val, WfVec (cw.val + (ct.val + cz.val)) x) :
    quadeval.rlin_stmt_loop7 pp innerRowsU zDigits cw ct cz innerCols tensor out 0#usize
      ⦃ z => z.val.length = out.val.length + innerRowsU.val ∧
        (∀ x ∈ z.val, WfVec (cw.val + (ct.val + cz.val)) x) ∧
        (∀ u, u < out.val.length →
          z.val.getD u (alloc.vec.Vec.new ring.Rq)
            = out.val.getD u (alloc.vec.Vec.new ring.Rq)) ∧
        ∀ u, u < innerRowsU.val → ∀ t, t < cw.val + (ct.val + cz.val) →
          toRq ((z.val.getD (out.val.length + u) (alloc.vec.Vec.new ring.Rq)).val.getD t
              (alloc.vec.Vec.new cpoly.field.Fp))
            = if t < cw.val then 0
              else if t < cw.val + ct.val then
                toRq ((tensor.val.getD u (alloc.vec.Vec.new ring.Rq)).val.getD (t - cw.val)
                  (alloc.vec.Vec.new cpoly.field.Fp))
              else - gtmVal zd (pp.inner.inner_matrix.val.getD u (alloc.vec.Vec.new ring.Rq))
                  (t - (cw.val + ct.val)) ⦄ := by
  rw [quadeval.rlin_stmt_loop7]
  apply loop.spec_decr_nat (fun s => innerRowsU.val - s.2.val)
    (fun s => s.2.val ≤ innerRowsU.val ∧ s.1.val.length = out.val.length + s.2.val ∧
      (∀ x ∈ s.1.val, WfVec (cw.val + (ct.val + cz.val)) x) ∧
      (∀ u, u < out.val.length →
        s.1.val.getD u (alloc.vec.Vec.new ring.Rq)
          = out.val.getD u (alloc.vec.Vec.new ring.Rq)) ∧
      ∀ u, u < s.2.val → ∀ t, t < cw.val + (ct.val + cz.val) →
        toRq ((s.1.val.getD (out.val.length + u) (alloc.vec.Vec.new ring.Rq)).val.getD t
            (alloc.vec.Vec.new cpoly.field.Fp))
          = if t < cw.val then 0
            else if t < cw.val + ct.val then
              toRq ((tensor.val.getD u (alloc.vec.Vec.new ring.Rq)).val.getD (t - cw.val)
                (alloc.vec.Vec.new cpoly.field.Fp))
            else - gtmVal zd (pp.inner.inner_matrix.val.getD u (alloc.vec.Vec.new ring.Rq))
                (t - (cw.val + ct.val)))
  · rintro ⟨o1, p1⟩ ⟨hp1, hlen1, hwf1, hpre1, hval1⟩
    dsimp only at hp1 hlen1 hwf1 hpre1 hval1
    simp only [quadeval.rlin_stmt_loop7.body]
    by_cases hlt : p1 < innerRowsU
    · rw [if_pos hlt]
      have hp1lt : p1.val < innerRowsU.val := by scalar_tac
      step with rlin_c5_zeros_cw_loop_spec cw (alloc.vec.Vec.new ring.Rq)
        (by simp; omega) (by intro y hy; simp at hy) as ⟨rowa, halen, hawf, _, haval⟩
      simp only [alloc.vec.Vec.new, List.length_nil, Nat.zero_add] at halen haval
      step with rlin_c5_tensor_loop_spec ct p1 tensor rowa ht (by omega) hct
        (by rw [halen]; omega) hawf as ⟨rowb, hblen, hbwf, hbpre, hbval⟩
      rw [halen] at hblen hbval
      simp only [quadeval.PublicParamsD.impl.inner, commit.PublicParams.impl.inner_matrix,
        linalg.PolyMatrix.row, bind_tc_ok]
      have hArow : p1.val < pp.inner.inner_matrix.val.length := by rw [hA.1]; omega
      step as ⟨pv, hpv⟩
      have hWpv : WfVec innerCols.val pv := by
        rw [hpv]; exact hA.2 _ (List.getElem_mem hArow)
      step with gadget_transpose_mul_entry_spec (rows := innerCols.val) (digits := zd)
        innerCols zDigits pv hWpv rfl hzd hfit as ⟨aj, hajwf, hajval⟩
      step with rlin_c5_neg_loop_spec cz aj rowb hajwf hcz (by rw [hblen]; omega) hbwf
        as ⟨rowc, hclen, hcwf, hcpre, hcval⟩
      rw [hblen] at hclen hcval
      simp only [linalg.PolyVec.new]
      have hcap1 : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨p2, hp2⟩
      have hrowval : ∀ t, t < cw.val + (ct.val + cz.val) →
          toRq (rowc.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = if t < cw.val then 0
              else if t < cw.val + ct.val then
                toRq ((tensor.val.getD p1.val (alloc.vec.Vec.new ring.Rq)).val.getD
                  (t - cw.val) (alloc.vec.Vec.new cpoly.field.Fp))
              else - gtmVal zd (pp.inner.inner_matrix.val.getD p1.val
                  (alloc.vec.Vec.new ring.Rq)) (t - (cw.val + ct.val)) := by
        intro t ht
        by_cases hlt2 : t < cw.val
        · rw [if_pos hlt2, hcpre t (by rw [hblen]; omega),
            hbpre t (by rw [halen]; omega), haval t hlt2]
        · rw [if_neg hlt2]
          by_cases hlt3 : t < cw.val + ct.val
          · rw [if_pos hlt3, hcpre t (by rw [hblen]; omega)]
            have h := hbval (t - cw.val) (by omega)
            rw [show cw.val + (t - cw.val) = t from by omega] at h
            exact h
          · rw [if_neg hlt3]
            have h := hcval (t - (cw.val + ct.val)) (by omega)
            rw [show cw.val + ct.val + (t - (cw.val + ct.val)) = t from by omega] at h
            rw [h, hajval (t - (cw.val + ct.val)) (by omega), hpv,
              ← List.getD_eq_getElem _ _ hArow]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · scalar_tac
      · rw [ho2, hp2, List.length_append, hlen1]
        simp only [List.length_cons, List.length_nil]
        omega
      · intro x hx
        rw [ho2] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hwf1 x h
        · rw [List.mem_singleton.mp h]
          exact ⟨by rw [hclen]; ring, hcwf⟩
      · intro u hu
        rw [ho2, getD_append_lt _ _ _ (by omega)]
        exact hpre1 u hu
      · intro u hu t ht
        rw [hp2] at hu
        rcases Nat.lt_or_ge u p1.val with hult | huge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 u hult t ht
        · have hueq : u = p1.val := by omega
          subst hueq
          rw [← hlen1, ho2, getD_append_eq]
          exact hrowval t ht
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : p1.val = innerRowsU.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1,
        fun u hu t ht => hval1 u (by rw [heq]; exact hu) t ht⟩
  · refine ⟨by scalar_tac, by scalar_tac, hwf, fun u _ => rfl, ?_⟩
    intro u hu
    exact absurd hu (by scalar_tac)

/-! ## Two `matMul` bridges

`ArkLib.Lattices.matMul` is the standalone computable product
`fun i k => dot (M i) (fun j => N j k)`, not Mathlib's `Matrix.mul`, so
`Matrix.transpose_mul` does not apply to it and no transpose law for it exists
upstream. The two facts the `c4` and `c5` blocks need are proved here directly
from `matMul_apply` and `Finset.sum_comm`. -/

/-- Transposing a `matMul` and applying it to a vector is applying the two
transposes in the opposite order: `(M N)ᵀ v = Nᵀ (Mᵀ v)`. This is the bridge
between the specification's `c4` block `(G_{2^m} J)ᵀ a` and the reshaped form
`Jᵀ (G_{2^m}ᵀ a)` that the extracted code computes. -/
theorem matMul_transpose_mulVec {P : Type} [CommSemiring P] {a b c : ℕ}
    (M : PolyMatrix P a b) (N : PolyMatrix P b c) (v : PolyVec P a) :
    (matMul M N).transpose *ᵥ v = N.transpose *ᵥ (M.transpose *ᵥ v) := by
  funext k
  simp only [matVecMul_apply, dot_eq_sum, Matrix.transpose_apply, matMul_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- A row of a `matMul` is the second factor's transpose applied to the first
factor's row: the `c5` block `(A J) p` is `Jᵀ (A p)`. -/
theorem matMul_row {P : Type} [CommSemiring P] {a b c : ℕ}
    (M : PolyMatrix P a b) (N : PolyMatrix P b c) (p : Fin a) :
    matMul M N p = N.transpose *ᵥ (M p) := by
  funext k
  simp only [matVecMul_apply, dot_eq_sum, Matrix.transpose_apply, matMul_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

set_option maxHeartbeats 2000000 in
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
  obtain ⟨hWinner, hWd, hparams, hdmat⟩ := hpp
  obtain ⟨hWu, hWa, hWb, hWy, hsu, hsa, hsb, hsy⟩ := hst
  have hWA : WfMat 1 (1024 * 8) pp.inner.inner_matrix := hWinner.1
  have hWB : WfMat 1 (1024 * (1 * 8)) pp.inner.outer_matrix := hWinner.2
  rw [quadeval.rlin_stmt]
  step with rlin_cw_spec b md hb hmd (by scalar_tac) as ⟨cw, hcwv⟩
  step with rlin_ct_spec b ir idg hb hir hidg (by scalar_tac) (by scalar_tac) as ⟨ct, hctv⟩
  step with rlin_cz_spec mr md zd hmr hmd hzd (by scalar_tac) (by scalar_tac) as ⟨cz, hczv⟩
  have hmul : mr.val * md.val ≤ Usize.max := by rw [hmr, hmd]; scalar_tac
  step as ⟨innerCols, hicv0⟩
  have hicv : innerCols.val = 2 ^ 10 * 8 := by rw [hicv0, hmr, hmd]
  have hwidth : cw.val + (ct.val + cz.val) ≤ Usize.max := by
    rw [hcwv, hctv, hczv]; scalar_tac
  simp only [quadeval.QuadEvalStatement.impl.avec, quadeval.QuadEvalStatement.impl.bvec,
    quadeval.QuadEvalStatement.impl.y, bind_tc_ok]
  step with gadget_transpose_mul_spec (rows := 2 ^ 10) (digits := 8) mr md stmt.avec hWa hmr hmd
    (by scalar_tac) as ⟨g_a, hWga, hgav⟩
  step with gadget_transpose_mul_spec (rows := 2 ^ 10 * 8) (digits := 5) innerCols zd g_a hWga
    hicv hzd (by scalar_tac) as ⟨jtga, hWjt, hjtv⟩
  step with gadget_transpose_mul_spec (rows := 2 ^ 10) (digits := 8) b md stmt.bvec hWb hb hmd
    (by scalar_tac) as ⟨g_b, hWgb, hgbv⟩
  step with gadget_transpose_mul_spec (rows := 2 ^ 10) (digits := 8) b md c hc hb hmd
    (by scalar_tac) as ⟨g_c, hWgc, hgcv⟩
  step with tensor_g_matrix_spec (k := 1) (digits := 8) (blocks := 2 ^ 10) ir idg c hir hidg hc
    (by scalar_tac) as ⟨tensor, hWt, htv⟩
  -- c1: the `D` row block
  step with rlin_c1_outer_loop_spec (rows := 1) (cols := 2 ^ 10 * 8) pp cw ct cz
    (alloc.vec.Vec.new linalg.PolyVec) 0#usize hWd (le_of_eq hcwv)
    (by rw [hctv, hczv]; scalar_tac) hwidth (by simp) (by simp)
    (by intro x hx; simp at hx) (by intro u hu; simp at hu) as ⟨o0, h0len, h0wf, h0val⟩
  -- c2: the `B` row block
  step with rlin_c2_outer_loop_spec (rows := 1) (cols := 2 ^ 10 * (1 * 8)) pp cw ct cz o0 hWB
    (le_of_eq hctv) hwidth (by rw [h0len]; scalar_tac) h0wf
    as ⟨o1, h1len, h1wf, h1pre, h1val⟩
  rw [h0len] at h1len h1val
  -- c3: the `(G_{2^r})ᵀ b` row
  step with rlin_c3_gb_loop_spec (n := 2 ^ 10 * 8) cw g_b (alloc.vec.Vec.new ring.Rq) hWgb
    (le_of_eq hcwv) (by simp only [List.length_nil, Nat.zero_add]; omega)
    (by intro y hy; simp at hy) as ⟨row3, h3len, h3wf, _, h3val⟩
  have hnewR : (alloc.vec.Vec.new ring.Rq).val.length = 0 := rfl
  rw [hnewR] at h3len h3val
  simp only [Nat.zero_add] at h3len h3val
  step with rlin_c3_zeros_loop_spec ct cz row3 (by rw [hctv, hczv]; scalar_tac)
    (by rw [h3len]; omega) h3wf as ⟨row31, h31len, h31wf, h31pre, h31val⟩
  rw [h3len] at h31len h31val h31pre
  simp only [linalg.PolyVec.new]
  have hcapo1 : o1.val.length < Usize.max := by rw [h1len]; scalar_tac
  step as ⟨o2, ho2v⟩
  -- c4: the `(G_{2^r})ᵀ c | 0 | −Jᵀ(G_{2^m}ᵀ a)` row
  step with rlin_c4_gc_loop_spec (n := 2 ^ 10 * 8) cw g_c (alloc.vec.Vec.new ring.Rq) hWgc
    (le_of_eq hcwv) (by simp only [List.length_nil, Nat.zero_add]; omega)
    (by intro y hy; simp at hy) as ⟨row4, h4len, h4wf, _, h4val⟩
  rw [hnewR] at h4len h4val
  simp only [Nat.zero_add] at h4len h4val
  step with rlin_c4_zeros_ct_loop_spec ct row4 (by rw [h4len]; omega) h4wf
    as ⟨row41, h41len, h41wf, h41pre, h41val⟩
  rw [h4len] at h41len h41val h41pre
  step with rlin_c4_neg_loop_spec (n := 2 ^ 10 * 8 * 5) cz jtga row41 hWjt (le_of_eq hczv)
    (by rw [h41len]; omega) h41wf as ⟨row42, h42len, h42wf, h42pre, h42val⟩
  rw [h41len] at h42len h42val h42pre
  have hcapo2 : o2.val.length < Usize.max := by
    rw [ho2v, List.length_append, h1len]
    simp only [List.length_cons, List.length_nil]
    scalar_tac
  step as ⟨o3, ho3v⟩
  -- c5: the tensor rows
  have ho3len : o3.val.length = 4 := by
    rw [ho3v, ho2v, List.length_append, List.length_append, h1len]
    simp only [List.length_cons, List.length_nil]
  step with rlin_c5_outer_loop_spec (rowsT := 1) (colsT := 2 ^ 10 * (1 * 8)) (rowsA := 1)
    (zd := 5) pp ir zd cw ct cz innerCols tensor o3 hWt (le_of_eq hctv) (le_of_eq hir)
    (by rw [hicv]; exact hWA) (le_of_eq hir) hzd (by rw [hicv]; scalar_tac)
    (by rw [hczv, hicv]) hwidth (by rw [ho3len, hir]; scalar_tac)
    (by
      intro x hx
      rw [ho3v] at hx
      rcases List.mem_append.mp hx with h | h
      · rw [ho2v] at h
        rcases List.mem_append.mp h with h2 | h2
        · exact h1wf x h2
        · rw [List.mem_singleton.mp h2]
          exact ⟨h31len, h31wf⟩
      · rw [List.mem_singleton.mp h]
        exact ⟨by rw [h42len]; ring, h42wf⟩)
    as ⟨o4, h7len, h7wf, h7pre, h7val⟩
  rw [ho3len, hir] at h7len h7val
  -- the right-hand side
  step with rlin_y_v_loop_spec (n := 1) v (alloc.vec.Vec.new ring.Rq) hv
    (by simp only [List.length_nil, Nat.zero_add]; scalar_tac)
    (by intro y hy; simp at hy) as ⟨y0, hy0len, hy0wf, _, hy0val⟩
  rw [hnewR] at hy0len hy0val
  simp only [Nat.zero_add] at hy0len hy0val
  step with rlin_y_u_loop_spec (n := 1) stmt y0 hWu (by rw [hy0len]; scalar_tac) hy0wf
    as ⟨y1, hy1len, hy1wf, hy1pre, hy1val⟩
  rw [hy0len] at hy1len hy1val hy1pre
  step with RqBridge.copy_spec stmt.y hWy as ⟨r1, hWr1, hr1v⟩
  have hcapy1 : y1.val.length < Usize.max := by rw [hy1len]; scalar_tac
  step as ⟨y2, hy2v⟩
  step with RqBridge.zero_spec as ⟨r2, hWr2, hr2v⟩
  have hy2len : y2.val.length = 3 := by
    rw [hy2v, List.length_append, hy1len]
    simp only [List.length_cons, List.length_nil]
  have hcapy2 : y2.val.length < Usize.max := by rw [hy2len]; scalar_tac
  step as ⟨y3, hy3v⟩
  have hy3len : y3.val.length = 4 := by
    rw [hy3v, List.length_append, hy2len]
    simp only [List.length_cons, List.length_nil]
  step with rlin_y_repeat_loop_spec r2 ir y3 hWr2 (by rw [hy3len, hir]; scalar_tac)
    (by
      intro y hy
      rw [hy3v] at hy
      rcases List.mem_append.mp hy with h | h
      · rw [hy2v] at h
        rcases List.mem_append.mp h with h2 | h2
        · exact hy1wf y h2
        · rw [List.mem_singleton.mp h2]; exact hWr1
      · rw [List.mem_singleton.mp h]; exact hWr2)
    as ⟨y4, hy4len, hy4wf, hy4pre, hy4val⟩
  rw [hy3len, hir] at hy4len hy4val
  simp only [linalg.PolyMatrix.new]
  simp only [bind_tc_ok]
  -- the specification's public matrices, read off the parameter relation
  have houter : toMat (rows := 1) (cols := 2 ^ 10 * (1 * 8)) pp.inner.outer_matrix
      = sp.outerMatrix := congrArg InnerOuter.PublicParams.outerMatrix hparams
  have hinner : toMat (rows := 1) (cols := 2 ^ 10 * 8) pp.inner.inner_matrix
      = sp.innerMatrix := congrArg InnerOuter.PublicParams.innerMatrix hparams
  have hcvec : (fun i : Fin (2 ^ 10) => (toChals c hcn i).val) = toVec (k := 2 ^ 10) c := rfl
  rw [hsa] at hgav
  rw [hgav] at hjtv
  rw [hsb] at hgbv
  -- the five rows of the assembled matrix
  have ho2len : o2.val.length = 3 := by
    rw [ho2v, List.length_append, h1len]
    simp only [List.length_cons, List.length_nil]
  have hR0 : o4.val.getD 0 (alloc.vec.Vec.new ring.Rq)
      = o0.val.getD 0 (alloc.vec.Vec.new ring.Rq) := by
    rw [h7pre 0 (by omega), ho3v, getD_append_lt _ _ _ (by omega), ho2v,
      getD_append_lt _ _ _ (by omega), h1pre 0 (by omega)]
  have hR1 : o4.val.getD 1 (alloc.vec.Vec.new ring.Rq)
      = o1.val.getD 1 (alloc.vec.Vec.new ring.Rq) := by
    rw [h7pre 1 (by omega), ho3v, getD_append_lt _ _ _ (by omega), ho2v,
      getD_append_lt _ _ _ (by omega)]
  have hR2 : o4.val.getD 2 (alloc.vec.Vec.new ring.Rq) = row31 := by
    have h2 : o1.val.length = 2 := by omega
    rw [h7pre 2 (by omega), ho3v, getD_append_lt _ _ _ (by omega), ho2v, ← h2]
    exact getD_append_eq _ _ _
  have hR3 : o4.val.getD 3 (alloc.vec.Vec.new ring.Rq) = row42 := by
    rw [h7pre 3 (by omega), ho3v, ← ho2len]
    exact getD_append_eq _ _ _
  have h0val0 := h0val 0 (by omega)
  have h1val0 := h1val 0 (by omega)
  have h7val0 := h7val 0 (by omega)
  simp only [Nat.add_zero] at h1val0 h7val0
  rw [← hR0] at h0val0
  rw [← hR1] at h1val0
  have hrow2 : ∀ t, t < cw.val + (ct.val + cz.val) →
      toRq ((o4.val.getD 2 (alloc.vec.Vec.new ring.Rq)).val.getD t
          (alloc.vec.Vec.new cpoly.field.Fp))
        = if t < cw.val then toRq (g_b.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          else 0 := by
    intro t ht
    rw [hR2]
    by_cases hlt : t < cw.val
    · rw [if_pos hlt, h31pre t hlt, h3val t hlt]
    · rw [if_neg hlt]
      have h := h31val (t - cw.val) (by omega)
      rw [show cw.val + (t - cw.val) = t from by omega] at h
      exact h
  have hrow3 : ∀ t, t < cw.val + (ct.val + cz.val) →
      toRq ((o4.val.getD 3 (alloc.vec.Vec.new ring.Rq)).val.getD t
          (alloc.vec.Vec.new cpoly.field.Fp))
        = if t < cw.val then toRq (g_c.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          else if t < cw.val + ct.val then 0
          else - toRq (jtga.val.getD (t - (cw.val + ct.val))
            (alloc.vec.Vec.new cpoly.field.Fp)) := by
    intro t ht
    rw [hR3]
    by_cases hlt : t < cw.val
    · rw [if_pos hlt, h42pre t (by omega), h41pre t hlt, h4val t hlt]
    · rw [if_neg hlt]
      by_cases hlt2 : t < cw.val + ct.val
      · rw [if_pos hlt2, h42pre t hlt2]
        have h := h41val (t - cw.val) (by omega)
        rw [show cw.val + (t - cw.val) = t from by omega] at h
        exact h
      · rw [if_neg hlt2]
        have h := h42val (t - (cw.val + ct.val)) (by omega)
        rw [show cw.val + ct.val + (t - (cw.val + ct.val)) = t from by omega] at h
        exact h
  rw [hcwv, hctv, hczv] at h0val0 h1val0 h7val0 hrow2 hrow3
  -- the right-hand side entries
  have hE0 : y4.val.getD 0 (alloc.vec.Vec.new cpoly.field.Fp)
      = y0.val.getD 0 (alloc.vec.Vec.new cpoly.field.Fp) := by
    rw [hy4pre 0 (by omega), hy3v, getD_append_lt _ _ _ (by omega), hy2v,
      getD_append_lt _ _ _ (by omega), hy1pre 0 (by omega)]
  have hE1 : y4.val.getD 1 (alloc.vec.Vec.new cpoly.field.Fp)
      = y1.val.getD 1 (alloc.vec.Vec.new cpoly.field.Fp) := by
    rw [hy4pre 1 (by omega), hy3v, getD_append_lt _ _ _ (by omega), hy2v,
      getD_append_lt _ _ _ (by omega)]
  have hE2 : y4.val.getD 2 (alloc.vec.Vec.new cpoly.field.Fp) = r1 := by
    have h2 : y1.val.length = 2 := by omega
    rw [hy4pre 2 (by omega), hy3v, getD_append_lt _ _ _ (by omega), hy2v, ← h2]
    exact getD_append_eq _ _ _
  have hE3 : y4.val.getD 3 (alloc.vec.Vec.new cpoly.field.Fp) = r2 := by
    rw [hy4pre 3 (by omega), hy3v, ← hy2len]
    exact getD_append_eq _ _ _
  have hy1val0 := hy1val 0 (by omega)
  have hy4val0 := hy4val 0 (by omega)
  simp only [Nat.add_zero] at hy1val0 hy4val0
  rw [← hE1] at hy1val0
  have hWeq : cw.val + (ct.val + cz.val) = InnerOuter.rlinCols 1 8 8 5 10 10 := by
    rw [hcwv, hctv, hczv]
  -- the block matrix
  have hM : toMat (rows := InnerOuter.rlinRows 1 1 1)
      (cols := InnerOuter.rlinCols 1 8 8 5 10 10) o4
      = (InnerOuter.rlinStmt (zDigits := 5) Φ sp (16 : ZMod q) 16 gamma.val
          (ss, toVec (k := 1) v, toChals c hcn)).M := by
    funext i j
    simp only [toMat, toVec, InnerOuter.rlinStmt, Hachi.jMatrix, hcvec]
    refine Fin.addCases (fun i0 => ?_) (fun i1 => ?_) i
    · -- c1: `[ D | 0 ]`
      have hi0 : i0.val = 0 := Nat.lt_one_iff.mp i0.isLt
      have hd0 : toVec (k := 2 ^ 10 * 8)
          (pp.d_matrix.val.getD 0 (alloc.vec.Vec.new ring.Rq)) = sp.dMatrix i0 := by
        have h : toVec (k := 2 ^ 10 * 8)
            (pp.d_matrix.val.getD i0.val (alloc.vec.Vec.new ring.Rq)) = sp.dMatrix i0 :=
          congrFun hdmat i0
        rwa [hi0] at h
      simp only [Fin.append_left, Fin.val_castAdd, hi0]
      rw [h0val0 j.val j.isLt]
      refine Fin.addCases (fun jw => ?_) (fun jr => ?_) j
      · simp only [Fin.append_left, Fin.val_castAdd]
        rw [if_pos jw.isLt]
        have h := congrFun hd0 jw
        simp only [toVec] at h
        exact h
      · simp only [Fin.append_right, Fin.val_natAdd, Pi.zero_apply]
        rw [if_neg (by omega)]
    · refine Fin.addCases (fun i0 => ?_) (fun i2 => ?_) i1
      · -- c2: `[ 0 | B | 0 ]`
        have hi0 : i0.val = 0 := Nat.lt_one_iff.mp i0.isLt
        have hb0 : toVec (k := 2 ^ 10 * (1 * 8))
            (pp.inner.outer_matrix.val.getD 0 (alloc.vec.Vec.new ring.Rq))
            = sp.outerMatrix i0 := by
          have h : toVec (k := 2 ^ 10 * (1 * 8))
              (pp.inner.outer_matrix.val.getD i0.val (alloc.vec.Vec.new ring.Rq))
              = sp.outerMatrix i0 := congrFun houter i0
          rwa [hi0] at h
        simp only [Fin.append_right, Fin.append_left, Fin.val_natAdd, Fin.val_castAdd, hi0,
          Nat.add_zero]
        rw [h1val0 j.val j.isLt]
        refine Fin.addCases (fun jw => ?_) (fun jr => ?_) j
        · simp only [Fin.append_left, Fin.val_castAdd, Pi.zero_apply]
          rw [if_pos jw.isLt]
        · simp only [Fin.append_right, Fin.val_natAdd]
          refine Fin.addCases (fun jt => ?_) (fun jz => ?_) jr
          · simp only [Fin.append_left, Fin.val_castAdd]
            rw [if_neg (by omega), if_pos (by omega),
              show 2 ^ 10 * 8 + jt.val - 2 ^ 10 * 8 = jt.val from by omega]
            have h := congrFun hb0 jt
            simp only [toVec] at h
            exact h
          · simp only [Fin.append_right, Fin.val_natAdd, Pi.zero_apply]
            rw [if_neg (by omega), if_neg (by omega)]
      · refine Fin.addCases (fun i0 => ?_) (fun i3 => ?_) i2
        · -- c3: `[ (G_{2^r})ᵀ b | 0 ]`
          have hi0 : i0.val = 0 := Nat.lt_one_iff.mp i0.isLt
          simp only [Fin.append_right, Fin.append_left, Fin.val_natAdd, Fin.val_castAdd, hi0,
            Nat.add_zero]
          rw [show 1 + (1 + 0) = 2 from rfl, hrow2 j.val j.isLt]
          refine Fin.addCases (fun jw => ?_) (fun jr => ?_) j
          · simp only [Fin.append_left, Fin.val_castAdd]
            rw [if_pos jw.isLt]
            have h := congrFun hgbv jw
            simp only [toVec] at h
            exact h
          · simp only [Fin.append_right, Fin.val_natAdd, Pi.zero_apply]
            rw [if_neg (by omega)]
        · refine Fin.addCases (fun i0 => ?_) (fun i4 => ?_) i3
          · -- c4: `[ (G_{2^r})ᵀ c | 0 | −Jᵀ(G_{2^m}ᵀ a) ]`
            have hi0 : i0.val = 0 := Nat.lt_one_iff.mp i0.isLt
            simp only [Fin.append_right, Fin.append_left, Fin.val_natAdd, Fin.val_castAdd, hi0,
              Nat.add_zero]
            rw [show 1 + (1 + (1 + 0)) = 3 from rfl, hrow3 j.val j.isLt]
            refine Fin.addCases (fun jw => ?_) (fun jr => ?_) j
            · simp only [Fin.append_left, Fin.val_castAdd]
              rw [if_pos jw.isLt]
              have h := congrFun hgcv jw
              simp only [toVec] at h
              exact h
            · simp only [Fin.append_right, Fin.val_natAdd]
              refine Fin.addCases (fun jt => ?_) (fun jz => ?_) jr
              · simp only [Fin.append_left, Fin.val_castAdd, Pi.zero_apply]
                rw [if_neg (by omega), if_pos (by omega)]
              · simp only [Fin.append_right, Fin.val_natAdd]
                rw [if_neg (by omega), if_neg (by omega),
                  show 2 ^ 10 * 8 + (2 ^ 10 * (1 * 8) + jz.val) - (2 ^ 10 * 8 + 2 ^ 10 * (1 * 8))
                    = jz.val from by omega, matMul_transpose_mulVec]
                simp only [Pi.neg_apply]
                have h := congrFun hjtv jz
                simp only [toVec] at h
                rw [h]
          · -- c5: `[ 0 | (cᵀ ⊗ G) | −(A J) ]`
            have hi0 : i4.val = 0 := Nat.lt_one_iff.mp i4.isLt
            have ht0 : toVec (k := 2 ^ 10 * (1 * 8))
                (tensor.val.getD 0 (alloc.vec.Vec.new ring.Rq))
                = InnerOuter.tensorGMatrix Φ 16 1 8 (2 ^ 10) (toVec (k := 2 ^ 10) c) i4 := by
              have h : toVec (k := 2 ^ 10 * (1 * 8))
                  (tensor.val.getD i4.val (alloc.vec.Vec.new ring.Rq))
                  = InnerOuter.tensorGMatrix Φ 16 1 8 (2 ^ 10) (toVec (k := 2 ^ 10) c) i4 :=
                congrFun htv i4
              rwa [hi0] at h
            have hA0 : toVec (k := 2 ^ 10 * 8)
                (pp.inner.inner_matrix.val.getD 0 (alloc.vec.Vec.new ring.Rq))
                = sp.innerMatrix i4 := by
              have h : toVec (k := 2 ^ 10 * 8)
                  (pp.inner.inner_matrix.val.getD i4.val (alloc.vec.Vec.new ring.Rq))
                  = sp.innerMatrix i4 := congrFun hinner i4
              rwa [hi0] at h
            simp only [Fin.append_right, Fin.val_natAdd, hi0, Nat.add_zero]
            rw [show 1 + (1 + (1 + 1)) = 4 from rfl, h7val0 j.val j.isLt]
            refine Fin.addCases (fun jw => ?_) (fun jr => ?_) j
            · simp only [Fin.append_left, Fin.val_castAdd, Pi.zero_apply]
              rw [if_pos jw.isLt]
            · simp only [Fin.append_right, Fin.val_natAdd]
              refine Fin.addCases (fun jt => ?_) (fun jz => ?_) jr
              · simp only [Fin.append_left, Fin.val_castAdd]
                rw [if_neg (by omega), if_pos (by omega),
                  show 2 ^ 10 * 8 + jt.val - 2 ^ 10 * 8 = jt.val from by omega]
                have h := congrFun ht0 jt
                simp only [toVec] at h
                exact h
              · simp only [Fin.append_right, Fin.val_natAdd]
                rw [if_neg (by omega), if_neg (by omega),
                  show 2 ^ 10 * 8 + (2 ^ 10 * (1 * 8) + jz.val) - (2 ^ 10 * 8 + 2 ^ 10 * (1 * 8))
                    = jz.val from by omega, matMul_row]
                simp only [Pi.neg_apply]
                rw [gtmVal_eq_transpose_apply (rows := 2 ^ 10 * 8) (digits := 5), hA0]
  -- the right-hand side
  have hY : toVec (k := InnerOuter.rlinRows 1 1 1) y4
      = (InnerOuter.rlinStmt (zDigits := 5) Φ sp (16 : ZMod q) 16 gamma.val
          (ss, toVec (k := 1) v, toChals c hcn)).yvec := by
    funext i
    simp only [toVec, InnerOuter.rlinStmt]
    refine Fin.addCases (fun i0 => ?_) (fun i1 => ?_) i
    · have hi0 : i0.val = 0 := Nat.lt_one_iff.mp i0.isLt
      simp only [Fin.append_left, Fin.val_castAdd, toVec, hi0]
      rw [hE0]
      exact hy0val 0 (by omega)
    · refine Fin.addCases (fun i0 => ?_) (fun i2 => ?_) i1
      · have hi0 : i0.val = 0 := Nat.lt_one_iff.mp i0.isLt
        have hu0 : toRq (stmt.u.val.getD 0 (alloc.vec.Vec.new cpoly.field.Fp)) = ss.u i0 := by
          have h : toVec (k := 1) stmt.u i0 = ss.u i0 := congrFun hsu i0
          simp only [toVec, hi0] at h
          exact h
        simp only [Fin.append_right, Fin.append_left, Fin.val_natAdd, Fin.val_castAdd, hi0,
          Nat.add_zero]
        rw [hy1val0, hu0]
      · refine Fin.addCases (fun i0 => ?_) (fun i3 => ?_) i2
        · simp only [Fin.append_right, Fin.append_left, Fin.val_natAdd, Fin.val_castAdd,
            Nat.lt_one_iff.mp i0.isLt, Nat.add_zero]
          rw [show 1 + (1 + 0) = 2 from rfl, hE2, hr1v, hsy]
        · refine Fin.addCases (fun i0 => ?_) (fun i4 => ?_) i3
          · simp only [Fin.append_right, Fin.append_left, Fin.val_natAdd, Fin.val_castAdd,
              Nat.lt_one_iff.mp i0.isLt, Nat.add_zero]
            rw [show 1 + (1 + (1 + 0)) = 3 from rfl, hE3, hr2v]
          · simp only [Fin.append_right, Fin.val_natAdd, Nat.lt_one_iff.mp i4.isLt, Nat.add_zero]
            rw [show 1 + (1 + (1 + 1)) = 4 from rfl, hy4val0, hr2v]
  refine ZeroCheck.RlinStatement_new_spec (n := InnerOuter.rlinRows 1 1 1)
    (μ := InnerOuter.rlinCols 1 8 8 5 10 10) o4 y4 gamma _ hM hY rfl ⟨by omega, ?_⟩
    ⟨by omega, hy4wf⟩
  intro x hx
  have h := h7wf x hx
  rwa [hWeq] at h

end HachiEquiv.Rlin
