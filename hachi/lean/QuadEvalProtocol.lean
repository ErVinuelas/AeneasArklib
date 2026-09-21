/-
Target 2's QuadEval **protocol layer**, **proved and promoted** (2026-09-09,
Aristotle session `982bd0af`, eleven obligations to zero, no headline
signature changed).

Eleven headline specs, the debt `make spec-check` found on 2026-09-08: the
QuadEval fold's arithmetic was proved and promoted first (`lean/QuadEval.lean`,
Aristotle session `14b9bf77`), but eleven of the module's items -- its three
carriers, the honest prover's three functions, the two gadget-level helpers and
the two output relations -- carried `Mirrors` lines and had no `_spec` anywhere.
`coverage` asked "is it measured" and answered yes; nothing asked "is it
stated". This file is the answer to the second question for `quadeval`.

# What this file rests on

It imports the promoted `QuadEval.lean`, which supplies the whole representation
kit: `toVec`/`WfVec`, `toMat`/`WfMat`, `toParams`/`WfParams`, `toOpening`,
`toRq`/`Wf`, and the two digit maps `ddBal` (full width, base 16, 8 digits) and
`bddZ` (bounded, base 16, `τ = 5`, `zBound = 131072`). Nothing new is needed at
the ring level; what is new is the four representations below.

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
import Raw32
import SchemeTwoLane

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi
open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme
open HachiEquiv.SchemeTwoLane
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

/-! ## Target-local helpers

Six extracted folds have no spec in the promoted files: `PolyVec::zeros` and
`PolyVec::copy`, the `carrier` and `tensor_g` loops, the `honest_z` loop and the
pass-through loop of `honest_compute_resp`. Their loop invariants are
`lean/Scheme.lean`'s scaffold, unchanged. Nothing in this section is part of the
file's public surface; the eleven obligations below are. -/

/-- A guarded `if` whose `else` rejects: the decision is the conjunction of the
guard and the decision the `then` branch makes. This is the shape both output
relations end in -- five nested flags and then the range block. -/
theorem ite_reject_spec {c : Prop} [Decidable c] {P R : Prop} (hc : c ↔ P)
    (m : Result Bool) (hm : m ⦃ b => b = true ↔ R ⦄) :
    (if c then m else ok false) ⦃ b => b = true ↔ (P ∧ R) ⦄ := by
  by_cases h : c
  · rw [if_pos h]
    apply spec_mono hm
    intro b hb
    rw [hb]
    exact (and_iff_right (hc.mp h)).symm
  · rw [if_neg h, WP.spec_ok]
    constructor
    · intro hb; exact absurd hb (by simp)
    · rintro ⟨hp, _⟩; exact absurd (hc.mpr hp) h

/-- `gadget::gadget_mul_z` (`lean/QuadEval.lean:414`) with the row count given as
an `ℕ` rather than read off the `usize`. -/
theorem gadget_mul_z_spec' {rows : ℕ} (n : Std.Usize) (v : linalg.PolyVec)
    (hn : n.val = rows) (hv : WfVec (rows * 5) v) (hmax : 5 * rows ≤ Usize.max) :
    gadget.gadget_mul_z n v
      ⦃ z => WfVec rows z ∧ toVec (k := rows) z
        = gadgetMul Φ (16 : ZMod q) (toVec (k := rows * 5) v) ⦄ := by
  subst hn
  exact QuadEval.gadget_mul_z_spec n v hv hmax

/-- The loop of `PolyVec::zeros`. -/
theorem poly_vec_zeros_loop_spec (k : Std.Usize) (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hi : i.val ≤ k.val) (hlen : out.val.length = i.val) (hwf : ∀ y ∈ out.val, Wf y)
    (hval : ∀ j, j < i.val → toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) = 0) :
    linalg.PolyVec.zeros_loop k out i
      ⦃ z => z.val.length = k.val ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < k.val → toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) = 0 ⦄ := by
  rw [linalg.PolyVec.zeros_loop]
  apply loop.spec_decr_nat (fun s => k.val - s.2.val)
    (fun s => s.2.val ≤ k.val ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ j, j < s.2.val → toRq (s.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) = 0)
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [linalg.PolyVec.zeros_loop.body]
    by_cases hlt : i1 < k
    · rw [if_pos hlt]
      step with RqBridge.zero_spec as ⟨r, hWr, hr⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 j hjlt]
        · have hjeq : j = o1.val.length := by omega
          rw [hjeq, ho2, getD_append_eq, hr]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = k.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, by intro j hj; exact hval1 j (by omega)⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- `PolyVec::zeros` is the all-zero vector of the requested length. Stated
entrywise rather than as a `toVec` equality: the length is a `usize`, and the
callers below read it at an `ℕ` the `usize` is only propositionally equal to. -/
theorem poly_vec_zeros_spec (n : Std.Usize) :
    linalg.PolyVec.zeros n
      ⦃ z => z.val.length = n.val ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < n.val → toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) = 0 ⦄ := by
  rw [linalg.PolyVec.zeros]
  simp only [bind_ok_id]
  exact poly_vec_zeros_loop_spec n (alloc.vec.Vec.new ring.Rq) 0#usize
    (by simp) (by simp) (by intro y hy; simp at hy) (by intro j hj; simp at hj)

/-- The loop of `PolyVec::copy`. -/
theorem poly_vec_copy_loop_spec {k : ℕ} (v : linalg.PolyVec) (n : Std.Usize)
    (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hv : WfVec k v) (hn : n.val = k) (hi : i.val ≤ n.val)
    (hlen : out.val.length = i.val) (hwf : ∀ y ∈ out.val, Wf y)
    (hval : ∀ j, j < i.val → toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
      = toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))) :
    linalg.PolyVec.copy_loop v n out i
      ⦃ z => z.val.length = k ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < k → toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [linalg.PolyVec.copy_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ j, j < s.2.val → toRq (s.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [linalg.PolyVec.copy_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hiv : i1.val < v.val.length := by rw [hv.1, ← hn]; scalar_tac
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hv.2 _ (List.getElem_mem hiv)
      step with RqBridge.copy_spec r hWr as ⟨r1, hWr1, hr1⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 j hjlt]
        · have hjeq : j = o1.val.length := by omega
          rw [hjeq, ho2, getD_append_eq, hr1, hr, hlen1, List.getD_eq_getElem _ _ hiv]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = k := by rw [← hn]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, by intro j hj; exact hval1 j (by omega)⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- `PolyVec::copy` represents the same vector. -/
theorem poly_vec_copy_spec {k : ℕ} (v : linalg.PolyVec) (hv : WfVec k v) :
    linalg.PolyVec.copy v ⦃ z => WfVec k z ∧ toVec (k := k) z = toVec (k := k) v ⦄ := by
  rw [linalg.PolyVec.copy]
  simp only [bind_ok_id]
  apply spec_mono (poly_vec_copy_loop_spec v (alloc.vec.Vec.len v)
    (alloc.vec.Vec.new ring.Rq) 0#usize hv (by simp [hv.1]) (by simp) (by simp)
    (by intro y hy; simp at hy) (by intro j hj; simp at hj))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i
  simp only [toVec]
  exact hzval i.val i.isLt

/-- The loop of `quadeval::carrier`: entry `j` already written is the carrier
entry of block `j`. -/
theorem carrier_loop_spec {rows blocks : ℕ} (a : linalg.PolyVec)
    (s : alloc.vec.Vec linalg.PolyVec) (n : Std.Usize) (out : alloc.vec.Vec ring.Rq)
    (i : Std.Usize) (ha : WfVec rows a) (hs : WfBlocks blocks (rows * 8) s)
    (hmax : 8 * rows ≤ Usize.max) (hn : n.val = blocks) (hi : i.val ≤ n.val)
    (hlen : out.val.length = i.val) (hwf : ∀ y ∈ out.val, Wf y)
    (hval : ∀ j, j < i.val → toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
      = Hachi.carrierEntry Φ (16 : ZMod q) (toVec (k := rows) a)
          (toVec (k := rows * 8) (s.val.getD j (alloc.vec.Vec.new ring.Rq)))) :
    quadeval.carrier_loop a s n out i
      ⦃ z => z.val.length = blocks ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < blocks → toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          = Hachi.carrierEntry Φ (16 : ZMod q) (toVec (k := rows) a)
              (toVec (k := rows * 8) (s.val.getD j (alloc.vec.Vec.new ring.Rq))) ⦄ := by
  rw [quadeval.carrier_loop]
  apply loop.spec_decr_nat (fun t => n.val - t.2.val)
    (fun t => t.2.val ≤ n.val ∧ t.1.val.length = t.2.val ∧ (∀ y ∈ t.1.val, Wf y) ∧
      ∀ j, j < t.2.val → toRq (t.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = Hachi.carrierEntry Φ (16 : ZMod q) (toVec (k := rows) a)
            (toVec (k := rows * 8) (s.val.getD j (alloc.vec.Vec.new ring.Rq))))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [quadeval.carrier_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have his : i1.val < s.val.length := by rw [hs.1, ← hn]; scalar_tac
      step as ⟨pv, hpv⟩
      have hWpv : WfVec (rows * 8) pv := by
        rw [hpv]; exact hs.2 _ (List.getElem_mem his)
      step with QuadEval.carrier_entry_spec (rows := rows) a pv ha hWpv hmax as ⟨r, hWr, hr⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 j hjlt]
        · have hjeq : j = o1.val.length := by omega
          rw [hjeq, ho2, getD_append_eq, hr, hlen1, List.getD_eq_getElem _ _ his, hpv]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = blocks := by rw [← hn]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, by intro j hj; exact hval1 j (by omega)⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- `quadeval::carrier` computes ArkLib's `carrier`: `wᵢ = aᵀ G sᵢ`. -/
theorem carrier_spec {rows blocks : ℕ} (a : linalg.PolyVec)
    (s : alloc.vec.Vec linalg.PolyVec) (ha : WfVec rows a)
    (hs : WfBlocks blocks (rows * 8) s) (hmax : 8 * rows ≤ Usize.max) :
    quadeval.carrier a s
      ⦃ out => WfVec blocks out ∧ toVec (k := blocks) out
        = Hachi.carrier Φ (16 : ZMod q) (toVec (k := rows) a)
            (toBlocks (blocks := blocks) (width := rows * 8) s) ⦄ := by
  rw [quadeval.carrier]
  simp only [linalg.PolyVec.new, bind_ok_id]
  apply spec_mono (carrier_loop_spec a s (alloc.vec.Vec.len s) (alloc.vec.Vec.new ring.Rq)
    0#usize ha hs hmax (by simpa using hs.1) (by simp) (by simp)
    (by intro y hy; simp at hy) (by intro j hj; simp at hj))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i
  simp only [toVec, Hachi.carrier, toBlocks]
  exact hzval i.val i.isLt

/-! ## The streamed carrier

`carrier_from_raw` takes the *raw* message and computes the same `w`, without
the decomposed message and -- this is the part worth stating -- without any
gadget arithmetic at all. ArkLib's `carrier` recomposes its argument with
`gadgetMul` before the dot, and `gadgetMul ∘ gadgetDecompose` is the identity
(`gadgetDecompose_lawful`), so the recomposition the streamed prover would have
performed cancels against the decomposition it would have performed first.

The conclusion is `carrier_spec`'s with the block family replaced by the
decomposition of `raw`: the same value, from an argument that is never built. -/

/-- The loop of `quadeval::carrier_from_raw`: entry `j` is `a · rawⱼ`. -/
theorem carrier_from_raw_loop_spec {rows blocks : ℕ} (a : linalg.PolyVec)
    (am : linalg.PolyMatrix) (prep : linalg.PreparedMatrixGA)
    (raw : alloc.vec.Vec linalg.PolyVec) (n : Std.Usize)
    (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (ha : WfVec rows a) (ham : WfMat 1 rows am)
    (ha0 : toVec (k := rows) (am.val.getD 0 (alloc.vec.Vec.new ring.Rq))
             = toVec (k := rows) a)
    (hprep : WfPrepGA 1 rows prep am)
    (hraw : WfBlocks blocks rows raw) (hn : n.val = blocks)
    (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hwf : ∀ y ∈ out.val, Wf y)
    (hval : ∀ j, j < i.val →
      toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ArkLib.Lattices.dot (toVec (k := rows) a)
            (toVec (k := rows) (raw.val.getD j (alloc.vec.Vec.new ring.Rq)))) :
    quadeval.carrier_from_raw_loop raw n prep out i
      ⦃ z => z.val.length = blocks ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < blocks →
          toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
            = ArkLib.Lattices.dot (toVec (k := rows) a)
                (toVec (k := rows) (raw.val.getD j (alloc.vec.Vec.new ring.Rq))) ⦄ := by
  rw [quadeval.carrier_from_raw_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ j, j < s.2.val → toRq (s.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ArkLib.Lattices.dot (toVec (k := rows) a)
            (toVec (k := rows) (raw.val.getD j (alloc.vec.Vec.new ring.Rq))))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [quadeval.carrier_from_raw_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hib : i1.val < raw.val.length := by rw [hraw.1, ← hn]; scalar_tac
      step as ⟨pv, hpv⟩
      have hWpv : WfVec rows pv := by rw [hpv]; exact hraw.2 _ (List.getElem_mem hib)
      have hri : raw.val.getD i1.val (alloc.vec.Vec.new ring.Rq) = pv := by
        rw [hpv]; exact List.getD_eq_getElem _ _ hib
      -- the prepared row, applied: `matVecMul` at one row IS the dot against it
      step with apply_ga_spec (rows := 1) (cols := rows) prep am pv ham hWpv hprep
        as ⟨rv, hWrv, hrv⟩
      have hr0 : (0 : ℕ) < rv.val.length := by rw [hWrv.1]; norm_num
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hWrv.2 _ (List.getElem_mem hr0)
      have hrval : toRq r = ArkLib.Lattices.dot (toVec (k := rows) a)
          (toVec (k := rows) pv) := by
        have h1 := congrFun hrv (0 : Fin 1)
        rw [ArkLib.Lattices.matVecMul_apply, toMat_apply] at h1
        simp only [Fin.val_zero] at h1
        rw [ha0] at h1
        rw [hr, ← h1]
        simp only [toVec, Fin.val_zero]
        rw [List.getD_eq_getElem _ _ hr0]
      step with RqBridge.copy_spec r hWr as ⟨rc, hWrc, hrc⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWrc
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 j hjlt]
        · have hjeq : j = o1.val.length := by omega
          rw [hjeq, ho2, getD_append_eq, hrc, hrval, hlen1, hri]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq, hn], hwf1,
        by intro j hj; exact hval1 j (by rw [heq, hn]; exact hj)⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- **The gadget round trip inside `carrierEntry` cancels.** The dot of `a`
against `b` *is* `carrierEntry` at `b`'s decomposition, because `carrierEntry` is
`splitForm G` -- the dot against `gadgetMul` -- and `gadgetMul ∘ gadgetDecompose`
is the identity.

Its own lemma, not a step inside `carrier_from_raw_spec`: unfolding `carrier`
here and elaborating `spec_mono` there in one declaration exceeded four million
heartbeats together, and separately each is cheap. -/
theorem dot_eq_carrierEntry_of_decomp {rows : ℕ} (a b : linalg.PolyVec) :
    ArkLib.Lattices.dot (toVec (k := rows) a) (toVec (k := rows) b)
      = Hachi.carrierEntry Φ (16 : ZMod q) (toVec (k := rows) a)
          (gadgetDecompose Φ dd (toVec (k := rows) b)) := by
  simp only [Hachi.carrierEntry, ArkLib.Lattices.splitForm]
  congr 1
  exact (gadgetDecompose_lawful Φ (rows := rows) (by norm_num)
    (by rw [RqBridge.phi_natDegree]; norm_num) dd (toVec (k := rows) b)).symm

-- The one-row prepared matrix makes `spec_mono`'s unification heavy: it has to
-- see through `PolyMatrix`'s reducible alias and `PreparedMatrix`'s two fields
-- at once. Slow, not divergent, and the budget below is measured rather than
-- guessed -- 200 000 (the default) and 800 000 both time out, 1 000 000 passes
-- once the `carrier` unfolding is out of this declaration and in
-- `dot_eq_carrierEntry_of_decomp`. Splitting the two apart is what made either
-- of them affordable: together they wanted more than four million.
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
/-- **`quadeval::carrier_from_raw` is `carrier` at the decomposed message.**

The gadget round trip is where the work goes: the streamed form never
decomposes, and never recomposes either, because `carrier_entry` would have
undone exactly what the decomposition did. -/
theorem carrier_from_raw_spec {rows blocks : ℕ} (a : linalg.PolyVec)
    (raw : alloc.vec.Vec linalg.PolyVec) (ha : WfVec rows a)
    (hraw : WfBlocks blocks rows raw) (hmax : rows * N ≤ Std.Usize.max) :
    quadeval.carrier_from_raw a raw
      ⦃ out => WfVec blocks out ∧ toVec (k := blocks) out
        = Hachi.carrier Φ (16 : ZMod q) (toVec (k := rows) a)
            (fun i : Fin blocks => gadgetDecompose Φ dd
              (toVec (k := rows) (raw.val.getD i.val (alloc.vec.Vec.new ring.Rq)))) ⦄ := by
  rw [quadeval.carrier_from_raw]
  -- `a` as a one-row matrix, prepared once
  step with poly_vec_copy_spec (k := rows) a ha as ⟨ac, hWac, hac⟩
  step as ⟨rws, hrws⟩
  rw [linalg.PolyMatrix.new]
  simp only [bind_tc_ok]
  -- `PolyMatrix` is a reducible alias for the vector, so `rws` is the matrix
  have ham : WfMat 1 rows rws := by
    refine ⟨by rw [hrws]; simp, ?_⟩
    intro r hr
    rw [hrws] at hr
    rcases List.mem_append.mp hr with h | h
    · simp at h
    · rw [List.mem_singleton.mp h]; exact hWac
  have ha0 : toVec (k := rows) (rws.val.getD 0 (alloc.vec.Vec.new ring.Rq))
      = toVec (k := rows) a := by
    rw [hrws]
    simpa using hac
  step with prepare_ga_spec (rows := 1) (cols := rows) rws ham (by norm_num) hmax
    as ⟨prep, hprep⟩
  simp only [linalg.PolyVec.new, bind_ok_id]
  -- bound to a `have` before the `apply`: elaborating the loop spec's arguments
  -- first is what keeps `spec_mono`'s unification from blowing up on
  -- `PolyMatrix`'s reducible alias (200 000 heartbeats were not enough inline)
  have hloop := carrier_from_raw_loop_spec (rows := rows) (blocks := blocks)
    a rws prep raw (alloc.vec.Vec.len raw)
    (alloc.vec.Vec.new ring.Rq) 0#usize ha ham ha0 hprep hraw (by simpa using hraw.1)
    (by simp) (by simp) (by intro y hy; simp at hy) (by intro j hj; simp at hj)
  apply spec_mono hloop
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i
  rw [show toVec (k := blocks) z i
        = toRq (z.val.getD i.val (alloc.vec.Vec.new cpoly.field.Fp)) from rfl,
    hzval i.val i.isLt]
  exact dot_eq_carrierEntry_of_decomp (rows := rows) a
    (raw.val.getD i.val (alloc.vec.Vec.new ring.Rq))

/-- The loop of `quadeval::tensor_g`: the accumulator is the partial
challenge-weighted gadget sum. -/
theorem tensor_g_loop_spec {krows blocks : ℕ} (r : Std.Usize) (c : linalg.PolyVec)
    (x : alloc.vec.Vec linalg.PolyVec) (n : Std.Usize) (acc : linalg.PolyVec) (i : Std.Usize)
    (hr : r.val = krows) (hc : WfVec blocks c) (hx : WfBlocks blocks (krows * 8) x)
    (hn : n.val = blocks) (hi : i.val ≤ n.val) (hacc : WfVec krows acc)
    (hval : toVec (k := krows) acc
      = ∑ j ∈ Finset.range i.val,
          scalarVecMul (toRq (c.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))
            (gadgetMul Φ (16 : ZMod q)
              (toVec (k := krows * 8) (x.val.getD j (alloc.vec.Vec.new ring.Rq))))) :
    quadeval.tensor_g_loop r c x n acc i
      ⦃ z => WfVec krows z ∧ toVec (k := krows) z
        = ∑ j ∈ Finset.range blocks,
            scalarVecMul (toRq (c.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))
              (gadgetMul Φ (16 : ZMod q)
                (toVec (k := krows * 8) (x.val.getD j (alloc.vec.Vec.new ring.Rq)))) ⦄ := by
  rw [quadeval.tensor_g_loop]
  apply loop.spec_decr_nat (fun t => n.val - t.2.val)
    (fun t => t.2.val ≤ n.val ∧ WfVec krows t.1 ∧ toVec (k := krows) t.1
      = ∑ j ∈ Finset.range t.2.val,
          scalarVecMul (toRq (c.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))
            (gadgetMul Φ (16 : ZMod q)
              (toVec (k := krows * 8) (x.val.getD j (alloc.vec.Vec.new ring.Rq)))))
  · rintro ⟨a1, i1⟩ ⟨hi1, hacc1, hval1⟩
    dsimp only at hi1 hacc1 hval1
    simp only [quadeval.tensor_g_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hix : i1.val < x.val.length := by rw [hx.1, ← hn]; scalar_tac
      have hic : i1.val < c.val.length := by rw [hc.1, ← hn]; scalar_tac
      step as ⟨pv, hpv⟩
      have hWpv : WfVec (krows * 8) pv := by
        rw [hpv]; exact hx.2 _ (List.getElem_mem hix)
      step with gadget_mul_spec (rows := krows) r pv hr hWpv as ⟨rc, hRwf, hRval⟩
      simp only [linalg.PolyVec.get]
      step as ⟨cr, hcr⟩
      have hWcr : Wf cr := by rw [hcr]; exact hc.2 _ (List.getElem_mem hic)
      step with scalar_vec_mul_spec (k := krows) cr rc hWcr hRwf as ⟨scaled, hSwf, hSval⟩
      step with vec_add_spec (k := krows) a1 scaled hacc1 hSwf as ⟨a2, hAwf, hAval⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, hAwf, ?_, ?_⟩
      · have hterm : scalarVecMul (toRq cr) (toVec (k := krows) rc)
            = scalarVecMul (toRq (c.val.getD i1.val (alloc.vec.Vec.new cpoly.field.Fp)))
                (gadgetMul Φ (16 : ZMod q)
                  (toVec (k := krows * 8) (x.val.getD i1.val (alloc.vec.Vec.new ring.Rq)))) := by
          rw [hRval, hcr, hpv, List.getD_eq_getElem _ _ hic, List.getD_eq_getElem _ _ hix]
        rw [hAval, hSval, hval1, hterm, hi2, Finset.sum_range_succ]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = blocks := by rw [← hn]; scalar_tac
      rw [← heq]
      exact ⟨hacc1, hval1⟩
  · exact ⟨hi, hacc, hval⟩

/-- `quadeval::tensor_g` computes ArkLib's `tensorG`, the Eq. (20) row-5 left
side. -/
theorem tensor_g_spec {krows blocks : ℕ} (r : Std.Usize) (c : linalg.PolyVec)
    (x : alloc.vec.Vec linalg.PolyVec) (hr : r.val = krows) (hc : WfVec blocks c)
    (hx : WfBlocks blocks (krows * 8) x) :
    quadeval.tensor_g r c x
      ⦃ out => WfVec krows out ∧ toVec (k := krows) out
        = Hachi.tensorG Φ (16 : ZMod q) krows 8 (toVec (k := blocks) c)
            (toBlocks (blocks := blocks) (width := krows * 8) x) ⦄ := by
  rw [quadeval.tensor_g]
  step with poly_vec_zeros_spec r as ⟨acc, hAlen, hAwf, hAval⟩
  have hWacc : WfVec krows acc := ⟨by rw [hAlen, hr], hAwf⟩
  have hAzero : toVec (k := krows) acc = 0 := by
    funext j
    simp only [toVec, Pi.zero_apply]
    exact hAval j.val (by rw [hr]; exact j.isLt)
  apply spec_mono (tensor_g_loop_spec r c x (alloc.vec.Vec.len x) acc 0#usize hr hc hx
    (by simpa using hx.1) (by simp) hWacc (by rw [hAzero]; simp))
  rintro z ⟨hzwf, hzval⟩
  refine ⟨hzwf, ?_⟩
  rw [hzval, Hachi.tensorG,
    ← Fin.sum_univ_eq_sum_range (fun j =>
      scalarVecMul (toRq (c.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))
        (gadgetMul Φ (16 : ZMod q)
          (toVec (k := krows * 8) (x.val.getD j (alloc.vec.Vec.new ring.Rq))))) blocks]
  rfl

/-! ### `quadeval::honest_z`, accumulating in place

Candidate T17 Change 2. The accumulator is a bare `Vec ring.Rq` written through
`index_mut`, so there are four loops where there was one: the zero-fill, the
block loop, and one inner loop per branch of `classify_short`. Every invariant
below is *pointwise* -- `toRq (acc[t]) = …` -- which is the natural shape for an
in-place write and which `toVec`'s definition turns back into the function
equality `honest_z_spec` needs.

`honest_z_spec`'s statement does not move, again. -/

private theorem vgetD_set_eq {α : Type} {v : alloc.vec.Vec α} {t : Std.Usize} {x d : α}
    (ht : t.val < v.val.length) : (v.set t x).val.getD t.val d = x := by
  rw [alloc.vec.Vec.set_val_eq,
    List.getD_eq_getElem _ _ (by rw [List.length_set]; exact ht), List.getElem_set]
  simp

private theorem vgetD_set_ne {α : Type} {v : alloc.vec.Vec α} {t : Std.Usize} {x d : α}
    {k : ℕ} (h : k ≠ t.val) : (v.set t x).val.getD k d = v.val.getD k d := by
  rw [alloc.vec.Vec.set_val_eq]
  by_cases hk : k < v.val.length
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_set]; exact hk),
      List.getD_eq_getElem _ _ hk, List.getElem_set_ne (fun hh => h hh.symm)]
  · rw [List.getD_eq_default _ _ (by rw [List.length_set]; omega),
      List.getD_eq_default _ _ (by omega)]

private theorem all_set {α : Type} {P : α → Prop} {v : alloc.vec.Vec α}
    {t : Std.Usize} {y : α} (hv : ∀ x ∈ v.val, P x) (hy : P y) :
    ∀ x ∈ (v.set t y).val, P x := by
  intro x hx
  rw [alloc.vec.Vec.set_val_eq] at hx
  rcases List.mem_or_eq_of_mem_set hx with h | h
  · exact hv x h
  · rw [h]; exact hy

/-- The zero-fill: `width` copies of `0`, pushed. -/
theorem honest_z_loop0_spec {width : ℕ} (widthU : Std.Usize)
    (acc : alloc.vec.Vec ring.Rq) (zU : Std.Usize)
    (hw : widthU.val = width) (hz : zU.val ≤ width)
    (hlen : acc.val.length = zU.val) (hwf : ∀ x ∈ acc.val, Wf x)
    (hval : ∀ t, t < zU.val →
      toRq (acc.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = 0) :
    quadeval.honest_z_loop0 widthU acc zU
      ⦃ z => z.val.length = width ∧ (∀ x ∈ z.val, Wf x) ∧
        ∀ t, t < width →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = 0 ⦄ := by
  rw [quadeval.honest_z_loop0]
  apply loop.spec_decr_nat (fun r => width - r.2.val)
    (fun r => r.2.val ≤ width ∧ r.1.val.length = r.2.val
      ∧ (∀ x ∈ r.1.val, Wf x)
      ∧ ∀ t, t < r.2.val →
          toRq (r.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = 0)
  · rintro ⟨d, zz⟩ ⟨hzz, hdl, hdw, hdv⟩
    dsimp only at hzz hdl hdw hdv
    simp only [quadeval.honest_z_loop0.body]
    by_cases hlt : zz < widthU
    · rw [if_pos hlt]
      have hzlt : zz.val < width := by rw [← hw]; scalar_tac
      step with HachiEquiv.RqBridge.zero_spec as ⟨r, hrwf, hrval⟩
      step as ⟨d1, hd1⟩
      step as ⟨zz1, hzz1⟩
      refine ⟨by rw [hzz1]; omega, ?_, ?_, ?_, by rw [hzz1]; omega⟩
      · rw [hd1, hzz1, List.length_append, hdl]; simp
      · intro x hx
        rw [hd1] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hdw x h
        · rw [List.mem_singleton.mp h]; exact hrwf
      · intro t ht
        rw [hzz1] at ht
        rcases Nat.lt_or_ge t zz.val with htlt | htge
        · rw [hd1, getD_append_lt _ _ _ (by omega)]
          exact hdv t htlt
        · have hteq : t = d.val.length := by omega
          rw [hteq, hd1, getD_append_eq]; exact hrval
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : zz.val = width := by rw [← hw]; scalar_tac
      exact ⟨by rw [hdl, heq], hdw, fun t ht => hdv t (by rw [heq]; exact ht)⟩
  · exact ⟨hz, hlen, hwf, hval⟩

/-- The **short** branch's inner loop: `width` products added into `acc` in
place. `prev` is what the accumulator held when the block started. -/
theorem honest_z_loop1_loop1_spec {width : ℕ} (message : alloc.vec.Vec linalg.PolyVec)
    (widthU iU jU : Std.Usize) (desc : ring.ShortMul) (ci : ring.Rq)
    (acc : alloc.vec.Vec ring.Rq) (prev : ℕ → Rq Φ)
    (hw : widthU.val = width) (hib : iU.val < message.val.length)
    (hmi : WfVec width (message.val.getD iU.val (alloc.vec.Vec.new ring.Rq)))
    (hci : Wf ci)
    (hmlen : desc.idx.val.length ≤ desc.mag.val.length)
    (hnlen : desc.idx.val.length ≤ desc.neg.val.length)
    (hidx : ∀ u, u < desc.idx.val.length →
      HachiEquiv.RingShort.idxAt desc.idx u < N)
    (hden : ∀ j, j < N → coeffK ci j
      = HachiEquiv.RingShort.descCoeffW desc.idx desc.mag desc.neg
          desc.idx.val.length j)
    (hj : jU.val ≤ width) (hlen : acc.val.length = width)
    (hwf : ∀ x ∈ acc.val, Wf x)
    (hval : ∀ t, t < width →
      toRq (acc.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        = prev t + (if t < jU.val then toRq ci
            * toRq ((message.val.getD iU.val (alloc.vec.Vec.new ring.Rq)).val.getD t
                (alloc.vec.Vec.new cpoly.field.Fp)) else 0)) :
    quadeval.honest_z_loop1_loop1 message widthU acc iU desc jU
      ⦃ z => z.val.length = width ∧ (∀ x ∈ z.val, Wf x) ∧
        ∀ t, t < width →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = prev t + toRq ci
                * toRq ((message.val.getD iU.val (alloc.vec.Vec.new ring.Rq)).val.getD t
                    (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [quadeval.honest_z_loop1_loop1]
  apply loop.spec_decr_nat (fun r => width - r.2.val)
    (fun r => r.2.val ≤ width ∧ r.1.val.length = width ∧ (∀ x ∈ r.1.val, Wf x)
      ∧ ∀ t, t < width →
          toRq (r.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = prev t + (if t < r.2.val then toRq ci
                * toRq ((message.val.getD iU.val (alloc.vec.Vec.new ring.Rq)).val.getD t
                    (alloc.vec.Vec.new cpoly.field.Fp)) else 0))
  · rintro ⟨d, jj⟩ ⟨hjj, hdl, hdw, hdv⟩
    dsimp only at hjj hdl hdw hdv
    simp only [quadeval.honest_z_loop1_loop1.body]
    by_cases hlt : jj < widthU
    · rw [if_pos hlt]
      have hjlt : jj.val < width := by rw [← hw]; scalar_tac
      step as ⟨pv, hpv⟩
      have hpvv : pv = message.val.getD iU.val (alloc.vec.Vec.new ring.Rq) := by
        rw [hpv, List.getD_eq_getElem _ _ hib]
      have hjb : jj.val < pv.val.length := by rw [hpvv, hmi.1]; exact hjlt
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hrwf : Wf r := by
        rw [hr]; exact hmi.2 _ (by rw [← hpvv]; exact List.getElem_mem hjb)
      step as ⟨elem, back, helem, hback⟩
      have hdjb : jj.val < d.val.length := by rw [hdl]; exact hjlt
      have hewf : Wf elem := by rw [helem]; exact hdw _ (List.getElem_mem hdjb)
      step with HachiEquiv.RqBridge.mul_short_add_into_spec desc r elem ci hrwf
        hci hewf hmlen hnlen hidx hden as ⟨r2, hr2wf, hr2val⟩
      step as ⟨jj1, hjj1⟩
      rw [hback]
      refine ⟨by rw [hjj1]; omega, ?_, all_set hdw hr2wf, ?_, by rw [hjj1]; omega⟩
      · rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hdl
      · intro t ht
        rw [hjj1]
        by_cases heq : t = jj.val
        · have hdgetD : d.val.getD jj.val (alloc.vec.Vec.new cpoly.field.Fp) = elem := by
            rw [helem, List.getD_eq_getElem _ _ hdjb]
          have hrg : r = (message.val.getD iU.val
              (alloc.vec.Vec.new ring.Rq)).val.getD jj.val
                (alloc.vec.Vec.new cpoly.field.Fp) := by
            rw [hr, ← hpvv, List.getD_eq_getElem _ _ hjb]
          rw [heq, vgetD_set_eq hdjb, hr2val, ← hdgetD, hdv jj.val hjlt,
            if_neg (by omega), add_zero, hrg, if_pos (by omega)]
        · rw [vgetD_set_ne heq, hdv t ht]
          by_cases hlt2 : t < jj.val
          · rw [if_pos hlt2, if_pos (by omega)]
          · rw [if_neg hlt2, if_neg (by omega)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = width := by rw [← hw]; scalar_tac
      refine ⟨hdl, hdw, ?_⟩
      intro t ht
      rw [hdv t ht, heq, if_pos ht]
  · exact ⟨hj, hlen, hwf, hval⟩

/-- The **fallback** branch's inner loop: the generic scaled vector, added in
place. Same shape as the short branch's, with `scaled` in hand rather than a
description. -/
theorem honest_z_loop1_loop0_spec {width : ℕ} (widthU jU : Std.Usize)
    (scaled : linalg.PolyVec) (acc : alloc.vec.Vec ring.Rq) (prev : ℕ → Rq Φ)
    (hw : widthU.val = width) (hs : WfVec width scaled)
    (hj : jU.val ≤ width) (hlen : acc.val.length = width)
    (hwf : ∀ x ∈ acc.val, Wf x)
    (hval : ∀ t, t < width →
      toRq (acc.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        = prev t + (if t < jU.val then
            toRq (scaled.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) else 0)) :
    quadeval.honest_z_loop1_loop0 widthU acc scaled jU
      ⦃ z => z.val.length = width ∧ (∀ x ∈ z.val, Wf x) ∧
        ∀ t, t < width →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = prev t
                + toRq (scaled.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [quadeval.honest_z_loop1_loop0]
  apply loop.spec_decr_nat (fun r => width - r.2.val)
    (fun r => r.2.val ≤ width ∧ r.1.val.length = width ∧ (∀ x ∈ r.1.val, Wf x)
      ∧ ∀ t, t < width →
          toRq (r.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = prev t + (if t < r.2.val then
                toRq (scaled.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) else 0))
  · rintro ⟨d, jj⟩ ⟨hjj, hdl, hdw, hdv⟩
    dsimp only at hjj hdl hdw hdv
    simp only [quadeval.honest_z_loop1_loop0.body]
    by_cases hlt : jj < widthU
    · rw [if_pos hlt]
      have hjlt : jj.val < width := by rw [← hw]; scalar_tac
      have hdjb : jj.val < d.val.length := by rw [hdl]; exact hjlt
      have hsjb : jj.val < scaled.val.length := by rw [hs.1]; exact hjlt
      step as ⟨r, hr⟩
      have hrwf : Wf r := by rw [hr]; exact hdw _ (List.getElem_mem hdjb)
      simp only [linalg.PolyVec.get]
      step as ⟨r1, hr1⟩
      have hr1wf : Wf r1 := by rw [hr1]; exact hs.2 _ (List.getElem_mem hsjb)
      step with HachiEquiv.RqBridge.add_spec r r1 hrwf hr1wf as ⟨r2, hr2wf, hr2val⟩
      step as ⟨elem, back, helem, hback⟩
      step as ⟨jj1, hjj1⟩
      rw [hback]
      refine ⟨by rw [hjj1]; omega, ?_, all_set hdw hr2wf, ?_, by rw [hjj1]; omega⟩
      · rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hdl
      · intro t ht
        rw [hjj1]
        by_cases heq : t = jj.val
        · have hdgetD : d.val.getD jj.val (alloc.vec.Vec.new cpoly.field.Fp) = r := by
            rw [hr, List.getD_eq_getElem _ _ hdjb]
          have hsgetD : scaled.val.getD jj.val (alloc.vec.Vec.new cpoly.field.Fp) = r1 := by
            rw [hr1, List.getD_eq_getElem _ _ hsjb]
          rw [heq, vgetD_set_eq hdjb, hr2val, ← hdgetD, hdv jj.val hjlt,
            if_neg (by omega), add_zero, hsgetD, if_pos (by omega)]
        · rw [vgetD_set_ne heq, hdv t ht]
          by_cases hlt2 : t < jj.val
          · rw [if_pos hlt2, if_pos (by omega)]
          · rw [if_neg hlt2, if_neg (by omega)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = width := by rw [← hw]; scalar_tac
      refine ⟨hdl, hdw, ?_⟩
      intro t ht
      rw [hdv t ht, heq, if_pos ht]
  · exact ⟨hj, hlen, hwf, hval⟩

/-- The block loop of `quadeval::honest_z`.

The two branches of `classify_short` discharge to the *same* pointwise goal --
`prev t + toRq cᵢ * toRq messageᵢ[t]` -- the `some` branch through
`RqBridge.mul_short_add_into_spec` and the `none` branch through the generic
`scalar_vec_mul` followed by `Rq::add`. -/
theorem honest_z_loop1_spec {width blocks : ℕ} (message : alloc.vec.Vec linalg.PolyVec)
    (c : linalg.PolyVec) (blocksU widthU : Std.Usize)
    (acc : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hm : WfBlocks blocks width message) (hc : WfVec blocks c)
    (hn : blocksU.val = blocks) (hw : widthU.val = width)
    (hi : i.val ≤ blocks) (hlen : acc.val.length = width)
    (hwf : ∀ x ∈ acc.val, Wf x)
    (hval : ∀ t, t < width →
      toRq (acc.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        = ∑ j ∈ Finset.range i.val,
            toRq (c.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
              * toRq ((message.val.getD j (alloc.vec.Vec.new ring.Rq)).val.getD t
                  (alloc.vec.Vec.new cpoly.field.Fp))) :
    quadeval.honest_z_loop1 message c blocksU widthU acc i
      ⦃ z => z.val.length = width ∧ (∀ x ∈ z.val, Wf x) ∧
        ∀ t, t < width →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = ∑ j ∈ Finset.range blocks,
                toRq (c.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
                  * toRq ((message.val.getD j (alloc.vec.Vec.new ring.Rq)).val.getD t
                      (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [quadeval.honest_z_loop1]
  apply loop.spec_decr_nat (fun r => blocks - r.2.val)
    (fun r => r.2.val ≤ blocks ∧ r.1.val.length = width ∧ (∀ x ∈ r.1.val, Wf x)
      ∧ ∀ t, t < width →
          toRq (r.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = ∑ j ∈ Finset.range r.2.val,
                toRq (c.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
                  * toRq ((message.val.getD j (alloc.vec.Vec.new ring.Rq)).val.getD t
                      (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨d, ii⟩ ⟨hii, hdl, hdw, hdv⟩
    dsimp only at hii hdl hdw hdv
    simp only [quadeval.honest_z_loop1.body]
    by_cases hlt : ii < blocksU
    · rw [if_pos hlt]
      have hiib : ii.val < blocks := by rw [← hn]; scalar_tac
      have hib : ii.val < message.val.length := by rw [hm.1]; exact hiib
      have hic : ii.val < c.val.length := by rw [hc.1]; exact hiib
      simp only [linalg.PolyVec.get]
      step as ⟨cr, hcr⟩
      have hWcr : Wf cr := by rw [hcr]; exact hc.2 _ (List.getElem_mem hic)
      have hcrv : cr = c.val.getD ii.val (alloc.vec.Vec.new cpoly.field.Fp) := by
        rw [hcr, List.getD_eq_getElem _ _ hic]
      have hmiwf : WfVec width (message.val.getD ii.val (alloc.vec.Vec.new ring.Rq)) := by
        rw [List.getD_eq_getElem _ _ hib]; exact hm.2 _ (List.getElem_mem hib)
      -- the pointwise term this block adds, shared by both branches
      set term : ℕ → Rq Φ := fun t =>
        toRq (c.val.getD ii.val (alloc.vec.Vec.new cpoly.field.Fp))
          * toRq ((message.val.getD ii.val (alloc.vec.Vec.new ring.Rq)).val.getD t
              (alloc.vec.Vec.new cpoly.field.Fp)) with hterm
      step with HachiEquiv.RingShort.classify_short_spec cr hWcr as ⟨o, ho⟩
      cases o with
      | none =>
        step as ⟨pv, hpv⟩
        have hpvv : pv = message.val.getD ii.val (alloc.vec.Vec.new ring.Rq) := by
          rw [hpv, List.getD_eq_getElem _ _ hib]
        have hWpv : WfVec width pv := by rw [hpvv]; exact hmiwf
        step with scalar_vec_mul_spec (k := width) cr pv hWcr hWpv
          as ⟨scaled, hSwf, hSval⟩
        step with honest_z_loop1_loop0_spec (width := width) widthU 0#usize scaled d
          (fun t => ∑ j ∈ Finset.range ii.val,
            toRq (c.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
              * toRq ((message.val.getD j (alloc.vec.Vec.new ring.Rq)).val.getD t
                  (alloc.vec.Vec.new cpoly.field.Fp)))
          hw hSwf (by simp) hdl hdw
          (by intro t ht; simpa using hdv t ht) as ⟨z, hzl, hzw, hzv⟩
        step as ⟨ii1, hii1⟩
        refine ⟨by rw [hii1]; omega, hzl, hzw, ?_, by rw [hii1]; omega⟩
        intro t ht
        have hst : toRq (scaled.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = term t := by
          have := congrFun hSval ⟨t, by omega⟩
          simpa [toVec, scalarVecMul, hterm, hcrv, hpvv] using this
        rw [hii1, hzv t ht, hst, hterm, Finset.sum_range_succ]
      | some desc =>
        obtain ⟨e2, e3, e4, e5⟩ := ho desc rfl
        step with honest_z_loop1_loop1_spec (width := width) message widthU ii 0#usize
          desc cr d
          (fun t => ∑ j ∈ Finset.range ii.val,
            toRq (c.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
              * toRq ((message.val.getD j (alloc.vec.Vec.new ring.Rq)).val.getD t
                  (alloc.vec.Vec.new cpoly.field.Fp)))
          hw hib hmiwf hWcr e2 e3 e4 e5 (by simp) hdl hdw
          (by intro t ht; simpa using hdv t ht) as ⟨z, hzl, hzw, hzv⟩
        step as ⟨ii1, hii1⟩
        refine ⟨by rw [hii1]; omega, hzl, hzw, ?_, by rw [hii1]; omega⟩
        intro t ht
        rw [hii1, hzv t ht, hcrv, Finset.sum_range_succ]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ii.val = blocks := by rw [← hn]; scalar_tac
      refine ⟨hdl, hdw, ?_⟩
      intro t ht
      rw [hdv t ht, heq]
  · exact ⟨hi, hlen, hwf, hval⟩

/-- The copy loop of `quadeval::honest_compute_resp`: the inner decompositions
are passed through unchanged. -/
theorem honest_compute_resp_loop_spec {blocks width : ℕ}
    (inner_decomp inner : alloc.vec.Vec linalg.PolyVec) (i : Std.Usize)
    (hid : WfBlocks blocks width inner_decomp) (hi : i.val ≤ blocks)
    (hlen : inner.val.length = i.val) (hwf : ∀ y ∈ inner.val, WfVec width y)
    (hval : ∀ j, j < i.val → toVec (k := width) (inner.val.getD j (alloc.vec.Vec.new ring.Rq))
      = toVec (k := width) (inner_decomp.val.getD j (alloc.vec.Vec.new ring.Rq))) :
    quadeval.honest_compute_resp_loop inner_decomp inner i
      ⦃ z => z.val.length = blocks ∧ (∀ y ∈ z.val, WfVec width y) ∧
        ∀ j, j < blocks → toVec (k := width) (z.val.getD j (alloc.vec.Vec.new ring.Rq))
          = toVec (k := width) (inner_decomp.val.getD j (alloc.vec.Vec.new ring.Rq)) ⦄ := by
  have hnn : (alloc.vec.Vec.len inner_decomp).val = blocks := by simpa using hid.1
  rw [quadeval.honest_compute_resp_loop]
  apply loop.spec_decr_nat (fun t => blocks - t.2.val)
    (fun t => t.2.val ≤ blocks ∧ t.1.val.length = t.2.val ∧ (∀ y ∈ t.1.val, WfVec width y) ∧
      ∀ j, j < t.2.val → toVec (k := width) (t.1.val.getD j (alloc.vec.Vec.new ring.Rq))
        = toVec (k := width) (inner_decomp.val.getD j (alloc.vec.Vec.new ring.Rq)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [quadeval.honest_compute_resp_loop.body]
    by_cases hlt : i1.val < blocks
    · rw [if_pos (by scalar_tac : i1 < alloc.vec.Vec.len inner_decomp)]
      have hix : i1.val < inner_decomp.val.length := by rw [hid.1]; exact hlt
      step as ⟨pv, hpv⟩
      have hWpv : WfVec width pv := by
        rw [hpv]; exact hid.2 _ (List.getElem_mem hix)
      step with poly_vec_copy_spec (k := width) pv hWpv as ⟨pv1, hPwf, hPval⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hPwf
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 j hjlt]
        · have hjeq : j = o1.val.length := by omega
          rw [hjeq, ho2, getD_append_eq, hPval, hpv, hlen1, List.getD_eq_getElem _ _ hix]
      · scalar_tac
    · rw [if_neg (by scalar_tac : ¬ i1 < alloc.vec.Vec.len inner_decomp), WP.spec_ok]
      dsimp only
      have heq : i1.val = blocks := by omega
      exact ⟨by rw [hlen1, heq], hwf1, by intro j hj; exact hval1 j (by omega)⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- `linalg::flatten_blocks` (`lean/Scheme.lean:656`) restated against
`toBlocks`, which is the spelling the two relation obligations consume. -/
theorem flatten_blocks_spec' {blocks width : ℕ} (xs : alloc.vec.Vec linalg.PolyVec)
    (hsize : blocks * width ≤ Usize.max) (hxs : WfBlocks blocks width xs) :
    linalg.flatten_blocks xs
      ⦃ z => WfVec (blocks * width) z ∧ toVec (k := blocks * width) z
        = PolyVec.flattenBlocks (toBlocks (blocks := blocks) (width := width) xs) ⦄ :=
  flatten_blocks_spec xs hsize hxs

/-- The `ℓ∞` range block of `rel_out`: the three `≤ γ` checks at `γ = 15`. -/
theorem chain_gamma_spec {k2 k3 : ℕ} (n1 : Std.U64) (flat zd : linalg.PolyVec)
    (hf : WfVec k2 flat) (hz : WfVec k3 zd) (m1 : ℕ) (hn1 : n1.val = m1) :
    (if n1 ≤ params.CHAIN_GAMMA then
      (do
        let i1 ← commit.vec_l_infty_norm flat
        if i1 ≤ params.CHAIN_GAMMA then
          (do
            let i2 ← commit.vec_l_infty_norm zd
            ok (i2 ≤ params.CHAIN_GAMMA))
        else ok false)
      else ok false)
      ⦃ b => b = true ↔ (m1 ≤ 15 ∧ vecLInftyNorm Φ (toVec (k := k2) flat) ≤ 15 ∧
        vecLInftyNorm Φ (toVec (k := k3) zd) ≤ 15) ⦄ := by
  have hg : (params.CHAIN_GAMMA).val = 15 := by simp [params.CHAIN_GAMMA]
  refine ite_reject_spec ?_ _ ?_
  · constructor <;> intro h <;> scalar_tac
  · step with vec_l_infty_norm_spec (k := k2) flat hf as ⟨n2, hn2⟩
    refine ite_reject_spec ?_ _ ?_
    · constructor <;> intro h <;> scalar_tac
    · step with vec_l_infty_norm_spec (k := k3) zd hz as ⟨n3, hn3⟩
      simp only [decide_eq_true_eq]
      constructor <;> intro h <;> scalar_tac

/-- The `S_β` range block of `paper_rel_out`: the three box checks at `β = 16`. -/
theorem paper_chain_spec {k2 k3 : ℕ} (b0 : Bool) (flat zd : linalg.PolyVec)
    (hf : WfVec k2 flat) (hz : WfVec k3 zd) (P0 : Prop) (hb0 : b0 = true ↔ P0) :
    (if b0 then
      (do
        let b1 ← quadeval.vec_in_sb flat
        if b1 then quadeval.vec_in_sb zd else ok false)
      else ok false)
      ⦃ b => b = true ↔ (P0 ∧ InnerOuter.vecInSb Φ 16 (toVec (k := k2) flat) ∧
        InnerOuter.vecInSb Φ 16 (toVec (k := k3) zd)) ⦄ := by
  refine ite_reject_spec hb0 _ ?_
  step with QuadEval.vec_in_sb_spec (cols := k2) flat hf as ⟨b1, hb1⟩
  exact ite_reject_spec hb1 _ (QuadEval.vec_in_sb_spec (cols := k3) zd hz)

/-- The five-flag `if` chain both output relations end in: the run accepts
exactly when every one of the six checks passes. -/
theorem rel_chain_spec {c1 c2 c3 c4 c5 c6 : Bool} {P1 P2 P3 P4 P5 P6 : Prop}
    (h1 : c1 = true ↔ P1) (h2 : c2 = true ↔ P2) (h3 : c3 = true ↔ P3)
    (h4 : c4 = true ↔ P4) (h5 : c5 = true ↔ P5) (h6 : c6 = true ↔ P6) :
    (if c1 then if c2 then if c3 then if c4 then if c5 then ok c6 else ok false
      else ok false else ok false else ok false else ok false)
      ⦃ b => b = true ↔ (P1 ∧ P2 ∧ P3 ∧ P4 ∧ P5 ∧ P6) ⦄ :=
  ite_reject_spec h1 _ (ite_reject_spec h2 _ (ite_reject_spec h3 _
    (ite_reject_spec h4 _ (ite_reject_spec h5 (ok c6) (by rw [WP.spec_ok]; exact h6)))))

/-! ## The three carriers -/

/-- The commitment key's constructor preserves the relation. -/
theorem PublicParamsD_new_spec (inner : commit.PublicParams) (d_matrix : linalg.PolyMatrix)
    (sp : Hachi.PublicParamsD Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (hi : toParams inner = sp.toPublicParams)
    (hd : toMat (rows := 1) (cols := 2 ^ 10 * 8) d_matrix = sp.dMatrix)
    (hWi : WfParams inner) (hWd : WfMat 1 (2 ^ 10 * 8) d_matrix) :
    quadeval.PublicParamsD.new inner d_matrix
      ⦃ out => RepParamsD out sp ⦄ := by
  rw [quadeval.PublicParamsD.new, WP.spec_ok]
  exact ⟨hWi, hWd, hi, hd⟩

/-- The input statement's constructor preserves the relation. -/
theorem QuadEvalStatement_new_spec (u avec bvec : linalg.PolyVec) (y : ring.Rq)
    (ss : InnerOuter.QuadEvalStatement Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (hu : toVec (k := 1) u = ss.u) (ha : toVec (k := 2 ^ 10) avec = ss.avec)
    (hb : toVec (k := 2 ^ 10) bvec = ss.bvec) (hy : toRq y = ss.y)
    (hWu : WfVec 1 u) (hWa : WfVec (2 ^ 10) avec) (hWb : WfVec (2 ^ 10) bvec) (hWy : Wf y) :
    quadeval.QuadEvalStatement.new u avec bvec y
      ⦃ out => RepStmt out ss ⦄ := by
  rw [quadeval.QuadEvalStatement.new, WP.spec_ok]
  exact ⟨hWu, hWa, hWb, hWy, hu, ha, hb, hy⟩

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
  rw [quadeval.QuadEvalResponse.new, WP.spec_ok]
  exact ⟨hWc, hWi, hWz, hc, hi, hz⟩

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
  rw [quadeval.carrier_decomp]
  step with carrier_spec (rows := 2 ^ 10) (blocks := 2 ^ 10) a s hWa hWs (by scalar_tac)
    as ⟨w, hWw, hw⟩
  apply spec_mono (Balanced.balanced_gadget_decompose_spec (rows := 2 ^ 10) w hWw (by scalar_tac))
  rintro z ⟨hzwf, hzval⟩
  exact ⟨hzwf, by rw [hzval, hw, Hachi.carrierDecomp]⟩

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
  rw [quadeval.carrier_commit]
  step with carrier_decomp_spec a s hWa hWs as ⟨what, hWwhat, hwhat⟩
  apply spec_mono (mat_vec_mul_spec (rows := 1) (cols := 2 ^ 10 * 8) d_matrix what hWd hWwhat)
  rintro z ⟨hzwf, hzval⟩
  exact ⟨hzwf, by rw [Hachi.carrierCommit, Simple.commit, hzval, hwhat]⟩

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
  rw [quadeval.j_mul]
  step as ⟨n, hn⟩
  case hmax => simp [params.MESSAGE_ROWS, params.GADGET_DIGITS]; scalar_tac
  have hnv : n.val = 2 ^ 10 * 8 := by
    have h : (2 : ℕ) ^ 10 * 8 = 8192 := by norm_num
    rw [h]
    simp only [params.MESSAGE_ROWS, params.GADGET_DIGITS] at hn
    scalar_tac
  apply spec_mono (gadget_mul_z_spec' n z_dec hnv hWz (by scalar_tac))
  rintro z ⟨hzwf, hzval⟩
  exact ⟨hzwf, by rw [hzval]; rfl⟩

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
  rw [quadeval.honest_z]
  step as ⟨width, hwidth⟩
  case hmax => simp [params.MESSAGE_ROWS, params.GADGET_DIGITS]; scalar_tac
  have hwv : width.val = 2 ^ 10 * 8 := by
    have h : (2 : ℕ) ^ 10 * 8 = 8192 := by norm_num
    rw [h]
    simp only [params.MESSAGE_ROWS, params.GADGET_DIGITS] at hwidth
    scalar_tac
  simp only [alloc.vec.Vec.with_capacity]
  step with honest_z_loop0_spec (width := 2 ^ 10 * 8) width
    (alloc.vec.Vec.new ring.Rq) 0#usize hwv (by simp) (by simp)
    (by intro x hx; simp at hx) (by intro t ht; simp at ht)
    as ⟨acc1, hA1len, hA1wf, hA1zero⟩
  step with honest_z_loop1_spec (width := 2 ^ 10 * 8) (blocks := 2 ^ 10) message c
    (alloc.vec.Vec.len message) width acc1 0#usize hWm hWc (by simpa using hWm.1)
    hwv (by simp) hA1len hA1wf
    (by intro t ht; rw [hA1zero t ht]; simp)
    as ⟨acc2, hA2len, hA2wf, hA2val⟩
  rw [linalg.PolyVec.new, WP.spec_ok]
  -- the loops deliver the fold *pointwise*; `toVec` turns that back into the
  -- function equality, and `Finset.sum_apply` is the only step involved
  have hfun : toVec (k := 2 ^ 10 * 8) acc2
      = ∑ j ∈ Finset.range (2 ^ 10),
          scalarVecMul (toRq (c.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))
            (toVec (k := 2 ^ 10 * 8)
              (message.val.getD j (alloc.vec.Vec.new ring.Rq))) := by
    funext t
    simp only [toVec, Finset.sum_apply, scalarVecMul]
    exact hA2val t.val t.isLt
  refine ⟨⟨hA2len, hA2wf⟩, ?_⟩
  rw [hfun, InnerOuter.honestZ, ← hm,
    ← Fin.sum_univ_eq_sum_range (fun j =>
      scalarVecMul (toRq (c.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))
        (toVec (k := 2 ^ 10 * 8) (message.val.getD j (alloc.vec.Vec.new ring.Rq)))) (2 ^ 10)]
  rfl

/-! ## The streamed `z` pass

`honest_z_from_raw` computes the same `z` as `honest_z`, from the raw message,
rebuilding one block's `sᵢ` per iteration instead of reading it out of a 68.7 GiB
table.

The loop spec below is `honest_z_loop1_spec` with the block vector supplied by a
decomposition rather than an index, and the device that makes that cheap is
`sv` with `hsv`: rather than putting `gadgetDecompose` in the invariant -- where
its `Fin (rows * 8)` index would fight the `∀ t, t < width` form every other
spec in this file uses -- the block family is abstract, and `hsv` is the
specification of "decomposing block `j` gives a vector whose entries are
`sv j`". The top-level theorem instantiates it from `gadget_decompose_spec`.

The inner loops are the same two `honest_z` has, at new names: Aeneas numbers
loops positionally, so the streamed function's are separate constants even
though the `None` arm's body is textually identical. -/

/-- The zero-fill loop of `quadeval::honest_z_from_raw`. Byte-identical to
`honest_z_loop0_spec`'s; Aeneas names loops positionally, so it is a separate
constant. -/
theorem honest_z_from_raw_loop0_spec {width : ℕ} (widthU : Std.Usize)
    (acc : alloc.vec.Vec ring.Rq) (zU : Std.Usize)
    (hw : widthU.val = width) (hz : zU.val ≤ width)
    (hlen : acc.val.length = zU.val) (hwf : ∀ x ∈ acc.val, Wf x)
    (hval : ∀ t, t < zU.val →
      toRq (acc.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = 0) :
    quadeval.honest_z_from_raw_loop0 widthU acc zU
      ⦃ z => z.val.length = width ∧ (∀ x ∈ z.val, Wf x) ∧
        ∀ t, t < width →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = 0 ⦄ := by
  rw [quadeval.honest_z_from_raw_loop0]
  apply loop.spec_decr_nat (fun r => width - r.2.val)
    (fun r => r.2.val ≤ width ∧ r.1.val.length = r.2.val
      ∧ (∀ x ∈ r.1.val, Wf x)
      ∧ ∀ t, t < r.2.val →
          toRq (r.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = 0)
  · rintro ⟨d, zz⟩ ⟨hzz, hdl, hdw, hdv⟩
    dsimp only at hzz hdl hdw hdv
    simp only [quadeval.honest_z_from_raw_loop0.body]
    by_cases hlt : zz < widthU
    · rw [if_pos hlt]
      have hzlt : zz.val < width := by rw [← hw]; scalar_tac
      step with HachiEquiv.RqBridge.zero_spec as ⟨r, hrwf, hrval⟩
      step as ⟨d1, hd1⟩
      step as ⟨zz1, hzz1⟩
      refine ⟨by rw [hzz1]; omega, ?_, ?_, ?_, by rw [hzz1]; omega⟩
      · rw [hd1, hzz1, List.length_append, hdl]; simp
      · intro x hx
        rw [hd1] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hdw x h
        · rw [List.mem_singleton.mp h]; exact hrwf
      · intro t ht
        rw [hzz1] at ht
        rcases Nat.lt_or_ge t zz.val with htlt | htge
        · rw [hd1, getD_append_lt _ _ _ (by omega)]
          exact hdv t htlt
        · have hteq : t = d.val.length := by omega
          rw [hteq, hd1, getD_append_eq]; exact hrval
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : zz.val = width := by rw [← hw]; scalar_tac
      exact ⟨by rw [hdl, heq], hdw, fun t ht => hdv t (by rw [heq]; exact ht)⟩
  · exact ⟨hz, hlen, hwf, hval⟩

/-- The fallback branch's inner loop, at the streamed function's name. -/
theorem honest_z_from_raw_loop1_loop0_spec {width : ℕ} (widthU jU : Std.Usize)
    (scaled : linalg.PolyVec) (acc : alloc.vec.Vec ring.Rq) (prev : ℕ → Rq Φ)
    (hw : widthU.val = width) (hs : WfVec width scaled)
    (hj : jU.val ≤ width) (hlen : acc.val.length = width)
    (hwf : ∀ x ∈ acc.val, Wf x)
    (hval : ∀ t, t < width →
      toRq (acc.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        = prev t + (if t < jU.val then
            toRq (scaled.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) else 0)) :
    quadeval.honest_z_from_raw_loop1_loop0 widthU acc scaled jU
      ⦃ z => z.val.length = width ∧ (∀ x ∈ z.val, Wf x) ∧
        ∀ t, t < width →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = prev t
                + toRq (scaled.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [quadeval.honest_z_from_raw_loop1_loop0]
  apply loop.spec_decr_nat (fun r => width - r.2.val)
    (fun r => r.2.val ≤ width ∧ r.1.val.length = width ∧ (∀ x ∈ r.1.val, Wf x)
      ∧ ∀ t, t < width →
          toRq (r.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = prev t + (if t < r.2.val then
                toRq (scaled.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) else 0))
  · rintro ⟨d, jj⟩ ⟨hjj, hdl, hdw, hdv⟩
    dsimp only at hjj hdl hdw hdv
    simp only [quadeval.honest_z_from_raw_loop1_loop0.body]
    by_cases hlt : jj < widthU
    · rw [if_pos hlt]
      have hjlt : jj.val < width := by rw [← hw]; scalar_tac
      have hdjb : jj.val < d.val.length := by rw [hdl]; exact hjlt
      have hsjb : jj.val < scaled.val.length := by rw [hs.1]; exact hjlt
      step as ⟨r, hr⟩
      have hrwf : Wf r := by rw [hr]; exact hdw _ (List.getElem_mem hdjb)
      simp only [linalg.PolyVec.get]
      step as ⟨r1, hr1⟩
      have hr1wf : Wf r1 := by rw [hr1]; exact hs.2 _ (List.getElem_mem hsjb)
      step with HachiEquiv.RqBridge.add_spec r r1 hrwf hr1wf as ⟨r2, hr2wf, hr2val⟩
      step as ⟨elem, back, helem, hback⟩
      step as ⟨jj1, hjj1⟩
      rw [hback]
      refine ⟨by rw [hjj1]; omega, ?_, all_set hdw hr2wf, ?_, by rw [hjj1]; omega⟩
      · rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hdl
      · intro t ht
        rw [hjj1]
        by_cases heq : t = jj.val
        · have hdgetD : d.val.getD jj.val (alloc.vec.Vec.new cpoly.field.Fp) = r := by
            rw [hr, List.getD_eq_getElem _ _ hdjb]
          have hsgetD : scaled.val.getD jj.val (alloc.vec.Vec.new cpoly.field.Fp) = r1 := by
            rw [hr1, List.getD_eq_getElem _ _ hsjb]
          rw [heq, vgetD_set_eq hdjb, hr2val, ← hdgetD, hdv jj.val hjlt,
            if_neg (by omega), add_zero, hsgetD, if_pos (by omega)]
        · rw [vgetD_set_ne heq, hdv t ht]
          by_cases hlt2 : t < jj.val
          · rw [if_pos hlt2, if_pos (by omega)]
          · rw [if_neg hlt2, if_neg (by omega)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = width := by rw [← hw]; scalar_tac
      refine ⟨hdl, hdw, ?_⟩
      intro t ht
      rw [hdv t ht, heq, if_pos ht]
  · exact ⟨hj, hlen, hwf, hval⟩

/-- The short branch's inner loop, with the block in hand as a local. -/
theorem honest_z_from_raw_loop1_loop1_spec {width : ℕ} (s : linalg.PolyVec)
    (widthU jU : Std.Usize) (desc : ring.ShortMul) (ci : ring.Rq)
    (acc : alloc.vec.Vec ring.Rq) (prev : ℕ → Rq Φ)
    (hw : widthU.val = width) (hmi : WfVec width s)
    (hci : Wf ci)
    (hmlen : desc.idx.val.length ≤ desc.mag.val.length)
    (hnlen : desc.idx.val.length ≤ desc.neg.val.length)
    (hidx : ∀ u, u < desc.idx.val.length →
      HachiEquiv.RingShort.idxAt desc.idx u < N)
    (hden : ∀ j, j < N → coeffK ci j
      = HachiEquiv.RingShort.descCoeffW desc.idx desc.mag desc.neg
          desc.idx.val.length j)
    (hj : jU.val ≤ width) (hlen : acc.val.length = width)
    (hwf : ∀ x ∈ acc.val, Wf x)
    (hval : ∀ t, t < width →
      toRq (acc.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        = prev t + (if t < jU.val then toRq ci
            * toRq (s.val.getD t
                (alloc.vec.Vec.new cpoly.field.Fp)) else 0)) :
    quadeval.honest_z_from_raw_loop1_loop1 widthU acc s desc jU
      ⦃ z => z.val.length = width ∧ (∀ x ∈ z.val, Wf x) ∧
        ∀ t, t < width →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = prev t + toRq ci
                * toRq (s.val.getD t
                    (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [quadeval.honest_z_from_raw_loop1_loop1]
  apply loop.spec_decr_nat (fun r => width - r.2.val)
    (fun r => r.2.val ≤ width ∧ r.1.val.length = width ∧ (∀ x ∈ r.1.val, Wf x)
      ∧ ∀ t, t < width →
          toRq (r.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = prev t + (if t < r.2.val then toRq ci
                * toRq (s.val.getD t
                    (alloc.vec.Vec.new cpoly.field.Fp)) else 0))
  · rintro ⟨d, jj⟩ ⟨hjj, hdl, hdw, hdv⟩
    dsimp only at hjj hdl hdw hdv
    simp only [quadeval.honest_z_from_raw_loop1_loop1.body]
    by_cases hlt : jj < widthU
    · rw [if_pos hlt]
      have hjlt : jj.val < width := by rw [← hw]; scalar_tac
      -- `s` is a local, so it is indexed directly: no outer `message[i]` step
      have hjb : jj.val < s.val.length := by rw [hmi.1]; exact hjlt
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hrwf : Wf r := by rw [hr]; exact hmi.2 _ (List.getElem_mem hjb)
      step as ⟨elem, back, helem, hback⟩
      have hdjb : jj.val < d.val.length := by rw [hdl]; exact hjlt
      have hewf : Wf elem := by rw [helem]; exact hdw _ (List.getElem_mem hdjb)
      step with HachiEquiv.RqBridge.mul_short_add_into_spec desc r elem ci hrwf
        hci hewf hmlen hnlen hidx hden as ⟨r2, hr2wf, hr2val⟩
      step as ⟨jj1, hjj1⟩
      rw [hback]
      refine ⟨by rw [hjj1]; omega, ?_, all_set hdw hr2wf, ?_, by rw [hjj1]; omega⟩
      · rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hdl
      · intro t ht
        rw [hjj1]
        by_cases heq : t = jj.val
        · have hdgetD : d.val.getD jj.val (alloc.vec.Vec.new cpoly.field.Fp) = elem := by
            rw [helem, List.getD_eq_getElem _ _ hdjb]
          have hrg : r = s.val.getD jj.val (alloc.vec.Vec.new cpoly.field.Fp) := by
            rw [hr, List.getD_eq_getElem _ _ hjb]
          rw [heq, vgetD_set_eq hdjb, hr2val, ← hdgetD, hdv jj.val hjlt,
            if_neg (by omega), add_zero, hrg, if_pos (by omega)]
        · rw [vgetD_set_ne heq, hdv t ht]
          by_cases hlt2 : t < jj.val
          · rw [if_pos hlt2, if_pos (by omega)]
          · rw [if_neg hlt2, if_neg (by omega)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = width := by rw [← hw]; scalar_tac
      refine ⟨hdl, hdw, ?_⟩
      intro t ht
      rw [hdv t ht, heq, if_pos ht]
  · exact ⟨hj, hlen, hwf, hval⟩

/-- The block loop of `quadeval::honest_z_from_raw`.

`honest_z_loop1_spec` with the block vector supplied by a decomposition rather
than an index. The abstract family `sv`, pinned by `hsv`, is what keeps the
invariant in the `∀ t, t < width` form every other spec in this file uses:
putting `gadgetDecompose` there directly would drag its `Fin (rows * 8)` index
into an arithmetic side condition at every step. `hsv` is itself a
specification -- "decomposing block `j` gives a vector whose entries are
`sv j`" -- which the top-level theorem discharges from
`gadget_decompose_spec`. -/
theorem honest_z_from_raw_loop1_spec {width blocks rows : ℕ}
    (raw : alloc.vec.Vec linalg.PolyVec) (c : linalg.PolyVec)
    (blocksU widthU : Std.Usize) (acc : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (sv : ℕ → ℕ → Rq Φ)
    (hraw : WfBlocks blocks rows raw) (hc : WfVec blocks c)
    (hn : blocksU.val = blocks) (hw : widthU.val = width)
    (hsv : ∀ j, j < blocks →
      gadget.gadget_decompose (raw.val.getD j (alloc.vec.Vec.new ring.Rq))
        ⦃ s => WfVec width s ∧ ∀ t, t < width →
                 toRq (s.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = sv j t ⦄)
    (hi : i.val ≤ blocks) (hlen : acc.val.length = width)
    (hwf : ∀ x ∈ acc.val, Wf x)
    (hval : ∀ t, t < width →
      toRq (acc.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        = ∑ j ∈ Finset.range i.val,
            toRq (c.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) * sv j t) :
    quadeval.honest_z_from_raw_loop1 raw c blocksU widthU acc i
      ⦃ z => z.val.length = width ∧ (∀ x ∈ z.val, Wf x) ∧
        ∀ t, t < width →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = ∑ j ∈ Finset.range blocks,
                toRq (c.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) * sv j t ⦄ := by
  rw [quadeval.honest_z_from_raw_loop1]
  apply loop.spec_decr_nat (fun r => blocks - r.2.val)
    (fun r => r.2.val ≤ blocks ∧ r.1.val.length = width ∧ (∀ x ∈ r.1.val, Wf x)
      ∧ ∀ t, t < width →
          toRq (r.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = ∑ j ∈ Finset.range r.2.val,
                toRq (c.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) * sv j t)
  · rintro ⟨d, ii⟩ ⟨hii, hdl, hdw, hdv⟩
    dsimp only at hii hdl hdw hdv
    simp only [quadeval.honest_z_from_raw_loop1.body]
    by_cases hlt : ii < blocksU
    · rw [if_pos hlt]
      have hiib : ii.val < blocks := by rw [← hn]; scalar_tac
      have hib : ii.val < raw.val.length := by rw [hraw.1]; exact hiib
      have hic : ii.val < c.val.length := by rw [hc.1]; exact hiib
      -- the block, decomposed here and dropped at the end of the iteration
      step as ⟨pv, hpv⟩
      have hri : raw.val.getD ii.val (alloc.vec.Vec.new ring.Rq) = pv := by
        rw [hpv, List.getD_eq_getElem _ _ hib]
      have hdec := hsv ii.val hiib
      rw [hri] at hdec
      step with hdec as ⟨s, hWs, hsval⟩
      simp only [linalg.PolyVec.get]
      step as ⟨cr, hcr⟩
      have hWcr : Wf cr := by rw [hcr]; exact hc.2 _ (List.getElem_mem hic)
      have hcrv : cr = c.val.getD ii.val (alloc.vec.Vec.new cpoly.field.Fp) := by
        rw [hcr, List.getD_eq_getElem _ _ hic]
      step with HachiEquiv.RingShort.classify_short_spec cr hWcr as ⟨o, ho⟩
      cases o with
      | none =>
        step with scalar_vec_mul_spec (k := width) cr s hWcr hWs
          as ⟨scaled, hSwf, hSval⟩
        step with honest_z_from_raw_loop1_loop0_spec (width := width) widthU 0#usize
          scaled d
          (fun t => ∑ j ∈ Finset.range ii.val,
            toRq (c.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) * sv j t)
          hw hSwf (by simp) hdl hdw
          (by intro t ht; simpa using hdv t ht) as ⟨z, hzl, hzw, hzv⟩
        step as ⟨ii1, hii1⟩
        refine ⟨by rw [hii1]; omega, hzl, hzw, ?_, by rw [hii1]; omega⟩
        intro t ht
        have hst : toRq (scaled.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = toRq (c.val.getD ii.val (alloc.vec.Vec.new cpoly.field.Fp)) * sv ii.val t := by
          have h1 := congrFun hSval ⟨t, by omega⟩
          simp only [toVec, scalarVecMul] at h1
          rw [h1, hcrv, hsval t ht]
        rw [hii1, hzv t ht, hst, Finset.sum_range_succ]
      | some desc =>
        obtain ⟨e2, e3, e4, e5⟩ := ho desc rfl
        step with honest_z_from_raw_loop1_loop1_spec (width := width) s widthU 0#usize
          desc cr d
          (fun t => ∑ j ∈ Finset.range ii.val,
            toRq (c.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) * sv j t)
          hw hWs hWcr e2 e3 e4 e5 (by simp) hdl hdw
          (by intro t ht; simpa using hdv t ht) as ⟨z, hzl, hzw, hzv⟩
        step as ⟨ii1, hii1⟩
        refine ⟨by rw [hii1]; omega, hzl, hzw, ?_, by rw [hii1]; omega⟩
        intro t ht
        rw [hii1, hzv t ht, hcrv, hsval t ht, Finset.sum_range_succ]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ii.val = blocks := by rw [← hn]; scalar_tac
      refine ⟨hdl, hdw, ?_⟩
      intro t ht
      rw [hdv t ht, heq]
  · exact ⟨hi, hlen, hwf, hval⟩

/-- **`quadeval::honest_z_from_raw` computes `honestZ`.**

`honest_z_spec`'s conclusion, word for word. What changes is the hypothesis: the
message blocks are no longer handed in decomposed, so `hm` ties the *raw* blocks
to the opening through `gadgetDecompose`. That is the whole statement of the
change -- the prover reads the raw message and the value is unaffected. -/
theorem honest_z_from_raw_spec (raw : alloc.vec.Vec linalg.PolyVec) (c : linalg.PolyVec)
    (wo : InnerOuter.Opening Φ 1 (2 ^ 10) 8 (2 ^ 10) 8)
    (hc : ∀ i : Fin (2 ^ 10), Rq.l1Norm Φ (toVec (k := 2 ^ 10) c i) ≤ 16)
    (hm : (fun i : Fin (2 ^ 10) => gadgetDecompose Φ dd
            (toVec (k := 2 ^ 10) (raw.val.getD i.val (alloc.vec.Vec.new ring.Rq))))
          = wo.message)
    (hWraw : WfBlocks (2 ^ 10) (2 ^ 10) raw) (hWc : WfVec (2 ^ 10) c) :
    quadeval.honest_z_from_raw raw c
      ⦃ out => WfVec (2 ^ 10 * 8) out ∧
        toVec (k := 2 ^ 10 * 8) out = InnerOuter.honestZ Φ wo (toChals c hc) ⦄ := by
  rw [quadeval.honest_z_from_raw]
  step as ⟨width, hwidth⟩
  case hmax => simp [params.MESSAGE_ROWS, params.GADGET_DIGITS]; scalar_tac
  have hwv : width.val = 2 ^ 10 * 8 := by
    have h : (2 : ℕ) ^ 10 * 8 = 8192 := by norm_num
    rw [h]
    simp only [params.MESSAGE_ROWS, params.GADGET_DIGITS] at hwidth
    scalar_tac
  simp only [alloc.vec.Vec.with_capacity]
  step with honest_z_from_raw_loop0_spec (width := 2 ^ 10 * 8) width
    (alloc.vec.Vec.new ring.Rq) 0#usize hwv (by simp) (by simp)
    (by intro x hx; simp at hx) (by intro t ht; simp at ht)
    as ⟨acc1, hA1len, hA1wf, hA1zero⟩
  -- the block family, and its defining specification, both from
  -- `gadget_decompose_spec` at one block
  set sv : ℕ → ℕ → Rq Φ := fun j t =>
    if h : t < 2 ^ 10 * 8 then
      gadgetDecompose Φ dd
        (toVec (k := 2 ^ 10) (raw.val.getD j (alloc.vec.Vec.new ring.Rq))) ⟨t, h⟩
    else 0 with hsvdef
  have hsv : ∀ j, j < 2 ^ 10 →
      gadget.gadget_decompose (raw.val.getD j (alloc.vec.Vec.new ring.Rq))
        ⦃ s => WfVec (2 ^ 10 * 8) s ∧ ∀ t, t < 2 ^ 10 * 8 →
                 toRq (s.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = sv j t ⦄ := by
    intro j hj
    have hWj : WfVec (2 ^ 10) (raw.val.getD j (alloc.vec.Vec.new ring.Rq)) := by
      rw [List.getD_eq_getElem _ _ (by rw [hWraw.1]; exact hj)]
      exact hWraw.2 _ (List.getElem_mem _)
    apply spec_mono (gadget_decompose_spec (rows := 2 ^ 10)
      (raw.val.getD j (alloc.vec.Vec.new ring.Rq)) hWj (by scalar_tac))
    rintro s ⟨hWs, hsval⟩
    refine ⟨hWs, ?_⟩
    intro t ht
    have h1 : toVec (k := 2 ^ 10 * 8) s ⟨t, ht⟩
        = toRq (s.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) := rfl
    rw [hsvdef]
    simp only [dif_pos ht]
    rw [← h1, hsval]
  step with honest_z_from_raw_loop1_spec (width := 2 ^ 10 * 8) (blocks := 2 ^ 10)
    (rows := 2 ^ 10) raw c (alloc.vec.Vec.len raw) width acc1 0#usize sv
    hWraw hWc (by simpa using hWraw.1) hwv hsv (by simp) hA1len hA1wf
    (by intro t ht; rw [hA1zero t ht]; simp)
    as ⟨acc2, hA2len, hA2wf, hA2val⟩
  rw [linalg.PolyVec.new, WP.spec_ok]
  -- the loops deliver the fold pointwise; this is `honest_z_spec`'s tail with
  -- `sv` unfolded back into the decomposition it was standing for
  have hfun : toVec (k := 2 ^ 10 * 8) acc2
      = ∑ j ∈ Finset.range (2 ^ 10),
          scalarVecMul (toRq (c.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))
            (gadgetDecompose Φ dd
              (toVec (k := 2 ^ 10) (raw.val.getD j (alloc.vec.Vec.new ring.Rq)))) := by
    funext t
    simp only [toVec, Finset.sum_apply, scalarVecMul]
    rw [hA2val t.val t.isLt]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    -- `sv` is already unfolded here, so all that is left is the guard
    rw [dif_pos t.isLt]
  refine ⟨⟨hA2len, hA2wf⟩, ?_⟩
  rw [hfun, InnerOuter.honestZ, ← hm,
    ← Fin.sum_univ_eq_sum_range (fun j =>
      scalarVecMul (toRq (c.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))
        (gadgetDecompose Φ dd
          (toVec (k := 2 ^ 10) (raw.val.getD j (alloc.vec.Vec.new ring.Rq))))) (2 ^ 10)]
  rfl

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
  obtain ⟨hWpi, hWpd, hpi, hpd⟩ := hpp
  obtain ⟨hWu, hWa, hWb, hWy, hu, ha, hb, hy⟩ := hst
  rw [quadeval.honest_compute_v]
  simp only [quadeval.PublicParamsD.impl.d_matrix, quadeval.QuadEvalStatement.impl.avec,
    bind_tc_ok]
  apply spec_mono (carrier_commit_spec pp.d_matrix stmt.avec message hWpd hWa hWm)
  rintro z ⟨hzwf, hzval⟩
  refine ⟨hzwf, ?_⟩
  rw [hzval, hpd, ha, hm, InnerOuter.honestComputeV]

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
  obtain ⟨hWu, hWa, hWb, hWy, hu, ha, hb, hy⟩ := hst
  rw [quadeval.honest_compute_resp]
  simp only [quadeval.QuadEvalStatement.impl.avec, bind_tc_ok]
  step with carrier_decomp_spec stmt.avec message hWa hWm as ⟨cdec, hCwf, hCval⟩
  step with honest_z_spec message c wo hc hm hWm hWc as ⟨zz, hZwf, hZval⟩
  step with QuadEval.bounded_z_gadget_decompose_spec (rows := 2 ^ 10 * 8) zz hZwf (by scalar_tac)
    as ⟨zdec, hDwf, hDval⟩
  step with honest_compute_resp_loop_spec (blocks := 2 ^ 10) (width := 1 * 8) inner_decomp
    (alloc.vec.Vec.new linalg.PolyVec) 0#usize hWi (by simp) (by simp)
    (by intro y hy; simp at hy) (by intro j hj; simp at hj)
    as ⟨inner, hIlen, hIwf, hIval⟩
  rw [quadeval.QuadEvalResponse.new, WP.spec_ok]
  refine ⟨hCwf, ⟨hIlen, hIwf⟩, hDwf, ?_, ?_, ?_⟩
  · show toVec (k := 2 ^ 10 * 8) cdec = Hachi.carrierDecomp Φ ddBal ss.avec wo.message
    rw [hCval, ha, hm]
  · show toBlocks (blocks := 2 ^ 10) (width := 1 * 8) inner = wo.innerDecomp
    rw [← hi]
    funext j
    exact hIval j.val j.isLt
  · show toVec (k := 2 ^ 10 * 8 * 5) zdec
      = Hachi.zDecompBounded Φ bddZ (InnerOuter.honestZ Φ wo (toChals c hc))
    rw [hDval, hZval, Hachi.zDecompBounded]

/-! ### The streamed prover's entry points

The three specifications below are the ones above with the message blocks handed
in **raw**: each hypothesis `toBlocks message = wo.message` becomes
"the decomposition of `raw` is `wo.message`", and nothing in any conclusion
moves. Together with `Scheme.commit_streamed_spec` they are what lets the honest
prover run without ever holding `Decomp.message`. -/

/-- The inner-decomposition copy loop, at the streamed function's name. -/
theorem honest_compute_resp_from_raw_loop_spec {blocks width : ℕ}
    (inner_decomp inner : alloc.vec.Vec linalg.PolyVec) (i : Std.Usize)
    (hid : WfBlocks blocks width inner_decomp) (hi : i.val ≤ blocks)
    (hlen : inner.val.length = i.val) (hwf : ∀ y ∈ inner.val, WfVec width y)
    (hval : ∀ j, j < i.val → toVec (k := width) (inner.val.getD j (alloc.vec.Vec.new ring.Rq))
      = toVec (k := width) (inner_decomp.val.getD j (alloc.vec.Vec.new ring.Rq))) :
    quadeval.honest_compute_resp_from_raw_loop inner_decomp inner i
      ⦃ z => z.val.length = blocks ∧ (∀ y ∈ z.val, WfVec width y) ∧
        ∀ j, j < blocks → toVec (k := width) (z.val.getD j (alloc.vec.Vec.new ring.Rq))
          = toVec (k := width) (inner_decomp.val.getD j (alloc.vec.Vec.new ring.Rq)) ⦄ := by
  have hnn : (alloc.vec.Vec.len inner_decomp).val = blocks := by simpa using hid.1
  rw [quadeval.honest_compute_resp_from_raw_loop]
  apply loop.spec_decr_nat (fun t => blocks - t.2.val)
    (fun t => t.2.val ≤ blocks ∧ t.1.val.length = t.2.val ∧ (∀ y ∈ t.1.val, WfVec width y) ∧
      ∀ j, j < t.2.val → toVec (k := width) (t.1.val.getD j (alloc.vec.Vec.new ring.Rq))
        = toVec (k := width) (inner_decomp.val.getD j (alloc.vec.Vec.new ring.Rq)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [quadeval.honest_compute_resp_from_raw_loop.body]
    by_cases hlt : i1.val < blocks
    · rw [if_pos (by scalar_tac : i1 < alloc.vec.Vec.len inner_decomp)]
      have hix : i1.val < inner_decomp.val.length := by rw [hid.1]; exact hlt
      step as ⟨pv, hpv⟩
      have hWpv : WfVec width pv := by
        rw [hpv]; exact hid.2 _ (List.getElem_mem hix)
      step with poly_vec_copy_spec (k := width) pv hWpv as ⟨pv1, hPwf, hPval⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hPwf
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 j hjlt]
        · have hjeq : j = o1.val.length := by omega
          rw [hjeq, ho2, getD_append_eq, hPval, hpv, hlen1, List.getD_eq_getElem _ _ hix]
      · scalar_tac
    · rw [if_neg (by scalar_tac : ¬ i1 < alloc.vec.Vec.len inner_decomp), WP.spec_ok]
      dsimp only
      have heq : i1.val = blocks := by omega
      exact ⟨by rw [hlen1, heq], hwf1, by intro j hj; exact hval1 j (by omega)⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- The raw-message carrier decomposition. -/
theorem carrier_decomp_from_raw_spec (a : linalg.PolyVec)
    (raw : alloc.vec.Vec linalg.PolyVec)
    (hWa : WfVec (2 ^ 10) a) (hWraw : WfBlocks (2 ^ 10) (2 ^ 10) raw) :
    quadeval.carrier_decomp_from_raw a raw
      ⦃ out => WfVec (2 ^ 10 * 8) out ∧
        toVec (k := 2 ^ 10 * 8) out
          = Hachi.carrierDecomp Φ ddBal (toVec (k := 2 ^ 10) a)
              (fun i : Fin (2 ^ 10) => gadgetDecompose Φ dd
                (toVec (k := 2 ^ 10) (raw.val.getD i.val (alloc.vec.Vec.new ring.Rq)))) ⦄ := by
  rw [quadeval.carrier_decomp_from_raw]
  step with carrier_from_raw_spec (rows := 2 ^ 10) (blocks := 2 ^ 10) a raw hWa hWraw
    as ⟨w, hWw, hw⟩
  apply spec_mono (Balanced.balanced_gadget_decompose_spec (rows := 2 ^ 10) w hWw (by scalar_tac))
  rintro z ⟨hzwf, hzval⟩
  exact ⟨hzwf, by rw [hzval, hw, Hachi.carrierDecomp]⟩

/-- The raw-message carrier commitment. -/
theorem carrier_commit_from_raw_spec (d_matrix : linalg.PolyMatrix) (a : linalg.PolyVec)
    (raw : alloc.vec.Vec linalg.PolyVec)
    (hWd : WfMat 1 (2 ^ 10 * 8) d_matrix) (hWa : WfVec (2 ^ 10) a)
    (hWraw : WfBlocks (2 ^ 10) (2 ^ 10) raw) :
    quadeval.carrier_commit_from_raw d_matrix a raw
      ⦃ out => WfVec 1 out ∧
        toVec (k := 1) out
          = Hachi.carrierCommit Φ (toMat (rows := 1) (cols := 2 ^ 10 * 8) d_matrix) ddBal
              (toVec (k := 2 ^ 10) a)
              (fun i : Fin (2 ^ 10) => gadgetDecompose Φ dd
                (toVec (k := 2 ^ 10) (raw.val.getD i.val (alloc.vec.Vec.new ring.Rq)))) ⦄ := by
  rw [quadeval.carrier_commit_from_raw]
  step with carrier_decomp_from_raw_spec a raw hWa hWraw as ⟨what, hWwhat, hwhat⟩
  apply spec_mono (mat_vec_mul_spec (rows := 1) (cols := 2 ^ 10 * 8) d_matrix what hWd hWwhat)
  rintro z ⟨hzwf, hzval⟩
  exact ⟨hzwf, by rw [Hachi.carrierCommit, Simple.commit, hzval, hwhat]⟩

/-- **`honest_compute_v_from_raw` computes `honestComputeV`** -- the same round-0
message, from the raw blocks. This is what `chain_open` calls. -/
theorem honest_compute_v_from_raw_spec (pp : quadeval.PublicParamsD)
    (stmt : quadeval.QuadEvalStatement) (raw : alloc.vec.Vec linalg.PolyVec)
    (sp : Hachi.PublicParamsD Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (ss : InnerOuter.QuadEvalStatement Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (wo : InnerOuter.Opening Φ 1 (2 ^ 10) 8 (2 ^ 10) 8)
    (hpp : RepParamsD pp sp) (hst : RepStmt stmt ss)
    (hm : (fun i : Fin (2 ^ 10) => gadgetDecompose Φ dd
            (toVec (k := 2 ^ 10) (raw.val.getD i.val (alloc.vec.Vec.new ring.Rq))))
          = wo.message)
    (hWraw : WfBlocks (2 ^ 10) (2 ^ 10) raw) :
    quadeval.honest_compute_v_from_raw pp stmt raw
      ⦃ out => WfVec 1 out ∧
        toVec (k := 1) out = InnerOuter.honestComputeV Φ sp ddBal ss wo ⦄ := by
  obtain ⟨hWpi, hWpd, hpi, hpd⟩ := hpp
  obtain ⟨hWu, hWa, hWb, hWy, hu, ha, hb, hy⟩ := hst
  rw [quadeval.honest_compute_v_from_raw]
  simp only [quadeval.PublicParamsD.impl.d_matrix, quadeval.QuadEvalStatement.impl.avec,
    bind_tc_ok]
  apply spec_mono (carrier_commit_from_raw_spec pp.d_matrix stmt.avec raw hWpd hWa hWraw)
  rintro z ⟨hzwf, hzval⟩
  refine ⟨hzwf, ?_⟩
  rw [hzval, hpd, ha, hm, InnerOuter.honestComputeV]

/-- **`honest_compute_resp_from_raw` computes `honestComputeResp`** -- the second
half of the streamed prover. -/
theorem honest_compute_resp_from_raw_spec (stmt : quadeval.QuadEvalStatement)
    (raw inner_decomp : alloc.vec.Vec linalg.PolyVec) (c : linalg.PolyVec)
    (ss : InnerOuter.QuadEvalStatement Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (wo : InnerOuter.Opening Φ 1 (2 ^ 10) 8 (2 ^ 10) 8)
    (hc : ∀ i : Fin (2 ^ 10), Rq.l1Norm Φ (toVec (k := 2 ^ 10) c i) ≤ 16)
    (hst : RepStmt stmt ss)
    (hm : (fun i : Fin (2 ^ 10) => gadgetDecompose Φ dd
            (toVec (k := 2 ^ 10) (raw.val.getD i.val (alloc.vec.Vec.new ring.Rq))))
          = wo.message)
    (hi : toBlocks (blocks := 2 ^ 10) (width := 1 * 8) inner_decomp = wo.innerDecomp)
    (hWraw : WfBlocks (2 ^ 10) (2 ^ 10) raw)
    (hWi : WfBlocks (2 ^ 10) (1 * 8) inner_decomp) (hWc : WfVec (2 ^ 10) c) :
    quadeval.honest_compute_resp_from_raw stmt raw inner_decomp c
      ⦃ out => RepResp out
        (InnerOuter.honestComputeResp Φ ddBal bddZ ss wo (toChals c hc)) ⦄ := by
  obtain ⟨hWu, hWa, hWb, hWy, hu, ha, hb, hy⟩ := hst
  rw [quadeval.honest_compute_resp_from_raw]
  simp only [quadeval.QuadEvalStatement.impl.avec, bind_tc_ok]
  step with carrier_decomp_from_raw_spec stmt.avec raw hWa hWraw as ⟨cdec, hCwf, hCval⟩
  step with honest_z_from_raw_spec raw c wo hc hm hWraw hWc as ⟨zz, hZwf, hZval⟩
  step with QuadEval.bounded_z_gadget_decompose_spec (rows := 2 ^ 10 * 8) zz hZwf (by scalar_tac)
    as ⟨zdec, hDwf, hDval⟩
  step with honest_compute_resp_from_raw_loop_spec (blocks := 2 ^ 10) (width := 1 * 8)
    inner_decomp (alloc.vec.Vec.new linalg.PolyVec) 0#usize hWi (by simp) (by simp)
    (by intro y hy; simp at hy) (by intro j hj; simp at hj)
    as ⟨inner, hIlen, hIwf, hIval⟩
  rw [quadeval.QuadEvalResponse.new, WP.spec_ok]
  refine ⟨hCwf, ⟨hIlen, hIwf⟩, hDwf, ?_, ?_, ?_⟩
  · show toVec (k := 2 ^ 10 * 8) cdec = Hachi.carrierDecomp Φ ddBal ss.avec wo.message
    rw [hCval, ha, hm]
  · show toBlocks (blocks := 2 ^ 10) (width := 1 * 8) inner = wo.innerDecomp
    rw [← hi]
    funext j
    exact hIval j.val j.isLt
  · show toVec (k := 2 ^ 10 * 8 * 5) zdec
      = Hachi.zDecompBounded Φ bddZ (InnerOuter.honestZ Φ wo (toChals c hc))
    rw [hDval, hZval, Hachi.zDecompBounded]


/-! ## The compact raw carrier

`Raw32.lean` proves each `_32` consumer *equal* to the item above it on the
message its words denote, so each specification here is the corresponding one
above, inherited. The carrier halves the resident raw message -- 8448 MiB to
4360 MiB, measured at the pin -- and changes no value. -/

/-- **`carrier_from_raw_32` is `carrier` at the message its words denote.** -/
theorem carrier_from_raw_32_spec {rows blocks : ℕ} (a : linalg.PolyVec)
    (raw32 : alloc.vec.Vec linalg.RawVec32) (raw : alloc.vec.Vec linalg.PolyVec)
    (hex : Raw32.ExpandsTo raw32 raw) (ha : WfVec rows a)
    (hraw : WfBlocks blocks rows raw) (hmax : rows * N ≤ Std.Usize.max) :
    quadeval.carrier_from_raw_32 a raw32
      ⦃ out => WfVec blocks out ∧ toVec (k := blocks) out
        = Hachi.carrier Φ (16 : ZMod q) (toVec (k := rows) a)
            (fun i : Fin blocks => gadgetDecompose Φ dd
              (toVec (k := rows) (raw.val.getD i.val (alloc.vec.Vec.new ring.Rq)))) ⦄ := by
  rw [Raw32.carrier_from_raw_32_eq a hex]
  exact carrier_from_raw_spec (rows := rows) (blocks := blocks) a raw ha hraw hmax

/-- The raw-message carrier decomposition, over the compact carrier. -/
theorem carrier_decomp_from_raw_32_spec (a : linalg.PolyVec)
    (raw32 : alloc.vec.Vec linalg.RawVec32) (raw : alloc.vec.Vec linalg.PolyVec)
    (hex : Raw32.ExpandsTo raw32 raw)
    (hWa : WfVec (2 ^ 10) a) (hWraw : WfBlocks (2 ^ 10) (2 ^ 10) raw) :
    quadeval.carrier_decomp_from_raw_32 a raw32
      ⦃ out => WfVec (2 ^ 10 * 8) out ∧
        toVec (k := 2 ^ 10 * 8) out
          = Hachi.carrierDecomp Φ ddBal (toVec (k := 2 ^ 10) a)
              (fun i : Fin (2 ^ 10) => gadgetDecompose Φ dd
                (toVec (k := 2 ^ 10) (raw.val.getD i.val (alloc.vec.Vec.new ring.Rq)))) ⦄ := by
  rw [Raw32.carrier_decomp_from_raw_32_eq a hex]
  exact carrier_decomp_from_raw_spec a raw hWa hWraw

/-- The raw-message carrier commitment, over the compact carrier. -/
theorem carrier_commit_from_raw_32_spec (d_matrix : linalg.PolyMatrix) (a : linalg.PolyVec)
    (raw32 : alloc.vec.Vec linalg.RawVec32) (raw : alloc.vec.Vec linalg.PolyVec)
    (hex : Raw32.ExpandsTo raw32 raw)
    (hWd : WfMat 1 (2 ^ 10 * 8) d_matrix) (hWa : WfVec (2 ^ 10) a)
    (hWraw : WfBlocks (2 ^ 10) (2 ^ 10) raw) :
    quadeval.carrier_commit_from_raw_32 d_matrix a raw32
      ⦃ out => WfVec 1 out ∧
        toVec (k := 1) out
          = Hachi.carrierCommit Φ (toMat (rows := 1) (cols := 2 ^ 10 * 8) d_matrix) ddBal
              (toVec (k := 2 ^ 10) a)
              (fun i : Fin (2 ^ 10) => gadgetDecompose Φ dd
                (toVec (k := 2 ^ 10) (raw.val.getD i.val (alloc.vec.Vec.new ring.Rq)))) ⦄ := by
  rw [Raw32.carrier_commit_from_raw_32_eq d_matrix a hex]
  exact carrier_commit_from_raw_spec d_matrix a raw hWd hWa hWraw

/-- **`honest_z_from_raw_32` computes `honestZ`.** -/
theorem honest_z_from_raw_32_spec (raw32 : alloc.vec.Vec linalg.RawVec32)
    (raw : alloc.vec.Vec linalg.PolyVec) (c : linalg.PolyVec)
    (wo : InnerOuter.Opening Φ 1 (2 ^ 10) 8 (2 ^ 10) 8)
    (hex : Raw32.ExpandsTo raw32 raw)
    (hc : ∀ i : Fin (2 ^ 10), Rq.l1Norm Φ (toVec (k := 2 ^ 10) c i) ≤ 16)
    (hm : (fun i : Fin (2 ^ 10) => gadgetDecompose Φ dd
            (toVec (k := 2 ^ 10) (raw.val.getD i.val (alloc.vec.Vec.new ring.Rq))))
          = wo.message)
    (hWraw : WfBlocks (2 ^ 10) (2 ^ 10) raw) (hWc : WfVec (2 ^ 10) c) :
    quadeval.honest_z_from_raw_32 raw32 c
      ⦃ out => WfVec (2 ^ 10 * 8) out ∧
        toVec (k := 2 ^ 10 * 8) out = InnerOuter.honestZ Φ wo (toChals c hc) ⦄ := by
  rw [Raw32.honest_z_from_raw_32_eq c hex]
  exact honest_z_from_raw_spec raw c wo hc hm hWraw hWc

/-- **`honest_compute_v_from_raw_32` computes `honestComputeV`** -- what
`chain_open` calls, over the carrier the prover actually holds. -/
theorem honest_compute_v_from_raw_32_spec (pp : quadeval.PublicParamsD)
    (stmt : quadeval.QuadEvalStatement) (raw32 : alloc.vec.Vec linalg.RawVec32)
    (raw : alloc.vec.Vec linalg.PolyVec)
    (sp : Hachi.PublicParamsD Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (ss : InnerOuter.QuadEvalStatement Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (wo : InnerOuter.Opening Φ 1 (2 ^ 10) 8 (2 ^ 10) 8)
    (hex : Raw32.ExpandsTo raw32 raw)
    (hpp : RepParamsD pp sp) (hst : RepStmt stmt ss)
    (hm : (fun i : Fin (2 ^ 10) => gadgetDecompose Φ dd
            (toVec (k := 2 ^ 10) (raw.val.getD i.val (alloc.vec.Vec.new ring.Rq))))
          = wo.message)
    (hWraw : WfBlocks (2 ^ 10) (2 ^ 10) raw) :
    quadeval.honest_compute_v_from_raw_32 pp stmt raw32
      ⦃ out => WfVec 1 out ∧
        toVec (k := 1) out = InnerOuter.honestComputeV Φ sp ddBal ss wo ⦄ := by
  rw [Raw32.honest_compute_v_from_raw_32_eq pp stmt hex]
  exact honest_compute_v_from_raw_spec pp stmt raw sp ss wo hpp hst hm hWraw

/-! ### The carrier decomposition, computed once (candidate T28)

`honest_compute_v_from_raw_32` computed `ŵ = G⁻¹(a · raw)` and
`honest_compute_resp_from_raw_32` computed it again; at the pin that second pass
is 98.7 s. Both now take it. The specifications below are what makes that a
scheduling change rather than a protocol one: the *conclusions* are the ones
above, and what moves is a premise -- from "`raw` decomposes to `wo.message`" to
"`carrier_dec` IS the carrier decomposition of `wo.message`", which
`carrier_decomp_from_raw_32_spec` discharges from the former. Nothing is
weakened: composing the two recovers the old premise set exactly. -/

/-- `honest_compute_v_from_decomp` is the matrix-vector product, and nothing
else -- which is the content of the split. -/
theorem honest_compute_v_from_decomp_spec (d_matrix : linalg.PolyMatrix)
    (carrier_dec : linalg.PolyVec) (hWd : WfMat 1 (2 ^ 10 * 8) d_matrix)
    (hWc : WfVec (2 ^ 10 * 8) carrier_dec) :
    quadeval.honest_compute_v_from_decomp d_matrix carrier_dec
      ⦃ out => WfVec 1 out ∧ toVec (k := 1) out
        = ArkLib.Lattices.matVecMul
            (toMat (rows := 1) (cols := 2 ^ 10 * 8) d_matrix)
            (toVec (k := 2 ^ 10 * 8) carrier_dec) ⦄ := by
  rw [quadeval.honest_compute_v_from_decomp]
  exact mat_vec_mul_spec (rows := 1) (cols := 2 ^ 10 * 8) d_matrix carrier_dec hWd hWc

/-- **and at the carrier decomposition it is `honestComputeV`** -- the round-0
message, unchanged, from a value the prover already had. This is what
`chain_open` steps through. -/
theorem honest_compute_v_from_decomp_honest (pp : quadeval.PublicParamsD)
    (carrier_dec : linalg.PolyVec)
    (sp : Hachi.PublicParamsD Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (ss : InnerOuter.QuadEvalStatement Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (wo : InnerOuter.Opening Φ 1 (2 ^ 10) 8 (2 ^ 10) 8)
    (hpp : RepParamsD pp sp) (hWc : WfVec (2 ^ 10 * 8) carrier_dec)
    (hcd : toVec (k := 2 ^ 10 * 8) carrier_dec
      = Hachi.carrierDecomp Φ ddBal ss.avec wo.message) :
    quadeval.honest_compute_v_from_decomp pp.d_matrix carrier_dec
      ⦃ out => WfVec 1 out ∧
        toVec (k := 1) out = InnerOuter.honestComputeV Φ sp ddBal ss wo ⦄ := by
  obtain ⟨hWpi, hWpd, hpi, hpd⟩ := hpp
  apply spec_mono (honest_compute_v_from_decomp_spec pp.d_matrix carrier_dec hWpd hWc)
  rintro z ⟨hzwf, hzval⟩
  refine ⟨hzwf, ?_⟩
  rw [hzval, hcd, hpd, InnerOuter.honestComputeV, Hachi.carrierCommit, Simple.commit]

/-- **`honest_compute_resp_from_raw_32` computes `honestComputeResp`** -- with
the carrier decomposition supplied. `honest_compute_resp_from_raw_spec`'s
conclusion word for word; `stmt` has left the statement entirely, because the
only thing the response used it for was the carrier it no longer computes. -/
theorem honest_compute_resp_from_raw_32_spec (carrier_dec : linalg.PolyVec)
    (raw32 : alloc.vec.Vec linalg.RawVec32)
    (raw inner_decomp : alloc.vec.Vec linalg.PolyVec) (c : linalg.PolyVec)
    (ss : InnerOuter.QuadEvalStatement Φ 1 (2 ^ 10) 8 1 (2 ^ 10) 8 1)
    (wo : InnerOuter.Opening Φ 1 (2 ^ 10) 8 (2 ^ 10) 8)
    (hex : Raw32.ExpandsTo raw32 raw)
    (hc : ∀ i : Fin (2 ^ 10), Rq.l1Norm Φ (toVec (k := 2 ^ 10) c i) ≤ 16)
    (hWcd : WfVec (2 ^ 10 * 8) carrier_dec)
    (hcd : toVec (k := 2 ^ 10 * 8) carrier_dec
      = Hachi.carrierDecomp Φ ddBal ss.avec wo.message)
    (hm : (fun i : Fin (2 ^ 10) => gadgetDecompose Φ dd
            (toVec (k := 2 ^ 10) (raw.val.getD i.val (alloc.vec.Vec.new ring.Rq))))
          = wo.message)
    (hi : toBlocks (blocks := 2 ^ 10) (width := 1 * 8) inner_decomp = wo.innerDecomp)
    (hWraw : WfBlocks (2 ^ 10) (2 ^ 10) raw)
    (hWi : WfBlocks (2 ^ 10) (1 * 8) inner_decomp) (hWc : WfVec (2 ^ 10) c) :
    quadeval.honest_compute_resp_from_raw_32 carrier_dec raw32 inner_decomp c
      ⦃ out => RepResp out
        (InnerOuter.honestComputeResp Φ ddBal bddZ ss wo (toChals c hc)) ⦄ := by
  rw [quadeval.honest_compute_resp_from_raw_32]
  step with poly_vec_copy_spec (k := 2 ^ 10 * 8) carrier_dec hWcd as ⟨cdec, hCwf, hCval⟩
  step with honest_z_from_raw_32_spec raw32 raw c wo hex hc hm hWraw hWc as ⟨zz, hZwf, hZval⟩
  step with QuadEval.bounded_z_gadget_decompose_spec (rows := 2 ^ 10 * 8) zz hZwf (by scalar_tac)
    as ⟨zdec, hDwf, hDval⟩
  rw [Raw32.resp_inner_loop_eq]
  step with honest_compute_resp_from_raw_loop_spec (blocks := 2 ^ 10) (width := 1 * 8)
    inner_decomp (alloc.vec.Vec.new linalg.PolyVec) 0#usize hWi (by simp) (by simp)
    (by intro y hy; simp at hy) (by intro j hj; simp at hj)
    as ⟨inner, hIlen, hIwf, hIval⟩
  rw [quadeval.QuadEvalResponse.new, WP.spec_ok]
  refine ⟨hCwf, ⟨hIlen, hIwf⟩, hDwf, ?_, ?_, ?_⟩
  · show toVec (k := 2 ^ 10 * 8) cdec = Hachi.carrierDecomp Φ ddBal ss.avec wo.message
    rw [hCval, hcd]
  · show toBlocks (blocks := 2 ^ 10) (width := 1 * 8) inner = wo.innerDecomp
    rw [← hi]
    funext j
    exact hIval j.val j.isLt
  · show toVec (k := 2 ^ 10 * 8 * 5) zdec
      = Hachi.zDecompBounded Φ bddZ (InnerOuter.honestZ Φ wo (toChals c hc))
    rw [hDval, hZval, Hachi.zDecompBounded]

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
  obtain ⟨hWpi, hWpd, hpi, hpd⟩ := hpp
  obtain ⟨hWu, hWa, hWb, hWy, hu, ha, hbv, hy⟩ := hst
  obtain ⟨hWrc, hWri, hWrz, hrc, hri, hrz⟩ := hre
  have hinner : toMat (rows := 1) (cols := 2 ^ 10 * 8) pp.inner.inner_matrix = sp.innerMatrix :=
    congrArg InnerOuter.PublicParams.innerMatrix hpi
  have houter :
      toMat (rows := 1) (cols := 2 ^ 10 * (1 * 8)) pp.inner.outer_matrix = sp.outerMatrix :=
    congrArg InnerOuter.PublicParams.outerMatrix hpi
  rw [quadeval.rel_out]
  simp only [quadeval.QuadEvalResponse.impl.z_dec, quadeval.QuadEvalResponse.impl.inner_dec,
    quadeval.QuadEvalResponse.impl.carrier_dec, quadeval.QuadEvalStatement.impl.u,
    quadeval.QuadEvalStatement.impl.avec, quadeval.QuadEvalStatement.impl.bvec,
    quadeval.QuadEvalStatement.impl.y, quadeval.PublicParamsD.impl.inner,
    quadeval.PublicParamsD.impl.d_matrix, commit.PublicParams.impl.outer_matrix,
    commit.PublicParams.impl.inner_matrix, bind_tc_ok]
  step with j_mul_spec resp.z_dec hWrz as ⟨z, hZwf, hZval⟩
  step with flatten_blocks_spec' (blocks := 2 ^ 10) (width := 1 * 8) resp.inner_dec
    (by scalar_tac) hWri as ⟨flat, hFwf, hFval⟩
  step with mat_vec_mul_spec (rows := 1) (cols := 2 ^ 10 * 8) pp.d_matrix resp.carrier_dec
    hWpd hWrc as ⟨dv, hDwf, hDval⟩
  step with poly_vec_equals_spec (k := 1) dv v hDwf hWv as ⟨c1, hc1⟩
  step with mat_vec_mul_spec (rows := 1) (cols := 2 ^ 10 * (1 * 8)) pp.inner.outer_matrix flat
    hWpi.2 hFwf as ⟨uv, hUwf, hUval⟩
  step with poly_vec_equals_spec (k := 1) uv stmt.u hUwf hWu as ⟨c2, hc2⟩
  step with gadget_mul_spec (rows := 2 ^ 10) params.BLOCKS resp.carrier_dec
    (by norm_num [params.BLOCKS]) hWrc as ⟨gw, hGwf, hGval⟩
  step with dot_spec (k := 2 ^ 10) stmt.bvec gw hWb hGwf as ⟨yv, hYwf, hYval⟩
  step with RqBridge.equals_spec yv stmt.y hYwf hWy as ⟨c3, hc3⟩
  step with QuadEval.tensor_g1_spec (blocks := 2 ^ 10) c resp.carrier_dec hWc hWrc (by scalar_tac)
    as ⟨t1, hT1wf, hT1val⟩
  step with gadget_mul_spec (rows := 2 ^ 10) params.MESSAGE_ROWS z
    (by norm_num [params.MESSAGE_ROWS]) hZwf as ⟨gz, hGZwf, hGZval⟩
  step with dot_spec (k := 2 ^ 10) stmt.avec gz hWa hGZwf as ⟨az, hAZwf, hAZval⟩
  step with RqBridge.equals_spec t1 az hT1wf hAZwf as ⟨c4, hc4⟩
  step with tensor_g_spec (krows := 1) (blocks := 2 ^ 10) params.INNER_ROWS c resp.inner_dec
    (by norm_num [params.INNER_ROWS]) hWc hWri as ⟨tg, hTGwf, hTGval⟩
  step with mat_vec_mul_spec (rows := 1) (cols := 2 ^ 10 * 8) pp.inner.inner_matrix z
    hWpi.1 hZwf as ⟨iz, hIZwf, hIZval⟩
  step with poly_vec_equals_spec (k := 1) tg iz hTGwf hIZwf as ⟨c5, hc5⟩
  step with vec_l_infty_norm_spec (k := 2 ^ 10 * 8) resp.carrier_dec hWrc as ⟨n1, hn1⟩
  step with chain_gamma_spec n1 flat resp.z_dec hFwf hWrz _ hn1 as ⟨c6, hc6⟩
  apply spec_mono (rel_chain_spec hc1 hc2 hc3 hc4 hc5 hc6)
  intro b hb
  rw [hb, hDval, hUval, hFval, hYval, hGval, hT1val, hAZval, hGZval, hTGval, hIZval, hZval,
    hrc, hri, hrz, hu, ha, hbv, hy, hpd, hinner, houter]
  exact Iff.rfl

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
  obtain ⟨hWpi, hWpd, hpi, hpd⟩ := hpp
  obtain ⟨hWu, hWa, hWb, hWy, hu, ha, hbv, hy⟩ := hst
  obtain ⟨hWrc, hWri, hWrz, hrc, hri, hrz⟩ := hre
  have hinner : toMat (rows := 1) (cols := 2 ^ 10 * 8) pp.inner.inner_matrix = sp.innerMatrix :=
    congrArg InnerOuter.PublicParams.innerMatrix hpi
  have houter :
      toMat (rows := 1) (cols := 2 ^ 10 * (1 * 8)) pp.inner.outer_matrix = sp.outerMatrix :=
    congrArg InnerOuter.PublicParams.outerMatrix hpi
  rw [quadeval.paper_rel_out]
  simp only [quadeval.QuadEvalResponse.impl.z_dec, quadeval.QuadEvalResponse.impl.inner_dec,
    quadeval.QuadEvalResponse.impl.carrier_dec, quadeval.QuadEvalStatement.impl.u,
    quadeval.QuadEvalStatement.impl.avec, quadeval.QuadEvalStatement.impl.bvec,
    quadeval.QuadEvalStatement.impl.y, quadeval.PublicParamsD.impl.inner,
    quadeval.PublicParamsD.impl.d_matrix, commit.PublicParams.impl.outer_matrix,
    commit.PublicParams.impl.inner_matrix, bind_tc_ok]
  step with j_mul_spec resp.z_dec hWrz as ⟨z, hZwf, hZval⟩
  step with flatten_blocks_spec' (blocks := 2 ^ 10) (width := 1 * 8) resp.inner_dec
    (by scalar_tac) hWri as ⟨flat, hFwf, hFval⟩
  step with mat_vec_mul_spec (rows := 1) (cols := 2 ^ 10 * 8) pp.d_matrix resp.carrier_dec
    hWpd hWrc as ⟨dv, hDwf, hDval⟩
  step with poly_vec_equals_spec (k := 1) dv v hDwf hWv as ⟨c1, hc1⟩
  step with mat_vec_mul_spec (rows := 1) (cols := 2 ^ 10 * (1 * 8)) pp.inner.outer_matrix flat
    hWpi.2 hFwf as ⟨uv, hUwf, hUval⟩
  step with poly_vec_equals_spec (k := 1) uv stmt.u hUwf hWu as ⟨c2, hc2⟩
  step with gadget_mul_spec (rows := 2 ^ 10) params.BLOCKS resp.carrier_dec
    (by norm_num [params.BLOCKS]) hWrc as ⟨gw, hGwf, hGval⟩
  step with dot_spec (k := 2 ^ 10) stmt.bvec gw hWb hGwf as ⟨yv, hYwf, hYval⟩
  step with RqBridge.equals_spec yv stmt.y hYwf hWy as ⟨c3, hc3⟩
  step with QuadEval.tensor_g1_spec (blocks := 2 ^ 10) c resp.carrier_dec hWc hWrc (by scalar_tac)
    as ⟨t1, hT1wf, hT1val⟩
  step with gadget_mul_spec (rows := 2 ^ 10) params.MESSAGE_ROWS z
    (by norm_num [params.MESSAGE_ROWS]) hZwf as ⟨gz, hGZwf, hGZval⟩
  step with dot_spec (k := 2 ^ 10) stmt.avec gz hWa hGZwf as ⟨az, hAZwf, hAZval⟩
  step with RqBridge.equals_spec t1 az hT1wf hAZwf as ⟨c4, hc4⟩
  step with tensor_g_spec (krows := 1) (blocks := 2 ^ 10) params.INNER_ROWS c resp.inner_dec
    (by norm_num [params.INNER_ROWS]) hWc hWri as ⟨tg, hTGwf, hTGval⟩
  step with mat_vec_mul_spec (rows := 1) (cols := 2 ^ 10 * 8) pp.inner.inner_matrix z
    hWpi.1 hZwf as ⟨iz, hIZwf, hIZval⟩
  step with poly_vec_equals_spec (k := 1) tg iz hTGwf hIZwf as ⟨c5, hc5⟩
  step with QuadEval.vec_in_sb_spec (cols := 2 ^ 10 * 8) resp.carrier_dec hWrc as ⟨b0, hb0⟩
  step with paper_chain_spec b0 flat resp.z_dec hFwf hWrz _ hb0 as ⟨c6, hc6⟩
  apply spec_mono (rel_chain_spec hc1 hc2 hc3 hc4 hc5 hc6)
  intro b hb
  rw [hb, hDval, hUval, hFval, hYval, hGval, hT1val, hAZval, hGZval, hTGval, hIZval, hZval,
    hrc, hri, hrz, hu, ha, hbv, hy, hpd, hinner, houter]
  exact Iff.rfl

end HachiEquiv.QuadEvalProtocol
