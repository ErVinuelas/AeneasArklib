/-
The **QuadEval fold**: the `z`-side gadget siblings at `τ = 5`, the carrier
entry, `tensorG1`, and the Eq. (20) box and relation decisions.

Proved, on the bridge from `Scheme.lean` and the balanced layer of
`Balanced.lean`, and part of the audited library -- `lean/Check.lean` § 4 prints
the axiom dependencies of every headline spec below, so a `sorry` here is a
`make build` failure. Proved by Aristotle session `14b9bf77` (2026-09-04, eight
obligations to zero) and promoted out of `lean-wip/` on the strength of that: no
errors, no `declaration uses 'sorry'`, and all eight headline specs on exactly
the three Lean kernel axioms.

It imports `Balanced` for `ddBal` and `bddZ`. When this file was first staged
that import was not available -- `lean-wip/Balanced.lean` was itself out with an
Aristotle session, and `lake build` produces no `.olean` for anything under
`lean-wip/` -- so the file briefly carried duplicates that stood in for them;
they went the day `Balanced.lean` was promoted.

## The shape that is new here

Every `_spec` in `lean/Scheme.lean` is an *equality*: the extracted function
returns a value, and the spec says which. Four of the statements below are
**iffs** instead, and that is forced by the specification rather than chosen:
`InSb`, `vecInSb`, `relOut` and `paperRelOut` are `Prop`s — `relOut` is a `Set`
of conjunctions (`QuadEval/Reduction.lean:258`) — while the Rust returns a
`Bool`. So the obligation is "the decision procedure decides the proposition",
not "two values agree". `commit.verify_weak` is the contrasting case: ArkLib
states *that* one as a `Bool`, so its spec is an equality.

This shape is not in the Stage 2 scoping document's erasure catalogue. It is low-risk —
every conjunct is decidable, `Rq` equality being canonical and the norms `ℕ` —
but it changes what the proof has to produce.

## Proof notes

`in_sb_spec` is the one genuinely new arithmetic obligation and the one worth
reading twice. The box is **asymmetric**: `-⌊b/2⌋` is admissible and `+⌊b/2⌋`
is not, so the Rust branches on the sign of the centered representative rather
than testing a magnitude. The lemma that closes it is that branch against
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

/-- The bounded `z`-side digit map at an unbounded exponent: `bddZ.digit c ⟨e, _⟩`
read at a bare `ℕ`. The `Fin 5`-indexed form is what `bddZ` carries; this one is
what the loop invariants below range over. -/
def bddZDigitK (c : ZMod q) (e : ℕ) : ZMod q :=
  (((Nat.digits 16 (c.valMinAbs
      + ((16 / 2 : ℕ) : ℤ) * (digitOnesValue 16 5 : ℤ)).toNat).getD e 0 : ℕ) : ZMod q)
    - ((16 / 2 : ℕ) : ZMod q)

theorem bddZ_digit_eq (c : ZMod q) (e : Fin 5) : bddZ.digit c e = bddZDigitK c e.val := rfl

/-- The ring element `gadget::bounded_z_gadget_decompose` writes at the flat index
`5 * i + e`: bounded balanced digit `e` of every coefficient of block `i`. -/
def boundedZDigitBlock (x : linalg.PolyVec) (i e : ℕ) : Rq Φ :=
  Rq.ofFinCoeff Φ N (fun t =>
    bddZDigitK ((toRq (x.val.getD i (alloc.vec.Vec.new cpoly.field.Fp))).1.coeff t) e)

/-- The innermost loop of `gadget::bounded_z_gadget_decompose`: `coeffs` collects
bounded digit `e` of the first `k` coefficients of block `i`. -/
theorem bounded_z_gadget_decompose_coeff_loop_spec {rows : ℕ} (x : linalg.PolyVec)
    (degree i e : Std.Usize) (coeffs : alloc.vec.Vec cpoly.field.Fp) (k : Std.Usize)
    (hx : WfVec rows x) (hdeg : degree.val = N) (hi : i.val < rows) (he : e.val < 5)
    (hk : k.val ≤ N) (hlen : coeffs.val.length = k.val)
    (hred : ∀ u ∈ coeffs.val, Red u)
    (hval : ∀ t < k.val, coeffK coeffs t
      = bddZDigitK ((toRq (x.val.getD i.val
          (alloc.vec.Vec.new cpoly.field.Fp))).1.coeff t) e.val) :
    gadget.bounded_z_gadget_decompose_loop0_loop0_loop0 x degree i e coeffs k
      ⦃ z => z.val.length = N ∧ (∀ u ∈ z.val, Red u) ∧ ∀ t < N, coeffK z t
        = bddZDigitK ((toRq (x.val.getD i.val
            (alloc.vec.Vec.new cpoly.field.Fp))).1.coeff t) e.val ⦄ := by
  have hilt : i.val < x.val.length := by rw [hx.1]; exact hi
  have hxi : x.val.getD i.val (alloc.vec.Vec.new cpoly.field.Fp) = x.val[i.val] :=
    List.getD_eq_getElem _ _ hilt
  have hWx : Wf x.val[i.val] := hx.2 _ (List.getElem_mem hilt)
  rw [gadget.bounded_z_gadget_decompose_loop0_loop0_loop0]
  apply loop.spec_decr_nat (fun s => degree.val - s.2.val)
    (fun s => s.2.val ≤ N ∧ s.1.val.length = s.2.val ∧ (∀ u ∈ s.1.val, Red u) ∧
      ∀ t < s.2.val, coeffK s.1 t
        = bddZDigitK ((toRq (x.val.getD i.val
            (alloc.vec.Vec.new cpoly.field.Fp))).1.coeff t) e.val)
  · rintro ⟨c1, k1⟩ ⟨hk1, hlen1, hred1, hval1⟩
    dsimp only at hk1 hlen1 hred1 hval1
    simp only [gadget.bounded_z_gadget_decompose_loop0_loop0_loop0.body]
    by_cases hlt : k1 < degree
    · rw [if_pos hlt]
      have hkN : k1.val < N := by rw [← hdeg]; scalar_tac
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hWx
      step with RqBridge.coeff_spec r k1 hWr as ⟨f, hRf, hf⟩
      step with HachiEquiv.Balanced.bounded_z_digit_at_spec f e hRf he as ⟨g, hRg, hg⟩
      step as ⟨c2, hc2⟩
      step as ⟨k2, hk2⟩
      refine ⟨by omega, ?_, ?_, ?_, ?_⟩
      · rw [hc2, hk2, List.length_append, hlen1]; simp
      · intro u hu
        rw [hc2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hred1 u h
        · rw [List.mem_singleton.mp h]; exact hRg
      · intro t ht
        rw [hk2] at ht
        rcases Nat.lt_or_ge t k1.val with htlt | htge
        · rw [coeffK_append_lt hc2 (by omega), hval1 t htlt]
        · have hteq : t = k1.val := by omega
          have hpush : coeffK c2 k1.val = toK g := by
            rw [← hlen1]; exact coeffK_append_eq hc2
          rw [hteq, hpush, hg, bddZ_digit_eq, hf, hr, ← hxi]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = N := by rw [← hdeg] at hk1 ⊢; scalar_tac
      refine ⟨by rw [hlen1, heq], hred1, ?_⟩
      rw [← heq]; exact hval1
  · exact ⟨hk, hlen, hred, hval⟩

/-- The middle loop of `gadget::bounded_z_gadget_decompose`: one digit block of
row `i` per turn. -/
theorem bounded_z_gadget_decompose_digit_loop_spec {rows : ℕ} (x : linalg.PolyVec)
    (digits degree i : Std.Usize) (out : alloc.vec.Vec ring.Rq) (e : Std.Usize)
    (hx : WfVec rows x) (hmax : 5 * rows ≤ Usize.max)
    (hdig : digits.val = 5) (hdeg : degree.val = N) (hi : i.val < rows)
    (he : e.val ≤ 5) (hlen : out.val.length = 5 * i.val + e.val)
    (hwf : ∀ y ∈ out.val, Wf y)
    (hval : ∀ i' e' : ℕ, e' < 5 → 5 * i' + e' < 5 * i.val + e.val →
      toRq (out.val.getD (5 * i' + e') (alloc.vec.Vec.new cpoly.field.Fp))
        = boundedZDigitBlock x i' e') :
    gadget.bounded_z_gadget_decompose_loop0_loop0 x digits degree out i e
      ⦃ z => z.val.length = 5 * i.val + 5 ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ i' e' : ℕ, e' < 5 → 5 * i' + e' < 5 * i.val + 5 →
          toRq (z.val.getD (5 * i' + e') (alloc.vec.Vec.new cpoly.field.Fp))
            = boundedZDigitBlock x i' e' ⦄ := by
  have hmaxb : 5 * i.val + 5 ≤ Usize.max := by
    have h1 : 5 * (i.val + 1) ≤ 5 * rows := Nat.mul_le_mul_left 5 (by omega)
    omega
  rw [gadget.bounded_z_gadget_decompose_loop0_loop0]
  apply loop.spec_decr_nat (fun s => digits.val - s.2.val)
    (fun s => s.2.val ≤ 5 ∧ s.1.val.length = 5 * i.val + s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ i' e' : ℕ, e' < 5 → 5 * i' + e' < 5 * i.val + s.2.val →
        toRq (s.1.val.getD (5 * i' + e') (alloc.vec.Vec.new cpoly.field.Fp))
          = boundedZDigitBlock x i' e')
  · rintro ⟨o1, e1⟩ ⟨he1, hlen1, hwf1, hval1⟩
    dsimp only at he1 hlen1 hwf1 hval1
    simp only [gadget.bounded_z_gadget_decompose_loop0_loop0.body]
    simp only [alloc.vec.Vec.with_capacity]
    by_cases hlt : e1 < digits
    · rw [if_pos hlt]
      have helt : e1.val < 5 := by rw [← hdig]; scalar_tac
      have hinner := bounded_z_gadget_decompose_coeff_loop_spec x degree i e1
        (alloc.vec.Vec.new cpoly.field.Fp) 0#usize hx hdeg hi helt (by simp) (by simp)
        (by intro u hu; simp at hu) (by intro t ht; simp at ht)
      step with hinner as ⟨cs, hcslen, hcsred, hcsval⟩
      step with RqBridge.from_coeffs_spec cs hcsred as ⟨rr, hWrr, hrr⟩
      step as ⟨o2, ho2⟩
      step as ⟨e2, he2⟩
      have hblock : toRq rr = boundedZDigitBlock x i.val e1.val := by
        rw [hrr, boundedZDigitBlock]
        exact ofFinCoeff_congr (fun t ht => hcsval t ht)
      refine ⟨by omega, ?_, ?_, ?_, ?_⟩
      · rw [ho2, he2, List.length_append, hlen1]; simp; omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWrr
      · intro i' e' he' hb
        rw [he2] at hb
        rcases Nat.lt_or_ge (5 * i' + e') (5 * i.val + e1.val) with hjlt | hjge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 i' e' he' hjlt]
        · have hi'e : i' = i.val ∧ e' = e1.val := by omega
          obtain ⟨hii, hee⟩ := hi'e
          have hidx : 5 * i' + e' = o1.val.length := by omega
          rw [hidx, ho2, getD_append_eq, hblock, hii, hee]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : e1.val = 5 := by rw [← hdig] at he1 ⊢; scalar_tac
      rw [heq] at hlen1 hval1
      exact ⟨hlen1, hwf1, hval1⟩
  · exact ⟨he, hlen, hwf, hval⟩

/-- The outer loop of `gadget::bounded_z_gadget_decompose`: one block of `5` digit
slots per row. -/
theorem bounded_z_gadget_decompose_outer_loop_spec {rows : ℕ} (x : linalg.PolyVec)
    (digits degree r : Std.Usize) (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hx : WfVec rows x) (hmax : 5 * rows ≤ Usize.max)
    (hdig : digits.val = 5) (hdeg : degree.val = N) (hr : r.val = rows)
    (hi : i.val ≤ rows) (hlen : out.val.length = 5 * i.val)
    (hwf : ∀ y ∈ out.val, Wf y)
    (hval : ∀ i' e' : ℕ, e' < 5 → 5 * i' + e' < 5 * i.val →
      toRq (out.val.getD (5 * i' + e') (alloc.vec.Vec.new cpoly.field.Fp))
        = boundedZDigitBlock x i' e') :
    gadget.bounded_z_gadget_decompose_loop0 x digits degree r out i
      ⦃ z => z.val.length = 5 * rows ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ i' e' : ℕ, e' < 5 → 5 * i' + e' < 5 * rows →
          toRq (z.val.getD (5 * i' + e') (alloc.vec.Vec.new cpoly.field.Fp))
            = boundedZDigitBlock x i' e' ⦄ := by
  rw [gadget.bounded_z_gadget_decompose_loop0]
  apply loop.spec_decr_nat (fun s => r.val - s.2.val)
    (fun s => s.2.val ≤ rows ∧ s.1.val.length = 5 * s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ i' e' : ℕ, e' < 5 → 5 * i' + e' < 5 * s.2.val →
        toRq (s.1.val.getD (5 * i' + e') (alloc.vec.Vec.new cpoly.field.Fp))
          = boundedZDigitBlock x i' e')
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [gadget.bounded_z_gadget_decompose_loop0.body]
    by_cases hlt : i1 < r
    · rw [if_pos hlt]
      have hilt : i1.val < rows := by rw [← hr]; scalar_tac
      have hmid := bounded_z_gadget_decompose_digit_loop_spec x digits degree i1 o1 0#usize
        hx hmax hdig hdeg hilt (by simp) (by simpa using hlen1) hwf1
        (by simpa using hval1)
      step with hmid as ⟨o2, hlen2, hwf2, hval2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by omega, ?_, ?_, ?_, ?_⟩
      · rw [hi2, hlen2]; ring
      · exact hwf2
      · intro i' e' he' hb
        rw [hi2] at hb
        exact hval2 i' e' he' (by omega)
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = rows := by rw [← hr] at hi1 ⊢; scalar_tac
      rw [heq] at hlen1 hval1
      exact ⟨hlen1, hwf1, hval1⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- `gadget::bounded_z_gadget_decompose` — ArkLib's
`BoundedDigitDecomposition.gadgetDecompose` at `bddZ`. The same triple loop as
the full-width gadget, at `τ = 5` over the bounded digit map. -/
theorem bounded_z_gadget_decompose_spec {rows : ℕ} (x : linalg.PolyVec)
    (hx : WfVec rows x) (hmax : 5 * rows ≤ Usize.max) :
    gadget.bounded_z_gadget_decompose x
      ⦃ z => WfVec (rows * 5) z ∧ toVec (k := rows * 5) z
        = bddZ.gadgetDecompose Φ (toVec (k := rows) x) ⦄ := by
  have hdig : (params.Z_DIGITS).val = 5 := by simp [params.Z_DIGITS]
  have hdeg : (params.RING_DEGREE).val = N := by simp
  rw [gadget.bounded_z_gadget_decompose]
  simp only [alloc.vec.Vec.with_capacity]
  simp only [linalg.PolyVec.len, linalg.PolyVec.new, bind_ok_id]
  apply spec_mono (bounded_z_gadget_decompose_outer_loop_spec x params.Z_DIGITS
    params.RING_DEGREE (alloc.vec.Vec.len x) (alloc.vec.Vec.new ring.Rq) 0#usize
    hx hmax hdig hdeg (by simpa using hx.1) (by simp) (by simp)
    (by intro y hy; simp at hy) (by intro i' e' _ hb; simp at hb))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨by rw [hzlen]; ring, hzwf⟩, ?_⟩
  funext m
  have hm : m.val < rows * 5 := m.isLt
  have he'lt : m.val % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hi'lt : m.val / 5 < rows := by omega
  have hsplit : 5 * (m.val / 5) + m.val % 5 = m.val := by omega
  have hfp : (finProdFinEquiv (⟨m.val / 5, hi'lt⟩, ⟨m.val % 5, he'lt⟩) : Fin (rows * 5))
      = m := by
    apply Fin.ext
    show m.val % 5 + 5 * (m.val / 5) = m.val
    omega
  have hgd : bddZ.gadgetDecompose Φ (toVec (k := rows) x)
      (finProdFinEquiv (⟨m.val / 5, hi'lt⟩, ⟨m.val % 5, he'lt⟩))
      = Rq.ofFinCoeff Φ Φ.φ.natDegree
          (fun k => bddZ.digit ((toVec (k := rows) x ⟨m.val / 5, hi'lt⟩).1.coeff k)
            ⟨m.val % 5, he'lt⟩) :=
    gadgetDecomposeFun_apply Φ bddZ.digit (toVec (k := rows) x) _ _
  rw [hfp] at hgd
  rw [hgd]
  simp only [toVec]
  have hz := hzval (m.val / 5) (m.val % 5) he'lt (by omega)
  rw [hsplit] at hz
  rw [hz, boundedZDigitBlock, RqBridge.phi_natDegree]
  rfl

/-- The inner loop of `gadget::gadget_mul_z`: the accumulator is the base-weighted
sum over the digit slots of block `i` already visited. -/
theorem gadget_mul_z_inner_loop_spec {rows : ℕ} (v : linalg.PolyVec) (dg : Std.Usize)
    (i : Std.Usize) (acc : ring.Rq) (e : Std.Usize)
    (hv : WfVec (rows * 5) v) (hdg : dg.val = 5) (hi : i.val < rows)
    (hacc : Wf acc) (he : e.val ≤ 5)
    (hval : toRq acc = ∑ t ∈ Finset.range e.val, Rq.constRq Φ ((16 : ZMod q) ^ t)
      * toRq (v.val.getD (t + 5 * i.val) (alloc.vec.Vec.new cpoly.field.Fp))) :
    gadget.gadget_mul_z_loop0_loop0 v dg i acc e
      ⦃ z => Wf z ∧ toRq z = ∑ t ∈ Finset.range 5, Rq.constRq Φ ((16 : ZMod q) ^ t)
        * toRq (v.val.getD (t + 5 * i.val) (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  have hvlen : rows * 5 ≤ Usize.max := by rw [← hv.1]; exact v.property
  have hib : 5 * i.val + 5 ≤ Usize.max := by
    have h1 : (i.val + 1) * 5 ≤ rows * 5 := Nat.mul_le_mul_right 5 (by omega)
    have h2 : (i.val + 1) * 5 = 5 * i.val + 5 := by ring
    omega
  rw [gadget.gadget_mul_z_loop0_loop0]
  apply loop.spec_decr_nat (fun s => dg.val - s.2.val)
    (fun s => s.2.val ≤ 5 ∧ Wf s.1 ∧
      toRq s.1 = ∑ t ∈ Finset.range s.2.val, Rq.constRq Φ ((16 : ZMod q) ^ t)
        * toRq (v.val.getD (t + 5 * i.val) (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨a1, e1⟩ ⟨he1, hW1, hval1⟩
    dsimp only at he1 hW1 hval1
    simp only [gadget.gadget_mul_z_loop0_loop0.body]
    by_cases hlt : e1 < dg
    · rw [if_pos hlt]
      have helt : e1.val < 5 := by rw [← hdg]; scalar_tac
      step as ⟨p, hp⟩
      step as ⟨p2, hp2⟩
      have hidx : p2.val = e1.val + 5 * i.val := by rw [hp2, hp, hdg]; ring
      have hlen : p2.val < v.val.length := by
        rw [hv.1, hidx]
        have : (i.val + 1) * 5 ≤ rows * 5 := Nat.mul_le_mul_right 5 (by omega)
        have h2 : (i.val + 1) * 5 = 5 * i.val + 5 := by ring
        omega
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hv.2 _ (List.getElem_mem hlen)
      step with base_pow_spec e1 as ⟨f, hRf, hf⟩
      step with RqBridge.scalar_mul_spec r f hWr hRf as ⟨scaled, hWs, hs⟩
      step with RqBridge.add_spec a1 scaled hW1 hWs as ⟨a2, hWa2, ha2⟩
      step as ⟨e2, he2⟩
      refine ⟨by scalar_tac, hWa2, ?_, ?_⟩
      · rw [ha2, hs, hf, hr, hval1, he2, Finset.sum_range_succ,
          ← List.getD_eq_getElem _ _ hlen, hidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : e1.val = 5 := by rw [← hdg]; scalar_tac
      exact ⟨hW1, by rw [hval1, heq]⟩
  · exact ⟨he, hacc, hval⟩

/-- The outer loop of `gadget::gadget_mul_z`: one accumulated row per block. -/
theorem gadget_mul_z_outer_loop_spec {rows : ℕ} (r : Std.Usize) (v : linalg.PolyVec)
    (dg : Std.Usize) (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hv : WfVec (rows * 5) v) (hdg : dg.val = 5) (hr : r.val = rows)
    (hi : i.val ≤ rows) (hlen : out.val.length = i.val)
    (hwf : ∀ z ∈ out.val, Wf z)
    (hval : ∀ j, j < i.val →
      toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ∑ t ∈ Finset.range 5, Rq.constRq Φ ((16 : ZMod q) ^ t)
            * toRq (v.val.getD (t + 5 * j) (alloc.vec.Vec.new cpoly.field.Fp))) :
    gadget.gadget_mul_z_loop0 r v dg out i
      ⦃ z => z.val.length = rows ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < rows → toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          = ∑ t ∈ Finset.range 5, Rq.constRq Φ ((16 : ZMod q) ^ t)
              * toRq (v.val.getD (t + 5 * j) (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [gadget.gadget_mul_z_loop0]
  apply loop.spec_decr_nat (fun s => r.val - s.2.val)
    (fun s => s.2.val ≤ rows ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ j, j < s.2.val → toRq (s.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ∑ t ∈ Finset.range 5, Rq.constRq Φ ((16 : ZMod q) ^ t)
            * toRq (v.val.getD (t + 5 * j) (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [gadget.gadget_mul_z_loop0.body]
    by_cases hlt : i1 < r
    · rw [if_pos hlt]
      have hilt : i1.val < rows := by rw [← hr]; scalar_tac
      step with RqBridge.zero_spec as ⟨z0, hWz0, hz0⟩
      have hinner := gadget_mul_z_inner_loop_spec (rows := rows) v dg i1 z0 0#usize
        hv hdg hilt hWz0 (by simp) (by simp [hz0])
      step with hinner as ⟨a1, hWa1, ha1⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWa1
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 j hjlt]
        · have hjeq : j = o1.val.length := by omega
          rw [hjeq, ho2, getD_append_eq, ha1, hlen1]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = rows := by rw [← hr]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, by intro j hj; exact hval1 j (by omega)⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- `gadget::gadget_mul_z` — ArkLib's `gadgetMul` at `digits = 5`, equivalently
`jMatrix Φ 16 rows 5 *ᵥ ·`. Collapsed: the Rust computes the per-block digit
sum, and `gadgetMul_apply` is what makes that the matrix product. -/
theorem gadget_mul_z_spec (rows : Std.Usize) (v : linalg.PolyVec)
    (hv : WfVec (rows.val * 5) v) (hmax : 5 * rows.val ≤ Usize.max) :
    gadget.gadget_mul_z rows v
      ⦃ z => WfVec rows.val z ∧ toVec (k := rows.val) z
        = gadgetMul Φ (16 : ZMod q) (toVec (k := rows.val * 5) v) ⦄ := by
  have hdg : (params.Z_DIGITS).val = 5 := by simp [params.Z_DIGITS]
  rw [gadget.gadget_mul_z]
  simp only [alloc.vec.Vec.with_capacity]
  simp only [linalg.PolyVec.new, bind_ok_id]
  apply spec_mono (gadget_mul_z_outer_loop_spec (rows := rows.val) rows v params.Z_DIGITS
    (alloc.vec.Vec.new ring.Rq) 0#usize hv hdg rfl (by simp) (by simp)
    (by intro y hy; simp at hy) (by intro j hj; simp at hj))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i
  rw [gadgetMul_apply Φ (16 : ZMod q) (by norm_num)]
  simp only [toVec]
  rw [hzval i.val i.isLt]
  have hfp : ∀ x : Fin 5,
      ((finProdFinEquiv (i, x) : Fin (rows.val * 5)) : ℕ) = x.val + 5 * i.val := fun _ => rfl
  simp only [hfp]
  rw [Fin.sum_univ_eq_sum_range (fun t => Rq.constRq Φ ((16 : ZMod q) ^ t)
    * toRq (v.val.getD (t + 5 * i.val) (alloc.vec.Vec.new cpoly.field.Fp))) 5]

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
  step with bounded_z_gadget_decompose_spec (rows := rows.val) x hx hmax as ⟨zd, hzwf, hzval⟩
  apply spec_mono (gadget_mul_z_spec rows zd hzwf hmax)
  rintro y ⟨hywf, hyval⟩
  refine ⟨hywf, ?_⟩
  rw [hyval, hzval]
  refine boundedGadgetDecompose_gadgetMul_eq Φ (by norm_num) (by rw [RqBridge.phi_natDegree]; norm_num)
    bddZ (toVec (k := rows.val) x) ?_
  intro i k hk
  exact hshort i k (by rwa [RqBridge.phi_natDegree] at hk)

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
  rw [quadeval.carrier_entry]
  simp only [linalg.PolyVec.len]
  step with gadget_mul_spec (rows := rows) (alloc.vec.Vec.len a) s (by simpa using ha.1) hs
    as ⟨w, hwwf, hwval⟩
  apply spec_mono (dot_spec (k := rows) a w ha hwwf)
  rintro z ⟨hzwf, hzval⟩
  refine ⟨hzwf, ?_⟩
  rw [hzval, hwval, Hachi.carrierEntry, ArkLib.Lattices.splitForm, gadgetMul]

/-- `quadeval::tensor_g1` — ArkLib's `tensorG1`, the Eq. (20) row-4 left side. -/
theorem tensor_g1_spec {blocks : ℕ} (c x : linalg.PolyVec)
    (hc : WfVec blocks c) (hx : WfVec (blocks * 8) x) (hmax : 8 * blocks ≤ Usize.max) :
    quadeval.tensor_g1 c x
      ⦃ y => Wf y ∧ toRq y
        = Hachi.tensorG1 Φ (16 : ZMod q) 8 (toVec (k := blocks) c)
            (toVec (k := blocks * 8) x) ⦄ := by
  rw [quadeval.tensor_g1]
  simp only [linalg.PolyVec.len]
  step with gadget_mul_spec (rows := blocks) (alloc.vec.Vec.len c) x (by simpa using hc.1) hx
    as ⟨w, hwwf, hwval⟩
  apply spec_mono (dot_spec (k := blocks) c w hc hwwf)
  rintro z ⟨hzwf, hzval⟩
  refine ⟨hzwf, ?_⟩
  rw [hzval, hwval, Hachi.tensorG1, gadgetMul]

/-! ## The box, and why these are iffs -/

/-- The box `S_16` at a single coefficient, in the shape the `in_sb` loop
invariant needs: the centered representative lies in `[-8, 7]`. -/
def InBoxK (c : ZMod q) : Prop := -(8 : ℤ) ≤ c.valMinAbs ∧ c.valMinAbs ≤ 7

set_option maxRecDepth 4096 in
/-- `InSb` at `β = 16` is the coefficientwise box, read below `N`. -/
theorem inSb_iff (a : ring.Rq) :
    (∀ t < N, InBoxK ((toRq a).1.coeff t)) ↔ InnerOuter.InSb Φ 16 (toRq a) := by
  simp only [InnerOuter.InSb, InBoxK, RqBridge.phi_natDegree]
  norm_num

/-- The decision the `in_sb` loop makes at one coefficient: the branch on the sign
of the centered representative decides `InBoxK`. The box is asymmetric, so the two
sides are two different tests — `≤ SB_HI = 7` above zero, `centered_abs ≤ 8` below. -/
theorem in_sb_check_spec (f : cpoly.field.Fp) (half : Std.U64) (b1 : Bool)
    (hRf : Red f) (hhalf : half.val = q / 2) :
    (if (f : Std.U64) ≤ half
      then (if (f : Std.U64) > params.SB_HI then ok false else ok b1)
      else (do
        let i ← commit.centered_abs f
        if i > params.HALF_BASE then ok false else ok b1))
      ⦃ c => (c = true ↔ (b1 = true ∧ InBoxK (toK f))) ⦄ := by
  have hsb : (params.SB_HI).val = 7 := by simp [params.SB_HI]
  have hhb : (params.HALF_BASE).val = 8 := by simp [params.HALF_BASE]
  have hfq : f.val < q := hRf
  have hqnum : q = 4294967197 := rfl
  have hcv : (toK f).val = f.val := by
    simp only [toK, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hRf
  have hmin : (toK f).valMinAbs
      = if f.val ≤ q / 2 then (f.val : ℤ) else (f.val : ℤ) - (q : ℤ) := by
    rw [ZMod.valMinAbs_def_pos, hcv]
  split
  · rename_i hle
    have hfle : f.val ≤ q / 2 := by scalar_tac
    have hva : (toK f).valMinAbs = (f.val : ℤ) := by rw [hmin, if_pos hfle]
    split
    · rename_i hgt
      rw [WP.spec_ok]
      have h7 : 7 < f.val := by scalar_tac
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro _ hbox
      have := hbox.2
      rw [hva] at this
      omega
    · rename_i hng
      rw [WP.spec_ok]
      have h7 : f.val ≤ 7 := by scalar_tac
      constructor
      · intro hb1
        refine ⟨hb1, ?_, ?_⟩ <;> rw [hva] <;> omega
      · intro h; exact h.1
  · rename_i hgt
    have hfgt : ¬ (f.val ≤ q / 2) := by scalar_tac
    have hva : (toK f).valMinAbs = (f.val : ℤ) - (q : ℤ) := by rw [hmin, if_neg hfgt]
    step with centered_abs_spec f hRf as ⟨cn, hcn⟩
    have hcnv : cn.val = q - f.val := by
      rw [hcn, hva]
      omega
    split
    · rename_i hgt2
      rw [WP.spec_ok]
      have h8 : 8 < cn.val := by scalar_tac
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro _ hbox
      have := hbox.1
      rw [hva] at this
      omega
    · rename_i hng2
      rw [WP.spec_ok]
      have h8 : cn.val ≤ 8 := by scalar_tac
      constructor
      · intro hb1
        refine ⟨hb1, ?_, ?_⟩ <;> rw [hva] <;> omega
      · intro h; exact h.1

/-- The loop of `quadeval::in_sb`: branchless, so the invariant is "no coefficient
visited so far has left the box". -/
theorem in_sb_loop_spec (a : ring.Rq) (n : Std.Usize) (half : Std.U64) (ok1 : Bool)
    (k : Std.Usize) (ha : Wf a) (hn : n.val = N) (hhalf : half.val = q / 2)
    (hk : k.val ≤ N)
    (hok : ok1 = true ↔ ∀ t < k.val, InBoxK ((toRq a).1.coeff t)) :
    quadeval.in_sb_loop a n half ok1 k
      ⦃ b => (b = true ↔ ∀ t < N, InBoxK ((toRq a).1.coeff t)) ⦄ := by
  rw [quadeval.in_sb_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ N ∧ (s.1 = true ↔ ∀ t < s.2.val, InBoxK ((toRq a).1.coeff t)))
  · rintro ⟨b1, k1⟩ ⟨hk1, hok1⟩
    dsimp only at hk1 hok1
    simp only [quadeval.in_sb_loop.body]
    by_cases hlt : k1 < n
    · rw [if_pos hlt]
      have hkN : k1.val < N := by rw [← hn]; scalar_tac
      step with RqBridge.coeff_spec a k1 ha as ⟨f, hRf, hf⟩
      simp only [cpoly.field.Fp.to_u64, bind_tc_ok]
      step with in_sb_check_spec f half b1 hRf hhalf as ⟨b2, hb2⟩
      step as ⟨k2, hk2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [hk2, hb2, hf]
        constructor
        · rintro ⟨hb1, hbox⟩ t ht
          rcases Nat.lt_or_ge t k1.val with htlt | htge
          · exact hok1.mp hb1 t htlt
          · have : t = k1.val := by omega
            rw [this]; exact hbox
        · intro h
          exact ⟨hok1.mpr (fun t ht => h t (by omega)), h k1.val (by omega)⟩
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = N := by rw [← hn] at hk1 ⊢; scalar_tac
      rw [← heq]; exact hok1
  · exact ⟨hk, hok⟩

set_option maxRecDepth 4096 in
/-- `quadeval::in_sb` **decides** ArkLib's `InSb` at `β = 16`.

An iff, not an equality: `InSb` is a `Prop` (`QuadEval/Reduction.lean:297`).
The box `[-⌊b/2⌋, ⌈b/2⌉-1] = [-8, 7]` is asymmetric, so the proof splits on the
sign of `valMinAbs` — see the file header. -/
theorem in_sb_spec (a : ring.Rq) (ha : Wf a) :
    quadeval.in_sb a ⦃ b => (b = true ↔ InnerOuter.InSb Φ 16 (toRq a)) ⦄ := by
  rw [quadeval.in_sb]
  step as ⟨half, hhalf⟩
  apply spec_mono (in_sb_loop_spec a params.RING_DEGREE half true 0#usize ha
    (by simp) (by scalar_tac) (by simp) (by simp))
  intro b hb
  rw [hb, inSb_iff]

/-- The loop of `quadeval::vec_in_sb`: the accumulator records that no entry
visited so far has left the box. -/
theorem vec_in_sb_loop_spec {cols : ℕ} (v : linalg.PolyVec) (n : Std.Usize) (ok1 : Bool)
    (i : Std.Usize) (hv : WfVec cols v) (hn : n.val = cols) (hi : i.val ≤ cols)
    (hok : ok1 = true ↔ ∀ j < i.val, InnerOuter.InSb Φ 16
      (toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))) :
    quadeval.vec_in_sb_loop v n ok1 i
      ⦃ b => (b = true ↔ ∀ j < cols, InnerOuter.InSb Φ 16
        (toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))) ⦄ := by
  rw [quadeval.vec_in_sb_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ cols ∧ (s.1 = true ↔ ∀ j < s.2.val, InnerOuter.InSb Φ 16
      (toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))))
  · rintro ⟨b1, i1⟩ ⟨hi1, hok1⟩
    dsimp only at hi1 hok1
    simp only [quadeval.vec_in_sb_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hilt : i1.val < v.val.length := by rw [hv.1, ← hn]; scalar_tac
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hv.2 _ (List.getElem_mem hilt)
      step with in_sb_spec r hWr as ⟨bb, hbb⟩
      have hentry : InnerOuter.InSb Φ 16
          (toRq (v.val.getD i1.val (alloc.vec.Vec.new cpoly.field.Fp))) ↔ bb = true := by
        rw [hbb, hr, List.getD_eq_getElem _ _ hilt]
      have hite : (if bb then ok b1 else ok false)
          ⦃ c => (c = true ↔ (b1 = true ∧ bb = true)) ⦄ := by
        cases bb with
        | true =>
          show (ok b1 : Result Bool)
            ⦃ c => (c = true ↔ (b1 = true ∧ (true : Bool) = true)) ⦄
          rw [WP.spec_ok]; simp
        | false =>
          show (ok false : Result Bool)
            ⦃ c => (c = true ↔ (b1 = true ∧ (false : Bool) = true)) ⦄
          rw [WP.spec_ok]; simp
      step with hite as ⟨b2, hb2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [hi2, hb2]
        constructor
        · rintro ⟨hb1, hbt⟩ j hj
          rcases Nat.lt_or_ge j i1.val with hjlt | hjge
          · exact hok1.mp hb1 j hjlt
          · have : j = i1.val := by omega
            rw [this]; exact hentry.mpr hbt
        · intro h
          exact ⟨hok1.mpr (fun j hj => h j (by omega)),
            hentry.mp (h i1.val (by omega))⟩
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = cols := by rw [← hn] at hi1 ⊢; scalar_tac
      rw [← heq]; exact hok1
  · exact ⟨hi, hok⟩

/-- `quadeval::vec_in_sb` decides `vecInSb`. Branchless to the end, so the loop
invariant is "no entry so far has failed" rather than an early exit. -/
theorem vec_in_sb_spec {cols : ℕ} (v : linalg.PolyVec) (hv : WfVec cols v) :
    quadeval.vec_in_sb v
      ⦃ b => (b = true ↔ InnerOuter.vecInSb Φ 16 (toVec (k := cols) v)) ⦄ := by
  rw [quadeval.vec_in_sb]
  simp only [linalg.PolyVec.len]
  apply spec_mono (vec_in_sb_loop_spec v (alloc.vec.Vec.len v) true 0#usize hv
    (by simpa using hv.1) (by simp) (by simp))
  intro b hb
  rw [hb]
  constructor
  · intro h i
    exact h i.val i.isLt
  · intro h j hj
    exact h ⟨j, hj⟩

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
  step with vec_in_sb_spec v hv as ⟨b, hb⟩
  intro hbt
  exact InnerOuter.vecLInftyNorm_le_of_vecInSb Φ (by norm_num) (hb.mp hbt)

end HachiEquiv.QuadEval
