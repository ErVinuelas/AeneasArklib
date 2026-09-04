/-
The **balanced digit layer**: the Hachi gadget inverse `G⁻¹` proper.

Proved, on the bridge from `Scheme.lean`, and part of the audited library --
`lean/Check.lean` § 4 prints the axiom dependencies of every headline spec
below, so a `sorry` here is a `make build` failure. Proved by Aristotle session
`58843236` (2026-09-04, nine obligations to zero) and promoted out of
`lean-wip/` on the strength of that: no errors, no `declaration uses 'sorry'`,
and all nine headline specs on exactly the three Lean kernel axioms.

At ArkLib PR #847 the Hachi gadget inverse `G⁻¹` is the **balanced** digit
decomposition (`balancedZmodDigitDecomposition`), and the unsigned one
(`zmodDigitDecomposition`) is documented as the building block it is shifted
from. `lean/Scheme.lean` proves the unsigned layer — seventy-four specs against
`dd` — and stays as it is: `InnerOuter/Scheme.lean` is generic in the
decomposition, so the two layers are one set of functions at two arguments.
What is added here is the sibling statement at `ddBal`, plus two things the
unsigned layer has no counterpart for:

* the **bounded** `z`-side digit map at `τ = 5`
  (`boundedBalancedZmodDigit`), which is not a `DigitDecomposition` at all
  (`16^5 < q`, so no five-digit decomposition of every residue exists) and
  whose reconstruction law is therefore conditional on `‖x‖ ≤ zBound`. Only
  its per-digit statement is here; the `Fin 5`-indexed reconstruction belongs
  to the `z` decomposition, which is target 2's;
* the **quotient digits** (`rhoDigits`), stated coefficientwise, which is the
  form `rhoAsRq` and the widened `w̃` table consume.

## How the proofs go

`balanced_digit_at_spec` is cheap: `balancedDigit_eq_digit` is `rfl`, so the
statement unfolds to the unsigned digit read at the shifted argument followed by
two field steps. What it needs beyond the unsigned proof is that
`Fp::new BALANCED_SHIFT` is the specification's `balancedShift 16 8` — an `ℕ`
identity, since `BALANCED_SHIFT < q` (`lean/Check.lean` § 1 records both) — and
that the shift add is `Fp`'s, i.e. reduced. `balanced_gadget_decompose_spec`
and `generate_decomps_balanced_spec` are then the `lean/Scheme.lean` loop
scaffolds with `ddBal` for `dd`; the analytic input the unsigned side takes from
`dd_digit_natAbs_le` is upstream's `balancedZmodDigit_natAbs_le` here, so no
local copy is needed.

`bounded_z_digit_at_spec` is the one genuinely new arithmetic obligation. The
Rust computes `Int.toNat (x.valMinAbs + ⌊b/2⌋·S)` by the same three-case split
`commit::centered_abs` makes, with a third case for the clamp; the missing
lemma is that split against `ZMod.valMinAbs`, after which the digit read is the
unsigned division loop unchanged.

**No local `[DecidableEq (ZMod q)]` binder** in any statement below. The
committer's decomposition and ArkLib's generic lemmas would otherwise carry
different instances and unification diverges — the pin says so itself at
`Commitment.lean`.
-/

import Scheme
import ArkLib.Commitments.Functional.Hachi.RingSwitch.RhoDigits
import ArkLib.Commitments.Functional.Hachi.Params

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.Balanced

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme

/-! ## The instantiated decompositions -/

/-- **The Hachi gadget inverse's digit map** at this crate's parameters: the
balanced base-16 decomposition at `δ = 8`. Its two side conditions are `1 < b`
and `q ≤ b ^ digits`, the same two `dd` takes and the same two
`lean/Check.lean` § 1 checks of the extracted constants. -/
def ddBal : DigitDecomposition (R := ZMod q) (16 : ZMod q) 8 :=
  balancedZmodDigitDecomposition 16 8 (by norm_num) (by norm_num)

/-- **The folded witness's digit map**: balanced base-16 at `τ = 5`, bounded by
`zBound = 131072`. Not a `DigitDecomposition` and cannot be — `16^5 < q` — so
the structure is `BoundedDigitDecomposition`, whose reconstruction law carries
the shortness hypothesis. Its capacity obligation
`131072 ≤ balancedDigitCapacity 16 5 = 489335` is `lean/Check.lean` § 1's. -/
def bddZ : BoundedDigitDecomposition (q := q) (16 : ZMod q) 5 131072 :=
  boundedBalancedZmodDigitDecomposition 16 5 131072 (by norm_num) (by
    have h := InnerOuter.HachiParams.balancedDigitCapacity_eq
    simp only [InnerOuter.HachiParams.hachiB, InnerOuter.HachiParams.hachiTau] at h
    simp [h])

/-! ## The extracted constants, in the specification's vocabulary -/

/-- `params::BALANCED_SHIFT` is the specification's `balancedShift 16 8`, read in
`ZMod q`: `⌊b/2⌋ · (1 + b + ⋯ + b^7) = 8 · 286331153`. -/
theorem balanced_shift_eq :
    ((params.BALANCED_SHIFT.val : ℕ) : ZMod q) = balancedShift (q := q) 16 8 := by
  simp only [balancedShift, params.BALANCED_SHIFT, Fin.sum_univ_eight]
  norm_num

/-- `params::HALF_BASE` is `⌊b/2⌋`, read in `ZMod q`. -/
theorem half_base_eq :
    ((params.HALF_BASE.val : ℕ) : ZMod q) = (((16 / 2 : ℕ) : ℕ) : ZMod q) := by
  norm_num [params.HALF_BASE]

/-- `params::Z_BALANCED_SHIFT` is the `z`-side shift `⌊b/2⌋ · S` at `τ = 5`. -/
theorem z_balanced_shift_eq :
    ((16 / 2 : ℕ) : ℤ) * (digitOnesValue 16 5 : ℤ) = 559240 := by
  norm_num [digitOnesValue, Finset.sum_range_succ]

/-! ## The balanced digit layer -/

/-- `gadget::digit_at` read without a `Fin` index: the unsigned base-16 digit of
the canonical representative, at every `e`. The `Fin 8`-indexed form is
`HachiEquiv.Scheme.digit_at_spec`; this one is what the balanced layer needs,
since `balancedDigit` takes a bare `ℕ`. -/
theorem digit_at_raw_spec (c : cpoly.field.Fp) (e : Std.Usize) (hc : Red c) :
    gadget.digit_at c e
      ⦃ d => Red d ∧
        toK d = (((Nat.digits 16 (toK c).val).getD e.val 0 : ℕ) : ZMod q) ⦄ := by
  have hb : (params.GADGET_BASE).val = 16 := by simp [params.GADGET_BASE]
  have hcv : (toK c).val = c.val := by
    simp only [toK, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hc
  rw [gadget.digit_at]
  simp only [cpoly.field.Fp.to_u64]
  show (do
      let rest1 ← gadget.digit_at_loop e params.GADGET_BASE c 0#usize
      let i ← rest1 % params.GADGET_BASE
      cpoly.field.Fp.new i)
    ⦃ d => Red d ∧ toK d = (((Nat.digits 16 (toK c).val).getD e.val 0 : ℕ) : ZMod q) ⦄
  step with digit_at_loop_spec e c 0#usize c.val (by simp) (by simp) as ⟨r, hr⟩
  step as ⟨m, hm⟩
  step as ⟨d, hRd, hd⟩
  refine ⟨hRd, ?_⟩
  rw [hd, hcv, Nat.getD_digits _ _ (by norm_num), hm, hr, hb]

/-- `gadget::balanced_digit_at` read without a `Fin` index: ArkLib's
`InnerOuter.balancedDigit 16 8`, at every `e`. -/
theorem balanced_digit_at_raw_spec (c : cpoly.field.Fp) (e : Std.Usize) (hc : Red c) :
    gadget.balanced_digit_at c e
      ⦃ d => Red d ∧ toK d = InnerOuter.balancedDigit 16 8 (toK c) e.val ⦄ := by
  rw [gadget.balanced_digit_at]
  step as ⟨shift, hRshift, hshift⟩
  step as ⟨half, hRhalf, hhalf⟩
  step as ⟨f, hRf, hf⟩
  step with digit_at_raw_spec f e hRf as ⟨g, hRg, hg⟩
  step as ⟨d, hRd, hd⟩
  refine ⟨hRd, ?_⟩
  rw [hd, hg, hhalf, hf, hshift, balanced_shift_eq, half_base_eq,
    InnerOuter.balancedDigit]

/-- `gadget::balanced_digit_at` — ArkLib's `balancedZmodDigitDecomposition.digit`
at one `e`: the unsigned digit of the **field**-shifted coefficient, less
`⌊b/2⌋`. -/
theorem balanced_digit_at_spec (c : cpoly.field.Fp) (e : Std.Usize)
    (hc : Red c) (he : e.val < 8) :
    gadget.balanced_digit_at c e
      ⦃ d => Red d ∧ toK d = ddBal.digit (toK c) ⟨e.val, he⟩ ⦄ := by
  apply spec_mono (balanced_digit_at_raw_spec c e hc)
  rintro d ⟨hRd, hd⟩
  refine ⟨hRd, ?_⟩
  rw [hd, ddBal]
  exact InnerOuter.balancedDigit_eq_digit (by norm_num) (by norm_num)
    (toK c) ⟨e.val, he⟩

/-- The loop of `gadget::balanced_digit_decompose`: after `e` turns the
accumulator holds balanced digits `0 … e-1`, in order. -/
theorem balanced_digit_decompose_loop_spec (c : cpoly.field.Fp) (digits : Std.Usize)
    (out : alloc.vec.Vec cpoly.field.Fp) (e : Std.Usize)
    (hc : Red c) (hdig : digits.val = 8) (he : e.val ≤ 8)
    (hlen : out.val.length = e.val) (hred : ∀ u ∈ out.val, Red u)
    (hval : ∀ (t : ℕ) (ht : t < 8), t < e.val →
      coeffK out t = ddBal.digit (toK c) ⟨t, ht⟩) :
    gadget.balanced_digit_decompose_loop c digits out e
      ⦃ z => z.val.length = 8 ∧ (∀ u ∈ z.val, Red u) ∧
        ∀ (t : ℕ) (ht : t < 8), coeffK z t = ddBal.digit (toK c) ⟨t, ht⟩ ⦄ := by
  rw [gadget.balanced_digit_decompose_loop]
  apply loop.spec_decr_nat (fun s => digits.val - s.2.val)
    (fun s => s.2.val ≤ 8 ∧ s.1.val.length = s.2.val ∧ (∀ u ∈ s.1.val, Red u) ∧
      ∀ (t : ℕ) (ht : t < 8), t < s.2.val →
        coeffK s.1 t = ddBal.digit (toK c) ⟨t, ht⟩)
  · rintro ⟨o1, e1⟩ ⟨he1, hlen1, hred1, hval1⟩
    dsimp only at he1 hlen1 hred1 hval1
    simp only [gadget.balanced_digit_decompose_loop.body]
    by_cases hlt : e1 < digits
    · rw [if_pos hlt]
      have he1lt : e1.val < 8 := by rw [← hdig]; scalar_tac
      step with balanced_digit_at_spec c e1 hc he1lt as ⟨f, hRf, hf⟩
      have hcap : o1.val.length < Usize.max := by rw [hlen1]; scalar_tac
      step as ⟨o2, ho2⟩
      step as ⟨e2, he2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, he2, List.length_append, hlen1]; simp
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hred1 u h
        · rw [List.mem_singleton.mp h]; exact hRf
      · intro t ht htlt
        rw [he2] at htlt
        rcases Nat.lt_or_ge t e1.val with h | h
        · rw [coeffK_append_lt ho2 (by omega : t < o1.val.length)]
          exact hval1 t ht h
        · have hteq : t = e1.val := by omega
          subst hteq
          conv_lhs => rw [← hlen1]
          rw [coeffK_append_eq ho2]
          exact hf
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : e1.val = 8 := by scalar_tac
      refine ⟨by rw [hlen1, heq], hred1, ?_⟩
      intro t ht
      exact hval1 t ht (by omega)
  · exact ⟨he, hlen, hred, hval⟩

/-- `gadget::balanced_digit_decompose` — the same at every `e < 8`, as a vector,
least-significant first. -/
theorem balanced_digit_decompose_spec (c : cpoly.field.Fp) (hc : Red c) :
    gadget.balanced_digit_decompose c
      ⦃ z => z.val.length = 8 ∧ (∀ u ∈ z.val, Red u) ∧
        ∀ e : Fin 8, coeffK z e.val = ddBal.digit (toK c) e ⦄ := by
  simp only [gadget.balanced_digit_decompose]
  apply spec_mono (balanced_digit_decompose_loop_spec c params.GADGET_DIGITS
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize hc (by simp [params.GADGET_DIGITS])
    (by simp) (by simp) (by intro u hu; simp at hu) (by intro t ht h; simp at h))
  rintro z ⟨h1, h2, h3⟩
  exact ⟨h1, h2, fun e => h3 e.val e.isLt⟩

/-! ### `gadget::balanced_gadget_decompose` -/

/-- The ring element `gadget::balanced_gadget_decompose` writes at the flat index
`8 * i + e`: balanced digit `e` of every coefficient of block `i`. -/
def balancedDigitBlock (x : linalg.PolyVec) (i e : ℕ) : Rq Φ :=
  Rq.ofFinCoeff Φ N (fun t =>
    InnerOuter.balancedDigit 16 8
      ((toRq (x.val.getD i (alloc.vec.Vec.new cpoly.field.Fp))).1.coeff t) e)

/-- The innermost loop of `gadget::balanced_gadget_decompose`: `coeffs` collects
balanced digit `e` of the first `k` coefficients of block `i`. -/
theorem balanced_gadget_decompose_coeff_loop_spec {rows : ℕ} (x : linalg.PolyVec)
    (degree i e : Std.Usize) (coeffs : alloc.vec.Vec cpoly.field.Fp) (k : Std.Usize)
    (hx : WfVec rows x) (hdeg : degree.val = N) (hi : i.val < rows)
    (hk : k.val ≤ N) (hlen : coeffs.val.length = k.val)
    (hred : ∀ u ∈ coeffs.val, Red u)
    (hval : ∀ t < k.val, coeffK coeffs t
      = InnerOuter.balancedDigit 16 8
          ((toRq (x.val.getD i.val (alloc.vec.Vec.new cpoly.field.Fp))).1.coeff t) e.val) :
    gadget.balanced_gadget_decompose_loop0_loop0_loop0 x degree i e coeffs k
      ⦃ z => z.val.length = N ∧ (∀ u ∈ z.val, Red u) ∧ ∀ t < N, coeffK z t
        = InnerOuter.balancedDigit 16 8
            ((toRq (x.val.getD i.val
              (alloc.vec.Vec.new cpoly.field.Fp))).1.coeff t) e.val ⦄ := by
  have hilt : i.val < x.val.length := by rw [hx.1]; exact hi
  have hxi : x.val.getD i.val (alloc.vec.Vec.new cpoly.field.Fp) = x.val[i.val] :=
    List.getD_eq_getElem _ _ hilt
  have hWx : Wf x.val[i.val] := hx.2 _ (List.getElem_mem hilt)
  rw [gadget.balanced_gadget_decompose_loop0_loop0_loop0]
  apply loop.spec_decr_nat (fun s => degree.val - s.2.val)
    (fun s => s.2.val ≤ N ∧ s.1.val.length = s.2.val ∧ (∀ u ∈ s.1.val, Red u) ∧
      ∀ t < s.2.val, coeffK s.1 t
        = InnerOuter.balancedDigit 16 8
            ((toRq (x.val.getD i.val
              (alloc.vec.Vec.new cpoly.field.Fp))).1.coeff t) e.val)
  · rintro ⟨c1, k1⟩ ⟨hk1, hlen1, hred1, hval1⟩
    dsimp only at hk1 hlen1 hred1 hval1
    simp only [gadget.balanced_gadget_decompose_loop0_loop0_loop0.body]
    by_cases hlt : k1 < degree
    · rw [if_pos hlt]
      have hkN : k1.val < N := by rw [← hdeg]; scalar_tac
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hWx
      step with RqBridge.coeff_spec r k1 hWr as ⟨f, hRf, hf⟩
      step with balanced_digit_at_raw_spec f e hRf as ⟨g, hRg, hg⟩
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
          rw [hteq, hpush, hg, hf, hr, ← hxi]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = N := by rw [← hdeg] at hk1 ⊢; scalar_tac
      refine ⟨by rw [hlen1, heq], hred1, ?_⟩
      rw [← heq]; exact hval1
  · exact ⟨hk, hlen, hred, hval⟩

/-- The middle loop of `gadget::balanced_gadget_decompose`: one digit block of
row `i` per turn. -/
theorem balanced_gadget_decompose_digit_loop_spec {rows : ℕ} (x : linalg.PolyVec)
    (digits degree i : Std.Usize) (out : alloc.vec.Vec ring.Rq) (e : Std.Usize)
    (hx : WfVec rows x) (hmax : 8 * rows ≤ Usize.max)
    (hdig : digits.val = 8) (hdeg : degree.val = N) (hi : i.val < rows)
    (he : e.val ≤ 8) (hlen : out.val.length = 8 * i.val + e.val)
    (hwf : ∀ y ∈ out.val, Wf y)
    (hval : ∀ i' e' : ℕ, e' < 8 → 8 * i' + e' < 8 * i.val + e.val →
      toRq (out.val.getD (8 * i' + e') (alloc.vec.Vec.new cpoly.field.Fp))
        = balancedDigitBlock x i' e') :
    gadget.balanced_gadget_decompose_loop0_loop0 x digits degree out i e
      ⦃ z => z.val.length = 8 * i.val + 8 ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ i' e' : ℕ, e' < 8 → 8 * i' + e' < 8 * i.val + 8 →
          toRq (z.val.getD (8 * i' + e') (alloc.vec.Vec.new cpoly.field.Fp))
            = balancedDigitBlock x i' e' ⦄ := by
  have hmaxb : 8 * i.val + 8 ≤ Usize.max := by
    have h1 : 8 * (i.val + 1) ≤ 8 * rows := Nat.mul_le_mul_left 8 (by omega)
    omega
  rw [gadget.balanced_gadget_decompose_loop0_loop0]
  apply loop.spec_decr_nat (fun s => digits.val - s.2.val)
    (fun s => s.2.val ≤ 8 ∧ s.1.val.length = 8 * i.val + s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ i' e' : ℕ, e' < 8 → 8 * i' + e' < 8 * i.val + s.2.val →
        toRq (s.1.val.getD (8 * i' + e') (alloc.vec.Vec.new cpoly.field.Fp))
          = balancedDigitBlock x i' e')
  · rintro ⟨o1, e1⟩ ⟨he1, hlen1, hwf1, hval1⟩
    dsimp only at he1 hlen1 hwf1 hval1
    simp only [gadget.balanced_gadget_decompose_loop0_loop0.body]
    by_cases hlt : e1 < digits
    · rw [if_pos hlt]
      have helt : e1.val < 8 := by rw [← hdig]; scalar_tac
      have hinner := balanced_gadget_decompose_coeff_loop_spec x degree i e1
        (alloc.vec.Vec.new cpoly.field.Fp) 0#usize hx hdeg hi (by simp) (by simp)
        (by intro u hu; simp at hu) (by intro t ht; simp at ht)
      step with hinner as ⟨cs, hcslen, hcsred, hcsval⟩
      step with RqBridge.from_coeffs_spec cs hcsred as ⟨rr, hWrr, hrr⟩
      step as ⟨o2, ho2⟩
      step as ⟨e2, he2⟩
      have hblock : toRq rr = balancedDigitBlock x i.val e1.val := by
        rw [hrr, balancedDigitBlock]
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
        rcases Nat.lt_or_ge (8 * i' + e') (8 * i.val + e1.val) with hjlt | hjge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 i' e' he' hjlt]
        · have hi'e : i' = i.val ∧ e' = e1.val := by omega
          obtain ⟨hii, hee⟩ := hi'e
          have hidx : 8 * i' + e' = o1.val.length := by omega
          rw [hidx, ho2, getD_append_eq, hblock, hii, hee]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : e1.val = 8 := by rw [← hdig] at he1 ⊢; scalar_tac
      rw [heq] at hlen1 hval1
      exact ⟨hlen1, hwf1, hval1⟩
  · exact ⟨he, hlen, hwf, hval⟩

/-- The outer loop of `gadget::balanced_gadget_decompose`: one block of `8` digit
slots per row. -/
theorem balanced_gadget_decompose_outer_loop_spec {rows : ℕ} (x : linalg.PolyVec)
    (digits degree r : Std.Usize) (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hx : WfVec rows x) (hmax : 8 * rows ≤ Usize.max)
    (hdig : digits.val = 8) (hdeg : degree.val = N) (hr : r.val = rows)
    (hi : i.val ≤ rows) (hlen : out.val.length = 8 * i.val)
    (hwf : ∀ y ∈ out.val, Wf y)
    (hval : ∀ i' e' : ℕ, e' < 8 → 8 * i' + e' < 8 * i.val →
      toRq (out.val.getD (8 * i' + e') (alloc.vec.Vec.new cpoly.field.Fp))
        = balancedDigitBlock x i' e') :
    gadget.balanced_gadget_decompose_loop0 x digits degree r out i
      ⦃ z => z.val.length = 8 * rows ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ i' e' : ℕ, e' < 8 → 8 * i' + e' < 8 * rows →
          toRq (z.val.getD (8 * i' + e') (alloc.vec.Vec.new cpoly.field.Fp))
            = balancedDigitBlock x i' e' ⦄ := by
  rw [gadget.balanced_gadget_decompose_loop0]
  apply loop.spec_decr_nat (fun s => r.val - s.2.val)
    (fun s => s.2.val ≤ rows ∧ s.1.val.length = 8 * s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ i' e' : ℕ, e' < 8 → 8 * i' + e' < 8 * s.2.val →
        toRq (s.1.val.getD (8 * i' + e') (alloc.vec.Vec.new cpoly.field.Fp))
          = balancedDigitBlock x i' e')
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [gadget.balanced_gadget_decompose_loop0.body]
    by_cases hlt : i1 < r
    · rw [if_pos hlt]
      have hilt : i1.val < rows := by rw [← hr]; scalar_tac
      have hmid := balanced_gadget_decompose_digit_loop_spec x digits degree i1 o1 0#usize
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

/-- **The headline for the balanced layer**: `gadget::balanced_gadget_decompose`
is ArkLib's `gadgetDecompose` at `ddBal` — the gadget inverse `G⁻¹` the paper's
Eq. (20) range check accepts.

`hmax` is the output vector's capacity side condition, exactly as in
`gadget_decompose_spec`: the Rust pushes `8 * rows` ring elements into a `Vec`,
which the extracted model only permits below `Usize.max`. -/
theorem balanced_gadget_decompose_spec {rows : ℕ} (x : linalg.PolyVec)
    (hx : WfVec rows x) (hmax : 8 * rows ≤ Usize.max) :
    gadget.balanced_gadget_decompose x
      ⦃ z => WfVec (rows * 8) z ∧ toVec (k := rows * 8) z
        = gadgetDecompose Φ ddBal (toVec (k := rows) x) ⦄ := by
  have hdig : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  have hdeg : (params.RING_DEGREE).val = N := by simp
  rw [gadget.balanced_gadget_decompose]
  simp only [linalg.PolyVec.len, linalg.PolyVec.new, bind_ok_id]
  apply spec_mono (balanced_gadget_decompose_outer_loop_spec x params.GADGET_DIGITS
    params.RING_DEGREE (alloc.vec.Vec.len x) (alloc.vec.Vec.new ring.Rq) 0#usize
    hx hmax hdig hdeg (by simpa using hx.1) (by simp) (by simp)
    (by intro y hy; simp at hy) (by intro i' e' _ hb; simp at hb))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨by rw [hzlen]; ring, hzwf⟩, ?_⟩
  funext m
  have hm : m.val < rows * 8 := m.isLt
  have he'lt : m.val % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hi'lt : m.val / 8 < rows := by omega
  have hsplit : 8 * (m.val / 8) + m.val % 8 = m.val := by omega
  have hfp : (finProdFinEquiv (⟨m.val / 8, hi'lt⟩, ⟨m.val % 8, he'lt⟩) : Fin (rows * 8))
      = m := by
    apply Fin.ext
    show m.val % 8 + 8 * (m.val / 8) = m.val
    omega
  have hgd : gadgetDecompose Φ ddBal (toVec (k := rows) x)
      (finProdFinEquiv (⟨m.val / 8, hi'lt⟩, ⟨m.val % 8, he'lt⟩))
      = Rq.ofFinCoeff Φ Φ.φ.natDegree
          (fun k => ddBal.digit ((toVec (k := rows) x ⟨m.val / 8, hi'lt⟩).1.coeff k)
            ⟨m.val % 8, he'lt⟩) :=
    gadgetDecomposeFun_apply Φ ddBal.digit (toVec (k := rows) x) _ _
  rw [hfp] at hgd
  rw [hgd]
  simp only [toVec]
  have hz := hzval (m.val / 8) (m.val % 8) he'lt (by omega)
  rw [hsplit] at hz
  rw [hz, balancedDigitBlock, RqBridge.phi_natDegree]
  rfl

/-- **The balanced digits are `⌊b/2⌋`-short**, unconditionally in the input —
ArkLib's `balancedZmodDigit_natAbs_le` read on the extracted digit. The
counterpart of `dd_digit_natAbs_le` for this layer, and the reason no local copy
of an upstream norm lemma is needed here: PR #847 kept the balanced bounds and
dropped only the unsigned ones. -/
theorem balanced_digit_at_natAbs_le (c : cpoly.field.Fp) (e : Std.Usize)
    (hc : Red c) (he : e.val < 8) :
    gadget.balanced_digit_at c e ⦃ d => (toK d).valMinAbs.natAbs ≤ 8 ⦄ := by
  apply spec_mono (balanced_digit_at_spec c e hc he)
  rintro d ⟨-, hd⟩
  rw [hd, ddBal]
  simpa using balancedZmodDigit_natAbs_le (q := q) (b := 16) (digits := 8)
    (by norm_num) (by norm_num) (by norm_num) (toK c) ⟨e.val, he⟩

/-! ## The bounded digit layer, for the folded witness -/

/-- The division loop of `gadget::bounded_z_digit_at`: after `i` divisions by 16
the remaining word is `c₀ / 16ⁱ`. The same loop as `gadget::digit_at`'s, but a
distinct extracted definition, so it takes its own statement. -/
theorem bounded_z_digit_at_loop_spec (e : Std.Usize) (rest : Std.U64) (i : Std.Usize)
    (c0 : ℕ) (hi : i.val ≤ e.val) (hrest : rest.val = c0 / 16 ^ i.val) :
    gadget.bounded_z_digit_at_loop e params.GADGET_BASE rest i
      ⦃ z => z.val = c0 / 16 ^ e.val ⦄ := by
  have hb : (params.GADGET_BASE).val = 16 := by simp [params.GADGET_BASE]
  rw [gadget.bounded_z_digit_at_loop]
  apply loop.spec_decr_nat (fun s => e.val - s.2.val)
    (fun s => s.2.val ≤ e.val ∧ s.1.val = c0 / 16 ^ s.2.val)
  · rintro ⟨r1, i1⟩ ⟨hi1, hval1⟩
    dsimp only at hi1 hval1
    simp only [gadget.bounded_z_digit_at_loop.body]
    by_cases hlt : i1 < e
    · rw [if_pos hlt]
      step as ⟨r2, hr2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [hr2, hval1, hb, hi2, Nat.div_div_eq_div_mul, ← pow_succ]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = e.val := by scalar_tac
      rw [hval1, heq]
  · exact ⟨hi, hrest⟩

/-- `gadget::bounded_z_digit_at` — ArkLib's `boundedBalancedZmodDigit` at
`τ = 5`: centre first (`ZMod.valMinAbs`), shift in `ℤ`, clamp with `Int.toNat`,
then read an unsigned base-16 digit and recentre.

Total at every input, and the range bound below is unconditional; what an input
within `zBound` buys is *reconstruction*, which is the `Fin 5`-indexed statement
the `z` decomposition needs and is not stated here. -/
theorem bounded_z_digit_at_spec (c : cpoly.field.Fp) (e : Std.Usize)
    (hc : Red c) (he : e.val < 5) :
    gadget.bounded_z_digit_at c e
      ⦃ d => Red d ∧ toK d = bddZ.digit (toK c) ⟨e.val, he⟩ ⦄ := by
  have hb : (params.GADGET_BASE).val = 16 := by simp [params.GADGET_BASE]
  have hcq : c.val < 4294967197 := hc
  have hqnum : q = 4294967197 := rfl
  have hz : (params.Z_BALANCED_SHIFT).val = 559240 := by simp [params.Z_BALANCED_SHIFT]
  have hcv : (toK c).val = c.val := by
    simp only [toK, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hc
  have hmin : (toK c).valMinAbs
      = if c.val ≤ q / 2 then (c.val : ℤ) else (c.val : ℤ) - (q : ℤ) := by
    rw [ZMod.valMinAbs_def_pos, hcv]
  -- the tail of the function, once the shifted word is known
  have htail : ∀ w : Std.U64,
      (w.val : ℤ) = ((toK c).valMinAbs
        + ((16 / 2 : ℕ) : ℤ) * (digitOnesValue 16 5 : ℤ)).toNat →
      (do
        let rest1 ← gadget.bounded_z_digit_at_loop e params.GADGET_BASE w 0#usize
        let i ← rest1 % params.GADGET_BASE
        let f ← cpoly.field.Fp.new i
        let f1 ← cpoly.field.Fp.new params.HALF_BASE
        cpoly.field.Fp.Insts.CoreOpsArithSubFpFp.sub f f1)
        ⦃ d => Red d ∧ toK d = bddZ.digit (toK c) ⟨e.val, he⟩ ⦄ := by
    intro w hw
    have hwn : w.val = ((toK c).valMinAbs
        + ((16 / 2 : ℕ) : ℤ) * (digitOnesValue 16 5 : ℤ)).toNat := by exact_mod_cast hw
    step with bounded_z_digit_at_loop_spec e w 0#usize w.val (by simp) (by simp) as ⟨r, hr⟩
    step as ⟨m, hm⟩
    step as ⟨f, hRf, hf⟩
    step as ⟨f1, hRf1, hf1⟩
    step as ⟨d, hRd, hd⟩
    refine ⟨hRd, ?_⟩
    rw [hd, hf, hf1, hm, hr, hb, hwn, half_base_eq]
    simp only [bddZ, boundedBalancedZmodDigitDecomposition, boundedBalancedZmodDigit]
    rw [Nat.getD_digits _ _ (by norm_num)]
  rw [gadget.bounded_z_digit_at]
  step as ⟨hq2, hhq2⟩
  simp only [cpoly.field.Fp.to_u64, bind_tc_ok]
  split
  · -- the centered representative is non-negative: shift up in `ℕ`
    rename_i hle
    have hcle : c.val ≤ q / 2 := by scalar_tac
    step as ⟨w, hwv⟩
    refine htail w ?_
    rw [hmin, if_pos hcle, z_balanced_shift_eq]
    omega
  · rename_i hgt
    have hcgt : ¬ c.val ≤ q / 2 := by scalar_tac
    step as ⟨neg, hneg⟩
    split
    · rename_i hle2
      step as ⟨w, hwv⟩
      refine htail w ?_
      have hwval : w.val = 559240 - (4294967197 - c.val) := by scalar_tac
      have hcbig : 4294967197 - c.val ≤ 559240 := by scalar_tac
      rw [hmin, if_neg hcgt, z_balanced_shift_eq, hwval, hqnum]
      omega
    · rename_i hgt2
      simp only [bind_tc_ok]
      refine htail 0#u64 ?_
      have hcsmall : 559240 < 4294967197 - c.val := by scalar_tac
      have hqz : ((q : ℕ) : ℤ) = 4294967197 := by norm_num
      have hzero : ((0#u64 : Std.U64).val : ℕ) = 0 := by simp
      rw [hmin, if_neg hcgt, z_balanced_shift_eq, hzero]
      omega

/-- The bounded digits lie in the same box `[-8, 7]`, for *every* input —
ArkLib's `boundedBalancedZmodDigit_valMinAbs_mem`, which takes no shortness
hypothesis. -/
theorem bounded_z_digit_at_natAbs_le (c : cpoly.field.Fp) (e : Std.Usize)
    (hc : Red c) (he : e.val < 5) :
    gadget.bounded_z_digit_at c e ⦃ d => (toK d).valMinAbs.natAbs ≤ 8 ⦄ := by
  apply spec_mono (bounded_z_digit_at_spec c e hc he)
  rintro d ⟨-, hd⟩
  rw [hd]
  simp only [bddZ, boundedBalancedZmodDigitDecomposition]
  simpa using boundedBalancedZmodDigit_natAbs_le (q := q) (b := 16) (digits := 5)
    (by norm_num) (by norm_num) (toK c) ⟨e.val, he⟩

/-! ## The quotient digits -/

/-- The digit count the quotient is split into *is* the gadget's:
`rhoDigitCount q 16 = Nat.clog 16 q = 8`. -/
theorem rhoDigitCount_eq : InnerOuter.rhoDigitCount q 16 = 8 := by
  have h := InnerOuter.HachiParams.clog_eq_delta
  simp only [InnerOuter.HachiParams.hachiB, InnerOuter.HachiParams.hachiQ,
    InnerOuter.HachiParams.hachiDelta] at h
  exact h

/-- The loop of `ringswitch::rho_digits`: `coeffs` collects digit `u` of the
first `k` coefficients of `ρ`. -/
theorem rho_digits_loop_spec (rho : ring.Rq) (u degree : Std.Usize)
    (coeffs : alloc.vec.Vec cpoly.field.Fp) (k : Std.Usize)
    (hrho : Wf rho) (hdeg : degree.val = N) (hk : k.val ≤ N)
    (hlen : coeffs.val.length = k.val) (hred : ∀ x ∈ coeffs.val, Red x)
    (hval : ∀ t < k.val, coeffK coeffs t
      = InnerOuter.balancedDigit 16 8 (coeffK rho t) u.val) :
    ringswitch.rho_digits_loop rho u degree coeffs k
      ⦃ z => z.val.length = N ∧ (∀ x ∈ z.val, Red x) ∧
        ∀ t < N, coeffK z t = InnerOuter.balancedDigit 16 8 (coeffK rho t) u.val ⦄ := by
  rw [ringswitch.rho_digits_loop]
  apply loop.spec_decr_nat (fun s => degree.val - s.2.val)
    (fun s => s.2.val ≤ N ∧ s.1.val.length = s.2.val ∧ (∀ x ∈ s.1.val, Red x) ∧
      ∀ t < s.2.val, coeffK s.1 t = InnerOuter.balancedDigit 16 8 (coeffK rho t) u.val)
  · rintro ⟨c1, k1⟩ ⟨hk1, hlen1, hred1, hval1⟩
    dsimp only at hk1 hlen1 hred1 hval1
    simp only [ringswitch.rho_digits_loop.body]
    by_cases hlt : k1 < degree
    · rw [if_pos hlt]
      have hkN : k1.val < N := by rw [← hdeg]; scalar_tac
      step with HachiEquiv.Ring.coeff_spec rho k1 hrho as ⟨f, hRf, hf⟩
      step with balanced_digit_at_raw_spec f u hRf as ⟨g, hRg, hg⟩
      step as ⟨c2, hc2⟩
      step as ⟨k2, hk2⟩
      refine ⟨by omega, ?_, ?_, ?_, ?_⟩
      · rw [hc2, hk2, List.length_append, hlen1]; simp
      · intro x hx
        rw [hc2] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hred1 x h
        · rw [List.mem_singleton.mp h]; exact hRg
      · intro t ht
        rw [hk2] at ht
        rcases Nat.lt_or_ge t k1.val with htlt | htge
        · rw [coeffK_append_lt hc2 (by omega), hval1 t htlt]
        · have hteq : t = k1.val := by omega
          have hpush : coeffK c2 k1.val = toK g := by
            rw [← hlen1]; exact coeffK_append_eq hc2
          rw [hteq, hpush, hg, hf]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = N := by rw [← hdeg] at hk1 ⊢; scalar_tac
      refine ⟨by rw [hlen1, heq], hred1, ?_⟩
      rw [← heq]; exact hval1
  · exact ⟨hk, hlen, hred, hval⟩

/-- `ringswitch::rho_digits` — ArkLib's `rhoDigits` at `b = 16`, coefficientwise.

Stated on the coefficients rather than through `rhoAsRq` because that is the
form `rhoDigits_coeff` gives and the form the widened `w̃` table consumes: the
lift `rhoAsRq Φ (rhoDigits Φ 16 ρ u) = toRq z` follows from this together with
`Rq.ofFinCoeff`'s own extensionality, and needs `ρ`'s degree bound
(`LiftedWitness.hρ`) only where the *reconstruction* is claimed.

The digit count is `rhoDigitCount q 16 = Nat.clog 16 q`, which
`lean/Check.lean` § 1 proves is `GADGET_DIGITS = 8` — so the digit map here is
the same `balancedDigit 16 8` that `ddBal` bundles, and this spec reduces to
`balanced_digit_at_spec` inside a coefficient loop. -/
theorem rho_digits_spec (rho : ring.Rq) (u : Std.Usize) (hrho : Wf rho) :
    ringswitch.rho_digits rho u
      ⦃ z => Wf z ∧ ∀ k : Fin N,
          coeffK z k.val
            = InnerOuter.balancedDigit 16 (InnerOuter.rhoDigitCount q 16) (coeffK rho k.val) u.val ⦄ := by
  have hdeg : (params.RING_DEGREE).val = N := by simp
  rw [ringswitch.rho_digits]
  step with rho_digits_loop_spec rho u params.RING_DEGREE
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize hrho hdeg (by simp) (by simp)
    (by intro x hx; simp at hx) (by intro t ht; simp at ht) as ⟨cs, hcslen, hcsred, hcsval⟩
  apply spec_mono (HachiEquiv.Ring.from_coeffs_spec cs hcsred)
  rintro z ⟨hWz, hz⟩
  refine ⟨hWz, ?_⟩
  intro k
  rw [rhoDigitCount_eq, hz k.val k.isLt, hcsval k.val k.isLt]

/-! ## The balanced committer -/

/-- The loop of `commit::generate_decomps_balanced`: per block `sᵢ = G⁻¹(mᵢ)`
and `t̂ᵢ = G⁻¹(A sᵢ)`, at the balanced digit map. -/
theorem generate_decomps_balanced_loop_spec (pp : commit.PublicParams)
    (m : alloc.vec.Vec linalg.PolyVec) (blocks : Std.Usize)
    (ss ts : alloc.vec.Vec linalg.PolyVec) (i : Std.Usize)
    (hpp : WfParams pp) (hm : m.val.length = 1024 ∧ ∀ x ∈ m.val, WfVec 1024 x)
    (hb : blocks.val = 1024) (hi : i.val ≤ 1024)
    (hss : ss.val.length = i.val) (hts : ts.val.length = i.val)
    (hWss : ∀ y ∈ ss.val, WfVec (1024 * 8) y) (hWts : ∀ y ∈ ts.val, WfVec (1 * 8) y)
    (hvss : ∀ j < i.val, toVec (k := 1024 * 8) (ss.val.getD j (alloc.vec.Vec.new ring.Rq))
      = gadgetDecompose Φ ddBal (toVec (k := 1024) (m.val.getD j (alloc.vec.Vec.new ring.Rq))))
    (hvts : ∀ j < i.val, toVec (k := 1 * 8) (ts.val.getD j (alloc.vec.Vec.new ring.Rq))
      = gadgetDecompose Φ ddBal (ArkLib.Lattices.matVecMul
          (toMat (rows := 1) (cols := 1024 * 8) pp.inner_matrix)
          (gadgetDecompose Φ ddBal
            (toVec (k := 1024) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))))) :
    commit.generate_decomps_balanced_loop pp m blocks ss ts i
      ⦃ r => r.1.val.length = 1024 ∧ r.2.val.length = 1024 ∧
        (∀ y ∈ r.1.val, WfVec (1024 * 8) y) ∧ (∀ y ∈ r.2.val, WfVec (1 * 8) y) ∧
        (∀ j < 1024, toVec (k := 1024 * 8) (r.1.val.getD j (alloc.vec.Vec.new ring.Rq))
          = gadgetDecompose Φ ddBal
              (toVec (k := 1024) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))) ∧
        (∀ j < 1024, toVec (k := 1 * 8) (r.2.val.getD j (alloc.vec.Vec.new ring.Rq))
          = gadgetDecompose Φ ddBal (ArkLib.Lattices.matVecMul
              (toMat (rows := 1) (cols := 1024 * 8) pp.inner_matrix)
              (gadgetDecompose Φ ddBal
                (toVec (k := 1024) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))))) ⦄ := by
  rw [commit.generate_decomps_balanced_loop]
  apply loop.spec_decr_nat (fun s => blocks.val - s.2.2.val)
    (fun s => s.2.2.val ≤ 1024 ∧ s.1.val.length = s.2.2.val ∧ s.2.1.val.length = s.2.2.val ∧
      (∀ y ∈ s.1.val, WfVec (1024 * 8) y) ∧ (∀ y ∈ s.2.1.val, WfVec (1 * 8) y) ∧
      (∀ j < s.2.2.val, toVec (k := 1024 * 8) (s.1.val.getD j (alloc.vec.Vec.new ring.Rq))
        = gadgetDecompose Φ ddBal
            (toVec (k := 1024) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))) ∧
      (∀ j < s.2.2.val, toVec (k := 1 * 8) (s.2.1.val.getD j (alloc.vec.Vec.new ring.Rq))
        = gadgetDecompose Φ ddBal (ArkLib.Lattices.matVecMul
            (toMat (rows := 1) (cols := 1024 * 8) pp.inner_matrix)
            (gadgetDecompose Φ ddBal
              (toVec (k := 1024) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))))))
  · rintro ⟨s1, t1, i1⟩ ⟨hi1, hs1, ht1, hWs1, hWt1, hvs1, hvt1⟩
    dsimp only at hi1 hs1 ht1 hWs1 hWt1 hvs1 hvt1
    simp only [commit.generate_decomps_balanced_loop.body]
    by_cases hlt : i1 < blocks
    · rw [if_pos hlt]
      have hilt : i1.val < m.val.length := by rw [hm.1, ← hb]; scalar_tac
      step as ⟨pv, hpv⟩
      have hWpv : WfVec 1024 pv := by rw [hpv]; exact hm.2 _ (List.getElem_mem hilt)
      step with balanced_gadget_decompose_spec (rows := 1024) pv hWpv (by scalar_tac)
        as ⟨s, hWs, hs⟩
      simp only [commit.PublicParams.impl.inner_matrix]
      step with mat_vec_mul_spec (rows := 1) (cols := 1024 * 8) pp.inner_matrix s
        hpp.1 hWs as ⟨inner, hWinner, hinner⟩
      step with balanced_gadget_decompose_spec (rows := 1) inner hWinner (by scalar_tac)
        as ⟨t, hWt, ht⟩
      step as ⟨t2, ht2⟩
      step as ⟨s2, hs2⟩
      step as ⟨i2, hi2⟩
      have hmi : m.val.getD i1.val (alloc.vec.Vec.new ring.Rq) = pv := by
        rw [hpv]; exact List.getD_eq_getElem _ _ hilt
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hs2, hi2, List.length_append, hs1]; simp
      · rw [ht2, hi2, List.length_append, ht1]; simp
      · intro y hy
        rw [hs2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hWs1 y h
        · rw [List.mem_singleton.mp h]; exact hWs
      · intro y hy
        rw [ht2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hWt1 y h
        · rw [List.mem_singleton.mp h]; exact hWt
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [hs2, getD_append_lt _ _ _ (by omega), hvs1 j hjlt]
        · have hjeq : j = s1.val.length := by omega
          rw [hjeq, hs2, getD_append_eq, hs, hs1, hmi]
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [ht2, getD_append_lt _ _ _ (by omega), hvt1 j hjlt]
        · have hjeq : j = t1.val.length := by omega
          rw [hjeq, ht2, getD_append_eq, ht, hinner, hs, ht1, hmi]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = 1024 := by rw [← hb] at hi1 ⊢; scalar_tac
      rw [heq] at hs1 ht1 hvs1 hvt1
      exact ⟨hs1, ht1, hWs1, hWt1, hvs1, hvt1⟩
  · exact ⟨hi, hss, hts, hWss, hWts, hvss, hvts⟩

/-- `commit::generate_decomps_balanced` — ArkLib's `generateDecomps` at
`Decomposition.ofDigits ddBal ddBal`. The unsigned twin's statement with `ddBal`
for `dd`, which is the whole of the difference on the specification side too:
`generateDecomps` takes the decomposition as a parameter. -/
theorem generate_decomps_balanced_spec (pp : commit.PublicParams)
    (m : alloc.vec.Vec linalg.PolyVec) (hpp : WfParams pp)
    (hm : m.val.length = 1024 ∧ ∀ x ∈ m.val, WfVec 1024 x) :
    commit.generate_decomps_balanced pp m
      ⦃ d => WfDecomp d ∧ toDecompSpec d
        = InnerOuter.generateDecomps Φ
            (InnerOuter.Decomposition.ofDigits Φ ddBal ddBal) (toParams pp)
            (fun i : Fin 1024 => toVec (k := 1024) (m.val.getD i.val
              (alloc.vec.Vec.new ring.Rq))) ⦄ := by
  rw [commit.generate_decomps_balanced]
  simp only [commit.Decomp.new]
  step with generate_decomps_balanced_loop_spec pp m (alloc.vec.Vec.len m)
    (alloc.vec.Vec.new linalg.PolyVec) (alloc.vec.Vec.new linalg.PolyVec) 0#usize
    hpp hm (by simpa using hm.1) (by simp) (by simp) (by simp)
    (by intro y hy; simp at hy) (by intro y hy; simp at hy)
    (by intro j hj; simp at hj) (by intro j hj; simp at hj)
    as ⟨ss, ts, hsl, htl, hWs, hWt, hvs, hvt⟩
  refine ⟨⟨⟨hsl, hWs⟩, ⟨htl, hWt⟩⟩, ?_⟩
  show (toDecompSpec ⟨ss, ts⟩ : InnerOuter.Decomp Φ 1 1024 8 1024 8) = _
  simp only [toDecompSpec, InnerOuter.generateDecomps, InnerOuter.Decomposition.ofDigits,
    InnerOuter.Decomp.mk.injEq]
  constructor
  · funext i; exact hvs i.val i.isLt
  · funext i; exact hvt i.val i.isLt

/-- **The honest Hachi commitment.** `commit::commit_balanced` is ArkLib's
`commitmentScheme.commit` at the balanced decomposition — which, composed with
`Hachi.toMatrix`, is `Hachi.commit` itself (`Commitment.lean`). This is the
statement that makes the extracted crate a translation of the *paper's*
committer rather than of the unsigned building block underneath it. -/
theorem commit_balanced_spec (pp : commit.PublicParams)
    (m : alloc.vec.Vec linalg.PolyVec) (hpp : WfParams pp)
    (hm : m.val.length = 1024 ∧ ∀ x ∈ m.val, WfVec 1024 x) :
    commit.commit_balanced pp m
      ⦃ z => WfVec 1 z.1 ∧ WfDecomp z.2 ∧
        toDecompSpec z.2 = InnerOuter.generateDecomps Φ
            (InnerOuter.Decomposition.ofDigits Φ ddBal ddBal) (toParams pp)
            (fun i : Fin 1024 => toVec (k := 1024) (m.val.getD i.val
              (alloc.vec.Vec.new ring.Rq))) ∧
        toVec (k := 1) z.1
          = InnerOuter.commitWithDecomps Φ (toParams pp) (toDecompSpec z.2) ⦄ := by
  rw [commit.commit_balanced]
  step with generate_decomps_balanced_spec pp m hpp hm as ⟨d, hWd, hdspec⟩
  step with commit_with_decomps_spec pp d hpp hWd as ⟨u, hWu, huspec⟩
  exact ⟨hWu, hWd, hdspec, huspec⟩

end HachiEquiv.Balanced
