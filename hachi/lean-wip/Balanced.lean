/-
The **balanced digit layer**: statements only, not proofs.

Staged here rather than in `lean/` because nothing below is proved yet — see
`lean-wip/README.md` for what the two directories claim and how a file is
promoted out of this one. `make build` does not look here, so the "no errors,
no `sorry`" the audited library rests on is not diluted by anything in this
file; the `sorry`s below are debt, recorded where `Check.lean` cannot see them.

## What these are about

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

## Proof notes, for whoever picks these up

`balanced_digit_at_spec` should be cheap: `balancedDigit_eq_digit` is `rfl`,
so the statement unfolds to `digit_at_spec` at the shifted argument followed by
two field steps. What it needs beyond the unsigned proof is that
`Fp::new BALANCED_SHIFT` is the specification's `balancedShift 16 8` — an `ℕ`
identity, since `BALANCED_SHIFT < q` (`lean/Check.lean` § 1 records both) — and
that the shift add is `Fp`'s, i.e. reduced. `balanced_gadget_decompose_spec`
and `generate_decomps_balanced_spec` are then the `lean/Scheme.lean` loop
scaffolds verbatim with `ddBal` for `dd`; the analytic input the unsigned side
takes from `dd_digit_natAbs_le` is upstream's `balancedZmodDigit_natAbs_le`
here, so no local copy is needed.

`bounded_z_digit_at_spec` is the one genuinely new arithmetic obligation. The
Rust computes `Int.toNat (x.valMinAbs + ⌊b/2⌋·S)` by the same two-case split
`commit::centered_abs` makes, with a third case for the clamp; the missing
lemma is that split against `ZMod.valMinAbs`, after which the digit read is
`digit_at_loop_spec` unchanged.

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

/-! ## The balanced digit layer -/

/-- `gadget::balanced_digit_at` — ArkLib's `balancedZmodDigitDecomposition.digit`
at one `e`: the unsigned digit of the **field**-shifted coefficient, less
`⌊b/2⌋`. -/
theorem balanced_digit_at_spec (c : cpoly.field.Fp) (e : Std.Usize)
    (hc : Red c) (he : e.val < 8) :
    gadget.balanced_digit_at c e
      ⦃ d => Red d ∧ toK d = ddBal.digit (toK c) ⟨e.val, he⟩ ⦄ := by
  sorry

/-- `gadget::balanced_digit_decompose` — the same at every `e < 8`, as a vector,
least-significant first. -/
theorem balanced_digit_decompose_spec (c : cpoly.field.Fp) (hc : Red c) :
    gadget.balanced_digit_decompose c
      ⦃ z => z.val.length = 8 ∧ (∀ u ∈ z.val, Red u) ∧
        ∀ e : Fin 8, coeffK z e.val = ddBal.digit (toK c) e ⦄ := by
  sorry

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
  sorry

/-- **The balanced digits are `⌊b/2⌋`-short**, unconditionally in the input —
ArkLib's `balancedZmodDigit_natAbs_le` read on the extracted digit. The
counterpart of `dd_digit_natAbs_le` for this layer, and the reason no local copy
of an upstream norm lemma is needed here: PR #847 kept the balanced bounds and
dropped only the unsigned ones. -/
theorem balanced_digit_at_natAbs_le (c : cpoly.field.Fp) (e : Std.Usize)
    (hc : Red c) (he : e.val < 8) :
    gadget.balanced_digit_at c e ⦃ d => (toK d).valMinAbs.natAbs ≤ 8 ⦄ := by
  sorry

/-! ## The bounded digit layer, for the folded witness -/

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
  sorry

/-- The bounded digits lie in the same box `[-8, 7]`, for *every* input —
ArkLib's `boundedBalancedZmodDigit_valMinAbs_mem`, which takes no shortness
hypothesis. -/
theorem bounded_z_digit_at_natAbs_le (c : cpoly.field.Fp) (e : Std.Usize)
    (hc : Red c) (he : e.val < 5) :
    gadget.bounded_z_digit_at c e ⦃ d => (toK d).valMinAbs.natAbs ≤ 8 ⦄ := by
  sorry

/-! ## The quotient digits -/

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
  sorry

/-! ## The balanced committer -/

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
  sorry

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
  sorry

end HachiEquiv.Balanced
