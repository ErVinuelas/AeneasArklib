/-
The **`Rq Φ` bridge**: the step from the coefficient-level ring layer
(`lean/Ring.lean`, proved) to ArkLib's `CyclotomicModulus.Rq Φ`.

**Proved and audited**: every theorem below is complete, this file is a root of the
`HachiEquiv` Lake library, and `lean/Check.lean` § 4 prints the axiom dependencies of
each headline spec -- the three Lean kernel axioms and nothing else.

## What is proved, and where the work was

The development is split at the coefficient level, and the split is where the work
is rather than where the statement is:

| | where | status |
|---|---|---|
| `Fp` operator impls total and equal to `ZMod q` arithmetic | `lean/Field.lean` | **proved** |
| ring operations total, length-preserving, coefficientwise correct | `lean/Ring.lean` | **proved** |
| those coefficient facts lifted to `Rq Φ` | *this file* | **proved** |

Lifting is bookkeeping, and the two lemmas that do it are `toRq_coeff` (a
coefficient of `toRq v` is the corresponding `coeffK v`, by ArkLib's
`ofFinCoeff_coeff`) and `toRq_eq_iff` (two represented elements are equal exactly
when their coefficients agree below `N`, by `Subtype.ext` and
`CPolynomial.eq_iff_coeff`). Given those, `add_spec` below is `Ring.add_spec`
plus ArkLib's `add_val` — which says the reduction in `Rq.mk` does nothing for a
sum of two reduced representatives, i.e. exactly that addition is coefficientwise
on both sides.

`mul_spec` is the one that is not bookkeeping, and it is **proved**: the coefficient-level
work is `Ring.mul_spec` (the nested loop invariants of the negacyclic convolution), and
what this file adds is `mul_two_block` -- that reducing modulo `X^N + 1` is exactly the
two-block fold with a minus sign, which is the specification's side of what the Rust does
inline. ArkLib proves that identity too, but `private`ly, inside
`NormBounds/MicciancioYoung.lean`, so it is re-proved here rather than imported.

## The one thing to check before trusting a statement here

That it is not vacuous. Each says the extracted operation *succeeds* (the triple
implies `∃ r, m = ok r`) and that its `toRq` is the ArkLib operation applied to the
`toRq`s of the inputs — a claim about behaviour, not a definition. Two of them,
`equals_spec` and `is_zero_spec`, are `↔` rather than implications for the same reason:
the rejection direction is the half a broken implementation would still satisfy, and it is
the half `Simple.verify` rests on.
-/
import Ring
import ArkLib.Commitments.Functional.Hachi.InnerOuter.Arithmetic
-- `Nat.Prime 4294967197` is decided by norm_num's primality extension, which is not
-- reached by the ArkLib import above; without this the instance below is unprovable
-- by `norm_num` and fails with a bare `⊢ Nat.Prime 4294967197`.
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open hachi
open HachiEquiv.Field HachiEquiv.Ring

namespace HachiEquiv.RqBridge

/-! ## The specification side, instantiated at this crate's parameters

`q` and `N` come from the proved layers (`Field.q`, `Ring.N`); what is added here
is the cyclotomic index and the instances ArkLib's `Rq` needs. -/

/-- The cyclotomic index `α`; the ring degree is `N = 2^α`. -/
abbrev α : ℕ := 6

instance : Fact (Nat.Prime q) := ⟨by norm_num⟩

/-- `ZMod q` needs this for `valMinAbs` (so for every centered norm) and for
`ZMod.val_lt`, which `zmodDigitDecomposition`'s reconstruction proof uses. Stated
rather than left to instance search, because a missing `NeZero` surfaces far from
its cause. -/
instance : NeZero q := ⟨by norm_num⟩

/-- `Rq` needs a lawful `BEq` on the coefficient ring (`CPolynomial`'s trimming
does), and `ZMod q` has `DecidableEq`, so the decidable-equality `BEq` serves. -/
instance : BEq (ZMod q) := instBEqOfDecidableEq

instance : LawfulBEq (ZMod q) where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

/-- The commitment ring's modulus, `φ = X^{2^α} + 1` over `ZMod q`: ArkLib's
`hachiModulus`, which is `@[reducible]`-equal to `powTwoCyclotomic α`, so the
`IsCyclotomic` instance and every `powTwoCyclotomic`-stated lemma apply. -/
abbrev Φ : CyclotomicModulus (ZMod q) := Ajtai.InnerOuter.hachiModulus q α

/-- `deg φ = N`: the equation that lets the Rust's `RING_DEGREE` and the
specification's `Φ.φ.natDegree` be used interchangeably. The same fact
`lean/Check.lean` § 3 states about `params.RING_DEGREE`. -/
@[simp] theorem phi_natDegree : Φ.φ.natDegree = N := by
  rw [Ajtai.InnerOuter.hachiModulus_natDegree]
  norm_num

/-! ## The representation map

`toRq` hands the coefficient function of a vector to ArkLib's `ofFinCoeff` at
width `N`. That is the same constructor the specification's own gadget
decomposition uses (`gadgetDecompose`, at `Φ.φ.natDegree`), which is why the gadget
layer's statements will compose with these without a translation step. -/

/-- The ArkLib ring element a coefficient vector represents. -/
def toRq (v : ring.Rq) : Rq Φ := Rq.ofFinCoeff Φ N (coeffK v)

/-- `N` does not exceed `deg φ` — with equality, in fact. The side condition of
`Rq.ofFinCoeff_coeff`, and the reason `toRq` loses nothing. -/
theorem N_le_degree : (N : WithBot ℕ) ≤ Φ.φ.toPoly.degree := by
  have h := Rq.phi_natDegree_le_degree Φ
  rwa [phi_natDegree] at h

/-- The coefficients of `toRq v`: the represented words below `N`, zero above. -/
theorem toRq_coeff (v : ring.Rq) (k : ℕ) :
    (toRq v).1.coeff k = if k < N then coeffK v k else 0 := by
  rw [toRq, Rq.ofFinCoeff_coeff Φ _ N_le_degree]

/-- Two represented elements are equal exactly when their coefficient functions
agree below `N`. The extensionality principle every spec below ends with. -/
theorem toRq_eq_iff (v w : ring.Rq) :
    toRq v = toRq w ↔ ∀ k < N, coeffK v k = coeffK w k := by
  constructor
  · intro h k hk
    have h2 : (toRq v).1.coeff k = (toRq w).1.coeff k := by rw [h]
    rw [toRq_coeff, toRq_coeff, if_pos hk, if_pos hk] at h2
    exact h2
  · intro h
    apply Subtype.ext
    rw [CompPoly.CPolynomial.eq_iff_coeff]
    intro k
    rw [toRq_coeff, toRq_coeff]
    by_cases hk : k < N
    · simp only [if_pos hk, h k hk]
    · simp only [if_neg hk]

/-! ## The modulus as a Mathlib polynomial

`mul_spec` is the only obligation that has to look inside `φ` rather than only at its
degree: `modByMonic` is a `Polynomial` operation, so the three facts below are what carry
`Φ.φ` across the `CPolynomial`/`Polynomial` boundary. -/

/-- `φ = X^N + 1` as a Mathlib polynomial. `powTwoCyclotomic_toPoly` states it at
`X^{2^α}`; the `norm_num` is what turns `2^6` into this crate's `N`. -/
theorem phi_toPoly : Φ.φ.toPoly = (Polynomial.X : Polynomial (ZMod q)) ^ N + 1 := by
  rw [show Φ.φ = (powTwoCyclotomic (R := ZMod q) α).φ from rfl,
    CyclotomicModulus.powTwoCyclotomic_toPoly]
  norm_num

/-- `deg φ = N` as a `WithBot ℕ`. The `natDegree` version is `phi_natDegree`; this is the
form the degree bounds on reduced representatives come in. -/
theorem phi_degree : Φ.φ.toPoly.degree = (N : WithBot ℕ) := by
  rw [phi_toPoly,
    show ((Polynomial.X : Polynomial (ZMod q)) ^ N + 1)
      = Polynomial.X ^ N + Polynomial.C 1 by rw [Polynomial.C_1]]
  exact Polynomial.degree_X_pow_add_C (by norm_num) 1

/-- **Negacyclic two-block coefficient identity.**  Reducing a polynomial of degree `< 2n`
modulo the monic `X^n + 1` mixes only the coefficient blocks `k` and `n + k`. -/
theorem coeff_modByMonic_X_pow_add_one {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (hn : 0 < n) (P : Polynomial R) (hP : P.natDegree < 2 * n) {k : ℕ} (hk : k < n) :
    (P %ₘ (Polynomial.X ^ n + 1)).coeff k = P.coeff k - P.coeff (n + k) := by
  classical
  open Polynomial in
  set g : Polynomial R := X ^ n + 1 with hgdef
  have hg : g.Monic := by rw [hgdef, ← C_1]; exact monic_X_pow_add_C (1 : R) hn.ne'
  have hgdeg : g.degree = (n : ℕ) := by rw [hgdef, ← C_1]; exact degree_X_pow_add_C hn 1
  have hgnd : g.natDegree = n := by rw [hgdef, ← C_1]; exact natDegree_X_pow_add_C
  set Q : Polynomial R := P /ₘ g with hQdef
  have hsum : P %ₘ g + g * Q = P := modByMonic_add_div P g
  have hQnd : Q.natDegree < n := by
    have hh : Q.natDegree = P.natDegree - n := by rw [hQdef, natDegree_divByMonic P hg, hgnd]
    omega
  have hRrlt : (P %ₘ g).degree < (n : WithBot ℕ) := by
    rw [← hgdeg]; exact degree_modByMonic_lt P hg
  have hcoeff : ∀ m : ℕ, P.coeff m
      = (P %ₘ g).coeff m + ((if n ≤ m then Q.coeff (m - n) else 0) + Q.coeff m) := by
    intro m
    have hgQ : g * Q = Q * X ^ n + Q := by rw [hgdef]; ring
    have hP' : P = (P %ₘ g) + (Q * X ^ n + Q) := by rw [← hgQ, hsum]
    conv_lhs => rw [hP']
    rw [coeff_add, coeff_add, coeff_mul_X_pow']
  have hk' : ¬ n ≤ k := by omega
  have hPk := hcoeff k
  rw [if_neg hk'] at hPk
  have hPnk := hcoeff (n + k)
  rw [if_pos (Nat.le_add_right n k)] at hPnk
  have hRr0 : (P %ₘ g).coeff (n + k) = 0 :=
    coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hRrlt (by exact_mod_cast Nat.le_add_right n k))
  have hQ0 : Q.coeff (n + k) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hQnd (Nat.le_add_right n k))
  have hsub : n + k - n = k := by omega
  rw [hsub, hRr0, hQ0] at hPnk
  rw [hPk, hPnk]; ring

/-- `CPolynomial.C 1 = 1`.  CompPoly has `coeff_C` and `coeff_one` but no `C_1`, so this
goes through extensionality. -/
theorem C_one : (CompPoly.CPolynomial.C (1 : ZMod q)) = 1 := by
  rw [CompPoly.CPolynomial.eq_iff_coeff]
  intro k
  rw [CompPoly.CPolynomial.coeff_C, CompPoly.CPolynomial.coeff_one]

/-- ArkLib has no `one_val`. `(1 : Rq Φ)` is `Rq.mk Φ 1` and `constRq Φ 1` is
`Rq.mk Φ (C 1)`; they agree only through `C_one`, which is what `one_spec` needs. -/
theorem one_eq_constRq : (1 : Rq Φ) = Rq.constRq Φ 1 := by
  rw [Rq.constRq, C_one]; rfl

/-- A vector whose coefficients below `N` are `c` at slot `0` and zero elsewhere
represents the constant `constRq Φ c`.  Both `constant_spec` and `one_spec` are this
lemma; the only work is matching the bounded `if k < N` of `toRq_coeff` against the
unbounded `if k = 0` of `coeff_C`, which is a case split on `k < N` plus `0 < N`. -/
private theorem toRq_eq_constRq {z : ring.Rq} {c : ZMod q}
    (hcoef : ∀ k, k < N → coeffK z k = if k = 0 then c else 0) :
    toRq z = Rq.constRq Φ c := by
  apply Subtype.ext
  rw [CompPoly.CPolynomial.eq_iff_coeff]
  intro k
  rw [Rq.constRq_val Φ (by rw [phi_natDegree]; norm_num),
    CompPoly.CPolynomial.coeff_C]
  by_cases hk : k < N
  · rw [toRq_coeff, if_pos hk, hcoef k hk]
  · have hN : 0 < N := by norm_num
    have hk0 : ¬ k = 0 := by omega
    rw [toRq_coeff, if_neg hk, if_neg hk0]

/-- `toRq v` is the zero of `Rq Φ` exactly when the represented coefficients below `N`
all vanish. The `is_zero` analogue of `toRq_eq_iff`: forward by reading coefficients
through `toRq_coeff`, backward by extensionality against `Rq.zero_val`. -/
private theorem toRq_eq_zero_iff (v : ring.Rq) :
    toRq v = 0 ↔ ∀ k < N, coeffK v k = 0 := by
  constructor
  · intro h k hk
    have h2 : (toRq v).1.coeff k = (0 : Rq Φ).1.coeff k := by rw [h]
    rw [toRq_coeff, if_pos hk, Rq.zero_val, CompPoly.CPolynomial.coeff_zero] at h2
    exact h2
  · intro h
    apply Subtype.ext
    rw [Rq.zero_val, CompPoly.CPolynomial.eq_iff_coeff]
    intro k
    rw [toRq_coeff, CompPoly.CPolynomial.coeff_zero]
    by_cases hk : k < N
    · rw [if_pos hk, h k hk]
    · rw [if_neg hk]

/-! ## The obligations

Each is the corresponding `lean/Ring.lean` theorem lifted to `Rq Φ`. Three shapes recur:
`toRq_eq_iff` where both sides are a `toRq` (`copy`, `from_coeffs`); `Subtype.ext` plus
`CPolynomial.eq_iff_coeff` where the right-hand side is an ArkLib operation, with
`toRq_coeff_eq_coeffK` below `N` and `Rq.coeff_eq_zero_of_natDegree_le` above it (the
arithmetic ops, and `mul`); and `Iff.trans` for the two decision procedures. -/

/-- `Rq::zero` — the zero of `Rq Φ`. From `Ring.zero_spec` plus `Rq.zero_val`. -/
theorem zero_spec : ring.Rq.zero ⦃ z => Wf z ∧ toRq z = 0 ⦄ := by
  apply spec_mono HachiEquiv.Ring.zero_spec
  rintro z ⟨hz, hcoef⟩
  refine ⟨hz, ?_⟩
  apply Subtype.ext
  rw [CompPoly.CPolynomial.eq_iff_coeff]
  intro k
  -- `Ring.zero_spec` is unguarded, so there is no `k < N` split to make: the
  -- coefficient is `0` in both branches of `toRq_coeff`, and so is that of `(0 : Rq Φ)`.
  rw [toRq_coeff, hcoef k, ite_self, Rq.zero_val, CompPoly.CPolynomial.coeff_zero]

/-- `Rq::add` — ArkLib's `Add` instance. From `Ring.add_spec` plus the spec's
`add_val`, which is what says the reduction in `Rq.mk` does nothing here. -/
theorem add_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b) :
    ring.Rq.add a b ⦃ c => Wf c ∧ toRq c = toRq a + toRq b ⦄ := by
  apply spec_mono (HachiEquiv.Ring.add_spec a b ha hb)
  rintro z ⟨hz, hcoef⟩
  refine ⟨hz, ?_⟩
  apply Subtype.ext
  rw [CompPoly.CPolynomial.eq_iff_coeff]
  intro k
  -- `add_val` says the reduction in `Rq.mk` does nothing on already-reduced
  -- representatives, so the specification side is coefficientwise too; the three
  -- `if k < N` guards of `toRq_coeff` are then the same guard, split once.
  rw [Rq.add_val, CompPoly.CPolynomial.coeff_add]
  simp only [toRq_coeff]
  split_ifs with hk
  · exact hcoef k hk
  · rw [add_zero]

/-- `Rq::sub` — coefficientwise; the specification's `sub_val`. -/
theorem sub_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b) :
    ring.Rq.sub a b ⦃ c => Wf c ∧ toRq c = toRq a - toRq b ⦄ := by
  apply spec_mono (HachiEquiv.Ring.sub_spec a b ha hb)
  rintro z ⟨hz, hcoef⟩
  refine ⟨hz, ?_⟩
  apply Subtype.ext
  rw [CompPoly.CPolynomial.eq_iff_coeff]
  intro k
  rw [Rq.sub_val, CompPoly.CPolynomial.coeff_sub]
  simp only [toRq_coeff]
  split_ifs with hk
  · exact hcoef k hk
  · rw [sub_zero]

/-- `Rq::neg` — coefficientwise; the specification's `neg_val`. -/
theorem neg_spec (a : ring.Rq) (ha : Wf a) :
    ring.Rq.neg a ⦃ c => Wf c ∧ toRq c = - toRq a ⦄ := by
  apply spec_mono (HachiEquiv.Ring.neg_spec a ha)
  rintro z ⟨hz, hcoef⟩
  refine ⟨hz, ?_⟩
  apply Subtype.ext
  rw [CompPoly.CPolynomial.eq_iff_coeff]
  intro k
  rw [Rq.neg_val, CompPoly.CPolynomial.coeff_neg]
  simp only [toRq_coeff]
  split_ifs with hk
  · exact hcoef k hk
  · rw [neg_zero]

/-- `Rq::constant` — ArkLib's `constRq`. No reduction happens on either side:
`deg (C c) = 0 < deg φ` (the spec's `constRq_val`), and the Rust puts `c` in slot
`0` and zeros elsewhere. -/
theorem constant_spec (c : cpoly.field.Fp) (hc : Red c) :
    ring.Rq.constant c ⦃ z => Wf z ∧ toRq z = Rq.constRq Φ (toK c) ⦄ := by
  apply spec_mono (HachiEquiv.Ring.constant_spec c hc)
  rintro z ⟨hz, hcoef⟩
  exact ⟨hz, toRq_eq_constRq hcoef⟩

/-- `Rq::one` — the multiplicative identity, which is `constant Fp::ONE`. -/
theorem one_spec : ring.Rq.one ⦃ z => Wf z ∧ toRq z = 1 ⦄ := by
  apply spec_mono HachiEquiv.Ring.one_spec
  rintro z ⟨hz, hcoef⟩
  refine ⟨hz, ?_⟩
  rw [one_eq_constRq]
  exact toRq_eq_constRq hcoef

/-- `Rq::from_coeffs` — ArkLib's `ofFinCoeff`, zero-padded and truncated to `N`.
Stated over an arbitrary input length, since that is what makes the Rust total. -/
theorem from_coeffs_spec (v : ring.Rq) (hv : ∀ u ∈ v.val, Red u) :
    ring.Rq.from_coeffs v ⦃ z => Wf z ∧ toRq z = Rq.ofFinCoeff Φ N (coeffK v) ⦄ := by
  apply spec_mono (HachiEquiv.Ring.from_coeffs_spec v hv)
  rintro z ⟨hz, hcoef⟩
  refine ⟨hz, ?_⟩
  show toRq z = toRq v
  rw [toRq_eq_iff]
  exact hcoef

/-- `Rq::coeff` — ArkLib's `coeffHom`. Zero at and beyond `N`, which on the
specification side is `coeff_eq_zero_of_natDegree_le` rather than a convention. -/
theorem coeff_spec (v : ring.Rq) (k : Std.Usize) (hv : Wf v) :
    ring.Rq.coeff v k ⦃ c => Red c ∧ toK c = (toRq v).1.coeff k.val ⦄ := by
  apply spec_mono (HachiEquiv.Ring.coeff_spec v k hv)
  rintro c ⟨hc, hval⟩
  refine ⟨hc, ?_⟩
  -- `toRq_coeff_eq_coeffK` is stated further down the file, so its one-line proof is
  -- repeated here: below `N` the `if` fires, and at or above it `Wf v` makes both sides `0`.
  rw [hval, toRq_coeff]
  by_cases hk : k.val < N
  · rw [if_pos hk]
  · rw [if_neg hk, coeffK_of_ge (by rw [hv.1]; exact Nat.le_of_not_lt hk)]

/-- `Rq::scalar_mul` — multiplication by a constant. The specification has no
primitive for this: the corresponding operation is `constRq c * x`, whose
coefficientwise action is `constRq_mul_coeff`. Stating it in that form is what lets
the gadget layer use it where the spec writes
`Rq.constRq Φ (base ^ e) * v j`. -/
theorem scalar_mul_spec (a : ring.Rq) (c : cpoly.field.Fp) (ha : Wf a) (hc : Red c) :
    ring.Rq.scalar_mul a c ⦃ z => Wf z ∧ toRq z = Rq.constRq Φ (toK c) * toRq a ⦄ := by
  apply spec_mono (HachiEquiv.Ring.scalar_mul_spec a c ha hc)
  rintro z ⟨hz, hcoef⟩
  refine ⟨hz, ?_⟩
  apply Subtype.ext
  rw [CompPoly.CPolynomial.eq_iff_coeff]
  intro k
  by_cases hk : k < N
  · rw [toRq_coeff, if_pos hk, hcoef k hk,
      Rq.constRq_mul_coeff Φ (by rw [phi_natDegree]; norm_num),
      toRq_coeff, if_pos hk]
  · rw [toRq_coeff, if_neg hk]
    exact (Rq.coeff_eq_zero_of_natDegree_le Φ _ (by rw [phi_natDegree]; omega)).symm

/-- `Rq::equals` — decides equality of two represented elements.

An `↔`, not an implication: `Simple.verify` is `decide (commit Φ A s = c)`, so this
is the operation the verifier's equality check corresponds to, and a one-way
implication would be satisfied by an `equals` that always answered `false`. -/
theorem equals_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b) :
    ring.Rq.equals a b ⦃ r => r = true ↔ toRq a = toRq b ⦄ := by
  -- Not a weakening but a transport: the coefficient-level `↔` composed with the
  -- extensionality `↔`, both read left to right.
  apply spec_mono (HachiEquiv.Ring.equals_spec a b ha hb)
  intro r hr
  exact hr.trans (toRq_eq_iff a b).symm

/-- `Rq::is_zero`. -/
theorem is_zero_spec (a : ring.Rq) (ha : Wf a) :
    ring.Rq.is_zero a ⦃ r => r = true ↔ toRq a = 0 ⦄ := by
  apply spec_mono (HachiEquiv.Ring.is_zero_spec a ha)
  intro r hr
  exact hr.trans (toRq_eq_zero_iff a).symm

/-- `Rq::copy`. -/
theorem copy_spec (a : ring.Rq) (ha : Wf a) :
    ring.Rq.copy a ⦃ z => Wf z ∧ toRq z = toRq a ⦄ := by
  apply spec_mono (HachiEquiv.Ring.copy_spec a ha)
  rintro z ⟨hz, hcoef⟩
  exact ⟨hz, (toRq_eq_iff z a).2 hcoef⟩

/-- The product of two reduced representatives, coefficientwise: the raw `CPolynomial`
product folded at `N` with a minus sign. This is the specification side of the sign the
Rust folds in as it goes -- a public re-proof of ArkLib's `coeff_mul_rq_two_block`, which
is `private` to `NormBounds/MicciancioYoung.lean` and so cannot be imported. -/
theorem mul_two_block (x y : Rq Φ) {k : ℕ} (hk : k < N) :
    (x * y).1.coeff k
      = (x.1.toPoly * y.1.toPoly).coeff k - (x.1.toPoly * y.1.toPoly).coeff (N + k) := by
  have hN : 0 < N := by norm_num
  have hnd : ∀ z : Rq Φ, z.1.toPoly.natDegree < N := by
    intro z
    by_cases h : z.1.toPoly = 0
    · rw [h, Polynomial.natDegree_zero]; exact hN
    · rw [Polynomial.natDegree_lt_iff_degree_lt h]
      calc z.1.toPoly.degree < Φ.φ.toPoly.degree := Φ.degree_toPoly_lt_of_reduced z.2
        _ = (N : WithBot ℕ) := phi_degree
  have hmul : (x * y).1 = Φ.reduce (x.1 * y.1) := rfl
  rw [hmul, CompPoly.CPolynomial.coeff_toPoly, Φ.reduce_toPoly,
    CompPoly.CPolynomial.toPoly_mul, phi_toPoly]
  refine coeff_modByMonic_X_pow_add_one hN _ ?_ hk
  calc (x.1.toPoly * y.1.toPoly).natDegree
      ≤ x.1.toPoly.natDegree + y.1.toPoly.natDegree := Polynomial.natDegree_mul_le
    _ < 2 * N := by have := hnd x; have := hnd y; omega

/-- For a well-formed vector the `if k < N` in `toRq_coeff` is vacuous: past the end the
vector reads `0` and so does `coeffK`, so the represented polynomial agrees with `coeffK`
at *every* index. -/
theorem toRq_coeff_eq_coeffK {v : ring.Rq} (hv : Wf v) (m : ℕ) :
    (toRq v).1.coeff m = coeffK v m := by
  rw [toRq_coeff]
  by_cases hm : m < N
  · rw [if_pos hm]
  · rw [if_neg hm, coeffK_of_ge (by rw [hv.1]; exact Nat.le_of_not_lt hm)]

/-- Coefficient `k` of the specification's product of two represented vectors is the
coefficient-level `negConv`: the step that closes the gap between the spec's `modByMonic`
and the Rust's wraparound. -/
theorem coeff_toRq_mul (a b : ring.Rq) (ha : Wf a) (hb : Wf b) {k : ℕ} (hk : k < N) :
    (toRq a * toRq b).1.coeff k = negConv a b k := by
  -- The two-block identity turns the `Rq` product into a difference of two raw
  -- `Polynomial` coefficients, and `Polynomial.coeff_mul` turns each into an
  -- antidiagonal sum — which is exactly the shape of `negConv`.
  have hsum : ∀ m : ℕ,
      (∑ p ∈ Finset.antidiagonal m,
        (toRq a).1.toPoly.coeff p.1 * (toRq b).1.toPoly.coeff p.2)
      = ∑ p ∈ Finset.antidiagonal m, coeffK a p.1 * coeffK b p.2 := by
    intro m
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← CPolynomial.coeff_toPoly, ← CPolynomial.coeff_toPoly,
      toRq_coeff_eq_coeffK ha, toRq_coeff_eq_coeffK hb]
  rw [mul_two_block _ _ hk, Polynomial.coeff_mul, Polynomial.coeff_mul, hsum, hsum, negConv]

/-- `Rq::mul` -- **the substantial one.** The Rust is a schoolbook convolution that folds
the wraparound in as it goes: the term `aᵢbⱼ` is *added* into slot `i + j` when that is
below `N` and *subtracted* from slot `i + j - N` otherwise. The specification's `Mul` is
`Rq.mk Φ (a.val * b.val)`, i.e. the raw `CPolynomial` product followed by `modByMonic`
against `X^N + 1`.

The three steps are the three lemmas it rests on. `Ring.mul_spec` is the work: the nested
loop invariants, and the coefficientwise closed form `negConv`. `mul_two_block` is the
specification side of the same fold -- that reducing modulo `X^N + 1` subtracts the block
at `N + k` from the block at `k`, and nothing else. `coeff_toRq_mul` is the two meeting,
through `Polynomial.coeff_mul`. What is left here is extensionality:
`CPolynomial.eq_iff_coeff` below `N`, and `Rq.coeff_eq_zero_of_natDegree_le` above it. -/
theorem mul_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b) :
    ring.Rq.mul a b ⦃ c => Wf c ∧ toRq c = toRq a * toRq b ⦄ := by
  apply spec_mono (HachiEquiv.Ring.mul_spec a b ha hb)
  rintro z ⟨hz, hcoef⟩
  refine ⟨hz, ?_⟩
  apply Subtype.ext
  rw [CompPoly.CPolynomial.eq_iff_coeff]
  intro k
  by_cases hk : k < N
  · rw [toRq_coeff, if_pos hk, hcoef k hk, coeff_toRq_mul a b ha hb hk]
  · rw [toRq_coeff, if_neg hk]
    exact (Rq.coeff_eq_zero_of_natDegree_le Φ _ (by rw [phi_natDegree]; omega)).symm

end HachiEquiv.RqBridge
