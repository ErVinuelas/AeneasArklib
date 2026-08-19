/-
The **`Rq Φ` bridge**: what remains between the coefficient-level ring layer
(`lean/Ring.lean`, proved) and ArkLib's `CyclotomicModulus.Rq Φ`.

Unchecked. See `lean-wip/README.md` for why this file is outside the audited
library and what has to happen before it moves into `lean/`.

## What is already proved, and what is left

The development is split at the coefficient level, and the split is where the work
is rather than where the statement is:

| | where | status |
|---|---|---|
| `Fp` operator impls total and equal to `ZMod q` arithmetic | `lean/Field.lean` | **proved** |
| ring operations total, length-preserving, coefficientwise correct | `lean/Ring.lean` | **partly proved** (`zero`, `add`) |
| those coefficient facts lifted to `Rq Φ` | *this file* | stated |

Lifting is bookkeeping, and the two lemmas that do it are `toRq_coeff` (a
coefficient of `toRq v` is the corresponding `coeffK v`, by ArkLib's
`ofFinCoeff_coeff`) and `toRq_eq_iff` (two represented elements are equal exactly
when their coefficients agree below `N`, by `Subtype.ext` and
`CPolynomial.eq_iff_coeff`). Given those, `add_spec` below is `Ring.add_spec`
plus ArkLib's `add_val` — which says the reduction in `Rq.mk` does nothing for a
sum of two reduced representatives, i.e. exactly that addition is coefficientwise
on both sides.

`mul_spec` is the one that is not bookkeeping; its proof plan is at the bottom.

## The one thing to check before trusting a statement here

That it is not vacuous. Each says the extracted operation *succeeds* (the triple
implies `∃ r, m = ok r`) and that its `toRq` is the ArkLib operation applied to the
`toRq`s of the inputs — so a `sorry`'d theorem here is a claim about behaviour, not
a definition, and filling the proof cannot change what it claims.
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

/-! ## The obligations

Each is the corresponding `lean/Ring.lean` theorem lifted through `toRq_eq_iff`,
except `mul_spec`. -/

/-- `Rq::zero` — the zero of `Rq Φ`. From `Ring.zero_spec` plus `Rq.zero_val`. -/
theorem zero_spec : ring.Rq.zero ⦃ z => Wf z ∧ toRq z = 0 ⦄ := by
  sorry

/-- `Rq::add` — ArkLib's `Add` instance. From `Ring.add_spec` plus the spec's
`add_val`, which is what says the reduction in `Rq.mk` does nothing here. -/
theorem add_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b) :
    ring.Rq.add a b ⦃ c => Wf c ∧ toRq c = toRq a + toRq b ⦄ := by
  sorry

/-- `Rq::sub` — coefficientwise; the specification's `sub_val`. -/
theorem sub_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b) :
    ring.Rq.sub a b ⦃ c => Wf c ∧ toRq c = toRq a - toRq b ⦄ := by
  sorry

/-- `Rq::neg` — coefficientwise; the specification's `neg_val`. -/
theorem neg_spec (a : ring.Rq) (ha : Wf a) :
    ring.Rq.neg a ⦃ c => Wf c ∧ toRq c = - toRq a ⦄ := by
  sorry

/-- `Rq::constant` — ArkLib's `constRq`. No reduction happens on either side:
`deg (C c) = 0 < deg φ` (the spec's `constRq_val`), and the Rust puts `c` in slot
`0` and zeros elsewhere. -/
theorem constant_spec (c : cpoly.field.Fp) (hc : Red c) :
    ring.Rq.constant c ⦃ z => Wf z ∧ toRq z = Rq.constRq Φ (toK c) ⦄ := by
  sorry

/-- `Rq::one` — the multiplicative identity, which is `constant Fp::ONE`. -/
theorem one_spec : ring.Rq.one ⦃ z => Wf z ∧ toRq z = 1 ⦄ := by
  sorry

/-- `Rq::from_coeffs` — ArkLib's `ofFinCoeff`, zero-padded and truncated to `N`.
Stated over an arbitrary input length, since that is what makes the Rust total. -/
theorem from_coeffs_spec (v : ring.Rq) (hv : ∀ u ∈ v.val, Red u) :
    ring.Rq.from_coeffs v ⦃ z => Wf z ∧ toRq z = Rq.ofFinCoeff Φ N (coeffK v) ⦄ := by
  sorry

/-- `Rq::coeff` — ArkLib's `coeffHom`. Zero at and beyond `N`, which on the
specification side is `coeff_eq_zero_of_natDegree_le` rather than a convention. -/
theorem coeff_spec (v : ring.Rq) (k : Std.Usize) (hv : Wf v) :
    ring.Rq.coeff v k ⦃ c => Red c ∧ toK c = (toRq v).1.coeff k.val ⦄ := by
  sorry

/-- `Rq::scalar_mul` — multiplication by a constant. The specification has no
primitive for this: the corresponding operation is `constRq c * x`, whose
coefficientwise action is `constRq_mul_coeff`. Stating it in that form is what lets
the gadget layer use it where the spec writes
`Rq.constRq Φ (base ^ e) * v j`. -/
theorem scalar_mul_spec (a : ring.Rq) (c : cpoly.field.Fp) (ha : Wf a) (hc : Red c) :
    ring.Rq.scalar_mul a c ⦃ z => Wf z ∧ toRq z = Rq.constRq Φ (toK c) * toRq a ⦄ := by
  sorry

/-- `Rq::equals` — decides equality of two represented elements.

An `↔`, not an implication: `Simple.verify` is `decide (commit Φ A s = c)`, so this
is the operation the verifier's equality check corresponds to, and a one-way
implication would be satisfied by an `equals` that always answered `false`. -/
theorem equals_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b) :
    ring.Rq.equals a b ⦃ r => r = true ↔ toRq a = toRq b ⦄ := by
  sorry

/-- `Rq::is_zero`. -/
theorem is_zero_spec (a : ring.Rq) (ha : Wf a) :
    ring.Rq.is_zero a ⦃ r => r = true ↔ toRq a = 0 ⦄ := by
  sorry

/-- `Rq::copy`. -/
theorem copy_spec (a : ring.Rq) (ha : Wf a) :
    ring.Rq.copy a ⦃ z => Wf z ∧ toRq z = toRq a ⦄ := by
  sorry

/-- `Rq::mul` — **the substantial one.** The Rust is a schoolbook convolution that
folds the wraparound in as it goes: the term `aᵢbⱼ` is *added* into slot `i + j`
when that is below `N` and *subtracted* from slot `i + j - N` otherwise. The
specification's `Mul` is `Rq.mk Φ (a.val * b.val)`, i.e. the raw `CPolynomial`
product followed by `modByMonic` against `X^N + 1`.

Proof plan, for whoever finishes it. Three steps, and only the middle one is work:

1. **The loops.** Two nested `loop.spec_decr_nat`s, as in `lean/Ring.lean`'s
   `add_loop_spec` but with the accumulator threaded through `index_mut` rather
   than `push`. The inner invariant is the partial convolution: after `j`
   iterations of the pass for row `i`, slot `k` holds
   `Σ_{i' < i, j' < N} ± aᵢ'bⱼ' + Σ_{j' < j} ± aᵢbⱼ'`, the sign being negative
   exactly when `i' + j' ≥ N`. Totality is `Field.fp_add_spec` /
   `fp_sub_spec` / `fp_mul_spec` at every step, plus `i + j < 2N` not overflowing
   `Usize`, which `scalar_tac` gets from the loop bounds.
2. **The closed form.** The result satisfies
   `coeffK c k = Σ_{i+j=k} aᵢbⱼ - Σ_{i+j=k+N} aᵢbⱼ`, and what has to be shown is
   that this is the `k`-th coefficient of `(a * b) %ₘ (X^N + 1)`. The way in is
   `Rq.lean`'s `reduce_toPoly` (reduction *is* `%ₘ`) plus `X^N ≡ -1`; ArkLib's
   `Subfield/Basis.lean` has the power-of-two coefficient machinery.
3. **The lift**, exactly as for `add_spec`: `toRq_eq_iff` and `Rq.mk_mul`. -/
theorem mul_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b) :
    ring.Rq.mul a b ⦃ c => Wf c ∧ toRq c = toRq a * toRq b ⦄ := by
  sorry

end HachiEquiv.RqBridge
