/-
`OptRingShort.lean` -- the algebra of multiplication by a short element
(candidate T17 change 1): `HachiEquiv.Opt.MulShort`, stated between pure functions
against `Ring.negConv`. The word level of the same loops is `RingShort.lean`.

Every `Foo.opt` here is a pure Lean definition in the shape `lean-to-rust`
translates trivially (one fold = one `while` loop, explicit tuple state,
ascending indices), named after the **Rust item** it replaces, and paired in the
same change with a proved `opt_eq_spec` lemma against the ArkLib definition that
item mirrors. The lemma is stated between pure functions: at candidate time no
Rust exists, so the algebra is settled here and the Aeneas triple over the
extracted model (the outer verification pass) only has to route through it.
`Check.lean` § 4 prints the axioms of every lemma below, which is what makes a
`sorry` here a build failure rather than silent debt (`lean-opt` § "The
opt-contract"). Every part keeps `namespace HachiEquiv.Opt`, so a lemma's
fully qualified name is the same whichever file it lives in; `Opt.lean` imports
all the parts, and `import Opt` still brings the whole layer.
-/
import RingShort

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.Opt

open HachiEquiv.Field HachiEquiv.Ring

/-! ## Candidate T17 Change 1 -- `ring::mul_short_desc`, for `quadeval::honest_z`

Multiplication by a short element.

A protocol challenge is `ShortChallenge Φ ω`, so its centred `ℓ₁` norm is at
most `params::OMEGA = 16`. `honest_z` multiplies by such an element
`blocks · MESSAGE_ROWS · GADGET_DIGITS` times, and the frozen translation sends
every one of those through the full auxiliary-prime transform. A short element
needs no transform at all: it is a handful of signed monomials, and multiplying
by a monomial is a shift.

**What is settled here, and what is not.** The algebra below is the identity
`(Σ_t ε_t m_t X^{j_t}) · s = Σ_t (the shifted, sign-folded s)` read
coefficientwise, against `Ring.negConv` -- the *same* right-hand side
`Ring.mul_spec` proves, so the optimization is checked against the
specification and not against the other implementation. Two things are
deliberately **not** here, because they are properties of the extracted Rust
rather than of the algebra:

* that `classify_short a` returns a description denoting `a` (its `descCoeff`
  is `coeffK a`) -- an obligation on the classification loop;
* that the `pass` loop's `m_t` repeated additions realize the factor `m_t` --
  `passLoop_eq` below is the algebra for it, and the loop invariant that uses
  it belongs to the extracted spec.

Note what is **not** a hypothesis anywhere below: the `ℓ₁` budget. The identity
holds for every `a`, so the budget cannot be a source of unsoundness -- failing
it only costs the generic path. Nor is distinctness of the described indices
needed: `descCoeff` sums duplicate indices and the shift-sum sums their
contributions, and both are additive in exactly the same way. -/

namespace MulShort

open HachiEquiv.RingShort

/-- A described term: the coefficient index, the centred magnitude, and the sign
(`true` = the centred coefficient is negative). Mirrors one slot of the Rust
`ShortMul`'s three parallel vectors. -/
abbrev Term : Type := ℕ × ℕ × Bool

/-- The centred coefficient a term denotes. -/
def termVal (t : Term) : ZMod q :=
  if t.2.2 then -((t.2.1 : ℕ) : ZMod q) else ((t.2.1 : ℕ) : ZMod q)

/-- The coefficient function of a whole description: the sum of its monomials. -/
def descCoeff (d : List Term) : ℕ → ZMod q :=
  fun i => (d.map (fun t => single t.1 (termVal t) i)).sum

/-- `mul_short_desc`, coefficientwise: one shifted, signed pass per term. -/
def opt (s : ℕ → ZMod q) (d : List Term) (k : ℕ) : ZMod q :=
  (d.map (fun t => contrib s t.1 (termVal t) k)).sum

/-! ### The algebra -/

theorem descCoeff_cons (t : Term) (d : List Term) (i : ℕ) :
    descCoeff (t :: d) i = single t.1 (termVal t) i + descCoeff d i := by
  unfold descCoeff; simp

/-- **`opt_eq_spec`, the pure form.** The shift-sum over a description equals
`negConvF` against the element that description denotes. Induction on the
description, monomial by monomial. -/
theorem opt_eq_negConvF (s : ℕ → ZMod q) (d : List Term) (k : ℕ)
    (hk : k < N) (hidx : ∀ t ∈ d, t.1 < N) (hs : ∀ i, N ≤ i → s i = 0) :
    opt s d k = negConvF (descCoeff d) s k := by
  induction d with
  | nil =>
    unfold opt descCoeff
    simp only [List.map_nil, List.sum_nil]
    exact (negConvF_zero_left s k).symm
  | cons t rest ih =>
    have hfun : descCoeff (t :: rest) = fun i => single t.1 (termVal t) i + descCoeff rest i :=
      funext (descCoeff_cons t rest)
    rw [hfun, negConvF_add_left,
      negConvF_single t.1 (termVal t) s k (hidx t (by simp)) hk hs,
      ← ih (fun u hu => hidx u (by simp [hu]))]
    unfold opt
    simp

/-- **The headline.** Against a well-formed `s` and a description denoting `a`,
the shift-sum is `negConv a s` -- the identical right-hand side of
`Ring.mul_spec`, so `honest_z`'s specification does not move. -/
theorem opt_eq_spec (a s : ring.Rq) (d : List Term) (k : ℕ)
    (hs : Wf s) (hk : k < N) (hidx : ∀ t ∈ d, t.1 < N)
    (hden : ∀ i, descCoeff d i = coeffK a i) :
    opt (coeffK s) d k = negConv a s k := by
  rw [← negConvF_coeffK,
    opt_eq_negConvF (coeffK s) d k hk hidx
      (fun i hi => coeffK_of_ge (by rw [hs.1]; exact hi))]
  exact congrArg (fun f => negConvF f (coeffK s) k) (funext hden)

/-! ### The `pass` loop

`mul_short_desc` never multiplies: it adds the shifted operand `m` times. That
is the one place the Rust is *not* this model, and this is the algebra the
extracted loop invariant needs. -/

/-- `m` repeated additions of `x`. -/
def passLoop (m : ℕ) (x acc : ZMod q) : ZMod q :=
  (List.range m).foldl (fun s _ => s + x) acc

theorem passLoop_eq (m : ℕ) (x acc : ZMod q) :
    passLoop m x acc = acc + (m : ZMod q) * x := by
  unfold passLoop
  induction m with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    push_cast
    ring

end MulShort

end HachiEquiv.Opt
