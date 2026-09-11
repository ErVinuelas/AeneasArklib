/-
The honest lift prover (`RingSwitch/ComputableWitness.lean`): **statements only**.

Five obligations for the chain's last untranslated item: `honestLiftWitnessC`,
its row quotient `cQuotient`, the unreduced row sum `cRowSum`, and the two
private helpers they are built from -- the product in `Zq[X]` and the division
by the modulus. The headline is `honest_lift_witness_spec`, against
`honestLiftWitnessC` through `RepLiftedWitness`; everything below it is the
loop and helper decomposition the proof will want.

# The one new carrier

`cRowSum` is a `CPolynomial (ZMod q)` of degree up to `2N − 2`, the first
polynomial in this crate that is *not* folded back into `Rq`. The Rust carries
it as a `Vec<Fp>` of exactly `2N − 1` words, the `Raw` array reading; the
representation function `toCPolyK` is `CPolynomial.ofArray` of the word map --
trim on the specification side -- the same move `Sumcheck.lean`'s `toUni`
makes for the extension field, at the base field and with the length as a
separate invariant (`WfWords`).

# Hypotheses

The `Fin`-typed indices of the specification erased to `Vec` lengths:
`RepRlin s rs` (matrix `n × μ`, right-hand side `n`), `WfVec μ z`, `i < n`,
`p.val.length = 2N − 1` for the division. `hd : 0 < Φ.φ.natDegree` is the
specification's own argument to `honestLiftWitnessC` and holds at `N = 1024`
(`phi_natDegree`); it is taken as a hypothesis so the statement is the generic
ArkLib one, exactly as `h_alpha_spec` takes it.

It imports only promoted files, so it needs no `LEAN_PATH` detour.
-/
import ZeroCheck
import CompPoly.Univariate.Raw.Division

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.LiftProver

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme
open HachiEquiv.RingSwitch HachiEquiv.ZeroCheck

/-! ## The carrier -/

/-- Every word of a coefficient vector is reduced, and there are exactly `k`
of them. -/
def WfWords (k : ℕ) (v : alloc.vec.Vec cpoly.field.Fp) : Prop :=
  v.val.length = k ∧ ∀ x ∈ v.val, Red x

/-- The base-field polynomial a word vector represents: the canonical
`CPolynomial` of its coefficient array (`ofArray` trims). -/
def toCPolyK (v : alloc.vec.Vec cpoly.field.Fp) : CPolynomial (ZMod q) :=
  CPolynomial.ofArray ((v.val.map toK).toArray)

/-! ## The helpers -/

/-- `long_mul` is the product of the two canonical representatives in `Zq[X]`
(spec: the `*` of `CPolynomial (ZMod q)` inside `cRowSum`). Exactly `2N − 1`
words. -/
theorem long_mul_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b) :
    ringswitch.long_mul a b
      ⦃ out => WfWords (2 * N - 1) out ∧ toCPolyK out = (toRq a).1 * (toRq b).1 ⦄ := by
  sorry

/-- `div_by_modulus` is `CPolynomial.divByMonic` at the modulus, on a word
vector of exactly `2N − 1` coefficients. Exactly `N` words come back, and the
quotient's degree is below `N − 1` (its top word is zero), which is what lets
`QuotientRow::new` hold it. -/
theorem div_by_modulus_spec (p : alloc.vec.Vec cpoly.field.Fp) (hp : WfWords (2 * N - 1) p) :
    ringswitch.div_by_modulus p
      ⦃ out => WfWords N out ∧ toCPolyK out = (toCPolyK p).divByMonic Φ.φ ⦄ := by
  sorry

/-! ## The three ArkLib definitions -/

/-- `c_row_sum` computes `cRowSum` (`RingSwitch/Reduction.lean:439`): the
`i`-th lifted row, unreduced. -/
theorem c_row_sum_spec {n μ : ℕ} (s : ringswitch.RlinStatement) (z : linalg.PolyVec)
    (i : Std.Usize) (rs : InnerOuter.RlinStatement Φ n μ)
    (hs : RepRlin (n := n) (μ := μ) s rs) (hz : WfVec μ z) (hi : i.val < n) :
    ringswitch.c_row_sum s z i
      ⦃ out => WfWords (2 * N - 1) out ∧
        toCPolyK out = InnerOuter.cRowSum Φ rs (toVec (k := μ) z) ⟨i.val, hi⟩ ⦄ := by
  sorry

/-- `c_quotient` computes `cQuotient` (`RingSwitch/ComputableWitness.lean:65`):
the row defect divided by the modulus, as a quotient row. -/
theorem c_quotient_spec {n μ : ℕ} (s : ringswitch.RlinStatement) (z : linalg.PolyVec)
    (i : Std.Usize) (rs : InnerOuter.RlinStatement Φ n μ)
    (hs : RepRlin (n := n) (μ := μ) s rs) (hz : WfVec μ z) (hi : i.val < n) :
    ringswitch.c_quotient s z i
      ⦃ out => Wf out ∧ toQuotientRow out = InnerOuter.cQuotient Φ rs (toVec (k := μ) z) ⟨i.val, hi⟩ ⦄ := by
  sorry

/-- `honest_lift_witness` computes `honestLiftWitnessC`
(`RingSwitch/ComputableWitness.lean:89`): `z` itself and the row quotients. The
specification's `hd` is taken as the hypothesis it is there; `hρ` is a `Prop`
and is carried by the relation's `toRho`. -/
theorem honest_lift_witness_spec {n μ : ℕ} (s : ringswitch.RlinStatement) (z : linalg.PolyVec)
    (rs : InnerOuter.RlinStatement Φ n μ) (hd : 0 < Φ.φ.natDegree)
    (hs : RepRlin (n := n) (μ := μ) s rs) (hz : WfVec μ z) :
    ringswitch.honest_lift_witness s z
      ⦃ out => RepLiftedWitness (μ := μ) (n := n) out
        (InnerOuter.honestLiftWitnessC Φ hd rs (toVec (k := μ) z)) ⦄ := by
  sorry

end HachiEquiv.LiftProver
