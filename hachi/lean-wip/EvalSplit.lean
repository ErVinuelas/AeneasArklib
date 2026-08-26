/-
# Equivalence statements for `hachi/src/evalsplit.rs` (and `linalg::split_form`)

**Statements only — every proof is `sorry`.** This file typechecks against the
pinned ArkLib specification, which is the claim staging here makes (see
`lean-wip/README.md`): each statement is well-formed at this crate's parameters
and about the specification's own definitions. Proving them is the recorded
debt of the EvalSplit onboarding, owed to the next verification campaign.

The vocabulary is `lean/Scheme.lean`'s (`Wf`/`WfVec`/`WfMat`, `toRq`/`toVec`/
`toMat`), extended with the two `Vector`-valued representation maps the
multilinear layer needs (`toVector`, and the polynomial readings `toMlPoly` /
`toMlEvals`). The split dimensions are the crate's `ML_VARS_LOW = 1`,
`ML_VARS_HIGH = 2` (`params.rs`; `2^nl = BLOCKS`, `2^nh = MESSAGE_ROWS`, the
shape `derivedMsgMatrix` fixes).

Two model-artefact hypotheses appear, in the `flatten_blocks_spec` tradition:
`two_pow` multiplies its way to `2^n`, so any statement through it carries
`2 ^ n ≤ Usize.max`; everything else is exact.
-/
import Scheme
import ArkLib.Commitments.Functional.Hachi.EvalSplit

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi
open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme

namespace HachiEquiv.EvalSplit

/-! ## The split dimensions, and the `Vector`-valued representation maps -/

/-- The low variable count `nl` (`params.ML_VARS_LOW`): rows are `2^nl = 2`. -/
abbrev nl : ℕ := 1

/-- The high variable count `nh` (`params.ML_VARS_HIGH`): columns are `2^nh = 4`. -/
abbrev nh : ℕ := 2

/-- A well-formed length-`n` vector, read as the spec's `Vector (Rq Φ) n` (the
carrier `CMlPolynomial` and the basis functions take, where `toVec` produces the
`Fin`-function `PolyVec`). -/
def toVector {n : ℕ} (v : linalg.PolyVec) : Vector (Rq Φ) n :=
  Vector.ofFn (toVec (k := n) v)

/-- An extracted `MlPoly`, read as the spec's monomial-coefficient polynomial. -/
def toMlPoly (p : evalsplit.MlPoly) : CMlPolynomial (Rq Φ) (nl + nh) :=
  toVector (n := 2 ^ (nl + nh)) p

/-- An extracted `MlEvals`, read as the spec's hypercube-value polynomial. -/
def toMlEvals (p : evalsplit.MlEvals) : CMlPolynomialEval (Rq Φ) (nl + nh) :=
  toVector (n := 2 ^ (nl + nh)) p

/-! ## Index helpers -/

/-- `two_pow` is `2 ^ n`, total up to the `usize` ceiling (the checked
multiplication is the model artefact the hypothesis discharges). -/
theorem two_pow_spec (n : Std.Usize) (hn : 2 ^ n.val ≤ Usize.max) :
    evalsplit.two_pow n ⦃ s => s.val = 2 ^ n.val ⦄ := by
  sorry

/-- `test_bit` is `Nat.testBit`, i.e. the spec's `(BitVec.ofFin i).getLsb j`.
Total unconditionally: the loop only divides. -/
theorem test_bit_spec (i j : Std.Usize) :
    evalsplit.test_bit i j ⦃ b => b = Nat.testBit i.val j.val ⦄ := by
  sorry

/-- `split_equiv` is the value of ArkLib's `splitEquiv nl nh` (`splitEquiv_val`:
`(x, y) ↦ y + 2^nl · x`). The `Fin` bounds arrive as hypotheses; totality of the
checked `+`/`*` follows from them. -/
theorem split_equiv_spec (x y : Std.Usize) (hx : x.val < 2 ^ nh) (hy : y.val < 2 ^ nl) :
    evalsplit.split_equiv x y
      ⦃ k => k.val = (Hachi.splitEquiv nl nh (⟨x.val, hx⟩, ⟨y.val, hy⟩)).val ⦄ := by
  sorry

/-- `split_equiv_inv` is `splitEquiv.symm`, componentwise. -/
theorem split_equiv_inv_spec (k : Std.Usize) (hk : k.val < 2 ^ (nl + nh)) :
    evalsplit.split_equiv_inv k
      ⦃ p => p.1.val = ((Hachi.splitEquiv nl nh).symm ⟨k.val, hk⟩).1.val
           ∧ p.2.val = ((Hachi.splitEquiv nl nh).symm ⟨k.val, hk⟩).2.val ⦄ := by
  sorry

/-! ## The bases -/

/-- `monomial_basis` computes `CMlPolynomial.monomialBasis` of the represented
point, entrywise: length `2^n`, entries reduced, and the `Fin`-function reading
equal to the spec's basis vector. Stated at every point length `n` with the
`usize` ceiling as the one model-artefact hypothesis. -/
theorem monomial_basis_spec {n : ℕ} (w : linalg.PolyVec)
    (hw : WfVec n w) (hn : 2 ^ n ≤ Usize.max) :
    evalsplit.monomial_basis w
      ⦃ z => WfVec (2 ^ n) z ∧
        toVec (k := 2 ^ n) z
          = (CMlPolynomial.monomialBasis (toVector (n := n) w)).get ⦄ := by
  sorry

/-- `lagrange_basis` computes `CMlPolynomialEval.lagrangeBasis` of the
represented point, entrywise (the multilinear equality kernel `eq̃(·, w)`). -/
theorem lagrange_basis_spec {n : ℕ} (w : linalg.PolyVec)
    (hw : WfVec n w) (hn : 2 ^ n ≤ Usize.max) :
    evalsplit.lagrange_basis w
      ⦃ z => WfVec (2 ^ n) z ∧
        toVec (k := 2 ^ n) z
          = (CMlPolynomialEval.lagrangeBasis (toVector (n := n) w)).get ⦄ := by
  sorry

/-! ## The split bilinear form (`linalg::split_form`) -/

/-- `split_form` is ArkLib's `splitForm`: `⟨u, M *ᵥ v⟩`. Generic in the shape,
like `mat_vec_mul_spec`, and total under the same well-formedness. -/
theorem split_form_spec {a b : ℕ} (m : linalg.PolyMatrix) (u v : linalg.PolyVec)
    (hm : WfMat a b m) (hu : WfVec a u) (hv : WfVec b v) :
    linalg.PolyMatrix.split_form m u v
      ⦃ z => Wf z ∧
        toRq z = ArkLib.Lattices.splitForm (toMat (rows := a) (cols := b) m)
          (toVec (k := a) u) (toVec (k := b) v) ⦄ := by
  sorry

/-! ## The reshapes -/

/-- `to_matrix` is ArkLib's `Hachi.toMatrix` at the crate's split: a
`2^nl × 2^nh` matrix whose `(i, j)` entry is coefficient `splitEquiv (j, i)`.
The length hypothesis is the `MlPoly` shape invariant (`ML_POLY_LEN = 8`),
which Aeneas cannot see across the privacy boundary. -/
theorem to_matrix_spec (p : evalsplit.MlPoly) (hp : WfVec (2 ^ (nl + nh)) p) :
    evalsplit.MlPoly.to_matrix p
      ⦃ m => WfMat (2 ^ nl) (2 ^ nh) m ∧
        toMat (rows := 2 ^ nl) (cols := 2 ^ nh) m = Hachi.toMatrix (toMlPoly p) ⦄ := by
  sorry

/-- `to_polynomial` is ArkLib's `Hachi.toPolynomial`, the inverse reshape. -/
theorem to_polynomial_spec (m : linalg.PolyMatrix) (hm : WfMat (2 ^ nl) (2 ^ nh) m) :
    evalsplit.to_polynomial m
      ⦃ p => WfVec (2 ^ (nl + nh)) p ∧
        toMlPoly p = Hachi.toPolynomial (toMat (rows := 2 ^ nl) (cols := 2 ^ nh) m) ⦄ := by
  sorry

/-- `to_matrix_eval` is ArkLib's `Hachi.toMatrixEval` — the same reshape on the
hypercube-value reading (a distinct spec definition on a distinct spec type). -/
theorem to_matrix_eval_spec (p : evalsplit.MlEvals) (hp : WfVec (2 ^ (nl + nh)) p) :
    evalsplit.MlEvals.to_matrix_eval p
      ⦃ m => WfMat (2 ^ nl) (2 ^ nh) m ∧
        toMat (rows := 2 ^ nl) (cols := 2 ^ nh) m = Hachi.toMatrixEval (toMlEvals p) ⦄ := by
  sorry

/-! ## The headline evaluations -/

/-- **Headline.** `eval_split` is ArkLib's `Hachi.evalSplit` at this crate's
split: the bilinear form of the reshaped coefficient matrix against the monomial
bases of the two point halves. Through ArkLib's `evalSplit_eq_eval` this is
`CMlPolynomial.eval (toMlPoly p) (toVector xl ++ toVector xh)` — the statement
targets the definition and inherits the evaluation reading from the
specification's own theorem. -/
theorem eval_split_spec (p : evalsplit.MlPoly) (xl xh : linalg.PolyVec)
    (hp : WfVec (2 ^ (nl + nh)) p) (hxl : WfVec nl xl) (hxh : WfVec nh xh) :
    evalsplit.MlPoly.eval_split p xl xh
      ⦃ z => Wf z ∧
        toRq z = Hachi.evalSplit (toMlPoly p) (toVector (n := nl) xl)
          (toVector (n := nh) xh) ⦄ := by
  sorry

/-- **Headline.** `eval_split_eval` is ArkLib's `Hachi.evalSplitEval` (the
Lagrange / hypercube representation), with `evalSplitEval_eq_eval` supplying the
evaluation reading. -/
theorem eval_split_eval_spec (p : evalsplit.MlEvals) (xl xh : linalg.PolyVec)
    (hp : WfVec (2 ^ (nl + nh)) p) (hxl : WfVec nl xl) (hxh : WfVec nh xh) :
    evalsplit.MlEvals.eval_split_eval p xl xh
      ⦃ z => Wf z ∧
        toRq z = Hachi.evalSplitEval (toMlEvals p) (toVector (n := nl) xl)
          (toVector (n := nh) xh) ⦄ := by
  sorry

end HachiEquiv.EvalSplit
