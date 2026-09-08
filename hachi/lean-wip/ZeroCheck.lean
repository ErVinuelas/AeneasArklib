/-
Target 4's zero-check link: **statements only**.

Twenty obligations, none proved here. Target 6's end piece is a separate file,
`EndPiece.lean`, which imports this one -- one file per module, as `lean/` has. They sit on `lean-wip/Ext.lean`'s
extension-field layer, which is why this file is staged rather than promoted:
`Ext.lean` still carries the eight ported `Ext4` arithmetic specs, and a wip
file importing another wip file needs the `LEAN_PATH` detour of
`lean-wip/README.md` § "Working here".

# The two conventions this file follows, both deliberate

**The computable side, on both polynomials.** `ZeroCheck/Constraints.lean` has
four `noncomputable def`s and they are two different kinds: `hZeroML` (`:255`)
and `hAlphaML` (`:261`) are *Mathlib views* (`MLE` inside
`MvPolynomial.restrictDegree`, "used only in algebraic proofs"), while
`hAlphaEvals` (`:176`) and `hAlpha` (`:213`) are the α table itself. Every
statement below is against a **computable** ArkLib definition: `hZero`,
`wTable`, `rangeProduct`, `cWTableMle`, `wTableMleEval` are plain `def`s
already, and the α side goes through `alphaDefect` (`:549`), which
`hAlphaEvals_eq_alphaDefect` (`:771`) proves equal to the noncomputable form.
So `h_alpha_evals_spec` below is stated against `alphaDefect` and the bridge to
`hAlphaEvals` is a *separate* statement (`h_alpha_evals_eq_hAlphaEvals`) rather
than a hypothesis -- nothing is assumed, and the `…ML` views are never touched.
That also means `cRowSum` -- whose unreduced product would need a
2047-coefficient carrier this crate does not have -- appears nowhere.

**Arities travel as arguments.** `m₀`, `m₁`, `μ` and `n` are function arguments
or read off the data, never `params` constants, so each statement below is the
*generic* ArkLib statement at an arbitrary width rather than an instantiation at
`M_ZERO = 26`. That is strictly stronger, and it is also what makes the
operations testable at all (NOTES.md § "Target 4 opens").

# The one hypothesis class that is real here

`w_table` and `alpha_contract` form `d·u + ℓ` as a **checked `usize` product**,
so their statements carry a bound. Unlike the flat index that was removed from
`rho_digits_short_check` (NOTES.md § "The flat index the specification does not
have"), this product **is in the specification**: `wTablePoint` (`:525`) is
literally `d·u + ℓ` carrying a proof that it lands in the cube, and its side
condition is ArkLib's own `hμn`, now pinned by `sumcheckWidthAtProfile`. The
triage rule that distinguishes the two cases: ask whether the *specification*
forms the product.
-/

import RingSwitch
import Ext
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Constraints
import ArkLib.Commitments.Functional.Hachi.EndPiece.Reduction

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly CompPoly.Extension CompPoly.Extension.Ext ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.ZeroCheck

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme
open HachiEquiv.RingSwitch HachiEquiv.Ext

/-! ## The representation layer

`Ext.lean` supplies `toExt`, `Reduced` and `VecReduced` for one extension
element and for a vector of them. What this file adds is the three carriers the
zero-check layer introduces: the ring map `φF` that every ArkLib definition
here takes, an evaluation point, and a Lagrange-form table. -/

/-- The ring map `φF : ZMod q →+* F` that `wTable`, `hZero`, `mAlphaTilde` and
`cEvalAt` are all parameterised by: the base-field embedding into the quartic
extension, bundled by CompPoly as `ofBaseRingHom`
(`CompPoly/Fields/Extension/Bridge.lean:354`).

It is *the* embedding and not a choice: `ext_from_base_spec` (`Ext.lean`) says
the extracted `Ext4::from_base` computes `Ext.ofBase`, and `from_base` is what
every `φF`-image in `hachi/src/zerocheck.rs` goes through. -/
def phiF : ZMod q →+* F := Ext.ofBaseRingHom Hachi.ext4Params.toExtensionParams

/-- An extracted `Vec Ext4` read as an evaluation point `Fin m → F`. -/
def toPoint {m : ℕ} (a : alloc.vec.Vec cpoly.field.Ext4) : Fin m → F :=
  fun j => toExt (a.val.getD j.val cpoly.field.Ext4.ZERO)

/-- Well-formedness of a point: the length is the arity, and every coefficient
is a reduced word. -/
def WfPoint (m : ℕ) (a : alloc.vec.Vec cpoly.field.Ext4) : Prop :=
  a.val.length = m ∧ VecReduced a

/-- A `MultilinearEvals` read as ArkLib's `CMlPolynomialEval F m`, which is
`Vector F (2 ^ m)` (`CompPoly/Multilinear/Basic.lean:47`). -/
def toEvals {m : ℕ} (t : cpoly.multilinear.MultilinearEvals) : CMlPolynomialEval F m :=
  Vector.ofFn (fun i : Fin (2 ^ m) => toExt (t.val.getD i.val cpoly.field.Ext4.ZERO))

/-- Well-formedness of a Lagrange-form table: `2 ^ m` reduced entries. -/
def WfEvals (m : ℕ) (t : cpoly.multilinear.MultilinearEvals) : Prop :=
  t.val.length = 2 ^ m ∧ VecReduced t

/-- Relation between the extracted `R^lin` statement and ArkLib's. The bound is
a `u64` against the specification's `ℕ`, as `params::CHAIN_GAMMA` is. -/
def RepRlin {n μ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) : Prop :=
  WfMat n μ s.m ∧ WfVec n s.yvec ∧
    toMat (rows := n) (cols := μ) s.m = rs.M ∧
    toVec (k := n) s.yvec = rs.yvec ∧
    s.bound.val = rs.bound

/-- Relation between the extracted end-piece statement and ArkLib's
`WEvalStatement` (`Sumcheck/FinalEval.lean:72`), whose `TCom` is instantiated at
the lift commitment's carrier `PolyVec (Rq Φ) dRows`. -/
def RepWEval {dRows m₀ : ℕ} (stmt : endpiece.WEvalStatement)
    (ws : InnerOuter.WEvalStatement (PolyVec (Rq Φ) dRows) F m₀) : Prop :=
  WfVec dRows stmt.t ∧ WfPoint m₀ stmt.point ∧ Reduced stmt.value ∧
    toVec (k := dRows) stmt.t = ws.t ∧
    toPoint (m := m₀) stmt.point = ws.point ∧
    toExt stmt.value = ws.value

/-! ## `ringswitch`: the mixed evaluation

Three obligations that belong to the ring-switch module by ArkLib's own file
split (`RingSwitch/{Rlin,Reduction}.lean`) but were first needed here. -/

/-- `c_eval_at` computes `cEvalAt`: a `Zq[X]` polynomial at a point of the
extension field (`RingSwitch/Reduction.lean:444`).

`cEvalAt φF a p = p.eval₂ φF a`, and `eval₂` is the *power sum*
`foldl (acc + f a * x ^ i)` (`CompPoly/Univariate/Basic.lean:251`), not Horner
-- which CompPoly offers separately and this definition does not use. The
extracted loop is that sum with the power recomputed per term. -/
theorem c_eval_at_spec (alpha : cpoly.field.Ext4) (p : ring.Rq)
    (ha : Reduced alpha) (hp : Wf p) :
    ringswitch.c_eval_at alpha p
      ⦃ out => Reduced out ∧ toExt out = InnerOuter.cEvalAt phiF (toExt alpha) (toRq p).1 ⦄ := by
  sorry

/-- `c_eval_at_modulus` computes `cEvalAt φF α Φ.φ`, the `φ(α)` factor of
`mAlphaTilde` (`ZeroCheck/Constraints.lean:519`).

A separate entry point because `Φ.φ = X^d + 1` has `d + 1` coefficients and no
`Rq` can hold it -- the invariant is exactly `d` of them. -/
theorem c_eval_at_modulus_spec (alpha : cpoly.field.Ext4) (ha : Reduced alpha) :
    ringswitch.c_eval_at_modulus alpha
      ⦃ out => Reduced out ∧ toExt out = InnerOuter.cEvalAt phiF (toExt alpha) Φ.φ ⦄ := by
  sorry

/-- The `R^lin` statement's constructor preserves the relation. -/
theorem RlinStatement_new_spec {n μ : ℕ} (m : linalg.PolyMatrix) (yvec : linalg.PolyVec)
    (bound : Std.U64) (rs : InnerOuter.RlinStatement Φ n μ)
    (hm : toMat (rows := n) (cols := μ) m = rs.M) (hy : toVec (k := n) yvec = rs.yvec)
    (hb : bound.val = rs.bound) (hWm : WfMat n μ m) (hWy : WfVec n yvec) :
    ringswitch.RlinStatement.new m yvec bound
      ⦃ out => RepRlin (n := n) (μ := μ) out rs ⦄ := by
  sorry

/-! ## `zerocheck`: the `H₀` side -/

/-- `range_product` computes `rangeProduct`, the vanishing polynomial of the
symmetric range `{−(b−1), …, b−1}` (`Constraints.lean:96`). -/
theorem range_product_spec (v : cpoly.field.Ext4) (hv : Reduced v) :
    zerocheck.range_product v
      ⦃ out => Reduced out ∧ toExt out = InnerOuter.rangeProduct 16 (toExt v) ⦄ := by
  sorry

/-- `w_table` computes `wTable` at the cube point the flat index encodes
(`Constraints.lean:140`).

The specification's argument is a cube point `Fin m₀ → Fin 2`; the extracted
function takes its flat index, which is faithful because every consumer feeds
`finFunctionFinEquiv.symm i` into a `wTable` whose first act is
`finFunctionFinEquiv` (the simp step of `wTable_zRow`'s own proof, `:378`).

`hidx` is the specification's own coverage bound, not a translation artefact:
the index must name a cube point. -/
theorem w_table_spec {μ n m₀ : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (idx : Std.Usize)
    (hw : RepLiftedWitness w sw) (hidx : idx.val < 2 ^ m₀) :
    zerocheck.w_table w idx
      ⦃ out => Reduced out ∧ toExt out =
        InnerOuter.wTable Φ m₀ phiF 16 sw
          (finFunctionFinEquiv.symm ⟨idx.val, hidx⟩) ⦄ := by
  sorry

/-- `c_w_table_mle` computes `cWTableMle`, the committed table in Lagrange form
(`Constraints.lean:328`). -/
theorem c_w_table_mle_spec {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (m0 : Std.Usize)
    (hw : RepLiftedWitness w sw) (hm0 : 2 ^ m0.val ≤ Usize.max) :
    zerocheck.c_w_table_mle w m0
      ⦃ out => WfEvals m0.val out ∧ toEvals (m := m0.val) out =
        InnerOuter.cWTableMle Φ m0.val phiF 16 sw ⦄ := by
  sorry

/-- `w_table_mle_eval` computes `wTableMleEval`, the evaluation claim the
final-evaluation step carries (`Constraints.lean:335`). -/
theorem w_table_mle_eval_spec {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (m0 : Std.Usize)
    (a : alloc.vec.Vec cpoly.field.Ext4)
    (hw : RepLiftedWitness w sw) (ha : WfPoint m0.val a)
    (hm0 : 2 ^ m0.val ≤ Usize.max) :
    zerocheck.w_table_mle_eval w m0 a
      ⦃ out => Reduced out ∧ toExt out =
        InnerOuter.wTableMleEval Φ m0.val phiF 16 sw (toPoint (m := m0.val) a) ⦄ := by
  sorry

/-- `h_zero` computes `hZero`, the range-constraint block
(`Constraints.lean:204`). -/
theorem h_zero_spec {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (m0 : Std.Usize)
    (hw : RepLiftedWitness w sw) (hm0 : 2 ^ m0.val ≤ Usize.max) :
    zerocheck.h_zero w m0
      ⦃ out => WfEvals m0.val out ∧ toEvals (m := m0.val) out =
        InnerOuter.hZero Φ m0.val phiF 16 sw ⦄ := by
  sorry

/-- `h_zero_is_zero` **decides** `hZero = 0`, in the pointwise form of
`hZero_eq_zero_iff` (`Constraints.lean:219`).

An `↔`, not an implication: a verifier that rejected everything would satisfy
the accepting direction alone, and the rejection path is the half a broken
implementation still passes. -/
theorem h_zero_is_zero_spec {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (m0 : Std.Usize)
    (hw : RepLiftedWitness w sw) (hm0 : 2 ^ m0.val ≤ Usize.max) :
    zerocheck.h_zero_is_zero w m0
      ⦃ b => (b = true ↔ InnerOuter.hZero Φ m0.val phiF 16 sw = 0) ⦄ := by
  sorry

/-! ## `zerocheck`: the `H_α` side, through `alphaDefect` -/

/-- `alpha_tilde` computes `alphaTilde α ℓ = α ^ ℓ`, the public
column-contraction vector (`Constraints.lean:502`). -/
theorem alpha_tilde_spec (alpha : cpoly.field.Ext4) (l : Std.Usize)
    (ha : Reduced alpha) :
    zerocheck.alpha_tilde alpha l
      ⦃ out => Reduced out ∧ toExt out = InnerOuter.alphaTilde (toExt alpha) l.val ⦄ := by
  sorry

/-- `eq_weight` computes entry `i` of `CMlPolynomialEval.lagrangeBasis τ₁`, the
`m₁`-cube equality weight (`Constraints.lean:845-847`; the bit product does
**not** cancel against `finFunctionFinEquiv`, see brief 4 § Corrections item
1). -/
theorem eq_weight_spec {m₁ : ℕ} (tau1 : alloc.vec.Vec cpoly.field.Ext4)
    (i : Std.Usize) (ht : WfPoint m₁ tau1) (hi : i.val < 2 ^ m₁) :
    zerocheck.eq_weight tau1 i
      ⦃ out => Reduced out ∧ toExt out =
        (CMlPolynomialEval.lagrangeBasis (Vector.ofFn (toPoint (m := m₁) tau1))).get
          ⟨i.val, hi⟩ ⦄ := by
  sorry

/-- `m_alpha_tilde` computes `mAlphaTilde`, the public constraint matrix at `α`
(`Constraints.lean:517`), in the specification's three cases. -/
theorem m_alpha_tilde_spec {n μ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (i u : Std.Usize) (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (hi : i.val < n) :
    zerocheck.m_alpha_tilde s alpha i u
      ⦃ out => Reduced out ∧ toExt out =
        InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨i.val, hi⟩ u.val ⦄ := by
  sorry

/-- `alpha_public_evals` computes `alphaPublicEvals`, the public table
multiplying `mle[w̃]` in the linear-constraint sumcheck
(`Constraints.lean:840`). -/
theorem alpha_public_evals_spec {n μ m₀ m₁ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) (idx : Std.Usize)
    (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (ht : WfPoint m₁ tau1) (hidx : idx.val < 2 ^ m₀) :
    zerocheck.alpha_public_evals s alpha tau1 idx
      ⦃ out => Reduced out ∧ toExt out =
        InnerOuter.alphaPublicEvals Φ m₀ m₁ phiF 16 rs (toExt alpha)
          (toPoint (m := m₁) tau1) (finFunctionFinEquiv.symm ⟨idx.val, hidx⟩) ⦄ := by
  sorry

/-- `zc_target_alpha` computes `zcTargetAlpha`, the public initial target of the
linear sumcheck (`Constraints.lean:875`). -/
theorem zc_target_alpha_spec {n μ m₁ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4)
    (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (ht : WfPoint m₁ tau1) :
    zerocheck.zc_target_alpha s alpha tau1
      ⦃ out => Reduced out ∧ toExt out =
        InnerOuter.zcTargetAlpha Φ m₁ phiF rs (toExt alpha) (toPoint (m := m₁) tau1) ⦄ := by
  sorry

/-- `alpha_contract` computes `alphaContract` at `T = wTable`
(`Constraints.lean:540`).

The specification takes the table as a *function*; a function argument has no
translation here, so this is the instantiated form -- which is the only one the
chain uses and the one `hAlphaEvals_eq_alphaDefect` is stated at.

`hmn` is the specification's own `hμn`, and it is a genuine obligation: the
extracted loop forms `d·u + ℓ` as a checked `usize` product. -/
theorem alpha_contract_spec {n μ m₀ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (i : Std.Usize) (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (hw : RepLiftedWitness w sw) (hi : i.val < n)
    (hmn : (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree ≤ 2 ^ m₀) :
    zerocheck.alpha_contract s alpha w i
      ⦃ out => Reduced out ∧ toExt out =
        InnerOuter.alphaContract Φ m₀ phiF 16 rs (toExt alpha) hmn
          (InnerOuter.wTable Φ m₀ phiF 16 sw) ⟨i.val, hi⟩ ⦄ := by
  sorry

/-- `alpha_defect` computes `alphaDefect` at `T = wTable`
(`Constraints.lean:549`): the contraction minus the public right-hand side. -/
theorem alpha_defect_spec {n μ m₀ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (i : Std.Usize) (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (hw : RepLiftedWitness w sw) (hi : i.val < n)
    (hmn : (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree ≤ 2 ^ m₀) :
    zerocheck.alpha_defect s alpha w i
      ⦃ out => Reduced out ∧ toExt out =
        InnerOuter.alphaDefect Φ m₀ phiF 16 rs (toExt alpha) hmn
          (InnerOuter.wTable Φ m₀ phiF 16 sw) ⟨i.val, hi⟩ ⦄ := by
  sorry

/-- `h_alpha_evals` computes entry `idx` of the `H_α` table, in `alphaDefect`
form. -/
theorem h_alpha_evals_spec {n μ m₀ m₁ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (idx : Std.Usize) (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (hw : RepLiftedWitness w sw)
    (hmn : (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree ≤ 2 ^ m₀) :
    zerocheck.h_alpha_evals s alpha w idx
      ⦃ out => Reduced out ∧ toExt out =
        (if h : idx.val < n then
            InnerOuter.alphaDefect Φ m₀ phiF 16 rs (toExt alpha) hmn
              (InnerOuter.wTable Φ m₀ phiF 16 sw) ⟨idx.val, h⟩
          else 0) ⦄ := by
  sorry

/-- **The bridge to the noncomputable definition**, stated rather than assumed:
`h_alpha_evals` computes `hAlphaEvals` itself, via
`hAlphaEvals_eq_alphaDefect` (`Constraints.lean:771`).

This is the statement that makes the computable route sound. Its hypotheses are
that theorem's: `1 < b`, `0 < d` and `hμn`. -/
theorem h_alpha_evals_eq_hAlphaEvals_spec {n μ m₀ m₁ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (idx : Std.Usize) (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (hw : RepLiftedWitness w sw) (hd : 0 < Φ.φ.natDegree)
    (hidx : idx.val < 2 ^ m₁)
    (hmn : (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree ≤ 2 ^ m₀) :
    zerocheck.h_alpha_evals s alpha w idx
      ⦃ out => Reduced out ∧ toExt out =
        InnerOuter.hAlphaEvals Φ m₁ phiF 16 rs (toExt alpha) sw
          (finFunctionFinEquiv.symm ⟨idx.val, hidx⟩) ⦄ := by
  sorry

/-- `h_alpha` computes `hAlpha`'s Lagrange-form block (`Constraints.lean:213`),
through the same bridge. -/
theorem h_alpha_spec {n μ m₀ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (m1 : Std.Usize) (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (hw : RepLiftedWitness w sw) (hd : 0 < Φ.φ.natDegree)
    (hm1 : 2 ^ m1.val ≤ Usize.max)
    (hmn : (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree ≤ 2 ^ m₀) :
    zerocheck.h_alpha s alpha w m1
      ⦃ out => WfEvals m1.val out ∧ toEvals (m := m1.val) out =
        InnerOuter.hAlpha Φ m1.val phiF 16 rs (toExt alpha) sw ⦄ := by
  sorry

/-- `h_alpha_is_zero` **decides** `hAlpha = 0`, in the pointwise form of
`hAlpha_eq_zero_iff` (`Constraints.lean:233`). An `↔`, for the reason
`h_zero_is_zero_spec` gives. -/
theorem h_alpha_is_zero_spec {n μ m₀ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (m1 : Std.Usize) (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (hw : RepLiftedWitness w sw) (hd : 0 < Φ.φ.natDegree)
    (hm1 : 2 ^ m1.val ≤ Usize.max)
    (hmn : (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree ≤ 2 ^ m₀) :
    zerocheck.h_alpha_is_zero s alpha w m1
      ⦃ b => (b = true ↔
        InnerOuter.hAlpha Φ m1.val phiF 16 rs (toExt alpha) sw = 0) ⦄ := by
  sorry

end HachiEquiv.ZeroCheck
