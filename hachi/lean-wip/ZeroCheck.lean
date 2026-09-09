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

/-- `phiF` is the bare `Ext.ofBase`, definitionally: the bundling is only there
so that `RingHom` lemmas apply to it. -/
@[simp] theorem phiF_apply (c : ZMod q) : phiF c = Ext.ofBase c := rfl

/-- The image of a natural-number residue under the base embedding is that
natural number in the extension field. -/
theorem ofBase_natCast (k : ℕ) : (Ext.ofBase ((k : ZMod q)) : F) = (k : F) := by
  rw [← phiF_apply]
  exact map_natCast phiF k

/-! ## Loop helpers shared by the whole file

`zerocheck::two_pow` is the crate's own copy of the doubling loop `EvalSplit`
already has for `evalsplit::two_pow`: a distinct extracted constant, so a
distinct statement, carrying the same `2 ^ n ≤ Usize.max` the checked
multiplication forces.

That bound is **implied by representability and invisible to the `Vec` model**,
which is the distinction worth keeping. Every remaining caller of `two_pow`
uses its result to size a `2 ^ m`-entry table, so a caller that cannot supply
`2 ^ m ≤ Usize.max` could not hold the table either -- the hypothesis is a fact
about the output's own existence. What the `Vec` type exposes is only
`length ≤ Usize.max` for a vector that already exists; it says nothing about a
size computed before the vector is built, so the obligation has to be stated
rather than derived. Contrast the bounds this file *dropped*
(NOTES.md § "Two invented powers of two, removed"): those sized nothing, and
were forced only by computing a number where a predicate was wanted. -/

/-- The loop of `zerocheck::two_pow`: the accumulator is `2 ^ t` after `t`
doublings. -/
theorem two_pow_loop_spec (n size t : Std.Usize) (hn : 2 ^ n.val ≤ Usize.max)
    (ht : t.val ≤ n.val) (hsize : size.val = 2 ^ t.val) :
    zerocheck.two_pow_loop n size t ⦃ s => s.val = 2 ^ n.val ⦄ := by
  rw [zerocheck.two_pow_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val = 2 ^ s.2.val)
  · rintro ⟨s1, t1⟩ ⟨ht1, hs1⟩
    dsimp only at ht1 hs1
    simp only [zerocheck.two_pow_loop.body]
    by_cases hlt : t1 < n
    · rw [if_pos hlt]
      have hfit : s1.val * 2 ≤ Usize.max := by
        have hmono : 2 ^ (t1.val + 1) ≤ 2 ^ n.val :=
          Nat.pow_le_pow_right (by norm_num) (by scalar_tac)
        rw [hs1, ← pow_succ] at *
        omega
      step as ⟨s2, hs2⟩
      step as ⟨t2, ht2⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hs2, hs1, ht2, pow_succ]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : t1.val = n.val := by scalar_tac
      rw [hs1, heq]
  · exact ⟨ht, hsize⟩

/-- `zerocheck::two_pow` is `2 ^ n`, total up to the `usize` ceiling. -/
theorem two_pow_spec (n : Std.Usize) (hn : 2 ^ n.val ≤ Usize.max) :
    zerocheck.two_pow n ⦃ s => s.val = 2 ^ n.val ⦄ :=
  two_pow_loop_spec n 1#usize 0#usize hn (by simp) (by simp)

/-! ## `ringswitch`: the mixed evaluation

Three obligations that belong to the ring-switch module by ArkLib's own file
split (`RingSwitch/{Rlin,Reduction}.lean`) but were first needed here. -/

/-- The loop of `ext_pow`: the accumulator is `x ^ t` after `t` steps. -/
theorem ext_pow_loop_spec (x : cpoly.field.Ext4) (i : Std.Usize) (acc : cpoly.field.Ext4)
    (t : Std.Usize) (hx : Reduced x) (hacc : Reduced acc) (ht : t.val ≤ i.val)
    (hval : toExt acc = toExt x ^ t.val) :
    ringswitch.ext_pow_loop x i acc t
      ⦃ out => Reduced out ∧ toExt out = toExt x ^ i.val ⦄ := by
  rw [ringswitch.ext_pow_loop]
  apply loop.spec_decr_nat (fun s => i.val - s.2.val)
    (fun s => s.2.val ≤ i.val ∧ Reduced s.1 ∧ toExt s.1 = toExt x ^ s.2.val)
  · rintro ⟨a1, t1⟩ ⟨ht1, hR1, hv1⟩
    dsimp only at ht1 hR1 hv1
    simp only [ringswitch.ext_pow_loop.body]
    by_cases hlt : t1 < i
    · rw [if_pos hlt]
      step with ext_mul_spec a1 x hR1 hx as ⟨a2, hR2, hv2⟩
      step as ⟨t2, ht2⟩
      refine ⟨by scalar_tac, hR2, ?_, by scalar_tac⟩
      have ht2n : t2.val = t1.val + 1 := by scalar_tac
      rw [hv2, hv1, ht2n, pow_succ]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : t1.val = i.val := by scalar_tac
      exact ⟨hR1, by rw [hv1, heq]⟩
  · exact ⟨ht, hacc, hval⟩

/-- `ext_pow` is the power map of the extension field. -/
theorem ext_pow_spec (x : cpoly.field.Ext4) (i : Std.Usize) (hx : Reduced x) :
    ringswitch.ext_pow x i ⦃ out => Reduced out ∧ toExt out = toExt x ^ i.val ⦄ := by
  rw [ringswitch.ext_pow]
  exact ext_pow_loop_spec x i cpoly.field.Ext4.ONE 0#usize hx reduced_ONE (by simp) (by simp)

/-- A represented `Rq` has `CPolynomial` degree strictly below `N`, which is what
licenses reading its evaluation as the `N`-term power sum. -/
theorem toRq_natDegree_lt (p : ring.Rq) : (toRq p).1.natDegree < N := by
  have h := Rq.natDegree_val_toPoly_lt' Φ (by rw [phi_natDegree]; norm_num) (toRq p)
  rw [← phi_natDegree, CPolynomial.natDegree_toPoly]
  exact h

/-- The loop of `c_eval_at`: the accumulator is the partial power sum. -/
theorem c_eval_at_loop_spec (alpha : cpoly.field.Ext4) (p : ring.Rq)
    (acc : cpoly.field.Ext4) (k : Std.Usize) (ha : Reduced alpha) (hp : Wf p)
    (hacc : Reduced acc) (hk : k.val ≤ N)
    (hval : toExt acc = ∑ l ∈ Finset.range k.val, phiF (coeffK p l) * toExt alpha ^ l) :
    ringswitch.c_eval_at_loop alpha p params.RING_DEGREE acc k
      ⦃ out => Reduced out ∧ toExt out =
        ∑ l ∈ Finset.range N, phiF (coeffK p l) * toExt alpha ^ l ⦄ := by
  have hrd : (params.RING_DEGREE).val = N := params_RING_DEGREE_val
  rw [ringswitch.c_eval_at_loop]
  apply loop.spec_decr_nat (fun s => N - s.2.val)
    (fun s => s.2.val ≤ N ∧ Reduced s.1 ∧ toExt s.1 =
      ∑ l ∈ Finset.range s.2.val, phiF (coeffK p l) * toExt alpha ^ l)
  · rintro ⟨a1, k1⟩ ⟨hk1, hR1, hv1⟩
    dsimp only at hk1 hR1 hv1
    simp only [ringswitch.c_eval_at_loop.body]
    by_cases hlt : k1 < params.RING_DEGREE
    · rw [if_pos hlt]
      have hk1lt : k1.val < N := by scalar_tac
      step with RqBridge.coeff_spec p k1 hp as ⟨f, hRf, hf⟩
      rw [toRq_coeff, if_pos hk1lt] at hf
      step with ext_from_base_spec f hRf as ⟨c, hRc, hc⟩
      step with ext_pow_spec alpha k1 ha as ⟨pw, hRpw, hpw⟩
      step with ext_mul_spec c pw hRc hRpw as ⟨e, hRe, he⟩
      step with ext_add_spec a1 e hR1 hRe as ⟨a2, hR2, ha2⟩
      step as ⟨k2, hk2⟩
      have hk2n : k2.val = k1.val + 1 := by scalar_tac
      refine ⟨by scalar_tac, hR2, ?_, by scalar_tac⟩
      rw [ha2, hv1, he, hc, hf, hpw, hk2n, Finset.sum_range_succ, phiF_apply]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = N := by scalar_tac
      exact ⟨hR1, by rw [hv1, heq]⟩
  · exact ⟨hk, hacc, hval⟩

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
  rw [ringswitch.c_eval_at, InnerOuter.cEvalAt_eq_sum_range phiF (toExt alpha) (toRq_natDegree_lt p)]
  apply spec_mono (c_eval_at_loop_spec alpha p cpoly.field.Ext4.ZERO 0#usize ha hp
    reduced_ZERO (by simp) (by simp))
  rintro out ⟨hR, hout⟩
  refine ⟨hR, ?_⟩
  rw [hout]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [toRq_coeff, if_pos (Finset.mem_range.mp hl)]

/-- The coefficients of the modulus `φ = X^N + 1`. -/
theorem phi_coeff (l : ℕ) :
    Φ.φ.coeff l = if l = 0 then 1 else if l = N then 1 else 0 := by
  rw [CPolynomial.coeff_toPoly, phi_toPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_one]
  by_cases h0 : l = 0
  · subst h0
    norm_num
  · by_cases hN : l = N
    · subst hN
      simp [h0]
    · simp [h0, hN]

/-- The loop of `c_eval_at_modulus`: the accumulator is the partial power sum of
the modulus, which runs to `N` *inclusive*. -/
theorem c_eval_at_modulus_loop_spec (alpha : cpoly.field.Ext4) (acc : cpoly.field.Ext4)
    (k : Std.Usize) (ha : Reduced alpha) (hacc : Reduced acc) (hk : k.val ≤ N + 1)
    (hval : toExt acc = ∑ l ∈ Finset.range k.val, phiF (Φ.φ.coeff l) * toExt alpha ^ l) :
    ringswitch.c_eval_at_modulus_loop alpha params.RING_DEGREE acc k
      ⦃ out => Reduced out ∧ toExt out =
        ∑ l ∈ Finset.range (N + 1), phiF (Φ.φ.coeff l) * toExt alpha ^ l ⦄ := by
  have hrd : (params.RING_DEGREE).val = N := params_RING_DEGREE_val
  rw [ringswitch.c_eval_at_modulus_loop]
  apply loop.spec_decr_nat (fun s => N + 1 - s.2.val)
    (fun s => s.2.val ≤ N + 1 ∧ Reduced s.1 ∧ toExt s.1 =
      ∑ l ∈ Finset.range s.2.val, phiF (Φ.φ.coeff l) * toExt alpha ^ l)
  · rintro ⟨a1, k1⟩ ⟨hk1, hR1, hv1⟩
    dsimp only at hk1 hR1 hv1
    simp only [ringswitch.c_eval_at_modulus_loop.body]
    by_cases hlt : k1 ≤ params.RING_DEGREE
    · rw [if_pos hlt]
      have hk1le : k1.val ≤ N := by scalar_tac
      have hbranch : ∃ co : cpoly.field.Fp, Red co ∧ toK co = Φ.φ.coeff k1.val ∧
          (if k1 = 0#usize then ok cpoly.field.Fp.ONE
            else if k1 = params.RING_DEGREE then ok cpoly.field.Fp.ONE
            else ok cpoly.field.Fp.ZERO) = (ok co : Result cpoly.field.Fp) := by
        by_cases h0 : k1 = 0#usize
        · refine ⟨cpoly.field.Fp.ONE, Red_one, ?_, by rw [if_pos h0]⟩
          have : k1.val = 0 := by rw [h0]; rfl
          rw [toK_one, phi_coeff, if_pos this]
        · have h0' : k1.val ≠ 0 := by
            intro h
            exact h0 (by scalar_tac)
          by_cases hN : k1 = params.RING_DEGREE
          · refine ⟨cpoly.field.Fp.ONE, Red_one, ?_, by rw [if_neg h0, if_pos hN]⟩
            have : k1.val = N := by rw [hN]; exact hrd
            rw [toK_one, phi_coeff, if_neg h0', if_pos this]
          · have hN' : k1.val ≠ N := by
              intro h
              exact hN (by scalar_tac)
            refine ⟨cpoly.field.Fp.ZERO, Red_zero, ?_, by rw [if_neg h0, if_neg hN]⟩
            rw [toK_zero, phi_coeff, if_neg h0', if_neg hN']
      obtain ⟨co, hRco, hco, hite⟩ := hbranch
      rw [hite]
      simp only [bind_tc_ok]
      step with ext_from_base_spec co hRco as ⟨c, hRc, hc⟩
      step with ext_pow_spec alpha k1 ha as ⟨pw, hRpw, hpw⟩
      step with ext_mul_spec c pw hRc hRpw as ⟨e, hRe, he⟩
      step with ext_add_spec a1 e hR1 hRe as ⟨a2, hR2, ha2⟩
      step as ⟨k2, hk2⟩
      have hk2n : k2.val = k1.val + 1 := by scalar_tac
      refine ⟨by scalar_tac, hR2, ?_, by scalar_tac⟩
      rw [ha2, hv1, he, hc, hco, hpw, hk2n, Finset.sum_range_succ, phiF_apply]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = N + 1 := by scalar_tac
      exact ⟨hR1, by rw [hv1, heq]⟩
  · exact ⟨hk, hacc, hval⟩

/-- `c_eval_at_modulus` computes `cEvalAt φF α Φ.φ`, the `φ(α)` factor of
`mAlphaTilde` (`ZeroCheck/Constraints.lean:519`).

A separate entry point because `Φ.φ = X^d + 1` has `d + 1` coefficients and no
`Rq` can hold it -- the invariant is exactly `d` of them. -/
theorem c_eval_at_modulus_spec (alpha : cpoly.field.Ext4) (ha : Reduced alpha) :
    ringswitch.c_eval_at_modulus alpha
      ⦃ out => Reduced out ∧ toExt out = InnerOuter.cEvalAt phiF (toExt alpha) Φ.φ ⦄ := by
  have hdeg : Φ.φ.natDegree < N + 1 := by rw [phi_natDegree]; omega
  rw [ringswitch.c_eval_at_modulus,
    InnerOuter.cEvalAt_eq_sum_range phiF (toExt alpha) hdeg]
  exact c_eval_at_modulus_loop_spec alpha cpoly.field.Ext4.ZERO 0#usize ha reduced_ZERO
    (by simp)
    (by rw [show (0#usize).val = 0 from rfl, Finset.range_zero, Finset.sum_empty, toExt_ZERO])

/-- The `R^lin` statement's constructor preserves the relation. -/
theorem RlinStatement_new_spec {n μ : ℕ} (m : linalg.PolyMatrix) (yvec : linalg.PolyVec)
    (bound : Std.U64) (rs : InnerOuter.RlinStatement Φ n μ)
    (hm : toMat (rows := n) (cols := μ) m = rs.M) (hy : toVec (k := n) yvec = rs.yvec)
    (hb : bound.val = rs.bound) (hWm : WfMat n μ m) (hWy : WfVec n yvec) :
    ringswitch.RlinStatement.new m yvec bound
      ⦃ out => RepRlin (n := n) (μ := μ) out rs ⦄ := by
  rw [ringswitch.RlinStatement.new, WP.spec_ok]
  exact ⟨hWm, hWy, hm, hy, hb⟩

/-! ## `zerocheck`: the `H₀` side -/

/-- `range_product` computes `rangeProduct`, the vanishing polynomial of the
symmetric range `{−(b−1), …, b−1}` (`Constraints.lean:96`). -/
theorem range_product_loop_spec (v : cpoly.field.Ext4) (acc : cpoly.field.Ext4)
    (j : Std.U64) (hv : Reduced v) (hacc : Reduced acc) (hj : 1 ≤ j.val) (hjle : j.val ≤ 16)
    (hval : toExt acc = toExt v *
      ∏ k ∈ Finset.Ico (1 : ℕ) j.val, ((toExt v - (k : F)) * (toExt v + (k : F)))) :
    zerocheck.range_product_loop v params.GADGET_BASE acc j
      ⦃ out => Reduced out ∧ toExt out = InnerOuter.rangeProduct 16 (toExt v) ⦄ := by
  have hgb : (params.GADGET_BASE).val = 16 := by simp [params.GADGET_BASE]
  rw [zerocheck.range_product_loop]
  apply loop.spec_decr_nat (fun s => 16 - s.2.val)
    (fun s => 1 ≤ s.2.val ∧ s.2.val ≤ 16 ∧ Reduced s.1 ∧ toExt s.1 = toExt v *
      ∏ k ∈ Finset.Ico (1 : ℕ) s.2.val, ((toExt v - (k : F)) * (toExt v + (k : F))))
  · rintro ⟨a1, j1⟩ ⟨hj1, hj1le, hR1, hv1⟩
    dsimp only at hj1 hj1le hR1 hv1
    simp only [zerocheck.range_product_loop.body]
    by_cases hlt : j1 < params.GADGET_BASE
    · rw [if_pos hlt]
      have hj1lt : j1.val < 16 := by scalar_tac
      step as ⟨f, hRf, hf⟩
      step with ext_from_base_spec f hRf as ⟨sc, hRsc, hsc⟩
      step with ext_sub_spec v sc hv hRsc as ⟨lo, hRlo, hlo⟩
      step with ext_add_spec v sc hv hRsc as ⟨hi, hRhi, hhi⟩
      step with ext_mul_spec a1 lo hR1 hRlo as ⟨e, hRe, he⟩
      step with ext_mul_spec e hi hRe hRhi as ⟨a2, hR2, ha2⟩
      step as ⟨j2, hj2⟩
      have hscv : toExt sc = ((j1.val : ℕ) : F) := by rw [hsc, hf, ofBase_natCast]
      have hj2n : j2.val = j1.val + 1 := by scalar_tac
      refine ⟨by scalar_tac, by scalar_tac, hR2, ?_, by scalar_tac⟩
      rw [ha2, he, hv1, hlo, hhi, hscv, hj2n,
        Finset.prod_Ico_succ_top (by omega)]
      ring
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : j1.val = 16 := by scalar_tac
      have hIco : Finset.Ico (1 : ℕ) 16 = Finset.Icc 1 (16 - 1) := by decide
      refine ⟨hR1, ?_⟩
      rw [hv1, heq, InnerOuter.rangeProduct, hIco]
  · exact ⟨hj, hjle, hacc, hval⟩

/-- `range_product` computes `rangeProduct` at the crate's gadget base. -/
theorem range_product_spec (v : cpoly.field.Ext4) (hv : Reduced v) :
    zerocheck.range_product v
      ⦃ out => Reduced out ∧ toExt out = InnerOuter.rangeProduct 16 (toExt v) ⦄ := by
  rw [zerocheck.range_product]
  exact range_product_loop_spec v v 1#u64 hv hv (by simp) (by simp) (by simp)

/-- The specification's table, read at the cube point a flat index encodes: the
`let`s of `wTable` resolved, with `d = N` and `rhoDigitCount q 16 = 8` put in.
The shape every `w_table` caller wants. -/
theorem wTable_at_flat_index {μ n m₀ : ℕ} (sw : InnerOuter.LiftedWitness Φ μ n)
    {idx : ℕ} (hidx : idx < 2 ^ m₀) :
    InnerOuter.wTable Φ m₀ phiF 16 sw (finFunctionFinEquiv.symm ⟨idx, hidx⟩)
      = if hz : idx / N < μ then phiF ((sw.z ⟨idx / N, hz⟩).1.coeff (idx % N))
        else if hr : idx / N - μ < n * 8 then
          phiF ((InnerOuter.rhoDigits Φ 16
            (sw.ρ ⟨(idx / N - μ) / 8, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])⟩)
            ((idx / N - μ) % 8)).coeff (idx % N))
        else 0 := by
  simp only [InnerOuter.wTable, Equiv.apply_symm_apply, phi_natDegree, rhoDigitCount_eq]

/-- `w_table` computes `wTable` at the cube point the flat index encodes
(`Constraints.lean:140`).

`hmax` is the arity bound the crate's checked `rows * GADGET_DIGITS` forces, and
it is the specification's own product: `wTable`'s second case is guarded by
`idx / d - μ < n * rhoDigitCount q b`. It is the same hypothesis
`lift_message_spec` and `end_piece_check_spec` already carry.

The specification's argument is a cube point `Fin m₀ → Fin 2`; the extracted
function takes its flat index, which is faithful because every consumer feeds
`finFunctionFinEquiv.symm i` into a `wTable` whose first act is
`finFunctionFinEquiv` (the simp step of `wTable_zRow`'s own proof, `:378`).

`hidx` is the specification's own coverage bound, not a translation artefact:
the index must name a cube point. -/
theorem w_table_spec {μ n m₀ : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (idx : Std.Usize)
    (hw : RepLiftedWitness w sw) (hidx : idx.val < 2 ^ m₀)
    (hmax : μ + n * 8 ≤ Usize.max) :
    zerocheck.w_table w idx
      ⦃ out => Reduced out ∧ toExt out =
        InnerOuter.wTable Φ m₀ phiF 16 sw
          (finFunctionFinEquiv.symm ⟨idx.val, hidx⟩) ⦄ := by
  obtain ⟨hWz, hWrho, hzeq, hrhoeq⟩ := hw
  have hgd : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  have hrd : (params.RING_DEGREE).val = N := params_RING_DEGREE_val
  have hzlen : (alloc.vec.Vec.len w.z).val = μ := by simpa using hWz.1
  have hrholen : (alloc.vec.Vec.len w.rho).val = n := by simpa using hWrho.1
  rw [wTable_at_flat_index (idx := idx.val) (hidx := hidx)]
  rw [zerocheck.w_table]
  simp only [ringswitch.LiftedWitness.impl.z, ringswitch.LiftedWitness.impl.rho,
    linalg.PolyVec.len, bind_tc_ok]
  step as ⟨row, hrow⟩
  step as ⟨col, hcol⟩
  have hrowv : row.val = idx.val / N := by rw [hrow, hrd]
  have hcolv : col.val = idx.val % N := by rw [hcol, hrd]
  have hcolN : col.val < N := by rw [hcolv]; exact Nat.mod_lt _ (by norm_num)
  by_cases hlt : row < alloc.vec.Vec.len w.z
  · have hz : idx.val / N < μ := by rw [← hrowv, ← hzlen]; scalar_tac
    rw [if_pos hlt, dif_pos hz]
    have hrowlt : row.val < w.z.val.length := by rw [hWz.1, hrowv]; exact hz
    simp only [linalg.PolyVec.get]
    step as ⟨r, hr⟩
    have hWr : Wf r := by rw [hr]; exact hWz.2 _ (List.getElem_mem hrowlt)
    step with RqBridge.coeff_spec r col hWr as ⟨f, hRf, hf⟩
    apply spec_mono (ext_from_base_spec f hRf)
    rintro out ⟨hRout, hout⟩
    refine ⟨hRout, ?_⟩
    have hzentry : sw.z ⟨idx.val / N, hz⟩ = toRq r := by
      rw [← hzeq]
      show toRq (w.z.val.getD (idx.val / N) (alloc.vec.Vec.new cpoly.field.Fp)) = toRq r
      rw [← hrowv, List.getD_eq_getElem _ _ hrowlt, hr]
    rw [hout, hf, ← phiF_apply, hzentry, ← hcolv]
  · have hz : ¬ idx.val / N < μ := by rw [← hrowv, ← hzlen]; scalar_tac
    rw [if_neg hlt, dif_neg hz]
    step as ⟨i, hi⟩
    have hiv : i.val = idx.val / N - μ := by rw [hi, hzlen, hrowv]
    have hmul : (alloc.vec.Vec.len w.rho).val * (params.GADGET_DIGITS).val ≤ Usize.max := by
      rw [hrholen, hgd]; omega
    step as ⟨i1, hi1⟩
    have hi1v : i1.val = n * 8 := by rw [hi1, hrholen, hgd]
    by_cases hlt2 : i < i1
    · have hr8 : idx.val / N - μ < n * 8 := by rw [← hiv, ← hi1v]; scalar_tac
      rw [if_pos hlt2, dif_pos hr8]
      have hivlt : i.val < n * 8 := by rw [hiv]; exact hr8
      have hrlt : i.val / 8 < n := by omega
      have helt : i.val % 8 < 8 := by omega
      step with rho_digit_as_rq_raw_spec (n := n) w.rho i hWrho hivlt as ⟨r, hWr, hr⟩
      step with RqBridge.coeff_spec r col hWr as ⟨f, hRf, hf⟩
      apply spec_mono (ext_from_base_spec f hRf)
      rintro out ⟨hRout, hout⟩
      refine ⟨hRout, ?_⟩
      have key : (toRq r).1.coeff col.val
          = (InnerOuter.rhoDigits Φ 16 (toRho (n := n) w.rho ⟨i.val / 8, hrlt⟩)
              (i.val % 8)).coeff col.val := by
        have hd := digitRq_coeff_eq_rhoDigits (n := n) w.rho hrlt helt (k := col.val) hcolN
        rw [show i.val / 8 * 8 + i.val % 8 = i.val from by omega] at hd
        rw [hr, hd]
      rw [hout, hf, ← phiF_apply, ← hrhoeq, ← hcolv]
      simp only [← hiv]
      rw [key]
    · have hr8 : ¬ idx.val / N - μ < n * 8 := by rw [← hiv, ← hi1v]; scalar_tac
      rw [if_neg hlt2, dif_neg hr8, WP.spec_ok]
      exact ⟨reduced_ZERO, toExt_ZERO⟩

/-- The table entry at a flat index, as a function of a plain `ℕ`: the shape a
loop invariant can carry, since the loop counter has no `2 ^ m₀` bound in its
type. Off the cube it is `0`, a value no loop ever reads. -/
noncomputable def wTableFlat {μ n : ℕ} (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n)
    (t : ℕ) : F :=
  if h : t < 2 ^ m₀ then InnerOuter.wTable Φ m₀ phiF 16 sw (finFunctionFinEquiv.symm ⟨t, h⟩)
  else 0

/-- `w_table`, against the `ℕ`-indexed table. -/
theorem w_table_flat_spec {μ n m₀ : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (idx : Std.Usize)
    (hw : RepLiftedWitness w sw) (hidx : idx.val < 2 ^ m₀)
    (hmax : μ + n * 8 ≤ Usize.max) :
    zerocheck.w_table w idx
      ⦃ out => Reduced out ∧ toExt out = wTableFlat m₀ sw idx.val ⦄ := by
  apply spec_mono (w_table_spec w sw idx hw hidx hmax)
  rintro out ⟨hR, hout⟩
  exact ⟨hR, by rw [hout, wTableFlat, dif_pos hidx]⟩

/-- A property of every cube point is a property at every flat index below
`2 ^ m₀`: the two quantifiers are transported by `finFunctionFinEquiv`. -/
theorem forall_cube_iff_forall_flat {m₀ : ℕ} (P : (Fin m₀ → Fin 2) → Prop) :
    (∀ x, P x) ↔ ∀ t, ∀ h : t < 2 ^ m₀, P (finFunctionFinEquiv.symm ⟨t, h⟩) := by
  constructor
  · intro h t ht
    exact h _
  · intro h x
    have := h (finFunctionFinEquiv x) (finFunctionFinEquiv x).isLt
    rwa [Fin.eta, Equiv.symm_apply_apply] at this

/-- The loop of `c_w_table_mle`: the values already pushed are the table entries
of their indices. -/
theorem c_w_table_mle_loop_spec {μ n m₀ : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (size : Std.Usize)
    (values : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize)
    (hw : RepLiftedWitness w sw) (hmax : μ + n * 8 ≤ Usize.max)
    (hm0 : 2 ^ m₀ ≤ Usize.max) (hsize : size.val = 2 ^ m₀) (hi : i.val ≤ 2 ^ m₀)
    (hlen : values.val.length = i.val) (hred : VecReduced values)
    (hval : ∀ t < i.val, toExt (values.val.getD t cpoly.field.Ext4.ZERO) = wTableFlat m₀ sw t) :
    zerocheck.c_w_table_mle_loop w size values i
      ⦃ o => o.val.length = 2 ^ m₀ ∧ VecReduced o ∧
        ∀ t < 2 ^ m₀, toExt (o.val.getD t cpoly.field.Ext4.ZERO) = wTableFlat m₀ sw t ⦄ := by
  rw [zerocheck.c_w_table_mle_loop]
  apply loop.spec_decr_nat (fun s => 2 ^ m₀ - s.2.val)
    (fun s => s.2.val ≤ 2 ^ m₀ ∧ s.1.val.length = s.2.val ∧ VecReduced s.1 ∧
      ∀ t < s.2.val, toExt (s.1.val.getD t cpoly.field.Ext4.ZERO) = wTableFlat m₀ sw t)
  · rintro ⟨v1, i1⟩ ⟨hi1, hlen1, hred1, hval1⟩
    dsimp only at hi1 hlen1 hred1 hval1
    simp only [zerocheck.c_w_table_mle_loop.body]
    by_cases hlt : i1 < size
    · rw [if_pos hlt]
      have hilt : i1.val < 2 ^ m₀ := by rw [← hsize]; scalar_tac
      step with w_table_flat_spec (m₀ := m₀) w sw i1 hw hilt hmax as ⟨e, hRe, he⟩
      have hbound : v1.val.length < Usize.max := by omega
      step as ⟨v2, hv2⟩
      step as ⟨i2, hi2⟩
      have hi2n : i2.val = i1.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, ?_, ?_, by scalar_tac⟩
      · rw [hi2n, hv2, List.length_append, hlen1]; simp
      · intro y hy
        rw [hv2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hred1 y h
        · rw [List.mem_singleton.mp h]; exact hRe
      · intro t ht
        rw [hi2n] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = v1.val.length := by omega
          rw [hteq, hv2, getD_append_eq, he, hlen1]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = 2 ^ m₀ := by rw [← hsize] at hi1 ⊢; scalar_tac
      exact ⟨by rw [hlen1, heq], hred1, by rw [← heq]; exact hval1⟩
  · exact ⟨hi, hlen, hred, hval⟩

/-- `c_w_table_mle` computes `cWTableMle`, the committed table in Lagrange form
(`Constraints.lean:328`).

Carries the same `μ + n * 8 ≤ Usize.max` as `w_table_spec`, which it calls. -/
theorem c_w_table_mle_spec {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (m0 : Std.Usize)
    (hw : RepLiftedWitness w sw) (hm0 : 2 ^ m0.val ≤ Usize.max)
    (hmax : μ + n * 8 ≤ Usize.max) :
    zerocheck.c_w_table_mle w m0
      ⦃ out => WfEvals m0.val out ∧ toEvals (m := m0.val) out =
        InnerOuter.cWTableMle Φ m0.val phiF 16 sw ⦄ := by
  rw [zerocheck.c_w_table_mle]
  step with two_pow_spec m0 hm0 as ⟨size, hsize⟩
  step with c_w_table_mle_loop_spec (m₀ := m0.val) w sw size
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize hw hmax hm0 hsize (by simp) (by simp)
    (by intro y hy; simp at hy) (by intro t ht; simp at ht) as ⟨o, hlen, hred, hval⟩
  simp only [cpoly.multilinear.MultilinearEvals.from_values, WP.spec_ok]
  refine ⟨⟨hlen, hred⟩, ?_⟩
  rw [toEvals, InnerOuter.cWTableMle]
  congr 1
  funext j
  rw [hval j.val j.isLt, wTableFlat, dif_pos j.isLt, Fin.eta]

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

/-- The loop of `h_zero`: the values already pushed are the range factors of the
table entries of their indices. -/
theorem h_zero_loop_spec {μ n m₀ : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (size : Std.Usize)
    (values : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize)
    (hw : RepLiftedWitness w sw) (hmax : μ + n * 8 ≤ Usize.max)
    (hm0 : 2 ^ m₀ ≤ Usize.max) (hsize : size.val = 2 ^ m₀) (hi : i.val ≤ 2 ^ m₀)
    (hlen : values.val.length = i.val) (hred : VecReduced values)
    (hval : ∀ t < i.val, toExt (values.val.getD t cpoly.field.Ext4.ZERO) =
      InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t)) :
    zerocheck.h_zero_loop w size values i
      ⦃ o => o.val.length = 2 ^ m₀ ∧ VecReduced o ∧
        ∀ t < 2 ^ m₀, toExt (o.val.getD t cpoly.field.Ext4.ZERO) =
          InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t) ⦄ := by
  rw [zerocheck.h_zero_loop]
  apply loop.spec_decr_nat (fun s => 2 ^ m₀ - s.2.val)
    (fun s => s.2.val ≤ 2 ^ m₀ ∧ s.1.val.length = s.2.val ∧ VecReduced s.1 ∧
      ∀ t < s.2.val, toExt (s.1.val.getD t cpoly.field.Ext4.ZERO) =
        InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t))
  · rintro ⟨v1, i1⟩ ⟨hi1, hlen1, hred1, hval1⟩
    dsimp only at hi1 hlen1 hred1 hval1
    simp only [zerocheck.h_zero_loop.body]
    by_cases hlt : i1 < size
    · rw [if_pos hlt]
      have hilt : i1.val < 2 ^ m₀ := by rw [← hsize]; scalar_tac
      step with w_table_flat_spec (m₀ := m₀) w sw i1 hw hilt hmax as ⟨e, hRe, he⟩
      step with range_product_spec e hRe as ⟨pe, hRpe, hpe⟩
      have hbound : v1.val.length < Usize.max := by omega
      step as ⟨v2, hv2⟩
      step as ⟨i2, hi2⟩
      have hi2n : i2.val = i1.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, ?_, ?_, by scalar_tac⟩
      · rw [hi2n, hv2, List.length_append, hlen1]; simp
      · intro y hy
        rw [hv2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hred1 y h
        · rw [List.mem_singleton.mp h]; exact hRpe
      · intro t ht
        rw [hi2n] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = v1.val.length := by omega
          rw [hteq, hv2, getD_append_eq, hpe, he, hlen1]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = 2 ^ m₀ := by rw [← hsize] at hi1 ⊢; scalar_tac
      exact ⟨by rw [hlen1, heq], hred1, by rw [← heq]; exact hval1⟩
  · exact ⟨hi, hlen, hred, hval⟩

/-- `h_zero` computes `hZero`, the range-constraint block
(`Constraints.lean:204`).

Carries the same `μ + n * 8 ≤ Usize.max` as `w_table_spec`, which it calls. -/
theorem h_zero_spec {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (m0 : Std.Usize)
    (hw : RepLiftedWitness w sw) (hm0 : 2 ^ m0.val ≤ Usize.max)
    (hmax : μ + n * 8 ≤ Usize.max) :
    zerocheck.h_zero w m0
      ⦃ out => WfEvals m0.val out ∧ toEvals (m := m0.val) out =
        InnerOuter.hZero Φ m0.val phiF 16 sw ⦄ := by
  rw [zerocheck.h_zero]
  step with two_pow_spec m0 hm0 as ⟨size, hsize⟩
  step with h_zero_loop_spec (m₀ := m0.val) w sw size
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize hw hmax hm0 hsize (by simp) (by simp)
    (by intro y hy; simp at hy) (by intro t ht; simp at ht) as ⟨o, hlen, hred, hval⟩
  simp only [cpoly.multilinear.MultilinearEvals.from_values, WP.spec_ok]
  refine ⟨⟨hlen, hred⟩, ?_⟩
  rw [toEvals, InnerOuter.hZero]
  refine congrArg Vector.ofFn (funext fun j => ?_)
  rw [hval j.val j.isLt, wTableFlat, dif_pos j.isLt, Fin.eta]

/-- `h_zero_is_zero` **decides** `hZero = 0`, in the pointwise form of
`hZero_eq_zero_iff` (`Constraints.lean:219`).

An `↔`, not an implication: a verifier that rejected everything would satisfy
the accepting direction alone, and the rejection path is the half a broken
implementation still passes. -/
theorem h_zero_is_zero_loop_spec {μ n m₀ : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (size : Std.Usize) (zero : Bool) (i : Std.Usize)
    (hw : RepLiftedWitness w sw) (hmax : μ + n * 8 ≤ Usize.max)
    (hsize : size.val = 2 ^ m₀) (hi : i.val ≤ 2 ^ m₀)
    (hzero : zero = true ↔ ∀ t < i.val, InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t) = 0) :
    zerocheck.h_zero_is_zero_loop w size zero i
      ⦃ b => (b = true ↔
        ∀ t < 2 ^ m₀, InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t) = 0) ⦄ := by
  rw [zerocheck.h_zero_is_zero_loop]
  apply loop.spec_decr_nat (fun s => 2 ^ m₀ - s.2.val)
    (fun s => s.2.val ≤ 2 ^ m₀ ∧
      (s.1 = true ↔ ∀ t < s.2.val, InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t) = 0))
  · rintro ⟨b1, i1⟩ ⟨hi1, hb1⟩
    dsimp only at hi1 hb1
    simp only [zerocheck.h_zero_is_zero_loop.body]
    by_cases hlt : i1 < size
    · rw [if_pos hlt]
      have hilt : i1.val < 2 ^ m₀ := by rw [← hsize]; scalar_tac
      step with w_table_flat_spec (m₀ := m₀) w sw i1 hw hilt hmax as ⟨e, hRe, he⟩
      step with range_product_spec e hRe as ⟨pe, hRpe, hpe⟩
      step with ext_is_zero_spec pe hRpe as ⟨bz, hbz⟩
      rw [hpe, he] at hbz
      by_cases hbzt : bz = true
      · rw [if_pos hbzt]
        simp only [bind_tc_ok]
        step as ⟨i2, hi2⟩
        have hi2n : i2.val = i1.val + 1 := by scalar_tac
        refine ⟨by omega, ?_, by scalar_tac⟩
        rw [hi2n, hb1]
        constructor
        · intro h t ht
          rcases Nat.lt_or_ge t i1.val with htlt | htge
          · exact h t htlt
          · have hti : t = i1.val := by omega
            rw [hti]
            exact hbz.mp hbzt
        · intro h t ht
          exact h t (by omega)
      · rw [if_neg hbzt]
        simp only [bind_tc_ok]
        step as ⟨i2, hi2⟩
        have hi2n : i2.val = i1.val + 1 := by scalar_tac
        refine ⟨by omega, ?_, by scalar_tac⟩
        rw [hi2n]
        simp only [Bool.false_eq_true, false_iff, not_forall]
        exact ⟨i1.val, by omega, fun h => hbzt (hbz.mpr h)⟩
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = 2 ^ m₀ := by rw [← hsize] at hi1 ⊢; scalar_tac
      rw [hb1, heq]
  · exact ⟨hi, hzero⟩

/-- `h_zero_is_zero` **decides** `hZero = 0`.

Carries the same `μ + n * 8 ≤ Usize.max` as `w_table_spec`, which it calls. -/
theorem h_zero_is_zero_spec {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (m0 : Std.Usize)
    (hw : RepLiftedWitness w sw) (hm0 : 2 ^ m0.val ≤ Usize.max)
    (hmax : μ + n * 8 ≤ Usize.max) :
    zerocheck.h_zero_is_zero w m0
      ⦃ b => (b = true ↔ InnerOuter.hZero Φ m0.val phiF 16 sw = 0) ⦄ := by
  rw [zerocheck.h_zero_is_zero]
  step with two_pow_spec m0 hm0 as ⟨size, hsize⟩
  apply spec_mono (h_zero_is_zero_loop_spec (m₀ := m0.val) w sw size true 0#usize hw hmax hsize
    (by simp) (by simp))
  intro b hb
  rw [hb, InnerOuter.hZero_eq_zero_iff,
    forall_cube_iff_forall_flat
      (fun x => InnerOuter.rangeProduct 16 (InnerOuter.wTable Φ m0.val phiF 16 sw x) = 0)]
  constructor
  · intro h t ht
    have := h t ht
    rwa [wTableFlat, dif_pos ht] at this
  · intro h t ht
    rw [wTableFlat, dif_pos ht]
    exact h t ht

/-! ## `zerocheck`: the `H_α` side, through `alphaDefect` -/

/-- The loop of `alpha_tilde`: the accumulator is `α ^ t` after `t` steps. -/
theorem alpha_tilde_loop_spec (alpha : cpoly.field.Ext4) (l : Std.Usize)
    (acc : cpoly.field.Ext4) (t : Std.Usize) (ha : Reduced alpha) (hacc : Reduced acc)
    (ht : t.val ≤ l.val) (hval : toExt acc = toExt alpha ^ t.val) :
    zerocheck.alpha_tilde_loop alpha l acc t
      ⦃ out => Reduced out ∧ toExt out = toExt alpha ^ l.val ⦄ := by
  rw [zerocheck.alpha_tilde_loop]
  apply loop.spec_decr_nat (fun s => l.val - s.2.val)
    (fun s => s.2.val ≤ l.val ∧ Reduced s.1 ∧ toExt s.1 = toExt alpha ^ s.2.val)
  · rintro ⟨a1, t1⟩ ⟨ht1, hR1, hv1⟩
    dsimp only at ht1 hR1 hv1
    simp only [zerocheck.alpha_tilde_loop.body]
    by_cases hlt : t1 < l
    · rw [if_pos hlt]
      step with ext_mul_spec a1 alpha hR1 ha as ⟨a2, hR2, hv2⟩
      step as ⟨t2, ht2⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · exact hR2
      · rw [hv2, hv1, ht2, pow_succ]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : t1.val = l.val := by scalar_tac
      exact ⟨hR1, by rw [hv1, heq]⟩
  · exact ⟨ht, hacc, hval⟩

/-- `alpha_tilde` computes `alphaTilde α ℓ = α ^ ℓ`, the public
column-contraction vector (`Constraints.lean:502`). -/
theorem alpha_tilde_spec (alpha : cpoly.field.Ext4) (l : Std.Usize)
    (ha : Reduced alpha) :
    zerocheck.alpha_tilde alpha l
      ⦃ out => Reduced out ∧ toExt out = InnerOuter.alphaTilde (toExt alpha) l.val ⦄ := by
  rw [InnerOuter.alphaTilde, zerocheck.alpha_tilde]
  exact alpha_tilde_loop_spec alpha l cpoly.field.Ext4.ONE 0#usize ha reduced_ONE
    (by simp) (by simp)

/-- `eq_weight` computes entry `i` of `CMlPolynomialEval.lagrangeBasis τ₁`, the
`m₁`-cube equality weight (`Constraints.lean:845-847`; the bit product does
**not** cancel against `finFunctionFinEquiv`, see brief 4 § Corrections item
1). -/
theorem lagrangeBasis_get_toPoint {m₁ : ℕ} (tau1 : alloc.vec.Vec cpoly.field.Ext4)
    (t : Fin (2 ^ m₁)) :
    (CMlPolynomialEval.lagrangeBasis (Vector.ofFn (toPoint (m := m₁) tau1))).get t
      = ∏ s ∈ Finset.range m₁,
        (if Nat.testBit t.val s then toExt (tau1.val.getD s cpoly.field.Ext4.ZERO)
          else 1 - toExt (tau1.val.getD s cpoly.field.Ext4.ZERO)) := by
  rw [Hachi.lagrangeBasis_get, ← Fin.prod_univ_eq_prod_range
    (fun s => if Nat.testBit t.val s then toExt (tau1.val.getD s cpoly.field.Ext4.ZERO)
      else 1 - toExt (tau1.val.getD s cpoly.field.Ext4.ZERO)) m₁]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.get_ofFn,
    toPoint]

/-- The loop of `eq_weight`: the accumulator is the running bit product, and the
new state component `q` is the running quotient.

`i` is no longer an argument of the extracted loop. The translation carries
`q = i / 2 ^ j` through the state instead of rebuilding `i / 2 ^ j` from a
materialized power, so `i` appears here as a specification-level index tied to
the state by `hq`. That is exactly what retires the old
`hm1 : 2 ^ m₁ ≤ Usize.max`: nothing in this loop forms a power of two any
more (NOTES.md § "Two invented powers of two, removed"). -/
theorem eq_weight_loop_spec {m₁ : ℕ} (tau1 : alloc.vec.Vec cpoly.field.Ext4)
    (i vars : Std.Usize) (acc : cpoly.field.Ext4) (q j : Std.Usize)
    (ht : WfPoint m₁ tau1) (hvars : vars.val = m₁)
    (hj : j.val ≤ m₁) (hacc : Reduced acc) (hq : q.val = i.val / 2 ^ j.val)
    (hval : toExt acc = ∏ s ∈ Finset.range j.val,
      (if Nat.testBit i.val s then toExt (tau1.val.getD s cpoly.field.Ext4.ZERO)
        else 1 - toExt (tau1.val.getD s cpoly.field.Ext4.ZERO))) :
    zerocheck.eq_weight_loop tau1 vars acc q j
      ⦃ out => Reduced out ∧ toExt out = ∏ s ∈ Finset.range m₁,
        (if Nat.testBit i.val s then toExt (tau1.val.getD s cpoly.field.Ext4.ZERO)
          else 1 - toExt (tau1.val.getD s cpoly.field.Ext4.ZERO)) ⦄ := by
  sorry
/-- `eq_weight` computes the `m₁`-cube equality weight.

**Unconditional in the machine model.** The previous statement carried
`hm1 : 2 ^ m₁ ≤ Usize.max`, forced by the bit test building `2 ^ j` as a
checked `usize`. The running quotient forms no power, so the only hypothesis
left is `hi`, which is not an artefact: `.get` needs its index in range, and
that is the specification's own `i < 2 ^ m₁`. -/
theorem eq_weight_spec {m₁ : ℕ} (tau1 : alloc.vec.Vec cpoly.field.Ext4)
    (i : Std.Usize) (ht : WfPoint m₁ tau1) (hi : i.val < 2 ^ m₁) :
    zerocheck.eq_weight tau1 i
      ⦃ out => Reduced out ∧ toExt out =
        (CMlPolynomialEval.lagrangeBasis (Vector.ofFn (toPoint (m := m₁) tau1))).get
          ⟨i.val, hi⟩ ⦄ := by
  sorry

/-- The loop of `below_two_pow`: `q` is the running quotient `i / 2 ^ k`. -/
theorem below_two_pow_loop_spec (i m q k : Std.Usize)
    (hk : k.val ≤ m.val) (hq : q.val = i.val / 2 ^ k.val) :
    zerocheck.below_two_pow_loop m q k
      ⦃ out => out.val = i.val / 2 ^ m.val ⦄ := by
  sorry

/-- `below_two_pow` decides the specification's cube guard `i < 2 ^ m`.

**No hypothesis at all**, which is the point of the item: halving `i` exactly
`m` times cannot fail, so the decision procedure is total at every `m` --
including those where `2 ^ m` exceeds `Usize.max` and the previous
`i < two_pow m` wrapped to zero. An equality of decisions rather than an
implication, per the house rule for decision procedures. -/
theorem below_two_pow_spec (i m : Std.Usize) :
    zerocheck.below_two_pow i m
      ⦃ b => b = true ↔ i.val < 2 ^ m.val ⦄ := by
  sorry
/-- `m_alpha_tilde` computes `mAlphaTilde`, the public constraint matrix at `α`
(`Constraints.lean:517`), in the specification's three cases. -/
theorem poly_matrix_cols_spec {rows cols : ℕ} (a : linalg.PolyMatrix)
    (ha : WfMat rows cols a) (hrows : 0 < rows) :
    linalg.PolyMatrix.cols a ⦃ c => c.val = cols ⦄ := by
  have hlen : a.val.length = rows := ha.1
  have h0lt : 0 < a.val.length := by rw [hlen]; exact hrows
  rw [linalg.PolyMatrix.cols]
  have hne : ¬ (alloc.vec.Vec.len a = 0#usize) := by scalar_tac
  rw [if_neg hne]
  step as ⟨pv, hpv⟩
  have hWpv : WfVec cols pv := by rw [hpv]; exact ha.2 _ (List.getElem_mem h0lt)
  simp only [linalg.PolyVec.len, WP.spec_ok]
  simpa using hWpv.1

/-- `m_alpha_tilde` computes `mAlphaTilde`, in the specification's three cases.

`hmax` is the arity bound the crate's checked `mu + rows * GADGET_DIGITS`
forces; the specification forms the same sum in its second case. -/
theorem m_alpha_tilde_spec {n μ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (i u : Std.Usize) (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (hi : i.val < n) (hmax : μ + n * 8 ≤ Usize.max) :
    zerocheck.m_alpha_tilde s alpha i u
      ⦃ out => Reduced out ∧ toExt out =
        InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨i.val, hi⟩ u.val ⦄ := by
  obtain ⟨hWm, hWy, hmeq, hyeq, hbeq⟩ := hs
  have hgd : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  have hrows : (alloc.vec.Vec.len s.m).val = n := by simpa using hWm.1
  rw [zerocheck.m_alpha_tilde, InnerOuter.mAlphaTilde, rhoDigitCount_eq]
  simp only [ringswitch.RlinStatement.impl.m, linalg.PolyMatrix.rows, bind_tc_ok]
  step with poly_matrix_cols_spec (rows := n) (cols := μ) s.m hWm (by omega) as ⟨mu, hmu⟩
  by_cases hlt : u < mu
  · have hu : u.val < μ := by rw [← hmu]; scalar_tac
    rw [if_pos hlt, dif_pos hu]
    have hrowlt : i.val < s.m.val.length := by rw [hWm.1]; exact hi
    simp only [linalg.PolyMatrix.row]
    step as ⟨pv, hpv⟩
    have hWpv : WfVec μ pv := by rw [hpv]; exact hWm.2 _ (List.getElem_mem hrowlt)
    have hulen : u.val < pv.val.length := by rw [hWpv.1]; exact hu
    simp only [linalg.PolyVec.get]
    step as ⟨r, hr⟩
    have hWr : Wf r := by rw [hr]; exact hWpv.2 _ (List.getElem_mem hulen)
    apply spec_mono (c_eval_at_spec alpha r ha hWr)
    rintro out ⟨hRout, hout⟩
    refine ⟨hRout, ?_⟩
    have hentry : rs.M ⟨i.val, hi⟩ ⟨u.val, hu⟩ = toRq r := by
      rw [← hmeq, toMat_apply]
      show toVec (k := μ) (s.m.val.getD i.val (alloc.vec.Vec.new ring.Rq)) ((⟨u.val, hu⟩ : Fin μ))
        = toRq r
      rw [toVec]
      show toRq ((s.m.val.getD i.val (alloc.vec.Vec.new ring.Rq)).val.getD u.val
        (alloc.vec.Vec.new cpoly.field.Fp)) = toRq r
      rw [List.getD_eq_getElem _ _ hrowlt, ← hpv, List.getD_eq_getElem _ _ hulen, hr]
    rw [hout, hentry]
  · have hu : ¬ u.val < μ := by rw [← hmu]; scalar_tac
    rw [if_neg hlt, dif_neg hu]
    have hmul : (alloc.vec.Vec.len s.m).val * (params.GADGET_DIGITS).val ≤ Usize.max := by
      rw [hrows, hgd]; omega
    step as ⟨i1, hi1⟩
    have hi1v : i1.val = n * 8 := by rw [hi1, hrows, hgd]
    have hadd : mu.val + i1.val ≤ Usize.max := by rw [hmu, hi1v]; omega
    step as ⟨i2, hi2⟩
    have hi2v : i2.val = μ + n * 8 := by rw [hi2, hmu, hi1v]
    by_cases hlt2 : u < i2
    · have hult : u.val < μ + n * 8 := by rw [← hi2v]; scalar_tac
      rw [if_pos hlt2]
      step as ⟨i3, hi3⟩
      have hi3v : i3.val = u.val - μ := by rw [hi3, hmu]
      step as ⟨i4, hi4⟩
      have hi4v : i4.val = (u.val - μ) / 8 := by rw [hi4, hgd, hi3v]
      by_cases heq : i4 = i
      · have hdiv : (u.val - μ) / 8 = i.val := by rw [← hi4v, heq]
        rw [if_pos heq, if_pos ⟨hult, hdiv⟩]
        step as ⟨e, he⟩
        have hev : e.val = (u.val - μ) % 8 := by rw [he, hgd, hi3v]
        step with HachiEquiv.Scheme.base_pow_spec e as ⟨f, hRf, hf⟩
        step with ext_from_base_spec f hRf as ⟨weight, hRw, hweight⟩
        step with c_eval_at_modulus_spec alpha ha as ⟨e1, hRe1, he1⟩
        step with ext_sub_spec cpoly.field.Ext4.ZERO e1 reduced_ZERO hRe1 as ⟨e2, hRe2, he2⟩
        apply spec_mono (ext_mul_spec e2 weight hRe2 hRw)
        rintro out ⟨hRout, hout⟩
        refine ⟨hRout, ?_⟩
        rw [hout, he2, he1, hweight, hf, hev, toExt_ZERO, zero_sub, ← phiF_apply]
        simp only [Nat.cast_ofNat]
      · have hdiv : ¬ ((u.val - μ) / 8 = i.val) := by
          intro h
          exact heq (by scalar_tac)
        rw [if_neg heq, if_neg (by rintro ⟨-, h⟩; exact hdiv h), WP.spec_ok]
        exact ⟨reduced_ZERO, toExt_ZERO⟩
    · have hult : ¬ u.val < μ + n * 8 := by rw [← hi2v]; scalar_tac
      rw [if_neg hlt2, if_neg (by rintro ⟨h, -⟩; exact hult h), WP.spec_ok]
      exact ⟨reduced_ZERO, toExt_ZERO⟩

/-! ### The cube weight, shared by `alpha_public_evals` and `zc_target_alpha` -/

/-- A cube coordinate of a flat index is `1` exactly at a set bit. -/
theorem cube_coord_eq_one_iff {m₁ : ℕ} (t : ℕ) (h : t < 2 ^ m₁) (j : Fin m₁) :
    (finFunctionFinEquiv.symm ⟨t, h⟩ j = 1) ↔ Nat.testBit t j.val := by
  have hval : ((finFunctionFinEquiv.symm (⟨t, h⟩ : Fin (2 ^ m₁)) j : Fin 2) : ℕ)
      = t / 2 ^ (j : ℕ) % 2 := rfl
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq, Fin.ext_iff, hval]
  rfl

/-- The Lagrange weight of a cube point, in the specification's own
`finFunctionFinEquiv` form. -/
theorem lagrangeBasis_get_eq_cube_prod {m₁ : ℕ} (tau1 : alloc.vec.Vec cpoly.field.Ext4)
    (t : ℕ) (h : t < 2 ^ m₁) :
    (CMlPolynomialEval.lagrangeBasis (Vector.ofFn (toPoint (m := m₁) tau1))).get ⟨t, h⟩
      = ∏ j : Fin m₁, (if (finFunctionFinEquiv.symm ⟨t, h⟩) j = 1 then toPoint (m := m₁) tau1 j
        else 1 - toPoint (m := m₁) tau1 j) := by
  rw [Hachi.lagrangeBasis_get]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hbit : ((BitVec.ofFin (⟨t, h⟩ : Fin (2 ^ m₁))).getLsb j = true)
      ↔ (finFunctionFinEquiv.symm ⟨t, h⟩) j = 1 := by
    rw [cube_coord_eq_one_iff]
    simp [BitVec.getLsb_eq_getElem]
  simp only [Vector.get_ofFn]
  exact if_congr hbit rfl rfl

/-- A sum over `Fin n` as a sum over `Finset.range n`, in the `dite` form a loop
invariant produces. -/
theorem sum_fin_eq_sum_range_dite {M : Type*} [AddCommMonoid M] {n : ℕ} (f : Fin n → M) :
    ∑ i : Fin n, f i = ∑ t ∈ Finset.range n, (if ht : t < n then f ⟨t, ht⟩ else 0) := by
  rw [← Fin.sum_univ_eq_sum_range (fun t => if ht : t < n then f ⟨t, ht⟩ else 0) n]
  exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.isLt, Fin.eta]

noncomputable def apTerm {n μ m₁ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ) (alpha : F)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) (u : ℕ) (t : ℕ) : F :=
  if ht : t < n then
    (if h : t < 2 ^ m₁ then
      (CMlPolynomialEval.lagrangeBasis (Vector.ofFn (toPoint (m := m₁) tau1))).get ⟨t, h⟩ *
        InnerOuter.mAlphaTilde Φ phiF 16 rs alpha ⟨t, ht⟩ u
     else 0)
  else 0

/-- The loop of `alpha_public_evals`: the accumulator is the partial row sum.

The `cube` argument is gone: the loop decides the specification's `i < 2 ^ m₁`
guard with `below_two_pow` instead of comparing against a materialized cube
size, so the state is one component shorter and `hm1` is retired. `hmax`
stays -- `m_alpha_tilde` genuinely forms `μ + n · 8` as a `usize`. -/
theorem alpha_public_evals_loop_spec {n μ m₁ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) (idx rows : Std.Usize)
    (sum : cpoly.field.Ext4) (i : Std.Usize)
    (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (htau : WfPoint m₁ tau1) (hmax : μ + n * 8 ≤ Usize.max)
    (hrows : rows.val = n) (hi : i.val ≤ n) (hRsum : Reduced sum)
    (hval : toExt sum = ∑ t ∈ Finset.range i.val,
      apTerm (m₁ := m₁) rs (toExt alpha) tau1 (idx.val / N) t) :
    zerocheck.alpha_public_evals_loop s alpha tau1 idx params.RING_DEGREE rows sum i
      ⦃ out => Reduced out ∧ toExt out =
        ∑ t ∈ Finset.range n, apTerm (m₁ := m₁) rs (toExt alpha) tau1 (idx.val / N) t ⦄ := by
  sorry
/-- `alpha_public_evals` computes `alphaPublicEvals`.

Carries `m_alpha_tilde_spec`'s arity bound `hmax` and no longer carries
`eq_weight_spec`'s retired `hm1`. -/
theorem alpha_public_evals_spec {n μ m₀ m₁ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) (idx : Std.Usize)
    (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (ht : WfPoint m₁ tau1) (hidx : idx.val < 2 ^ m₀)
    (hmax : μ + n * 8 ≤ Usize.max) :
    zerocheck.alpha_public_evals s alpha tau1 idx
      ⦃ out => Reduced out ∧ toExt out =
        InnerOuter.alphaPublicEvals Φ m₀ m₁ phiF 16 rs (toExt alpha)
          (toPoint (m := m₁) tau1) (finFunctionFinEquiv.symm ⟨idx.val, hidx⟩) ⦄ := by
  sorry
/-- Term `t` of the public initial target, as a function of a plain `ℕ`. -/
noncomputable def zcTerm {n μ m₁ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ) (alpha : F)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) (t : ℕ) : F :=
  if ht : t < n then
    (if h : t < 2 ^ m₁ then
      (CMlPolynomialEval.lagrangeBasis (Vector.ofFn (toPoint (m := m₁) tau1))).get ⟨t, h⟩ *
        InnerOuter.cEvalAt phiF alpha (rs.yvec ⟨t, ht⟩).1
     else 0)
  else 0

/-- The loop of `zc_target_alpha`: the accumulator is the partial row sum.

Like `alpha_public_evals_loop`, one component shorter and free of `hm1`: the
cube size is decided rather than built. -/
theorem zc_target_alpha_loop_spec {n μ m₁ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) (rows : Std.Usize)
    (sum : cpoly.field.Ext4) (i : Std.Usize)
    (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (htau : WfPoint m₁ tau1)
    (hrows : rows.val = n) (hi : i.val ≤ n) (hRsum : Reduced sum)
    (hval : toExt sum = ∑ t ∈ Finset.range i.val, zcTerm (m₁ := m₁) rs (toExt alpha) tau1 t) :
    zerocheck.zc_target_alpha_loop s alpha tau1 rows sum i
      ⦃ out => Reduced out ∧ toExt out =
        ∑ t ∈ Finset.range n, zcTerm (m₁ := m₁) rs (toExt alpha) tau1 t ⦄ := by
  sorry
/-- `zc_target_alpha` computes `zcTargetAlpha`.

**Unconditional in the machine model**: this function forms no `usize` that can
overflow. It walks `n` rows, and the cube guard is decided by
`below_two_pow`. -/
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
noncomputable def acTerm (m₀ : ℕ) {n μ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ)
    (sw : InnerOuter.LiftedWitness Φ μ n) (alpha : F) (i : Fin n) (u l : ℕ) : F :=
  InnerOuter.mAlphaTilde Φ phiF 16 rs alpha i u * wTableFlat m₀ sw (N * u + l) *
    InnerOuter.alphaTilde alpha l

/-- A table cell of the contraction, at the flat index the extracted loop
forms. -/
theorem wTable_wTablePoint_flat {n μ m₀ : ℕ} (sw : InnerOuter.LiftedWitness Φ μ n)
    (hmn : (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (u : Fin (μ + n * InnerOuter.rhoDigitCount q 16)) (l : Fin Φ.φ.natDegree) :
    InnerOuter.wTable Φ m₀ phiF 16 sw (InnerOuter.wTablePoint Φ m₀ 16 hmn u l)
      = wTableFlat m₀ sw (N * u.val + l.val) := by
  have hd : Φ.φ.natDegree = N := phi_natDegree
  have hu := u.isLt
  have hl := l.isLt
  have hlt : N * u.val + l.val < 2 ^ m₀ := by
    have h1 : N * (u.val + 1) ≤ N * (μ + n * InnerOuter.rhoDigitCount q 16) :=
      Nat.mul_le_mul_left N (by omega)
    have h2 : N * (μ + n * InnerOuter.rhoDigitCount q 16)
        = (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree := by
      rw [hd]; ring
    have h3 : N * (u.val + 1) = N * u.val + N := by ring
    omega
  rw [wTableFlat, dif_pos hlt, InnerOuter.wTablePoint]
  congr 1
  refine congrArg _ (Fin.ext ?_)
  simp only [hd]

/-- Eq. (22)'s contraction as the double range sum the extracted loops build. -/
theorem alphaContract_eq_range_sum {n μ m₀ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ)
    (sw : InnerOuter.LiftedWitness Φ μ n) (alpha : F) (i : Fin n)
    (hmn : (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree ≤ 2 ^ m₀) :
    InnerOuter.alphaContract Φ m₀ phiF 16 rs alpha hmn
        (InnerOuter.wTable Φ m₀ phiF 16 sw) i
      = ∑ u ∈ Finset.range (μ + n * 8), ∑ l ∈ Finset.range N,
          acTerm m₀ rs sw alpha i u l := by
  rw [InnerOuter.alphaContract, ← rhoDigitCount_eq,
    ← Fin.sum_univ_eq_sum_range
      (fun u => ∑ l ∈ Finset.range N, acTerm m₀ rs sw alpha i u l) _]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hbody : ∀ l : Fin Φ.φ.natDegree,
      InnerOuter.mAlphaTilde Φ phiF 16 rs alpha i (u : ℕ) *
          InnerOuter.wTable Φ m₀ phiF 16 sw (InnerOuter.wTablePoint Φ m₀ 16 hmn u l) *
          InnerOuter.alphaTilde alpha (l : ℕ)
        = acTerm m₀ rs sw alpha i (u : ℕ) (l : ℕ) := by
    intro l
    rw [acTerm, wTable_wTablePoint_flat]
  rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hbody l),
    Fin.sum_univ_eq_sum_range (fun l => acTerm m₀ rs sw alpha i (u : ℕ) l) Φ.φ.natDegree,
    phi_natDegree]

/-- The inner loop of `alpha_contract`: the accumulator collects the `N` column
terms of table row `u`, on top of whatever it started with. -/
theorem alpha_contract_inner_loop_spec {n μ m₀ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (i u l : Std.Usize) (acc : cpoly.field.Ext4) (base : F)
    (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha) (hw : RepLiftedWitness w sw)
    (hi : i.val < n) (hmax : μ + n * 8 ≤ Usize.max) (hm0 : 2 ^ m₀ ≤ Usize.max)
    (hbound : N * u.val + N ≤ 2 ^ m₀) (hl : l.val ≤ N) (hRacc : Reduced acc)
    (hval : toExt acc = base + ∑ t ∈ Finset.range l.val,
      acTerm m₀ rs sw (toExt alpha) ⟨i.val, hi⟩ u.val t) :
    zerocheck.alpha_contract_loop0_loop0 s alpha w i params.RING_DEGREE acc u l
      ⦃ out => Reduced out ∧ toExt out = base + ∑ t ∈ Finset.range N,
        acTerm m₀ rs sw (toExt alpha) ⟨i.val, hi⟩ u.val t ⦄ := by
  have hrd : (params.RING_DEGREE).val = N := params_RING_DEGREE_val
  rw [zerocheck.alpha_contract_loop0_loop0]
  apply loop.spec_decr_nat (fun st => N - st.2.val)
    (fun st => st.2.val ≤ N ∧ Reduced st.1 ∧ toExt st.1 = base + ∑ t ∈ Finset.range st.2.val,
      acTerm m₀ rs sw (toExt alpha) ⟨i.val, hi⟩ u.val t)
  · rintro ⟨a1, l1⟩ ⟨hl1, hR1, hv1⟩
    dsimp only at hl1 hR1 hv1
    simp only [zerocheck.alpha_contract_loop0_loop0.body]
    by_cases hlt : l1 < params.RING_DEGREE
    · rw [if_pos hlt]
      have hl1lt : l1.val < N := by rw [← hrd]; scalar_tac
      step with m_alpha_tilde_spec (n := n) (μ := μ) s rs alpha i u hs ha hi hmax
        as ⟨entry, hRentry, hentry⟩
      have hmul : (params.RING_DEGREE).val * u.val ≤ Usize.max := by rw [hrd]; omega
      step as ⟨j1, hj1⟩
      have hj1v : j1.val = N * u.val := by rw [hj1, hrd]
      have hadd : j1.val + l1.val ≤ Usize.max := by rw [hj1v]; omega
      step as ⟨j2, hj2⟩
      have hj2v : j2.val = N * u.val + l1.val := by rw [hj2, hj1v]
      have hj2lt : j2.val < 2 ^ m₀ := by rw [hj2v]; omega
      step with w_table_flat_spec (m₀ := m₀) w sw j2 hw hj2lt hmax as ⟨cell, hRcell, hcell⟩
      step with ext_mul_spec entry cell hRentry hRcell as ⟨e, hRe, he⟩
      step with alpha_tilde_spec alpha l1 ha as ⟨p, hRp, hp⟩
      step with ext_mul_spec e p hRe hRp as ⟨e2, hRe2, he2⟩
      step with ext_add_spec a1 e2 hR1 hRe2 as ⟨a2, hR2, ha2⟩
      step as ⟨l2, hl2⟩
      have hl2n : l2.val = l1.val + 1 := by scalar_tac
      refine ⟨by omega, hR2, ?_, by omega⟩
      rw [ha2, hv1, he2, he, hentry, hcell, hp, hj2v, hl2n, Finset.sum_range_succ, acTerm,
        add_assoc]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : l1.val = N := by rw [← hrd] at hl1 ⊢; scalar_tac
      exact ⟨hR1, by rw [hv1, heq]⟩
  · exact ⟨hl, hRacc, hval⟩

/-- The outer loop of `alpha_contract`: the accumulator is the partial double
sum over the table rows already processed. -/
theorem alpha_contract_outer_loop_spec {n μ m₀ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (i tableRows u : Std.Usize) (acc : cpoly.field.Ext4)
    (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha) (hw : RepLiftedWitness w sw)
    (hi : i.val < n) (hm0 : 2 ^ m₀ ≤ Usize.max)
    (hmn : (μ + n * 8) * N ≤ 2 ^ m₀) (htr : tableRows.val = μ + n * 8)
    (hu : u.val ≤ μ + n * 8) (hRacc : Reduced acc)
    (hval : toExt acc = ∑ t ∈ Finset.range u.val, ∑ l ∈ Finset.range N,
      acTerm m₀ rs sw (toExt alpha) ⟨i.val, hi⟩ t l) :
    zerocheck.alpha_contract_loop0 s alpha w i params.RING_DEGREE tableRows acc u
      ⦃ out => Reduced out ∧ toExt out = ∑ t ∈ Finset.range (μ + n * 8),
        ∑ l ∈ Finset.range N, acTerm m₀ rs sw (toExt alpha) ⟨i.val, hi⟩ t l ⦄ := by
  have hNpos : 0 < N := by norm_num
  have hmax : μ + n * 8 ≤ Usize.max := by
    have : μ + n * 8 ≤ (μ + n * 8) * N := Nat.le_mul_of_pos_right _ hNpos
    omega
  rw [zerocheck.alpha_contract_loop0]
  apply loop.spec_decr_nat (fun st => μ + n * 8 - st.2.val)
    (fun st => st.2.val ≤ μ + n * 8 ∧ Reduced st.1 ∧ toExt st.1 =
      ∑ t ∈ Finset.range st.2.val, ∑ l ∈ Finset.range N,
        acTerm m₀ rs sw (toExt alpha) ⟨i.val, hi⟩ t l)
  · rintro ⟨a1, u1⟩ ⟨hu1, hR1, hv1⟩
    dsimp only at hu1 hR1 hv1
    simp only [zerocheck.alpha_contract_loop0.body]
    by_cases hlt : u1 < tableRows
    · rw [if_pos hlt]
      have hu1lt : u1.val < μ + n * 8 := by rw [← htr]; scalar_tac
      have hbound : N * u1.val + N ≤ 2 ^ m₀ := by
        have h1 : N * u1.val + N = N * (u1.val + 1) := by ring
        have h2 : N * (u1.val + 1) ≤ N * (μ + n * 8) := Nat.mul_le_mul_left N (by omega)
        have h3 : N * (μ + n * 8) = (μ + n * 8) * N := Nat.mul_comm _ _
        omega
      step with alpha_contract_inner_loop_spec (m₀ := m₀) s rs alpha w sw i u1 0#usize a1
        (∑ t ∈ Finset.range u1.val, ∑ l ∈ Finset.range N,
          acTerm m₀ rs sw (toExt alpha) ⟨i.val, hi⟩ t l)
        hs ha hw hi hmax hm0 hbound (by simp) hR1
        (by rw [hv1, show (0#usize).val = 0 from rfl, Finset.range_zero, Finset.sum_empty,
          add_zero]) as ⟨a2, hR2, ha2⟩
      step as ⟨u2, hu2⟩
      have hu2n : u2.val = u1.val + 1 := by scalar_tac
      refine ⟨by omega, hR2, ?_, by omega⟩
      rw [ha2, hu2n, Finset.sum_range_succ
        (fun t => ∑ l ∈ Finset.range N, acTerm m₀ rs sw (toExt alpha) ⟨i.val, hi⟩ t l) u1.val]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : u1.val = μ + n * 8 := by rw [← htr] at hu1 ⊢; scalar_tac
      exact ⟨hR1, by rw [hv1, heq]⟩
  · exact ⟨hu, hRacc, hval⟩

/-- `alpha_contract` computes `alphaContract` at `T = wTable`.

`hm0` is implied by representability and invisible to the `Vec` model: the
checked flat index `degree * u + ℓ` is the same index the specification's
`wTablePoint` forms, `hmn` bounds it by `2 ^ m₀`, and all `hm0` adds is that
the cube itself fits a `usize` -- which anything holding a `2 ^ m₀`-entry table
already owes. -/
theorem alpha_contract_spec {n μ m₀ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (i : Std.Usize) (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (hw : RepLiftedWitness w sw) (hi : i.val < n)
    (hmn : (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (hm0 : 2 ^ m₀ ≤ Usize.max) :
    zerocheck.alpha_contract s alpha w i
      ⦃ out => Reduced out ∧ toExt out =
        InnerOuter.alphaContract Φ m₀ phiF 16 rs (toExt alpha) hmn
          (InnerOuter.wTable Φ m₀ phiF 16 sw) ⟨i.val, hi⟩ ⦄ := by
  have hmn' : (μ + n * 8) * N ≤ 2 ^ m₀ := by
    rw [← rhoDigitCount_eq, ← phi_natDegree]; exact hmn
  have hNpos : 0 < N := by norm_num
  have hmax : μ + n * 8 ≤ Usize.max := by
    have : μ + n * 8 ≤ (μ + n * 8) * N := Nat.le_mul_of_pos_right _ hNpos
    omega
  have hgd : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  have hrows : (alloc.vec.Vec.len s.m).val = n := by simpa using hs.1.1
  rw [zerocheck.alpha_contract]
  simp only [ringswitch.RlinStatement.impl.m, linalg.PolyMatrix.rows, bind_tc_ok]
  step with poly_matrix_cols_spec (rows := n) (cols := μ) s.m hs.1 (by omega) as ⟨mu, hmu⟩
  have hmul : (alloc.vec.Vec.len s.m).val * (params.GADGET_DIGITS).val ≤ Usize.max := by
    rw [hrows, hgd]; omega
  step as ⟨i1, hi1⟩
  have hi1v : i1.val = n * 8 := by rw [hi1, hrows, hgd]
  have hadd : mu.val + i1.val ≤ Usize.max := by rw [hmu, hi1v]; omega
  step as ⟨tr, htr⟩
  have htrv : tr.val = μ + n * 8 := by rw [htr, hmu, hi1v]
  apply spec_mono (alpha_contract_outer_loop_spec (m₀ := m₀) s rs alpha w sw i tr 0#usize
    cpoly.field.Ext4.ZERO hs ha hw hi hm0 hmn' htrv (by simp) reduced_ZERO
    (by rw [show (0#usize).val = 0 from rfl, Finset.range_zero, Finset.sum_empty, toExt_ZERO]))
  rintro out ⟨hRout, hout⟩
  exact ⟨hRout, by rw [hout, alphaContract_eq_range_sum]⟩

/-- `alpha_defect` computes `alphaDefect` at `T = wTable`
(`Constraints.lean:549`): the contraction minus the public right-hand side. -/
theorem alpha_defect_spec {n μ m₀ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (i : Std.Usize) (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (hw : RepLiftedWitness w sw) (hi : i.val < n)
    (hmn : (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (hm0 : 2 ^ m₀ ≤ Usize.max) :
    zerocheck.alpha_defect s alpha w i
      ⦃ out => Reduced out ∧ toExt out =
        InnerOuter.alphaDefect Φ m₀ phiF 16 rs (toExt alpha) hmn
          (InnerOuter.wTable Φ m₀ phiF 16 sw) ⟨i.val, hi⟩ ⦄ := by
  obtain ⟨hWm, hWy, hmeq, hyeq, hbeq⟩ := hs
  rw [zerocheck.alpha_defect]
  step with alpha_contract_spec (m₀ := m₀) s rs alpha w sw i ⟨hWm, hWy, hmeq, hyeq, hbeq⟩
    ha hw hi hmn hm0 as ⟨c, hRc, hc⟩
  simp only [ringswitch.RlinStatement.impl.yvec, bind_tc_ok]
  have hylen : i.val < s.yvec.val.length := by rw [hWy.1]; exact hi
  simp only [linalg.PolyVec.get]
  step as ⟨r, hr⟩
  have hWr : Wf r := by rw [hr]; exact hWy.2 _ (List.getElem_mem hylen)
  step with c_eval_at_spec alpha r ha hWr as ⟨e1, hRe1, he1⟩
  apply spec_mono (ext_sub_spec c e1 hRc hRe1)
  rintro out ⟨hRout, hout⟩
  refine ⟨hRout, ?_⟩
  have hyentry : rs.yvec ⟨i.val, hi⟩ = toRq r := by
    rw [← hyeq]
    show toRq (s.yvec.val.getD i.val (alloc.vec.Vec.new cpoly.field.Fp)) = toRq r
    rw [List.getD_eq_getElem _ _ hylen, hr]
  rw [hout, hc, he1, ← hyentry, InnerOuter.alphaDefect]

/-- `h_alpha_evals` computes entry `idx` of the `H_α` table, in `alphaDefect`
form. -/
theorem h_alpha_evals_spec {n μ m₀ m₁ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (idx : Std.Usize) (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (hw : RepLiftedWitness w sw)
    (hmn : (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (hm0 : 2 ^ m₀ ≤ Usize.max) :
    zerocheck.h_alpha_evals s alpha w idx
      ⦃ out => Reduced out ∧ toExt out =
        (if h : idx.val < n then
            InnerOuter.alphaDefect Φ m₀ phiF 16 rs (toExt alpha) hmn
              (InnerOuter.wTable Φ m₀ phiF 16 sw) ⟨idx.val, h⟩
          else 0) ⦄ := by
  have hrows : (alloc.vec.Vec.len s.yvec).val = n := by simpa using hs.2.1.1
  rw [zerocheck.h_alpha_evals]
  simp only [ringswitch.RlinStatement.impl.yvec, linalg.PolyVec.len, bind_tc_ok]
  by_cases hlt : idx < alloc.vec.Vec.len s.yvec
  · have hi : idx.val < n := by rw [← hrows]; scalar_tac
    rw [if_pos hlt, dif_pos hi]
    exact alpha_defect_spec (m₀ := m₀) s rs alpha w sw idx hs ha hw hi hmn hm0
  · have hi : ¬ idx.val < n := by rw [← hrows]; scalar_tac
    rw [if_neg hlt, dif_neg hi, WP.spec_ok]
    exact ⟨reduced_ZERO, toExt_ZERO⟩

/-- `hAlphaEvals` at the cube point of a flat index, in `alphaDefect` form: the
flat-index reading of `hAlphaEvals_eq_alphaDefect` (`Constraints.lean:771`). -/
theorem hAlphaEvals_at_flat_index {n μ m₀ m₁ : ℕ}
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : F)
    (sw : InnerOuter.LiftedWitness Φ μ n) (hd : 0 < Φ.φ.natDegree)
    {idx : ℕ} (hidx : idx < 2 ^ m₁)
    (hmn : (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree ≤ 2 ^ m₀) :
    InnerOuter.hAlphaEvals Φ m₁ phiF 16 rs alpha sw (finFunctionFinEquiv.symm ⟨idx, hidx⟩)
      = (if h : idx < n then
          InnerOuter.alphaDefect Φ m₀ phiF 16 rs alpha hmn
            (InnerOuter.wTable Φ m₀ phiF 16 sw) ⟨idx, h⟩
        else 0) := by
  rw [InnerOuter.hAlphaEvals_eq_alphaDefect Φ m₀ m₁ phiF 16 (by norm_num) rs alpha sw hd hmn]
  simp only [Equiv.apply_symm_apply]

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
    (hmn : (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (hm0 : 2 ^ m₀ ≤ Usize.max) :
    zerocheck.h_alpha_evals s alpha w idx
      ⦃ out => Reduced out ∧ toExt out =
        InnerOuter.hAlphaEvals Φ m₁ phiF 16 rs (toExt alpha) sw
          (finFunctionFinEquiv.symm ⟨idx.val, hidx⟩) ⦄ := by
  apply spec_mono (h_alpha_evals_spec (m₀ := m₀) (m₁ := m₁) s rs alpha w sw idx hs ha hw hmn hm0)
  rintro out ⟨hRout, hout⟩
  refine ⟨hRout, ?_⟩
  rw [hout, hAlphaEvals_at_flat_index (m₀ := m₀) rs (toExt alpha) sw hd hidx hmn]

/-- The `H_α` table entry at a flat index, as a function of a plain `ℕ`. -/
noncomputable def hAlphaFlat (m₁ : ℕ) {n μ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ)
    (alpha : F) (sw : InnerOuter.LiftedWitness Φ μ n) (t : ℕ) : F :=
  if h : t < 2 ^ m₁ then
    InnerOuter.hAlphaEvals Φ m₁ phiF 16 rs alpha sw (finFunctionFinEquiv.symm ⟨t, h⟩)
  else 0

/-- `h_alpha_evals`, against the `ℕ`-indexed `H_α` table. -/
theorem h_alpha_evals_flat_spec {n μ m₀ m₁ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (idx : Std.Usize) (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (hw : RepLiftedWitness w sw) (hd : 0 < Φ.φ.natDegree)
    (hidx : idx.val < 2 ^ m₁)
    (hmn : (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (hm0 : 2 ^ m₀ ≤ Usize.max) :
    zerocheck.h_alpha_evals s alpha w idx
      ⦃ out => Reduced out ∧ toExt out = hAlphaFlat m₁ rs (toExt alpha) sw idx.val ⦄ := by
  apply spec_mono (h_alpha_evals_eq_hAlphaEvals_spec (m₀ := m₀) (m₁ := m₁) s rs alpha w sw idx
    hs ha hw hd hidx hmn hm0)
  rintro out ⟨hRout, hout⟩
  exact ⟨hRout, by rw [hout, hAlphaFlat, dif_pos hidx]⟩

/-- The loop of `h_alpha`: the values already pushed are the `H_α` entries of
their indices. -/
theorem h_alpha_loop_spec {n μ m₀ m₁ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (size : Std.Usize) (values : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize)
    (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (hw : RepLiftedWitness w sw) (hd : 0 < Φ.φ.natDegree)
    (hmn : (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (hm0 : 2 ^ m₀ ≤ Usize.max) (hmx : 2 ^ m₁ ≤ Usize.max)
    (hsize : size.val = 2 ^ m₁) (hi : i.val ≤ 2 ^ m₁)
    (hlen : values.val.length = i.val) (hred : VecReduced values)
    (hval : ∀ t < i.val, toExt (values.val.getD t cpoly.field.Ext4.ZERO) =
      hAlphaFlat m₁ rs (toExt alpha) sw t) :
    zerocheck.h_alpha_loop s alpha w size values i
      ⦃ o => o.val.length = 2 ^ m₁ ∧ VecReduced o ∧
        ∀ t < 2 ^ m₁, toExt (o.val.getD t cpoly.field.Ext4.ZERO) =
          hAlphaFlat m₁ rs (toExt alpha) sw t ⦄ := by
  rw [zerocheck.h_alpha_loop]
  apply loop.spec_decr_nat (fun st => 2 ^ m₁ - st.2.val)
    (fun st => st.2.val ≤ 2 ^ m₁ ∧ st.1.val.length = st.2.val ∧ VecReduced st.1 ∧
      ∀ t < st.2.val, toExt (st.1.val.getD t cpoly.field.Ext4.ZERO) =
        hAlphaFlat m₁ rs (toExt alpha) sw t)
  · rintro ⟨v1, i1⟩ ⟨hi1, hlen1, hred1, hval1⟩
    dsimp only at hi1 hlen1 hred1 hval1
    simp only [zerocheck.h_alpha_loop.body]
    by_cases hlt : i1 < size
    · rw [if_pos hlt]
      have hilt : i1.val < 2 ^ m₁ := by rw [← hsize]; scalar_tac
      step with h_alpha_evals_flat_spec (m₀ := m₀) (m₁ := m₁) s rs alpha w sw i1
        hs ha hw hd hilt hmn hm0 as ⟨e, hRe, he⟩
      have hbound : v1.val.length < Usize.max := by omega
      step as ⟨v2, hv2⟩
      step as ⟨i2, hi2⟩
      have hi2n : i2.val = i1.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, ?_, ?_, by scalar_tac⟩
      · rw [hi2n, hv2, List.length_append, hlen1]; simp
      · intro y hy
        rw [hv2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hred1 y h
        · rw [List.mem_singleton.mp h]; exact hRe
      · intro t ht
        rw [hi2n] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = v1.val.length := by omega
          rw [hteq, hv2, getD_append_eq, he, hlen1]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = 2 ^ m₁ := by rw [← hsize] at hi1 ⊢; scalar_tac
      exact ⟨by rw [hlen1, heq], hred1, by rw [← heq]; exact hval1⟩
  · exact ⟨hi, hlen, hred, hval⟩

/-- `h_alpha` computes `hAlpha`'s Lagrange-form block (`Constraints.lean:213`),
through the same bridge. -/
theorem h_alpha_spec {n μ m₀ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (m1 : Std.Usize) (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (hw : RepLiftedWitness w sw) (hd : 0 < Φ.φ.natDegree)
    (hm1 : 2 ^ m1.val ≤ Usize.max)
    (hmn : (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (hm0 : 2 ^ m₀ ≤ Usize.max) :
    zerocheck.h_alpha s alpha w m1
      ⦃ out => WfEvals m1.val out ∧ toEvals (m := m1.val) out =
        InnerOuter.hAlpha Φ m1.val phiF 16 rs (toExt alpha) sw ⦄ := by
  rw [zerocheck.h_alpha]
  step with two_pow_spec m1 hm1 as ⟨size, hsize⟩
  step with h_alpha_loop_spec (m₀ := m₀) (m₁ := m1.val) s rs alpha w sw size
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize hs ha hw hd hmn hm0 hm1 hsize (by simp)
    (by simp) (by intro y hy; simp at hy) (by intro t ht; simp at ht)
    as ⟨o, hlen, hred, hval⟩
  simp only [cpoly.multilinear.MultilinearEvals.from_values, WP.spec_ok]
  refine ⟨⟨hlen, hred⟩, ?_⟩
  rw [toEvals, InnerOuter.hAlpha]
  refine congrArg Vector.ofFn (funext fun j => ?_)
  rw [hval j.val j.isLt, hAlphaFlat, dif_pos j.isLt, Fin.eta]

/-- The loop of `h_alpha_is_zero`: the flag is the running conjunction. -/
theorem h_alpha_is_zero_loop_spec {n μ m₀ m₁ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (size : Std.Usize) (zero : Bool) (i : Std.Usize)
    (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (hw : RepLiftedWitness w sw) (hd : 0 < Φ.φ.natDegree)
    (hmn : (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (hm0 : 2 ^ m₀ ≤ Usize.max)
    (hsize : size.val = 2 ^ m₁) (hi : i.val ≤ 2 ^ m₁)
    (hzero : zero = true ↔ ∀ t < i.val, hAlphaFlat m₁ rs (toExt alpha) sw t = 0) :
    zerocheck.h_alpha_is_zero_loop s alpha w size zero i
      ⦃ b => (b = true ↔ ∀ t < 2 ^ m₁, hAlphaFlat m₁ rs (toExt alpha) sw t = 0) ⦄ := by
  rw [zerocheck.h_alpha_is_zero_loop]
  apply loop.spec_decr_nat (fun st => 2 ^ m₁ - st.2.val)
    (fun st => st.2.val ≤ 2 ^ m₁ ∧
      (st.1 = true ↔ ∀ t < st.2.val, hAlphaFlat m₁ rs (toExt alpha) sw t = 0))
  · rintro ⟨b1, i1⟩ ⟨hi1, hb1⟩
    dsimp only at hi1 hb1
    simp only [zerocheck.h_alpha_is_zero_loop.body]
    by_cases hlt : i1 < size
    · rw [if_pos hlt]
      have hilt : i1.val < 2 ^ m₁ := by rw [← hsize]; scalar_tac
      step with h_alpha_evals_flat_spec (m₀ := m₀) (m₁ := m₁) s rs alpha w sw i1
        hs ha hw hd hilt hmn hm0 as ⟨e, hRe, he⟩
      step with ext_is_zero_spec e hRe as ⟨bz, hbz⟩
      rw [he] at hbz
      by_cases hbzt : bz = true
      · rw [if_pos hbzt]
        step as ⟨i2, hi2⟩
        have hi2n : i2.val = i1.val + 1 := by scalar_tac
        refine ⟨by omega, ?_, by scalar_tac⟩
        rw [hi2n, hb1]
        constructor
        · intro h t ht
          rcases Nat.lt_or_ge t i1.val with htlt | htge
          · exact h t htlt
          · have hti : t = i1.val := by omega
            rw [hti]
            exact hbz.mp hbzt
        · intro h t ht
          exact h t (by omega)
      · rw [if_neg hbzt]
        step as ⟨i2, hi2⟩
        have hi2n : i2.val = i1.val + 1 := by scalar_tac
        refine ⟨by omega, ?_, by scalar_tac⟩
        rw [hi2n]
        simp only [Bool.false_eq_true, false_iff, not_forall]
        exact ⟨i1.val, by omega, fun h => hbzt (hbz.mpr h)⟩
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = 2 ^ m₁ := by rw [← hsize] at hi1 ⊢; scalar_tac
      rw [hb1, heq]
  · exact ⟨hi, hzero⟩

/-- `h_alpha_is_zero` **decides** `hAlpha = 0`, in the pointwise form of
`hAlpha_eq_zero_iff` (`Constraints.lean:233`). An `↔`, for the reason
`h_zero_is_zero_spec` gives. -/
theorem h_alpha_is_zero_spec {n μ m₀ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (m1 : Std.Usize) (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (hw : RepLiftedWitness w sw) (hd : 0 < Φ.φ.natDegree)
    (hm1 : 2 ^ m1.val ≤ Usize.max)
    (hmn : (μ + n * InnerOuter.rhoDigitCount q 16) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (hm0 : 2 ^ m₀ ≤ Usize.max) :
    zerocheck.h_alpha_is_zero s alpha w m1
      ⦃ b => (b = true ↔
        InnerOuter.hAlpha Φ m1.val phiF 16 rs (toExt alpha) sw = 0) ⦄ := by
  rw [zerocheck.h_alpha_is_zero]
  step with two_pow_spec m1 hm1 as ⟨size, hsize⟩
  apply spec_mono (h_alpha_is_zero_loop_spec (m₀ := m₀) (m₁ := m1.val) s rs alpha w sw size
    true 0#usize hs ha hw hd hmn hm0 hsize (by simp) (by simp))
  intro b hb
  rw [hb, InnerOuter.hAlpha_eq_zero_iff,
    forall_cube_iff_forall_flat
      (fun x => InnerOuter.hAlphaEvals Φ m1.val phiF 16 rs (toExt alpha) sw x = 0)]
  constructor
  · intro h t ht
    have := h t ht
    rwa [hAlphaFlat, dif_pos ht] at this
  · intro h t ht
    rw [hAlphaFlat, dif_pos ht]
    exact h t ht

end HachiEquiv.ZeroCheck
