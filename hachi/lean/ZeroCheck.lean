/-
Target 4's zero-check link, **proved and promoted** (2026-09-09, Aristotle
session `2266ab16`, thirteen obligations to zero together with `EndPiece.lean`).

Twenty-five headline specs cover the sixteen `zerocheck` items and the three
`ringswitch` items the α side introduced (`c_eval_at`, `c_eval_at_modulus`,
`RlinStatement`); `Check.lean` § 4 prints their axioms. The file was staged in
`lean-wip/` on `lean-wip/Ext.lean`'s extension-field layer and promoted with it;
that history is in `lean-wip/README.md`. Since Stage 6 iteration 1 (2026-09-14)
it also carries the specs of the optimized bodies: the running-power `c_eval_at`
(`(acc, pw, k)` loops), the row-hoisted table builders (`w_table_row`,
`c_w_table_mle_values`, the nested `h_zero` / `h_zero_is_zero` loops, the layer
fold of `w_table_mle_eval`) and the hoisted α-side tables (`alpha_pow_table`,
`eq_weight_table`, `m_alpha_table`), each stated against the same ArkLib
definition as before; the pure algebra those bodies rest on is in
`lean/Opt.lean`, which imports this file -- so the loop proofs here re-establish
their invariants directly and the pure row lemma (`wTableRow`,
`wTableFlat_eq_row`) lives here.

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

/-- Well-formedness of a **base-field** Lagrange-form table: `2 ^ m` reduced
words. The `Fp` counterpart of `WfEvals`, and the invariant round 0 of the
sumcheck carries (candidate I): before the first challenge the whole table is
`φF` of witness coefficients, so it is held as a `Vec<Fp>` and folded in
`ZMod q`. -/
def WfEvalsFp (m : ℕ) (t : alloc.vec.Vec cpoly.field.Fp) : Prop :=
  t.val.length = 2 ^ m ∧ ∀ a ∈ t.val, Red a

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

/-- `φF` is injective, so it reflects zero: a ring homomorphism out of a
division ring (`ZMod q` is a field, `Ext.lean:57`'s `Fact (Nat.Prime q)`) into a
nontrivial semiring has trivial kernel. This is what lets the extracted
`h_zero_is_zero` test `range_product_base(…).is_zero()` in `Fp`
(`fp_is_zero_spec`, `lean/Ext.lean:212`) rather than embedding first and calling
`Ext4::is_zero` -- candidate G's verdict half. Moved here from `lean/Opt.lean`
so that `range_product_base_spec` below can use it; `Opt.lean` still reaches it
through `open HachiEquiv.ZeroCheck`. -/
theorem phiF_eq_zero_iff (y : ZMod q) : phiF y = 0 ↔ y = 0 :=
  map_eq_zero_iff phiF phiF.injective

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

/-- A represented `Rq` has `CPolynomial` degree strictly below `N`, which is what
licenses reading its evaluation as the `N`-term power sum. -/
theorem toRq_natDegree_lt (p : ring.Rq) : (toRq p).1.natDegree < N := by
  have h := Rq.natDegree_val_toPoly_lt' Φ (by rw [phi_natDegree]; norm_num) (toRq p)
  rw [← phi_natDegree, CPolynomial.natDegree_toPoly]
  exact h

/-- The loop of `c_eval_at`: the state is `(acc, pw, k)` with `acc` the partial
power sum and `pw` the *running power* `α ^ k`, advanced by one multiplication
per step instead of recomputed per term. -/
theorem c_eval_at_loop_spec (alpha : cpoly.field.Ext4) (p : ring.Rq)
    (acc : cpoly.field.Ext4) (pw : cpoly.field.Ext4) (k : Std.Usize)
    (ha : Reduced alpha) (hp : Wf p) (hacc : Reduced acc) (hpw : Reduced pw)
    (hk : k.val ≤ N) (hpwv : toExt pw = toExt alpha ^ k.val)
    (hval : toExt acc = ∑ l ∈ Finset.range k.val, phiF (coeffK p l) * toExt alpha ^ l) :
    ringswitch.c_eval_at_loop alpha p params.RING_DEGREE acc pw k
      ⦃ out => Reduced out ∧ toExt out =
        ∑ l ∈ Finset.range N, phiF (coeffK p l) * toExt alpha ^ l ⦄ := by
  have hrd : (params.RING_DEGREE).val = N := params_RING_DEGREE_val
  rw [ringswitch.c_eval_at_loop]
  apply loop.spec_decr_nat (fun s => N - s.2.2.val)
    (fun s => s.2.2.val ≤ N ∧ Reduced s.1 ∧ Reduced s.2.1 ∧
      toExt s.2.1 = toExt alpha ^ s.2.2.val ∧
      toExt s.1 = ∑ l ∈ Finset.range s.2.2.val, phiF (coeffK p l) * toExt alpha ^ l)
  · rintro ⟨a1, w1, k1⟩ ⟨hk1, hR1, hRw1, hwv1, hv1⟩
    dsimp only at hk1 hR1 hRw1 hwv1 hv1
    simp only [ringswitch.c_eval_at_loop.body]
    by_cases hlt : k1 < params.RING_DEGREE
    · rw [if_pos hlt]
      have hk1lt : k1.val < N := by scalar_tac
      step with RqBridge.coeff_spec p k1 hp as ⟨f, hRf, hf⟩
      rw [toRq_coeff, if_pos hk1lt] at hf
      step with ext_from_base_spec f hRf as ⟨c, hRc, hc⟩
      step with ext_mul_spec c w1 hRc hRw1 as ⟨e, hRe, he⟩
      step with ext_add_spec a1 e hR1 hRe as ⟨a2, hR2, ha2⟩
      step with ext_mul_spec w1 alpha hRw1 ha as ⟨w2, hRw2, hw2⟩
      step as ⟨k2, hk2⟩
      have hk2n : k2.val = k1.val + 1 := by scalar_tac
      refine ⟨by scalar_tac, hR2, hRw2, ?_, ?_, by scalar_tac⟩
      · rw [hw2, hwv1, hk2n, pow_succ]
      · rw [ha2, hv1, he, hc, hf, hwv1, hk2n, Finset.sum_range_succ, phiF_apply]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = N := by scalar_tac
      exact ⟨hR1, by rw [hv1, heq]⟩
  · exact ⟨hk, hacc, hpw, hpwv, hval⟩

/-- `c_eval_at` computes `cEvalAt`: a `Zq[X]` polynomial at a point of the
extension field (`RingSwitch/Reduction.lean:444`).

`cEvalAt φF a p = p.eval₂ φF a`, and `eval₂` is the *power sum*
`foldl (acc + f a * x ^ i)` (`CompPoly/Univariate/Basic.lean:251`), not Horner
-- which CompPoly offers separately and this definition does not use. The
extracted body is the translation of `HachiEquiv.Opt.c_eval_at.opt`
(`lean/Opt.lean`): that same sum with the power carried in the loop state --
`pw` is `α ^ k` at the top of iteration `k` -- rather than recomputed per term.
The loop starts at `pw = 1 = α ^ 0`. -/
theorem c_eval_at_spec (alpha : cpoly.field.Ext4) (p : ring.Rq)
    (ha : Reduced alpha) (hp : Wf p) :
    ringswitch.c_eval_at alpha p
      ⦃ out => Reduced out ∧ toExt out = InnerOuter.cEvalAt phiF (toExt alpha) (toRq p).1 ⦄ := by
  rw [ringswitch.c_eval_at, InnerOuter.cEvalAt_eq_sum_range phiF (toExt alpha) (toRq_natDegree_lt p)]
  apply spec_mono (c_eval_at_loop_spec alpha p cpoly.field.Ext4.ZERO cpoly.field.Ext4.ONE
    0#usize ha hp reduced_ZERO reduced_ONE (by simp) (by simp) (by simp))
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

/-- The modulus evaluation in closed form: `Φ.φ = X^N + 1` has coefficient `1`
at `0` and at `N` and `0` everywhere else (`phi_coeff`), so the specification's
`N + 1`-term sum collapses to `α ^ N + 1`.

This is `HachiEquiv.Opt.c_eval_at_modulus.opt_eq_spec` (`lean/Opt.lean`) with
the loop stripped off; it is re-proved here because `Opt.lean` imports this
file and so cannot be imported back. -/
theorem cEvalAt_phi_eq_pow_add_one (a : F) :
    InnerOuter.cEvalAt phiF a Φ.φ = a ^ N + 1 := by
  have hdeg : Φ.φ.natDegree < N + 1 := by rw [phi_natDegree]; exact Nat.lt_succ_self _
  have hN0 : N ≠ 0 := by norm_num [N]
  have hcN : Φ.φ.coeff N = 1 := by rw [phi_coeff]; simp [hN0]
  have htail : phiF (Φ.φ.coeff N) * a ^ N = a ^ N := by rw [hcN, map_one, one_mul]
  have hhead : ∑ l ∈ Finset.range N, phiF (Φ.φ.coeff l) * a ^ l = 1 := by
    have hmem : (0 : ℕ) ∈ Finset.range N := Finset.mem_range.mpr (by norm_num [N])
    have hzero : ∀ l ∈ Finset.range N, l ≠ 0 → phiF (Φ.φ.coeff l) * a ^ l = 0 := by
      intro l hl hl0
      have hlN : l ≠ N := Nat.ne_of_lt (Finset.mem_range.mp hl)
      rw [phi_coeff]
      simp [hl0, hlN]
    rw [Finset.sum_eq_single_of_mem 0 hmem hzero, phi_coeff]
    simp
  rw [InnerOuter.cEvalAt_eq_sum_range phiF a hdeg, Finset.sum_range_succ, hhead, htail]
  exact add_comm _ _

/-- The loop of `c_eval_at_modulus`: a bare running power over the state
`(pw, k)`, so the accumulator *is* `α ^ k` and the loop returns `α ^ N`. No
coefficient branch and no `from_base`: the two non-zero terms of the modulus'
`eval₂` sum are handled by the caller's single addition. -/
theorem c_eval_at_modulus_loop_spec (alpha : cpoly.field.Ext4) (pw : cpoly.field.Ext4)
    (k : Std.Usize) (ha : Reduced alpha) (hpw : Reduced pw) (hk : k.val ≤ N)
    (hpwv : toExt pw = toExt alpha ^ k.val) :
    ringswitch.c_eval_at_modulus_loop alpha params.RING_DEGREE pw k
      ⦃ out => Reduced out ∧ toExt out = toExt alpha ^ N ⦄ := by
  have hrd : (params.RING_DEGREE).val = N := params_RING_DEGREE_val
  rw [ringswitch.c_eval_at_modulus_loop]
  apply loop.spec_decr_nat (fun s => N - s.2.val)
    (fun s => s.2.val ≤ N ∧ Reduced s.1 ∧ toExt s.1 = toExt alpha ^ s.2.val)
  · rintro ⟨w1, k1⟩ ⟨hk1, hR1, hv1⟩
    dsimp only at hk1 hR1 hv1
    simp only [ringswitch.c_eval_at_modulus_loop.body]
    by_cases hlt : k1 < params.RING_DEGREE
    · rw [if_pos hlt]
      step with ext_mul_spec w1 alpha hR1 ha as ⟨w2, hR2, hw2⟩
      step as ⟨k2, hk2⟩
      have hk2n : k2.val = k1.val + 1 := by scalar_tac
      refine ⟨by scalar_tac, hR2, ?_, by scalar_tac⟩
      rw [hw2, hv1, hk2n, pow_succ]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = N := by scalar_tac
      exact ⟨hR1, by rw [hv1, heq]⟩
  · exact ⟨hk, hpw, hpwv⟩

/-- `c_eval_at_modulus` computes `cEvalAt φF α Φ.φ`, the `φ(α)` factor of
`mAlphaTilde` (`ZeroCheck/Constraints.lean:519`).

A separate entry point because `Φ.φ = X^d + 1` has `d + 1` coefficients and no
`Rq` can hold it -- the invariant is exactly `d` of them. The extracted body is
the translation of `HachiEquiv.Opt.c_eval_at_modulus.opt` (`lean/Opt.lean`): a
running power of `N` multiplications, then one addition of `1`, which
`cEvalAt_phi_eq_pow_add_one` matches to the specification's `N + 1`-term sum. -/
theorem c_eval_at_modulus_spec (alpha : cpoly.field.Ext4) (ha : Reduced alpha) :
    ringswitch.c_eval_at_modulus alpha
      ⦃ out => Reduced out ∧ toExt out = InnerOuter.cEvalAt phiF (toExt alpha) Φ.φ ⦄ := by
  rw [ringswitch.c_eval_at_modulus]
  step with c_eval_at_modulus_loop_spec alpha cpoly.field.Ext4.ONE 0#usize ha reduced_ONE
    (by simp) (by simp) as ⟨pw, hRpw, hpwv⟩
  step with ext_add_spec pw cpoly.field.Ext4.ONE hRpw reduced_ONE as ⟨out, hRout, hout⟩
  refine ⟨hRout, ?_⟩
  rw [hout, hpwv, toExt_ONE, cEvalAt_phi_eq_pow_add_one]

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

/-- The loop of `range_product`: ascending `j`, one extension multiplication
per step by `v² - j²` (candidate F's contraction of the two symmetric factors,
`(v - j)(v + j) = v² - j²`). `v` is not a component of the extracted loop
state -- only the square `v2` is, which is why `v` is an ordinary parameter here
and enters only through `hv2v` and the invariant `hval`, and why it needs no
`Reduced v`: only `toExt v` is ever mentioned (the sibling
`range_product_base_loop_spec` drops `Red c` for the same reason).

`j * j` is a *checked* `u64` product, and the guard `j < GADGET_BASE = 16` is
what discharges it (`j · j ≤ 225`); `Fp::new` then never actually reduces, but
the model still goes through `fp_new_spec`. The exit branch is the whole
algebraic content: `Finset.Ico 1 16 = Finset.Icc 1 15` plus the pairwise
identity, which is `ring` after `Nat.cast_mul`. -/
theorem range_product_loop_spec (v v2 acc : cpoly.field.Ext4)
    (j : Std.U64) (hv2 : Reduced v2) (hacc : Reduced acc)
    (hj : 1 ≤ j.val) (hjle : j.val ≤ 16) (hv2v : toExt v2 = toExt v * toExt v)
    (hval : toExt acc = toExt v *
      ∏ k ∈ Finset.Ico (1 : ℕ) j.val, (toExt v * toExt v - ((k * k : ℕ) : F))) :
    zerocheck.range_product_loop params.GADGET_BASE v2 acc j
      ⦃ out => Reduced out ∧ toExt out = InnerOuter.rangeProduct 16 (toExt v) ⦄ := by
  have hgb : (params.GADGET_BASE).val = 16 := by simp [params.GADGET_BASE]
  rw [zerocheck.range_product_loop]
  apply loop.spec_decr_nat (fun s => 16 - s.2.val)
    (fun s => 1 ≤ s.2.val ∧ s.2.val ≤ 16 ∧ Reduced s.1 ∧ toExt s.1 = toExt v *
      ∏ k ∈ Finset.Ico (1 : ℕ) s.2.val, (toExt v * toExt v - ((k * k : ℕ) : F)))
  · rintro ⟨a1, j1⟩ ⟨hj1, hj1le, hR1, hv1⟩
    dsimp only at hj1 hj1le hR1 hv1
    simp only [zerocheck.range_product_loop.body]
    by_cases hlt : j1 < params.GADGET_BASE
    · rw [if_pos hlt]
      have hj1lt : j1.val < 16 := by scalar_tac
      step as ⟨sq, hsq⟩
      step with fp_new_spec sq as ⟨f, hRf, hf⟩
      step with ext_from_base_spec f hRf as ⟨sc, hRsc, hsc⟩
      step with ext_sub_spec v2 sc hv2 hRsc as ⟨d, hRd, hd⟩
      step with ext_mul_spec a1 d hR1 hRd as ⟨a2, hR2, ha2⟩
      step as ⟨j2, hj2⟩
      have hj2n : j2.val = j1.val + 1 := by scalar_tac
      have hfv : toK f = ((j1.val * j1.val : ℕ) : ZMod q) := by
        rw [hf]; exact congrArg (fun t : ℕ => (t : ZMod q)) (by scalar_tac)
      have hscv : toExt sc = ((j1.val * j1.val : ℕ) : F) := by
        rw [hsc, hfv, ofBase_natCast]
      refine ⟨by scalar_tac, by scalar_tac, hR2, ?_, by scalar_tac⟩
      rw [ha2, hv1, hd, hv2v, hscv, hj2n, Finset.prod_Ico_succ_top hj1]
      ring
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : j1.val = 16 := by scalar_tac
      have hIco : Finset.Ico (1 : ℕ) 16 = Finset.Icc 1 (16 - 1) := by decide
      refine ⟨hR1, ?_⟩
      rw [hv1, heq, InnerOuter.rangeProduct, hIco]
      refine congrArg (fun t => toExt v * t) (Finset.prod_congr rfl ?_)
      intro k _
      rw [Nat.cast_mul]
      ring
  · exact ⟨hj, hjle, hacc, hval⟩

/-- `range_product` computes `rangeProduct` at the crate's gadget base. -/
theorem range_product_spec (v : cpoly.field.Ext4) (hv : Reduced v) :
    zerocheck.range_product v
      ⦃ out => Reduced out ∧ toExt out = InnerOuter.rangeProduct 16 (toExt v) ⦄ := by
  rw [zerocheck.range_product]
  step with ext_mul_spec v v hv hv as ⟨v2, hRv2, hv2v⟩
  exact range_product_loop_spec v v2 v 1#u64 hRv2 hv (by simp) (by simp) hv2v (by simp)

/-- The base-field product, embedded, is the specification's extension range
factor at the embedded argument: `φF` is a bundled `RingHom`, so the leading
factor, the product, the two symmetric differences and the natural-number
literals all commute with it. This is the whole algebraic content of candidate
G, restated here because `lean/Opt.lean` imports this file and not the other way
round. -/
theorem phiF_rangeProduct_prod (b : ℕ) (x : ZMod q) :
    phiF (x * ∏ j ∈ Finset.Icc 1 (b - 1), ((x - (j : ZMod q)) * (x + (j : ZMod q))))
      = InnerOuter.rangeProduct b (phiF x) := by
  rw [InnerOuter.rangeProduct, map_mul, map_prod]
  refine congrArg (fun t => phiF x * t) (Finset.prod_congr rfl ?_)
  intro j _
  rw [map_mul, map_sub, map_add, map_natCast]

/-- The loop of `range_product_base`: ascending `j`, one base-field
multiplication per step by `c² - j²` (candidate F's contraction of the two
symmetric factors, computed in `Fp` -- candidate G). `c` is not a component of
the extracted loop state; it enters only through `hc2v` and the invariant
`hval`, which is why it is an ordinary parameter here -- and why it needs no
`Red c`: only `toK c` is ever mentioned.

`j * j` is a *checked* `u64` product, and the guard `j < GADGET_BASE = 16` is
what discharges it (`j · j ≤ 225`); `Fp::new` then never actually reduces, but
the model still goes through `fp_new_spec`. -/
theorem range_product_base_loop_spec (c c2 acc : cpoly.field.Fp) (j : Std.U64)
    (hc2 : Red c2) (hacc : Red acc) (hj : 1 ≤ j.val) (hjle : j.val ≤ 16)
    (hc2v : toK c2 = toK c * toK c)
    (hval : toK acc = toK c *
      ∏ k ∈ Finset.Ico (1 : ℕ) j.val, (toK c * toK c - ((k * k : ℕ) : ZMod q))) :
    zerocheck.range_product_base_loop params.GADGET_BASE c2 acc j
      ⦃ out => Red out ∧ toK out = toK c *
        ∏ k ∈ Finset.Icc (1 : ℕ) 15, ((toK c - (k : ZMod q)) * (toK c + (k : ZMod q))) ⦄ := by
  have hgb : (params.GADGET_BASE).val = 16 := by simp [params.GADGET_BASE]
  rw [zerocheck.range_product_base_loop]
  apply loop.spec_decr_nat (fun s => 16 - s.2.val)
    (fun s => 1 ≤ s.2.val ∧ s.2.val ≤ 16 ∧ Red s.1 ∧ toK s.1 = toK c *
      ∏ k ∈ Finset.Ico (1 : ℕ) s.2.val, (toK c * toK c - ((k * k : ℕ) : ZMod q)))
  · rintro ⟨a1, j1⟩ ⟨hj1, hj1le, hR1, hv1⟩
    dsimp only at hj1 hj1le hR1 hv1
    simp only [zerocheck.range_product_base_loop.body]
    by_cases hlt : j1 < params.GADGET_BASE
    · rw [if_pos hlt]
      have hj1lt : j1.val < 16 := by scalar_tac
      step as ⟨sq, hsq⟩
      step with fp_new_spec sq as ⟨f, hRf, hf⟩
      step with fp_sub_spec c2 f hc2 hRf as ⟨d, hRd, hd⟩
      step with fp_mul_spec a1 d hR1 hRd as ⟨a2, hR2, ha2⟩
      step as ⟨j2, hj2⟩
      have hj2n : j2.val = j1.val + 1 := by scalar_tac
      have hfv : toK f = ((j1.val * j1.val : ℕ) : ZMod q) := by
        rw [hf]; exact congrArg (fun t : ℕ => (t : ZMod q)) (by scalar_tac)
      refine ⟨by scalar_tac, by scalar_tac, hR2, ?_, by scalar_tac⟩
      rw [ha2, hv1, hd, hc2v, hfv, hj2n, Finset.prod_Ico_succ_top (by omega)]
      ring
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : j1.val = 16 := by scalar_tac
      have hIco : Finset.Ico (1 : ℕ) 16 = Finset.Icc 1 15 := by decide
      refine ⟨hR1, ?_⟩
      rw [hv1, heq, hIco]
      refine congrArg (fun t => toK c * t) (Finset.prod_congr rfl ?_)
      intro k _
      rw [Nat.cast_mul]
      ring
  · exact ⟨hj, hjle, hacc, hval⟩

/-- **`range_product_base` computes `rangeProduct` at the embedded argument.**
The range factor of `Constraints.lean:96` with the whole product carried out in
`ZMod q` and `φF` applied once, which is exactly what licenses the two
zero-check table builders to call it on a bare `Fp` coefficient (candidate G,
`HachiEquiv.Opt.range_product_base.opt`). Total for every reduced `c`: the only
fail points are the checked `j * j`, bounded by the loop guard, and the field
operations, total under `Red`. -/
theorem range_product_base_spec (c : cpoly.field.Fp) (hc : Red c) :
    zerocheck.range_product_base c
      ⦃ out => Red out ∧ phiF (toK out) = InnerOuter.rangeProduct 16 (phiF (toK c)) ⦄ := by
  rw [zerocheck.range_product_base]
  step with fp_mul_spec c c hc hc as ⟨c2, hRc2, hc2⟩
  apply spec_mono (range_product_base_loop_spec c c2 c 1#u64 hRc2 hc
    (by simp) (by simp) hc2 (by simp))
  rintro out ⟨hRout, hout⟩
  exact ⟨hRout, by rw [hout]; exact phiF_rangeProduct_prod 16 (toK c)⟩

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

/-! ### The row of the table, computed once

`wTable` reads entry `idx` as row `u = idx / d`, coefficient `ℓ = idx % d`
(`Constraints.lean:140`), and it is the *same* polynomial for all `d` values of
`ℓ`. The three table builders below stream the table row block by row block, so
their statements need the row rather than one entry of it.

These three declarations were proved for the candidate in `lean/Opt.lean`
§ "Candidate B" and moved here verbatim: `Opt.lean` **imports** this file, so the
row hoist cannot live there and still be visible to the Aeneas triples. `Opt.lean`
now refers to them unqualified, through its `open HachiEquiv.ZeroCheck`. -/

/-- Row `u` of the table `w̃` as a polynomial over `ZMod q`, at the crate's
instantiation (`d = N`, base `16`, `rhoDigitCount q 16 = 8`):

* `u < μ`: the witness entry `z u`;
* `u - μ < n·8`: digit `(u-μ) % 8` of quotient row `(u-μ) / 8`;
* otherwise: the zero polynomial, whose every coefficient is `0` -- which is
  what `wTable`'s third branch returns.

The three branches are `wTable_at_flat_index`'s three branches with the
coefficient read pulled out. -/
def wTableRow {μ n : ℕ} (sw : InnerOuter.LiftedWitness Φ μ n) (u : ℕ) :
    CPolynomial (ZMod q) :=
  if hz : u < μ then (sw.z ⟨u, hz⟩).1
  else if hr : u - μ < n * 8 then
    InnerOuter.rhoDigits Φ 16
      (sw.ρ ⟨(u - μ) / 8, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])⟩) ((u - μ) % 8)
  else 0

/-- **The row hoist is sound**: the `ℕ`-indexed table `wTableFlat` is a
coefficient of the row polynomial. Every entry of every table builder below
factors through this equation. -/
theorem wTableFlat_eq_row {μ n m₀ : ℕ} (sw : InnerOuter.LiftedWitness Φ μ n)
    (t : ℕ) (ht : t < 2 ^ m₀) :
    wTableFlat m₀ sw t = phiF ((wTableRow sw (t / N)).coeff (t % N)) := by
  rw [wTableFlat, dif_pos ht, wTable_at_flat_index (μ := μ) (n := n) sw ht, wTableRow]
  by_cases hz : t / N < μ
  · rw [dif_pos hz, dif_pos hz]
  · rw [dif_neg hz, dif_neg hz]
    by_cases hr : t / N - μ < n * 8
    · rw [dif_pos hr, dif_pos hr]
    · rw [dif_neg hr, dif_neg hr, CPolynomial.coeff_zero, map_zero]

/-- `wTableFlat`'s defining `dif`, resolved on the cube: the specification's own
`wTable` at a cube point, as a coefficient of the row polynomial. -/
theorem wTable_symm_eq_row {μ n m₀ : ℕ} (sw : InnerOuter.LiftedWitness Φ μ n)
    (t : ℕ) (ht : t < 2 ^ m₀) :
    InnerOuter.wTable Φ m₀ phiF 16 sw (finFunctionFinEquiv.symm ⟨t, ht⟩)
      = phiF ((wTableRow sw (t / N)).coeff (t % N)) := by
  have h1 : wTableFlat m₀ sw t
      = InnerOuter.wTable Φ m₀ phiF 16 sw (finFunctionFinEquiv.symm ⟨t, ht⟩) := by
    rw [wTableFlat, dif_pos ht]
  rw [← h1, wTableFlat_eq_row sw t ht]

/-- The flat index of coefficient `l` of row `u`, decoded back. `omega` does not
unfold `N` (an `abbrev` for `1024`), so the division and the modulus are named
here and handed to the loop proofs as hypotheses. -/
private theorem block_div_mod {u l : ℕ} (hl : l < N) :
    (N * u + l) / N = u ∧ (N * u + l) % N = l := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by norm_num : 0 < N),
      Nat.div_eq_of_lt hl, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]

/-- The entry the three table builders push at flat index `N * u + l`: coefficient
`l` of row `u`. -/
private theorem wTableFlat_at_block {μ n m₀ : ℕ} (sw : InnerOuter.LiftedWitness Φ μ n)
    {u l : ℕ} (hl : l < N) (ht : N * u + l < 2 ^ m₀) :
    wTableFlat m₀ sw (N * u + l) = phiF ((wTableRow sw u).coeff l) := by
  obtain ⟨hd, hm⟩ := block_div_mod (u := u) hl
  rw [wTableFlat_eq_row sw _ ht, hd, hm]
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

/-- `w_table_row` computes `wTableRow`, the row of the committed table: the three
branches of `wTable` (`Constraints.lean:140`) read at the row rather than at the
entry (opt: `HachiEquiv.Opt.wTableRow`, now `wTableRow` above).

Stated coefficientwise below `N`, which is the only range the three table
builders read: their inner loop is guarded by `l < RING_DEGREE`.

`hmax` is the arity bound the crate's checked `rows * GADGET_DIGITS` forces, and
it is the specification's own product -- the same hypothesis `w_table_spec`
(`:427`) carries, for the same reason. -/
theorem w_table_row_spec {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (u : Std.Usize)
    (hw : RepLiftedWitness w sw) (hmax : μ + n * 8 ≤ Usize.max) :
    zerocheck.w_table_row w u
      ⦃ out => Wf out ∧
        ∀ k < N, (toRq out).1.coeff k = (wTableRow sw u.val).coeff k ⦄ := by
  obtain ⟨hWz, hWrho, hzeq, hrhoeq⟩ := hw
  have hgd : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  have hzlen : (alloc.vec.Vec.len w.z).val = μ := by simpa using hWz.1
  have hrholen : (alloc.vec.Vec.len w.rho).val = n := by simpa using hWrho.1
  rw [zerocheck.w_table_row]
  simp only [ringswitch.LiftedWitness.impl.z, ringswitch.LiftedWitness.impl.rho,
    linalg.PolyVec.len, bind_tc_ok]
  by_cases hlt : u < alloc.vec.Vec.len w.z
  · have hz : u.val < μ := by rw [← hzlen]; scalar_tac
    rw [if_pos hlt]
    have hrowlt : u.val < w.z.val.length := by rw [hWz.1]; exact hz
    simp only [linalg.PolyVec.get]
    step as ⟨r, hr⟩
    have hWr : Wf r := by rw [hr]; exact hWz.2 _ (List.getElem_mem hrowlt)
    apply spec_mono (RqBridge.copy_spec r hWr)
    rintro out ⟨hWout, hout⟩
    refine ⟨hWout, fun k _ => ?_⟩
    have hzentry : sw.z ⟨u.val, hz⟩ = toRq r := by
      rw [← hzeq]
      show toRq (w.z.val.getD u.val (alloc.vec.Vec.new cpoly.field.Fp)) = toRq r
      rw [List.getD_eq_getElem _ _ hrowlt, hr]
    rw [hout, wTableRow, dif_pos hz, hzentry]
  · have hz : ¬ u.val < μ := by rw [← hzlen]; scalar_tac
    rw [if_neg hlt]
    step as ⟨i, hi⟩
    have hiv : i.val = u.val - μ := by rw [hi, hzlen]
    have hmul : (alloc.vec.Vec.len w.rho).val * (params.GADGET_DIGITS).val ≤ Usize.max := by
      rw [hrholen, hgd]; omega
    step as ⟨i1, hi1⟩
    have hi1v : i1.val = n * 8 := by rw [hi1, hrholen, hgd]
    by_cases hlt2 : i < i1
    · have hr8 : u.val - μ < n * 8 := by rw [← hiv, ← hi1v]; scalar_tac
      rw [if_pos hlt2]
      have hivlt : i.val < n * 8 := by rw [hiv]; exact hr8
      have hrlt : i.val / 8 < n := by omega
      have helt : i.val % 8 < 8 := by omega
      apply spec_mono (rho_digit_as_rq_raw_spec (n := n) w.rho i hWrho hivlt)
      rintro out ⟨hWout, hout⟩
      refine ⟨hWout, fun k hk => ?_⟩
      have hd := digitRq_coeff_eq_rhoDigits (n := n) w.rho hrlt helt (k := k) hk
      rw [show i.val / 8 * 8 + i.val % 8 = i.val from by omega] at hd
      rw [wTableRow, dif_neg hz, dif_pos hr8, ← hrhoeq]
      simp only [← hiv]
      rw [hout, hd]
    · have hr8 : ¬ u.val - μ < n * 8 := by rw [← hiv, ← hi1v]; scalar_tac
      rw [if_neg hlt2]
      apply spec_mono RqBridge.zero_spec
      rintro out ⟨hWout, hout⟩
      refine ⟨hWout, fun k _ => ?_⟩
      rw [hout, wTableRow, dif_neg hz, dif_neg hr8, Rq.zero_val]

/-- The values vector, read as ArkLib's `CMlPolynomialEval F m₀`, is the
specification's committed table. Shared by `c_w_table_mle_spec` and
`w_table_mle_eval_spec`, which read the *same* value vector. -/
theorem toEvals_eq_cWTableMle {μ n m₀ : ℕ} (sw : InnerOuter.LiftedWitness Φ μ n)
    (o : alloc.vec.Vec cpoly.field.Ext4)
    (hval : ∀ t < 2 ^ m₀, toExt (o.val.getD t cpoly.field.Ext4.ZERO) =
      wTableFlat m₀ sw t) :
    toEvals (m := m₀) o = InnerOuter.cWTableMle Φ m₀ phiF 16 sw := by
  rw [toEvals, InnerOuter.cWTableMle]
  refine congrArg Vector.ofFn (funext fun j => ?_)
  rw [hval j.val j.isLt, wTableFlat, dif_pos j.isLt, Fin.eta]

/-- The inner loop of `c_w_table_mle_values`: the `N` coefficients of the row `r`,
pushed for ascending `l`, stopping at the row width or at the table end `size`,
whichever comes first -- the second guard is what truncates the final block, so
the traversal emits exactly `2 ^ m₀` entries for every `m₀`, `μ`, `n`.

The running flat index is `idx = base + l`, and `base` is an opaque `ℕ` here:
that is deliberate, since `omega` cannot see through the product `N * u` but does
not have to, `hg` carrying the row's entries already indexed by the flat
position. The Lean side of this loop is `HachiEquiv.Opt.blockLoop`
(`lean/Opt.lean`). -/
theorem c_w_table_mle_values_loop0_loop0_spec {μ n m₀ : ℕ}
    (sw : InnerOuter.LiftedWitness Φ μ n) (size : Std.Usize) (r : ring.Rq) (base : ℕ)
    (values : alloc.vec.Vec cpoly.field.Ext4) (idx l : Std.Usize) (hr : Wf r)
    (hg : ∀ k, k < N → base + k < 2 ^ m₀ →
      phiF ((toRq r).1.coeff k) = wTableFlat m₀ sw (base + k))
    (hm0 : 2 ^ m₀ ≤ Usize.max) (hsize : size.val = 2 ^ m₀) (hl : l.val ≤ N)
    (hidx : idx.val = base + l.val) (hidxle : idx.val ≤ 2 ^ m₀)
    (hlen : values.val.length = idx.val) (hred : VecReduced values)
    (hval : ∀ t < idx.val, toExt (values.val.getD t cpoly.field.Ext4.ZERO) =
      wTableFlat m₀ sw t) :
    zerocheck.c_w_table_mle_values_loop0_loop0 size params.RING_DEGREE values idx r l
      ⦃ (o, x) => x.val = min (base + N) (2 ^ m₀) ∧ o.val.length = x.val ∧
        VecReduced o ∧ ∀ t < x.val,
          toExt (o.val.getD t cpoly.field.Ext4.ZERO) = wTableFlat m₀ sw t ⦄ := by
  have hrd : (params.RING_DEGREE).val = N := params_RING_DEGREE_val
  rw [zerocheck.c_w_table_mle_values_loop0_loop0]
  apply loop.spec_decr_nat (fun s => N - s.2.2.val)
    (fun s => s.2.2.val ≤ N ∧ s.2.1.val = base + s.2.2.val ∧ s.2.1.val ≤ 2 ^ m₀ ∧
      s.1.val.length = s.2.1.val ∧ VecReduced s.1 ∧
      ∀ t < s.2.1.val, toExt (s.1.val.getD t cpoly.field.Ext4.ZERO) = wTableFlat m₀ sw t)
  · rintro ⟨v1, x1, l1⟩ ⟨hl1, hx1, hx1le, hlen1, hred1, hval1⟩
    dsimp only at hl1 hx1 hx1le hlen1 hred1 hval1
    simp only [zerocheck.c_w_table_mle_values_loop0_loop0.body]
    by_cases hlt : l1 < params.RING_DEGREE
    · rw [if_pos hlt]
      have hllt : l1.val < N := by rw [← hrd]; scalar_tac
      by_cases hlt2 : x1 < size
      · rw [if_pos hlt2]
        have hxlt : x1.val < 2 ^ m₀ := by rw [← hsize]; scalar_tac
        step with RqBridge.coeff_spec r l1 hr as ⟨f, hRf, hf⟩
        step with ext_from_base_spec f hRf as ⟨e, hRe, he⟩
        have hentry : toExt e = wTableFlat m₀ sw x1.val := by
          rw [he, hf, ← phiF_apply, hx1, hg l1.val hllt (by rw [← hx1]; exact hxlt)]
        have hbound : v1.val.length < Usize.max := by omega
        step as ⟨v2, hv2⟩
        step as ⟨l2, hl2⟩
        step as ⟨x2, hx2⟩
        have hl2v : l2.val = l1.val + 1 := by scalar_tac
        have hx2v : x2.val = x1.val + 1 := by scalar_tac
        refine ⟨by omega, by omega, by omega, ?_, ?_, ?_, by omega⟩
        · rw [hx2v, hv2, List.length_append, hlen1]; simp
        · intro y hy
          rw [hv2] at hy
          rcases List.mem_append.mp hy with h | h
          · exact hred1 y h
          · rw [List.mem_singleton.mp h]; exact hRe
        · intro t ht
          rw [hx2v] at ht
          rcases Nat.lt_or_ge t x1.val with htlt | htge
          · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
          · have hteq : t = v1.val.length := by omega
            rw [hteq, hv2, getD_append_eq, hentry, hlen1]
      · rw [if_neg hlt2, WP.spec_ok]
        dsimp only
        have hge : size.val ≤ x1.val := by scalar_tac
        rw [hsize] at hge
        rw [show min (base + N) (2 ^ m₀) = x1.val from by omega]
        exact ⟨rfl, hlen1, hred1, hval1⟩
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hlge : N ≤ l1.val := by rw [← hrd]; scalar_tac
      rw [show min (base + N) (2 ^ m₀) = x1.val from by omega]
      exact ⟨rfl, hlen1, hred1, hval1⟩
  · exact ⟨hl, hidx, hidxle, hlen, hred, hval⟩

/-- The outer loop of `c_w_table_mle_values`: one `w_table_row` per row, its
coefficient block streamed by the inner loop. `idx = min (N * u) (2 ^ m₀)` is the
running state's own invariant; the `min` is what survives a truncated final
block, which is what happens whenever `2 ^ m₀` is not a multiple of `N`. The Lean
side of this loop is `HachiEquiv.Opt.rowLoop` (`lean/Opt.lean`). -/
theorem c_w_table_mle_values_loop0_spec {μ n m₀ : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (size : Std.Usize)
    (values : alloc.vec.Vec cpoly.field.Ext4) (u idx : Std.Usize)
    (hw : RepLiftedWitness w sw) (hmax : μ + n * 8 ≤ Usize.max)
    (hm0 : 2 ^ m₀ ≤ Usize.max) (hsize : size.val = 2 ^ m₀)
    (hidx : idx.val = min (N * u.val) (2 ^ m₀))
    (hlen : values.val.length = idx.val) (hred : VecReduced values)
    (hval : ∀ t < idx.val, toExt (values.val.getD t cpoly.field.Ext4.ZERO) =
      wTableFlat m₀ sw t) :
    zerocheck.c_w_table_mle_values_loop0 w size params.RING_DEGREE values u idx
      ⦃ o => o.val.length = 2 ^ m₀ ∧ VecReduced o ∧
        ∀ t < 2 ^ m₀, toExt (o.val.getD t cpoly.field.Ext4.ZERO) =
          wTableFlat m₀ sw t ⦄ := by
  have hN : 0 < N := by norm_num
  have h1v : (1#usize : Std.Usize).val = 1 := by scalar_tac
  rw [zerocheck.c_w_table_mle_values_loop0]
  apply loop.spec_decr_nat (fun s => 2 ^ m₀ - s.2.2.val)
    (fun s => s.2.2.val = min (N * s.2.1.val) (2 ^ m₀) ∧ s.1.val.length = s.2.2.val ∧
      VecReduced s.1 ∧
      ∀ t < s.2.2.val, toExt (s.1.val.getD t cpoly.field.Ext4.ZERO) = wTableFlat m₀ sw t)
  · rintro ⟨v1, u1, x1⟩ ⟨hx1, hlen1, hred1, hval1⟩
    dsimp only at hx1 hlen1 hred1 hval1
    simp only [zerocheck.c_w_table_mle_values_loop0.body]
    by_cases hlt : x1 < size
    · rw [if_pos hlt]
      have hxlt : x1.val < 2 ^ m₀ := by rw [← hsize]; scalar_tac
      have hbase : x1.val = N * u1.val := by omega
      step with w_table_row_spec w sw u1 hw hmax as ⟨r, hWr, hrow⟩
      have hg : ∀ k, k < N → N * u1.val + k < 2 ^ m₀ →
          phiF ((toRq r).1.coeff k) = wTableFlat m₀ sw (N * u1.val + k) := by
        intro k hk hklt
        rw [hrow k hk, wTableFlat_at_block sw hk hklt]
      step with c_w_table_mle_values_loop0_loop0_spec (m₀ := m₀) sw size r (N * u1.val)
        v1 x1 0#usize hWr hg hm0 hsize (by simp) (by rw [hbase]; simp) (by omega)
        hlen1 hred1 hval1 as ⟨v2, x2, hx2, hlen2, hred2, hval2⟩
      step as ⟨u2, hu2⟩
      have hu2v : u2.val = u1.val + 1 := by omega
      refine ⟨?_, hlen2, hred2, hval2, by omega⟩
      rw [hx2, hu2v, Nat.mul_add, Nat.mul_one]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hge : size.val ≤ x1.val := by scalar_tac
      rw [hsize] at hge
      have hxeq : x1.val = 2 ^ m₀ := by omega
      exact ⟨by rw [hlen1, hxeq], hred1, by rw [← hxeq]; exact hval1⟩
  · exact ⟨hidx, hlen, hred, hval⟩

/-- `c_w_table_mle_values` builds the `2 ^ m₀` table entries row block by row
block: the private helper both `c_w_table_mle` and `w_table_mle_eval` call
(opt: `HachiEquiv.Opt.c_w_table_mle.opt`, `lean/Opt.lean`). -/
theorem c_w_table_mle_values_spec {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (m0 : Std.Usize)
    (hw : RepLiftedWitness w sw) (hm0 : 2 ^ m0.val ≤ Usize.max)
    (hmax : μ + n * 8 ≤ Usize.max) :
    zerocheck.c_w_table_mle_values w m0
      ⦃ o => o.val.length = 2 ^ m0.val ∧ VecReduced o ∧
        ∀ t < 2 ^ m0.val, toExt (o.val.getD t cpoly.field.Ext4.ZERO) =
          wTableFlat m0.val sw t ⦄ := by
  rw [zerocheck.c_w_table_mle_values]
  step with two_pow_spec m0 hm0 as ⟨size, hsize⟩
  exact c_w_table_mle_values_loop0_spec (m₀ := m0.val) w sw size
    (alloc.vec.Vec.with_capacity cpoly.field.Ext4 size) 0#usize 0#usize hw hmax hm0 hsize
    (by simp) (by simp [alloc.vec.Vec.with_capacity])
    (by intro y hy; simp [alloc.vec.Vec.with_capacity] at hy)
    (by intro t ht; simp at ht)

/-! ### The same table, in the base field

`c_w_table_fp` is `c_w_table_mle_values` with `Ext4::from_base` left out: the
identical row-blocked traversal pushing the bare coefficient `r.coeff(l) : Fp`.
That is sound because *every* entry of `w~` is `phiF` of a coefficient
(`Constraints.lean:146,148`), so the embedding step carries no information --
and dropping it is what lets round 0 of the sumcheck run in `ZMod q`
(candidate I, `lean/Opt.lean` section "Candidate I"). One `u64` per entry
instead of four.

The three specs below mirror `c_w_table_mle_values`' three exactly, with
`toExt (values.getD t _) = wTableFlat ...` replaced by
`phiF (coeffK values t) = wTableFlat ...` and `VecReduced` by `Red` on every
word: the only step that disappears is `ext_from_base_spec`, whose conclusion
`toExt e = Ext.ofBase (toK f)` was the sole use of the embedding. -/

/-- The inner loop of `c_w_table_fp`: the `N` coefficients of the row `r`, pushed
for ascending `l`, stopping at the row width or at the table end `size`. Same
`base + l` flat index, same truncating second guard, same opaque `base`, as
`c_w_table_mle_values_loop0_loop0_spec`. -/
theorem c_w_table_fp_loop0_loop0_spec {μ n m₀ : ℕ}
    (sw : InnerOuter.LiftedWitness Φ μ n) (size : Std.Usize) (r : ring.Rq) (base : ℕ)
    (values : alloc.vec.Vec cpoly.field.Fp) (idx l : Std.Usize) (hr : Wf r)
    (hg : ∀ k, k < N → base + k < 2 ^ m₀ →
      phiF ((toRq r).1.coeff k) = wTableFlat m₀ sw (base + k))
    (hm0 : 2 ^ m₀ ≤ Usize.max) (hsize : size.val = 2 ^ m₀) (hl : l.val ≤ N)
    (hidx : idx.val = base + l.val) (hidxle : idx.val ≤ 2 ^ m₀)
    (hlen : values.val.length = idx.val) (hred : ∀ a ∈ values.val, Red a)
    (hval : ∀ t < idx.val, phiF (coeffK values t) = wTableFlat m₀ sw t) :
    zerocheck.c_w_table_fp_loop0_loop0 size params.RING_DEGREE values idx r l
      ⦃ (o, x) => x.val = min (base + N) (2 ^ m₀) ∧ o.val.length = x.val ∧
        (∀ a ∈ o.val, Red a) ∧ ∀ t < x.val,
          phiF (coeffK o t) = wTableFlat m₀ sw t ⦄ := by
  have hrd : (params.RING_DEGREE).val = N := params_RING_DEGREE_val
  rw [zerocheck.c_w_table_fp_loop0_loop0]
  apply loop.spec_decr_nat (fun s => N - s.2.2.val)
    (fun s => s.2.2.val ≤ N ∧ s.2.1.val = base + s.2.2.val ∧ s.2.1.val ≤ 2 ^ m₀ ∧
      s.1.val.length = s.2.1.val ∧ (∀ a ∈ s.1.val, Red a) ∧
      ∀ t < s.2.1.val, phiF (coeffK s.1 t) = wTableFlat m₀ sw t)
  · rintro ⟨v1, x1, l1⟩ ⟨hl1, hx1, hx1le, hlen1, hred1, hval1⟩
    dsimp only at hl1 hx1 hx1le hlen1 hred1 hval1
    simp only [zerocheck.c_w_table_fp_loop0_loop0.body]
    by_cases hlt : l1 < params.RING_DEGREE
    · rw [if_pos hlt]
      have hllt : l1.val < N := by rw [← hrd]; scalar_tac
      by_cases hlt2 : x1 < size
      · rw [if_pos hlt2]
        have hxlt : x1.val < 2 ^ m₀ := by rw [← hsize]; scalar_tac
        step with RqBridge.coeff_spec r l1 hr as ⟨f, hRf, hf⟩
        have hentry : phiF (toK f) = wTableFlat m₀ sw x1.val := by
          rw [hf, hx1, hg l1.val hllt (by rw [← hx1]; exact hxlt)]
        have hbound : v1.val.length < Usize.max := by omega
        step as ⟨v2, hv2⟩
        step as ⟨l2, hl2⟩
        step as ⟨x2, hx2⟩
        have hl2v : l2.val = l1.val + 1 := by scalar_tac
        have hx2v : x2.val = x1.val + 1 := by scalar_tac
        refine ⟨by omega, by omega, by omega, ?_, ?_, ?_, by omega⟩
        · rw [hx2v, hv2, List.length_append, hlen1]; simp
        · intro y hy
          rw [hv2] at hy
          rcases List.mem_append.mp hy with h | h
          · exact hred1 y h
          · rw [List.mem_singleton.mp h]; exact hRf
        · intro t ht
          rw [hx2v] at ht
          rcases Nat.lt_or_ge t x1.val with htlt | htge
          · rw [coeffK_append_lt hv2 (by omega)]; exact hval1 t htlt
          · have hteq : t = v1.val.length := by omega
            rw [hteq, coeffK_append_eq hv2, hlen1]; exact hentry
      · rw [if_neg hlt2, WP.spec_ok]
        dsimp only
        have hge : size.val ≤ x1.val := by scalar_tac
        rw [hsize] at hge
        rw [show min (base + N) (2 ^ m₀) = x1.val from by omega]
        exact ⟨rfl, hlen1, hred1, hval1⟩
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hlge : N ≤ l1.val := by rw [← hrd]; scalar_tac
      rw [show min (base + N) (2 ^ m₀) = x1.val from by omega]
      exact ⟨rfl, hlen1, hred1, hval1⟩
  · exact ⟨hl, hidx, hidxle, hlen, hred, hval⟩

/-- The outer loop of `c_w_table_fp`: one `w_table_row` per row, its coefficient
block streamed by the inner loop; `idx = min (N * u) (2 ^ m₀)` as in
`c_w_table_mle_values_loop0_spec`. -/
theorem c_w_table_fp_loop0_spec {μ n m₀ : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (size : Std.Usize)
    (values : alloc.vec.Vec cpoly.field.Fp) (u idx : Std.Usize)
    (hw : RepLiftedWitness w sw) (hmax : μ + n * 8 ≤ Usize.max)
    (hm0 : 2 ^ m₀ ≤ Usize.max) (hsize : size.val = 2 ^ m₀)
    (hidx : idx.val = min (N * u.val) (2 ^ m₀))
    (hlen : values.val.length = idx.val) (hred : ∀ a ∈ values.val, Red a)
    (hval : ∀ t < idx.val, phiF (coeffK values t) = wTableFlat m₀ sw t) :
    zerocheck.c_w_table_fp_loop0 w size params.RING_DEGREE values u idx
      ⦃ o => o.val.length = 2 ^ m₀ ∧ (∀ a ∈ o.val, Red a) ∧
        ∀ t < 2 ^ m₀, phiF (coeffK o t) = wTableFlat m₀ sw t ⦄ := by
  have hN : 0 < N := by norm_num
  have h1v : (1#usize : Std.Usize).val = 1 := by scalar_tac
  rw [zerocheck.c_w_table_fp_loop0]
  apply loop.spec_decr_nat (fun s => 2 ^ m₀ - s.2.2.val)
    (fun s => s.2.2.val = min (N * s.2.1.val) (2 ^ m₀) ∧ s.1.val.length = s.2.2.val ∧
      (∀ a ∈ s.1.val, Red a) ∧
      ∀ t < s.2.2.val, phiF (coeffK s.1 t) = wTableFlat m₀ sw t)
  · rintro ⟨v1, u1, x1⟩ ⟨hx1, hlen1, hred1, hval1⟩
    dsimp only at hx1 hlen1 hred1 hval1
    simp only [zerocheck.c_w_table_fp_loop0.body]
    by_cases hlt : x1 < size
    · rw [if_pos hlt]
      have hxlt : x1.val < 2 ^ m₀ := by rw [← hsize]; scalar_tac
      have hbase : x1.val = N * u1.val := by omega
      step with w_table_row_spec w sw u1 hw hmax as ⟨r, hWr, hrow⟩
      have hg : ∀ k, k < N → N * u1.val + k < 2 ^ m₀ →
          phiF ((toRq r).1.coeff k) = wTableFlat m₀ sw (N * u1.val + k) := by
        intro k hk hklt
        rw [hrow k hk, wTableFlat_at_block sw hk hklt]
      step with c_w_table_fp_loop0_loop0_spec (m₀ := m₀) sw size r (N * u1.val)
        v1 x1 0#usize hWr hg hm0 hsize (by simp) (by rw [hbase]; simp) (by omega)
        hlen1 hred1 hval1 as ⟨v2, x2, hx2, hlen2, hred2, hval2⟩
      step as ⟨u2, hu2⟩
      have hu2v : u2.val = u1.val + 1 := by omega
      refine ⟨?_, hlen2, hred2, hval2, by omega⟩
      rw [hx2, hu2v, Nat.mul_add, Nat.mul_one]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hge : size.val ≤ x1.val := by scalar_tac
      rw [hsize] at hge
      have hxeq : x1.val = 2 ^ m₀ := by omega
      exact ⟨by rw [hlen1, hxeq], hred1, by rw [← hxeq]; exact hval1⟩
  · exact ⟨hidx, hlen, hred, hval⟩

/-- **`c_w_table_fp` builds the committed table as `2 ^ m₀` base-field words.**
`c_w_table_mle_values` without the embedding: entry `t` is the coefficient whose
image under `phiF` is `wTableFlat m₀ sw t`, which is the same table
`c_w_table_mle_values_spec` delivers, read one layer lower. Carries
`c_w_table_mle_values_spec`'s two bounds unchanged -- `two_pow`'s checked
doubling and `w_table`'s `μ + n * 8`. -/
theorem c_w_table_fp_spec {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (m0 : Std.Usize)
    (hw : RepLiftedWitness w sw) (hm0 : 2 ^ m0.val ≤ Usize.max)
    (hmax : μ + n * 8 ≤ Usize.max) :
    zerocheck.c_w_table_fp w m0
      ⦃ o => o.val.length = 2 ^ m0.val ∧ (∀ a ∈ o.val, Red a) ∧
        ∀ t < 2 ^ m0.val, phiF (coeffK o t) = wTableFlat m0.val sw t ⦄ := by
  rw [zerocheck.c_w_table_fp]
  step with two_pow_spec m0 hm0 as ⟨size, hsize⟩
  exact c_w_table_fp_loop0_spec (m₀ := m0.val) w sw size
    (alloc.vec.Vec.with_capacity cpoly.field.Fp size) 0#usize 0#usize hw hmax hm0 hsize
    (by simp) (by simp [alloc.vec.Vec.with_capacity])
    (by intro y hy; simp [alloc.vec.Vec.with_capacity] at hy)
    (by intro t ht; simp at ht)

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
  step with c_w_table_mle_values_spec (μ := μ) (n := n) w sw m0 hw hm0 hmax
    as ⟨o, hlen, hred, hval⟩
  simp only [cpoly.multilinear.MultilinearEvals.from_values, WP.spec_ok]
  exact ⟨⟨hlen, hred⟩, toEvals_eq_cWTableMle sw o hval⟩

/-! ### The Lagrange basis at a represented point

One pure lemma, used by the `h_alpha` constraint block: entry `t` of CompPoly's
`CMlPolynomialEval.lagrangeBasis` at a represented point, as the bit product the
specification's own constraint rows build.

This section used to also carry the extracted side of `cpoly::multilinear`'s
`MultilinearEvals::eval` -- `table_len`, the two `lagrange_basis` loops,
`lagrange_basis` itself, the `dot` loop and `dot`, five triples on `Slice`s.
`final_check` was the last caller in the crate, through
`cpoly::multilinear::eq_tilde`, and once it was rerouted through hachi's own
`eq_prefix` none of those six functions is reachable any more, so none of them is
in `Generated.lean` and their specs are deleted rather than parked. Nothing above
lost a claim: the multilinear evaluation this crate performs is the `evalMleLayer`
fold below, which CompPoly proves equal to the Lagrange dot
(`eval_mle_eq_eval`, `CompPoly/Multilinear/Basic.lean:574`). See NOTES.md
§ "The model contains what the crate reaches". -/

/-- Entry `t` of `CMlPolynomialEval.lagrangeBasis` at a represented point, as
the bit product the specification's constraint rows build
(`Constraints.lean:845-847`; the bit product does **not** cancel against
`finFunctionFinEquiv`). -/
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

/-! ### The layer fold `w_table_mle_eval` runs

`cpoly::multilinear::eval_mle_layer` is CompPoly's `evalMleLayer`, and `m₀` of
them compose into `CMlPolynomialEval.evalMle`, which CompPoly proves equal to the
Lagrange dot above (`eval_mle_eq_eval`, `CompPoly/Multilinear/Basic.lean:574`).

The four pure helpers and the two layer specs below were proved in
`lean/Sumcheck.lean` and are moved here verbatim, because `Sumcheck.lean`
**imports** this file (through `EndPiece.lean`) and `w_table_mle_eval` now needs
them. `Sumcheck.lean` keeps its fifty-odd uses through its
`open HachiEquiv.ZeroCheck`. -/

/-- Even index `2y` into a table twice the size: the `(cs, 0, y)` entry. -/
def lo {k : ℕ} (y : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  ⟨2 * y.val, by have := y.isLt; rw [pow_succ]; omega⟩

/-- Odd index `2y + 1`: the `(cs, 1, y)` entry. -/
def hi {k : ℕ} (y : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  ⟨2 * y.val + 1, by have := y.isLt; rw [pow_succ]; omega⟩

/-- One multilinear fold step: the table's value at `T` in its first free
coordinate, `(1 - T)·w[2y] + T·w[2y + 1]`. This is what `eval_mle_layer` does
at `T = a`, and what a round polynomial's node value reads at `T = node`. -/
def fold {k : ℕ} (w : Fin (2 ^ (k + 1)) → F) (T : F) (y : Fin (2 ^ k)) : F :=
  (1 - T) * w (lo y) + T * w (hi y)

/-- A table as a function of its index. -/
def tableFn {m : ℕ} (t : alloc.vec.Vec cpoly.field.Ext4) : Fin (2 ^ m) → F :=
  fun y => (toEvals (m := m) t).get y
/-- `tableFn` reads the underlying vector at the index. -/
theorem tableFn_apply {m : ℕ} (t : alloc.vec.Vec cpoly.field.Ext4) (y : Fin (2 ^ m)) :
    tableFn (m := m) t y = toExt (t.val.getD y.val cpoly.field.Ext4.ZERO) := by
  simp [tableFn, toEvals]

/-- A **base-field** table as a function of its index: the `Fp` counterpart of
`tableFn`, read through `coeffK` so that a short vector reads as `0` past its
end exactly as `tableFn` does. Composed with `phiF` it is the table the
extension-field specs talk about, which is how every `_base` spec of
`lean/Sumcheck.lean` states its conclusion. -/
def tableFnFp {m : ℕ} (t : alloc.vec.Vec cpoly.field.Fp) : Fin (2 ^ m) → ZMod q :=
  fun y => coeffK t y.val

/-- `tableFnFp` reads the underlying vector at the index. -/
theorem tableFnFp_apply {m : ℕ} (t : alloc.vec.Vec cpoly.field.Fp) (y : Fin (2 ^ m)) :
    tableFnFp (m := m) t y = toK (t.val.getD y.val cpoly.field.Fp.ZERO) := rfl

/-- The loop of `cpoly::multilinear::eval_mle_layer`: the output holds the `j`
folded entries produced so far. -/
theorem eval_mle_layer_loop_spec {k : ℕ} (values : Slice cpoly.field.Ext4)
    (x0 one_minus : cpoly.field.Ext4) (half : Std.Usize)
    (hvred : SliceReduced values) (hvlen : values.val.length = 2 ^ (k + 1))
    (hx : Reduced x0) (hom : Reduced one_minus) (homv : toExt one_minus = 1 - toExt x0)
    (hhalf : half.val = 2 ^ k)
    (out : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize)
    (hj : j.val ≤ 2 ^ k) (holen : out.val.length = j.val) (hored : VecReduced out)
    (hoval : ∀ t : ℕ, t < j.val →
      toExt (out.val.getD t cpoly.field.Ext4.ZERO)
        = (1 - toExt x0) * toExt (values.val.getD (2 * t) cpoly.field.Ext4.ZERO)
          + toExt x0 * toExt (values.val.getD (2 * t + 1) cpoly.field.Ext4.ZERO)) :
    cpoly.multilinear.eval_mle_layer_loop values x0 half one_minus out j
      ⦃ o => o.val.length = 2 ^ k ∧ VecReduced o ∧
        ∀ t : ℕ, t < 2 ^ k →
          toExt (o.val.getD t cpoly.field.Ext4.ZERO)
            = (1 - toExt x0) * toExt (values.val.getD (2 * t) cpoly.field.Ext4.ZERO)
              + toExt x0 * toExt (values.val.getD (2 * t + 1) cpoly.field.Ext4.ZERO) ⦄ := by
  have hmax : 2 ^ (k + 1) ≤ Usize.max := by
    have := values.property
    omega
  rw [cpoly.multilinear.eval_mle_layer_loop]
  apply loop.spec_decr_nat (fun st => 2 ^ k - st.2.val)
    (fun st => st.2.val ≤ 2 ^ k ∧ st.1.val.length = st.2.val ∧ VecReduced st.1 ∧
      ∀ t : ℕ, t < st.2.val →
        toExt (st.1.val.getD t cpoly.field.Ext4.ZERO)
          = (1 - toExt x0) * toExt (values.val.getD (2 * t) cpoly.field.Ext4.ZERO)
            + toExt x0 * toExt (values.val.getD (2 * t + 1) cpoly.field.Ext4.ZERO))
  · rintro ⟨o1, j1⟩ ⟨hj1, hlen1, hred1, hval1⟩
    dsimp only at hj1 hlen1 hred1 hval1
    simp only [cpoly.multilinear.eval_mle_layer_loop.body]
    by_cases hlt : j1 < half
    · rw [if_pos hlt]
      have hjlt : j1.val < 2 ^ k := by rw [← hhalf]; scalar_tac
      have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      have hlo : 2 * j1.val < values.val.length := by rw [hvlen, hpow]; omega
      have hhi : 2 * j1.val + 1 < values.val.length := by rw [hvlen, hpow]; omega
      step as ⟨idx, hidx⟩
      have hidxv : idx.val = 2 * j1.val := by scalar_tac
      step as ⟨lo, hlov⟩
      step as ⟨idx1, hidx1⟩
      have hidx1v : idx1.val = 2 * j1.val + 1 := by scalar_tac
      step as ⟨hiv, hhiv⟩
      simp only [hidxv] at hlov
      simp only [hidx1v] at hhiv
      have hRlo : Reduced lo := by
        rw [hlov]; exact hvred _ (List.getElem_mem (by omega))
      have hRhi : Reduced hiv := by
        rw [hhiv]; exact hvred _ (List.getElem_mem (by omega))
      step with ext_mul_spec one_minus lo hom hRlo as ⟨p1, hRp1, hp1⟩
      step with ext_mul_spec x0 hiv hx hRhi as ⟨p2, hRp2, hp2⟩
      step with ext_add_spec p1 p2 hRp1 hRp2 as ⟨sm, hRsm, hsm⟩
      have hpush : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨j2, hj2⟩
      have hj2v : j2.val = j1.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · rw [hj2v, ho2, List.length_append, hlen1]; simp
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hred1 u h
        · rw [List.mem_singleton.mp h]; exact hRsm
      · intro t ht
        rw [hj2v] at ht
        rcases Nat.lt_or_ge t j1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = o1.val.length := by omega
          rw [hteq, ho2, getD_append_eq, hsm, hp1, hp2, homv, hlov, hhiv, hlen1,
            List.getD_eq_getElem _ _ (show 2 * j1.val < values.val.length from by omega),
            List.getD_eq_getElem _ _ (show 2 * j1.val + 1 < values.val.length from by omega)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hjeq : j1.val = 2 ^ k := by rw [← hhalf] at hj1 ⊢; scalar_tac
      exact ⟨by rw [hlen1, hjeq], hred1, by rw [← hjeq]; exact hval1⟩
  · exact ⟨hj, holen, hored, hoval⟩

/-- `cpoly::multilinear::eval_mle_layer` folds a table's first coordinate at `x0`:
the specification's `fold`. -/
theorem eval_mle_layer_spec {k : ℕ} (t : alloc.vec.Vec cpoly.field.Ext4)
    (x0 : cpoly.field.Ext4) (ht : WfEvals (k + 1) t) (hx : Reduced x0) :
    cpoly.multilinear.eval_mle_layer (alloc.vec.Vec.deref t) x0
      ⦃ o => WfEvals k o ∧ ∀ y : Fin (2 ^ k),
          tableFn (m := k) o y = fold (tableFn (m := k + 1) t) (toExt x0) y ⦄ := by
  obtain ⟨htlen, htred⟩ := ht
  have hR1 : Reduced cpoly.field.Ext4.ONE := reduced_ONE
  rw [cpoly.multilinear.eval_mle_layer]
  step as ⟨half, hhalf⟩
  have hhalfv : half.val = 2 ^ k := by
    have : (Slice.len (alloc.vec.Vec.deref t)).val = 2 ^ (k + 1) := by
      simp only [deref_len]
      scalar_tac
    have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    scalar_tac
  step with ext_sub_spec cpoly.field.Ext4.ONE x0 hR1 hx as ⟨om, hRom, homv⟩
  apply spec_mono (eval_mle_layer_loop_spec (k := k) (alloc.vec.Vec.deref t) x0 om half
    (sliceReduced_deref htred) (by simpa using htlen) hx hRom
    (by rw [homv, toExt_ONE]) hhalfv (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize
    (by simp) (by simp) (by intro u hu; simp at hu) (by intro t' ht'; simp at ht'))
  rintro o ⟨holen, hored, hoval⟩
  refine ⟨⟨holen, hored⟩, fun y => ?_⟩
  rw [tableFn_apply, hoval y.val y.isLt, fold, tableFn_apply, tableFn_apply]
  simp only [deref_val, lo, hi]


/-! ### `w_table_mle_eval`: the fold, layer by layer

The loop's state carries a table whose *arity* shrinks by one per iteration, so
the invariant cannot be an equation between two tables of a fixed width. What it
carries instead is the remaining work: `mleFold` of the current table against the
point's remaining coordinates, which never changes and is the answer. -/

/-- The point's coordinate `i`, as a function of a plain `ℕ`: the shape the layer
loop's invariant can carry, since its counter has no `m₀` bound in its type. -/
def ptFlat (a : alloc.vec.Vec cpoly.field.Ext4) (i : ℕ) : F :=
  toExt (a.val.getD i cpoly.field.Ext4.ZERO)

/-- `CMlPolynomialEval.evalMleValues` with the remaining point coordinates given
as a function of a plain `ℕ`: `mleFold k t p` folds `t`'s `k` variables at
`p 0, …, p (k-1)`. `mleFold_eq_evalMle` is the single place the `ℕ`-indexed point
is put back into a `Vector`. -/
def mleFold : (k : ℕ) → CMlPolynomialEval F k → (ℕ → F) → F
  | 0, t, _ => t.get ⟨0, by norm_num⟩
  | k + 1, t, p => mleFold k (CMlPolynomialEval.evalMleLayer t (p 0)) (fun i => p (i + 1))

/-- `mleFold` is CompPoly's `evalMle`: the same layer recursion, with the point
re-indexed. -/
theorem mleFold_eq_evalMle : ∀ (k : ℕ) (t : CMlPolynomialEval F k) (p : ℕ → F),
    mleFold k t p
      = CMlPolynomialEval.evalMle t (Vector.ofFn (fun i : Fin k => p i.val)) := by
  intro k
  induction k with
  | zero =>
    intro t p
    rfl
  | succ k ih =>
    intro t p
    have hhead : (Vector.ofFn (fun i : Fin (k + 1) => p i.val)).head = p 0 := by
      simp [Vector.head]
    have htail : (Vector.ofFn (fun i : Fin (k + 1) => p i.val)).tail
        = Vector.ofFn (fun i : Fin k => p (i.val + 1)) := by
      apply Vector.ext
      intro i hib
      simp
      rw [Nat.add_comm 1 i]
    rw [mleFold, ih, CMlPolynomialEval.evalMle_succ, hhead, htail]

/-- Vector equality from its `Fin`-indexed reads, which is the form `tableFn`
gives. -/
private theorem vector_eq_of_get {m : ℕ} {u v : Vector F m}
    (h : ∀ i : Fin m, u.get i = v.get i) : u = v := by
  apply Vector.ext
  intro i hib
  exact h ⟨i, hib⟩

/-- One extracted layer, as one step of `mleFold`: `toEvals` of the layer's
output is `evalMleLayer` of `toEvals` of its input. This is the bridge between
`eval_mle_layer_spec`'s `fold` conclusion and CompPoly's own layer. -/
theorem toEvals_evalMleLayer {k : ℕ} (o t : alloc.vec.Vec cpoly.field.Ext4) (x0 : F)
    (h : ∀ y : Fin (2 ^ k), tableFn (m := k) o y = fold (tableFn (m := k + 1) t) x0 y) :
    toEvals (m := k) o = CMlPolynomialEval.evalMleLayer (toEvals (m := k + 1) t) x0 := by
  refine vector_eq_of_get fun y => ?_
  rw [CMlPolynomialEval.evalMleLayer_get,
    show (toEvals (m := k) o).get y = tableFn (m := k) o y from rfl, h y, fold]
  rfl

/-- The loop of `w_table_mle_eval`: after `j` layers the table has `m₀ - j` free
variables left, and `mleFold` of what remains is still the whole evaluation. The
answer travels as the parameter `tgt`, which is what lets the invariant be an
equation between two closed terms rather than a statement about a table whose
arity moves. -/
theorem w_table_mle_eval_loop_spec {m₀ : ℕ} (a : alloc.vec.Vec cpoly.field.Ext4)
    (vars : Std.Usize) (cur : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize) (tgt : F)
    (ha : WfPoint m₀ a) (hvars : vars.val = m₀) (hj : j.val ≤ m₀)
    (hcur : WfEvals (m₀ - j.val) cur)
    (hinv : mleFold (m₀ - j.val) (toEvals (m := m₀ - j.val) cur)
      (fun i => ptFlat a (j.val + i)) = tgt) :
    zerocheck.w_table_mle_eval_loop a vars cur j
      ⦃ o => o.val.length = 1 ∧ VecReduced o ∧
        toExt (o.val.getD 0 cpoly.field.Ext4.ZERO) = tgt ⦄ := by
  obtain ⟨halen, hared⟩ := ha
  rw [zerocheck.w_table_mle_eval_loop]
  apply loop.spec_decr_nat (fun s => m₀ - s.2.val)
    (fun s => s.2.val ≤ m₀ ∧ WfEvals (m₀ - s.2.val) s.1 ∧
      mleFold (m₀ - s.2.val) (toEvals (m := m₀ - s.2.val) s.1)
        (fun i => ptFlat a (s.2.val + i)) = tgt)
  · rintro ⟨c1, j1⟩ ⟨hj1, hc1, hinv1⟩
    dsimp only at hj1 hc1 hinv1
    simp only [zerocheck.w_table_mle_eval_loop.body]
    by_cases hlt : j1 < vars
    · rw [if_pos hlt]
      have hjlt : j1.val < m₀ := by rw [← hvars]; scalar_tac
      have halt : j1.val < a.val.length := by rw [halen]; exact hjlt
      obtain ⟨k, hkeq⟩ : ∃ k, m₀ - j1.val = k + 1 := ⟨m₀ - j1.val - 1, by omega⟩
      rw [hkeq] at hc1 hinv1
      step as ⟨e, he⟩
      have hRe : Reduced e := by rw [he]; exact hared _ (List.getElem_mem halt)
      have hev : ptFlat a j1.val = toExt e := by
        rw [ptFlat, List.getD_eq_getElem _ _ halt, he]
      step with eval_mle_layer_spec (k := k) c1 e hc1 hRe as ⟨c2, hc2, hfold⟩
      step as ⟨j2, hj2⟩
      have hj2v : j2.val = j1.val + 1 := by scalar_tac
      have hkeq2 : m₀ - j2.val = k := by omega
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [hkeq2]; exact hc2
      · simp only [mleFold] at hinv1
        rw [show ptFlat a (j1.val + 0) = toExt e from by rw [Nat.add_zero, hev],
          ← toEvals_evalMleLayer c2 c1 (toExt e) hfold,
          show (fun i => ptFlat a (j1.val + (i + 1)))
            = (fun i => ptFlat a (j2.val + i)) from by
              funext i
              rw [show j1.val + (i + 1) = j2.val + i from by omega]] at hinv1
        rw [hkeq2]
        exact hinv1
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hjeq : j1.val = m₀ := by rw [← hvars] at hj1 ⊢; scalar_tac
      rw [hjeq, Nat.sub_self] at hc1 hinv1
      obtain ⟨hclen, hcred⟩ := hc1
      refine ⟨by simpa using hclen, hcred, ?_⟩
      rw [← hinv1]
      simp only [mleFold]
      exact (tableFn_apply (m := 0) c1 ⟨0, by norm_num⟩).symm
  · exact ⟨hj, hcur, hinv⟩

/-- `w_table_mle_eval` computes `wTableMleEval`, the evaluation claim the
final-evaluation step carries (`Constraints.lean:335`).

The body is the `O(2^m₀)` layer fold, not the `O(m₀·2^m₀)` Lagrange dot the
specification names (opt: `HachiEquiv.Opt.w_table_mle_eval.opt`, `lean/Opt.lean`);
`mleFold_eq_evalMle` and CompPoly's `eval_mle_eq_eval` are what carry it back to
`CMlPolynomialEval.eval`, so the statement does not move.

*Statement modified*: the hypothesis `hmax : μ + n * 8 ≤ Usize.max` was added.
It is `w_table_spec`'s own bound, and this function inherits it through
`c_w_table_mle_values`: `w_table_row` forms `rows * GADGET_DIGITS` as a checked
`usize`, so without the bound the extracted code can *fail* and no postcondition
holds of it. Nothing in `RepLiftedWitness` implies it -- the `Vec` model bounds
each length on its own, not the arity sum -- and `end_piece_check_spec`, the only
caller, carries the same hypothesis already. -/
theorem w_table_mle_eval_spec {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (m0 : Std.Usize)
    (a : alloc.vec.Vec cpoly.field.Ext4)
    (hw : RepLiftedWitness w sw) (ha : WfPoint m0.val a)
    (hm0 : 2 ^ m0.val ≤ Usize.max) (hmax : μ + n * 8 ≤ Usize.max) :
    zerocheck.w_table_mle_eval w m0 a
      ⦃ out => Reduced out ∧ toExt out =
        InnerOuter.wTableMleEval Φ m0.val phiF 16 sw (toPoint (m := m0.val) a) ⦄ := by
  have h0 : (0#usize : Std.Usize).val = 0 := by scalar_tac
  rw [zerocheck.w_table_mle_eval]
  step with c_w_table_mle_values_spec (μ := μ) (n := n) w sw m0 hw hm0 hmax
    as ⟨cur, hclen, hcred, hcval⟩
  have hWcur : WfEvals m0.val cur := ⟨hclen, hcred⟩
  have htgt : mleFold m0.val (toEvals (m := m0.val) cur) (fun i => ptFlat a i)
      = InnerOuter.wTableMleEval Φ m0.val phiF 16 sw (toPoint (m := m0.val) a) := by
    rw [mleFold_eq_evalMle, toEvals_eq_cWTableMle sw cur hcval,
      CMlPolynomialEval.eval_mle_eq_eval, InnerOuter.wTableMleEval]
    rfl
  step with w_table_mle_eval_loop_spec (m₀ := m0.val) a (alloc.vec.Vec.len a) cur 0#usize
    (InnerOuter.wTableMleEval Φ m0.val phiF 16 sw (toPoint (m := m0.val) a))
    ha (by simpa using ha.1) (by simp)
    (by simp only [h0, Nat.sub_zero]; exact hWcur)
    (by simp only [h0, Nat.zero_add]; exact htgt)
    as ⟨o, holen, hored, hoval⟩
  have hbnd : (0 : ℕ) < o.val.length := by rw [holen]; norm_num
  have hgd : o.val.getD 0 cpoly.field.Ext4.ZERO = o.val[0] :=
    List.getD_eq_getElem _ _ hbnd
  step as ⟨z, hz⟩
  have hmem : z ∈ o.val := by rw [hz]; exact List.getElem_mem hbnd
  refine ⟨hored _ hmem, ?_⟩
  rw [hz, ← hgd]
  exact hoval

/-- The values vector, read as ArkLib's `CMlPolynomialEval F m₀`, is the
specification's `H₀`. -/
theorem toEvals_eq_hZero {μ n m₀ : ℕ} (sw : InnerOuter.LiftedWitness Φ μ n)
    (o : alloc.vec.Vec cpoly.field.Ext4)
    (hval : ∀ t < 2 ^ m₀, toExt (o.val.getD t cpoly.field.Ext4.ZERO) =
      InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t)) :
    toEvals (m := m₀) o = InnerOuter.hZero Φ m₀ phiF 16 sw := by
  rw [toEvals, InnerOuter.hZero]
  refine congrArg Vector.ofFn (funext fun j => ?_)
  rw [hval j.val j.isLt, wTableFlat, dif_pos j.isLt, Fin.eta]

/-- The inner loop of `h_zero`: the row's coefficients with the range factor
applied to each as it is produced. Same shape as
`c_w_table_mle_values_loop0_loop0_spec`, one `range_product_base` further on --
the factor is computed in `Fp` and embedded once, so the `Ext4::from_base` now
comes *after* it (candidate G); the Lean side is
`HachiEquiv.Opt.blockLoopBase` at `g = fun c => phiF (range_product_base.opt 16 c)`
(opt: `HachiEquiv.Opt.h_zero.opt2`, `lean/Opt.lean`). -/
theorem h_zero_loop0_loop0_spec {μ n m₀ : ℕ}
    (sw : InnerOuter.LiftedWitness Φ μ n) (size : Std.Usize) (r : ring.Rq) (base : ℕ)
    (values : alloc.vec.Vec cpoly.field.Ext4) (idx l : Std.Usize) (hr : Wf r)
    (hg : ∀ k, k < N → base + k < 2 ^ m₀ →
      phiF ((toRq r).1.coeff k) = wTableFlat m₀ sw (base + k))
    (hm0 : 2 ^ m₀ ≤ Usize.max) (hsize : size.val = 2 ^ m₀) (hl : l.val ≤ N)
    (hidx : idx.val = base + l.val) (hidxle : idx.val ≤ 2 ^ m₀)
    (hlen : values.val.length = idx.val) (hred : VecReduced values)
    (hval : ∀ t < idx.val, toExt (values.val.getD t cpoly.field.Ext4.ZERO) =
      InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t)) :
    zerocheck.h_zero_loop0_loop0 size params.RING_DEGREE values idx r l
      ⦃ (o, x) => x.val = min (base + N) (2 ^ m₀) ∧ o.val.length = x.val ∧
        VecReduced o ∧ ∀ t < x.val,
          toExt (o.val.getD t cpoly.field.Ext4.ZERO) =
            InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t) ⦄ := by
  have hrd : (params.RING_DEGREE).val = N := params_RING_DEGREE_val
  rw [zerocheck.h_zero_loop0_loop0]
  apply loop.spec_decr_nat (fun s => N - s.2.2.val)
    (fun s => s.2.2.val ≤ N ∧ s.2.1.val = base + s.2.2.val ∧ s.2.1.val ≤ 2 ^ m₀ ∧
      s.1.val.length = s.2.1.val ∧ VecReduced s.1 ∧
      ∀ t < s.2.1.val, toExt (s.1.val.getD t cpoly.field.Ext4.ZERO) =
        InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t))
  · rintro ⟨v1, x1, l1⟩ ⟨hl1, hx1, hx1le, hlen1, hred1, hval1⟩
    dsimp only at hl1 hx1 hx1le hlen1 hred1 hval1
    simp only [zerocheck.h_zero_loop0_loop0.body]
    by_cases hlt : l1 < params.RING_DEGREE
    · rw [if_pos hlt]
      have hllt : l1.val < N := by rw [← hrd]; scalar_tac
      by_cases hlt2 : x1 < size
      · rw [if_pos hlt2]
        have hxlt : x1.val < 2 ^ m₀ := by rw [← hsize]; scalar_tac
        step with RqBridge.coeff_spec r l1 hr as ⟨f, hRf, hf⟩
        step with range_product_base_spec f hRf as ⟨f1, hRf1, hf1⟩
        step with ext_from_base_spec f1 hRf1 as ⟨e, hRe, he⟩
        have hentry : toExt e =
            InnerOuter.rangeProduct 16 (wTableFlat m₀ sw x1.val) := by
          rw [he, ← phiF_apply, hf1, hf, hx1,
            hg l1.val hllt (by rw [← hx1]; exact hxlt)]
        have hbound : v1.val.length < Usize.max := by omega
        step as ⟨v2, hv2⟩
        step as ⟨l2, hl2⟩
        step as ⟨x2, hx2⟩
        have hl2v : l2.val = l1.val + 1 := by scalar_tac
        have hx2v : x2.val = x1.val + 1 := by scalar_tac
        refine ⟨by omega, by omega, by omega, ?_, ?_, ?_, by omega⟩
        · rw [hx2v, hv2, List.length_append, hlen1]; simp
        · intro y hy
          rw [hv2] at hy
          rcases List.mem_append.mp hy with h | h
          · exact hred1 y h
          · rw [List.mem_singleton.mp h]; exact hRe
        · intro t ht
          rw [hx2v] at ht
          rcases Nat.lt_or_ge t x1.val with htlt | htge
          · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
          · have hteq : t = v1.val.length := by omega
            rw [hteq, hv2, getD_append_eq, hentry, hlen1]
      · rw [if_neg hlt2, WP.spec_ok]
        dsimp only
        have hge : size.val ≤ x1.val := by scalar_tac
        rw [hsize] at hge
        rw [show min (base + N) (2 ^ m₀) = x1.val from by omega]
        exact ⟨rfl, hlen1, hred1, hval1⟩
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hlge : N ≤ l1.val := by rw [← hrd]; scalar_tac
      rw [show min (base + N) (2 ^ m₀) = x1.val from by omega]
      exact ⟨rfl, hlen1, hred1, hval1⟩
  · exact ⟨hl, hidx, hidxle, hlen, hred, hval⟩

/-- The outer loop of `h_zero`: one `w_table_row` per row; the Lean side is
`HachiEquiv.Opt.rowLoopBase` at `g = fun c => phiF (range_product_base.opt 16 c)`. -/
theorem h_zero_loop0_spec {μ n m₀ : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (size : Std.Usize)
    (values : alloc.vec.Vec cpoly.field.Ext4) (u idx : Std.Usize)
    (hw : RepLiftedWitness w sw) (hmax : μ + n * 8 ≤ Usize.max)
    (hm0 : 2 ^ m₀ ≤ Usize.max) (hsize : size.val = 2 ^ m₀)
    (hidx : idx.val = min (N * u.val) (2 ^ m₀))
    (hlen : values.val.length = idx.val) (hred : VecReduced values)
    (hval : ∀ t < idx.val, toExt (values.val.getD t cpoly.field.Ext4.ZERO) =
      InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t)) :
    zerocheck.h_zero_loop0 w size params.RING_DEGREE values u idx
      ⦃ o => o.val.length = 2 ^ m₀ ∧ VecReduced o ∧
        ∀ t < 2 ^ m₀, toExt (o.val.getD t cpoly.field.Ext4.ZERO) =
          InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t) ⦄ := by
  have hN : 0 < N := by norm_num
  have h1v : (1#usize : Std.Usize).val = 1 := by scalar_tac
  rw [zerocheck.h_zero_loop0]
  apply loop.spec_decr_nat (fun s => 2 ^ m₀ - s.2.2.val)
    (fun s => s.2.2.val = min (N * s.2.1.val) (2 ^ m₀) ∧ s.1.val.length = s.2.2.val ∧
      VecReduced s.1 ∧
      ∀ t < s.2.2.val, toExt (s.1.val.getD t cpoly.field.Ext4.ZERO) =
        InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t))
  · rintro ⟨v1, u1, x1⟩ ⟨hx1, hlen1, hred1, hval1⟩
    dsimp only at hx1 hlen1 hred1 hval1
    simp only [zerocheck.h_zero_loop0.body]
    by_cases hlt : x1 < size
    · rw [if_pos hlt]
      have hxlt : x1.val < 2 ^ m₀ := by rw [← hsize]; scalar_tac
      have hbase : x1.val = N * u1.val := by omega
      step with w_table_row_spec w sw u1 hw hmax as ⟨r, hWr, hrow⟩
      have hg : ∀ k, k < N → N * u1.val + k < 2 ^ m₀ →
          phiF ((toRq r).1.coeff k) = wTableFlat m₀ sw (N * u1.val + k) := by
        intro k hk hklt
        rw [hrow k hk, wTableFlat_at_block sw hk hklt]
      step with h_zero_loop0_loop0_spec (m₀ := m₀) sw size r (N * u1.val)
        v1 x1 0#usize hWr hg hm0 hsize (by simp) (by rw [hbase]; simp) (by omega)
        hlen1 hred1 hval1 as ⟨v2, x2, hx2, hlen2, hred2, hval2⟩
      step as ⟨u2, hu2⟩
      have hu2v : u2.val = u1.val + 1 := by omega
      refine ⟨?_, hlen2, hred2, hval2, by omega⟩
      rw [hx2, hu2v, Nat.mul_add, Nat.mul_one]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hge : size.val ≤ x1.val := by scalar_tac
      rw [hsize] at hge
      have hxeq : x1.val = 2 ^ m₀ := by omega
      exact ⟨by rw [hlen1, hxeq], hred1, by rw [← hxeq]; exact hval1⟩
  · exact ⟨hidx, hlen, hred, hval⟩

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
  step with h_zero_loop0_spec (m₀ := m0.val) w sw size
    (alloc.vec.Vec.with_capacity cpoly.field.Ext4 size) 0#usize 0#usize hw hmax hm0 hsize
    (by simp) (by simp [alloc.vec.Vec.with_capacity])
    (by intro y hy; simp [alloc.vec.Vec.with_capacity] at hy)
    (by intro t ht; simp at ht) as ⟨o, hlen, hred, hval⟩
  simp only [cpoly.multilinear.MultilinearEvals.from_values, WP.spec_ok]
  exact ⟨⟨hlen, hred⟩, toEvals_eq_hZero sw o hval⟩

/-- The inner loop of `h_zero_is_zero`: the same traversal with a `Bool` state,
running branchless to the end. The verdict needs no embedding at all: the Rust
tests `range_product_base(…).is_zero()` in `Fp` and `phiF_eq_zero_iff` reflects
that to the specification's extension factor (candidate G). The Lean side is
`HachiEquiv.Opt.zeroBlockLoopBase` (opt:
`HachiEquiv.Opt.h_zero_is_zero.opt2`, `lean/Opt.lean`). -/
theorem h_zero_is_zero_loop0_loop0_spec {μ n m₀ : ℕ}
    (sw : InnerOuter.LiftedWitness Φ μ n) (size : Std.Usize) (r : ring.Rq) (base : ℕ)
    (zero : Bool) (idx l : Std.Usize) (hr : Wf r)
    (hg : ∀ k, k < N → base + k < 2 ^ m₀ →
      phiF ((toRq r).1.coeff k) = wTableFlat m₀ sw (base + k))
    (hsize : size.val = 2 ^ m₀) (hl : l.val ≤ N)
    (hidx : idx.val = base + l.val) (hidxle : idx.val ≤ 2 ^ m₀)
    (hzero : zero = true ↔ ∀ t < idx.val,
      InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t) = 0) :
    zerocheck.h_zero_is_zero_loop0_loop0 size params.RING_DEGREE zero idx r l
      ⦃ (b, x) => x.val = min (base + N) (2 ^ m₀) ∧
        (b = true ↔ ∀ t < x.val,
          InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t) = 0) ⦄ := by
  have hrd : (params.RING_DEGREE).val = N := params_RING_DEGREE_val
  rw [zerocheck.h_zero_is_zero_loop0_loop0]
  apply loop.spec_decr_nat (fun s => N - s.2.2.val)
    (fun s => s.2.2.val ≤ N ∧ s.2.1.val = base + s.2.2.val ∧ s.2.1.val ≤ 2 ^ m₀ ∧
      (s.1 = true ↔ ∀ t < s.2.1.val,
        InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t) = 0))
  · rintro ⟨b1, x1, l1⟩ ⟨hl1, hx1, hx1le, hb1⟩
    dsimp only at hl1 hx1 hx1le hb1
    simp only [zerocheck.h_zero_is_zero_loop0_loop0.body]
    by_cases hlt : l1 < params.RING_DEGREE
    · rw [if_pos hlt]
      have hllt : l1.val < N := by rw [← hrd]; scalar_tac
      by_cases hlt2 : x1 < size
      · rw [if_pos hlt2]
        have hxlt : x1.val < 2 ^ m₀ := by rw [← hsize]; scalar_tac
        step with RqBridge.coeff_spec r l1 hr as ⟨f, hRf, hf⟩
        step with range_product_base_spec f hRf as ⟨f1, hRf1, hf1⟩
        have hentry : phiF (toK f1) =
            InnerOuter.rangeProduct 16 (wTableFlat m₀ sw x1.val) := by
          rw [hf1, hf, hx1, hg l1.val hllt (by rw [← hx1]; exact hxlt)]
        step with fp_is_zero_spec f1 hRf1 as ⟨bz, hbz0⟩
        have hbz : bz = true ↔
            InnerOuter.rangeProduct 16 (wTableFlat m₀ sw x1.val) = 0 := by
          rw [hbz0, ← hentry, phiF_eq_zero_iff]
        by_cases hbzt : bz = true
        · rw [if_pos hbzt]
          simp only [bind_tc_ok]
          step as ⟨l2, hl2⟩
          step as ⟨x2, hx2⟩
          have hl2v : l2.val = l1.val + 1 := by scalar_tac
          have hx2v : x2.val = x1.val + 1 := by scalar_tac
          refine ⟨by omega, by omega, by omega, ?_, by omega⟩
          rw [hx2v, hb1]
          constructor
          · intro h t ht
            rcases Nat.lt_or_ge t x1.val with htlt | htge
            · exact h t htlt
            · have hteq : t = x1.val := by omega
              rw [hteq]
              exact hbz.mp hbzt
          · intro h t ht
            exact h t (by omega)
        · rw [if_neg hbzt]
          simp only [bind_tc_ok]
          step as ⟨l2, hl2⟩
          step as ⟨x2, hx2⟩
          have hl2v : l2.val = l1.val + 1 := by scalar_tac
          have hx2v : x2.val = x1.val + 1 := by scalar_tac
          refine ⟨by omega, by omega, by omega, ?_, by omega⟩
          rw [hx2v]
          simp only [Bool.false_eq_true, false_iff, not_forall]
          exact ⟨x1.val, by omega, fun h => hbzt (hbz.mpr h)⟩
      · rw [if_neg hlt2, WP.spec_ok]
        dsimp only
        have hge : size.val ≤ x1.val := by scalar_tac
        rw [hsize] at hge
        rw [show min (base + N) (2 ^ m₀) = x1.val from by omega]
        exact ⟨rfl, hb1⟩
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hlge : N ≤ l1.val := by rw [← hrd]; scalar_tac
      rw [show min (base + N) (2 ^ m₀) = x1.val from by omega]
      exact ⟨rfl, hb1⟩
  · exact ⟨hl, hidx, hidxle, hzero⟩

/-- The outer loop of `h_zero_is_zero`: one `w_table_row` per row; the Lean side
is `HachiEquiv.Opt.zeroRowLoopBase`. -/
theorem h_zero_is_zero_loop0_spec {μ n m₀ : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (size : Std.Usize) (zero : Bool)
    (u idx : Std.Usize)
    (hw : RepLiftedWitness w sw) (hmax : μ + n * 8 ≤ Usize.max)
    (hm0 : 2 ^ m₀ ≤ Usize.max) (hsize : size.val = 2 ^ m₀)
    (hidx : idx.val = min (N * u.val) (2 ^ m₀))
    (hzero : zero = true ↔ ∀ t < idx.val,
      InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t) = 0) :
    zerocheck.h_zero_is_zero_loop0 w size params.RING_DEGREE zero u idx
      ⦃ b => (b = true ↔
        ∀ t < 2 ^ m₀, InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t) = 0) ⦄ := by
  have hN : 0 < N := by norm_num
  have h1v : (1#usize : Std.Usize).val = 1 := by scalar_tac
  rw [zerocheck.h_zero_is_zero_loop0]
  apply loop.spec_decr_nat (fun s => 2 ^ m₀ - s.2.2.val)
    (fun s => s.2.2.val = min (N * s.2.1.val) (2 ^ m₀) ∧
      (s.1 = true ↔ ∀ t < s.2.2.val,
        InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t) = 0))
  · rintro ⟨b1, u1, x1⟩ ⟨hx1, hb1⟩
    dsimp only at hx1 hb1
    simp only [zerocheck.h_zero_is_zero_loop0.body]
    by_cases hlt : x1 < size
    · rw [if_pos hlt]
      have hxlt : x1.val < 2 ^ m₀ := by rw [← hsize]; scalar_tac
      have hbase : x1.val = N * u1.val := by omega
      step with w_table_row_spec w sw u1 hw hmax as ⟨r, hWr, hrow⟩
      have hg : ∀ k, k < N → N * u1.val + k < 2 ^ m₀ →
          phiF ((toRq r).1.coeff k) = wTableFlat m₀ sw (N * u1.val + k) := by
        intro k hk hklt
        rw [hrow k hk, wTableFlat_at_block sw hk hklt]
      step with h_zero_is_zero_loop0_loop0_spec (m₀ := m₀) sw size r (N * u1.val)
        b1 x1 0#usize hWr hg hsize (by simp) (by rw [hbase]; simp) (by omega)
        hb1 as ⟨b2, x2, hx2, hb2⟩
      step as ⟨u2, hu2⟩
      have hu2v : u2.val = u1.val + 1 := by omega
      refine ⟨?_, hb2, by omega⟩
      rw [hx2, hu2v, Nat.mul_add, Nat.mul_one]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hge : size.val ≤ x1.val := by scalar_tac
      rw [hsize] at hge
      have hxeq : x1.val = 2 ^ m₀ := by omega
      rw [hb1, hxeq]
  · exact ⟨hidx, hzero⟩

/-- `h_zero_is_zero` **decides** `hZero = 0`, in the pointwise form of
`hZero_eq_zero_iff` (`Constraints.lean:219`).

An `↔`, not an implication: a verifier that rejected everything would satisfy
the accepting direction alone, and the rejection path is the half a broken
implementation still passes.

Carries the same `μ + n * 8 ≤ Usize.max` as `w_table_spec`, which it calls. -/
theorem h_zero_is_zero_spec {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (m0 : Std.Usize)
    (hw : RepLiftedWitness w sw) (hm0 : 2 ^ m0.val ≤ Usize.max)
    (hmax : μ + n * 8 ≤ Usize.max) :
    zerocheck.h_zero_is_zero w m0
      ⦃ b => (b = true ↔ InnerOuter.hZero Φ m0.val phiF 16 sw = 0) ⦄ := by
  rw [zerocheck.h_zero_is_zero]
  step with two_pow_spec m0 hm0 as ⟨size, hsize⟩
  apply spec_mono (h_zero_is_zero_loop0_spec (m₀ := m0.val) w sw size true 0#usize 0#usize
    hw hmax hm0 hsize (by simp) (by simp))
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
  obtain ⟨hlen, hred⟩ := ht
  rw [zerocheck.eq_weight_loop]
  apply loop.spec_decr_nat (fun st => m₁ - st.2.2.val)
    (fun st => st.2.2.val ≤ m₁ ∧ st.2.1.val = i.val / 2 ^ st.2.2.val ∧ Reduced st.1 ∧
      toExt st.1 = ∏ s ∈ Finset.range st.2.2.val,
        (if Nat.testBit i.val s then toExt (tau1.val.getD s cpoly.field.Ext4.ZERO)
          else 1 - toExt (tau1.val.getD s cpoly.field.Ext4.ZERO)))
  · rintro ⟨a1, q1, j1⟩ ⟨hj1, hq1, hR1, hv1⟩
    dsimp only at hj1 hq1 hR1 hv1
    simp only [zerocheck.eq_weight_loop.body]
    by_cases hlt : j1 < vars
    · rw [if_pos hlt]
      have hjlt : j1.val < m₁ := by rw [← hvars]; scalar_tac
      have hidx : j1.val < tau1.val.length := by rw [hlen]; exact hjlt
      have hRget : Reduced tau1.val[j1.val] := hred _ (List.getElem_mem hidx)
      have hgetD : tau1.val.getD j1.val cpoly.field.Ext4.ZERO = tau1.val[j1.val] :=
        List.getD_eq_getElem _ _ hidx
      step as ⟨bit, hbit⟩
      have hbitv : bit.val = i.val / 2 ^ j1.val % 2 := by rw [hbit, hq1]
      by_cases hb : bit = 1#usize
      · have hbitone : Nat.testBit i.val j1.val = true := by
          rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq, ← hbitv]
          scalar_tac
        rw [if_pos hb]
        step as ⟨fac, hfac⟩
        step with ext_mul_spec a1 fac hR1 (by rw [hfac]; exact hRget) as ⟨a2, hR2, ha2⟩
        step as ⟨q2, hq2⟩
        step as ⟨j2, hj2⟩
        have hj2v : j2.val = j1.val + 1 := by scalar_tac
        refine ⟨by omega, ?_, hR2, ?_, by omega⟩
        · rw [hq2, hq1, hj2v, pow_succ, Nat.div_div_eq_div_mul]
        · rw [ha2, hv1, hj2v, Finset.prod_range_succ, hfac, if_pos hbitone, hgetD]
      · have hbitzero : Nat.testBit i.val j1.val = false := by
          rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not, ← hbitv]
          intro h
          exact hb (by scalar_tac)
        rw [if_neg hb]
        step as ⟨e, he⟩
        step with ext_sub_spec cpoly.field.Ext4.ONE e reduced_ONE (by rw [he]; exact hRget)
          as ⟨fac, hRfac, hfac⟩
        step with ext_mul_spec a1 fac hR1 hRfac as ⟨a2, hR2, ha2⟩
        step as ⟨q2, hq2⟩
        step as ⟨j2, hj2⟩
        have hj2v : j2.val = j1.val + 1 := by scalar_tac
        refine ⟨by omega, ?_, hR2, ?_, by omega⟩
        · rw [hq2, hq1, hj2v, pow_succ, Nat.div_div_eq_div_mul]
        · rw [ha2, hv1, hj2v, Finset.prod_range_succ, hfac, he, if_neg (by simp [hbitzero]),
            hgetD, toExt_ONE]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : j1.val = m₁ := by rw [← hvars] at hj1 ⊢; scalar_tac
      exact ⟨hR1, by rw [hv1, heq]⟩
  · exact ⟨hj, hq, hacc, hval⟩

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
  rw [zerocheck.eq_weight]
  apply spec_mono (eq_weight_loop_spec (m₁ := m₁) tau1 i (alloc.vec.Vec.len tau1)
    cpoly.field.Ext4.ONE i 0#usize ht (by simpa using ht.1) (by simp) reduced_ONE
    (by simp) (by simp))
  rintro out ⟨hR, hv⟩
  exact ⟨hR, by rw [hv, lagrangeBasis_get_toPoint tau1 ⟨i.val, hi⟩]⟩

/-- The loop of `below_two_pow`: `q` is the running quotient `i / 2 ^ k`. -/
theorem below_two_pow_loop_spec (i m q k : Std.Usize)
    (hk : k.val ≤ m.val) (hq : q.val = i.val / 2 ^ k.val) :
    zerocheck.below_two_pow_loop m q k
      ⦃ out => out.val = i.val / 2 ^ m.val ⦄ := by
  rw [zerocheck.below_two_pow_loop]
  apply loop.spec_decr_nat (fun s => m.val - s.2.val)
    (fun s => s.2.val ≤ m.val ∧ s.1.val = i.val / 2 ^ s.2.val)
  · rintro ⟨q1, k1⟩ ⟨hk1, hq1⟩
    dsimp only at hk1 hq1
    simp only [zerocheck.below_two_pow_loop.body]
    by_cases hlt : k1 < m
    · rw [if_pos hlt]
      step as ⟨q2, hq2⟩
      step as ⟨k2, hk2⟩
      have hk2v : k2.val = k1.val + 1 := by scalar_tac
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hq2, hq1, hk2v, pow_succ, Nat.div_div_eq_div_mul]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = m.val := by scalar_tac
      rw [hq1, heq]
  · exact ⟨hk, hq⟩

/-- `below_two_pow` decides the specification's cube guard `i < 2 ^ m`.

**No hypothesis at all**, which is the point of the item: halving `i` exactly
`m` times cannot fail, so the decision procedure is total at every `m` --
including those where `2 ^ m` exceeds `Usize.max` and the previous
`i < two_pow m` wrapped to zero. An equality of decisions rather than an
implication, per the house rule for decision procedures. -/
theorem below_two_pow_spec (i m : Std.Usize) :
    zerocheck.below_two_pow i m
      ⦃ b => b = true ↔ i.val < 2 ^ m.val ⦄ := by
  rw [zerocheck.below_two_pow]
  step with below_two_pow_loop_spec i m i 0#usize (by simp) (by simp) as ⟨out, hout⟩
  simp only [decide_eq_true_eq]
  have hzero : out = 0#usize ↔ out.val = 0 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; scalar_tac
  rw [hzero, hout, Nat.div_eq_zero_iff]
  simp
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
  have hrd : (params.RING_DEGREE).val = N := params_RING_DEGREE_val
  have hlen : (alloc.vec.Vec.len tau1).val = m₁ := by simpa using htau.1
  rw [zerocheck.alpha_public_evals_loop]
  apply loop.spec_decr_nat (fun st => n - st.2.val)
    (fun st => st.2.val ≤ n ∧ Reduced st.1 ∧ toExt st.1 =
      ∑ t ∈ Finset.range st.2.val, apTerm (m₁ := m₁) rs (toExt alpha) tau1 (idx.val / N) t)
  · rintro ⟨s1, i1⟩ ⟨hi1, hR1, hv1⟩
    dsimp only at hi1 hR1 hv1
    simp only [zerocheck.alpha_public_evals_loop.body]
    by_cases hlt : i1 < rows
    · rw [if_pos hlt]
      have hilt : i1.val < n := by rw [← hrows]; scalar_tac
      step with below_two_pow_spec i1 (alloc.vec.Vec.len tau1) as ⟨b, hb⟩
      rw [hlen] at hb
      by_cases hbt : b = true
      · have hcube : i1.val < 2 ^ m₁ := hb.mp hbt
        rw [if_pos hbt]
        step with eq_weight_spec (m₁ := m₁) tau1 i1 htau hcube as ⟨weight, hRw, hw⟩
        step as ⟨u, hu⟩
        have huv : u.val = idx.val / N := by rw [hu, hrd]
        step with m_alpha_tilde_spec (n := n) (μ := μ) s rs alpha i1 u hs ha hilt hmax
          as ⟨e, hRe, he⟩
        step with ext_mul_spec weight e hRw hRe as ⟨e1, hRe1, he1⟩
        step with ext_add_spec s1 e1 hR1 hRe1 as ⟨s2, hR2, hs2⟩
        step as ⟨i2, hi2⟩
        have hi2v : i2.val = i1.val + 1 := by scalar_tac
        refine ⟨by omega, hR2, ?_, by omega⟩
        rw [hs2, hv1, he1, hw, he, huv, hi2v, Finset.sum_range_succ, apTerm,
          dif_pos hilt, dif_pos hcube]
      · have hcube : ¬ i1.val < 2 ^ m₁ := fun h => hbt (hb.mpr h)
        rw [if_neg hbt]
        step as ⟨i2, hi2⟩
        have hi2v : i2.val = i1.val + 1 := by scalar_tac
        refine ⟨by omega, hR1, ?_, by omega⟩
        rw [hv1, hi2v, Finset.sum_range_succ, apTerm, dif_pos hilt, dif_neg hcube, add_zero]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n := by rw [← hrows] at hi1 ⊢; scalar_tac
      exact ⟨hR1, by rw [hv1, heq]⟩
  · exact ⟨hi, hRsum, hval⟩

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
  have hrd : (params.RING_DEGREE).val = N := params_RING_DEGREE_val
  have hrows : (alloc.vec.Vec.len s.m).val = n := by simpa using hs.1.1
  rw [zerocheck.alpha_public_evals]
  simp only [ringswitch.RlinStatement.impl.m, linalg.PolyMatrix.rows, bind_tc_ok]
  step with alpha_public_evals_loop_spec (n := n) (μ := μ) (m₁ := m₁) s rs alpha tau1 idx
    (alloc.vec.Vec.len s.m) cpoly.field.Ext4.ZERO 0#usize hs ha ht hmax hrows (by simp)
    reduced_ZERO (by simp) as ⟨sum, hRsum, hsum⟩
  step as ⟨l, hl⟩
  have hlv : l.val = idx.val % N := by rw [hl, hrd]
  step with alpha_tilde_spec alpha l ha as ⟨e, hRe, he⟩
  apply spec_mono (ext_mul_spec e sum hRe hRsum)
  rintro out ⟨hRout, hout⟩
  refine ⟨hRout, ?_⟩
  rw [hout, he, hsum, hlv, InnerOuter.alphaPublicEvals]
  simp only [Equiv.apply_symm_apply, phi_natDegree]
  congr 1
  rw [sum_fin_eq_sum_range_dite]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases htn : t < n
  · rw [dif_pos htn, apTerm, dif_pos htn]
    by_cases h2 : t < 2 ^ m₁
    · rw [dif_pos h2, dif_pos h2, lagrangeBasis_get_eq_cube_prod]
    · rw [dif_neg h2, dif_neg h2]
  · rw [dif_neg htn, apTerm, dif_neg htn]

/-! ### The three hoisted tables of candidate C

`sumcheck::alpha_public_table`'s accepted champion (`hachi/src/sumcheck.rs:433`)
builds three tables once and reads them per cube entry: the `d`-entry power
table `α^ℓ`, the `n` equality weights, and the `n × (μ + n·δ)` public matrix at
`α` with `φ(α)` and the digit weights `b^e` computed once. The specs below are
what `alpha_public_table_spec` (`lean/Sumcheck.lean`) composes; the pure algebra
is `HachiEquiv.Opt`'s `alphaPowTable`, `eqWeightTable` and `mAlphaTable`
(opt: `lean/Opt.lean` § "Candidate C", licensed entrywise by
`alphaPowTable_getD`, `eqWeightTable_getD` and `mAlphaTable_getD_eq`), and these
statements are the entrywise shapes those lemmas license.

`Opt.lean` imports this file, so nothing here may refer to it; the loop
invariants are small enough to re-establish directly, and the one pure fact the
traversal genuinely needs -- `mAlphaTilde_eq_zero_of_ge`, the absent columns --
lives here now. -/

/-- Outside the stored columns the specification's matrix is zero -- read
straight off `mAlphaTilde` (`Constraints.lean:517`) at `δ = 8`.

This is what lets `m_alpha_table` store `μ + n·δ` columns and
`alpha_public_table`'s `u < cols` guard drop the rest: past the guard the
summand is not merely unstored, it is the specification's own `0`. Moved here
from `lean/Opt.lean` so that the spec layer can use it without importing the
candidate layer. -/
theorem mAlphaTilde_eq_zero_of_ge {n μ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ)
    (α : F) (i : Fin n) {u : ℕ} (hu : μ + n * 8 ≤ u) :
    InnerOuter.mAlphaTilde Φ phiF 16 rs α i u = 0 := by
  rw [InnerOuter.mAlphaTilde, rhoDigitCount_eq, dif_neg (by omega), if_neg (by omega)]

/-- `PolyMatrix::cols` is **total**: an empty matrix reports `0` columns rather
than failing, so the width is only pinned once there is a row.

`poly_matrix_cols_spec` needs `0 < rows` because it reads row `0`. Both table
builders below reach `cols` before they know `n > 0` -- at `n = 0` the row loop
never runs and the width never matters -- so they need this shape instead. The
`c.val ≤ cols` half is what discharges the checked `mu + rows * δ` at `n = 0`. -/
theorem poly_matrix_cols_le_spec {rows cols : ℕ} (a : linalg.PolyMatrix)
    (ha : WfMat rows cols a) :
    linalg.PolyMatrix.cols a ⦃ c => c.val ≤ cols ∧ (0 < rows → c.val = cols) ⦄ := by
  have hlen : a.val.length = rows := ha.1
  rw [linalg.PolyMatrix.cols]
  by_cases hz : alloc.vec.Vec.len a = 0#usize
  · rw [if_pos hz, WP.spec_ok]
    have hrows : rows = 0 := by rw [← hlen]; scalar_tac
    exact ⟨by simp, by rw [hrows]; intro h; exact absurd h (by omega)⟩
  · rw [if_neg hz]
    have h0lt : 0 < a.val.length := by scalar_tac
    have hrows : 0 < rows := by rw [← hlen]; exact h0lt
    step as ⟨pv, hpv⟩
    have hWpv : WfVec cols pv := by rw [hpv]; exact ha.2 _ (List.getElem_mem h0lt)
    simp only [linalg.PolyVec.len, WP.spec_ok]
    have hc : (alloc.vec.Vec.len pv).val = cols := by simpa using hWpv.1
    exact ⟨by rw [hc], fun _ => hc⟩

/-- The loop of `alpha_pow_table`: state `(out, pw, l)`, with `out` holding
`α^0 … α^(l−1)` and `pw` the running power `α^l`. One multiplication per entry,
where `alpha_tilde` pays `ℓ` per call. -/
theorem alpha_pow_table_loop_spec (alpha : cpoly.field.Ext4) (d : Std.Usize)
    (out : alloc.vec.Vec cpoly.field.Ext4) (pw : cpoly.field.Ext4) (l : Std.Usize)
    (ha : Reduced alpha) (hl : l.val ≤ d.val) (hlen : out.val.length = l.val)
    (hred : VecReduced out) (hRpw : Reduced pw) (hpw : toExt pw = toExt alpha ^ l.val)
    (hval : ∀ t < l.val, toExt (out.val.getD t cpoly.field.Ext4.ZERO) = toExt alpha ^ t) :
    zerocheck.alpha_pow_table_loop alpha d out pw l
      ⦃ o => o.val.length = d.val ∧ VecReduced o ∧
        ∀ t < d.val, toExt (o.val.getD t cpoly.field.Ext4.ZERO) = toExt alpha ^ t ⦄ := by
  have hdmax : d.val ≤ Usize.max := by scalar_tac
  rw [zerocheck.alpha_pow_table_loop]
  apply loop.spec_decr_nat (fun st => d.val - st.2.2.val)
    (fun st => st.2.2.val ≤ d.val ∧ st.1.val.length = st.2.2.val ∧ VecReduced st.1 ∧
      Reduced st.2.1 ∧ toExt st.2.1 = toExt alpha ^ st.2.2.val ∧
      ∀ t < st.2.2.val, toExt (st.1.val.getD t cpoly.field.Ext4.ZERO) = toExt alpha ^ t)
  · rintro ⟨v1, p1, l1⟩ ⟨hl1, hlen1, hred1, hRp1, hp1, hval1⟩
    dsimp only at hl1 hlen1 hred1 hRp1 hp1 hval1
    simp only [zerocheck.alpha_pow_table_loop.body]
    by_cases hlt : l1 < d
    · rw [if_pos hlt]
      have hllt : l1.val < d.val := by scalar_tac
      have hbound : v1.val.length < Usize.max := by omega
      step as ⟨v2, hv2⟩
      step with ext_mul_spec p1 alpha hRp1 ha as ⟨p2, hRp2, hp2⟩
      step as ⟨l2, hl2⟩
      have hl2v : l2.val = l1.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, ?_, hRp2, ?_, ?_, by omega⟩
      · rw [hl2v, hv2, List.length_append, hlen1]; simp
      · intro y hy
        rw [hv2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hred1 y h
        · rw [List.mem_singleton.mp h]; exact hRp1
      · rw [hp2, hp1, hl2v, pow_succ]
      · intro t ht
        rw [hl2v] at ht
        rcases Nat.lt_or_ge t l1.val with htlt | htge
        · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = v1.val.length := by omega
          rw [hteq, hv2, getD_append_eq, hp1, hlen1]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : l1.val = d.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hred1, by rw [← heq]; exact hval1⟩
  · exact ⟨hl, hlen, hred, hRpw, hpw, hval⟩

/-- `alpha_pow_table` tabulates `alphaTilde α ℓ = α ^ ℓ` (`Constraints.lean:502`)
for `ℓ < d`, at one multiplication per entry.

**No side condition.** A `Vec` of length `d` already fits -- the type carries
`≤ Usize.max` -- and the only fallible arithmetic is the counter's `l + 1` under
the guard `l < d`, so nothing here forms a value the caller has to bound. -/
theorem alpha_pow_table_spec (alpha : cpoly.field.Ext4) (d : Std.Usize)
    (ha : Reduced alpha) :
    zerocheck.alpha_pow_table alpha d
      ⦃ out => out.val.length = d.val ∧ VecReduced out ∧
        ∀ l < d.val, toExt (out.val.getD l cpoly.field.Ext4.ZERO) = toExt alpha ^ l ⦄ := by
  rw [zerocheck.alpha_pow_table]
  exact alpha_pow_table_loop_spec alpha d
    (alloc.vec.Vec.with_capacity cpoly.field.Ext4 d) cpoly.field.Ext4.ONE 0#usize ha
    (by simp) (by simp [alloc.vec.Vec.with_capacity])
    (by intro y hy; simp [alloc.vec.Vec.with_capacity] at hy) reduced_ONE (by simp)
    (by intro t ht; simp at ht)

/-- The weight of row `i` in the `m₁`-cube: the `∏ j : Fin m₁` factor of
`alphaPublicEvals` (`Constraints.lean:845-847`) inside the specification's own
`i < 2 ^ m₁` guard, and `0` outside it.

The guard is carried, not assumed: at the pinned `n = 5 ≤ 8 = 2 ^ 3` it never
fires, and a parameter move that broke `n ≤ 2 ^ m₁` must not silently change
what the table holds. -/
noncomputable def eqWeightVal {m₁ : ℕ} (tau1 : alloc.vec.Vec cpoly.field.Ext4) (i : ℕ) : F :=
  if h : i < 2 ^ m₁ then
    (CMlPolynomialEval.lagrangeBasis (Vector.ofFn (toPoint (m := m₁) tau1))).get ⟨i, h⟩
  else 0

/-- `apTerm` factored through the weight table: for a row index in range the
summand is the stored weight times the stored matrix entry, the guard having
been absorbed into `eqWeightVal`. -/
theorem apTerm_eq_mul {n μ m₁ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ) (alpha : F)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) (u : ℕ) {t : ℕ} (ht : t < n) :
    apTerm (m₁ := m₁) rs alpha tau1 u t
      = eqWeightVal (m₁ := m₁) tau1 t *
        InnerOuter.mAlphaTilde Φ phiF 16 rs alpha ⟨t, ht⟩ u := by
  rw [apTerm, dif_pos ht, eqWeightVal]
  by_cases h : t < 2 ^ m₁
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, zero_mul]

/-- `alphaPublicEvals` at a flat cube index, as the power times the row sum the
table traversal computes -- the entrywise identity the hoisted form needs, and
the tail of `alpha_public_evals_spec`'s own proof factored out. -/
theorem alphaPublicEvals_eq_pow_mul_sum {n μ m₀ m₁ : ℕ}
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : F)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) (idx : ℕ) (hidx : idx < 2 ^ m₀) :
    InnerOuter.alphaPublicEvals Φ m₀ m₁ phiF 16 rs alpha (toPoint (m := m₁) tau1)
        (finFunctionFinEquiv.symm ⟨idx, hidx⟩)
      = alpha ^ (idx % N) *
        ∑ t ∈ Finset.range n, apTerm (m₁ := m₁) rs alpha tau1 (idx / N) t := by
  rw [InnerOuter.alphaPublicEvals]
  simp only [Equiv.apply_symm_apply, phi_natDegree, InnerOuter.alphaTilde]
  congr 1
  rw [sum_fin_eq_sum_range_dite]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases htn : t < n
  · rw [dif_pos htn, apTerm, dif_pos htn]
    by_cases h2 : t < 2 ^ m₁
    · rw [dif_pos h2, dif_pos h2, lagrangeBasis_get_eq_cube_prod]
    · rw [dif_neg h2, dif_neg h2]
  · rw [dif_neg htn, apTerm, dif_neg htn]

/-- The loop of `eq_weight_table`: one entry per row, the specification's cube
guard decided by `below_two_pow` so that no power of two is formed. -/
theorem eq_weight_table_loop_spec {m₁ : ℕ} (tau1 : alloc.vec.Vec cpoly.field.Ext4)
    (n vars : Std.Usize) (out : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize)
    (htau : WfPoint m₁ tau1) (hvars : vars.val = m₁) (hi : i.val ≤ n.val)
    (hlen : out.val.length = i.val) (hred : VecReduced out)
    (hval : ∀ t < i.val, toExt (out.val.getD t cpoly.field.Ext4.ZERO) =
      eqWeightVal (m₁ := m₁) tau1 t) :
    zerocheck.eq_weight_table_loop tau1 n vars out i
      ⦃ o => o.val.length = n.val ∧ VecReduced o ∧
        ∀ t < n.val, toExt (o.val.getD t cpoly.field.Ext4.ZERO) =
          eqWeightVal (m₁ := m₁) tau1 t ⦄ := by
  have hnmax : n.val ≤ Usize.max := by scalar_tac
  rw [zerocheck.eq_weight_table_loop]
  apply loop.spec_decr_nat (fun st => n.val - st.2.val)
    (fun st => st.2.val ≤ n.val ∧ st.1.val.length = st.2.val ∧ VecReduced st.1 ∧
      ∀ t < st.2.val, toExt (st.1.val.getD t cpoly.field.Ext4.ZERO) =
        eqWeightVal (m₁ := m₁) tau1 t)
  · rintro ⟨v1, i1⟩ ⟨hi1, hlen1, hred1, hval1⟩
    dsimp only at hi1 hlen1 hred1 hval1
    simp only [zerocheck.eq_weight_table_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hilt : i1.val < n.val := by scalar_tac
      have hbound : v1.val.length < Usize.max := by omega
      have hpush : ∀ (e : cpoly.field.Ext4), Reduced e →
          toExt e = eqWeightVal (m₁ := m₁) tau1 i1.val →
          alloc.vec.Vec.push v1 e
            ⦃ r => r.val.length = i1.val + 1 ∧ VecReduced r ∧
              ∀ t < i1.val + 1, toExt (r.val.getD t cpoly.field.Ext4.ZERO) =
                eqWeightVal (m₁ := m₁) tau1 t ⦄ := by
        intro e hRe hev
        step as ⟨v2, hv2⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [hv2, List.length_append, hlen1]; simp
        · intro y hy
          rw [hv2] at hy
          rcases List.mem_append.mp hy with h | h
          · exact hred1 y h
          · rw [List.mem_singleton.mp h]; exact hRe
        · intro t ht
          rcases Nat.lt_or_ge t i1.val with htlt | htge
          · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
          · have hteq : t = v1.val.length := by omega
            rw [hteq, hv2, getD_append_eq, hev, hlen1]
      step with below_two_pow_spec i1 vars as ⟨b, hb⟩
      rw [hvars] at hb
      have hrow : (if b = true then
            (do let e ← zerocheck.eq_weight tau1 i1
                alloc.vec.Vec.push v1 e)
          else alloc.vec.Vec.push v1 cpoly.field.Ext4.ZERO)
            ⦃ r => r.val.length = i1.val + 1 ∧ VecReduced r ∧
              ∀ t < i1.val + 1, toExt (r.val.getD t cpoly.field.Ext4.ZERO) =
                eqWeightVal (m₁ := m₁) tau1 t ⦄ := by
        by_cases hbt : b = true
        · have hcube : i1.val < 2 ^ m₁ := hb.mp hbt
          rw [if_pos hbt]
          step with eq_weight_spec (m₁ := m₁) tau1 i1 htau hcube as ⟨e, hRe, he⟩
          exact hpush e hRe (by rw [he, eqWeightVal, dif_pos hcube])
        · have hcube : ¬ i1.val < 2 ^ m₁ := fun h => hbt (hb.mpr h)
          rw [if_neg hbt]
          exact hpush cpoly.field.Ext4.ZERO reduced_ZERO
            (by rw [toExt_ZERO, eqWeightVal, dif_neg hcube])
      step with hrow as ⟨v2, hlen2, hred2, hval2⟩
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = i1.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, hred2, ?_, by omega⟩
      · rw [hi2v]; exact hlen2
      · rw [hi2v]; exact hval2
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hred1, by rw [← heq]; exact hval1⟩
  · exact ⟨hi, hlen, hred, hval⟩

/-- `eq_weight_table` tabulates the `m₁`-cube equality weight of each of the `n`
rows, under the specification's own `i < 2 ^ m₁` guard.

**Unconditional**, for `eq_weight_spec`'s and `below_two_pow_spec`'s reasons: the
bits are read by a running quotient and the guard is decided by halving, so no
power of two is ever formed. -/
theorem eq_weight_table_spec {m₁ : ℕ} (tau1 : alloc.vec.Vec cpoly.field.Ext4)
    (n : Std.Usize) (ht : WfPoint m₁ tau1) :
    zerocheck.eq_weight_table tau1 n
      ⦃ out => out.val.length = n.val ∧ VecReduced out ∧
        ∀ i < n.val, toExt (out.val.getD i cpoly.field.Ext4.ZERO) =
          eqWeightVal (m₁ := m₁) tau1 i ⦄ := by
  rw [zerocheck.eq_weight_table]
  exact eq_weight_table_loop_spec tau1 n (alloc.vec.Vec.len tau1)
    (alloc.vec.Vec.with_capacity cpoly.field.Ext4 n) 0#usize ht (by simpa using ht.1)
    (by simp) (by simp [alloc.vec.Vec.with_capacity])
    (by intro y hy; simp [alloc.vec.Vec.with_capacity] at hy)
    (by intro t ht'; simp at ht')

/-- Row `i` of a table of tables, read the way the `getD` layer reads every
other extracted container. -/
def tableRow (mt : alloc.vec.Vec (alloc.vec.Vec cpoly.field.Ext4)) (i : ℕ) :
    alloc.vec.Vec cpoly.field.Ext4 :=
  mt.val.getD i (alloc.vec.Vec.new cpoly.field.Ext4)

/-- The inner loop of `m_alpha_table`: one row of `μ + n·δ` columns, in
`mAlphaTilde`'s three cases.

`φ(α)` and the digit weights `b^e` arrive as arguments -- the champion computes
them once for the whole table -- so `hphi` and `hbp` say what they are; the
entry value is then `mAlphaTilde`'s by its own definition, exactly as
`m_alpha_tilde_spec` computes it per call. The loop guard `u < cols` already
gives the specification's `u < μ + n·δ`, so only the digit-block test `(u −
μ)/δ = i` is decided here. -/
theorem m_alpha_table_loop0_loop0_spec {n μ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (mu cols : Std.Usize) (phi_alpha : cpoly.field.Ext4)
    (bp : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize)
    (row : alloc.vec.Vec cpoly.field.Ext4) (u : Std.Usize)
    (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha) (hi : i.val < n)
    (hmu : mu.val = μ) (hcols : cols.val = μ + n * 8)
    (hRphi : Reduced phi_alpha)
    (hphi : toExt phi_alpha = InnerOuter.cEvalAt phiF (toExt alpha) Φ.φ)
    (hbplen : bp.val.length = 8) (hbpred : VecReduced bp)
    (hbp : ∀ e < 8, toExt (bp.val.getD e cpoly.field.Ext4.ZERO) = phiF ((16 : ZMod q) ^ e))
    (hu : u.val ≤ cols.val) (hlen : row.val.length = u.val) (hred : VecReduced row)
    (hval : ∀ t < u.val, toExt (row.val.getD t cpoly.field.Ext4.ZERO) =
      InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨i.val, hi⟩ t) :
    zerocheck.m_alpha_table_loop0_loop0 s alpha params.GADGET_DIGITS mu cols phi_alpha bp
      i row u
      ⦃ o => o.val.length = μ + n * 8 ∧ VecReduced o ∧
        ∀ t < μ + n * 8, toExt (o.val.getD t cpoly.field.Ext4.ZERO) =
          InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨i.val, hi⟩ t ⦄ := by
  obtain ⟨hWm, hWy, hmeq, hyeq, hbeq⟩ := hs
  have hgd : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  have hcmax : cols.val ≤ Usize.max := by scalar_tac
  have hrowlt : i.val < s.m.val.length := by rw [hWm.1]; exact hi
  rw [zerocheck.m_alpha_table_loop0_loop0]
  apply loop.spec_decr_nat (fun st => cols.val - st.2.val)
    (fun st => st.2.val ≤ cols.val ∧ st.1.val.length = st.2.val ∧ VecReduced st.1 ∧
      ∀ t < st.2.val, toExt (st.1.val.getD t cpoly.field.Ext4.ZERO) =
        InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨i.val, hi⟩ t)
  · rintro ⟨v1, u1⟩ ⟨hu1, hlen1, hred1, hval1⟩
    dsimp only at hu1 hlen1 hred1 hval1
    simp only [zerocheck.m_alpha_table_loop0_loop0.body]
    by_cases hlt : u1 < cols
    · rw [if_pos hlt]
      have hult : u1.val < cols.val := by scalar_tac
      have hultc : u1.val < μ + n * 8 := by rw [← hcols]; exact hult
      have hbound : v1.val.length < Usize.max := by omega
      have hpush : ∀ (e : cpoly.field.Ext4) (v2 : alloc.vec.Vec cpoly.field.Ext4),
          Reduced e →
          toExt e = InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨i.val, hi⟩ u1.val →
          v2.val = v1.val ++ [e] →
          v2.val.length = u1.val + 1 ∧ VecReduced v2 ∧
            ∀ t < u1.val + 1, toExt (v2.val.getD t cpoly.field.Ext4.ZERO) =
              InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨i.val, hi⟩ t := by
        intro e v2 hRe hev hv2
        refine ⟨?_, ?_, ?_⟩
        · rw [hv2, List.length_append, hlen1]; simp
        · intro y hy
          rw [hv2] at hy
          rcases List.mem_append.mp hy with h | h
          · exact hred1 y h
          · rw [List.mem_singleton.mp h]; exact hRe
        · intro t ht
          rcases Nat.lt_or_ge t u1.val with htlt | htge
          · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
          · have hteq : t = v1.val.length := by omega
            rw [hteq, hv2, getD_append_eq, hev, hlen1]
      have htail : ∀ (e : cpoly.field.Ext4), Reduced e →
          toExt e = InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨i.val, hi⟩ u1.val →
          ∀ (v2 : alloc.vec.Vec cpoly.field.Ext4), v2.val = v1.val ++ [e] →
          ∀ (u2 : Std.Usize), u2.val = u1.val + 1 →
            u2.val ≤ cols.val ∧ v2.val.length = u2.val ∧ VecReduced v2 ∧
              (∀ t < u2.val, toExt (v2.val.getD t cpoly.field.Ext4.ZERO) =
                InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨i.val, hi⟩ t) ∧
              cols.val - u2.val < cols.val - u1.val := by
        intro e hRe hev v2 hv2 u2 hu2v
        obtain ⟨h1, h2, h3⟩ := hpush e v2 hRe hev hv2
        exact ⟨by omega, by rw [hu2v]; exact h1, h2, by rw [hu2v]; exact h3, by omega⟩
      by_cases hltmu : u1 < mu
      · rw [if_pos hltmu]
        have humu : u1.val < μ := by rw [← hmu]; scalar_tac
        simp only [ringswitch.RlinStatement.impl.m, linalg.PolyMatrix.row, bind_tc_ok]
        step as ⟨pv, hpv⟩
        have hWpv : WfVec μ pv := by rw [hpv]; exact hWm.2 _ (List.getElem_mem hrowlt)
        have hulen : u1.val < pv.val.length := by rw [hWpv.1]; exact humu
        simp only [linalg.PolyVec.get]
        step as ⟨r, hr⟩
        have hWr : Wf r := by rw [hr]; exact hWpv.2 _ (List.getElem_mem hulen)
        step with c_eval_at_spec alpha r ha hWr as ⟨e, hRe, he⟩
        have hentry : rs.M ⟨i.val, hi⟩ ⟨u1.val, humu⟩ = toRq r := by
          rw [← hmeq, toMat_apply]
          show toVec (k := μ) (s.m.val.getD i.val (alloc.vec.Vec.new ring.Rq))
            ((⟨u1.val, humu⟩ : Fin μ)) = toRq r
          rw [toVec]
          show toRq ((s.m.val.getD i.val (alloc.vec.Vec.new ring.Rq)).val.getD u1.val
            (alloc.vec.Vec.new cpoly.field.Fp)) = toRq r
          rw [List.getD_eq_getElem _ _ hrowlt, ← hpv, List.getD_eq_getElem _ _ hulen, hr]
        have hev : toExt e =
            InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨i.val, hi⟩ u1.val := by
          rw [InnerOuter.mAlphaTilde, rhoDigitCount_eq, dif_pos humu, he, hentry]
        step as ⟨v2, hv2⟩
        step as ⟨u2, hu2⟩
        exact htail e hRe hev v2 hv2 u2 (by scalar_tac)
      · rw [if_neg hltmu]
        have humu : ¬ u1.val < μ := by rw [← hmu]; scalar_tac
        step as ⟨j1, hj1⟩
        have hj1v : j1.val = u1.val - μ := by rw [hj1, hmu]
        step as ⟨j2, hj2⟩
        have hj2v : j2.val = (u1.val - μ) / 8 := by rw [hj2, hgd, hj1v]
        by_cases heq : j2 = i
        · rw [if_pos heq]
          have hdiv : (u1.val - μ) / 8 = i.val := by rw [← hj2v, heq]
          step as ⟨e, he⟩
          have hev : e.val = (u1.val - μ) % 8 := by rw [he, hgd, hj1v]
          have helt : e.val < 8 := by rw [hev]; omega
          have hbplt : e.val < bp.val.length := by rw [hbplen]; exact helt
          step with ext_sub_spec cpoly.field.Ext4.ZERO phi_alpha reduced_ZERO hRphi
            as ⟨e1, hRe1, he1⟩
          step as ⟨e2, he2⟩
          have he2' : e2 = bp.val.getD e.val cpoly.field.Ext4.ZERO := by
            rw [List.getD_eq_getElem _ _ hbplt, he2]
          have hRe2 : Reduced e2 := by
            rw [he2]; exact hbpred _ (List.getElem_mem hbplt)
          have he2v : toExt e2 = phiF ((16 : ZMod q) ^ e.val) := by
            rw [he2']; exact hbp e.val helt
          step with ext_mul_spec e1 e2 hRe1 hRe2 as ⟨e3, hRe3, he3⟩
          have hentryv : toExt e3 =
              InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨i.val, hi⟩ u1.val := by
            rw [InnerOuter.mAlphaTilde, rhoDigitCount_eq, dif_neg humu,
              if_pos ⟨hultc, hdiv⟩, he3, he1, he2v, toExt_ZERO, hphi, zero_sub, hev]
            simp only [Nat.cast_ofNat]
          step as ⟨v2, hv2⟩
          step as ⟨u2, hu2⟩
          exact htail e3 hRe3 hentryv v2 hv2 u2 (by scalar_tac)
        · rw [if_neg heq]
          have hdiv : ¬ ((u1.val - μ) / 8 = i.val) := by
            intro h
            exact heq (by scalar_tac)
          have hentryv : toExt cpoly.field.Ext4.ZERO =
              InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨i.val, hi⟩ u1.val := by
            rw [InnerOuter.mAlphaTilde, rhoDigitCount_eq, dif_neg humu,
              if_neg (by rintro ⟨-, h⟩; exact hdiv h), toExt_ZERO]
          step as ⟨v2, hv2⟩
          step as ⟨u2, hu2⟩
          exact htail cpoly.field.Ext4.ZERO reduced_ZERO hentryv v2 hv2 u2 (by scalar_tac)
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : u1.val = cols.val := by scalar_tac
      rw [hcols] at heq
      exact ⟨by rw [hlen1, heq], hred1, by rw [← heq]; exact hval1⟩
  · exact ⟨hu, hlen, hred, hval⟩

/-- The outer loop of `m_alpha_table`: one row per constraint row.

`hmu` and `hcols` are guarded by `0 < n` because at `n = 0` the extracted
`PolyMatrix::cols` reports `0` rather than `μ` (there is no row to measure) and
the row loop never runs -- the degenerate case the headline has to survive,
since `alpha_public_table_spec` assumes nothing about `n`. -/
theorem m_alpha_table_loop0_spec {n μ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (mu rows cols : Std.Usize) (phi_alpha : cpoly.field.Ext4)
    (bp : alloc.vec.Vec cpoly.field.Ext4)
    (out : alloc.vec.Vec (alloc.vec.Vec cpoly.field.Ext4)) (i : Std.Usize)
    (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (hrows : rows.val = n) (hmu : 0 < n → mu.val = μ)
    (hcols : 0 < n → cols.val = μ + n * 8) (hRphi : Reduced phi_alpha)
    (hphi : toExt phi_alpha = InnerOuter.cEvalAt phiF (toExt alpha) Φ.φ)
    (hbplen : bp.val.length = 8) (hbpred : VecReduced bp)
    (hbp : ∀ e < 8, toExt (bp.val.getD e cpoly.field.Ext4.ZERO) = phiF ((16 : ZMod q) ^ e))
    (hi : i.val ≤ n) (hlen : out.val.length = i.val)
    (hval : ∀ (t : ℕ) (ht : t < n), t < i.val →
      (tableRow out t).val.length = μ + n * 8 ∧ VecReduced (tableRow out t) ∧
      ∀ c < μ + n * 8, toExt ((tableRow out t).val.getD c cpoly.field.Ext4.ZERO) =
        InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨t, ht⟩ c) :
    zerocheck.m_alpha_table_loop0 s alpha params.GADGET_DIGITS mu rows cols phi_alpha bp
      out i
      ⦃ o => o.val.length = n ∧ ∀ (t : ℕ) (ht : t < n),
        (tableRow o t).val.length = μ + n * 8 ∧ VecReduced (tableRow o t) ∧
        ∀ c < μ + n * 8, toExt ((tableRow o t).val.getD c cpoly.field.Ext4.ZERO) =
          InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨t, ht⟩ c ⦄ := by
  have hnmax : n ≤ Usize.max := by rw [← hrows]; scalar_tac
  rw [zerocheck.m_alpha_table_loop0]
  apply loop.spec_decr_nat (fun st => n - st.2.val)
    (fun st => st.2.val ≤ n ∧ st.1.val.length = st.2.val ∧
      ∀ (t : ℕ) (ht : t < n), t < st.2.val →
        (tableRow st.1 t).val.length = μ + n * 8 ∧ VecReduced (tableRow st.1 t) ∧
        ∀ c < μ + n * 8, toExt ((tableRow st.1 t).val.getD c cpoly.field.Ext4.ZERO) =
          InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨t, ht⟩ c)
  · rintro ⟨v1, i1⟩ ⟨hi1, hlen1, hval1⟩
    dsimp only at hi1 hlen1 hval1
    simp only [zerocheck.m_alpha_table_loop0.body]
    by_cases hlt : i1 < rows
    · rw [if_pos hlt]
      have hilt : i1.val < n := by rw [← hrows]; scalar_tac
      have hnpos : 0 < n := by omega
      step with m_alpha_table_loop0_loop0_spec (n := n) (μ := μ) s rs alpha mu cols
        phi_alpha bp i1 (alloc.vec.Vec.with_capacity cpoly.field.Ext4 cols) 0#usize
        hs ha hilt (hmu hnpos) (hcols hnpos) hRphi hphi
        hbplen hbpred hbp (by simp) (by simp [alloc.vec.Vec.with_capacity])
        (by intro y hy; simp [alloc.vec.Vec.with_capacity] at hy)
        (by intro t ht; simp at ht) as ⟨r1, hrlen, hrred, hrval⟩
      have hbound : v1.val.length < Usize.max := by omega
      step as ⟨v2, hv2⟩
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = i1.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [hi2v, hv2, List.length_append, hlen1]; simp
      · intro t ht htlt
        rw [hi2v] at htlt
        rcases Nat.lt_or_ge t i1.val with hlt' | hge'
        · have hrow : tableRow v2 t = tableRow v1 t := by
            rw [tableRow, tableRow, hv2, getD_append_lt _ _ _ (by omega)]
          rw [hrow]
          exact hval1 t ht hlt'
        · have hteq : t = i1.val := by omega
          have hrow : tableRow v2 t = r1 := by
            rw [tableRow, hv2, hteq, ← hlen1, getD_append_eq]
          have hfin : (⟨t, ht⟩ : Fin n) = ⟨i1.val, hilt⟩ := Fin.ext hteq
          rw [hrow, hfin]
          exact ⟨hrlen, hrred, hrval⟩
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n := by rw [← hrows] at hi1 ⊢; scalar_tac
      exact ⟨by rw [hlen1, heq], fun t ht => hval1 t ht (by rw [heq]; exact ht)⟩
  · exact ⟨hi, hlen, hval⟩

/-- `m_alpha_table` tabulates `mAlphaTilde` (`Constraints.lean:517`): `n` rows of
`μ + n·δ` columns, with `φ(α)` evaluated once for the whole table and the digit
weights `b^e` read from an `δ`-entry power table instead of recomputed per
column.

`hmax` is `m_alpha_tilde_spec`'s own arity bound, and the same checked
`mu + rows·δ` forces it here. Columns `u ≥ μ + n·δ` are not stored:
`mAlphaTilde_eq_zero_of_ge` says the specification is `0` there, which is what
lets `alpha_public_table`'s `u < cols` guard drop them. -/
theorem m_alpha_table_spec {n μ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha)
    (hmax : μ + n * 8 ≤ Usize.max) :
    zerocheck.m_alpha_table s alpha
      ⦃ out => out.val.length = n ∧ ∀ (i : ℕ) (hi : i < n),
        (tableRow out i).val.length = μ + n * 8 ∧ VecReduced (tableRow out i) ∧
        ∀ u < μ + n * 8, toExt ((tableRow out i).val.getD u cpoly.field.Ext4.ZERO) =
          InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨i, hi⟩ u ⦄ := by
  have hWm : WfMat n μ s.m := hs.1
  have hgd : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  have hrows : (alloc.vec.Vec.len s.m).val = n := by simpa using hWm.1
  rw [zerocheck.m_alpha_table]
  simp only [ringswitch.RlinStatement.impl.m, linalg.PolyMatrix.rows, bind_tc_ok]
  step with poly_matrix_cols_le_spec (rows := n) (cols := μ) s.m hWm as ⟨mu, hmule, hmu⟩
  have hmulbound : (alloc.vec.Vec.len s.m).val * (params.GADGET_DIGITS).val ≤ Usize.max := by
    rw [hrows, hgd]; omega
  step as ⟨j1, hj1⟩
  have hj1v : j1.val = n * 8 := by rw [hj1, hrows, hgd]
  have haddbound : mu.val + j1.val ≤ Usize.max := by rw [hj1v]; omega
  step as ⟨cols, hcols⟩
  have hcolsv : 0 < n → cols.val = μ + n * 8 := by
    intro hn; rw [hcols, hmu hn, hj1v]
  step with c_eval_at_modulus_spec alpha ha as ⟨phi_alpha, hRphi, hphi⟩
  step with HachiEquiv.Scheme.base_pow_spec 1#usize as ⟨f, hRf, hf⟩
  have hf' : toK f = (16 : ZMod q) := by rw [hf]; simp
  step with ext_from_base_spec f hRf as ⟨base, hRbase, hbase⟩
  step with alpha_pow_table_spec base params.GADGET_DIGITS hRbase as ⟨bp, hbplen, hbpred, hbpv⟩
  rw [hgd] at hbplen hbpv
  have hbp : ∀ e < 8, toExt (bp.val.getD e cpoly.field.Ext4.ZERO)
      = phiF ((16 : ZMod q) ^ e) := by
    intro e he
    rw [hbpv e he, hbase, hf', ← phiF_apply, ← map_pow]
  exact m_alpha_table_loop0_spec (n := n) (μ := μ) s rs alpha mu (alloc.vec.Vec.len s.m)
    cols phi_alpha bp (alloc.vec.Vec.with_capacity (alloc.vec.Vec cpoly.field.Ext4)
    (alloc.vec.Vec.len s.m)) 0#usize hs ha hrows hmu hcolsv hRphi hphi hbplen hbpred hbp
    (by simp) (by simp [alloc.vec.Vec.with_capacity])
    (by intro t ht htlt; simp at htlt)
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
  obtain ⟨hWm, hWy, hmeq, hyeq, hbeq⟩ := hs
  have hlen : (alloc.vec.Vec.len tau1).val = m₁ := by simpa using htau.1
  rw [zerocheck.zc_target_alpha_loop]
  apply loop.spec_decr_nat (fun st => n - st.2.val)
    (fun st => st.2.val ≤ n ∧ Reduced st.1 ∧ toExt st.1 =
      ∑ t ∈ Finset.range st.2.val, zcTerm (m₁ := m₁) rs (toExt alpha) tau1 t)
  · rintro ⟨s1, i1⟩ ⟨hi1, hR1, hv1⟩
    dsimp only at hi1 hR1 hv1
    simp only [zerocheck.zc_target_alpha_loop.body]
    by_cases hlt : i1 < rows
    · rw [if_pos hlt]
      have hilt : i1.val < n := by rw [← hrows]; scalar_tac
      have hylt : i1.val < s.yvec.val.length := by rw [hWy.1]; exact hilt
      step with below_two_pow_spec i1 (alloc.vec.Vec.len tau1) as ⟨b, hb⟩
      rw [hlen] at hb
      by_cases hbt : b = true
      · have hcube : i1.val < 2 ^ m₁ := hb.mp hbt
        rw [if_pos hbt]
        step with eq_weight_spec (m₁ := m₁) tau1 i1 htau hcube as ⟨weight, hRw, hw⟩
        simp only [ringswitch.RlinStatement.impl.yvec, linalg.PolyVec.get, bind_tc_ok]
        step as ⟨r, hr⟩
        have hWr : Wf r := by rw [hr]; exact hWy.2 _ (List.getElem_mem hylt)
        have hentry : (rs.yvec ⟨i1.val, hilt⟩).1 = (toRq r).1 := by
          rw [← hyeq]
          show (toRq (s.yvec.val.getD i1.val (alloc.vec.Vec.new cpoly.field.Fp))).1 = (toRq r).1
          rw [List.getD_eq_getElem _ _ hylt, hr]
        step with c_eval_at_spec alpha r ha hWr as ⟨e, hRe, he⟩
        step with ext_mul_spec weight e hRw hRe as ⟨e1, hRe1, he1⟩
        step with ext_add_spec s1 e1 hR1 hRe1 as ⟨s2, hR2, hs2⟩
        step as ⟨i2, hi2⟩
        have hi2v : i2.val = i1.val + 1 := by scalar_tac
        refine ⟨by omega, hR2, ?_, by omega⟩
        rw [hs2, hv1, he1, hw, he, hi2v, Finset.sum_range_succ, zcTerm,
          dif_pos hilt, dif_pos hcube, hentry]
      · have hcube : ¬ i1.val < 2 ^ m₁ := fun h => hbt (hb.mpr h)
        rw [if_neg hbt]
        step as ⟨i2, hi2⟩
        have hi2v : i2.val = i1.val + 1 := by scalar_tac
        refine ⟨by omega, hR1, ?_, by omega⟩
        rw [hv1, hi2v, Finset.sum_range_succ, zcTerm, dif_pos hilt, dif_neg hcube, add_zero]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n := by rw [← hrows] at hi1 ⊢; scalar_tac
      exact ⟨hR1, by rw [hv1, heq]⟩
  · exact ⟨hi, hRsum, hval⟩

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
  have hrows : (alloc.vec.Vec.len s.yvec).val = n := by simpa using hs.2.1.1
  rw [zerocheck.zc_target_alpha]
  simp only [ringswitch.RlinStatement.impl.yvec, linalg.PolyVec.len, bind_tc_ok]
  apply spec_mono (zc_target_alpha_loop_spec (n := n) (μ := μ) (m₁ := m₁) s rs alpha tau1
    (alloc.vec.Vec.len s.yvec) cpoly.field.Ext4.ZERO 0#usize hs ha ht hrows (by simp)
    reduced_ZERO (by simp))
  rintro out ⟨hR, hv⟩
  refine ⟨hR, ?_⟩
  rw [hv, InnerOuter.zcTargetAlpha, sum_fin_eq_sum_range_dite]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases htn : t < n
  · rw [dif_pos htn, zcTerm, dif_pos htn]
    by_cases h2 : t < 2 ^ m₁
    · rw [dif_pos h2, dif_pos h2, lagrangeBasis_get_eq_cube_prod]
    · rw [dif_neg h2, dif_neg h2]
  · rw [dif_neg htn, zcTerm, dif_neg htn]
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
