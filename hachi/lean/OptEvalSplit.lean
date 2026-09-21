/-
`OptEvalSplit.lean` -- the optimized variants of `hachi/src/evalsplit.rs`'s two
`Rq`-valued bases (candidates M and N), with their `opt_eq_spec` lemmas.

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
import EvalSplit
import Ext
import CompPoly.Multilinear.Basic

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly CompPoly.Extension CompPoly.Extension.Ext ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.Opt

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme

/-! # Stage 6, iteration 8 (the `Rq`-valued bases; `hachi/src/evalsplit.rs`)

## Candidate M -- `evalsplit::monomial_basis`

Strategy `opt-algo-swap`, "build the table one variable at a time". The frozen
translation reads the specification literally: entry `i` of the length-`2 ^ n`
result is a product of exactly `n` factors, one per variable, `1` where bit `j`
of `i` is clear (`hachi/src/evalsplit.rs:142`, the `crate::gadget::base_pow`
convention). That is `2 ^ n · n` ring products per call, `n - popcount i` of
them multiplications by `Rq::one()`, and at `ML_VARS_LOW = ML_VARS_HIGH = 10`
it is `10 240` schoolbook degree-1024 products -- twice over in
`quadeval::to_quad_eval_statement`, which `NOTES.md` prices at ~29 s.

The doubling build pays `2 ^ n - 1 = 1 023`. Bit `j` of every index below
`2 ^ j` is clear and bit `j` of `2 ^ j + r` is set, so the table for the prefix
`w₀ … wⱼ` is the table for `w₀ … wⱼ₋₁` followed by that same table scaled by
`wⱼ` -- no index arithmetic, no `1`-factors, and one multiplication per entry
ever written. The shape is already in this crate at `Ext4`
(`sumcheck::eq_suffix_table`, `hachi/src/sumcheck.rs:302`), which is why the
translation is trivial and the loop specs have a precedent.

Stated over a `CommSemiring`, not at `Rq`: candidate N reuses it for the
Lagrange basis.
-/

section MonomialBasis

variable {R : Type*} [CommSemiring R]

/-! ## 1. The candidate -/

/-- One level of the doubling build: the table for the prefix `w₀ … wⱼ` is the
table for `w₀ … wⱼ₋₁` followed by that same table scaled by `wⱼ`. -/
def monomial_basis.optStep (tab : List R) (x : R) : List R :=
  tab ++ tab.map (fun p => p * x)

/-- `CMlPolynomial.monomialBasis` built one variable at a time: `2 ^ n - 1`
products instead of `2 ^ n · n`. One `List.foldl` over the point, whose step is
one ascending `while` loop appending to the table the Rust already holds. -/
def monomial_basis.opt (w : List R) : List R :=
  w.foldl monomial_basis.optStep [1]

/-! ## 2. What one entry of the build is -/

@[simp] theorem monomial_basis.opt_nil : monomial_basis.opt ([] : List R) = [1] := rfl

theorem monomial_basis.opt_append (w : List R) (x : R) :
    monomial_basis.opt (w ++ [x]) = monomial_basis.optStep (monomial_basis.opt w) x := by
  simp only [monomial_basis.opt, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The build doubles: after `j` variables the table has `2 ^ j` entries. This
is the `Vec`'s length invariant, and the `2 ^ n ≤ Usize.max` the campaign's
`push` obligations need. -/
theorem monomial_basis.opt_length (w : List R) :
    (monomial_basis.opt w).length = 2 ^ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp only [monomial_basis.opt_nil, List.length_singleton, List.length_nil, pow_zero]
  | append_singleton w x ih =>
      rw [monomial_basis.opt_append, monomial_basis.optStep]
      simp only [List.length_append, List.length_map, ih, List.length_singleton]
      ring

omit [CommSemiring R] in
private theorem getD_append_lt {l₁ l₂ : List R} {t : ℕ} (h : t < l₁.length) (d : R) :
    (l₁ ++ l₂).getD t d = l₁.getD t d := by
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_append]; omega),
    List.getD_eq_getElem _ _ h, List.getElem_append_left h]

omit [CommSemiring R] in
private theorem getD_append_singleton {l : List R} {x d : R} :
    (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_append, List.length_singleton]; omega),
    List.getElem_append_right (Nat.le_refl _)]
  simp

/-- Entry `i` of the doubling build is the specification's product of the
factors of `w` that the bits of `i` select. The induction is on the point from
the right, so the step is exactly one level of the build: the low half keeps
its value because bit `j` of an index below `2 ^ j` is clear
(`Nat.testBit_eq_false_of_lt`), and the high half gains the factor `wⱼ` because
bit `j` of `2 ^ j + r` is set (`Nat.testBit_two_pow_add_eq`) while its lower
bits are `r`'s (`Nat.testBit_two_pow_add_gt`). -/
theorem monomial_basis.opt_getD (w : List R) : ∀ i : ℕ, i < 2 ^ w.length →
    (monomial_basis.opt w).getD i 1
      = ∏ t ∈ Finset.range w.length, (if Nat.testBit i t then w.getD t 1 else 1) := by
  induction w using List.reverseRecOn with
  | nil =>
      intro i hi
      simp only [List.length_nil, pow_zero] at hi
      have hi0 : i = 0 := by omega
      subst hi0
      simp only [monomial_basis.opt_nil, List.length_nil, Finset.range_zero, Finset.prod_empty]
      rfl
  | append_singleton w x ih =>
      intro i hi
      have hlen : (monomial_basis.opt w).length = 2 ^ w.length := monomial_basis.opt_length w
      have hsplit : (2 : ℕ) ^ (w.length + 1) = 2 ^ w.length + 2 ^ w.length := by ring
      simp only [List.length_append, List.length_singleton] at hi ⊢
      rw [monomial_basis.opt_append, monomial_basis.optStep, Finset.prod_range_succ]
      by_cases hsmall : i < 2 ^ w.length
      · rw [getD_append_lt (by omega) (1 : R), ih i hsmall,
          Nat.testBit_eq_false_of_lt hsmall]
        simp only [Bool.false_eq_true, if_false, mul_one]
        refine Finset.prod_congr rfl (fun t ht => ?_)
        simp only [Finset.mem_range] at ht
        rw [getD_append_lt ht (1 : R)]
      · obtain ⟨r, hrlt, rfl⟩ : ∃ r, r < 2 ^ w.length ∧ i = 2 ^ w.length + r :=
          ⟨i - 2 ^ w.length, by omega, by omega⟩
        rw [List.getD_eq_getElem
              (l := monomial_basis.opt w ++ List.map (fun p => p * x) (monomial_basis.opt w))
              (d := (1 : R)) (by simp only [List.length_append, List.length_map]; omega),
          List.getElem_append_right (by omega), List.getElem_map]
        simp only [hlen, Nat.add_sub_cancel_left]
        rw [← List.getD_eq_getElem (l := monomial_basis.opt w) (d := (1 : R)) (by omega),
          ih r hrlt, Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hrlt]
        simp only [Bool.not_false, if_true]
        rw [getD_append_singleton (l := w) (x := x) (d := (1 : R))]
        congr 1
        refine Finset.prod_congr rfl (fun t ht => ?_)
        simp only [Finset.mem_range] at ht
        rw [Nat.testBit_two_pow_add_gt ht, getD_append_lt ht (1 : R)]

/-! ## 3. The candidate's lemma -/

/-- **Candidate M's `opt_eq_spec`.** The doubling build *is*
`CMlPolynomial.monomialBasis`, as a list of the same length and the same
entries -- so `monomial_basis_spec`'s statement does not move. -/
theorem monomial_basis.opt_eq_spec {n : ℕ} (v : Vector R n) :
    monomial_basis.opt v.toList = (CMlPolynomial.monomialBasis v).toList := by
  have hvlen : v.toList.length = n := by simp
  refine List.ext_getElem
    (by simp only [monomial_basis.opt_length, hvlen, Vector.length_toList]) ?_
  intro i h₁ h₂
  have hi : i < 2 ^ n := by simpa using h₂
  have hrhs : (CMlPolynomial.monomialBasis v)[i]
      = ∏ j : Fin n, (if (BitVec.ofFin (⟨i, hi⟩ : Fin (2 ^ n))).getLsb j then v[j] else 1) := by
    simpa using CMlPolynomial.monomialBasis_getElem (w := v) ⟨i, hi⟩
  rw [← List.getD_eq_getElem (l := monomial_basis.opt v.toList) (d := (1 : R)) h₁,
    monomial_basis.opt_getD v.toList i (by rw [hvlen]; exact hi), hvlen,
    Vector.getElem_toList, hrhs,
    ← Fin.prod_univ_eq_prod_range
      (fun t => if Nat.testBit i t then v.toList.getD t 1 else 1) n]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin]
  rw [List.getD_eq_getElem (l := v.toList) (d := (1 : R)) (by simp), Vector.getElem_toList]

end MonomialBasis

/-! ## Candidate N -- `evalsplit::lagrange_basis`

The same doubling build as candidate M, specialized to the ring carrier. Both
children of an entry `p` are `p*(1-wj)` and `p*wj`; spelling the first as
`p - p*wj` makes a level cost **one** ring multiplication and one ring
subtraction per entry instead of two multiplications, so the call pays
`2^n - 1 = 1023` products at `n = 10`, where upstream's own two-multiplication
form would pay `2046` and the frozen baseline paid `2^n * n = 10240`. `Rq::sub`
is `N` coefficient subtractions against `Rq::mul`'s `N^2` products, so at
`N = 1024` the subtraction is free at this ratio.

`CommRing`, not `CommSemiring`: the clear-bit factor is `1 - x`. -/

section LagrangeBasis

variable {R : Type*} [CommRing R]

/-- One level of the doubling build, in the form the ring carrier wants:
`p·(1−x)` spelled `p − p·x`, so an entry costs **one** multiplication and one
subtraction instead of two multiplications. -/
def lagrange_basis.optStep (tab : List R) (x : R) : List R :=
  tab.map (fun p => p - p * x) ++ tab.map (fun p => p * x)

/-- The Lagrange basis built one variable at a time. -/
def lagrange_basis.optLoop (w : List R) : List R := w.foldl lagrange_basis.optStep [1]

theorem lagrange_basis.optLoop_nil : lagrange_basis.optLoop ([] : List R) = [1] := rfl

theorem lagrange_basis.optLoop_append (w : List R) (x : R) :
    lagrange_basis.optLoop (w ++ [x]) = lagrange_basis.optStep (lagrange_basis.optLoop w) x := by
  simp only [lagrange_basis.optLoop, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem lagrange_basis.optLoop_length (w : List R) : (lagrange_basis.optLoop w).length = 2 ^ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp only [lagrange_basis.optLoop_nil, List.length_singleton, List.length_nil, pow_zero]
  | append_singleton w x ih =>
      rw [lagrange_basis.optLoop_append, lagrange_basis.optStep]
      simp only [List.length_append, List.length_map, ih, List.length_singleton]
      ring

omit [CommRing R] in
private theorem lagGetD_map_lt {l : List R} {f : R → R} {t : ℕ} (h : t < l.length) (d : R) :
    (l.map f).getD t d = f (l.getD t d) := by
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_map]; omega),
    List.getD_eq_getElem _ _ h, List.getElem_map]

omit [CommRing R] in
private theorem lagGetD_append_left {l₁ l₂ : List R} {t : ℕ} (h : t < l₁.length) (d : R) :
    (l₁ ++ l₂).getD t d = l₁.getD t d := by
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_append]; omega),
    List.getD_eq_getElem _ _ h, List.getElem_append_left h]

/-- Entry `i` of the doubling build is the specification's product: `wⱼ` where
bit `j` of `i` is set, `1 − wⱼ` where it is clear. -/
theorem lagrange_basis.optLoop_getD (w : List R) : ∀ i : ℕ, i < 2 ^ w.length →
    (lagrange_basis.optLoop w).getD i 1
      = ∏ t ∈ Finset.range w.length,
        (if Nat.testBit i t then w.getD t 1 else 1 - w.getD t 1) := by
  induction w using List.reverseRecOn with
  | nil =>
      intro i hi
      simp only [List.length_nil, pow_zero] at hi
      have hi0 : i = 0 := by omega
      subst hi0
      simp only [lagrange_basis.optLoop_nil, List.length_nil, Finset.range_zero, Finset.prod_empty]
      rfl
  | append_singleton w x ih =>
      intro i hi
      have hlen : (lagrange_basis.optLoop w).length = 2 ^ w.length := lagrange_basis.optLoop_length w
      have hprefix : ∀ t, t < w.length → (w ++ [x]).getD t (1 : R) = w.getD t 1 :=
        fun t ht => lagGetD_append_left (l₁ := w) (l₂ := [x]) ht (1 : R)
      have hxlast : (w ++ [x]).getD w.length (1 : R) = x := by
        rw [List.getD_eq_getElem _ _
            (by simp only [List.length_append, List.length_singleton]; omega),
          List.getElem_append_right (Nat.le_refl _)]
        simp
      simp only [List.length_append, List.length_singleton] at hi ⊢
      rw [lagrange_basis.optLoop_append, lagrange_basis.optStep, Finset.prod_range_succ]
      have hcongr : ∀ k : ℕ, (∏ t ∈ Finset.range w.length,
              (if Nat.testBit k t then (w ++ [x]).getD t (1 : R)
                else 1 - (w ++ [x]).getD t 1))
            = ∏ t ∈ Finset.range w.length,
              (if Nat.testBit k t then w.getD t (1 : R) else 1 - w.getD t 1) :=
        fun k => Finset.prod_congr rfl (fun t ht => by
          rw [hprefix t (Finset.mem_range.mp ht)])
      by_cases hsmall : i < 2 ^ w.length
      · rw [lagGetD_append_left (l₁ := (lagrange_basis.optLoop w).map (fun p => p - p * x))
              (l₂ := (lagrange_basis.optLoop w).map (fun p => p * x)) (t := i)
              (by simp only [List.length_map]; omega) (1 : R),
          lagGetD_map_lt (l := lagrange_basis.optLoop w) (f := fun p => p - p * x) (t := i)
            (by omega) (1 : R),
          ih i hsmall, Nat.testBit_eq_false_of_lt hsmall, hxlast, hcongr i]
        simp only [Bool.false_eq_true, if_false]
        exact (mul_one_sub _ _).symm
      · obtain ⟨r, hrlt, rfl⟩ : ∃ r, r < 2 ^ w.length ∧ i = 2 ^ w.length + r :=
          ⟨i - 2 ^ w.length, by omega, by omega⟩
        rw [List.getD_eq_getElem
              (l := (lagrange_basis.optLoop w).map (fun p => p - p * x) ++ (lagrange_basis.optLoop w).map (fun p => p * x))
              (d := (1 : R))
              (by simp only [List.length_append, List.length_map]; omega),
          List.getElem_append_right (by simp only [List.length_map]; omega)]
        simp only [List.length_map, hlen, Nat.add_sub_cancel_left, List.getElem_map]
        rw [← List.getD_eq_getElem (l := lagrange_basis.optLoop w) (d := (1 : R)) (by omega), ih r hrlt,
          Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hrlt, hxlast,
          hcongr (2 ^ w.length + r)]
        simp only [Bool.not_false, if_true]
        congr 1
        refine Finset.prod_congr rfl (fun t ht => ?_)
        simp only [Finset.mem_range] at ht
        rw [Nat.testBit_two_pow_add_gt ht]

/-- `opt_eq_spec` for candidate N. -/
theorem lagrange_basis.opt_eq_spec {n : ℕ} (v : Vector R n) :
    lagrange_basis.optLoop v.toList = (CMlPolynomialEval.lagrangeBasis v).toList := by
  have hvlen : v.toList.length = n := by simp
  refine List.ext_getElem (by simp only [lagrange_basis.optLoop_length, hvlen, Vector.length_toList]) ?_
  intro i h₁ h₂
  have hi : i < 2 ^ n := by simpa using h₂
  have hrhs : (CMlPolynomialEval.lagrangeBasis v)[i]
      = ∏ j : Fin n,
          (if (BitVec.ofFin (⟨i, hi⟩ : Fin (2 ^ n))).getLsb j then v[j] else 1 - v[j]) := by
    simpa using CMlPolynomialEval.lagrangeBasis_getElem (w := v) ⟨i, hi⟩
  rw [← List.getD_eq_getElem (l := lagrange_basis.optLoop v.toList) (d := (1 : R)) h₁,
    lagrange_basis.optLoop_getD v.toList i (by rw [hvlen]; exact hi), hvlen, Vector.getElem_toList, hrhs,
    ← Fin.prod_univ_eq_prod_range
      (fun t => if Nat.testBit i t then v.toList.getD t 1 else 1 - v.toList.getD t 1) n]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin]
  rw [List.getD_eq_getElem (l := v.toList) (d := (1 : R)) (by simp), Vector.getElem_toList]

/-- The build, as one `List.foldl` over the point -- the shape `lean-to-rust`
turns into the level loop with the append loop inside it. -/
def lagrange_basis.opt (w : List R) : List R := lagrange_basis.optLoop w

end LagrangeBasis


end HachiEquiv.Opt
