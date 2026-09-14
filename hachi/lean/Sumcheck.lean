/-
Target 5's paired sumcheck (chain rows 6 and 8), **proved**, plus the
univariate carrier it rests on.

Twenty-four headline specs, all audited in `Check.lean` § 4. Proved across
three Aristotle sessions on 2026-09-10/11 -- `430518ae` (32 → 7), `c8d6894b`
(7 → 3, adopted over hand proofs of three of the seven), `3fd1e8a2` (3 → 0) --
with every headline statement byte-identical to the file as first staged;
the sessions added the helper lemmas (`cMLE_eval_update`, the interpolation
loop specs, `hypercubePoint_snoc_update`, `fold_tableFn_eq_mle`, …) and no
hypothesis. The paragraphs below are the design record from the staging.

Twenty-four `sumcheck` items carry `Mirrors` lines and had no `_spec` anywhere
(`make spec-check`, 2026-09-10; the last two, the prover's and the verifier's
halves of the round loop, landed while this file was being written). This file
states all twenty-four. It also opens
with a **design step** that NOTES.md § "What target 5's file will need first"
called for: a representation for cpoly's `UnivariatePoly`, which this tree did
not have. Every earlier carrier is a vector or a matrix; a round message is a
pair of polynomials, and the specification's `RoundMsg F b` is a pair of
`degreeLE` **subtypes of `CPolynomial F`**, whose invariant is canonicity.

# The carrier, and why it is a port

cpoly's own equivalence development (`cpoly/lean/Univariate.lean`, the file
`lean/Ext.lean` was ported from) already has the representation and the proofs
for every `cpoly.univariate` item this crate reaches — `zero`, `from_coeffs`,
`trim`, `eval`, and the two `Mul` impls `honest_compute_g` uses. Its carrier is
`toRaw : Vec Ext4 → CPolynomial.Raw F`, the coefficient array **as it stands**,
with `VecReduced` as the only invariant: canonicity is what `trim`
*establishes*, not what the representation presupposes. That is the right
call for this crate too, because the extracted code is **not canonical**:
`interpolate` returns exactly `values.len()` coefficients with a zero top
coefficient whenever the interpolant's degree is lower, `from_coeffs` never
trims, and the scalar `Mul<Ext4>` does not trim either. Only the poly×poly
`Mul` trims (once, at the end, as `CPolynomial.Raw.mul` does).

So the layer is `toRaw` (ported, with its coefficient kit and the ten specs,
names prefixed `uni_`) and, on top of it, the one new definition
`toUni v := CPolynomial.ofArray (toRaw v)` — `ofArray` **is** trim — which lands
in the specification's `CPolynomial F` and lets `RepRoundMsg` say
`toUni g.g_zero = sg.1.1` against the `degreeLE` subtype's value. The ported
proofs cross the same Lean v4.32 → v4.33.1 gap `Ext.lean`'s did; the ones that
break are left as `sorry` for the prover with the upstream script in place.

# Conventions

**Generic arities, `b = 16`, `TCom = PolyVec (Rq Φ) dRows`.** The Rust reads
`m₀` off `tau0.len()` and `m₁` off `tau1.len()` and takes `i` as an argument,
so every statement is the generic ArkLib one in `{n μ m₀ m₁ i dRows : ℕ}`; the
one pinned value is the range base `b = 16` (`GADGET_BASE`), as in
`lean/ZeroCheck.lean`. The commitment type is instantiated as `RepWEval` did
(`PolyVec (Rq Φ) dRows`, the chain's commitment). `honestComputeG` is stated
at arity `M + 1`, because that is how ArkLib types it (`Completeness.lean:74`).

**Headline and lower half.** The Mirrors lines split the round polynomial into
pieces ArkLib does not name — `round_value_zero` is "computableRoundPoly at the
`sumcheckPolyZero` summand, one node, *without* its `cEqualityPolynomial`
factor". Those pieces get **lower-half** statements in explicit field
arithmetic (`rangeSumZero`, `linSumAlpha`, `eqProd`, `fold` below, all plain
defs), and the item that mirrors an ArkLib definition *whole* gets the
headline against it: `honest_compute_g_spec` against `honestComputeG`,
`interpolate_spec` against `CLagrange.interpolateArray`, `round_check_spec`
against `roundCheck`, `round_out_spec` against `roundOut`, `final_check_spec`
against `finalCheck`, `nested_to_round_statement_spec` against
`nestedToRoundStatement`, and `honest_compute_y_spec` against
`wTableMleEval` (not `honestComputeY`, which picks up `[SampleableType F]` by
section-variable accident — the brief's Correction 5).

**The round polynomial's two forms.** ArkLib builds `computableRoundPoly`
symbolically (`CMvPolynomial.eval₂ CPolynomial.CHom`, `RoundPoly.lean:246`);
the crate samples the summand at `2b + 1 = 33` resp. `3` nodes and
interpolates. So `round_poly_zero_spec` says the interpolant **evaluates to
the node function everywhere**, not just at the nodes — true because
`rangeSumZero` is a polynomial function of degree `2b − 1 < 33` in the node —
and `honest_compute_g_spec`'s proof is then an equality of two polynomials of
degree `≤ 2b` through `computableRoundPoly_eval` (`RoundPoly.lean:316`) and
`eval_sumcheckPolyZero` (`Constraints.lean:1382`). The `CPolynomial` identity
`computableRoundPoly_toPoly` never has to appear.

**The round loop is stated as the honest run.** `roundsReductionAux` is a
`Reduction`, not a function; what the Rust computes is the honest prover's
`m₀`-fold iteration of `roundOut` on `honestComputeG`, with every
`roundCheck` passing. `honestRounds` below is that iteration, built from the
two ArkLib definitions, and `round_loop_spec` says the loop returns `some` of
its `m₀`-th statement when the initial targets are the two hypercube sums
(the two sum clauses of `nestedRoundRel`, `Constraints.lean:1443`). A failing
check returns `None`, which is the specification's `failure`
(`Rounds.lean:113`). The two halves are stated on their own as well:
`honest_round_messages_spec` (the prover, `roundProver` at
`computeG := honestComputeG`) says the wire content is `honestComputeG` at each
`honestRounds` statement, and `round_verify_loop_spec` (the verifier,
`roundVerifier`) is stated **for any messages**, honest or not, through
`verifyRounds` -- the `m₀`-fold chain of `if roundCheck then roundOut else
failure` -- so it carries both directions of every round's decision.

# Hypotheses

Every `Ext4` operation is a `Result` discharged under `Reduced`, so every
input carries its representation invariant (`WfPoint`, `WfEvals`,
`VecReduced`, the three `Rep*`), and outputs re-establish it. Value bounds,
each at a concrete fail point:

* `2 ^ m₀ ≤ Usize.max` wherever `cube_size` or `two_pow` sizes a table
  (`alpha_public_table`, `final_check`, `round_loop`, `honest_compute_y`) —
  the checked doubling, exactly `zerocheck.two_pow`'s obligation. Where only
  the *predicate* `i < 2^m` was needed, `zerocheck::below_two_pow` already
  removed the bound (NOTES.md § "Two invented powers of two, removed"); here
  the number is the output's own size and the bound is genuine.
* `μ + n * 8 ≤ Usize.max` wherever `alpha_public_evals` or `w_table` is
  reached — inherited from the four table-side specs of `ZeroCheck.lean`.
* `i < Usize.max` on `round_out`, whose `challenges.push(a)` is the one push
  not bounded by an input's length (it is the erasure of `Fin.snoc`).
* `n ≤ inv_weights.len()` on `interpolate`, read at `inv_weights[i]`; and the
  weights hypothesis itself, `w_i · ∏_{j ≠ i} (i − j) = 1`, which is what
  makes the extracted Lagrange form *be* `interpolateArray`.
* `i < m₀` on `honest_compute_g`: the specification's own side condition
  (`Fin (M + 1)` framing) and the fail point `tau0[i]`. On `eq_suffix_table`
  alone the honest bounds are weaker -- `i < Usize.max` for the checked
  `i + 1`, and `2^(m₀ − i − 1) ≤ Usize.max` for the table it builds -- and
  those are what it carries.

Promoted from `lean-wip/` on 2026-09-11; the proofs here are re-checked by
every `make build`, and a `sorry` in this file is a build failure.
-/
import EndPiece
import CompPoly.Univariate.Raw.Ops
import CompPoly.Univariate.Raw.Proofs
import CompPoly.Univariate.LagrangeArray
import ArkLib.Commitments.Functional.Hachi.Sumcheck.Completeness
import ArkLib.Commitments.Functional.Hachi.Sumcheck.FinalEval
import ArkLib.Commitments.Functional.Hachi.Sumcheck.Bridge

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly CompPoly.CPolynomial CompPoly.Extension ArkLib.Lattices
open ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.Sumcheck

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme
open HachiEquiv.RingSwitch HachiEquiv.Ext HachiEquiv.ZeroCheck HachiEquiv.EndPiece

/-- `F = Ext4` is a length-four coefficient vector, so its `BEq` is the vector's
and is lawful; `EndPiece.lean` proves this inline, every `CPolynomial`
operation over `F` needs it, and nothing in `Ext.lean` exports it. -/
instance instLawfulBEqF : LawfulBEq F :=
  inferInstanceAs (LawfulBEq (Vector K Hachi.ext4Params.d))

/-- Rewrite `getElem` under a list equality (sidesteps the dependent-motive
issue that blocks `rw` on `l[i]`). Ported from cpoly's `Field.lean`. -/
theorem getElem_of_list_eq {α} {l l' : List α} (h : l = l') {i : ℕ}
    {hi : i < l.length} : l[i] = l'[i]'(h ▸ hi) := by cases h; rfl

/-- A `usize` holds at least `2 ^ 32 - 1`: the small literal lengths below fit. -/
theorem usize_max_ge : 4294967295 ≤ Usize.max := by
  rw [Usize.max_def]
  rcases System.Platform.numBits_eq with h | h <;> simp [Usize.numBits, h]

/-! ## The univariate carrier (ported from cpoly's `Univariate.lean`)

A `Vec Ext4` whose words are all `Reduced` represents the `CPolynomial.Raw F`
obtained by mapping `toExt` over its coefficients. No length, no canonicity:
`trim` is an operation, not an invariant. -/

/-- The reference `CPolynomial.Raw` represented by a `Vec Ext4`. -/
def toRaw (v : alloc.vec.Vec cpoly.field.Ext4) : CPolynomial.Raw F :=
  (v.val.map toExt).toArray

/-- The `k`-th coefficient of `toRaw v` is `toExt` of the `k`-th word (or `0`). -/
theorem toRaw_coeff (v : alloc.vec.Vec cpoly.field.Ext4) (k : ℕ) :
    (toRaw v).coeff k = (v.val.map toExt).getD k 0 := by
  unfold toRaw CPolynomial.Raw.coeff
  simp only [Array.getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : k < v.val.length
  · simp [List.getElem?_eq_getElem h, dif_pos h]
  · simp [List.getElem?_eq_none_iff.mpr (not_lt.mp h), dif_neg h]

@[simp] theorem toRaw_size (v : alloc.vec.Vec cpoly.field.Ext4) :
    (toRaw v).size = v.val.length := by
  simp [toRaw]

/-- In-range coefficients of `toRaw v` are the `toExt`-images of the words. -/
theorem toRaw_coeff_of_lt (v : alloc.vec.Vec cpoly.field.Ext4) {k : ℕ}
    (hk : k < v.val.length) : (toRaw v).coeff k = toExt v.val[k] := by
  rw [toRaw_coeff, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]

/-- Out-of-range coefficients of `toRaw v` are zero. -/
theorem toRaw_coeff_of_ge (v : alloc.vec.Vec cpoly.field.Ext4) {k : ℕ}
    (hk : v.val.length ≤ k) : (toRaw v).coeff k = 0 := by
  rw [toRaw_coeff, List.getD_eq_default]; simpa using hk

/-- The specification-side polynomial: `ofArray` trims, so a raw vector with
trailing zeros and its trimmed form denote the same `CPolynomial`. This is the
function `RepRoundMsg` compares against the `degreeLE` subtypes' values. -/
def toUni (v : alloc.vec.Vec cpoly.field.Ext4) : CPolynomial F :=
  CPolynomial.ofArray (toRaw v)

theorem toUni_val (v : alloc.vec.Vec cpoly.field.Ext4) :
    (toUni v).val = (toRaw v).trim := rfl

/-- Trimming does not move an evaluation, so the canonical polynomial and the
raw vector evaluate alike. The bridge every `eval` statement below crosses. -/
theorem toUni_eval (v : alloc.vec.Vec cpoly.field.Ext4) (x : F) :
    CPolynomial.eval x (toUni v) = (toRaw v).eval x := by
  show CPolynomial.Raw.eval x ((toRaw v).trim) = (toRaw v).eval x
  exact CPolynomial.Raw.eval_trim_eq_eval x (toRaw v)

set_option maxHeartbeats 1000000 in
/-- The evaluation of a represented coefficient vector as an explicit finite sum,
over any range that covers its length. -/
theorem toRaw_eval_eq_sum (v : alloc.vec.Vec cpoly.field.Ext4) (x : F) (n : ℕ)
    (hn : v.val.length ≤ n) :
    (toRaw v).eval x = ∑ i ∈ Finset.range n, (toRaw v).coeff i * x ^ i := by
  have hco : ∀ i, (toUni v).coeff i = (toRaw v).coeff i := by
    intro i; rw [toUni, CPolynomial.coeff_ofArray]
  rw [← toUni_eval v x, CPolynomial.eval_eq_sum_support,
    Finset.sum_congr rfl (fun i _ => by rw [hco i])]
  refine Finset.sum_subset (s₁ := (toUni v).support) (s₂ := Finset.range n) ?_ ?_
  · intro i hi
    simp only [Finset.mem_range]
    by_contra hc
    exact (CPolynomial.mem_support_iff _ i).mp hi
      (by rw [hco]; exact toRaw_coeff_of_ge v (by simpa using by omega))
  · intro i _ hi
    have hz : (toUni v).coeff i = 0 := by
      by_contra hc; exact hi ((CPolynomial.mem_support_iff _ i).mpr hc)
    rw [← hco i, hz, MulZeroClass.zero_mul]

/-- `Ext4::clone` is the identity — what `Vec.resize_spec` and `from_elem_spec`
ask for. Ported from cpoly's `Field.lean`. -/
theorem ext_clone_eq (a : cpoly.field.Ext4) :
    cpoly.field.Ext4.Insts.CoreCloneClone.clone a = ok a := by
  rw [cpoly.field.Ext4.Insts.CoreCloneClone.clone]

/-- `UnivariatePoly::zero` is the empty coefficient vector, i.e. the zero polynomial. -/
theorem uni_zero_spec :
    cpoly.univariate.UnivariatePoly.zero
      ⦃ z => VecReduced z ∧ toRaw z = (0 : CPolynomial.Raw F) ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.zero]
  simp only [spec_ok]
  exact ⟨by intro u hu; simp at hu, by simp [toRaw]⟩

/-- `UnivariatePoly::from_coeffs` takes the vector as it stands: no trimming, so
a trailing zero survives. -/
theorem uni_from_coeffs_spec (v : alloc.vec.Vec cpoly.field.Ext4) (hv : VecReduced v) :
    cpoly.univariate.UnivariatePoly.from_coeffs v ⦃ z => VecReduced z ∧ toRaw z = toRaw v ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.from_coeffs]
  simp only [spec_ok]
  exact ⟨hv, trivial⟩

/-- `trim`'s scan loop runs from `m` downward and returns the canonical length
`n1`: all coefficients `≥ n1` are zero, and (if `n1 > 0`) coefficient `n1-1` is
nonzero. -/
theorem uni_trim_loop_spec (p : alloc.vec.Vec cpoly.field.Ext4) (m : Std.Usize)
    (hp : VecReduced p) (hm : m.val ≤ p.val.length) :
    cpoly.univariate.UnivariatePoly.trim_loop p m ⦃ n1 => n1.val ≤ m.val ∧
      (∀ k, n1.val ≤ k → k < m.val → (toRaw p).coeff k = 0) ∧
      (n1.val = 0 ∨ (toRaw p).coeff (n1.val - 1) ≠ 0) ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.trim_loop]
  apply loop.spec_decr_nat (fun s => s.val)
    (fun s => s.val ≤ m.val ∧ ∀ k, s.val ≤ k → k < m.val → (toRaw p).coeff k = 0)
  · intro m' ⟨hm'le, hm'z⟩
    simp only [cpoly.univariate.UnivariatePoly.trim_loop.body]
    by_cases hpos : m' > 0#usize
    · rw [if_pos hpos]
      have hb : m'.val - 1 < p.val.length := by scalar_tac
      step as ⟨i, hi⟩
      have hib : i.val < p.val.length := by rw [hi]; exact hb
      step as ⟨c, hc⟩
      have hRc : Reduced c := hc ▸ hp _ (List.getElem_mem hib)
      have hcoeff : (toRaw p).coeff i.val = toExt c := by
        rw [toRaw_coeff, List.getD_eq_getElem _ _ (by simpa using hib),
          List.getElem_map, hc]
      apply spec_bind (ext_is_zero_spec c hRc)
      intro z hz
      cases z
      · simp only [Bool.false_eq_true, if_false]
        refine ⟨hm'le, hm'z, Or.inr ?_⟩
        rw [show m'.val - 1 = i.val by rw [hi], hcoeff]
        exact fun hc0 => by simpa using hz.mpr hc0
      · simp only [if_true]
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro k hk1 hk2
        rcases Nat.lt_or_ge k m'.val with hkm | hkm
        · have hki : k = i.val := by scalar_tac
          rw [hki, hcoeff]; exact hz.mp rfl
        · exact hm'z k hkm hk2
    · rw [if_neg hpos]
      exact ⟨hm'le, hm'z, Or.inl (by scalar_tac)⟩
  · exact ⟨le_refl _, fun k hk1 hk2 => absurd hk2 (by omega)⟩

/-- `UnivariatePoly::trim` ↔ `CPolynomial.Raw.trim`. -/
theorem uni_trim_spec (v : alloc.vec.Vec cpoly.field.Ext4) (hv : VecReduced v) :
    cpoly.univariate.UnivariatePoly.trim v ⦃ w => VecReduced w ∧ toRaw w = (toRaw v).trim ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.trim]
  simp only [bind_ok_id]
  apply spec_bind (uni_trim_loop_spec v (alloc.vec.Vec.len v) hv (by simp))
  rintro n1 ⟨hn1le, hn1zero, hn1bound⟩
  have hn1len : n1.val ≤ v.val.length := by simpa using hn1le
  apply spec_mono (alloc.vec.Vec.resize_spec cpoly.field.Ext4.Insts.CoreCloneClone v n1
    cpoly.field.Ext4.ZERO (ext_clone_eq _))
  intro z hzres
  have hzval : z.val = v.val.take n1.val := by
    rw [hzres, List.resize, if_pos (Nat.zero_le _),
      Nat.sub_eq_zero_of_le (by simpa using hn1len), List.replicate_zero, List.append_nil]
  have hzred : VecReduced z := by
    intro u hu; rw [hzval] at hu; exact hv u (List.mem_of_mem_take hu)
  refine ⟨hzred, ?_⟩
  have hsz : (toRaw z).size = n1.val := by
    simp only [toRaw, hzval]; simp [List.length_take]; omega
  have hzc : ∀ i, (toRaw z).coeff i = if i < n1.val then (toRaw v).coeff i else 0 := by
    intro i
    by_cases hi : i < n1.val
    · rw [if_pos hi, toRaw_coeff, hzval,
        List.getD_eq_getElem _ _ (by simp [List.length_take]; omega),
        List.getElem_map, List.getElem_take, toRaw_coeff,
        List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]
    · rw [if_neg hi, toRaw_coeff, hzval, List.getD_eq_default]
      simp only [List.length_map, List.length_take]; omega
  have hvzero : ∀ i, n1.val ≤ i → (toRaw v).coeff i = 0 := by
    intro i hi
    rcases Nat.lt_or_ge i v.val.length with hil | hil
    · exact hn1zero i hi (by simpa using hil)
    · rw [toRaw_coeff, List.getD_eq_default]; simp only [List.length_map]; omega
  apply CPolynomial.Raw.Trim.canonical_ext ?_ (CPolynomial.Raw.Trim.trim_twice _)
  · intro i
    rw [CPolynomial.Raw.Trim.coeff_eq_coeff, hzc i]
    by_cases hi : i < n1.val
    · rw [if_pos hi]
    · rw [if_neg hi]; exact (hvzero i (by omega)).symm
  · rw [CPolynomial.Raw.Trim.trim_eq_iff_size_eq_zero_or_getLastD_ne_zero]
    rcases hn1bound with h0 | hne
    · left; rw [hsz, h0]
    · right
      have hn1pos : 0 < n1.val := by
        rcases Nat.eq_zero_or_pos n1.val with h0 | hpos
        · exact absurd (by rw [h0] at hne ⊢; exact hvzero 0 (by omega)) hne
        · exact hpos
      have hgl : (toRaw z).getLastD 0 = (toRaw z).coeff (n1.val - 1) := by
        unfold Array.getLastD CPolynomial.Raw.coeff; rw [hsz]
      rw [hgl, hzc (n1.val - 1), if_pos (by omega)]; exact hne

/-- Horner's loop, from the top coefficient down. -/
theorem uni_eval_loop_spec (p : alloc.vec.Vec cpoly.field.Ext4) (xv : cpoly.field.Ext4)
    (hp : VecReduced p) (hx : Reduced xv) :
    ∀ (acc : cpoly.field.Ext4) (i : Std.Usize), i.val ≤ p.val.length → Reduced acc →
      toExt acc = ((p.val.drop i.val).map toExt).foldr (fun a b => b * toExt xv + a) 0 →
      cpoly.univariate.UnivariatePoly.eval_loop p xv acc i ⦃ r => Reduced r ∧
        toExt r = ((p.val).map toExt).foldr (fun a b => b * toExt xv + a) 0 ⦄ := by
  intro acc i hi hacc hrel
  rw [cpoly.univariate.UnivariatePoly.eval_loop]
  apply loop.spec_decr_nat (fun s => s.2.val)
    (fun s => s.2.val ≤ p.val.length ∧ Reduced s.1 ∧
       toExt s.1 = ((p.val.drop s.2.val).map toExt).foldr (fun a b => b * toExt xv + a) 0)
  · rintro ⟨acc1, i1⟩ ⟨hi1, haccR, hrel1⟩
    simp only [cpoly.univariate.UnivariatePoly.eval_loop.body]
    by_cases hlt : i1 > 0#usize
    · rw [if_pos hlt]
      have hib : i1.val - 1 < p.val.length := by scalar_tac
      step as ⟨j, hj⟩
      have hjb : j.val < p.val.length := by rw [hj]; exact hib
      step as ⟨m, hmR, hmF⟩
      step as ⟨e, he⟩
      have hRe : Reduced e := he ▸ hp _ (List.getElem_mem hjb)
      step as ⟨acc2, hacc2R, hacc2F⟩
      refine ⟨by scalar_tac, hacc2R, ?_, by scalar_tac⟩
      have hdrop : p.val.drop j.val = p.val[j.val] :: p.val.drop i1.val := by
        rw [show i1.val = j.val + 1 from by scalar_tac]
        exact List.drop_eq_getElem_cons hjb
      rw [hacc2F, hmF, he, hdrop]
      simp only [List.map_cons, List.foldr_cons, hrel1]
    · rw [if_neg hlt]
      have hz : i1.val = 0 := by scalar_tac
      exact ⟨haccR, by rw [hrel1, hz]; simp⟩
  · exact ⟨hi, hacc, hrel⟩

/-- `UnivariatePoly::eval` ↔ `CPolynomial.Raw.eval` (Horner against the power
sum: `eval₂Horner_eq_eval₂`). -/
theorem uni_eval_spec (v : alloc.vec.Vec cpoly.field.Ext4) (xv : cpoly.field.Ext4)
    (hv : VecReduced v) (hx : Reduced xv) :
    cpoly.univariate.UnivariatePoly.eval v xv
      ⦃ r => Reduced r ∧ toExt r = (toRaw v).eval (toExt xv) ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.eval]
  apply spec_mono (uni_eval_loop_spec v xv hv hx cpoly.field.Ext4.ZERO (alloc.vec.Vec.len v)
    (by simp) reduced_ZERO (by simp))
  rintro r ⟨hrR, hrF⟩
  refine ⟨hrR, ?_⟩
  rw [hrF, CPolynomial.Raw.eval, ← CPolynomial.Raw.eval₂Horner_eq_eval₂,
    CPolynomial.Raw.eval₂Horner, Array.foldr_toList]
  simp [toRaw]

/-- The loop of `Mul<Ext4>`: the prefix pushed so far is the scaled prefix. -/
theorem uni_smul_loop_spec (rr : cpoly.field.Ext4) (p : alloc.vec.Vec cpoly.field.Ext4)
    (n : Std.Usize) (hrr : Reduced rr) (hp : VecReduced p) (hn : n.val = p.val.length) :
    ∀ (out : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize),
      i.val ≤ n.val → VecReduced out →
      out.val.map toExt = (p.val.take i.val).map (fun u => toExt rr * toExt u) →
      Shared0UnivariatePoly.Insts.CoreOpsArithMulExt4UnivariatePoly.mul_loop p rr n out i
        ⦃ z => VecReduced z ∧ z.val.map toExt = p.val.map (fun u => toExt rr * toExt u) ⦄ := by
  intro out i hi hout hrel
  rw [Shared0UnivariatePoly.Insts.CoreOpsArithMulExt4UnivariatePoly.mul_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ VecReduced s.1 ∧
       s.1.val.map toExt = (p.val.take s.2.val).map (fun u => toExt rr * toExt u))
  · rintro ⟨out1, i1⟩ ⟨hi1, hout1, hrel1⟩
    simp only [Shared0UnivariatePoly.Insts.CoreOpsArithMulExt4UnivariatePoly.mul_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hlt' : i1.val < p.val.length := by scalar_tac
      have hout1len : out1.val.length = i1.val := by
        have h := congrArg List.length hrel1
        simp only [List.length_map, List.length_take] at h; omega
      step as ⟨e, he⟩
      have hRe : Reduced e := he ▸ hp _ (List.getElem_mem hlt')
      step as ⟨pe, hpeR, hpeF⟩
      step as ⟨out2, hout2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · intro u hu; rw [hout2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hout1 u h
        · rw [List.mem_singleton.mp h]; exact hpeR
      · rw [hout2, hi2, ← List.take_concat_get' _ _ hlt']
        simp only [List.map_append, List.map_cons, List.map_nil, hrel1, hpeF, he]
      · have hlt2 : i1.val < n.val := by scalar_tac
        omega
    · rw [if_neg hlt]
      have heq : i1.val = n.val := by scalar_tac
      refine ⟨hout1, ?_⟩
      rw [hrel1, heq, hn, List.take_length]
  · exact ⟨hi, hout, hrel⟩

/-- `impl Mul<Ext4> for &UnivariatePoly` ↔ `CPolynomial.Raw.smul`. Not trimmed. -/
theorem uni_smul_spec (r : cpoly.field.Ext4) (v : alloc.vec.Vec cpoly.field.Ext4)
    (hr : Reduced r) (hv : VecReduced v) :
    Shared0UnivariatePoly.Insts.CoreOpsArithMulExt4UnivariatePoly.mul v r
      ⦃ z => VecReduced z ∧ toRaw z = CPolynomial.Raw.smul (toExt r) (toRaw v) ⦄ := by
  rw [Shared0UnivariatePoly.Insts.CoreOpsArithMulExt4UnivariatePoly.mul]
  simp only [bind_ok_id]
  apply spec_mono (uni_smul_loop_spec r v (alloc.vec.Vec.len v) hr hv (by simp)
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by simp) (by intro u hu; simp at hu) (by simp))
  rintro z ⟨hzred, hzmap⟩
  refine ⟨hzred, ?_⟩
  simp only [toRaw, hzmap, CPolynomial.Raw.smul, List.map_toArray, List.map_map,
    Function.comp_def]

/-- The contribution of the first `m` coefficients of `p` to coefficient `k` of
the product `p * q`: the outer convolution loop's invariant. -/
def convol (p q : alloc.vec.Vec cpoly.field.Ext4) (m k : ℕ) : F :=
  ∑ i ∈ Finset.range m, if i ≤ k then (toRaw p).coeff i * (toRaw q).coeff (k - i) else 0

theorem convol_zero (p q : alloc.vec.Vec cpoly.field.Ext4) (k : ℕ) : convol p q 0 k = 0 := by
  simp [convol]

theorem convol_succ (p q : alloc.vec.Vec cpoly.field.Ext4) (m k : ℕ) :
    convol p q (m + 1) k
      = convol p q m k + (if m ≤ k then (toRaw p).coeff m * (toRaw q).coeff (k - m) else 0) := by
  simp [convol, Finset.sum_range_succ]

/-- The inner convolution loop: `r[i+j] += p[i] * q[j]` for `j ∈ [j₀, nq)`. -/
theorem uni_mul_inner_loop_spec (p q : alloc.vec.Vec cpoly.field.Ext4) (nq i : Std.Usize)
    (hp : VecReduced p) (hq : VecReduced q) (hnq : nq.val = q.val.length)
    (hip : i.val < p.val.length) :
    ∀ (r : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      VecReduced r → j.val ≤ nq.val → i.val + nq.val ≤ r.val.length →
      Shared1UnivariatePoly.Insts.CoreOpsArithMulShared0UnivariatePolyUnivariatePoly.mul_loop0_loop0
          p q nq r i j
        ⦃ z => VecReduced z ∧ z.val.length = r.val.length ∧
          ∀ k, (toRaw z).coeff k = (toRaw r).coeff k +
            (if i.val + j.val ≤ k ∧ k < i.val + nq.val
              then (toRaw p).coeff i.val * (toRaw q).coeff (k - i.val) else 0) ⦄ := by
  intro r j hr hj hbound
  rw [Shared1UnivariatePoly.Insts.CoreOpsArithMulShared0UnivariatePolyUnivariatePoly.mul_loop0_loop0]
  apply loop.spec_decr_nat (fun s => nq.val - s.2.val)
    (fun s => VecReduced s.1 ∧ s.2.val ≤ nq.val ∧ j.val ≤ s.2.val ∧
      s.1.val.length = r.val.length ∧
      ∀ k, (toRaw s.1).coeff k = (toRaw r).coeff k +
        (if i.val + j.val ≤ k ∧ k < i.val + s.2.val
          then (toRaw p).coeff i.val * (toRaw q).coeff (k - i.val) else 0))
  · rintro ⟨r1, j1⟩ hinv
    obtain ⟨hr1, hj1, hjj1, hlen1, hcoeff1⟩ :
        VecReduced r1 ∧ j1.val ≤ nq.val ∧ j.val ≤ j1.val ∧
        r1.val.length = r.val.length ∧
        (∀ k, (toRaw r1).coeff k = (toRaw r).coeff k +
          (if i.val + j.val ≤ k ∧ k < i.val + j1.val
            then (toRaw p).coeff i.val * (toRaw q).coeff (k - i.val) else 0)) := hinv
    simp only [Shared1UnivariatePoly.Insts.CoreOpsArithMulShared0UnivariatePolyUnivariatePoly.mul_loop0_loop0.body]
    by_cases hlt : j1 < nq
    · rw [if_pos hlt]
      have hjb : j1.val < q.val.length := by scalar_tac
      have hidxb : i.val + j1.val < r1.val.length := by scalar_tac
      step as ⟨a, ha⟩
      step as ⟨b, hb⟩
      have haR : Reduced a := ha ▸ hp _ (List.getElem_mem hip)
      have hbR : Reduced b := hb ▸ hq _ (List.getElem_mem hjb)
      step as ⟨prod, hprodR, hprodF⟩
      step as ⟨idx, hidx⟩
      have hidxb2 : idx.val < r1.val.length := by scalar_tac
      step as ⟨c, hc⟩
      have hcR : Reduced c := hc ▸ hr1 _ (List.getElem_mem hidxb2)
      step as ⟨w, hwR, hwF⟩
      step as ⟨_x, back, _hx, hback⟩
      step as ⟨j2, hj2⟩
      subst hback
      have hset : (r1.set idx w).val = r1.val.set idx.val w := by simp
      have hsetlen : (r1.set idx w).val.length = r.val.length := by
        rw [hset, List.length_set, hlen1]
      have hpa : (toRaw p).coeff i.val = toExt a := by rw [toRaw_coeff_of_lt p hip, ha]
      have hqb : (toRaw q).coeff j1.val = toExt b := by rw [toRaw_coeff_of_lt q hjb, hb]
      have hrc : (toRaw r1).coeff idx.val = toExt c := by
        rw [toRaw_coeff_of_lt r1 hidxb2, hc]
      have hcset : ∀ k, (toRaw (r1.set idx w)).coeff k =
          if idx.val = k then toExt w else (toRaw r1).coeff k := by
        intro k
        by_cases hk : k < r1.val.length
        · rw [toRaw_coeff_of_lt _ (by rw [hsetlen]; omega), toRaw_coeff_of_lt r1 hk,
            getElem_of_list_eq hset, List.getElem_set]
          split <;> rfl
        · rw [toRaw_coeff_of_ge _ (by omega), toRaw_coeff_of_ge r1 (by omega),
            if_neg (by omega)]
      refine ⟨?_, by scalar_tac, by scalar_tac, hsetlen, ?_, by scalar_tac⟩
      · intro u hu
        rw [hset] at hu
        rcases List.mem_or_eq_of_mem_set hu with h | h
        · exact hr1 u h
        · exact h ▸ hwR
      · intro k
        rw [hcset k]
        by_cases hke : idx.val = k
        · rw [if_pos hke, if_pos (show i.val + j.val ≤ k ∧ k < i.val + j2.val by omega),
            hpa, show k - i.val = j1.val from by omega, hqb, hwF, hprodF]
          have hcr : toExt c = (toRaw r).coeff idx.val := by
            rw [← hrc, hcoeff1 idx.val, if_neg (by omega), add_zero]
          rw [hcr, hke]
        · rw [if_neg hke, hcoeff1 k]
          congr 1
          by_cases hcond : i.val + j.val ≤ k ∧ k < i.val + j1.val
          · rw [if_pos hcond, if_pos (show i.val + j.val ≤ k ∧ k < i.val + j2.val by omega)]
          · rw [if_neg hcond, if_neg (show ¬(i.val + j.val ≤ k ∧ k < i.val + j2.val) by omega)]
    · rw [if_neg hlt]
      have heq : j1.val = nq.val := by scalar_tac
      refine ⟨hr1, hlen1, ?_⟩
      intro k
      rw [hcoeff1 k, heq]
  · refine ⟨hr, hj, le_refl _, rfl, fun k => ?_⟩
    have hfalse : ¬(i.val + j.val ≤ k ∧ k < i.val + j.val) := by omega
    simp [hfalse]

/-- The outer convolution loop accumulates `convol p q np`. -/
theorem uni_mul_outer_loop_spec (p q : alloc.vec.Vec cpoly.field.Ext4) (np nq : Std.Usize)
    (hp : VecReduced p) (hq : VecReduced q)
    (hnp : np.val = p.val.length) (hnq : nq.val = q.val.length) :
    ∀ (r : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize),
      VecReduced r → i.val ≤ np.val → np.val + nq.val ≤ r.val.length + 1 →
      (∀ k, (toRaw r).coeff k = convol p q i.val k) →
      Shared1UnivariatePoly.Insts.CoreOpsArithMulShared0UnivariatePolyUnivariatePoly.mul_loop0
          p q np nq r i
        ⦃ z => VecReduced z ∧ z.val.length = r.val.length ∧
          ∀ k, (toRaw z).coeff k = convol p q np.val k ⦄ := by
  intro r i hr hi hbound hcoeff
  rw [Shared1UnivariatePoly.Insts.CoreOpsArithMulShared0UnivariatePolyUnivariatePoly.mul_loop0]
  apply loop.spec_decr_nat (fun s => np.val - s.2.val)
    (fun s => VecReduced s.1 ∧ s.2.val ≤ np.val ∧ s.1.val.length = r.val.length ∧
      ∀ k, (toRaw s.1).coeff k = convol p q s.2.val k)
  · rintro ⟨r1, i1⟩ hinv
    obtain ⟨hr1, hi1, hlen1, hcoeff1⟩ : VecReduced r1 ∧ i1.val ≤ np.val ∧
        r1.val.length = r.val.length ∧
        (∀ k, (toRaw r1).coeff k = convol p q i1.val k) := hinv
    simp only [Shared1UnivariatePoly.Insts.CoreOpsArithMulShared0UnivariatePolyUnivariatePoly.mul_loop0.body]
    by_cases hlt : i1 < np
    · rw [if_pos hlt]
      have h1 : i1.val < np.val := by scalar_tac
      have hip : i1.val < p.val.length := by omega
      have hib : i1.val + nq.val ≤ r1.val.length := by omega
      apply spec_bind (uni_mul_inner_loop_spec p q nq i1 hp hq hnq hip
        r1 0#usize hr1 (by scalar_tac) hib)
      rintro r2 ⟨hr2, hlen2, hcoeff2⟩
      step as ⟨i2, hi2⟩
      have hz : (0#usize).val = 0 := by scalar_tac
      refine ⟨hr2, by scalar_tac, by omega, ?_, by scalar_tac⟩
      intro k
      rw [hcoeff2 k, hz, Nat.add_zero, hcoeff1 k,
        show i2.val = i1.val + 1 by scalar_tac, convol_succ]
      congr 1
      by_cases hk : i1.val ≤ k
      · by_cases hk2 : k < i1.val + nq.val
        · rw [if_pos ⟨hk, hk2⟩, if_pos hk]
        · rw [if_neg (by tauto), if_pos hk, toRaw_coeff_of_ge q (by omega), MulZeroClass.mul_zero]
      · rw [if_neg (by tauto), if_neg hk]
    · rw [if_neg hlt]
      have heq : i1.val = np.val := by scalar_tac
      exact ⟨hr1, hlen1, by rw [← heq]; exact hcoeff1⟩
  · exact ⟨hr, hi, rfl, hcoeff⟩

private theorem convol_eq_sum_range_aux (n k : ℕ) :
    (Finset.range n).filter (fun i => i ≤ k) = Finset.range (min n (k + 1)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The full convolution is the sum shape of `CPolynomial.Raw.mul_coeff`. -/
theorem convol_eq_sum_range (p q : alloc.vec.Vec cpoly.field.Ext4) (k : ℕ) :
    convol p q p.val.length k
      = ∑ i ∈ Finset.range (k + 1), (toRaw p).coeff i * (toRaw q).coeff (k - i) := by
  have hL : convol p q p.val.length k
      = ∑ i ∈ Finset.range (min p.val.length (k + 1)),
          (toRaw p).coeff i * (toRaw q).coeff (k - i) := by
    rw [convol, ← Finset.sum_filter, convol_eq_sum_range_aux]
  have hR : ∑ i ∈ Finset.range (min p.val.length (k + 1)),
          (toRaw p).coeff i * (toRaw q).coeff (k - i)
      = ∑ i ∈ Finset.range (k + 1), (toRaw p).coeff i * (toRaw q).coeff (k - i) := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · intro x hx hnx
      simp only [Finset.mem_range] at hx hnx
      rw [toRaw_coeff_of_ge p (by omega), MulZeroClass.zero_mul]
  rw [hL, hR]

/-- `impl Mul<&UnivariatePoly> for &UnivariatePoly` ↔ `CPolynomial.Raw.mul`
(schoolbook, trimmed once at the end).

`hlen` is necessary, not convenient: the accumulator is sized by a *checked*
`np + nq`, which fails above `Usize.max` before `n ← i - 1` can bring it
back — cpoly's header records that the triple is false without it. -/
theorem uni_mul_spec (v w : alloc.vec.Vec cpoly.field.Ext4)
    (hv : VecReduced v) (hw : VecReduced w)
    (hlen : v.val.length + w.val.length ≤ Std.Usize.max) :
    Shared1UnivariatePoly.Insts.CoreOpsArithMulShared0UnivariatePolyUnivariatePoly.mul v w
      ⦃ z => VecReduced z ∧ toRaw z = CPolynomial.Raw.mul (toRaw v) (toRaw w) ∧
        z.val.length ≤ v.val.length + w.val.length ⦄ := by
  have hnewred : VecReduced (alloc.vec.Vec.new cpoly.field.Ext4) := by intro u hu; simp at hu
  have hnewraw : toRaw (alloc.vec.Vec.new cpoly.field.Ext4) = (0 : CPolynomial.Raw F) := by
    simp [toRaw]
  rw [Shared1UnivariatePoly.Insts.CoreOpsArithMulShared0UnivariatePolyUnivariatePoly.mul]
  by_cases hp0 : alloc.vec.Vec.len v = 0#usize
  · rw [if_pos hp0, cpoly.univariate.UnivariatePoly.zero]
    simp only [spec_ok]
    refine ⟨hnewred, ?_, by simp⟩
    have hvz : toRaw v = (0 : CPolynomial.Raw F) := by
      have hl : v.val.length = 0 := by scalar_tac
      simp [toRaw, List.length_eq_zero_iff.mp hl]
    rw [hnewraw, hvz]
    exact (CPolynomial.Raw.zero_mul (toRaw w)).symm
  · rw [if_neg hp0]
    by_cases hq0 : alloc.vec.Vec.len w = 0#usize
    · rw [if_pos hq0, cpoly.univariate.UnivariatePoly.zero]
      simp only [spec_ok]
      refine ⟨hnewred, ?_, by simp⟩
      have hwz : toRaw w = (0 : CPolynomial.Raw F) := by
        have hl : w.val.length = 0 := by scalar_tac
        simp [toRaw, List.length_eq_zero_iff.mp hl]
      rw [hnewraw, hwz]
      exact (CPolynomial.Raw.mul_zero (toRaw v)).symm
    · rw [if_neg hq0]
      have hvpos : 0 < v.val.length := by scalar_tac
      have hwpos : 0 < w.val.length := by scalar_tac
      step as ⟨i, hi⟩
      step as ⟨n, hn⟩
      apply spec_bind (alloc.vec.from_elem_spec cpoly.field.Ext4.Insts.CoreCloneClone
        cpoly.field.Ext4.ZERO n (ext_clone_eq _))
      rintro r ⟨hr, hrlen'⟩
      have hrlen : r.val.length = n.val := by simpa using hrlen'
      have hrred : VecReduced r := by
        intro u hu
        rw [hr] at hu
        rw [List.eq_of_mem_replicate hu]
        exact reduced_ZERO
      have hrcoeff : ∀ k, (toRaw r).coeff k = 0 := by
        intro k
        rcases Nat.lt_or_ge k r.val.length with h | h
        · rw [toRaw_coeff_of_lt r h]; simp [hr]
        · exact toRaw_coeff_of_ge r h
      apply spec_bind (uni_mul_outer_loop_spec v w (alloc.vec.Vec.len v) (alloc.vec.Vec.len w)
        hv hw (by simp) (by simp) r 0#usize hrred (by simp) (by scalar_tac)
        (by intro k; rw [hrcoeff k, show (0#usize).val = 0 from by scalar_tac, convol_zero]))
      rintro r1 ⟨hr1red, hr1len, hr1coeff⟩
      apply spec_mono (uni_trim_spec r1 hr1red)
      rintro z ⟨hzred, hztrim⟩
      have hzlen : z.val.length ≤ r1.val.length := by
        rw [← toRaw_size z, ← toRaw_size r1, hztrim]
        exact CPolynomial.Raw.Trim.size_le_size (toRaw r1)
      refine ⟨hzred, ?_, by scalar_tac⟩
      rw [hztrim]
      have hlenv : (alloc.vec.Vec.len v).val = v.val.length := by simp
      have h2 : (toRaw r1).trim = ((toRaw v) * (toRaw w)).trim := by
        apply CPolynomial.Raw.Trim.eq_of_equiv
        intro k
        rw [hr1coeff k, CPolynomial.Raw.mul_coeff, hlenv, convol_eq_sum_range]
      rw [h2, CPolynomial.Raw.mul_is_trimmed]
      rfl

/-! ## The pure mathematics the lower-half statements are stated in -/

/- `lo`, `hi` and `fold` moved to `lean/ZeroCheck.lean` § "The layer fold
   `w_table_mle_eval` runs"; still in scope here through `open HachiEquiv.ZeroCheck`. -/

/-- The range summand's inner sum at one node, **without** the equality
kernel's free factor and prefix: `Σ_y eq[y] · P_b(W(T, y))`. Degree `2b − 1`
in `T`. -/
def rangeSumZero {k : ℕ} (w : Fin (2 ^ (k + 1)) → F) (eq : Fin (2 ^ k) → F) (T : F) : F :=
  ∑ y : Fin (2 ^ k), eq y * InnerOuter.rangeProduct 16 (fold w T y)

/-- The linear summand at one node: `Σ_y W(T, y) · Ã(T, y)`. Degree `2` in `T`. -/
def linSumAlpha {k : ℕ} (w a : Fin (2 ^ (k + 1)) → F) (T : F) : F :=
  ∑ y : Fin (2 ^ k), fold w T y * fold a T y

/-- The equality kernel `eq̃(τ, a) = ∏_j (τ_j a_j + (1 − τ_j)(1 − a_j))`, the
value `cEqualityPolynomial k τ` takes at `a`. -/
def eqProd {k : ℕ} (τ a : Fin k → F) : F :=
  ∏ j : Fin k, (τ j * a j + (1 - τ j) * (1 - a j))

/- `tableFn` moved to `lean/ZeroCheck.lean` § "The layer fold `w_table_mle_eval`
   runs". -/

/-- The equality kernel is the value of the specification's
`cEqualityPolynomial`: the bridge between the crate's product and ArkLib's
`CMvPolynomial`. -/
theorem cEqualityPolynomial_eval_eq_eqProd {k : ℕ} (τ a : Fin k → F) :
    (InnerOuter.cEqualityPolynomial k τ).eval a = eqProd τ a := by
  rw [InnerOuter.cEqualityPolynomial, InnerOuter.cMultilinearExtension_eval,
    InnerOuter.eval_MLE_eq_sum, eqProd]
  have hstep : ∀ x : Fin k → Fin 2,
      (∏ i, if x i = 1 then τ i else 1 - τ i) * ∏ i, (if x i = 1 then a i else 1 - a i)
        = ∏ i, (if x i = 1 then τ i * a i else (1 - τ i) * (1 - a i)) := by
    intro x
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => by split <;> rfl)
  have hsplit : ∀ i : Fin k, τ i * a i + (1 - τ i) * (1 - a i)
      = ∑ j : Fin 2, (if j = 1 then τ i * a i else (1 - τ i) * (1 - a i)) := by
    intro i; rw [Fin.sum_univ_two]; simp; ring
  rw [Finset.sum_congr rfl (fun x _ => hstep x),
    Finset.prod_congr rfl (fun i _ => hsplit i),
    Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Fin 2)))
      (fun i j => if j = 1 then τ i * a i else (1 - τ i) * (1 - a i)),
    Fintype.piFinset_univ]

/-- A Mathlib polynomial of bounded degree, read as a `CPolynomial` with the same
values: the bridge the two degree lemmas below cross. -/
theorem exists_cpoly_of_polynomial (P : Polynomial F) (n : ℕ) (hdeg : P.natDegree ≤ n) :
    ∃ p : CPolynomial F, p ∈ CPolynomial.degreeLE (R := F) (n : ℕ) ∧
      ∀ T, CPolynomial.eval T p = P.eval T := by
  refine ⟨⟨P.toImpl, CPolynomial.Raw.isCanonical_toImpl P⟩, ?_, ?_⟩
  · rw [CPolynomial.degreeLE_toPoly, CPolynomial.toPoly_mk_toImpl, Polynomial.mem_degreeLE]
    exact le_trans Polynomial.degree_le_natDegree (by exact_mod_cast hdeg)
  · intro T
    show CPolynomial.Raw.eval T P.toImpl = _
    exact CPolynomial.eval_toImpl_eq_eval T P

/-- The affine polynomial a multilinear fold is in the free coordinate. -/
private noncomputable def foldPoly (c₀ c₁ : F) : Polynomial F :=
  Polynomial.C c₀ + Polynomial.C (c₁ - c₀) * Polynomial.X

private theorem foldPoly_natDegree (c₀ c₁ : F) : (foldPoly c₀ c₁).natDegree ≤ 1 := by
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  simp only [Polynomial.natDegree_C, max_le_iff]
  exact ⟨Nat.zero_le _, le_trans (Polynomial.natDegree_mul_le)
    (by simp [Polynomial.natDegree_C, Polynomial.natDegree_X])⟩

private theorem foldPoly_eval (c₀ c₁ T : F) :
    (foldPoly c₀ c₁).eval T = (1 - T) * c₀ + T * c₁ := by
  simp only [foldPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  ring

/-- `rangeSumZero` is a polynomial function of degree `≤ 2b − 1 = 31` in the
node — the fact that makes `2b + 1 = 33` interpolation nodes reproduce it. -/
theorem rangeSumZero_poly {k : ℕ} (w : Fin (2 ^ (k + 1)) → F) (eq : Fin (2 ^ k) → F) :
    ∃ p : CPolynomial F, p ∈ CPolynomial.degreeLE (R := F) (31 : ℕ) ∧
      ∀ T, CPolynomial.eval T p = rangeSumZero w eq T := by
  classical
  set u : Fin (2 ^ k) → Polynomial F := fun y => foldPoly (w (lo y)) (w (hi y)) with hu
  set P : Polynomial F := ∑ y : Fin (2 ^ k), Polynomial.C (eq y) *
    (u y * ∏ j ∈ Finset.Icc 1 15,
      ((u y - Polynomial.C ((j : ℕ) : F)) * (u y + Polynomial.C ((j : ℕ) : F)))) with hP
  have hdegu : ∀ y, (u y).natDegree ≤ 1 := fun y => foldPoly_natDegree _ _
  have hdegfac : ∀ (y : Fin (2 ^ k)) (j : ℕ),
      ((u y - Polynomial.C ((j : ℕ) : F)) * (u y + Polynomial.C ((j : ℕ) : F))).natDegree ≤ 2 := by
    intro y j
    refine le_trans Polynomial.natDegree_mul_le ?_
    have h1 : (u y - Polynomial.C ((j : ℕ) : F)).natDegree ≤ 1 :=
      le_trans (Polynomial.natDegree_sub_le _ _) (by simp [hdegu y])
    have h2 : (u y + Polynomial.C ((j : ℕ) : F)).natDegree ≤ 1 :=
      le_trans (Polynomial.natDegree_add_le _ _) (by simp [hdegu y])
    omega
  have hdeg : P.natDegree ≤ 31 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun y _ => ?_)
    refine le_trans Polynomial.natDegree_mul_le ?_
    have hC : (Polynomial.C (eq y)).natDegree = 0 := Polynomial.natDegree_C _
    have hrest : (u y * ∏ j ∈ Finset.Icc 1 15,
        ((u y - Polynomial.C ((j : ℕ) : F)) * (u y + Polynomial.C ((j : ℕ) : F)))).natDegree
          ≤ 31 := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      have hprod : (∏ j ∈ Finset.Icc 1 15,
          ((u y - Polynomial.C ((j : ℕ) : F)) * (u y + Polynomial.C ((j : ℕ) : F)))).natDegree
            ≤ 30 := by
        refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
        calc ∑ j ∈ Finset.Icc 1 15,
              ((u y - Polynomial.C ((j : ℕ) : F)) * (u y + Polynomial.C ((j : ℕ) : F))).natDegree
            ≤ ∑ _j ∈ Finset.Icc 1 15, 2 :=
              Finset.sum_le_sum (fun j _ => hdegfac y j)
          _ = 30 := by simp
      have := hdegu y
      omega
    omega
  obtain ⟨p, hp1, hp2⟩ := exists_cpoly_of_polynomial P 31 hdeg
  refine ⟨p, hp1, fun T => ?_⟩
  rw [hp2, hP, rangeSumZero]
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [InnerOuter.rangeProduct]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_sub, hu, foldPoly_eval]
  have hfold : (1 - T) * w (lo y) + T * w (hi y) = fold w T y := by rw [fold]
  rw [hfold]

/-- `linSumAlpha` is a polynomial function of degree `≤ 2` in the node. -/
theorem linSumAlpha_poly {k : ℕ} (w a : Fin (2 ^ (k + 1)) → F) :
    ∃ p : CPolynomial F, p ∈ CPolynomial.degreeLE (R := F) (2 : ℕ) ∧
      ∀ T, CPolynomial.eval T p = linSumAlpha w a T := by
  classical
  set P : Polynomial F := ∑ y : Fin (2 ^ k),
    foldPoly (w (lo y)) (w (hi y)) * foldPoly (a (lo y)) (a (hi y)) with hP
  have hdeg : P.natDegree ≤ 2 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun y _ => ?_)
    refine le_trans Polynomial.natDegree_mul_le ?_
    have h1 := foldPoly_natDegree (w (lo y)) (w (hi y))
    have h2 := foldPoly_natDegree (a (lo y)) (a (hi y))
    omega
  obtain ⟨p, hp1, hp2⟩ := exists_cpoly_of_polynomial P 2 hdeg
  refine ⟨p, hp1, fun T => ?_⟩
  rw [hp2, hP, linSumAlpha, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Polynomial.eval_mul, foldPoly_eval, foldPoly_eval, fold, fold]

/-! ## The representation relations -/

/-- Relation between the extracted nested zero-check statement and ArkLib's
`NestedZeroCheckStatement` (`Constraints.lean:1407`), with `TCom` at the
chain's commitment type as `RepWEval` has it. `tau0.len() = m₀` and
`tau1.len() = m₁` travel inside `WfPoint`: the specification's `Fin m → F`
erases to a `Vec`, and Aeneas cannot see a privacy boundary. -/
def RepNestedZC {n μ m₀ m₁ dRows : ℕ} (s : sumcheck.NestedZeroCheckStmt)
    (ss : InnerOuter.NestedZeroCheckStatement Φ (PolyVec (Rq Φ) dRows) F n μ m₀ m₁) : Prop :=
  RepRlin (n := n) (μ := μ) s.rlin ss.rlin ∧ WfVec dRows s.t ∧ Reduced s.alpha ∧
    WfPoint m₀ s.tau0 ∧ WfPoint m₁ s.tau1 ∧
    toVec (k := dRows) s.t = ss.t ∧ toExt s.alpha = ss.α ∧
    toPoint (m := m₀) s.tau0 = ss.τ₀ ∧ toPoint (m := m₁) s.tau1 = ss.τα

/-- Relation between the extracted round message and ArkLib's `RoundMsg F b`
(`Rounds.lean:65`) at `b = 16`: a pair of `degreeLE` subtypes, related through
`toUni`, so the degree bounds are carried by the specification side and the
raw vectors need not be canonical. -/
def RepRoundMsg (g : sumcheck.RoundMsg) (sg : InnerOuter.RoundMsg F 16) : Prop :=
  VecReduced g.g_zero ∧ VecReduced g.g_alpha ∧
    toUni g.g_zero = sg.1.1 ∧ toUni g.g_alpha = sg.2.1

/-- Relation between the extracted round statement and ArkLib's
`NestedRoundStatement` at round `i` (`Constraints.lean:1421`), whose only
computational content is `challenges.len() = i` — here inside `WfPoint i`. -/
def RepRoundStmt {n μ m₀ m₁ i dRows : ℕ} (s : sumcheck.RoundStatement)
    (ss : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ m₀ m₁ i) : Prop :=
  RepNestedZC (n := n) (μ := μ) (m₀ := m₀) (m₁ := m₁) (dRows := dRows) s.zc ss.zc ∧
    WfPoint i s.challenges ∧ Reduced s.target_zero ∧ Reduced s.target_alpha ∧
    toPoint (m := i) s.challenges = ss.challenges ∧
    toExt s.target_zero = ss.target₀ ∧ toExt s.target_alpha = ss.targetα

/-! ## The carriers' constructors -/

/-- `NestedZeroCheckStmt::new` preserves the relation. -/
theorem NestedZeroCheckStmt_new_spec {n μ m₀ m₁ dRows : ℕ}
    (rlin : ringswitch.RlinStatement) (t : linalg.PolyVec) (alpha : cpoly.field.Ext4)
    (tau0 tau1 : alloc.vec.Vec cpoly.field.Ext4)
    (ss : InnerOuter.NestedZeroCheckStatement Φ (PolyVec (Rq Φ) dRows) F n μ m₀ m₁)
    (hr : RepRlin (n := n) (μ := μ) rlin ss.rlin) (hWt : WfVec dRows t) (hWa : Reduced alpha)
    (hW0 : WfPoint m₀ tau0) (hW1 : WfPoint m₁ tau1)
    (ht : toVec (k := dRows) t = ss.t) (ha : toExt alpha = ss.α)
    (h0 : toPoint (m := m₀) tau0 = ss.τ₀) (h1 : toPoint (m := m₁) tau1 = ss.τα) :
    sumcheck.NestedZeroCheckStmt.new rlin t alpha tau0 tau1
      ⦃ out => RepNestedZC (n := n) (μ := μ) (m₀ := m₀) (m₁ := m₁) (dRows := dRows) out ss ⦄ := by
  rw [sumcheck.NestedZeroCheckStmt.new]
  simp only [spec_ok]
  exact ⟨hr, hWt, hWa, hW0, hW1, ht, ha, h0, h1⟩

/-- `RoundMsg::new` preserves the relation. -/
theorem RoundMsg_new_spec (g_zero g_alpha : cpoly.univariate.UnivariatePoly)
    (sg : InnerOuter.RoundMsg F 16)
    (hW0 : VecReduced g_zero) (hWa : VecReduced g_alpha)
    (h0 : toUni g_zero = sg.1.1) (ha : toUni g_alpha = sg.2.1) :
    sumcheck.RoundMsg.new g_zero g_alpha ⦃ out => RepRoundMsg out sg ⦄ := by
  rw [sumcheck.RoundMsg.new]
  simp only [spec_ok]
  exact ⟨hW0, hWa, h0, ha⟩

/-- `RoundStatement::new` preserves the relation. -/
theorem RoundStatement_new_spec {n μ m₀ m₁ i dRows : ℕ}
    (zc : sumcheck.NestedZeroCheckStmt) (challenges : alloc.vec.Vec cpoly.field.Ext4)
    (target_zero target_alpha : cpoly.field.Ext4)
    (ss : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ m₀ m₁ i)
    (hzc : RepNestedZC (n := n) (μ := μ) (m₀ := m₀) (m₁ := m₁) (dRows := dRows) zc ss.zc)
    (hWc : WfPoint i challenges) (hW0 : Reduced target_zero) (hWa : Reduced target_alpha)
    (hc : toPoint (m := i) challenges = ss.challenges)
    (h0 : toExt target_zero = ss.target₀) (ha : toExt target_alpha = ss.targetα) :
    sumcheck.RoundStatement.new zc challenges target_zero target_alpha
      ⦃ out => RepRoundStmt (n := n) (μ := μ) (m₀ := m₀) (m₁ := m₁) (i := i) (dRows := dRows)
        out ss ⦄ := by
  rw [sumcheck.RoundStatement.new]
  simp only [spec_ok]
  exact ⟨hzc, hWc, hW0, hWa, hc, h0, ha⟩

/-! ## The cube size and the nodes -/

/-- The loop of `cube_size`: the accumulator is `2 ^ k` after `k` doublings. -/
theorem cube_size_loop_spec (vars sz k : Std.Usize) (hn : 2 ^ vars.val ≤ Usize.max)
    (hk : k.val ≤ vars.val) (hsz : sz.val = 2 ^ k.val) :
    sumcheck.cube_size_loop vars sz k ⦃ s => s.val = 2 ^ vars.val ⦄ := by
  rw [sumcheck.cube_size_loop]
  apply loop.spec_decr_nat (fun s => vars.val - s.2.val)
    (fun s => s.2.val ≤ vars.val ∧ s.1.val = 2 ^ s.2.val)
  · rintro ⟨s1, k1⟩ ⟨hk1, hs1⟩
    dsimp only at hk1 hs1
    simp only [sumcheck.cube_size_loop.body]
    by_cases hlt : k1 < vars
    · rw [if_pos hlt]
      have hfit : s1.val * 2 ≤ Usize.max := by
        have hmono : 2 ^ (k1.val + 1) ≤ 2 ^ vars.val :=
          Nat.pow_le_pow_right (by norm_num) (by scalar_tac)
        rw [hs1, ← pow_succ] at *
        omega
      step as ⟨s2, hs2⟩
      step as ⟨k2, hk2⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hs2, hs1, hk2, pow_succ]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = vars.val := by scalar_tac
      rw [hs1, heq]
  · exact ⟨hk, hsz⟩

/-- `cube_size` computes `2 ^ vars`, sizing the tables `alpha_public_table`
fills. The bound is `two_pow_spec`'s (`ZeroCheck.lean`): a checked doubling
that forms the number, and a table that does not fit a `usize` does not fit
memory either. -/
theorem cube_size_spec (vars : Std.Usize) (hn : 2 ^ vars.val ≤ Usize.max) :
    sumcheck.cube_size vars ⦃ s => s.val = 2 ^ vars.val ⦄ :=
  cube_size_loop_spec vars 1#usize 0#usize hn (by simp) (by simp)

/-- `round_node i` is the field element `i` (spec: `CPolynomial.pointNode` at
the node array `0 … 2b`): `φF (i : ZMod q) = (i : F)`. Total. -/
theorem round_node_spec (i : Std.Usize) :
    sumcheck.round_node i ⦃ out => Reduced out ∧ toExt out = (i.val : F) ⦄ := by
  rw [sumcheck.round_node]
  have hcast : lift (UScalar.cast .U64 i) ⦃ y => y.val = i.val ⦄ :=
    UScalar.cast_inBounds_spec .U64 i (by
      have h1 : i.val ≤ Usize.max := by scalar_tac
      have h3 : UScalar.max UScalarTy.U64 = 18446744073709551615 := by
        simp [UScalar.max_def, UScalarTy.numBits]
      have h2 : Usize.max ≤ 18446744073709551615 := by
        rw [Usize.max_def]
        rcases System.Platform.numBits_eq with h | h <;> simp [Usize.numBits, h]
      omega)
  step with hcast as ⟨w, hw⟩
  step with fp_new_spec w as ⟨c, hRc, hc⟩
  apply spec_mono (ext_from_base_spec c hRc)
  rintro out ⟨hRout, hout⟩
  refine ⟨hRout, ?_⟩
  rw [hout, hc, hw, ofBase_natCast]

/-- The `2b + 1 = 33` range-side weights: entry `i` inverts `∏_{j ≠ i} (i − j)`
over the nodes `0 … 32`. The arithmetic content of `params.ROUND_NODE_INV`. -/
theorem round_node_weights_spec :
    sumcheck.round_node_weights ⦃ out => out.val.length = 33 ∧ (∀ a ∈ out.val, Red a) ∧
      ∀ i : Fin 33, toK (out.val.getD i.val (0#u64 : cpoly.field.Fp)) *
        ∏ j ∈ (Finset.univ : Finset (Fin 33)).erase i, ((i.val : ZMod q) - (j.val : ZMod q)) = 1 ⦄ := by
  have hrn : (params.ROUND_NODES).val = 33 := by simp [params.ROUND_NODES]
  have hmax := usize_max_ge
  rw [sumcheck.round_node_weights, sumcheck.round_node_weights_loop]
  apply loop.spec_decr_nat (fun st => 33 - st.2.val)
    (fun st => st.2.val ≤ 33 ∧ st.1.val.length = st.2.val ∧ (∀ a ∈ st.1.val, Red a) ∧
      ∀ t : ℕ, t < st.2.val → toK (st.1.val.getD t (0#u64 : cpoly.field.Fp)) =
        (((params.ROUND_NODE_INV.val.getD t (0#u64 : Std.U64)).val : ℕ) : ZMod q))
  · rintro ⟨v1, i1⟩ ⟨hi1, hlen1, hred1, hval1⟩
    dsimp only at hi1 hlen1 hred1 hval1
    simp only [sumcheck.round_node_weights_loop.body]
    by_cases hlt : i1 < params.ROUND_NODES
    · rw [if_pos hlt]
      have hi1lt : i1.val < 33 := by scalar_tac
      have harr : i1.val < params.ROUND_NODE_INV.val.length := by
        rw [params.ROUND_NODE_INV.property]; scalar_tac
      step as ⟨u, hu⟩
      step with fp_new_spec u as ⟨f, hRf, hf⟩
      have hbound : v1.val.length < Usize.max := by omega
      step as ⟨v2, hv2⟩
      step as ⟨i2, hi2⟩
      have hi2n : i2.val = i1.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, ?_, ?_, by scalar_tac⟩
      · rw [hi2n, hv2, List.length_append, hlen1]; simp
      · intro a hmem
        rw [hv2] at hmem
        rcases List.mem_append.mp hmem with h | h
        · exact hred1 a h
        · rw [List.mem_singleton.mp h]; exact hRf
      · intro t ht
        rw [hi2n] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = v1.val.length := by omega
          rw [hteq, hv2, getD_append_eq, hf, hu, hlen1,
            List.getD_eq_getElem _ _ harr]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hieq : i1.val = 33 := by scalar_tac
      refine ⟨by rw [hlen1, hieq], hred1, fun i => ?_⟩
      rw [hval1 i.val (by rw [hieq]; exact i.isLt)]
      revert i
      simp only [params.ROUND_NODE_INV]
      decide
  · exact ⟨by simp, by simp, by intro a ha; simp at ha, by intro t ht; simp at ht⟩

/-- The three linear-side weights, for the nodes `0, 1, 2`: `2⁻¹, −1, 2⁻¹`. -/
theorem round_node_weights_alpha_spec :
    sumcheck.round_node_weights_alpha ⦃ out => out.val.length = 3 ∧ (∀ a ∈ out.val, Red a) ∧
      ∀ i : Fin 3, toK (out.val.getD i.val (0#u64 : cpoly.field.Fp)) *
        ∏ j ∈ (Finset.univ : Finset (Fin 3)).erase i, ((i.val : ZMod q) - (j.val : ZMod q)) = 1 ⦄ := by
  have hrn : (params.ROUND_NODES_ALPHA).val = 3 := by simp [params.ROUND_NODES_ALPHA]
  have hmax := usize_max_ge
  rw [sumcheck.round_node_weights_alpha, sumcheck.round_node_weights_alpha_loop]
  apply loop.spec_decr_nat (fun st => 3 - st.2.val)
    (fun st => st.2.val ≤ 3 ∧ st.1.val.length = st.2.val ∧ (∀ a ∈ st.1.val, Red a) ∧
      ∀ t : ℕ, t < st.2.val → toK (st.1.val.getD t (0#u64 : cpoly.field.Fp)) =
        (((params.ROUND_NODE_INV_ALPHA.val.getD t (0#u64 : Std.U64)).val : ℕ) : ZMod q))
  · rintro ⟨v1, i1⟩ ⟨hi1, hlen1, hred1, hval1⟩
    dsimp only at hi1 hlen1 hred1 hval1
    simp only [sumcheck.round_node_weights_alpha_loop.body]
    by_cases hlt : i1 < params.ROUND_NODES_ALPHA
    · rw [if_pos hlt]
      have hi1lt : i1.val < 3 := by scalar_tac
      have harr : i1.val < params.ROUND_NODE_INV_ALPHA.val.length := by
        rw [params.ROUND_NODE_INV_ALPHA.property]; scalar_tac
      step as ⟨u, hu⟩
      step with fp_new_spec u as ⟨f, hRf, hf⟩
      have hbound : v1.val.length < Usize.max := by omega
      step as ⟨v2, hv2⟩
      step as ⟨i2, hi2⟩
      have hi2n : i2.val = i1.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, ?_, ?_, by scalar_tac⟩
      · rw [hi2n, hv2, List.length_append, hlen1]; simp
      · intro a hmem
        rw [hv2] at hmem
        rcases List.mem_append.mp hmem with h | h
        · exact hred1 a h
        · rw [List.mem_singleton.mp h]; exact hRf
      · intro t ht
        rw [hi2n] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = v1.val.length := by omega
          rw [hteq, hv2, getD_append_eq, hf, hu, hlen1,
            List.getD_eq_getElem _ _ harr]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hieq : i1.val = 3 := by scalar_tac
      refine ⟨by rw [hlen1, hieq], hred1, fun i => ?_⟩
      rw [hval1 i.val (by rw [hieq]; exact i.isLt)]
      revert i
      simp only [params.ROUND_NODE_INV_ALPHA]
      decide
  · exact ⟨by simp, by simp, by intro a ha; simp at ha, by intro t ht; simp at ht⟩

/-! ## Interpolation -/

/-- Multiplying by a linear factor `X − c`, on coefficients. -/
theorem coeff_X_sub_C_mul (c : F) (P : Polynomial F) (k : ℕ) :
    ((Polynomial.X - Polynomial.C c) * P).coeff k
      = (if k = 0 then 0 else P.coeff (k - 1)) - c * P.coeff k := by
  rcases k with _ | k
  · simp [Polynomial.mul_coeff_zero]
  · rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
    simp

/-- The Lagrange numerator for node `i`, over the nodes below `J`. -/
noncomputable def basisProd (i J : ℕ) : Polynomial F :=
  ∏ l ∈ (Finset.range J).erase i, (Polynomial.X - Polynomial.C ((l : ℕ) : F))

theorem basisProd_zero (i : ℕ) : basisProd i 0 = 1 := by simp [basisProd]

theorem basisProd_succ_of_ne {i J : ℕ} (h : J ≠ i) :
    basisProd i (J + 1) = (Polynomial.X - Polynomial.C ((J : ℕ) : F)) * basisProd i J := by
  rw [basisProd, basisProd, Finset.range_add_one, Finset.erase_insert_of_ne h,
    Finset.prod_insert (by simp)]

theorem basisProd_succ_of_eq {i J : ℕ} (h : J = i) :
    basisProd i (J + 1) = basisProd i J := by
  subst h
  rw [basisProd, basisProd, Finset.range_add_one, Finset.erase_insert (by simp),
    Finset.erase_eq_of_notMem (by simp)]

/-- The number of coefficients of the basis product built from the nodes below `J`. -/
theorem basisLen_eq (i J : ℕ) :
    1 + ((Finset.range J).erase i).card = if i < J then J else J + 1 := by
  by_cases h : i < J
  · rw [if_pos h, Finset.card_erase_of_mem (Finset.mem_range.mpr h), Finset.card_range]
    omega
  · rw [if_neg h, Finset.erase_eq_of_notMem (by simpa using h), Finset.card_range]
    omega

/-- `interpolate`'s innermost loop multiplies the basis by `X − xⱼ`, one
coefficient per iteration: entry `t` is `basis[t−1] − basis[t]·xⱼ`. -/
theorem interpolate_shift_loop_spec (basis : alloc.vec.Vec cpoly.field.Ext4)
    (xj : cpoly.field.Ext4) (P : Polynomial F)
    (hb : VecReduced basis) (hxj : Reduced xj)
    (hP : ∀ k, (toRaw basis).coeff k = P.coeff k)
    (hmax : basis.val.length + 1 ≤ Usize.max) :
    ∀ (next : alloc.vec.Vec cpoly.field.Ext4) (t : Std.Usize),
      VecReduced next → t.val ≤ basis.val.length + 1 → next.val.length = t.val →
      (∀ k, k < t.val → (toRaw next).coeff k
        = ((Polynomial.X - Polynomial.C (toExt xj)) * P).coeff k) →
      sumcheck.interpolate_loop1_loop0_loop0 basis xj next t
        ⦃ z => VecReduced z ∧ z.val.length = basis.val.length + 1 ∧
          ∀ k, (toRaw z).coeff k
            = ((Polynomial.X - Polynomial.C (toExt xj)) * P).coeff k ⦄ := by
  intro next t hnext ht hlen hval
  have hRZ : Reduced cpoly.field.Ext4.ZERO := reduced_ZERO
  rw [sumcheck.interpolate_loop1_loop0_loop0]
  apply loop.spec_decr_nat (fun s => basis.val.length + 1 - s.2.val)
    (fun s => VecReduced s.1 ∧ s.2.val ≤ basis.val.length + 1 ∧ s.1.val.length = s.2.val ∧
      ∀ k, k < s.2.val → (toRaw s.1).coeff k
        = ((Polynomial.X - Polynomial.C (toExt xj)) * P).coeff k)
  · rintro ⟨v1, t1⟩ ⟨hv1, ht1, hlen1, hval1⟩
    dsimp only at hv1 ht1 hlen1 hval1
    simp only [sumcheck.interpolate_loop1_loop0_loop0.body]
    step as ⟨i1, hi1⟩
    by_cases hlt : t1 < i1
    · rw [if_pos hlt]
      have htb : t1.val ≤ basis.val.length := by scalar_tac
      have hshift :
          (if t1 > 0#usize then
            (do let i2 ← t1 - 1#usize
                alloc.vec.Vec.index_usize basis i2)
          else ok cpoly.field.Ext4.ZERO)
            ⦃ s => Reduced s ∧ toExt s =
              (if t1.val = 0 then 0 else (toRaw basis).coeff (t1.val - 1)) ⦄ := by
        by_cases ht0 : t1 > 0#usize
        · rw [if_pos ht0]
          have hpos : 0 < t1.val := by scalar_tac
          have hib : t1.val - 1 < basis.val.length := by omega
          step as ⟨i2, hi2⟩
          step as ⟨s, hs⟩
          refine ⟨?_, ?_⟩
          · rw [hs]; exact hb _ (List.getElem_mem (by scalar_tac))
          · rw [hs, if_neg (by omega), toRaw_coeff_of_lt basis hib]
            congr 1
            scalar_tac
        · rw [if_neg ht0, WP.spec_ok]
          have ht0' : t1.val = 0 := by scalar_tac
          exact ⟨hRZ, by rw [if_pos ht0', toExt_ZERO]⟩
      step with hshift as ⟨sh, hRsh, hsh⟩
      have hscale :
          (if t1 < alloc.vec.Vec.len basis then
            (do let e ← alloc.vec.Vec.index_usize basis t1
                cpoly.field.Ext4.Insts.CoreOpsArithMulExt4Ext4.mul e xj)
          else ok cpoly.field.Ext4.ZERO)
            ⦃ s => Reduced s ∧ toExt s = (toRaw basis).coeff t1.val * toExt xj ⦄ := by
        by_cases hts : t1 < alloc.vec.Vec.len basis
        · rw [if_pos hts]
          have hib : t1.val < basis.val.length := by scalar_tac
          step as ⟨e, he⟩
          have hRe : Reduced e := by rw [he]; exact hb _ (List.getElem_mem hib)
          apply spec_mono (ext_mul_spec e xj hRe hxj)
          rintro s ⟨hRs, hsv⟩
          exact ⟨hRs, by rw [hsv, he, toRaw_coeff_of_lt basis hib]⟩
        · rw [if_neg hts, WP.spec_ok]
          have hge : basis.val.length ≤ t1.val := by scalar_tac
          exact ⟨hRZ, by rw [toExt_ZERO, toRaw_coeff_of_ge basis hge, MulZeroClass.zero_mul]⟩
      step with hscale as ⟨sc, hRsc, hsc⟩
      step with ext_sub_spec sh sc hRsh hRsc as ⟨e, hRe, he⟩
      have hpush : v1.val.length < Usize.max := by omega
      step as ⟨v2, hv2⟩
      step as ⟨t2, ht2⟩
      have ht2v : t2.val = t1.val + 1 := by scalar_tac
      refine ⟨?_, by omega, ?_, ?_, by omega⟩
      · intro u hu
        rw [hv2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hv1 u h
        · rw [List.mem_singleton.mp h]; exact hRe
      · rw [ht2v, hv2, List.length_append, hlen1]; simp
      · intro k hk
        rw [ht2v] at hk
        rcases Nat.lt_or_ge k t1.val with hklt | hkge
        · rw [toRaw_coeff_of_lt _ (by rw [hv2, List.length_append, hlen1]; simp; omega),
            getElem_of_list_eq hv2, List.getElem_append_left (by omega),
            ← toRaw_coeff_of_lt v1 (by omega)]
          exact hval1 k hklt
        · have hkeq : k = t1.val := by omega
          subst hkeq
          rw [toRaw_coeff_of_lt _ (by rw [hv2, List.length_append, hlen1]; simp),
            getElem_of_list_eq hv2, List.getElem_append_right (by omega)]
          simp only [hlen1, Nat.sub_self, List.getElem_cons_zero]
          rw [he, hsh, hsc, coeff_X_sub_C_mul, hP, hP]
          ring
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hteq : t1.val = basis.val.length + 1 := by scalar_tac
      refine ⟨hv1, by rw [hlen1, hteq], fun k => ?_⟩
      rcases Nat.lt_or_ge k t1.val with hklt | hkge
      · exact hval1 k hklt
      · have hk1 : basis.val.length + 1 ≤ k := by omega
        rw [toRaw_coeff_of_ge _ (by omega), coeff_X_sub_C_mul, ← hP, ← hP,
          toRaw_coeff_of_ge basis (by omega)]
        rw [if_neg (by omega), toRaw_coeff_of_ge basis (by omega)]
        ring
  · exact ⟨hnext, ht, hlen, hval⟩

/-- The `n` interpolation nodes `0 … n − 1` are distinct in `F`: the weights
invert `∏_{j ≠ i} (i − j)`, so no factor of that product can vanish. -/
theorem node_ne_of_weights {n : ℕ} (wt : Fin n → ZMod q)
    (hwt : ∀ i : Fin n, wt i *
      ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, ((i.val : ZMod q) - (j.val : ZMod q)) = 1)
    (i j : Fin n) (hij : i ≠ j) : ((i.val : ℕ) : F) - ((j.val : ℕ) : F) ≠ 0 := by
  have hprodne : ∏ l ∈ (Finset.univ : Finset (Fin n)).erase i,
      ((i.val : ZMod q) - (l.val : ZMod q)) ≠ 0 := by
    intro h0
    have h1 := hwt i
    rw [h0, MulZeroClass.mul_zero] at h1
    exact zero_ne_one h1
  have hjmem : j ∈ (Finset.univ : Finset (Fin n)).erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
  have hfac : ((i.val : ZMod q) - (j.val : ZMod q)) ≠ 0 :=
    fun h => hprodne (Finset.prod_eq_zero hjmem h)
  intro hcon
  refine hfac ?_
  have hmap : phiF ((i.val : ZMod q) - (j.val : ZMod q))
      = ((i.val : ℕ) : F) - ((j.val : ℕ) : F) := by
    rw [map_sub, map_natCast, map_natCast]
  have hzero : phiF ((i.val : ZMod q) - (j.val : ZMod q)) = 0 := by rw [hmap, hcon]
  have hinj : Function.Injective phiF := phiF.injective
  exact hinj (by rw [hzero, map_zero])

/-- The uniqueness half of Lagrange interpolation at the nodes `0 … n − 1`: a
polynomial of degree `< n` taking the prescribed values **is** the interpolant. -/
theorem interpolateArray_toPoly_eq {n : ℕ} (g : Fin n → F) (Q : Polynomial F)
    (hnodes : ∀ i j : Fin n, i ≠ j → ((i.val : ℕ) : F) - ((j.val : ℕ) : F) ≠ 0)
    (hdeg : Q.degree < (n : WithBot ℕ))
    (heval : ∀ i : Fin n, Q.eval ((i.val : ℕ) : F) = g i) :
    (CLagrange.interpolateArray
      (Array.ofFn fun i : Fin n => (((i.val : ℕ) : F), g i))).toPoly = Q := by
  classical
  have hsz : (Array.ofFn fun i : Fin n => (((i.val : ℕ) : F), g i)).size = n := by simp
  have hnode : ∀ i : Fin (Array.ofFn fun i : Fin n => (((i.val : ℕ) : F), g i)).size,
      CLagrange.pointNode (Array.ofFn fun i : Fin n => (((i.val : ℕ) : F), g i)) i
        = ((i.val : ℕ) : F) := by
    intro i; simp [CLagrange.pointNode]
  have hvalue : ∀ i : Fin (Array.ofFn fun i : Fin n => (((i.val : ℕ) : F), g i)).size,
      CLagrange.pointValue (Array.ofFn fun i : Fin n => (((i.val : ℕ) : F), g i)) i
        = g ⟨i.val, by have := i.isLt; simpa using this⟩ := by
    intro i; simp [CLagrange.pointValue]
  have hinj : Set.InjOn
      (CLagrange.pointNode (Array.ofFn fun i : Fin n => (((i.val : ℕ) : F), g i)))
      ↑(Finset.univ :
        Finset (Fin (Array.ofFn fun i : Fin n => (((i.val : ℕ) : F), g i)).size)) := by
    intro i _ j _ hij
    rw [hnode, hnode] at hij
    by_contra hne
    have hi : i.val < n := by have := i.isLt; omega
    have hj : j.val < n := by have := j.isLt; omega
    refine hnodes ⟨i.val, hi⟩ ⟨j.val, hj⟩ ?_ (by simp [hij])
    intro hcon
    have hvv : i.val = j.val := by simpa using hcon
    exact hne (Fin.ext hvv)
  have hdeg' : Q.degree < (Finset.univ :
      Finset (Fin (Array.ofFn fun i : Fin n => (((i.val : ℕ) : F), g i)).size)).card := by
    have h2 : (Finset.univ :
        Finset (Fin (Array.ofFn fun i : Fin n => (((i.val : ℕ) : F), g i)).size)).card = n := by
      simp [hsz]
    rw [h2]
    exact hdeg
  have heval' : ∀ i ∈ (Finset.univ :
      Finset (Fin (Array.ofFn fun i : Fin n => (((i.val : ℕ) : F), g i)).size)),
      Q.eval (CLagrange.pointNode
          (Array.ofFn fun i : Fin n => (((i.val : ℕ) : F), g i)) i)
        = CLagrange.pointValue (Array.ofFn fun i : Fin n => (((i.val : ℕ) : F), g i)) i := by
    intro i _
    rw [hnode, hvalue, heval ⟨i.val, by have := i.isLt; simpa using this⟩]
  have hkey := Lagrange.eq_interpolate_of_eval_eq
    (v := CLagrange.pointNode (Array.ofFn fun i : Fin n => (((i.val : ℕ) : F), g i)))
    (r := CLagrange.pointValue (Array.ofFn fun i : Fin n => (((i.val : ℕ) : F), g i)))
    (s := Finset.univ) hinj hdeg' heval'
  show (CLagrange.interpolate _ _ _).toPoly = _
  rw [CLagrange.cinterpolate_eq_interpolate, ← hkey]

/-- An `n`-node interpolant of a polynomial of degree `< n` is that polynomial. -/
theorem interpolateArray_eval_of_degreeLE {n d : ℕ} (g : Fin n → F) (p : CPolynomial F)
    (hd : d < n) (hdeg : p ∈ CPolynomial.degreeLE (R := F) (d : ℕ))
    (hnodes : ∀ i j : Fin n, i ≠ j → ((i.val : ℕ) : F) - ((j.val : ℕ) : F) ≠ 0)
    (hval : ∀ i : Fin n, g i = CPolynomial.eval ((i.val : ℕ) : F) p) (x : F) :
    CPolynomial.eval x (CLagrange.interpolateArray
      (Array.ofFn fun i : Fin n => (((i.val : ℕ) : F), g i))) = CPolynomial.eval x p := by
  have hdeg' : p.toPoly.degree < (n : WithBot ℕ) := by
    rw [CPolynomial.degreeLE_toPoly, Polynomial.mem_degreeLE] at hdeg
    exact lt_of_le_of_lt hdeg (by exact_mod_cast hd)
  have hkey := interpolateArray_toPoly_eq (n := n) g p.toPoly hnodes hdeg'
    (fun i => by rw [← CPolynomial.eval_toPoly, ← hval i])
  rw [CPolynomial.eval_toPoly, CPolynomial.eval_toPoly, hkey]

/-- The `j` loop of `interpolate`: the basis is `∏_{l < J, l ≠ i} (X − l)`. -/
theorem interpolate_basis_loop_spec {n : ℕ} (nn iu : Std.Usize)
    (hnn : nn.val = n) (hiu : iu.val < n) (hnmax : n ≤ Usize.max) :
    ∀ (basis : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      VecReduced basis → j.val ≤ n →
      basis.val.length = (if iu.val < j.val then j.val else j.val + 1) →
      (∀ k, (toRaw basis).coeff k = (basisProd iu.val j.val).coeff k) →
      sumcheck.interpolate_loop1_loop0 nn iu basis j
        ⦃ z => VecReduced z ∧ z.val.length = n ∧
          ∀ k, (toRaw z).coeff k = (basisProd iu.val n).coeff k ⦄ := by
  intro basis j hb hj hlen hcoeff
  rw [sumcheck.interpolate_loop1_loop0]
  apply loop.spec_decr_nat (fun s => n - s.2.val)
    (fun s => VecReduced s.1 ∧ s.2.val ≤ n ∧
      s.1.val.length = (if iu.val < s.2.val then s.2.val else s.2.val + 1) ∧
      ∀ k, (toRaw s.1).coeff k = (basisProd iu.val s.2.val).coeff k)
  · rintro ⟨b1, j1⟩ ⟨hb1, hj1, hlen1, hc1⟩
    dsimp only at hb1 hj1 hlen1 hc1
    simp only [sumcheck.interpolate_loop1_loop0.body]
    by_cases hlt : j1 < nn
    · rw [if_pos hlt]
      have hjlt : j1.val < n := by scalar_tac
      by_cases hne : j1.val = iu.val
      · rw [if_neg (by simp only [bne_iff_ne, ne_eq, not_not]; exact Std.UScalar.eq_of_val_eq hne)]
        step as ⟨j2, hj2⟩
        have hj2v : j2.val = j1.val + 1 := by scalar_tac
        refine ⟨hb1, by omega, ?_, ?_, by omega⟩
        · rw [hj2v, hlen1, if_neg (by omega), if_pos (by omega)]
        · intro k
          rw [hj2v, basisProd_succ_of_eq hne]
          exact hc1 k
      · rw [if_pos (by simp only [bne_iff_ne, ne_eq]; exact fun h => hne (by rw [h]))]
        have hlenb : b1.val.length + 1 ≤ n := by
          rw [hlen1]
          by_cases h : iu.val < j1.val
          · rw [if_pos h]; omega
          · rw [if_neg h]; omega
        step with round_node_spec j1 as ⟨xj, hRxj, hxj⟩
        step with interpolate_shift_loop_spec b1 xj (basisProd iu.val j1.val) hb1 hRxj hc1
          (by omega) (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize
          (by intro u hu; simp at hu) (by simp) (by simp) (by intro k hk; simp at hk)
          as ⟨b2, hb2, hlen2, hc2⟩
        step as ⟨j2, hj2⟩
        have hj2v : j2.val = j1.val + 1 := by scalar_tac
        refine ⟨hb2, by omega, ?_, ?_, by omega⟩
        · rw [hj2v, hlen2, hlen1]
          by_cases h : iu.val < j1.val
          · rw [if_pos h, if_pos (by omega)]
          · rw [if_neg h, if_neg (by omega)]
        · intro k
          rw [hj2v, basisProd_succ_of_ne hne, ← hxj]
          exact hc2 k
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hjeq : j1.val = n := by scalar_tac
      refine ⟨hb1, ?_, ?_⟩
      · rw [hlen1, hjeq, if_pos hiu]
      · rw [← hjeq]; exact hc1
  · exact ⟨hb, hj, hlen, hcoeff⟩

/-- The accumulation loop of `interpolate`: `acc += scale · basis`, coefficient
by coefficient. -/
theorem interpolate_acc_loop_spec (basis : alloc.vec.Vec cpoly.field.Ext4)
    (scale : cpoly.field.Ext4) (A B : Polynomial F) (L : ℕ)
    (hb : VecReduced basis) (hs : Reduced scale)
    (hB : ∀ k, (toRaw basis).coeff k = B.coeff k)
    (hblen : basis.val.length ≤ L) :
    ∀ (acc : alloc.vec.Vec cpoly.field.Ext4) (t : Std.Usize),
      VecReduced acc → acc.val.length = L → t.val ≤ basis.val.length →
      (∀ k, (toRaw acc).coeff k =
        (if k < t.val then (A + Polynomial.C (toExt scale) * B).coeff k else A.coeff k)) →
      sumcheck.interpolate_loop1_loop1 acc basis scale t
        ⦃ z => VecReduced z ∧ z.val.length = L ∧
          ∀ k, (toRaw z).coeff k = (A + Polynomial.C (toExt scale) * B).coeff k ⦄ := by
  intro acc t hacc hlen ht hval
  rw [sumcheck.interpolate_loop1_loop1]
  apply loop.spec_decr_nat (fun s => basis.val.length - s.2.val)
    (fun s => VecReduced s.1 ∧ s.1.val.length = L ∧ s.2.val ≤ basis.val.length ∧
      ∀ k, (toRaw s.1).coeff k =
        (if k < s.2.val then (A + Polynomial.C (toExt scale) * B).coeff k else A.coeff k))
  · rintro ⟨a1, t1⟩ ⟨ha1, hl1, ht1, hv1⟩
    dsimp only at ha1 hl1 ht1 hv1
    simp only [sumcheck.interpolate_loop1_loop1.body]
    by_cases hlt : t1 < alloc.vec.Vec.len basis
    · rw [if_pos hlt]
      have htb : t1.val < basis.val.length := by scalar_tac
      have hta : t1.val < a1.val.length := by omega
      step as ⟨e, he⟩
      have hRe : Reduced e := by rw [he]; exact ha1 _ (List.getElem_mem hta)
      step as ⟨e1, he1⟩
      have hRe1 : Reduced e1 := by rw [he1]; exact hb _ (List.getElem_mem htb)
      step with ext_mul_spec e1 scale hRe1 hs as ⟨e2, hRe2, he2⟩
      step with ext_add_spec e e2 hRe hRe2 as ⟨e3, hRe3, he3⟩
      step as ⟨_x, back, _hx, hback⟩
      step as ⟨t2, ht2⟩
      subst hback
      have ht2v : t2.val = t1.val + 1 := by scalar_tac
      have hset : (a1.set t1 e3).val = a1.val.set t1.val e3 := by simp
      have hsetlen : (a1.set t1 e3).val.length = L := by rw [hset, List.length_set, hl1]
      have hcset : ∀ k, (toRaw (a1.set t1 e3)).coeff k =
          if t1.val = k then toExt e3 else (toRaw a1).coeff k := by
        intro k
        by_cases hk : k < a1.val.length
        · rw [toRaw_coeff_of_lt _ (by rw [hsetlen]; omega), toRaw_coeff_of_lt a1 hk,
            getElem_of_list_eq hset, List.getElem_set]
          split <;> rfl
        · rw [toRaw_coeff_of_ge _ (by omega), toRaw_coeff_of_ge a1 (by omega),
            if_neg (by omega)]
      refine ⟨?_, hsetlen, by omega, ?_, by omega⟩
      · intro u hu
        rw [hset] at hu
        rcases List.mem_or_eq_of_mem_set hu with h | h
        · exact ha1 u h
        · exact h ▸ hRe3
      · intro k
        rw [hcset k, ht2v]
        by_cases hke : t1.val = k
        · rw [if_pos hke, if_pos (by omega), he3, he2, he, he1,
            ← toRaw_coeff_of_lt a1 hta, ← toRaw_coeff_of_lt basis htb, hv1 t1.val,
            if_neg (by omega), hB, hke, Polynomial.coeff_add, Polynomial.coeff_C_mul]
          rw [hke] at *
          ring
        · rw [if_neg hke, hv1 k]
          by_cases hcond : k < t1.val
          · rw [if_pos hcond, if_pos (by omega)]
          · rw [if_neg hcond, if_neg (by omega)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hteq : t1.val = basis.val.length := by scalar_tac
      refine ⟨ha1, hl1, fun k => ?_⟩
      rw [hv1 k]
      by_cases hk : k < t1.val
      · rw [if_pos hk]
      · rw [if_neg hk, Polynomial.coeff_add, Polynomial.coeff_C_mul, ← hB,
          toRaw_coeff_of_ge basis (by omega), MulZeroClass.mul_zero, add_zero]
  · exact ⟨hacc, hlen, ht, hval⟩

/-- One summand's coefficient: `values[i] · φF(inv_weights[i])`. -/
noncomputable def interpCoeff (values : alloc.vec.Vec cpoly.field.Ext4)
    (inv_weights : alloc.vec.Vec cpoly.field.Fp) (i : ℕ) : F :=
  toExt (values.val.getD i cpoly.field.Ext4.ZERO) *
    Ext.ofBase (toK (inv_weights.val.getD i (0#u64 : cpoly.field.Fp)))

/-- The partial interpolation sum after `I` summands. -/
noncomputable def interpPartial (values : alloc.vec.Vec cpoly.field.Ext4)
    (inv_weights : alloc.vec.Vec cpoly.field.Fp) (n I : ℕ) : Polynomial F :=
  ∑ i ∈ Finset.range I, Polynomial.C (interpCoeff values inv_weights i) * basisProd i n

/-- The zeroing loop of `interpolate`: `n` zero coefficients. -/
theorem interpolate_zeros_loop_spec {n : ℕ} (nn : Std.Usize) (hnn : nn.val = n)
    (hnmax : n ≤ Usize.max) :
    ∀ (acc : alloc.vec.Vec cpoly.field.Ext4) (k : Std.Usize),
      VecReduced acc → k.val ≤ n → acc.val.length = k.val →
      (∀ j, (toRaw acc).coeff j = 0) →
      sumcheck.interpolate_loop0 nn acc k
        ⦃ z => VecReduced z ∧ z.val.length = n ∧ ∀ j, (toRaw z).coeff j = 0 ⦄ := by
  intro acc k hacc hk hlen hz
  have hRZ : Reduced cpoly.field.Ext4.ZERO := reduced_ZERO
  rw [sumcheck.interpolate_loop0]
  apply loop.spec_decr_nat (fun s => n - s.2.val)
    (fun s => VecReduced s.1 ∧ s.2.val ≤ n ∧ s.1.val.length = s.2.val ∧
      ∀ j, (toRaw s.1).coeff j = 0)
  · rintro ⟨v1, k1⟩ ⟨hv1, hk1, hl1, hz1⟩
    dsimp only at hv1 hk1 hl1 hz1
    simp only [sumcheck.interpolate_loop0.body]
    by_cases hlt : k1 < nn
    · rw [if_pos hlt]
      have hklt : k1.val < n := by scalar_tac
      have hpush : v1.val.length < Usize.max := by omega
      step as ⟨v2, hv2⟩
      step as ⟨k2, hk2⟩
      have hk2v : k2.val = k1.val + 1 := by scalar_tac
      refine ⟨?_, by omega, ?_, ?_, by omega⟩
      · intro u hu
        rw [hv2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hv1 u h
        · rw [List.mem_singleton.mp h]; exact hRZ
      · rw [hk2v, hv2, List.length_append, hl1]; simp
      · intro j
        by_cases hj : j < v1.val.length
        · rw [toRaw_coeff_of_lt _ (by rw [hv2, List.length_append]; simp; omega),
            getElem_of_list_eq hv2, List.getElem_append_left hj,
            ← toRaw_coeff_of_lt v1 hj]
          exact hz1 j
        · rcases Nat.lt_or_ge j (v1.val.length + 1) with hj2 | hj2
          · have hje : j = v1.val.length := by omega
            subst hje
            rw [toRaw_coeff_of_lt _ (by rw [hv2, List.length_append]; simp),
              getElem_of_list_eq hv2, List.getElem_append_right (by omega)]
            simp only [Nat.sub_self, List.getElem_cons_zero]
            exact toExt_ZERO
          · rw [toRaw_coeff_of_ge _ (by rw [hv2, List.length_append]; simp; omega)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hkeq : k1.val = n := by scalar_tac
      exact ⟨hv1, by rw [hl1, hkeq], hz1⟩
  · exact ⟨hacc, hk, hlen, hz⟩

theorem interpPartial_succ (values : alloc.vec.Vec cpoly.field.Ext4)
    (inv_weights : alloc.vec.Vec cpoly.field.Fp) (n I : ℕ) :
    interpPartial values inv_weights n (I + 1)
      = interpPartial values inv_weights n I
        + Polynomial.C (interpCoeff values inv_weights I) * basisProd I n := by
  rw [interpPartial, interpPartial, Finset.sum_range_succ]

/-- The `i` loop of `interpolate`: the accumulator is the partial sum. -/
theorem interpolate_outer_loop_spec {n : ℕ} (values : alloc.vec.Vec cpoly.field.Ext4)
    (inv_weights : alloc.vec.Vec cpoly.field.Fp) (nn : Std.Usize)
    (hv : WfPoint n values) (hnn : nn.val = n)
    (hwlen : n ≤ inv_weights.val.length)
    (hwred : ∀ k < n, Red (inv_weights.val.getD k (0#u64 : cpoly.field.Fp))) :
    ∀ (acc : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize),
      VecReduced acc → acc.val.length = n → i.val ≤ n →
      (∀ k, (toRaw acc).coeff k = (interpPartial values inv_weights n i.val).coeff k) →
      sumcheck.interpolate_loop1 values inv_weights nn acc i
        ⦃ z => VecReduced z ∧ z.val.length = n ∧
          ∀ k, (toRaw z).coeff k = (interpPartial values inv_weights n n).coeff k ⦄ := by
  intro acc i hacc hlen hi hcoeff
  obtain ⟨hvlen, hvred⟩ := hv
  have hnmax : n ≤ Usize.max := by rw [← hvlen]; exact values.property
  have hR1 : Reduced cpoly.field.Ext4.ONE := reduced_ONE
  rw [sumcheck.interpolate_loop1]
  apply loop.spec_decr_nat (fun s => n - s.2.val)
    (fun s => VecReduced s.1 ∧ s.1.val.length = n ∧ s.2.val ≤ n ∧
      ∀ k, (toRaw s.1).coeff k = (interpPartial values inv_weights n s.2.val).coeff k)
  · rintro ⟨a1, i1⟩ ⟨ha1, hl1, hi1, hc1⟩
    dsimp only at ha1 hl1 hi1 hc1
    simp only [sumcheck.interpolate_loop1.body]
    by_cases hlt : i1 < nn
    · rw [if_pos hlt]
      have hilt : i1.val < n := by scalar_tac
      have hpush0 : (alloc.vec.Vec.new cpoly.field.Ext4).val.length < Usize.max := by
        simp; omega
      step as ⟨b0, hb0⟩
      have hb0v : b0.val = [cpoly.field.Ext4.ONE] := by rw [hb0]; simp
      have hb0len : b0.val.length = 1 := by rw [hb0v]; simp
      have hb0red : VecReduced b0 := by
        intro u hu; rw [hb0v] at hu; rw [List.mem_singleton.mp hu]; exact hR1
      have hb0c : ∀ k, (toRaw b0).coeff k = (basisProd i1.val 0).coeff k := by
        intro k
        rw [basisProd_zero, toRaw_coeff, hb0v]
        rcases k with _ | k <;> simp [Polynomial.coeff_one]
      step with interpolate_basis_loop_spec (n := n) nn i1 hnn hilt hnmax b0 0#usize
        hb0red (by simp) (by rw [hb0len]; simp) hb0c as ⟨b1, hb1red, hb1len, hb1c⟩
      have hvb : i1.val < values.val.length := by omega
      have hwb : i1.val < inv_weights.val.length := by omega
      step as ⟨e, he⟩
      step as ⟨f, hf⟩
      have hRf : Red f := by
        have := hwred i1.val hilt
        rwa [List.getD_eq_getElem _ _ hwb, ← hf] at this
      step with ext_from_base_spec f hRf as ⟨e1, hRe1, he1⟩
      have hRe : Reduced e := by rw [he]; exact hvred _ (List.getElem_mem hvb)
      step with ext_mul_spec e e1 hRe hRe1 as ⟨scale, hRscale, hscale⟩
      have hscalev : toExt scale = interpCoeff values inv_weights i1.val := by
        rw [hscale, he1, hf, he, interpCoeff, List.getD_eq_getElem _ _ hvb,
          List.getD_eq_getElem _ _ hwb]
      step with interpolate_acc_loop_spec b1 scale (interpPartial values inv_weights n i1.val)
        (basisProd i1.val n) n hb1red hRscale hb1c (by omega) a1 0#usize
        ha1 hl1 (by simp) (by intro k; simpa using hc1 k) as ⟨a2, ha2, hl2, hc2⟩
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = i1.val + 1 := by scalar_tac
      refine ⟨ha2, hl2, by omega, ?_, by omega⟩
      intro k
      rw [hi2v, interpPartial_succ, ← hscalev]
      exact hc2 k
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hieq : i1.val = n := by scalar_tac
      have hEq : interpPartial values inv_weights n i1.val
          = interpPartial values inv_weights n n := by rw [hieq]
      refine ⟨ha1, hl1, fun k => ?_⟩
      rw [← hEq]
      exact hc1 k
  · exact ⟨hacc, hlen, hi, hcoeff⟩

/-- A product over `(range n).erase i` is the same as one over `univ.erase i`. -/
theorem prod_erase_range_eq_univ {n : ℕ} (i : Fin n) (f : ℕ → F) :
    ∏ l ∈ (Finset.range n).erase i.val, f l
      = ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, f j.val := by
  classical
  have himg : Finset.image (fun j : Fin n => j.val) ((Finset.univ : Finset (Fin n)).erase i)
      = (Finset.range n).erase i.val := by
    ext l
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨fun h => hj (Fin.ext h), j.isLt⟩
    · rintro ⟨hne, hlt⟩
      refine ⟨⟨l, hlt⟩, ?_, rfl⟩
      intro h
      exact hne (by rw [← h])
  rw [← himg, Finset.prod_image (fun a _ b _ h => Fin.ext h)]

/-- The supplied weights invert the node differences, in `F`. -/
theorem weights_prod_eq_one {n : ℕ} (inv_weights : alloc.vec.Vec cpoly.field.Fp)
    (hw : ∀ i : Fin n, toK (inv_weights.val.getD i.val (0#u64 : cpoly.field.Fp)) *
      ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        ((i.val : ZMod q) - (j.val : ZMod q)) = 1)
    (i : Fin n) :
    Ext.ofBase (toK (inv_weights.val.getD i.val (0#u64 : cpoly.field.Fp))) *
      ∏ l ∈ (Finset.range n).erase i.val, (((i.val : ℕ) : F) - ((l : ℕ) : F)) = 1 := by
  rw [prod_erase_range_eq_univ i (fun l => ((i.val : ℕ) : F) - ((l : ℕ) : F))]
  have h2 := congrArg phiF (hw i)
  rw [map_mul, map_one, map_prod] at h2
  simp only [map_sub, map_natCast] at h2
  rw [← h2]
  rfl

/-- The interpolation sum has degree below the number of nodes. -/
theorem interpPartial_degree_lt {n : ℕ} (values : alloc.vec.Vec cpoly.field.Ext4)
    (inv_weights : alloc.vec.Vec cpoly.field.Fp) (I : ℕ) (hI : I ≤ n) :
    (interpPartial values inv_weights n I).degree < (n : WithBot ℕ) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · have hI0 : I = 0 := by omega
    subst hn0
    subst hI0
    simp [interpPartial]
  · have hnat : (interpPartial values inv_weights n I).natDegree ≤ n - 1 := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i hi => ?_)
      have hin : i < n := lt_of_lt_of_le (Finset.mem_range.mp hi) hI
      refine le_trans Polynomial.natDegree_mul_le ?_
      have h1 : (Polynomial.C (interpCoeff values inv_weights i)).natDegree = 0 :=
        Polynomial.natDegree_C _
      have h2 : (basisProd i n).natDegree ≤ n - 1 := by
        have hcard : ((Finset.range n).erase i).card = n - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hin), Finset.card_range]
        have hstep : ∀ l ∈ (Finset.range n).erase i,
            (Polynomial.X - Polynomial.C ((l : ℕ) : F)).natDegree ≤ 1 :=
          fun l _ => le_trans (Polynomial.natDegree_sub_le _ _) (by simp)
        rw [basisProd]
        refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
        refine le_trans (Finset.sum_le_sum hstep) ?_
        rw [Finset.sum_const, smul_eq_mul, mul_one, hcard]
      omega
    have hle : (interpPartial values inv_weights n I).degree ≤ ((n - 1 : ℕ) : WithBot ℕ) :=
      le_trans Polynomial.degree_le_natDegree (by exact_mod_cast hnat)
    have hlt : ((n - 1 : ℕ) : WithBot ℕ) < (n : WithBot ℕ) := by
      exact_mod_cast (by omega : n - 1 < n)
    exact lt_of_le_of_lt hle hlt

/-- The interpolation sum takes the prescribed value at every node. -/
theorem interpPartial_eval {n : ℕ} (values : alloc.vec.Vec cpoly.field.Ext4)
    (inv_weights : alloc.vec.Vec cpoly.field.Fp)
    (hw : ∀ i : Fin n, toK (inv_weights.val.getD i.val (0#u64 : cpoly.field.Fp)) *
      ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        ((i.val : ZMod q) - (j.val : ZMod q)) = 1)
    (m : Fin n) :
    (interpPartial values inv_weights n n).eval ((m.val : ℕ) : F)
      = toPoint (m := n) values m := by
  classical
  rw [interpPartial, Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single_of_mem m.val (Finset.mem_range.mpr m.isLt) ?_]
  · rw [Polynomial.eval_mul, Polynomial.eval_C, basisProd, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [interpCoeff, mul_assoc, weights_prod_eq_one inv_weights hw m, mul_one, toPoint]
  · intro i hi hne
    rw [Polynomial.eval_mul, basisProd, Polynomial.eval_prod]
    have hmem : m.val ∈ (Finset.range n).erase i :=
      Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_range.mpr m.isLt⟩
    rw [Finset.prod_eq_zero hmem (by simp), MulZeroClass.mul_zero]

/-- `interpolate` computes `CLagrange.interpolateArray` at the nodes `0 … n − 1`
(spec: `CPolynomial.interpolateArray`, `LagrangeArray.lean:48`).

The extracted code forms `Σ_i y_i · w_i · ∏_{j ≠ i} (X − j)` with the nodes
hard-wired to `round_node` and the weights supplied, because cpoly has no
inversion at either carrier; `hw` says the supplied weights *are* the inverse
denominators, which is also what makes the nodes distinct (a repeated node
would zero the product). `hwlen` is the fail point `inv_weights[i]`. The
output has exactly `n` coefficients and is not trimmed; `toUni` trims. -/
theorem interpolate_spec {n : ℕ} (values : alloc.vec.Vec cpoly.field.Ext4)
    (inv_weights : alloc.vec.Vec cpoly.field.Fp)
    (hv : WfPoint n values) (hwlen : n ≤ inv_weights.val.length)
    (hwred : ∀ k < n, Red (inv_weights.val.getD k (0#u64 : cpoly.field.Fp)))
    (hw : ∀ i : Fin n, toK (inv_weights.val.getD i.val (0#u64 : cpoly.field.Fp)) *
      ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, ((i.val : ZMod q) - (j.val : ZMod q)) = 1) :
    sumcheck.interpolate values inv_weights
      ⦃ out => out.val.length = n ∧ VecReduced out ∧
        toUni out = CLagrange.interpolateArray
          (Array.ofFn fun i : Fin n => ((i.val : F), toPoint (m := n) values i)) ⦄ := by
  obtain ⟨hvlen, hvred⟩ := hv
  have hnmax : n ≤ Usize.max := by rw [← hvlen]; exact values.property
  have hnn : (alloc.vec.Vec.len values).val = n := by simpa using hvlen
  rw [sumcheck.interpolate]
  step with interpolate_zeros_loop_spec (n := n) (alloc.vec.Vec.len values) hnn hnmax
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize (by intro u hu; simp at hu) (by simp) (by simp)
    (by intro j; simp [toRaw]) as ⟨acc0, hacc0red, hacc0len, hacc0z⟩
  step with interpolate_outer_loop_spec (n := n) values inv_weights (alloc.vec.Vec.len values)
    ⟨hvlen, hvred⟩ hnn hwlen hwred acc0 0#usize hacc0red hacc0len (by simp)
    (by intro k; rw [hacc0z k, interpPartial]; simp) as ⟨acc, haccred, hacclen, haccc⟩
  apply spec_mono (uni_from_coeffs_spec acc haccred)
  rintro out ⟨houtred, houtraw⟩
  have houtlen : out.val.length = n := by
    have hs : (toRaw out).size = (toRaw acc).size := by rw [houtraw]
    rw [toRaw_size, toRaw_size, hacclen] at hs
    exact hs
  refine ⟨houtlen, houtred, ?_⟩
  have hnodes : ∀ i j : Fin n, i ≠ j → ((i.val : ℕ) : F) - ((j.val : ℕ) : F) ≠ 0 :=
    node_ne_of_weights (fun i => toK (inv_weights.val.getD i.val (0#u64 : cpoly.field.Fp))) hw
  have hQ : (CLagrange.interpolateArray
      (Array.ofFn fun i : Fin n => (((i.val : ℕ) : F), toPoint (m := n) values i))).toPoly
      = interpPartial values inv_weights n n :=
    interpolateArray_toPoly_eq _ _ hnodes
      (interpPartial_degree_lt values inv_weights n le_rfl)
      (interpPartial_eval values inv_weights hw)
  have htoUni : ∀ j, (toUni out).coeff j = (toRaw out).coeff j := by
    intro j; rw [toUni, CPolynomial.coeff_ofArray]
  refine CPolynomial.eq_iff_coeff.mpr (fun k => ?_)
  rw [htoUni k, houtraw, haccc k, CPolynomial.coeff_toPoly, hQ]

/- `tableFn_apply` moved to `lean/ZeroCheck.lean`, beside `tableFn`. -/

/-- `rangeSumZero` at a represented pair of tables, as a sum over a range. -/
theorem rangeSumZero_eq_sum_range {k : ℕ} (w eq : alloc.vec.Vec cpoly.field.Ext4) (T : F) :
    rangeSumZero (tableFn (m := k + 1) w) (tableFn (m := k) eq) T
      = ∑ y ∈ Finset.range (2 ^ k),
          toExt (eq.val.getD y cpoly.field.Ext4.ZERO) *
            InnerOuter.rangeProduct 16
              ((1 - T) * toExt (w.val.getD (2 * y) cpoly.field.Ext4.ZERO) +
                T * toExt (w.val.getD (2 * y + 1) cpoly.field.Ext4.ZERO)) := by
  rw [rangeSumZero, ← Fin.sum_univ_eq_sum_range (fun y : ℕ =>
    toExt (eq.val.getD y cpoly.field.Ext4.ZERO) *
      InnerOuter.rangeProduct 16
        ((1 - T) * toExt (w.val.getD (2 * y) cpoly.field.Ext4.ZERO) +
          T * toExt (w.val.getD (2 * y + 1) cpoly.field.Ext4.ZERO))) (2 ^ k)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [tableFn_apply, fold, tableFn_apply, tableFn_apply]
  rfl

/-- `linSumAlpha` at a represented pair of tables, as a sum over a range. -/
theorem linSumAlpha_eq_sum_range {k : ℕ} (w a : alloc.vec.Vec cpoly.field.Ext4) (T : F) :
    linSumAlpha (tableFn (m := k + 1) w) (tableFn (m := k + 1) a) T
      = ∑ y ∈ Finset.range (2 ^ k),
          ((1 - T) * toExt (w.val.getD (2 * y) cpoly.field.Ext4.ZERO) +
              T * toExt (w.val.getD (2 * y + 1) cpoly.field.Ext4.ZERO)) *
            ((1 - T) * toExt (a.val.getD (2 * y) cpoly.field.Ext4.ZERO) +
              T * toExt (a.val.getD (2 * y + 1) cpoly.field.Ext4.ZERO)) := by
  rw [linSumAlpha, ← Fin.sum_univ_eq_sum_range (fun y : ℕ =>
    ((1 - T) * toExt (w.val.getD (2 * y) cpoly.field.Ext4.ZERO) +
        T * toExt (w.val.getD (2 * y + 1) cpoly.field.Ext4.ZERO)) *
      ((1 - T) * toExt (a.val.getD (2 * y) cpoly.field.Ext4.ZERO) +
        T * toExt (a.val.getD (2 * y + 1) cpoly.field.Ext4.ZERO))) (2 ^ k)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [fold, fold, tableFn_apply, tableFn_apply, tableFn_apply, tableFn_apply]
  rfl

/-! ## The range summand -/

/-- `round_value_zero` at one node is `rangeSumZero` (spec: `computableRoundPoly`
at the `sumcheckPolyZero` summand, one node, less the kernel's free factor).
`w` has `2^(k+1)` entries and `eq` has `2^k`: the fail points are the reads
`w[2y]`, `w[2y+1]`, `eq[y]`, all inside those lengths. -/
theorem round_value_zero_spec {k : ℕ} (w eq : alloc.vec.Vec cpoly.field.Ext4)
    (node : cpoly.field.Ext4)
    (hw : WfEvals (k + 1) w) (heq : WfEvals k eq) (hn : Reduced node) :
    sumcheck.round_value_zero w eq node
      ⦃ out => Reduced out ∧
        toExt out = rangeSumZero (tableFn (m := k + 1) w) (tableFn (m := k) eq) (toExt node) ⦄ := by
  obtain ⟨hwlen, hwred⟩ := hw
  obtain ⟨heqlen, heqred⟩ := heq
  have hR1 : Reduced cpoly.field.Ext4.ONE := reduced_ONE
  have hRZ : Reduced cpoly.field.Ext4.ZERO := reduced_ZERO
  have hwmax : w.val.length ≤ Usize.max := w.property
  rw [sumcheck.round_value_zero]
  step as ⟨om, hRom, hom⟩
  rw [sumcheck.round_value_zero_loop]
  apply loop.spec_decr_nat (fun s => 2 ^ k - s.2.val)
    (fun s => s.2.val ≤ 2 ^ k ∧ Reduced s.1 ∧
      toExt s.1 = ∑ y ∈ Finset.range s.2.val,
        toExt (eq.val.getD y cpoly.field.Ext4.ZERO) *
          InnerOuter.rangeProduct 16
            ((1 - toExt node) * toExt (w.val.getD (2 * y) cpoly.field.Ext4.ZERO) +
              toExt node * toExt (w.val.getD (2 * y + 1) cpoly.field.Ext4.ZERO)))
  · rintro ⟨acc, y⟩ ⟨hy, hRacc, hacc⟩
    dsimp only at hy hRacc hacc
    simp only [sumcheck.round_value_zero_loop.body]
    by_cases hlt : y < alloc.vec.Vec.len eq
    · rw [if_pos hlt]
      have hylt : y.val < 2 ^ k := by
        have : y.val < eq.val.length := by scalar_tac
        omega
      have h2y : 2 * y.val + 1 < w.val.length := by rw [hwlen, pow_succ]; omega
      have hmul : 2 * y.val ≤ Usize.max := by omega
      step as ⟨i, hi⟩
      have hib : i.val < w.val.length := by rw [hi]; omega
      step as ⟨lo0, hlo0⟩
      have hRlo0 : Reduced lo0 := hlo0 ▸ hwred _ (List.getElem_mem hib)
      step as ⟨i1, hi1⟩
      have hi1b : i1.val < w.val.length := by rw [hi1, hi]; omega
      step as ⟨hi0, hhi0⟩
      have hRhi0 : Reduced hi0 := hhi0 ▸ hwred _ (List.getElem_mem hi1b)
      step as ⟨e, hRe, he⟩
      step as ⟨e1, hRe1, he1⟩
      step as ⟨folded, hRf, hf⟩
      have hyb : y.val < eq.val.length := by omega
      step as ⟨e2, he2⟩
      have hRe2 : Reduced e2 := he2 ▸ heqred _ (List.getElem_mem hyb)
      step with range_product_spec folded hRf as ⟨e3, hRe3, he3⟩
      step as ⟨e4, hRe4, he4⟩
      step as ⟨acc1, hRacc1, hacc1⟩
      step as ⟨y1, hy1⟩
      refine ⟨by scalar_tac, hRacc1, ?_, by scalar_tac⟩
      rw [hacc1, hacc, hy1, Finset.sum_range_succ, he4, he3, hf, he, he1, hom, toExt_ONE,
        he2, hlo0, hhi0,
        ← List.getD_eq_getElem eq.val cpoly.field.Ext4.ZERO hyb,
        ← List.getD_eq_getElem w.val cpoly.field.Ext4.ZERO hib,
        ← List.getD_eq_getElem w.val cpoly.field.Ext4.ZERO hi1b, hi1, hi]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hyeq : y.val = 2 ^ k := by
        have : eq.val.length ≤ y.val := by scalar_tac
        omega
      refine ⟨hRacc, ?_⟩
      rw [hacc, hyeq, rangeSumZero_eq_sum_range]
  · exact ⟨by simp, hRZ, by simp⟩

/-- `round_values_zero`: the `33` node values of `rangeSumZero`, at `0 … 32`. -/
theorem round_values_zero_spec {k : ℕ} (w eq : alloc.vec.Vec cpoly.field.Ext4)
    (hw : WfEvals (k + 1) w) (heq : WfEvals k eq) :
    sumcheck.round_values_zero w eq
      ⦃ out => out.val.length = 33 ∧ VecReduced out ∧
        ∀ t : Fin 33, toExt (out.val.getD t.val cpoly.field.Ext4.ZERO) =
          rangeSumZero (tableFn (m := k + 1) w) (tableFn (m := k) eq) (t.val : F) ⦄ := by
  have hrn : (params.ROUND_NODES).val = 33 := by simp [params.ROUND_NODES]
  have hmax := usize_max_ge
  rw [sumcheck.round_values_zero, sumcheck.round_values_zero_loop]
  apply loop.spec_decr_nat (fun s => 33 - s.2.val)
    (fun s => s.2.val ≤ 33 ∧ s.1.val.length = s.2.val ∧ VecReduced s.1 ∧
      ∀ t : ℕ, t < s.2.val → toExt (s.1.val.getD t cpoly.field.Ext4.ZERO) =
        rangeSumZero (tableFn (m := k + 1) w) (tableFn (m := k) eq) (t : F))
  · rintro ⟨v1, t1⟩ ⟨ht1, hlen1, hred1, hval1⟩
    dsimp only at ht1 hlen1 hred1 hval1
    simp only [sumcheck.round_values_zero_loop.body]
    by_cases hlt : t1 < params.ROUND_NODES
    · rw [if_pos hlt]
      have ht1lt : t1.val < 33 := by scalar_tac
      step with round_node_spec t1 as ⟨nd, hRnd, hnd⟩
      step with round_value_zero_spec (k := k) w eq nd hw heq hRnd as ⟨e, hRe, he⟩
      have hbound : v1.val.length < Usize.max := by omega
      step as ⟨v2, hv2⟩
      step as ⟨t2, ht2⟩
      have ht2n : t2.val = t1.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, ?_, ?_, by scalar_tac⟩
      · rw [ht2n, hv2, List.length_append, hlen1]; simp
      · intro u hu
        rw [hv2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hred1 u h
        · rw [List.mem_singleton.mp h]; exact hRe
      · intro t ht
        rw [ht2n] at ht
        rcases Nat.lt_or_ge t t1.val with htlt | htge
        · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = v1.val.length := by omega
          rw [hteq, hv2, getD_append_eq, he, hnd, hlen1]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hteq : t1.val = 33 := by scalar_tac
      exact ⟨by rw [hlen1, hteq], hred1, fun t => hval1 t.val (by rw [hteq]; exact t.isLt)⟩
  · exact ⟨by simp, by simp, by intro u hu; simp at hu, by intro t ht; simp at ht⟩


/-- `round_poly_zero` interpolates the `33` node values, and the interpolant
**is** `rangeSumZero` everywhere: the node function is a polynomial of degree
`2b − 1 = 31 < 33` (`rangeSumZero_poly`), so `33` nodes determine it. Exactly
`33` coefficients, untrimmed — the top one is zero, which is the arithmetic
fingerprint of the missing free factor (NOTES.md § "The dropped `eq̃` factor"). -/
theorem round_poly_zero_spec {k : ℕ} (w eq : alloc.vec.Vec cpoly.field.Ext4)
    (hw : WfEvals (k + 1) w) (heq : WfEvals k eq) :
    sumcheck.round_poly_zero w eq
      ⦃ out => out.val.length = 33 ∧ VecReduced out ∧
        ∀ x : F, CPolynomial.eval x (toUni out) =
          rangeSumZero (tableFn (m := k + 1) w) (tableFn (m := k) eq) x ⦄ := by
  rw [sumcheck.round_poly_zero]
  step with round_values_zero_spec (k := k) w eq hw heq as ⟨values, hvlen, hvred, hvval⟩
  step with round_node_weights_spec as ⟨weights, hwtlen, hwtred, hwtval⟩
  obtain ⟨p, hpdeg, hpval⟩ := rangeSumZero_poly (tableFn (m := k + 1) w) (tableFn (m := k) eq)
  have hpt : ∀ i : Fin 33, toPoint (m := 33) values i = CPolynomial.eval ((i.val : ℕ) : F) p := by
    intro i
    rw [toPoint, hvval i, hpval]
  apply spec_mono (interpolate_spec (n := 33) values weights ⟨hvlen, hvred⟩ (by omega)
    (fun t ht => hwtred _ (by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem (by omega))) hwtval)
  rintro out ⟨holen, hored, hoval⟩
  refine ⟨holen, hored, fun x => ?_⟩
  rw [hoval]
  rw [interpolateArray_eval_of_degreeLE (n := 33) (d := 31) (toPoint (m := 33) values) p
    (by norm_num) hpdeg
    (node_ne_of_weights (fun i => toK (weights.val.getD i.val (0#u64 : cpoly.field.Fp))) hwtval)
    hpt x]
  rw [hpval]

/-! ## The equality kernel in three pieces -/

/-- `eq_prefix` is the kernel on the bound prefix: `eq̃(τ₀|<i, a)` (spec:
`cEqualityPolynomial` at its bound prefix, `cEqualityPolynomial_eval_eq_eqProd`).
`i = challenges.len() ≤ m₀` is the fail point `tau0[k]`. -/
theorem eq_prefix_spec {m₀ i : ℕ} (tau0 challenges : alloc.vec.Vec cpoly.field.Ext4)
    (h0 : WfPoint m₀ tau0) (hc : WfPoint i challenges) (hi : i ≤ m₀) :
    sumcheck.eq_prefix tau0 challenges
      ⦃ out => Reduced out ∧ toExt out =
        eqProd (fun k : Fin i => toPoint (m := m₀) tau0 (Fin.castLE hi k))
          (toPoint (m := i) challenges) ⦄ := by
  obtain ⟨h0len, h0red⟩ := h0
  obtain ⟨hclen, hcred⟩ := hc
  have hR1 : Reduced cpoly.field.Ext4.ONE := reduced_ONE
  have hprod : eqProd (fun k : Fin i => toPoint (m := m₀) tau0 (Fin.castLE hi k))
      (toPoint (m := i) challenges)
      = ∏ j ∈ Finset.range i,
        (toExt (tau0.val.getD j cpoly.field.Ext4.ZERO) *
            toExt (challenges.val.getD j cpoly.field.Ext4.ZERO) +
          (1 - toExt (tau0.val.getD j cpoly.field.Ext4.ZERO)) *
            (1 - toExt (challenges.val.getD j cpoly.field.Ext4.ZERO))) := by
    rw [eqProd, ← Fin.prod_univ_eq_prod_range (fun j : ℕ =>
      (toExt (tau0.val.getD j cpoly.field.Ext4.ZERO) *
          toExt (challenges.val.getD j cpoly.field.Ext4.ZERO) +
        (1 - toExt (tau0.val.getD j cpoly.field.Ext4.ZERO)) *
          (1 - toExt (challenges.val.getD j cpoly.field.Ext4.ZERO)))) i]
    exact Finset.prod_congr rfl (fun j _ => rfl)
  rw [sumcheck.eq_prefix, sumcheck.eq_prefix_loop, hprod]
  apply loop.spec_decr_nat (fun s => i - s.2.val)
    (fun s => s.2.val ≤ i ∧ Reduced s.1 ∧
      toExt s.1 = ∏ j ∈ Finset.range s.2.val,
        (toExt (tau0.val.getD j cpoly.field.Ext4.ZERO) *
            toExt (challenges.val.getD j cpoly.field.Ext4.ZERO) +
          (1 - toExt (tau0.val.getD j cpoly.field.Ext4.ZERO)) *
            (1 - toExt (challenges.val.getD j cpoly.field.Ext4.ZERO))))
  · rintro ⟨acc, k⟩ ⟨hk, hRacc, hacc⟩
    dsimp only at hk hRacc hacc
    simp only [sumcheck.eq_prefix_loop.body]
    by_cases hlt : k < alloc.vec.Vec.len challenges
    · rw [if_pos hlt]
      have hkc : k.val < challenges.val.length := by scalar_tac
      have hkt : k.val < tau0.val.length := by rw [h0len]; omega
      step as ⟨t, ht⟩
      have hRt : Reduced t := ht ▸ h0red _ (List.getElem_mem hkt)
      step as ⟨a, ha⟩
      have hRa : Reduced a := ha ▸ hcred _ (List.getElem_mem hkc)
      step as ⟨e, hRe, he⟩
      step as ⟨e1, hRe1, he1⟩
      step as ⟨e2, hRe2, he2⟩
      step as ⟨e3, hRe3, he3⟩
      step as ⟨e4, hRe4, he4⟩
      step as ⟨acc1, hRacc1, hacc1⟩
      step as ⟨k1, hk1⟩
      refine ⟨by scalar_tac, hRacc1, ?_, by scalar_tac⟩
      rw [hacc1, hacc, hk1, Finset.prod_range_succ, he4, he, he3, he1, he2, toExt_ONE, ht, ha,
        ← List.getD_eq_getElem tau0.val cpoly.field.Ext4.ZERO hkt,
        ← List.getD_eq_getElem challenges.val cpoly.field.Ext4.ZERO hkc]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hkeq : k.val = i := by scalar_tac
      exact ⟨hRacc, by rw [hacc, hkeq]⟩
  · exact ⟨by simp, hR1, by simp⟩

/-- `getD` into the left part of an append. -/
theorem getD_append_left' {α : Type} (l1 l2 : List α) (d : α) {j : ℕ} (h : j < l1.length) :
    (l1 ++ l2).getD j d = l1.getD j d := by
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_append]; omega),
    List.getD_eq_getElem _ _ h, List.getElem_append_left h]

/-- `getD` into the right part of an append. -/
theorem getD_append_right' {α : Type} (l1 l2 : List α) (d : α) {j : ℕ} (h : l1.length ≤ j) :
    (l1 ++ l2).getD j d = l2.getD (j - l1.length) d := by
  by_cases hj : j - l1.length < l2.length
  · rw [List.getD_eq_getElem _ _ (by simp only [List.length_append]; omega),
      List.getD_eq_getElem _ _ hj, List.getElem_append_right h]
  · rw [List.getD_eq_default _ _ (by simp only [List.length_append]; omega),
      List.getD_eq_default _ _ (by omega)]

/-- Reading a represented vector's entry through the `toExt`-image list. -/
theorem toExt_getD_map (v : alloc.vec.Vec cpoly.field.Ext4) (idx : ℕ) :
    toExt (v.val.getD idx cpoly.field.Ext4.ZERO) = (v.val.map toExt).getD idx 0 := by
  by_cases h : idx < v.val.length
  · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by simpa using h),
      List.getElem_map]
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simpa using by omega),
      toExt_ZERO]

/-- The doubling loop of `eq_suffix_table`, scaling the current table by one
factor and appending it to what has been accumulated. -/
theorem eq_suffix_scale_loop_spec (tab : alloc.vec.Vec cpoly.field.Ext4)
    (c : cpoly.field.Ext4) (half : Std.Usize)
    (htab : VecReduced tab) (hc : Reduced c) (hhalf : half.val = tab.val.length)
    (pre : List F) (hpre : pre.length + tab.val.length ≤ Usize.max) :
    ∀ (next : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      VecReduced next → j.val ≤ half.val →
      next.val.map toExt = pre ++ (tab.val.take j.val).map (fun u => toExt u * toExt c) →
      sumcheck.eq_suffix_table_loop0_loop0 tab c half next j
        ⦃ z => VecReduced z ∧
          z.val.map toExt = pre ++ tab.val.map (fun u => toExt u * toExt c) ⦄ := by
  intro next j hnred hj hnmap
  rw [sumcheck.eq_suffix_table_loop0_loop0]
  apply loop.spec_decr_nat (fun st => half.val - st.2.val)
    (fun st => st.2.val ≤ half.val ∧ VecReduced st.1 ∧
      st.1.val.map toExt = pre ++ (tab.val.take st.2.val).map (fun u => toExt u * toExt c))
  · rintro ⟨nx, j1⟩ ⟨hj1, hnx, hmap⟩
    dsimp only at hj1 hnx hmap
    simp only [sumcheck.eq_suffix_table_loop0_loop0.body]
    by_cases hlt : j1 < half
    · rw [if_pos hlt]
      have hjt : j1.val < tab.val.length := by scalar_tac
      have hnxlen : nx.val.length = pre.length + j1.val := by
        have := congrArg List.length hmap
        simp only [List.length_map, List.length_append, List.length_take] at this
        omega
      have hbound : nx.val.length < Usize.max := by omega
      step as ⟨e, he⟩
      have hRe : Reduced e := he ▸ htab _ (List.getElem_mem hjt)
      step as ⟨e1, hRe1, he1⟩
      step as ⟨nx1, hnx1⟩
      step as ⟨j2, hj2⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · intro u hu
        rw [hnx1] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hnx u h
        · rw [List.mem_singleton.mp h]; exact hRe1
      · rw [hnx1, show j2.val = j1.val + 1 from by scalar_tac,
          ← List.take_concat_get' _ _ hjt]
        simp only [List.map_append, List.map_cons, List.map_nil, hmap, he1, he, List.append_assoc]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      refine ⟨hnx, ?_⟩
      rw [hmap, show j1.val = tab.val.length from by scalar_tac, List.take_length]
  · exact ⟨hj, hnred, hnmap⟩

/-- The second doubling loop of `eq_suffix_table`: the same shape at the other
factor. -/
theorem eq_suffix_scale_loop1_spec (tab : alloc.vec.Vec cpoly.field.Ext4)
    (c : cpoly.field.Ext4) (half : Std.Usize)
    (htab : VecReduced tab) (hc : Reduced c) (hhalf : half.val = tab.val.length)
    (pre : List F) (hpre : pre.length + tab.val.length ≤ Usize.max) :
    ∀ (next : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      VecReduced next → j.val ≤ half.val →
      next.val.map toExt = pre ++ (tab.val.take j.val).map (fun u => toExt u * toExt c) →
      sumcheck.eq_suffix_table_loop0_loop1 tab c half next j
        ⦃ z => VecReduced z ∧
          z.val.map toExt = pre ++ tab.val.map (fun u => toExt u * toExt c) ⦄ := by
  intro next j hnred hj hnmap
  rw [sumcheck.eq_suffix_table_loop0_loop1]
  apply loop.spec_decr_nat (fun st => half.val - st.2.val)
    (fun st => st.2.val ≤ half.val ∧ VecReduced st.1 ∧
      st.1.val.map toExt = pre ++ (tab.val.take st.2.val).map (fun u => toExt u * toExt c))
  · rintro ⟨nx, j1⟩ ⟨hj1, hnx, hmap⟩
    dsimp only at hj1 hnx hmap
    simp only [sumcheck.eq_suffix_table_loop0_loop1.body]
    by_cases hlt : j1 < half
    · rw [if_pos hlt]
      have hjt : j1.val < tab.val.length := by scalar_tac
      have hnxlen : nx.val.length = pre.length + j1.val := by
        have := congrArg List.length hmap
        simp only [List.length_map, List.length_append, List.length_take] at this
        omega
      have hbound : nx.val.length < Usize.max := by omega
      step as ⟨e, he⟩
      have hRe : Reduced e := he ▸ htab _ (List.getElem_mem hjt)
      step as ⟨e1, hRe1, he1⟩
      step as ⟨nx1, hnx1⟩
      step as ⟨j2, hj2⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · intro u hu
        rw [hnx1] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hnx u h
        · rw [List.mem_singleton.mp h]; exact hRe1
      · rw [hnx1, show j2.val = j1.val + 1 from by scalar_tac,
          ← List.take_concat_get' _ _ hjt]
        simp only [List.map_append, List.map_cons, List.map_nil, hmap, he1, he, List.append_assoc]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      refine ⟨hnx, ?_⟩
      rw [hmap, show j1.val = tab.val.length from by scalar_tac, List.take_length]
  · exact ⟨hj, hnred, hnmap⟩

/-- `eq_suffix_table` is the Lagrange basis of the suffix `τ₀|>i`, indexed
little-endian (the first suffix coordinate is the low bit, as
`lagrangeBasis`'s `getLsb` has it) (spec: `lagrangeBasis` at the suffix
coordinates, `CompPoly/Multilinear/Basic.lean:410`).

Two fail points, two bounds. The checked `i + 1` needs `i < Usize.max` and
nothing stronger: at `i ≥ m₀` the loop is empty, the table is `[1]`, and the
postcondition holds at width `0` (`lagrangeBasis` of the empty point is
`#[1]`), so the specification's `i < m₀` framing is *not* a precondition of
this function and is not assumed. The table doubles once per suffix
coordinate through `Vec::push`, so its final size `2^(m₀ − i − 1)` must fit a
`usize` -- the output's own length, the same shape as `cube_size`'s bound.
Found by cross-review: the first version had neither the right bound nor
the honest one. -/
theorem eq_suffix_table_spec {m₀ : ℕ} (tau0 : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize)
    (h0 : WfPoint m₀ tau0) (hi : i.val < Usize.max)
    (hsz : 2 ^ (m₀ - i.val - 1) ≤ Usize.max) :
    sumcheck.eq_suffix_table tau0 i
      ⦃ out => WfEvals (m₀ - i.val - 1) out ∧
        toEvals (m := m₀ - i.val - 1) out =
          CMlPolynomialEval.lagrangeBasis (Vector.ofFn fun k : Fin (m₀ - i.val - 1) =>
            toPoint (m := m₀) tau0 ⟨i.val + 1 + k.val, by omega⟩) ⦄ := by
  obtain ⟨h0len, h0red⟩ := h0
  have hR1 : Reduced cpoly.field.Ext4.ONE := reduced_ONE
  have hmaxbig := usize_max_ge
  rw [sumcheck.eq_suffix_table]
  have hpush0 : (alloc.vec.Vec.new cpoly.field.Ext4).val.length < Usize.max := by simp; omega
  step as ⟨tab0, htab0⟩
  step as ⟨k0, hk0⟩
  have hk0v : k0.val = i.val + 1 := by scalar_tac
  rw [sumcheck.eq_suffix_table_loop0]
  apply loop.spec_decr_nat (fun st => m₀ - st.2.val)
    (fun st => i.val + 1 ≤ st.2.val ∧ st.2.val ≤ max (i.val + 1) m₀ ∧ VecReduced st.1 ∧
      st.1.val.length = 2 ^ (st.2.val - i.val - 1) ∧
      ∀ idx : ℕ, idx < st.1.val.length →
        toExt (st.1.val.getD idx cpoly.field.Ext4.ZERO) =
          ∏ s ∈ Finset.range (st.2.val - i.val - 1),
            (if Nat.testBit idx s then toExt (tau0.val.getD (i.val + 1 + s) cpoly.field.Ext4.ZERO)
              else 1 - toExt (tau0.val.getD (i.val + 1 + s) cpoly.field.Ext4.ZERO)))
  · rintro ⟨tab, k⟩ ⟨hk1, hk2, hred, hlen, hval⟩
    dsimp only at hk1 hk2 hred hlen hval
    simp only [sumcheck.eq_suffix_table_loop0.body]
    by_cases hlt : k < alloc.vec.Vec.len tau0
    · rw [if_pos hlt]
      have hklt : k.val < m₀ := by rw [← h0len]; scalar_tac
      have hd : k.val - i.val - 1 < m₀ - i.val - 1 := by omega
      have hdlen : tab.val.length = 2 ^ (k.val - i.val - 1) := hlen
      have hbnd : 2 * tab.val.length ≤ Usize.max := by
        rw [hdlen]
        calc 2 * 2 ^ (k.val - i.val - 1) = 2 ^ (k.val - i.val) := by
              rw [← pow_succ']
              congr 1
              omega
          _ ≤ 2 ^ (m₀ - i.val - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ Usize.max := hsz
      have hkt : k.val < tau0.val.length := by omega
      step as ⟨t, ht⟩
      have hRt : Reduced t := ht ▸ h0red _ (List.getElem_mem hkt)
      step as ⟨om, hRom, hom⟩
      rw [toExt_ONE] at hom
      apply spec_bind (eq_suffix_scale_loop_spec tab om (alloc.vec.Vec.len tab) hred hRom
        (by simp) [] (by simpa using by omega) (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize
        (by intro u hu; simp at hu) (by simp) (by simp))
      rintro nxt ⟨hnred, hnmap⟩
      simp only [List.nil_append] at hnmap
      have hnlen : nxt.val.length = tab.val.length := by
        have := congrArg List.length hnmap
        simpa using this
      apply spec_bind (eq_suffix_scale_loop1_spec tab t (alloc.vec.Vec.len tab) hred hRt
        (by simp) (nxt.val.map toExt) (by simp [hnlen]; omega) nxt 0#usize hnred (by simp)
        (by simp))
      rintro nxt1 ⟨hn1red, hn1map⟩
      step as ⟨k1, hk1v⟩
      have hk1n : k1.val = k.val + 1 := by scalar_tac
      have hn1len : nxt1.val.length = 2 * tab.val.length := by
        have := congrArg List.length hn1map
        simp only [List.length_map, List.length_append] at this
        omega
      refine ⟨by omega, by omega, ?_, ?_, ?_, by scalar_tac⟩
      · exact hn1red
      · rw [hk1n, hn1len, hdlen]
        rw [show k.val + 1 - i.val - 1 = (k.val - i.val - 1) + 1 from by omega, pow_succ]
        omega
      · intro idx hidx
        rw [hk1n]
        rw [show k.val + 1 - i.val - 1 = (k.val - i.val - 1) + 1 from by omega,
          Finset.prod_range_succ]
        have hdt : i.val + 1 + (k.val - i.val - 1) = k.val := by omega
        have htauk : toExt (tau0.val.getD k.val cpoly.field.Ext4.ZERO) = toExt t := by
          rw [ht, List.getD_eq_getElem _ _ hkt]
        rw [hdt, htauk]
        rw [toExt_getD_map, hn1map]
        rcases Nat.lt_or_ge idx tab.val.length with hlow | hhigh
        · have hbitfalse : Nat.testBit idx (k.val - i.val - 1) = false :=
            Nat.testBit_lt_two_pow (by rw [← hdlen]; exact hlow)
          rw [hbitfalse, if_neg (by simp),
            getD_append_left' _ _ _ (by simp only [List.length_map, hnlen]; omega), hnmap,
            List.getD_eq_getElem _ _ (by simpa using hlow), List.getElem_map,
            ← List.getD_eq_getElem _ _ hlow, hval idx hlow, hom]
        · have hidx' : idx - tab.val.length < tab.val.length := by
            rw [hn1len] at hidx; omega
          have hidxsplit : idx = 2 ^ (k.val - i.val - 1) + (idx - tab.val.length) := by
            rw [← hdlen]; omega
          have hbittrue : Nat.testBit idx (k.val - i.val - 1) = true := by
            rw [hidxsplit, Nat.testBit_two_pow_add_eq,
              Nat.testBit_lt_two_pow (by rw [← hdlen]; exact hidx')]
            rfl
          have hbitlow : ∀ s ∈ Finset.range (k.val - i.val - 1),
              (if Nat.testBit idx s then toExt (tau0.val.getD (i.val + 1 + s) cpoly.field.Ext4.ZERO)
                else 1 - toExt (tau0.val.getD (i.val + 1 + s) cpoly.field.Ext4.ZERO))
              = (if Nat.testBit (idx - tab.val.length) s then
                  toExt (tau0.val.getD (i.val + 1 + s) cpoly.field.Ext4.ZERO)
                else 1 - toExt (tau0.val.getD (i.val + 1 + s) cpoly.field.Ext4.ZERO)) := by
            intro s hs
            have hbit : Nat.testBit idx s = Nat.testBit (idx - tab.val.length) s := by
              conv_lhs => rw [hidxsplit]
              exact Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hs) _
            rw [hbit]
          have hlenmap : (nxt.val.map toExt).length = tab.val.length := by simp [hnlen]
          rw [hbittrue, if_pos rfl, Finset.prod_congr rfl hbitlow, ← hval _ hidx',
            getD_append_right' _ _ _ (by rw [hlenmap]; omega), hlenmap,
            List.getD_eq_getElem _ _ (by simpa using hidx'), List.getElem_map,
            ← List.getD_eq_getElem _ _ hidx']
    · rw [if_neg hlt, WP.spec_ok]
      have hkm : m₀ ≤ k.val := by rw [← h0len] at hk2 ⊢; scalar_tac
      have hdeq : k.val - i.val - 1 = m₀ - i.val - 1 := by omega
      rw [hdeq] at hlen hval
      refine ⟨⟨hlen, hred⟩, ?_⟩
      apply Vector.ext
      intro idx hidx
      have hidxlen : idx < tab.val.length := by rw [hlen]; exact hidx
      have hbasis : (CMlPolynomialEval.lagrangeBasis
          (Vector.ofFn fun s : Fin (m₀ - i.val - 1) =>
            toPoint (m := m₀) tau0 ⟨i.val + 1 + s.val, by omega⟩))[idx]
          = ∏ s : Fin (m₀ - i.val - 1),
            (if (BitVec.ofFin (⟨idx, hidx⟩ : Fin (2 ^ (m₀ - i.val - 1)))).getLsb s then
                (Vector.ofFn fun s : Fin (m₀ - i.val - 1) =>
                  toPoint (m := m₀) tau0 ⟨i.val + 1 + s.val, by omega⟩).get s
              else 1 - (Vector.ofFn fun s : Fin (m₀ - i.val - 1) =>
                  toPoint (m := m₀) tau0 ⟨i.val + 1 + s.val, by omega⟩).get s) :=
        Hachi.lagrangeBasis_get _ ⟨idx, hidx⟩
      have hlhs : (toEvals (m := m₀ - i.val - 1) tab)[idx]
          = toExt (tab.val.getD idx cpoly.field.Ext4.ZERO) := by
        simp [toEvals]
      rw [hlhs, hval idx hidxlen, hbasis]
      rw [← Fin.prod_univ_eq_prod_range (fun s =>
        (if Nat.testBit idx s then toExt (tau0.val.getD (i.val + 1 + s) cpoly.field.Ext4.ZERO)
          else 1 - toExt (tau0.val.getD (i.val + 1 + s) cpoly.field.Ext4.ZERO)))
        (m₀ - i.val - 1)]
      refine Finset.prod_congr rfl (fun s _ => ?_)
      simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, Vector.get_ofFn,
        toPoint]
  · dsimp only
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · intro u hu
      rw [htab0] at hu
      simp only [List.mem_append, List.mem_singleton] at hu
      rcases hu with h | h
      · simp at h
      · exact h ▸ hR1
    · rw [htab0, hk0v]
      simp
    · intro idx hidx
      rw [htab0] at hidx ⊢
      simp only [List.length_append, List.length_singleton] at hidx
      have hidx0 : idx = 0 := by simpa using hidx
      rw [hidx0, hk0v]
      simp

/-- `eq_free_factor t` is the degree-one polynomial `eq(t, X) = (1 − t) + (2t − 1)X`
(spec: `cEqualityPolynomial` at its free coordinate), stated by its values.
Two coefficients, untrimmed. -/
theorem eq_free_factor_spec (t : cpoly.field.Ext4) (ht : Reduced t) :
    sumcheck.eq_free_factor t
      ⦃ out => out.val.length = 2 ∧ VecReduced out ∧
        ∀ x : F, CPolynomial.eval x (toUni out) = (1 - toExt t) * (1 - x) + toExt t * x ⦄ := by
  have hR1 : Reduced cpoly.field.Ext4.ONE := reduced_ONE
  rw [sumcheck.eq_free_factor]
  step as ⟨a, hRa, ha⟩
  step as ⟨c1, hc1⟩
  step as ⟨d, hRd, hd⟩
  step as ⟨e, hRe, he⟩
  step as ⟨c2, hc2⟩
  have hc2v : c2.val = [a, e] := by rw [hc2, hc1]; simp
  have hc2red : VecReduced c2 := by
    intro u hu
    rw [hc2v] at hu
    rcases List.mem_cons.mp hu with h | h
    · exact h ▸ hRa
    · rcases List.mem_cons.mp h with h' | h'
      · exact h' ▸ hRe
      · simp at h'
  apply spec_mono (uni_from_coeffs_spec c2 hc2red)
  rintro z ⟨hzred, hzraw⟩
  have hzlen : z.val.length = 2 := by
    have := congrArg Array.size hzraw
    rw [toRaw_size, toRaw_size, hc2v] at this
    simpa using this
  refine ⟨hzlen, hzred, ?_⟩
  intro x
  rw [toUni_eval, toRaw_eval_eq_sum z x 2 (by omega), Finset.sum_range_succ,
    Finset.sum_range_one, hzraw, toRaw_coeff_of_lt c2 (by rw [hc2v]; simp),
    toRaw_coeff_of_lt c2 (by rw [hc2v]; simp),
    getElem_of_list_eq hc2v (i := 0), getElem_of_list_eq hc2v (i := 1)]
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, he, hd, ha, toExt_ONE, pow_zero,
    pow_one, mul_one]
  ring

/-! ## The linear summand -/

/-- `round_value_alpha` at one node is `linSumAlpha` (spec: `computableRoundPoly`
at the `sumcheckPolyAlpha` summand, one node). Here the half-width is read off
`w`, so both tables carry `2^(k+1)` entries. -/
theorem round_value_alpha_spec {k : ℕ} (w a_tab : alloc.vec.Vec cpoly.field.Ext4)
    (node : cpoly.field.Ext4)
    (hw : WfEvals (k + 1) w) (ha : WfEvals (k + 1) a_tab) (hn : Reduced node) :
    sumcheck.round_value_alpha w a_tab node
      ⦃ out => Reduced out ∧
        toExt out = linSumAlpha (tableFn (m := k + 1) w) (tableFn (m := k + 1) a_tab) (toExt node) ⦄ := by
  obtain ⟨hwlen, hwred⟩ := hw
  obtain ⟨halen, hared⟩ := ha
  have hR1 : Reduced cpoly.field.Ext4.ONE := reduced_ONE
  have hRZ : Reduced cpoly.field.Ext4.ZERO := reduced_ZERO
  have hwmax : w.val.length ≤ Usize.max := w.property
  rw [sumcheck.round_value_alpha]
  step as ⟨half, hhalf⟩
  have hlenw : (alloc.vec.Vec.len w).val = w.val.length := by simp
  have hhalfv : half.val = 2 ^ k := by
    rw [hhalf, hlenw, hwlen, pow_succ]
    omega
  step as ⟨om, hRom, hom⟩
  rw [sumcheck.round_value_alpha_loop]
  apply loop.spec_decr_nat (fun s => 2 ^ k - s.2.val)
    (fun s => s.2.val ≤ 2 ^ k ∧ Reduced s.1 ∧
      toExt s.1 = ∑ y ∈ Finset.range s.2.val,
        ((1 - toExt node) * toExt (w.val.getD (2 * y) cpoly.field.Ext4.ZERO) +
            toExt node * toExt (w.val.getD (2 * y + 1) cpoly.field.Ext4.ZERO)) *
          ((1 - toExt node) * toExt (a_tab.val.getD (2 * y) cpoly.field.Ext4.ZERO) +
            toExt node * toExt (a_tab.val.getD (2 * y + 1) cpoly.field.Ext4.ZERO)))
  · rintro ⟨acc, y⟩ ⟨hy, hRacc, hacc⟩
    dsimp only at hy hRacc hacc
    simp only [sumcheck.round_value_alpha_loop.body]
    by_cases hlt : y < half
    · rw [if_pos hlt]
      have hylt : y.val < 2 ^ k := by
        have : y.val < half.val := by scalar_tac
        omega
      have h2y : 2 * y.val + 1 < w.val.length := by rw [hwlen, pow_succ]; omega
      have h2ya : 2 * y.val + 1 < a_tab.val.length := by rw [halen, pow_succ]; omega
      have hmul : 2 * y.val ≤ Usize.max := by omega
      step as ⟨i, hi⟩
      have hib : i.val < w.val.length := by rw [hi]; omega
      step as ⟨wlo, hwlo⟩
      have hRwlo : Reduced wlo := hwlo ▸ hwred _ (List.getElem_mem hib)
      step as ⟨e1, hRe1, he1⟩
      step as ⟨i1, hi1⟩
      have hi1b : i1.val < w.val.length := by rw [hi1, hi]; omega
      step as ⟨whi, hwhi⟩
      have hRwhi : Reduced whi := hwhi ▸ hwred _ (List.getElem_mem hi1b)
      step as ⟨e3, hRe3, he3⟩
      step as ⟨wf, hRwf, hwf⟩
      have hiba : i.val < a_tab.val.length := by rw [hi]; omega
      step as ⟨alo, halo⟩
      have hRalo : Reduced alo := halo ▸ hared _ (List.getElem_mem hiba)
      step as ⟨e5, hRe5, he5⟩
      step as ⟨i2, hi2⟩
      have hi2b : i2.val < a_tab.val.length := by rw [hi2, hi]; omega
      step as ⟨ahi, hahi⟩
      have hRahi : Reduced ahi := hahi ▸ hared _ (List.getElem_mem hi2b)
      step as ⟨e7, hRe7, he7⟩
      step as ⟨af, hRaf, haf⟩
      step as ⟨e8, hRe8, he8⟩
      step as ⟨acc1, hRacc1, hacc1⟩
      step as ⟨y1, hy1⟩
      refine ⟨by scalar_tac, hRacc1, ?_, by scalar_tac⟩
      rw [hacc1, hacc, hy1, Finset.sum_range_succ, he8, hwf, haf, he1, he3, he5, he7, hom,
        toExt_ONE, hwlo, hwhi, halo, hahi,
        ← List.getD_eq_getElem w.val cpoly.field.Ext4.ZERO hib,
        ← List.getD_eq_getElem w.val cpoly.field.Ext4.ZERO hi1b,
        ← List.getD_eq_getElem a_tab.val cpoly.field.Ext4.ZERO hiba,
        ← List.getD_eq_getElem a_tab.val cpoly.field.Ext4.ZERO hi2b, hi1, hi2, hi]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hyeq : y.val = 2 ^ k := by
        have : half.val ≤ y.val := by scalar_tac
        omega
      refine ⟨hRacc, ?_⟩
      rw [hacc, hyeq, linSumAlpha_eq_sum_range]
  · exact ⟨by simp, hRZ, by simp⟩

/-- `round_values_alpha`: the `3` node values of `linSumAlpha`, at `0, 1, 2`. -/
theorem round_values_alpha_spec {k : ℕ} (w a_tab : alloc.vec.Vec cpoly.field.Ext4)
    (hw : WfEvals (k + 1) w) (ha : WfEvals (k + 1) a_tab) :
    sumcheck.round_values_alpha w a_tab
      ⦃ out => out.val.length = 3 ∧ VecReduced out ∧
        ∀ t : Fin 3, toExt (out.val.getD t.val cpoly.field.Ext4.ZERO) =
          linSumAlpha (tableFn (m := k + 1) w) (tableFn (m := k + 1) a_tab) (t.val : F) ⦄ := by
  have hrn : (params.ROUND_NODES_ALPHA).val = 3 := by simp [params.ROUND_NODES_ALPHA]
  have hmax := usize_max_ge
  rw [sumcheck.round_values_alpha, sumcheck.round_values_alpha_loop]
  apply loop.spec_decr_nat (fun s => 3 - s.2.val)
    (fun s => s.2.val ≤ 3 ∧ s.1.val.length = s.2.val ∧ VecReduced s.1 ∧
      ∀ t : ℕ, t < s.2.val → toExt (s.1.val.getD t cpoly.field.Ext4.ZERO) =
        linSumAlpha (tableFn (m := k + 1) w) (tableFn (m := k + 1) a_tab) (t : F))
  · rintro ⟨v1, t1⟩ ⟨ht1, hlen1, hred1, hval1⟩
    dsimp only at ht1 hlen1 hred1 hval1
    simp only [sumcheck.round_values_alpha_loop.body]
    by_cases hlt : t1 < params.ROUND_NODES_ALPHA
    · rw [if_pos hlt]
      have ht1lt : t1.val < 3 := by scalar_tac
      step with round_node_spec t1 as ⟨nd, hRnd, hnd⟩
      step with round_value_alpha_spec (k := k) w a_tab nd hw ha hRnd as ⟨e, hRe, he⟩
      have hbound : v1.val.length < Usize.max := by omega
      step as ⟨v2, hv2⟩
      step as ⟨t2, ht2⟩
      have ht2n : t2.val = t1.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, ?_, ?_, by scalar_tac⟩
      · rw [ht2n, hv2, List.length_append, hlen1]; simp
      · intro u hu
        rw [hv2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hred1 u h
        · rw [List.mem_singleton.mp h]; exact hRe
      · intro t ht
        rw [ht2n] at ht
        rcases Nat.lt_or_ge t t1.val with htlt | htge
        · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = v1.val.length := by omega
          rw [hteq, hv2, getD_append_eq, he, hnd, hlen1]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hteq : t1.val = 3 := by scalar_tac
      exact ⟨by rw [hlen1, hteq], hred1, fun t => hval1 t.val (by rw [hteq]; exact t.isLt)⟩
  · exact ⟨by simp, by simp, by intro u hu; simp at hu, by intro t ht; simp at ht⟩

/-- `round_poly_alpha` interpolates the `3` node values, and the interpolant is
`linSumAlpha` everywhere (`linSumAlpha_poly`: degree `≤ 2 < 3`). -/
theorem round_poly_alpha_spec {k : ℕ} (w a_tab : alloc.vec.Vec cpoly.field.Ext4)
    (hw : WfEvals (k + 1) w) (ha : WfEvals (k + 1) a_tab) :
    sumcheck.round_poly_alpha w a_tab
      ⦃ out => out.val.length = 3 ∧ VecReduced out ∧
        ∀ x : F, CPolynomial.eval x (toUni out) =
          linSumAlpha (tableFn (m := k + 1) w) (tableFn (m := k + 1) a_tab) x ⦄ := by
  rw [sumcheck.round_poly_alpha]
  step with round_values_alpha_spec (k := k) w a_tab hw ha as ⟨values, hvlen, hvred, hvval⟩
  step with round_node_weights_alpha_spec as ⟨weights, hwtlen, hwtred, hwtval⟩
  obtain ⟨p, hpdeg, hpval⟩ :=
    linSumAlpha_poly (tableFn (m := k + 1) w) (tableFn (m := k + 1) a_tab)
  have hpt : ∀ i : Fin 3, toPoint (m := 3) values i = CPolynomial.eval ((i.val : ℕ) : F) p := by
    intro i
    rw [toPoint, hvval i, hpval]
  apply spec_mono (interpolate_spec (n := 3) values weights ⟨hvlen, hvred⟩ (by omega)
    (fun t ht => hwtred _ (by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem (by omega))) hwtval)
  rintro out ⟨holen, hored, hoval⟩
  refine ⟨holen, hored, fun x => ?_⟩
  rw [hoval]
  rw [interpolateArray_eval_of_degreeLE (n := 3) (d := 2) (toPoint (m := 3) values) p
    (by norm_num) hpdeg
    (node_ne_of_weights (fun i => toK (weights.val.getD i.val (0#u64 : cpoly.field.Fp))) hwtval)
    hpt x]
  rw [hpval]

/-! ## The public α table -/

/-- `alpha_public_table` tabulates `alphaPublicEvals` over the `m₀`-cube, entry
`idx` at the point `finFunctionFinEquiv.symm idx` (spec: `alphaPublicEvals` as a
hypercube table). `2 ^ m₀ ≤ Usize.max` is `cube_size`'s; `hmax` is
`alpha_public_evals_spec`'s. -/
theorem alpha_public_table_spec {n μ m₁ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) (m0 : Std.Usize)
    (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha) (ht : WfPoint m₁ tau1)
    (hm0 : 2 ^ m0.val ≤ Usize.max) (hmax : μ + n * 8 ≤ Usize.max) :
    sumcheck.alpha_public_table s alpha tau1 m0
      ⦃ out => WfEvals m0.val out ∧ toEvals (m := m0.val) out =
        Vector.ofFn fun idx : Fin (2 ^ m0.val) =>
          InnerOuter.alphaPublicEvals Φ m0.val m₁ phiF 16 rs (toExt alpha)
            (toPoint (m := m₁) tau1) (finFunctionFinEquiv.symm idx) ⦄ := by
  rw [sumcheck.alpha_public_table]
  step with cube_size_spec m0 hm0 as ⟨sz, hsz⟩
  rw [sumcheck.alpha_public_table_loop]
  apply loop.spec_decr_nat (fun st => 2 ^ m0.val - st.2.val)
    (fun st => st.2.val ≤ 2 ^ m0.val ∧ st.1.val.length = st.2.val ∧ VecReduced st.1 ∧
      ∀ t : Fin (2 ^ m0.val), t.val < st.2.val →
        toExt (st.1.val.getD t.val cpoly.field.Ext4.ZERO) =
          InnerOuter.alphaPublicEvals Φ m0.val m₁ phiF 16 rs (toExt alpha)
            (toPoint (m := m₁) tau1) (finFunctionFinEquiv.symm t))
  · rintro ⟨v1, i1⟩ ⟨hi1, hlen1, hred1, hval1⟩
    dsimp only at hi1 hlen1 hred1 hval1
    simp only [sumcheck.alpha_public_table_loop.body]
    by_cases hlt : i1 < sz
    · rw [if_pos hlt]
      have hilt : i1.val < 2 ^ m0.val := by rw [← hsz]; scalar_tac
      step with alpha_public_evals_spec (n := n) (μ := μ) (m₀ := m0.val) (m₁ := m₁)
        s rs alpha tau1 i1 hs ha ht hilt hmax as ⟨e, hRe, he⟩
      have hbound : v1.val.length < Usize.max := by omega
      step as ⟨v2, hv2⟩
      step as ⟨i2, hi2⟩
      have hi2n : i2.val = i1.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, ?_, ?_, by scalar_tac⟩
      · rw [hi2n, hv2, List.length_append, hlen1]; simp
      · intro u hu
        rw [hv2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hred1 u h
        · rw [List.mem_singleton.mp h]; exact hRe
      · intro t ht'
        rw [hi2n] at ht'
        rcases Nat.lt_or_ge t.val i1.val with htlt | htge
        · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t.val = v1.val.length := by omega
          rw [hteq, hv2, getD_append_eq, he]
          congr 2
          refine Fin.ext ?_
          show i1.val = t.val
          omega
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hieq : i1.val = 2 ^ m0.val := by rw [← hsz] at hi1 ⊢; scalar_tac
      refine ⟨⟨by rw [hlen1, hieq], hred1⟩, ?_⟩
      rw [toEvals]
      congr 1
      funext t
      exact hval1 t (by rw [hieq]; exact t.isLt)
  · exact ⟨by simp, by simp, by intro u hu; simp at hu, by intro t ht'; simp at ht'⟩

/-! ## Generic tools for the honest round message -/

/-- A coefficient vector of length `≤ d + 1` denotes a polynomial of degree `≤ d`. -/
theorem toUni_mem_degreeLE (v : alloc.vec.Vec cpoly.field.Ext4) (d : ℕ)
    (hlen : v.val.length ≤ d + 1) :
    toUni v ∈ CPolynomial.degreeLE (R := F) (d : ℕ) := by
  rw [CPolynomial.degreeLE_toPoly, Polynomial.mem_degreeLE,
    Polynomial.degree_le_iff_coeff_zero]
  intro k hk
  have hdj : d < k := by exact_mod_cast hk
  rw [← CPolynomial.coeff_toPoly, toUni, CPolynomial.coeff_ofArray]
  exact toRaw_coeff_of_ge v (by omega)

/-- Two `CPolynomial`s of degree `≤ d`, with `d + 1 ≤ q`, that agree at every point of `F`
are equal: `F` has `q ^ 4` elements, so `d + 1` distinct nodes are available and Lagrange
uniqueness applies. -/
theorem cpoly_eq_of_eval_eq {d : ℕ} (hdq : d + 1 ≤ q) (p₁ p₂ : CPolynomial F)
    (h1 : p₁ ∈ CPolynomial.degreeLE (R := F) (d : ℕ))
    (h2 : p₂ ∈ CPolynomial.degreeLE (R := F) (d : ℕ))
    (h : ∀ x : F, CPolynomial.eval x p₁ = CPolynomial.eval x p₂) : p₁ = p₂ := by
  classical
  set v : Fin (d + 1) → F := fun j => ((j.val : ℕ) : F) with hv
  have hinj : Set.InjOn v ↑(Finset.univ : Finset (Fin (d + 1))) := by
    intro a _ b _ hab
    rw [hv] at hab
    dsimp only at hab
    have hmap : ∀ c : ℕ, ((c : ℕ) : F) = phiF ((c : ℕ) : ZMod q) := fun c =>
      (map_natCast phiF c).symm
    rw [hmap, hmap] at hab
    have hzm : ((a.val : ℕ) : ZMod q) = ((b.val : ℕ) : ZMod q) := phiF.injective hab
    have ha : ((a.val : ℕ) : ZMod q).val = a.val :=
      ZMod.val_natCast_of_lt (by have := a.isLt; omega)
    have hb : ((b.val : ℕ) : ZMod q).val = b.val :=
      ZMod.val_natCast_of_lt (by have := b.isLt; omega)
    exact Fin.ext (by rw [← ha, ← hb, hzm])
  have hcard : (Finset.univ : Finset (Fin (d + 1))).card = d + 1 := by simp
  have hdeg : ∀ p : CPolynomial F, p ∈ CPolynomial.degreeLE (R := F) (d : ℕ) →
      p.toPoly.degree < (Finset.univ : Finset (Fin (d + 1))).card := by
    intro p hp
    rw [CPolynomial.degreeLE_toPoly, Polynomial.mem_degreeLE] at hp
    rw [hcard]
    exact lt_of_le_of_lt hp (by exact_mod_cast Nat.lt_succ_self d)
  have e1 := Lagrange.eq_interpolate_of_eval_eq (v := v)
    (r := fun j => CPolynomial.eval (v j) p₁) (s := Finset.univ) hinj (hdeg p₁ h1)
    (fun j _ => by rw [CPolynomial.eval_toPoly])
  have e2 := Lagrange.eq_interpolate_of_eval_eq (v := v)
    (r := fun j => CPolynomial.eval (v j) p₁) (s := Finset.univ) hinj (hdeg p₂ h2)
    (fun j _ => by rw [← CPolynomial.eval_toPoly]; exact (h (v j)).symm)
  have htp : p₁.toPoly = p₂.toPoly := by rw [e1, e2]
  rw [CPolynomial.eq_iff_coeff]
  intro k
  rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly, htp]

/-- **Multilinearity of a multilinear extension in one coordinate.** -/
theorem cMLE_eval_update {m : ℕ} (evals : (Fin m → Fin 2) → F) (p : Fin m → F) (c : Fin m) :
    (InnerOuter.cMultilinearExtension m evals).eval p =
      (1 - p c) * (InnerOuter.cMultilinearExtension m evals).eval (Function.update p c 0) +
        p c * (InnerOuter.cMultilinearExtension m evals).eval (Function.update p c 1) := by
  rw [InnerOuter.cMultilinearExtension_eval, InnerOuter.cMultilinearExtension_eval,
    InnerOuter.cMultilinearExtension_eval, InnerOuter.eval_MLE_eq_sum,
    InnerOuter.eval_MLE_eq_sum, InnerOuter.eval_MLE_eq_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have key : ∀ t : F, ∏ j : Fin m, (if x j = 1 then Function.update p c t j
        else 1 - Function.update p c t j)
      = (if x c = 1 then t else 1 - t) *
        ∏ j ∈ Finset.univ.erase c, (if x j = 1 then p j else 1 - p j) := by
    intro t
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [key 0, key 1, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
  by_cases h : x c = 1
  · simp only [if_pos h]; ring
  · simp only [if_neg h]; ring

/-- The little-endian index of a cube point with a prepended bit. -/
theorem finFunctionFinEquiv_cons_val {A B : ℕ} (hAB : A = B + 1)
    (a : Fin A → Fin 2) (b : Fin B → Fin 2) (c : Fin 2)
    (h0 : a ⟨0, by omega⟩ = c)
    (hs : ∀ j : Fin B, a ⟨j.val + 1, by omega⟩ = b j) :
    ((finFunctionFinEquiv a : Fin (2 ^ A)) : ℕ)
      = 2 * ((finFunctionFinEquiv b : Fin (2 ^ B)) : ℕ) + (c : ℕ) := by
  rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply]
  have hA : ∑ j : Fin A, ((a j : ℕ) * 2 ^ (j : ℕ))
      = ∑ j ∈ Finset.range A, (if h : j < A then ((a ⟨j, h⟩ : ℕ) * 2 ^ j) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => if h : j < A then ((a ⟨j, h⟩ : ℕ) * 2 ^ j) else 0) A]
    exact Finset.sum_congr rfl fun j _ => by rw [dif_pos j.isLt]
  have hB : ∑ j : Fin B, ((b j : ℕ) * 2 ^ (j : ℕ))
      = ∑ j ∈ Finset.range B, (if h : j < B then ((b ⟨j, h⟩ : ℕ) * 2 ^ j) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => if h : j < B then ((b ⟨j, h⟩ : ℕ) * 2 ^ j) else 0) B]
    exact Finset.sum_congr rfl fun j _ => by rw [dif_pos j.isLt]
  rw [hA, hB]
  subst hAB
  rw [Finset.sum_range_succ']
  have hterm : ∀ j ∈ Finset.range B,
      (if h : j + 1 < B + 1 then ((a ⟨j + 1, h⟩ : ℕ) * 2 ^ (j + 1)) else 0)
        = 2 * (if h : j < B then ((b ⟨j, h⟩ : ℕ) * 2 ^ j) else 0) := by
    intro j hj
    have hjB : j < B := Finset.mem_range.mp hj
    rw [dif_pos (by omega), dif_pos hjB]
    have hab : a ⟨j + 1, by omega⟩ = b ⟨j, hjB⟩ := hs ⟨j, hjB⟩
    rw [hab]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, dif_pos (by omega), h0]
  simp

/-- Evaluating a schoolbook product. -/
theorem raw_eval_mul (x : F) (p r : CPolynomial.Raw F) :
    (CPolynomial.Raw.mul p r).eval x = p.eval x * r.eval x := by
  show (p * r).eval x = _
  rw [← CPolynomial.Raw.eval_toPoly_eq_eval, CPolynomial.Raw.toPoly_mul,
    Polynomial.eval_mul, CPolynomial.Raw.eval_toPoly_eq_eval,
    CPolynomial.Raw.eval_toPoly_eq_eval]

/-- Evaluating a scalar multiple. -/
theorem raw_eval_smul (x c : F) (p : CPolynomial.Raw F) :
    (CPolynomial.Raw.smul c p).eval x = c * p.eval x := by
  have hsm : (CPolynomial.Raw.smul c p).toPoly = c • p.toPoly := by
    refine Polynomial.ext fun k => ?_
    rw [Polynomial.coeff_smul, CPolynomial.Raw.coeff_toPoly, CPolynomial.Raw.coeff_toPoly]
    exact CPolynomial.Raw.smul_coeff c p k
  rw [← CPolynomial.Raw.eval_toPoly_eq_eval, hsm,
    Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C,
    CPolynomial.Raw.eval_toPoly_eq_eval]

/-- `degreeLE` is monotone in the bound. -/
theorem degreeLE_mono' {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) {p : CPolynomial F}
    (hp : p ∈ CPolynomial.degreeLE (R := F) (d₁ : ℕ)) :
    p ∈ CPolynomial.degreeLE (R := F) (d₂ : ℕ) := by
  rw [CPolynomial.degreeLE_toPoly, Polynomial.mem_degreeLE] at hp ⊢
  exact le_trans hp (by exact_mod_cast h)

/-- Reading a table at two indices of equal value gives the same entry, whatever the two
arities recorded in the types. -/
theorem tableFn_congr {a b : ℕ} (t : alloc.vec.Vec cpoly.field.Ext4)
    (u : Fin (2 ^ a)) (v : Fin (2 ^ b)) (h : u.val = v.val) :
    tableFn (m := a) t u = tableFn (m := b) t v := by
  rw [tableFn_apply, tableFn_apply, h]

/-- Overwriting the last challenge of a cube point. -/
theorem hypercubePoint_snoc_update {M i : ℕ} (hi : i < M + 1) (cs : Fin i → F) (x v : F)
    (z : Fin (M + 1 - (i + 1)) → Fin 2) :
    Function.update (InnerOuter.hypercubePoint (M + 1) (i + 1) (Fin.snoc cs x) z) ⟨i, hi⟩ v =
      InnerOuter.hypercubePoint (M + 1) (i + 1) (Fin.snoc cs v) z := by
  funext j
  by_cases hj : j = ⟨i, hi⟩
  · subst hj
    rw [Function.update_self]
    simp only [InnerOuter.hypercubePoint]
    rw [dif_pos (by omega)]
    have : (⟨i, by omega⟩ : Fin (i + 1)) = Fin.last i := rfl
    rw [this, Fin.snoc_last]
  · rw [Function.update_of_ne hj]
    simp only [InnerOuter.hypercubePoint]
    by_cases h1 : j.val < i + 1
    · rw [dif_pos h1, dif_pos h1]
      have hjv : j.val < i := by
        rcases Nat.lt_or_ge j.val i with h | h
        · exact h
        · exact absurd (Fin.ext (by omega : j.val = i)) hj
      have : (⟨j.val, h1⟩ : Fin (i + 1)) = Fin.castSucc ⟨j.val, hjv⟩ := rfl
      rw [this, Fin.snoc_castSucc, Fin.snoc_castSucc]
    · rw [dif_neg h1, dif_neg h1]

/-- Prepending a bit to a cube tail is extending the challenge prefix by that bit. -/
theorem hypercubePoint_cons_eq {M i k : ℕ} (hi : i < M + 1) (hk : M + 1 - (i + 1) = k)
    (cs : Fin i → F) (b : Fin 2) (z : Fin (M + 1 - (i + 1)) → Fin 2)
    (zb : Fin (M + 1 - i) → Fin 2)
    (hz0 : zb ⟨0, by omega⟩ = b)
    (hzs : ∀ j : Fin k, zb ⟨j.val + 1, by omega⟩ = z (Fin.cast hk.symm j)) :
    InnerOuter.hypercubePoint (M + 1) i cs zb =
      InnerOuter.hypercubePoint (M + 1) (i + 1) (Fin.snoc cs ((b.val : ℕ) : F)) z := by
  funext j
  simp only [InnerOuter.hypercubePoint]
  by_cases h1 : j.val < i
  · rw [dif_pos h1, dif_pos (by omega : j.val < i + 1)]
    have : (⟨j.val, by omega⟩ : Fin (i + 1)) = Fin.castSucc ⟨j.val, h1⟩ := rfl
    rw [this, Fin.snoc_castSucc]
  · rw [dif_neg h1]
    by_cases h2 : j.val = i
    · rw [dif_pos (by omega : j.val < i + 1)]
      have hlast : (⟨j.val, by omega⟩ : Fin (i + 1)) = Fin.last i := Fin.ext (by simp; omega)
      rw [hlast, Fin.snoc_last]
      have : (⟨j.val - i, by omega⟩ : Fin (M + 1 - i)) = ⟨0, by omega⟩ :=
        Fin.ext (show j.val - i = 0 from by omega)
      rw [this, hz0]
    · rw [dif_neg (by omega : ¬ j.val < i + 1)]
      have hjk : j.val - (i + 1) < k := by omega
      have h3 : (⟨j.val - i, by omega⟩ : Fin (M + 1 - i)) = ⟨(j.val - (i+1)) + 1, by omega⟩ :=
        Fin.ext (show j.val - i = (j.val - (i+1)) + 1 from by omega)
      rw [h3, hzs ⟨j.val - (i+1), hjk⟩]
      rfl

/-- The Lagrange weight at a cube point, as a product over the bits. -/
theorem lagrangeBasis_get_cube {k : ℕ} (v : Vector F k) (z : Fin k → Fin 2) :
    (CMlPolynomialEval.lagrangeBasis v).get (finFunctionFinEquiv z)
      = ∏ j : Fin k, (if z j = 1 then v.get j else 1 - v.get j) := by
  rw [Hachi.lagrangeBasis_get]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hsym : finFunctionFinEquiv.symm (finFunctionFinEquiv z : Fin (2 ^ k)) = z :=
    Equiv.symm_apply_apply _ _
  have hbit : ((BitVec.ofFin (finFunctionFinEquiv z : Fin (2 ^ k))).getLsb j = true)
      ↔ z j = 1 := by
    rw [← hsym]
    rw [cube_coord_eq_one_iff ((finFunctionFinEquiv z : Fin (2 ^ k)) : ℕ)
      (finFunctionFinEquiv z).isLt j]
    simp [BitVec.getLsb_eq_getElem]
  exact if_congr hbit rfl rfl


/-- One fold step of a tabulated multilinear extension. -/
theorem fold_tableFn_eq_mle {M i k : ℕ} (him : i < M + 1) (hk : M + 1 - (i + 1) = k)
    (t : alloc.vec.Vec cpoly.field.Ext4) (evals : (Fin (M + 1) → Fin 2) → F)
    (cs : Fin i → F) (x : F)
    (hv : ∀ y : Fin (M + 1 - i) → Fin 2, tableFn (m := M + 1 - i) t (finFunctionFinEquiv y)
        = (InnerOuter.cMultilinearExtension (M + 1) evals).eval
            (InnerOuter.hypercubePoint (M + 1) i cs y))
    (z : Fin (M + 1 - (i + 1)) → Fin 2) :
    fold (tableFn (m := k + 1) t) x
        (finFunctionFinEquiv (fun j : Fin k => z (Fin.cast hk.symm j)))
      = (InnerOuter.cMultilinearExtension (M + 1) evals).eval
          (InnerOuter.hypercubePoint (M + 1) (i + 1) (Fin.snoc cs x) z) := by
  have hk1 : M + 1 - i = k + 1 := by omega
  set Y : Fin (2 ^ k) := finFunctionFinEquiv (fun j : Fin k => z (Fin.cast hk.symm j)) with hY
  have key : ∀ b : Fin 2, ∀ idx : Fin (2 ^ (k + 1)), idx.val = 2 * Y.val + b.val →
      tableFn (m := k + 1) t idx
        = (InnerOuter.cMultilinearExtension (M + 1) evals).eval
            (InnerOuter.hypercubePoint (M + 1) (i + 1) (Fin.snoc cs ((b.val : ℕ) : F)) z) := by
    intro b idx hidx
    set zb : Fin (M + 1 - i) → Fin 2 :=
      fun j => if h : j.val = 0 then b
        else z (Fin.cast hk.symm ⟨j.val - 1, by have := j.isLt; omega⟩) with hzb
    have hz0 : zb ⟨0, by omega⟩ = b := by rw [hzb]; simp
    have hzs : ∀ j : Fin k, zb ⟨j.val + 1, by omega⟩ = z (Fin.cast hk.symm j) := by
      intro j
      rw [hzb]
      dsimp only
      rw [dif_neg (by omega)]
      congr 1
    have hval : ((finFunctionFinEquiv zb : Fin (2 ^ (M + 1 - i))) : ℕ) = 2 * Y.val + b.val := by
      rw [hY]
      exact finFunctionFinEquiv_cons_val hk1 zb (fun j : Fin k => z (Fin.cast hk.symm j)) b
        hz0 hzs
    rw [tableFn_congr (a := k + 1) (b := M + 1 - i) t idx (finFunctionFinEquiv zb)
      (by rw [hidx, hval]), hv zb,
      hypercubePoint_cons_eq him hk cs b z zb hz0 hzs]
  have h0 := key 0 (lo Y) (by simp [lo])
  have h1 := key 1 (hi Y) (by simp [hi])
  rw [fold, h0, h1]
  have hpt : (InnerOuter.hypercubePoint (M + 1) (i + 1) (Fin.snoc cs x) z) ⟨i, him⟩ = x := by
    simp only [InnerOuter.hypercubePoint]
    rw [dif_pos (by omega : i < i + 1)]
    have : (⟨i, by omega⟩ : Fin (i + 1)) = Fin.last i := rfl
    rw [this, Fin.snoc_last]
  have hup := cMLE_eval_update (m := M + 1) evals
    (InnerOuter.hypercubePoint (M + 1) (i + 1) (Fin.snoc cs x) z) ⟨i, him⟩
  rw [hpt, hypercubePoint_snoc_update him cs x 0 z,
    hypercubePoint_snoc_update him cs x 1 z] at hup
  rw [hup]
  norm_num

set_option maxHeartbeats 1000000 in
/-- The equality kernel at a cube point splits into prefix, free coordinate and suffix. -/
theorem eqProd_hypercubePoint_split {M i : ℕ} (him : i < M + 1) (tau : Fin (M + 1) → F)
    (cs : Fin i → F) (x : F) (z : Fin (M + 1 - (i + 1)) → Fin 2) :
    eqProd tau (InnerOuter.hypercubePoint (M + 1) (i + 1) (Fin.snoc cs x) z)
      = eqProd (fun j : Fin i => tau (Fin.castLE (by omega) j)) cs
        * ((1 - tau ⟨i, him⟩) * (1 - x) + tau ⟨i, him⟩ * x)
        * ∏ j : Fin (M + 1 - (i + 1)),
            (if z j = 1 then tau ⟨i + 1 + j.val, by have := j.isLt; omega⟩
              else 1 - tau ⟨i + 1 + j.val, by have := j.isLt; omega⟩) := by
  set a := InnerOuter.hypercubePoint (M + 1) (i + 1) (Fin.snoc cs x) z with ha
  have halt : ∀ j : Fin i, a ⟨j.val, by have := j.isLt; omega⟩ = cs j := by
    intro j
    have hj := j.isLt
    rw [ha]
    simp only [InnerOuter.hypercubePoint]
    rw [dif_pos (show j.val < i + 1 by omega)]
    have h3 : (⟨j.val, show j.val < i + 1 by omega⟩ : Fin (i + 1)) = Fin.castSucc j := rfl
    rw [h3, Fin.snoc_castSucc]
  have haeq : a ⟨i, him⟩ = x := by
    rw [ha]
    simp only [InnerOuter.hypercubePoint]
    rw [dif_pos (show i < i + 1 by omega)]
    have : (⟨i, by omega⟩ : Fin (i + 1)) = Fin.last i := rfl
    rw [this, Fin.snoc_last]
  have hagt : ∀ v : Fin (M + 1 - (i + 1)), a ⟨i + 1 + v.val, by have := v.isLt; omega⟩
      = ((z v).val : F) := by
    intro v
    have hv := v.isLt
    rw [ha]
    simp only [InnerOuter.hypercubePoint]
    rw [dif_neg (show ¬ (i + 1 + v.val < i + 1) by omega)]
    have hzz : z ⟨i + 1 + v.val - (i + 1), by omega⟩ = z v := by
      congr 1
      exact Fin.ext (show i + 1 + v.val - (i + 1) = v.val from by omega)
    rw [hzz]
  set g : ℕ → F := fun j => if h : j < M + 1 then
    tau ⟨j, h⟩ * a ⟨j, h⟩ + (1 - tau ⟨j, h⟩) * (1 - a ⟨j, h⟩) else 1 with hg
  have hfull : eqProd tau a = ∏ j ∈ Finset.range (M + 1), g j := by
    rw [eqProd, ← Fin.prod_univ_eq_prod_range g (M + 1)]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hg]
    dsimp only
    rw [dif_pos j.isLt, Fin.eta]
  have hA : ∏ j ∈ Finset.range i, g j
      = eqProd (fun j : Fin i => tau (Fin.castLE (by omega) j)) cs := by
    rw [eqProd, ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hj := j.isLt
    rw [hg]
    dsimp only
    rw [dif_pos (show j.val < M + 1 by omega), halt j]
    have h4 : (⟨j.val, show j.val < M + 1 by omega⟩ : Fin (M + 1))
        = Fin.castLE (by omega) j := Fin.ext rfl
    rw [h4]
  have hB : ∏ y ∈ Finset.range 1, g (i + y)
      = (1 - tau ⟨i, him⟩) * (1 - x) + tau ⟨i, him⟩ * x := by
    rw [Finset.prod_range_one, hg]
    dsimp only
    rw [dif_pos (show i + 0 < M + 1 by omega)]
    have h1 : (⟨i + 0, show i + 0 < M + 1 by omega⟩ : Fin (M + 1)) = ⟨i, him⟩ :=
      Fin.ext (show i + 0 = i from by omega)
    rw [h1, haeq]
    ring
  have hC : ∏ v ∈ Finset.range (M + 1 - (i + 1)), g (i + (1 + v))
      = ∏ j : Fin (M + 1 - (i + 1)),
          (if z j = 1 then tau ⟨i + 1 + j.val, by have := j.isLt; omega⟩
            else 1 - tau ⟨i + 1 + j.val, by have := j.isLt; omega⟩) := by
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hv := v.isLt
    rw [hg]
    dsimp only
    rw [dif_pos (show i + (1 + v.val) < M + 1 by omega)]
    have h2 : (⟨i + (1 + v.val), show i + (1 + v.val) < M + 1 by omega⟩ : Fin (M + 1))
        = ⟨i + 1 + v.val, by omega⟩ :=
      Fin.ext (show i + (1 + v.val) = i + 1 + v.val from by omega)
    rw [h2, hagt v]
    by_cases hz : z v = 1
    · rw [if_pos hz, hz]
      push_cast
      ring
    · have hne : (z v).val ≠ 1 := fun hcon => hz (Fin.ext hcon)
      have hz2 := (z v).isLt
      have hz0 : z v = 0 := Fin.ext (by omega)
      rw [if_neg hz, hz0]
      push_cast
      ring
  have hsplit : M + 1 = i + (1 + (M + 1 - (i + 1))) := by omega
  rw [hfull]
  rw [show (Finset.range (M + 1)) = Finset.range (i + (1 + (M + 1 - (i + 1)))) from
    by rw [← hsplit]]
  rw [Finset.prod_range_add g i (1 + (M + 1 - (i + 1)))]
  rw [Finset.prod_range_add (fun y => g (i + y)) 1 (M + 1 - (i + 1))]
  rw [← mul_assoc, hA, hB]
  rw [show (∏ v ∈ Finset.range (M + 1 - (i + 1)), g (i + (1 + v)))
      = ∏ v ∈ Finset.range (M + 1 - (i + 1)), g (i + (1 + v)) from rfl]
  rw [hC]

/-! ## The honest prover's round message -/

set_option maxHeartbeats 1000000 in
/-- `honest_compute_g` computes `honestComputeG` (`Completeness.lean:74`), the
one item that mirrors a summand's `computableRoundPoly` **whole**: it applies
the kernel's prefix and free factor that `round_poly_zero` leaves out, so
`g_zero` has degree exactly `2b` and `g_alpha` degree `2`.

The two tables are the witness MLE and the public α MLE **folded through the
`i` challenges drawn so far**, which is what `hwv`/`hav` say: entry `y` is the
MLE at `hypercubePoint m₀ i cs y` (`Constraints.lean:852`) — the first `i`
coordinates are the challenges, the rest the bits of `y`, little-endian as
`finFunctionFinEquiv` has them. Maintaining that is `round_loop`'s job. Stated
at arity `M + 1` because `honestComputeG` is.

For the prover: the equality `toUni g_zero = sg.1.1` is an equality of
`CPolynomial`s that agree as *functions* on `F` (`computableRoundPoly_eval`,
`RoundPoly.lean:316`, against `rangeSumZero · free · prefix`); both sides have
degree `≤ 33` and `|F| = q⁴`, so it goes through "equal at more than `deg`
points", **not** `Polynomial.funext`, which needs an infinite domain.

No value bound: every read is
inside a length the relations fix, `i + 1 ≤ m₀ ≤ Usize.max`, the suffix
table's `2^(m₀ − i − 1)` pushes are bounded by `w_tab`'s own `Vec` bound
(`2^(m₀ − i)` entries), and the two polynomial products have `33 + 2`
coefficients. -/
theorem honest_compute_g_spec {n μ M m₁ dRows : ℕ} (stmt : sumcheck.RoundStatement)
    (w_tab a_tab : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize)
    (ss : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ (M + 1) m₁ i.val)
    (sw : InnerOuter.LiftedWitness Φ μ n)
    (hs : RepRoundStmt (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := i.val) (dRows := dRows)
      stmt ss)
    (hi : i.val < M + 1)
    (hw : WfEvals (M + 1 - i.val) w_tab) (ha : WfEvals (M + 1 - i.val) a_tab)
    (hwv : ∀ y : Fin (M + 1 - i.val) → Fin 2,
      tableFn (m := M + 1 - i.val) w_tab (finFunctionFinEquiv y) =
        InnerOuter.wTableMleEval Φ (M + 1) phiF 16 sw
          (InnerOuter.hypercubePoint (M + 1) i.val ss.challenges y))
    (hav : ∀ y : Fin (M + 1 - i.val) → Fin 2,
      tableFn (m := M + 1 - i.val) a_tab (finFunctionFinEquiv y) =
        (InnerOuter.cMultilinearExtension (M + 1)
          (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)).eval
          (InnerOuter.hypercubePoint (M + 1) i.val ss.challenges y)) :
    sumcheck.honest_compute_g stmt w_tab a_tab i
      ⦃ out => RepRoundMsg out
        (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF i.val hi ss sw) ⦄ := by
  obtain ⟨hzc, hWc, hRt0, hRta, hc, ht0, hta⟩ := hs
  obtain ⟨hr, hWt, hWa, hW0, hW1, htv, hav', h0v, h1v⟩ := hzc
  obtain ⟨h0len, h0red⟩ := hW0
  have hM1 : M + 1 ≤ Usize.max := by
    have := stmt.zc.tau0.property
    omega
  have hkk : M + 1 - i.val = (M + 1 - i.val - 1) + 1 := by omega
  have hw' : WfEvals ((M + 1 - i.val - 1) + 1) w_tab := by rwa [hkk] at hw
  have ha' : WfEvals ((M + 1 - i.val - 1) + 1) a_tab := by rwa [hkk] at ha
  have hcube : 2 ^ (M + 1 - i.val) ≤ Usize.max := by
    have hlen := hw.1
    have := w_tab.property
    omega
  simp only [sumcheck.honest_compute_g, sumcheck.RoundStatement.impl.zc,
    sumcheck.NestedZeroCheckStmt.impl.tau0, sumcheck.RoundStatement.impl.challenges, bind_tc_ok]
  step with eq_prefix_spec (m₀ := M + 1) (i := i.val) stmt.zc.tau0 stmt.challenges
    ⟨h0len, h0red⟩ hWc (by omega) as ⟨pref, hRpref, hprefv⟩
  step with eq_suffix_table_spec (m₀ := M + 1) stmt.zc.tau0 i ⟨h0len, h0red⟩ (by omega)
    (by
      have hmono : (2 : ℕ) ^ (M + 1 - i.val - 1) ≤ 2 ^ (M + 1 - i.val) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega)
      as ⟨suffix, hWsuf, hsufv⟩
  step with round_poly_zero_spec (k := M + 1 - i.val - 1) w_tab suffix hw' hWsuf
    as ⟨inner, hinlen, hinred, hinval⟩
  step as ⟨e, he⟩
  have hRe : Reduced e := he ▸ h0red _ (List.getElem_mem (by omega))
  step with eq_free_factor_spec e hRe as ⟨free, hfreelen, hfreered, hfreeval⟩
  step with uni_mul_spec inner free hinred hfreered
    (by rw [hinlen, hfreelen]; have := usize_max_ge; omega) as ⟨wf, hwfred, hwfraw, hwflen⟩
  step with uni_smul_spec pref wf hRpref hwfred as ⟨gz, hgzred, hgzraw⟩
  step with round_poly_alpha_spec (k := M + 1 - i.val - 1) w_tab a_tab hw' ha'
    as ⟨ga, hgalen, hgared, hgaval⟩
  have hwv2 : ∀ y : Fin (M + 1 - i.val) → Fin 2,
      tableFn (m := M + 1 - i.val) w_tab (finFunctionFinEquiv y)
        = (InnerOuter.cMultilinearExtension (M + 1)
            (InnerOuter.wTable Φ (M + 1) phiF 16 sw)).eval
            (InnerOuter.hypercubePoint (M + 1) i.val ss.challenges y) := by
    intro y
    rw [hwv y, InnerOuter.wTableMleEval_eq, InnerOuter.cMultilinearExtension_eval]
  have hfoldw : ∀ (x : F) (z : Fin (M + 1 - i.val - 1) → Fin 2),
      fold (tableFn (m := (M + 1 - i.val - 1) + 1) w_tab) x (finFunctionFinEquiv z)
        = InnerOuter.wTableMleEval Φ (M + 1) phiF 16 sw
            (InnerOuter.hypercubePoint (M + 1) (i.val + 1) (Fin.snoc ss.challenges x) z) := by
    intro x z
    have hstep := fold_tableFn_eq_mle (k := M + 1 - i.val - 1) hi rfl w_tab
      (InnerOuter.wTable Φ (M + 1) phiF 16 sw) ss.challenges x hwv2 z
    rw [show (fun j : Fin (M + 1 - i.val - 1) => z (Fin.cast rfl j)) = z from rfl] at hstep
    rw [hstep, InnerOuter.wTableMleEval_eq, InnerOuter.cMultilinearExtension_eval]
  have hfolda : ∀ (x : F) (z : Fin (M + 1 - i.val - 1) → Fin 2),
      fold (tableFn (m := (M + 1 - i.val - 1) + 1) a_tab) x (finFunctionFinEquiv z)
        = (InnerOuter.cMultilinearExtension (M + 1)
            (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)).eval
            (InnerOuter.hypercubePoint (M + 1) (i.val + 1) (Fin.snoc ss.challenges x) z) := by
    intro x z
    have hstep := fold_tableFn_eq_mle (k := M + 1 - i.val - 1) hi rfl a_tab
      (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)
      ss.challenges x hav z
    rw [show (fun j : Fin (M + 1 - i.val - 1) => z (Fin.cast rfl j)) = z from rfl] at hstep
    exact hstep
  have hre : ∀ f : Fin (2 ^ (M + 1 - i.val - 1)) → F,
      ∑ Y : Fin (2 ^ (M + 1 - i.val - 1)), f Y
        = ∑ z : Fin (M + 1 - i.val - 1) → Fin 2, f (finFunctionFinEquiv z) :=
    fun f => (Fintype.sum_equiv finFunctionFinEquiv _ f (fun _ => rfl)).symm
  have htau : ∀ (j : ℕ) (h : j < M + 1),
      ss.zc.τ₀ ⟨j, h⟩ = toExt (stmt.zc.tau0.val.getD j cpoly.field.Ext4.ZERO) := by
    intro j h
    rw [← h0v]
    rfl
  have hev : toExt e = ss.zc.τ₀ ⟨i.val, hi⟩ := by
    rw [htau i.val hi, he, List.getD_eq_getElem _ _ (by omega)]
  have hpref : toExt pref
      = eqProd (fun j : Fin i.val => ss.zc.τ₀ (Fin.castLE (by omega) j)) ss.challenges := by
    rw [hprefv, hc, h0v]
  have hsuf : ∀ z : Fin (M + 1 - i.val - 1) → Fin 2,
      tableFn (m := M + 1 - i.val - 1) suffix (finFunctionFinEquiv z)
        = ∏ j : Fin (M + 1 - (i.val + 1)),
            (if z j = 1 then ss.zc.τ₀ ⟨i.val + 1 + j.val, by have := j.isLt; omega⟩
              else 1 - ss.zc.τ₀ ⟨i.val + 1 + j.val, by have := j.isLt; omega⟩) := by
    intro z
    rw [tableFn, hsufv, lagrangeBasis_get_cube]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Vector.get_ofFn, htau (i.val + 1 + j.val) (by have := j.isLt; omega)]
    rfl
  refine ⟨hgzred, hgared, ?_, ?_⟩
  · have hgzlen : gz.val.length ≤ 35 := by
      have h1 : (toRaw gz).size = (CPolynomial.Raw.smul (toExt pref) (toRaw wf)).size := by
        rw [hgzraw]
      rw [toRaw_size] at h1
      have h2 : (CPolynomial.Raw.smul (toExt pref) (toRaw wf)).size = (toRaw wf).size := by
        simp [CPolynomial.Raw.smul]
      rw [h2, toRaw_size] at h1
      rw [h1, hinlen, hfreelen] at *
      omega
    refine cpoly_eq_of_eval_eq (d := 34) (by norm_num) _ _
      (toUni_mem_degreeLE gz 34 (by omega))
      (degreeLE_mono' (by simp [InnerOuter.roundDegZero])
        (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF i.val hi ss sw).1.2) ?_
    intro x
    rw [toUni_eval, hgzraw, raw_eval_smul, hwfraw, raw_eval_mul, ← toUni_eval inner,
      ← toUni_eval free, hinval x, hfreeval x]
    show _ = CPolynomial.eval x
      (InnerOuter.computableRoundPoly
        (InnerOuter.sumcheckPolyZero Φ (M + 1) phiF 16 ss.zc.τ₀ sw) ⟨i.val, hi⟩ ss.challenges)
    have hHS : InnerOuter.hypercubeSum (M + 1)
        (InnerOuter.sumcheckPolyZero Φ (M + 1) phiF 16 ss.zc.τ₀ sw) (i.val + 1)
        (Fin.snoc ss.challenges x)
        = ∑ z : Fin (M + 1 - i.val - 1) → Fin 2,
            (InnerOuter.sumcheckPolyZero Φ (M + 1) phiF 16 ss.zc.τ₀ sw).eval
              (InnerOuter.hypercubePoint (M + 1) (i.val + 1) (Fin.snoc ss.challenges x) z) := rfl
    rw [InnerOuter.computableRoundPoly_eval, hHS]
    have hterm : ∀ z : Fin (M + 1 - i.val - 1) → Fin 2,
        (InnerOuter.sumcheckPolyZero Φ (M + 1) phiF 16 ss.zc.τ₀ sw).eval
            (InnerOuter.hypercubePoint (M + 1) (i.val + 1) (Fin.snoc ss.challenges x) z)
          = toExt pref * (tableFn (m := M + 1 - i.val - 1) suffix (finFunctionFinEquiv z)
              * InnerOuter.rangeProduct 16
                (fold (tableFn (m := (M + 1 - i.val - 1) + 1) w_tab) x (finFunctionFinEquiv z)))
            * ((1 - toExt e) * (1 - x) + toExt e * x) := by
      intro z
      rw [InnerOuter.eval_sumcheckPolyZero, cEqualityPolynomial_eval_eq_eqProd,
        eqProd_hypercubePoint_split hi ss.zc.τ₀ ss.challenges x z, hfoldw x z, hsuf z,
        hpref, hev]
      ring
    rw [Finset.sum_congr rfl (fun z _ => hterm z), rangeSumZero, hre,
      ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  · refine cpoly_eq_of_eval_eq (d := 2) (by norm_num) _ _
      (toUni_mem_degreeLE ga 2 (by omega))
      (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF i.val hi ss sw).2.2 ?_
    intro x
    rw [hgaval x]
    show linSumAlpha _ _ x = CPolynomial.eval x
      (InnerOuter.computableRoundPoly
        (InnerOuter.sumcheckPolyAlpha Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα sw)
        ⟨i.val, hi⟩ ss.challenges)
    have hHS : InnerOuter.hypercubeSum (M + 1)
        (InnerOuter.sumcheckPolyAlpha Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα sw)
        (i.val + 1) (Fin.snoc ss.challenges x)
        = ∑ z : Fin (M + 1 - i.val - 1) → Fin 2,
            (InnerOuter.sumcheckPolyAlpha Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα sw).eval
              (InnerOuter.hypercubePoint (M + 1) (i.val + 1) (Fin.snoc ss.challenges x) z) := rfl
    rw [InnerOuter.computableRoundPoly_eval, hHS, linSumAlpha, hre]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [InnerOuter.eval_sumcheckPolyAlpha, hfoldw x z, hfolda x z]

/-! ## The verifier's two decisions and its state map -/

/-- `round_check` decides `roundCheck` (`Rounds.lean:100`): an equality of
decisions, not an implication — both rejection paths are the content. -/
theorem round_check_spec {n μ m₀ m₁ i dRows : ℕ} (stmt : sumcheck.RoundStatement)
    (g : sumcheck.RoundMsg)
    (ss : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ m₀ m₁ i)
    (sg : InnerOuter.RoundMsg F 16)
    (hs : RepRoundStmt (n := n) (μ := μ) (m₀ := m₀) (m₁ := m₁) (i := i) (dRows := dRows) stmt ss)
    (hg : RepRoundMsg g sg) :
    sumcheck.round_check stmt g ⦃ b => b = InnerOuter.roundCheck Φ m₀ m₁ 16 ss sg ⦄ := by
  obtain ⟨-, -, hRt0, hRta, -, ht0, hta⟩ := hs
  obtain ⟨hg0red, hgared, hg0, hga⟩ := hg
  have hRZ : Reduced cpoly.field.Ext4.ZERO := reduced_ZERO
  have hR1 : Reduced cpoly.field.Ext4.ONE := reduced_ONE
  rw [sumcheck.round_check, sumcheck.RoundMsg.impl.g_zero, sumcheck.RoundMsg.impl.g_alpha,
    sumcheck.RoundStatement.impl.target_zero, sumcheck.RoundStatement.impl.target_alpha]
  step with uni_eval_spec g.g_zero cpoly.field.Ext4.ZERO hg0red hRZ as ⟨e, hRe, he⟩
  step with uni_eval_spec g.g_zero cpoly.field.Ext4.ONE hg0red hR1 as ⟨e1, hRe1, he1⟩
  step as ⟨zs, hRzs, hzs⟩
  step with uni_eval_spec g.g_alpha cpoly.field.Ext4.ZERO hgared hRZ as ⟨e2, hRe2, he2⟩
  step with uni_eval_spec g.g_alpha cpoly.field.Ext4.ONE hgared hR1 as ⟨e3, hRe3, he3⟩
  step as ⟨asum, hRasum, hasum⟩
  have hzsv : toExt zs = CPolynomial.eval 0 sg.1.1 + CPolynomial.eval 1 sg.1.1 := by
    rw [hzs, he, he1, ← hg0, toUni_eval, toUni_eval, toExt_ZERO, toExt_ONE]
  have hasumv : toExt asum = CPolynomial.eval 0 sg.2.1 + CPolynomial.eval 1 sg.2.1 := by
    rw [hasum, he2, he3, ← hga, toUni_eval, toUni_eval, toExt_ZERO, toExt_ONE]
  step with ext_eq_spec zs stmt.target_zero hRzs hRt0 as ⟨b, hb⟩
  rw [InnerOuter.roundCheck]
  by_cases hbt : b = true
  · rw [if_pos hbt]
    have hfirst : (CPolynomial.eval 0 sg.1.1 + CPolynomial.eval 1 sg.1.1 == ss.target₀) = true := by
      rw [beq_iff_eq, ← hzsv, ← ht0]
      exact hb.mp hbt
    apply spec_mono (ext_eq_spec asum stmt.target_alpha hRasum hRta)
    intro r hr
    rw [hfirst, Bool.true_and]
    cases r with
    | true =>
      have hq : toExt asum = toExt stmt.target_alpha := hr.mp rfl
      rw [← hasumv, ← hta, hq]
      exact (beq_self_eq_true (toExt stmt.target_alpha)).symm
    | false =>
      have hne : toExt asum ≠ toExt stmt.target_alpha := by
        intro hcon; simpa using hr.mpr hcon
      rw [← hasumv, ← hta]
      symm
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact hne
  · have hbf : b = false := by cases b <;> simp_all
    rw [if_neg (by simp [hbf]), WP.spec_ok]
    have hne : toExt zs ≠ toExt stmt.target_zero := by
      intro hcon
      rw [hb.mpr hcon] at hbf
      simp at hbf
    have hfirst : (CPolynomial.eval 0 sg.1.1 + CPolynomial.eval 1 sg.1.1 == ss.target₀) = false := by
      rw [beq_eq_false_iff_ne, ne_eq, ← hzsv, ← ht0]
      exact fun hcon => hne hcon
    rw [hfirst, Bool.false_and]

/-- `round_out` computes `roundOut` (`Rounds.lean:109`): the challenge is
appended and both targets move to `g(a)`. The one push not bounded by an
input's length is the erasure of `Fin.snoc`, hence `hpush`. -/
theorem round_out_spec {n μ m₀ m₁ i dRows : ℕ} (stmt : sumcheck.RoundStatement)
    (g : sumcheck.RoundMsg) (a : cpoly.field.Ext4)
    (ss : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ m₀ m₁ i)
    (sg : InnerOuter.RoundMsg F 16)
    (hs : RepRoundStmt (n := n) (μ := μ) (m₀ := m₀) (m₁ := m₁) (i := i) (dRows := dRows) stmt ss)
    (hg : RepRoundMsg g sg) (ha : Reduced a) (hpush : i < Usize.max) :
    sumcheck.round_out stmt g a
      ⦃ out => RepRoundStmt (n := n) (μ := μ) (m₀ := m₀) (m₁ := m₁) (i := i + 1) (dRows := dRows)
        out (InnerOuter.roundOut Φ m₀ m₁ 16 ss sg (toExt a)) ⦄ := by
  obtain ⟨hzc, hWc, hRt0, hRta, hc, ht0, hta⟩ := hs
  obtain ⟨hg0red, hgared, hg0, hga⟩ := hg
  obtain ⟨hclen, hcred⟩ := hWc
  rw [sumcheck.round_out, sumcheck.RoundMsg.impl.g_zero, sumcheck.RoundMsg.impl.g_alpha]
  step with uni_eval_spec g.g_zero a hg0red ha as ⟨t0, hRt0', ht0'⟩
  step with uni_eval_spec g.g_alpha a hgared ha as ⟨ta', hRta', hta''⟩
  have hbound : stmt.challenges.val.length < Usize.max := by rw [hclen]; exact hpush
  step as ⟨chs, hchs⟩
  refine ⟨hzc, ⟨?_, ?_⟩, hRt0', hRta', ?_, ?_, ?_⟩
  · rw [hchs, List.length_append, hclen]; simp
  · intro u hu
    rw [hchs] at hu
    rcases List.mem_append.mp hu with h | h
    · exact hcred u h
    · rw [List.mem_singleton.mp h]; exact ha
  · funext j
    rw [InnerOuter.roundOut]
    dsimp only
    rcases Nat.lt_or_ge j.val i with hj | hj
    · rw [show (Fin.snoc ss.challenges (toExt a) : Fin (i + 1) → F) j
        = ss.challenges ⟨j.val, hj⟩ from by
          simp only [Fin.snoc]
          rw [dif_pos hj]
          rfl]
      rw [← hc]
      simp only [toPoint]
      rw [hchs, getD_append_lt _ _ _ (by rw [hclen]; exact hj)]
    · have hji : j.val = i := by omega
      have hsnoc : (Fin.snoc ss.challenges (toExt a) : Fin (i + 1) → F) j = toExt a := by
        have hjl : j = Fin.last i := Fin.ext (by simp only [Fin.val_last]; omega)
        rw [hjl, Fin.snoc_last]
      rw [hsnoc]
      simp only [toPoint]
      rw [hji, hchs, ← hclen, getD_append_eq]
  · rw [InnerOuter.roundOut]
    dsimp only
    rw [ht0', ← hg0, toUni_eval]
  · rw [InnerOuter.roundOut]
    dsimp only
    rw [hta'', ← hga, toUni_eval]

/-- Entry `t` of a represented Lagrange-form table. -/
theorem toEvals_get {m : ℕ} (tab : cpoly.multilinear.MultilinearEvals) (t : Fin (2 ^ m)) :
    (toEvals (m := m) tab).get t = toExt (tab.val.getD t.val cpoly.field.Ext4.ZERO) :=
  Vector.get_ofFn _ t

/-- The multilinear extension of a cube table, at an arbitrary point, written as
the flat-index sum the extracted dot product forms. -/
theorem cMultilinearExtension_eval_flat {m : ℕ} (evals : (Fin m → Fin 2) → F) (a : Fin m → F) :
    (InnerOuter.cMultilinearExtension m evals).eval a =
      ∑ t : Fin (2 ^ m), evals (finFunctionFinEquiv.symm t) *
        ∏ j : Fin m, (if (finFunctionFinEquiv.symm t) j = 1 then a j else 1 - a j) := by
  rw [InnerOuter.cMultilinearExtension_eval, InnerOuter.eval_MLE_eq_sum]
  exact (Equiv.sum_comp finFunctionFinEquiv.symm
    (fun x : Fin m → Fin 2 => evals x * ∏ j : Fin m, if x j = 1 then a j else 1 - a j)).symm

/-- `eq̃(p, q) = Σ_y eq̃(p, y) · eq̃(q, y)`: the kernel as a cube sum, which is
what `eq_tilde` computes (a Lagrange basis dotted against a Lagrange basis). -/
theorem eqProd_eq_flat_sum {m : ℕ} (p q : Fin m → F) :
    eqProd p q =
      ∑ t : Fin (2 ^ m),
        (∏ j : Fin m, if (finFunctionFinEquiv.symm t) j = 1 then p j else 1 - p j) *
          (∏ j : Fin m, if (finFunctionFinEquiv.symm t) j = 1 then q j else 1 - q j) := by
  rw [← cEqualityPolynomial_eval_eq_eqProd p q, InnerOuter.cEqualityPolynomial,
    cMultilinearExtension_eval_flat]

/-- `cpoly::multilinear::eq_tilde` computes the equality kernel at the two
represented points. -/
theorem eq_tilde_spec {m : ℕ} (w x : alloc.vec.Vec cpoly.field.Ext4)
    (hw : WfPoint m w) (hx : WfPoint m x) (hm : 2 ^ m ≤ Usize.max) :
    cpoly.multilinear.eq_tilde (alloc.vec.Vec.deref w) (alloc.vec.Vec.deref x)
      ⦃ out => Reduced out ∧
        toExt out = eqProd (toPoint (m := m) w) (toPoint (m := m) x) ⦄ := by
  rw [cpoly.multilinear.eq_tilde]
  step with cpoly_lagrange_basis_spec (m := m) w hw hm as ⟨bw, hbwlen, hbwred, hbwval⟩
  rw [cpoly.multilinear.MultilinearEvals.eval]
  step with cpoly_lagrange_basis_spec (m := m) x hx hm as ⟨bx, hbxlen, hbxred, hbxval⟩
  apply spec_mono (cpoly_dot_spec (k := 2 ^ m) (alloc.vec.Vec.deref bw)
    (alloc.vec.Vec.deref bx) (sliceReduced_deref hbwred) (sliceReduced_deref hbxred)
    (by simpa using hbwlen) (by simpa using hbxlen))
  rintro out ⟨hR, hout⟩
  refine ⟨hR, ?_⟩
  rw [hout, eqProd_eq_flat_sum,
    ← Fin.sum_univ_eq_sum_range (fun t =>
      toExt ((alloc.vec.Vec.deref bw).val.getD t cpoly.field.Ext4.ZERO) *
        toExt ((alloc.vec.Vec.deref bx).val.getD t cpoly.field.Ext4.ZERO)) (2 ^ m)]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [deref_val]
  rw [hbwval t.val t.isLt, hbxval t.val t.isLt,
    lagrangeBasis_get_eq_cube_prod w t.val t.isLt,
    lagrangeBasis_get_eq_cube_prod x t.val t.isLt]

set_option maxHeartbeats 1000000 in
/-- `final_check` decides `finalCheck` (`FinalEval.lean:99`) at round `m₀`: the
three conjuncts, the third the `u64` bound compare. `m₀` is read off `tau0`;
`2 ^ m₀ ≤ Usize.max` is `cube_size`'s and cpoly's `table_len` shift's; `hmax`
is `alpha_public_evals_spec`'s. The first check in the chain that can reject. -/
theorem final_check_spec {n μ m₀ m₁ dRows : ℕ} (stmt : sumcheck.RoundStatement)
    (y_prime : cpoly.field.Ext4) (bound : Std.U64)
    (ss : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ m₀ m₁ m₀)
    (hs : RepRoundStmt (n := n) (μ := μ) (m₀ := m₀) (m₁ := m₁) (i := m₀) (dRows := dRows) stmt ss)
    (hy : Reduced y_prime) (hm0 : 2 ^ m₀ ≤ Usize.max) (hmax : μ + n * 8 ≤ Usize.max) :
    sumcheck.final_check stmt y_prime bound
      ⦃ b => b = InnerOuter.finalCheck Φ m₀ m₁ bound.val 16 phiF ss (toExt y_prime) ⦄ := by
  obtain ⟨hzc, hWc, hRt0, hRta, hc, ht0, hta⟩ := hs
  obtain ⟨hr, hWt, hRalpha, hWtau0, hWtau1, hvt, hva, htau0, htau1⟩ := hzc
  have hm0v : (alloc.vec.Vec.len stmt.zc.tau0).val = m₀ := by simpa using hWtau0.1
  simp only [sumcheck.final_check, sumcheck.RoundStatement.impl.zc,
    sumcheck.NestedZeroCheckStmt.impl.tau0, sumcheck.RoundStatement.impl.challenges,
    sumcheck.NestedZeroCheckStmt.impl.rlin, sumcheck.NestedZeroCheckStmt.impl.alpha,
    sumcheck.NestedZeroCheckStmt.impl.tau1, sumcheck.RoundStatement.impl.target_zero,
    sumcheck.RoundStatement.impl.target_alpha, ringswitch.RlinStatement.impl.bound,
    cpoly.multilinear.MultilinearEvals.from_values, bind_tc_ok]
  set m0 : Std.Usize := alloc.vec.Vec.len stmt.zc.tau0 with hm0def
  clear_value m0
  subst hm0v
  step with eq_tilde_spec stmt.zc.tau0 stmt.challenges hWtau0 hWc hm0 as ⟨eqall, hReqall, heqall⟩
  step with alpha_public_table_spec (n := n) (μ := μ) (m₁ := m₁) stmt.zc.rlin ss.zc.rlin
    stmt.zc.alpha stmt.zc.tau1 m0 hr hRalpha hWtau1 hm0 hmax
    as ⟨table, hWtab, htabval⟩
  rw [cpoly.multilinear.MultilinearEvals.eval]
  step with cpoly_lagrange_basis_spec stmt.challenges hWc hm0 as ⟨basis, hblen, hbred, hbval⟩
  step with cpoly_dot_spec (k := 2 ^ m0.val)
    (alloc.vec.Vec.deref table) (alloc.vec.Vec.deref basis)
    (sliceReduced_deref hWtab.2) (sliceReduced_deref hbred)
    (by simpa using hWtab.1) (by simpa using hblen) as ⟨amle, hRamle, hamle⟩
  step with range_product_spec y_prime hy as ⟨rp, hRrp, hrp⟩
  step with ext_mul_spec eqall rp hReqall hRrp as ⟨prod0, hRprod0, hprod0⟩
  have hAval : toExt prod0 =
      (InnerOuter.cEqualityPolynomial m0.val ss.zc.τ₀).eval
        ss.challenges * InnerOuter.rangeProduct 16 (toExt y_prime) := by
    rw [hprod0, heqall, hrp, cEqualityPolynomial_eval_eq_eqProd, htau0, hc]
  have hBval : toExt amle =
      (InnerOuter.cMultilinearExtension m0.val
        (InnerOuter.alphaPublicEvals Φ m0.val m₁ phiF 16
          ss.zc.rlin ss.zc.α ss.zc.τα)).eval ss.challenges := by
    have htabget : ∀ t : Fin (2 ^ m0.val),
        toExt (table.val.getD t.val cpoly.field.Ext4.ZERO) =
          InnerOuter.alphaPublicEvals Φ m0.val m₁ phiF 16
            ss.zc.rlin ss.zc.α ss.zc.τα (finFunctionFinEquiv.symm t) := by
      intro t
      rw [← toEvals_get table t, htabval, Vector.get_ofFn, hva, htau1]
    rw [hamle, cMultilinearExtension_eval_flat,
      ← Fin.sum_univ_eq_sum_range (fun t =>
        toExt ((alloc.vec.Vec.deref table).val.getD t cpoly.field.Ext4.ZERO) *
          toExt ((alloc.vec.Vec.deref basis).val.getD t cpoly.field.Ext4.ZERO))
        (2 ^ m0.val)]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [deref_val]
    rw [htabget t, hbval t.val t.isLt,
      lagrangeBasis_get_eq_cube_prod stmt.challenges t.val t.isLt, hc]
  have hbnd : decide (bound ≤ stmt.zc.rlin.bound) =
      decide (bound.val ≤ ss.zc.rlin.bound) := by
    refine decide_eq_decide.mpr ?_
    rw [← hr.2.2.2.2]
    constructor <;> intro h <;> scalar_tac
  step with ext_eq_spec prod0 stmt.target_zero hRprod0 hRt0 as ⟨b, hb⟩
  rw [InnerOuter.finalCheck]
  by_cases hbt : b = true
  · rw [if_pos hbt]
    have hfirst : ((InnerOuter.cEqualityPolynomial
        m0.val ss.zc.τ₀).eval ss.challenges *
          InnerOuter.rangeProduct 16 (toExt y_prime) == ss.target₀) = true := by
      rw [beq_iff_eq, ← hAval, ← ht0]
      exact hb.mp hbt
    step with ext_mul_spec y_prime amle hy hRamle as ⟨prod1, hRprod1, hprod1⟩
    have hBmul : toExt prod1 = toExt y_prime *
        (InnerOuter.cMultilinearExtension m0.val
          (InnerOuter.alphaPublicEvals Φ m0.val m₁ phiF 16
            ss.zc.rlin ss.zc.α ss.zc.τα)).eval ss.challenges := by
      rw [hprod1, hBval]
    step with ext_eq_spec prod1 stmt.target_alpha hRprod1 hRta as ⟨b1, hb1⟩
    by_cases hb1t : b1 = true
    · rw [if_pos hb1t, WP.spec_ok]
      have hsecond : (toExt y_prime *
          (InnerOuter.cMultilinearExtension m0.val
            (InnerOuter.alphaPublicEvals Φ m0.val m₁ phiF 16
              ss.zc.rlin ss.zc.α ss.zc.τα)).eval ss.challenges == ss.targetα) = true := by
        rw [beq_iff_eq, ← hBmul, ← hta]
        exact hb1.mp hb1t
      rw [hfirst, hsecond, Bool.true_and, Bool.true_and]
      exact hbnd
    · have hb1f : b1 = false := by cases b1 <;> simp_all
      rw [if_neg (by simp [hb1f]), WP.spec_ok]
      have hne : toExt prod1 ≠ toExt stmt.target_alpha := fun hcon => hb1t (hb1.mpr hcon)
      have hsecond : (toExt y_prime *
          (InnerOuter.cMultilinearExtension m0.val
            (InnerOuter.alphaPublicEvals Φ m0.val m₁ phiF 16
              ss.zc.rlin ss.zc.α ss.zc.τα)).eval ss.challenges == ss.targetα) = false := by
        rw [beq_eq_false_iff_ne, ne_eq, ← hBmul, ← hta]
        exact hne
      rw [hsecond, Bool.and_false, Bool.false_and]
  · have hbf : b = false := by cases b <;> simp_all
    rw [if_neg (by simp [hbf]), WP.spec_ok]
    have hne : toExt prod0 ≠ toExt stmt.target_zero := fun hcon => hbt (hb.mpr hcon)
    have hfirst : ((InnerOuter.cEqualityPolynomial
        m0.val ss.zc.τ₀).eval ss.challenges *
          InnerOuter.rangeProduct 16 (toExt y_prime) == ss.target₀) = false := by
      rw [beq_eq_false_iff_ne, ne_eq, ← hAval, ← ht0]
      exact hne
    rw [hfirst, Bool.false_and, Bool.false_and]

/-! ## The honest prover's final value -/

/-- `honest_compute_y` is `w_table_mle_eval`, and is stated against
`wTableMleEval` rather than `honestComputeY` (`FinalEval.lean:246`), which
picks up `[SampleableType F]` from its section by accident. Same hypotheses as
`w_table_mle_eval_spec`. -/
theorem honest_compute_y_spec {μ n : ℕ} (w : ringswitch.LiftedWitness) (m0 : Std.Usize)
    (challenges : alloc.vec.Vec cpoly.field.Ext4) (sw : InnerOuter.LiftedWitness Φ μ n)
    (hw : RepLiftedWitness w sw) (hc : WfPoint m0.val challenges)
    (hm0 : 2 ^ m0.val ≤ Usize.max) (hmax : μ + n * 8 ≤ Usize.max) :
    sumcheck.honest_compute_y w m0 challenges
      ⦃ out => Reduced out ∧ toExt out =
        InnerOuter.wTableMleEval Φ m0.val phiF 16 sw (toPoint (m := m0.val) challenges) ⦄ := by
  rw [sumcheck.honest_compute_y]
  exact w_table_mle_eval_spec (μ := μ) (n := n) w sw m0 challenges hw hc hm0 hmax

/-! ## The bridge into the rounds -/

/-- `nested_to_round_statement` computes `nestedToRoundStatement`
(`Bridge.lean:49`): no challenges, the range target the literal `0`, the linear
target `zcTargetAlpha`. The asymmetry is the row's whole content. -/
theorem nested_to_round_statement_spec {n μ m₀ m₁ dRows : ℕ} (zc : sumcheck.NestedZeroCheckStmt)
    (ss : InnerOuter.NestedZeroCheckStatement Φ (PolyVec (Rq Φ) dRows) F n μ m₀ m₁)
    (hzc : RepNestedZC (n := n) (μ := μ) (m₀ := m₀) (m₁ := m₁) (dRows := dRows) zc ss) :
    sumcheck.nested_to_round_statement zc
      ⦃ out => RepRoundStmt (n := n) (μ := μ) (m₀ := m₀) (m₁ := m₁) (i := 0) (dRows := dRows)
        out (InnerOuter.nestedToRoundStatement Φ m₀ m₁ phiF ss) ⦄ := by
  obtain ⟨hr, hWt, hWa, hW0, hW1, ht, ha, h0, h1⟩ := hzc
  rw [sumcheck.nested_to_round_statement, sumcheck.NestedZeroCheckStmt.impl.rlin,
    sumcheck.NestedZeroCheckStmt.impl.alpha, sumcheck.NestedZeroCheckStmt.impl.tau1]
  have hspec := zc_target_alpha_spec (n := n) (μ := μ) (m₁ := m₁) zc.rlin ss.rlin zc.alpha zc.tau1
    hr hWa hW1
  step with hspec as ⟨ta, hRta, hta⟩
  apply RoundStatement_new_spec (n := n) (μ := μ) (m₀ := m₀) (m₁ := m₁) (i := 0) (dRows := dRows)
    zc (alloc.vec.Vec.new cpoly.field.Ext4) cpoly.field.Ext4.ZERO ta _
     ?_ ?_ reduced_ZERO hRta ?_ ?_ ?_
  · exact ⟨hr, hWt, hWa, hW0, hW1, ht, ha, h0, h1⟩
  · exact ⟨by simp, by intro u hu; simp at hu⟩
  · funext j; exact j.elim0
  · rw [toExt_ZERO, InnerOuter.nestedToRoundStatement]
  · rw [hta, ha, h1, InnerOuter.nestedToRoundStatement]

/- `eval_mle_layer_loop_spec` and `eval_mle_layer_spec` moved to
   `lean/ZeroCheck.lean` § "The layer fold `w_table_mle_eval` runs": this file
   imports `ZeroCheck` (through `EndPiece`), and `w_table_mle_eval` now needs them. -/

/-- The zero-round cube point is the Boolean point itself. -/
theorem hypercubePoint_zero {m : ℕ} (cs : Fin 0 → F) (y : Fin m → Fin 2) :
    InnerOuter.hypercubePoint m 0 cs y = fun j => ((y j : ℕ) : F) := by
  funext j
  simp only [InnerOuter.hypercubePoint]
  rw [dif_neg (by omega)]
  congr 2

/-- The honest round message passes the round check whenever the two targets are the
partial hypercube sums (spec: `roundCheck_honestComputeG`, `Completeness.lean:119`,
without the relation's other conjuncts). -/
theorem roundCheck_honest {n μ M m₁ dRows i : ℕ}
    (s : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ (M + 1) m₁ i)
    (sw : InnerOuter.LiftedWitness Φ μ n) (hi : i < M + 1)
    (h0 : s.target₀ = InnerOuter.hypercubeSum (M + 1)
      (InnerOuter.sumcheckPolyZero Φ (M + 1) phiF 16 s.zc.τ₀ sw) i s.challenges)
    (hα : s.targetα = InnerOuter.hypercubeSum (M + 1)
      (InnerOuter.sumcheckPolyAlpha Φ (M + 1) m₁ phiF 16 s.zc.rlin s.zc.α s.zc.τα sw) i
      s.challenges) :
    InnerOuter.roundCheck Φ (M + 1) m₁ 16 s
      (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF i hi s sw) = true := by
  rw [InnerOuter.roundCheck, Bool.and_eq_true, beq_iff_eq, beq_iff_eq,
    InnerOuter.honestComputeG_fst_eval, InnerOuter.honestComputeG_fst_eval,
    InnerOuter.honestComputeG_snd_eval, InnerOuter.honestComputeG_snd_eval, h0, hα,
    InnerOuter.hypercubeSum_succ (i := ⟨i, hi⟩),
    InnerOuter.hypercubeSum_succ (i := ⟨i, hi⟩)]
  exact ⟨rfl, rfl⟩

/-- One fold of a represented table: `eval_mle_layer` carries the round-`i` tabulation
of a multilinear extension to the round-`(i+1)` one. -/
theorem eval_mle_layer_table_spec {M i : ℕ} (him : i < M + 1)
    (t : alloc.vec.Vec cpoly.field.Ext4) (evals : (Fin (M + 1) → Fin 2) → F)
    (cs : Fin i → F) (a : cpoly.field.Ext4)
    (ht : WfEvals (M + 1 - i) t) (hRa : Reduced a)
    (hv : ∀ y : Fin (M + 1 - i) → Fin 2, tableFn (m := M + 1 - i) t (finFunctionFinEquiv y)
        = (InnerOuter.cMultilinearExtension (M + 1) evals).eval
            (InnerOuter.hypercubePoint (M + 1) i cs y)) :
    cpoly.multilinear.eval_mle_layer (alloc.vec.Vec.deref t) a
      ⦃ o => WfEvals (M + 1 - (i + 1)) o ∧
          ∀ y : Fin (M + 1 - (i + 1)) → Fin 2,
            tableFn (m := M + 1 - (i + 1)) o (finFunctionFinEquiv y)
              = (InnerOuter.cMultilinearExtension (M + 1) evals).eval
                  (InnerOuter.hypercubePoint (M + 1) (i + 1) (Fin.snoc cs (toExt a)) y) ⦄ := by
  have ht' : WfEvals ((M + 1 - i - 1) + 1) t := by
    rwa [show M + 1 - i = (M + 1 - i - 1) + 1 from by omega] at ht
  apply spec_mono (eval_mle_layer_spec (k := M + 1 - i - 1) t a ht' hRa)
  rintro o ⟨hWo, hov⟩
  refine ⟨hWo, fun y => ?_⟩
  rw [hov (finFunctionFinEquiv y)]
  have hstep := fold_tableFn_eq_mle (k := M + 1 - i - 1) him rfl t evals cs (toExt a) hv y
  rw [show (fun j : Fin (M + 1 - i - 1) => y (Fin.cast rfl j)) = y from rfl] at hstep
  exact hstep

/-- The witness table at round `0` tabulates `wTableMleEval` over the cube. -/
theorem initial_w_table {μ n M : ℕ} (w_tab : alloc.vec.Vec cpoly.field.Ext4)
    (sw : InnerOuter.LiftedWitness Φ μ n) (cs : Fin 0 → F)
    (h : toEvals (m := M + 1) w_tab = InnerOuter.cWTableMle Φ (M + 1) phiF 16 sw) :
    ∀ y : Fin (M + 1) → Fin 2, tableFn (m := M + 1) w_tab (finFunctionFinEquiv y)
      = InnerOuter.wTableMleEval Φ (M + 1) phiF 16 sw
          (InnerOuter.hypercubePoint (M + 1) 0 cs y) := by
  intro y
  show (toEvals (m := M + 1) w_tab).get _ = _
  rw [h, InnerOuter.cWTableMle, Vector.get_ofFn, Equiv.symm_apply_apply,
    InnerOuter.wTableMleEval_eq, ← InnerOuter.cMultilinearExtension_eval,
    hypercubePoint_zero]
  exact (InnerOuter.cMultilinearExtension_eval_boolean (M + 1)
    (InnerOuter.wTable Φ (M + 1) phiF 16 sw) y).symm

/-- The public α table at round `0` tabulates its multilinear extension over the cube. -/
theorem initial_a_table {m₁ n μ M : ℕ} (a_tab : alloc.vec.Vec cpoly.field.Ext4)
    (rs : InnerOuter.RlinStatement Φ n μ) (al : F) (tau : Fin m₁ → F) (cs : Fin 0 → F)
    (h : toEvals (m := M + 1) a_tab = Vector.ofFn fun idx : Fin (2 ^ (M + 1)) =>
      InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 rs al tau (finFunctionFinEquiv.symm idx)) :
    ∀ y : Fin (M + 1) → Fin 2, tableFn (m := M + 1) a_tab (finFunctionFinEquiv y)
      = (InnerOuter.cMultilinearExtension (M + 1)
          (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 rs al tau)).eval
          (InnerOuter.hypercubePoint (M + 1) 0 cs y) := by
  intro y
  show (toEvals (m := M + 1) a_tab).get _ = _
  rw [h, Vector.get_ofFn, Equiv.symm_apply_apply, hypercubePoint_zero]
  exact (InnerOuter.cMultilinearExtension_eval_boolean (M + 1)
    (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 rs al tau) y).symm


/-! ## The round loop, as the honest run -/

/-- The honest prover's statements, round by round: `roundOut` applied to
`honestComputeG` at each of the first `k` challenges. `roundsReductionAux`
(`Completeness.lean:347`) is the reduction whose honest execution this is. -/
def honestRounds {n μ M m₁ dRows : ℕ}
    (ss : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ (M + 1) m₁ 0)
    (sw : InnerOuter.LiftedWitness Φ μ n) (cs : Fin (M + 1) → F) :
    (k : ℕ) → k ≤ M + 1 →
      InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ (M + 1) m₁ k
  | 0, _ => ss
  | k + 1, hk =>
    InnerOuter.roundOut Φ (M + 1) m₁ 16 (honestRounds ss sw cs k (Nat.le_of_succ_le hk))
      (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF k (by omega)
        (honestRounds ss sw cs k (Nat.le_of_succ_le hk)) sw)
      (cs ⟨k, hk⟩)

/-- The honest run never changes the zero-check statement it started from. -/
theorem honestRounds_zc {n μ M m₁ dRows : ℕ}
    (ss : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ (M + 1) m₁ 0)
    (sw : InnerOuter.LiftedWitness Φ μ n) (cs : Fin (M + 1) → F) :
    ∀ (k : ℕ) (hk : k ≤ M + 1), (honestRounds ss sw cs k hk).zc = ss.zc := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih => intro hk; exact ih (Nat.le_of_succ_le hk)

/-- Transporting a round statement's relation along an equality of round indices. -/
theorem repRoundStmt_honestRounds_congr {n μ M m₁ dRows : ℕ}
    (ss : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ (M + 1) m₁ 0)
    (sw : InnerOuter.LiftedWitness Φ μ n) (cs : Fin (M + 1) → F)
    (s : sumcheck.RoundStatement) {k k' : ℕ} (hk : k ≤ M + 1) (hk' : k' ≤ M + 1) (h : k = k')
    (hrep : RepRoundStmt (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := k) (dRows := dRows)
      s (honestRounds ss sw cs k hk)) :
    RepRoundStmt (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := k') (dRows := dRows)
      s (honestRounds ss sw cs k' hk') := by
  subst h
  exact hrep

set_option maxHeartbeats 2000000 in
/-- `round_loop` runs the honest prover through all `m₀` rounds against the
verifier's checks (spec: `roundsReductionAux`, `Completeness.lean:347`): when
the initial targets are the two hypercube sums — the sum clauses of
`nestedRoundRel` — every `roundCheck` passes and the result is `some` of the
`m₀`-th `honestRounds` statement. A failing check would return `None`, the
specification's `failure`. `m₀ = M + 1` is read off `tau0`; the two bounds are
`c_w_table_mle_spec`'s and `alpha_public_evals_spec`'s. -/
theorem round_loop_spec {n μ M m₁ dRows : ℕ} (stmt : sumcheck.RoundStatement)
    (w : ringswitch.LiftedWitness) (challenges : alloc.vec.Vec cpoly.field.Ext4)
    (ss : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ (M + 1) m₁ 0)
    (sw : InnerOuter.LiftedWitness Φ μ n)
    (hs : RepRoundStmt (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := 0) (dRows := dRows)
      stmt ss)
    (hw : RepLiftedWitness w sw) (hc : WfPoint (M + 1) challenges)
    (hm0 : 2 ^ (M + 1) ≤ Usize.max) (hmax : μ + n * 8 ≤ Usize.max)
    (h0 : ss.target₀ = InnerOuter.hypercubeSum (M + 1)
      (InnerOuter.sumcheckPolyZero Φ (M + 1) phiF 16 ss.zc.τ₀ sw) 0 ss.challenges)
    (hα : ss.targetα = InnerOuter.hypercubeSum (M + 1)
      (InnerOuter.sumcheckPolyAlpha Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα sw) 0
      ss.challenges) :
    sumcheck.round_loop stmt w challenges
      ⦃ out => ∃ s, out = some s ∧
        RepRoundStmt (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := M + 1) (dRows := dRows)
          s (honestRounds ss sw (toPoint (m := M + 1) challenges) (M + 1) le_rfl) ⦄ := by
  obtain ⟨hzc, hWc, hRt0, hRta, hcv, ht0, hta⟩ := id hs
  obtain ⟨hr, hWt, hWa, hW0, hW1, htv, halv, h0v, h1v⟩ := hzc
  obtain ⟨h0len, h0red⟩ := hW0
  obtain ⟨hclen, hcred⟩ := hc
  set cs := toPoint (m := M + 1) challenges with hcs
  have hm0len : (alloc.vec.Vec.len stmt.zc.tau0).val = M + 1 := by simpa using h0len
  have hMmax : M + 1 ≤ Usize.max := by
    have := Nat.lt_two_pow_self (n := M + 1)
    omega
  simp only [sumcheck.round_loop, sumcheck.RoundStatement.impl.zc,
    sumcheck.NestedZeroCheckStmt.impl.tau0, sumcheck.NestedZeroCheckStmt.impl.rlin,
    sumcheck.NestedZeroCheckStmt.impl.alpha, sumcheck.NestedZeroCheckStmt.impl.tau1,
    bind_tc_ok]
  step with c_w_table_mle_spec (μ := μ) (n := n) w sw (alloc.vec.Vec.len stmt.zc.tau0) hw
    (by rw [hm0len]; exact hm0) hmax as ⟨me, hWme, hmev⟩
  rw [hm0len] at hWme hmev
  simp only [cpoly.multilinear.MultilinearEvals.into_values, bind_tc_ok]
  step with alpha_public_table_spec (n := n) (μ := μ) (m₁ := m₁) stmt.zc.rlin ss.zc.rlin
    stmt.zc.alpha stmt.zc.tau1 (alloc.vec.Vec.len stmt.zc.tau0) hr hWa hW1
    (by rw [hm0len]; exact hm0) hmax as ⟨a_tab, hWa_tab, hatv⟩
  rw [hm0len] at hWa_tab hatv
  rw [halv, h1v] at hatv
  rw [sumcheck.round_loop_loop]
  apply loop.spec_decr_nat (fun st => M + 1 - st.2.2.2.val)
    (fun st => ∃ (j : ℕ) (hj : j ≤ M + 1), st.2.2.2.val = j ∧
      RepRoundStmt (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := j)
          (dRows := dRows) st.2.2.1 (honestRounds ss sw cs j hj) ∧
        WfEvals (M + 1 - j) st.1 ∧ WfEvals (M + 1 - j) st.2.1 ∧
        (∀ y : Fin (M + 1 - j) → Fin 2,
          tableFn (m := M + 1 - j) st.1 (finFunctionFinEquiv y) =
            InnerOuter.wTableMleEval Φ (M + 1) phiF 16 sw
              (InnerOuter.hypercubePoint (M + 1) j (honestRounds ss sw cs j hj).challenges y)) ∧
        (∀ y : Fin (M + 1 - j) → Fin 2,
          tableFn (m := M + 1 - j) st.2.1 (finFunctionFinEquiv y) =
            (InnerOuter.cMultilinearExtension (M + 1)
              (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)).eval
              (InnerOuter.hypercubePoint (M + 1) j (honestRounds ss sw cs j hj).challenges y)) ∧
        (honestRounds ss sw cs j hj).target₀ = InnerOuter.hypercubeSum (M + 1)
          (InnerOuter.sumcheckPolyZero Φ (M + 1) phiF 16 ss.zc.τ₀ sw) j
          (honestRounds ss sw cs j hj).challenges ∧
        (honestRounds ss sw cs j hj).targetα = InnerOuter.hypercubeSum (M + 1)
          (InnerOuter.sumcheckPolyAlpha Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα sw) j
          (honestRounds ss sw cs j hj).challenges)
  · rintro ⟨wt, at1, cur, i⟩ ⟨j, hj, hij, hrep, hWw, hWa2, hwv, hav, htg0, htgα⟩
    dsimp only at hij
    subst hij
    dsimp only at hrep hWw hWa2 hwv hav htg0 htgα
    simp only [sumcheck.round_loop_loop.body]
    by_cases hlt : i < alloc.vec.Vec.len stmt.zc.tau0
    · rw [if_pos hlt]
      have hilt : i.val < M + 1 := by rw [← hm0len]; scalar_tac
      have hzceq : (honestRounds ss sw cs i.val hj).zc = ss.zc := honestRounds_zc ss sw cs i.val hj
      have hav' : ∀ y : Fin (M + 1 - i.val) → Fin 2,
          tableFn (m := M + 1 - i.val) at1 (finFunctionFinEquiv y) =
            (InnerOuter.cMultilinearExtension (M + 1)
              (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16
                (honestRounds ss sw cs i.val hj).zc.rlin (honestRounds ss sw cs i.val hj).zc.α
                (honestRounds ss sw cs i.val hj).zc.τα)).eval
              (InnerOuter.hypercubePoint (M + 1) i.val
                (honestRounds ss sw cs i.val hj).challenges y) := by
        rw [hzceq]; exact hav
      step with honest_compute_g_spec (n := n) (μ := μ) (M := M) (m₁ := m₁) (dRows := dRows)
        cur wt at1 i (honestRounds ss sw cs i.val hj) sw hrep hilt hWw hWa2 hwv hav'
          as ⟨g, hgrep⟩
      step with round_check_spec (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := i.val)
        (dRows := dRows) cur g (honestRounds ss sw cs i.val hj)
        (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF i.val hilt
          (honestRounds ss sw cs i.val hj) sw) hrep hgrep as ⟨b, hb⟩
      have hbt : b = true := by
        rw [hb]
        exact roundCheck_honest (honestRounds ss sw cs i.val hj) sw hilt
          (by rw [htg0, hzceq]) (by rw [htgα, hzceq])
      rw [if_pos hbt]
      have hich : i.val < challenges.val.length := by omega
      step as ⟨a, hav2⟩
      have hRa : Reduced a := hav2 ▸ hcred _ (List.getElem_mem hich)
      have haval : toExt a = cs ⟨i.val, hilt⟩ := by
        rw [hcs]
        simp only [toPoint]
        rw [hav2, List.getD_eq_getElem _ _ hich]
      step with round_out_spec (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := i.val)
        (dRows := dRows) cur g a (honestRounds ss sw cs i.val hj)
        (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF i.val hilt
          (honestRounds ss sw cs i.val hj) sw) hrep hgrep hRa (by omega) as ⟨cur1, hrep1⟩
      step with eval_mle_layer_table_spec (M := M) (i := i.val) hilt wt
        (InnerOuter.wTable Φ (M + 1) phiF 16 sw)
        (honestRounds ss sw cs i.val hj).challenges a hWw hRa
        (by
          intro y
          rw [hwv y, InnerOuter.wTableMleEval_eq, InnerOuter.cMultilinearExtension_eval])
          as ⟨wt1, hWw1, hwv1⟩
      step with eval_mle_layer_table_spec (M := M) (i := i.val) hilt at1
        (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)
        (honestRounds ss sw cs i.val hj).challenges a hWa2 hRa hav as ⟨at2, hWa3, hav3⟩
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = i.val + 1 := by scalar_tac
      have hnext : honestRounds ss sw cs (i.val + 1) (by omega)
          = InnerOuter.roundOut Φ (M + 1) m₁ 16 (honestRounds ss sw cs i.val hj)
              (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF i.val hilt
                (honestRounds ss sw cs i.val hj) sw) (cs ⟨i.val, hilt⟩) := rfl
      rw [haval] at hrep1 hwv1 hav3
      refine ⟨⟨i.val + 1, by omega, hi1v, ?_, hWw1, hWa3, ?_, ?_, ?_, ?_⟩, by omega⟩
      · rw [hnext]; exact hrep1
      · intro y
        rw [hwv1 y, hnext, InnerOuter.roundOut,
          InnerOuter.wTableMleEval_eq, InnerOuter.cMultilinearExtension_eval]
      · intro y
        rw [hav3 y, hnext, InnerOuter.roundOut]
      · rw [hnext, InnerOuter.roundOut]
        dsimp only
        rw [InnerOuter.honestComputeG_fst_eval, hzceq]
      · rw [hnext, InnerOuter.roundOut]
        dsimp only
        rw [InnerOuter.honestComputeG_snd_eval, hzceq]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hieq : i.val = M + 1 := by rw [← hm0len] at hj ⊢; scalar_tac
      exact ⟨cur, rfl,
        repRoundStmt_honestRounds_congr ss sw cs cur hj le_rfl hieq hrep⟩
  · exact ⟨0, Nat.zero_le _, by simp, hs, by simpa using hWme, by simpa using hWa_tab,
      (fun y => initial_w_table (μ := μ) (n := n) (M := M) me sw _ hmev y),
      (fun y => initial_a_table (m₁ := m₁) (n := n) (μ := μ) (M := M) a_tab ss.zc.rlin ss.zc.α
        ss.zc.τα _ hatv y),
      h0, hα⟩


/-! ## The two halves of the rounds, separately -/

set_option maxHeartbeats 2000000 in
/-- `honest_round_messages` is the prover's half of `round_loop`: the `m₀` wire
messages `honestComputeG` produces along `honestRounds` (spec: `roundProver`
at `computeG := honestComputeG`, `Rounds.lean:157`, one per round of
`roundsReductionAux`). Same tables, same folds, same `round_out` threading as
`round_loop`, but no check and the messages are what comes out. `challenges`
must hold `m₀` entries, read at `challenges[i]`; `out.push` is bounded by it. -/
theorem honest_round_messages_spec {n μ M m₁ dRows : ℕ} (stmt : sumcheck.RoundStatement)
    (w : ringswitch.LiftedWitness) (challenges : alloc.vec.Vec cpoly.field.Ext4)
    (ss : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ (M + 1) m₁ 0)
    (sw : InnerOuter.LiftedWitness Φ μ n)
    (hs : RepRoundStmt (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := 0) (dRows := dRows)
      stmt ss)
    (hw : RepLiftedWitness w sw) (hc : WfPoint (M + 1) challenges)
    (hm0 : 2 ^ (M + 1) ≤ Usize.max) (hmax : μ + n * 8 ≤ Usize.max) :
    sumcheck.honest_round_messages stmt w challenges
      ⦃ out => out.val.length = M + 1 ∧
        ∀ (k : ℕ) (hk : k < M + 1),
          RepRoundMsg
            (out.val.getD k { g_zero := alloc.vec.Vec.new cpoly.field.Ext4,
                              g_alpha := alloc.vec.Vec.new cpoly.field.Ext4 })
            (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF k hk
              (honestRounds ss sw (toPoint (m := M + 1) challenges) k (Nat.le_of_lt hk)) sw) ⦄ := by
  obtain ⟨hzc, hWc, hRt0, hRta, hcv, ht0, hta⟩ := id hs
  obtain ⟨hr, hWt, hWa, hW0, hW1, htv, halv, h0v, h1v⟩ := hzc
  obtain ⟨h0len, h0red⟩ := hW0
  obtain ⟨hclen, hcred⟩ := hc
  set cs := toPoint (m := M + 1) challenges with hcs
  have hm0len : (alloc.vec.Vec.len stmt.zc.tau0).val = M + 1 := by simpa using h0len
  have hMmax : M + 1 ≤ Usize.max := by
    have := Nat.lt_two_pow_self (n := M + 1)
    omega
  simp only [sumcheck.honest_round_messages, sumcheck.RoundStatement.impl.zc,
    sumcheck.NestedZeroCheckStmt.impl.tau0, sumcheck.NestedZeroCheckStmt.impl.rlin,
    sumcheck.NestedZeroCheckStmt.impl.alpha, sumcheck.NestedZeroCheckStmt.impl.tau1,
    bind_tc_ok]
  step with c_w_table_mle_spec (μ := μ) (n := n) w sw (alloc.vec.Vec.len stmt.zc.tau0) hw
    (by rw [hm0len]; exact hm0) hmax as ⟨me, hWme, hmev⟩
  rw [hm0len] at hWme hmev
  simp only [cpoly.multilinear.MultilinearEvals.into_values, bind_tc_ok]
  step with alpha_public_table_spec (n := n) (μ := μ) (m₁ := m₁) stmt.zc.rlin ss.zc.rlin
    stmt.zc.alpha stmt.zc.tau1 (alloc.vec.Vec.len stmt.zc.tau0) hr hWa hW1
    (by rw [hm0len]; exact hm0) hmax as ⟨a_tab, hWa_tab, hatv⟩
  rw [hm0len] at hWa_tab hatv
  rw [halv, h1v] at hatv
  rw [sumcheck.honest_round_messages_loop]
  apply loop.spec_decr_nat (fun st => M + 1 - st.2.2.2.2.val)
    (fun st => ∃ (j : ℕ) (hj : j ≤ M + 1), st.2.2.2.2.val = j ∧
      RepRoundStmt (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := j)
          (dRows := dRows) st.2.2.1 (honestRounds ss sw cs j hj) ∧
        WfEvals (M + 1 - j) st.1 ∧ WfEvals (M + 1 - j) st.2.1 ∧
        (∀ y : Fin (M + 1 - j) → Fin 2,
          tableFn (m := M + 1 - j) st.1 (finFunctionFinEquiv y) =
            InnerOuter.wTableMleEval Φ (M + 1) phiF 16 sw
              (InnerOuter.hypercubePoint (M + 1) j (honestRounds ss sw cs j hj).challenges y)) ∧
        (∀ y : Fin (M + 1 - j) → Fin 2,
          tableFn (m := M + 1 - j) st.2.1 (finFunctionFinEquiv y) =
            (InnerOuter.cMultilinearExtension (M + 1)
              (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)).eval
              (InnerOuter.hypercubePoint (M + 1) j (honestRounds ss sw cs j hj).challenges y)) ∧
        st.2.2.2.1.val.length = j ∧
        ∀ (k : ℕ) (hk : k < j),
          RepRoundMsg
            (st.2.2.2.1.val.getD k { g_zero := alloc.vec.Vec.new cpoly.field.Ext4,
                                      g_alpha := alloc.vec.Vec.new cpoly.field.Ext4 })
            (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF k (by omega)
              (honestRounds ss sw cs k (by omega)) sw))
  · rintro ⟨wt, at1, cur, out, i⟩ ⟨j, hj, hij, hrep, hWw, hWa2, hwv, hav, houtlen, houtrep⟩
    dsimp only at hij
    subst hij
    dsimp only at hrep hWw hWa2 hwv hav houtlen houtrep
    simp only [sumcheck.honest_round_messages_loop.body]
    by_cases hlt : i < alloc.vec.Vec.len stmt.zc.tau0
    · rw [if_pos hlt]
      have hilt : i.val < M + 1 := by rw [← hm0len]; scalar_tac
      have hzceq : (honestRounds ss sw cs i.val hj).zc = ss.zc := honestRounds_zc ss sw cs i.val hj
      have hav' : ∀ y : Fin (M + 1 - i.val) → Fin 2,
          tableFn (m := M + 1 - i.val) at1 (finFunctionFinEquiv y) =
            (InnerOuter.cMultilinearExtension (M + 1)
              (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16
                (honestRounds ss sw cs i.val hj).zc.rlin (honestRounds ss sw cs i.val hj).zc.α
                (honestRounds ss sw cs i.val hj).zc.τα)).eval
              (InnerOuter.hypercubePoint (M + 1) i.val
                (honestRounds ss sw cs i.val hj).challenges y) := by
        rw [hzceq]; exact hav
      step with honest_compute_g_spec (n := n) (μ := μ) (M := M) (m₁ := m₁) (dRows := dRows)
        cur wt at1 i (honestRounds ss sw cs i.val hj) sw hrep hilt hWw hWa2 hwv hav'
          as ⟨g, hgrep⟩
      have hich : i.val < challenges.val.length := by omega
      step as ⟨a, hav2⟩
      have hRa : Reduced a := hav2 ▸ hcred _ (List.getElem_mem hich)
      have haval : toExt a = cs ⟨i.val, hilt⟩ := by
        rw [hcs]
        simp only [toPoint]
        rw [hav2, List.getD_eq_getElem _ _ hich]
      step with round_out_spec (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := i.val)
        (dRows := dRows) cur g a (honestRounds ss sw cs i.val hj)
        (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF i.val hilt
          (honestRounds ss sw cs i.val hj) sw) hrep hgrep hRa (by omega) as ⟨cur1, hrep1⟩
      step with eval_mle_layer_table_spec (M := M) (i := i.val) hilt wt
        (InnerOuter.wTable Φ (M + 1) phiF 16 sw)
        (honestRounds ss sw cs i.val hj).challenges a hWw hRa
        (by
          intro y
          rw [hwv y, InnerOuter.wTableMleEval_eq, InnerOuter.cMultilinearExtension_eval])
          as ⟨wt1, hWw1, hwv1⟩
      step with eval_mle_layer_table_spec (M := M) (i := i.val) hilt at1
        (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)
        (honestRounds ss sw cs i.val hj).challenges a hWa2 hRa hav as ⟨at2, hWa3, hav3⟩
      have hpush : out.val.length < Usize.max := by omega
      step as ⟨out1, hout1⟩
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = i.val + 1 := by scalar_tac
      have hnext : honestRounds ss sw cs (i.val + 1) (by omega)
          = InnerOuter.roundOut Φ (M + 1) m₁ 16 (honestRounds ss sw cs i.val hj)
              (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF i.val hilt
                (honestRounds ss sw cs i.val hj) sw) (cs ⟨i.val, hilt⟩) := rfl
      rw [haval] at hrep1 hwv1 hav3
      refine ⟨⟨i.val + 1, by omega, hi1v, ?_, hWw1, hWa3, ?_, ?_, ?_, ?_⟩, by omega⟩
      · rw [hnext]; exact hrep1
      · intro y
        rw [hwv1 y, hnext, InnerOuter.roundOut,
          InnerOuter.wTableMleEval_eq, InnerOuter.cMultilinearExtension_eval]
      · intro y
        rw [hav3 y, hnext, InnerOuter.roundOut]
      · rw [hout1, List.length_append, houtlen]; simp
      · intro k hk
        rcases Nat.lt_or_ge k i.val with hklt | hkge
        · rw [hout1, getD_append_lt _ _ _ (by omega)]
          exact houtrep k hklt
        · have hkeq : k = i.val := by omega
          subst hkeq
          have hgetd : out1.val.getD i.val
              { g_zero := alloc.vec.Vec.new cpoly.field.Ext4,
                g_alpha := alloc.vec.Vec.new cpoly.field.Ext4 } = g := by
            rw [hout1, ← houtlen, getD_append_eq]
          rw [hgetd]
          exact hgrep
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hieq : i.val = M + 1 := by rw [← hm0len] at hj ⊢; scalar_tac
      exact ⟨by rw [houtlen, hieq], fun k hk => houtrep k (by omega)⟩
  · exact ⟨0, Nat.zero_le _, by simp, hs, by simpa using hWme, by simpa using hWa_tab,
      (fun y => initial_w_table (μ := μ) (n := n) (M := M) me sw _ hmev y),
      (fun y => initial_a_table (m₁ := m₁) (n := n) (μ := μ) (M := M) a_tab ss.zc.rlin ss.zc.α
        ss.zc.τα _ hatv y),
      by simp, fun k hk => absurd hk (by omega)⟩


/-- The verifier's half, on the specification side: `roundVerifier`'s
`if roundCheck then pure roundOut else failure` (`Rounds.lean:116`), iterated
over the first `k` rounds as `roundsChain` does (`:402`). `none` is the
first failing round's `failure`. -/
def verifyRounds {n μ m₀ m₁ dRows : ℕ}
    (ss : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ m₀ m₁ 0)
    (gs : Fin m₀ → InnerOuter.RoundMsg F 16) (cs : Fin m₀ → F) :
    (k : ℕ) → k ≤ m₀ →
      Option (InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ m₀ m₁ k)
  | 0, _ => some ss
  | k + 1, hk =>
    (verifyRounds ss gs cs k (Nat.le_of_succ_le hk)).bind fun s =>
      if InnerOuter.roundCheck Φ m₀ m₁ 16 s (gs ⟨k, hk⟩) then
        some (InnerOuter.roundOut Φ m₀ m₁ 16 s (gs ⟨k, hk⟩) (cs ⟨k, hk⟩))
      else none

/-- Once a round fails, every later round of `verifyRounds` fails too. -/
theorem verifyRounds_none_mono {n μ m₀ m₁ dRows : ℕ}
    (ss : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ m₀ m₁ 0)
    (gs : Fin m₀ → InnerOuter.RoundMsg F 16) (cs : Fin m₀ → F) :
    ∀ (l : ℕ) (hl : l ≤ m₀) (k : ℕ) (hk : k ≤ m₀), k ≤ l →
      verifyRounds ss gs cs k hk = none → verifyRounds ss gs cs l hl = none := by
  intro l
  induction l with
  | zero =>
    intro hl k hk hkl h
    have hk0 : k = 0 := Nat.le_zero.mp hkl
    subst hk0
    exact h
  | succ l ih =>
    intro hl k hk hkl h
    rcases Nat.lt_or_ge k (l + 1) with hlt | hge
    · have hprev := ih (Nat.le_of_succ_le hl) k hk (by omega) h
      show (verifyRounds ss gs cs l _).bind _ = _
      rw [hprev]
      rfl
    · have hkeq : k = l + 1 := by omega
      subst hkeq
      exact h

/-- Relation between a vector of extracted round messages and `m₀` specification
messages, entrywise. -/
def RepMsgs {m₀ : ℕ} (msgs : alloc.vec.Vec sumcheck.RoundMsg)
    (gs : Fin m₀ → InnerOuter.RoundMsg F 16) : Prop :=
  msgs.val.length = m₀ ∧ ∀ k : Fin m₀,
    RepRoundMsg (msgs.val.getD k.val { g_zero := alloc.vec.Vec.new cpoly.field.Ext4,
                                        g_alpha := alloc.vec.Vec.new cpoly.field.Ext4 })
      (gs k)

/-- `round_verify_loop` computes `verifyRounds` over all `m₀` rounds (spec:
`roundVerifier`, over every round): `none` exactly when the specification
fails, and otherwise the related `m₀`-th statement. It holds no witness and no
table, so it needs no cube bound: the fail points are `msgs[i]` and
`challenges[i]`, both inside `m₀` by the relations, and `round_out`'s push,
whose `i < m₀ ≤ Usize.max` the loop guard gives. -/
theorem round_verify_loop_spec {n μ m₀ m₁ dRows : ℕ} (stmt : sumcheck.RoundStatement)
    (msgs : alloc.vec.Vec sumcheck.RoundMsg) (challenges : alloc.vec.Vec cpoly.field.Ext4)
    (ss : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ m₀ m₁ 0)
    (gs : Fin m₀ → InnerOuter.RoundMsg F 16)
    (hs : RepRoundStmt (n := n) (μ := μ) (m₀ := m₀) (m₁ := m₁) (i := 0) (dRows := dRows) stmt ss)
    (hg : RepMsgs (m₀ := m₀) msgs gs) (hc : WfPoint m₀ challenges) :
    sumcheck.round_verify_loop stmt msgs challenges
      ⦃ out => match verifyRounds ss gs (toPoint (m := m₀) challenges) m₀ le_rfl with
        | none => out = none
        | some s' => ∃ s, out = some s ∧
            RepRoundStmt (n := n) (μ := μ) (m₀ := m₀) (m₁ := m₁) (i := m₀) (dRows := dRows)
              s s' ⦄ := by
  obtain ⟨hmlen, hmrep⟩ := hg
  obtain ⟨hclen, hcred⟩ := hc
  set cs := toPoint (m := m₀) challenges with hcs
  have hm0 : (alloc.vec.Vec.len (sumcheck.NestedZeroCheckStmt.tau0 stmt.zc)).val = m₀ := by
    have := hs.1.2.2.2.1
    simpa using this.1
  simp only [sumcheck.round_verify_loop, sumcheck.RoundStatement.impl.zc,
    sumcheck.NestedZeroCheckStmt.impl.tau0, bind_tc_ok]
  rw [sumcheck.round_verify_loop_loop]
  apply loop.spec_decr_nat (fun st => m₀ - st.2.val)
    (fun st => ∃ (hi : st.2.val ≤ m₀) (s' : InnerOuter.NestedRoundStatement Φ
        (PolyVec (Rq Φ) dRows) F n μ m₀ m₁ st.2.val),
      verifyRounds ss gs cs st.2.val hi = some s' ∧
        RepRoundStmt (n := n) (μ := μ) (m₀ := m₀) (m₁ := m₁) (i := st.2.val) (dRows := dRows)
          st.1 s')
  · rintro ⟨cur, i⟩ ⟨hi, s', hver, hrep⟩
    dsimp only at hi hver hrep
    simp only [sumcheck.round_verify_loop_loop.body]
    by_cases hlt : i < alloc.vec.Vec.len (sumcheck.NestedZeroCheckStmt.tau0 stmt.zc)
    · rw [if_pos hlt]
      have hilt : i.val < m₀ := by rw [← hm0]; scalar_tac
      have himsg : i.val < msgs.val.length := by omega
      have hich : i.val < challenges.val.length := by omega
      step as ⟨gmsg, hgmsg⟩
      have hgrep : RepRoundMsg gmsg (gs ⟨i.val, hilt⟩) := by
        have := hmrep ⟨i.val, hilt⟩
        rwa [List.getD_eq_getElem _ _ himsg, ← hgmsg] at this
      step with round_check_spec (n := n) (μ := μ) (m₀ := m₀) (m₁ := m₁) (i := i.val)
        (dRows := dRows) cur gmsg s' (gs ⟨i.val, hilt⟩) hrep hgrep as ⟨b, hb⟩
      by_cases hbt : b = true
      · rw [if_pos hbt]
        have hcheck : InnerOuter.roundCheck Φ m₀ m₁ 16 s' (gs ⟨i.val, hilt⟩) = true := by
          rw [← hb]; exact hbt
        step as ⟨a, ha⟩
        have hRa : Reduced a := ha ▸ hcred _ (List.getElem_mem hich)
        have hav : toExt a = cs ⟨i.val, hilt⟩ := by
          rw [hcs]
          simp only [toPoint]
          rw [ha, List.getD_eq_getElem _ _ hich]
        step with round_out_spec (n := n) (μ := μ) (m₀ := m₀) (m₁ := m₁) (i := i.val)
          (dRows := dRows) cur gmsg a s' (gs ⟨i.val, hilt⟩) hrep hgrep hRa
          (by have : i.val < m₀ := hilt
              have : (m₀ : ℕ) ≤ Usize.max := by
                have := challenges.property
                omega
              omega) as ⟨cur1, hrep1⟩
        step as ⟨i1, hi1⟩
        have hi1n : i1.val = i.val + 1 := by scalar_tac
        refine ⟨?_, by scalar_tac⟩
        rw [hi1n]
        refine ⟨by omega,
          InnerOuter.roundOut Φ m₀ m₁ 16 s' (gs ⟨i.val, hilt⟩) (cs ⟨i.val, hilt⟩), ?_, ?_⟩
        · show (verifyRounds ss gs cs i.val _).bind _ = _
          rw [hver]
          simp only [Option.bind_some, hcheck, if_true]
        · rw [hav] at hrep1
          exact hrep1
      · have hbf : b = false := by cases b <;> simp_all
        rw [if_neg (by simp [hbf]), WP.spec_ok]
        have hcheck : InnerOuter.roundCheck Φ m₀ m₁ 16 s' (gs ⟨i.val, hilt⟩) = false := by
          rw [← hb]; exact hbf
        have hnone : verifyRounds ss gs cs (i.val + 1) (by omega) = none := by
          show (verifyRounds ss gs cs i.val _).bind _ = _
          rw [hver]
          simp only [Option.bind_some, hcheck]
          rfl
        have hall : verifyRounds ss gs cs m₀ le_rfl = none :=
          verifyRounds_none_mono ss gs cs m₀ le_rfl (i.val + 1) (by omega) (by omega) hnone
        rw [hall]
    · rw [if_neg hlt, WP.spec_ok]
      have hieq : i.val = m₀ := by rw [← hm0] at hi ⊢; scalar_tac
      subst hieq
      rw [hver]
      exact ⟨cur, rfl, hrep⟩
  · exact ⟨Nat.zero_le _, ss, rfl, hs⟩

end HachiEquiv.Sumcheck
