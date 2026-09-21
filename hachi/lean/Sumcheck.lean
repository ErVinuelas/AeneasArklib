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
import SumcheckShift
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
theorem poly_mul_inner_loop_spec (p q : alloc.vec.Vec cpoly.field.Ext4) (nq i : Std.Usize)
    (hp : VecReduced p) (hq : VecReduced q) (hnq : nq.val = q.val.length)
    (hip : i.val < p.val.length) :
    ∀ (r : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize),
      VecReduced r → j.val ≤ nq.val → i.val + nq.val ≤ r.val.length →
      sumcheck.poly_mul_loop0_loop0
          p q nq r i j
        ⦃ z => VecReduced z ∧ z.val.length = r.val.length ∧
          ∀ k, (toRaw z).coeff k = (toRaw r).coeff k +
            (if i.val + j.val ≤ k ∧ k < i.val + nq.val
              then (toRaw p).coeff i.val * (toRaw q).coeff (k - i.val) else 0) ⦄ := by
  intro r j hr hj hbound
  rw [sumcheck.poly_mul_loop0_loop0]
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
    simp only [sumcheck.poly_mul_loop0_loop0.body,
      cpoly.univariate.UnivariatePoly.Insts.CoreOpsIndexIndexUsizeExt4.index]
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
theorem poly_mul_outer_loop_spec (p q : alloc.vec.Vec cpoly.field.Ext4) (np nq : Std.Usize)
    (hp : VecReduced p) (hq : VecReduced q)
    (hnp : np.val = p.val.length) (hnq : nq.val = q.val.length) :
    ∀ (r : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize),
      VecReduced r → i.val ≤ np.val → np.val + nq.val ≤ r.val.length + 1 →
      (∀ k, (toRaw r).coeff k = convol p q i.val k) →
      sumcheck.poly_mul_loop0
          p q np nq r i
        ⦃ z => VecReduced z ∧ z.val.length = r.val.length ∧
          ∀ k, (toRaw z).coeff k = convol p q np.val k ⦄ := by
  intro r i hr hi hbound hcoeff
  rw [sumcheck.poly_mul_loop0]
  apply loop.spec_decr_nat (fun s => np.val - s.2.val)
    (fun s => VecReduced s.1 ∧ s.2.val ≤ np.val ∧ s.1.val.length = r.val.length ∧
      ∀ k, (toRaw s.1).coeff k = convol p q s.2.val k)
  · rintro ⟨r1, i1⟩ hinv
    obtain ⟨hr1, hi1, hlen1, hcoeff1⟩ : VecReduced r1 ∧ i1.val ≤ np.val ∧
        r1.val.length = r.val.length ∧
        (∀ k, (toRaw r1).coeff k = convol p q i1.val k) := hinv
    simp only [sumcheck.poly_mul_loop0.body]
    by_cases hlt : i1 < np
    · rw [if_pos hlt]
      have h1 : i1.val < np.val := by scalar_tac
      have hip : i1.val < p.val.length := by omega
      have hib : i1.val + nq.val ≤ r1.val.length := by omega
      apply spec_bind (poly_mul_inner_loop_spec p q nq i1 hp hq hnq hip
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

/-- `UnivariatePoly::len` is `ok (Vec.len ·)`; no `@[step]` lemma is registered
for it, so `poly_mul_spec` needs it spelled out (as `Ring.lean` does for
`Fp::to_u64`). Candidate P reaches it because hachi cannot touch
`UnivariatePoly`'s private field, where cpoly's own body used it directly. -/
private theorem uni_len_id (p : cpoly.univariate.UnivariatePoly) :
    cpoly.univariate.UnivariatePoly.len p ⦃ x => x = alloc.vec.Vec.len p ⦄ := by
  rw [cpoly.univariate.UnivariatePoly.len, WP.spec_ok]

/-- `sumcheck::poly_mul` ↔ `CPolynomial.Raw.mul` (schoolbook, trimmed once at
the end).

Candidate P moved this multiplication into hachi. The three specs below were
written against cpoly's `impl Mul<&UnivariatePoly> for &UnivariatePoly` and are
retargeted here by item name alone -- the body is that body, so the two loops and
their invariants did not move. What did move is *whose* code they are about: with
cpoly's generic multiplication out of the reachable model, a `cpoly` pin bump can
no longer break them.

`hlen` is necessary, not convenient: the accumulator is sized by a *checked*
`np + nq`, which fails above `Usize.max` before `n ← i - 1` can bring it
back — cpoly's header records that the triple is false without it. -/
theorem poly_mul_spec (v w : alloc.vec.Vec cpoly.field.Ext4)
    (hv : VecReduced v) (hw : VecReduced w)
    (hlen : v.val.length + w.val.length ≤ Std.Usize.max) :
    sumcheck.poly_mul v w
      ⦃ z => VecReduced z ∧ toRaw z = CPolynomial.Raw.mul (toRaw v) (toRaw w) ∧
        z.val.length ≤ v.val.length + w.val.length ⦄ := by
  have hnewred : VecReduced (alloc.vec.Vec.new cpoly.field.Ext4) := by intro u hu; simp at hu
  have hnewraw : toRaw (alloc.vec.Vec.new cpoly.field.Ext4) = (0 : CPolynomial.Raw F) := by
    simp [toRaw]
  rw [sumcheck.poly_mul]
  -- `UnivariatePoly::len` is `ok (Vec.len ·)`; stepping past the two calls and
  -- rewriting back restores the shape cpoly's body had, where the lengths were
  -- pure. Everything below is the ported proof, unchanged.
  step with uni_len_id v as ⟨np, hnp⟩
  step with uni_len_id w as ⟨nq, hnq⟩
  rw [hnp, hnq]
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
      apply spec_bind (poly_mul_outer_loop_spec v w (alloc.vec.Vec.len v) (alloc.vec.Vec.len w)
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

/-- The `usize → u64` cast every interpolation-node index goes through. Total,
and for a reason that is not about the nodes: `Usize.max ≤ U64.max` on both
platforms Aeneas models, so the cast is in bounds for *any* `usize`. Shared by
`round_node_spec` and by the two base-field node loops, which stop one step
earlier than it does. -/
theorem node_cast_spec (i : Std.Usize) :
    lift (UScalar.cast .U64 i) ⦃ y => y.val = i.val ⦄ :=
  UScalar.cast_inBounds_spec .U64 i (by
    have h1 : i.val ≤ Usize.max := by scalar_tac
    have h3 : UScalar.max UScalarTy.U64 = 18446744073709551615 := by
      simp [UScalar.max_def, UScalarTy.numBits]
    have h2 : Usize.max ≤ 18446744073709551615 := by
      rw [Usize.max_def]
      rcases System.Platform.numBits_eq with h | h <;> simp [Usize.numBits, h]
    omega)

/-- `round_node i` is the field element `i` (spec: `CPolynomial.pointNode` at
the node array `0 … 2b`): `φF (i : ZMod q) = (i : F)`. Total. -/
theorem round_node_spec (i : Std.Usize) :
    sumcheck.round_node i ⦃ out => Reduced out ∧ toExt out = (i.val : F) ⦄ := by
  rw [sumcheck.round_node]
  step with node_cast_spec i as ⟨w, hw⟩
  step with fp_new_spec w as ⟨c, hRc, hc⟩
  apply spec_mono (ext_from_base_spec c hRc)
  rintro out ⟨hRout, hout⟩
  refine ⟨hRout, ?_⟩
  rw [hout, hc, hw, ofBase_natCast]

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

/-! ### The same two sums at a base-field `w̃` table

Round 0 of the sumcheck holds `w̃` as a `Vec<Fp>` (candidate I, `lean/Opt.lean`
§ "Candidate I"): every entry of the committed table is `φF` of a witness
coefficient, so before the first challenge has touched it the fold and the range
factor are `ZMod q` arithmetic, and only the equality table `eq̃` is a genuine
extension element. Neither `rangeSumZero` nor `linSumAlpha` moves -- the tables
below are the *embedded* ones, `φF ∘ tableFnFp`, and the node is the embedded
node -- so what follows is the two range forms above with the embedding pushed
inside, which is the whole content of "round 0 is base-field". -/

/-- `rangeSumZero` at an embedded base-field table, as a sum over a range: the
shape `round_value_zero_base`'s loop invariant carries. The summand is in the
Rust's operand order -- the range factor on the **left** of `eq[y]`, which is
what selects `impl Mul<Ext4> for Fp` -- so the `mul_comm` against
`rangeSumZero`'s own orientation is paid here and not in the loop. -/
theorem rangeSumZeroFp_eq_sum_range {k : ℕ} (w : alloc.vec.Vec cpoly.field.Fp)
    (eq : alloc.vec.Vec cpoly.field.Ext4) (T : ZMod q) :
    rangeSumZero (phiF ∘ tableFnFp (m := k + 1) w) (tableFn (m := k) eq) (phiF T)
      = ∑ y ∈ Finset.range (2 ^ k),
          InnerOuter.rangeProduct 16
              (phiF ((1 - T) * coeffK w (2 * y) + T * coeffK w (2 * y + 1)))
            * toExt (eq.val.getD y cpoly.field.Ext4.ZERO) := by
  rw [rangeSumZero, ← Fin.sum_univ_eq_sum_range (fun y : ℕ =>
    InnerOuter.rangeProduct 16
        (phiF ((1 - T) * coeffK w (2 * y) + T * coeffK w (2 * y + 1)))
      * toExt (eq.val.getD y cpoly.field.Ext4.ZERO)) (2 ^ k)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have hfold : fold (phiF ∘ tableFnFp (m := k + 1) w) (phiF T) y
      = phiF ((1 - T) * coeffK w (2 * y.val) + T * coeffK w (2 * y.val + 1)) := by
    rw [map_add, map_mul, map_mul, map_sub, map_one]
    rfl
  rw [tableFn_apply, hfold]
  exact mul_comm _ _

/-- `linSumAlpha` at an embedded base-field `w̃` table against an extension `Ã`
table, as a sum over a range: the `w̃` fold in `ZMod q` scaling the `Ã` fold,
again with the `Fp` factor on the left. -/
theorem linSumAlphaFp_eq_sum_range {k : ℕ} (w : alloc.vec.Vec cpoly.field.Fp)
    (a : alloc.vec.Vec cpoly.field.Ext4) (T : ZMod q) :
    linSumAlpha (phiF ∘ tableFnFp (m := k + 1) w) (tableFn (m := k + 1) a) (phiF T)
      = ∑ y ∈ Finset.range (2 ^ k),
          phiF ((1 - T) * coeffK w (2 * y) + T * coeffK w (2 * y + 1)) *
            ((1 - phiF T) * toExt (a.val.getD (2 * y) cpoly.field.Ext4.ZERO) +
              phiF T * toExt (a.val.getD (2 * y + 1) cpoly.field.Ext4.ZERO)) := by
  rw [linSumAlpha, ← Fin.sum_univ_eq_sum_range (fun y : ℕ =>
    phiF ((1 - T) * coeffK w (2 * y) + T * coeffK w (2 * y + 1)) *
      ((1 - phiF T) * toExt (a.val.getD (2 * y) cpoly.field.Ext4.ZERO) +
        phiF T * toExt (a.val.getD (2 * y + 1) cpoly.field.Ext4.ZERO))) (2 ^ k)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [map_add, map_mul, map_mul, map_sub, map_one, fold, fold, tableFn_apply, tableFn_apply]
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

/-- The **inner** loop of `round_values_zero`: one pair per step, with the
two-point fold done in the **base field** (candidate T2c).

`round_values_zero` knows what `round_value_zero` cannot: its node is
`Fp::new(t)`, so `one_minus = Fp::ONE - node` is a base-field element too, and
each of the two fold products is the *mixed* `Mul<Ext4> for Fp` impl --
`fp_ext_mul_spec`, four base multiplications -- where `round_value_zero`'s
`Ext4 x Ext4` fold pays nineteen apiece. That is the whole candidate; the sum
being computed is unchanged, which is why the caller's statement below does not
move.

The scalars enter only through `hone`, and `hom` in the step is the one line of
new proof content: `ofBase` is a ring homomorphism, so
`ofBase (1 - toK node) = 1 - ofBase (toK node)` and the invariant is
`round_value_zero_spec`'s with `toExt node` read as `ofBase (toK node)`.
`half` is a *pure* `let` in the extracted body (`Vec.len` is not monadic), so it
arrives as a parameter and `hhalf` is what translates the loop guard. -/
theorem round_values_zero_loop0_loop0_spec {k : ℕ}
    (w eq : alloc.vec.Vec cpoly.field.Ext4)
    (node one_minus : cpoly.field.Fp) (half : Std.Usize)
    (acc : cpoly.field.Ext4) (y : Std.Usize)
    (hw : WfEvals (k + 1) w) (heq : WfEvals k eq)
    (hRn : Red node) (hRo : Red one_minus)
    (hone : toK one_minus = 1 - toK node)
    (hhalf : half.val = eq.val.length)
    (hy : y.val ≤ 2 ^ k) (hRacc : Reduced acc)
    (hacc : toExt acc = ∑ y' ∈ Finset.range y.val,
      toExt (eq.val.getD y' cpoly.field.Ext4.ZERO) *
        InnerOuter.rangeProduct 16
          ((1 - Ext.ofBase (toK node)) *
              toExt (w.val.getD (2 * y') cpoly.field.Ext4.ZERO) +
            Ext.ofBase (toK node) *
              toExt (w.val.getD (2 * y' + 1) cpoly.field.Ext4.ZERO))) :
    sumcheck.round_values_zero_loop0_loop0 w eq node one_minus half acc y
      ⦃ out => Reduced out ∧ toExt out =
        rangeSumZero (tableFn (m := k + 1) w) (tableFn (m := k) eq)
          (Ext.ofBase (toK node)) ⦄ := by
  obtain ⟨hwlen, hwred⟩ := hw
  obtain ⟨heqlen, heqred⟩ := heq
  have hwmax : w.val.length ≤ Usize.max := w.property
  rw [sumcheck.round_values_zero_loop0_loop0]
  apply loop.spec_decr_nat (fun s => 2 ^ k - s.2.val)
    (fun s => s.2.val ≤ 2 ^ k ∧ Reduced s.1 ∧
      toExt s.1 = ∑ y' ∈ Finset.range s.2.val,
        toExt (eq.val.getD y' cpoly.field.Ext4.ZERO) *
          InnerOuter.rangeProduct 16
            ((1 - Ext.ofBase (toK node)) *
                toExt (w.val.getD (2 * y') cpoly.field.Ext4.ZERO) +
              Ext.ofBase (toK node) *
                toExt (w.val.getD (2 * y' + 1) cpoly.field.Ext4.ZERO)))
  · rintro ⟨a1, y1⟩ ⟨hy1, hRa1, ha1⟩
    dsimp only at hy1 hRa1 ha1
    simp only [sumcheck.round_values_zero_loop0_loop0.body]
    by_cases hlt : y1 < half
    · rw [if_pos hlt]
      have hylt : y1.val < 2 ^ k := by
        have : y1.val < eq.val.length := by scalar_tac
        omega
      have h2y : 2 * y1.val + 1 < w.val.length := by rw [hwlen, pow_succ]; omega
      have hmul : 2 * y1.val ≤ Usize.max := by omega
      step as ⟨i, hi⟩
      have hib : i.val < w.val.length := by rw [hi]; omega
      step as ⟨lo0, hlo0⟩
      have hRlo0 : Reduced lo0 := hlo0 ▸ hwred _ (List.getElem_mem hib)
      step as ⟨i1, hi1⟩
      have hi1b : i1.val < w.val.length := by rw [hi1, hi]; omega
      step as ⟨hi0, hhi0⟩
      have hRhi0 : Reduced hi0 := hhi0 ▸ hwred _ (List.getElem_mem hi1b)
      step with fp_ext_mul_spec one_minus lo0 hRo hRlo0 as ⟨e, hRe, he⟩
      step with fp_ext_mul_spec node hi0 hRn hRhi0 as ⟨e1, hRe1, he1⟩
      step with ext_add_spec e e1 hRe hRe1 as ⟨folded, hRf, hf⟩
      have hyb : y1.val < eq.val.length := by omega
      step as ⟨e2, he2⟩
      have hRe2 : Reduced e2 := he2 ▸ heqred _ (List.getElem_mem hyb)
      step with range_product_spec folded hRf as ⟨e3, hRe3, he3⟩
      step with ext_mul_spec e2 e3 hRe2 hRe3 as ⟨e4, hRe4, he4⟩
      step with ext_add_spec a1 e4 hRa1 hRe4 as ⟨acc1, hRacc1, hacc1⟩
      step as ⟨y2, hy2⟩
      refine ⟨by scalar_tac, hRacc1, ?_, by scalar_tac⟩
      have hom : (Ext.ofBase (toK one_minus) : F) = 1 - Ext.ofBase (toK node) := by
        rw [hone, ← phiF_apply, ← phiF_apply, map_sub, map_one]
      rw [hacc1, ha1, hy2, Finset.sum_range_succ, he4, he3, hf, he, he1, hom,
        he2, hlo0, hhi0,
        ← List.getD_eq_getElem eq.val cpoly.field.Ext4.ZERO hyb,
        ← List.getD_eq_getElem w.val cpoly.field.Ext4.ZERO hib,
        ← List.getD_eq_getElem w.val cpoly.field.Ext4.ZERO hi1b, hi1, hi]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hyeq : y1.val = 2 ^ k := by
        have : half.val ≤ y1.val := by scalar_tac
        omega
      refine ⟨hRa1, ?_⟩
      rw [ha1, hyeq, rangeSumZero_eq_sum_range]
  · exact ⟨hy, hRacc, hacc⟩

/-- `round_values_zero`: the `33` node values of `rangeSumZero`, at `0 … 32`.

**The statement is candidate F's, unchanged.** It is pointwise in the node, so it
says nothing about how the `33` values were produced, and candidate T2c's
rearrangement of the fold leaves it exactly where it was -- only the proof below
is restated, around the new inner loop. Aeneas renamed the outer loop
`round_values_zero_loop` to `_loop0` when the second loop appeared, which is what
made the restatement mandatory rather than optional. -/
theorem round_values_zero_spec {k : ℕ} (w eq : alloc.vec.Vec cpoly.field.Ext4)
    (hw : WfEvals (k + 1) w) (heq : WfEvals k eq) :
    sumcheck.round_values_zero w eq
      ⦃ out => out.val.length = 33 ∧ VecReduced out ∧
        ∀ t : Fin 33, toExt (out.val.getD t.val cpoly.field.Ext4.ZERO) =
          rangeSumZero (tableFn (m := k + 1) w) (tableFn (m := k) eq)
            (t.val : F) ⦄ := by
  have hrn : (params.ROUND_NODES).val = 33 := by simp [params.ROUND_NODES]
  have hmax := usize_max_ge
  have hRZ : Reduced cpoly.field.Ext4.ZERO := reduced_ZERO
  rw [sumcheck.round_values_zero, sumcheck.round_values_zero_loop0]
  apply loop.spec_decr_nat (fun s => 33 - s.2.val)
    (fun s => s.2.val ≤ 33 ∧ s.1.val.length = s.2.val ∧ VecReduced s.1 ∧
      ∀ t : ℕ, t < s.2.val → toExt (s.1.val.getD t cpoly.field.Ext4.ZERO) =
        rangeSumZero (tableFn (m := k + 1) w) (tableFn (m := k) eq) (t : F))
  · rintro ⟨v1, t1⟩ ⟨ht1, hlen1, hred1, hval1⟩
    dsimp only at ht1 hlen1 hred1 hval1
    simp only [sumcheck.round_values_zero_loop0.body]
    by_cases hlt : t1 < params.ROUND_NODES
    · rw [if_pos hlt]
      have ht1lt : t1.val < 33 := by scalar_tac
      step with node_cast_spec t1 as ⟨u, hu⟩
      step with fp_new_spec u as ⟨nd, hRnd, hnd⟩
      step with fp_sub_spec cpoly.field.Fp.ONE nd red_Fp_ONE hRnd as ⟨om, hRom, hom⟩
      step with round_values_zero_loop0_loop0_spec (k := k) w eq nd om
        (alloc.vec.Vec.len eq) cpoly.field.Ext4.ZERO 0#usize hw heq hRnd hRom
        (by rw [hom, toK_one]) (by simp) (by simp) hRZ (by simp) as ⟨e, hRe, he⟩
      have hbound : v1.val.length < Usize.max := by omega
      step as ⟨v2, hv2⟩
      step as ⟨t2, ht2⟩
      have ht2n : t2.val = t1.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, ?_, ?_, by scalar_tac⟩
      · rw [ht2n, hv2, List.length_append, hlen1]; simp
      · intro u' hu'
        rw [hv2] at hu'
        rcases List.mem_append.mp hu' with h | h
        · exact hred1 u' h
        · rw [List.mem_singleton.mp h]; exact hRe
      · intro t ht
        rw [ht2n] at ht
        rcases Nat.lt_or_ge t t1.val with htlt | htge
        · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = v1.val.length := by omega
          rw [hteq, hv2, getD_append_eq, he, hnd, hu, hlen1, ofBase_natCast]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hteq : t1.val = 33 := by scalar_tac
      exact ⟨by rw [hlen1, hteq], hred1, fun t => hval1 t.val (by rw [hteq]; exact t.isLt)⟩
  · exact ⟨by simp, by simp, by intro u hu; simp at hu, by intro t ht; simp at ht⟩

/-- **`round_poly_zero` is the Taylor shift of the range summand**
(Stage 6 candidate T3).

The statement is the one the interpolating version had, word for word: `33`
coefficients, reduced, and the polynomial they denote evaluates to
`rangeSumZero` everywhere. Only the proof moved. It used to be a Lagrange
uniqueness argument — `2b + 1` nodes determine a polynomial of degree
`2b − 1 < 2b + 1`. It is now the binomial theorem: the fold is affine in the
node, so `P_b(W(T, y))` is `P_b` shifted, and
[`SumcheckShift.rangeProduct_shift`] writes its coefficients down.

The top coefficient is still zero — `P_b` has degree `2b − 1 = 31`, so the
shift has `2b = 32` coefficients and the `33`rd is the explicit `ZERO` the code
pushes. It is the same arithmetic fingerprint of the missing free factor
(NOTES.md § "The dropped `eq̃` factor") that the interpolating version left
behind, arrived at the other way round. -/
theorem round_poly_zero_spec {k : ℕ} (w eq : alloc.vec.Vec cpoly.field.Ext4)
    (hw : WfEvals (k + 1) w) (heq : WfEvals k eq) :
    sumcheck.round_poly_zero w eq
      ⦃ out => out.val.length = 33 ∧ VecReduced out ∧
        ∀ x : F, CPolynomial.eval x (toUni out) =
          rangeSumZero (tableFn (m := k + 1) w) (tableFn (m := k) eq) x ⦄ := by
  rw [sumcheck.round_poly_zero]
  simp only [alloc.vec.Vec.with_capacity]
  step with HachiEquiv.SumcheckShift.zero_fill_spec params.SHIFT_DEG
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize HachiEquiv.SumcheckShift.shift_deg_val
    (by simp) (by simp) (by intro a ha; simp at ha) (by intro t ht; simp at ht)
    as ⟨acc1, hacl, hacr, hacv⟩
  have hhalf : (alloc.vec.Vec.len eq).val = eq.val.length := by simp
  have hwl : w.val.length = 2 * eq.val.length := by
    rw [hw.1, heq.1, pow_succ]; ring
  step with HachiEquiv.SumcheckShift.pair_loop_spec w eq (alloc.vec.Vec.len eq) acc1 0#usize
    hhalf hwl hw.2 heq.2 (by simp) hacl hacr
    (by intro t ht; rw [hacv t ht]; simp)
    as ⟨acc2, ha2l, ha2r, ha2v⟩
  have hmax : acc2.val.length < Std.Usize.max := by
    rw [ha2l]; have := usize_max_ge'; omega
  step as ⟨acc3, ha3⟩
  rw [cpoly.univariate.UnivariatePoly.from_coeffs, WP.spec_ok]
  have ha3l : acc3.val.length = 33 := by
    rw [ha3, List.length_append, ha2l]; simp
  refine ⟨ha3l, ?_, fun x => ?_⟩
  · intro a ha
    rw [ha3] at ha
    rcases List.mem_append.mp ha with h | h
    · exact ha2r a h
    · rw [List.mem_singleton.mp h]; exact reduced_ZERO
  -- the coefficients, read back
  have hco : ∀ t, t < 32 → toExt (acc3.val.getD t cpoly.field.Ext4.ZERO)
      = ∑ y' ∈ Finset.range eq.val.length,
          HachiEquiv.SumcheckShift.eqF eq y'
            * HachiEquiv.SumcheckShift.shiftCoeff (HachiEquiv.SumcheckShift.loF w y')
                (HachiEquiv.SumcheckShift.dF w y') t := by
    intro t ht
    rw [ha3, HachiEquiv.GoldTransform.getD_append_lt' _ _ _ (by rw [ha2l]; exact ht)]
    rw [ha2v t ht, hhalf]
  have hco32 : toExt (acc3.val.getD 32 cpoly.field.Ext4.ZERO) = 0 := by
    rw [ha3, show (32 : ℕ) = acc2.val.length by rw [ha2l],
      HachiEquiv.GoldTransform.getD_append_eq']
    exact toExt_ZERO
  rw [toUni_eval, toRaw_eval_eq_sum acc3 x 33 (by rw [ha3l]),
    Finset.sum_range_succ]
  have hlast : (toRaw acc3).coeff 32 * x ^ 32 = 0 := by
    rw [toRaw_coeff_of_lt acc3 (by rw [ha3l]; norm_num),
      ← List.getD_eq_getElem (l := acc3.val) (d := cpoly.field.Ext4.ZERO)
        (by rw [ha3l]; norm_num), hco32]
    ring
  rw [hlast, add_zero]
  have hterm : ∀ t ∈ Finset.range 32, (toRaw acc3).coeff t * x ^ t
      = ∑ y' ∈ Finset.range eq.val.length,
          HachiEquiv.SumcheckShift.eqF eq y'
            * (HachiEquiv.SumcheckShift.shiftCoeff (HachiEquiv.SumcheckShift.loF w y')
                (HachiEquiv.SumcheckShift.dF w y') t * x ^ t) := by
    intro t ht
    simp only [Finset.mem_range] at ht
    rw [toRaw_coeff_of_lt acc3 (by rw [ha3l]; omega),
      ← List.getD_eq_getElem (l := acc3.val) (d := cpoly.field.Ext4.ZERO)
        (by rw [ha3l]; omega), hco t ht, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun y' _ => by ring)
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  -- each pair's inner sum is the shifted range factor, by `rangeProduct_shift`
  have hpair : ∀ y' ∈ Finset.range eq.val.length,
      ∑ t ∈ Finset.range 32, HachiEquiv.SumcheckShift.eqF eq y'
          * (HachiEquiv.SumcheckShift.shiftCoeff (HachiEquiv.SumcheckShift.loF w y')
              (HachiEquiv.SumcheckShift.dF w y') t * x ^ t)
        = HachiEquiv.SumcheckShift.eqF eq y'
            * ArkLib.Lattices.Ajtai.InnerOuter.rangeProduct 16
                (HachiEquiv.SumcheckShift.loF w y' + HachiEquiv.SumcheckShift.dF w y' * x) := by
    intro y' _
    rw [← Finset.mul_sum, HachiEquiv.SumcheckShift.rangeProduct_shift]
  rw [Finset.sum_congr rfl hpair]
  -- and the pair sum over `range` is the specification's sum over `Fin (2^k)`
  rw [rangeSumZero]
  have hlen : eq.val.length = 2 ^ k := heq.1
  rw [hlen, ← Fin.sum_univ_eq_sum_range
    (fun y' => HachiEquiv.SumcheckShift.eqF eq y'
      * ArkLib.Lattices.Ajtai.InnerOuter.rangeProduct 16
          (HachiEquiv.SumcheckShift.loF w y' + HachiEquiv.SumcheckShift.dF w y' * x)) (2 ^ k)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have hlo : tableFn (m := k + 1) w (lo y) = HachiEquiv.SumcheckShift.loF w y.val := by
    rw [tableFn_apply, HachiEquiv.SumcheckShift.loF, lo]
  have hhi : tableFn (m := k + 1) w (hi y)
      = HachiEquiv.SumcheckShift.dF w y.val + HachiEquiv.SumcheckShift.loF w y.val := by
    rw [tableFn_apply, HachiEquiv.SumcheckShift.dF, HachiEquiv.SumcheckShift.loF, hi]
    ring
  have hfold : fold (tableFn (m := k + 1) w) x y
      = HachiEquiv.SumcheckShift.loF w y.val + HachiEquiv.SumcheckShift.dF w y.val * x := by
    rw [fold, hlo, hhi]; ring
  rw [hfold, tableFn_apply, HachiEquiv.SumcheckShift.eqF]

/-! ### The range summand at round 0, in the base field

`round_value_zero_base`, `round_values_zero_base` and `round_poly_zero_base` are
the three items above with the `w̃` table held as a `Vec<Fp>` and the fold and
the range factor carried out in `ZMod q` (candidate I). Every statement is the
extension-field one at the *embedded* table `φF ∘ tableFnFp w` and, for the
node, at `φF (toK node)`: nothing on the specification side moves, which is what
makes the peeled round 0 of `honest_round_messages` a placement change and not a
different computation.

Three steps are new and each is one line: `φF`'s `RingHom` maps for the fold,
`range_product_base_spec` (`lean/ZeroCheck.lean`) for the range factor computed
in `ZMod q`, and `fp_ext_mul_spec` (`lean/Ext.lean`) for the single mixed
product `p * eq[y]`. -/

/-- `round_value_zero_base` at one node is `rangeSumZero` at the embedded table
(spec: as `round_value_zero_spec`, one node of the `sumcheckPolyZero` summand's
`computableRoundPoly`, less the kernel's free factor). `w` carries `2^(k+1)`
base-field words and `eq` carries `2^k` extension entries: the fail points are
the reads `w[2y]`, `w[2y+1]` and `eq[y]`, all inside those lengths, and the `Fp`
arithmetic, which is total under `Red`. -/
theorem round_value_zero_base_spec {k : ℕ} (w : alloc.vec.Vec cpoly.field.Fp)
    (eq : alloc.vec.Vec cpoly.field.Ext4) (node : cpoly.field.Fp)
    (hw : WfEvalsFp (k + 1) w) (heq : WfEvals k eq) (hn : Red node) :
    sumcheck.round_value_zero_base w eq node
      ⦃ out => Reduced out ∧ toExt out =
        rangeSumZero (phiF ∘ tableFnFp (m := k + 1) w) (tableFn (m := k) eq)
          (phiF (toK node)) ⦄ := by
  obtain ⟨hwlen, hwred⟩ := hw
  obtain ⟨heqlen, heqred⟩ := heq
  have hR1 : Red cpoly.field.Fp.ONE := Red_one
  have hRZ : Reduced cpoly.field.Ext4.ZERO := reduced_ZERO
  have hwmax : w.val.length ≤ Usize.max := w.property
  rw [sumcheck.round_value_zero_base]
  step as ⟨om, hRom, hom⟩
  rw [sumcheck.round_value_zero_base_loop]
  apply loop.spec_decr_nat (fun s => 2 ^ k - s.2.val)
    (fun s => s.2.val ≤ 2 ^ k ∧ Reduced s.1 ∧
      toExt s.1 = ∑ y ∈ Finset.range s.2.val,
        InnerOuter.rangeProduct 16
            (phiF ((1 - toK node) * coeffK w (2 * y) + toK node * coeffK w (2 * y + 1)))
          * toExt (eq.val.getD y cpoly.field.Ext4.ZERO))
  · rintro ⟨acc, y⟩ ⟨hy, hRacc, hacc⟩
    dsimp only at hy hRacc hacc
    simp only [sumcheck.round_value_zero_base_loop.body]
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
      have hRlo0 : Red lo0 := hlo0 ▸ hwred _ (List.getElem_mem hib)
      step as ⟨i1, hi1⟩
      have hi1b : i1.val < w.val.length := by rw [hi1, hi]; omega
      step as ⟨hi0, hhi0⟩
      have hRhi0 : Red hi0 := hhi0 ▸ hwred _ (List.getElem_mem hi1b)
      step as ⟨f, hRf, hf⟩
      step as ⟨f1, hRf1, hf1⟩
      step as ⟨folded, hRfd, hfd⟩
      step with range_product_base_spec folded hRfd as ⟨p, hRp, hp⟩
      have hyb : y.val < eq.val.length := by omega
      step as ⟨e, he⟩
      have hRe : Reduced e := he ▸ heqred _ (List.getElem_mem hyb)
      step with fp_ext_mul_spec p e hRp hRe as ⟨e1, hRe1, he1⟩
      step as ⟨acc1, hRacc1, hacc1⟩
      step as ⟨y1, hy1⟩
      refine ⟨by scalar_tac, hRacc1, ?_, by scalar_tac⟩
      have he1' : toExt e1 = phiF (toK p) * toExt e := by rw [he1, phiF_apply]
      have hentry : toExt e1 = InnerOuter.rangeProduct 16
            (phiF ((1 - toK node) * coeffK w (2 * y.val)
              + toK node * coeffK w (2 * y.val + 1)))
          * toExt (eq.val.getD y.val cpoly.field.Ext4.ZERO) := by
        rw [he1', hp, hfd, hf, hf1, hom, toK_one, coeffK, coeffK, he, hlo0, hhi0,
          ← List.getD_eq_getElem eq.val cpoly.field.Ext4.ZERO hyb,
          ← List.getD_eq_getElem w.val cpoly.field.Fp.ZERO hib,
          ← List.getD_eq_getElem w.val cpoly.field.Fp.ZERO hi1b, hi1, hi]
      rw [hacc1, hacc, hy1, Finset.sum_range_succ, hentry]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hyeq : y.val = 2 ^ k := by
        have : eq.val.length ≤ y.val := by scalar_tac
        omega
      refine ⟨hRacc, ?_⟩
      rw [hacc, hyeq, rangeSumZeroFp_eq_sum_range]
  · exact ⟨by simp, hRZ, by simp⟩

/-- `round_values_zero_base`: the `33` node values of `rangeSumZero` at the
embedded nodes `Fp::new 0 … Fp::new 32`. The one step `round_values_zero_spec`
does not have is `φF (toK (Fp::new t)) = (t : F)` (`ofBase_natCast`,
`lean/ZeroCheck.lean`) -- the base-field path never builds the `Ext4` node. -/
theorem round_values_zero_base_spec {k : ℕ} (w : alloc.vec.Vec cpoly.field.Fp)
    (eq : alloc.vec.Vec cpoly.field.Ext4)
    (hw : WfEvalsFp (k + 1) w) (heq : WfEvals k eq) :
    sumcheck.round_values_zero_base w eq
      ⦃ out => out.val.length = 33 ∧ VecReduced out ∧
        ∀ t : Fin 33, toExt (out.val.getD t.val cpoly.field.Ext4.ZERO) =
          rangeSumZero (phiF ∘ tableFnFp (m := k + 1) w) (tableFn (m := k) eq)
            (t.val : F) ⦄ := by
  have hrn : (params.ROUND_NODES).val = 33 := by simp [params.ROUND_NODES]
  have hmax := usize_max_ge
  rw [sumcheck.round_values_zero_base, sumcheck.round_values_zero_base_loop]
  apply loop.spec_decr_nat (fun s => 33 - s.2.val)
    (fun s => s.2.val ≤ 33 ∧ s.1.val.length = s.2.val ∧ VecReduced s.1 ∧
      ∀ t : ℕ, t < s.2.val → toExt (s.1.val.getD t cpoly.field.Ext4.ZERO) =
        rangeSumZero (phiF ∘ tableFnFp (m := k + 1) w) (tableFn (m := k) eq) (t : F))
  · rintro ⟨v1, t1⟩ ⟨ht1, hlen1, hred1, hval1⟩
    dsimp only at ht1 hlen1 hred1 hval1
    simp only [sumcheck.round_values_zero_base_loop.body]
    by_cases hlt : t1 < params.ROUND_NODES
    · rw [if_pos hlt]
      have ht1lt : t1.val < 33 := by scalar_tac
      step with node_cast_spec t1 as ⟨u, hu⟩
      step with fp_new_spec u as ⟨nd, hRnd, hnd⟩
      step with round_value_zero_base_spec (k := k) w eq nd hw heq hRnd as ⟨e, hRe, he⟩
      have hbound : v1.val.length < Usize.max := by omega
      step as ⟨v2, hv2⟩
      step as ⟨t2, ht2⟩
      have ht2n : t2.val = t1.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, ?_, ?_, by scalar_tac⟩
      · rw [ht2n, hv2, List.length_append, hlen1]; simp
      · intro u' hu'
        rw [hv2] at hu'
        rcases List.mem_append.mp hu' with h | h
        · exact hred1 u' h
        · rw [List.mem_singleton.mp h]; exact hRe
      · intro t ht
        rw [ht2n] at ht
        rcases Nat.lt_or_ge t t1.val with htlt | htge
        · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = v1.val.length := by omega
          rw [hteq, hv2, getD_append_eq, he, hnd, hu, hlen1, phiF_apply, ofBase_natCast]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hteq : t1.val = 33 := by scalar_tac
      exact ⟨by rw [hlen1, hteq], hred1, fun t => hval1 t.val (by rw [hteq]; exact t.isLt)⟩
  · exact ⟨by simp, by simp, by intro u hu; simp at hu, by intro t ht; simp at ht⟩

/-- `round_poly_zero_base` interpolates the `33` base-field node values, and the
interpolant is `rangeSumZero` at the embedded table everywhere: the same
degree-`31 < 33` argument `round_poly_zero_spec` makes, at a different table. -/
theorem round_poly_zero_base_spec {k : ℕ} (w : alloc.vec.Vec cpoly.field.Fp)
    (eq : alloc.vec.Vec cpoly.field.Ext4)
    (hw : WfEvalsFp (k + 1) w) (heq : WfEvals k eq) :
    sumcheck.round_poly_zero_base w eq
      ⦃ out => out.val.length = 33 ∧ VecReduced out ∧
        ∀ x : F, CPolynomial.eval x (toUni out) =
          rangeSumZero (phiF ∘ tableFnFp (m := k + 1) w) (tableFn (m := k) eq) x ⦄ := by
  rw [sumcheck.round_poly_zero_base]
  simp only [alloc.vec.Vec.with_capacity]
  step with HachiEquiv.SumcheckShift.zero_fill_base_spec params.SHIFT_DEG
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize HachiEquiv.SumcheckShift.shift_deg_val
    (by simp) (by simp) (by intro a ha; simp at ha) (by intro t ht; simp at ht)
    as ⟨acc1, hacl, hacr, hacv⟩
  have hhalf : (alloc.vec.Vec.len eq).val = eq.val.length := by simp
  have hwl : w.val.length = 2 * eq.val.length := by
    rw [hw.1, heq.1, pow_succ]; ring
  step with HachiEquiv.SumcheckShift.pair_loop_base_spec w eq (alloc.vec.Vec.len eq)
    acc1 0#usize hhalf hwl hw.2 heq.2 (by simp) hacl hacr
    (by intro t ht; rw [hacv t ht]; simp)
    as ⟨acc2, ha2l, ha2r, ha2v⟩
  have hmax : acc2.val.length < Std.Usize.max := by
    rw [ha2l]; have := usize_max_ge'; omega
  step as ⟨acc3, ha3⟩
  rw [cpoly.univariate.UnivariatePoly.from_coeffs, WP.spec_ok]
  have ha3l : acc3.val.length = 33 := by
    rw [ha3, List.length_append, ha2l]; simp
  refine ⟨ha3l, ?_, fun x => ?_⟩
  · intro a ha
    rw [ha3] at ha
    rcases List.mem_append.mp ha with h | h
    · exact ha2r a h
    · rw [List.mem_singleton.mp h]; exact reduced_ZERO
  have hco : ∀ t, t < 32 → toExt (acc3.val.getD t cpoly.field.Ext4.ZERO)
      = ∑ y' ∈ Finset.range eq.val.length,
          phiF (HachiEquiv.SumcheckShift.shiftCoeffK (HachiEquiv.SumcheckShift.loK w y')
            (HachiEquiv.SumcheckShift.dK w y') t) * HachiEquiv.SumcheckShift.eqF eq y' := by
    intro t ht
    rw [ha3, HachiEquiv.GoldTransform.getD_append_lt' _ _ _ (by rw [ha2l]; exact ht),
      ha2v t ht, hhalf]
  have hco32 : toExt (acc3.val.getD 32 cpoly.field.Ext4.ZERO) = 0 := by
    rw [ha3, show (32 : ℕ) = acc2.val.length by rw [ha2l],
      HachiEquiv.GoldTransform.getD_append_eq']
    exact toExt_ZERO
  rw [toUni_eval, toRaw_eval_eq_sum acc3 x 33 (by rw [ha3l]), Finset.sum_range_succ]
  have hlast : (toRaw acc3).coeff 32 * x ^ 32 = 0 := by
    rw [toRaw_coeff_of_lt acc3 (by rw [ha3l]; norm_num),
      ← List.getD_eq_getElem (l := acc3.val) (d := cpoly.field.Ext4.ZERO)
        (by rw [ha3l]; norm_num), hco32]
    ring
  rw [hlast, add_zero]
  have hterm : ∀ t ∈ Finset.range 32, (toRaw acc3).coeff t * x ^ t
      = ∑ y' ∈ Finset.range eq.val.length,
          HachiEquiv.SumcheckShift.eqF eq y'
            * (HachiEquiv.SumcheckShift.shiftCoeff
                (phiF (HachiEquiv.SumcheckShift.loK w y'))
                (phiF (HachiEquiv.SumcheckShift.dK w y')) t * x ^ t) := by
    intro t ht
    simp only [Finset.mem_range] at ht
    rw [toRaw_coeff_of_lt acc3 (by rw [ha3l]; omega),
      ← List.getD_eq_getElem (l := acc3.val) (d := cpoly.field.Ext4.ZERO)
        (by rw [ha3l]; omega), hco t ht, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y' _ => ?_)
    rw [HachiEquiv.SumcheckShift.shiftCoeffK_phi]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  have hpair : ∀ y' ∈ Finset.range eq.val.length,
      ∑ t ∈ Finset.range 32, HachiEquiv.SumcheckShift.eqF eq y'
          * (HachiEquiv.SumcheckShift.shiftCoeff (phiF (HachiEquiv.SumcheckShift.loK w y'))
              (phiF (HachiEquiv.SumcheckShift.dK w y')) t * x ^ t)
        = HachiEquiv.SumcheckShift.eqF eq y'
            * ArkLib.Lattices.Ajtai.InnerOuter.rangeProduct 16
                (phiF (HachiEquiv.SumcheckShift.loK w y')
                  + phiF (HachiEquiv.SumcheckShift.dK w y') * x) := by
    intro y' _
    rw [← Finset.mul_sum, HachiEquiv.SumcheckShift.rangeProduct_shift]
  rw [Finset.sum_congr rfl hpair, rangeSumZero]
  have hlen : eq.val.length = 2 ^ k := heq.1
  rw [hlen, ← Fin.sum_univ_eq_sum_range
    (fun y' => HachiEquiv.SumcheckShift.eqF eq y'
      * ArkLib.Lattices.Ajtai.InnerOuter.rangeProduct 16
          (phiF (HachiEquiv.SumcheckShift.loK w y')
            + phiF (HachiEquiv.SumcheckShift.dK w y') * x)) (2 ^ k)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have hlo : (phiF ∘ tableFnFp (m := k + 1) w) (lo y)
      = phiF (HachiEquiv.SumcheckShift.loK w y.val) := by
    show phiF (tableFnFp (m := k + 1) w (lo y)) = _
    rw [tableFnFp_apply, HachiEquiv.SumcheckShift.loK, lo]
    rfl
  have hhi : (phiF ∘ tableFnFp (m := k + 1) w) (hi y)
      = phiF (HachiEquiv.SumcheckShift.dK w y.val) + phiF (HachiEquiv.SumcheckShift.loK w y.val) := by
    show phiF (tableFnFp (m := k + 1) w (hi y)) = _
    rw [tableFnFp_apply, HachiEquiv.SumcheckShift.dK, HachiEquiv.SumcheckShift.loK, hi,
      ← map_add]
    congr 1
    show toK (w.val.getD (2 * y.val + 1) cpoly.field.Fp.ZERO) = _
    rw [← coeffK]
    ring
  have hfold : fold (phiF ∘ tableFnFp (m := k + 1) w) x y
      = phiF (HachiEquiv.SumcheckShift.loK w y.val)
        + phiF (HachiEquiv.SumcheckShift.dK w y.val) * x := by
    rw [fold, hlo, hhi]; ring
  rw [hfold, tableFn_apply, HachiEquiv.SumcheckShift.eqF]

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

/-! ### The linear summand at round 0, in the base field

The `Ã` table carries `α` and `τ₁` and so stays in the extension from round 0
on; what moves into `ZMod q` is the `w̃` fold, and the product of the two folds
becomes one `Fp × Ext4` scaling. As on the zero side, the three statements are
the three above at the embedded table and the embedded node. -/

/-- `round_value_alpha_base` at one node is `linSumAlpha` at the embedded `w̃`
table (spec: as `round_value_alpha_spec`). The half-width is read off `w`, so
both tables carry `2^(k+1)` entries. -/
theorem round_value_alpha_base_spec {k : ℕ} (w : alloc.vec.Vec cpoly.field.Fp)
    (a_tab : alloc.vec.Vec cpoly.field.Ext4) (node : cpoly.field.Fp)
    (hw : WfEvalsFp (k + 1) w) (ha : WfEvals (k + 1) a_tab) (hn : Red node) :
    sumcheck.round_value_alpha_base w a_tab node
      ⦃ out => Reduced out ∧ toExt out =
        linSumAlpha (phiF ∘ tableFnFp (m := k + 1) w) (tableFn (m := k + 1) a_tab)
          (phiF (toK node)) ⦄ := by
  obtain ⟨hwlen, hwred⟩ := hw
  obtain ⟨halen, hared⟩ := ha
  have hR1 : Red cpoly.field.Fp.ONE := Red_one
  have hE1 : Reduced cpoly.field.Ext4.ONE := reduced_ONE
  have hRZ : Reduced cpoly.field.Ext4.ZERO := reduced_ZERO
  have hwmax : w.val.length ≤ Usize.max := w.property
  rw [sumcheck.round_value_alpha_base]
  step as ⟨half, hhalf⟩
  have hlenw : (alloc.vec.Vec.len w).val = w.val.length := by simp
  have hhalfv : half.val = 2 ^ k := by
    rw [hhalf, hlenw, hwlen, pow_succ]
    omega
  step as ⟨om, hRom, hom⟩
  step with ext_from_base_spec node hn as ⟨ne, hRne, hne⟩
  have hne' : toExt ne = phiF (toK node) := by rw [hne, phiF_apply]
  step as ⟨ome, hRome, home⟩
  rw [sumcheck.round_value_alpha_base_loop]
  apply loop.spec_decr_nat (fun s => 2 ^ k - s.2.val)
    (fun s => s.2.val ≤ 2 ^ k ∧ Reduced s.1 ∧
      toExt s.1 = ∑ y ∈ Finset.range s.2.val,
        phiF ((1 - toK node) * coeffK w (2 * y) + toK node * coeffK w (2 * y + 1)) *
          ((1 - phiF (toK node)) * toExt (a_tab.val.getD (2 * y) cpoly.field.Ext4.ZERO) +
            phiF (toK node) * toExt (a_tab.val.getD (2 * y + 1) cpoly.field.Ext4.ZERO)))
  · rintro ⟨acc, y⟩ ⟨hy, hRacc, hacc⟩
    dsimp only at hy hRacc hacc
    simp only [sumcheck.round_value_alpha_base_loop.body]
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
      have hRwlo : Red wlo := hwlo ▸ hwred _ (List.getElem_mem hib)
      step as ⟨f1, hRf1, hf1⟩
      step as ⟨i1, hi1⟩
      have hi1b : i1.val < w.val.length := by rw [hi1, hi]; omega
      step as ⟨whi, hwhi⟩
      have hRwhi : Red whi := hwhi ▸ hwred _ (List.getElem_mem hi1b)
      step as ⟨f3, hRf3, hf3⟩
      step as ⟨wf, hRwf, hwf⟩
      have hiba : i.val < a_tab.val.length := by rw [hi]; omega
      step as ⟨alo, halo⟩
      have hRalo : Reduced alo := halo ▸ hared _ (List.getElem_mem hiba)
      step as ⟨e1, hRe1, he1⟩
      step as ⟨i2, hi2⟩
      have hi2b : i2.val < a_tab.val.length := by rw [hi2, hi]; omega
      step as ⟨ahi, hahi⟩
      have hRahi : Reduced ahi := hahi ▸ hared _ (List.getElem_mem hi2b)
      step as ⟨e3, hRe3, he3⟩
      step as ⟨af, hRaf, haf⟩
      step with fp_ext_mul_spec wf af hRwf hRaf as ⟨e4, hRe4, he4⟩
      step as ⟨acc1, hRacc1, hacc1⟩
      step as ⟨y1, hy1⟩
      refine ⟨by scalar_tac, hRacc1, ?_, by scalar_tac⟩
      have he4' : toExt e4 = phiF (toK wf) * toExt af := by rw [he4, phiF_apply]
      have hentry : toExt e4 =
          phiF ((1 - toK node) * coeffK w (2 * y.val) + toK node * coeffK w (2 * y.val + 1)) *
            ((1 - phiF (toK node)) *
                toExt (a_tab.val.getD (2 * y.val) cpoly.field.Ext4.ZERO) +
              phiF (toK node) *
                toExt (a_tab.val.getD (2 * y.val + 1) cpoly.field.Ext4.ZERO)) := by
        rw [he4', hwf, hf1, hf3, hom, toK_one, haf, he1, he3, home, hne', toExt_ONE,
          coeffK, coeffK, hwlo, hwhi, halo, hahi,
          ← List.getD_eq_getElem w.val cpoly.field.Fp.ZERO hib,
          ← List.getD_eq_getElem w.val cpoly.field.Fp.ZERO hi1b,
          ← List.getD_eq_getElem a_tab.val cpoly.field.Ext4.ZERO hiba,
          ← List.getD_eq_getElem a_tab.val cpoly.field.Ext4.ZERO hi2b, hi1, hi2, hi]
      rw [hacc1, hacc, hy1, Finset.sum_range_succ, hentry]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hyeq : y.val = 2 ^ k := by
        have : half.val ≤ y.val := by scalar_tac
        omega
      refine ⟨hRacc, ?_⟩
      rw [hacc, hyeq, linSumAlphaFp_eq_sum_range]
  · exact ⟨by simp, hRZ, by simp⟩

/-- `round_values_alpha_base`: the `3` node values of `linSumAlpha` at the
embedded nodes `Fp::new 0, 1, 2`. -/
theorem round_values_alpha_base_spec {k : ℕ} (w : alloc.vec.Vec cpoly.field.Fp)
    (a_tab : alloc.vec.Vec cpoly.field.Ext4)
    (hw : WfEvalsFp (k + 1) w) (ha : WfEvals (k + 1) a_tab) :
    sumcheck.round_values_alpha_base w a_tab
      ⦃ out => out.val.length = 3 ∧ VecReduced out ∧
        ∀ t : Fin 3, toExt (out.val.getD t.val cpoly.field.Ext4.ZERO) =
          linSumAlpha (phiF ∘ tableFnFp (m := k + 1) w) (tableFn (m := k + 1) a_tab)
            (t.val : F) ⦄ := by
  have hrn : (params.ROUND_NODES_ALPHA).val = 3 := by simp [params.ROUND_NODES_ALPHA]
  have hmax := usize_max_ge
  rw [sumcheck.round_values_alpha_base, sumcheck.round_values_alpha_base_loop]
  apply loop.spec_decr_nat (fun s => 3 - s.2.val)
    (fun s => s.2.val ≤ 3 ∧ s.1.val.length = s.2.val ∧ VecReduced s.1 ∧
      ∀ t : ℕ, t < s.2.val → toExt (s.1.val.getD t cpoly.field.Ext4.ZERO) =
        linSumAlpha (phiF ∘ tableFnFp (m := k + 1) w) (tableFn (m := k + 1) a_tab) (t : F))
  · rintro ⟨v1, t1⟩ ⟨ht1, hlen1, hred1, hval1⟩
    dsimp only at ht1 hlen1 hred1 hval1
    simp only [sumcheck.round_values_alpha_base_loop.body]
    by_cases hlt : t1 < params.ROUND_NODES_ALPHA
    · rw [if_pos hlt]
      have ht1lt : t1.val < 3 := by scalar_tac
      step with node_cast_spec t1 as ⟨u, hu⟩
      step with fp_new_spec u as ⟨nd, hRnd, hnd⟩
      step with round_value_alpha_base_spec (k := k) w a_tab nd hw ha hRnd as ⟨e, hRe, he⟩
      have hbound : v1.val.length < Usize.max := by omega
      step as ⟨v2, hv2⟩
      step as ⟨t2, ht2⟩
      have ht2n : t2.val = t1.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, ?_, ?_, by scalar_tac⟩
      · rw [ht2n, hv2, List.length_append, hlen1]; simp
      · intro u' hu'
        rw [hv2] at hu'
        rcases List.mem_append.mp hu' with h | h
        · exact hred1 u' h
        · rw [List.mem_singleton.mp h]; exact hRe
      · intro t ht
        rw [ht2n] at ht
        rcases Nat.lt_or_ge t t1.val with htlt | htge
        · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = v1.val.length := by omega
          rw [hteq, hv2, getD_append_eq, he, hnd, hu, hlen1, phiF_apply, ofBase_natCast]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hteq : t1.val = 3 := by scalar_tac
      exact ⟨by rw [hlen1, hteq], hred1, fun t => hval1 t.val (by rw [hteq]; exact t.isLt)⟩
  · exact ⟨by simp, by simp, by intro u hu; simp at hu, by intro t ht; simp at ht⟩

/-- `round_poly_alpha_base` interpolates the `3` base-field node values, and the
interpolant is `linSumAlpha` at the embedded table everywhere (degree `≤ 2 < 3`,
as in `round_poly_alpha_spec`). -/
theorem round_poly_alpha_base_spec {k : ℕ} (w : alloc.vec.Vec cpoly.field.Fp)
    (a_tab : alloc.vec.Vec cpoly.field.Ext4)
    (hw : WfEvalsFp (k + 1) w) (ha : WfEvals (k + 1) a_tab) :
    sumcheck.round_poly_alpha_base w a_tab
      ⦃ out => out.val.length = 3 ∧ VecReduced out ∧
        ∀ x : F, CPolynomial.eval x (toUni out) =
          linSumAlpha (phiF ∘ tableFnFp (m := k + 1) w) (tableFn (m := k + 1) a_tab) x ⦄ := by
  rw [sumcheck.round_poly_alpha_base]
  step with round_values_alpha_base_spec (k := k) w a_tab hw ha as ⟨values, hvlen, hvred, hvval⟩
  step with round_node_weights_alpha_spec as ⟨weights, hwtlen, hwtred, hwtval⟩
  obtain ⟨p, hpdeg, hpval⟩ :=
    linSumAlpha_poly (phiF ∘ tableFnFp (m := k + 1) w) (tableFn (m := k + 1) a_tab)
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

/-! ## The public α table

`sumcheck::alpha_public_table`'s accepted champion (`hachi/src/sumcheck.rs:433`)
no longer calls `zerocheck::alpha_public_evals` per cube entry. It builds the
three tables `zerocheck::alpha_pow_table`, `zerocheck::eq_weight_table` and
`zerocheck::m_alpha_table` once -- whose specs are in `lean/ZeroCheck.lean` --
and reads them, so entry `idx` is `pw[idx % d] · Σ_i eqw[i] · mt[i][idx / d]`.
The headline statement below is unchanged from the frozen form; only the route
to it is new (opt: `HachiEquiv.Opt.alpha_public_table.opt`, `lean/Opt.lean`,
licensed by `alpha_public_table.opt_eq_spec`). -/

/-- The inner loop of `alpha_public_table`: the accumulator is the partial row
sum `Σ_{i' < i} eq̃(τ₁, i') · M̃_α(i', u)`.

The guard `u < cols` is the translation of a `getD … 0` off the end of a stored
row, and the statement carries **no** case split for it: past the stored columns
`mAlphaTilde` is itself `0` (`mAlphaTilde_eq_zero_of_ge`), so the skipped
summand and the computed summand agree, and the invariant is the same sum on
both sides of the guard. `hcols` is guarded by `0 < n` because at `n = 0` the
extracted `PolyMatrix::cols` reports `0` rather than `μ` and this loop never
runs. -/
theorem alpha_public_table_loop0_loop0_spec {n μ m₁ : ℕ}
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) (rows cols : Std.Usize)
    (eqw : alloc.vec.Vec cpoly.field.Ext4)
    (mt : alloc.vec.Vec (alloc.vec.Vec cpoly.field.Ext4)) (u : Std.Usize)
    (sum : cpoly.field.Ext4) (i : Std.Usize)
    (hrows : rows.val = n) (hcols : 0 < n → cols.val = μ + n * 8)
    (heqwlen : eqw.val.length = n) (heqwred : VecReduced eqw)
    (heqwval : ∀ t < n, toExt (eqw.val.getD t cpoly.field.Ext4.ZERO) =
      eqWeightVal (m₁ := m₁) tau1 t)
    (hmtlen : mt.val.length = n)
    (hmtval : ∀ (t : ℕ) (ht : t < n),
      (tableRow mt t).val.length = μ + n * 8 ∧ VecReduced (tableRow mt t) ∧
      ∀ c < μ + n * 8, toExt ((tableRow mt t).val.getD c cpoly.field.Ext4.ZERO) =
        InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨t, ht⟩ c)
    (hi : i.val ≤ n) (hRsum : Reduced sum)
    (hval : toExt sum = ∑ t ∈ Finset.range i.val,
      apTerm (m₁ := m₁) rs (toExt alpha) tau1 u.val t) :
    sumcheck.alpha_public_table_loop0_loop0 rows cols eqw mt u sum i
      ⦃ out => Reduced out ∧ toExt out = ∑ t ∈ Finset.range n,
        apTerm (m₁ := m₁) rs (toExt alpha) tau1 u.val t ⦄ := by
  rw [sumcheck.alpha_public_table_loop0_loop0]
  apply loop.spec_decr_nat (fun st => n - st.2.val)
    (fun st => st.2.val ≤ n ∧ Reduced st.1 ∧ toExt st.1 =
      ∑ t ∈ Finset.range st.2.val, apTerm (m₁ := m₁) rs (toExt alpha) tau1 u.val t)
  · rintro ⟨s1, i1⟩ ⟨hi1, hR1, hv1⟩
    dsimp only at hi1 hR1 hv1
    simp only [sumcheck.alpha_public_table_loop0_loop0.body]
    by_cases hlt : i1 < rows
    · rw [if_pos hlt]
      have hilt : i1.val < n := by rw [← hrows]; scalar_tac
      obtain ⟨hrlen, hrred, hrval⟩ := hmtval i1.val hilt
      have hiwlen : i1.val < eqw.val.length := by rw [heqwlen]; exact hilt
      have himlen : i1.val < mt.val.length := by rw [hmtlen]; exact hilt
      by_cases hltc : u < cols
      · rw [if_pos hltc]
        have hult : u.val < μ + n * 8 := by rw [← hcols (by omega)]; scalar_tac
        have hrowlen : u.val < (tableRow mt i1.val).val.length := by rw [hrlen]; exact hult
        step as ⟨e, he⟩
        have he' : e = eqw.val.getD i1.val cpoly.field.Ext4.ZERO := by
          rw [List.getD_eq_getElem _ _ hiwlen, he]
        have hRe : Reduced e := by
          rw [he]; exact heqwred _ (List.getElem_mem hiwlen)
        have hev : toExt e = eqWeightVal (m₁ := m₁) tau1 i1.val := by
          rw [he']; exact heqwval i1.val hilt
        step as ⟨v, hv⟩
        have hvrow : v.val = (tableRow mt i1.val).val := by
          rw [hv, tableRow, List.getD_eq_getElem _ _ himlen]
        have hulen : u.val < v.val.length := by rw [hvrow]; exact hrowlen
        step as ⟨e1, he1⟩
        have he1' : e1 = (tableRow mt i1.val).val.getD u.val cpoly.field.Ext4.ZERO := by
          rw [List.getD_eq_getElem _ _ hrowlen, he1, getElem_of_list_eq hvrow]
        have hRe1 : Reduced e1 := by
          rw [he1', List.getD_eq_getElem _ _ hrowlen]
          exact hrred _ (List.getElem_mem hrowlen)
        have he1v : toExt e1 =
            InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨i1.val, hilt⟩ u.val := by
          rw [he1']; exact hrval u.val hult
        step with ext_mul_spec e e1 hRe hRe1 as ⟨e2, hRe2, he2⟩
        step with ext_add_spec s1 e2 hR1 hRe2 as ⟨s2, hR2, hs2⟩
        step as ⟨i2, hi2⟩
        have hi2v : i2.val = i1.val + 1 := by scalar_tac
        refine ⟨by omega, hR2, ?_, by omega⟩
        rw [hs2, hv1, he2, hev, he1v, hi2v, Finset.sum_range_succ,
          apTerm_eq_mul rs (toExt alpha) tau1 u.val hilt]
      · rw [if_neg hltc]
        simp only [bind_tc_ok]
        have huge : μ + n * 8 ≤ u.val := by rw [← hcols (by omega)]; scalar_tac
        step as ⟨i2, hi2⟩
        have hi2v : i2.val = i1.val + 1 := by scalar_tac
        refine ⟨by omega, hR1, ?_, by omega⟩
        rw [hv1, hi2v, Finset.sum_range_succ,
          apTerm_eq_mul rs (toExt alpha) tau1 u.val hilt,
          mAlphaTilde_eq_zero_of_ge rs (toExt alpha) ⟨i1.val, hilt⟩ huge, MulZeroClass.mul_zero, add_zero]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n := by rw [← hrows] at hi1 ⊢; scalar_tac
      exact ⟨hR1, by rw [hv1, heq]⟩
  · exact ⟨hi, hRsum, hval⟩

/-- The outer loop of `alpha_public_table`: one cube entry per step, the power
read from the table and the row sum computed by the inner loop. -/
theorem alpha_public_table_loop0_spec {n μ m₀ m₁ : ℕ}
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) (rows cols sz : Std.Usize)
    (pw eqw : alloc.vec.Vec cpoly.field.Ext4)
    (mt : alloc.vec.Vec (alloc.vec.Vec cpoly.field.Ext4))
    (out : alloc.vec.Vec cpoly.field.Ext4) (idx : Std.Usize)
    (hrows : rows.val = n) (hcols : 0 < n → cols.val = μ + n * 8)
    (hsz : sz.val = 2 ^ m₀)
    (hpwlen : pw.val.length = N) (hpwred : VecReduced pw)
    (hpwval : ∀ l < N, toExt (pw.val.getD l cpoly.field.Ext4.ZERO) = toExt alpha ^ l)
    (heqwlen : eqw.val.length = n) (heqwred : VecReduced eqw)
    (heqwval : ∀ t < n, toExt (eqw.val.getD t cpoly.field.Ext4.ZERO) =
      eqWeightVal (m₁ := m₁) tau1 t)
    (hmtlen : mt.val.length = n)
    (hmtval : ∀ (t : ℕ) (ht : t < n),
      (tableRow mt t).val.length = μ + n * 8 ∧ VecReduced (tableRow mt t) ∧
      ∀ c < μ + n * 8, toExt ((tableRow mt t).val.getD c cpoly.field.Ext4.ZERO) =
        InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨t, ht⟩ c)
    (hidx : idx.val ≤ 2 ^ m₀) (hlen : out.val.length = idx.val) (hred : VecReduced out)
    (hval : ∀ t : Fin (2 ^ m₀), t.val < idx.val →
      toExt (out.val.getD t.val cpoly.field.Ext4.ZERO) =
        InnerOuter.alphaPublicEvals Φ m₀ m₁ phiF 16 rs (toExt alpha)
          (toPoint (m := m₁) tau1) (finFunctionFinEquiv.symm t)) :
    sumcheck.alpha_public_table_loop0 params.RING_DEGREE rows cols sz pw eqw mt out idx
      ⦃ o => o.val.length = 2 ^ m₀ ∧ VecReduced o ∧
        ∀ t : Fin (2 ^ m₀), toExt (o.val.getD t.val cpoly.field.Ext4.ZERO) =
          InnerOuter.alphaPublicEvals Φ m₀ m₁ phiF 16 rs (toExt alpha)
            (toPoint (m := m₁) tau1) (finFunctionFinEquiv.symm t) ⦄ := by
  have hrd : (params.RING_DEGREE).val = N := params_RING_DEGREE_val
  have hm0 : 2 ^ m₀ ≤ Usize.max := by rw [← hsz]; scalar_tac
  rw [sumcheck.alpha_public_table_loop0]
  apply loop.spec_decr_nat (fun st => 2 ^ m₀ - st.2.val)
    (fun st => st.2.val ≤ 2 ^ m₀ ∧ st.1.val.length = st.2.val ∧ VecReduced st.1 ∧
      ∀ t : Fin (2 ^ m₀), t.val < st.2.val →
        toExt (st.1.val.getD t.val cpoly.field.Ext4.ZERO) =
          InnerOuter.alphaPublicEvals Φ m₀ m₁ phiF 16 rs (toExt alpha)
            (toPoint (m := m₁) tau1) (finFunctionFinEquiv.symm t))
  · rintro ⟨v1, i1⟩ ⟨hi1, hlen1, hred1, hval1⟩
    dsimp only at hi1 hlen1 hred1 hval1
    simp only [sumcheck.alpha_public_table_loop0.body]
    by_cases hlt : i1 < sz
    · rw [if_pos hlt]
      have hilt : i1.val < 2 ^ m₀ := by rw [← hsz]; scalar_tac
      step as ⟨u, hu⟩
      have huv : u.val = i1.val / N := by rw [hu, hrd]
      step as ⟨l, hl⟩
      have hlv : l.val = i1.val % N := by rw [hl, hrd]
      step with alpha_public_table_loop0_loop0_spec (n := n) (μ := μ) (m₁ := m₁) rs alpha
        tau1 rows cols eqw mt u cpoly.field.Ext4.ZERO 0#usize hrows hcols heqwlen
        heqwred heqwval hmtlen hmtval (by simp) reduced_ZERO (by simp)
        as ⟨sum, hRsum, hsum⟩
      have hllen : l.val < pw.val.length := by
        rw [hpwlen, hlv]; exact Nat.mod_lt _ (by norm_num)
      step as ⟨e, he⟩
      have he' : e = pw.val.getD l.val cpoly.field.Ext4.ZERO := by
        rw [List.getD_eq_getElem _ _ hllen, he]
      have hRe : Reduced e := by rw [he]; exact hpwred _ (List.getElem_mem hllen)
      have hev : toExt e = toExt alpha ^ (i1.val % N) := by
        rw [he', hpwval l.val (by rw [hlv]; exact Nat.mod_lt _ (by norm_num)), hlv]
      step with ext_mul_spec e sum hRe hRsum as ⟨e1, hRe1, he1⟩
      have hentry : toExt e1 =
          InnerOuter.alphaPublicEvals Φ m₀ m₁ phiF 16 rs (toExt alpha)
            (toPoint (m := m₁) tau1) (finFunctionFinEquiv.symm ⟨i1.val, hilt⟩) := by
        rw [he1, hev, hsum, huv,
          alphaPublicEvals_eq_pow_mul_sum rs (toExt alpha) tau1 i1.val hilt]
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
        · rw [List.mem_singleton.mp h]; exact hRe1
      · intro t ht'
        rw [hi2n] at ht'
        rcases Nat.lt_or_ge t.val i1.val with htlt | htge
        · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t.val = v1.val.length := by omega
          rw [hteq, hv2, getD_append_eq, hentry]
          congr 2
          refine Fin.ext ?_
          show i1.val = t.val
          omega
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hieq : i1.val = 2 ^ m₀ := by rw [← hsz] at hi1 ⊢; scalar_tac
      exact ⟨by rw [hlen1, hieq], hred1, fun t => hval1 t (by rw [hieq]; exact t.isLt)⟩
  · exact ⟨hidx, hlen, hred, hval⟩

/-- `alpha_public_table` tabulates `alphaPublicEvals` over the `m₀`-cube, entry
`idx` at the point `finFunctionFinEquiv.symm idx` (spec: `alphaPublicEvals` as a
hypercube table). `2 ^ m₀ ≤ Usize.max` is `cube_size`'s; `hmax` is
`m_alpha_table_spec`'s -- the champion reaches `mAlphaTilde` through the table
rather than per entry, and the checked `mu + rows · δ` is formed in both. -/
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
  have hWm : WfRlinMat n μ s.m := hs.1
  have hgd : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  have hrd : (params.RING_DEGREE).val = N := params_RING_DEGREE_val
  rw [sumcheck.alpha_public_table]
  simp only [ringswitch.RlinStatement.impl.m, bind_tc_ok]
  step with ZeroCheck.rlin_rows_spec (n := n) (μ := μ) s.m hWm as ⟨rows, hrows⟩
  step with ZeroCheck.rlin_cols_le_spec (n := n) (μ := μ) s.m hWm as ⟨mu, hmule, hmu⟩
  have hmulbound : rows.val * (params.GADGET_DIGITS).val ≤ Usize.max := by
    rw [hrows, hgd]; omega
  step as ⟨j1, hj1⟩
  have hj1v : j1.val = n * 8 := by rw [hj1, hrows, hgd]
  have haddbound : mu.val + j1.val ≤ Usize.max := by rw [hj1v]; omega
  step as ⟨cols, hcols⟩
  have hcolsv : 0 < n → cols.val = μ + n * 8 := by
    intro hn; rw [hcols, hmu hn, hj1v]
  step with cube_size_spec m0 hm0 as ⟨sz, hsz⟩
  step with HachiEquiv.ZeroCheck.alpha_pow_table_spec alpha params.RING_DEGREE ha
    as ⟨pw, hpwlen, hpwred, hpwval⟩
  rw [hrd] at hpwlen hpwval
  step with eq_weight_table_spec (m₁ := m₁) tau1 rows ht
    as ⟨eqw, heqwlen, heqwred, heqwval⟩
  rw [hrows] at heqwlen heqwval
  step with m_alpha_table_spec (n := n) (μ := μ) s rs alpha hs ha hmax
    as ⟨mt, hmtlen, hmtval⟩
  step with alpha_public_table_loop0_spec (n := n) (μ := μ) (m₀ := m0.val) (m₁ := m₁) rs
    alpha tau1 rows cols sz pw eqw mt
    (alloc.vec.Vec.with_capacity cpoly.field.Ext4 sz) 0#usize hrows hcolsv hsz hpwlen
    hpwred hpwval heqwlen heqwred heqwval hmtlen hmtval (by simp)
    (by simp [alloc.vec.Vec.with_capacity])
    (by intro y hy; simp [alloc.vec.Vec.with_capacity] at hy)
    (by intro t ht'; simp at ht') as ⟨o, holen, hored, hoval⟩
  refine ⟨⟨holen, hored⟩, ?_⟩
  rw [toEvals]
  congr 1
  funext t
  exact hoval t

/-! ### `alpha_public_mle_eval`: the tensor split of `Ã` (candidate J)

`final_check` no longer builds the `2 ^ m₀` table and dots it against a
`2 ^ m₀`-entry Lagrange basis. `alphaPublicEvals` (`Constraints.lean:840`) reads
the flat cube index `idx = finFunctionFinEquiv x` only through `idx % d` and
`idx / d`, with `d = Φ.φ.natDegree = N = 2 ^ 10` at the pin, and
`finFunctionFinEquiv` is little-endian: the table is therefore a tensor product
of a function of the low `k = min m₀ 10` coordinates and a function of the high
`m₀ − k`, and a tensor product's multilinear extension is the product of the two
extensions. Two tables of `2 ^ 10` and `2 ^ (m₀ − 10)` entries and two layer
folds replace the `2 ^ m₀` table and the `2 ^ m₀` dot (opt:
`HachiEquiv.Opt.alpha_public_mle_eval.opt`, `lean/Opt.lean` § "Candidate J").

The pure algebra of the split lives here rather than in `lean/Opt.lean`, because
the spec layer below needs it and `Opt.lean` **imports** this file;
`alpha_public_mle_eval.opt_eq_spec` is stated there against these definitions,
exactly as `mAlphaTilde_eq_zero_of_ge` was moved into `lean/ZeroCheck.lean`. -/

/-! #### 1. Splitting the cube at coordinate `k`

`Fin m₀ → Fin 2` is the low block `Fin k → Fin 2` followed by the high block
`Fin (m₀ − k) → Fin 2`. The equivalence is written with an explicit `dif` on
`j < k` rather than through `Fin.append`, so that the two projection lemmas
below are `dif_pos` / `dif_neg` and no `Fin.cast` survives into the statements
the campaign reads. -/

/-- Coordinate `k + j` of the big cube: the `j`-th high coordinate. -/
def highIdx {m₀ k : ℕ} (hk : k ≤ m₀) (j : Fin (m₀ - k)) : Fin m₀ :=
  ⟨k + (j : ℕ), by have := j.isLt; omega⟩

@[simp] theorem highIdx_val {m₀ k : ℕ} (hk : k ≤ m₀) (j : Fin (m₀ - k)) :
    ((highIdx hk j : Fin m₀) : ℕ) = k + (j : ℕ) := rfl

/-- The cube point assembled from a low and a high block: coordinate `j` is read
from the low block when `j < k` and from the high block otherwise. -/
def cubeJoin {m₀ k : ℕ} (hk : k ≤ m₀) (xl : Fin k → Fin 2) (xh : Fin (m₀ - k) → Fin 2) :
    Fin m₀ → Fin 2 := fun j =>
  if h : (j : ℕ) < k then xl ⟨(j : ℕ), h⟩
  else xh ⟨(j : ℕ) - k, by have := j.isLt; omega⟩

/-- The low coordinates of an assembled cube point. -/
@[simp] theorem cubeJoin_low {m₀ k : ℕ} (hk : k ≤ m₀) (xl : Fin k → Fin 2)
    (xh : Fin (m₀ - k) → Fin 2) (j : Fin k) :
    cubeJoin hk xl xh (Fin.castLE hk j) = xl j := by
  rw [cubeJoin, dif_pos (show ((Fin.castLE hk j : Fin m₀) : ℕ) < k from j.isLt)]
  exact congrArg xl (Fin.ext rfl)

/-- The high coordinates of an assembled cube point. -/
@[simp] theorem cubeJoin_high {m₀ k : ℕ} (hk : k ≤ m₀) (xl : Fin k → Fin 2)
    (xh : Fin (m₀ - k) → Fin 2) (j : Fin (m₀ - k)) :
    cubeJoin hk xl xh (highIdx hk j) = xh j := by
  have hnot : ¬ ((highIdx hk j : Fin m₀) : ℕ) < k := by
    show ¬ k + (j : ℕ) < k
    omega
  rw [cubeJoin, dif_neg hnot]
  refine congrArg xh (Fin.ext ?_)
  show k + (j : ℕ) - k = (j : ℕ)
  omega

/-- The low/high decomposition of the Boolean cube at coordinate `k`. -/
def cubeSplit {m₀ k : ℕ} (hk : k ≤ m₀) :
    ((Fin k → Fin 2) × (Fin (m₀ - k) → Fin 2)) ≃ (Fin m₀ → Fin 2) where
  toFun p := cubeJoin hk p.1 p.2
  invFun x := (fun j => x (Fin.castLE hk j), fun j => x (highIdx hk j))
  left_inv := by
    intro p
    refine Prod.ext ?_ ?_ <;> funext j
    · exact cubeJoin_low hk p.1 p.2 j
    · exact cubeJoin_high hk p.1 p.2 j
  right_inv := by
    intro x
    funext j
    show cubeJoin hk (fun j => x (Fin.castLE hk j)) (fun j => x (highIdx hk j)) j = x j
    rw [cubeJoin]
    by_cases h : (j : ℕ) < k
    · rw [dif_pos h]
      exact congrArg x (Fin.ext rfl)
    · rw [dif_neg h]
      refine congrArg x (Fin.ext ?_)
      show k + ((j : ℕ) - k) = (j : ℕ)
      omega

@[simp] theorem cubeSplit_apply {m₀ k : ℕ} (hk : k ≤ m₀) (xl : Fin k → Fin 2)
    (xh : Fin (m₀ - k) → Fin 2) :
    cubeSplit hk (xl, xh) = cubeJoin hk xl xh := rfl

/-- The low coordinates of a split cube point. -/
theorem cubeSplit_low {m₀ k : ℕ} (hk : k ≤ m₀) (xl : Fin k → Fin 2)
    (xh : Fin (m₀ - k) → Fin 2) (j : Fin k) :
    cubeSplit hk (xl, xh) (Fin.castLE hk j) = xl j := cubeJoin_low hk xl xh j

/-- The high coordinates of a split cube point. -/
theorem cubeSplit_high {m₀ k : ℕ} (hk : k ≤ m₀) (xl : Fin k → Fin 2)
    (xh : Fin (m₀ - k) → Fin 2) (j : Fin (m₀ - k)) :
    cubeSplit hk (xl, xh) (highIdx hk j) = xh j := cubeJoin_high hk xl xh j

/-! #### 2. Sums and products over the split index

The `Fin m₀` index set is `Fin k ⊕ Fin (m₀ − k)` in the two shapes the proof
needs. Both are `Fin.sum_univ_add` / `Fin.prod_univ_add` transported along
`k + (m₀ − k) = m₀`. -/

theorem split_sum {M : Type*} [AddCommMonoid M] {m₀ k : ℕ} (hk : k ≤ m₀) (f : Fin m₀ → M) :
    ∑ i : Fin m₀, f i
      = (∑ j : Fin k, f (Fin.castLE hk j)) + ∑ j : Fin (m₀ - k), f (highIdx hk j) := by
  have h0 : k + (m₀ - k) = m₀ := by omega
  have e1 : ∑ i : Fin m₀, f i = ∑ i : Fin (k + (m₀ - k)), f (Fin.cast h0 i) :=
    (Fintype.sum_equiv (finCongr h0) (fun i => f (Fin.cast h0 i)) f (fun _ => rfl)).symm
  have hlow : ∀ i : Fin k, f (Fin.cast h0 (Fin.castAdd (m₀ - k) i)) = f (Fin.castLE hk i) :=
    fun i => congrArg f (Fin.ext rfl)
  have hhigh : ∀ i : Fin (m₀ - k), f (Fin.cast h0 (Fin.natAdd k i)) = f (highIdx hk i) :=
    fun i => congrArg f (Fin.ext rfl)
  rw [e1, Fin.sum_univ_add, Finset.sum_congr rfl (fun i _ => hlow i),
    Finset.sum_congr rfl (fun i _ => hhigh i)]

theorem split_prod {M : Type*} [CommMonoid M] {m₀ k : ℕ} (hk : k ≤ m₀) (f : Fin m₀ → M) :
    ∏ i : Fin m₀, f i
      = (∏ j : Fin k, f (Fin.castLE hk j)) * ∏ j : Fin (m₀ - k), f (highIdx hk j) := by
  have h0 : k + (m₀ - k) = m₀ := by omega
  have e1 : ∏ i : Fin m₀, f i = ∏ i : Fin (k + (m₀ - k)), f (Fin.cast h0 i) :=
    (Fintype.prod_equiv (finCongr h0) (fun i => f (Fin.cast h0 i)) f (fun _ => rfl)).symm
  have hlow : ∀ i : Fin k, f (Fin.cast h0 (Fin.castAdd (m₀ - k) i)) = f (Fin.castLE hk i) :=
    fun i => congrArg f (Fin.ext rfl)
  have hhigh : ∀ i : Fin (m₀ - k), f (Fin.cast h0 (Fin.natAdd k i)) = f (highIdx hk i) :=
    fun i => congrArg f (Fin.ext rfl)
  rw [e1, Fin.prod_univ_add, Finset.prod_congr rfl (fun i _ => hlow i),
    Finset.prod_congr rfl (fun i _ => hhigh i)]

/-- **The flat index of a split cube point.** `finFunctionFinEquiv` is
little-endian, so the low block contributes the low `k` bits and the high block
is scaled by `2 ^ k`. -/
theorem ffe_cubeSplit_val {m₀ k : ℕ} (hk : k ≤ m₀) (xl : Fin k → Fin 2)
    (xh : Fin (m₀ - k) → Fin 2) :
    ((finFunctionFinEquiv (cubeSplit hk (xl, xh)) : Fin (2 ^ m₀)) : ℕ)
      = ((finFunctionFinEquiv xl : Fin (2 ^ k)) : ℕ)
        + 2 ^ k * ((finFunctionFinEquiv xh : Fin (2 ^ (m₀ - k))) : ℕ) := by
  rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply, finFunctionFinEquiv_apply,
    split_sum hk (fun i : Fin m₀ => ((cubeSplit hk (xl, xh) i : Fin 2) : ℕ) * 2 ^ (i : ℕ)),
    Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [cubeSplit_low]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [cubeSplit_high, highIdx_val, pow_add]
    ring

/-! #### 3. The two halves of the point

`a_low` is `a` restricted to the first `k` coordinates, `a_high` to the rest --
the point the two folds consume, in the order the folds run (least significant
variable first, so the low block is folded first). -/

/-- The first `k` coordinates of the sumcheck point. -/
def splitLowPoint {m₀ k : ℕ} (hk : k ≤ m₀) (a : Fin m₀ → F) : Fin k → F :=
  fun j => a (Fin.castLE hk j)

/-- The last `m₀ − k` coordinates of the sumcheck point. -/
def splitHighPoint {m₀ k : ℕ} (hk : k ≤ m₀) (a : Fin m₀ → F) : Fin (m₀ - k) → F :=
  fun j => a (highIdx hk j)

/-! #### 4. The tensor-split lemma for multilinear extensions

Entirely generic: a Boolean table that factorizes along the cube split has a
multilinear extension that factorizes along the point split. Both sides go to
the `eq̃`-weighted cube sum (`eval_MLE_eq_sum`, `Constraints.lean:942`), the
cube is re-indexed by `cubeSplit`, and the Lagrange weight splits by
`split_prod`. -/

theorem mle_tensor_split {m₀ k : ℕ} (hk : k ≤ m₀) (L : Fin (2 ^ k) → F)
    (H : Fin (2 ^ (m₀ - k)) → F) (G : (Fin m₀ → Fin 2) → F) (a : Fin m₀ → F)
    (hG : ∀ (xl : Fin k → Fin 2) (xh : Fin (m₀ - k) → Fin 2),
        G (cubeSplit hk (xl, xh))
          = L (finFunctionFinEquiv xl) * H (finFunctionFinEquiv xh)) :
    MvPolynomial.eval (splitLowPoint hk a) (MvPolynomial.MLE' L)
        * MvPolynomial.eval (splitHighPoint hk a) (MvPolynomial.MLE' H)
      = MvPolynomial.eval a (MvPolynomial.MLE G) := by
  rw [MvPolynomial.MLE', MvPolynomial.MLE', InnerOuter.eval_MLE_eq_sum,
    InnerOuter.eval_MLE_eq_sum, InnerOuter.eval_MLE_eq_sum, Finset.sum_mul_sum,
    ← (cubeSplit hk).sum_comp (fun x => G x * ∏ i : Fin m₀, if x i = 1 then a i else 1 - a i),
    ← Finset.sum_product']
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨xl, xh⟩ := p
  rw [hG xl xh, split_prod hk (fun i : Fin m₀ =>
    if cubeSplit hk (xl, xh) i = 1 then a i else 1 - a i)]
  simp only [cubeSplit_low, cubeSplit_high, Function.comp_apply, splitLowPoint, splitHighPoint]
  ring

/-! #### 5. The two tables

`alphaLowTable` is the power table `α^ℓ` -- the specification's `alphaTilde`
(`Constraints.lean:502`), read as a `Fin (2 ^ k)`-indexed function so that the
campaign's fold specs, which consume `tableFn`-shaped functions, apply to it
directly. It is candidate C's `alphaPowTable` in `Fin`-function form, and
`HachiEquiv.Opt.alphaLowTable_eq_alphaPowTable` (`lean/Opt.lean`) is the bridge
to the list the Rust builds.

`alphaHighTable` is `alphaPublicEvals`'s inner sum, verbatim, at `idx / d := u`. -/

/-- The low factor: `α^ℓ` for `ℓ < 2 ^ k`. -/
def alphaLowTable (α : F) (k : ℕ) : Fin (2 ^ k) → F := fun l => α ^ (l : ℕ)
/-- The high factor: `∑ᵢ eq̃(τ₁,i) · M̃_α(i,u)` for `u < 2 ^ j`. The body is
`alphaPublicEvals`'s inner sum (`ZeroCheck/Constraints.lean:845-848`) with
`idx / d` replaced by `u`, copied verbatim including the `i < 2 ^ m₁` guard. -/
noncomputable def alphaHighTable {n μ m₁ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ)
    (α : F) (τ₁ : Fin m₁ → F) (j : ℕ) : Fin (2 ^ j) → F := fun u =>
  ∑ i : Fin n,
    (if hi : (i : ℕ) < 2 ^ m₁ then
      (∏ t : Fin m₁,
        if (finFunctionFinEquiv.symm ⟨(i : ℕ), hi⟩) t = 1 then τ₁ t else 1 - τ₁ t) *
          InnerOuter.mAlphaTilde Φ phiF 16 rs α i ((u : ℕ))
    else 0)

/-! #### 6. The split point

`k = min m₀ 10`: the low block is the `d = 2 ^ 10` coefficient coordinates, or
the whole cube when `m₀ < 10`. At the pin `m₀ = 26`, so `k = 10` and the high
block is `16` coordinates. -/

/-- `min m₀ 10 ≤ m₀`, the only side condition the split carries. -/
theorem alphaSplit_le (m₀ : ℕ) : min m₀ 10 ≤ m₀ := min_le_left _ _
/-! #### 7. `d = 2 ^ 10` at the pin, and the index split it licenses

`Φ.φ.natDegree = N = 1024` is `phi_natDegree` (`lean/RqBridge.lean:96`), which
is how `lean/Opt.lean` states everything at the pin's `Φ`
(`alpha_public_table.opt_eq_spec` uses the same rewrite). `N = 2 ^ 10` is
arithmetic. -/

theorem N_eq_two_pow : N = 2 ^ 10 := by norm_num

theorem phi_natDegree_eq_two_pow : Φ.φ.natDegree = 2 ^ 10 := by
  rw [phi_natDegree, N_eq_two_pow]

/-- The arithmetic of a little-endian two-block index, with no dependent types
in sight: the low block is recovered by `% d` and the high one by `/ d`, either
because the block boundary *is* `d` (`2 ^ k = d`, the pin's regime) or because
there is no high block at all (`hi = 0`, the `m₀ < 10` regime). -/
theorem split_mod_div_gen {K d : ℕ} (lo hi : ℕ) (hlo : lo < 2 ^ K) (hd : 2 ^ K ≤ d)
    (hcase : 2 ^ K = d ∨ hi = 0) :
    (lo + 2 ^ K * hi) % d = lo ∧ (lo + 2 ^ K * hi) / d = hi := by
  have hlod : lo < d := lt_of_lt_of_le hlo hd
  rcases hcase with hKd | hhi
  · subst hKd
    refine ⟨?_, ?_⟩
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
    · rw [Nat.add_mul_div_left _ _ ((by positivity : 0 < 2 ^ K)),
        Nat.div_eq_of_lt hlo, zero_add]
  · subst hhi
    rw [Nat.mul_zero, Nat.add_zero]
    exact ⟨Nat.mod_eq_of_lt hlod, Nat.div_eq_of_lt hlod⟩

/-- The two index readings at `k = min m₀ 10` and `d = 2 ^ 10`. Both regimes are
discharged: `m₀ ≥ 10` makes `2 ^ k = d` (the pin's case, `m₀ = 26`), and
`m₀ < 10` makes the high block a single point. -/
theorem split_mod_div {m₀ : ℕ} (xl : Fin (2 ^ min m₀ 10))
    (xh : Fin (2 ^ (m₀ - min m₀ 10))) :
    ((xl : ℕ) + 2 ^ min m₀ 10 * (xh : ℕ)) % 2 ^ 10 = (xl : ℕ)
      ∧ ((xl : ℕ) + 2 ^ min m₀ 10 * (xh : ℕ)) / 2 ^ 10 = (xh : ℕ) := by
  have hd : 2 ^ min m₀ 10 ≤ 2 ^ 10 :=
    Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)
  refine split_mod_div_gen (xl : ℕ) (xh : ℕ) xl.isLt hd ?_
  rcases Nat.lt_or_ge m₀ 10 with hm | hm
  · right
    have h2 : (xh : ℕ) < 2 ^ (m₀ - min m₀ 10) := xh.isLt
    have h3 : 2 ^ (m₀ - min m₀ 10) = 1 := by
      rw [show m₀ - min m₀ 10 = 0 from by omega]
      norm_num
    omega
  · left
    rw [min_eq_right hm]

/-! #### 8. The two spellings of a tabulated extension

`cMultilinearExtension` of a flat table and `MLE'` of it are the same
polynomial; the tensor split is written in the second spelling and the
specification in the first. -/

/-- `cMultilinearExtension` of a flat table is `MLE'` of it -- the one step
between the fold specs' spelling and § 4's. -/
theorem cMLE_flat_eq_MLE' {j : ℕ} (T : Fin (2 ^ j) → F) (z : Fin j → F) :
    (InnerOuter.cMultilinearExtension j (T ∘ finFunctionFinEquiv)).eval z
      = MvPolynomial.eval z (MvPolynomial.MLE' T) := by
  rw [InnerOuter.cMultilinearExtension_eval, MvPolynomial.MLE']

/-- **The split, against the specification.** The two-fold product is the
specification's multilinear extension of `alphaPublicEvals` at the point -- the
exact value `final_check` needs, and the right-hand side
`alpha_public_table_spec` plus a Lagrange dot used to reach.

Unconditional in `m₀`, `n`, `μ` and `m₁`: the `i < 2 ^ m₁` guard is carried by
`alphaHighTable` verbatim and the `m₀ < 10` regime is discharged in
`split_mod_div`. `HachiEquiv.Opt.alpha_public_mle_eval.opt_eq_spec` is this
lemma at the candidate's own definition. -/
theorem alphaSplit_eval_eq {n μ m₁ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ) (α : F)
    (τ₁ : Fin m₁ → F) (m₀ : ℕ) (a : Fin m₀ → F) :
    MvPolynomial.eval (splitLowPoint (alphaSplit_le m₀) a)
        (MvPolynomial.MLE' (alphaLowTable α (min m₀ 10)))
      * MvPolynomial.eval (splitHighPoint (alphaSplit_le m₀) a)
        (MvPolynomial.MLE' (alphaHighTable rs α τ₁ (m₀ - min m₀ 10)))
      = (InnerOuter.cMultilinearExtension m₀
          (InnerOuter.alphaPublicEvals Φ m₀ m₁ phiF 16 rs α τ₁)).eval a := by
  rw [InnerOuter.cMultilinearExtension_eval]
  refine mle_tensor_split (alphaSplit_le m₀) _ _ _ a ?_
  intro xl xh
  obtain ⟨hmod, hdiv⟩ := split_mod_div (m₀ := m₀) (finFunctionFinEquiv xl) (finFunctionFinEquiv xh)
  rw [InnerOuter.alphaPublicEvals]
  simp only [phi_natDegree_eq_two_pow, InnerOuter.alphaTilde]
  rw [ffe_cubeSplit_val (alphaSplit_le m₀) xl xh, hmod, hdiv]
  rfl

/-! #### 9. The two bridges the extracted loops need

The fold specs below conclude in `mleFold`, which `mleFold_eq_evalMle` and
CompPoly's `eval_mle_eq_eval` carry to `CMlPolynomialEval.eval`; the tensor split
above is phrased in `MvPolynomial.eval … (MLE' …)`. `eval_toEvals_eq_MLE'` is the
one step between them. `alphaHighTable_eq_apTerm_sum` is the other bridge: the
high table's entries as the row sum `alpha_public_table_loop0_loop0_spec` already
concludes. -/

/-- Strictly monotone powers of two, in the form the doubling loop's guards want
and with no lemma-name risk: `Nat.pow_le_pow_right` and arithmetic. -/
private theorem two_pow_lt_two_pow {i j : ℕ} (h : i < j) : (2 : ℕ) ^ i < 2 ^ j := by
  have h1 : (2 : ℕ) ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ] at h1
  have h2 : 0 < (2 : ℕ) ^ i := by positivity
  omega

/-- An extracted table folded over a whole point, in the `MLE'` spelling:
CompPoly's dot-product evaluator at a table whose entries are `T` is
`MvPolynomial.eval` of `T`'s multilinear extension. -/
theorem eval_toEvals_eq_MLE' {k : ℕ} (t : alloc.vec.Vec cpoly.field.Ext4)
    (T : Fin (2 ^ k) → F) (hT : ∀ y : Fin (2 ^ k), tableFn (m := k) t y = T y)
    (z : Fin k → F) :
    CMlPolynomialEval.eval (toEvals (m := k) t) (Vector.ofFn z)
      = MvPolynomial.eval z (MvPolynomial.MLE' T) := by
  have hv : toEvals (m := k) t
      = Vector.ofFn (fun i : Fin (2 ^ k) =>
          (T ∘ finFunctionFinEquiv) (finFunctionFinEquiv.symm i)) := by
    rw [toEvals]
    refine congrArg Vector.ofFn (funext fun i => ?_)
    show toExt (t.val.getD i.val cpoly.field.Ext4.ZERO)
      = T (finFunctionFinEquiv (finFunctionFinEquiv.symm i))
    rw [Equiv.apply_symm_apply, ← tableFn_apply]
    exact hT i
  rw [hv, CMlPolynomialEval.eval_eq_MvPolynomial_MLE, MvPolynomial.MLE']

/-- The high factor's entries are the row sum the extracted column loop
accumulates: `alphaHighTable` is `alphaPublicEvals`'s inner sum written with the
cube product, `apTerm` is the same summand written with cpoly's Lagrange basis,
and `lagrangeBasis_get_eq_cube_prod` is the one step between them. -/
theorem alphaHighTable_eq_apTerm_sum {n μ m₁ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ)
    (alpha : F) (tau1 : alloc.vec.Vec cpoly.field.Ext4) (j : ℕ) (u : Fin (2 ^ j)) :
    alphaHighTable rs alpha (toPoint (m := m₁) tau1) j u
      = ∑ t ∈ Finset.range n, apTerm (m₁ := m₁) rs alpha tau1 (u : ℕ) t := by
  rw [alphaHighTable, sum_fin_eq_sum_range_dite]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htn : t < n := Finset.mem_range.mp ht
  rw [dif_pos htn, apTerm, dif_pos htn]
  by_cases hb : t < 2 ^ m₁
  · rw [dif_pos hb, dif_pos hb, lagrangeBasis_get_eq_cube_prod]
  · rw [dif_neg hb, dif_neg hb]

/-! #### 10. The extracted item, loop by loop -/

/-- Loop 0 of `alpha_public_mle_eval`: the `k`/`sz` doubling that computes
`k = min m₀ (log₂ d)` and `sz = 2 ^ k` without ever forming a power.

`d = N = 2 ^ 10` at the pin, so the loop stops either because the whole cube is
"low" (`k = m₀`, the `m₀ < 10` regime) or because `sz` has reached `d`
(`k = 10`). `sz` never overflows: it doubles only while `sz < d`, so it stays
`≤ d`, and `d` is a `usize` literal. -/
theorem alpha_public_mle_eval_loop0_spec (m0 k sz : Std.Usize)
    (hk : k.val ≤ min m0.val 10) (hsz : sz.val = 2 ^ k.val) :
    sumcheck.alpha_public_mle_eval_loop0 params.RING_DEGREE m0 k sz
      ⦃ (k', sz') => k'.val = min m0.val 10 ∧ sz'.val = 2 ^ k'.val ⦄ := by
  have hrd : (params.RING_DEGREE).val = N := params_RING_DEGREE_val
  have hNmax : N ≤ Usize.max := by
    have hb : (params.RING_DEGREE).val ≤ Usize.max := by
      simp only [params.RING_DEGREE]; scalar_tac
    omega
  have hN : N = 2 ^ 10 := N_eq_two_pow
  rw [sumcheck.alpha_public_mle_eval_loop0]
  apply loop.spec_decr_nat (fun st => min m0.val 10 - st.1.val)
    (fun st => st.1.val ≤ min m0.val 10 ∧ st.2.val = 2 ^ st.1.val)
  · rintro ⟨k1, s1⟩ ⟨hk1, hs1⟩
    dsimp only at hk1 hs1
    simp only [sumcheck.alpha_public_mle_eval_loop0.body]
    by_cases hlt : k1 < m0
    · rw [if_pos hlt]
      have hklt : k1.val < m0.val := by scalar_tac
      by_cases hlt2 : s1 < params.RING_DEGREE
      · rw [if_pos hlt2]
        have hsltN : s1.val < N := by rw [← hrd]; scalar_tac
        have hk10 : k1.val < 10 := by
          rcases Nat.lt_or_ge k1.val 10 with h | h
          · exact h
          · exact absurd hsltN (by
              have h1 : (2 : ℕ) ^ 10 ≤ 2 ^ k1.val := Nat.pow_le_pow_right (by norm_num) h
              omega)
        have hdouble : s1.val * 2 = 2 ^ (k1.val + 1) := by rw [pow_succ, hs1]
        have hle : s1.val * 2 ≤ N := by
          rw [hdouble, hN]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        have hbound : s1.val * 2 ≤ Usize.max := le_trans hle hNmax
        step as ⟨s2, hs2⟩
        have hs2v : s2.val = 2 ^ (k1.val + 1) := by rw [← hdouble]; scalar_tac
        step as ⟨k2, hk2⟩
        have hk2v : k2.val = k1.val + 1 := by scalar_tac
        refine ⟨by omega, ?_, by omega⟩
        rw [hs2v, hk2v]
      · rw [if_neg hlt2, WP.spec_ok]
        dsimp only
        have hsgeN : N ≤ s1.val := by rw [← hrd]; scalar_tac
        have h10 : 10 ≤ k1.val := by
          rcases Nat.lt_or_ge k1.val 10 with h | h
          · exact absurd hsgeN (by
              have h1 : (2 : ℕ) ^ k1.val < 2 ^ 10 := two_pow_lt_two_pow h
              omega)
          · exact h
        exact ⟨by omega, hs1⟩
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hge : m0.val ≤ k1.val := by scalar_tac
      exact ⟨by omega, hs1⟩
  · exact ⟨hk, hsz⟩

/-- Loop 1 of `alpha_public_mle_eval`: the low table folded over the point's
first `k` coordinates, one `eval_mle_layer` per coordinate.

Same shape as `w_table_mle_eval_loop_spec` (`lean/ZeroCheck.lean`) -- the answer
travels as the parameter `tgt`, so the invariant is an equation between two
closed terms rather than a statement about a table whose arity moves -- with one
difference: `a` is the **whole** sumcheck point and only its first `k`
coordinates are consumed, so the hypothesis is `k ≤ a.val.length` rather than an
equality. -/
theorem alpha_public_mle_eval_loop1_spec {k : ℕ} (a : alloc.vec.Vec cpoly.field.Ext4)
    (kk : Std.Usize) (cur : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize) (tgt : F)
    (hared : VecReduced a) (halen : k ≤ a.val.length) (hkk : kk.val = k) (hj : j.val ≤ k)
    (hcur : WfEvals (k - j.val) cur)
    (hinv : mleFold (k - j.val) (toEvals (m := k - j.val) cur)
      (fun i => ptFlat a (j.val + i)) = tgt) :
    sumcheck.alpha_public_mle_eval_loop1 a kk cur j
      ⦃ o => o.val.length = 1 ∧ VecReduced o ∧
        toExt (o.val.getD 0 cpoly.field.Ext4.ZERO) = tgt ⦄ := by
  rw [sumcheck.alpha_public_mle_eval_loop1]
  apply loop.spec_decr_nat (fun s => k - s.2.val)
    (fun s => s.2.val ≤ k ∧ WfEvals (k - s.2.val) s.1 ∧
      mleFold (k - s.2.val) (toEvals (m := k - s.2.val) s.1)
        (fun i => ptFlat a (s.2.val + i)) = tgt)
  · rintro ⟨c1, j1⟩ ⟨hj1, hc1, hinv1⟩
    dsimp only at hj1 hc1 hinv1
    simp only [sumcheck.alpha_public_mle_eval_loop1.body]
    by_cases hlt : j1 < kk
    · rw [if_pos hlt]
      have hjlt : j1.val < k := by rw [← hkk]; scalar_tac
      have halt : j1.val < a.val.length := by omega
      obtain ⟨k', hkeq⟩ : ∃ k', k - j1.val = k' + 1 := ⟨k - j1.val - 1, by omega⟩
      rw [hkeq] at hc1 hinv1
      step as ⟨e, he⟩
      have hRe : Reduced e := by rw [he]; exact hared _ (List.getElem_mem halt)
      have hev : ptFlat a j1.val = toExt e := by
        rw [ptFlat, List.getD_eq_getElem _ _ halt, he]
      step with eval_mle_layer_spec (k := k') c1 e hc1 hRe as ⟨c2, hc2, hfold⟩
      step as ⟨j2, hj2⟩
      have hj2v : j2.val = j1.val + 1 := by scalar_tac
      have hkeq2 : k - j2.val = k' := by omega
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
      have hjeq : j1.val = k := by rw [← hkk] at hj1 ⊢; scalar_tac
      rw [hjeq, Nat.sub_self] at hc1 hinv1
      obtain ⟨hclen, hcred⟩ := hc1
      refine ⟨by simpa using hclen, hcred, ?_⟩
      rw [← hinv1]
      simp only [mleFold]
      exact (tableFn_apply (m := 0) c1 ⟨0, by norm_num⟩).symm
  · exact ⟨hj, hcur, hinv⟩

/-- The inner loop of loop 2: the partial row sum `Σ_{i' < i} eq̃(τ₁, i') ·
M̃_α(i', u)`, the same column contraction `alpha_public_table` runs.

The extracted body is *identical* to `alpha_public_table_loop0_loop0`'s -- same
guard, same arguments, same order -- so the statement and the proof are that
loop's, transported across the two names. -/
theorem alpha_public_mle_eval_loop2_loop0_spec {n μ m₁ : ℕ}
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) (rows cols : Std.Usize)
    (eqw : alloc.vec.Vec cpoly.field.Ext4)
    (mt : alloc.vec.Vec (alloc.vec.Vec cpoly.field.Ext4)) (u : Std.Usize)
    (sum : cpoly.field.Ext4) (i : Std.Usize)
    (hrows : rows.val = n) (hcols : 0 < n → cols.val = μ + n * 8)
    (heqwlen : eqw.val.length = n) (heqwred : VecReduced eqw)
    (heqwval : ∀ t < n, toExt (eqw.val.getD t cpoly.field.Ext4.ZERO) =
      eqWeightVal (m₁ := m₁) tau1 t)
    (hmtlen : mt.val.length = n)
    (hmtval : ∀ (t : ℕ) (ht : t < n),
      (tableRow mt t).val.length = μ + n * 8 ∧ VecReduced (tableRow mt t) ∧
      ∀ c < μ + n * 8, toExt ((tableRow mt t).val.getD c cpoly.field.Ext4.ZERO) =
        InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨t, ht⟩ c)
    (hi : i.val ≤ n) (hRsum : Reduced sum)
    (hval : toExt sum = ∑ t ∈ Finset.range i.val,
      apTerm (m₁ := m₁) rs (toExt alpha) tau1 u.val t) :
    sumcheck.alpha_public_mle_eval_loop2_loop0 rows cols eqw mt u sum i
      ⦃ out => Reduced out ∧ toExt out = ∑ t ∈ Finset.range n,
        apTerm (m₁ := m₁) rs (toExt alpha) tau1 u.val t ⦄ := by
  have hsame : sumcheck.alpha_public_mle_eval_loop2_loop0 rows cols eqw mt u sum i
      = sumcheck.alpha_public_table_loop0_loop0 rows cols eqw mt u sum i := rfl
  rw [hsame]
  exact alpha_public_table_loop0_loop0_spec (m₁ := m₁) rs alpha tau1 rows cols eqw mt u sum i
    hrows hcols heqwlen heqwred heqwval hmtlen hmtval hi hRsum hval

/-- Loop 2 of `alpha_public_mle_eval`: one column of the high table per step,
each the row sum the inner loop computes. `2 ^ j` columns, not `2 ^ m₀` cube
entries, and no power table is read -- the `α^ℓ` factor belongs to the low half
of the split. -/
theorem alpha_public_mle_eval_loop2_spec {n μ j m₁ : ℕ}
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) (rows cols hsz : Std.Usize)
    (eqw : alloc.vec.Vec cpoly.field.Ext4)
    (mt : alloc.vec.Vec (alloc.vec.Vec cpoly.field.Ext4))
    (out : alloc.vec.Vec cpoly.field.Ext4) (u : Std.Usize)
    (hrows : rows.val = n) (hcols : 0 < n → cols.val = μ + n * 8)
    (hhsz : hsz.val = 2 ^ j)
    (heqwlen : eqw.val.length = n) (heqwred : VecReduced eqw)
    (heqwval : ∀ t < n, toExt (eqw.val.getD t cpoly.field.Ext4.ZERO) =
      eqWeightVal (m₁ := m₁) tau1 t)
    (hmtlen : mt.val.length = n)
    (hmtval : ∀ (t : ℕ) (ht : t < n),
      (tableRow mt t).val.length = μ + n * 8 ∧ VecReduced (tableRow mt t) ∧
      ∀ c < μ + n * 8, toExt ((tableRow mt t).val.getD c cpoly.field.Ext4.ZERO) =
        InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨t, ht⟩ c)
    (hu : u.val ≤ 2 ^ j) (hlen : out.val.length = u.val) (hred : VecReduced out)
    (hval : ∀ t < u.val, toExt (out.val.getD t cpoly.field.Ext4.ZERO) =
      ∑ t' ∈ Finset.range n, apTerm (m₁ := m₁) rs (toExt alpha) tau1 t t') :
    sumcheck.alpha_public_mle_eval_loop2 rows cols hsz eqw mt out u
      ⦃ o => o.val.length = 2 ^ j ∧ VecReduced o ∧
        ∀ t < 2 ^ j, toExt (o.val.getD t cpoly.field.Ext4.ZERO) =
          ∑ t' ∈ Finset.range n, apTerm (m₁ := m₁) rs (toExt alpha) tau1 t t' ⦄ := by
  have hjmax : 2 ^ j ≤ Usize.max := by rw [← hhsz]; scalar_tac
  rw [sumcheck.alpha_public_mle_eval_loop2]
  apply loop.spec_decr_nat (fun st => 2 ^ j - st.2.val)
    (fun st => st.2.val ≤ 2 ^ j ∧ st.1.val.length = st.2.val ∧ VecReduced st.1 ∧
      ∀ t < st.2.val, toExt (st.1.val.getD t cpoly.field.Ext4.ZERO) =
        ∑ t' ∈ Finset.range n, apTerm (m₁ := m₁) rs (toExt alpha) tau1 t t')
  · rintro ⟨v1, u1⟩ ⟨hu1, hlen1, hred1, hval1⟩
    dsimp only at hu1 hlen1 hred1 hval1
    simp only [sumcheck.alpha_public_mle_eval_loop2.body]
    by_cases hlt : u1 < hsz
    · rw [if_pos hlt]
      have hult : u1.val < 2 ^ j := by rw [← hhsz]; scalar_tac
      step with alpha_public_mle_eval_loop2_loop0_spec (n := n) (μ := μ) (m₁ := m₁) rs alpha
        tau1 rows cols eqw mt u1 cpoly.field.Ext4.ZERO 0#usize hrows hcols heqwlen
        heqwred heqwval hmtlen hmtval (by simp) reduced_ZERO (by simp)
        as ⟨sum, hRsum, hsum⟩
      have hbound : v1.val.length < Usize.max := by omega
      step as ⟨v2, hv2⟩
      step as ⟨u2, hu2⟩
      have hu2n : u2.val = u1.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · rw [hu2n, hv2, List.length_append, hlen1]; simp
      · intro y hy
        rw [hv2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hred1 y h
        · rw [List.mem_singleton.mp h]; exact hRsum
      · intro t ht'
        rw [hu2n] at ht'
        rcases Nat.lt_or_ge t u1.val with htlt | htge
        · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = v1.val.length := by omega
          rw [hteq, hv2, getD_append_eq, hsum, hlen1]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hueq : u1.val = 2 ^ j := by rw [← hhsz] at hu1 ⊢; scalar_tac
      exact ⟨by rw [hlen1, hueq], hred1, by rw [← hueq]; exact hval1⟩
  · exact ⟨hu, hlen, hred, hval⟩

/-- Loop 3 of `alpha_public_mle_eval`: the high table folded over the point's
last `m₀ − k` coordinates. The extracted body is identical to loop 1's, so the
statement and the proof are that loop's, transported across the two names -- the
only difference is where the counter starts. -/
theorem alpha_public_mle_eval_loop3_spec {m₀ : ℕ} (a : alloc.vec.Vec cpoly.field.Ext4)
    (mm : Std.Usize) (cur : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize) (tgt : F)
    (hared : VecReduced a) (halen : m₀ ≤ a.val.length) (hmm : mm.val = m₀) (hj : j.val ≤ m₀)
    (hcur : WfEvals (m₀ - j.val) cur)
    (hinv : mleFold (m₀ - j.val) (toEvals (m := m₀ - j.val) cur)
      (fun i => ptFlat a (j.val + i)) = tgt) :
    sumcheck.alpha_public_mle_eval_loop3 a mm cur j
      ⦃ o => o.val.length = 1 ∧ VecReduced o ∧
        toExt (o.val.getD 0 cpoly.field.Ext4.ZERO) = tgt ⦄ := by
  have hsame : sumcheck.alpha_public_mle_eval_loop3 a mm cur j
      = sumcheck.alpha_public_mle_eval_loop1 a mm cur j := rfl
  rw [hsame]
  exact alpha_public_mle_eval_loop1_spec (k := m₀) a mm cur j tgt hared halen hmm hj hcur hinv

/-- `alpha_public_mle_eval` evaluates the multilinear extension of the public
table `Ã` at the sumcheck point -- the same value `alpha_public_table` followed
by cpoly's Lagrange dot produces, computed from two tables of `2 ^ min m₀ 10`
and `2 ^ (m₀ − min m₀ 10)` entries instead of `2 ^ m₀` of them (opt:
`HachiEquiv.Opt.alpha_public_mle_eval.opt`, licensed by
`alpha_public_mle_eval.opt_eq_spec`, which is `alphaSplit_eval_eq` above).

Hypotheses are `alpha_public_table_spec`'s, and for the same reasons.
`2 ^ m₀ ≤ Usize.max` is `cube_size`'s: the high block's size is formed by
doubling, and `2 ^ (m₀ − k) ≤ 2 ^ m₀` is what bounds it. `hmax` is
`m_alpha_table_spec`'s -- the checked `mu + rows · δ` is formed here too.
`WfPoint m₀ a` is what pins `m₀`, which the extracted code reads off `a.len()`
rather than taking as an argument; the reducedness half is what the two folds
need of the point's coordinates. -/
theorem alpha_public_mle_eval_spec {n μ m₀ m₁ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (tau1 a : alloc.vec.Vec cpoly.field.Ext4)
    (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha) (ht : WfPoint m₁ tau1)
    (hpt : WfPoint m₀ a) (hm0 : 2 ^ m₀ ≤ Usize.max) (hmax : μ + n * 8 ≤ Usize.max) :
    sumcheck.alpha_public_mle_eval s alpha tau1 a
      ⦃ out => Reduced out ∧ toExt out =
        (InnerOuter.cMultilinearExtension m₀
          (InnerOuter.alphaPublicEvals Φ m₀ m₁ phiF 16 rs (toExt alpha)
            (toPoint (m := m₁) tau1))).eval (toPoint (m := m₀) a) ⦄ := by
  have hWm : WfRlinMat n μ s.m := hs.1
  have hgd : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  have halen : a.val.length = m₀ := hpt.1
  have hared : VecReduced a := hpt.2
  have hm0v : (alloc.vec.Vec.len a).val = m₀ := by simpa using halen
  have hklem : min m₀ 10 ≤ m₀ := alphaSplit_le m₀
  have h0 : (0#usize : Std.Usize).val = 0 := by simp
  -- the two factors the tensor split names
  set tlow : F := MvPolynomial.eval (splitLowPoint (alphaSplit_le m₀) (toPoint (m := m₀) a))
    (MvPolynomial.MLE' (alphaLowTable (toExt alpha) (min m₀ 10))) with htlowdef
  set thigh : F := MvPolynomial.eval (splitHighPoint (alphaSplit_le m₀) (toPoint (m := m₀) a))
    (MvPolynomial.MLE' (alphaHighTable rs (toExt alpha) (toPoint (m := m₁) tau1)
      (m₀ - min m₀ 10))) with hthighdef
  rw [sumcheck.alpha_public_mle_eval]
  simp only [ringswitch.RlinStatement.impl.m, bind_tc_ok]
  step with ZeroCheck.rlin_rows_spec (n := n) (μ := μ) s.m hWm as ⟨rows, hrows⟩
  step with ZeroCheck.rlin_cols_le_spec (n := n) (μ := μ) s.m hWm as ⟨mu, hmule, hmu⟩
  have hmulbound : rows.val * (params.GADGET_DIGITS).val ≤ Usize.max := by
    rw [hrows, hgd]; omega
  step as ⟨j1, hj1⟩
  have hj1v : j1.val = n * 8 := by rw [hj1, hrows, hgd]
  have haddbound : mu.val + j1.val ≤ Usize.max := by rw [hj1v]; omega
  step as ⟨cols, hcols⟩
  have hcolsv : 0 < n → cols.val = μ + n * 8 := by
    intro hn; rw [hcols, hmu hn, hj1v]
  step with alpha_public_mle_eval_loop0_spec (alloc.vec.Vec.len a) 0#usize 1#usize
    (by simp) (by simp) as ⟨kv, szv, hkv, hszv⟩
  rw [hm0v] at hkv
  rw [hkv] at hszv
  step with HachiEquiv.ZeroCheck.alpha_pow_table_spec alpha szv ha
    as ⟨low, hlowlen, hlowred, hlowval⟩
  rw [hszv] at hlowlen hlowval
  have hWlow : WfEvals (min m₀ 10) low := ⟨hlowlen, hlowred⟩
  have hlowtab : ∀ y : Fin (2 ^ min m₀ 10), tableFn (m := min m₀ 10) low y
      = alphaLowTable (toExt alpha) (min m₀ 10) y := by
    intro y
    rw [tableFn_apply, alphaLowTable]
    exact hlowval y.val y.isLt
  have htlow : mleFold (min m₀ 10) (toEvals (m := min m₀ 10) low)
      (fun i => ptFlat a i) = tlow := by
    rw [mleFold_eq_evalMle, CMlPolynomialEval.eval_mle_eq_eval, htlowdef]
    rw [show (Vector.ofFn (fun i : Fin (min m₀ 10) => ptFlat a i.val))
        = Vector.ofFn (splitLowPoint (alphaSplit_le m₀) (toPoint (m := m₀) a)) from
      congrArg Vector.ofFn (funext fun i => by
        simp only [ptFlat, splitLowPoint, toPoint]
        rfl)]
    exact eval_toEvals_eq_MLE' low _ hlowtab _
  step with alpha_public_mle_eval_loop1_spec (k := min m₀ 10) a kv low 0#usize tlow
    hared (by omega) hkv (by simp)
    (by simp only [h0, Nat.sub_zero]; exact hWlow)
    (by simp only [h0, Nat.zero_add]; exact htlow)
    as ⟨low1, hlow1len, hlow1red, hlow1val⟩
  have hsub : (alloc.vec.Vec.len a).val - kv.val ≤ Usize.max := by scalar_tac
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = m₀ - min m₀ 10 := by rw [hi2, hm0v, hkv]
  step with cube_size_spec i2 (by
    rw [hi2v]
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hm0) as ⟨hsz, hhsz⟩
  rw [hi2v] at hhsz
  step with eq_weight_table_spec (m₁ := m₁) tau1 rows ht
    as ⟨eqw, heqwlen, heqwred, heqwval⟩
  rw [hrows] at heqwlen heqwval
  step with m_alpha_table_spec (n := n) (μ := μ) s rs alpha hs ha hmax
    as ⟨mt, hmtlen, hmtval⟩
  step with alpha_public_mle_eval_loop2_spec (n := n) (μ := μ) (j := m₀ - min m₀ 10)
    (m₁ := m₁) rs alpha tau1 rows cols hsz eqw mt
    (alloc.vec.Vec.with_capacity cpoly.field.Ext4 hsz) 0#usize hrows hcolsv hhsz
    heqwlen heqwred heqwval hmtlen hmtval (by simp)
    (by simp [alloc.vec.Vec.with_capacity])
    (by intro y hy; simp [alloc.vec.Vec.with_capacity] at hy)
    (by intro t ht'; simp at ht') as ⟨high1, hhlen, hhred, hhval⟩
  have hWhigh : WfEvals (m₀ - min m₀ 10) high1 := ⟨hhlen, hhred⟩
  have hhightab : ∀ y : Fin (2 ^ (m₀ - min m₀ 10)),
      tableFn (m := m₀ - min m₀ 10) high1 y
        = alphaHighTable rs (toExt alpha) (toPoint (m := m₁) tau1) (m₀ - min m₀ 10) y := by
    intro y
    rw [tableFn_apply, alphaHighTable_eq_apTerm_sum]
    exact hhval y.val y.isLt
  have hthigh : mleFold (m₀ - min m₀ 10) (toEvals (m := m₀ - min m₀ 10) high1)
      (fun i => ptFlat a (min m₀ 10 + i)) = thigh := by
    rw [mleFold_eq_evalMle, CMlPolynomialEval.eval_mle_eq_eval, hthighdef]
    rw [show (Vector.ofFn (fun i : Fin (m₀ - min m₀ 10) => ptFlat a (min m₀ 10 + i.val)))
        = Vector.ofFn (splitHighPoint (alphaSplit_le m₀) (toPoint (m := m₀) a)) from
      congrArg Vector.ofFn (funext fun i => by
        simp only [ptFlat, splitHighPoint, toPoint]
        rfl)]
    exact eval_toEvals_eq_MLE' high1 _ hhightab _
  step with alpha_public_mle_eval_loop3_spec (m₀ := m₀) a (alloc.vec.Vec.len a) high1 kv thigh
    hared (by omega) hm0v (by omega) (by rw [hkv]; exact hWhigh)
    (by rw [hkv]; exact hthigh) as ⟨high2, hh2len, hh2red, hh2val⟩
  have hlb : (0 : ℕ) < low1.val.length := by rw [hlow1len]; norm_num
  have hhb : (0 : ℕ) < high2.val.length := by rw [hh2len]; norm_num
  step as ⟨e, he⟩
  have hRe : Reduced e := by rw [he]; exact hlow1red _ (List.getElem_mem hlb)
  have hev : toExt e = tlow := by
    rw [he, ← List.getD_eq_getElem _ _ hlb]; exact hlow1val
  step as ⟨e1, he1⟩
  have hRe1 : Reduced e1 := by rw [he1]; exact hh2red _ (List.getElem_mem hhb)
  have he1v : toExt e1 = thigh := by
    rw [he1, ← List.getD_eq_getElem _ _ hhb]; exact hh2val
  apply spec_mono (ext_mul_spec e e1 hRe hRe1)
  rintro out ⟨hR, hout⟩
  refine ⟨hR, ?_⟩
  rw [hout, hev, he1v, htlowdef, hthighdef,
    alphaSplit_eval_eq rs (toExt alpha) (toPoint (m := m₁) tau1) m₀ (toPoint (m := m₀) a)]

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
/-- One fold step of a table read by **natural** index, against the multilinear
extension it tabulates. This is the arity bookkeeping of a fold -- the `Fin`
casts between `M + 1 - i` and `k + 1`, and the two cube branches -- done once,
with the carrier abstracted to a plain `ℕ → F` reader. Both carriers this
development folds are of that shape: an extracted `Vec Ext4` through
`toExt ∘ getD` (`fold_tableFn_eq_mle` below) and round 0's `Vec Fp` through
`φF ∘ coeffK` (`fold_tableFnFp_eq_mle`). -/
theorem fold_natTable_eq_mle {M i k : ℕ} (him : i < M + 1) (hk : M + 1 - (i + 1) = k)
    (g : ℕ → F) (evals : (Fin (M + 1) → Fin 2) → F) (cs : Fin i → F) (x : F)
    (hv : ∀ y : Fin (M + 1 - i) → Fin 2,
        g ((finFunctionFinEquiv y : Fin (2 ^ (M + 1 - i))) : ℕ)
          = (InnerOuter.cMultilinearExtension (M + 1) evals).eval
              (InnerOuter.hypercubePoint (M + 1) i cs y))
    (z : Fin (M + 1 - (i + 1)) → Fin 2) :
    fold (fun y : Fin (2 ^ (k + 1)) => g y.val) x
        (finFunctionFinEquiv (fun j : Fin k => z (Fin.cast hk.symm j)))
      = (InnerOuter.cMultilinearExtension (M + 1) evals).eval
          (InnerOuter.hypercubePoint (M + 1) (i + 1) (Fin.snoc cs x) z) := by
  have hk1 : M + 1 - i = k + 1 := by omega
  set Y : Fin (2 ^ k) := finFunctionFinEquiv (fun j : Fin k => z (Fin.cast hk.symm j)) with hY
  have key : ∀ b : Fin 2, ∀ idx : Fin (2 ^ (k + 1)), idx.val = 2 * Y.val + b.val →
      g idx.val
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
    rw [hidx, ← hval, hv zb, hypercubePoint_cons_eq him hk cs b z zb hz0 hzs]
  have h0 := key 0 (lo Y) (by simp [lo])
  have h1 := key 1 (hi Y) (by simp [hi])
  rw [fold]
  show (1 - x) * g (lo Y).val + x * g (hi Y).val = _
  rw [h0, h1]
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

/-- One fold step of a tabulated multilinear extension: `fold_natTable_eq_mle`
at the `Vec Ext4` reader. -/
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
  have hv' : ∀ y : Fin (M + 1 - i) → Fin 2,
      toExt (t.val.getD ((finFunctionFinEquiv y : Fin (2 ^ (M + 1 - i))) : ℕ)
          cpoly.field.Ext4.ZERO)
        = (InnerOuter.cMultilinearExtension (M + 1) evals).eval
            (InnerOuter.hypercubePoint (M + 1) i cs y) := by
    intro y
    rw [← tableFn_apply]
    exact hv y
  have h := fold_natTable_eq_mle him hk
    (fun n => toExt (t.val.getD n cpoly.field.Ext4.ZERO)) evals cs x hv' z
  rwa [show (fun y : Fin (2 ^ (k + 1)) => toExt (t.val.getD y.val cpoly.field.Ext4.ZERO))
      = tableFn (m := k + 1) t from funext fun y => (tableFn_apply t y).symm] at h

/-- One fold step of an **embedded base-field** table: `fold_natTable_eq_mle` at
the `Vec Fp` reader `φF ∘ coeffK`, which is what round 0 of the sumcheck folds
(candidate I). The conclusion is the same as `fold_tableFn_eq_mle`'s, so
`honest_compute_g_base_spec` reuses `honest_compute_g_spec`'s argument verbatim
from here on. -/
theorem fold_tableFnFp_eq_mle {M i k : ℕ} (him : i < M + 1) (hk : M + 1 - (i + 1) = k)
    (t : alloc.vec.Vec cpoly.field.Fp) (evals : (Fin (M + 1) → Fin 2) → F)
    (cs : Fin i → F) (x : F)
    (hv : ∀ y : Fin (M + 1 - i) → Fin 2,
        phiF (tableFnFp (m := M + 1 - i) t (finFunctionFinEquiv y))
          = (InnerOuter.cMultilinearExtension (M + 1) evals).eval
              (InnerOuter.hypercubePoint (M + 1) i cs y))
    (z : Fin (M + 1 - (i + 1)) → Fin 2) :
    fold (phiF ∘ tableFnFp (m := k + 1) t) x
        (finFunctionFinEquiv (fun j : Fin k => z (Fin.cast hk.symm j)))
      = (InnerOuter.cMultilinearExtension (M + 1) evals).eval
          (InnerOuter.hypercubePoint (M + 1) (i + 1) (Fin.snoc cs x) z) :=
  fold_natTable_eq_mle him hk (fun n => phiF (coeffK t n)) evals cs x hv z

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
  step with poly_mul_spec inner free hinred hfreered
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

set_option maxHeartbeats 1000000 in
/-- `honest_compute_g_base` computes `honestComputeG` at round `0` with the
witness table in the base field: **`honest_compute_g_spec`'s statement at
`i = 0`**, with `hw`/`hwv` moved onto the `Vec<Fp>` carrier and its embedding
`φF ∘ tableFnFp`. The conclusion is untouched, which is what makes the peeled
round 0 of `honest_round_messages` produce the same wire message the frozen loop
produced (candidate I).

`i = 0` is fixed because round 0 is the only round whose table is base-field:
from round 1 on the challenge has entered it. So the prefix kernel is the empty
product — still computed by `eq_prefix`, so that the body is
`honest_compute_g`'s with the index substituted and nothing else — and the
suffix table has the full `2^M` entries.

No value bound, for `honest_compute_g_spec`'s reasons at `i = 0`: every read is
inside a length the relations fix, `1 ≤ m₀ ≤ Usize.max`, the suffix table's
`2^M` pushes are bounded by `w_fp`'s own `Vec` bound, and the two polynomial
products have `33 + 2` coefficients. -/
theorem honest_compute_g_base_spec {n μ M m₁ dRows : ℕ} (stmt : sumcheck.RoundStatement)
    (w_fp : alloc.vec.Vec cpoly.field.Fp) (a_tab : alloc.vec.Vec cpoly.field.Ext4)
    (ss : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ (M + 1) m₁ 0)
    (sw : InnerOuter.LiftedWitness Φ μ n)
    (hs : RepRoundStmt (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := 0) (dRows := dRows)
      stmt ss)
    (hw : WfEvalsFp (M + 1) w_fp) (ha : WfEvals (M + 1) a_tab)
    (hwv : ∀ y : Fin (M + 1) → Fin 2,
      phiF (tableFnFp (m := M + 1) w_fp (finFunctionFinEquiv y)) =
        InnerOuter.wTableMleEval Φ (M + 1) phiF 16 sw
          (InnerOuter.hypercubePoint (M + 1) 0 ss.challenges y))
    (hav : ∀ y : Fin (M + 1) → Fin 2,
      tableFn (m := M + 1) a_tab (finFunctionFinEquiv y) =
        (InnerOuter.cMultilinearExtension (M + 1)
          (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)).eval
          (InnerOuter.hypercubePoint (M + 1) 0 ss.challenges y)) :
    sumcheck.honest_compute_g_base stmt w_fp a_tab
      ⦃ out => RepRoundMsg out
        (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF 0 (Nat.succ_pos M) ss sw) ⦄ := by
  obtain ⟨hzc, hWc, hRt0, hRta, hc, ht0, hta⟩ := hs
  obtain ⟨hr, hWt, hWa, hW0, hW1, htv, hav', h0v, h1v⟩ := hzc
  obtain ⟨h0len, h0red⟩ := hW0
  have hi : (0 : ℕ) < M + 1 := Nat.succ_pos M
  have hM1 : M + 1 ≤ Usize.max := by
    have := stmt.zc.tau0.property
    omega
  have hcube : 2 ^ (M + 1) ≤ Usize.max := by
    have hlen := hw.1
    have := w_fp.property
    omega
  simp only [sumcheck.honest_compute_g_base, sumcheck.RoundStatement.impl.zc,
    sumcheck.NestedZeroCheckStmt.impl.tau0, sumcheck.RoundStatement.impl.challenges, bind_tc_ok]
  step with eq_prefix_spec (m₀ := M + 1) (i := 0) stmt.zc.tau0 stmt.challenges
    ⟨h0len, h0red⟩ hWc (by omega) as ⟨pref, hRpref, hprefv⟩
  have hsub0 : M + 1 - (0#usize : Std.Usize).val - 1 = M := by scalar_tac
  step with eq_suffix_table_spec (m₀ := M + 1) stmt.zc.tau0 0#usize ⟨h0len, h0red⟩
    (by scalar_tac)
    (by
      rw [hsub0]
      have hmono : (2 : ℕ) ^ M ≤ 2 ^ (M + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega)
      as ⟨suffix, hWsuf, hsufv⟩
  have hsufv' : toEvals (m := M) suffix =
      CMlPolynomialEval.lagrangeBasis (Vector.ofFn fun k : Fin M =>
        toPoint (m := M + 1) stmt.zc.tau0 ⟨0 + 1 + k.val, by have := k.isLt; omega⟩) := hsufv
  step with round_poly_zero_base_spec (k := M) w_fp suffix hw hWsuf
    as ⟨inner, hinlen, hinred, hinval⟩
  step as ⟨e, he⟩
  have hRe : Reduced e := he ▸ h0red _ (List.getElem_mem (by omega))
  step with eq_free_factor_spec e hRe as ⟨free, hfreelen, hfreered, hfreeval⟩
  step with poly_mul_spec inner free hinred hfreered
    (by rw [hinlen, hfreelen]; have := usize_max_ge; omega) as ⟨wf, hwfred, hwfraw, hwflen⟩
  step with uni_smul_spec pref wf hRpref hwfred as ⟨gz, hgzred, hgzraw⟩
  step with round_poly_alpha_base_spec (k := M) w_fp a_tab hw ha
    as ⟨ga, hgalen, hgared, hgaval⟩
  have hwv2 : ∀ y : Fin (M + 1) → Fin 2,
      phiF (tableFnFp (m := M + 1) w_fp (finFunctionFinEquiv y))
        = (InnerOuter.cMultilinearExtension (M + 1)
            (InnerOuter.wTable Φ (M + 1) phiF 16 sw)).eval
            (InnerOuter.hypercubePoint (M + 1) 0 ss.challenges y) := by
    intro y
    rw [hwv y, InnerOuter.wTableMleEval_eq, InnerOuter.cMultilinearExtension_eval]
  have hfoldw : ∀ (x : F) (z : Fin M → Fin 2),
      fold (phiF ∘ tableFnFp (m := M + 1) w_fp) x (finFunctionFinEquiv z)
        = InnerOuter.wTableMleEval Φ (M + 1) phiF 16 sw
            (InnerOuter.hypercubePoint (M + 1) (0 + 1) (Fin.snoc ss.challenges x) z) := by
    intro x z
    have hstep := fold_tableFnFp_eq_mle (M := M) (i := 0) (k := M) hi rfl w_fp
      (InnerOuter.wTable Φ (M + 1) phiF 16 sw) ss.challenges x hwv2 z
    rw [show (fun j : Fin M => z (Fin.cast rfl j)) = z from rfl] at hstep
    rw [hstep, InnerOuter.wTableMleEval_eq, InnerOuter.cMultilinearExtension_eval]
  have hfolda : ∀ (x : F) (z : Fin M → Fin 2),
      fold (tableFn (m := M + 1) a_tab) x (finFunctionFinEquiv z)
        = (InnerOuter.cMultilinearExtension (M + 1)
            (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)).eval
            (InnerOuter.hypercubePoint (M + 1) (0 + 1) (Fin.snoc ss.challenges x) z) := by
    intro x z
    have hstep := fold_tableFn_eq_mle (M := M) (i := 0) (k := M) hi rfl a_tab
      (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)
      ss.challenges x hav z
    rw [show (fun j : Fin M => z (Fin.cast rfl j)) = z from rfl] at hstep
    exact hstep
  have hre : ∀ f : Fin (2 ^ M) → F,
      ∑ Y : Fin (2 ^ M), f Y = ∑ z : Fin M → Fin 2, f (finFunctionFinEquiv z) :=
    fun f => (Fintype.sum_equiv finFunctionFinEquiv _ f (fun _ => rfl)).symm
  have htau : ∀ (j : ℕ) (h : j < M + 1),
      ss.zc.τ₀ ⟨j, h⟩ = toExt (stmt.zc.tau0.val.getD j cpoly.field.Ext4.ZERO) := by
    intro j h
    rw [← h0v]
    rfl
  have hev : toExt e = ss.zc.τ₀ ⟨0, hi⟩ := by
    rw [htau 0 hi, he, List.getD_eq_getElem _ _ (by omega)]
  have hpref : toExt pref
      = eqProd (fun j : Fin 0 => ss.zc.τ₀ (Fin.castLE (by omega) j)) ss.challenges := by
    rw [hprefv, hc, h0v]
  have hsuf : ∀ z : Fin M → Fin 2,
      tableFn (m := M) suffix (finFunctionFinEquiv z)
        = ∏ j : Fin (M + 1 - (0 + 1)),
            (if z j = 1 then ss.zc.τ₀ ⟨0 + 1 + j.val, by have := j.isLt; omega⟩
              else 1 - ss.zc.τ₀ ⟨0 + 1 + j.val, by have := j.isLt; omega⟩) := by
    intro z
    rw [tableFn, hsufv', lagrangeBasis_get_cube]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Vector.get_ofFn, htau (0 + 1 + j.val) (by have := j.isLt; omega)]
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
        (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF 0 hi ss sw).1.2) ?_
    intro x
    rw [toUni_eval, hgzraw, raw_eval_smul, hwfraw, raw_eval_mul, ← toUni_eval inner,
      ← toUni_eval free, hinval x, hfreeval x]
    show _ = CPolynomial.eval x
      (InnerOuter.computableRoundPoly
        (InnerOuter.sumcheckPolyZero Φ (M + 1) phiF 16 ss.zc.τ₀ sw) ⟨0, hi⟩ ss.challenges)
    have hHS : InnerOuter.hypercubeSum (M + 1)
        (InnerOuter.sumcheckPolyZero Φ (M + 1) phiF 16 ss.zc.τ₀ sw) (0 + 1)
        (Fin.snoc ss.challenges x)
        = ∑ z : Fin M → Fin 2,
            (InnerOuter.sumcheckPolyZero Φ (M + 1) phiF 16 ss.zc.τ₀ sw).eval
              (InnerOuter.hypercubePoint (M + 1) (0 + 1) (Fin.snoc ss.challenges x) z) := rfl
    rw [InnerOuter.computableRoundPoly_eval, hHS]
    have hterm : ∀ z : Fin M → Fin 2,
        (InnerOuter.sumcheckPolyZero Φ (M + 1) phiF 16 ss.zc.τ₀ sw).eval
            (InnerOuter.hypercubePoint (M + 1) (0 + 1) (Fin.snoc ss.challenges x) z)
          = toExt pref * (tableFn (m := M) suffix (finFunctionFinEquiv z)
              * InnerOuter.rangeProduct 16
                (fold (phiF ∘ tableFnFp (m := M + 1) w_fp) x (finFunctionFinEquiv z)))
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
      (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF 0 hi ss sw).2.2 ?_
    intro x
    rw [hgaval x]
    show linSumAlpha _ _ x = CPolynomial.eval x
      (InnerOuter.computableRoundPoly
        (InnerOuter.sumcheckPolyAlpha Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα sw)
        ⟨0, hi⟩ ss.challenges)
    have hHS : InnerOuter.hypercubeSum (M + 1)
        (InnerOuter.sumcheckPolyAlpha Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα sw)
        (0 + 1) (Fin.snoc ss.challenges x)
        = ∑ z : Fin M → Fin 2,
            (InnerOuter.sumcheckPolyAlpha Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα sw).eval
              (InnerOuter.hypercubePoint (M + 1) (0 + 1) (Fin.snoc ss.challenges x) z) := rfl
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

set_option maxHeartbeats 1000000 in
/-- `final_check` decides `finalCheck` (`FinalEval.lean:99`) at round `m₀`: the
three conjuncts, the third the `u64` bound compare. `m₀` is read off `tau0`;
`2 ^ m₀ ≤ Usize.max` is `cube_size`'s and `alpha_public_mle_eval`'s; `hmax`
is `alpha_public_evals_spec`'s. The first check in the chain that can reject.

The statement is unchanged; only the two routes into it are. The linear claim's
factor arrives from one `alpha_public_mle_eval_spec` step -- the tensor split,
two small tables and two folds -- where it used to be assembled from
`alpha_public_table_spec` and the specs of cpoly's `lagrange_basis` and `dot`
over the whole `2 ^ m₀` cube (candidate J). And the kernel factor `eq̃(τ₀, a)`
now comes from hachi's own `eq_prefix` at `i = m₀`, the `m₀`-factor closed form,
rather than from `cpoly::multilinear::eq_tilde`'s pair of `2 ^ m₀` Lagrange
bases and their dot product (candidate K) -- which is why none of those cpoly
functions is in the model any more, and why their specs are gone rather than
parked. `eq_prefix_spec` states the kernel over the bound prefix `τ₀|<i`; at
`i = m₀` the prefix is all of `τ₀`, which is the `Fin.castLE le_rfl` step
below. -/
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
    bind_tc_ok]
  set m0 : Std.Usize := alloc.vec.Vec.len stmt.zc.tau0 with hm0def
  clear_value m0
  subst hm0v
  step with eq_prefix_spec (m₀ := m0.val) (i := m0.val) stmt.zc.tau0 stmt.challenges
    hWtau0 hWc le_rfl as ⟨eqall, hReqall, heqall⟩
  rw [show (fun k : Fin m0.val =>
      toPoint (m := m0.val) stmt.zc.tau0 (Fin.castLE le_rfl k))
      = toPoint (m := m0.val) stmt.zc.tau0 from rfl] at heqall
  step with alpha_public_mle_eval_spec (n := n) (μ := μ) (m₀ := m0.val) (m₁ := m₁)
    stmt.zc.rlin ss.zc.rlin stmt.zc.alpha stmt.zc.tau1 stmt.challenges hr hRalpha hWtau1
    hWc hm0 hmax as ⟨amle, hRamle, hamle⟩
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
    rw [hamle, hva, htau1, hc]
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


/-! ### The one mixed layer fold

Round 0's challenge is a genuine extension element, so the table its fold
produces is an `Ext4` table and rounds `1 …` proceed through
`eval_mle_layer_spec` unchanged. What `eval_mle_layer_base` is, is that single
layer with a base-field input: two `Fp × Ext4` scalings per output entry instead
of two `Ext4` multiplications (candidate I). Its conclusion is
`eval_mle_layer_spec`'s at the embedded table, which is what lets the peeled
round 0 hand the loop below exactly the table the old first iteration produced. -/

/-- The loop of `eval_mle_layer_base`: the output holds the `j` folded entries
produced so far, each `w[2j]·(1 − x₀) + w[2j+1]·x₀` with the `Fp` factor on the
left (`impl Mul<Ext4> for Fp`). -/
theorem eval_mle_layer_base_loop_spec {k : ℕ} (values : alloc.vec.Vec cpoly.field.Fp)
    (x0 one_minus : cpoly.field.Ext4) (half : Std.Usize)
    (hvred : ∀ a ∈ values.val, Red a) (hvlen : values.val.length = 2 ^ (k + 1))
    (hx : Reduced x0) (hom : Reduced one_minus) (homv : toExt one_minus = 1 - toExt x0)
    (hhalf : half.val = 2 ^ k)
    (out : alloc.vec.Vec cpoly.field.Ext4) (j : Std.Usize)
    (hj : j.val ≤ 2 ^ k) (holen : out.val.length = j.val) (hored : VecReduced out)
    (hoval : ∀ t : ℕ, t < j.val →
      toExt (out.val.getD t cpoly.field.Ext4.ZERO)
        = phiF (coeffK values (2 * t)) * (1 - toExt x0)
          + phiF (coeffK values (2 * t + 1)) * toExt x0) :
    sumcheck.eval_mle_layer_base_loop values x0 half one_minus out j
      ⦃ o => o.val.length = 2 ^ k ∧ VecReduced o ∧
        ∀ t : ℕ, t < 2 ^ k →
          toExt (o.val.getD t cpoly.field.Ext4.ZERO)
            = phiF (coeffK values (2 * t)) * (1 - toExt x0)
              + phiF (coeffK values (2 * t + 1)) * toExt x0 ⦄ := by
  have hmax : 2 ^ (k + 1) ≤ Usize.max := by
    have := values.property
    omega
  rw [sumcheck.eval_mle_layer_base_loop]
  apply loop.spec_decr_nat (fun st => 2 ^ k - st.2.val)
    (fun st => st.2.val ≤ 2 ^ k ∧ st.1.val.length = st.2.val ∧ VecReduced st.1 ∧
      ∀ t : ℕ, t < st.2.val →
        toExt (st.1.val.getD t cpoly.field.Ext4.ZERO)
          = phiF (coeffK values (2 * t)) * (1 - toExt x0)
            + phiF (coeffK values (2 * t + 1)) * toExt x0)
  · rintro ⟨o1, j1⟩ ⟨hj1, hlen1, hred1, hval1⟩
    dsimp only at hj1 hlen1 hred1 hval1
    simp only [sumcheck.eval_mle_layer_base_loop.body]
    by_cases hlt : j1 < half
    · rw [if_pos hlt]
      have hjlt : j1.val < 2 ^ k := by rw [← hhalf]; scalar_tac
      have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      have hlob : 2 * j1.val < values.val.length := by rw [hvlen, hpow]; omega
      have hhib : 2 * j1.val + 1 < values.val.length := by rw [hvlen, hpow]; omega
      have hmul : 2 * j1.val ≤ Usize.max := by omega
      step as ⟨idx, hidx⟩
      have hidxb : idx.val < values.val.length := by rw [hidx]; omega
      step as ⟨lo0, hlo0⟩
      have hRlo0 : Red lo0 := hlo0 ▸ hvred _ (List.getElem_mem hidxb)
      step as ⟨idx1, hidx1⟩
      have hidx1b : idx1.val < values.val.length := by rw [hidx1, hidx]; omega
      step as ⟨hi0, hhi0⟩
      have hRhi0 : Red hi0 := hhi0 ▸ hvred _ (List.getElem_mem hidx1b)
      step with fp_ext_mul_spec lo0 one_minus hRlo0 hom as ⟨e, hRe, he⟩
      step with fp_ext_mul_spec hi0 x0 hRhi0 hx as ⟨e1, hRe1, he1⟩
      step as ⟨sm, hRsm, hsm⟩
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
          have he' : toExt e = phiF (toK lo0) * toExt one_minus := by rw [he, phiF_apply]
          have he1' : toExt e1 = phiF (toK hi0) * toExt x0 := by rw [he1, phiF_apply]
          rw [hteq, ho2, getD_append_eq, hsm, he', he1', homv, coeffK, coeffK, hlen1,
            hlo0, hhi0,
            ← List.getD_eq_getElem values.val cpoly.field.Fp.ZERO hidxb,
            ← List.getD_eq_getElem values.val cpoly.field.Fp.ZERO hidx1b, hidx1, hidx]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hjeq : j1.val = 2 ^ k := by rw [← hhalf] at hj1 ⊢; scalar_tac
      exact ⟨by rw [hlen1, hjeq], hred1, by rw [← hjeq]; exact hval1⟩
  · exact ⟨hj, holen, hored, hoval⟩

/-- `eval_mle_layer_base` folds a base-field table's first coordinate at the
extension challenge `x0`: the specification's `fold` on the embedded table, the
very conclusion `eval_mle_layer_spec` delivers for an `Ext4` table. -/
theorem eval_mle_layer_base_spec {k : ℕ} (values : alloc.vec.Vec cpoly.field.Fp)
    (x0 : cpoly.field.Ext4) (hv : WfEvalsFp (k + 1) values) (hx : Reduced x0) :
    sumcheck.eval_mle_layer_base values x0
      ⦃ o => WfEvals k o ∧ ∀ y : Fin (2 ^ k),
          tableFn (m := k) o y
            = fold (phiF ∘ tableFnFp (m := k + 1) values) (toExt x0) y ⦄ := by
  obtain ⟨hvlen, hvred⟩ := hv
  have hR1 : Reduced cpoly.field.Ext4.ONE := reduced_ONE
  rw [sumcheck.eval_mle_layer_base]
  step as ⟨half, hhalf⟩
  have hhalfv : half.val = 2 ^ k := by
    have hlen : (alloc.vec.Vec.len values).val = 2 ^ (k + 1) := by simpa using hvlen
    have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    scalar_tac
  step with ext_sub_spec cpoly.field.Ext4.ONE x0 hR1 hx as ⟨om, hRom, homv⟩
  apply spec_mono (eval_mle_layer_base_loop_spec (k := k) values x0 om half
    hvred hvlen hx hRom (by rw [homv, toExt_ONE]) hhalfv
    (alloc.vec.Vec.with_capacity cpoly.field.Ext4 half) 0#usize
    (by simp) (by simp [alloc.vec.Vec.with_capacity])
    (by intro u hu; simp [alloc.vec.Vec.with_capacity] at hu)
    (by intro t' ht'; simp at ht'))
  rintro o ⟨holen, hored, hoval⟩
  refine ⟨⟨holen, hored⟩, fun y => ?_⟩
  rw [tableFn_apply, hoval y.val y.isLt]
  show _ = (1 - toExt x0) * phiF (coeffK values (2 * y.val))
    + toExt x0 * phiF (coeffK values (2 * y.val + 1))
  ring

/-- One fold of a represented base-field table: `eval_mle_layer_base` carries
the round-`i` tabulation of a multilinear extension to the round-`(i+1)` one,
exactly as `eval_mle_layer_table_spec` does for an `Ext4` table -- and its
output *is* an `Ext4` table, which is why it is the last base-field step. -/
theorem eval_mle_layer_base_table_spec {M i : ℕ} (him : i < M + 1)
    (t : alloc.vec.Vec cpoly.field.Fp) (evals : (Fin (M + 1) → Fin 2) → F)
    (cs : Fin i → F) (a : cpoly.field.Ext4)
    (ht : WfEvalsFp (M + 1 - i) t) (hRa : Reduced a)
    (hv : ∀ y : Fin (M + 1 - i) → Fin 2,
        phiF (tableFnFp (m := M + 1 - i) t (finFunctionFinEquiv y))
          = (InnerOuter.cMultilinearExtension (M + 1) evals).eval
              (InnerOuter.hypercubePoint (M + 1) i cs y)) :
    sumcheck.eval_mle_layer_base t a
      ⦃ o => WfEvals (M + 1 - (i + 1)) o ∧
          ∀ y : Fin (M + 1 - (i + 1)) → Fin 2,
            tableFn (m := M + 1 - (i + 1)) o (finFunctionFinEquiv y)
              = (InnerOuter.cMultilinearExtension (M + 1) evals).eval
                  (InnerOuter.hypercubePoint (M + 1) (i + 1) (Fin.snoc cs (toExt a)) y) ⦄ := by
  have ht' : WfEvalsFp ((M + 1 - i - 1) + 1) t := by
    rwa [show M + 1 - i = (M + 1 - i - 1) + 1 from by omega] at ht
  apply spec_mono (eval_mle_layer_base_spec (k := M + 1 - i - 1) t a ht' hRa)
  rintro o ⟨hWo, hov⟩
  refine ⟨hWo, fun y => ?_⟩
  rw [hov (finFunctionFinEquiv y)]
  have hstep := fold_tableFnFp_eq_mle (k := M + 1 - i - 1) him rfl t evals cs (toExt a) hv y
  rw [show (fun j : Fin (M + 1 - i - 1) => y (Fin.cast rfl j)) = y from rfl] at hstep
  exact hstep

/-- The witness table at round `0`, in the base field: `initial_w_table` for the
`Vec<Fp>` that `c_w_table_fp` builds, read off the value condition
`c_w_table_fp_spec` delivers rather than off a `MultilinearEvals` equality --
the base-field table is not a `MultilinearEvals`. -/
theorem initial_w_table_fp {μ n M : ℕ} (w_fp : alloc.vec.Vec cpoly.field.Fp)
    (sw : InnerOuter.LiftedWitness Φ μ n) (cs : Fin 0 → F)
    (h : ∀ t < 2 ^ (M + 1), phiF (coeffK w_fp t) = wTableFlat (M + 1) sw t) :
    ∀ y : Fin (M + 1) → Fin 2,
      phiF (tableFnFp (m := M + 1) w_fp (finFunctionFinEquiv y))
        = InnerOuter.wTableMleEval Φ (M + 1) phiF 16 sw
            (InnerOuter.hypercubePoint (M + 1) 0 cs y) := by
  intro y
  have hY := (finFunctionFinEquiv y : Fin (2 ^ (M + 1))).isLt
  show phiF (coeffK w_fp ((finFunctionFinEquiv y : Fin (2 ^ (M + 1))) : ℕ)) = _
  rw [h _ hY, wTableFlat, dif_pos hY, Fin.eta, Equiv.symm_apply_apply,
    InnerOuter.wTableMleEval_eq, ← InnerOuter.cMultilinearExtension_eval, hypercubePoint_zero]
  exact (InnerOuter.cMultilinearExtension_eval_boolean (M + 1)
    (InnerOuter.wTable Φ (M + 1) phiF 16 sw) y).symm

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


/-! ## The α table as two factors (candidate L, brief 5's S4, prover half; wall W1)

`honest_round_messages` no longer builds the `2 ^ m₀`-entry public table `Ã`
(`alpha_public_table`, still in the model and still used by `round_loop`). It
carries `Ã` as the **tensor product** of the two small tables candidate J's
`alpha_public_mle_eval` already splits it into -- `low` of `2 ^ k` entries,
`k = min m₀ 10`, and `high` of `2 ^ (m₀ − k)` -- reading

    `Ã[idx] = low[idx % low.len()] * high[idx / low.len()]`

and folding the pair instead of the table: the fold acts on `low` while `low`
has more than one entry and on `high` afterwards. `2 GiB` becomes `2.06 MiB` at
the pin (wall W1), and the per-read cost is one extension multiplication.

The pure algebra below (subsections 0–6) is candidate L's, **moved verbatim out
of `lean/Opt.lean` § "Candidate L"**: `Opt.lean` imports this file, so the spec
layer here cannot import it, and the house pattern (campaign J with
`mle_tensor_split`, `alphaLowTable`, `alphaHighTable`) is to let the pure lemmas
live at the level that consumes them and keep only the `opt_eq_spec` upstairs.
`HachiEquiv.Opt.honest_round_messages.opt_eq_spec` still packages the three facts
as the candidate's contract, stated over the names below.

The extracted items' specs follow in subsections 7–12, each the spec of its flat
twin with the tensor read substituted for `a_tab`'s. -/

/-! #### 0. Index arithmetic

Two elementary facts, stated over plain naturals so that no `Fin` cast reaches
the lemmas below: a little-endian two-block index is recovered by `%` and `/`,
and doubling a block boundary doubles the low remainder. -/

/-- The defining property of `%` and `/`: if `a = n·Q + r` with `r < n`, then `Q`
and `r` *are* the quotient and the remainder. -/
private theorem mod_div_eq_of {n a Q r : ℕ} (hn : 0 < n) (h : a = n * Q + r) (hr : r < n) :
    a % n = r ∧ a / n = Q := by
  subst h
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  · rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hr, Nat.add_zero]

/-- **Doubling the block boundary.** With `y = d·Q + r` (`r < d`), the two
children `2y` and `2y + 1` of `y` sit in the same high block `Q` of the doubled
boundary `2d`, at the low positions `2r` and `2r + 1`. This is the whole content
of "the layer fold commutes with the tensor structure". -/
private theorem split_two {d y r Q : ℕ} (hd : 0 < d) (hr : r < d) (hy : y = d * Q + r) :
    (2 * y) % (2 * d) = 2 * r ∧ (2 * y) / (2 * d) = Q
      ∧ (2 * y + 1) % (2 * d) = 2 * r + 1 ∧ (2 * y + 1) / (2 * d) = Q := by
  have hd2 : 0 < 2 * d := by omega
  have e0 : 2 * y = 2 * d * Q + 2 * r := by rw [hy]; ring
  have e1 : 2 * y + 1 = 2 * d * Q + (2 * r + 1) := by rw [hy]; ring
  exact ⟨(mod_div_eq_of hd2 e0 (by omega)).1, (mod_div_eq_of hd2 e0 (by omega)).2,
    (mod_div_eq_of hd2 e1 (by omega)).1, (mod_div_eq_of hd2 e1 (by omega)).2⟩

/-! #### 1. The tensor table

`tensorTable L H` is the `2 ^ (j + k)`-entry table the prover no longer stores:
entry `idx` is `low[idx % 2 ^ k] * high[idx / 2 ^ k]`, which is *verbatim* the
Rust's tensor read. The exponent is written `j + k` (high block first) on
purpose: `j + (k + 1)` and `(j + 1) + 0` are then **definitionally**
`(j + k) + 1` and `j + 1`, so the two fold-commutation statements below need no
`Fin` cast at all. -/

/-- The tensor product of a `2 ^ k`-entry low table and a `2 ^ j`-entry high
table, as one `2 ^ (j + k)`-entry table: `T(idx) = L(idx % 2 ^ k) · H(idx / 2 ^ k)`. -/
def tensorTable {j k : ℕ} (L : Fin (2 ^ k) → F) (H : Fin (2 ^ j) → F) :
    Fin (2 ^ (j + k)) → F := fun idx =>
  L ⟨(idx : ℕ) % 2 ^ k, Nat.mod_lt _ (by positivity)⟩
    * H ⟨(idx : ℕ) / 2 ^ k, Nat.div_lt_of_lt_mul
        (lt_of_lt_of_eq idx.isLt (by rw [pow_add]; ring))⟩

/-- **The Rust's read.** `tensorTable` at an index is the product of the two
table entries at `idx % low.len()` and `idx / low.len()` -- the expression
`round_value_alpha_split` and `honest_compute_g_split` evaluate in place of
`a_tab[idx]`. -/
theorem tensorTable_apply {j k : ℕ} (L : Fin (2 ^ k) → F) (H : Fin (2 ^ j) → F)
    (idx : Fin (2 ^ (j + k))) (hm : (idx : ℕ) % 2 ^ k < 2 ^ k)
    (hd : (idx : ℕ) / 2 ^ k < 2 ^ j) :
    tensorTable L H idx = L ⟨(idx : ℕ) % 2 ^ k, hm⟩ * H ⟨(idx : ℕ) / 2 ^ k, hd⟩ := rfl

/-- `tensorTable` at a *split* index: when `idx = l + 2 ^ k · u` the two reads are
`l` and `u` on the nose. The shape `ffe_cubeSplit_val` delivers. -/
theorem tensorTable_eq_of_split {j k : ℕ} (L : Fin (2 ^ k) → F) (H : Fin (2 ^ j) → F)
    (idx : Fin (2 ^ (j + k))) (l : Fin (2 ^ k)) (u : Fin (2 ^ j))
    (h : (idx : ℕ) = (l : ℕ) + 2 ^ k * (u : ℕ)) :
    tensorTable L H idx = L l * H u := by
  obtain ⟨hmod, hdiv⟩ :=
    split_mod_div_gen (K := k) (d := 2 ^ k) (l : ℕ) (u : ℕ) l.isLt le_rfl (Or.inl rfl)
  simp only [tensorTable]
  congr 1
  · exact congrArg L (Fin.ext (by show (idx : ℕ) % 2 ^ k = (l : ℕ); rw [h, hmod]))
  · exact congrArg H (Fin.ext (by show (idx : ℕ) / 2 ^ k = (u : ℕ); rw [h, hdiv]))

/-! #### 2. The fold commutes with the tensor structure, low factor

While the low table has more than one entry, one `eval_mle_layer` on the tensor
table is one `eval_mle_layer` on the low table, the high table untouched. This is
the `1 < low.len()` branch of `alpha_split_fold`. -/

/-- **Candidate L's first half.** `fold (L ⊗ H) a = (fold L a) ⊗ H` for a low
table of `2 ^ (k+1) > 1` entries. Both sides are functions on `Fin (2 ^ (j + k))`;
no cast, because `j + (k + 1)` is definitionally `(j + k) + 1`. -/
theorem fold_tensorTable_low {j k : ℕ} (L : Fin (2 ^ (k + 1)) → F) (H : Fin (2 ^ j) → F)
    (a : F) :
    fold (tensorTable (j := j) (k := k + 1) L H) a
      = tensorTable (j := j) (k := k) (fold L a) H := by
  funext y
  have hk : (0 : ℕ) < 2 ^ k := by positivity
  have hylt : (y : ℕ) < 2 ^ k * 2 ^ j :=
    lt_of_lt_of_eq y.isLt (by show (2 : ℕ) ^ (j + k) = 2 ^ k * 2 ^ j; rw [pow_add]; ring)
  obtain ⟨R, Q, hR, hQ, hval⟩ :
      ∃ R Q, R < 2 ^ k ∧ Q < 2 ^ j ∧ (y : ℕ) = 2 ^ k * Q + R :=
    ⟨(y : ℕ) % 2 ^ k, (y : ℕ) / 2 ^ k, Nat.mod_lt _ hk, Nat.div_lt_of_lt_mul hylt,
      (Nat.div_add_mod _ _).symm⟩
  have hR2 : 2 * R < 2 ^ (k + 1) := by rw [pow_succ]; omega
  have hR2' : 2 * R + 1 < 2 ^ (k + 1) := by rw [pow_succ]; omega
  rw [fold,
    tensorTable_eq_of_split (j := j) (k := k + 1) L H (lo y) ⟨2 * R, hR2⟩ ⟨Q, hQ⟩
      (by show 2 * (y : ℕ) = 2 * R + 2 ^ (k + 1) * Q; rw [hval, pow_succ]; ring),
    tensorTable_eq_of_split (j := j) (k := k + 1) L H (hi y) ⟨2 * R + 1, hR2'⟩ ⟨Q, hQ⟩
      (by show 2 * (y : ℕ) + 1 = 2 * R + 1 + 2 ^ (k + 1) * Q; rw [hval, pow_succ]; ring),
    tensorTable_eq_of_split (j := j) (k := k) (fold L a) H y ⟨R, hR⟩ ⟨Q, hQ⟩
      (by rw [hval]; ring),
    fold]
  simp only [lo, hi]
  ring

/-! #### 3. The fold commutes with the tensor structure, scalar factor

Once the low table is a single entry it is a scalar and the fold passes straight
through to the high table. This is the `else` branch of `alpha_split_fold`. -/

/-- **Candidate L's second half.** `fold (L ⊗ H) a = L ⊗ (fold H a)` for a
one-entry low table. Cast-free for the same reason: `(j + 1) + 0` is
definitionally `j + 1` and `j + 0` is `j`. -/
theorem fold_tensorTable_scalar {j : ℕ} (L : Fin (2 ^ 0) → F) (H : Fin (2 ^ (j + 1)) → F)
    (a : F) :
    fold (tensorTable (j := j + 1) (k := 0) L H) a
      = tensorTable (j := j) (k := 0) L (fold H a) := by
  funext y
  rw [fold,
    tensorTable_eq_of_split (j := j + 1) (k := 0) L H (lo y) ⟨0, by norm_num⟩ (lo y) (by simp),
    tensorTable_eq_of_split (j := j + 1) (k := 0) L H (hi y) ⟨0, by norm_num⟩ (hi y) (by simp),
    tensorTable_eq_of_split (j := j) (k := 0) L (fold H a) y ⟨0, by norm_num⟩ y (by simp),
    fold]
  ring

/-! #### 4. The round-0 table is the tensor table

The pointwise content of candidate J's split, restated at the flat index the
prover's `a_tab` is indexed by: `alphaPublicEvals` at a cube point equals
`tensorTable (alphaLowTable α k) (alphaHighTable rs α τ₁ (m₀ − k))` at the flat
index of that point, with `k = min m₀ 10`. The argument is the one inside
`alphaSplit_eval_eq` (`lean/Sumcheck.lean`): `ffe_cubeSplit_val` for the index
and `split_mod_div` for the two readings, with `d = 2 ^ 10` supplied by
`phi_natDegree_eq_two_pow`.

The index is taken as a separate argument with its value as a hypothesis rather
than as a `Fin.cast` of `finFunctionFinEquiv x`, because `(m₀ − k) + k = m₀` is
not definitional: the campaign discharges `hidx` by `simp` from its own
`low.len() * high.len() = 2 ^ m₀`. -/

/-- **The round-0 invariant.** The `2 ^ m₀`-entry public table the prover no
longer builds is the tensor table of the two small ones. -/
theorem alphaPublicEvals_eq_tensorTable {n μ m₁ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ)
    (α : F) (τ₁ : Fin m₁ → F) (m₀ : ℕ) (x : Fin m₀ → Fin 2)
    (idx : Fin (2 ^ ((m₀ - min m₀ 10) + min m₀ 10)))
    (hidx : (idx : ℕ) = ((finFunctionFinEquiv x : Fin (2 ^ m₀)) : ℕ)) :
    InnerOuter.alphaPublicEvals Φ m₀ m₁ phiF 16 rs α τ₁ x
      = tensorTable (alphaLowTable α (min m₀ 10))
          (alphaHighTable rs α τ₁ (m₀ - min m₀ 10)) idx := by
  have hk : min m₀ 10 ≤ m₀ := alphaSplit_le m₀
  obtain ⟨⟨xl, xh⟩, hx⟩ : ∃ p, cubeSplit hk p = x :=
    ⟨(cubeSplit hk).symm x, (cubeSplit hk).apply_symm_apply x⟩
  obtain ⟨hmod, hdiv⟩ :=
    split_mod_div (m₀ := m₀) (finFunctionFinEquiv xl) (finFunctionFinEquiv xh)
  rw [tensorTable_eq_of_split (j := m₀ - min m₀ 10) (k := min m₀ 10) _ _ idx
      (finFunctionFinEquiv xl) (finFunctionFinEquiv xh)
      (by rw [hidx, ← hx, ffe_cubeSplit_val hk xl xh]),
    ← hx, InnerOuter.alphaPublicEvals]
  simp only [phi_natDegree_eq_two_pow, InnerOuter.alphaTilde]
  rw [ffe_cubeSplit_val hk xl xh, hmod, hdiv]
  rfl

/-! #### 5. The round value off the split read

`round_value_alpha_split` folds `w` as before and folds the *product of the two
tensor entries* -- not the product of a folded low table with the high table.
So its accumulator is `linSumAlpha` at the tensor table, and the only new
per-point fact the round-value spec needs is this one. -/

/-- **The split read computes the same round value.** With the loop invariant
"`a` reads as the tensor table" (`ha`), `linSumAlpha w a T` is the Rust's
accumulator: `fold w T y` times the fold of the two tensor reads at `2y` and
`2y + 1`. -/
theorem linSumAlpha_tensor {j k : ℕ} (w a : Fin (2 ^ ((j + k) + 1)) → F)
    (L : Fin (2 ^ (k + 1)) → F) (H : Fin (2 ^ j) → F) (T : F)
    (ha : ∀ z, a z = tensorTable L H z) :
    linSumAlpha w a T
      = ∑ y : Fin (2 ^ (j + k)),
          fold w T y * ((1 - T) * tensorTable (j := j) (k := k + 1) L H (lo y)
            + T * tensorTable (j := j) (k := k + 1) L H (hi y)) := by
  simp only [linSumAlpha, fold, ha]

/-- The same per-point read spelled with `%` and `/`, which is what the Rust
loop body writes: `lo_a = low[(2y) % L] * high[(2y) / L]`,
`hi_a = low[(2y+1) % L] * high[(2y+1) / L]`. -/
theorem fold_tensorTable_read {j k : ℕ} (L : Fin (2 ^ (k + 1)) → F) (H : Fin (2 ^ j) → F)
    (T : F) (y : Fin (2 ^ (j + k)))
    (hm0 : 2 * (y : ℕ) % 2 ^ (k + 1) < 2 ^ (k + 1))
    (hd0 : 2 * (y : ℕ) / 2 ^ (k + 1) < 2 ^ j)
    (hm1 : (2 * (y : ℕ) + 1) % 2 ^ (k + 1) < 2 ^ (k + 1))
    (hd1 : (2 * (y : ℕ) + 1) / 2 ^ (k + 1) < 2 ^ j) :
    fold (tensorTable (j := j) (k := k + 1) L H) T y
      = (1 - T) * (L ⟨2 * (y : ℕ) % 2 ^ (k + 1), hm0⟩ * H ⟨2 * (y : ℕ) / 2 ^ (k + 1), hd0⟩)
        + T * (L ⟨(2 * (y : ℕ) + 1) % 2 ^ (k + 1), hm1⟩
                 * H ⟨(2 * (y : ℕ) + 1) / 2 ^ (k + 1), hd1⟩) := rfl

/-- The scalar-branch read: a one-entry low table contributes `low[0]` at every
index, so the round value is `low[0]` times the high fold. -/
theorem fold_tensorTable_read_scalar {j : ℕ} (L : Fin (2 ^ 0) → F)
    (H : Fin (2 ^ (j + 1)) → F) (T : F) (y : Fin (2 ^ j)) :
    fold (tensorTable (j := j + 1) (k := 0) L H) T y = L ⟨0, by norm_num⟩ * fold H T y := by
  rw [fold_tensorTable_scalar,
    tensorTable_eq_of_split (j := j) (k := 0) L (fold H T) y ⟨0, by norm_num⟩ y (by simp)]

/-! #### 6. The whole run: `i` folds of the pair are `i` folds of the tensor table

The invariant the campaign's `honest_round_messages_spec` carries, as one
statement. `foldIter i a w` is `i` layer folds of `w` with the challenges
`a 0, a 1, …, a (i−1)` in the order `honest_round_messages` consumes them.

The reindexing `reidx` is the one unavoidable cast: `j + (k + i)` and
`(j + k) + i` are equal but not definitionally so. It is the identity on values
(`reidx_apply`), so it disappears in the campaign, where the table's length is a
single `usize`. -/

/-- Reindexing a table along an equality of exponents; the identity on values. -/
def reidx {A B : ℕ} (h : A = B) (w : Fin (2 ^ A) → F) : Fin (2 ^ B) → F :=
  fun y => w ⟨(y : ℕ), by rw [h]; exact y.isLt⟩

/-- `reidx` reads at the same natural index. -/
theorem reidx_apply {A B : ℕ} (h : A = B) (w : Fin (2 ^ A) → F) (y : Fin (2 ^ B))
    (hy : (y : ℕ) < 2 ^ A) : reidx h w y = w ⟨(y : ℕ), hy⟩ := rfl

/-- `i` layer folds with the challenges `a 0, …, a (i−1)`, least significant
coordinate first -- the order `honest_round_messages` folds in. -/
def foldIter (i : ℕ) (a : ℕ → F) {K : ℕ} (w : Fin (2 ^ (K + i)) → F) : Fin (2 ^ K) → F :=
  match i, w with
  | 0, w => w
  | (i' + 1), w => foldIter i' (fun t => a (t + 1)) (fold w (a 0))

/-- **The whole-run invariant.** Folding the pair -- the low table while it has
more than one entry, the high table afterwards -- is folding the tensor table.
Stated for the first `i ≤ k` rounds, which is the only regime in which the low
table is still being consumed; the remaining rounds are
`fold_tensorTable_scalar` at `k = 0`, i.e. this lemma at `k = 0` with the roles
exchanged. -/
theorem foldIter_tensorTable {j : ℕ} :
    ∀ (i k : ℕ) (a : ℕ → F) (L : Fin (2 ^ (k + i)) → F) (H : Fin (2 ^ j) → F)
      (h : j + (k + i) = (j + k) + i),
      foldIter i a (reidx h (tensorTable (j := j) (k := k + i) L H))
        = tensorTable (j := j) (k := k) (foldIter i a L) H := by
  intro i
  induction i with
  | zero =>
    intro k a L H h
    funext y
    exact congrArg _ (Fin.ext rfl)
  | succ i ih =>
    intro k a L H h
    have h' : j + (k + i) = (j + k) + i := by omega
    have hstep : fold (reidx h (tensorTable (j := j) (k := k + (i + 1)) L H)) (a 0)
        = reidx h' (tensorTable (j := j) (k := k + i) (fold L (a 0)) H) := by
      funext y
      rw [← fold_tensorTable_low (j := j) (k := k + i) L H (a 0)]
      simp only [reidx, fold, lo, hi]
    show foldIter i (fun t => a (t + 1))
        (fold (reidx h (tensorTable (j := j) (k := k + (i + 1)) L H)) (a 0)) = _
    rw [hstep, ih k (fun t => a (t + 1)) (fold L (a 0)) H h']
    rfl

/-! #### 7. The tensor read at a flat index

`tensorTable` is `Fin`-indexed, which the loop invariants cannot be: their
counter is a `Std.Usize` with no arity in its type. `tensorRead` is the same
value read through `getD` at a plain `ℕ`, exactly as `ptFlat` does for a point,
and the two bridges below are the whole of "the Rust's read is the tensor
table". `reidx` disappears in both, which is why the loop invariants may forget
that `low.len() * high.len() = 2 ^ (κ + 1)` and the function specs may not. -/

/-- The Rust's `Ã[idx]`: `low[idx % l] * high[idx / l]`, read through `getD` at a
plain `ℕ` index so that a loop invariant can carry it at its `Std.Usize`
counter. `l` is `low.len()`, which the specs pin to `2 ^ k`. -/
def tensorRead (low high : alloc.vec.Vec cpoly.field.Ext4) (l idx : ℕ) : F :=
  toExt (low.val.getD (idx % l) cpoly.field.Ext4.ZERO)
    * toExt (high.val.getD (idx / l) cpoly.field.Ext4.ZERO)

/-- `tensorRead` at `l = 2 ^ k` is `tensorTable` of the two represented tables:
both sides are the product of the same two `getD` reads, the `Fin` bounds in
`tensorTable` being irrelevant to `getD`. -/
theorem tensorRead_eq_tensorTable {j k : ℕ} (low high : alloc.vec.Vec cpoly.field.Ext4)
    (idx : Fin (2 ^ (j + k))) :
    tensorRead low high (2 ^ k) (idx : ℕ)
      = tensorTable (tableFn (m := k) low) (tableFn (m := j) high) idx := by
  simp only [tensorRead, tensorTable, tableFn_apply]

/-- The same read through the reindexing the function specs carry: `reidx` is the
identity on values (`reidx_apply`), so `j + k = κ + 1` costs nothing here. -/
theorem tensorRead_eq_reidx {j k κ : ℕ} (hjk : j + k = κ + 1)
    (low high : alloc.vec.Vec cpoly.field.Ext4) (y : Fin (2 ^ (κ + 1))) :
    tensorRead low high (2 ^ k) (y : ℕ)
      = reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)) y := by
  simp only [tensorRead, reidx, tensorTable, tableFn_apply]

/-- `linSumAlpha` against the tensor read, as a sum over a range: this is
`linSumAlpha_eq_sum_range` with the `Ã` reads replaced by `tensorRead`, and it is
the shape `round_value_alpha_split`'s loop invariant carries. -/
theorem linSumAlphaSplit_eq_sum_range {j k κ : ℕ} (hjk : j + k = κ + 1)
    (w low high : alloc.vec.Vec cpoly.field.Ext4) (T : F) :
    linSumAlpha (tableFn (m := κ + 1) w)
        (reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high))) T
      = ∑ y ∈ Finset.range (2 ^ κ),
          ((1 - T) * toExt (w.val.getD (2 * y) cpoly.field.Ext4.ZERO) +
              T * toExt (w.val.getD (2 * y + 1) cpoly.field.Ext4.ZERO)) *
            ((1 - T) * tensorRead low high (2 ^ k) (2 * y) +
              T * tensorRead low high (2 ^ k) (2 * y + 1)) := by
  rw [linSumAlpha, ← Fin.sum_univ_eq_sum_range (fun y : ℕ =>
    ((1 - T) * toExt (w.val.getD (2 * y) cpoly.field.Ext4.ZERO) +
        T * toExt (w.val.getD (2 * y + 1) cpoly.field.Ext4.ZERO)) *
      ((1 - T) * tensorRead low high (2 ^ k) (2 * y) +
        T * tensorRead low high (2 ^ k) (2 * y + 1))) (2 ^ κ)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  simp only [fold, tableFn_apply, reidx, tensorTable, tensorRead, lo, hi]

/-- `linSumAlphaFp_eq_sum_range` against the tensor read: the `w̃` fold in
`ZMod q` scaling the fold of the two tensor reads, the `Fp` factor on the left as
the Rust's operand order has it. The shape
`round_value_alpha_base_split`'s loop invariant carries. -/
theorem linSumAlphaSplitFp_eq_sum_range {j k κ : ℕ} (hjk : j + k = κ + 1)
    (w : alloc.vec.Vec cpoly.field.Fp) (low high : alloc.vec.Vec cpoly.field.Ext4)
    (T : ZMod q) :
    linSumAlpha (phiF ∘ tableFnFp (m := κ + 1) w)
        (reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high))) (phiF T)
      = ∑ y ∈ Finset.range (2 ^ κ),
          phiF ((1 - T) * coeffK w (2 * y) + T * coeffK w (2 * y + 1)) *
            ((1 - phiF T) * tensorRead low high (2 ^ k) (2 * y) +
              phiF T * tensorRead low high (2 ^ k) (2 * y + 1)) := by
  rw [linSumAlpha, ← Fin.sum_univ_eq_sum_range (fun y : ℕ =>
    phiF ((1 - T) * coeffK w (2 * y) + T * coeffK w (2 * y + 1)) *
      ((1 - phiF T) * tensorRead low high (2 ^ k) (2 * y) +
        phiF T * tensorRead low high (2 ^ k) (2 * y + 1))) (2 ^ κ)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [map_add, map_mul, map_mul, map_sub, map_one]
  simp only [fold, tableFn_apply, reidx, tensorTable, tensorRead, lo, hi,
    Function.comp_apply, tableFnFp]

/-! #### 8. The two factors, built

`alpha_split_low` and `alpha_split_high` are `alpha_public_mle_eval`'s two table
builders with the folds removed: the prover wants the tables, not their
evaluations. `alpha_split_low` ends in `zerocheck::alpha_pow_table` verbatim, and
`alpha_split_high`'s two loops are **byte-identical** to
`alpha_public_mle_eval_loop2` / `_loop2_loop0`, so those two specs are `rfl`
transports of the ones proved there and cost Aristotle nothing. Only the two
`k`/`sz` doubling loops are new, and they are `alpha_public_mle_eval_loop0`'s
with one component of the state dropped from the `done` value. -/

/-- The doubling loop of `alpha_split_low`: `alpha_public_mle_eval_loop0`'s, but
returning `sz = 2 ^ min m₀ (log₂ d)` rather than the pair -- the low table's
size is all the caller needs.

**Statement delta from `alpha_public_mle_eval_loop0_spec`:** the conclusion is
the second component only, with `k'` eliminated by `k' = min m₀ 10`. The
argument order also differs (`m0` before `degree`), so this is *not* a `rfl`
transport of that loop; the proof is its proof with the `done` value changed.
`sz` never overflows: it doubles only while `sz < d`, so it stays `≤ d = N`. -/
theorem alpha_split_low_loop_spec (m0 k sz : Std.Usize)
    (hk : k.val ≤ min m0.val 10) (hsz : sz.val = 2 ^ k.val) :
    sumcheck.alpha_split_low_loop m0 params.RING_DEGREE k sz
      ⦃ sz' => sz'.val = 2 ^ min m0.val 10 ⦄ := by
  have hrd : (params.RING_DEGREE).val = N := params_RING_DEGREE_val
  have hNmax : N ≤ Usize.max := by
    have hb : (params.RING_DEGREE).val ≤ Usize.max := by
      simp only [params.RING_DEGREE]; scalar_tac
    omega
  have hN : N = 2 ^ 10 := N_eq_two_pow
  rw [sumcheck.alpha_split_low_loop]
  apply loop.spec_decr_nat (fun st => min m0.val 10 - st.1.val)
    (fun st => st.1.val ≤ min m0.val 10 ∧ st.2.val = 2 ^ st.1.val)
  · rintro ⟨k1, s1⟩ ⟨hk1, hs1⟩
    dsimp only at hk1 hs1
    simp only [sumcheck.alpha_split_low_loop.body]
    by_cases hlt : k1 < m0
    · rw [if_pos hlt]
      have hklt : k1.val < m0.val := by scalar_tac
      by_cases hlt2 : s1 < params.RING_DEGREE
      · rw [if_pos hlt2]
        have hsltN : s1.val < N := by rw [← hrd]; scalar_tac
        have hk10 : k1.val < 10 := by
          rcases Nat.lt_or_ge k1.val 10 with h | h
          · exact h
          · exact absurd hsltN (by
              have h1 : (2 : ℕ) ^ 10 ≤ 2 ^ k1.val := Nat.pow_le_pow_right (by norm_num) h
              omega)
        have hdouble : s1.val * 2 = 2 ^ (k1.val + 1) := by rw [pow_succ, hs1]
        have hle : s1.val * 2 ≤ N := by
          rw [hdouble, hN]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        have hbound : s1.val * 2 ≤ Usize.max := le_trans hle hNmax
        step as ⟨s2, hs2⟩
        have hs2v : s2.val = 2 ^ (k1.val + 1) := by rw [← hdouble]; scalar_tac
        step as ⟨k2, hk2⟩
        have hk2v : k2.val = k1.val + 1 := by scalar_tac
        refine ⟨by omega, ?_, by omega⟩
        rw [hs2v, hk2v]
      · rw [if_neg hlt2, WP.spec_ok]
        dsimp only
        have hsgeN : N ≤ s1.val := by rw [← hrd]; scalar_tac
        have h10 : 10 ≤ k1.val := by
          rcases Nat.lt_or_ge k1.val 10 with h | h
          · exact absurd hsgeN (by
              have h1 : (2 : ℕ) ^ k1.val < 2 ^ 10 := Nat.pow_lt_pow_right (by norm_num) h
              omega)
          · exact h
        rw [hs1, show min m0.val 10 = k1.val by omega]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hge : m0.val ≤ k1.val := by scalar_tac
      rw [hs1, show min m0.val 10 = k1.val by omega]
  · exact ⟨hk, hsz⟩

/-- `alpha_split_low` is the low factor of the tensor split: the `2 ^ min m₀ 10`
powers of `α`, i.e. `alphaLowTable (φ α) (min m₀ 10)` as a represented table.

**Statement delta from `alpha_pow_table_spec`** (`lean/ZeroCheck.lean`): the same
table, with the size specialized to `2 ^ min m₀ 10` by the doubling loop above
and the conclusion re-phrased through `WfEvals` / `tableFn` -- the shape the
round specs consume -- instead of `length`/`getD`.
`alphaLowTable_eq_alphaPowTable` (`lean/Opt.lean` § "Candidate J") is the bridge
between the two spellings.

**No side condition.** `2 ^ min m₀ 10 ≤ 2 ^ 10 = N`, a `usize` literal, so the
`Vec` fits and `alpha_pow_table_spec` is itself unconditional. -/
theorem alpha_split_low_spec {m₀ : ℕ} (alpha : cpoly.field.Ext4) (m0 : Std.Usize)
    (ha : Reduced alpha) (hm0v : m0.val = m₀) :
    sumcheck.alpha_split_low alpha m0
      ⦃ out => WfEvals (min m₀ 10) out ∧
        ∀ l : Fin (2 ^ min m₀ 10),
          tableFn (m := min m₀ 10) out l = alphaLowTable (toExt alpha) (min m₀ 10) l ⦄ := by
  rw [sumcheck.alpha_split_low]
  step with alpha_split_low_loop_spec m0 0#usize 1#usize (by simp) (by simp) as ⟨szv, hszv⟩
  rw [hm0v] at hszv
  apply spec_mono (HachiEquiv.ZeroCheck.alpha_pow_table_spec alpha szv ha)
  rintro low ⟨hlowlen, hlowred, hlowval⟩
  rw [hszv] at hlowlen hlowval
  refine ⟨⟨hlowlen, hlowred⟩, fun y => ?_⟩
  rw [tableFn_apply, alphaLowTable]
  exact hlowval y.val y.isLt

/-- The doubling loop of `alpha_split_high`: `alpha_split_low_loop`'s body with
`k` as the `done` value instead of `sz`, because the high table's arity is
`m₀ − k`.

**Statement delta from `alpha_public_mle_eval_loop0_spec`:** the first component
only. -/
theorem alpha_split_high_loop0_spec (m0 k sz : Std.Usize)
    (hk : k.val ≤ min m0.val 10) (hsz : sz.val = 2 ^ k.val) :
    sumcheck.alpha_split_high_loop0 m0 params.RING_DEGREE k sz
      ⦃ k' => k'.val = min m0.val 10 ⦄ := by
  have hrd : (params.RING_DEGREE).val = N := params_RING_DEGREE_val
  have hNmax : N ≤ Usize.max := by
    have hb : (params.RING_DEGREE).val ≤ Usize.max := by
      simp only [params.RING_DEGREE]; scalar_tac
    omega
  have hN : N = 2 ^ 10 := N_eq_two_pow
  rw [sumcheck.alpha_split_high_loop0]
  apply loop.spec_decr_nat (fun st => min m0.val 10 - st.1.val)
    (fun st => st.1.val ≤ min m0.val 10 ∧ st.2.val = 2 ^ st.1.val)
  · rintro ⟨k1, s1⟩ ⟨hk1, hs1⟩
    dsimp only at hk1 hs1
    simp only [sumcheck.alpha_split_high_loop0.body]
    by_cases hlt : k1 < m0
    · rw [if_pos hlt]
      have hklt : k1.val < m0.val := by scalar_tac
      by_cases hlt2 : s1 < params.RING_DEGREE
      · rw [if_pos hlt2]
        have hsltN : s1.val < N := by rw [← hrd]; scalar_tac
        have hk10 : k1.val < 10 := by
          rcases Nat.lt_or_ge k1.val 10 with h | h
          · exact h
          · exact absurd hsltN (by
              have h1 : (2 : ℕ) ^ 10 ≤ 2 ^ k1.val := Nat.pow_le_pow_right (by norm_num) h
              omega)
        have hdouble : s1.val * 2 = 2 ^ (k1.val + 1) := by rw [pow_succ, hs1]
        have hle : s1.val * 2 ≤ N := by
          rw [hdouble, hN]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        have hbound : s1.val * 2 ≤ Usize.max := le_trans hle hNmax
        step as ⟨s2, hs2⟩
        have hs2v : s2.val = 2 ^ (k1.val + 1) := by rw [← hdouble]; scalar_tac
        step as ⟨k2, hk2⟩
        have hk2v : k2.val = k1.val + 1 := by scalar_tac
        refine ⟨by omega, ?_, by omega⟩
        rw [hs2v, hk2v]
      · rw [if_neg hlt2, WP.spec_ok]
        dsimp only
        have hsgeN : N ≤ s1.val := by rw [← hrd]; scalar_tac
        have h10 : 10 ≤ k1.val := by
          rcases Nat.lt_or_ge k1.val 10 with h | h
          · exact absurd hsgeN (by
              have h1 : (2 : ℕ) ^ k1.val < 2 ^ 10 := Nat.pow_lt_pow_right (by norm_num) h
              omega)
          · exact h
        omega
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hge : m0.val ≤ k1.val := by scalar_tac
      omega
  · exact ⟨hk, hsz⟩

/-- The inner loop of `alpha_split_high`'s column loop: the partial row sum
`Σ_{i' < i} eq̃(τ₁, i') · M̃_α(i', u)`.

The extracted body is *identical* to `alpha_public_mle_eval_loop2_loop0`'s --
same guard, same arguments, same order -- so the statement and the proof are that
loop's, transported across the two names. -/
theorem alpha_split_high_loop1_loop0_spec {n μ m₁ : ℕ}
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) (rows cols : Std.Usize)
    (eqw : alloc.vec.Vec cpoly.field.Ext4)
    (mt : alloc.vec.Vec (alloc.vec.Vec cpoly.field.Ext4)) (u : Std.Usize)
    (sum : cpoly.field.Ext4) (i : Std.Usize)
    (hrows : rows.val = n) (hcols : 0 < n → cols.val = μ + n * 8)
    (heqwlen : eqw.val.length = n) (heqwred : VecReduced eqw)
    (heqwval : ∀ t < n, toExt (eqw.val.getD t cpoly.field.Ext4.ZERO) =
      eqWeightVal (m₁ := m₁) tau1 t)
    (hmtlen : mt.val.length = n)
    (hmtval : ∀ (t : ℕ) (ht : t < n),
      (tableRow mt t).val.length = μ + n * 8 ∧ VecReduced (tableRow mt t) ∧
      ∀ c < μ + n * 8, toExt ((tableRow mt t).val.getD c cpoly.field.Ext4.ZERO) =
        InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨t, ht⟩ c)
    (hi : i.val ≤ n) (hRsum : Reduced sum)
    (hval : toExt sum = ∑ t ∈ Finset.range i.val,
      apTerm (m₁ := m₁) rs (toExt alpha) tau1 u.val t) :
    sumcheck.alpha_split_high_loop1_loop0 rows cols eqw mt u sum i
      ⦃ out => Reduced out ∧ toExt out = ∑ t ∈ Finset.range n,
        apTerm (m₁ := m₁) rs (toExt alpha) tau1 u.val t ⦄ := by
  have hsame : sumcheck.alpha_split_high_loop1_loop0 rows cols eqw mt u sum i
      = sumcheck.alpha_public_mle_eval_loop2_loop0 rows cols eqw mt u sum i := rfl
  rw [hsame]
  exact alpha_public_mle_eval_loop2_loop0_spec (m₁ := m₁) rs alpha tau1 rows cols eqw mt u sum i
    hrows hcols heqwlen heqwred heqwval hmtlen hmtval hi hRsum hval

/-- The column loop of `alpha_split_high`: one entry of the high table per step,
each the row sum the inner loop computes.

The extracted body is *identical* to `alpha_public_mle_eval_loop2`'s, so the
statement and the proof are that loop's, transported across the two names. -/
theorem alpha_split_high_loop1_spec {n μ j m₁ : ℕ}
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) (rows cols hsz : Std.Usize)
    (eqw : alloc.vec.Vec cpoly.field.Ext4)
    (mt : alloc.vec.Vec (alloc.vec.Vec cpoly.field.Ext4))
    (out : alloc.vec.Vec cpoly.field.Ext4) (u : Std.Usize)
    (hrows : rows.val = n) (hcols : 0 < n → cols.val = μ + n * 8)
    (hhsz : hsz.val = 2 ^ j)
    (heqwlen : eqw.val.length = n) (heqwred : VecReduced eqw)
    (heqwval : ∀ t < n, toExt (eqw.val.getD t cpoly.field.Ext4.ZERO) =
      eqWeightVal (m₁ := m₁) tau1 t)
    (hmtlen : mt.val.length = n)
    (hmtval : ∀ (t : ℕ) (ht : t < n),
      (tableRow mt t).val.length = μ + n * 8 ∧ VecReduced (tableRow mt t) ∧
      ∀ c < μ + n * 8, toExt ((tableRow mt t).val.getD c cpoly.field.Ext4.ZERO) =
        InnerOuter.mAlphaTilde Φ phiF 16 rs (toExt alpha) ⟨t, ht⟩ c)
    (hu : u.val ≤ 2 ^ j) (hlen : out.val.length = u.val) (hred : VecReduced out)
    (hval : ∀ t < u.val, toExt (out.val.getD t cpoly.field.Ext4.ZERO) =
      ∑ t' ∈ Finset.range n, apTerm (m₁ := m₁) rs (toExt alpha) tau1 t t') :
    sumcheck.alpha_split_high_loop1 rows cols hsz eqw mt out u
      ⦃ o => o.val.length = 2 ^ j ∧ VecReduced o ∧
        ∀ t < 2 ^ j, toExt (o.val.getD t cpoly.field.Ext4.ZERO) =
          ∑ t' ∈ Finset.range n, apTerm (m₁ := m₁) rs (toExt alpha) tau1 t t' ⦄ := by
  have hsame : sumcheck.alpha_split_high_loop1 rows cols hsz eqw mt out u
      = sumcheck.alpha_public_mle_eval_loop2 rows cols hsz eqw mt out u := rfl
  rw [hsame]
  exact alpha_public_mle_eval_loop2_spec (n := n) (μ := μ) (j := j) (m₁ := m₁) rs alpha tau1
    rows cols hsz eqw mt out u hrows hcols hhsz heqwlen heqwred heqwval hmtlen hmtval
    hu hlen hred hval

/-- `alpha_split_high` is the high factor of the tensor split: entry `u` is
`Σᵢ eq̃(τ₁, i) · M̃_α(i, u)`, zero on the unstored columns -- i.e.
`alphaHighTable rs (φ α) τ₁ (m₀ − min m₀ 10)` as a represented table.

**Statement delta from `alpha_public_mle_eval_spec`:** the same hypotheses (its
`WfPoint m₀ a` becomes `m0.val = m₀`, since the arity is now an argument rather
than read off the point), and the conclusion is the *table* rather than its fold
-- the two folds `alpha_public_mle_eval` runs after building it are what this
item drops. `alphaHighTable_eq_apTerm_sum` is the bridge from the loop's row sum
to `alphaHighTable`.

`2 ^ m₀ ≤ Usize.max` is `cube_size`'s, at the high block's `2 ^ (m₀ − k)`;
`hmax` is `m_alpha_table_spec`'s, the checked `mu + rows · δ` being formed here
too. -/
theorem alpha_split_high_spec {n μ m₀ m₁ : ℕ} (s : ringswitch.RlinStatement)
    (rs : InnerOuter.RlinStatement Φ n μ) (alpha : cpoly.field.Ext4)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) (m0 : Std.Usize)
    (hs : RepRlin (n := n) (μ := μ) s rs) (ha : Reduced alpha) (ht : WfPoint m₁ tau1)
    (hm0v : m0.val = m₀) (hm0 : 2 ^ m₀ ≤ Usize.max) (hmax : μ + n * 8 ≤ Usize.max) :
    sumcheck.alpha_split_high s alpha tau1 m0
      ⦃ out => WfEvals (m₀ - min m₀ 10) out ∧
        ∀ u : Fin (2 ^ (m₀ - min m₀ 10)),
          tableFn (m := m₀ - min m₀ 10) out u
            = alphaHighTable rs (toExt alpha) (toPoint (m := m₁) tau1)
                (m₀ - min m₀ 10) u ⦄ := by
  have hWm : WfRlinMat n μ s.m := hs.1
  have hgd : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  have hklem : min m₀ 10 ≤ m₀ := alphaSplit_le m₀
  rw [sumcheck.alpha_split_high]
  simp only [ringswitch.RlinStatement.impl.m, bind_tc_ok]
  step with ZeroCheck.rlin_rows_spec (n := n) (μ := μ) s.m hWm as ⟨rows, hrows⟩
  step with ZeroCheck.rlin_cols_le_spec (n := n) (μ := μ) s.m hWm as ⟨mu, hmule, hmu⟩
  have hmulbound : rows.val * (params.GADGET_DIGITS).val ≤ Usize.max := by
    rw [hrows, hgd]; omega
  step as ⟨j1, hj1⟩
  have hj1v : j1.val = n * 8 := by rw [hj1, hrows, hgd]
  have haddbound : mu.val + j1.val ≤ Usize.max := by rw [hj1v]; omega
  step as ⟨cols, hcols⟩
  have hcolsv : 0 < n → cols.val = μ + n * 8 := by
    intro hn; rw [hcols, hmu hn, hj1v]
  step with alpha_split_high_loop0_spec m0 0#usize 1#usize (by simp) (by simp) as ⟨kv, hkv⟩
  rw [hm0v] at hkv
  have hsub : m0.val - kv.val ≤ Usize.max := by scalar_tac
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = m₀ - min m₀ 10 := by rw [hi2, hm0v, hkv]
  step with cube_size_spec i2 (by
    rw [hi2v]
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hm0) as ⟨hsz, hhsz⟩
  rw [hi2v] at hhsz
  step with eq_weight_table_spec (m₁ := m₁) tau1 rows ht
    as ⟨eqw, heqwlen, heqwred, heqwval⟩
  rw [hrows] at heqwlen heqwval
  step with m_alpha_table_spec (n := n) (μ := μ) s rs alpha hs ha hmax
    as ⟨mt, hmtlen, hmtval⟩
  apply spec_mono (alpha_split_high_loop1_spec (n := n) (μ := μ) (j := m₀ - min m₀ 10)
    (m₁ := m₁) rs alpha tau1 rows cols hsz eqw mt
    (alloc.vec.Vec.with_capacity cpoly.field.Ext4 hsz) 0#usize hrows hcolsv hhsz
    heqwlen heqwred heqwval hmtlen hmtval (by simp)
    (by simp [alloc.vec.Vec.with_capacity])
    (by intro y hy; simp [alloc.vec.Vec.with_capacity] at hy)
    (by intro t ht'; simp at ht'))
  rintro high1 ⟨hhlen, hhred, hhval⟩
  refine ⟨⟨hhlen, hhred⟩, fun y => ?_⟩
  rw [tableFn_apply, alphaHighTable_eq_apTerm_sum]
  exact hhval y.val y.isLt

/-! #### 9. One round's fold of the pair

`alpha_split_fold` is the `eval_mle_layer` of the champion: the fold acts on
`low` while `low` has more than one entry and on `high` afterwards. The spec is
`eval_mle_layer_spec`'s (`lean/ZeroCheck.lean`) twice, once per branch, plus the
tensor conjunct that makes the headline's invariant step a single `step with`:
the two branches are exactly `fold_tensorTable_low` and
`fold_tensorTable_scalar` above. -/

/-- One round's fold of the two factors. The guard `1 < low.len()` is `0 < k`,
so the two branches are indexed by `k = k' + 1` and `k = 0`; the second needs
`0 < j` as well, which `hjk` supplies (there is always a coordinate left to
fold). Each branch states both the carrier fact (`WfEvals` + the pointwise
`fold`) and the tensor fact the headline's `hav` invariant steps through.

**No value bound.** `eval_mle_layer` is called on a `Vec` of `2 ^ (k' + 1)` (resp.
`2 ^ (j' + 1)`) entries and returns half of them, and the untouched factor is
returned unchanged; nothing here forms a value the caller must bound. -/
theorem alpha_split_fold_spec {j k : ℕ} (low high : alloc.vec.Vec cpoly.field.Ext4)
    (a : cpoly.field.Ext4)
    (hlow : WfEvals k low) (hhigh : WfEvals j high) (hRa : Reduced a) (hjk : 0 < j + k) :
    sumcheck.alpha_split_fold low high a
      ⦃ p =>
        (∀ k' : ℕ, k = k' + 1 →
            WfEvals k' p.1 ∧ p.2 = high ∧
            (∀ y : Fin (2 ^ k'), tableFn (m := k') p.1 y
                = fold (tableFn (m := k' + 1) low) (toExt a) y) ∧
            (∀ z : Fin (2 ^ (j + k')),
              tensorTable (tableFn (m := k') p.1) (tableFn (m := j) p.2) z
                = fold (k := j + k') (tensorTable (j := j) (k := k' + 1)
                    (tableFn (m := k' + 1) low) (tableFn (m := j) high)) (toExt a) z)) ∧
        (∀ j' : ℕ, k = 0 → j = j' + 1 →
            p.1 = low ∧ WfEvals j' p.2 ∧
            (∀ y : Fin (2 ^ j'), tableFn (m := j') p.2 y
                = fold (tableFn (m := j' + 1) high) (toExt a) y) ∧
            (∀ z : Fin (2 ^ (j' + 0)),
              tensorTable (tableFn (m := 0) p.1) (tableFn (m := j') p.2) z
                = fold (k := j') (tensorTable (j := j' + 1) (k := 0)
                    (tableFn (m := 0) low) (tableFn (m := j' + 1) high)) (toExt a) z)) ⦄ := by
  have hlowlen : low.val.length = 2 ^ k := hlow.1
  rw [sumcheck.alpha_split_fold]
  match k, hlow with
  | (k' + 1), hlow =>
    have hgt : (1#usize : Std.Usize) < alloc.vec.Vec.len low := by
      have : (alloc.vec.Vec.len low).val = 2 ^ (k' + 1) := by simp [hlowlen]
      have h2 : 2 ≤ 2 ^ (k' + 1) := by
        calc (2:ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      scalar_tac
    rw [if_pos hgt]
    step with eval_mle_layer_spec (k := k') low a hlow hRa as ⟨low1, hW1, hv1⟩
    refine ⟨fun k'' hk'' => ?_, fun j' hk0 _ => by exact absurd hk0 (by omega)⟩
    obtain rfl : k'' = k' := (Nat.succ_injective hk'').symm
    refine ⟨hW1, hv1, fun z => ?_⟩
    rw [fold_tensorTable_low]
    simp only [tensorTable, hv1]
  | 0, hlow =>
    have hgt : ¬ ((1#usize : Std.Usize) < alloc.vec.Vec.len low) := by
      have : (alloc.vec.Vec.len low).val = 1 := by simp [hlowlen]
      scalar_tac
    rw [if_neg hgt]
    match j, hhigh, hjk with
    | (j' + 1), hhigh, _ =>
      step with eval_mle_layer_spec (k := j') high a hhigh hRa as ⟨high1, hW1, hv1⟩
      refine ⟨fun k'' hk'' => by exact absurd hk''.symm (by omega), fun j'' hj'' => ?_⟩
      obtain rfl : j'' = j' := (Nat.succ_injective hj'').symm
      refine ⟨hW1, hv1, fun z => ?_⟩
      rw [fold_tensorTable_scalar]
      simp only [tensorTable, hv1]

/-! #### 10. The linear summand off the split read

The six items of `round_poly_alpha` / `round_poly_alpha_base` again, with `Ã`
read as `low[idx % l] * high[idx / l]`. The specifications' right-hand sides do
not move: each is its flat twin's, with `tableFn (m := κ + 1) a_tab` replaced by
`reidx hjk (tensorTable (tableFn low) (tableFn high))` -- the same function,
since `reidx` is the identity on values and `hjk : j + k = κ + 1` is the usize
fact `low.len() * high.len() = w.len()`.

`0 < low.len()` is what makes the `%` and `/` of the loop body total, and it is
`WfEvals k low`; `idx / 2 ^ k < 2 ^ j = high.len()` is what makes the `high` read
in range, and it is `hjk`. -/

/-- The accumulator loop of `round_value_alpha_split`.

**Statement delta from `round_value_alpha_spec`'s inline invariant:** the two
`a_tab` reads at `2y` and `2y + 1` become `tensorRead low high (2 ^ k)` at the
same indices; nothing else moves. -/
theorem round_value_alpha_split_loop_spec {j k κ : ℕ} (hjk : j + k = κ + 1)
    (w low high : alloc.vec.Vec cpoly.field.Ext4) (node : cpoly.field.Ext4)
    (half l : Std.Usize) (one_minus acc : cpoly.field.Ext4) (y : Std.Usize)
    (hw : WfEvals (κ + 1) w) (hlow : WfEvals k low) (hhigh : WfEvals j high)
    (hn : Reduced node) (hRom : Reduced one_minus)
    (hom : toExt one_minus = 1 - toExt node)
    (hhalf : half.val = 2 ^ κ) (hl : l.val = 2 ^ k)
    (hy : y.val ≤ 2 ^ κ) (hRacc : Reduced acc)
    (hacc : toExt acc = ∑ t ∈ Finset.range y.val,
      ((1 - toExt node) * toExt (w.val.getD (2 * t) cpoly.field.Ext4.ZERO) +
          toExt node * toExt (w.val.getD (2 * t + 1) cpoly.field.Ext4.ZERO)) *
        ((1 - toExt node) * tensorRead low high (2 ^ k) (2 * t) +
          toExt node * tensorRead low high (2 ^ k) (2 * t + 1))) :
    sumcheck.round_value_alpha_split_loop w low high node half l one_minus acc y
      ⦃ out => Reduced out ∧
        toExt out = linSumAlpha (tableFn (m := κ + 1) w)
          (reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
          (toExt node) ⦄ := by
  obtain ⟨hwlen, hwred⟩ := hw
  obtain ⟨hlowlen, hlowred⟩ := hlow
  obtain ⟨hhighlen, hhighred⟩ := hhigh
  have hwmax : w.val.length ≤ Usize.max := w.property
  have htwo : (2 : ℕ) ^ k * 2 ^ j = 2 ^ (κ + 1) := by rw [← pow_add]; congr 1; omega
  rw [sumcheck.round_value_alpha_split_loop]
  apply loop.spec_decr_nat (fun s => 2 ^ κ - s.2.val)
    (fun s => s.2.val ≤ 2 ^ κ ∧ Reduced s.1 ∧
      toExt s.1 = ∑ t ∈ Finset.range s.2.val,
        ((1 - toExt node) * toExt (w.val.getD (2 * t) cpoly.field.Ext4.ZERO) +
            toExt node * toExt (w.val.getD (2 * t + 1) cpoly.field.Ext4.ZERO)) *
          ((1 - toExt node) * tensorRead low high (2 ^ k) (2 * t) +
            toExt node * tensorRead low high (2 ^ k) (2 * t + 1)))
  · rintro ⟨acc1, y1⟩ ⟨hy1, hRacc1, hacc1⟩
    dsimp only at hy1 hRacc1 hacc1
    simp only [sumcheck.round_value_alpha_split_loop.body]
    by_cases hlt : y1 < half
    · rw [if_pos hlt]
      have hylt : y1.val < 2 ^ κ := by
        have : y1.val < half.val := by scalar_tac
        omega
      have hpow : (2 : ℕ) ^ (κ + 1) = 2 * 2 ^ κ := by ring
      have h2y : 2 * y1.val + 1 < w.val.length := by rw [hwlen]; omega
      have hmul : 2 * y1.val ≤ Usize.max := by omega
      have hlpos : 0 < l.val := by rw [hl]; positivity
      step as ⟨i, hi⟩
      have hib : i.val < w.val.length := by rw [hi]; omega
      step as ⟨e, he⟩
      have hRe : Reduced e := he ▸ hwred _ (List.getElem_mem hib)
      step as ⟨e1, hRe1, he1⟩
      step as ⟨i1, hi1⟩
      have hi1b : i1.val < w.val.length := by rw [hi1, hi]; omega
      step as ⟨e2, he2⟩
      have hRe2 : Reduced e2 := he2 ▸ hwred _ (List.getElem_mem hi1b)
      step as ⟨e3, hRe3, he3⟩
      step as ⟨wf, hRwf, hwf⟩
      -- the low read at `2y`
      step as ⟨i2, hi2⟩
      have hi2b : i2.val < low.val.length := by
        rw [hlowlen, hi2, hl]; exact Nat.mod_lt _ (by positivity)
      step as ⟨e4, he4⟩
      have hRe4 : Reduced e4 := he4 ▸ hlowred _ (List.getElem_mem hi2b)
      step as ⟨i3, hi3⟩
      have hi3b : i3.val < high.val.length := by
        rw [hhighlen, hi3, hi, hl]
        refine Nat.div_lt_of_lt_mul ?_
        rw [htwo]
        omega
      step as ⟨e5, he5⟩
      have hRe5 : Reduced e5 := he5 ▸ hhighred _ (List.getElem_mem hi3b)
      step as ⟨la, hRla, hla⟩
      -- the low read at `2y + 1`
      step as ⟨i4, hi4⟩
      step as ⟨i5, hi5⟩
      have hi5b : i5.val < low.val.length := by
        rw [hlowlen, hi5, hl]; exact Nat.mod_lt _ (by positivity)
      step as ⟨e6, he6⟩
      have hRe6 : Reduced e6 := he6 ▸ hlowred _ (List.getElem_mem hi5b)
      step as ⟨i6, hi6⟩
      step as ⟨i7, hi7⟩
      have hi7b : i7.val < high.val.length := by
        rw [hhighlen, hi7, hi6, hi, hl]
        refine Nat.div_lt_of_lt_mul ?_
        rw [htwo]
        omega
      step as ⟨e7, he7⟩
      have hRe7 : Reduced e7 := he7 ▸ hhighred _ (List.getElem_mem hi7b)
      step as ⟨ha1, hRha1, hha1⟩
      step as ⟨e8, hRe8, he8⟩
      step as ⟨e9, hRe9, he9⟩
      step as ⟨af, hRaf, haf⟩
      step as ⟨e10, hRe10, he10⟩
      step as ⟨acc2, hRacc2, hacc2⟩
      step as ⟨y2, hy2⟩
      refine ⟨by scalar_tac, hRacc2, ?_, by scalar_tac⟩
      rw [hacc2, hacc1, hy2, Finset.sum_range_succ, he10, hwf, haf, he1, he3, he8, he9,
        hla, hha1, he4, he5, he6, he7, hom, he, he2,
        ← List.getD_eq_getElem w.val cpoly.field.Ext4.ZERO hib,
        ← List.getD_eq_getElem w.val cpoly.field.Ext4.ZERO hi1b,
        ← List.getD_eq_getElem low.val cpoly.field.Ext4.ZERO hi2b,
        ← List.getD_eq_getElem high.val cpoly.field.Ext4.ZERO hi3b,
        ← List.getD_eq_getElem low.val cpoly.field.Ext4.ZERO hi5b,
        ← List.getD_eq_getElem high.val cpoly.field.Ext4.ZERO hi7b]
      simp only [tensorRead, hi1, hi2, hi3, hi5, hi7, hi6, hi4, hi, hl]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hyeq : y1.val = 2 ^ κ := by
        have : half.val ≤ y1.val := by scalar_tac
        omega
      refine ⟨hRacc1, ?_⟩
      rw [hacc1, hyeq, linSumAlphaSplit_eq_sum_range hjk]
  · exact ⟨hy, hRacc, hacc⟩

/-- `round_value_alpha_split` at one node is `linSumAlpha` against the tensor
table -- `round_value_alpha_spec`'s conclusion with the split read substituted.

**Statement delta from `round_value_alpha_spec`:** `ha : WfEvals (k + 1) a_tab`
splits into `hlow`/`hhigh` plus the usize fact `hjk`, which is the length side
condition `low.len() * high.len() = w.len()`. -/
theorem round_value_alpha_split_spec {j k κ : ℕ} (hjk : j + k = κ + 1)
    (w low high : alloc.vec.Vec cpoly.field.Ext4) (node : cpoly.field.Ext4)
    (hw : WfEvals (κ + 1) w) (hlow : WfEvals k low) (hhigh : WfEvals j high)
    (hn : Reduced node) :
    sumcheck.round_value_alpha_split w low high node
      ⦃ out => Reduced out ∧
        toExt out = linSumAlpha (tableFn (m := κ + 1) w)
          (reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
          (toExt node) ⦄ := by
  have hwlen : w.val.length = 2 ^ (κ + 1) := hw.1
  have hlowlen : low.val.length = 2 ^ k := hlow.1
  have hR1 : Reduced cpoly.field.Ext4.ONE := reduced_ONE
  have hRZ : Reduced cpoly.field.Ext4.ZERO := reduced_ZERO
  rw [sumcheck.round_value_alpha_split]
  step as ⟨half, hhalf⟩
  have hlenw : (alloc.vec.Vec.len w).val = w.val.length := by simp
  have hhalfv : half.val = 2 ^ κ := by
    rw [hhalf, hlenw, hwlen, pow_succ]
    omega
  step as ⟨om, hRom, hom⟩
  exact round_value_alpha_split_loop_spec hjk w low high node half
    (alloc.vec.Vec.len low) om cpoly.field.Ext4.ZERO 0#usize hw hlow hhigh hn hRom
    (by rw [hom, toExt_ONE]) hhalfv (by simp [hlowlen]) (by simp) hRZ (by simp)

/-- The node loop of `round_values_alpha_split`: `round_values_alpha_spec`'s
inline invariant with the split read substituted. -/
theorem round_values_alpha_split_loop_spec {j k κ : ℕ} (hjk : j + k = κ + 1)
    (w low high out : alloc.vec.Vec cpoly.field.Ext4) (t : Std.Usize)
    (hw : WfEvals (κ + 1) w) (hlow : WfEvals k low) (hhigh : WfEvals j high)
    (ht : t.val ≤ 3) (hlen : out.val.length = t.val) (hred : VecReduced out)
    (hval : ∀ u < t.val, toExt (out.val.getD u cpoly.field.Ext4.ZERO) =
      linSumAlpha (tableFn (m := κ + 1) w)
        (reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
        ((u : ℕ) : F)) :
    sumcheck.round_values_alpha_split_loop w low high params.ROUND_NODES_ALPHA out t
      ⦃ o => o.val.length = 3 ∧ VecReduced o ∧
        ∀ u < 3, toExt (o.val.getD u cpoly.field.Ext4.ZERO) =
          linSumAlpha (tableFn (m := κ + 1) w)
            (reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
            ((u : ℕ) : F) ⦄ := by
  have hrn : (params.ROUND_NODES_ALPHA).val = 3 := by simp [params.ROUND_NODES_ALPHA]
  have hmax := usize_max_ge
  rw [sumcheck.round_values_alpha_split_loop]
  apply loop.spec_decr_nat (fun s => 3 - s.2.val)
    (fun s => s.2.val ≤ 3 ∧ s.1.val.length = s.2.val ∧ VecReduced s.1 ∧
      ∀ u : ℕ, u < s.2.val → toExt (s.1.val.getD u cpoly.field.Ext4.ZERO) =
        linSumAlpha (tableFn (m := κ + 1) w)
          (reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
          ((u : ℕ) : F))
  · rintro ⟨v1, t1⟩ ⟨ht1, hlen1, hred1, hval1⟩
    dsimp only at ht1 hlen1 hred1 hval1
    simp only [sumcheck.round_values_alpha_split_loop.body]
    by_cases hlt : t1 < params.ROUND_NODES_ALPHA
    · rw [if_pos hlt]
      have ht1lt : t1.val < 3 := by scalar_tac
      step with round_node_spec t1 as ⟨nd, hRnd, hnd⟩
      step with round_value_alpha_split_spec hjk w low high nd hw hlow hhigh hRnd
        as ⟨e, hRe, he⟩
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
      · intro u hu
        rw [ht2n] at hu
        rcases Nat.lt_or_ge u t1.val with hult | huge
        · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 u hult]
        · have hteq : u = v1.val.length := by omega
          rw [hteq, hv2, getD_append_eq, he, hnd, hlen1]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hteq : t1.val = 3 := by scalar_tac
      exact ⟨by rw [hlen1, hteq], hred1, fun u hu => hval1 u (by omega)⟩
  · exact ⟨ht, hlen, hred, hval⟩

/-- `round_values_alpha_split`: the `3` node values of `linSumAlpha` against the
tensor table, at `0, 1, 2` -- `round_values_alpha_spec` with the split read
substituted. -/
theorem round_values_alpha_split_spec {j k κ : ℕ} (hjk : j + k = κ + 1)
    (w low high : alloc.vec.Vec cpoly.field.Ext4)
    (hw : WfEvals (κ + 1) w) (hlow : WfEvals k low) (hhigh : WfEvals j high) :
    sumcheck.round_values_alpha_split w low high
      ⦃ out => out.val.length = 3 ∧ VecReduced out ∧
        ∀ t : Fin 3, toExt (out.val.getD t.val cpoly.field.Ext4.ZERO) =
          linSumAlpha (tableFn (m := κ + 1) w)
            (reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
            (t.val : F) ⦄ := by
  rw [sumcheck.round_values_alpha_split]
  apply spec_mono (round_values_alpha_split_loop_spec hjk w low high
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize hw hlow hhigh (by simp) (by simp)
    (by intro u hu; simp at hu) (by intro u hu; simp at hu))
  rintro o ⟨holen, hored, hoval⟩
  exact ⟨holen, hored, fun t => hoval t.val t.isLt⟩

/-- `round_poly_alpha_split` interpolates the `3` node values, and the
interpolant is `linSumAlpha` against the tensor table everywhere
(`linSumAlpha_poly`: degree `≤ 2 < 3`) -- `round_poly_alpha_spec` with the split
read substituted. -/
theorem round_poly_alpha_split_spec {j k κ : ℕ} (hjk : j + k = κ + 1)
    (w low high : alloc.vec.Vec cpoly.field.Ext4)
    (hw : WfEvals (κ + 1) w) (hlow : WfEvals k low) (hhigh : WfEvals j high) :
    sumcheck.round_poly_alpha_split w low high
      ⦃ out => out.val.length = 3 ∧ VecReduced out ∧
        ∀ x : F, CPolynomial.eval x (toUni out) =
          linSumAlpha (tableFn (m := κ + 1) w)
            (reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
            x ⦄ := by
  rw [sumcheck.round_poly_alpha_split]
  step with round_values_alpha_split_spec hjk w low high hw hlow hhigh
    as ⟨values, hvlen, hvred, hvval⟩
  step with round_node_weights_alpha_spec as ⟨weights, hwtlen, hwtred, hwtval⟩
  obtain ⟨p, hpdeg, hpval⟩ :=
    linSumAlpha_poly (tableFn (m := κ + 1) w)
      (reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
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

/-! #### 11. The same three at round 0, in the base field

`Ã` carries `α` and `τ₁`, so both factors stay in the extension from round 0 on;
what moves into `ZMod q` is the `w̃` fold. These are
`round_value_alpha_base_spec` / `round_values_alpha_base_spec` /
`round_poly_alpha_base_spec` with the split read substituted, exactly as
subsection 10 is the extension-field trio. -/

/-- The accumulator loop of `round_value_alpha_base_split`.

**Statement delta from `round_value_alpha_base_spec`'s inline invariant:** the
two `a_tab` reads become `tensorRead low high (2 ^ k)`. -/
theorem round_value_alpha_base_split_loop_spec {j k κ : ℕ} (hjk : j + k = κ + 1)
    (w : alloc.vec.Vec cpoly.field.Fp) (low high : alloc.vec.Vec cpoly.field.Ext4)
    (node : cpoly.field.Fp) (half l : Std.Usize) (one_minus : cpoly.field.Fp)
    (node_ext one_minus_ext acc : cpoly.field.Ext4) (y : Std.Usize)
    (hw : WfEvalsFp (κ + 1) w) (hlow : WfEvals k low) (hhigh : WfEvals j high)
    (hn : Red node) (hRom : Red one_minus) (hom : toK one_minus = 1 - toK node)
    (hRne : Reduced node_ext) (hne : toExt node_ext = phiF (toK node))
    (hRome : Reduced one_minus_ext)
    (home : toExt one_minus_ext = 1 - phiF (toK node))
    (hhalf : half.val = 2 ^ κ) (hl : l.val = 2 ^ k)
    (hy : y.val ≤ 2 ^ κ) (hRacc : Reduced acc)
    (hacc : toExt acc = ∑ t ∈ Finset.range y.val,
      phiF ((1 - toK node) * coeffK w (2 * t) + toK node * coeffK w (2 * t + 1)) *
        ((1 - phiF (toK node)) * tensorRead low high (2 ^ k) (2 * t) +
          phiF (toK node) * tensorRead low high (2 ^ k) (2 * t + 1))) :
    sumcheck.round_value_alpha_base_split_loop w low high node half l one_minus
        node_ext one_minus_ext acc y
      ⦃ out => Reduced out ∧
        toExt out = linSumAlpha (phiF ∘ tableFnFp (m := κ + 1) w)
          (reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
          (phiF (toK node)) ⦄ := by
  obtain ⟨hwlen, hwred⟩ := hw
  obtain ⟨hlowlen, hlowred⟩ := hlow
  obtain ⟨hhighlen, hhighred⟩ := hhigh
  have hwmax : w.val.length ≤ Usize.max := w.property
  have htwo : (2 : ℕ) ^ k * 2 ^ j = 2 ^ (κ + 1) := by rw [← pow_add]; congr 1; omega
  rw [sumcheck.round_value_alpha_base_split_loop]
  apply loop.spec_decr_nat (fun s => 2 ^ κ - s.2.val)
    (fun s => s.2.val ≤ 2 ^ κ ∧ Reduced s.1 ∧
      toExt s.1 = ∑ t ∈ Finset.range s.2.val,
        phiF ((1 - toK node) * coeffK w (2 * t) + toK node * coeffK w (2 * t + 1)) *
          ((1 - phiF (toK node)) * tensorRead low high (2 ^ k) (2 * t) +
            phiF (toK node) * tensorRead low high (2 ^ k) (2 * t + 1)))
  · rintro ⟨acc1, y1⟩ ⟨hy1, hRacc1, hacc1⟩
    dsimp only at hy1 hRacc1 hacc1
    simp only [sumcheck.round_value_alpha_base_split_loop.body]
    by_cases hlt : y1 < half
    · rw [if_pos hlt]
      have hylt : y1.val < 2 ^ κ := by
        have : y1.val < half.val := by scalar_tac
        omega
      have hpow : (2 : ℕ) ^ (κ + 1) = 2 * 2 ^ κ := by ring
      have h2y : 2 * y1.val + 1 < w.val.length := by rw [hwlen]; omega
      have hmul : 2 * y1.val ≤ Usize.max := by omega
      have hlpos : 0 < l.val := by rw [hl]; positivity
      step as ⟨i, hi⟩
      have hib : i.val < w.val.length := by rw [hi]; omega
      step as ⟨wlo, hwlo⟩
      have hRwlo : Red wlo := hwlo ▸ hwred _ (List.getElem_mem hib)
      step as ⟨f1, hRf1, hf1⟩
      step as ⟨i1, hi1⟩
      have hi1b : i1.val < w.val.length := by rw [hi1, hi]; omega
      step as ⟨whi, hwhi⟩
      have hRwhi : Red whi := hwhi ▸ hwred _ (List.getElem_mem hi1b)
      step as ⟨f3, hRf3, hf3⟩
      step as ⟨wf, hRwf, hwf⟩
      step as ⟨i2, hi2⟩
      have hi2b : i2.val < low.val.length := by
        rw [hlowlen, hi2, hl]; exact Nat.mod_lt _ (by positivity)
      step as ⟨e, he⟩
      have hRe : Reduced e := he ▸ hlowred _ (List.getElem_mem hi2b)
      step as ⟨i3, hi3⟩
      have hi3b : i3.val < high.val.length := by
        rw [hhighlen, hi3, hi, hl]
        refine Nat.div_lt_of_lt_mul ?_
        rw [htwo]
        omega
      step as ⟨e1, he1⟩
      have hRe1 : Reduced e1 := he1 ▸ hhighred _ (List.getElem_mem hi3b)
      step as ⟨la, hRla, hla⟩
      step as ⟨i4, hi4⟩
      step as ⟨i5, hi5⟩
      have hi5b : i5.val < low.val.length := by
        rw [hlowlen, hi5, hl]; exact Nat.mod_lt _ (by positivity)
      step as ⟨e2, he2⟩
      have hRe2 : Reduced e2 := he2 ▸ hlowred _ (List.getElem_mem hi5b)
      step as ⟨i6, hi6⟩
      step as ⟨i7, hi7⟩
      have hi7b : i7.val < high.val.length := by
        rw [hhighlen, hi7, hi6, hi, hl]
        refine Nat.div_lt_of_lt_mul ?_
        rw [htwo]
        omega
      step as ⟨e3, he3⟩
      have hRe3 : Reduced e3 := he3 ▸ hhighred _ (List.getElem_mem hi7b)
      step as ⟨ha1, hRha1, hha1⟩
      step as ⟨e4, hRe4, he4⟩
      step as ⟨e5, hRe5, he5⟩
      step as ⟨af, hRaf, haf⟩
      step with fp_ext_mul_spec wf af hRwf hRaf as ⟨e6, hRe6, he6⟩
      step as ⟨acc2, hRacc2, hacc2⟩
      step as ⟨y2, hy2⟩
      refine ⟨by scalar_tac, hRacc2, ?_, by scalar_tac⟩
      have he6' : toExt e6 = phiF (toK wf) * toExt af := by rw [he6, phiF_apply]
      have hentry : toExt e6 =
          phiF ((1 - toK node) * coeffK w (2 * y1.val) + toK node * coeffK w (2 * y1.val + 1)) *
            ((1 - phiF (toK node)) * tensorRead low high (2 ^ k) (2 * y1.val) +
              phiF (toK node) * tensorRead low high (2 ^ k) (2 * y1.val + 1)) := by
        rw [he6', hwf, hf1, hf3, hom, haf, he4, he5, home, hne, hla, hha1, he, he1, he2, he3,
          coeffK, coeffK, hwlo, hwhi,
          ← List.getD_eq_getElem w.val cpoly.field.Fp.ZERO hib,
          ← List.getD_eq_getElem w.val cpoly.field.Fp.ZERO hi1b,
          ← List.getD_eq_getElem low.val cpoly.field.Ext4.ZERO hi2b,
          ← List.getD_eq_getElem high.val cpoly.field.Ext4.ZERO hi3b,
          ← List.getD_eq_getElem low.val cpoly.field.Ext4.ZERO hi5b,
          ← List.getD_eq_getElem high.val cpoly.field.Ext4.ZERO hi7b]
        simp only [tensorRead, hi1, hi2, hi3, hi5, hi7, hi6, hi4, hi, hl]
      rw [hacc2, hacc1, hy2, Finset.sum_range_succ, hentry]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hyeq : y1.val = 2 ^ κ := by
        have : half.val ≤ y1.val := by scalar_tac
        omega
      refine ⟨hRacc1, ?_⟩
      rw [hacc1, hyeq, linSumAlphaSplitFp_eq_sum_range hjk]
  · exact ⟨hy, hRacc, hacc⟩

/-- `round_value_alpha_base_split` at one node is `linSumAlpha` at the embedded
`w̃` table against the tensor table -- `round_value_alpha_base_spec` with the
split read substituted. -/
theorem round_value_alpha_base_split_spec {j k κ : ℕ} (hjk : j + k = κ + 1)
    (w : alloc.vec.Vec cpoly.field.Fp) (low high : alloc.vec.Vec cpoly.field.Ext4)
    (node : cpoly.field.Fp)
    (hw : WfEvalsFp (κ + 1) w) (hlow : WfEvals k low) (hhigh : WfEvals j high)
    (hn : Red node) :
    sumcheck.round_value_alpha_base_split w low high node
      ⦃ out => Reduced out ∧
        toExt out = linSumAlpha (phiF ∘ tableFnFp (m := κ + 1) w)
          (reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
          (phiF (toK node)) ⦄ := by
  have hwlen : w.val.length = 2 ^ (κ + 1) := hw.1
  have hlowlen : low.val.length = 2 ^ k := hlow.1
  have hR1 : Red cpoly.field.Fp.ONE := Red_one
  have hE1 : Reduced cpoly.field.Ext4.ONE := reduced_ONE
  have hRZ : Reduced cpoly.field.Ext4.ZERO := reduced_ZERO
  rw [sumcheck.round_value_alpha_base_split]
  step as ⟨half, hhalf⟩
  have hlenw : (alloc.vec.Vec.len w).val = w.val.length := by simp
  have hhalfv : half.val = 2 ^ κ := by
    rw [hhalf, hlenw, hwlen, pow_succ]
    omega
  step as ⟨om, hRom, hom⟩
  step with ext_from_base_spec node hn as ⟨ne, hRne, hne⟩
  have hne' : toExt ne = phiF (toK node) := by rw [hne, phiF_apply]
  step as ⟨ome, hRome, home⟩
  exact round_value_alpha_base_split_loop_spec hjk w low high node half
    (alloc.vec.Vec.len low) om ne ome cpoly.field.Ext4.ZERO 0#usize hw hlow hhigh hn hRom
    (by rw [hom, toK_one]) hRne hne' hRome (by rw [home, hne', toExt_ONE]) hhalfv
    (by simp [hlowlen]) (by simp) hRZ (by simp)

/-- The node loop of `round_values_alpha_base_split`:
`round_values_alpha_base_spec`'s inline invariant with the split read
substituted. The nodes are the embedded `Fp::new t`. -/
theorem round_values_alpha_base_split_loop_spec {j k κ : ℕ} (hjk : j + k = κ + 1)
    (w : alloc.vec.Vec cpoly.field.Fp)
    (low high out : alloc.vec.Vec cpoly.field.Ext4) (t : Std.Usize)
    (hw : WfEvalsFp (κ + 1) w) (hlow : WfEvals k low) (hhigh : WfEvals j high)
    (ht : t.val ≤ 3) (hlen : out.val.length = t.val) (hred : VecReduced out)
    (hval : ∀ u < t.val, toExt (out.val.getD u cpoly.field.Ext4.ZERO) =
      linSumAlpha (phiF ∘ tableFnFp (m := κ + 1) w)
        (reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
        ((u : ℕ) : F)) :
    sumcheck.round_values_alpha_base_split_loop w low high params.ROUND_NODES_ALPHA out t
      ⦃ o => o.val.length = 3 ∧ VecReduced o ∧
        ∀ u < 3, toExt (o.val.getD u cpoly.field.Ext4.ZERO) =
          linSumAlpha (phiF ∘ tableFnFp (m := κ + 1) w)
            (reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
            ((u : ℕ) : F) ⦄ := by
  have hrn : (params.ROUND_NODES_ALPHA).val = 3 := by simp [params.ROUND_NODES_ALPHA]
  have hmax := usize_max_ge
  rw [sumcheck.round_values_alpha_base_split_loop]
  apply loop.spec_decr_nat (fun s => 3 - s.2.val)
    (fun s => s.2.val ≤ 3 ∧ s.1.val.length = s.2.val ∧ VecReduced s.1 ∧
      ∀ u : ℕ, u < s.2.val → toExt (s.1.val.getD u cpoly.field.Ext4.ZERO) =
        linSumAlpha (phiF ∘ tableFnFp (m := κ + 1) w)
          (reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
          ((u : ℕ) : F))
  · rintro ⟨v1, t1⟩ ⟨ht1, hlen1, hred1, hval1⟩
    dsimp only at ht1 hlen1 hred1 hval1
    simp only [sumcheck.round_values_alpha_base_split_loop.body]
    by_cases hlt : t1 < params.ROUND_NODES_ALPHA
    · rw [if_pos hlt]
      have ht1lt : t1.val < 3 := by scalar_tac
      step with node_cast_spec t1 as ⟨u, hu⟩
      step with fp_new_spec u as ⟨nd, hRnd, hnd⟩
      step with round_value_alpha_base_split_spec hjk w low high nd hw hlow hhigh hRnd
        as ⟨e, hRe, he⟩
      have hbound : v1.val.length < Usize.max := by omega
      step as ⟨v2, hv2⟩
      step as ⟨t2, ht2⟩
      have ht2n : t2.val = t1.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, ?_, ?_, by scalar_tac⟩
      · rw [ht2n, hv2, List.length_append, hlen1]; simp
      · intro u' hu'
        rw [hv2] at hu'
        rcases List.mem_append.mp hu' with h | h
        · exact hred1 u' h
        · rw [List.mem_singleton.mp h]; exact hRe
      · intro t ht
        rw [ht2n] at ht
        rcases Nat.lt_or_ge t t1.val with htlt | htge
        · rw [hv2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = v1.val.length := by omega
          rw [hteq, hv2, getD_append_eq, he, hnd, hu, hlen1, phiF_apply, ofBase_natCast]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hteq : t1.val = 3 := by scalar_tac
      exact ⟨by rw [hlen1, hteq], hred1, fun u hu => hval1 u (by omega)⟩
  · exact ⟨ht, hlen, hred, hval⟩

/-- `round_values_alpha_base_split`: the `3` node values at the embedded nodes
`Fp::new 0, 1, 2` -- `round_values_alpha_base_spec` with the split read
substituted. -/
theorem round_values_alpha_base_split_spec {j k κ : ℕ} (hjk : j + k = κ + 1)
    (w : alloc.vec.Vec cpoly.field.Fp) (low high : alloc.vec.Vec cpoly.field.Ext4)
    (hw : WfEvalsFp (κ + 1) w) (hlow : WfEvals k low) (hhigh : WfEvals j high) :
    sumcheck.round_values_alpha_base_split w low high
      ⦃ out => out.val.length = 3 ∧ VecReduced out ∧
        ∀ t : Fin 3, toExt (out.val.getD t.val cpoly.field.Ext4.ZERO) =
          linSumAlpha (phiF ∘ tableFnFp (m := κ + 1) w)
            (reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
            (t.val : F) ⦄ := by
  rw [sumcheck.round_values_alpha_base_split]
  apply spec_mono (round_values_alpha_base_split_loop_spec hjk w low high
    (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize hw hlow hhigh (by simp) (by simp)
    (by intro u hu; simp at hu) (by intro u hu; simp at hu))
  rintro o ⟨holen, hored, hoval⟩
  exact ⟨holen, hored, fun t => hoval t.val t.isLt⟩

/-- `round_poly_alpha_base_split` interpolates the `3` base-field node values,
and the interpolant is `linSumAlpha` at the embedded table against the tensor
table everywhere -- `round_poly_alpha_base_spec` with the split read
substituted. -/
theorem round_poly_alpha_base_split_spec {j k κ : ℕ} (hjk : j + k = κ + 1)
    (w : alloc.vec.Vec cpoly.field.Fp) (low high : alloc.vec.Vec cpoly.field.Ext4)
    (hw : WfEvalsFp (κ + 1) w) (hlow : WfEvals k low) (hhigh : WfEvals j high) :
    sumcheck.round_poly_alpha_base_split w low high
      ⦃ out => out.val.length = 3 ∧ VecReduced out ∧
        ∀ x : F, CPolynomial.eval x (toUni out) =
          linSumAlpha (phiF ∘ tableFnFp (m := κ + 1) w)
            (reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
            x ⦄ := by
  rw [sumcheck.round_poly_alpha_base_split]
  step with round_values_alpha_base_split_spec hjk w low high hw hlow hhigh
    as ⟨values, hvlen, hvred, hvval⟩
  step with round_node_weights_alpha_spec as ⟨weights, hwtlen, hwtred, hwtval⟩
  obtain ⟨p, hpdeg, hpval⟩ :=
    linSumAlpha_poly (phiF ∘ tableFnFp (m := κ + 1) w)
      (reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
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

/-! #### 12. The round message off the pair

`honest_compute_g_split` and `honest_compute_g_base_split` are
`honest_compute_g` / `honest_compute_g_base` with `a_tab` replaced by the pair:
the zero side is untouched (same `round_poly_zero` / `round_poly_zero_base`, same
prefix and free factor), and only `g_alpha` goes through the `_split` round
polynomial. The conclusions are therefore **verbatim** their twins': the same
`RepRoundMsg out (honestComputeG …)`. What moves is `hav`, which now says that
the *tensor table* of the two factors tabulates the public MLE at the round's
hypercube points. -/

/-- `honest_compute_g_split` computes `honestComputeG` off the two factors:
`honest_compute_g_spec`'s statement with `a_tab` replaced by `(low, high)` and
`hav` stated on `tensorTable (tableFn low) (tableFn high)`.

**Statement delta from `honest_compute_g_spec`:** `ha : WfEvals (M + 1 − i) a_tab`
becomes `hlow : WfEvals k low`, `hhigh : WfEvals j high` and the usize fact
`hjk : j + k = M + 1 − i`; `hav` reads the tensor table through `reidx hjk`
instead of `tableFn a_tab`. The conclusion is unchanged, which is what makes the
champion produce the same wire message. The proof is the twin's with
`round_poly_alpha_split_spec` in place of `round_poly_alpha_spec`.

No value bound, for `honest_compute_g_spec`'s reasons: every read is inside a
length the relations fix, and the two polynomial products have `33 + 2`
coefficients. -/
theorem honest_compute_g_split_spec {n μ M m₁ dRows j k : ℕ} (stmt : sumcheck.RoundStatement)
    (w_tab low high : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize)
    (ss : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ (M + 1) m₁ i.val)
    (sw : InnerOuter.LiftedWitness Φ μ n)
    (hs : RepRoundStmt (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := i.val) (dRows := dRows)
      stmt ss)
    (hi : i.val < M + 1) (hjk : j + k = M + 1 - i.val)
    (hw : WfEvals (M + 1 - i.val) w_tab)
    (hlow : WfEvals k low) (hhigh : WfEvals j high)
    (hwv : ∀ y : Fin (M + 1 - i.val) → Fin 2,
      tableFn (m := M + 1 - i.val) w_tab (finFunctionFinEquiv y) =
        InnerOuter.wTableMleEval Φ (M + 1) phiF 16 sw
          (InnerOuter.hypercubePoint (M + 1) i.val ss.challenges y))
    (hav : ∀ y : Fin (M + 1 - i.val) → Fin 2,
      reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high))
          (finFunctionFinEquiv y) =
        (InnerOuter.cMultilinearExtension (M + 1)
          (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)).eval
          (InnerOuter.hypercubePoint (M + 1) i.val ss.challenges y)) :
    sumcheck.honest_compute_g_split stmt w_tab low high i
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
  have hjk' : j + k = (M + 1 - i.val - 1) + 1 := by omega
  have hcube : 2 ^ (M + 1 - i.val) ≤ Usize.max := by
    have hlen := hw.1
    have := w_tab.property
    omega
  simp only [sumcheck.honest_compute_g_split, sumcheck.RoundStatement.impl.zc,
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
  step with poly_mul_spec inner free hinred hfreered
    (by rw [hinlen, hfreelen]; have := usize_max_ge; omega) as ⟨wf, hwfred, hwfraw, hwflen⟩
  step with uni_smul_spec pref wf hRpref hwfred as ⟨gz, hgzred, hgzraw⟩
  step with round_poly_alpha_split_spec hjk' w_tab low high hw' hlow hhigh
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
  have hgv : ∀ y : Fin (M + 1 - i.val) → Fin 2,
      tensorRead low high (2 ^ k)
          ((finFunctionFinEquiv y : Fin (2 ^ (M + 1 - i.val))) : ℕ)
        = (InnerOuter.cMultilinearExtension (M + 1)
            (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)).eval
            (InnerOuter.hypercubePoint (M + 1) i.val ss.challenges y) := by
    intro y
    rw [← hav y]
    simp only [tensorRead, reidx, tensorTable, tableFn_apply]
  have hfolda : ∀ (x : F) (z : Fin (M + 1 - i.val - 1) → Fin 2),
      fold (reidx hjk' (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
          x (finFunctionFinEquiv z)
        = (InnerOuter.cMultilinearExtension (M + 1)
            (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)).eval
            (InnerOuter.hypercubePoint (M + 1) (i.val + 1) (Fin.snoc ss.challenges x) z) := by
    intro x z
    have hstep := fold_natTable_eq_mle (M := M) (i := i.val) (k := M + 1 - i.val - 1) hi rfl
      (fun t => tensorRead low high (2 ^ k) t)
      (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)
      ss.challenges x hgv z
    rw [show (fun j : Fin (M + 1 - i.val - 1) => z (Fin.cast rfl j)) = z from rfl] at hstep
    rw [show (reidx hjk' (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
        = (fun y : Fin (2 ^ ((M + 1 - i.val - 1) + 1)) =>
            tensorRead low high (2 ^ k) (y : ℕ)) from
      funext fun y => (tensorRead_eq_reidx hjk' low high y).symm]
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

/-- `honest_compute_g_base_split` computes `honestComputeG` at round `0` off the
two factors and a base-field witness table: `honest_compute_g_base_spec`'s
statement with `a_tab` replaced by `(low, high)`.

**Statement delta from `honest_compute_g_base_spec`:** as for
`honest_compute_g_split_spec`, at `i = 0` -- so `hjk : j + k = M + 1`, which at
round `0` is `min (M+1) 10 + ((M+1) − min (M+1) 10) = M + 1`, the two arities
`alpha_split_low_spec` and `alpha_split_high_spec` deliver. The proof is the
twin's with `round_poly_alpha_base_split_spec` in place of
`round_poly_alpha_base_spec`. -/
theorem honest_compute_g_base_split_spec {n μ M m₁ dRows j k : ℕ}
    (stmt : sumcheck.RoundStatement) (w_fp : alloc.vec.Vec cpoly.field.Fp)
    (low high : alloc.vec.Vec cpoly.field.Ext4)
    (ss : InnerOuter.NestedRoundStatement Φ (PolyVec (Rq Φ) dRows) F n μ (M + 1) m₁ 0)
    (sw : InnerOuter.LiftedWitness Φ μ n)
    (hs : RepRoundStmt (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := 0) (dRows := dRows)
      stmt ss)
    (hjk : j + k = M + 1)
    (hw : WfEvalsFp (M + 1) w_fp)
    (hlow : WfEvals k low) (hhigh : WfEvals j high)
    (hwv : ∀ y : Fin (M + 1) → Fin 2,
      phiF (tableFnFp (m := M + 1) w_fp (finFunctionFinEquiv y)) =
        InnerOuter.wTableMleEval Φ (M + 1) phiF 16 sw
          (InnerOuter.hypercubePoint (M + 1) 0 ss.challenges y))
    (hav : ∀ y : Fin (M + 1) → Fin 2,
      reidx hjk (tensorTable (tableFn (m := k) low) (tableFn (m := j) high))
          (finFunctionFinEquiv y) =
        (InnerOuter.cMultilinearExtension (M + 1)
          (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)).eval
          (InnerOuter.hypercubePoint (M + 1) 0 ss.challenges y)) :
    sumcheck.honest_compute_g_base_split stmt w_fp low high
      ⦃ out => RepRoundMsg out
        (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF 0 (Nat.succ_pos M) ss sw) ⦄ := by
  obtain ⟨hzc, hWc, hRt0, hRta, hc, ht0, hta⟩ := hs
  obtain ⟨hr, hWt, hWa, hW0, hW1, htv, hav', h0v, h1v⟩ := hzc
  obtain ⟨h0len, h0red⟩ := hW0
  have hi : (0 : ℕ) < M + 1 := Nat.succ_pos M
  have hjk' : j + k = M + 1 := hjk
  have hM1 : M + 1 ≤ Usize.max := by
    have := stmt.zc.tau0.property
    omega
  have hcube : 2 ^ (M + 1) ≤ Usize.max := by
    have hlen := hw.1
    have := w_fp.property
    omega
  simp only [sumcheck.honest_compute_g_base_split, sumcheck.RoundStatement.impl.zc,
    sumcheck.NestedZeroCheckStmt.impl.tau0, sumcheck.RoundStatement.impl.challenges, bind_tc_ok]
  step with eq_prefix_spec (m₀ := M + 1) (i := 0) stmt.zc.tau0 stmt.challenges
    ⟨h0len, h0red⟩ hWc (by omega) as ⟨pref, hRpref, hprefv⟩
  have hsub0 : M + 1 - (0#usize : Std.Usize).val - 1 = M := by scalar_tac
  step with eq_suffix_table_spec (m₀ := M + 1) stmt.zc.tau0 0#usize ⟨h0len, h0red⟩
    (by scalar_tac)
    (by
      rw [hsub0]
      have hmono : (2 : ℕ) ^ M ≤ 2 ^ (M + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega)
      as ⟨suffix, hWsuf, hsufv⟩
  have hsufv' : toEvals (m := M) suffix =
      CMlPolynomialEval.lagrangeBasis (Vector.ofFn fun k : Fin M =>
        toPoint (m := M + 1) stmt.zc.tau0 ⟨0 + 1 + k.val, by have := k.isLt; omega⟩) := hsufv
  step with round_poly_zero_base_spec (k := M) w_fp suffix hw hWsuf
    as ⟨inner, hinlen, hinred, hinval⟩
  step as ⟨e, he⟩
  have hRe : Reduced e := he ▸ h0red _ (List.getElem_mem (by omega))
  step with eq_free_factor_spec e hRe as ⟨free, hfreelen, hfreered, hfreeval⟩
  step with poly_mul_spec inner free hinred hfreered
    (by rw [hinlen, hfreelen]; have := usize_max_ge; omega) as ⟨wf, hwfred, hwfraw, hwflen⟩
  step with uni_smul_spec pref wf hRpref hwfred as ⟨gz, hgzred, hgzraw⟩
  step with round_poly_alpha_base_split_spec hjk' w_fp low high hw hlow hhigh
    as ⟨ga, hgalen, hgared, hgaval⟩
  have hwv2 : ∀ y : Fin (M + 1) → Fin 2,
      phiF (tableFnFp (m := M + 1) w_fp (finFunctionFinEquiv y))
        = (InnerOuter.cMultilinearExtension (M + 1)
            (InnerOuter.wTable Φ (M + 1) phiF 16 sw)).eval
            (InnerOuter.hypercubePoint (M + 1) 0 ss.challenges y) := by
    intro y
    rw [hwv y, InnerOuter.wTableMleEval_eq, InnerOuter.cMultilinearExtension_eval]
  have hfoldw : ∀ (x : F) (z : Fin M → Fin 2),
      fold (phiF ∘ tableFnFp (m := M + 1) w_fp) x (finFunctionFinEquiv z)
        = InnerOuter.wTableMleEval Φ (M + 1) phiF 16 sw
            (InnerOuter.hypercubePoint (M + 1) (0 + 1) (Fin.snoc ss.challenges x) z) := by
    intro x z
    have hstep := fold_tableFnFp_eq_mle (M := M) (i := 0) (k := M) hi rfl w_fp
      (InnerOuter.wTable Φ (M + 1) phiF 16 sw) ss.challenges x hwv2 z
    rw [show (fun j : Fin M => z (Fin.cast rfl j)) = z from rfl] at hstep
    rw [hstep, InnerOuter.wTableMleEval_eq, InnerOuter.cMultilinearExtension_eval]
  have hgv : ∀ y : Fin (M + 1) → Fin 2,
      tensorRead low high (2 ^ k) ((finFunctionFinEquiv y : Fin (2 ^ (M + 1))) : ℕ)
        = (InnerOuter.cMultilinearExtension (M + 1)
            (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)).eval
            (InnerOuter.hypercubePoint (M + 1) 0 ss.challenges y) := by
    intro y
    rw [← hav y]
    simp only [tensorRead, reidx, tensorTable, tableFn_apply]
  have hfolda : ∀ (x : F) (z : Fin M → Fin 2),
      fold (reidx hjk' (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
          x (finFunctionFinEquiv z)
        = (InnerOuter.cMultilinearExtension (M + 1)
            (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)).eval
            (InnerOuter.hypercubePoint (M + 1) (0 + 1) (Fin.snoc ss.challenges x) z) := by
    intro x z
    have hstep := fold_natTable_eq_mle (M := M) (i := 0) (k := M) hi rfl
      (fun t => tensorRead low high (2 ^ k) t)
      (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)
      ss.challenges x hgv z
    rw [show (fun j : Fin M => z (Fin.cast rfl j)) = z from rfl] at hstep
    rw [show (reidx hjk' (tensorTable (tableFn (m := k) low) (tableFn (m := j) high)))
        = (fun y : Fin (2 ^ (M + 1)) => tensorRead low high (2 ^ k) (y : ℕ)) from
      funext fun y => (tensorRead_eq_reidx hjk' low high y).symm]
    exact hstep
  have hre : ∀ f : Fin (2 ^ M) → F,
      ∑ Y : Fin (2 ^ M), f Y = ∑ z : Fin M → Fin 2, f (finFunctionFinEquiv z) :=
    fun f => (Fintype.sum_equiv finFunctionFinEquiv _ f (fun _ => rfl)).symm
  have htau : ∀ (j : ℕ) (h : j < M + 1),
      ss.zc.τ₀ ⟨j, h⟩ = toExt (stmt.zc.tau0.val.getD j cpoly.field.Ext4.ZERO) := by
    intro j h
    rw [← h0v]
    rfl
  have hev : toExt e = ss.zc.τ₀ ⟨0, hi⟩ := by
    rw [htau 0 hi, he, List.getD_eq_getElem _ _ (by omega)]
  have hpref : toExt pref
      = eqProd (fun j : Fin 0 => ss.zc.τ₀ (Fin.castLE (by omega) j)) ss.challenges := by
    rw [hprefv, hc, h0v]
  have hsuf : ∀ z : Fin M → Fin 2,
      tableFn (m := M) suffix (finFunctionFinEquiv z)
        = ∏ j : Fin (M + 1 - (0 + 1)),
            (if z j = 1 then ss.zc.τ₀ ⟨0 + 1 + j.val, by have := j.isLt; omega⟩
              else 1 - ss.zc.τ₀ ⟨0 + 1 + j.val, by have := j.isLt; omega⟩) := by
    intro z
    rw [tableFn, hsufv', lagrangeBasis_get_cube]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Vector.get_ofFn, htau (0 + 1 + j.val) (by have := j.isLt; omega)]
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
        (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF 0 hi ss sw).1.2) ?_
    intro x
    rw [toUni_eval, hgzraw, raw_eval_smul, hwfraw, raw_eval_mul, ← toUni_eval inner,
      ← toUni_eval free, hinval x, hfreeval x]
    show _ = CPolynomial.eval x
      (InnerOuter.computableRoundPoly
        (InnerOuter.sumcheckPolyZero Φ (M + 1) phiF 16 ss.zc.τ₀ sw) ⟨0, hi⟩ ss.challenges)
    have hHS : InnerOuter.hypercubeSum (M + 1)
        (InnerOuter.sumcheckPolyZero Φ (M + 1) phiF 16 ss.zc.τ₀ sw) (0 + 1)
        (Fin.snoc ss.challenges x)
        = ∑ z : Fin M → Fin 2,
            (InnerOuter.sumcheckPolyZero Φ (M + 1) phiF 16 ss.zc.τ₀ sw).eval
              (InnerOuter.hypercubePoint (M + 1) (0 + 1) (Fin.snoc ss.challenges x) z) := rfl
    rw [InnerOuter.computableRoundPoly_eval, hHS]
    have hterm : ∀ z : Fin M → Fin 2,
        (InnerOuter.sumcheckPolyZero Φ (M + 1) phiF 16 ss.zc.τ₀ sw).eval
            (InnerOuter.hypercubePoint (M + 1) (0 + 1) (Fin.snoc ss.challenges x) z)
          = toExt pref * (tableFn (m := M) suffix (finFunctionFinEquiv z)
              * InnerOuter.rangeProduct 16
                (fold (phiF ∘ tableFnFp (m := M + 1) w_fp) x (finFunctionFinEquiv z)))
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
      (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF 0 hi ss sw).2.2 ?_
    intro x
    rw [hgaval x]
    show linSumAlpha _ _ x = CPolynomial.eval x
      (InnerOuter.computableRoundPoly
        (InnerOuter.sumcheckPolyAlpha Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα sw)
        ⟨0, hi⟩ ss.challenges)
    have hHS : InnerOuter.hypercubeSum (M + 1)
        (InnerOuter.sumcheckPolyAlpha Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα sw)
        (0 + 1) (Fin.snoc ss.challenges x)
        = ∑ z : Fin M → Fin 2,
            (InnerOuter.sumcheckPolyAlpha Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα sw).eval
              (InnerOuter.hypercubePoint (M + 1) (0 + 1) (Fin.snoc ss.challenges x) z) := rfl
    rw [InnerOuter.computableRoundPoly_eval, hHS, linSumAlpha, hre]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [InnerOuter.eval_sumcheckPolyAlpha, hfoldw x z, hfolda x z]
/-! ## The two halves of the rounds, separately -/

/-- **One round's step of the tensor invariant.** The Rust's `Ã` reads are the
tensor table of the two factors; this is the fact that one `alpha_split_fold`
carries the round-`i` tabulation of the public multilinear extension to the
round-`(i+1)` one, stated at the ℕ-level fold relation both branches of
`alpha_split_fold_spec` deliver (`tensorRead` at the halved index). It is
`fold_natTable_eq_mle` at the reader `fun t => tensorRead low high (2 ^ k) t`,
with `reidx` erased on both sides -- the shape `honest_round_messages`'s loop
invariant steps through. -/
theorem tensor_invariant_step {M : ℕ} (EV : (Fin (M + 1) → Fin 2) → F)
    (i : ℕ) (him : i < M + 1) (jj kk jj1 kk1 : ℕ)
    (hjk : jj + kk = M + 1 - i) (hjk1 : jj1 + kk1 = M + 1 - (i + 1))
    (low high low1 high1 : alloc.vec.Vec cpoly.field.Ext4) (x : F) (cs : Fin i → F)
    (hav : ∀ y : Fin (M + 1 - i) → Fin 2,
      reidx hjk (tensorTable (tableFn (m := kk) low) (tableFn (m := jj) high))
          (finFunctionFinEquiv y)
        = (InnerOuter.cMultilinearExtension (M + 1) EV).eval
            (InnerOuter.hypercubePoint (M + 1) i cs y))
    (hfold : ∀ t : ℕ, t < 2 ^ (jj1 + kk1) →
      tensorRead low1 high1 (2 ^ kk1) t
        = (1 - x) * tensorRead low high (2 ^ kk) (2 * t)
          + x * tensorRead low high (2 ^ kk) (2 * t + 1)) :
    ∀ y : Fin (M + 1 - (i + 1)) → Fin 2,
      reidx hjk1 (tensorTable (tableFn (m := kk1) low1) (tableFn (m := jj1) high1))
          (finFunctionFinEquiv y)
        = (InnerOuter.cMultilinearExtension (M + 1) EV).eval
            (InnerOuter.hypercubePoint (M + 1) (i + 1) (Fin.snoc cs x) y) := by
  intro y
  have hgv : ∀ z : Fin (M + 1 - i) → Fin 2,
      (fun t => tensorRead low high (2 ^ kk) t)
          ((finFunctionFinEquiv z : Fin (2 ^ (M + 1 - i))) : ℕ)
        = (InnerOuter.cMultilinearExtension (M + 1) EV).eval
            (InnerOuter.hypercubePoint (M + 1) i cs z) := by
    intro z
    rw [← hav z]
    simp only [tensorRead, reidx, tensorTable, tableFn_apply]
  have hstep := fold_natTable_eq_mle (M := M) (i := i) (k := M + 1 - (i + 1)) him rfl
    (fun t => tensorRead low high (2 ^ kk) t) EV cs x hgv y
  rw [show (fun j : Fin (M + 1 - (i + 1)) => y (Fin.cast rfl j)) = y from rfl] at hstep
  have hb : ((finFunctionFinEquiv y : Fin (2 ^ (M + 1 - (i + 1)))) : ℕ) < 2 ^ (jj1 + kk1) := by
    rw [hjk1]; exact (finFunctionFinEquiv y).isLt
  rw [← hstep]
  calc reidx hjk1 (tensorTable (tableFn (m := kk1) low1) (tableFn (m := jj1) high1))
          (finFunctionFinEquiv y)
      = tensorRead low1 high1 (2 ^ kk1)
          ((finFunctionFinEquiv y : Fin (2 ^ (M + 1 - (i + 1)))) : ℕ) := by
        simp only [reidx, tensorTable, tableFn_apply, tensorRead]
    _ = (1 - x) * tensorRead low high (2 ^ kk)
            (2 * ((finFunctionFinEquiv y : Fin (2 ^ (M + 1 - (i + 1)))) : ℕ))
          + x * tensorRead low high (2 ^ kk)
            (2 * ((finFunctionFinEquiv y : Fin (2 ^ (M + 1 - (i + 1)))) : ℕ) + 1) := hfold _ hb
    _ = fold (fun z : Fin (2 ^ ((M + 1 - (i + 1)) + 1)) =>
            tensorRead low high (2 ^ kk) (z : ℕ)) x (finFunctionFinEquiv y) := by
        simp only [fold, lo, ZeroCheck.hi]

set_option maxHeartbeats 2000000 in
/-- `honest_round_messages` is the prover's half of `round_loop`: the `m₀` wire
messages `honestComputeG` produces along `honestRounds` (spec: `roundProver`
at `computeG := honestComputeG`, `Rounds.lean:157`, one per round of
`roundsReductionAux`). Same tables, same folds, same `round_out` threading as
`round_loop`, but no check and the messages are what comes out. `challenges`
must hold `m₀` entries, read at `challenges[i]`; `out.push` is bounded by it.

**Round 0 is peeled** (candidate I, `lean/Opt.lean` § "Candidate I"): the
witness table is built in the base field by `c_w_table_fp`, the first message
comes from `honest_compute_g_base`, and `eval_mle_layer_base` produces the
extension table the loop from round 1 on consumes exactly as before. The
statement is unchanged -- the peel is what the proof has to absorb, not what the
theorem says. Since `m₀ = M + 1`, the `0 < m₀` guard is always taken and the
`else` branch of the extracted body is unreachable; the loop's invariant is the
frozen one at initial index `j = 1`, which the peeled round establishes with the
same four steps the old first iteration used. -/
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
  have hzero : (0 : ℕ) < M + 1 := Nat.succ_pos M
  have hkle : min (M + 1) 10 ≤ M + 1 := alphaSplit_le (M + 1)
  have hjk0 : (M + 1 - min (M + 1) 10) + min (M + 1) 10 = M + 1 := Nat.sub_add_cancel hkle
  obtain ⟨k0', hk0'⟩ : ∃ t, min (M + 1) 10 = t + 1 := ⟨min (M + 1) 10 - 1, by omega⟩
  simp only [sumcheck.honest_round_messages, sumcheck.RoundStatement.impl.zc,
    sumcheck.NestedZeroCheckStmt.impl.tau0, sumcheck.NestedZeroCheckStmt.impl.rlin,
    sumcheck.NestedZeroCheckStmt.impl.alpha, sumcheck.NestedZeroCheckStmt.impl.tau1,
    bind_tc_ok]
  step with alpha_split_low_spec (m₀ := M + 1) stmt.zc.alpha
    (alloc.vec.Vec.len stmt.zc.tau0) hWa hm0len as ⟨low, hWlow0, hlowtab⟩
  step with alpha_split_high_spec (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) stmt.zc.rlin
    ss.zc.rlin stmt.zc.alpha stmt.zc.tau1 (alloc.vec.Vec.len stmt.zc.tau0) hr hWa hW1
    hm0len hm0 hmax as ⟨high, hWhigh0, hhightab⟩
  rw [halv] at hlowtab
  rw [halv, h1v] at hhightab
  have hav0 : ∀ y : Fin (M + 1) → Fin 2,
      reidx hjk0 (tensorTable (tableFn (m := min (M + 1) 10) low)
          (tableFn (m := M + 1 - min (M + 1) 10) high)) (finFunctionFinEquiv y)
        = (InnerOuter.cMultilinearExtension (M + 1)
            (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)).eval
            (InnerOuter.hypercubePoint (M + 1) 0 ss.challenges y) := by
    intro y
    rw [show tableFn (m := min (M + 1) 10) low = alphaLowTable ss.zc.α (min (M + 1) 10) from
        funext hlowtab,
      show tableFn (m := M + 1 - min (M + 1) 10) high
          = alphaHighTable ss.zc.rlin ss.zc.α ss.zc.τα (M + 1 - min (M + 1) 10) from
        funext hhightab]
    simp only [reidx]
    rw [← alphaPublicEvals_eq_tensorTable ss.zc.rlin ss.zc.α ss.zc.τα (M + 1) y _ rfl,
      hypercubePoint_zero]
    exact (InnerOuter.cMultilinearExtension_eval_boolean (M + 1)
      (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα) y).symm
  rw [if_pos (show (0#usize : Std.Usize) < alloc.vec.Vec.len stmt.zc.tau0 from by scalar_tac)]
  step with c_w_table_fp_spec (μ := μ) (n := n) w sw (alloc.vec.Vec.len stmt.zc.tau0) hw
    (by rw [hm0len]; exact hm0) hmax as ⟨w_fp, hfplen, hfpred, hfpval⟩
  rw [hm0len] at hfplen hfpval
  have hWfp : WfEvalsFp (M + 1) w_fp := ⟨hfplen, hfpred⟩
  have hwv0 := initial_w_table_fp (μ := μ) (n := n) (M := M) w_fp sw ss.challenges hfpval
  step with honest_compute_g_base_split_spec (n := n) (μ := μ) (M := M) (m₁ := m₁)
    (dRows := dRows) (j := M + 1 - min (M + 1) 10) (k := min (M + 1) 10)
    stmt w_fp low high ss sw hs hjk0 hWfp hWlow0 hWhigh0 hwv0 hav0 as ⟨g0, hg0rep⟩
  have hich : (0 : ℕ) < challenges.val.length := by omega
  step as ⟨a0, ha0v⟩
  have hRa0 : Reduced a0 := ha0v ▸ hcred _ (List.getElem_mem hich)
  have ha0val : toExt a0 = cs ⟨0, hzero⟩ := by
    rw [hcs]
    simp only [toPoint]
    rw [ha0v, List.getD_eq_getElem _ _ hich]
  step with round_out_spec (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := 0)
    (dRows := dRows) stmt g0 a0 ss
    (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF 0 hzero ss sw) hs hg0rep hRa0
    (by omega) as ⟨cur1, hrep1⟩
  step with eval_mle_layer_base_table_spec (M := M) (i := 0) hzero w_fp
    (InnerOuter.wTable Φ (M + 1) phiF 16 sw) ss.challenges a0 hWfp hRa0
    (by
      intro y
      rw [hwv0 y, InnerOuter.wTableMleEval_eq, InnerOuter.cMultilinearExtension_eval])
      as ⟨wt1, hWw1, hwv1⟩
  step with alpha_split_fold_spec (j := M + 1 - min (M + 1) 10) (k := min (M + 1) 10)
    low high a0 hWlow0 hWhigh0 hRa0 (by omega) as ⟨low1, high1, hfA0, hfB0⟩
  obtain ⟨hWlow1, hhigh1eq, hlow1v, htens0⟩ := hfA0 k0' hk0'
  have hjk1 : (M + 1 - min (M + 1) 10) + k0' = M + 1 - (0 + 1) := by omega
  have hfold0 : ∀ t : ℕ, t < 2 ^ ((M + 1 - min (M + 1) 10) + k0') →
      tensorRead low1 high1 (2 ^ k0') t
        = (1 - toExt a0) * tensorRead low high (2 ^ min (M + 1) 10) (2 * t)
          + toExt a0 * tensorRead low high (2 ^ min (M + 1) 10) (2 * t + 1) := by
    intro t ht
    have h := htens0 ⟨t, ht⟩
    rw [hk0']
    simpa only [tensorTable, tableFn_apply, tensorRead, fold, lo, ZeroCheck.hi] using h
  have hav1 := tensor_invariant_step
    (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)
    0 hzero (M + 1 - min (M + 1) 10) (min (M + 1) 10) (M + 1 - min (M + 1) 10) k0'
    hjk0 hjk1 low high low1 high1 (toExt a0) ss.challenges hav0 hfold0
  have hpush0 : (alloc.vec.Vec.new sumcheck.RoundMsg).val.length < Usize.max := by simp; omega
  step as ⟨out1, hout1⟩
  have hnext1 : honestRounds ss sw cs 1 (by omega)
      = InnerOuter.roundOut Φ (M + 1) m₁ 16 ss
          (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF 0 hzero ss sw)
          (cs ⟨0, hzero⟩) := rfl
  rw [ha0val] at hrep1 hwv1 hav1
  have houtlen1 : out1.val.length = 1 := by rw [hout1, List.length_append]; simp
  have houtrep1 : ∀ (k : ℕ) (hk : k < 1),
      RepRoundMsg
        (out1.val.getD k { g_zero := alloc.vec.Vec.new cpoly.field.Ext4,
                           g_alpha := alloc.vec.Vec.new cpoly.field.Ext4 })
        (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF k (by omega)
          (honestRounds ss sw cs k (by omega)) sw) := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    have hg : out1.val.getD 0 { g_zero := alloc.vec.Vec.new cpoly.field.Ext4,
                                g_alpha := alloc.vec.Vec.new cpoly.field.Ext4 } = g0 := by
      rw [hout1]; simp
    rw [hg]
    exact hg0rep
  rw [sumcheck.honest_round_messages_loop]
  apply loop.spec_decr_nat (fun st => M + 1 - st.2.2.2.2.2.val)
    (fun st => ∃ (j : ℕ) (hj : j ≤ M + 1), st.2.2.2.2.2.val = j ∧
      RepRoundStmt (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := j)
          (dRows := dRows) st.2.2.1 (honestRounds ss sw cs j hj) ∧
        WfEvals (M + 1 - j) st.2.2.2.2.1 ∧
        (∀ y : Fin (M + 1 - j) → Fin 2,
          tableFn (m := M + 1 - j) st.2.2.2.2.1 (finFunctionFinEquiv y) =
            InnerOuter.wTableMleEval Φ (M + 1) phiF 16 sw
              (InnerOuter.hypercubePoint (M + 1) j (honestRounds ss sw cs j hj).challenges y)) ∧
        (∃ (jj kk : ℕ) (hjk : jj + kk = M + 1 - j),
          WfEvals kk st.1 ∧ WfEvals jj st.2.1 ∧
          ∀ y : Fin (M + 1 - j) → Fin 2,
            reidx hjk (tensorTable (tableFn (m := kk) st.1) (tableFn (m := jj) st.2.1))
                (finFunctionFinEquiv y)
              = (InnerOuter.cMultilinearExtension (M + 1)
                  (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16
                    ss.zc.rlin ss.zc.α ss.zc.τα)).eval
                  (InnerOuter.hypercubePoint (M + 1) j
                    (honestRounds ss sw cs j hj).challenges y)) ∧
        st.2.2.2.1.val.length = j ∧
        ∀ (k : ℕ) (hk : k < j),
          RepRoundMsg
            (st.2.2.2.1.val.getD k { g_zero := alloc.vec.Vec.new cpoly.field.Ext4,
                                      g_alpha := alloc.vec.Vec.new cpoly.field.Ext4 })
            (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF k (by omega)
              (honestRounds ss sw cs k (by omega)) sw))
  · rintro ⟨lw, hg, cur, out, wt, i⟩
      ⟨j, hj, hij, hrep, hWw, hwv, ⟨jj, kk, hjkk, hWlw, hWhg, hav⟩, houtlen, houtrep⟩
    dsimp only at hij
    subst hij
    dsimp only at hrep hWw hwv hWlw hWhg hav houtlen houtrep
    simp only [sumcheck.honest_round_messages_loop.body]
    by_cases hlt : i < alloc.vec.Vec.len stmt.zc.tau0
    · rw [if_pos hlt]
      have hilt : i.val < M + 1 := by rw [← hm0len]; scalar_tac
      have hzceq : (honestRounds ss sw cs i.val hj).zc = ss.zc := honestRounds_zc ss sw cs i.val hj
      have hav' : ∀ y : Fin (M + 1 - i.val) → Fin 2,
          reidx hjkk (tensorTable (tableFn (m := kk) lw) (tableFn (m := jj) hg))
              (finFunctionFinEquiv y) =
            (InnerOuter.cMultilinearExtension (M + 1)
              (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16
                (honestRounds ss sw cs i.val hj).zc.rlin (honestRounds ss sw cs i.val hj).zc.α
                (honestRounds ss sw cs i.val hj).zc.τα)).eval
              (InnerOuter.hypercubePoint (M + 1) i.val
                (honestRounds ss sw cs i.val hj).challenges y) := by
        rw [hzceq]; exact hav
      step with honest_compute_g_split_spec (n := n) (μ := μ) (M := M) (m₁ := m₁)
        (dRows := dRows) (j := jj) (k := kk)
        cur wt lw hg i (honestRounds ss sw cs i.val hj) sw hrep hilt hjkk hWw hWlw hWhg hwv hav'
          as ⟨g, hgrep⟩
      have hich' : i.val < challenges.val.length := by omega
      step as ⟨a, hav2⟩
      have hRa : Reduced a := hav2 ▸ hcred _ (List.getElem_mem hich')
      have haval : toExt a = cs ⟨i.val, hilt⟩ := by
        rw [hcs]
        simp only [toPoint]
        rw [hav2, List.getD_eq_getElem _ _ hich']
      step with round_out_spec (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := i.val)
        (dRows := dRows) cur g a (honestRounds ss sw cs i.val hj)
        (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF i.val hilt
          (honestRounds ss sw cs i.val hj) sw) hrep hgrep hRa (by omega) as ⟨cur2, hrep2⟩
      step with eval_mle_layer_table_spec (M := M) (i := i.val) hilt wt
        (InnerOuter.wTable Φ (M + 1) phiF 16 sw)
        (honestRounds ss sw cs i.val hj).challenges a hWw hRa
        (by
          intro y
          rw [hwv y, InnerOuter.wTableMleEval_eq, InnerOuter.cMultilinearExtension_eval])
          as ⟨wt2, hWw2, hwv2⟩
      step with alpha_split_fold_spec (j := jj) (k := kk) lw hg a hWlw hWhg hRa
        (by omega) as ⟨lw2, hg2, hfA, hfB⟩
      have hnewtens : ∃ (jj1 kk1 : ℕ) (hjk1 : jj1 + kk1 = M + 1 - (i.val + 1)),
          WfEvals kk1 lw2 ∧ WfEvals jj1 hg2 ∧
          ∀ y : Fin (M + 1 - (i.val + 1)) → Fin 2,
            reidx hjk1 (tensorTable (tableFn (m := kk1) lw2) (tableFn (m := jj1) hg2))
                (finFunctionFinEquiv y)
              = (InnerOuter.cMultilinearExtension (M + 1)
                  (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16
                    ss.zc.rlin ss.zc.α ss.zc.τα)).eval
                  (InnerOuter.hypercubePoint (M + 1) (i.val + 1)
                    (Fin.snoc (honestRounds ss sw cs i.val hj).challenges (toExt a)) y) := by
        rcases Nat.eq_zero_or_pos kk with hkk0 | hkkpos
        · obtain ⟨jj', hjj'⟩ : ∃ t, jj = t + 1 := ⟨jj - 1, by omega⟩
          obtain ⟨hlw2eq, hWhg2, hhg2v, htens⟩ := hfB jj' hkk0 hjj'
          have hjk1 : jj' + 0 = M + 1 - (i.val + 1) := by omega
          refine ⟨jj', 0, hjk1, by rw [hlw2eq]; rwa [hkk0] at hWlw, hWhg2, ?_⟩
          refine tensor_invariant_step
            (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)
            i.val hilt jj kk jj' 0 hjkk hjk1 lw hg lw2 hg2 (toExt a)
            (honestRounds ss sw cs i.val hj).challenges hav ?_
          intro t ht
          have h := htens ⟨t, ht⟩
          rw [hkk0]
          simpa only [tensorTable, tableFn_apply, tensorRead, fold, lo, ZeroCheck.hi] using h
        · obtain ⟨kk', hkk'⟩ : ∃ t, kk = t + 1 := ⟨kk - 1, by omega⟩
          obtain ⟨hWlw2, hhg2eq, hlw2v, htens⟩ := hfA kk' hkk'
          have hjk1 : jj + kk' = M + 1 - (i.val + 1) := by omega
          refine ⟨jj, kk', hjk1, hWlw2, by rw [hhg2eq]; exact hWhg, ?_⟩
          refine tensor_invariant_step
            (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)
            i.val hilt jj kk jj kk' hjkk hjk1 lw hg lw2 hg2 (toExt a)
            (honestRounds ss sw cs i.val hj).challenges hav ?_
          intro t ht
          have h := htens ⟨t, ht⟩
          rw [hkk']
          simpa only [tensorTable, tableFn_apply, tensorRead, fold, lo, ZeroCheck.hi] using h
      have hpush : out.val.length < Usize.max := by omega
      step as ⟨out2, hout2⟩
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = i.val + 1 := by scalar_tac
      have hnext : honestRounds ss sw cs (i.val + 1) (by omega)
          = InnerOuter.roundOut Φ (M + 1) m₁ 16 (honestRounds ss sw cs i.val hj)
              (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF i.val hilt
                (honestRounds ss sw cs i.val hj) sw) (cs ⟨i.val, hilt⟩) := rfl
      obtain ⟨jj1, kk1, hjk1, hWlw2', hWhg2', hav5⟩ := hnewtens
      rw [haval] at hrep2 hwv2 hav5
      refine ⟨⟨i.val + 1, by omega, hi1v, ?_, hWw2, ?_, ⟨jj1, kk1, hjk1, hWlw2', hWhg2', ?_⟩,
        ?_, ?_⟩, by omega⟩
      · rw [hnext]; exact hrep2
      · intro y
        rw [hwv2 y, hnext, InnerOuter.roundOut,
          InnerOuter.wTableMleEval_eq, InnerOuter.cMultilinearExtension_eval]
      · intro y
        rw [hav5 y, hnext, InnerOuter.roundOut]
      · rw [hout2, List.length_append, houtlen]; simp
      · intro k hk
        rcases Nat.lt_or_ge k i.val with hklt | hkge
        · rw [hout2, getD_append_lt _ _ _ (by omega)]
          exact houtrep k hklt
        · have hkeq : k = i.val := by omega
          subst hkeq
          have hgetd : out2.val.getD i.val
              { g_zero := alloc.vec.Vec.new cpoly.field.Ext4,
                g_alpha := alloc.vec.Vec.new cpoly.field.Ext4 } = g := by
            rw [hout2, ← houtlen, getD_append_eq]
          rw [hgetd]
          exact hgrep
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hieq : i.val = M + 1 := by rw [← hm0len] at hj ⊢; scalar_tac
      exact ⟨by rw [houtlen, hieq], fun k hk => houtrep k (by omega)⟩
  · exact ⟨1, by omega, by scalar_tac, by rw [hnext1]; exact hrep1, hWw1,
      (fun y => by
        rw [hwv1 y, hnext1, InnerOuter.roundOut,
          InnerOuter.wTableMleEval_eq, InnerOuter.cMultilinearExtension_eval]),
      ⟨M + 1 - min (M + 1) 10, k0', by omega, hWlow1, by rw [hhigh1eq]; exact hWhigh0,
        (fun y => by rw [hav1 y, hnext1, InnerOuter.roundOut])⟩,
      houtlen1, houtrep1⟩

/- **Campaign note for Aristotle (candidate L, brief 5's S4, prover half; wall W1).**

The statement above is **unchanged** (byte-identical to `git show
HEAD:hachi/lean/Sumcheck.lean`); the champion's extracted model moved underneath
it. The proof kept verbatim below is the one that went through against the old
model. What changed, and where each step of the old proof has to be re-routed:

1. **No `a_tab`.** `alpha_public_table` is gone from this item (it is still in
   the model and `round_loop` still calls it, so `alpha_public_table_spec` and
   `initial_a_table` stand untouched). In its place the body builds
   `low ← alpha_split_low stmt.zc.alpha m0` and
   `high ← alpha_split_high stmt.zc.rlin stmt.zc.alpha stmt.zc.tau1 m0`, so the
   opening `step with alpha_public_table_spec …` becomes two steps,
   `alpha_split_low_spec` and `alpha_split_high_spec`, at
   `k₀ = min (M + 1) 10` and `j₀ = (M + 1) − min (M + 1) 10`.

2. **The loop state is `(low, high, current, out, w_tab, i)`** -- six components,
   not five (`sumcheck.honest_round_messages_loop`, `Generated.lean`): the pair
   replaces the single `a_tab` in the *first* position and the rest keeps its
   order. So in the `loop.spec_decr_nat` invariant below, `st.1` (the old
   `a_tab`) becomes `st.1` = `low` and `st.2.1` = `high`, and every later
   projection shifts by one: `current` is `st.2.2.1`, `out` is `st.2.2.2.1`,
   `w_tab` is `st.2.2.2.2.1`, `i` is `st.2.2.2.2.2`. The measure becomes
   `M + 1 - st.2.2.2.2.2.val`.

3. **The recommended invariant.** Replace the two conjuncts
   `WfEvals (M + 1 - j) st.1` and the `hav` clause on `tableFn st.1` by the
   per-round *pair* shape, with the two arities existentially quantified and tied
   to the round by the usize fact `low.len() * high.len() = 2 ^ (M + 1 − i)`:

       ∃ (jᵢ kᵢ : ℕ) (hjk : jᵢ + kᵢ = M + 1 - j),
         WfEvals kᵢ st.1 ∧ WfEvals jᵢ st.2.1 ∧
         (∀ y : Fin (M + 1 - j) → Fin 2,
            reidx hjk (tensorTable (tableFn (m := kᵢ) st.1)
                                   (tableFn (m := jᵢ) st.2.1))
                (finFunctionFinEquiv y)
              = (InnerOuter.cMultilinearExtension (M + 1)
                  (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16
                     ss.zc.rlin ss.zc.α ss.zc.τα)).eval
                  (InnerOuter.hypercubePoint (M + 1) j
                     (honestRounds ss sw cs j hj).challenges y))

   `WfEvals kᵢ st.1` is `low.len() = 2 ^ kᵢ`, so `hjk` *is* the product fact; and
   `reidx` is the identity on values (`reidx_apply`), so it never obstructs a
   rewrite. All the other conjuncts of the invariant below (`j ≤ M + 1`, the
   counter, `RepRoundStmt`, the `w_tab` clauses, `out`'s length and the message
   representations) are carried **verbatim**.

   Concretely `kᵢ = min (M + 1) 10 − i` and `jᵢ = (M + 1) − min (M + 1) 10` while
   `i ≤ min (M + 1) 10`, and `kᵢ = 0`, `jᵢ = M + 1 − i` afterwards; the
   existential is what lets the two regimes share one invariant, and it is why
   `alpha_split_fold_spec` is stated with a branch per regime rather than with a
   single `k`.

4. **Where each old step goes.**
   * the initial `hav0` (`initial_a_table … hatv`) becomes
     `alphaPublicEvals_eq_tensorTable` (subsection 4 above) at
     `x := y`, `idx := finFunctionFinEquiv y`, fed by `alpha_split_low_spec`'s and
     `alpha_split_high_spec`'s two `tableFn = alphaLowTable/alphaHighTable`
     conclusions -- i.e. the round-0 instance of the invariant, with
     `hjk₀ : j₀ + k₀ = M + 1` discharged by `Nat.sub_add_cancel (alphaSplit_le _)`;
   * `step with honest_compute_g_base_spec … hWa_tab hav0` becomes
     `step with honest_compute_g_base_split_spec … hlow hhigh hav0`;
   * `step with eval_mle_layer_table_spec … a_tab … hav0` (the α fold of round 0)
     becomes `step with alpha_split_fold_spec … hlow hhigh hRa0`, whose tensor
     conjunct is `fold_tensorTable_low` (when `k₀ = k' + 1`) or
     `fold_tensorTable_scalar` (when `k₀ = 0`, i.e. `M + 1 < 1 + 10` and the whole
     cube is "low" -- unreachable at the pin but part of the statement), and whose
     composition with `hav0` is one instance of `fold_tableFn_eq_mle` exactly as
     `eval_mle_layer_table_spec` packaged it; `foldIter_tensorTable` (subsection 6)
     is the same fact for the whole run, stated in one piece;
   * inside the loop, `step with honest_compute_g_spec … at1 …` becomes
     `step with honest_compute_g_split_spec … low high …`, and the α fold step
     becomes `alpha_split_fold_spec` again;
   * the zero side -- `c_w_table_fp_spec`, `round_out_spec`,
     `eval_mle_layer_base_table_spec`, `eval_mle_layer_table_spec` on `w_tab`, the
     `out.push` bookkeeping and the two `honestRounds` `rfl` steps -- is
     **untouched**.

5. **What is *not* re-proved.** `honestRounds`, `RepRoundStmt`, `RepRoundMsg`,
   `honestComputeG` and `roundOut` are the specification side and did not move;
   neither did the conclusion. A statement change here would be a weakening and
   needs the approval gate.

The verbatim previous proof follows.

  obtain ⟨hzc, hWc, hRt0, hRta, hcv, ht0, hta⟩ := id hs
  obtain ⟨hr, hWt, hWa, hW0, hW1, htv, halv, h0v, h1v⟩ := hzc
  obtain ⟨h0len, h0red⟩ := hW0
  obtain ⟨hclen, hcred⟩ := hc
  set cs := toPoint (m := M + 1) challenges with hcs
  have hm0len : (alloc.vec.Vec.len stmt.zc.tau0).val = M + 1 := by simpa using h0len
  have hMmax : M + 1 ≤ Usize.max := by
    have := Nat.lt_two_pow_self (n := M + 1)
    omega
  have hzero : (0 : ℕ) < M + 1 := Nat.succ_pos M
  simp only [sumcheck.honest_round_messages, sumcheck.RoundStatement.impl.zc,
    sumcheck.NestedZeroCheckStmt.impl.tau0, sumcheck.NestedZeroCheckStmt.impl.rlin,
    sumcheck.NestedZeroCheckStmt.impl.alpha, sumcheck.NestedZeroCheckStmt.impl.tau1,
    bind_tc_ok]
  step with alpha_public_table_spec (n := n) (μ := μ) (m₁ := m₁) stmt.zc.rlin ss.zc.rlin
    stmt.zc.alpha stmt.zc.tau1 (alloc.vec.Vec.len stmt.zc.tau0) hr hWa hW1
    (by rw [hm0len]; exact hm0) hmax as ⟨a_tab, hWa_tab, hatv⟩
  rw [hm0len] at hWa_tab hatv
  rw [halv, h1v] at hatv
  have hav0 : ∀ y : Fin (M + 1) → Fin 2,
      tableFn (m := M + 1) a_tab (finFunctionFinEquiv y) =
        (InnerOuter.cMultilinearExtension (M + 1)
          (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)).eval
          (InnerOuter.hypercubePoint (M + 1) 0 ss.challenges y) :=
    fun y => initial_a_table (m₁ := m₁) (n := n) (μ := μ) (M := M) a_tab ss.zc.rlin ss.zc.α
      ss.zc.τα _ hatv y
  rw [if_pos (show (0#usize : Std.Usize) < alloc.vec.Vec.len stmt.zc.tau0 from by scalar_tac)]
  step with c_w_table_fp_spec (μ := μ) (n := n) w sw (alloc.vec.Vec.len stmt.zc.tau0) hw
    (by rw [hm0len]; exact hm0) hmax as ⟨w_fp, hfplen, hfpred, hfpval⟩
  rw [hm0len] at hfplen hfpval
  have hWfp : WfEvalsFp (M + 1) w_fp := ⟨hfplen, hfpred⟩
  have hwv0 := initial_w_table_fp (μ := μ) (n := n) (M := M) w_fp sw ss.challenges hfpval
  step with honest_compute_g_base_spec (n := n) (μ := μ) (M := M) (m₁ := m₁) (dRows := dRows)
    stmt w_fp a_tab ss sw hs hWfp hWa_tab hwv0 hav0 as ⟨g0, hg0rep⟩
  have hich : (0 : ℕ) < challenges.val.length := by omega
  step as ⟨a0, ha0v⟩
  have hRa0 : Reduced a0 := ha0v ▸ hcred _ (List.getElem_mem hich)
  have ha0val : toExt a0 = cs ⟨0, hzero⟩ := by
    rw [hcs]
    simp only [toPoint]
    rw [ha0v, List.getD_eq_getElem _ _ hich]
  step with round_out_spec (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := 0)
    (dRows := dRows) stmt g0 a0 ss
    (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF 0 hzero ss sw) hs hg0rep hRa0
    (by omega) as ⟨cur1, hrep1⟩
  step with eval_mle_layer_base_table_spec (M := M) (i := 0) hzero w_fp
    (InnerOuter.wTable Φ (M + 1) phiF 16 sw) ss.challenges a0 hWfp hRa0
    (by
      intro y
      rw [hwv0 y, InnerOuter.wTableMleEval_eq, InnerOuter.cMultilinearExtension_eval])
      as ⟨wt1, hWw1, hwv1⟩
  step with eval_mle_layer_table_spec (M := M) (i := 0) hzero a_tab
    (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)
    ss.challenges a0 hWa_tab hRa0 hav0 as ⟨at2, hWa3, hav3⟩
  have hpush0 : (alloc.vec.Vec.new sumcheck.RoundMsg).val.length < Usize.max := by simp; omega
  step as ⟨out1, hout1⟩
  have hnext1 : honestRounds ss sw cs 1 (by omega)
      = InnerOuter.roundOut Φ (M + 1) m₁ 16 ss
          (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF 0 hzero ss sw)
          (cs ⟨0, hzero⟩) := rfl
  rw [ha0val] at hrep1 hwv1 hav3
  have houtlen1 : out1.val.length = 1 := by rw [hout1, List.length_append]; simp
  have houtrep1 : ∀ (k : ℕ) (hk : k < 1),
      RepRoundMsg
        (out1.val.getD k { g_zero := alloc.vec.Vec.new cpoly.field.Ext4,
                           g_alpha := alloc.vec.Vec.new cpoly.field.Ext4 })
        (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF k (by omega)
          (honestRounds ss sw cs k (by omega)) sw) := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    have hg : out1.val.getD 0 { g_zero := alloc.vec.Vec.new cpoly.field.Ext4,
                                g_alpha := alloc.vec.Vec.new cpoly.field.Ext4 } = g0 := by
      rw [hout1]; simp
    rw [hg]
    exact hg0rep
  rw [sumcheck.honest_round_messages_loop]
  apply loop.spec_decr_nat (fun st => M + 1 - st.2.2.2.2.val)
    (fun st => ∃ (j : ℕ) (hj : j ≤ M + 1), st.2.2.2.2.val = j ∧
      RepRoundStmt (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := j)
          (dRows := dRows) st.2.1 (honestRounds ss sw cs j hj) ∧
        WfEvals (M + 1 - j) st.2.2.2.1 ∧ WfEvals (M + 1 - j) st.1 ∧
        (∀ y : Fin (M + 1 - j) → Fin 2,
          tableFn (m := M + 1 - j) st.2.2.2.1 (finFunctionFinEquiv y) =
            InnerOuter.wTableMleEval Φ (M + 1) phiF 16 sw
              (InnerOuter.hypercubePoint (M + 1) j (honestRounds ss sw cs j hj).challenges y)) ∧
        (∀ y : Fin (M + 1 - j) → Fin 2,
          tableFn (m := M + 1 - j) st.1 (finFunctionFinEquiv y) =
            (InnerOuter.cMultilinearExtension (M + 1)
              (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)).eval
              (InnerOuter.hypercubePoint (M + 1) j (honestRounds ss sw cs j hj).challenges y)) ∧
        st.2.2.1.val.length = j ∧
        ∀ (k : ℕ) (hk : k < j),
          RepRoundMsg
            (st.2.2.1.val.getD k { g_zero := alloc.vec.Vec.new cpoly.field.Ext4,
                                      g_alpha := alloc.vec.Vec.new cpoly.field.Ext4 })
            (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF k (by omega)
              (honestRounds ss sw cs k (by omega)) sw))
  · rintro ⟨at1, cur, out, wt, i⟩ ⟨j, hj, hij, hrep, hWw, hWa2, hwv, hav, houtlen, houtrep⟩
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
      have hich' : i.val < challenges.val.length := by omega
      step as ⟨a, hav2⟩
      have hRa : Reduced a := hav2 ▸ hcred _ (List.getElem_mem hich')
      have haval : toExt a = cs ⟨i.val, hilt⟩ := by
        rw [hcs]
        simp only [toPoint]
        rw [hav2, List.getD_eq_getElem _ _ hich']
      step with round_out_spec (n := n) (μ := μ) (m₀ := M + 1) (m₁ := m₁) (i := i.val)
        (dRows := dRows) cur g a (honestRounds ss sw cs i.val hj)
        (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF i.val hilt
          (honestRounds ss sw cs i.val hj) sw) hrep hgrep hRa (by omega) as ⟨cur2, hrep2⟩
      step with eval_mle_layer_table_spec (M := M) (i := i.val) hilt wt
        (InnerOuter.wTable Φ (M + 1) phiF 16 sw)
        (honestRounds ss sw cs i.val hj).challenges a hWw hRa
        (by
          intro y
          rw [hwv y, InnerOuter.wTableMleEval_eq, InnerOuter.cMultilinearExtension_eval])
          as ⟨wt2, hWw2, hwv2⟩
      step with eval_mle_layer_table_spec (M := M) (i := i.val) hilt at1
        (InnerOuter.alphaPublicEvals Φ (M + 1) m₁ phiF 16 ss.zc.rlin ss.zc.α ss.zc.τα)
        (honestRounds ss sw cs i.val hj).challenges a hWa2 hRa hav as ⟨at3, hWa4, hav4⟩
      have hpush : out.val.length < Usize.max := by omega
      step as ⟨out2, hout2⟩
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = i.val + 1 := by scalar_tac
      have hnext : honestRounds ss sw cs (i.val + 1) (by omega)
          = InnerOuter.roundOut Φ (M + 1) m₁ 16 (honestRounds ss sw cs i.val hj)
              (InnerOuter.honestComputeG Φ m₁ 16 (by norm_num) phiF i.val hilt
                (honestRounds ss sw cs i.val hj) sw) (cs ⟨i.val, hilt⟩) := rfl
      rw [haval] at hrep2 hwv2 hav4
      refine ⟨⟨i.val + 1, by omega, hi1v, ?_, hWw2, hWa4, ?_, ?_, ?_, ?_⟩, by omega⟩
      · rw [hnext]; exact hrep2
      · intro y
        rw [hwv2 y, hnext, InnerOuter.roundOut,
          InnerOuter.wTableMleEval_eq, InnerOuter.cMultilinearExtension_eval]
      · intro y
        rw [hav4 y, hnext, InnerOuter.roundOut]
      · rw [hout2, List.length_append, houtlen]; simp
      · intro k hk
        rcases Nat.lt_or_ge k i.val with hklt | hkge
        · rw [hout2, getD_append_lt _ _ _ (by omega)]
          exact houtrep k hklt
        · have hkeq : k = i.val := by omega
          subst hkeq
          have hgetd : out2.val.getD i.val
              { g_zero := alloc.vec.Vec.new cpoly.field.Ext4,
                g_alpha := alloc.vec.Vec.new cpoly.field.Ext4 } = g := by
            rw [hout2, ← houtlen, getD_append_eq]
          rw [hgetd]
          exact hgrep
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hieq : i.val = M + 1 := by rw [← hm0len] at hj ⊢; scalar_tac
      exact ⟨by rw [houtlen, hieq], fun k hk => houtrep k (by omega)⟩
  · exact ⟨1, by omega, by scalar_tac, by rw [hnext1]; exact hrep1, hWw1, hWa3,
      (fun y => by
        rw [hwv1 y, hnext1, InnerOuter.roundOut,
          InnerOuter.wTableMleEval_eq, InnerOuter.cMultilinearExtension_eval]),
      (fun y => by rw [hav3 y, hnext1, InnerOuter.roundOut]),
      houtlen1, houtrep1⟩
-/

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
