/-
The honest lift prover (`RingSwitch/ComputableWitness.lean`).

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
import LiftGadget
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

@[simp] theorem toCPolyK_coeff (v : alloc.vec.Vec cpoly.field.Fp) (k : ℕ) :
    (toCPolyK v).coeff k = if h : k < v.val.length then toK v.val[k] else 0 := by
  rw [toCPolyK, CPolynomial.coeff_ofArray]
  simp only [Array.getD]
  by_cases h : k < v.val.length
  · simp [dif_pos h]
  · simp [dif_neg h]

theorem toCPolyK_coeff_of_lt (v : alloc.vec.Vec cpoly.field.Fp) {k : ℕ}
    (h : k < v.val.length) : (toCPolyK v).coeff k = toK v.val[k] := by
  rw [toCPolyK_coeff, dif_pos h]

theorem toCPolyK_coeff_of_ge (v : alloc.vec.Vec cpoly.field.Fp) {k : ℕ}
    (h : v.val.length ≤ k) : (toCPolyK v).coeff k = 0 := by
  rw [toCPolyK_coeff, dif_neg (by omega)]

/-! ## Coefficient bookkeeping

`toCPolyK` and `coeffK` read the same word vector, one into a `CPolynomial` and
one into `ZMod q` directly, and `toCPolyK_coeff_eq_coeffK` says they agree at
every index -- past the end both are `0`. Every loop below is proved at the
`coeffK` level and lifted through that equation. -/

/-- The coefficients of the represented polynomial *are* `coeffK`. -/
theorem toCPolyK_coeff_eq_coeffK (v : alloc.vec.Vec cpoly.field.Fp) (k : ℕ) :
    (toCPolyK v).coeff k = coeffK v k := by
  rw [toCPolyK_coeff]
  by_cases h : k < v.val.length
  · rw [dif_pos h, coeffK_of_lt h]
  · rw [dif_neg h, coeffK_of_ge (Nat.le_of_not_lt h)]

/-- Extensionality for `toCPolyK`: a word vector represents a given polynomial
exactly when its coefficient function is that polynomial's. -/
theorem toCPolyK_eq_of_coeffK {v : alloc.vec.Vec cpoly.field.Fp}
    {p : CPolynomial (ZMod q)} (h : ∀ k, coeffK v k = p.coeff k) : toCPolyK v = p := by
  rw [CPolynomial.eq_iff_coeff]
  intro k
  rw [toCPolyK_coeff_eq_coeffK, h]

/-- A well-formed `Rq` word vector represents, as a `CPolynomial`, the canonical
representative of the `Rq Φ` element it represents. -/
theorem toRq_val_eq_toCPolyK {v : ring.Rq} (hv : Wf v) : (toRq v).1 = toCPolyK v := by
  rw [CPolynomial.eq_iff_coeff]
  intro k
  rw [toRq_coeff_eq_coeffK hv, toCPolyK_coeff_eq_coeffK]

/-- The same, for a quotient row. -/
theorem toQuotientRow_eq_toCPolyK {v : ringswitch.QuotientRow} (hv : Wf v) :
    toQuotientRow v = toCPolyK v := by
  rw [CPolynomial.eq_iff_coeff]
  intro k
  rw [toQuotientRow_coeff, toCPolyK_coeff_eq_coeffK]
  by_cases hk : k < N
  · rw [if_pos hk]
  · rw [if_neg hk, coeffK_of_ge (by rw [hv.1]; omega)]

/-! ### `CPolynomial` coefficients of sums and differences

CompPoly states its arithmetic through `toPoly`, so these three go through
`coeff_toPoly` and the Mathlib lemma of the same name. -/

theorem cpoly_coeff_add (p r : CPolynomial (ZMod q)) (k : ℕ) :
    (p + r).coeff k = p.coeff k + r.coeff k := by
  rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly,
    CPolynomial.toPoly_add, Polynomial.coeff_add]

theorem cpoly_coeff_sub (p r : CPolynomial (ZMod q)) (k : ℕ) :
    (p - r).coeff k = p.coeff k - r.coeff k := by
  rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly,
    CPolynomial.toPoly_sub, Polynomial.coeff_sub]

theorem cpoly_coeff_sum {ι : Type} (s : Finset ι) (f : ι → CPolynomial (ZMod q)) (k : ℕ) :
    (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, CPolynomial.coeff_zero]
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, cpoly_coeff_add, ih]

/-! ### Writing one word

The three loops that use `IndexMut` all update a single slot, so they all need
the same three facts about `v.val.set s x`. -/

theorem coeffK_set_eq {v w : alloc.vec.Vec cpoly.field.Fp} {s : ℕ} {x : cpoly.field.Fp}
    (hw : w.val = v.val.set s x) (hs : s < v.val.length) : coeffK w s = toK x := by
  unfold coeffK
  rw [hw, List.getD_eq_getElem _ _ (by rw [List.length_set]; exact hs),
    List.getElem_set_self]

theorem coeffK_set_ne {v w : alloc.vec.Vec cpoly.field.Fp} {s : ℕ} {x : cpoly.field.Fp}
    (hw : w.val = v.val.set s x) {k : ℕ} (hk : k ≠ s) : coeffK w k = coeffK v k := by
  unfold coeffK
  rw [hw, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_set_ne (Ne.symm hk)]

theorem Red_set {v w : alloc.vec.Vec cpoly.field.Fp} {s : ℕ} {x : cpoly.field.Fp}
    (hw : w.val = v.val.set s x) (hv : ∀ u ∈ v.val, Red u) (hx : Red x) :
    ∀ u ∈ w.val, Red u := by
  intro u hu
  rw [hw] at hu
  rcases List.mem_or_eq_of_mem_set hu with h | h
  · exact hv u h
  · rw [h]; exact hx

/-! ## The helpers -/

/-! ### `long_mul` -/

/-! ### Candidate R: the accumulator as a natural

Candidate R delayed the reduction here as candidate Q did in `Rq::mul`, and the
`ℕ`-level layer that made Q's proof work is reused verbatim: `wordN`,
`wordN_lt` and `accBound` are `HachiEquiv.Ring`'s, which this file opens. What is
*not* shared is the harder half of Q -- there is no negacyclic fold in a `Zq[X]`
product, so there is one accumulator and no sign split, and the sum runs over the
clipped antidiagonal `Ico lo hi` rather than all of `range N`. -/

/-- The accumulator after the inner loop has walked `Ico lo i` of slot `k`'s
antidiagonal. -/
def longSum (a b : ring.Rq) (k lo i : ℕ) : ℕ :=
  ∑ t ∈ Finset.Ico lo i, wordN a t * wordN b (k - t)

theorem longSum_self (a b : ring.Rq) (k lo : ℕ) : longSum a b k lo lo = 0 := by
  simp [longSum]

theorem longSum_succ (a b : ring.Rq) (k lo i : ℕ) (h : lo ≤ i) :
    longSum a b k lo (i + 1) = longSum a b k lo i + wordN a i * wordN b (k - i) := by
  unfold longSum
  rw [Finset.sum_Ico_succ_top h]

/-- Each term is below `q * q`, so the partial sum is below its own length times
that. The caller supplies the length bound -- for this loop `i - lo ≤ N`, the
antidiagonal never being longer than an operand. -/
theorem longSum_le {a b : ring.Rq} (ha : Wf a) (hb : Wf b) (k lo i : ℕ) :
    longSum a b k lo i ≤ (i - lo) * (q * q) := by
  unfold longSum
  calc ∑ t ∈ Finset.Ico lo i, wordN a t * wordN b (k - t)
      ≤ ∑ _t ∈ Finset.Ico lo i, q * q :=
        Finset.sum_le_sum (fun t _ => Nat.mul_le_mul
          (Nat.le_of_lt (wordN_lt ha t)) (Nat.le_of_lt (wordN_lt hb _)))
    _ = (i - lo) * (q * q) := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]

/-- The completed antidiagonal, cast once, *is* the specification's coefficient.
Outside `Ico lo hi` the summand vanishes for the two reasons the clipping
encodes: below `lo` the right operand's index has run past its `N` words, and
above `hi` the left one has (or `t` has passed `k`). -/
theorem longSum_cast {a b : ring.Rq} (_ha : Wf a) (hb : Wf b) {k lo hi : ℕ}
    (hlo : lo = if k + 1 > N then k + 1 - N else 0)
    (hhi : hi = if k + 1 < N then k + 1 else N) :
    ((longSum a b k lo hi : ℕ) : ZMod q)
      = ∑ t ∈ Finset.range N, if t ≤ k then coeffK a t * coeffK b (k - t) else 0 := by
  have hhiN : hi ≤ N := by rw [hhi]; split <;> omega
  have hhik : hi ≤ k + 1 := by rw [hhi]; split <;> omega
  -- Trim the specification's sum to the clipped antidiagonal: outside it the
  -- guarded summand is zero, below `lo` because the right operand's index has
  -- run past its `N` words and above `hi` because `t` has passed `k`.
  rw [← Finset.sum_subset (s₁ := Finset.Ico lo hi) (s₂ := Finset.range N)
    (by
      intro x hx
      simp only [Finset.mem_Ico] at hx
      simp only [Finset.mem_range]
      omega)
    (by
      intro x hx hx2
      simp only [Finset.mem_range] at hx
      simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hx2
      rcases hx2 with h | h
      · have hkx : N ≤ k - x := by rw [hlo] at h; split at h <;> omega
        rw [if_pos (by rw [hlo] at h; split at h <;> omega),
          coeffK_of_ge (v := b) (k := k - x) (by rw [hb.1]; exact hkx), mul_zero]
      · rw [if_neg (by rw [hhi] at h; split at h <;> omega)])]
  unfold longSum
  push_cast
  refine Finset.sum_congr rfl (fun t ht => ?_)
  simp only [Finset.mem_Ico] at ht
  rw [if_pos (by omega : t ≤ k), coeffK_eq_cast_wordN, coeffK_eq_cast_wordN]

/-- `Rq::coeff` at the word level. `coeff_spec` gives the `ZMod q` value, which
is the wrong currency for a `u128` accumulator: what the loop needs is the word
itself. Total, like the Rust -- out of range it reads `Fp::ZERO`, whose word is
the `0` that `wordN`'s default supplies. -/
private theorem coeff_word (v : ring.Rq) (hv : Wf v) (k : Std.Usize) :
    ring.Rq.coeff v k ⦃ c => Red c ∧ c.val = wordN v k.val ⦄ := by
  rw [ring.Rq.coeff]
  by_cases hk : k < alloc.vec.Vec.len v
  · rw [if_pos hk]
    have hkl : k.val < v.val.length := by scalar_tac
    step as ⟨f, hf⟩
    refine ⟨by rw [hf]; exact hv.2 _ (List.getElem_mem hkl), ?_⟩
    rw [hf]
    unfold wordN
    rw [List.getD_eq_getElem _ _ hkl]
  · rw [if_neg hk, WP.spec_ok]
    have hkl : v.val.length ≤ k.val := by scalar_tac
    refine ⟨Red_zero, ?_⟩
    unfold wordN
    rw [List.getD_eq_default _ _ hkl, cpoly_Fp_ZERO_val]

/-! ### The two clipped bounds

The Rust computes slot `k`'s antidiagonal bounds with `if`s whose branches are
*monadic* -- `k + 1 - n` is a checked subtraction -- so `step` cannot take them
directly. One spec each, and the four-way case split stays out of the loop
proof. -/

private theorem clip_lo_spec (x n : Std.Usize) :
    (if x > n then x - n else ok (0#usize))
      ⦃ z => z.val = if n.val < x.val then x.val - n.val else 0 ⦄ := by
  by_cases h : x > n
  · rw [if_pos h, if_pos (by scalar_tac)]
    step as ⟨d, hd⟩
    rw [hd]
  · rw [if_neg h, if_neg (by scalar_tac), WP.spec_ok]
    simp

private theorem clip_hi_spec (x n : Std.Usize) :
    (if x < n then ok x else ok n)
      ⦃ z => z.val = if x.val < n.val then x.val else n.val ⦄ := by
  by_cases h : x < n
  · rw [if_pos h, if_pos (by scalar_tac), WP.spec_ok]
  · rw [if_neg h, if_neg (by scalar_tac), WP.spec_ok]

/-- Everything the loop proof needs about the clipped bounds, once. `N` is a
literal, so each of the three regions (`k + 1` below, at, or above `N`) closes by
`omega` -- including the fact that makes `k - i` a legal checked subtraction and
the right operand's index in range. -/
private theorem clip_bounds {k lo hi : ℕ} (hk : k < 2 * N - 1)
    (hlo : lo = if k + 1 > N then k + 1 - N else 0)
    (hhi : hi = if k + 1 < N then k + 1 else N) :
    lo ≤ hi ∧ hi ≤ N ∧ hi ≤ k + 1 ∧ ∀ t, lo ≤ t → t < hi → k - t < N := by
  -- `omega` does not unfold `N`, so hand it the value.
  have hNv : N = 1024 := rfl
  subst hlo
  subst hhi
  by_cases h1 : k + 1 < N
  · rw [if_neg (by omega), if_pos h1]
    exact ⟨by omega, by omega, by omega, fun t h2 h3 => by omega⟩
  · rw [if_neg h1]
    by_cases h2 : k + 1 > N
    · rw [if_pos h2]
      exact ⟨by omega, by omega, by omega, fun t h3 h4 => by omega⟩
    · rw [if_neg h2]
      exact ⟨by omega, by omega, by omega, fun t h3 h4 => by omega⟩

/-! ### The two loops -/

theorem long_mul_loop0_loop0_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b)
    (k hi : Std.Usize) (acc : Std.U128) (i : Std.Usize) (lo : ℕ)
    (hlo : lo ≤ i.val) (hik : i.val ≤ hi.val) (hhiN : hi.val ≤ N)
    (hhik : hi.val ≤ k.val + 1)
    (hkb : ∀ t, lo ≤ t → t < hi.val → k.val - t < N)
    (hacc : acc.val = longSum a b k.val lo i.val) :
    ringswitch.long_mul_loop0_loop0 a b k hi acc i
      ⦃ z => z.val = longSum a b k.val lo hi.val ⦄ := by
  rw [ringswitch.long_mul_loop0_loop0]
  apply loop.spec_decr_nat (fun s => hi.val - s.2.val)
    (fun s => lo ≤ s.2.val ∧ s.2.val ≤ hi.val ∧
      s.1.val = longSum a b k.val lo s.2.val)
  · rintro ⟨sa, si⟩ ⟨hlo1, hle1, hval1⟩
    dsimp only at hlo1 hle1 hval1
    simp only [ringswitch.long_mul_loop0_loop0.body]
    by_cases hlt : si < hi
    · rw [if_pos hlt]
      have hsiN : si.val < N := by scalar_tac
      have hkiN : k.val - si.val < N := hkb si.val hlo1 (by scalar_tac)
      -- `k - i` is a *checked* subtraction; this is what makes it legal.
      have hsik : si.val ≤ k.val := by scalar_tac
      step with coeff_word a ha si as ⟨f, _hRf, hfv⟩
      step with to_u64_id f as ⟨w, hw⟩
      have haiv : w.val = wordN a si.val := by rw [hw, hfv]
      have hcast : lift (UScalar.cast .U128 w) ⦃ y => y.val = w.val ⦄ :=
        UScalar.cast_inBounds_spec .U128 w (by scalar_tac)
      step with hcast as ⟨ai, hai⟩
      step as ⟨d, hd⟩
      step with coeff_word b hb d as ⟨g, _hRg, hgv⟩
      step with to_u64_id g as ⟨w2, hw2⟩
      have hbjv : w2.val = wordN b (k.val - si.val) := by rw [hw2, hgv, hd]
      have hcast2 : lift (UScalar.cast .U128 w2) ⦃ y => y.val = w2.val ⦄ :=
        UScalar.cast_inBounds_spec .U128 w2 (by scalar_tac)
      step with hcast2 as ⟨bj, hbj⟩
      have hbnd : sa.val + ai.val * bj.val ≤ Std.U128.max := by
        have hNv : N = 1024 := rfl
        have hprod : ai.val * bj.val ≤ q * q := by
          rw [hai, hbj, haiv, hbjv]
          exact Nat.mul_le_mul (Nat.le_of_lt (wordN_lt ha _)) (Nat.le_of_lt (wordN_lt hb _))
        -- The accumulator holds at most `si - lo` terms and one more still fits:
        -- `si < hi ≤ N`, so `si - lo ≤ N - 1`.
        have hone : sa.val ≤ (N - 1) * (q * q) := by
          rw [hval1]
          exact le_trans (longSum_le ha hb k.val lo si.val)
            (Nat.mul_le_mul_right _ (by omega))
        have := accBound
        calc sa.val + ai.val * bj.val ≤ (N - 1) * (q * q) + q * q :=
              Nat.add_le_add hone hprod
          _ = N * (q * q) := by
              have : N - 1 + 1 = N := by omega
              calc (N - 1) * (q * q) + q * q = ((N - 1) + 1) * (q * q) := by ring
                _ = N * (q * q) := by rw [this]
          _ ≤ Std.U128.max := Nat.le_of_lt this
      step as ⟨t, ht⟩
      step as ⟨sa2, hsa2⟩
      step as ⟨si2, hsi2⟩
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      rw [hsa2, ht, hai, hbj, haiv, hbjv, hval1, hsi2,
        longSum_succ a b k.val lo si.val hlo1]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : si.val = hi.val := by scalar_tac
      rw [hval1, heq]
  · exact ⟨hlo, hik, hacc⟩

theorem long_mul_loop0_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b)
    (n width : Std.Usize) (qw : Std.U128) (out : alloc.vec.Vec cpoly.field.Fp)
    (k : Std.Usize) (hn : n.val = N) (hw : width.val = 2 * N - 1) (hq : qw.val = q)
    (hk : k.val ≤ width.val) (hlen : out.val.length = k.val)
    (hred : ∀ x ∈ out.val, Red x)
    (hcoeff : ∀ s, s < k.val → coeffK out s
      = ∑ t ∈ Finset.range N, if t ≤ s then coeffK a t * coeffK b (s - t) else 0) :
    ringswitch.long_mul_loop0 a b n width qw out k
      ⦃ z => z.val.length = 2 * N - 1 ∧ (∀ x ∈ z.val, Red x) ∧
        ∀ s, s < 2 * N - 1 → coeffK z s
          = ∑ t ∈ Finset.range N, if t ≤ s then coeffK a t * coeffK b (s - t) else 0 ⦄ := by
  rw [ringswitch.long_mul_loop0]
  apply loop.spec_decr_nat (fun s => width.val - s.2.val)
    (fun s => s.2.val ≤ width.val ∧ s.1.val.length = s.2.val ∧
      (∀ x ∈ s.1.val, Red x) ∧
      ∀ u, u < s.2.val → coeffK s.1 u
        = ∑ t ∈ Finset.range N, if t ≤ u then coeffK a t * coeffK b (u - t) else 0)
  · rintro ⟨so, sk⟩ ⟨hk1, hlen1, hred1, hc1⟩
    dsimp only at hk1 hlen1 hred1 hc1
    simp only [ringswitch.long_mul_loop0.body]
    by_cases hlt : sk < width
    · rw [if_pos hlt]
      have hqpos : 0 < q := by norm_num [q]
      step as ⟨kp1, hkp1⟩
      step with clip_lo_spec kp1 n as ⟨lo, hlo⟩
      step with clip_hi_spec kp1 n as ⟨hiv, hhiv⟩
      have hlov : lo.val = if sk.val + 1 > N then sk.val + 1 - N else 0 := by
        rw [hlo, hkp1, hn]
      have hhivv : hiv.val = if sk.val + 1 < N then sk.val + 1 else N := by
        rw [hhiv, hkp1, hn]
      obtain ⟨hlohi, hhiN, hhik, hkb⟩ := clip_bounds (by scalar_tac) hlov hhivv
      step with long_mul_loop0_loop0_spec a b ha hb sk hiv 0#u128 lo lo.val
        (by simp) hlohi hhiN hhik hkb (by simp [longSum_self]) as ⟨acc, hacc⟩
      step as ⟨m, hm⟩
      have hcast : lift (UScalar.cast .U64 m) ⦃ y => y.val = m.val ⦄ :=
        UScalar.cast_inBounds_spec .U64 m (by
          rw [hm, hq]
          have hb1 : acc.val % q < q := Nat.mod_lt _ hqpos
          have hb2 : q ≤ UScalar.max UScalarTy.U64 := by
            simp only [q, UScalar.max, UScalarTy.numBits]; norm_num
          omega)
      step with hcast as ⟨wd, hwd⟩
      step with fp_new_spec wd as ⟨f, hRf, hfv⟩
      step as ⟨so2, hso2⟩
      step as ⟨sk2, hsk2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
      · rw [hso2, hsk2, List.length_append, hlen1]; simp
      · intro x hx
        rw [hso2] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hred1 x h
        · rw [List.mem_singleton.mp h]; exact hRf
      · intro u hu
        rw [hsk2] at hu
        rcases Nat.lt_or_ge u sk.val with hult | huge
        · rw [coeffK, hso2, getD_append_lt _ _ _ (by omega)]
          exact hc1 u hult
        · have hueq : u = so.val.length := by omega
          rw [coeffK, hueq, hso2, getD_append_eq _ _ _, hfv, hwd, hm, hq, hacc,
            ZMod.natCast_mod, hlen1]
          exact longSum_cast ha hb hlov hhivv
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : sk.val = width.val := by scalar_tac
      refine ⟨by rw [hlen1, heq, hw], hred1, ?_⟩
      intro s hs
      exact hc1 s (by rw [heq, hw]; exact hs)
  · exact ⟨hk, hlen, hred, hcoeff⟩

/-- The coefficients of the specification's product of two canonical
representatives: the convolution, over the `N` slots the words occupy. -/
theorem coeff_toRq_mul_unreduced (a b : ring.Rq) (ha : Wf a) (hb : Wf b) (s : ℕ) :
    ((toRq a).1 * (toRq b).1).coeff s
      = ∑ t ∈ Finset.range N, if t ≤ s then coeffK a t * coeffK b (s - t) else 0 := by
  have e1 : ∑ t ∈ Finset.range (s + 1), (if t ≤ s then coeffK a t * coeffK b (s - t) else 0)
      = ∑ t ∈ Finset.range (max (s + 1) N),
          (if t ≤ s then coeffK a t * coeffK b (s - t) else 0) := by
    refine Finset.sum_subset (fun x hx => ?_) (fun x _ hx => ?_)
    · simp only [Finset.mem_range] at hx ⊢; omega
    · simp only [Finset.mem_range, not_lt] at hx
      exact if_neg (by omega)
  have e2 : ∑ t ∈ Finset.range N, (if t ≤ s then coeffK a t * coeffK b (s - t) else 0)
      = ∑ t ∈ Finset.range (max (s + 1) N),
          (if t ≤ s then coeffK a t * coeffK b (s - t) else 0) := by
    refine Finset.sum_subset (fun x hx => ?_) (fun x _ hx => ?_)
    · simp only [Finset.mem_range] at hx ⊢; omega
    · simp only [Finset.mem_range, not_lt] at hx
      by_cases hxs : x ≤ s
      · rw [if_pos hxs, coeffK_of_ge (v := a) (by rw [ha.1]; omega), zero_mul]
      · rw [if_neg hxs]
  rw [e2, ← e1, CPolynomial.coeff_toPoly, CPolynomial.toPoly_mul, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rw [if_pos (by omega : t ≤ s), ← CPolynomial.coeff_toPoly, ← CPolynomial.coeff_toPoly,
    toRq_coeff_eq_coeffK ha, toRq_coeff_eq_coeffK hb]

/-- `long_mul` is the product of the two canonical representatives in `Zq[X]`
(spec: the `*` of `CPolynomial (ZMod q)` inside `cRowSum`). Exactly `2N − 1`
words. -/
theorem long_mul_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b) :
    ringswitch.long_mul a b
      ⦃ out => WfWords (2 * N - 1) out ∧ toCPolyK out = (toRq a).1 * (toRq b).1 ⦄ := by
  rw [ringswitch.long_mul]
  step as ⟨i, hi⟩
  step as ⟨width, hwidth⟩
  have hwv : width.val = 2 * N - 1 := by scalar_tac
  have hcast : lift (UScalar.cast .U128 params.Q) ⦃ y => y.val = (params.Q).val ⦄ :=
    UScalar.cast_inBounds_spec .U128 params.Q
      (by rw [params_Q_val]; norm_num [q, U128.max, U128.numBits])
  step with hcast as ⟨qw, hqw⟩
  simp only [alloc.vec.Vec.with_capacity]
  step with long_mul_loop0_spec a b ha hb params.RING_DEGREE width qw
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize params_RING_DEGREE_val hwv
    (by rw [hqw]; exact params_Q_val) (by simp) (by simp)
    (by intro x hx; simp at hx) (by intro s hs; simp at hs)
    as ⟨z, hzl, hzr, hzc⟩
  refine ⟨⟨hzl, hzr⟩, ?_⟩
  refine toCPolyK_eq_of_coeffK fun k => ?_
  by_cases hk : k < 2 * N - 1
  · rw [hzc k hk, coeff_toRq_mul_unreduced a b ha hb k]
  · rw [coeffK_of_ge (by rw [hzl]; omega), coeff_toRq_mul_unreduced a b ha hb k]
    refine (Finset.sum_eq_zero (fun t ht => ?_)).symm
    simp only [Finset.mem_range] at ht
    by_cases hle : t ≤ k
    · rw [if_pos hle, coeffK_of_ge (v := b) (k := k - t) (by rw [hb.1]; omega), mul_zero]
    · rw [if_neg hle]

/-! ### The high half (Stage 6 candidate T1a)

`div_by_modulus` reads only coefficients `N … 2N − 2` of the defect, and the
`y` subtraction touches only those below `N`. So the quotient is the **high
half of `cRowSum`**, and the low half of every `long_mul` — half the schoolbook
work — was computed and discarded. `long_mul_high` and `c_row_sum_high`
compute only what survives.

The three specs below are the `long_mul` / `c_row_sum` ones with the output
index shifted by `N`: `out[s]` is coefficient `N + s`. The antidiagonal
arithmetic is unchanged and reuses `longSum`, `longSum_cast` and
`coeff_toRq_mul_unreduced` verbatim — for `k ≥ N` the clip is exactly
`lo = k + 1 − N`, `hi = N`, which is what those lemmas already take. -/

/-- `long_mul_high`'s inner loop: the clipped antidiagonal, for `k ≥ N`. -/
theorem long_mul_high_loop0_loop0_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b)
    (n k : Std.Usize) (acc : Std.U128) (i : Std.Usize) (lo : ℕ)
    (hn : n.val = N) (hlo : lo ≤ i.val) (hik : i.val ≤ n.val)
    (hkN : N ≤ k.val) (hlov : lo = k.val + 1 - N)
    (hacc : acc.val = longSum a b k.val lo i.val) :
    ringswitch.long_mul_high_loop0_loop0 a b n k acc i
      ⦃ z => z.val = longSum a b k.val lo n.val ⦄ := by
  rw [ringswitch.long_mul_high_loop0_loop0]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => lo ≤ s.2.val ∧ s.2.val ≤ n.val ∧ s.1.val = longSum a b k.val lo s.2.val)
  · rintro ⟨sa, si⟩ ⟨hlo1, hle1, hval1⟩
    dsimp only at hlo1 hle1 hval1
    simp only [ringswitch.long_mul_high_loop0_loop0.body]
    by_cases hlt : si < n
    · rw [if_pos hlt]
      have hsiN : si.val < N := by rw [← hn]; scalar_tac
      have hsik : si.val ≤ k.val := by omega
      have hkiN : k.val - si.val < N := by omega
      step with coeff_word a ha si as ⟨f, _hRf, hfv⟩
      step with to_u64_id f as ⟨w, hw⟩
      have haiv : w.val = wordN a si.val := by rw [hw, hfv]
      have hcast : lift (UScalar.cast .U128 w) ⦃ y => y.val = w.val ⦄ :=
        UScalar.cast_inBounds_spec .U128 w (by scalar_tac)
      step with hcast as ⟨ai, hai⟩
      step as ⟨d, hd⟩
      step with coeff_word b hb d as ⟨g, _hRg, hgv⟩
      step with to_u64_id g as ⟨w2, hw2⟩
      have hbjv : w2.val = wordN b (k.val - si.val) := by rw [hw2, hgv, hd]
      have hcast2 : lift (UScalar.cast .U128 w2) ⦃ y => y.val = w2.val ⦄ :=
        UScalar.cast_inBounds_spec .U128 w2 (by scalar_tac)
      step with hcast2 as ⟨bj, hbj⟩
      have hbnd : sa.val + ai.val * bj.val ≤ Std.U128.max := by
        have hprod : ai.val * bj.val ≤ q * q := by
          rw [hai, hbj, haiv, hbjv]
          exact Nat.mul_le_mul (Nat.le_of_lt (wordN_lt ha _)) (Nat.le_of_lt (wordN_lt hb _))
        have hone : sa.val ≤ (N - 1) * (q * q) := by
          rw [hval1]
          exact le_trans (longSum_le ha hb k.val lo si.val)
            (Nat.mul_le_mul_right _ (by omega))
        have := accBound
        calc sa.val + ai.val * bj.val ≤ (N - 1) * (q * q) + q * q :=
              Nat.add_le_add hone hprod
          _ = N * (q * q) := by
              have hN1 : N - 1 + 1 = N := by omega
              calc (N - 1) * (q * q) + q * q = ((N - 1) + 1) * (q * q) := by ring
                _ = N * (q * q) := by rw [hN1]
          _ ≤ Std.U128.max := Nat.le_of_lt this
      step as ⟨t, ht⟩
      step as ⟨sa2, hsa2⟩
      step as ⟨si2, hsi2⟩
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      rw [hsa2, ht, hai, hbj, haiv, hbjv, hval1, hsi2,
        longSum_succ a b k.val lo si.val hlo1]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : si.val = n.val := by scalar_tac
      rw [hval1, heq]
  · exact ⟨hlo, hik, hacc⟩

/-- `long_mul_high`'s output loop: coefficient `N + s` at slot `s`. -/
theorem long_mul_high_loop0_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b)
    (n width : Std.Usize) (qw : Std.U128) (out : alloc.vec.Vec cpoly.field.Fp)
    (k : Std.Usize) (hn : n.val = N) (hw : width.val = 2 * N - 1) (hq : qw.val = q)
    (hkN : N ≤ k.val) (hk : k.val ≤ width.val) (hlen : out.val.length = k.val - N)
    (hred : ∀ x ∈ out.val, Red x)
    (hcoeff : ∀ s, s < k.val - N → coeffK out s
      = ∑ t ∈ Finset.range N, if t ≤ N + s then coeffK a t * coeffK b (N + s - t) else 0) :
    ringswitch.long_mul_high_loop0 a b n width qw out k
      ⦃ z => z.val.length = N - 1 ∧ (∀ x ∈ z.val, Red x) ∧
        ∀ s, s < N - 1 → coeffK z s
          = ∑ t ∈ Finset.range N,
              if t ≤ N + s then coeffK a t * coeffK b (N + s - t) else 0 ⦄ := by
  rw [ringswitch.long_mul_high_loop0]
  apply loop.spec_decr_nat (fun s => width.val - s.2.val)
    (fun s => N ≤ s.2.val ∧ s.2.val ≤ width.val ∧ s.1.val.length = s.2.val - N ∧
      (∀ x ∈ s.1.val, Red x) ∧
      ∀ u, u < s.2.val - N → coeffK s.1 u
        = ∑ t ∈ Finset.range N,
            if t ≤ N + u then coeffK a t * coeffK b (N + u - t) else 0)
  · rintro ⟨so, sk⟩ ⟨hkN1, hk1, hlen1, hred1, hc1⟩
    dsimp only at hkN1 hk1 hlen1 hred1 hc1
    simp only [ringswitch.long_mul_high_loop0.body]
    by_cases hlt : sk < width
    · rw [if_pos hlt]
      have hqpos : 0 < q := by norm_num [q]
      have hskb : sk.val < 2 * N - 1 := by rw [← hw]; scalar_tac
      step as ⟨kp1, hkp1⟩
      step as ⟨lo, hlo⟩
      have hlov : lo.val = sk.val + 1 - N := by rw [hlo, hkp1, hn]
      step with long_mul_high_loop0_loop0_spec a b ha hb n sk 0#u128 lo lo.val
        hn (by simp) (by rw [hn]; omega) hkN1 hlov (by simp [longSum_self])
        as ⟨acc, hacc⟩
      step as ⟨m, hm⟩
      have hcast : lift (UScalar.cast .U64 m) ⦃ y => y.val = m.val ⦄ :=
        UScalar.cast_inBounds_spec .U64 m (by
          rw [hm, hq]
          have hb1 : acc.val % q < q := Nat.mod_lt _ hqpos
          have hb2 : q ≤ UScalar.max UScalarTy.U64 := by
            simp only [q, UScalar.max, UScalarTy.numBits]; norm_num
          omega)
      step with hcast as ⟨wd, hwd⟩
      step with fp_new_spec wd as ⟨f, hRf, hfv⟩
      step as ⟨so2, hso2⟩
      step as ⟨sk2, hsk2⟩
      refine ⟨by omega, by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
      · rw [hso2, hsk2, List.length_append, hlen1]; simp; omega
      · intro x hx
        rw [hso2] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hred1 x h
        · rw [List.mem_singleton.mp h]; exact hRf
      · intro u hu
        rw [hsk2] at hu
        rcases Nat.lt_or_ge u (sk.val - N) with hult | huge
        · rw [coeffK, hso2, getD_append_lt _ _ _ (by omega)]
          exact hc1 u hult
        · have hueq : u = so.val.length := by omega
          have hukv : N + u = sk.val := by omega
          have hback : N + (sk.val - N) = sk.val := by omega
          rw [coeffK, hueq, hso2, getD_append_eq _ _ _, hfv, hwd, hm, hq, hacc,
            ZMod.natCast_mod, hlen1, hback, hn]
          exact longSum_cast ha hb (by rw [hlov, if_pos (by omega)])
            (by rw [if_neg (by omega)])
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : sk.val = width.val := by scalar_tac
      refine ⟨by rw [hlen1, heq, hw]; omega, hred1, ?_⟩
      intro s hs
      exact hc1 s (by rw [heq, hw]; omega)
  · exact ⟨hkN, hk, hlen, hred, hcoeff⟩

/-- **`long_mul_high` is the high half of the product**: `N − 1` words, and
`out[s]` is coefficient `N + s` of `a · b` in `Zq[X]`. -/
theorem long_mul_high_spec (a b : ring.Rq) (ha : Wf a) (hb : Wf b) :
    ringswitch.long_mul_high a b
      ⦃ out => WfWords (N - 1) out ∧
        ∀ s, s < N - 1 → coeffK out s = ((toRq a).1 * (toRq b).1).coeff (N + s) ⦄ := by
  rw [ringswitch.long_mul_high]
  step as ⟨i, hi⟩
  step as ⟨width, hwidth⟩
  have hwv : width.val = 2 * N - 1 := by scalar_tac
  have hcast : lift (UScalar.cast .U128 params.Q) ⦃ y => y.val = (params.Q).val ⦄ :=
    UScalar.cast_inBounds_spec .U128 params.Q
      (by rw [params_Q_val]; norm_num [q, U128.max, U128.numBits])
  step with hcast as ⟨qw, hqw⟩
  simp only [alloc.vec.Vec.with_capacity]
  apply spec_mono (long_mul_high_loop0_spec a b ha hb params.RING_DEGREE width qw
    (alloc.vec.Vec.new cpoly.field.Fp) params.RING_DEGREE params_RING_DEGREE_val hwv
    (by rw [hqw]; exact params_Q_val) (by rw [params_RING_DEGREE_val])
    (by rw [params_RING_DEGREE_val, hwv]; omega)
    (by rw [params_RING_DEGREE_val]; simp) (by intro x hx; simp at hx)
    (by intro s hs; rw [params_RING_DEGREE_val] at hs; omega))
  rintro z ⟨hzl, hzr, hzc⟩
  refine ⟨⟨hzl, hzr⟩, fun s hs => ?_⟩
  rw [hzc s hs, coeff_toRq_mul_unreduced a b ha hb (N + s)]

/-! ### `c_row_sum_high` (card T45a)

Since card T45a `c_row_sum_high` dispatches on the matrix's representation. A
dense matrix gets `band_high` over its whole row -- the per-entry walk the
function was before -- and a lazy one gets `c_row_sum_high_lazy`, which walks
the row band by band and contracts every group of a gadget band that passes
the run-time check `group_is_scaled`. The accumulators all hold `highSum`
(`LiftGadget.lean`) over the columns walked so far; a contracted group is
`highSum_contract`, which is bilinearity of the unreduced product and nothing
else. No hypothesis about the blocks' contents is made anywhere: a group that
fails the check is walked entry by entry, and one that passes contributes what
its entries would have. -/

open HachiEquiv.LiftGadget

/-- `add_high_into`'s loop: slots below `t` already hold `acc₀[s] + prod[s]`. -/
theorem add_high_into_loop_spec (n : Std.Usize) (hn : n.val = N)
    (acc0 acc prod : alloc.vec.Vec cpoly.field.Fp) (t : Std.Usize)
    (hal : acc.val.length = N - 1) (har : ∀ x ∈ acc.val, Red x)
    (hpl : prod.val.length = N - 1) (hpr : ∀ x ∈ prod.val, Red x)
    (ht : t.val ≤ N - 1)
    (hbase : ∀ s, s < N - 1 →
      coeffK acc s = coeffK acc0 s + (if s < t.val then coeffK prod s else 0)) :
    ringswitch.add_high_into_loop acc prod n t
      ⦃ z => WfWords (N - 1) z ∧
        ∀ s, s < N - 1 → coeffK z s = coeffK acc0 s + coeffK prod s ⦄ := by
  rw [ringswitch.add_high_into_loop]
  apply loop.spec_decr_nat
    (fun (st : alloc.vec.Vec cpoly.field.Fp × Std.Usize) => N - 1 - st.2.val)
    (fun (st : alloc.vec.Vec cpoly.field.Fp × Std.Usize) => st.2.val ≤ N - 1 ∧
      st.1.val.length = N - 1 ∧ (∀ x ∈ st.1.val, Red x) ∧
      ∀ s, s < N - 1 →
        coeffK st.1 s = coeffK acc0 s + (if s < st.2.val then coeffK prod s else 0))
  · rintro ⟨a1, t1⟩ ⟨ht1, hl1, hr1, hc1⟩
    dsimp only at ht1 hl1 hr1 hc1
    simp only [ringswitch.add_high_into_loop.body]
    step as ⟨nm1, hnm1⟩
    have hnm1v : nm1.val = N - 1 := by rw [hnm1, hn]
    by_cases hlt : t1 < nm1
    · rw [if_pos hlt]
      have ht1b : t1.val < N - 1 := by scalar_tac
      have hta : t1.val < a1.val.length := by rw [hl1]; omega
      have htp : t1.val < prod.val.length := by rw [hpl]; omega
      step as ⟨fa, hfa⟩
      have hRfa : Red fa := by rw [hfa]; exact hr1 _ (List.getElem_mem hta)
      step as ⟨fp, hfp⟩
      have hRfp : Red fp := by rw [hfp]; exact hpr _ (List.getElem_mem htp)
      step with HachiEquiv.Field.fp_add_spec fa fp hRfa hRfp as ⟨f2, hRf2, hf2⟩
      step as ⟨xa, backa, hxa, hbacka⟩
      step as ⟨t2, ht2⟩
      have hwset : (backa f2).val = a1.val.set t1.val f2 := by rw [hbacka]; simp
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · rw [hwset, List.length_set, hl1]
      · exact Red_set hwset hr1 hRf2
      · intro s hs
        by_cases hsq : s = t1.val
        · subst hsq
          rw [coeffK_set_eq hwset hta, hf2, hfa, hfp, ← coeffK_of_lt hta,
            ← coeffK_of_lt htp, hc1 t1.val hs, ht2, if_neg (by omega), if_pos (by omega),
            add_zero]
        · rw [coeffK_set_ne hwset hsq, hc1 s hs, ht2]
          congr 1
          by_cases hsl : s < t1.val
          · rw [if_pos hsl, if_pos (by omega)]
          · rw [if_neg hsl, if_neg (by omega)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : t1.val = N - 1 := by scalar_tac
      refine ⟨⟨hl1, hr1⟩, ?_⟩
      intro s hs
      rw [hc1 s hs, heq, if_pos hs]
  · exact ⟨ht, hal, har, hbase⟩

/-- **`add_high_into` adds two high halves**, slot by slot. -/
theorem add_high_into_spec (acc prod : alloc.vec.Vec cpoly.field.Fp)
    (ha : WfWords (N - 1) acc) (hp : WfWords (N - 1) prod) :
    ringswitch.add_high_into acc prod
      ⦃ z => WfWords (N - 1) z ∧
        ∀ s, s < N - 1 → coeffK z s = coeffK acc s + coeffK prod s ⦄ := by
  rw [ringswitch.add_high_into]
  exact add_high_into_loop_spec params.RING_DEGREE params_RING_DEGREE_val acc acc prod
    0#usize ha.1 ha.2 hp.1 hp.2 (by simp) (by intro s _; simp)

/-- `band_high`'s loop: after column `j` the accumulator has gained
`highSum` over `[lo, j)`. -/
theorem band_high_loop_spec {kb kz : ℕ} (blk z : linalg.PolyVec) (hblk : WfVec kb blk)
    (hz : WfVec kz z) (hi zoff : Std.Usize) (lo : ℕ) (hhi : hi.val ≤ kb)
    (hzoff : zoff.val + hi.val ≤ kz) (acc0 acc : alloc.vec.Vec cpoly.field.Fp)
    (j : Std.Usize) (hlo : lo ≤ j.val) (hj : j.val ≤ hi.val) (hacc : WfWords (N - 1) acc)
    (hval : ∀ t, t < N - 1 →
      coeffK acc t = coeffK acc0 t + highSum blk z zoff.val lo j.val t) :
    ringswitch.band_high_loop acc blk hi z zoff j
      ⦃ out => WfWords (N - 1) out ∧ ∀ t, t < N - 1 →
          coeffK out t = coeffK acc0 t + highSum blk z zoff.val lo hi.val t ⦄ := by
  rw [ringswitch.band_high_loop]
  apply loop.spec_decr_nat
    (fun (st : alloc.vec.Vec cpoly.field.Fp × Std.Usize) => hi.val - st.2.val)
    (fun (st : alloc.vec.Vec cpoly.field.Fp × Std.Usize) => lo ≤ st.2.val ∧
      st.2.val ≤ hi.val ∧ WfWords (N - 1) st.1 ∧ ∀ t, t < N - 1 →
        coeffK st.1 t = coeffK acc0 t + highSum blk z zoff.val lo st.2.val t)
  · rintro ⟨a1, j1⟩ ⟨hlo1, hj1, hW1, hv1⟩
    dsimp only at hlo1 hj1 hW1 hv1
    simp only [ringswitch.band_high_loop.body]
    by_cases hlt : j1 < hi
    · rw [if_pos hlt]
      have hj1b : j1.val < kb := by scalar_tac
      step with poly_vec_get_spec (k := kb) blk hblk j1 hj1b as ⟨e, hWe, he⟩
      step with RqBridge.is_zero_spec e hWe as ⟨bz, hbz⟩
      by_cases hzero : bz = true
      · rw [if_pos hzero]
        simp only [bind_tc_ok]
        step as ⟨j2, hj2⟩
        refine ⟨by scalar_tac, by scalar_tac, hW1, ?_, by scalar_tac⟩
        intro t ht
        have h0 : vecAt blk j1.val = 0 := by rw [← he]; exact hbz.1 hzero
        rw [hv1 t ht, hj2, highSum_succ _ _ _ _ _ _ hlo1, h0, Rq.zero_val, zero_mul,
          CPolynomial.coeff_zero, add_zero]
      · rw [if_neg hzero]
        have hkz : kz ≤ Usize.max := by rw [← hz.1]; exact z.property
        step as ⟨iz, hiz⟩
        step with poly_vec_get_spec (k := kz) z hz iz (by scalar_tac) as ⟨zj, hWzj, hzj⟩
        step with long_mul_high_spec e zj hWe hWzj as ⟨prod, hWp, hp⟩
        step with add_high_into_spec a1 prod hW1 hWp as ⟨a2, hW2, ha2⟩
        step as ⟨j2, hj2⟩
        refine ⟨by scalar_tac, by scalar_tac, hW2, ?_, by scalar_tac⟩
        intro t ht
        rw [ha2 t ht, hv1 t ht, hj2, highSum_succ _ _ _ _ _ _ hlo1, hp t ht, he, hzj, hiz,
          add_assoc]
    · rw [if_neg hlt, WP.spec_ok]
      have heq : j1.val = hi.val := by scalar_tac
      exact ⟨hW1, fun t ht => by rw [hv1 t ht, heq]⟩
  · exact ⟨hlo, hj, hacc, hval⟩

/-- **`band_high` is the per-entry walk over `[lo, hi)`**: the accumulator gains
coefficient `N + t` of `Σ_{lo ≤ j < hi} blk[j] · z[zoff + j]`. Zero entries are
skipped, which is `0 · z = 0`. -/
theorem band_high_spec {kb kz : ℕ} (acc : alloc.vec.Vec cpoly.field.Fp)
    (blk : linalg.PolyVec) (lo hi : Std.Usize) (z : linalg.PolyVec) (zoff : Std.Usize)
    (hblk : WfVec kb blk) (hz : WfVec kz z) (hlo : lo.val ≤ hi.val) (hhi : hi.val ≤ kb)
    (hzoff : zoff.val + hi.val ≤ kz) (hacc : WfWords (N - 1) acc) :
    ringswitch.band_high acc blk lo hi z zoff
      ⦃ out => WfWords (N - 1) out ∧ ∀ t, t < N - 1 →
          coeffK out t = coeffK acc t + highSum blk z zoff.val lo.val hi.val t ⦄ := by
  rw [ringswitch.band_high]
  exact band_high_loop_spec blk z hblk hz hi zoff lo.val hhi hzoff acc acc lo le_rfl hlo hacc
    (fun t _ => by rw [highSum_self, add_zero])

/-- `group_high`'s loop: after the whole groups below `base` the accumulator has
gained `highSum` over `[0, base)`, whichever way each group was paid for. -/
theorem group_high_loop_spec {kb kz : ℕ} (blk z : linalg.PolyVec) (hblk : WfVec kb blk)
    (hz : WfVec kz z) (len gsize zoff : Std.Usize) (w : alloc.vec.Vec cpoly.field.Fp)
    (hlen : len.val ≤ kb) (hzoff : zoff.val + len.val ≤ kz) (hg : 0 < gsize.val)
    (hw : WfWeights gsize.val w) (acc0 acc : alloc.vec.Vec cpoly.field.Fp)
    (base : Std.Usize) (hbase : base.val ≤ len.val) (hacc : WfWords (N - 1) acc)
    (hval : ∀ t, t < N - 1 →
      coeffK acc t = coeffK acc0 t + highSum blk z zoff.val 0 base.val t) :
    ringswitch.group_high_loop acc blk len gsize w z zoff base
      ⦃ res => WfWords (N - 1) res.1 ∧ res.2.val ≤ len.val ∧ ∀ t, t < N - 1 →
          coeffK res.1 t = coeffK acc0 t + highSum blk z zoff.val 0 res.2.val t ⦄ := by
  have hkb : kb ≤ Usize.max := by rw [← hblk.1]; exact blk.property
  have hkz : kz ≤ Usize.max := by rw [← hz.1]; exact z.property
  rw [ringswitch.group_high_loop]
  apply loop.spec_decr_nat
    (fun (st : alloc.vec.Vec cpoly.field.Fp × Std.Usize) => len.val - st.2.val)
    (fun (st : alloc.vec.Vec cpoly.field.Fp × Std.Usize) => st.2.val ≤ len.val ∧
      WfWords (N - 1) st.1 ∧ ∀ t, t < N - 1 →
        coeffK st.1 t = coeffK acc0 t + highSum blk z zoff.val 0 st.2.val t)
  · rintro ⟨a1, b1⟩ ⟨hb1, hW1, hv1⟩
    dsimp only at hb1 hW1 hv1
    simp only [ringswitch.group_high_loop.body]
    step as ⟨rest, hrest⟩
    by_cases hle : gsize ≤ rest
    · rw [if_pos hle]
      have hgb : b1.val + gsize.val ≤ len.val := by scalar_tac
      step with group_is_scaled_spec (kb := kb) blk hblk b1 gsize w hw (by omega) (by omega)
        as ⟨sc, hsc⟩
      have hnext : ∀ t, t < N - 1 →
          highSum blk z zoff.val 0 b1.val t
            + highSum blk z zoff.val b1.val (b1.val + gsize.val) t
          = highSum blk z zoff.val 0 (b1.val + gsize.val) t :=
        fun t _ => highSum_consecutive _ _ _ _ _ _ _ (Nat.zero_le _) (by omega)
      by_cases hs : sc = true
      · rw [if_pos hs]
        have hsc' := hsc hs
        step with poly_vec_get_spec (k := kb) blk hblk b1 (by omega) as ⟨f, hWf, hf⟩
        step with RqBridge.is_zero_spec f hWf as ⟨bz, hbz⟩
        by_cases hzero : bz = true
        · rw [if_pos hzero]
          simp only [bind_tc_ok]
          step as ⟨b2, hb2⟩
          refine ⟨by scalar_tac, hW1, ?_, by scalar_tac⟩
          intro t ht
          have h0 : vecAt blk b1.val = 0 := by rw [← hf]; exact hbz.1 hzero
          rw [hv1 t ht, hb2, ← hnext t ht,
            highSum_zero_group blk z zoff.val b1.val gsize.val t (wAt w) hsc' h0, add_zero]
        · rw [if_neg hzero]
          step as ⟨i1, hi1⟩
          step with recompose_spec (kz := kz) z hz i1 gsize w hw (by scalar_tac)
            as ⟨r, hWr, hr⟩
          step with long_mul_high_spec f r hWf hWr as ⟨prod, hWp, hp⟩
          step with add_high_into_spec a1 prod hW1 hWp as ⟨a2, hW2, ha2⟩
          step as ⟨b2, hb2⟩
          refine ⟨by scalar_tac, hW2, ?_, by scalar_tac⟩
          intro t ht
          rw [ha2 t ht, hv1 t ht, hb2, ← hnext t ht,
            highSum_contract blk z zoff.val b1.val gsize.val t (wAt w) hsc', hp t ht, hf, hr,
            hi1, add_assoc]
      · rw [if_neg hs]
        step as ⟨i1, hi1⟩
        step with band_high_spec (kb := kb) (kz := kz) a1 blk b1 i1 z zoff hblk hz
          (by scalar_tac) (by scalar_tac) (by scalar_tac) hW1 as ⟨a2, hW2, ha2⟩
        step as ⟨b2, hb2⟩
        refine ⟨by scalar_tac, hW2, ?_, by scalar_tac⟩
        intro t ht
        rw [ha2 t ht, hv1 t ht, hb2, ← hnext t ht, hi1, add_assoc]
    · rw [if_neg hle, WP.spec_ok]
      exact ⟨hW1, hb1, hv1⟩
  · exact ⟨hbase, hacc, hval⟩

/-- **`group_high` is the per-entry walk over `[0, len)`**, whatever the block
holds: a whole group that passes `group_is_scaled` is paid with one product
(`highSum_contract`), or none if its leader is zero (`highSum_zero_group`); a
group that fails, and the trailing partial group, go through `band_high`. -/
theorem group_high_spec {kb kz : ℕ} (acc : alloc.vec.Vec cpoly.field.Fp)
    (blk : linalg.PolyVec) (len gsize : Std.Usize) (w : alloc.vec.Vec cpoly.field.Fp)
    (z : linalg.PolyVec) (zoff : Std.Usize)
    (hblk : WfVec kb blk) (hz : WfVec kz z) (hlen : len.val ≤ kb)
    (hzoff : zoff.val + len.val ≤ kz) (hg : 0 < gsize.val) (hw : WfWeights gsize.val w)
    (hacc : WfWords (N - 1) acc) :
    ringswitch.group_high acc blk len gsize w z zoff
      ⦃ out => WfWords (N - 1) out ∧ ∀ t, t < N - 1 →
          coeffK out t = coeffK acc t + highSum blk z zoff.val 0 len.val t ⦄ := by
  rw [ringswitch.group_high]
  step with group_high_loop_spec (kb := kb) (kz := kz) blk z hblk hz len gsize zoff w hlen
    hzoff hg hw acc acc 0#usize (by simp) hacc
    (fun t _ => by rw [show ((0#usize : Std.Usize).val) = 0 from rfl, highSum_self, add_zero])
    as ⟨a1, b1, hW1, hb1, hv1⟩
  apply spec_mono (band_high_spec (kb := kb) (kz := kz) a1 blk b1 len z zoff hblk hz hb1
    hlen hzoff hW1)
  rintro out ⟨hW, hv⟩
  refine ⟨hW, fun t ht => ?_⟩
  rw [hv t ht, hv1 t ht, add_assoc,
    highSum_consecutive _ _ _ _ _ _ _ (Nat.zero_le _) hb1]

/-- What `high_zeros` hands the walks: a well-formed accumulator reading `0`. -/
theorem high_zeros_facts {acc : alloc.vec.Vec cpoly.field.Fp}
    (h : acc.val = List.replicate (N - 1) cpoly.field.Fp.ZERO) :
    WfWords (N - 1) acc ∧ ∀ t, t < N - 1 → coeffK acc t = 0 := by
  refine ⟨⟨by rw [h, List.length_replicate], fun x hx => ?_⟩, fun t ht => ?_⟩
  · rw [h] at hx
    rw [List.eq_of_mem_replicate hx]
    exact Red_zero
  · unfold coeffK
    rw [h, List.getD_eq_getElem _ _ (by rw [List.length_replicate]; omega),
      List.getElem_replicate]
    simp [toK, cpoly.field.Fp.ZERO]

/-- **The lazy row walk is the row's high half**: for every well-formed block
set, whatever the blocks hold, `c_row_sum_high_lazy` returns coefficient
`N + t` of `Σ_j blocksAt(i, j) · z_j`. The row is cut into its three column
bands (`blocks_row_split`); on each of the five row shapes every band is
either a zero band or one block's row, and the walks over the non-zero ones
are `band_high_spec` and `group_high_spec`. -/
theorem c_row_sum_high_lazy_spec {n μ : ℕ} (b : ringswitch.RlinBlocks)
    (hb : WfRlinBlocks n μ b) (z : linalg.PolyVec) (hz : WfVec μ z) (i : Std.Usize)
    (hi : i.val < n) :
    ringswitch.c_row_sum_high_lazy b z i
      ⦃ out => WfWords (N - 1) out ∧ ∀ t, t < N - 1 → coeffK out t
          = ∑ j ∈ Finset.range μ, ((blocksAt b i.val j).1 * (vecAt z j).1).coeff (N + t) ⦄ := by
  obtain ⟨hD, hB, hgb, hgc, hga, hT, hA, -, -, hn, hμ, hnmax, hμmax⟩ := hb
  have h8 : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  have h5 : (params.Z_DIGITS).val = 5 := by simp [params.Z_DIGITS]
  have hz0 : ((0#usize : Std.Usize)).val = 0 := rfl
  rw [ringswitch.c_row_sum_high_lazy]
  step as ⟨gz, hgz⟩
  step with gadget_weights_spec params.GADGET_DIGITS as ⟨gw, hgwl, hgwr, _hgwv⟩
  step with gadget_weights_spec params.Z_DIGITS as ⟨zw, hzwl, hzwr, _hzwv⟩
  step with jt_gadget_weights_spec as ⟨jw, hjwl, hjwr⟩
  step with high_zeros_spec as ⟨acc, hacc⟩
  obtain ⟨hWacc, hacc0⟩ := high_zeros_facts hacc
  have hgw : WfWeights (params.GADGET_DIGITS).val gw := WfWeights_of_table hgwl hgwr
  have hzw : WfWeights (params.Z_DIGITS).val zw := WfWeights_of_table hzwl hzwr
  have hgzv : gz.val = 40 := by rw [hgz, h8, h5]
  have hjw : WfWeights gz.val jw := WfWeights_of_table (by rw [hjwl, hgzv]) hjwr
  have hsplit : ∀ t, ∑ j ∈ Finset.range μ, ((blocksAt b i.val j).1 * (vecAt z j).1).coeff (N + t)
      = bandSum b i.val z 0 b.cw.val t + bandSum b i.val z b.cw.val b.ct.val t
        + bandSum b i.val z (b.cw.val + b.ct.val) b.cz.val t := by
    intro t
    rw [← hμ]
    exact blocks_row_split _ _ _ _ _ _ _
  by_cases h1 : i < b.d_rows
  · -- c1: `[ D | 0 | 0 ]`, per entry over `ŵ`.
    have h1' : i.val < b.d_rows.val := by scalar_tac
    rw [if_pos h1]
    step with poly_matrix_row_spec (rows := b.d_rows.val) (cols := b.cw.val) b.d hD i h1'
      as ⟨pv, hWpv, hpv⟩
    apply spec_mono (band_high_spec (kb := b.cw.val) (kz := μ) acc pv 0#usize b.cw z 0#usize
      hWpv hz (by simp) le_rfl (by rw [hz0]; omega) hWacc)
    rintro out ⟨hW, hv⟩
    refine ⟨hW, fun t ht => ?_⟩
    rw [hv t ht, hacc0 t ht, zero_add, hsplit t, hz0,
      bandSum_eq b i.val z 0 b.cw.val t pv (fun j hj => by
        rw [blocksAt_d h1', if_pos (by omega), hpv, zero_add]; rfl),
      bandSum_zero b i.val z _ _ t (fun j hj => by rw [blocksAt_d h1', if_neg (by omega)]),
      bandSum_zero b i.val z _ _ t (fun j hj => by rw [blocksAt_d h1', if_neg (by omega)]),
      add_zero, add_zero]
  · have h1' : ¬ i.val < b.d_rows.val := by scalar_tac
    rw [if_neg h1]
    step as ⟨i1, hi1⟩
    by_cases h2 : i < i1
    · -- c2: `[ 0 | B | 0 ]`, per entry over `t̂`.
      have h2' : i.val < b.d_rows.val + b.b_rows.val := by scalar_tac
      rw [if_pos h2]
      step as ⟨i2, hi2⟩
      step with poly_matrix_row_spec (rows := b.b_rows.val) (cols := b.ct.val) b.bmat hB i2
        (by scalar_tac) as ⟨pv, hWpv, hpv⟩
      apply spec_mono (band_high_spec (kb := b.ct.val) (kz := μ) acc pv 0#usize b.ct z b.cw
        hWpv hz (by simp) le_rfl (by omega) hWacc)
      rintro out ⟨hW, hv⟩
      refine ⟨hW, fun t ht => ?_⟩
      rw [hv t ht, hacc0 t ht, zero_add, hsplit t, hz0,
        bandSum_zero b i.val z _ _ t (fun j hj => by
          rw [blocksAt_b h1' h2', if_pos (by omega)]),
        bandSum_eq b i.val z b.cw.val b.ct.val t pv (fun j hj => by
          rw [blocksAt_b h1' h2', if_neg (by omega), if_pos (by omega), hpv, hi2,
            Nat.add_sub_cancel_left]; rfl),
        bandSum_zero b i.val z _ _ t (fun j hj => by
          rw [blocksAt_b h1' h2', if_neg (by omega), if_neg (by omega)]),
        zero_add, add_zero]
    · have h2' : ¬ i.val < b.d_rows.val + b.b_rows.val := by scalar_tac
      rw [if_neg h2]
      by_cases h3 : i = i1
      · -- c3: `[ Gᵀb | 0 | 0 ]`, contracted over `ŵ`.
        have h3' : i.val = b.d_rows.val + b.b_rows.val := by rw [h3]; scalar_tac
        rw [if_pos h3]
        apply spec_mono (group_high_spec (kb := b.cw.val) (kz := μ) acc b.g_b b.cw
          params.GADGET_DIGITS gw z 0#usize hgb hz le_rfl (by rw [hz0]; omega)
          (by rw [h8]; norm_num) hgw hWacc)
        rintro out ⟨hW, hv⟩
        refine ⟨hW, fun t ht => ?_⟩
        rw [hv t ht, hacc0 t ht, zero_add, hsplit t, hz0,
          bandSum_eq b i.val z 0 b.cw.val t b.g_b (fun j hj => by
            rw [blocksAt_gb h3', if_pos (by omega), zero_add]),
          bandSum_zero b i.val z _ _ t (fun j hj => by rw [blocksAt_gb h3', if_neg (by omega)]),
          bandSum_zero b i.val z _ _ t (fun j hj => by rw [blocksAt_gb h3', if_neg (by omega)]),
          add_zero, add_zero]
      · have h3' : i.val ≠ b.d_rows.val + b.b_rows.val := by
          intro hc; exact h3 (by scalar_tac)
        rw [if_neg h3]
        step as ⟨i2, hi2⟩
        by_cases h4 : i = i2
        · -- c4: `[ Gᵀc | 0 | −Jᵀ(Gᵀa) ]`, contracted over `ŵ` and `ẑ`.
          have h4' : i.val = b.d_rows.val + b.b_rows.val + 1 := by rw [h4]; scalar_tac
          rw [if_pos h4]
          step with group_high_spec (kb := b.cw.val) (kz := μ) acc b.g_c b.cw
            params.GADGET_DIGITS gw z 0#usize hgc hz le_rfl (by rw [hz0]; omega)
            (by rw [h8]; norm_num) hgw hWacc as ⟨acc1, hW1, hv1⟩
          step as ⟨off, hoff⟩
          apply spec_mono (group_high_spec (kb := b.cz.val) (kz := μ) acc1 b.neg_jt_g_a b.cz
            gz jw z off hga hz le_rfl (by omega) (by rw [hgzv]; norm_num) hjw hW1)
          rintro out ⟨hW, hv⟩
          refine ⟨hW, fun t ht => ?_⟩
          rw [hv t ht, hv1 t ht, hacc0 t ht, zero_add, hsplit t, hoff,
            bandSum_eq b i.val z 0 b.cw.val t b.g_c (fun j hj => by
              rw [blocksAt_gc h4', if_pos (by omega), zero_add]),
            bandSum_zero b i.val z _ _ t (fun j hj => by
              rw [blocksAt_gc h4', if_neg (by omega), if_pos (by omega)]),
            bandSum_eq b i.val z (b.cw.val + b.ct.val) b.cz.val t b.neg_jt_g_a (fun j hj => by
              rw [blocksAt_gc h4', if_neg (by omega), if_neg (by omega),
                show b.cw.val + b.ct.val + j - b.cw.val - b.ct.val = j by omega]),
            add_zero]
        · -- c5: `[ 0 | cᵀ ⊗ G | −(AJ) ]`, contracted over `t̂` and `ẑ`.
          have h4' : i.val ≠ b.d_rows.val + b.b_rows.val + 1 := by
            intro hc; exact h4 (by scalar_tac)
          rw [if_neg h4]
          step as ⟨i3, hi3⟩
          step as ⟨i4, hi4⟩
          step as ⟨p, hp⟩
          have hpv' : p.val = i.val - b.d_rows.val - b.b_rows.val - 2 := by scalar_tac
          have hplt : p.val < b.t_rows.val := by omega
          step with poly_matrix_row_spec (rows := b.t_rows.val) (cols := b.ct.val) b.tensor hT
            p hplt as ⟨pv, hWpv, hpv⟩
          step with group_high_spec (kb := b.ct.val) (kz := μ) acc pv b.ct
            params.GADGET_DIGITS gw z b.cw hWpv hz le_rfl (by omega)
            (by rw [h8]; norm_num) hgw hWacc as ⟨acc1, hW1, hv1⟩
          step as ⟨off, hoff⟩
          step with poly_matrix_row_spec (rows := b.t_rows.val) (cols := b.cz.val) b.neg_aj hA
            p hplt as ⟨pv1, hWpv1, hpv1⟩
          apply spec_mono (group_high_spec (kb := b.cz.val) (kz := μ) acc1 pv1 b.cz
            params.Z_DIGITS zw z off hWpv1 hz le_rfl (by omega) (by rw [h5]; norm_num) hzw hW1)
          rintro out ⟨hW, hv⟩
          refine ⟨hW, fun t ht => ?_⟩
          rw [hv t ht, hv1 t ht, hacc0 t ht, zero_add, hsplit t, hoff,
            bandSum_zero b i.val z _ _ t (fun j hj => by
              rw [blocksAt_t h2' h3' h4', if_pos (by omega)]),
            bandSum_eq b i.val z b.cw.val b.ct.val t pv (fun j hj => by
              rw [blocksAt_t h2' h3' h4', if_neg (by omega), if_pos (by omega), hpv, hpv',
                Nat.add_sub_cancel_left]; rfl),
            bandSum_eq b i.val z (b.cw.val + b.ct.val) b.cz.val t pv1 (fun j hj => by
              rw [blocksAt_t h2' h3' h4', if_neg (by omega), if_neg (by omega), hpv1, hpv',
                show b.cw.val + b.ct.val + j - b.cw.val - b.ct.val = j by omega]; rfl),
            zero_add]

/-! #### The dense arm

Card T45a keeps the dense arm's body inline in the `match` (routing it through
`band_high` cost both paths 17-22% at the bench: `band_high` stopped being
inlined), so the three loops below are the pre-T45a ones, extracted
byte-identically, and so are their specs. -/

/-- The zero-fill of `c_row_sum_high`: `N − 1` zero words. -/
theorem c_row_sum_high_zero_loop_spec (n : Std.Usize) (hn : n.val = N)
    (acc : alloc.vec.Vec cpoly.field.Fp) (k : Std.Usize) (hk : k.val ≤ N - 1)
    (hacc : acc.val = List.replicate k.val cpoly.field.Fp.ZERO) :
    ringswitch.c_row_sum_high_loop0 n acc k
      ⦃ z => z.val = List.replicate (N - 1) cpoly.field.Fp.ZERO ⦄ := by
  rw [ringswitch.c_row_sum_high_loop0]
  apply loop.spec_decr_nat (fun s => N - 1 - s.2.val)
    (fun s => s.2.val ≤ N - 1 ∧ s.1.val = List.replicate s.2.val cpoly.field.Fp.ZERO)
  · rintro ⟨o1, i1⟩ ⟨hi1, ho1⟩
    dsimp only at hi1 ho1
    simp only [ringswitch.c_row_sum_high_loop0.body]
    step as ⟨nm1, hnm1⟩
    have hnm1v : nm1.val = N - 1 := by rw [hnm1, hn]
    by_cases hlt : i1 < nm1
    · rw [if_pos hlt]
      have hlen : o1.val.length = i1.val := by rw [ho1, List.length_replicate]
      have hib : i1.val < N - 1 := by have := hlt; scalar_tac
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by omega, ?_, by omega⟩
      rw [ho2, hi2, ho1, List.replicate_succ']
    · rw [if_neg hlt, WP.spec_ok]
      show o1.val = List.replicate (N - 1) cpoly.field.Fp.ZERO
      have heq : i1.val = N - 1 := by scalar_tac
      rw [ho1, heq]
  · exact ⟨hk, hacc⟩

/-- The accumulation loop of `c_row_sum_high`, over `N − 1` slots. -/
theorem c_row_sum_high_add_loop_spec (n : Std.Usize) (hn : n.val = N)
    (acc prod : alloc.vec.Vec cpoly.field.Fp) (t : Std.Usize) (g : ℕ → ZMod q)
    (hal : acc.val.length = N - 1) (har : ∀ x ∈ acc.val, Red x)
    (hpl : prod.val.length = N - 1) (hpr : ∀ x ∈ prod.val, Red x)
    (ht : t.val ≤ N - 1)
    (hbase : ∀ s, s < N - 1 →
      coeffK acc s = g s + (if s < t.val then coeffK prod s else 0)) :
    ringswitch.c_row_sum_high_loop1_loop0 n acc prod t
      ⦃ z => z.val.length = N - 1 ∧ (∀ x ∈ z.val, Red x) ∧
        ∀ s, s < N - 1 → coeffK z s = g s + coeffK prod s ⦄ := by
  rw [ringswitch.c_row_sum_high_loop1_loop0]
  apply loop.spec_decr_nat (fun st => N - 1 - st.2.val)
    (fun st => st.2.val ≤ N - 1 ∧ st.1.val.length = N - 1 ∧ (∀ x ∈ st.1.val, Red x) ∧
      ∀ s, s < N - 1 → coeffK st.1 s = g s + (if s < st.2.val then coeffK prod s else 0))
  · rintro ⟨a1, t1⟩ ⟨ht1, hl1, hr1, hc1⟩
    dsimp only at ht1 hl1 hr1 hc1
    simp only [ringswitch.c_row_sum_high_loop1_loop0.body]
    step as ⟨nm1, hnm1⟩
    have hnm1v : nm1.val = N - 1 := by rw [hnm1, hn]
    by_cases hlt : t1 < nm1
    · rw [if_pos hlt]
      have ht1b : t1.val < N - 1 := by scalar_tac
      have hta : t1.val < a1.val.length := by rw [hl1]; omega
      have htp : t1.val < prod.val.length := by rw [hpl]; omega
      step as ⟨fa, hfa⟩
      have hRfa : Red fa := by rw [hfa]; exact hr1 _ (List.getElem_mem hta)
      step as ⟨fp, hfp⟩
      have hRfp : Red fp := by rw [hfp]; exact hpr _ (List.getElem_mem htp)
      step with HachiEquiv.Field.fp_add_spec fa fp hRfa hRfp as ⟨f2, hRf2, hf2⟩
      step as ⟨xa, backa, hxa, hbacka⟩
      step as ⟨t2, ht2⟩
      have hwset : (backa f2).val = a1.val.set t1.val f2 := by rw [hbacka]; simp
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · rw [hwset, List.length_set, hl1]
      · exact Red_set hwset hr1 hRf2
      · intro s hs
        by_cases hsq : s = t1.val
        · subst hsq
          rw [coeffK_set_eq hwset hta, hf2, hfa, hfp, ← coeffK_of_lt hta,
            ← coeffK_of_lt htp, hc1 t1.val hs, ht2, if_neg (by omega), if_pos (by omega),
            add_zero]
        · rw [coeffK_set_ne hwset hsq, hc1 s hs, ht2]
          congr 1
          by_cases hsl : s < t1.val
          · rw [if_pos hsl, if_pos (by omega)]
          · rw [if_neg hsl, if_neg (by omega)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : t1.val = N - 1 := by scalar_tac
      refine ⟨hl1, hr1, ?_⟩
      intro s hs
      rw [hc1 s hs, heq, if_pos hs]
  · exact ⟨ht, hal, har, hbase⟩

/-- The column loop of `c_row_sum_high`.

After card W2 the row is not pulled out of the matrix once and indexed; the
loop asks `RlinMat::entry` for `(i, j)` on each column, so the summand is
`rlinAt s.m i j` where it used to be the `j`-th entry of a fetched row.  The
two read the same element -- that is `rlin_entry_spec` -- and the invariant is
otherwise word for word what it was. -/
theorem c_row_sum_high_col_loop_spec {nr μ : ℕ} (s : ringswitch.RlinStatement)
    (z : linalg.PolyVec) (i n cols : Std.Usize)
    (hWm : WfRlinMat nr μ s.m) (hi : i.val < nr)
    (hn : n.val = N) (hcols : cols.val = μ)
    (hz : WfVec μ z) (acc : alloc.vec.Vec cpoly.field.Fp)
    (j : Std.Usize) (hal : acc.val.length = N - 1) (har : ∀ x ∈ acc.val, Red x)
    (hj : j.val ≤ μ)
    (hbase : ∀ w, w < N - 1 → coeffK acc w
      = (∑ t ∈ Finset.range j.val, (rlinAt s.m i.val t).1
            * (toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))).1).coeff (N + w)) :
    ringswitch.c_row_sum_high_loop1 s z i n cols acc j
      ⦃ out => WfWords (N - 1) out ∧
        ∀ w, w < N - 1 → coeffK out w
          = (∑ t ∈ Finset.range μ, (rlinAt s.m i.val t).1
                * (toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))).1).coeff (N + w) ⦄ := by
  rw [ringswitch.c_row_sum_high_loop1]
  apply loop.spec_decr_nat (fun st => μ - st.2.val)
    (fun st => st.2.val ≤ μ ∧ st.1.val.length = N - 1 ∧ (∀ x ∈ st.1.val, Red x) ∧
      ∀ w, w < N - 1 → coeffK st.1 w
        = (∑ t ∈ Finset.range st.2.val, (rlinAt s.m i.val t).1
              * (toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))).1).coeff (N + w))
  · rintro ⟨a1, j1⟩ ⟨hj1, hl1, hr1, hc1⟩
    dsimp only at hj1 hl1 hr1 hc1
    simp only [ringswitch.c_row_sum_high_loop1.body]
    by_cases hlt : j1 < cols
    · rw [if_pos hlt]
      have hjm : j1.val < μ := by rw [← hcols]; scalar_tac
      have hjz : j1.val < z.val.length := by rw [hz.1]; exact hjm
      simp only [ringswitch.RlinStatement.impl.m, bind_tc_ok]
      step with ZeroCheck.rlin_entry_spec (n := nr) (μ := μ) s.m hWm i j1 hi hjm
        as ⟨r, hWr, hrv⟩
      have hrv' : toRq r = rlinAt s.m i.val j1.val := hrv
      step with RqBridge.is_zero_spec r hWr as ⟨bz, hbz⟩
      by_cases hzero : bz = true
      · rw [if_pos hzero]
        step as ⟨j2, hj2⟩
        refine ⟨by scalar_tac, hl1, hr1, ?_, by scalar_tac⟩
        intro w hw
        have hz0 : rlinAt s.m i.val j1.val = 0 := by rw [← hrv']; exact hbz.1 hzero
        rw [hc1 w hw, hj2, Finset.sum_range_succ, hz0]
        simp
      rw [if_neg hzero]
      simp only [linalg.PolyVec.get]
      step as ⟨r1, hr1'⟩
      have hWr1 : Wf r1 := by rw [hr1']; exact hz.2 _ (List.getElem_mem hjz)
      step with long_mul_high_spec r r1 hWr hWr1 as ⟨prod, hWprod, hprod⟩
      step with c_row_sum_high_add_loop_spec n hn a1 prod 0#usize
        (fun w => (∑ t ∈ Finset.range j1.val, (rlinAt s.m i.val t).1
          * (toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))).1).coeff (N + w))
        hl1 hr1 hWprod.1 hWprod.2 (by simp)
        (by intro w hw; rw [hc1 w hw]; simp)
        as ⟨a2, hl2, hr2, hc2⟩
      step as ⟨j2, hj2⟩
      refine ⟨by scalar_tac, hl2, hr2, ?_, by scalar_tac⟩
      intro w hw
      rw [hc2 w hw, hj2, Finset.sum_range_succ, cpoly_coeff_add,
        hprod w hw, hrv', hr1', List.getD_eq_getElem _ _ hjz]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : j1.val = μ := by rw [← hcols]; scalar_tac
      exact ⟨⟨hl1, hr1⟩, fun w hw => by rw [hc1 w hw, heq]⟩
  · exact ⟨hj, hal, har, hbase⟩

/-- `c_row_sum_high` against the entry function `rlinAt`, in either
representation: the dense arm is `band_high` over the whole row, the lazy arm
`c_row_sum_high_lazy_spec`. -/
theorem c_row_sum_high_rlin_spec {n μ : ℕ} (s : ringswitch.RlinStatement)
    (z : linalg.PolyVec) (i : Std.Usize) (hWm : WfRlinMat n μ s.m) (hz : WfVec μ z)
    (hi : i.val < n) :
    ringswitch.c_row_sum_high s z i
      ⦃ out => WfWords (N - 1) out ∧ ∀ t, t < N - 1 → coeffK out t
          = ∑ j ∈ Finset.range μ, ((rlinAt s.m i.val j).1 * (vecAt z j).1).coeff (N + t) ⦄ := by
  have hz0 : ((0#usize : Std.Usize)).val = 0 := rfl
  rw [ringswitch.c_row_sum_high]
  simp only [ringswitch.RlinStatement.impl.m, bind_tc_ok]
  rcases hsm : s.m with a | b
  · -- Dense: the pre-T45a per-entry walk, inline in the match arm.
    have hWm' := hWm
    rw [hsm] at hWm'
    step with ZeroCheck.rlin_cols_spec (n := n) (μ := μ) (ringswitch.RlinMat.Dense a) hWm'
      (by omega) as ⟨cols, hcols⟩
    step with c_row_sum_high_zero_loop_spec params.RING_DEGREE params_RING_DEGREE_val
      (alloc.vec.Vec.new cpoly.field.Fp) 0#usize (by simp) (by simp) as ⟨acc, hacc⟩
    obtain ⟨hWacc, hacc0⟩ := high_zeros_facts hacc
    apply spec_mono (c_row_sum_high_col_loop_spec (nr := n) (μ := μ) s z i
      params.RING_DEGREE cols hWm hi params_RING_DEGREE_val hcols hz acc 0#usize hWacc.1
      hWacc.2 (by simp)
      (by
        intro t ht
        rw [hacc0 t ht, show ((0#usize : Std.Usize).val) = 0 from rfl, Finset.range_zero,
          Finset.sum_empty, CPolynomial.coeff_zero]))
    rintro out ⟨hW, hv⟩
    refine ⟨hW, fun t ht => ?_⟩
    rw [hv t ht, cpoly_coeff_sum, hsm]
    rfl
  · -- Lazy: band by band, with the gadget groups contracted.
    rw [hsm] at hWm
    exact c_row_sum_high_lazy_spec (n := n) (μ := μ) b hWm z hz i hi

/-- **`c_row_sum_high` is `cRowSum`'s high half**: `N − 1` words, `out[s]` the
coefficient `N + s`. -/
theorem c_row_sum_high_spec {n μ : ℕ} (s : ringswitch.RlinStatement) (z : linalg.PolyVec)
    (i : Std.Usize) (rs : InnerOuter.RlinStatement Φ n μ)
    (hs : RepRlin (n := n) (μ := μ) s rs) (hz : WfVec μ z) (hi : i.val < n) :
    ringswitch.c_row_sum_high s z i
      ⦃ out => WfWords (N - 1) out ∧
        ∀ t, t < N - 1 → coeffK out t
          = (InnerOuter.cRowSum Φ rs (toVec (k := μ) z) ⟨i.val, hi⟩).coeff (N + t) ⦄ := by
  obtain ⟨hWm, -, hmeq, -, -⟩ := hs
  apply spec_mono (c_row_sum_high_rlin_spec (n := n) (μ := μ) s z i hWm hz hi)
  rintro out ⟨hW, hv⟩
  refine ⟨hW, fun t ht => ?_⟩
  rw [hv t ht, InnerOuter.cRowSum, cpoly_coeff_sum,
    ← Fin.sum_univ_eq_sum_range
      (fun j => ((rlinAt s.m i.val j).1 * (vecAt z j).1).coeff (N + t)) μ]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hentry : rs.M ⟨i.val, hi⟩ j = rlinAt s.m i.val j.val := by rw [← hmeq]; rfl
  rw [hentry]
  rfl

/-! ### `div_by_modulus` -/

/-- The copy loop of `div_by_modulus`. -/
theorem div_by_modulus_copy_loop_spec (p rem : alloc.vec.Vec cpoly.field.Fp) (t : Std.Usize)
    (ht : t.val ≤ p.val.length) (hrem : rem.val = p.val.take t.val) :
    ringswitch.div_by_modulus_loop0 p rem t ⦃ z => z.val = p.val ⦄ := by
  have hmax : p.val.length ≤ Usize.max := p.property
  rw [ringswitch.div_by_modulus_loop0]
  apply loop.spec_decr_nat (fun s => p.val.length - s.2.val)
    (fun s => s.2.val ≤ p.val.length ∧ s.1.val = p.val.take s.2.val)
  · rintro ⟨r1, t1⟩ ⟨ht1, hr1⟩
    dsimp only at ht1 hr1
    simp only [ringswitch.div_by_modulus_loop0.body]
    have hlen : r1.val.length = t1.val := by
      rw [hr1, List.length_take]; omega
    by_cases hlt : t1 < alloc.vec.Vec.len p
    · rw [if_pos hlt]
      have hb : t1.val < p.val.length := by scalar_tac
      step as ⟨f, hf⟩
      step as ⟨r2, hr2⟩
      step as ⟨t2, ht2⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hr2, ht2, hr1, hf, List.take_add_one, List.getElem?_eq_getElem hb]
      simp
    · rw [if_neg hlt, WP.spec_ok]
      show r1.val = p.val
      have heq : t1.val = p.val.length := by scalar_tac
      rw [hr1, heq, List.take_length]
  · exact ⟨ht, hrem⟩

/-- The zeroing loop of `div_by_modulus`: `n` copies of `Fp::ZERO`. -/
theorem div_by_modulus_zero_loop_spec (n : Std.Usize) (quot : alloc.vec.Vec cpoly.field.Fp)
    (u : Std.Usize) (hu : u.val ≤ n.val)
    (hquot : quot.val = List.replicate u.val cpoly.field.Fp.ZERO) :
    ringswitch.div_by_modulus_loop1 n quot u
      ⦃ z => z.val = List.replicate n.val cpoly.field.Fp.ZERO ⦄ := by
  rw [ringswitch.div_by_modulus_loop1]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val = List.replicate s.2.val cpoly.field.Fp.ZERO)
  · rintro ⟨o1, i1⟩ ⟨hi1, ho1⟩
    dsimp only at hi1 ho1
    simp only [ringswitch.div_by_modulus_loop1.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hlen : o1.val.length = i1.val := by rw [ho1, List.length_replicate]
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [ho2, hi2, ho1, List.replicate_succ']
    · rw [if_neg hlt, WP.spec_ok]
      show o1.val = List.replicate n.val cpoly.field.Fp.ZERO
      have heq : i1.val = n.val := by scalar_tac
      rw [ho1, heq]
  · exact ⟨hu, hquot⟩

/-- The division loop of `div_by_modulus`, counting `k` down from `N − 1`: the
quotient words at and above `k` are already the high words of `p`. -/
theorem div_by_modulus_main_loop_spec (p : alloc.vec.Vec cpoly.field.Fp)
    (n : Std.Usize) (hn : n.val = N)
    (rem quot : alloc.vec.Vec cpoly.field.Fp) (k : Std.Usize)
    (hrl : rem.val.length = 2 * N - 1) (hrr : ∀ x ∈ rem.val, Red x)
    (hql : quot.val.length = N) (hqr : ∀ x ∈ quot.val, Red x)
    (hk : k.val ≤ N - 1)
    (hrem : ∀ u, u < k.val → coeffK rem (u + N) = coeffK p (u + N))
    (hquot : ∀ u, coeffK quot u = if k.val ≤ u ∧ u < N - 1 then coeffK p (u + N) else 0) :
    ringswitch.div_by_modulus_loop2 n rem quot k
      ⦃ z => z.val.length = N ∧ (∀ x ∈ z.val, Red x) ∧
        ∀ u, coeffK z u = if u < N - 1 then coeffK p (u + N) else 0 ⦄ := by
  rw [ringswitch.div_by_modulus_loop2]
  apply loop.spec_decr_nat (fun st => st.2.2.val)
    (fun st => st.2.2.val ≤ N - 1 ∧ st.1.val.length = 2 * N - 1 ∧ (∀ x ∈ st.1.val, Red x) ∧
      st.2.1.val.length = N ∧ (∀ x ∈ st.2.1.val, Red x) ∧
      (∀ u, u < st.2.2.val → coeffK st.1 (u + N) = coeffK p (u + N)) ∧
      (∀ u, coeffK st.2.1 u = if st.2.2.val ≤ u ∧ u < N - 1 then coeffK p (u + N) else 0))
  · rintro ⟨r1, q1, k1⟩ ⟨hk1, hrl1, hrr1, hql1, hqr1, hrem1, hquot1⟩
    dsimp only at hk1 hrl1 hrr1 hql1 hqr1 hrem1 hquot1
    simp only [ringswitch.div_by_modulus_loop2.body]
    by_cases hlt : k1 > 0#usize
    · rw [if_pos hlt]
      have hk1pos : 0 < k1.val := by scalar_tac
      step as ⟨k2, hk2⟩
      have hk2N : k2.val < N - 1 := by omega
      step as ⟨lead, hlead⟩
      have hleadb : lead.val < r1.val.length := by rw [hrl1]; omega
      step as ⟨c, hc⟩
      have hRc : Red c := by rw [hc]; exact hrr1 _ (List.getElem_mem hleadb)
      have hk2q : k2.val < q1.val.length := by rw [hql1]; omega
      step as ⟨xq, backq, hxq, hbackq⟩
      have hk2r : k2.val < r1.val.length := by rw [hrl1]; omega
      step as ⟨f, hf⟩
      have hRf : Red f := by rw [hf]; exact hrr1 _ (List.getElem_mem hk2r)
      step with HachiEquiv.Field.fp_sub_spec f c hRf hRc as ⟨f1, hRf1, hf1⟩
      step as ⟨xr, backr, hxr, hbackr⟩
      have hrem1w : (backr f1).val = r1.val.set k2.val f1 := by rw [hbackr]; simp
      have hrem1l : (backr f1).val.length = 2 * N - 1 := by
        rw [hrem1w, List.length_set, hrl1]
      have hleadb' : lead.val < (backr f1).val.length := by rw [hrem1l]; omega
      step as ⟨xr2, backr2, hxr2, hbackr2⟩
      have hrem2w : (backr2 cpoly.field.Fp.ZERO).val
          = (backr f1).val.set lead.val cpoly.field.Fp.ZERO := by rw [hbackr2]; simp
      have hquot1w : (backq c).val = q1.val.set k2.val c := by rw [hbackq]; simp
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
      · rw [hrem2w, List.length_set, hrem1l]
      · exact Red_set hrem2w (Red_set hrem1w hrr1 hRf1) Red_zero
      · rw [hquot1w, List.length_set, hql1]
      · exact Red_set hquot1w hqr1 hRc
      · intro u hu
        rw [coeffK_set_ne hrem2w (by omega), coeffK_set_ne hrem1w (by omega)]
        exact hrem1 u (by omega)
      · intro u
        by_cases hu : u = k2.val
        · subst hu
          rw [coeffK_set_eq hquot1w hk2q, if_pos ⟨le_refl _, hk2N⟩, hc, ← coeffK_of_lt hleadb,
            show lead.val = k2.val + N by omega]
          exact hrem1 k2.val (by omega)
        · rw [coeffK_set_ne hquot1w hu, hquot1 u]
          by_cases hc2 : k2.val ≤ u ∧ u < N - 1
          · rw [if_pos hc2, if_pos ⟨by omega, hc2.2⟩]
          · rw [if_neg hc2, if_neg (by rintro ⟨h1, h2⟩; exact hc2 ⟨by omega, h2⟩)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hk10 : k1.val = 0 := by scalar_tac
      refine ⟨hql1, hqr1, ?_⟩
      intro u
      rw [hquot1 u, hk10]
      by_cases hu : u < N - 1
      · rw [if_pos ⟨Nat.zero_le _, hu⟩, if_pos hu]
      · rw [if_neg (by rintro ⟨-, h⟩; exact hu h), if_neg hu]
  · exact ⟨hk, hrl, hrr, hql, hqr, hrem, hquot⟩

/-- Uniqueness of the quotient by the monic `X^d + 1`, stated at an abstract
degree. The modulus is kept as `X ^ d + 1` rather than as `Φ.φ.toPoly`
throughout: at `d = N` the latter is a concrete array of `N + 1` coefficients,
and instantiating a general lemma at it makes the kernel unfold it. -/
theorem divByMonic_X_pow_add_one_eq {d : ℕ} (hd : 0 < d) (P Q : Polynomial (ZMod q))
    (hdeg : (P - ((Polynomial.X : Polynomial (ZMod q)) ^ d + 1) * Q).degree
      < ((Polynomial.X : Polynomial (ZMod q)) ^ d + 1).degree) :
    P /ₘ ((Polynomial.X : Polynomial (ZMod q)) ^ d + 1) = Q := by
  have hg : ((Polynomial.X : Polynomial (ZMod q)) ^ d + 1).Monic := by
    rw [← Polynomial.C_1]
    exact Polynomial.monic_X_pow_add_C 1 hd.ne'
  exact (Polynomial.div_modByMonic_unique _ _ hg ⟨sub_add_cancel _ _, hdeg⟩).1

/-- The word-level shape of the quotient *is* `divByMonic` at the modulus: the
high block of `p`, which is the unique quotient because what is left is the low
block minus it, of degree below `N`. -/
theorem toCPolyK_eq_divByMonic (p out : alloc.vec.Vec cpoly.field.Fp)
    (hp : p.val.length = 2 * N - 1)
    (h : ∀ u, coeffK out u = if u < N - 1 then coeffK p (u + N) else 0) :
    toCPolyK out = (toCPolyK p).divByMonic Φ.φ := by
  apply CPolynomial.toPolyLinearEquiv.injective
  rw [CPolynomial.toPolyLinearEquiv_apply, CPolynomial.toPolyLinearEquiv_apply,
    CPolynomial.divByMonic_toPoly_eq_divByMonic _ _ (InnerOuter.cModulus_monic Φ), phi_toPoly]
  have hgdeg : ((Polynomial.X : Polynomial (ZMod q)) ^ N + 1).degree = (N : WithBot ℕ) := by
    rw [← Polynomial.C_1]
    exact Polynomial.degree_X_pow_add_C (by norm_num) 1
  have hPc : ∀ m, (toCPolyK p).toPoly.coeff m = coeffK p m := by
    intro m
    rw [← CPolynomial.coeff_toPoly, toCPolyK_coeff_eq_coeffK]
  have hQc : ∀ m, (toCPolyK out).toPoly.coeff m
      = if m < N - 1 then coeffK p (m + N) else 0 := by
    intro m
    rw [← CPolynomial.coeff_toPoly, toCPolyK_coeff_eq_coeffK, h]
  have hgQ : ∀ m : ℕ, N ≤ m →
      (((Polynomial.X : Polynomial (ZMod q)) ^ N + 1) * (toCPolyK out).toPoly).coeff m
        = coeffK p m := by
    intro m hm
    have hexp : ((Polynomial.X : Polynomial (ZMod q)) ^ N + 1) * (toCPolyK out).toPoly
        = (toCPolyK out).toPoly * Polynomial.X ^ N + (toCPolyK out).toPoly := by
      rw [add_mul, one_mul, mul_comm ((Polynomial.X : Polynomial (ZMod q)) ^ N)]
    rw [hexp, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow', if_pos hm, hQc, hQc]
    by_cases h1 : m - N < N - 1
    · rw [if_pos h1, if_neg (by omega : ¬ m < N - 1), show m - N + N = m by omega, add_zero]
    · rw [if_neg h1, if_neg (by omega : ¬ m < N - 1),
        coeffK_of_ge (v := p) (by rw [hp]; omega), add_zero]
  refine (divByMonic_X_pow_add_one_eq (d := N) (by norm_num) _ _ ?_).symm
  rw [hgdeg, Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  have hmN : N ≤ m := by exact_mod_cast hm
  rw [Polynomial.coeff_sub, hPc, hgQ m hmN, sub_self]

/-- `div_by_modulus` is `CPolynomial.divByMonic` at the modulus, on a word
vector of exactly `2N − 1` coefficients. Exactly `N` words come back, and the
quotient's degree is below `N − 1` (its top word is zero), which is what lets
`QuotientRow::new` hold it. -/
theorem div_by_modulus_spec (p : alloc.vec.Vec cpoly.field.Fp) (hp : WfWords (2 * N - 1) p) :
    ringswitch.div_by_modulus p
      ⦃ out => WfWords N out ∧ toCPolyK out = (toCPolyK p).divByMonic Φ.φ ⦄ := by
  rw [ringswitch.div_by_modulus]
  step with div_by_modulus_copy_loop_spec p (alloc.vec.Vec.new cpoly.field.Fp) 0#usize
    (by simp) (by simp) as ⟨rem, hrem⟩
  step with div_by_modulus_zero_loop_spec params.RING_DEGREE
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize (by simp) (by simp) as ⟨quot, hquot⟩
  have hql : quot.val.length = N := by
    rw [hquot, List.length_replicate, params_RING_DEGREE_val]
  have hqr : ∀ x ∈ quot.val, Red x := by
    intro x hx
    rw [hquot] at hx
    rw [List.eq_of_mem_replicate hx]
    exact Red_zero
  have hq0 : ∀ u, coeffK quot u = 0 := by
    intro u
    unfold coeffK
    rw [hquot]
    by_cases hu : u < (List.replicate ((params.RING_DEGREE).val) cpoly.field.Fp.ZERO).length
    · rw [List.getD_eq_getElem _ _ hu, List.getElem_replicate, toK_zero]
    · rw [List.getD_eq_default _ _ (by omega), toK_zero]
  step as ⟨k, hk⟩
  apply spec_mono (div_by_modulus_main_loop_spec p params.RING_DEGREE (by simp) rem quot k
    (by rw [hrem, hp.1]) (by intro x hx; rw [hrem] at hx; exact hp.2 x hx) hql hqr
    (by scalar_tac)
    (by intro u _; unfold coeffK; rw [hrem])
    (by intro u; rw [hq0 u]; exact (if_neg (by scalar_tac)).symm))
  rintro z ⟨hzl, hzr, hzc⟩
  exact ⟨⟨hzl, hzr⟩, toCPolyK_eq_divByMonic p z hp.1 hzc⟩

/-! ## The three ArkLib definitions -/

/-- The zeroing loop of `c_row_sum`. -/
theorem c_row_sum_zero_loop_spec (width : Std.Usize) (acc : alloc.vec.Vec cpoly.field.Fp)
    (k : Std.Usize) (hk : k.val ≤ width.val)
    (hacc : acc.val = List.replicate k.val cpoly.field.Fp.ZERO) :
    ringswitch.c_row_sum_loop0 width acc k
      ⦃ z => z.val = List.replicate width.val cpoly.field.Fp.ZERO ⦄ := by
  rw [ringswitch.c_row_sum_loop0]
  apply loop.spec_decr_nat (fun s => width.val - s.2.val)
    (fun s => s.2.val ≤ width.val ∧ s.1.val = List.replicate s.2.val cpoly.field.Fp.ZERO)
  · rintro ⟨o1, i1⟩ ⟨hi1, ho1⟩
    dsimp only at hi1 ho1
    simp only [ringswitch.c_row_sum_loop0.body]
    by_cases hlt : i1 < width
    · rw [if_pos hlt]
      have hlen : o1.val.length = i1.val := by rw [ho1, List.length_replicate]
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [ho2, hi2, ho1, List.replicate_succ']
    · rw [if_neg hlt, WP.spec_ok]
      show o1.val = List.replicate width.val cpoly.field.Fp.ZERO
      have heq : i1.val = width.val := by scalar_tac
      rw [ho1, heq]
  · exact ⟨hk, hacc⟩

/-- The accumulation loop of `c_row_sum`: one product added into the row sum. -/
theorem c_row_sum_add_loop_spec (width : Std.Usize) (hw : width.val = 2 * N - 1)
    (acc prod : alloc.vec.Vec cpoly.field.Fp) (t : Std.Usize) (g : ℕ → ZMod q)
    (hal : acc.val.length = 2 * N - 1) (har : ∀ x ∈ acc.val, Red x)
    (hpl : prod.val.length = 2 * N - 1) (hpr : ∀ x ∈ prod.val, Red x)
    (ht : t.val ≤ 2 * N - 1)
    (hbase : ∀ s, coeffK acc s = g s + (if s < t.val then coeffK prod s else 0)) :
    ringswitch.c_row_sum_loop1_loop0 width acc prod t
      ⦃ z => z.val.length = 2 * N - 1 ∧ (∀ x ∈ z.val, Red x) ∧
        ∀ s, coeffK z s = g s + coeffK prod s ⦄ := by
  rw [ringswitch.c_row_sum_loop1_loop0]
  apply loop.spec_decr_nat (fun st => 2 * N - 1 - st.2.val)
    (fun st => st.2.val ≤ 2 * N - 1 ∧ st.1.val.length = 2 * N - 1 ∧ (∀ x ∈ st.1.val, Red x) ∧
      ∀ s, coeffK st.1 s = g s + (if s < st.2.val then coeffK prod s else 0))
  · rintro ⟨a1, t1⟩ ⟨ht1, hl1, hr1, hc1⟩
    dsimp only at ht1 hl1 hr1 hc1
    simp only [ringswitch.c_row_sum_loop1_loop0.body]
    by_cases hlt : t1 < width
    · rw [if_pos hlt]
      have ht1b : t1.val < 2 * N - 1 := by rw [← hw]; scalar_tac
      have hta : t1.val < a1.val.length := by rw [hl1]; omega
      have htp : t1.val < prod.val.length := by rw [hpl]; omega
      step as ⟨fa, hfa⟩
      have hRfa : Red fa := by rw [hfa]; exact hr1 _ (List.getElem_mem hta)
      step as ⟨fp, hfp⟩
      have hRfp : Red fp := by rw [hfp]; exact hpr _ (List.getElem_mem htp)
      step with HachiEquiv.Field.fp_add_spec fa fp hRfa hRfp as ⟨f2, hRf2, hf2⟩
      step as ⟨xa, backa, hxa, hbacka⟩
      step as ⟨t2, ht2⟩
      have hwset : (backa f2).val = a1.val.set t1.val f2 := by rw [hbacka]; simp
      refine ⟨by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
      · rw [hwset, List.length_set, hl1]
      · exact Red_set hwset hr1 hRf2
      · intro s
        by_cases hs : s = t1.val
        · subst hs
          rw [coeffK_set_eq hwset hta, hf2, hfa, hfp, ← coeffK_of_lt hta,
            ← coeffK_of_lt htp, hc1 t1.val, ht2, if_neg (by omega), if_pos (by omega),
            add_zero]
        · rw [coeffK_set_ne hwset hs, hc1 s, ht2]
          congr 1
          by_cases hsl : s < t1.val
          · rw [if_pos hsl, if_pos (by omega)]
          · rw [if_neg hsl, if_neg (by omega)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : t1.val = 2 * N - 1 := by rw [← hw]; scalar_tac
      refine ⟨hl1, hr1, ?_⟩
      intro s
      rw [hc1 s, heq]
      by_cases hs : s < 2 * N - 1
      · rw [if_pos hs]
      · rw [if_neg hs, coeffK_of_ge (v := prod) (by rw [hpl]; omega)]
  · exact ⟨ht, hal, har, hbase⟩

/-- The column loop of `c_row_sum`: the partial row sum over the first `j`
columns.  As in the high half, card W2 turned the fetched row into a per-column
`RlinMat::entry` call; the summand is `rlinAt s.m i j`. -/
theorem c_row_sum_col_loop_spec {nr μ : ℕ} (s : ringswitch.RlinStatement)
    (z : linalg.PolyVec) (i width cols : Std.Usize)
    (hWm : WfRlinMat nr μ s.m) (hi : i.val < nr)
    (hw : width.val = 2 * N - 1) (hcols : cols.val = μ)
    (hz : WfVec μ z) (acc : alloc.vec.Vec cpoly.field.Fp)
    (j : Std.Usize) (hal : acc.val.length = 2 * N - 1) (har : ∀ x ∈ acc.val, Red x)
    (hj : j.val ≤ μ)
    (hbase : ∀ w, coeffK acc w
      = (∑ t ∈ Finset.range j.val, (rlinAt s.m i.val t).1
            * (toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))).1).coeff w) :
    ringswitch.c_row_sum_loop1 s z i width cols acc j
      ⦃ out => WfWords (2 * N - 1) out ∧
        toCPolyK out = ∑ t ∈ Finset.range μ, (rlinAt s.m i.val t).1
            * (toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))).1 ⦄ := by
  rw [ringswitch.c_row_sum_loop1]
  apply loop.spec_decr_nat (fun st => μ - st.2.val)
    (fun st => st.2.val ≤ μ ∧ st.1.val.length = 2 * N - 1 ∧ (∀ x ∈ st.1.val, Red x) ∧
      ∀ w, coeffK st.1 w
        = (∑ t ∈ Finset.range st.2.val, (rlinAt s.m i.val t).1
              * (toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))).1).coeff w)
  · rintro ⟨a1, j1⟩ ⟨hj1, hl1, hr1, hc1⟩
    dsimp only at hj1 hl1 hr1 hc1
    simp only [ringswitch.c_row_sum_loop1.body]
    by_cases hlt : j1 < cols
    · rw [if_pos hlt]
      have hjm : j1.val < μ := by rw [← hcols]; scalar_tac
      have hjz : j1.val < z.val.length := by rw [hz.1]; exact hjm
      simp only [ringswitch.RlinStatement.impl.m, bind_tc_ok]
      step with ZeroCheck.rlin_entry_spec (n := nr) (μ := μ) s.m hWm i j1 hi hjm
        as ⟨r, hWr, hrv⟩
      have hrv' : toRq r = rlinAt s.m i.val j1.val := hrv
      -- Candidate T1a1: the column is skipped when `M_ij = 0`. `rlin_stmt`
      -- builds `M` block structured, so at the pin rows c1-c3 are 86% literal
      -- `Rq::zero()`, and each of those entries would otherwise buy a full
      -- `long_mul` and a `2N − 1`-wide accumulation in order to add nothing.
      -- After card W2 those entries are not even stored: `entry` returns the
      -- blocks' shared `zero` and this branch is the one that runs.
      step with RqBridge.is_zero_spec r hWr as ⟨bz, hbz⟩
      by_cases hzero : bz = true
      · -- Skipped. The term is `0 · z_j = 0`, so the partial sum is unchanged
        -- and the invariant advances by `Finset.sum_range_succ` alone. This is
        -- the whole proof obligation the candidate adds.
        rw [if_pos hzero]
        step as ⟨j2, hj2⟩
        refine ⟨by scalar_tac, hl1, hr1, ?_, by scalar_tac⟩
        intro w
        have hz0 : rlinAt s.m i.val j1.val = 0 := by rw [← hrv']; exact hbz.1 hzero
        rw [hc1 w, hj2, Finset.sum_range_succ, hz0]
        simp
      rw [if_neg hzero]
      simp only [linalg.PolyVec.get]
      step as ⟨r1, hr1'⟩
      have hWr1 : Wf r1 := by rw [hr1']; exact hz.2 _ (List.getElem_mem hjz)
      step with long_mul_spec r r1 hWr hWr1 as ⟨prod, hWprod, hprod⟩
      step with c_row_sum_add_loop_spec width hw a1 prod 0#usize
        (fun w => (∑ t ∈ Finset.range j1.val, (rlinAt s.m i.val t).1
          * (toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))).1).coeff w)
        hl1 hr1 hWprod.1 hWprod.2 (by simp) (by intro w; rw [hc1 w]; simp)
        as ⟨a2, hl2, hr2, hc2⟩
      step as ⟨j2, hj2⟩
      refine ⟨by scalar_tac, hl2, hr2, ?_, by scalar_tac⟩
      intro w
      rw [hc2 w, hj2, Finset.sum_range_succ, cpoly_coeff_add,
        ← toCPolyK_coeff_eq_coeffK, hprod, hrv', hr1',
        List.getD_eq_getElem _ _ hjz]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : j1.val = μ := by rw [← hcols]; scalar_tac
      refine ⟨⟨hl1, hr1⟩, ?_⟩
      refine toCPolyK_eq_of_coeffK fun k => ?_
      rw [hc1 k, heq]
  · exact ⟨hj, hal, har, hbase⟩

/-- `c_row_sum` computes `cRowSum` (`RingSwitch/Reduction.lean:439`): the
`i`-th lifted row, unreduced. -/
theorem c_row_sum_spec {n μ : ℕ} (s : ringswitch.RlinStatement) (z : linalg.PolyVec)
    (i : Std.Usize) (rs : InnerOuter.RlinStatement Φ n μ)
    (hs : RepRlin (n := n) (μ := μ) s rs) (hz : WfVec μ z) (hi : i.val < n) :
    ringswitch.c_row_sum s z i
      ⦃ out => WfWords (2 * N - 1) out ∧
        toCPolyK out = InnerOuter.cRowSum Φ rs (toVec (k := μ) z) ⟨i.val, hi⟩ ⦄ := by
  obtain ⟨hWm, hWy, hmeq, hyeq, hbeq⟩ := hs
  rw [ringswitch.c_row_sum]
  step as ⟨i1, hi1⟩
  step as ⟨width, hwidth⟩
  have hwv : width.val = 2 * N - 1 := by scalar_tac
  simp only [ringswitch.RlinStatement.impl.m, bind_tc_ok]
  step with ZeroCheck.rlin_cols_spec (n := n) (μ := μ) s.m hWm (by omega) as ⟨cols, hcols⟩
  step with c_row_sum_zero_loop_spec width (alloc.vec.Vec.new cpoly.field.Fp) 0#usize
    (by simp) (by simp) as ⟨acc0, hacc0⟩
  have hl0 : acc0.val.length = 2 * N - 1 := by rw [hacc0, List.length_replicate, hwv]
  have hr0 : ∀ x ∈ acc0.val, Red x := by
    intro x hx
    rw [hacc0] at hx
    rw [List.eq_of_mem_replicate hx]
    exact Red_zero
  have hc0 : ∀ w, coeffK acc0 w
      = (∑ t ∈ Finset.range (0#usize : Std.Usize).val, (rlinAt s.m i.val t).1
            * (toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))).1).coeff w := by
    intro w
    have hzero : coeffK acc0 w = 0 := by
      unfold coeffK
      rw [hacc0]
      by_cases hs : w < (List.replicate width.val cpoly.field.Fp.ZERO).length
      · rw [List.getD_eq_getElem _ _ hs, List.getElem_replicate, toK_zero]
      · rw [List.getD_eq_default _ _ (by omega), toK_zero]
    rw [hzero, show ((0#usize : Std.Usize).val) = 0 from rfl, Finset.range_zero,
      Finset.sum_empty, CPolynomial.coeff_zero]
  apply spec_mono (c_row_sum_col_loop_spec (nr := n) (μ := μ) s z i width cols hWm hi
    hwv hcols hz acc0 0#usize hl0 hr0 (by simp) hc0)
  rintro out ⟨hW, hsum⟩
  refine ⟨hW, ?_⟩
  rw [hsum, InnerOuter.cRowSum,
    ← Fin.sum_univ_eq_sum_range (fun t => (rlinAt s.m i.val t).1
        * (toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))).1) μ]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hentry : rs.M ⟨i.val, hi⟩ j = rlinAt s.m i.val j.val := by rw [← hmeq]; rfl
  rw [hentry]
  rfl

/-! ### `c_quotient`, from the high half -/

/-- The product of two reduced representatives vanishes past degree `2N − 2`:
each factor is zero at and beyond `N`, so every term of the antidiagonal at
`m ≥ 2N − 1` has a zero factor. -/
theorem mul_coeff_of_high (a b : Rq Φ) {m : ℕ} (hm : 2 * N - 1 ≤ m) :
    (a.1 * b.1).coeff m = 0 := by
  rw [CPolynomial.coeff_toPoly, CPolynomial.toPoly_mul, Polynomial.coeff_mul]
  refine Finset.sum_eq_zero (fun x hx => ?_)
  have hxsum : x.1 + x.2 = m := by
    simpa using Finset.mem_antidiagonal.mp hx
  simp only [← CPolynomial.coeff_toPoly]
  rcases Nat.lt_or_ge x.1 N with h1 | h1
  · rw [Rq.coeff_eq_zero_of_natDegree_le Φ b
      (by rw [RqBridge.phi_natDegree]; omega), mul_zero]
  · rw [Rq.coeff_eq_zero_of_natDegree_le Φ a
      (by rw [RqBridge.phi_natDegree]; omega), zero_mul]

/-- `cRowSum` vanishes past degree `2N − 2`: it is a sum of such products. -/
theorem cRowSum_coeff_of_high {n μ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ)
    (zv : ArkLib.Lattices.PolyVec (Rq Φ) μ) (i : Fin n) {m : ℕ} (hm : 2 * N - 1 ≤ m) :
    (InnerOuter.cRowSum Φ rs zv i).coeff m = 0 := by
  rw [InnerOuter.cRowSum, cpoly_coeff_sum]
  exact Finset.sum_eq_zero (fun j _ => mul_coeff_of_high _ _ hm)

/-- **The quotient is the high half**, at the polynomial level:
[`toCPolyK_eq_divByMonic`]'s argument with the dividend an arbitrary
`CPolynomial` rather than a word vector. -/
theorem divByMonic_of_high (P Q : CPolynomial (ZMod q))
    (hP : ∀ m, 2 * N - 1 ≤ m → P.coeff m = 0)
    (hQ : ∀ m, Q.coeff m = if m < N - 1 then P.coeff (N + m) else 0) :
    Q = P.divByMonic Φ.φ := by
  apply CPolynomial.toPolyLinearEquiv.injective
  rw [CPolynomial.toPolyLinearEquiv_apply, CPolynomial.toPolyLinearEquiv_apply,
    CPolynomial.divByMonic_toPoly_eq_divByMonic _ _ (InnerOuter.cModulus_monic Φ), phi_toPoly]
  have hgdeg : ((Polynomial.X : Polynomial (ZMod q)) ^ N + 1).degree = (N : WithBot ℕ) := by
    rw [← Polynomial.C_1]
    exact Polynomial.degree_X_pow_add_C (by norm_num) 1
  have hPc : ∀ m, P.toPoly.coeff m = P.coeff m := fun m => (CPolynomial.coeff_toPoly _ _).symm
  have hQc : ∀ m, Q.toPoly.coeff m = if m < N - 1 then P.coeff (N + m) else 0 := by
    intro m; rw [← CPolynomial.coeff_toPoly, hQ]
  have hgQ : ∀ m : ℕ, N ≤ m →
      (((Polynomial.X : Polynomial (ZMod q)) ^ N + 1) * Q.toPoly).coeff m = P.coeff m := by
    intro m hm
    have hexp : ((Polynomial.X : Polynomial (ZMod q)) ^ N + 1) * Q.toPoly
        = Q.toPoly * Polynomial.X ^ N + Q.toPoly := by
      rw [add_mul, one_mul, mul_comm ((Polynomial.X : Polynomial (ZMod q)) ^ N)]
    rw [hexp, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow', if_pos hm, hQc, hQc]
    by_cases h1 : m - N < N - 1
    · rw [if_pos h1, if_neg (by omega : ¬ m < N - 1), show N + (m - N) = m by omega, add_zero]
    · rw [if_neg h1, if_neg (by omega : ¬ m < N - 1), hP m (by omega), add_zero]
  refine (divByMonic_X_pow_add_one_eq (d := N) (by norm_num) _ _ ?_).symm
  rw [hgdeg, Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  have hmN : N ≤ m := by exact_mod_cast hm
  rw [Polynomial.coeff_sub, hPc, hgQ m hmN, sub_self]

/-- The copy loop of `c_quotient`: `N − 1` words out of the high half. -/
theorem c_quotient_copy_loop_spec (n : Std.Usize) (hn : n.val = N)
    (hiv quot : alloc.vec.Vec cpoly.field.Fp) (k : Std.Usize)
    (hhl : hiv.val.length = N - 1) (hhr : ∀ x ∈ hiv.val, Red x)
    (hk : k.val ≤ N - 1) (hql : quot.val.length = k.val) (hqr : ∀ x ∈ quot.val, Red x)
    (hqv : ∀ u, u < k.val → coeffK quot u = coeffK hiv u) :
    ringswitch.c_quotient_loop n hiv quot k
      ⦃ z => z.val.length = N - 1 ∧ (∀ x ∈ z.val, Red x) ∧
          ∀ u, u < N - 1 → coeffK z u = coeffK hiv u ⦄ := by
  rw [ringswitch.c_quotient_loop]
  apply loop.spec_decr_nat (fun st => N - 1 - st.2.val)
    (fun st => st.2.val ≤ N - 1 ∧ st.1.val.length = st.2.val ∧ (∀ x ∈ st.1.val, Red x) ∧
      ∀ u, u < st.2.val → coeffK st.1 u = coeffK hiv u)
  · rintro ⟨q1, k1⟩ ⟨hk1, hl1, hr1, hv1⟩
    dsimp only at hk1 hl1 hr1 hv1
    simp only [ringswitch.c_quotient_loop.body]
    step as ⟨nm1, hnm1⟩
    have hnm1v : nm1.val = N - 1 := by rw [hnm1, hn]
    by_cases hlt : k1 < nm1
    · rw [if_pos hlt]
      have hk1b : k1.val < N - 1 := by scalar_tac
      have hkh : k1.val < hiv.val.length := by rw [hhl]; exact hk1b
      have hmax : q1.val.length < Std.Usize.max := by rw [hl1]; scalar_tac
      step as ⟨f, hf⟩
      have hRf : Red f := by rw [hf]; exact hhr _ (List.getElem_mem hkh)
      step as ⟨q2, hq2⟩
      step as ⟨k2, hk2⟩
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · rw [hq2, hk2, List.length_append, hl1]; simp
      · intro x hx
        rw [hq2] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hr1 x h
        · rw [List.mem_singleton.mp h]; exact hRf
      · intro u hu
        rw [hk2] at hu
        rcases Nat.lt_or_ge u k1.val with hult | huge
        · rw [coeffK, hq2, getD_append_lt _ _ _ (by omega)]
          exact hv1 u hult
        · have hueq : u = q1.val.length := by omega
          rw [coeffK, hueq, hq2, getD_append_eq, hf, hl1, ← coeffK_of_lt hkh]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = N - 1 := by scalar_tac
      exact ⟨by rw [hl1, heq], hr1, fun u hu => hv1 u (by rw [heq]; exact hu)⟩
  · exact ⟨hk, hql, hqr, hqv⟩

/-- **`c_quotient` computes `cQuotient`**, from the high half alone
(Stage 6 candidate T1a).

The statement is the one the dividing version had, word for word. What changed
is that neither the `y` subtraction nor the division loop runs: `y` has degree
below `N` so it does not reach the high half, and the quotient's coefficient
`k` is the dividend's `N + k` ([`divByMonic_of_high`]). The low half of every
`long_mul` is therefore never computed. -/
theorem c_quotient_spec {n μ : ℕ} (s : ringswitch.RlinStatement) (z : linalg.PolyVec)
    (i : Std.Usize) (rs : InnerOuter.RlinStatement Φ n μ)
    (hs : RepRlin (n := n) (μ := μ) s rs) (hz : WfVec μ z) (hi : i.val < n) :
    ringswitch.c_quotient s z i
      ⦃ out => Wf out ∧ toQuotientRow out = InnerOuter.cQuotient Φ rs (toVec (k := μ) z) ⟨i.val, hi⟩ ⦄ := by
  rw [ringswitch.c_quotient]
  step with c_row_sum_high_spec s z i rs hs hz hi as ⟨hiv, hWhi, hhv⟩
  simp only [alloc.vec.Vec.with_capacity]
  step with c_quotient_copy_loop_spec params.RING_DEGREE params_RING_DEGREE_val hiv
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize hWhi.1 hWhi.2 (by simp) (by simp)
    (by intro x hx; simp at hx) (by intro u hu; simp at hu)
    as ⟨quot1, hq1l, hq1r, hq1v⟩
  have hmax : quot1.val.length < Std.Usize.max := by
    rw [hq1l]; have := usize_max_ge'; norm_num [N]; omega
  step as ⟨quot2, hq2⟩
  have hNpos : 1 ≤ N := by norm_num [N]
  have hq2l : quot2.val.length = N := by
    rw [hq2, List.length_append, hq1l]
    simp only [List.length_singleton]
    omega
  have hq2r : ∀ x ∈ quot2.val, Red x := by
    intro x hx
    rw [hq2] at hx
    rcases List.mem_append.mp hx with h | h
    · exact hq1r x h
    · rw [List.mem_singleton.mp h]; exact Red_zero
  have hq2v : ∀ u, coeffK quot2 u
      = if u < N - 1
        then (InnerOuter.cRowSum Φ rs (toVec (k := μ) z) ⟨i.val, hi⟩).coeff (N + u) else 0 := by
    intro u
    by_cases hu : u < N - 1
    · rw [if_pos hu, coeffK, hq2, getD_append_lt _ _ _ (by rw [hq1l]; exact hu),
        ← coeffK, hq1v u hu, hhv u hu]
    · rw [if_neg hu]
      rcases Nat.lt_or_ge u N with hlt | hge
      · have hueq : u = quot1.val.length := by rw [hq1l]; omega
        rw [coeffK, hueq, hq2, getD_append_eq]
        simp [toK, cpoly.field.Fp.ZERO]
      · rw [coeffK_of_ge (by rw [hq2l]; exact hge)]
  rw [ringswitch.QuotientRow.new]
  simp only [bind_ok_id]
  apply spec_mono (HachiEquiv.Ring.from_coeffs_spec quot2 hq2r)
  rintro out ⟨hWout, hcoef⟩
  refine ⟨hWout, ?_⟩
  have hoq : toCPolyK out = toCPolyK quot2 := by
    refine toCPolyK_eq_of_coeffK fun k => ?_
    rw [toCPolyK_coeff_eq_coeffK]
    by_cases hk : k < N
    · exact hcoef k hk
    · rw [coeffK_of_ge (v := out) (by rw [hWout.1]; omega),
        coeffK_of_ge (v := quot2) (by rw [hq2l]; omega)]
  rw [toQuotientRow_eq_toCPolyK hWout, hoq, InnerOuter.cQuotient]
  -- the `y` subtraction never reached the high half
  have hyhigh : ∀ m, 2 * N - 1 ≤ m →
      (InnerOuter.cRowSum Φ rs (toVec (k := μ) z) ⟨i.val, hi⟩ - (rs.yvec ⟨i.val, hi⟩).1).coeff m
        = 0 := by
    intro m hm
    have hy : ((rs.yvec ⟨i.val, hi⟩).1).coeff m = 0 :=
      Rq.coeff_eq_zero_of_natDegree_le Φ _ (by rw [RqBridge.phi_natDegree]; omega)
    rw [cpoly_coeff_sub, cRowSum_coeff_of_high rs _ _ hm, hy, sub_zero]
  refine divByMonic_of_high _ _ hyhigh (fun m => ?_)
  rw [toCPolyK_coeff_eq_coeffK, hq2v m]
  by_cases hm : m < N - 1
  · have hy : ((rs.yvec ⟨i.val, hi⟩).1).coeff (N + m) = 0 :=
      Rq.coeff_eq_zero_of_natDegree_le Φ _ (by rw [RqBridge.phi_natDegree]; omega)
    rw [if_pos hm, if_pos hm, cpoly_coeff_sub, hy, sub_zero]
  · rw [if_neg hm, if_neg hm]

theorem honest_lift_witness_loop_spec {n μ : ℕ}
    (s : ringswitch.RlinStatement) (z : linalg.PolyVec) (rows : Std.Usize)
    (rho : alloc.vec.Vec ringswitch.QuotientRow) (i : Std.Usize)
    (rs : InnerOuter.RlinStatement Φ n μ)
    (hs : RepRlin (n := n) (μ := μ) s rs) (hz : WfVec μ z)
    (hrows : rows.val = n) (hi : i.val ≤ n)
    (hlen : rho.val.length = i.val) (hwf : ∀ x ∈ rho.val, Wf x)
    (hval : ∀ (t : ℕ) (ht : t < i.val),
      toQuotientRow (rho.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) =
        InnerOuter.cQuotient Φ rs (toVec (k := μ) z) ⟨t, lt_of_lt_of_le ht hi⟩) :
    ringswitch.honest_lift_witness_loop s z rows rho i
      ⦃ out => WfRho n out ∧ toRho (n := n) out =
        (InnerOuter.honestLiftWitnessC Φ (by rw [phi_natDegree]; decide) rs
          (toVec (k := μ) z)).ρ ⦄ := by
  rw [ringswitch.honest_lift_witness_loop]
  apply loop.spec_decr_nat (fun st => n - st.2.val)
    (fun st => st.2.val ≤ n ∧ st.1.val.length = st.2.val ∧
      (∀ x ∈ st.1.val, Wf x) ∧
      ∀ (t : ℕ) (ht : t < st.2.val) (htn : t < n),
        toQuotientRow (st.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) =
          InnerOuter.cQuotient Φ rs (toVec (k := μ) z) ⟨t, htn⟩)
  · rintro ⟨rho1, i1⟩ hinv
    obtain ⟨hi1, hlen1, hwf1, hval1⟩ : i1.val ≤ n ∧ rho1.val.length = i1.val ∧
        (∀ x ∈ rho1.val, Wf x) ∧
        ∀ (t : ℕ) (ht : t < i1.val) (htn : t < n),
          toQuotientRow (rho1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) =
            InnerOuter.cQuotient Φ rs (toVec (k := μ) z) ⟨t, htn⟩ := hinv
    simp only [ringswitch.honest_lift_witness_loop.body]
    by_cases hlt : i1 < rows
    · rw [if_pos hlt]
      have hin : i1.val < n := by rw [← hrows]; scalar_tac
      step with c_quotient_spec s z i1 rs hs hz hin as ⟨qr, hWqr, hqr⟩
      have hcap : rho1.val.length < Usize.max := by
        rw [hlen1]
        have hnmax : n ≤ Usize.max := ZeroCheck.rlin_rows_le_max hs.1
        omega
      step as ⟨rho2, hrho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
      · rw [hrho2, hi2, List.length_append, hlen1]
        simp
      · intro x hx
        rw [hrho2] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hwf1 x hx
        · rw [List.mem_singleton.mp hx]
          exact hWqr
      · intro t ht htn
        rw [hrho2]
        by_cases hold : t < i1.val
        · rw [HachiEquiv.Scheme.getD_append_lt _ _ _ (by simpa [hlen1] using hold)]
          simpa only using hval1 t hold htn
        · have heq : t = i1.val := by omega
          subst t
          conv_lhs => rw [← hlen1]
          rw [HachiEquiv.Scheme.getD_append_eq]
          simpa only using hqr
    · rw [if_neg hlt]
      have hieq : i1.val = n := by rw [← hrows]; scalar_tac
      refine ⟨⟨by simp [hlen1, hieq], hwf1⟩, ?_⟩
      funext t
      rw [toRho]
      have ht : t.val < i1.val := by simp [hieq]
      rw [hval1 t.val ht t.isLt]
      rfl
  · refine ⟨hi, hlen, hwf, ?_⟩
    intro t ht htn
    simpa only using hval t ht

/-- The loop of `PolyVec::copy`. A local copy of `QuadEvalProtocol.lean`'s
lemma of the same shape: that file is not below this one in the import graph. -/
theorem poly_vec_copy_loop_spec {k : ℕ} (v : linalg.PolyVec) (n : Std.Usize)
    (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hv : WfVec k v) (hn : n.val = k) (hi : i.val ≤ n.val)
    (hlen : out.val.length = i.val) (hwf : ∀ y ∈ out.val, Wf y)
    (hval : ∀ j, j < i.val → toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
      = toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))) :
    linalg.PolyVec.copy_loop v n out i
      ⦃ z => z.val.length = k ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < k → toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [linalg.PolyVec.copy_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ j, j < s.2.val → toRq (s.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (v.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [linalg.PolyVec.copy_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hiv : i1.val < v.val.length := by rw [hv.1, ← hn]; scalar_tac
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hv.2 _ (List.getElem_mem hiv)
      step with RqBridge.copy_spec r hWr as ⟨r1, hWr1, hr1⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [ho2, HachiEquiv.Scheme.getD_append_lt _ _ _ (by omega), hval1 j hjlt]
        · have hjeq : j = o1.val.length := by omega
          rw [hjeq, ho2, HachiEquiv.Scheme.getD_append_eq, hr1, hr, hlen1,
            List.getD_eq_getElem _ _ hiv]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = k := by rw [← hn]; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, by intro j hj; exact hval1 j (by omega)⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- `PolyVec::copy` represents the same vector. -/
theorem poly_vec_copy_spec {k : ℕ} (v : linalg.PolyVec) (hv : WfVec k v) :
    linalg.PolyVec.copy v ⦃ z => WfVec k z ∧ toVec (k := k) z = toVec (k := k) v ⦄ := by
  rw [linalg.PolyVec.copy]
  simp only [bind_ok_id]
  apply spec_mono (poly_vec_copy_loop_spec v (alloc.vec.Vec.len v)
    (alloc.vec.Vec.new ring.Rq) 0#usize hv (by simp [hv.1]) (by simp) (by simp)
    (by intro y hy; simp at hy) (by intro j hj; simp at hj))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i
  simp only [toVec]
  exact hzval i.val i.isLt

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
  rw [ringswitch.honest_lift_witness]
  simp only [ringswitch.RlinStatement.impl.m, bind_tc_ok]
  step with ZeroCheck.rlin_rows_spec (n := n) (μ := μ) s.m hs.1 as ⟨rows, hrows⟩
  step with honest_lift_witness_loop_spec s z rows
    (alloc.vec.Vec.new ringswitch.QuotientRow) 0#usize rs hs hz hrows (by simp) (by simp)
    (by intro x hx; simp at hx) (by intro t ht; simp at ht) as ⟨rho, hWrho, hrho⟩
  step with poly_vec_copy_spec (k := μ) z hz as ⟨pv, hWpv, hpv⟩
  rw [ringswitch.LiftedWitness.new, WP.spec_ok]
  exact ⟨hWpv, hWrho, hpv, hrho⟩

end HachiEquiv.LiftProver
