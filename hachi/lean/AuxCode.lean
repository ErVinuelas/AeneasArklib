/-
The **extracted transform**: `hachi.ntt`'s generated loops shown to compute the
word-level stage functions, and those shown to be `AuxNTT`'s ring-level stages
under the obvious reading of a buffer as a function `ℕ → ZMod p`.

## The two-step shape, and why

A stage's specification could be stated directly in `ZMod p`, but then every
loop proof would carry a cast on every line. Instead:

* [`difWord`] is the stage at the level the Rust actually computes at -- `ℕ`
  with `% p` -- and [`dif_stage_spec`] says the generated code computes it. That
  half is pure loop bookkeeping: three nested loops, a canonicality invariant
  and a frame condition.
* [`difWord_cast`] says `difWord` *is* `AuxNTT.difStage` once the words are read
  as elements of `ZMod p`. That half is pure algebra and has no loops in it.

Composing the two is what the transform proof uses. Splitting them is what keeps
either one readable.

## Reading a buffer

[`wordAt`] is the `ℕ` a buffer holds at an index, `0` past the end -- the same
convention `Ring.lean`'s `coeffK` uses, and for the same reason: it lets the
statements quantify over all indices rather than only over the in-range ones.
[`Canon`] is the representation invariant: exactly `NTT_LEN` entries, every one
a canonical residue below `p`.
-/
import AuxArith
import AuxNTT
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.AuxCode

open HachiEquiv.AuxArith

/-- The transform length, `N = 1024`. -/
abbrev N : ℕ := 1024

@[simp, scalar_tac_simps]
theorem ntt_NTT_LEN_val : (ntt.NTT_LEN).val = N := by
  simp only [ntt.NTT_LEN]; decide

/-- The word a buffer holds at an index; `0` past the end. -/
def wordAt (v : alloc.vec.Vec Std.U64) (t : ℕ) : ℕ := (v.val.getD t 0#u64).val

/-- Representation invariant: `NTT_LEN` entries, all canonical residues mod `p`. -/
def Canon (p : ℕ) (v : alloc.vec.Vec Std.U64) : Prop :=
  v.val.length = N ∧ ∀ u ∈ v.val, u.val < p

theorem wordAt_of_lt {v : alloc.vec.Vec Std.U64} {t : ℕ} (ht : t < v.val.length) :
    wordAt v t = (v.val[t]).val := by
  unfold wordAt; rw [List.getD_eq_getElem _ _ ht]

theorem wordAt_lt {p : ℕ} {v : alloc.vec.Vec Std.U64} (hv : Canon p v) (hp : 0 < p) (t : ℕ) :
    wordAt v t < p := by
  unfold wordAt
  by_cases ht : t < v.val.length
  · rw [List.getD_eq_getElem _ _ ht]; exact hv.2 _ (List.getElem_mem ht)
  · rw [List.getD_eq_default _ _ (by omega)]; simpa using hp

/-! ### Reading a `Vec.set`

The two lemmas every in-place write loop needs, in the `wordAt` form. `EvalSplit`
has the same pair for its own carrier; they cannot be shared because that file is
downstream of this one. -/

theorem wordAt_set_eq {v : alloc.vec.Vec Std.U64} {t : Std.Usize} {x : Std.U64}
    (ht : t.val < v.val.length) : wordAt (v.set t x) t.val = x.val := by
  unfold wordAt
  rw [alloc.vec.Vec.set_val_eq,
    List.getD_eq_getElem _ _ (by rw [List.length_set]; exact ht), List.getElem_set]
  simp

theorem wordAt_set_ne {v : alloc.vec.Vec Std.U64} {t : Std.Usize} {x : Std.U64} {k : ℕ}
    (h : k ≠ t.val) : wordAt (v.set t x) k = wordAt v k := by
  unfold wordAt
  rw [alloc.vec.Vec.set_val_eq]
  by_cases hk : k < v.val.length
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_set]; exact hk),
      List.getD_eq_getElem _ _ hk, List.getElem_set_ne (fun hh => h hh.symm)]
  · rw [List.getD_eq_default _ _ (by rw [List.length_set]; omega),
      List.getD_eq_default _ _ (by omega)]

theorem Canon_set {p : ℕ} {v : alloc.vec.Vec Std.U64} {t : Std.Usize} {x : Std.U64}
    (hv : Canon p v) (hx : x.val < p) : Canon p (v.set t x) := by
  refine ⟨by rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hv.1, ?_⟩
  intro u hu
  rw [alloc.vec.Vec.set_val_eq] at hu
  rcases List.mem_or_eq_of_mem_set hu with h | h
  · exact hv.2 u h
  · rw [h]; exact hx

/-! ## The word-level stages

Exactly what the Rust computes, in `ℕ`. The subtraction is written `a + p - b`,
as the Rust writes it, so that no truncating `ℕ` subtraction appears.
-/

/-- The DIF stage on words. -/
def difWord (p half step : ℕ) (sw tww : ℕ → ℕ) (t : ℕ) : ℕ :=
  if t % (2 * half) < half then (sw t + sw (t + half)) % p
  else ((sw (t - half) + p - sw t) % p * tww ((t % (2 * half) - half) * step)) % p

/-- The DIT stage on words. -/
def ditWord (p half step : ℕ) (sw tww : ℕ → ℕ) (t : ℕ) : ℕ :=
  if t % (2 * half) < half then
    (sw t + sw (t + half) * tww (t % (2 * half) * step) % p) % p
  else (sw (t - half) + p - sw t * tww ((t % (2 * half) - half) * step) % p) % p

theorem difWord_lt (p half step : ℕ) (hp : 0 < p) (sw tww : ℕ → ℕ) (t : ℕ) :
    difWord p half step sw tww t < p := by
  unfold difWord
  split <;> exact Nat.mod_lt _ hp

theorem ditWord_lt (p half step : ℕ) (hp : 0 < p) (sw tww : ℕ → ℕ) (t : ℕ) :
    ditWord p half step sw tww t < p := by
  unfold ditWord
  split <;> exact Nat.mod_lt _ hp

/-! ## `ntt::dif_stage`

Three loops. The outer one walks the block starts; the two inner ones write the
block's low half and then its high half, in that order, so `dst` is filled in one
strictly increasing stream.

Each inner loop's specification has three parts: the entries it has written hold
the stage value, the entries it has *not* written are untouched (the frame
condition -- without it the outer loop cannot know that earlier blocks survive),
and every entry is still a canonical residue.
-/

/-- The low half of one block: `dst[start + i] = src[start + i] + src[start + i + half]`
for `i < j`, nothing else changed. -/
theorem dif_stage_loop0_loop0_spec (src dst : alloc.vec.Vec Std.U64)
    (_p half start j : Std.Usize)
    (pw : Std.U64) (hp : pw.val < 2 ^ 32) (hppos : 0 < pw.val)
    (hsrc : Canon pw.val src) (hdst : Canon pw.val dst)
    (hblk : start.val + 2 * half.val ≤ N) (hj : j.val ≤ half.val)
    (hwrit : ∀ i, i < j.val →
      wordAt dst (start.val + i) = (wordAt src (start.val + i)
        + wordAt src (start.val + i + half.val)) % pw.val) :
    ntt.dif_stage_loop0_loop0 src dst pw half start j
      ⦃ z => Canon pw.val z
             ∧ (∀ i, i < half.val →
                 wordAt z (start.val + i) = (wordAt src (start.val + i)
                   + wordAt src (start.val + i + half.val)) % pw.val)
             ∧ (∀ k, (k < start.val ∨ start.val + half.val ≤ k) →
                 wordAt z k = wordAt dst k) ⦄ := by
  rw [ntt.dif_stage_loop0_loop0]
  apply loop.spec_decr_nat (fun s => half.val - s.2.val)
    (fun s => s.2.val ≤ half.val ∧ Canon pw.val s.1
      ∧ (∀ i, i < s.2.val →
          wordAt s.1 (start.val + i) = (wordAt src (start.val + i)
            + wordAt src (start.val + i + half.val)) % pw.val)
      ∧ (∀ k, (k < start.val ∨ start.val + half.val ≤ k) →
          wordAt s.1 k = wordAt dst k))
  · rintro ⟨d, jj⟩ ⟨hjj, hcd, hw, hfr⟩
    dsimp only at hjj hcd hw hfr
    simp only [ntt.dif_stage_loop0_loop0.body]
    by_cases hlt : jj < half
    · rw [if_pos hlt]
      have hjlt : jj.val < half.val := by scalar_tac
      have hsl : src.val.length = N := hsrc.1
      have hdl : d.val.length = N := hcd.1
      step as ⟨i, hi⟩
      have hib : i.val < src.val.length := by rw [hsl, hi]; omega
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = wordAt src (start.val + jj.val) := by
        rw [hi1, ← wordAt_of_lt (v := src) (t := i.val) hib, hi]
      step as ⟨i2, hi2⟩
      have hi2b : i2.val < src.val.length := by rw [hsl, hi2, hi]; omega
      step as ⟨i3, hi3⟩
      have hi3v : i3.val = wordAt src (start.val + jj.val + half.val) := by
        rw [hi3, ← wordAt_of_lt (v := src) (t := i2.val) hi2b, hi2, hi]
      have h1lt : i1.val < pw.val := by rw [hi1v]; exact wordAt_lt hsrc hppos _
      have h3lt : i3.val < pw.val := by rw [hi3v]; exact wordAt_lt hsrc hppos _
      step with aux_add_lt i1 i3 pw hp h1lt h3lt as ⟨i4, hi4v, hi4lt⟩
      have hidb : i.val < d.val.length := by rw [hdl, hi]; omega
      step as ⟨elem, back, helem, hback⟩
      rw [hback]
      step as ⟨j1, hj1⟩
      refine ⟨by scalar_tac, Canon_set hcd hi4lt, ?_, ?_, by scalar_tac⟩
      · intro t ht
        rw [hj1] at ht
        rcases Nat.lt_or_ge t jj.val with htlt | htge
        · rw [wordAt_set_ne (by omega)]
          exact hw t htlt
        · have hteq : t = jj.val := by omega
          subst hteq
          rw [← hi, wordAt_set_eq hidb, hi4v, hi1v, hi3v, hi]
      · intro k hk
        rw [wordAt_set_ne (by omega)]
        exact hfr k hk
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = half.val := by scalar_tac
      refine ⟨hcd, ?_, hfr⟩
      intro t ht
      exact hw t (by rw [heq]; exact ht)
  · exact ⟨hj, hdst, hwrit, fun k _ => rfl⟩

/-- The high half of one block: the twiddled difference, and the low half of the
same block (already written by the loop above) is preserved because the frame
condition covers it. -/
theorem dif_stage_loop0_loop1_spec (src dst tw : alloc.vec.Vec Std.U64)
    (pw mw : Std.U64) (half step start i e : Std.Usize) (h : Magic pw mw)
    (hsrc : Canon pw.val src) (hdst : Canon pw.val dst) (htw : Canon pw.val tw)
    (hblk : start.val + 2 * half.val ≤ N) (hi : i.val ≤ half.val)
    (hev : e.val = i.val * step.val) (hstep : 0 < step.val)
    (hebd : half.val * step.val ≤ N)
    (hwrit : ∀ t, t < i.val →
      wordAt dst (start.val + half.val + t)
        = ((wordAt src (start.val + t) + pw.val - wordAt src (start.val + t + half.val))
            % pw.val * wordAt tw (t * step.val)) % pw.val) :
    ntt.dif_stage_loop0_loop1 src dst tw pw mw half step start i e
      ⦃ z => Canon pw.val z
             ∧ (∀ t, t < half.val →
                 wordAt z (start.val + half.val + t)
                   = ((wordAt src (start.val + t) + pw.val
                       - wordAt src (start.val + t + half.val))
                       % pw.val * wordAt tw (t * step.val)) % pw.val)
             ∧ (∀ k, (k < start.val + half.val ∨ start.val + 2 * half.val ≤ k) →
                 wordAt z k = wordAt dst k) ⦄ := by
  have hp : pw.val < 2 ^ 32 := h.lt_pow
  have hppos : 0 < pw.val := h.pos
  rw [ntt.dif_stage_loop0_loop1]
  apply loop.spec_decr_nat (fun s => half.val - s.2.1.val)
    (fun s => s.2.1.val ≤ half.val ∧ s.2.2.val = s.2.1.val * step.val
      ∧ Canon pw.val s.1
      ∧ (∀ t, t < s.2.1.val →
          wordAt s.1 (start.val + half.val + t)
            = ((wordAt src (start.val + t) + pw.val
                - wordAt src (start.val + t + half.val))
                % pw.val * wordAt tw (t * step.val)) % pw.val)
      ∧ (∀ k, (k < start.val + half.val ∨ start.val + 2 * half.val ≤ k) →
          wordAt s.1 k = wordAt dst k))
  · rintro ⟨dd, ii, ee⟩ ⟨hii, hev1, hcd, hw, hfr⟩
    dsimp only at hii hev1 hcd hw hfr
    simp only [ntt.dif_stage_loop0_loop1.body]
    by_cases hlt : ii < half
    · rw [if_pos hlt]
      have hiilt : ii.val < half.val := by scalar_tac
      have hsl : src.val.length = N := hsrc.1
      have hdl : dd.val.length = N := hcd.1
      have htl : tw.val.length = N := htw.1
      step as ⟨i1, hi1⟩
      have hi1b : i1.val < src.val.length := by rw [hsl, hi1]; omega
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = wordAt src (start.val + ii.val) := by
        rw [hi2, ← wordAt_of_lt (v := src) (t := i1.val) hi1b, hi1]
      step as ⟨i3, hi3⟩
      have hi3b : i3.val < src.val.length := by rw [hsl, hi3, hi1]; omega
      step as ⟨i4, hi4⟩
      have hi4v : i4.val = wordAt src (start.val + ii.val + half.val) := by
        rw [hi4, ← wordAt_of_lt (v := src) (t := i3.val) hi3b, hi3, hi1]
      have h2lt : i2.val < pw.val := by rw [hi2v]; exact wordAt_lt hsrc hppos _
      have h4lt : i4.val < pw.val := by rw [hi4v]; exact wordAt_lt hsrc hppos _
      step with aux_sub_lt i2 i4 pw hp h2lt h4lt as ⟨sb, hsbv, hsblt⟩
      have heeb : ee.val < tw.val.length := by
        have hmul : ii.val * step.val < half.val * step.val :=
          Nat.mul_lt_mul_of_pos_right hiilt hstep
        rw [htl]; omega
      step as ⟨i5, hi5⟩
      have hi5v : i5.val = wordAt tw (ii.val * step.val) := by
        rw [hi5, ← wordAt_of_lt (v := tw) (t := ee.val) heeb, hev1]
      have h5lt : i5.val < pw.val := by rw [hi5v]; exact wordAt_lt htw hppos _
      step with aux_mul_lt sb i5 pw mw h hsblt h5lt as ⟨i6, hi6v, hi6lt⟩
      have hebnd : ee.val + step.val ≤ N := by
        have h1 : (ii.val + 1) * step.val ≤ half.val * step.val :=
          Nat.mul_le_mul_right _ (by omega)
        have h2 : (ii.val + 1) * step.val = ii.val * step.val + step.val := by ring
        omega
      step as ⟨i7, hi7⟩
      step as ⟨i8, hi8⟩
      have hi8v : i8.val = start.val + half.val + ii.val := by rw [hi8, hi7]
      have hidb : i8.val < dd.val.length := by rw [hdl, hi8v]; omega
      step as ⟨elem, back, helem, hback⟩
      rw [hback]
      step as ⟨i9, hi9⟩
      step as ⟨e1, he1⟩
      refine ⟨by scalar_tac, by rw [he1, hev1, hi9]; ring, Canon_set hcd hi6lt, ?_, ?_,
        by scalar_tac⟩
      · intro t ht
        rw [hi9] at ht
        rcases Nat.lt_or_ge t ii.val with htlt | htge
        · rw [wordAt_set_ne (by omega)]
          exact hw t htlt
        · have hteq : t = ii.val := by omega
          subst hteq
          rw [← hi8v, wordAt_set_eq hidb, hi6v, hsbv, hi2v, hi4v, hi5v]
      · intro k hk
        rw [wordAt_set_ne (by omega)]
        exact hfr k hk
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ii.val = half.val := by scalar_tac
      refine ⟨hcd, ?_, hfr⟩
      intro t ht
      exact hw t (by rw [heq]; exact ht)
  · exact ⟨hi, hev, hdst, hwrit, fun k _ => rfl⟩

/-- The three numeric facts about `len = 2 ^ (k+1)` dividing `N = 1024` that the
stage's parameter bookkeeping needs. Ten cases, all decidable. -/
private theorem difParams (k : ℕ) (hk : k < 10) :
    2 ^ (k + 1) ∣ N ∧ 0 < 2 * (N / 2 ^ (k + 1))
      ∧ 2 ^ k * (2 * (N / 2 ^ (k + 1))) = N := by
  have hN : N = 2 ^ 10 := by norm_num
  have hdiv : N / 2 ^ (k + 1) = 2 ^ (9 - k) := by
    rw [hN, Nat.pow_div (by omega) (by norm_num)]
    congr 1
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hN]; exact pow_dvd_pow 2 (by omega)
  · rw [hdiv]; positivity
  · rw [hdiv]
    have h9 : k + (9 - k) = 9 := by omega
    calc 2 ^ k * (2 * 2 ^ (9 - k)) = 2 * (2 ^ k * 2 ^ (9 - k)) := by ring
      _ = 2 * 2 ^ (k + (9 - k)) := by rw [pow_add]
      _ = 2 * 2 ^ 9 := by rw [h9]
      _ = N := by norm_num

/-- The outer loop of `dif_stage`: block starts below `start` are already the
stage's value, and the loop finishes the buffer. `start` is a multiple of the
block length, which is what makes the next block fit inside `N`. -/
theorem dif_stage_loop0_spec (src dst tw : alloc.vec.Vec Std.U64) (len : Std.Usize)
    (pw mw : Std.U64) (half step start : Std.Usize) (h : Magic pw mw)
    (hsrc : Canon pw.val src) (hdst : Canon pw.val dst) (htw : Canon pw.val tw)
    (hlen : len.val = 2 * half.val) (hhalf : 0 < half.val) (hdvd : len.val ∣ N)
    (hstep : 0 < step.val) (hebd : half.val * step.val ≤ N)
    (hstart : start.val ≤ N) (hmod : start.val % len.val = 0)
    (hval : ∀ t, t < start.val →
      wordAt dst t = difWord pw.val half.val step.val (wordAt src) (wordAt tw) t) :
    ntt.dif_stage_loop0 src dst len tw pw mw ntt.NTT_LEN half step start
      ⦃ z => Canon pw.val z
             ∧ ∀ t, t < N →
                 wordAt z t = difWord pw.val half.val step.val (wordAt src) (wordAt tw) t ⦄ := by
  have hp : pw.val < 2 ^ 32 := h.lt_pow
  have hppos : 0 < pw.val := h.pos
  rw [ntt.dif_stage_loop0]
  apply loop.spec_decr_nat (fun s => N - s.2.val)
    (fun s => s.2.val ≤ N ∧ s.2.val % len.val = 0 ∧ Canon pw.val s.1
      ∧ (∀ t, t < s.2.val →
          wordAt s.1 t = difWord pw.val half.val step.val (wordAt src) (wordAt tw) t))
  · rintro ⟨d, ss⟩ ⟨hss, hmod1, hcd, hval1⟩
    dsimp only at hss hmod1 hcd hval1
    simp only [ntt.dif_stage_loop0.body]
    by_cases hlt : ss < ntt.NTT_LEN
    · rw [if_pos hlt]
      have hsslt : ss.val < N := by scalar_tac
      have hlenpos : 0 < len.val := by omega
      have hblk : ss.val + len.val ≤ N := by
        obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hmod1
        obtain ⟨m0, hm0⟩ := hdvd
        have hcm : c < m0 := by
          have hlm : len.val * c < len.val * m0 := by rw [← hc, ← hm0]; exact hsslt
          exact Nat.lt_of_mul_lt_mul_left hlm
        have hle : len.val * (c + 1) ≤ len.val * m0 :=
          Nat.mul_le_mul (Nat.le_refl _) (by omega)
        rw [Nat.mul_add, Nat.mul_one] at hle
        omega
      have hblk2 : ss.val + 2 * half.val ≤ N := by omega
      -- the modulus fact that places an index inside its block
      have hmm : ∀ t, ss.val ≤ t → t < ss.val + len.val → t % len.val = t - ss.val := by
        intro t ha hb
        obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hmod1
        have ht : t = (t - ss.val) + len.val * c := by omega
        conv_lhs => rw [ht]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      step with dif_stage_loop0_loop0_spec src d 0#usize half ss 0#usize pw hp hppos
        hsrc hcd hblk2 (by simp) (by intro i hi; simp at hi) as ⟨d1, hc1, hwr1, hfr1⟩
      step with dif_stage_loop0_loop1_spec src d1 tw pw mw half step ss 0#usize 0#usize
        h hsrc hc1 htw hblk2 (by simp) (by simp) hstep hebd
        (by intro t ht; simp at ht) as ⟨d2, hc2, hwr2, hfr2⟩
      step as ⟨ss1, hss1⟩
      refine ⟨by omega, ?_, hc2, ?_, by omega⟩
      · rw [hss1, Nat.add_mod_right, hmod1]
      · intro t ht
        rw [hss1] at ht
        rcases Nat.lt_or_ge t ss.val with h1 | h1
        · rw [hfr2 t (Or.inl (by omega)), hfr1 t (Or.inl (by omega))]
          exact hval1 t h1
        · have hmd : t % (2 * half.val) = t - ss.val := by
            rw [← hlen]; exact hmm t h1 (by omega)
          rcases Nat.lt_or_ge t (ss.val + half.val) with h2 | h2
          · have hr : ss.val + (t - ss.val) = t := by omega
            have e1 := hwr1 (t - ss.val) (by omega)
            rw [hr] at e1
            rw [hfr2 t (Or.inl (by omega)), e1]
            unfold difWord
            rw [if_pos (by rw [hmd]; omega)]
          · have hr2 : ss.val + half.val + (t - ss.val - half.val) = t := by omega
            have e2 := hwr2 (t - ss.val - half.val) (by omega)
            rw [hr2] at e2
            have a1 : ss.val + (t - ss.val - half.val) = t - half.val := by omega
            rw [a1] at e2
            have a2 : t - half.val + half.val = t := by omega
            rw [a2] at e2
            have a3 : t - ss.val - half.val = t % (2 * half.val) - half.val := by
              rw [hmd]
            rw [a3] at e2
            rw [e2]
            unfold difWord
            rw [if_neg (by rw [hmd]; omega)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ss.val = N := by scalar_tac
      exact ⟨hcd, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · exact ⟨hstart, hmod, hdst, hval⟩

/-- The whole stage: every output index below `NTT_LEN` holds [`difWord`]. -/
theorem dif_stage_spec (src dst tw : alloc.vec.Vec Std.U64) (len : Std.Usize)
    (pw mw : Std.U64) (h : Magic pw mw) (k : ℕ) (hk : k < 10)
    (hlen : len.val = 2 ^ (k + 1))
    (hsrc : Canon pw.val src) (hdst : Canon pw.val dst) (htw : Canon pw.val tw) :
    ntt.dif_stage src dst len tw pw mw
      ⦃ z => Canon pw.val z
             ∧ ∀ t, t < N →
                 wordAt z t = difWord pw.val (2 ^ k) (2 * (N / 2 ^ (k + 1)))
                   (wordAt src) (wordAt tw) t ⦄ := by
  obtain ⟨hdvd, hsteppos, hprod⟩ := difParams k hk
  have hlen2 : len.val = 2 * 2 ^ k := by rw [hlen]; ring
  have hlne : len.val ≠ 0 := by omega
  rw [ntt.dif_stage]
  step as ⟨hf, hhf⟩
  have hhfv : hf.val = 2 ^ k := by rw [hhf, hlen2]; omega
  step as ⟨qq, hqq⟩
  have hqqv : qq.val = N / 2 ^ (k + 1) := by rw [hqq, ntt_NTT_LEN_val, hlen]
  have hqqle : qq.val ≤ N := by rw [hqqv]; exact Nat.div_le_self _ _
  step as ⟨st, hst⟩
  have hstv : st.val = 2 * (N / 2 ^ (k + 1)) := by rw [hst, hqqv]
  rw [← hhfv, ← hstv]
  exact dif_stage_loop0_spec src dst tw len pw mw hf st 0#usize h hsrc hdst htw
    (by rw [hlen2, hhfv]) (by rw [hhfv]; positivity) (by rw [hlen]; exact hdvd)
    (by rw [hstv]; exact hsteppos)
    (by rw [hhfv, hstv]; exact Nat.le_of_eq hprod)
    (by simp) (by simp) (by intro t ht; simp at ht)

/-! ## From words to the ring

`resK p v` reads a buffer as a function into `ZMod p`, and the word-level stage
becomes `AuxNTT.difStage` under it. The `ω` the ring-level stage runs on is the
*square* of the root the table holds, which is where the factor of two in the
code's `step` goes: `tw[(idx − half) · 2 · (N/len)] = ψ^(2·(idx−half)·(N/len))
= ω^((idx−half)·(N/len))`.
-/

/-- A buffer read as a function into `ZMod p`. -/
def resK (p : ℕ) (v : alloc.vec.Vec Std.U64) (t : ℕ) : ZMod p := ((wordAt v t : ℕ) : ZMod p)

/-
B2 deliverable: `difWord_cast`.

This is a FRAGMENT of `HachiEquiv/AuxCode.lean`, to be spliced in place of the
old `difWord_cast` (i.e. after `def resK`, before `end HachiEquiv.AuxCode`).
It needs nothing that file does not already have: the existing imports
(`AuxArith`, `AuxNTT`, `Mathlib.Data.ZMod.Basic`), `open HachiEquiv.AuxCode`
and `open HachiEquiv.AuxArith`.

NO new helper lemmas are required.

STATEMENT CHANGE: one hypothesis added, `(hsw : ∀ u, sw u < p)`, as the last
explicit hypothesis before `(t : ℕ)`. The unhypothesised statement is FALSE;
the `example` below is a machine-checked disproof of its universal closure.
Every call site has the hypothesis for free: a buffer satisfying `Canon p`
gives it via `wordAt_lt` (which needs `0 < p`, already available wherever
`Magic pw mw` / `0 < pw.val` is in scope).

-/

/-! ### Why `difWord_cast` needs canonicality

Without a bound on `sw`, the statement below is **false**. `difWord`'s `else`
branch subtracts in `ℕ`: `sw (t - half) + p - sw t` truncates at `0` when
`sw t > sw (t - half) + p`, and a truncated difference carries no information
about `sw t` at all, so no cast can recover `- sw t`. The counterexample fixes
`p = 5`, `half = step = 1`, `ψ = 1`, `tww ≡ 1`, `sw 0 = 0` and `sw 1 = 7`:
the word side computes `(0 + 5 - 7) % 5 = 0` while the ring side computes
`(0 - 7) · 1 = 3` in `ZMod 5`.

Every buffer this is applied to satisfies `Canon p`, hence `∀ u, sw u < p`; that
is the hypothesis added below. -/
example : ¬ (∀ (p half step : ℕ) (psi : ZMod p) (sw tww : ℕ → ℕ),
    (∀ e, ((tww e : ℕ) : ZMod p) = psi ^ e) → ∀ (t : ℕ),
    ((difWord p half (2 * step) sw tww t : ℕ) : ZMod p)
      = AuxNTT.difStage half step (psi ^ 2) (fun u => ((sw u : ℕ) : ZMod p)) t) := by
  intro h
  have hbad := h 5 1 1 1 (fun u => if u = 1 then 7 else 0) (fun _ => 1)
    (by intro e; simp) 1
  simp [difWord, AuxNTT.difStage] at hbad
  revert hbad
  decide

/-- The word-level DIF stage is the ring-level one, given a twiddle table that
holds the powers of `ψ` and with `ω = ψ²`.

`hsw` is the canonicality precondition: `difWord` writes its butterfly
difference as the truncating `ℕ` expression `sw (t - half) + p - sw t`, which
agrees with `sw (t - half) - sw t` in `ZMod p` only when `sw t ≤ sw (t - half) + p`.
`∀ u, sw u < p` gives that, and it holds of every buffer satisfying [`Canon`]
(see [`wordAt_lt`]); without it the statement is false -- see the counterexample
above. -/
theorem difWord_cast (p half step : ℕ) (psi : ZMod p) (sw tww : ℕ → ℕ)
    (htw : ∀ e, ((tww e : ℕ) : ZMod p) = psi ^ e) (hsw : ∀ u, sw u < p) (t : ℕ) :
    ((difWord p half (2 * step) sw tww t : ℕ) : ZMod p)
      = AuxNTT.difStage half step (psi ^ 2) (fun u => ((sw u : ℕ) : ZMod p)) t := by
  unfold difWord AuxNTT.difStage
  by_cases h : t % (2 * half) < half
  · rw [if_pos h, if_pos h, ZMod.natCast_mod, Nat.cast_add]
  · rw [if_neg h, if_neg h, ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod, htw]
    have hle : sw t ≤ sw (t - half) + p := by have := hsw t; omega
    rw [Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_self, add_zero, ← pow_mul]
    congr 2
    ring

/-! ## Conjoining two specifications of the same program

`spec_mono` weakens a postcondition; nothing in the Aeneas `WP` library
*combines* two postconditions of the same program. Change 6 needs exactly that:
`gadget_decompose` has an audited value specification and a separate word-level
digit bound, and the caller needs both without either theorem changing. -/

/-- Two specifications of the same program conjoin. -/
theorem spec_and {α} {m : Result α} {P Q : Post α} (hp : m ⦃ P ⦄) (hq : m ⦃ Q ⦄) :
    m ⦃ fun z => P z ∧ Q z ⦄ := by
  revert hp hq
  unfold WP.spec WP.theta WP.wp_return
  cases m <;> grind

end HachiEquiv.AuxCode


