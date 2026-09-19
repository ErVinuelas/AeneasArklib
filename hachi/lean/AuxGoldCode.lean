/-
The **Goldilocks DIF stage** (candidate T27): `AuxCode.lean`'s stage proof,
ported to the single 64-bit lane.

Everything structural is reused rather than restated. `wordAt`, `Canon`,
`difWord`, `ditWord`, `resK` and the ring-level bridge `difWord_cast` are all
already generic in the prime, so this file supplies only what the word
arithmetic changes: the three arithmetic steps, which move from
`aux_{add,sub,mul}_lt` at a `Magic` prime to `AuxGold`'s specs at `GP`.

The theorems come out *simpler* than their originals, because the prime is a
constant here rather than a parameter: no `pw`, no `mw`, no `Magic`, and no
`0 < pw.val` to thread. That is the one compensation for not being able to
instantiate `AuxArith` — `Magic` requires `p < 2^32`, and a product of two
Goldilocks residues needs a `u128`.
-/
import AuxCode
import AuxGold

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.AuxGoldCode

open HachiEquiv.AuxCode HachiEquiv.AuxGold

theorem GP_pos : 0 < GP := by norm_num

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
theorem gold_dif_stage_loop0_loop0_spec (src dst : alloc.vec.Vec Std.U64)
    (half start j : Std.Usize)
    (hsrc : Canon GP src) (hdst : Canon GP dst)
    (hblk : start.val + 2 * half.val ≤ N) (hj : j.val ≤ half.val)
    (hwrit : ∀ i, i < j.val →
      wordAt dst (start.val + i) = (wordAt src (start.val + i)
        + wordAt src (start.val + i + half.val)) % GP) :
    ntt.gold_dif_stage_loop0_loop0 src dst half start j
      ⦃ z => Canon GP z
             ∧ (∀ i, i < half.val →
                 wordAt z (start.val + i) = (wordAt src (start.val + i)
                   + wordAt src (start.val + i + half.val)) % GP)
             ∧ (∀ k, (k < start.val ∨ start.val + half.val ≤ k) →
                 wordAt z k = wordAt dst k) ⦄ := by
  rw [ntt.gold_dif_stage_loop0_loop0]
  apply loop.spec_decr_nat (fun s => half.val - s.2.val)
    (fun s => s.2.val ≤ half.val ∧ Canon GP s.1
      ∧ (∀ i, i < s.2.val →
          wordAt s.1 (start.val + i) = (wordAt src (start.val + i)
            + wordAt src (start.val + i + half.val)) % GP)
      ∧ (∀ k, (k < start.val ∨ start.val + half.val ≤ k) →
          wordAt s.1 k = wordAt dst k))
  · rintro ⟨d, jj⟩ ⟨hjj, hcd, hw, hfr⟩
    dsimp only at hjj hcd hw hfr
    simp only [ntt.gold_dif_stage_loop0_loop0.body]
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
      have h1lt : i1.val < GP := by rw [hi1v]; exact wordAt_lt hsrc GP_pos _
      have h3lt : i3.val < GP := by rw [hi3v]; exact wordAt_lt hsrc GP_pos _
      step with gold_add_spec i1 i3 h1lt h3lt as ⟨i4, hi4v, hi4lt⟩
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
theorem gold_dif_stage_loop0_loop1_spec (src dst tw : alloc.vec.Vec Std.U64)
    (half step start i e : Std.Usize)
    (hsrc : Canon GP src) (hdst : Canon GP dst) (htw : Canon GP tw)
    (hblk : start.val + 2 * half.val ≤ N) (hi : i.val ≤ half.val)
    (hev : e.val = i.val * step.val) (hstep : 0 < step.val)
    (hebd : half.val * step.val ≤ N)
    (hwrit : ∀ t, t < i.val →
      wordAt dst (start.val + half.val + t)
        = ((wordAt src (start.val + t) + GP - wordAt src (start.val + t + half.val))
            % GP * wordAt tw (t * step.val)) % GP) :
    ntt.gold_dif_stage_loop0_loop1 src dst tw half step start i e
      ⦃ z => Canon GP z
             ∧ (∀ t, t < half.val →
                 wordAt z (start.val + half.val + t)
                   = ((wordAt src (start.val + t) + GP
                       - wordAt src (start.val + t + half.val))
                       % GP * wordAt tw (t * step.val)) % GP)
             ∧ (∀ k, (k < start.val + half.val ∨ start.val + 2 * half.val ≤ k) →
                 wordAt z k = wordAt dst k) ⦄ := by
  rw [ntt.gold_dif_stage_loop0_loop1]
  apply loop.spec_decr_nat (fun s => half.val - s.2.1.val)
    (fun s => s.2.1.val ≤ half.val ∧ s.2.2.val = s.2.1.val * step.val
      ∧ Canon GP s.1
      ∧ (∀ t, t < s.2.1.val →
          wordAt s.1 (start.val + half.val + t)
            = ((wordAt src (start.val + t) + GP
                - wordAt src (start.val + t + half.val))
                % GP * wordAt tw (t * step.val)) % GP)
      ∧ (∀ k, (k < start.val + half.val ∨ start.val + 2 * half.val ≤ k) →
          wordAt s.1 k = wordAt dst k))
  · rintro ⟨dd, ii, ee⟩ ⟨hii, hev1, hcd, hw, hfr⟩
    dsimp only at hii hev1 hcd hw hfr
    simp only [ntt.gold_dif_stage_loop0_loop1.body]
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
      have h2lt : i2.val < GP := by rw [hi2v]; exact wordAt_lt hsrc GP_pos _
      have h4lt : i4.val < GP := by rw [hi4v]; exact wordAt_lt hsrc GP_pos _
      step with gold_sub_spec i2 i4 h2lt h4lt as ⟨sb, hsbv, hsblt⟩
      have heeb : ee.val < tw.val.length := by
        have hmul : ii.val * step.val < half.val * step.val :=
          Nat.mul_lt_mul_of_pos_right hiilt hstep
        rw [htl]; omega
      step as ⟨i5, hi5⟩
      have hi5v : i5.val = wordAt tw (ii.val * step.val) := by
        rw [hi5, ← wordAt_of_lt (v := tw) (t := ee.val) heeb, hev1]
      have h5lt : i5.val < GP := by rw [hi5v]; exact wordAt_lt htw GP_pos _
      step with gold_mul_spec sb i5 as ⟨i6, hi6v, hi6lt⟩
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
theorem gold_dif_stage_loop0_spec (src dst tw : alloc.vec.Vec Std.U64) (len : Std.Usize)
    (half step start : Std.Usize)
    (hsrc : Canon GP src) (hdst : Canon GP dst) (htw : Canon GP tw)
    (hlen : len.val = 2 * half.val) (hhalf : 0 < half.val) (hdvd : len.val ∣ N)
    (hstep : 0 < step.val) (hebd : half.val * step.val ≤ N)
    (hstart : start.val ≤ N) (hmod : start.val % len.val = 0)
    (hval : ∀ t, t < start.val →
      wordAt dst t = difWord GP half.val step.val (wordAt src) (wordAt tw) t) :
    ntt.gold_dif_stage_loop0 src dst len tw ntt.NTT_LEN half step start
      ⦃ z => Canon GP z
             ∧ ∀ t, t < N →
                 wordAt z t = difWord GP half.val step.val (wordAt src) (wordAt tw) t ⦄ := by
  rw [ntt.gold_dif_stage_loop0]
  apply loop.spec_decr_nat (fun s => N - s.2.val)
    (fun s => s.2.val ≤ N ∧ s.2.val % len.val = 0 ∧ Canon GP s.1
      ∧ (∀ t, t < s.2.val →
          wordAt s.1 t = difWord GP half.val step.val (wordAt src) (wordAt tw) t))
  · rintro ⟨d, ss⟩ ⟨hss, hmod1, hcd, hval1⟩
    dsimp only at hss hmod1 hcd hval1
    simp only [ntt.gold_dif_stage_loop0.body]
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
      step with gold_dif_stage_loop0_loop0_spec src d half ss 0#usize
        hsrc hcd hblk2 (by simp) (by intro i hi; simp at hi) as ⟨d1, hc1, hwr1, hfr1⟩
      step with gold_dif_stage_loop0_loop1_spec src d1 tw half step ss 0#usize 0#usize
        hsrc hc1 htw hblk2 (by simp) (by simp) hstep hebd
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
theorem gold_dif_stage_spec (src dst tw : alloc.vec.Vec Std.U64) (len : Std.Usize)
    (k : ℕ) (hk : k < 10)
    (hlen : len.val = 2 ^ (k + 1))
    (hsrc : Canon GP src) (hdst : Canon GP dst) (htw : Canon GP tw) :
    ntt.gold_dif_stage src dst len tw
      ⦃ z => Canon GP z
             ∧ ∀ t, t < N →
                 wordAt z t = difWord GP (2 ^ k) (2 * (N / 2 ^ (k + 1)))
                   (wordAt src) (wordAt tw) t ⦄ := by
  obtain ⟨hdvd, hsteppos, hprod⟩ := difParams k hk
  have hlen2 : len.val = 2 * 2 ^ k := by rw [hlen]; ring
  have hlne : len.val ≠ 0 := by omega
  rw [ntt.gold_dif_stage]
  step as ⟨hf, hhf⟩
  have hhfv : hf.val = 2 ^ k := by rw [hhf, hlen2]; omega
  step as ⟨qq, hqq⟩
  have hqqv : qq.val = N / 2 ^ (k + 1) := by rw [hqq, ntt_NTT_LEN_val, hlen]
  have hqqle : qq.val ≤ N := by rw [hqqv]; exact Nat.div_le_self _ _
  step as ⟨st, hst⟩
  have hstv : st.val = 2 * (N / 2 ^ (k + 1)) := by rw [hst, hqqv]
  rw [← hhfv, ← hstv]
  exact gold_dif_stage_loop0_spec src dst tw len hf st 0#usize hsrc hdst htw
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

end HachiEquiv.AuxGoldCode
