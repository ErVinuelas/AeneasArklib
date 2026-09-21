/-
The **fused Goldilocks DIF stage**: two decimation-in-frequency stages in one
pass over the array -- the radix-4 memory pattern, without a radix-4 theory.

A textbook radix-4 butterfly permutes its four outputs, so it agrees with the
radix-2 transform only up to base-4 digit reversal. Proving *that* would mean a
whole second theory: a `dif4Run`, its multiplicativity, its inverse, and new
versions of everything `NttProduct` builds on `difRun`. This file does the other
thing. `ntt::gold_dif_stage2` writes the four outputs of a group in the order
and with the twiddles the *composite* `difStage ∘ difStage` produces, so one
pass of it is exactly two passes of the old stage -- the same values, at the
same positions, from the same table.

The payoff is at the top: [`gold_dif_stage2_spec`]'s conclusion is literally
[`difWord`] of [`difWord`], the two shapes `gold_dif_stage_spec` already
produces at consecutive block lengths, so `gold_forward_spec`'s statement does
not move and `NttProduct.prod_difRun`, `inv_value` and `gold_dot_spec` are
untouched. `difRun_succ` is `rfl`, which is what makes the two-at-a-time
invariant step as cheap as the one-at-a-time one.

The structure mirrors `GoldStage`'s: an inner loop over the groups of one
block, an outer loop over the blocks, a top-level spec that fixes the
parameters. What changes is the inner loop, which now writes *four* entries per
iteration at four separated positions rather than one, so its specification has
four written-value clauses instead of one and its frame condition has to survive
four `Vec.set`s.
-/
import GoldStage

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.GoldFusedStage

open HachiEquiv.NttStage HachiEquiv.GoldArith HachiEquiv.GoldStage

/-! ## The four words one group writes

`bSum` and `bDif` are the two branches of a DIF butterfly, named so that the
first stage's four intermediate values can be written down without unfolding
[`difWord`] and without committing to how the index sits inside its block. The
outer loop is where they are matched against `difWord` proper. -/

/-- The sum branch of a DIF butterfly at `t`, for block half-length `half`. -/
def bSum (sw : ℕ → ℕ) (half t : ℕ) : ℕ := (sw t + sw (t + half)) % GP

/-- The twiddled-difference branch of a DIF butterfly at `t`, twiddle index `e`. -/
def bDif (sw tww : ℕ → ℕ) (half e t : ℕ) : ℕ :=
  ((sw t + GP - sw (t + half)) % GP * tww e) % GP

/-- What the group `(s, u)` writes at `s + u`. -/
def f0 (sw : ℕ → ℕ) (half quarter s u : ℕ) : ℕ :=
  (bSum sw half (s + u) + bSum sw half (s + u + quarter)) % GP

/-- What the group `(s, u)` writes at `s + u + quarter`. -/
def f1 (sw tww : ℕ → ℕ) (half quarter step2 s u : ℕ) : ℕ :=
  ((bSum sw half (s + u) + GP - bSum sw half (s + u + quarter)) % GP
    * tww (u * step2)) % GP

/-- What the group `(s, u)` writes at `s + half + u`. -/
def f2 (sw tww : ℕ → ℕ) (half quarter step1 s u : ℕ) : ℕ :=
  (bDif sw tww half (u * step1) (s + u)
    + bDif sw tww half ((u + quarter) * step1) (s + u + quarter)) % GP

/-- What the group `(s, u)` writes at `s + half + quarter + u`. -/
def f3 (sw tww : ℕ → ℕ) (half quarter step1 step2 s u : ℕ) : ℕ :=
  ((bDif sw tww half (u * step1) (s + u) + GP
      - bDif sw tww half ((u + quarter) * step1) (s + u + quarter)) % GP
    * tww (u * step2)) % GP

/-! ## The inner loop

One group per iteration: four reads at stride `quarter`, four writes at the same
four positions. The four written-value clauses are independent, and the frame
condition covers everything outside the block -- which is all the outer loop
needs, because inside the block the four clauses together account for every
index once the loop has run to `quarter`. -/

/-- One block's worth of fused groups. -/
theorem gold_dif_stage2_loop0_loop0_spec (src dst tw : alloc.vec.Vec Std.U64)
    (half quarter step1 step2 start j : Std.Usize)
    (hsrc : Canon GP src) (hdst : Canon GP dst) (htw : Canon GP tw)
    (hhq : half.val = 2 * quarter.val) (hqpos : 0 < quarter.val)
    (hblk : start.val + 2 * half.val ≤ N) (hj : j.val ≤ quarter.val)
    (hs2 : step2.val = 2 * step1.val) (hstep : 0 < step1.val)
    (hebd : half.val * step1.val ≤ N)
    (hw0 : ∀ u, u < j.val →
      wordAt dst (start.val + u) = f0 (wordAt src) half.val quarter.val start.val u)
    (hw1 : ∀ u, u < j.val →
      wordAt dst (start.val + u + quarter.val)
        = f1 (wordAt src) (wordAt tw) half.val quarter.val step2.val start.val u)
    (hw2 : ∀ u, u < j.val →
      wordAt dst (start.val + half.val + u)
        = f2 (wordAt src) (wordAt tw) half.val quarter.val step1.val start.val u)
    (hw3 : ∀ u, u < j.val →
      wordAt dst (start.val + half.val + quarter.val + u)
        = f3 (wordAt src) (wordAt tw) half.val quarter.val step1.val step2.val start.val u) :
    ntt.gold_dif_stage2_loop0_loop0 src dst tw half quarter step1 step2 start j
      ⦃ z => Canon GP z
             ∧ (∀ u, u < quarter.val →
                 wordAt z (start.val + u) = f0 (wordAt src) half.val quarter.val start.val u)
             ∧ (∀ u, u < quarter.val →
                 wordAt z (start.val + u + quarter.val)
                   = f1 (wordAt src) (wordAt tw) half.val quarter.val step2.val start.val u)
             ∧ (∀ u, u < quarter.val →
                 wordAt z (start.val + half.val + u)
                   = f2 (wordAt src) (wordAt tw) half.val quarter.val step1.val start.val u)
             ∧ (∀ u, u < quarter.val →
                 wordAt z (start.val + half.val + quarter.val + u)
                   = f3 (wordAt src) (wordAt tw) half.val quarter.val step1.val step2.val
                       start.val u)
             ∧ (∀ k, (k < start.val ∨ start.val + 2 * half.val ≤ k) →
                 wordAt z k = wordAt dst k) ⦄ := by
  rw [ntt.gold_dif_stage2_loop0_loop0]
  apply loop.spec_decr_nat (fun s => quarter.val - s.2.val)
    (fun s => s.2.val ≤ quarter.val ∧ Canon GP s.1
      ∧ (∀ u, u < s.2.val →
          wordAt s.1 (start.val + u) = f0 (wordAt src) half.val quarter.val start.val u)
      ∧ (∀ u, u < s.2.val →
          wordAt s.1 (start.val + u + quarter.val)
            = f1 (wordAt src) (wordAt tw) half.val quarter.val step2.val start.val u)
      ∧ (∀ u, u < s.2.val →
          wordAt s.1 (start.val + half.val + u)
            = f2 (wordAt src) (wordAt tw) half.val quarter.val step1.val start.val u)
      ∧ (∀ u, u < s.2.val →
          wordAt s.1 (start.val + half.val + quarter.val + u)
            = f3 (wordAt src) (wordAt tw) half.val quarter.val step1.val step2.val start.val u)
      ∧ (∀ k, (k < start.val ∨ start.val + 2 * half.val ≤ k) →
          wordAt s.1 k = wordAt dst k))
  · rintro ⟨d, jj⟩ ⟨hjj, hcd, hv0, hv1, hv2, hv3, hfr⟩
    dsimp only at hjj hcd hv0 hv1 hv2 hv3 hfr
    simp only [ntt.gold_dif_stage2_loop0_loop0.body]
    by_cases hlt : jj < quarter
    · rw [if_pos hlt]
      have hjlt : jj.val < quarter.val := by scalar_tac
      have hsl : src.val.length = N := hsrc.1
      have hdl : d.val.length = N := hcd.1
      have htl : tw.val.length = N := htw.1
      -- the twiddle indices this group reads, all inside the table
      have hbt1 : jj.val * step1.val < N := by
        have h := Nat.mul_lt_mul_of_pos_right (show jj.val < half.val by omega) hstep
        omega
      have hbt2 : (jj.val + quarter.val) * step1.val < N := by
        have h := Nat.mul_lt_mul_of_pos_right
          (show jj.val + quarter.val < half.val by omega) hstep
        omega
      have hbt3 : jj.val * step2.val < N := by
        have h := Nat.mul_lt_mul_of_pos_right
          (show 2 * jj.val < half.val by omega) hstep
        have he : jj.val * step2.val = 2 * jj.val * step1.val := by rw [hs2]; ring
        omega
      -- the four reads
      step as ⟨i, hi⟩
      have hib : i.val < src.val.length := by rw [hsl, hi]; omega
      step as ⟨a0, ha0⟩
      have ha0v : a0.val = wordAt src (start.val + jj.val) := by
        rw [ha0, ← wordAt_of_lt (v := src) (t := i.val) hib, hi]
      step as ⟨i1, hi1⟩
      have hi1b : i1.val < src.val.length := by rw [hsl, hi1, hi]; omega
      step as ⟨a1, ha1⟩
      have ha1v : a1.val = wordAt src (start.val + jj.val + quarter.val) := by
        rw [ha1, ← wordAt_of_lt (v := src) (t := i1.val) hi1b, hi1, hi]
      step as ⟨i2, hi2⟩
      have hi2b : i2.val < src.val.length := by rw [hsl, hi2, hi]; omega
      step as ⟨a2, ha2⟩
      have ha2v : a2.val = wordAt src (start.val + jj.val + half.val) := by
        rw [ha2, ← wordAt_of_lt (v := src) (t := i2.val) hi2b, hi2, hi]
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      have hi4b : i4.val < src.val.length := by rw [hsl, hi4, hi3, hi]; omega
      step as ⟨a3, ha3⟩
      have ha3v : a3.val = wordAt src (start.val + jj.val + quarter.val + half.val) := by
        rw [ha3, ← wordAt_of_lt (v := src) (t := i4.val) hi4b, hi4, hi3, hi]
        congr 1
        omega
      have h0lt : a0.val < GP := by rw [ha0v]; exact wordAt_lt hsrc GP_pos _
      have h1lt : a1.val < GP := by rw [ha1v]; exact wordAt_lt hsrc GP_pos _
      have h2lt : a2.val < GP := by rw [ha2v]; exact wordAt_lt hsrc GP_pos _
      have h3lt : a3.val < GP := by rw [ha3v]; exact wordAt_lt hsrc GP_pos _
      -- the first stage's four values
      step with gold_add_spec a0 a2 h0lt h2lt as ⟨b0, hb0v, hb0lt⟩
      step with gold_add_spec a1 a3 h1lt h3lt as ⟨b1, hb1v, hb1lt⟩
      step with gold_sub_spec a0 a2 h0lt h2lt as ⟨d0, hd0v, hd0lt⟩
      step as ⟨i5, hi5⟩
      have hi5b : i5.val < tw.val.length := by rw [htl, hi5]; exact hbt1
      step as ⟨t1, ht1⟩
      have ht1v : t1.val = wordAt tw (jj.val * step1.val) := by
        rw [ht1, ← wordAt_of_lt (v := tw) (t := i5.val) hi5b, hi5]
      step with gold_mul_spec d0 t1 as ⟨b2, hb2v, hb2lt⟩
      step with gold_sub_spec a1 a3 h1lt h3lt as ⟨d1, hd1v, hd1lt⟩
      step as ⟨i7, hi7⟩
      step as ⟨i8, hi8⟩
      have hi8b : i8.val < tw.val.length := by rw [htl, hi8, hi7]; exact hbt2
      step as ⟨t2, ht2⟩
      have ht2v : t2.val = wordAt tw ((jj.val + quarter.val) * step1.val) := by
        rw [ht2, ← wordAt_of_lt (v := tw) (t := i8.val) hi8b, hi8, hi7]
      step with gold_mul_spec d1 t2 as ⟨b3, hb3v, hb3lt⟩
      -- the four intermediates, in the `bSum` / `bDif` form
      have hb0f : b0.val = bSum (wordAt src) half.val (start.val + jj.val) := by
        rw [hb0v, ha0v, ha2v]; rfl
      have hb1f : b1.val
          = bSum (wordAt src) half.val (start.val + jj.val + quarter.val) := by
        rw [hb1v, ha1v, ha3v]; rfl
      have hb2f : b2.val
          = bDif (wordAt src) (wordAt tw) half.val (jj.val * step1.val)
              (start.val + jj.val) := by
        rw [hb2v, hd0v, ht1v, ha0v, ha2v]; rfl
      have hb3f : b3.val
          = bDif (wordAt src) (wordAt tw) half.val ((jj.val + quarter.val) * step1.val)
              (start.val + jj.val + quarter.val) := by
        rw [hb3v, hd1v, ht2v, ha1v, ha3v]; rfl
      -- write 1: `start + jj`
      step with gold_add_spec b0 b1 hb0lt hb1lt as ⟨o0, ho0v, ho0lt⟩
      have hidb : i.val < d.val.length := by rw [hdl, hi]; omega
      step as ⟨elem, back, helem, hback⟩
      rw [hback]
      step with gold_sub_spec b0 b1 hb0lt hb1lt as ⟨e0, he0v, he0lt⟩
      step as ⟨i11, hi11⟩
      have hi11b : i11.val < tw.val.length := by rw [htl, hi11]; exact hbt3
      step as ⟨t3, ht3⟩
      have ht3v : t3.val = wordAt tw (jj.val * step2.val) := by
        rw [ht3, ← wordAt_of_lt (v := tw) (t := i11.val) hi11b, hi11]
      step with gold_mul_spec e0 t3 as ⟨o1, ho1v, ho1lt⟩
      -- write 2: `start + jj + quarter`
      have hc1 : Canon GP (d.set i o0) := Canon_set hcd ho0lt
      have hd1l : (d.set i o0).val.length = N := hc1.1
      step as ⟨i14, hi14⟩
      have hi14b : i14.val < (d.set i o0).val.length := by rw [hd1l, hi14, hi]; omega
      step as ⟨elem1, back1, helem1, hback1⟩
      rw [hback1]
      step with gold_add_spec b2 b3 hb2lt hb3lt as ⟨o2, ho2v, ho2lt⟩
      -- write 3: `start + half + jj`
      have hc2 : Canon GP ((d.set i o0).set i14 o1) := Canon_set hc1 ho1lt
      have hd2l : ((d.set i o0).set i14 o1).val.length = N := hc2.1
      step as ⟨i16, hi16⟩
      step as ⟨i17, hi17⟩
      have hi17b : i17.val < ((d.set i o0).set i14 o1).val.length := by
        rw [hd2l, hi17, hi16]; omega
      step as ⟨elem2, back2, helem2, hback2⟩
      rw [hback2]
      step with gold_sub_spec b2 b3 hb2lt hb3lt as ⟨e1, he1v, he1lt⟩
      step as ⟨t4, ht4⟩
      have ht4v : t4.val = wordAt tw (jj.val * step2.val) := by
        rw [ht4, ← wordAt_of_lt (v := tw) (t := i11.val) hi11b, hi11]
      step with gold_mul_spec e1 t4 as ⟨o3, ho3v, ho3lt⟩
      -- write 4: `start + half + quarter + jj`
      have hc3 : Canon GP (((d.set i o0).set i14 o1).set i17 o2) := Canon_set hc2 ho2lt
      have hd3l : (((d.set i o0).set i14 o1).set i17 o2).val.length = N := hc3.1
      step as ⟨i20, hi20⟩
      step as ⟨i21, hi21⟩
      have hi21b : i21.val < (((d.set i o0).set i14 o1).set i17 o2).val.length := by
        rw [hd3l, hi21, hi20, hi16]; omega
      step as ⟨elem3, back3, helem3, hback3⟩
      rw [hback3]
      step as ⟨j1, hj1⟩
      -- the four positions, as naturals
      have p0 : i.val = start.val + jj.val := hi
      have p1 : i14.val = start.val + jj.val + quarter.val := by rw [hi14, hi]
      have p2 : i17.val = start.val + half.val + jj.val := by rw [hi17, hi16]
      have p3 : i21.val = start.val + half.val + quarter.val + jj.val := by
        rw [hi21, hi20, hi16]
      -- The disequalities the four writes need, proved in a context with the
      -- arithmetic facts alone. `omega` scans everything it is given, and the
      -- butterfly's `% GP` equations make it scan a 64-bit modulus fifteen
      -- times over; `clear * -` is the difference between a second and a
      -- heartbeat timeout.
      have hdisA : ∀ u, u < jj.val →
          (start.val + u ≠ i.val ∧ start.val + u ≠ i14.val
            ∧ start.val + u ≠ i17.val ∧ start.val + u ≠ i21.val)
          ∧ (start.val + u + quarter.val ≠ i.val
            ∧ start.val + u + quarter.val ≠ i14.val
            ∧ start.val + u + quarter.val ≠ i17.val
            ∧ start.val + u + quarter.val ≠ i21.val)
          ∧ (start.val + half.val + u ≠ i.val
            ∧ start.val + half.val + u ≠ i14.val
            ∧ start.val + half.val + u ≠ i17.val
            ∧ start.val + half.val + u ≠ i21.val)
          ∧ (start.val + half.val + quarter.val + u ≠ i.val
            ∧ start.val + half.val + quarter.val + u ≠ i14.val
            ∧ start.val + half.val + quarter.val + u ≠ i17.val
            ∧ start.val + half.val + quarter.val + u ≠ i21.val) := by
        clear * - p0 p1 p2 p3 hjlt hhq hqpos
        intro u hu
        refine ⟨⟨by omega, by omega, by omega, by omega⟩,
          ⟨by omega, by omega, by omega, by omega⟩,
          ⟨by omega, by omega, by omega, by omega⟩,
          ⟨by omega, by omega, by omega, by omega⟩⟩
      have hdisB :
          (start.val + jj.val ≠ i14.val ∧ start.val + jj.val ≠ i17.val
            ∧ start.val + jj.val ≠ i21.val)
          ∧ (start.val + jj.val + quarter.val ≠ i17.val
            ∧ start.val + jj.val + quarter.val ≠ i21.val)
          ∧ start.val + half.val + jj.val ≠ i21.val := by
        clear * - p0 p1 p2 p3 hjlt hhq hqpos
        exact ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, by omega⟩, by omega⟩
      have hdisF : ∀ k, (k < start.val ∨ start.val + 2 * half.val ≤ k) →
          k ≠ i.val ∧ k ≠ i14.val ∧ k ≠ i17.val ∧ k ≠ i21.val := by
        clear * - p0 p1 p2 p3 hjlt hhq hqpos
        intro k hk
        exact ⟨by omega, by omega, by omega, by omega⟩
      refine ⟨by clear * - hj1 hjlt; omega, Canon_set hc3 ho3lt, ?_, ?_, ?_, ?_, ?_,
        by clear * - hj1 hjlt hqpos; omega⟩
      · intro u hu
        rw [hj1] at hu
        rcases Nat.lt_or_ge u jj.val with hlt2 | hge
        · obtain ⟨⟨n0, n1, n2, n3⟩, -, -, -⟩ := hdisA u hlt2
          rw [wordAt_set_ne n3, wordAt_set_ne n2, wordAt_set_ne n1, wordAt_set_ne n0]
          exact hv0 u hlt2
        · have heu : u = jj.val := by clear * - hu hge; omega
          subst heu
          obtain ⟨⟨n1, n2, n3⟩, -, -⟩ := hdisB
          rw [wordAt_set_ne n3, wordAt_set_ne n2, wordAt_set_ne n1,
            ← p0, wordAt_set_eq hidb, ho0v, hb0f, hb1f]
          rfl
      · intro u hu
        rw [hj1] at hu
        rcases Nat.lt_or_ge u jj.val with hlt2 | hge
        · obtain ⟨-, ⟨n0, n1, n2, n3⟩, -, -⟩ := hdisA u hlt2
          rw [wordAt_set_ne n3, wordAt_set_ne n2, wordAt_set_ne n1, wordAt_set_ne n0]
          exact hv1 u hlt2
        · have heu : u = jj.val := by clear * - hu hge; omega
          subst heu
          obtain ⟨-, ⟨n2, n3⟩, -⟩ := hdisB
          rw [wordAt_set_ne n3, wordAt_set_ne n2,
            ← p1, wordAt_set_eq hi14b, ho1v, he0v, ht3v, hb0f, hb1f]
          rfl
      · intro u hu
        rw [hj1] at hu
        rcases Nat.lt_or_ge u jj.val with hlt2 | hge
        · obtain ⟨-, -, ⟨n0, n1, n2, n3⟩, -⟩ := hdisA u hlt2
          rw [wordAt_set_ne n3, wordAt_set_ne n2, wordAt_set_ne n1, wordAt_set_ne n0]
          exact hv2 u hlt2
        · have heu : u = jj.val := by clear * - hu hge; omega
          subst heu
          obtain ⟨-, -, n3⟩ := hdisB
          rw [wordAt_set_ne n3, ← p2, wordAt_set_eq hi17b, ho2v, hb2f, hb3f]
          rfl
      · intro u hu
        rw [hj1] at hu
        rcases Nat.lt_or_ge u jj.val with hlt2 | hge
        · obtain ⟨-, -, -, ⟨n0, n1, n2, n3⟩⟩ := hdisA u hlt2
          rw [wordAt_set_ne n3, wordAt_set_ne n2, wordAt_set_ne n1, wordAt_set_ne n0]
          exact hv3 u hlt2
        · have heu : u = jj.val := by clear * - hu hge; omega
          subst heu
          rw [← p3, wordAt_set_eq hi21b, ho3v, he1v, ht4v, hb2f, hb3f]
          rfl
      · intro k hk
        obtain ⟨n0, n1, n2, n3⟩ := hdisF k hk
        rw [wordAt_set_ne n3, wordAt_set_ne n2, wordAt_set_ne n1, wordAt_set_ne n0]
        exact hfr k hk
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = quarter.val := by scalar_tac
      exact ⟨hcd, fun u hu => hv0 u (by rw [heq]; exact hu),
        fun u hu => hv1 u (by rw [heq]; exact hu),
        fun u hu => hv2 u (by rw [heq]; exact hu),
        fun u hu => hv3 u (by rw [heq]; exact hu), hfr⟩
  · exact ⟨hj, hdst, hw0, hw1, hw2, hw3, fun k _ => rfl⟩

/-! ## From the four clauses to the composite stage

The inner loop delivers four raw values per group. This section shows that,
taken together over a whole block, they *are* `difWord ∘ difWord` -- which is
the only statement the transform above cares about.

`difWord`'s branch test is `t % (2 * half) < half`, so everything here turns on
one fact: the block start is a multiple of the block length, hence also of every
divisor of it, so an index's residue is its offset inside the block. The offset's
quarter then picks which of the four clauses applies. -/

/-- `difWord` on the sum branch. -/
theorem difWord_lo (p half step : ℕ) (sw tww : ℕ → ℕ) (t : ℕ)
    (h : t % (2 * half) < half) :
    difWord p half step sw tww t = (sw t + sw (t + half)) % p := by
  unfold difWord; rw [if_pos h]

/-- `difWord` on the twiddled-difference branch. -/
theorem difWord_hi (p half step : ℕ) (sw tww : ℕ → ℕ) (t : ℕ)
    (h : ¬ t % (2 * half) < half) :
    difWord p half step sw tww t
      = ((sw (t - half) + p - sw t) % p * tww ((t % (2 * half) - half) * step)) % p := by
  unfold difWord; rw [if_neg h]

/-- Adding a multiple of the modulus does not move a residue that is already small. -/
private theorem add_mod_zero {m s r : ℕ} (hs : s % m = 0) (hr : r < m) :
    (s + r) % m = r := by
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hs
  subst hc
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hr

/-- A block start is a multiple of every half of its length. -/
private theorem half_mod {half s : ℕ} (hsm : s % (2 * half) = 0) : s % half = 0 := by
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hsm
  subst hc
  rw [show 2 * half * c = half * (2 * c) by ring, Nat.mul_mod_right]

section Block

variable (sw tww : ℕ → ℕ) (half quarter step1 step2 s u : ℕ)

/-- Offset `u < quarter`: the first quarter of the block, both stages on their
sum branch. -/
theorem fusedA (hhq : half = 2 * quarter) (hu : u < quarter)
    (hsm : s % (2 * half) = 0) :
    difWord GP quarter step2 (difWord GP half step1 sw tww) tww (s + u)
      = f0 sw half quarter s u := by
  have hsh : s % half = 0 := half_mod hsm
  have hm2 : (s + u) % (2 * quarter) = u := by
    rw [← hhq]; exact add_mod_zero hsh (by omega)
  have hmA : (s + u) % (2 * half) = u := add_mod_zero hsm (by omega)
  have hmB : (s + u + quarter) % (2 * half) = u + quarter := by
    rw [show s + u + quarter = s + (u + quarter) by ring]
    exact add_mod_zero hsm (by omega)
  rw [difWord_lo GP quarter step2 _ tww (s + u) (by rw [hm2]; exact hu),
    difWord_lo GP half step1 sw tww (s + u) (by rw [hmA]; omega),
    difWord_lo GP half step1 sw tww (s + u + quarter) (by rw [hmB]; omega)]
  rfl

/-- Offset `quarter ≤ · < half`: the second stage takes its difference branch,
the first is still on its sum branch. -/
theorem fusedB (hhq : half = 2 * quarter) (hu : u < quarter)
    (hsm : s % (2 * half) = 0) :
    difWord GP quarter step2 (difWord GP half step1 sw tww) tww (s + u + quarter)
      = f1 sw tww half quarter step2 s u := by
  have hsh : s % half = 0 := half_mod hsm
  have hm2 : (s + u + quarter) % (2 * quarter) = u + quarter := by
    rw [← hhq, show s + u + quarter = s + (u + quarter) by ring]
    exact add_mod_zero hsh (by omega)
  have hmA : (s + u) % (2 * half) = u := add_mod_zero hsm (by omega)
  have hmB : (s + u + quarter) % (2 * half) = u + quarter := by
    rw [show s + u + quarter = s + (u + quarter) by ring]
    exact add_mod_zero hsm (by omega)
  rw [difWord_hi GP quarter step2 _ tww (s + u + quarter) (by rw [hm2]; omega), hm2,
    show u + quarter - quarter = u by omega,
    show s + u + quarter - quarter = s + u by omega,
    difWord_lo GP half step1 sw tww (s + u) (by rw [hmA]; omega),
    difWord_lo GP half step1 sw tww (s + u + quarter) (by rw [hmB]; omega)]
  rfl

/-- Offset `half ≤ · < half + quarter`: the first stage takes its difference
branch at both of the second stage's operands. -/
theorem fusedC (hhq : half = 2 * quarter) (hu : u < quarter)
    (hsm : s % (2 * half) = 0) :
    difWord GP quarter step2 (difWord GP half step1 sw tww) tww (s + half + u)
      = f2 sw tww half quarter step1 s u := by
  have hsh : s % half = 0 := half_mod hsm
  have hm2 : (s + half + u) % (2 * quarter) = u := by
    rw [← hhq, show s + half + u = (s + half) + u by ring]
    refine add_mod_zero ?_ (by omega)
    rw [Nat.add_mod, hsh, Nat.mod_self]
    simp
  have hmC : (s + half + u) % (2 * half) = half + u := by
    rw [show s + half + u = s + (half + u) by ring]
    exact add_mod_zero hsm (by omega)
  have hmD : (s + half + u + quarter) % (2 * half) = half + u + quarter := by
    rw [show s + half + u + quarter = s + (half + u + quarter) by ring]
    exact add_mod_zero hsm (by omega)
  have g2 : difWord GP half step1 sw tww (s + half + u)
      = bDif sw tww half (u * step1) (s + u) := by
    rw [difWord_hi GP half step1 sw tww (s + half + u) (by rw [hmC]; omega), hmC,
      show half + u - half = u by omega,
      show s + half + u - half = s + u by omega,
      show s + half + u = s + u + half by omega]
    rfl
  have g3 : difWord GP half step1 sw tww (s + half + u + quarter)
      = bDif sw tww half ((u + quarter) * step1) (s + u + quarter) := by
    rw [difWord_hi GP half step1 sw tww (s + half + u + quarter) (by rw [hmD]; omega), hmD,
      show half + u + quarter - half = u + quarter by omega,
      show s + half + u + quarter - half = s + u + quarter by omega,
      show s + half + u + quarter = s + u + quarter + half by omega]
    rfl
  rw [difWord_lo GP quarter step2 _ tww (s + half + u) (by rw [hm2]; exact hu), g2,
    show s + half + u + quarter = s + half + u + quarter from rfl, g3]
  rfl

/-- Offset `half + quarter ≤ · < 2·half`: both stages on their difference
branch. -/
theorem fusedD (hhq : half = 2 * quarter) (hu : u < quarter)
    (hsm : s % (2 * half) = 0) :
    difWord GP quarter step2 (difWord GP half step1 sw tww) tww
        (s + half + quarter + u)
      = f3 sw tww half quarter step1 step2 s u := by
  have hsh : s % half = 0 := half_mod hsm
  have hm2 : (s + half + quarter + u) % (2 * quarter) = quarter + u := by
    rw [← hhq, show s + half + quarter + u = (s + half) + (quarter + u) by ring]
    refine add_mod_zero ?_ (by omega)
    rw [Nat.add_mod, hsh, Nat.mod_self]
    simp
  have hmC : (s + half + u) % (2 * half) = half + u := by
    rw [show s + half + u = s + (half + u) by ring]
    exact add_mod_zero hsm (by omega)
  have hmD : (s + half + quarter + u) % (2 * half) = half + quarter + u := by
    rw [show s + half + quarter + u = s + (half + quarter + u) by ring]
    exact add_mod_zero hsm (by omega)
  have g2 : difWord GP half step1 sw tww (s + half + u)
      = bDif sw tww half (u * step1) (s + u) := by
    rw [difWord_hi GP half step1 sw tww (s + half + u) (by rw [hmC]; omega), hmC,
      show half + u - half = u by omega,
      show s + half + u - half = s + u by omega,
      show s + half + u = s + u + half by omega]
    rfl
  have g3 : difWord GP half step1 sw tww (s + half + quarter + u)
      = bDif sw tww half ((u + quarter) * step1) (s + u + quarter) := by
    rw [difWord_hi GP half step1 sw tww (s + half + quarter + u) (by rw [hmD]; omega), hmD,
      show half + quarter + u - half = u + quarter by omega,
      show s + half + quarter + u - half = s + u + quarter by omega,
      show s + half + quarter + u = s + u + quarter + half by omega]
    rfl
  rw [difWord_hi GP quarter step2 _ tww (s + half + quarter + u) (by rw [hm2]; omega), hm2,
    show quarter + u - quarter = u by omega,
    show s + half + quarter + u - quarter = s + half + u by omega, g2, g3]
  rfl

end Block

/-! ## The outer loop and the stage

Unchanged in shape from `GoldStage`'s: the blocks are walked in order, each
one filled by the inner loop, and the frame condition carries the finished
blocks forward. Only the per-index reconciliation is new, and that is the four
lemmas above. -/

/-- The outer loop of the fused stage. -/
theorem gold_dif_stage2_loop0_spec (src dst tw : alloc.vec.Vec Std.U64) (len : Std.Usize)
    (half quarter step1 step2 start : Std.Usize)
    (hsrc : Canon GP src) (hdst : Canon GP dst) (htw : Canon GP tw)
    (hlen : len.val = 2 * half.val) (hhq : half.val = 2 * quarter.val)
    (hqpos : 0 < quarter.val) (hdvd : len.val ∣ N)
    (hs2 : step2.val = 2 * step1.val) (hstep : 0 < step1.val)
    (hebd : half.val * step1.val ≤ N)
    (hstart : start.val ≤ N) (hmod : start.val % len.val = 0)
    (hval : ∀ t, t < start.val →
      wordAt dst t = difWord GP quarter.val step2.val
        (difWord GP half.val step1.val (wordAt src) (wordAt tw)) (wordAt tw) t) :
    ntt.gold_dif_stage2_loop0 src dst len tw ntt.NTT_LEN half quarter step1 step2 start
      ⦃ z => Canon GP z
             ∧ ∀ t, t < N →
                 wordAt z t = difWord GP quarter.val step2.val
                   (difWord GP half.val step1.val (wordAt src) (wordAt tw))
                   (wordAt tw) t ⦄ := by
  rw [ntt.gold_dif_stage2_loop0]
  apply loop.spec_decr_nat (fun s => N - s.2.val)
    (fun s => s.2.val ≤ N ∧ s.2.val % len.val = 0 ∧ Canon GP s.1
      ∧ (∀ t, t < s.2.val →
          wordAt s.1 t = difWord GP quarter.val step2.val
            (difWord GP half.val step1.val (wordAt src) (wordAt tw)) (wordAt tw) t))
  · rintro ⟨d, ss⟩ ⟨hss, hmod1, hcd, hval1⟩
    dsimp only at hss hmod1 hcd hval1
    simp only [ntt.gold_dif_stage2_loop0.body]
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
      have hsm : ss.val % (2 * half.val) = 0 := by rw [← hlen]; exact hmod1
      step with gold_dif_stage2_loop0_loop0_spec src d tw half quarter step1 step2
        ss 0#usize hsrc hcd htw hhq hqpos hblk2 (by simp) hs2 hstep hebd
        (by intro u hu; simp at hu) (by intro u hu; simp at hu)
        (by intro u hu; simp at hu) (by intro u hu; simp at hu)
        as ⟨d1, hc1, hwr0, hwr1, hwr2, hwr3, hfr1⟩
      step as ⟨ss1, hss1⟩
      refine ⟨by omega, ?_, hc1, ?_, by omega⟩
      · rw [hss1, Nat.add_mod_right, hmod1]
      · intro t ht
        rw [hss1] at ht
        rcases Nat.lt_or_ge t ss.val with h1 | h1
        · rw [hfr1 t (Or.inl h1)]
          exact hval1 t h1
        · -- inside the block just written
          rcases Nat.lt_or_ge (t - ss.val) quarter.val with h2 | h2
          · rw [show t = ss.val + (t - ss.val) by omega, hwr0 (t - ss.val) h2]
            exact (fusedA (wordAt src) (wordAt tw) half.val quarter.val step1.val
              step2.val ss.val (t - ss.val) hhq h2 hsm).symm
          · rcases Nat.lt_or_ge (t - ss.val) half.val with h3 | h3
            · rw [show t = ss.val + (t - ss.val - quarter.val) + quarter.val by omega,
                hwr1 (t - ss.val - quarter.val) (by omega)]
              exact (fusedB (wordAt src) (wordAt tw) half.val quarter.val step1.val
                step2.val ss.val (t - ss.val - quarter.val) hhq (by omega) hsm).symm
            · rcases Nat.lt_or_ge (t - ss.val) (half.val + quarter.val) with h4 | h4
              · rw [show t = ss.val + half.val + (t - ss.val - half.val) by omega,
                  hwr2 (t - ss.val - half.val) (by omega)]
                exact (fusedC (wordAt src) (wordAt tw) half.val quarter.val step1.val
                  step2.val ss.val (t - ss.val - half.val) hhq (by omega) hsm).symm
              · rw [show t = ss.val + half.val + quarter.val
                      + (t - ss.val - half.val - quarter.val) by omega,
                  hwr3 (t - ss.val - half.val - quarter.val) (by omega)]
                exact (fusedD (wordAt src) (wordAt tw) half.val quarter.val step1.val
                  step2.val ss.val (t - ss.val - half.val - quarter.val) hhq
                  (by omega) hsm).symm
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ss.val = N := by scalar_tac
      exact ⟨hcd, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · exact ⟨hstart, hmod, hdst, hval⟩

/-- The division facts for a block length `2 ^ (k+2)` dividing `N = 1024`. -/
private theorem fusedParams (k : ℕ) (hk : k < 9) :
    N / 2 ^ (k + 1) = 2 ^ (9 - k) ∧ N / 2 ^ (k + 2) = 2 ^ (8 - k)
      ∧ 2 ^ (k + 2) ∣ N := by
  have hN : N = 2 ^ 10 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [hN, Nat.pow_div (by omega) (by norm_num)]; congr 1; omega
  · rw [hN, Nat.pow_div (by omega) (by norm_num)]; congr 1; omega
  · rw [hN]; exact pow_dvd_pow 2 (by omega)

/-- The fused stage: one pass, two stages' worth of value. -/
theorem gold_dif_stage2_spec (src dst tw : alloc.vec.Vec Std.U64) (len : Std.Usize)
    (k : ℕ) (hk : k < 9) (hlen : len.val = 2 ^ (k + 2))
    (hsrc : Canon GP src) (hdst : Canon GP dst) (htw : Canon GP tw) :
    ntt.gold_dif_stage2 src dst len tw
      ⦃ z => Canon GP z
             ∧ ∀ t, t < N →
                 wordAt z t
                   = difWord GP (2 ^ k) (2 * (N / 2 ^ (k + 1)))
                       (difWord GP (2 ^ (k + 1)) (2 * (N / 2 ^ (k + 2)))
                         (wordAt src) (wordAt tw)) (wordAt tw) t ⦄ := by
  obtain ⟨hd1, hd2, hdvd⟩ := fusedParams k hk
  have hlne : len.val ≠ 0 := by rw [hlen]; positivity
  rw [ntt.gold_dif_stage2]
  step as ⟨hf, hhf⟩
  have hhfv : hf.val = 2 ^ (k + 1) := by
    rw [hhf, hlen, show k + 2 = (k + 1) + 1 by ring, pow_succ]
    omega
  step as ⟨qq, hqq⟩
  have hqqv : qq.val = 2 ^ k := by
    rw [hqq, hlen, show (2 : ℕ) ^ (k + 2) = 2 ^ k * 4 by ring]
    omega
  step as ⟨ii, hii⟩
  have hiiv : ii.val = 2 ^ (8 - k) := by rw [hii, ntt_NTT_LEN_val, hlen, ← hd2]
  -- the two doublings are checked for overflow, so each needs its operand bounded
  have hiile : ii.val ≤ N := by rw [hii, ntt_NTT_LEN_val]; exact Nat.div_le_self _ _
  step as ⟨st1, hst1⟩
  have hst1v : st1.val = 2 * (N / 2 ^ (k + 2)) := by rw [hst1, hiiv, hd2]
  have hst1le : st1.val ≤ 2 * N := by
    rw [hst1v]
    have := Nat.div_le_self N (2 ^ (k + 2))
    omega
  step as ⟨st2, hst2⟩
  have hst2v : st2.val = 2 * (N / 2 ^ (k + 1)) := by
    rw [hst2, hst1v, hd1, hd2, show 9 - k = (8 - k) + 1 by omega, pow_succ]
    ring
  rw [← hst2v, ← hst1v, ← hhfv, ← hqqv]
  refine gold_dif_stage2_loop0_spec src dst tw len hf qq st1 st2 0#usize
    hsrc hdst htw ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by simp) (by simp) (by intro t ht; simp at ht)
  · rw [hlen, hhfv, show k + 2 = (k + 1) + 1 by ring, pow_succ]; ring
  · rw [hhfv, hqqv, pow_succ]; ring
  · rw [hqqv]; positivity
  · rw [hlen]; exact hdvd
  · rw [hst2v, hst1v, hd1, hd2, show 9 - k = (8 - k) + 1 by omega, pow_succ]; ring
  · rw [hst1v, hd2]; positivity
  · rw [hhfv, hst1v, hd2, show (2 : ℕ) ^ (k + 1) * (2 * 2 ^ (8 - k))
        = 2 * (2 ^ (k + 1) * 2 ^ (8 - k)) by ring, ← pow_add,
      show k + 1 + (8 - k) = 9 by omega]
    norm_num

end HachiEquiv.GoldFusedStage
