/-
Card T35's limb layer: `ring::limb_at`, and the identity that makes the split
exact.

The general path used to need three 31-bit lanes, or two with a Garner
reconstruction (card G2). T35 replaces both with **one** Goldilocks lane by
splitting the reusable left operand coefficientwise into two 16-bit limbs,
`a = a₀ + 2¹⁶·a₁`, and running the already-landed bounded convolution twice
against a right operand that is transformed once.

This file is the first half of that argument: what `limb_at` computes, that
its output is bounded by the base, and that the two limbs reconstruct the
coefficient exactly. The bound the lanes need is
`RingFused.offConvSumB_lt` at `B = 2^16`, `C = 32`, proved there.

The reconstruction is exact rather than modular and that matters: the limbs
are natural numbers below `2^16`, the coefficient is a natural number below
`q < 2^32`, and `c = c % 2^16 + 2^16 * (c / 2^16)` is division, not a
congruence. Nothing here is mod `q`.
-/
import RingFused
import GoldDot
import GoldTransform

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.RingLimb

open HachiEquiv.NttArith HachiEquiv.NttStage HachiEquiv.RingFused
open HachiEquiv.GoldArith HachiEquiv.GoldTransform HachiEquiv.GoldDot

/-! ## The arithmetic identity -/

/-- **The limb identity.** A natural number below `d²` is its low limb plus
`d` times its high limb, and both limbs are below `d`. Stated at a general
radix because the two limb widths T35 prototyped (`2^16` twice, `2^11`
thrice) differ only in it. -/
theorem limb_recon (d c : ℕ) (hd : 0 < d) (hc : c < d * d) :
    c % d + d * ((c / d) % d) = c := by
  have hdiv : c / d < d := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hc)
  rw [Nat.mod_eq_of_lt hdiv]
  exact Nat.mod_add_div c d

/-- Both limbs are below the radix. -/
theorem limb_lt (d c : ℕ) (hd : 0 < d) : c % d < d ∧ (c / d) % d < d :=
  ⟨Nat.mod_lt _ hd, Nat.mod_lt _ hd⟩

/-- The instance T35 variant 2A uses: `q < 2^32 = 65536²`, so a reduced
coefficient splits exactly into two 16-bit limbs. -/
theorem limb_recon_q (c : ℕ) (hc : c < HachiEquiv.NttProduct.q) :
    c % 65536 + 65536 * ((c / 65536) % 65536) = c := by
  refine limb_recon 65536 c (by norm_num) ?_
  have : HachiEquiv.NttProduct.q < 65536 * 65536 := by
    simp only [HachiEquiv.NttProduct.q]; norm_num
  omega

/-! ## `ring::limb_at`

`Fp::new` reduces its word; `Raw32` has the same two lines, but it sits above
this file in the import order so they are restated rather than imported. -/

/-- `Fp::new` reduces the word. -/
theorem fp_new_rep' (v : Std.U64) :
    cpoly.field.Fp.new v ⦃ c => c.val = v.val % HachiEquiv.NttProduct.q ⦄ := by
  rw [cpoly.field.Fp.new]
  step as ⟨c, hc⟩
  rw [hc, HachiEquiv.Field.cpoly_P_val]


/-- The inner loop: coefficient `u` of limb `(div, base)` of `a[j]`. -/
theorem limb_at_inner_spec (a : alloc.vec.Vec ring.Rq) (div base : Std.U64)
    (deg : Std.Usize) (j : Std.Usize) (c : alloc.vec.Vec cpoly.field.Fp)
    (u : Std.Usize)
    (hdeg : deg.val = N) (hdiv : 0 < div.val) (hbase : 0 < base.val)
    (hbq : base.val ≤ HachiEquiv.NttProduct.q)
    (hjb : j.val < a.val.length)
    (haj : HachiEquiv.Ring.Wf (a.val.getD j.val (alloc.vec.Vec.new cpoly.field.Fp)))
    (hu : u.val ≤ N) (hlen : c.val.length = u.val)
    (hc0 : ∀ x ∈ c.val, x.val < base.val)
    (hval : ∀ t, t < u.val → HachiEquiv.Ring.wordN c t
      = (HachiEquiv.Ring.wordN
          (a.val.getD j.val (alloc.vec.Vec.new cpoly.field.Fp)) t / div.val) % base.val) :
    ring.limb_at_loop0_loop0 a div base deg j c u
      ⦃ z => z.val.length = N ∧ (∀ x ∈ z.val, x.val < base.val)
             ∧ ∀ t, t < N → HachiEquiv.Ring.wordN z t
                 = (HachiEquiv.Ring.wordN
                     (a.val.getD j.val (alloc.vec.Vec.new cpoly.field.Fp)) t
                       / div.val) % base.val ⦄ := by
  rw [ring.limb_at_loop0_loop0]
  apply loop.spec_decr_nat (fun s => N - s.2.val)
    (fun s => s.2.val ≤ N ∧ s.1.val.length = s.2.val
      ∧ (∀ x ∈ s.1.val, x.val < base.val)
      ∧ ∀ t, t < s.2.val → HachiEquiv.Ring.wordN s.1 t
          = (HachiEquiv.Ring.wordN
              (a.val.getD j.val (alloc.vec.Vec.new cpoly.field.Fp)) t
                / div.val) % base.val)
  · rintro ⟨d1, t1⟩ ⟨ht1, hl1, hb1, hv1⟩
    dsimp only at ht1 hl1 hb1 hv1
    simp only [ring.limb_at_loop0_loop0.body]
    by_cases hlt : t1 < deg
    · rw [if_pos hlt]
      have htlt : t1.val < N := by rw [← hdeg]; scalar_tac
      step as ⟨r, hr⟩
      have hrv : r = a.val.getD j.val (alloc.vec.Vec.new cpoly.field.Fp) := by
        rw [hr, List.getD_eq_getElem _ _ hjb]
      have hrb : t1.val < r.val.length := by rw [hrv, haj.1]; exact htlt
      step as ⟨f, hf⟩
      step with HachiEquiv.Ring.to_u64_id f as ⟨wd, hwd⟩
      have hwdv : wd.val = HachiEquiv.Ring.wordN
          (a.val.getD j.val (alloc.vec.Vec.new cpoly.field.Fp)) t1.val := by
        rw [hwd, hf, ← hrv]
        unfold HachiEquiv.Ring.wordN
        rw [List.getD_eq_getElem _ _ hrb]
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = (HachiEquiv.Ring.wordN
          (a.val.getD j.val (alloc.vec.Vec.new cpoly.field.Fp)) t1.val
            / div.val) % base.val := by rw [hi2, hi1, hwdv]
      have hi2lt : i2.val < base.val := by rw [hi2v]; exact Nat.mod_lt _ hbase
      step with fp_new_rep' i2 as ⟨f1, hf1⟩
      have hf1v : f1.val = i2.val := by
        rw [hf1, Nat.mod_eq_of_lt (by omega)]
      step as ⟨c1, hc1⟩
      step as ⟨t2, ht2⟩
      -- `scalar_tac` scans the whole context here and blows the recursion
      -- limit; the two numeric goals need one equation each.
      have ht2v : t2.val = t1.val + 1 := by clear * - ht2; scalar_tac
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · rw [hc1, ht2, List.length_append, hl1]; simp
      · intro x hx
        rw [hc1] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hb1 x h
        · rw [List.mem_singleton.mp h, hf1v]; exact hi2lt
      · intro t ht
        rw [ht2] at ht
        simp only [HachiEquiv.Ring.wordN] at hv1 ⊢
        rcases Nat.lt_or_ge t t1.val with hlt2 | hge
        · rw [hc1, HachiEquiv.GoldTransform.getD_append_lt' _ _ _ (by omega)]
          exact hv1 t hlt2
        · have hteq : t = d1.val.length := by omega
          rw [hteq, hc1, HachiEquiv.GoldTransform.getD_append_eq', hl1, hf1v, hi2v]
          simp only [HachiEquiv.Ring.wordN]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : t1.val = N := by rw [← hdeg]; scalar_tac
      exact ⟨by rw [hl1, heq], hb1, fun t ht => hv1 t (by rw [heq]; exact ht)⟩
  · exact ⟨hu, hlen, hc0, hval⟩

/-- The outer loop: one limb per entry. -/
theorem limb_at_outer_spec (a : alloc.vec.Vec ring.Rq) (n : Std.Usize)
    (div base : Std.U64) (deg : Std.Usize) (out : alloc.vec.Vec ring.Rq)
    (j : Std.Usize)
    (hdeg : deg.val = N) (hdiv : 0 < div.val) (hbase : 0 < base.val)
    (hbq : base.val ≤ HachiEquiv.NttProduct.q)
    (hna : n.val ≤ a.val.length)
    (haw : ∀ u, u < n.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hj : j.val ≤ n.val) (hlen : out.val.length = j.val)
    (hwf : ∀ x ∈ out.val, HachiEquiv.Ring.Wf x)
    (hbd : ∀ x ∈ out.val, BoundedWf base.val x)
    (hval : ∀ i, i < j.val → ∀ t, t < N →
      HachiEquiv.Ring.wordN (out.val.getD i (alloc.vec.Vec.new cpoly.field.Fp)) t
        = (HachiEquiv.Ring.wordN
            (a.val.getD i (alloc.vec.Vec.new cpoly.field.Fp)) t / div.val) % base.val) :
    ring.limb_at_loop0 a n div base deg out j
      ⦃ z => z.val.length = n.val
             ∧ (∀ x ∈ z.val, HachiEquiv.Ring.Wf x)
             ∧ (∀ x ∈ z.val, BoundedWf base.val x)
             ∧ ∀ i, i < n.val → ∀ t, t < N →
                 HachiEquiv.Ring.wordN (z.val.getD i (alloc.vec.Vec.new cpoly.field.Fp)) t
                   = (HachiEquiv.Ring.wordN
                       (a.val.getD i (alloc.vec.Vec.new cpoly.field.Fp)) t
                         / div.val) % base.val ⦄ := by
  rw [ring.limb_at_loop0]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val
      ∧ (∀ x ∈ s.1.val, HachiEquiv.Ring.Wf x)
      ∧ (∀ x ∈ s.1.val, BoundedWf base.val x)
      ∧ ∀ i, i < s.2.val → ∀ t, t < N →
          HachiEquiv.Ring.wordN (s.1.val.getD i (alloc.vec.Vec.new cpoly.field.Fp)) t
            = (HachiEquiv.Ring.wordN
                (a.val.getD i (alloc.vec.Vec.new cpoly.field.Fp)) t / div.val) % base.val)
  · rintro ⟨o1, j1⟩ ⟨hj1, hl1, hw1, hb1, hv1⟩
    dsimp only at hj1 hl1 hw1 hb1 hv1
    simp only [ring.limb_at_loop0.body]
    by_cases hlt : j1 < n
    · rw [if_pos hlt]
      have hj1lt : j1.val < n.val := by clear * - hlt; scalar_tac
      have hjb : j1.val < a.val.length := by omega
      simp only [alloc.vec.Vec.with_capacity]
      step with limb_at_inner_spec a div base deg j1 (alloc.vec.Vec.new cpoly.field.Fp)
        0#usize hdeg hdiv hbase hbq hjb (haw j1.val hj1lt) (by simp) (by simp)
        (by intro x hx; simp at hx) (by intro t ht; simp at ht)
        as ⟨c1, hc1l, hc1b, hc1v⟩
      step as ⟨o2, ho2⟩
      step as ⟨j2, hj2⟩
      have hj2v : j2.val = j1.val + 1 := by clear * - hj2; scalar_tac
      have hWc1 : HachiEquiv.Ring.Wf c1 :=
        ⟨hc1l, fun x hx => lt_of_lt_of_le (hc1b x hx) hbq⟩
      have hBc1 : BoundedWf base.val c1 := by
        intro t
        unfold HachiEquiv.Ring.wordN
        by_cases ht : t < c1.val.length
        · rw [List.getD_eq_getElem _ _ ht]; exact hc1b _ (List.getElem_mem ht)
        · rw [List.getD_eq_default _ _ (by omega)]
          simpa using hbase
      refine ⟨by omega, ?_, ?_, ?_, ?_, by omega⟩
      · rw [ho2, hj2v, List.length_append, hl1]; simp
      · intro x hx
        rw [ho2] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hw1 x h
        · rw [List.mem_singleton.mp h]; exact hWc1
      · intro x hx
        rw [ho2] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hb1 x h
        · rw [List.mem_singleton.mp h]; exact hBc1
      · intro i hi t ht
        rw [hj2v] at hi
        rcases Nat.lt_or_ge i j1.val with hilt | hige
        · rw [ho2, HachiEquiv.GoldTransform.getD_append_lt' _ _ _ (by omega)]
          exact hv1 i hilt t ht
        · have hieq : i = o1.val.length := by omega
          rw [hieq, ho2, HachiEquiv.GoldTransform.getD_append_eq', hl1]
          exact hc1v t ht
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : j1.val = n.val := by clear * - hlt hj1; scalar_tac
      exact ⟨by rw [hl1, heq], hw1, hb1,
        fun i hi t ht => hv1 i (by rw [heq]; exact hi) t ht⟩
  · exact ⟨hj, hlen, hwf, hbd, hval⟩

/-- **`limb_at`**: one limb of every entry, bounded by the base and reading
the digit the division picks out. -/
theorem limb_at_spec (a : alloc.vec.Vec ring.Rq) (n : Std.Usize) (div base : Std.U64)
    (hdiv : 0 < div.val) (hbase : 0 < base.val)
    (hbq : base.val ≤ HachiEquiv.NttProduct.q)
    (hna : n.val ≤ a.val.length)
    (haw : ∀ u, u < n.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))) :
    ring.limb_at a n div base
      ⦃ z => z.val.length = n.val
             ∧ (∀ x ∈ z.val, HachiEquiv.Ring.Wf x)
             ∧ (∀ x ∈ z.val, BoundedWf base.val x)
             ∧ ∀ i, i < n.val → ∀ t, t < N →
                 HachiEquiv.Ring.wordN (z.val.getD i (alloc.vec.Vec.new cpoly.field.Fp)) t
                   = (HachiEquiv.Ring.wordN
                       (a.val.getD i (alloc.vec.Vec.new cpoly.field.Fp)) t
                         / div.val) % base.val ⦄ := by
  rw [ring.limb_at]
  simp only [alloc.vec.Vec.with_capacity]
  exact limb_at_outer_spec a n div base params.RING_DEGREE
    (alloc.vec.Vec.new ring.Rq) 0#usize HachiEquiv.Ring.params_RING_DEGREE_val hdiv hbase hbq hna haw
    (by simp) (by simp) (by intro x hx; simp at hx) (by intro x hx; simp at hx)
    (by intro i hi; simp at hi)

/-! ## Linearity of the convolution over the split

`negConv` reads its left operand only through `coeffK`, so it is additive and
scalar-homogeneous in it. That is all card T35's reconstruction needs: the two
lanes compute `negConv a₀ b` and `negConv a₁ b`, and the recombination
`r₀ + 2¹⁶·r₁` is this lemma read right to left. -/

/-- The convolution is linear in its **left** operand, coefficientwise. -/
theorem negConv_split (a a0 a1 b : ring.Rq) (d : ℕ)
    (h : ∀ t, HachiEquiv.Ring.coeffK a t
      = HachiEquiv.Ring.coeffK a0 t + (d : ZMod HachiEquiv.NttProduct.q)
          * HachiEquiv.Ring.coeffK a1 t) (k : ℕ) :
    HachiEquiv.Ring.negConv a b k
      = HachiEquiv.Ring.negConv a0 b k
        + (d : ZMod HachiEquiv.NttProduct.q) * HachiEquiv.Ring.negConv a1 b k := by
  simp only [HachiEquiv.Ring.negConv]
  have hpos : ∀ m : ℕ, (∑ p ∈ Finset.antidiagonal m,
        HachiEquiv.Ring.coeffK a p.1 * HachiEquiv.Ring.coeffK b p.2)
      = (∑ p ∈ Finset.antidiagonal m,
          HachiEquiv.Ring.coeffK a0 p.1 * HachiEquiv.Ring.coeffK b p.2)
        + (d : ZMod HachiEquiv.NttProduct.q)
          * ∑ p ∈ Finset.antidiagonal m,
              HachiEquiv.Ring.coeffK a1 p.1 * HachiEquiv.Ring.coeffK b p.2 := by
    intro m
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [h p.1]
    ring
  rw [hpos k, hpos (N + k)]
  ring

/-- The two limbs of a reduced element reconstruct its coefficients in
`ZMod q`. This is [`limb_recon_q`] cast, and the one place where layer 2's
arithmetic meets the field. -/
theorem coeffK_of_limbs (a a0 a1 : ring.Rq) (ha : HachiEquiv.Ring.Wf a)
    (hl0 : a0.val.length = N) (hl1 : a1.val.length = N)
    (h0 : ∀ t, t < N → HachiEquiv.Ring.wordN a0 t = HachiEquiv.Ring.wordN a t % 65536)
    (h1 : ∀ t, t < N → HachiEquiv.Ring.wordN a1 t
      = (HachiEquiv.Ring.wordN a t / 65536) % 65536) (t : ℕ) :
    HachiEquiv.Ring.coeffK a t
      = HachiEquiv.Ring.coeffK a0 t
        + ((65536 : ℕ) : ZMod HachiEquiv.NttProduct.q) * HachiEquiv.Ring.coeffK a1 t := by
  rcases Nat.lt_or_ge t N with ht | ht
  · have hwlt : HachiEquiv.Ring.wordN a t < HachiEquiv.NttProduct.q := by
      unfold HachiEquiv.Ring.wordN
      rw [List.getD_eq_getElem _ _ (by rw [ha.1]; exact ht)]
      exact ha.2 _ (List.getElem_mem (by rw [ha.1]; exact ht))
    have hrec := limb_recon_q (HachiEquiv.Ring.wordN a t) hwlt
    simp only [HachiEquiv.Ring.coeffK_eq_cast_wordN, h0 t ht, h1 t ht]
    conv_lhs => rw [← hrec]
    push_cast
    ring
  · -- past the end every reader is the default, and `0 = 0 + d * 0`
    have hz : ∀ (v : ring.Rq), v.val.length = N → HachiEquiv.Ring.coeffK v t = 0 := by
      intro v hv
      simp only [HachiEquiv.Ring.coeffK, HachiEquiv.Field.toK]
      rw [List.getD_eq_default _ _ (by omega)]
      simp [cpoly.field.Fp.ZERO]
    rw [hz a ha.1, hz a0 hl0, hz a1 hl1]
    ring

/-! ## Card T52a: the fused term on the limb path

`dot_prep_chunk_limbs2`'s term runs as `gold_dot_one_fused_limbs2`, which is
`gold_dot_one_fused` (card T37) line for line with the last pass replaced by
`gold_dif_stage2_mac2`: `gold_dif_stage2_mac` (T49a's peel included) with each
accumulate written twice, once per `(acc, pf)` pair. The two accumulators
never read each other, so each accumulator's invariant is stated once
([`MacBlk`] inside a block, [`MacOut`] across blocks), its per-group advance
proved once ([`MacBlk_step`], [`MacOut_next`]), and the two-table loops apply
them twice. The peeled group `j = 0` is [`MacBlk_step`] at `j = 0` from
[`MacOut_blk0`], and the middle loop is `gold_dot_one_fused_loop` itself
([`gold_dot_one_fused_limbs2_loop_eq`]), so its spec is reused as it stands. -/

section T52a

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

open HachiEquiv.GoldStage HachiEquiv.GoldFusedStage HachiEquiv.GoldFusedBoundary

/-- One accumulator's state inside a block of the fused MAC stage. -/
def MacBlk (src tw pfwd acc0 accE : alloc.vec.Vec Std.U64)
    (base half quarter step1 step2 start j : ℕ) (d : alloc.vec.Vec Std.U64) : Prop :=
  Canon GP d
  ∧ (∀ u, u < j → wordAt d (start + u)
      = macAt (wordAt acc0) (pfW pfwd base) (start + u) (f0 (wordAt src) half quarter start u))
  ∧ (∀ u, u < j → wordAt d (start + u + quarter)
      = macAt (wordAt acc0) (pfW pfwd base) (start + u + quarter)
          (f1 (wordAt src) (wordAt tw) half quarter step2 start u))
  ∧ (∀ u, u < j → wordAt d (start + half + u)
      = macAt (wordAt acc0) (pfW pfwd base) (start + half + u)
          (f2 (wordAt src) (wordAt tw) half quarter step1 start u))
  ∧ (∀ u, u < j → wordAt d (start + half + quarter + u)
      = macAt (wordAt acc0) (pfW pfwd base) (start + half + quarter + u)
          (f3 (wordAt src) (wordAt tw) half quarter step1 step2 start u))
  ∧ (∀ u, j ≤ u → u < quarter → wordAt d (start + u) = wordAt acc0 (start + u))
  ∧ (∀ u, j ≤ u → u < quarter →
      wordAt d (start + u + quarter) = wordAt acc0 (start + u + quarter))
  ∧ (∀ u, j ≤ u → u < quarter →
      wordAt d (start + half + u) = wordAt acc0 (start + half + u))
  ∧ (∀ u, j ≤ u → u < quarter →
      wordAt d (start + half + quarter + u) = wordAt acc0 (start + half + quarter + u))
  ∧ (∀ k, (k < start ∨ start + 2 * half ≤ k) → wordAt d k = wordAt accE k)

/-- One group's four read-modify-writes advance [`MacBlk`] by one. -/
theorem MacBlk_step {src tw pfwd acc0 accE d : alloc.vec.Vec Std.U64}
    {base half quarter step1 step2 start jj : ℕ} {i o1i o2i o3i : Std.Usize}
    {x0 x1 x2 x3 : Std.U64}
    (hI : MacBlk src tw pfwd acc0 accE base half quarter step1 step2 start jj d)
    (hhq : half = 2 * quarter) (hjlt : jj < quarter) (hblk : start + 2 * half ≤ N)
    (p0 : i.val = start + jj) (p1 : o1i.val = start + jj + quarter)
    (p2 : o2i.val = start + half + jj) (p3 : o3i.val = start + half + quarter + jj)
    (hx0 : x0.val = macAt (wordAt acc0) (pfW pfwd base) (start + jj)
      (f0 (wordAt src) half quarter start jj))
    (hx1 : x1.val = macAt (wordAt acc0) (pfW pfwd base) (start + jj + quarter)
      (f1 (wordAt src) (wordAt tw) half quarter step2 start jj))
    (hx2 : x2.val = macAt (wordAt acc0) (pfW pfwd base) (start + half + jj)
      (f2 (wordAt src) (wordAt tw) half quarter step1 start jj))
    (hx3 : x3.val = macAt (wordAt acc0) (pfW pfwd base) (start + half + quarter + jj)
      (f3 (wordAt src) (wordAt tw) half quarter step1 step2 start jj)) :
    MacBlk src tw pfwd acc0 accE base half quarter step1 step2 start (jj + 1)
      ((((d.set i x0).set o1i x1).set o2i x2).set o3i x3) := by
  obtain ⟨hcd, hv0, hv1, hv2, hv3, hq0, hq1, hq2, hq3, hfr⟩ := hI
  have hc1 : Canon GP (d.set i x0) := Canon_set hcd (by rw [hx0]; exact macAt_lt _ _ _ _)
  have hc2 : Canon GP ((d.set i x0).set o1i x1) :=
    Canon_set hc1 (by rw [hx1]; exact macAt_lt _ _ _ _)
  have hc3 : Canon GP (((d.set i x0).set o1i x1).set o2i x2) :=
    Canon_set hc2 (by rw [hx2]; exact macAt_lt _ _ _ _)
  have hc4 : Canon GP ((((d.set i x0).set o1i x1).set o2i x2).set o3i x3) :=
    Canon_set hc3 (by rw [hx3]; exact macAt_lt _ _ _ _)
  have hidb : i.val < d.val.length := by rw [hcd.1, p0]; omega
  have ho1b : o1i.val < (d.set i x0).val.length := by rw [hc1.1, p1]; omega
  have ho2b : o2i.val < ((d.set i x0).set o1i x1).val.length := by rw [hc2.1, p2]; omega
  have ho3b : o3i.val < (((d.set i x0).set o1i x1).set o2i x2).val.length := by
    rw [hc3.1, p3]; omega
  have hqpos : 0 < quarter := by omega
  have hdisA : ∀ u, u ≠ jj → u < quarter →
      (start + u ≠ i.val ∧ start + u ≠ o1i.val
        ∧ start + u ≠ o2i.val ∧ start + u ≠ o3i.val)
      ∧ (start + u + quarter ≠ i.val ∧ start + u + quarter ≠ o1i.val
        ∧ start + u + quarter ≠ o2i.val ∧ start + u + quarter ≠ o3i.val)
      ∧ (start + half + u ≠ i.val ∧ start + half + u ≠ o1i.val
        ∧ start + half + u ≠ o2i.val ∧ start + half + u ≠ o3i.val)
      ∧ (start + half + quarter + u ≠ i.val ∧ start + half + quarter + u ≠ o1i.val
        ∧ start + half + quarter + u ≠ o2i.val ∧ start + half + quarter + u ≠ o3i.val) := by
    clear * - p0 p1 p2 p3 hjlt hhq hqpos
    intro u hu hu2
    refine ⟨⟨by omega, by omega, by omega, by omega⟩,
      ⟨by omega, by omega, by omega, by omega⟩,
      ⟨by omega, by omega, by omega, by omega⟩,
      ⟨by omega, by omega, by omega, by omega⟩⟩
  have hdisF : ∀ k, (k < start ∨ start + 2 * half ≤ k) →
      k ≠ i.val ∧ k ≠ o1i.val ∧ k ≠ o2i.val ∧ k ≠ o3i.val := by
    clear * - p0 p1 p2 p3 hjlt hhq hqpos
    intro k hk
    exact ⟨by omega, by omega, by omega, by omega⟩
  have hself :
      (start + jj ≠ o1i.val ∧ start + jj ≠ o2i.val ∧ start + jj ≠ o3i.val)
      ∧ (start + jj + quarter ≠ o2i.val ∧ start + jj + quarter ≠ o3i.val)
      ∧ start + half + jj ≠ o3i.val := by
    clear * - p0 p1 p2 p3 hjlt hhq hqpos
    exact ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, by omega⟩, by omega⟩
  refine ⟨hc4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rcases Nat.lt_or_ge u jj with hlt2 | hge
    · obtain ⟨⟨m0, m1, m2, m3⟩, -, -, -⟩ := hdisA u (by omega) (by omega)
      rw [wordAt_set_ne m3, wordAt_set_ne m2, wordAt_set_ne m1, wordAt_set_ne m0]
      exact hv0 u hlt2
    · have heu : u = jj := by clear * - hu hge; omega
      subst heu
      obtain ⟨⟨q1, q2, q3⟩, -, -⟩ := hself
      rw [wordAt_set_ne q3, wordAt_set_ne q2, wordAt_set_ne q1]
      conv_lhs => rw [← p0]
      rw [wordAt_set_eq hidb]
      exact hx0
  · intro u hu
    rcases Nat.lt_or_ge u jj with hlt2 | hge
    · obtain ⟨-, ⟨m0, m1, m2, m3⟩, -, -⟩ := hdisA u (by omega) (by omega)
      rw [wordAt_set_ne m3, wordAt_set_ne m2, wordAt_set_ne m1, wordAt_set_ne m0]
      exact hv1 u hlt2
    · have heu : u = jj := by clear * - hu hge; omega
      subst heu
      obtain ⟨-, ⟨q2, q3⟩, -⟩ := hself
      rw [wordAt_set_ne q3, wordAt_set_ne q2]
      conv_lhs => rw [← p1]
      rw [wordAt_set_eq ho1b]
      exact hx1
  · intro u hu
    rcases Nat.lt_or_ge u jj with hlt2 | hge
    · obtain ⟨-, -, ⟨m0, m1, m2, m3⟩, -⟩ := hdisA u (by omega) (by omega)
      rw [wordAt_set_ne m3, wordAt_set_ne m2, wordAt_set_ne m1, wordAt_set_ne m0]
      exact hv2 u hlt2
    · have heu : u = jj := by clear * - hu hge; omega
      subst heu
      obtain ⟨-, -, q3⟩ := hself
      rw [wordAt_set_ne q3]
      conv_lhs => rw [← p2]
      rw [wordAt_set_eq ho2b]
      exact hx2
  · intro u hu
    rcases Nat.lt_or_ge u jj with hlt2 | hge
    · obtain ⟨-, -, -, ⟨m0, m1, m2, m3⟩⟩ := hdisA u (by omega) (by omega)
      rw [wordAt_set_ne m3, wordAt_set_ne m2, wordAt_set_ne m1, wordAt_set_ne m0]
      exact hv3 u hlt2
    · have heu : u = jj := by clear * - hu hge; omega
      subst heu
      conv_lhs => rw [← p3]
      rw [wordAt_set_eq ho3b]
      exact hx3
  · intro u hu hu2
    obtain ⟨⟨m0, m1, m2, m3⟩, -, -, -⟩ := hdisA u (by omega) hu2
    rw [wordAt_set_ne m3, wordAt_set_ne m2, wordAt_set_ne m1, wordAt_set_ne m0]
    exact hq0 u (by omega) hu2
  · intro u hu hu2
    obtain ⟨-, ⟨m0, m1, m2, m3⟩, -, -⟩ := hdisA u (by omega) hu2
    rw [wordAt_set_ne m3, wordAt_set_ne m2, wordAt_set_ne m1, wordAt_set_ne m0]
    exact hq1 u (by omega) hu2
  · intro u hu hu2
    obtain ⟨-, -, ⟨m0, m1, m2, m3⟩, -⟩ := hdisA u (by omega) hu2
    rw [wordAt_set_ne m3, wordAt_set_ne m2, wordAt_set_ne m1, wordAt_set_ne m0]
    exact hq2 u (by omega) hu2
  · intro u hu hu2
    obtain ⟨-, -, -, ⟨m0, m1, m2, m3⟩⟩ := hdisA u (by omega) hu2
    rw [wordAt_set_ne m3, wordAt_set_ne m2, wordAt_set_ne m1, wordAt_set_ne m0]
    exact hq3 u (by omega) hu2
  · intro k hk
    obtain ⟨m0, m1, m2, m3⟩ := hdisF k hk
    rw [wordAt_set_ne m3, wordAt_set_ne m2, wordAt_set_ne m1, wordAt_set_ne m0]
    exact hfr k hk

/-- A block state is its own frame. -/
theorem MacBlk_self {src tw pfwd acc0 accE d : alloc.vec.Vec Std.U64}
    {base half quarter step1 step2 start j : ℕ}
    (hI : MacBlk src tw pfwd acc0 accE base half quarter step1 step2 start j d) :
    MacBlk src tw pfwd acc0 d base half quarter step1 step2 start j d := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hI
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, fun _ _ => rfl⟩

/-- One accumulator's state in the outer loop of the fused MAC stage. -/
def MacOut (src tw pfwd acc0 : alloc.vec.Vec Std.U64)
    (base half quarter step1 step2 s : ℕ) (d : alloc.vec.Vec Std.U64) : Prop :=
  Canon GP d
  ∧ (∀ t, t < s → wordAt d t = macAt (wordAt acc0) (pfW pfwd base) t
      (stage2W (wordAt src) (wordAt tw) half quarter step1 step2 t))
  ∧ (∀ t, s ≤ t → wordAt d t = wordAt acc0 t)

/-- At a block boundary nothing of the block is written yet. -/
theorem MacOut_blk0 {src tw pfwd acc0 d : alloc.vec.Vec Std.U64}
    {base half quarter step1 step2 ss : ℕ}
    (hO : MacOut src tw pfwd acc0 base half quarter step1 step2 ss d) :
    MacBlk src tw pfwd acc0 d base half quarter step1 step2 ss 0 d := by
  obtain ⟨hc, -, hp⟩ := hO
  refine ⟨hc, fun u hu => absurd hu (Nat.not_lt_zero _), fun u hu => absurd hu (Nat.not_lt_zero _),
    fun u hu => absurd hu (Nat.not_lt_zero _), fun u hu => absurd hu (Nat.not_lt_zero _),
    fun u _ _ => hp _ (by omega), fun u _ _ => hp _ (by omega),
    fun u _ _ => hp _ (by omega), fun u _ _ => hp _ (by omega), fun _ _ => rfl⟩

/-- A finished block advances the outer invariant by one block. -/
theorem MacOut_next {src tw pfwd acc0 accE d dn : alloc.vec.Vec Std.U64}
    {base half quarter step1 step2 ss : ℕ}
    (hO : MacOut src tw pfwd acc0 base half quarter step1 step2 ss d)
    (hB : MacBlk src tw pfwd acc0 accE base half quarter step1 step2 ss quarter dn)
    (hE : ∀ k, (k < ss ∨ ss + 2 * half ≤ k) → wordAt accE k = wordAt d k)
    (hhq : half = 2 * quarter) (hsm : ss % (2 * half) = 0) :
    MacOut src tw pfwd acc0 base half quarter step1 step2 (ss + 2 * half) dn := by
  obtain ⟨-, hval1, hfr1⟩ := hO
  obtain ⟨hcn, hwr0, hwr1, hwr2, hwr3, -, -, -, -, hfr2⟩ := hB
  have hfr3 : ∀ k, (k < ss ∨ ss + 2 * half ≤ k) → wordAt dn k = wordAt d k := by
    intro k hk
    rw [hfr2 k hk, hE k hk]
  refine ⟨hcn, ?_, ?_⟩
  · intro t ht
    rcases Nat.lt_or_ge t ss with h1 | h1
    · rw [hfr3 t (Or.inl h1)]
      exact hval1 t h1
    · simp only [stage2W]
      rcases Nat.lt_or_ge (t - ss) quarter with h2 | h2
      · rw [show t = ss + (t - ss) by omega, hwr0 (t - ss) h2]
        congr 1
        exact (fusedA (wordAt src) (wordAt tw) half quarter step1
            step2 ss (t - ss) hhq h2 hsm).symm
      · rcases Nat.lt_or_ge (t - ss) half with h3 | h3
        · rw [show t = ss + (t - ss - quarter) + quarter by omega,
            hwr1 (t - ss - quarter) (by omega)]
          congr 1
          exact (fusedB (wordAt src) (wordAt tw) half quarter step1
              step2 ss (t - ss - quarter) hhq (by omega) hsm).symm
        · rcases Nat.lt_or_ge (t - ss) (half + quarter) with h4 | h4
          · rw [show t = ss + half + (t - ss - half) by omega,
              hwr2 (t - ss - half) (by omega)]
            congr 1
            exact (fusedC (wordAt src) (wordAt tw) half quarter step1
                step2 ss (t - ss - half) hhq (by omega) hsm).symm
          · rw [show t = ss + half + quarter + (t - ss - half - quarter) by omega,
              hwr3 (t - ss - half - quarter) (by omega)]
            congr 1
            exact (fusedD (wordAt src) (wordAt tw) half quarter step1
                step2 ss (t - ss - half - quarter) hhq (by omega) hsm).symm
  · intro t ht
    rw [hfr3 t (Or.inr ht)]
    exact hfr1 t (by omega)


/-- The inner loop of [`ring.gold_dif_stage2_mac2`]: [`mac_loop0_loop0_spec`]
with each accumulate written twice. -/
theorem mac2_loop0_loop0_spec (src a0 a1 acc0 acc1 tw pf0 pf1 : alloc.vec.Vec Std.U64)
    (base half quarter step1 step2 start j : Std.Usize)
    (hsrc : Canon GP src) (htw : Canon GP tw)
    (hb0 : base.val + N ≤ pf0.val.length) (hb1 : base.val + N ≤ pf1.val.length)
    (hhq : half.val = 2 * quarter.val) (hqpos : 0 < quarter.val)
    (hblk : start.val + 2 * half.val ≤ N) (hj : j.val ≤ quarter.val)
    (hs2 : step2.val = 2 * step1.val) (hstep : 0 < step1.val)
    (hebd : half.val * step1.val ≤ N)
    (hI0 : MacBlk src tw pf0 a0 acc0 base.val half.val quarter.val step1.val step2.val
      start.val j.val acc0)
    (hI1 : MacBlk src tw pf1 a1 acc1 base.val half.val quarter.val step1.val step2.val
      start.val j.val acc1) :
    ring.gold_dif_stage2_mac2_loop0_loop0 src acc0 acc1 tw pf0 pf1 base half quarter step1
        step2 start j
      ⦃ z => MacBlk src tw pf0 a0 acc0 base.val half.val quarter.val step1.val step2.val
               start.val quarter.val z.1
             ∧ MacBlk src tw pf1 a1 acc1 base.val half.val quarter.val step1.val step2.val
               start.val quarter.val z.2 ⦄ := by
  rw [ring.gold_dif_stage2_mac2_loop0_loop0]
  apply loop.spec_decr_nat (fun s => quarter.val - s.2.2.val)
    (fun s => s.2.2.val ≤ quarter.val
      ∧ MacBlk src tw pf0 a0 acc0 base.val half.val quarter.val step1.val step2.val
          start.val s.2.2.val s.1
      ∧ MacBlk src tw pf1 a1 acc1 base.val half.val quarter.val step1.val step2.val
          start.val s.2.2.val s.2.1)
  · rintro ⟨d, e, jj⟩ ⟨hjj, hB0, hB1⟩
    dsimp only at hjj hB0 hB1
    simp only [ring.gold_dif_stage2_mac2_loop0_loop0.body]
    by_cases hlt : jj < quarter
    · rw [if_pos hlt]
      have hjlt : jj.val < quarter.val := by scalar_tac
      obtain ⟨hcd, -, -, -, -, hq0, hq1, hq2, hq3, -⟩ := id hB0
      obtain ⟨hce, -, -, -, -, hr0, hr1, hr2, hr3, -⟩ := id hB1
      have hsl : src.val.length = N := hsrc.1
      have hdl : d.val.length = N := hcd.1
      have hel : e.val.length = N := hce.1
      have htl : tw.val.length = N := htw.1
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
      -- the four reads of the source
      step as ⟨i, hi⟩
      have hib : i.val < src.val.length := by rw [hsl, hi]; omega
      step as ⟨a0', ha0⟩
      have ha0v : a0'.val = wordAt src (start.val + jj.val) := by
        rw [ha0, ← wordAt_of_lt (v := src) (t := i.val) hib, hi]
      step as ⟨i1, hi1⟩
      have hi1b : i1.val < src.val.length := by rw [hsl, hi1, hi]; omega
      step as ⟨a1', ha1⟩
      have ha1v : a1'.val = wordAt src (start.val + jj.val + quarter.val) := by
        rw [ha1, ← wordAt_of_lt (v := src) (t := i1.val) hi1b, hi1, hi]
      step as ⟨i2, hi2⟩
      have hi2b : i2.val < src.val.length := by rw [hsl, hi2, hi]; omega
      step as ⟨a2', ha2⟩
      have ha2v : a2'.val = wordAt src (start.val + jj.val + half.val) := by
        rw [ha2, ← wordAt_of_lt (v := src) (t := i2.val) hi2b, hi2, hi]
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      have hi4b : i4.val < src.val.length := by rw [hsl, hi4, hi3, hi]; omega
      step as ⟨a3', ha3⟩
      have ha3v : a3'.val = wordAt src (start.val + jj.val + quarter.val + half.val) := by
        rw [ha3, ← wordAt_of_lt (v := src) (t := i4.val) hi4b, hi4, hi3, hi]
        congr 1
        omega
      have h0lt : a0'.val < GP := by rw [ha0v]; exact wordAt_lt hsrc GoldFusedBoundary.GP_pos _
      have h1lt : a1'.val < GP := by rw [ha1v]; exact wordAt_lt hsrc GoldFusedBoundary.GP_pos _
      have h2lt : a2'.val < GP := by rw [ha2v]; exact wordAt_lt hsrc GoldFusedBoundary.GP_pos _
      have h3lt : a3'.val < GP := by rw [ha3v]; exact wordAt_lt hsrc GoldFusedBoundary.GP_pos _
      -- the first stage's four values
      step with gold_add_spec a0' a2' h0lt h2lt as ⟨b0, hb0v, hb0lt⟩
      step with gold_add_spec a1' a3' h1lt h3lt as ⟨b1, hb1v, hb1lt⟩
      step with gold_sub_spec a0' a2' h0lt h2lt as ⟨d0, hd0v, hd0lt⟩
      step as ⟨i5, hi5⟩
      have hi5b : i5.val < tw.val.length := by rw [htl, hi5]; exact hbt1
      step as ⟨t1, ht1⟩
      have ht1v : t1.val = wordAt tw (jj.val * step1.val) := by
        rw [ht1, ← wordAt_of_lt (v := tw) (t := i5.val) hi5b, hi5]
      step with gold_mul_spec d0 t1 as ⟨b2, hb2v, hb2lt⟩
      step with gold_sub_spec a1' a3' h1lt h3lt as ⟨d1, hd1v, hd1lt⟩
      step as ⟨i7, hi7⟩
      step as ⟨i8, hi8⟩
      have hi8b : i8.val < tw.val.length := by rw [htl, hi8, hi7]; exact hbt2
      step as ⟨t2, ht2⟩
      have ht2v : t2.val = wordAt tw ((jj.val + quarter.val) * step1.val) := by
        rw [ht2, ← wordAt_of_lt (v := tw) (t := i8.val) hi8b, hi8, hi7]
      step with gold_mul_spec d1 t2 as ⟨b3, hb3v, hb3lt⟩
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
      have p0 : i.val = start.val + jj.val := hi
      have hdisB :
          (start.val + jj.val ≠ start.val + jj.val + quarter.val
            ∧ start.val + jj.val ≠ start.val + half.val + jj.val
            ∧ start.val + jj.val ≠ start.val + half.val + quarter.val + jj.val)
          ∧ (start.val + jj.val + quarter.val ≠ start.val + half.val + jj.val
            ∧ start.val + jj.val + quarter.val ≠ start.val + half.val + quarter.val + jj.val)
          ∧ start.val + half.val + jj.val ≠ start.val + half.val + quarter.val + jj.val := by
        clear * - hjlt hhq hqpos
        exact ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, by omega⟩, by omega⟩
      obtain ⟨⟨n01, n02, n03⟩, ⟨n12, n13⟩, n23⟩ := hdisB
      /- Write 1, at `start + jj`: limb 0, then limb 1. -/
      step with gold_add_spec b0 b1 hb0lt hb1lt as ⟨v0, hv0v, hv0lt⟩
      have hv0f : v0.val = f0 (wordAt src) half.val quarter.val start.val jj.val := by
        rw [hv0v, hb0f, hb1f]; rfl
      have hidb : i.val < d.val.length := by rw [hdl, hi]; omega
      have hieb : i.val < e.val.length := by rw [hel, hi]; omega
      step as ⟨c0, hc0⟩
      have hc0v : c0.val = wordAt a0 (start.val + jj.val) := by
        rw [hc0, ← wordAt_of_lt (v := d) (t := i.val) hidb, hi]
        exact hq0 jj.val (le_refl _) hjlt
      have hc0lt : c0.val < GP := by
        rw [hc0, ← wordAt_of_lt (v := d) (t := i.val) hidb]
        exact wordAt_lt hcd GoldFusedBoundary.GP_pos _
      step as ⟨k0, hk0⟩
      try (case hmax => scalar_tac)
      have hk0b : k0.val < pf0.val.length := by rw [hk0, hi]; omega
      have hk0b' : k0.val < pf1.val.length := by rw [hk0, hi]; omega
      step as ⟨w0, hw0'⟩
      have hw0v : w0.val = pfW pf0 base.val (start.val + jj.val) := by
        rw [hw0', ← wordAt_of_lt (v := pf0) (t := k0.val) hk0b, hk0, hi]; rfl
      step with gold_mul_spec w0 v0 as ⟨m0, hm0v, hm0lt⟩
      step with gold_add_spec c0 m0 hc0lt hm0lt as ⟨o0, ho0v, ho0lt⟩
      have ho0f : o0.val = macAt (wordAt a0) (pfW pf0 base.val) (start.val + jj.val)
          (f0 (wordAt src) half.val quarter.val start.val jj.val) := by
        rw [ho0v, hm0v, hc0v, hw0v, hv0f]; rfl
      step as ⟨elem, back, helem, hback⟩
      step as ⟨g0, hg0⟩
      have hg0v : g0.val = wordAt a1 (start.val + jj.val) := by
        rw [hg0, ← wordAt_of_lt (v := e) (t := i.val) hieb, hi]
        exact hr0 jj.val (le_refl _) hjlt
      have hg0lt : g0.val < GP := by
        rw [hg0, ← wordAt_of_lt (v := e) (t := i.val) hieb]
        exact wordAt_lt hce GoldFusedBoundary.GP_pos _
      step as ⟨y0, hy0'⟩
      have hy0v : y0.val = pfW pf1 base.val (start.val + jj.val) := by
        rw [hy0', ← wordAt_of_lt (v := pf1) (t := k0.val) hk0b', hk0, hi]; rfl
      step with gold_mul_spec y0 v0 as ⟨n0, hn0v, hn0lt⟩
      step with gold_add_spec g0 n0 hg0lt hn0lt as ⟨r0, hr0v, hr0lt⟩
      have hr0f : r0.val = macAt (wordAt a1) (pfW pf1 base.val) (start.val + jj.val)
          (f0 (wordAt src) half.val quarter.val start.val jj.val) := by
        rw [hr0v, hn0v, hg0v, hy0v, hv0f]; rfl
      step as ⟨elem', back', helem', hback'⟩
      step as ⟨o1i, ho1i⟩
      have p1 : o1i.val = start.val + jj.val + quarter.val := by rw [ho1i, hi]
      step with gold_sub_spec b0 b1 hb0lt hb1lt as ⟨e0, he0v, he0lt⟩
      step as ⟨i15, hi15⟩
      have hi15b : i15.val < tw.val.length := by rw [htl, hi15]; exact hbt3
      step as ⟨t3, ht3⟩
      have ht3v : t3.val = wordAt tw (jj.val * step2.val) := by
        rw [ht3, ← wordAt_of_lt (v := tw) (t := i15.val) hi15b, hi15]
      step with gold_mul_spec e0 t3 as ⟨v1, hv1v, hv1lt⟩
      have hv1f : v1.val
          = f1 (wordAt src) (wordAt tw) half.val quarter.val step2.val start.val jj.val := by
        rw [hv1v, he0v, ht3v, hb0f, hb1f]; rfl
      rw [hback]
      /- Write 2, at `start + jj + quarter`. -/
      have hc1 : Canon GP (d.set i o0) := Canon_set hcd ho0lt
      have ho1b : o1i.val < (d.set i o0).val.length := by rw [hc1.1, p1]; omega
      step as ⟨c1, hc1'⟩
      have hc1v : c1.val = wordAt a0 (start.val + jj.val + quarter.val) := by
        rw [hc1', ← wordAt_of_lt (v := d.set i o0) (t := o1i.val) ho1b, p1,
          wordAt_set_ne (by rw [p0]; exact n01.symm)]
        exact hq1 jj.val (le_refl _) hjlt
      have hc1lt : c1.val < GP := by
        rw [hc1', ← wordAt_of_lt (v := d.set i o0) (t := o1i.val) ho1b]
        exact wordAt_lt hc1 GoldFusedBoundary.GP_pos _
      step as ⟨k1, hk1⟩
      try (case hmax => scalar_tac)
      have hk1b : k1.val < pf0.val.length := by rw [hk1, p1]; omega
      have hk1b' : k1.val < pf1.val.length := by rw [hk1, p1]; omega
      step as ⟨w1, hw1'⟩
      have hw1v : w1.val = pfW pf0 base.val (start.val + jj.val + quarter.val) := by
        rw [hw1', ← wordAt_of_lt (v := pf0) (t := k1.val) hk1b, hk1, p1]; rfl
      step with gold_mul_spec w1 v1 as ⟨m1, hm1v, hm1lt⟩
      step with gold_add_spec c1 m1 hc1lt hm1lt as ⟨o1, ho1v, ho1lt⟩
      have ho1f : o1.val = macAt (wordAt a0) (pfW pf0 base.val)
          (start.val + jj.val + quarter.val)
          (f1 (wordAt src) (wordAt tw) half.val quarter.val step2.val start.val jj.val) := by
        rw [ho1v, hm1v, hc1v, hw1v, hv1f]; rfl
      step as ⟨elem1, back1, helem1, hback1⟩
      rw [hback']
      have he1 : Canon GP (e.set i r0) := Canon_set hce hr0lt
      have ho1b' : o1i.val < (e.set i r0).val.length := by rw [he1.1, p1]; omega
      step as ⟨g1, hg1⟩
      have hg1v : g1.val = wordAt a1 (start.val + jj.val + quarter.val) := by
        rw [hg1, ← wordAt_of_lt (v := e.set i r0) (t := o1i.val) ho1b', p1,
          wordAt_set_ne (by rw [p0]; exact n01.symm)]
        exact hr1 jj.val (le_refl _) hjlt
      have hg1lt : g1.val < GP := by
        rw [hg1, ← wordAt_of_lt (v := e.set i r0) (t := o1i.val) ho1b']
        exact wordAt_lt he1 GoldFusedBoundary.GP_pos _
      step as ⟨y1, hy1'⟩
      have hy1v : y1.val = pfW pf1 base.val (start.val + jj.val + quarter.val) := by
        rw [hy1', ← wordAt_of_lt (v := pf1) (t := k1.val) hk1b', hk1, p1]; rfl
      step with gold_mul_spec y1 v1 as ⟨n1, hn1v, hn1lt⟩
      step with gold_add_spec g1 n1 hg1lt hn1lt as ⟨r1, hr1v, hr1lt⟩
      have hr1f : r1.val = macAt (wordAt a1) (pfW pf1 base.val)
          (start.val + jj.val + quarter.val)
          (f1 (wordAt src) (wordAt tw) half.val quarter.val step2.val start.val jj.val) := by
        rw [hr1v, hn1v, hg1v, hy1v, hv1f]; rfl
      step as ⟨elem1', back1', helem1', hback1'⟩
      step as ⟨i22, hi22⟩
      try (case hmax => scalar_tac)
      step as ⟨o2i, ho2i⟩
      try (case hmax => scalar_tac)
      have p2 : o2i.val = start.val + half.val + jj.val := by rw [ho2i, hi22]
      step with gold_add_spec b2 b3 hb2lt hb3lt as ⟨v2, hv2v, hv2lt⟩
      have hv2f : v2.val
          = f2 (wordAt src) (wordAt tw) half.val quarter.val step1.val start.val jj.val := by
        rw [hv2v, hb2f, hb3f]; rfl
      rw [hback1]
      /- Write 3, at `start + half + jj`. -/
      have hc2 : Canon GP ((d.set i o0).set o1i o1) := Canon_set hc1 ho1lt
      have ho2b : o2i.val < ((d.set i o0).set o1i o1).val.length := by rw [hc2.1, p2]; omega
      step as ⟨c2, hc2'⟩
      have hc2v : c2.val = wordAt a0 (start.val + half.val + jj.val) := by
        rw [hc2', ← wordAt_of_lt (v := (d.set i o0).set o1i o1) (t := o2i.val) ho2b, p2,
          wordAt_set_ne (by rw [p1]; exact n12.symm), wordAt_set_ne (by rw [p0]; exact n02.symm)]
        exact hq2 jj.val (le_refl _) hjlt
      have hc2lt : c2.val < GP := by
        rw [hc2', ← wordAt_of_lt (v := (d.set i o0).set o1i o1) (t := o2i.val) ho2b]
        exact wordAt_lt hc2 GoldFusedBoundary.GP_pos _
      step as ⟨k2, hk2⟩
      try (case hmax => scalar_tac)
      have hk2b : k2.val < pf0.val.length := by rw [hk2, p2]; omega
      have hk2b' : k2.val < pf1.val.length := by rw [hk2, p2]; omega
      step as ⟨w2, hw2'⟩
      have hw2v : w2.val = pfW pf0 base.val (start.val + half.val + jj.val) := by
        rw [hw2', ← wordAt_of_lt (v := pf0) (t := k2.val) hk2b, hk2, p2]; rfl
      step with gold_mul_spec w2 v2 as ⟨m2, hm2v, hm2lt⟩
      step with gold_add_spec c2 m2 hc2lt hm2lt as ⟨o2, ho2v, ho2lt⟩
      have ho2f : o2.val = macAt (wordAt a0) (pfW pf0 base.val)
          (start.val + half.val + jj.val)
          (f2 (wordAt src) (wordAt tw) half.val quarter.val step1.val start.val jj.val) := by
        rw [ho2v, hm2v, hc2v, hw2v, hv2f]; rfl
      step as ⟨elem2, back2, helem2, hback2⟩
      rw [hback1']
      have he2 : Canon GP ((e.set i r0).set o1i r1) := Canon_set he1 hr1lt
      have ho2b' : o2i.val < ((e.set i r0).set o1i r1).val.length := by rw [he2.1, p2]; omega
      step as ⟨g2, hg2⟩
      have hg2v : g2.val = wordAt a1 (start.val + half.val + jj.val) := by
        rw [hg2, ← wordAt_of_lt (v := (e.set i r0).set o1i r1) (t := o2i.val) ho2b', p2,
          wordAt_set_ne (by rw [p1]; exact n12.symm), wordAt_set_ne (by rw [p0]; exact n02.symm)]
        exact hr2 jj.val (le_refl _) hjlt
      have hg2lt : g2.val < GP := by
        rw [hg2, ← wordAt_of_lt (v := (e.set i r0).set o1i r1) (t := o2i.val) ho2b']
        exact wordAt_lt he2 GoldFusedBoundary.GP_pos _
      step as ⟨y2, hy2'⟩
      have hy2v : y2.val = pfW pf1 base.val (start.val + half.val + jj.val) := by
        rw [hy2', ← wordAt_of_lt (v := pf1) (t := k2.val) hk2b', hk2, p2]; rfl
      step with gold_mul_spec y2 v2 as ⟨n2, hn2v, hn2lt⟩
      step with gold_add_spec g2 n2 hg2lt hn2lt as ⟨r2, hr2v, hr2lt⟩
      have hr2f : r2.val = macAt (wordAt a1) (pfW pf1 base.val)
          (start.val + half.val + jj.val)
          (f2 (wordAt src) (wordAt tw) half.val quarter.val step1.val start.val jj.val) := by
        rw [hr2v, hn2v, hg2v, hy2v, hv2f]; rfl
      step as ⟨elem2', back2', helem2', hback2'⟩
      step as ⟨i28, hi28⟩
      try (case hmax => scalar_tac)
      step as ⟨o3i, ho3i⟩
      try (case hmax => scalar_tac)
      have p3 : o3i.val = start.val + half.val + quarter.val + jj.val := by
        rw [ho3i, hi28, hi22]
      step with gold_sub_spec b2 b3 hb2lt hb3lt as ⟨e1, he1v, he1lt⟩
      step as ⟨t4, ht4⟩
      have ht4v : t4.val = wordAt tw (jj.val * step2.val) := by
        rw [ht4, ← wordAt_of_lt (v := tw) (t := i15.val) hi15b, hi15]
      step with gold_mul_spec e1 t4 as ⟨v3, hv3v, hv3lt⟩
      have hv3f : v3.val = f3 (wordAt src) (wordAt tw) half.val quarter.val step1.val step2.val
          start.val jj.val := by
        rw [hv3v, he1v, ht4v, hb2f, hb3f]; rfl
      rw [hback2]
      /- Write 4, at `start + half + quarter + jj`. -/
      have hc3 : Canon GP (((d.set i o0).set o1i o1).set o2i o2) := Canon_set hc2 ho2lt
      have ho3b : o3i.val < (((d.set i o0).set o1i o1).set o2i o2).val.length := by
        rw [hc3.1, p3]; omega
      step as ⟨c3, hc3'⟩
      have hc3v : c3.val = wordAt a0 (start.val + half.val + quarter.val + jj.val) := by
        rw [hc3', ← wordAt_of_lt (v := ((d.set i o0).set o1i o1).set o2i o2) (t := o3i.val) ho3b,
          p3, wordAt_set_ne (by rw [p2]; exact n23.symm), wordAt_set_ne (by rw [p1]; exact n13.symm),
          wordAt_set_ne (by rw [p0]; exact n03.symm)]
        exact hq3 jj.val (le_refl _) hjlt
      have hc3lt : c3.val < GP := by
        rw [hc3', ← wordAt_of_lt (v := ((d.set i o0).set o1i o1).set o2i o2) (t := o3i.val) ho3b]
        exact wordAt_lt hc3 GoldFusedBoundary.GP_pos _
      step as ⟨k3, hk3⟩
      try (case hmax => scalar_tac)
      have hk3b : k3.val < pf0.val.length := by rw [hk3, p3]; omega
      have hk3b' : k3.val < pf1.val.length := by rw [hk3, p3]; omega
      step as ⟨w3, hw3'⟩
      have hw3v : w3.val = pfW pf0 base.val (start.val + half.val + quarter.val + jj.val) := by
        rw [hw3', ← wordAt_of_lt (v := pf0) (t := k3.val) hk3b, hk3, p3]; rfl
      step with gold_mul_spec w3 v3 as ⟨m3, hm3v, hm3lt⟩
      step with gold_add_spec c3 m3 hc3lt hm3lt as ⟨o3, ho3v, ho3lt⟩
      have ho3f : o3.val = macAt (wordAt a0) (pfW pf0 base.val)
          (start.val + half.val + quarter.val + jj.val)
          (f3 (wordAt src) (wordAt tw) half.val quarter.val step1.val step2.val start.val
            jj.val) := by
        rw [ho3v, hm3v, hc3v, hw3v, hv3f]; rfl
      step as ⟨elem3, back3, helem3, hback3⟩
      rw [hback2']
      have he3 : Canon GP (((e.set i r0).set o1i r1).set o2i r2) := Canon_set he2 hr2lt
      have ho3b' : o3i.val < (((e.set i r0).set o1i r1).set o2i r2).val.length := by
        rw [he3.1, p3]; omega
      step as ⟨g3, hg3⟩
      have hg3v : g3.val = wordAt a1 (start.val + half.val + quarter.val + jj.val) := by
        rw [hg3, ← wordAt_of_lt (v := ((e.set i r0).set o1i r1).set o2i r2) (t := o3i.val) ho3b',
          p3, wordAt_set_ne (by rw [p2]; exact n23.symm), wordAt_set_ne (by rw [p1]; exact n13.symm),
          wordAt_set_ne (by rw [p0]; exact n03.symm)]
        exact hr3 jj.val (le_refl _) hjlt
      have hg3lt : g3.val < GP := by
        rw [hg3, ← wordAt_of_lt (v := ((e.set i r0).set o1i r1).set o2i r2) (t := o3i.val) ho3b']
        exact wordAt_lt he3 GoldFusedBoundary.GP_pos _
      step as ⟨y3, hy3'⟩
      have hy3v : y3.val = pfW pf1 base.val (start.val + half.val + quarter.val + jj.val) := by
        rw [hy3', ← wordAt_of_lt (v := pf1) (t := k3.val) hk3b', hk3, p3]; rfl
      step with gold_mul_spec y3 v3 as ⟨n3, hn3v, hn3lt⟩
      step with gold_add_spec g3 n3 hg3lt hn3lt as ⟨r3, hr3v, hr3lt⟩
      have hr3f : r3.val = macAt (wordAt a1) (pfW pf1 base.val)
          (start.val + half.val + quarter.val + jj.val)
          (f3 (wordAt src) (wordAt tw) half.val quarter.val step1.val step2.val start.val
            jj.val) := by
        rw [hr3v, hn3v, hg3v, hy3v, hv3f]; rfl
      step as ⟨elem3', back3', helem3', hback3'⟩
      step as ⟨j1, hj1⟩
      try (case hmax => scalar_tac)
      rw [hback3, hback3']
      refine ⟨by clear * - hj1 hjlt; omega, ?_, ?_, by clear * - hj1 hjlt hqpos; omega⟩
      · rw [hj1]
        exact MacBlk_step hB0 hhq hjlt hblk p0 p1 p2 p3 ho0f ho1f ho2f ho3f
      · rw [hj1]
        exact MacBlk_step hB1 hhq hjlt hblk p0 p1 p2 p3 hr0f hr1f hr2f hr3f
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = quarter.val := by scalar_tac
      rw [heq] at hB0 hB1
      exact ⟨hB0, hB1⟩
  · exact ⟨hj, hI0, hI1⟩


/-- The outer loop of [`ring.gold_dif_stage2_mac2`]: [`mac_loop0_spec`] with each
accumulate written twice. The peeled group `j = 0` is one [`MacBlk_step`] at
`j = 0` per accumulator, from the block's untouched state [`MacOut_blk0`]. -/
theorem mac2_loop0_spec (src a0 a1 acc0 acc1 tw pf0 pf1 : alloc.vec.Vec Std.U64)
    (len : Std.Usize) (base half quarter step1 step2 start : Std.Usize)
    (hsrc : Canon GP src) (htw : Canon GP tw) (htw0 : wordAt tw 0 = 1)
    (hb0 : base.val + N ≤ pf0.val.length) (hb1 : base.val + N ≤ pf1.val.length)
    (hlen : len.val = 2 * half.val) (hhq : half.val = 2 * quarter.val)
    (hqpos : 0 < quarter.val) (hdvd : len.val ∣ N)
    (hs2 : step2.val = 2 * step1.val) (hstep : 0 < step1.val)
    (hebd : half.val * step1.val ≤ N)
    (hstart : start.val ≤ N) (hmod : start.val % len.val = 0)
    (hO0 : MacOut src tw pf0 a0 base.val half.val quarter.val step1.val step2.val start.val acc0)
    (hO1 : MacOut src tw pf1 a1 base.val half.val quarter.val step1.val step2.val start.val
      acc1) :
    ring.gold_dif_stage2_mac2_loop0 src acc0 acc1 len tw pf0 pf1 base ntt.NTT_LEN half quarter
        step1 step2 start
      ⦃ z => MacOut src tw pf0 a0 base.val half.val quarter.val step1.val step2.val N z.1
             ∧ MacOut src tw pf1 a1 base.val half.val quarter.val step1.val step2.val N z.2 ⦄ := by
  rw [ring.gold_dif_stage2_mac2_loop0]
  apply loop.spec_decr_nat (fun s => N - s.2.2.val)
    (fun s => s.2.2.val ≤ N ∧ s.2.2.val % len.val = 0
      ∧ MacOut src tw pf0 a0 base.val half.val quarter.val step1.val step2.val s.2.2.val s.1
      ∧ MacOut src tw pf1 a1 base.val half.val quarter.val step1.val step2.val s.2.2.val s.2.1)
  · rintro ⟨d, e, ss⟩ ⟨hss, hmod1, hO0', hO1'⟩
    dsimp only at hss hmod1 hO0' hO1'
    simp only [ring.gold_dif_stage2_mac2_loop0.body]
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
      have hcd : Canon GP d := hO0'.1
      have hce : Canon GP e := hO1'.1
      have hpend0 : ∀ k, ss.val ≤ k → wordAt d k = wordAt a0 k := hO0'.2.2
      have hpend1 : ∀ k, ss.val ≤ k → wordAt e k = wordAt a1 k := hO1'.2.2
      have hsl : src.val.length = N := hsrc.1
      have hdl : d.val.length = N := hcd.1
      have hel : e.val.length = N := hce.1
      have htl : tw.val.length = N := htw.1
      have hbtq : quarter.val * step1.val < N := by
        have h := Nat.mul_lt_mul_of_pos_right (show quarter.val < half.val by omega) hstep
        omega
      /- The peeled group `j = 0` (card T49a). The four reads of the source. -/
      have hsb : ss.val < src.val.length := by rw [hsl]; exact hsslt
      step as ⟨a0', ha0⟩
      have ha0v : a0'.val = wordAt src ss.val := by
        rw [ha0, ← wordAt_of_lt (v := src) (t := ss.val) hsb]
      step as ⟨i, hi⟩
      have hib : i.val < src.val.length := by rw [hsl, hi]; omega
      step as ⟨a1', ha1⟩
      have ha1v : a1'.val = wordAt src (ss.val + quarter.val) := by
        rw [ha1, ← wordAt_of_lt (v := src) (t := i.val) hib, hi]
      step as ⟨i1, hi1⟩
      have hi1b : i1.val < src.val.length := by rw [hsl, hi1]; omega
      step as ⟨a2', ha2⟩
      have ha2v : a2'.val = wordAt src (ss.val + half.val) := by
        rw [ha2, ← wordAt_of_lt (v := src) (t := i1.val) hi1b, hi1]
      step as ⟨i2, hi2⟩
      have hi2b : i2.val < src.val.length := by rw [hsl, hi2, hi1]; omega
      step as ⟨a3', ha3⟩
      have ha3v : a3'.val = wordAt src (ss.val + quarter.val + half.val) := by
        rw [ha3, ← wordAt_of_lt (v := src) (t := i2.val) hi2b, hi2, hi1]
        congr 1
        omega
      have h0lt : a0'.val < GP := by rw [ha0v]; exact wordAt_lt hsrc GoldFusedBoundary.GP_pos _
      have h1lt : a1'.val < GP := by rw [ha1v]; exact wordAt_lt hsrc GoldFusedBoundary.GP_pos _
      have h2lt : a2'.val < GP := by rw [ha2v]; exact wordAt_lt hsrc GoldFusedBoundary.GP_pos _
      have h3lt : a3'.val < GP := by rw [ha3v]; exact wordAt_lt hsrc GoldFusedBoundary.GP_pos _
      step with gold_add_spec a0' a2' h0lt h2lt as ⟨b0, hb0v, hb0lt⟩
      step with gold_add_spec a1' a3' h1lt h3lt as ⟨b1, hb1v, hb1lt⟩
      step with gold_sub_spec a0' a2' h0lt h2lt as ⟨b2, hb2v, hb2lt⟩
      step with gold_sub_spec a1' a3' h1lt h3lt as ⟨e1, he1v, he1lt⟩
      step as ⟨i3, hi3⟩
      have hi3b : i3.val < tw.val.length := by rw [htl, hi3]; exact hbtq
      step as ⟨t2, ht2⟩
      have ht2v : t2.val = wordAt tw (quarter.val * step1.val) := by
        rw [ht2, ← wordAt_of_lt (v := tw) (t := i3.val) hi3b, hi3]
      step with gold_mul_spec e1 t2 as ⟨b3, hb3v, hb3lt⟩
      have hb0f : b0.val = bSum (wordAt src) half.val ss.val := by
        rw [hb0v, ha0v, ha2v]; rfl
      have hb1f : b1.val = bSum (wordAt src) half.val (ss.val + quarter.val) := by
        rw [hb1v, ha1v, ha3v]; rfl
      have hb2f : b2.val = (wordAt src ss.val + GP - wordAt src (ss.val + half.val)) % GP := by
        rw [hb2v, ha0v, ha2v]
      have hb3f : b3.val
          = bDif (wordAt src) (wordAt tw) half.val (quarter.val * step1.val)
              (ss.val + quarter.val) := by
        rw [hb3v, he1v, ht2v, ha1v, ha3v]; rfl
      have p1 : i.val = ss.val + quarter.val := hi
      have p2 : i1.val = ss.val + half.val := hi1
      /- Write 1, at `start`: limb 0, then limb 1. -/
      step with gold_add_spec b0 b1 hb0lt hb1lt as ⟨v0, hv0v, hv0lt⟩
      have hv0f : v0.val = f0 (wordAt src) half.val quarter.val ss.val 0 := by
        rw [hv0v, hb0f, hb1f, f0_zero]
      have hsdb : ss.val < d.val.length := by rw [hdl]; exact hsslt
      have hseb : ss.val < e.val.length := by rw [hel]; exact hsslt
      step as ⟨c0, hc0⟩
      have hc0v : c0.val = wordAt a0 ss.val := by
        rw [hc0, ← wordAt_of_lt (v := d) (t := ss.val) hsdb]
        exact hpend0 ss.val (le_refl _)
      have hc0lt : c0.val < GP := by
        rw [hc0, ← wordAt_of_lt (v := d) (t := ss.val) hsdb]
        exact wordAt_lt hcd GoldFusedBoundary.GP_pos _
      step as ⟨k0, hk0⟩
      have hk0b : k0.val < pf0.val.length := by rw [hk0]; omega
      have hk0b' : k0.val < pf1.val.length := by rw [hk0]; omega
      step as ⟨w0, hw0'⟩
      have hw0v : w0.val = pfW pf0 base.val ss.val := by
        rw [hw0', ← wordAt_of_lt (v := pf0) (t := k0.val) hk0b, hk0]; rfl
      step with gold_mul_spec w0 v0 as ⟨m0, hm0v, hm0lt⟩
      step with gold_add_spec c0 m0 hc0lt hm0lt as ⟨o0, ho0v, ho0lt⟩
      have ho0f : o0.val = macAt (wordAt a0) (pfW pf0 base.val) ss.val
          (f0 (wordAt src) half.val quarter.val ss.val 0) := by
        rw [ho0v, hm0v, hc0v, hw0v, hv0f]; rfl
      step as ⟨elem, back, helem, hback⟩
      step as ⟨g0, hg0⟩
      have hg0v : g0.val = wordAt a1 ss.val := by
        rw [hg0, ← wordAt_of_lt (v := e) (t := ss.val) hseb]
        exact hpend1 ss.val (le_refl _)
      have hg0lt : g0.val < GP := by
        rw [hg0, ← wordAt_of_lt (v := e) (t := ss.val) hseb]
        exact wordAt_lt hce GoldFusedBoundary.GP_pos _
      step as ⟨y0, hy0'⟩
      have hy0v : y0.val = pfW pf1 base.val ss.val := by
        rw [hy0', ← wordAt_of_lt (v := pf1) (t := k0.val) hk0b', hk0]; rfl
      step with gold_mul_spec y0 v0 as ⟨n0, hn0v, hn0lt⟩
      step with gold_add_spec g0 n0 hg0lt hn0lt as ⟨r0, hr0v, hr0lt⟩
      have hr0f : r0.val = macAt (wordAt a1) (pfW pf1 base.val) ss.val
          (f0 (wordAt src) half.val quarter.val ss.val 0) := by
        rw [hr0v, hn0v, hg0v, hy0v, hv0f]; rfl
      step as ⟨elem', back', helem', hback'⟩
      step with gold_sub_spec b0 b1 hb0lt hb1lt as ⟨v1, hv1v, hv1lt⟩
      have hv1f : v1.val
          = f1 (wordAt src) (wordAt tw) half.val quarter.val step2.val ss.val 0 := by
        rw [hv1v, hb0f, hb1f, f1_tw0 (wordAt src) (wordAt tw) htw0]
      rw [hback]
      /- Write 2, at `start + quarter`. -/
      have r10 : ss.val + quarter.val ≠ ss.val := by clear * - hqpos; omega
      have hc1 : Canon GP (d.set ss o0) := Canon_set hcd ho0lt
      have ho1b : i.val < (d.set ss o0).val.length := by rw [hc1.1, p1]; omega
      step as ⟨c1, hc1'⟩
      have hc1v : c1.val = wordAt a0 (ss.val + quarter.val) := by
        rw [hc1', ← wordAt_of_lt (v := d.set ss o0) (t := i.val) ho1b, p1, wordAt_set_ne r10]
        exact hpend0 _ (by omega)
      have hc1lt : c1.val < GP := by
        rw [hc1', ← wordAt_of_lt (v := d.set ss o0) (t := i.val) ho1b]
        exact wordAt_lt hc1 GoldFusedBoundary.GP_pos _
      have hbo1 : base.val + i.val < pf0.val.length := by rw [p1]; omega
      step as ⟨k1, hk1⟩
      try (case hmax => clear * - hbo1; scalar_tac)
      have hk1b : k1.val < pf0.val.length := by rw [hk1, p1]; omega
      have hk1b' : k1.val < pf1.val.length := by rw [hk1, p1]; omega
      step as ⟨w1, hw1'⟩
      have hw1v : w1.val = pfW pf0 base.val (ss.val + quarter.val) := by
        rw [hw1', ← wordAt_of_lt (v := pf0) (t := k1.val) hk1b, hk1, p1]; rfl
      step with gold_mul_spec w1 v1 as ⟨m1, hm1v, hm1lt⟩
      step with gold_add_spec c1 m1 hc1lt hm1lt as ⟨o1, ho1v, ho1lt⟩
      have ho1f : o1.val = macAt (wordAt a0) (pfW pf0 base.val) (ss.val + quarter.val)
          (f1 (wordAt src) (wordAt tw) half.val quarter.val step2.val ss.val 0) := by
        rw [ho1v, hm1v, hc1v, hw1v, hv1f]; rfl
      step as ⟨elem1, back1, helem1, hback1⟩
      rw [hback']
      have he1 : Canon GP (e.set ss r0) := Canon_set hce hr0lt
      have ho1b' : i.val < (e.set ss r0).val.length := by rw [he1.1, p1]; omega
      step as ⟨g1, hg1⟩
      have hg1v : g1.val = wordAt a1 (ss.val + quarter.val) := by
        rw [hg1, ← wordAt_of_lt (v := e.set ss r0) (t := i.val) ho1b', p1, wordAt_set_ne r10]
        exact hpend1 _ (by omega)
      have hg1lt : g1.val < GP := by
        rw [hg1, ← wordAt_of_lt (v := e.set ss r0) (t := i.val) ho1b']
        exact wordAt_lt he1 GoldFusedBoundary.GP_pos _
      step as ⟨y1, hy1'⟩
      have hy1v : y1.val = pfW pf1 base.val (ss.val + quarter.val) := by
        rw [hy1', ← wordAt_of_lt (v := pf1) (t := k1.val) hk1b', hk1, p1]; rfl
      step with gold_mul_spec y1 v1 as ⟨n1, hn1v, hn1lt⟩
      step with gold_add_spec g1 n1 hg1lt hn1lt as ⟨r1, hr1v, hr1lt⟩
      have hr1f : r1.val = macAt (wordAt a1) (pfW pf1 base.val) (ss.val + quarter.val)
          (f1 (wordAt src) (wordAt tw) half.val quarter.val step2.val ss.val 0) := by
        rw [hr1v, hn1v, hg1v, hy1v, hv1f]; rfl
      step as ⟨elem1', back1', helem1', hback1'⟩
      step with gold_add_spec b2 b3 hb2lt hb3lt as ⟨v2, hv2v, hv2lt⟩
      have hv2f : v2.val
          = f2 (wordAt src) (wordAt tw) half.val quarter.val step1.val ss.val 0 := by
        rw [hv2v, hb2f, hb3f, f2_tw0 (wordAt src) (wordAt tw) htw0]
      rw [hback1]
      /- Write 3, at `start + half`. -/
      have r21 : ss.val + half.val ≠ i.val := by clear * - p1 hhq hqpos; omega
      have r20 : ss.val + half.val ≠ ss.val := by clear * - hhq hqpos; omega
      have hc2 : Canon GP ((d.set ss o0).set i o1) := Canon_set hc1 ho1lt
      have ho2b : i1.val < ((d.set ss o0).set i o1).val.length := by rw [hc2.1, p2]; omega
      step as ⟨c2, hc2'⟩
      have hc2v : c2.val = wordAt a0 (ss.val + half.val) := by
        rw [hc2', ← wordAt_of_lt (v := (d.set ss o0).set i o1) (t := i1.val) ho2b, p2,
          wordAt_set_ne r21, wordAt_set_ne r20]
        exact hpend0 _ (by omega)
      have hc2lt : c2.val < GP := by
        rw [hc2', ← wordAt_of_lt (v := (d.set ss o0).set i o1) (t := i1.val) ho2b]
        exact wordAt_lt hc2 GoldFusedBoundary.GP_pos _
      step as ⟨k2, hk2⟩
      try (case hmax => scalar_tac)
      have hk2b : k2.val < pf0.val.length := by rw [hk2, p2]; omega
      have hk2b' : k2.val < pf1.val.length := by rw [hk2, p2]; omega
      step as ⟨w2, hw2'⟩
      have hw2v : w2.val = pfW pf0 base.val (ss.val + half.val) := by
        rw [hw2', ← wordAt_of_lt (v := pf0) (t := k2.val) hk2b, hk2, p2]; rfl
      step with gold_mul_spec w2 v2 as ⟨m2, hm2v, hm2lt⟩
      step with gold_add_spec c2 m2 hc2lt hm2lt as ⟨o2, ho2v, ho2lt⟩
      have ho2f : o2.val = macAt (wordAt a0) (pfW pf0 base.val) (ss.val + half.val)
          (f2 (wordAt src) (wordAt tw) half.val quarter.val step1.val ss.val 0) := by
        rw [ho2v, hm2v, hc2v, hw2v, hv2f]; rfl
      step as ⟨elem2, back2, helem2, hback2⟩
      rw [hback1']
      have he2 : Canon GP ((e.set ss r0).set i r1) := Canon_set he1 hr1lt
      have ho2b' : i1.val < ((e.set ss r0).set i r1).val.length := by rw [he2.1, p2]; omega
      step as ⟨g2, hg2⟩
      have hg2v : g2.val = wordAt a1 (ss.val + half.val) := by
        rw [hg2, ← wordAt_of_lt (v := (e.set ss r0).set i r1) (t := i1.val) ho2b', p2,
          wordAt_set_ne r21, wordAt_set_ne r20]
        exact hpend1 _ (by omega)
      have hg2lt : g2.val < GP := by
        rw [hg2, ← wordAt_of_lt (v := (e.set ss r0).set i r1) (t := i1.val) ho2b']
        exact wordAt_lt he2 GoldFusedBoundary.GP_pos _
      step as ⟨y2, hy2'⟩
      have hy2v : y2.val = pfW pf1 base.val (ss.val + half.val) := by
        rw [hy2', ← wordAt_of_lt (v := pf1) (t := k2.val) hk2b', hk2, p2]; rfl
      step with gold_mul_spec y2 v2 as ⟨n2, hn2v, hn2lt⟩
      step with gold_add_spec g2 n2 hg2lt hn2lt as ⟨r2, hr2v, hr2lt⟩
      have hr2f : r2.val = macAt (wordAt a1) (pfW pf1 base.val) (ss.val + half.val)
          (f2 (wordAt src) (wordAt tw) half.val quarter.val step1.val ss.val 0) := by
        rw [hr2v, hn2v, hg2v, hy2v, hv2f]; rfl
      step as ⟨elem2', back2', helem2', hback2'⟩
      have ho3pre : i1.val + quarter.val < src.val.length := by rw [hsl, p2]; omega
      step as ⟨o3i, ho3i⟩
      · clear * - ho3pre; scalar_tac
      have p3 : o3i.val = ss.val + half.val + quarter.val := by rw [ho3i, hi1]
      step with gold_sub_spec b2 b3 hb2lt hb3lt as ⟨v3, hv3v, hv3lt⟩
      have hv3f : v3.val = f3 (wordAt src) (wordAt tw) half.val quarter.val step1.val step2.val
          ss.val 0 := by
        rw [hv3v, hb2f, hb3f, f3_tw0 (wordAt src) (wordAt tw) htw0]
      rw [hback2]
      /- Write 4, at `start + half + quarter`. -/
      have r32 : ss.val + half.val + quarter.val ≠ i1.val := by clear * - p2 hqpos; omega
      have r31 : ss.val + half.val + quarter.val ≠ i.val := by clear * - p1 hhq hqpos; omega
      have r30 : ss.val + half.val + quarter.val ≠ ss.val := by clear * - hhq hqpos; omega
      have hc3 : Canon GP (((d.set ss o0).set i o1).set i1 o2) := Canon_set hc2 ho2lt
      have ho3b : o3i.val < (((d.set ss o0).set i o1).set i1 o2).val.length := by
        rw [hc3.1, p3]; omega
      step as ⟨c3, hc3'⟩
      have hc3v : c3.val = wordAt a0 (ss.val + half.val + quarter.val) := by
        rw [hc3', ← wordAt_of_lt (v := ((d.set ss o0).set i o1).set i1 o2) (t := o3i.val) ho3b,
          p3, wordAt_set_ne r32, wordAt_set_ne r31, wordAt_set_ne r30]
        exact hpend0 _ (by omega)
      have hc3lt : c3.val < GP := by
        rw [hc3', ← wordAt_of_lt (v := ((d.set ss o0).set i o1).set i1 o2) (t := o3i.val) ho3b]
        exact wordAt_lt hc3 GoldFusedBoundary.GP_pos _
      step as ⟨k3, hk3⟩
      try (case hmax => scalar_tac)
      have hk3b : k3.val < pf0.val.length := by rw [hk3, p3]; omega
      have hk3b' : k3.val < pf1.val.length := by rw [hk3, p3]; omega
      step as ⟨w3, hw3'⟩
      have hw3v : w3.val = pfW pf0 base.val (ss.val + half.val + quarter.val) := by
        rw [hw3', ← wordAt_of_lt (v := pf0) (t := k3.val) hk3b, hk3, p3]; rfl
      step with gold_mul_spec w3 v3 as ⟨m3, hm3v, hm3lt⟩
      step with gold_add_spec c3 m3 hc3lt hm3lt as ⟨o3, ho3v, ho3lt⟩
      have ho3f : o3.val = macAt (wordAt a0) (pfW pf0 base.val)
          (ss.val + half.val + quarter.val)
          (f3 (wordAt src) (wordAt tw) half.val quarter.val step1.val step2.val ss.val 0) := by
        rw [ho3v, hm3v, hc3v, hw3v, hv3f]; rfl
      step as ⟨elem3, back3, helem3, hback3⟩
      rw [hback2']
      have he3 : Canon GP (((e.set ss r0).set i r1).set i1 r2) := Canon_set he2 hr2lt
      have ho3b' : o3i.val < (((e.set ss r0).set i r1).set i1 r2).val.length := by
        rw [he3.1, p3]; omega
      step as ⟨g3, hg3⟩
      have hg3v : g3.val = wordAt a1 (ss.val + half.val + quarter.val) := by
        rw [hg3, ← wordAt_of_lt (v := ((e.set ss r0).set i r1).set i1 r2) (t := o3i.val) ho3b',
          p3, wordAt_set_ne r32, wordAt_set_ne r31, wordAt_set_ne r30]
        exact hpend1 _ (by omega)
      have hg3lt : g3.val < GP := by
        rw [hg3, ← wordAt_of_lt (v := ((e.set ss r0).set i r1).set i1 r2) (t := o3i.val) ho3b']
        exact wordAt_lt he3 GoldFusedBoundary.GP_pos _
      step as ⟨y3, hy3'⟩
      have hy3v : y3.val = pfW pf1 base.val (ss.val + half.val + quarter.val) := by
        rw [hy3', ← wordAt_of_lt (v := pf1) (t := k3.val) hk3b', hk3, p3]; rfl
      step with gold_mul_spec y3 v3 as ⟨n3, hn3v, hn3lt⟩
      step with gold_add_spec g3 n3 hg3lt hn3lt as ⟨r3, hr3v, hr3lt⟩
      have hr3f : r3.val = macAt (wordAt a1) (pfW pf1 base.val)
          (ss.val + half.val + quarter.val)
          (f3 (wordAt src) (wordAt tw) half.val quarter.val step1.val step2.val ss.val 0) := by
        rw [hr3v, hn3v, hg3v, hy3v, hv3f]; rfl
      step as ⟨elem3', back3', helem3', hback3'⟩
      rw [hback3', hback3]
      /- The peel, as one block step at `j = 0` per accumulator: the inner
      invariant at `j = 1`, framed by the block's untouched state. -/
      have q0 : ss.val = ss.val + 0 := (Nat.add_zero _).symm
      have q1 : i.val = ss.val + 0 + quarter.val := by rw [Nat.add_zero]; exact p1
      have q2 : i1.val = ss.val + half.val + 0 := by rw [Nat.add_zero]; exact p2
      have q3 : o3i.val = ss.val + half.val + quarter.val + 0 := by rw [Nat.add_zero]; exact p3
      have hqp0 : 0 < quarter.val := hqpos
      have hP0 := MacBlk_step (i := ss) (MacOut_blk0 hO0') hhq hqp0 hblk2 q0 q1 q2 q3
        (by simpa only [Nat.add_zero] using ho0f) (by simpa only [Nat.add_zero] using ho1f)
        (by simpa only [Nat.add_zero] using ho2f) (by simpa only [Nat.add_zero] using ho3f)
      have hP1 := MacBlk_step (i := ss) (MacOut_blk0 hO1') hhq hqp0 hblk2 q0 q1 q2 q3
        (by simpa only [Nat.add_zero] using hr0f) (by simpa only [Nat.add_zero] using hr1f)
        (by simpa only [Nat.add_zero] using hr2f) (by simpa only [Nat.add_zero] using hr3f)
      have hone : (1#usize).val = 0 + 1 := by simp
      have hj1 : (1#usize).val ≤ quarter.val := by rw [hone]; omega
      have hP0' := MacBlk_self hP0
      have hP1' := MacBlk_self hP1
      rw [← hone] at hP0' hP1'
      step with mac2_loop0_loop0_spec src a0 a1 _ _ tw pf0 pf1 base half quarter step1 step2 ss
        1#usize hsrc htw hb0 hb1 hhq hqpos hblk2 hj1 hs2 hstep hebd hP0' hP1'
        as ⟨dn, en, hdn, hen⟩
      have hss1pre : ss.val + len.val ≤ src.val.length := by rw [hsl]; exact hblk
      step as ⟨ss1, hss1⟩
      · clear * - hss1pre; scalar_tac
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · rw [hss1, Nat.add_mod_right, hmod1]
      · rw [hss1, hlen]
        exact MacOut_next hO0' hdn hP0.2.2.2.2.2.2.2.2.2 hhq hsm
      · rw [hss1, hlen]
        exact MacOut_next hO1' hen hP1.2.2.2.2.2.2.2.2.2 hhq hsm
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ss.val = N := by scalar_tac
      rw [heq] at hO0' hO1'
      exact ⟨hO0', hO1'⟩
  · exact ⟨hstart, hmod, hO0, hO1⟩

/-- **The two-table MAC stage**: [`gold_dif_stage2_mac_spec`] once per
`(acc, pf)` pair. -/
theorem gold_dif_stage2_mac2_spec (src acc0 acc1 tw pf0 pf1 : alloc.vec.Vec Std.U64)
    (len base : Std.Usize) (k : ℕ) (hk : k < 9) (hlen : len.val = 2 ^ (k + 2))
    (hsrc : Canon GP src) (hacc0 : Canon GP acc0) (hacc1 : Canon GP acc1)
    (htw : Canon GP tw) (htw0 : wordAt tw 0 = 1)
    (hb0 : base.val + N ≤ pf0.val.length) (hb1 : base.val + N ≤ pf1.val.length) :
    ring.gold_dif_stage2_mac2 src acc0 acc1 len tw pf0 pf1 base
      ⦃ z => Canon GP z.1
             ∧ (∀ t, t < N →
                   wordAt z.1 t
                     = macAt (wordAt acc0) (pfW pf0 base.val) t
                         (difWord GP (2 ^ k) (2 * (N / 2 ^ (k + 1)))
                           (difWord GP (2 ^ (k + 1)) (2 * (N / 2 ^ (k + 2)))
                             (wordAt src) (wordAt tw)) (wordAt tw) t))
             ∧ Canon GP z.2
             ∧ (∀ t, t < N →
                   wordAt z.2 t
                     = macAt (wordAt acc1) (pfW pf1 base.val) t
                         (difWord GP (2 ^ k) (2 * (N / 2 ^ (k + 1)))
                           (difWord GP (2 ^ (k + 1)) (2 * (N / 2 ^ (k + 2)))
                             (wordAt src) (wordAt tw)) (wordAt tw) t)) ⦄ := by
  obtain ⟨hd1, hd2, hdvd⟩ := fusedParams' k hk
  have hlne : len.val ≠ 0 := by rw [hlen]; positivity
  rw [ring.gold_dif_stage2_mac2]
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
  apply spec_mono (mac2_loop0_spec src acc0 acc1 acc0 acc1 tw pf0 pf1 len base hf qq st1 st2
    0#usize hsrc htw htw0 hb0 hb1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by simp) (by simp)
    ⟨hacc0, fun t ht => by simp at ht, fun t _ => rfl⟩
    ⟨hacc1, fun t ht => by simp at ht, fun t _ => rfl⟩)
  · intro z hz
    exact ⟨hz.1.1, hz.1.2.1, hz.2.1, hz.2.2.1⟩
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

/-- The limb kernel's middle loop is [`ring.gold_dot_one_fused_loop`]: the two
extractions are the same loop over the same body. -/
theorem gold_dot_one_fused_limbs2_loop_eq (pt cur tmp : alloc.vec.Vec Std.U64)
    (len : Std.Usize) :
    ring.gold_dot_one_fused_limbs2_loop pt cur tmp len
      = ring.gold_dot_one_fused_loop pt cur tmp len := rfl


/-- **One right-hand term of the two-limb dot, fused** (card T52a):
[`gold_dot_one_fused_spec`] with the accumulate doubled. Each accumulator gains
its own table's entry times the one transform of `a`, and all four buffers come
back `Canon`. -/
theorem gold_dot_one_fused_limbs2_spec (a : ring.Rq)
    (cur0 tmp0 acc0 acc1 pt pf0 pf1 : alloc.vec.Vec Std.U64)
    (baseU : Std.Usize) (ps : ZMod GP) (A0 A1 : ℕ → ZMod GP)
    (hwf : HachiEquiv.Ring.Wf a) (hcur : Canon GP cur0) (htmp : Canon GP tmp0)
    (hacc0 : Canon GP acc0) (hacc1 : Canon GP acc1)
    (hptC : Canon GP pt) (hptv : ∀ e, e < N → resK GP pt e = ps ^ e)
    (hb0 : baseU.val + N ≤ pf0.val.length) (hb1 : baseU.val + N ≤ pf1.val.length)
    (hA0 : ∀ t, t < N → ((wordAt pf0 (baseU.val + t) : ℕ) : ZMod GP) = A0 t)
    (hA1 : ∀ t, t < N → ((wordAt pf1 (baseU.val + t) : ℕ) : ZMod GP) = A1 t) :
    ring.gold_dot_one_fused_limbs2 a cur0 tmp0 acc0 acc1 pt pf0 pf1 baseU
      ⦃ z => Canon GP z.1 ∧ Canon GP z.2.1 ∧ Canon GP z.2.2.1 ∧ Canon GP z.2.2.2
             ∧ (∀ t, t < N → resK GP z.1 t
                 = resK GP acc0 t
                   + A0 t * NttMath.difRun (ps ^ 2) 10 1
                       (NttMath.twistR ps
                         (fun u => ((HachiEquiv.Ring.wordN a u : ℕ) : ZMod GP))) t)
             ∧ (∀ t, t < N → resK GP z.2.1 t
                 = resK GP acc1 t
                   + A1 t * NttMath.difRun (ps ^ 2) 10 1
                       (NttMath.twistR ps
                         (fun u => ((HachiEquiv.Ring.wordN a u : ℕ) : ZMod GP))) t) ⦄ := by
  have hag : ∀ e, e < N → wordAt pt e = psiRep ps e := tw_agree' GP pt GoldFusedBoundary.GP_pos hptC ps hptv
  have htw0 : wordAt pt 0 = 1 := tw_zero_one GP pt (by norm_num) hptC ps hptv
  set F : ℕ → ZMod GP := fun u => ((twSrc a pt u : ℕ) : ZMod GP) with hF
  rw [ring.gold_dot_one_fused_limbs2]
  -- (A) the twist stage, the transform's first two stages at `len = N`
  step with gold_dif_stage2_twist_spec a cur0 pt pt ntt.NTT_LEN 8 (by norm_num)
    (by rw [ntt_NTT_LEN_val]; norm_num) hwf hcur hptC hptC as ⟨c1, hc1C, hc1w⟩
  have hstep1 : N / 2 ^ (8 + 1) = 2 ^ 1 := by norm_num
  have hstep2 : N / 2 ^ (8 + 2) = 2 ^ 0 := by norm_num
  have hinner : difWord GP (2 ^ (8 + 1)) (2 * (N / 2 ^ (8 + 2))) (twSrc a pt) (wordAt pt)
      = difWord GP (2 ^ (8 + 1)) (2 * (N / 2 ^ (8 + 2))) (twSrc a pt) (psiRep ps) :=
    funext (fun u => difWord_tw_congr GP (8 + 1) (by omega) (twSrc a pt)
      (wordAt pt) (psiRep ps) hag u)
  have hres1 : ∀ t, t < N →
      resK GP c1 t
        = NttMath.difStage (2 ^ 8) (2 ^ 1) (ps ^ 2)
            (NttMath.difStage (2 ^ (8 + 1)) (2 ^ 0) (ps ^ 2) F) t := by
    intro t ht
    have h1 : wordAt c1 t
        = difWord GP (2 ^ 8) (2 * (N / 2 ^ (8 + 1)))
            (difWord GP (2 ^ (8 + 1)) (2 * (N / 2 ^ (8 + 2))) (twSrc a pt) (psiRep ps))
            (psiRep ps) t := by
      rw [hc1w t ht, hinner]
      exact difWord_tw_congr GP 8 (by omega) _ (wordAt pt) (psiRep ps) hag t
    have hmid : (fun u => ((difWord GP (2 ^ (8 + 1)) (2 * 2 ^ 0) (twSrc a pt) (psiRep ps) u
          : ℕ) : ZMod GP))
        = NttMath.difStage (2 ^ (8 + 1)) (2 ^ 0) (ps ^ 2) F :=
      funext (fun u => difWord_cast GP (2 ^ (8 + 1)) (2 ^ 0) ps (twSrc a pt) (psiRep ps)
        (psiRep_cast GoldFusedBoundary.GP_pos ps) (twSrc_lt a pt) u)
    have hlt2 : ∀ u, difWord GP (2 ^ (8 + 1)) (2 * 2 ^ 0) (twSrc a pt) (psiRep ps) u < GP :=
      fun u => difWord_lt GP _ _ GoldFusedBoundary.GP_pos _ _ u
    rw [resK, h1, hstep1, hstep2,
      difWord_cast GP (2 ^ 8) (2 ^ 1) ps _ (psiRep ps) (psiRep_cast GoldFusedBoundary.GP_pos ps)
        hlt2 t, hmid]
  -- the invariant the middle loop starts from: eight stages remain
  have hinv0 : ∀ t, t < N →
      NttMath.difRun (ps ^ 2) (2 * 4) (2 ^ (10 - 2 * 4)) (resK GP c1) t
        = NttMath.difRun (ps ^ 2) 10 1 F t := by
    intro t ht
    have hdvd : (2 : ℕ) ^ (2 * 4) ∣ N := by norm_num
    rw [difRun_congr (ps ^ 2) (2 * 4) hdvd (2 ^ (10 - 2 * 4)) (resK GP c1)
      (NttMath.difStage (2 ^ 8) (2 ^ 1) (ps ^ 2)
        (NttMath.difStage (2 ^ (8 + 1)) (2 ^ 0) (ps ^ 2) F)) hres1 t ht]
    rfl
  -- (C) the middle loop, from `len = N/4` down to `len = 4`: the commitment's
  step as ⟨len, hlen⟩
  have hlenv : len.val = 2 ^ (2 * 4) := by rw [hlen, ntt_NTT_LEN_val]; norm_num
  rw [gold_dot_one_fused_limbs2_loop_eq]
  step with gold_dot_one_fused_loop_spec pt c1 tmp0 len 4 (by norm_num) (le_refl 4) hlenv
    hc1C htmp hptC ps hptv (NttMath.difRun (ps ^ 2) 10 1 F) hinv0
    as ⟨c2, t2, hc2C, ht2C, hc2v⟩
  -- (B) the two-table MAC stage, the last two stages at `len = 4`
  step with gold_dif_stage2_mac2_spec c2 acc0 acc1 pt pf0 pf1 4#usize baseU 0 (by norm_num)
    (by norm_num) hc2C hacc0 hacc1 hptC htw0 hb0 hb1
    as ⟨e0, e1, he0C, he0w, he1C, he1w⟩
  refine ⟨he0C, he1C, hc2C, ht2C, ?_, ?_⟩
  all_goals
    intro t ht
    have hstepM1 : N / 2 ^ (0 + 1) = 2 ^ 9 := by norm_num
    have hstepM2 : N / 2 ^ (0 + 2) = 2 ^ 8 := by norm_num
    have hinnerM : difWord GP (2 ^ (0 + 1)) (2 * (N / 2 ^ (0 + 2))) (wordAt c2) (wordAt pt)
        = difWord GP (2 ^ (0 + 1)) (2 * (N / 2 ^ (0 + 2))) (wordAt c2) (psiRep ps) :=
      funext (fun u => difWord_tw_congr GP (0 + 1) (by omega) (wordAt c2)
        (wordAt pt) (psiRep ps) hag u)
    have hswc : ∀ u, wordAt c2 u < GP := fun u => wordAt_lt hc2C GoldFusedBoundary.GP_pos u
    have hmidM : (fun u => ((difWord GP (2 ^ (0 + 1)) (2 * 2 ^ 8) (wordAt c2) (psiRep ps) u
          : ℕ) : ZMod GP))
        = NttMath.difStage (2 ^ (0 + 1)) (2 ^ 8) (ps ^ 2) (resK GP c2) :=
      funext (fun u => difWord_cast GP (2 ^ (0 + 1)) (2 ^ 8) ps (wordAt c2) (psiRep ps)
        (psiRep_cast GoldFusedBoundary.GP_pos ps) hswc u)
    have hlt2M : ∀ u, difWord GP (2 ^ (0 + 1)) (2 * 2 ^ 8) (wordAt c2) (psiRep ps) u < GP :=
      fun u => difWord_lt GP _ _ GoldFusedBoundary.GP_pos _ _ u
    have hresM : ((difWord GP (2 ^ 0) (2 * (N / 2 ^ (0 + 1)))
          (difWord GP (2 ^ (0 + 1)) (2 * (N / 2 ^ (0 + 2))) (wordAt c2) (wordAt pt))
          (wordAt pt) t : ℕ) : ZMod GP)
        = NttMath.difRun (ps ^ 2) 2 (2 ^ 8) (resK GP c2) t := by
      rw [hinnerM, difWord_tw_congr GP 0 (by omega) _ (wordAt pt) (psiRep ps) hag t,
        hstepM1, hstepM2,
        difWord_cast GP (2 ^ 0) (2 ^ 9) ps _ (psiRep ps) (psiRep_cast GoldFusedBoundary.GP_pos ps)
          hlt2M t, hmidM]
      rfl
    have hFtw : NttMath.difRun (ps ^ 2) 10 1 F t
        = NttMath.difRun (ps ^ 2) 10 1
            (NttMath.twistR ps (fun u => ((HachiEquiv.Ring.wordN a u : ℕ) : ZMod GP))) t :=
      difRun_congr (ps ^ 2) 10 (by norm_num) 1 F _
        (fun u hu => twSrc_cast a pt ps hptv u hu) t ht
  · rw [resK, he0w t ht, macAt_cast, show ((pfW pf0 baseU.val t : ℕ) : ZMod GP) = A0 t
      from hA0 t ht, hresM, hc2v t ht, hFtw]
    rfl
  · rw [resK, he1w t ht, macAt_cast, show ((pfW pf1 baseU.val t : ℕ) : ZMod GP) = A1 t
      from hA1 t ht, hresM, hc2v t ht, hFtw]
    rfl

end T52a

/-! ## The two-lane chunk

[`GoldDot.gold_terms_spec`] with a second accumulator. The right operand is
transformed **once** and multiply-accumulated into both prepared tables, which
is the entire performance claim of card T35; on the proof side it means one
loop whose invariant is two copies of the same `termFwd` sum, not two loops.

Since card T52a each term is one [`gold_dot_one_fused_limbs2_spec`] step -- the
twist, the transform and both MACs in five passes -- where it was
`load_twisted_into`, `gold_forward` and two `mac_into_gold_off`, and the loop
carries the transform's buffer pair (`scratch`, `cur`), both `Canon`, as
[`GoldDot.gold_terms_spec`]'s does. The prepared tables no longer need to be
canonical: the fused MAC reads them only through `gold_mul`.

The two prepared tables are the transforms of the two limbs, so the
conclusion is stated over two abstract left operands `a0`, `a1` -- layer 5
instantiates them at [`limb_at`]'s outputs. -/

-- The chunk's context runs to forty-odd hypotheses and the elaborator's
-- default depth does not survive it. `set_option` goes before the
-- declaration, not between a docstring and it.
set_option maxRecDepth 8000 in
theorem limb_terms_spec (f0 f1 : alloc.vec.Vec Std.U64)
    (a0 a1 b : alloc.vec.Vec ring.Rq) (startU endU nU : Std.Usize)
    (pt : alloc.vec.Vec Std.U64) (acc0 acc1 scratch cur : alloc.vec.Vec Std.U64)
    (jU : Std.Usize) (ps : ZMod GP)
    (hn : nU.val = N) (hord : ps ^ N = -1)
    (hptC : Canon GP pt) (hptv : ∀ e, e < N → resK GP pt e = ps ^ e)
    (hpl0 : endU.val * N ≤ f0.val.length) (hpl1 : endU.val * N ≤ f1.val.length)
    (hpv0 : ∀ j, j < endU.val → ∀ t, t < N →
        resK GP f0 (j * N + t)
          = NttMath.difRun (ps ^ 2) 10 1 (NttMath.twistR ps (entryK GP a0 j)) t)
    (hpv1 : ∀ j, j < endU.val → ∀ t, t < N →
        resK GP f1 (j * N + t)
          = NttMath.difRun (ps ^ 2) 10 1 (NttMath.twistR ps (entryK GP a1 j)) t)
    (hbwf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbe : endU.val ≤ b.val.length)
    (hjs : startU.val ≤ jU.val) (hje : jU.val ≤ endU.val)
    (hacc0C : Canon GP acc0) (hacc1C : Canon GP acc1) (hscC : Canon GP scratch)
    (hcurC : Canon GP cur)
    (hval0 : ∀ t, t < N → resK GP acc0 t
              = ∑ u ∈ Finset.Ico startU.val jU.val, termFwd ps a0 b u t)
    (hval1 : ∀ t, t < N → resK GP acc1 t
              = ∑ u ∈ Finset.Ico startU.val jU.val, termFwd ps a1 b u t) :
    ring.dot_prep_chunk_limbs2_loop f0 f1 b endU nU pt acc0 acc1 scratch cur jU
      ⦃ z => Canon GP z.1 ∧ Canon GP z.2.1 ∧ Canon GP z.2.2
             ∧ (∀ t, t < N → resK GP z.1 t
                 = ∑ u ∈ Finset.Ico startU.val endU.val, termFwd ps a0 b u t)
             ∧ (∀ t, t < N → resK GP z.2.1 t
                 = ∑ u ∈ Finset.Ico startU.val endU.val, termFwd ps a1 b u t) ⦄ := by
  rw [ring.dot_prep_chunk_limbs2_loop]
  apply loop.spec_decr_nat (fun r => endU.val - r.2.2.2.2.val)
    (fun r => startU.val ≤ r.2.2.2.2.val ∧ r.2.2.2.2.val ≤ endU.val
      ∧ Canon GP r.1 ∧ Canon GP r.2.1 ∧ Canon GP r.2.2.1 ∧ Canon GP r.2.2.2.1
      ∧ (∀ t, t < N → resK GP r.1 t
              = ∑ u ∈ Finset.Ico startU.val r.2.2.2.2.val, termFwd ps a0 b u t)
      ∧ (∀ t, t < N → resK GP r.2.1 t
              = ∑ u ∈ Finset.Ico startU.val r.2.2.2.2.val, termFwd ps a1 b u t))
  · rintro ⟨d0, d1, sc, cu, jj⟩ ⟨hjjs, hjje, hcd0, hcd1, hcsc, hcuC, hw0, hw1⟩
    dsimp only at hjjs hjje hcd0 hcd1 hcsc hcuC hw0 hw1
    simp only [ring.dot_prep_chunk_limbs2_loop.body]
    by_cases hlt : jj < endU
    · rw [if_pos hlt]
      have hjjlt : jj.val < endU.val := by clear * - hlt; scalar_tac
      have hjb : jj.val < b.val.length := by omega
      step as ⟨rq, hrq⟩
      have hrqv : rq = b.val.getD jj.val (alloc.vec.Vec.new cpoly.field.Fp) := by
        rw [hrq, List.getD_eq_getElem _ _ hjb]
      step as ⟨off, hoff⟩
      have hoffv : off.val = jj.val * N := by rw [hoff, hn]
      have hsl : ∀ (f : alloc.vec.Vec Std.U64), endU.val * N ≤ f.val.length →
          off.val + N ≤ f.val.length := by
        intro f hf
        rw [hoffv]
        have h1 : (jj.val + 1) * N ≤ endU.val * N :=
          Nat.mul_le_mul_right N (by clear * - hjjlt; omega)
        have h2 : (jj.val + 1) * N = jj.val * N + N := by ring
        clear * - h1 h2 hf
        omega
      have hFA0 : ∀ t, t < N → ((wordAt f0 (off.val + t) : ℕ) : ZMod GP)
          = NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK GP a0 jj.val)) t := by
        intro t ht
        rw [hoffv]
        simpa only [resK] using hpv0 jj.val hjjlt t ht
      have hFA1 : ∀ t, t < N → ((wordAt f1 (off.val + t) : ℕ) : ZMod GP)
          = NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK GP a1 jj.val)) t := by
        intro t ht
        rw [hoffv]
        simpa only [resK] using hpv1 jj.val hjjlt t ht
      -- card T52a: the whole term, both limbs, in one fused kernel
      step with gold_dot_one_fused_limbs2_spec rq cu sc d0 d1 pt f0 f1 off ps
        (fun t => NttMath.difRun (ps ^ 2) 10 1 (NttMath.twistR ps (entryK GP a0 jj.val)) t)
        (fun t => NttMath.difRun (ps ^ 2) 10 1 (NttMath.twistR ps (entryK GP a1 jj.val)) t)
        (by rw [hrqv]; exact hbwf jj.val hjjlt) hcuC hcsc hcd0 hcd1 hptC hptv
        (hsl f0 hpl0) (hsl f1 hpl1) hFA0 hFA1
        as ⟨e0, e1, cu1, sc1, he0C, he1C, hcu1C, hsc1C, he0v, he1v⟩
      have hFB : NttMath.twistR ps
            (fun u => ((HachiEquiv.Ring.wordN rq u : ℕ) : ZMod GP))
          = NttMath.twistR ps (entryK GP b jj.val) := by
        rw [hrqv]; rfl
      step as ⟨jj1, hjj1⟩
      have hjj1v : jj1.val = jj.val + 1 := by clear * - hjj1; scalar_tac
      have hstep : ∀ (aa : alloc.vec.Vec ring.Rq) (dd ee : alloc.vec.Vec Std.U64),
          (∀ t, t < N → resK GP dd t
            = ∑ u ∈ Finset.Ico startU.val jj.val, termFwd ps aa b u t) →
          (∀ t, t < N → resK GP ee t = resK GP dd t
            + NttMath.difRun (ps ^ 2) 10 1
                (NttMath.twistR ps (entryK GP aa jj.val)) t
              * NttMath.difRun (ps ^ 2) 10 1
                (NttMath.twistR ps (entryK GP b jj.val)) t) →
          ∀ t, t < N → resK GP ee t
            = ∑ u ∈ Finset.Ico startU.val jj1.val, termFwd ps aa b u t := by
        intro aa dd ee hdd hee t ht
        rw [hjj1v, Finset.sum_Ico_succ_top (by omega), ← hdd t ht, hee t ht]
        unfold termFwd
        rw [← HachiEquiv.NttProduct.prod_difRun ps hord (entryK GP aa jj.val)
          (entryK GP b jj.val)
          (NttMath.difRun (ps ^ 2) 10 1 (NttMath.twistR ps (entryK GP aa jj.val)))
          (NttMath.difRun (ps ^ 2) 10 1 (NttMath.twistR ps (entryK GP b jj.val)))
          (fun t' => NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK GP aa jj.val)) t'
            * NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK GP b jj.val)) t')
          (fun t' _ => rfl) (fun t' _ => rfl) (fun t' _ => rfl) t ht]
      refine ⟨by omega, by omega, he0C, he1C, hsc1C, hcu1C, ?_, ?_, by omega⟩
      · exact hstep a0 d0 e0 hw0 (fun t ht => by rw [he0v t ht, hFB])
      · exact hstep a1 d1 e1 hw1 (fun t ht => by rw [he1v t ht, hFB])
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = endU.val := by clear * - hlt hjje; scalar_tac
      exact ⟨hcd0, hcd1, hcsc, by rw [heq] at hw0; exact hw0, by rw [heq] at hw1; exact hw1⟩
  · exact ⟨hjs, hje, hacc0C, hacc1C, hscC, hcurC, hval0, hval1⟩

/-! ## One lane's read-back

`gold_dot_spec`'s `hwordv` step, factored so the two lanes share it: given an
untwisted buffer whose residues are the offset convolution sum, its *words*
are `offConvSumB`, because that natural number fits `GP` whole. -/

theorem lane_words_eq (B C : ℕ) (a b : alloc.vec.Vec ring.Rq)
    (words : alloc.vec.Vec Std.U64) (scaled : Std.U64) (st en : ℕ)
    (hwC : Canon GP words)
    (had : ∀ u, u < en → BoundedWf B (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hawf : ∀ u, u < en → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbwf : ∀ u, u < en → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hL : en - st ≤ C) (hfit : 2 * C * BOUNDB B < GP)
    (hscaled : ((scaled.val : ℕ) : ZMod GP) = (((en - st) * BOUNDB B : ℕ) : ZMod GP))
    (hres : ∀ t, t < N → resK GP words t
      = (∑ u ∈ Finset.Ico st en,
          NttMath.negConvR N (entryK GP a u) (entryK GP b u) t)
        + ((scaled.val : ℕ) : ZMod GP)) :
    ∀ k, k < N → wordAt words k = offConvSumB B a b st en k := by
  intro k hk
  have hlt : offConvSumB B a b st en k < GP :=
    offConvSumB_lt B C GP a b st en k had hbwf hL hfit
  have hcast : ((wordAt words k : ℕ) : ZMod GP)
      = ((offConvSumB B a b st en k : ℕ) : ZMod GP) := by
    have hle := negQB_sum_le B a b st en k had hbwf
    have hle' : (∑ u ∈ Finset.Ico st en,
          HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
               (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
        ≤ (∑ u ∈ Finset.Ico st en,
            HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                 (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
          + (en - st) * BOUNDB B := le_trans hle (Nat.le_add_left _ _)
    have h1 := hres k hk
    rw [resK] at h1
    rw [h1]
    unfold offConvSumB
    rw [Nat.cast_sub hle', Nat.cast_add]
    have hterm : ∀ u, NttMath.negConvR N (entryK GP a u) (entryK GP b u) k
        = ((HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
              (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod GP)
          - ((HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
              (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod GP) := by
      intro u
      rw [NttMath.negConvR, ordConv_entryK_pos GP a b u k hk,
        ordConv_entryK_neg GP a b u k hk]
    rw [Finset.sum_congr rfl (fun u _ => hterm u), Finset.sum_sub_distrib, hscaled]
    push_cast
    ring
  have h2 := HachiEquiv.NttProduct.natCast_inj_of_lt (wordAt_lt hwC HachiEquiv.GoldDot.GP_pos k) hcast
  rwa [Nat.mod_eq_of_lt hlt] at h2

/-! ## The chunk

[`GoldDot.gold_dot_spec`]'s shape at a chunk and two lanes. The offset is
`GOLD_LOFF2 = N·q·2^16`, which is `BOUNDB 65536` on the nose -- checked, not
asserted -- and a multiple of `q`, so it vanishes when the words are read back
mod `q` in the dot above. -/

theorem gold_loff2_val : (ring.GOLD_LOFF2).val = BOUNDB 65536 := by
  simp only [ring.GOLD_LOFF2, BOUNDB, N, HachiEquiv.NttProduct.q]
  norm_num

set_option maxRecDepth 8000 in
theorem limb_chunk_spec (f0 f1 : alloc.vec.Vec Std.U64)
    (a0 a1 b : alloc.vec.Vec ring.Rq) (startU endU : Std.Usize)
    (hpl0 : endU.val * N ≤ f0.val.length) (hpl1 : endU.val * N ≤ f1.val.length)
    (hpc0 : ∀ u ∈ f0.val, u.val < GP) (hpc1 : ∀ u ∈ f1.val, u.val < GP)
    (hpv0 : ∀ j, j < endU.val → ∀ t, t < N →
        resK GP f0 (j * N + t)
          = NttMath.difRun (((ntt.GOLD_PSI.val : ℕ) : ZMod GP) ^ 2) 10 1
              (NttMath.twistR ((ntt.GOLD_PSI.val : ℕ) : ZMod GP) (entryK GP a0 j)) t)
    (hpv1 : ∀ j, j < endU.val → ∀ t, t < N →
        resK GP f1 (j * N + t)
          = NttMath.difRun (((ntt.GOLD_PSI.val : ℕ) : ZMod GP) ^ 2) 10 1
              (NttMath.twistR ((ntt.GOLD_PSI.val : ℕ) : ZMod GP) (entryK GP a1 j)) t)
    (had0 : ∀ u, u < endU.val → BoundedWf 65536
      (a0.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (had1 : ∀ u, u < endU.val → BoundedWf 65536
      (a1.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (haw0 : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (a0.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (haw1 : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (a1.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbwf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbe : endU.val ≤ b.val.length) (hse : startU.val ≤ endU.val)
    (hchunk : endU.val - startU.val ≤ 32) :
    ring.dot_prep_chunk_limbs2 f0 f1 b startU endU ring.GOLD_LOFF2
      ⦃ z => Canon GP z.1 ∧ Canon GP z.2
             ∧ (∀ k, k < N → wordAt z.1 k
                 = offConvSumB 65536 a0 b startU.val endU.val k)
             ∧ (∀ k, k < N → wordAt z.2 k
                 = offConvSumB 65536 a1 b startU.val endU.val k) ⦄ := by
  set ps : ZMod GP := ((ntt.GOLD_PSI.val : ℕ) : ZMod GP) with hpsdef
  set psii : ZMod GP := ((ntt.GOLD_PSIINV.val : ℕ) : ZMod GP) with hpsiidef
  have hord : ps ^ N = -1 := HachiEquiv.GoldDot.gpsi_ord
  have hpinv : ps * psii = 1 := HachiEquiv.GoldDot.gpsi_inv
  have hfit : 2 * 32 * BOUNDB 65536 < GP := by
    have := boundB_fit_limb2
    simpa only [GP] using this
  rw [ring.dot_prep_chunk_limbs2]
  step with HachiEquiv.GoldTransform.gold_psi_table_cast ntt.GOLD_PSI (by decide +kernel)
    as ⟨pt, hptC, hptv⟩
  step with HachiEquiv.GoldTransform.gold_psi_table_cast ntt.GOLD_PSIINV (by decide +kernel)
    as ⟨it, hitC, hitv⟩
  step with zeros_canon_zero GP HachiEquiv.GoldDot.GP_pos as ⟨z0, hz0C, hz0v⟩
  step with limb_terms_spec f0 f1 a0 a1 b startU endU ntt.NTT_LEN pt z0 z0 z0 z0
    startU ps HachiEquiv.NttStage.ntt_NTT_LEN_val hord hptC hptv hpl0 hpl1 hpv0 hpv1
    hbwf hbe (le_refl _) hse hz0C hz0C hz0C hz0C
    (by intro t ht; rw [hz0v t ht]; simp) (by intro t ht; rw [hz0v t ht]; simp)
    as ⟨A0, A1, sc, hA0C, hA1C, hscC, hA0v, hA1v⟩
  step as ⟨len0, hlen0⟩
  have hcn : lift (UScalar.cast .U64 len0) ⦃ y => y.val = len0.val ⦄ :=
    UScalar.cast_inBounds_spec .U64 len0 (by
      have hl : len0.val ≤ 32 := by clear * - hlen0 hchunk; scalar_tac
      have hm : (UScalar.max UScalarTy.U64 : ℕ) = 18446744073709551615 := by
        simp only [UScalar.max, UScalarTy.numBits]; norm_num
      omega)
  step with hcn as ⟨lw, hlw⟩
  have hlwv : lw.val = endU.val - startU.val := by
    rw [hlw]; clear * - hlen0; scalar_tac
  step with HachiEquiv.GoldArith.gold_mul_spec ring.GOLD_LOFF2 lw
    as ⟨scaled, hscv, hsclt⟩
  have hscaled : ((scaled.val : ℕ) : ZMod GP)
      = (((endU.val - startU.val) * BOUNDB 65536 : ℕ) : ZMod GP) := by
    rw [hscv, gold_loff2_val, hlwv, ZMod.natCast_mod]
    push_cast
    ring
  -- the two lanes, each an inverse transform and an untwist
  step with HachiEquiv.GoldTransform.gold_inverse_spec A0 sc it hA0C hscC hitC psii hitv
    as ⟨v0, s0, hv0C, hs0C, hv0v⟩
  step with HachiEquiv.GoldDot.gold_untwist_cast v0 it scaled hv0C hitC hsclt psii hitv
    as ⟨w0, hw0C, hw0v⟩
  step with HachiEquiv.GoldTransform.gold_inverse_spec A1 s0 it hA1C hs0C hitC psii hitv
    as ⟨v1, s1, hv1C, hs1C, hv1v⟩
  step with HachiEquiv.GoldDot.gold_untwist_cast v1 it scaled hv1C hitC hsclt psii hitv
    as ⟨w1, hw1C, hw1v⟩
  refine ⟨hw0C, hw1C, ?_, ?_⟩
  · refine lane_words_eq 65536 32 a0 b w0 scaled startU.val endU.val hw0C had0 haw0
      hbwf hchunk hfit hscaled ?_
    intro t ht
    have hPR : ∀ t', t' < N → resK GP A0 t'
        = NttMath.difRun (ps ^ 2) 10 1
            (fun t'' => ∑ u ∈ Finset.Ico startU.val endU.val,
              NttMath.cyclicConv N (NttMath.twistR ps (entryK GP a0 u))
                (NttMath.twistR ps (entryK GP b u)) t'') t' := by
      intro t' ht'
      rw [hA0v t' ht', NttMath.difRun_sum (ps ^ 2) 10 1
        (Finset.Ico startU.val endU.val)
        (fun u => NttMath.cyclicConv N (NttMath.twistR ps (entryK GP a0 u))
          (NttMath.twistR ps (entryK GP b u)))]
      simp only [termFwd, hpsdef]
    have hIV := HachiEquiv.NttProduct.inv_value ps psii hpinv
      (fun t'' => ∑ u ∈ Finset.Ico startU.val endU.val,
        NttMath.cyclicConv N (NttMath.twistR ps (entryK GP a0 u))
          (NttMath.twistR ps (entryK GP b u)) t'')
      (resK GP A0) (resK GP v0) hPR hv0v
    rw [hw0v t ht, hIV t ht,
      untwist_value_sum ps psii ((ntt.GOLD_NINV.val : ℕ) : ZMod GP) hord hpinv
        HachiEquiv.GoldDot.gninv_inv (Finset.Ico startU.val endU.val)
        (fun u => entryK GP a0 u) (fun u => entryK GP b u) t ht]
  · refine lane_words_eq 65536 32 a1 b w1 scaled startU.val endU.val hw1C had1 haw1
      hbwf hchunk hfit hscaled ?_
    intro t ht
    have hPR : ∀ t', t' < N → resK GP A1 t'
        = NttMath.difRun (ps ^ 2) 10 1
            (fun t'' => ∑ u ∈ Finset.Ico startU.val endU.val,
              NttMath.cyclicConv N (NttMath.twistR ps (entryK GP a1 u))
                (NttMath.twistR ps (entryK GP b u)) t'') t' := by
      intro t' ht'
      rw [hA1v t' ht', NttMath.difRun_sum (ps ^ 2) 10 1
        (Finset.Ico startU.val endU.val)
        (fun u => NttMath.cyclicConv N (NttMath.twistR ps (entryK GP a1 u))
          (NttMath.twistR ps (entryK GP b u)))]
      simp only [termFwd, hpsdef]
    have hIV := HachiEquiv.NttProduct.inv_value ps psii hpinv
      (fun t'' => ∑ u ∈ Finset.Ico startU.val endU.val,
        NttMath.cyclicConv N (NttMath.twistR ps (entryK GP a1 u))
          (NttMath.twistR ps (entryK GP b u)) t'')
      (resK GP A1) (resK GP v1) hPR hv1v
    rw [hw1v t ht, hIV t ht,
      untwist_value_sum ps psii ((ntt.GOLD_NINV.val : ℕ) : ZMod GP) hord hpinv
        HachiEquiv.GoldDot.gninv_inv (Finset.Ico startU.val endU.val)
        (fun u => entryK GP a1 u) (fun u => entryK GP b u) t ht]

/-! ## The recombination

`r₀ + 2¹⁶·r₁ mod q`, one coefficient at a time. Both lane words are below
`GP < 2^64`, so `w₀ + 2¹⁶·w₁ < 2^80` and the `u128` holds it with room; the
`% q` at the end is the only reduction in the whole dot. -/

set_option maxRecDepth 8000 in
theorem limb_out_loop_spec (degU : Std.Usize) (qwU : Std.U128)
    (w0 w1 : alloc.vec.Vec Std.U64) (out : alloc.vec.Vec cpoly.field.Fp)
    (tU : Std.Usize) (X0 X1 : ℕ → ℕ)
    (hdeg : degU.val = N) (hqw : qwU.val = HachiEquiv.NttProduct.q)
    (hw0 : ∀ k, k < N → wordAt w0 k = X0 k) (hw1 : ∀ k, k < N → wordAt w1 k = X1 k)
    (hc0 : Canon GP w0) (hc1 : Canon GP w1)
    (ht : tU.val ≤ N) (hlen : out.val.length = tU.val)
    (hred : ∀ x ∈ out.val, x.val < HachiEquiv.NttProduct.q)
    (hval : ∀ k, k < tU.val → HachiEquiv.Ring.coeffK out k
      = ((X0 k : ℕ) : ZMod HachiEquiv.NttProduct.q)
        + ((65536 : ℕ) : ZMod HachiEquiv.NttProduct.q)
          * ((X1 k : ℕ) : ZMod HachiEquiv.NttProduct.q)) :
    ring.dot_prepared_limbs2_loop0_loop0 degU qwU (w0, w1) out tU
      ⦃ z => HachiEquiv.Ring.Wf z ∧ ∀ k, k < N → HachiEquiv.Ring.coeffK z k
          = ((X0 k : ℕ) : ZMod HachiEquiv.NttProduct.q)
            + ((65536 : ℕ) : ZMod HachiEquiv.NttProduct.q)
              * ((X1 k : ℕ) : ZMod HachiEquiv.NttProduct.q) ⦄ := by
  have hqpos : 0 < HachiEquiv.NttProduct.q := by
    simp only [HachiEquiv.NttProduct.q]; norm_num
  rw [ring.dot_prepared_limbs2_loop0_loop0]
  apply loop.spec_decr_nat (fun s => N - s.2.val)
    (fun s => s.2.val ≤ N ∧ s.1.val.length = s.2.val
      ∧ (∀ x ∈ s.1.val, x.val < HachiEquiv.NttProduct.q)
      ∧ ∀ k, k < s.2.val → HachiEquiv.Ring.coeffK s.1 k
          = ((X0 k : ℕ) : ZMod HachiEquiv.NttProduct.q)
            + ((65536 : ℕ) : ZMod HachiEquiv.NttProduct.q)
              * ((X1 k : ℕ) : ZMod HachiEquiv.NttProduct.q))
  · rintro ⟨o1, t1⟩ ⟨ht1, hl1, hr1, hv1⟩
    dsimp only at ht1 hl1 hr1 hv1
    simp only [ring.dot_prepared_limbs2_loop0_loop0.body]
    by_cases hlt : t1 < degU
    · rw [if_pos hlt]
      have htlt : t1.val < N := by rw [← hdeg]; clear * - hlt hdeg; scalar_tac
      have hb0 : t1.val < w0.val.length := by rw [hc0.1]; exact htlt
      have hb1 : t1.val < w1.val.length := by rw [hc1.1]; exact htlt
      step as ⟨x0, hx0⟩
      have hx0v : x0.val = X0 t1.val := by
        rw [hx0, ← wordAt_of_lt (v := w0) (t := t1.val) hb0, hw0 t1.val htlt]
      have hcast0 : lift (UScalar.cast .U128 x0) ⦃ y => y.val = x0.val ⦄ :=
        UScalar.cast_inBounds_spec .U128 x0 (HachiEquiv.NttCRT.u64_le_u128_max x0)
      step with hcast0 as ⟨y0, hy0⟩
      step as ⟨x1, hx1⟩
      have hx1v : x1.val = X1 t1.val := by
        rw [hx1, ← wordAt_of_lt (v := w1) (t := t1.val) hb1, hw1 t1.val htlt]
      have hcast1 : lift (UScalar.cast .U128 x1) ⦃ y => y.val = x1.val ⦄ :=
        UScalar.cast_inBounds_spec .U128 x1 (HachiEquiv.NttCRT.u64_le_u128_max x1)
      step with hcast1 as ⟨y1, hy1⟩
      -- both lane words are below `GP < 2^64`, so the shifted sum fits a `u128`
      have hx0lt : x0.val < GP := by
        rw [hx0]; exact hc0.2 _ (List.getElem_mem hb0)
      have hx1lt : x1.val < GP := by
        rw [hx1]; exact hc1.2 _ (List.getElem_mem hb1)
      have hu128 : (Std.U128.max : ℕ) = 340282366920938463463374607431768211455 := by
        simp only [Std.U128.max, UScalar.max, Std.U128.numBits]
        norm_num
      have hGP : (GP : ℕ) = 18446744069414584321 := rfl
      have hmul : 65536 * y1.val ≤ Std.U128.max := by rw [hy1]; omega
      step as ⟨p1, hp1⟩
      have hadd : y0.val + p1.val ≤ Std.U128.max := by rw [hp1, hy0, hy1]; omega
      step as ⟨sm, hsm⟩
      have hqwpos : 0 < qwU.val := by rw [hqw]; exact hqpos
      step as ⟨rd, hrd⟩
      have hrdv : rd.val = (x0.val + 65536 * x1.val) % HachiEquiv.NttProduct.q := by
        rw [hrd, hsm, hp1, hy0, hy1, hqw]
      have hrdlt : rd.val < HachiEquiv.NttProduct.q := by
        rw [hrdv]; exact Nat.mod_lt _ hqpos
      have hcast2 : lift (UScalar.cast .U64 rd) ⦃ y => y.val = rd.val ⦄ :=
        UScalar.cast_inBounds_spec .U64 rd (by
          have hm : (UScalar.max UScalarTy.U64 : ℕ) = 18446744073709551615 := by
            simp only [UScalar.max, UScalarTy.numBits]; norm_num
          have : HachiEquiv.NttProduct.q = 4294967197 := rfl
          omega)
      step with hcast2 as ⟨rw64, hrw64⟩
      step with fp_new_rep' rw64 as ⟨f, hf⟩
      have hfv : f.val = rd.val := by
        rw [hf, hrw64, Nat.mod_eq_of_lt hrdlt]
      step as ⟨o2, ho2⟩
      step as ⟨t2, ht2⟩
      have ht2v : t2.val = t1.val + 1 := by clear * - ht2; scalar_tac
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · rw [ho2, ht2v, List.length_append, hl1]; simp
      · intro x hx
        rw [ho2] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hr1 x h
        · rw [List.mem_singleton.mp h, hfv]; exact hrdlt
      · intro k hk
        rw [ht2v] at hk
        rcases Nat.lt_or_ge k t1.val with hklt | hkge
        · simp only [HachiEquiv.Ring.coeffK]
          rw [ho2, HachiEquiv.GoldTransform.getD_append_lt' _ _ _ (by omega)]
          exact hv1 k hklt
        · have hkeq : k = o1.val.length := by omega
          simp only [HachiEquiv.Ring.coeffK]
          rw [hkeq, ho2, HachiEquiv.GoldTransform.getD_append_eq', hl1]
          simp only [HachiEquiv.Field.toK, hfv, hrdv, hx0v, hx1v]
          rw [ZMod.natCast_mod]
          push_cast
          ring
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : t1.val = N := by
        have : degU.val ≤ t1.val := by clear * - hlt; scalar_tac
        omega
      exact ⟨⟨by rw [hl1, heq], hr1⟩, fun k hk => hv1 k (by rw [heq]; exact hk)⟩
  · exact ⟨ht, hlen, hred, hval⟩

/-! ## The chunked dot

`RingTwoLane.prep_chunk_ga_loop_spec`'s shape, with the two Barrett-and-
Goldilocks lanes replaced by two Goldilocks limb lanes and Garner replaced by
the shift-and-add. The conclusion is `dot_prepared_spec`'s, word for word:
what changed is how the value is reached, not what it is. -/

/-- One prepared table is the forward transform of its operand's entries.
`RingTwoLane` has the same predicate, but that file is card G2's and this card
supersedes it, so the definition is restated rather than imported. -/
def PrepAtLimb (pfwd : alloc.vec.Vec Std.U64) (a : alloc.vec.Vec ring.Rq) (n : ℕ) : Prop :=
  n * N ≤ pfwd.val.length
  ∧ (∀ u ∈ pfwd.val, u.val < GP)
  ∧ ∀ j, j < n → ∀ t, t < N →
      resK GP pfwd (j * N + t)
        = NttMath.difRun (((ntt.GOLD_PSI.val : ℕ) : ZMod GP) ^ 2) 10 1
            (NttMath.twistR ((ntt.GOLD_PSI.val : ℕ) : ZMod GP) (entryK GP a j)) t

/-- The two limbs of `a`, as the dot needs them: right length, reduced,
bounded by `2^16`, and reconstructing `a`'s coefficients. -/
def LimbsOf (a a0 a1 : alloc.vec.Vec ring.Rq) (n : ℕ) : Prop :=
  (∀ u, u < n → HachiEquiv.Ring.Wf (a0.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
  ∧ (∀ u, u < n → HachiEquiv.Ring.Wf (a1.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
  ∧ (∀ u, u < n → BoundedWf 65536 (a0.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
  ∧ (∀ u, u < n → BoundedWf 65536 (a1.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
  ∧ ∀ u, u < n → ∀ t, HachiEquiv.Ring.coeffK
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) t
    = HachiEquiv.Ring.coeffK (a0.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) t
      + ((65536 : ℕ) : ZMod HachiEquiv.NttProduct.q)
        * HachiEquiv.Ring.coeffK (a1.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) t

/-- One chunk's contribution, in `ZMod q`: the two lanes' offset sums, shifted
and added, are the chunk's slice of `Σ negConv a b`. Layers 1 and 3 meet
here -- `offConvSumB_cast_q` on each lane, then `negConv_split`. -/
theorem limb_chunk_value (a a0 a1 b : alloc.vec.Vec ring.Rq) (st en k : ℕ)
    (hk : k < N) (hl : LimbsOf a a0 a1 en)
    (hbwf : ∀ u, u < en → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))) :
    ((offConvSumB 65536 a0 b st en k : ℕ) : ZMod HachiEquiv.NttProduct.q)
      + ((65536 : ℕ) : ZMod HachiEquiv.NttProduct.q)
        * ((offConvSumB 65536 a1 b st en k : ℕ) : ZMod HachiEquiv.NttProduct.q)
      = ∑ u ∈ Finset.Ico st en, HachiEquiv.Ring.negConv
          (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
          (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k := by
  obtain ⟨hw0, hw1, hb0, hb1, hrec⟩ := hl
  have hqq : HachiEquiv.NttProduct.q = HachiEquiv.Field.q := rfl
  rw [hqq] at *
  rw [offConvSumB_cast_q 65536 a0 b st en k hk hb0 hw0 hbwf,
      offConvSumB_cast_q 65536 a1 b st en k hk hb1 hw1 hbwf,
      Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  simp only [Finset.mem_Ico] at hu
  exact (negConv_split _ _ _ _ 65536 (hrec u hu.2) k).symm

set_option maxRecDepth 20000 in
/-- The chunk loop of `dot_prepared_limbs2`. -/
theorem limb_dot_loop_spec (prep : ring.PreparedVecL2)
    (a a0 a1 b : alloc.vec.Vec ring.Rq) (nU degU : Std.Usize) (qwU : Std.U128)
    (acc : ring.Rq) (startU : Std.Usize)
    (hbw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbn : nU.val ≤ b.val.length)
    (hl : LimbsOf a a0 a1 nU.val)
    (hp0 : PrepAtLimb prep.f0 a0 nU.val)
    (hp1 : PrepAtLimb prep.f1 a1 nU.val)
    (hdeg : degU.val = N) (hqw : qwU.val = HachiEquiv.NttProduct.q)
    (hs : startU.val ≤ nU.val) (hacc : HachiEquiv.Ring.Wf acc)
    (hval : ∀ k, k < N → HachiEquiv.Ring.coeffK acc k
              = ∑ u ∈ Finset.range startU.val, HachiEquiv.Ring.negConv
                  (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                  (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k) :
    ring.dot_prepared_limbs2_loop0 prep b nU degU qwU acc startU
      ⦃ z => HachiEquiv.Ring.Wf z ∧ ∀ k, k < N → HachiEquiv.Ring.coeffK z k
              = ∑ u ∈ Finset.range nU.val, HachiEquiv.Ring.negConv
                  (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                  (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k ⦄ := by
  rw [ring.dot_prepared_limbs2_loop0]
  apply loop.spec_decr_nat (fun r => nU.val - r.2.val)
    (fun r => r.2.val ≤ nU.val ∧ HachiEquiv.Ring.Wf r.1
      ∧ ∀ k, k < N → HachiEquiv.Ring.coeffK r.1 k
              = ∑ u ∈ Finset.range r.2.val, HachiEquiv.Ring.negConv
                  (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                  (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k)
  · rintro ⟨d, st⟩ ⟨hst, hdw, hdv⟩
    dsimp only at hst hdw hdv
    simp only [ring.dot_prepared_limbs2_loop0.body]
    by_cases hlt : st < nU
    · rw [if_pos hlt]
      have hstlt : st.val < nU.val := by clear * - hlt; scalar_tac
      step as ⟨rem, hrem⟩
      have hite : (if rem < ring.LIMB2_CHUNK then ok rem else ok ring.LIMB2_CHUNK)
          = ok (if rem < ring.LIMB2_CHUNK then rem else ring.LIMB2_CHUNK) := by
        split_ifs <;> rfl
      rw [hite]
      set tk : Std.Usize := if rem < ring.LIMB2_CHUNK then rem else ring.LIMB2_CHUNK
        with htk
      have hdc : (ring.LIMB2_CHUNK).val = 32 := by simp only [ring.LIMB2_CHUNK]; rfl
      have hremv : rem.val = nU.val - st.val := hrem
      have htkle : tk.val ≤ rem.val := by
        rw [htk]; split_ifs with hc
        · exact le_refl _
        · have : ¬ (rem.val < (ring.LIMB2_CHUNK).val) := by clear * - hc; scalar_tac
          omega
      have htk32 : tk.val ≤ 32 := by
        rw [htk]; split_ifs with hc
        · have : rem.val < (ring.LIMB2_CHUNK).val := by clear * - hc; scalar_tac
          rw [hdc] at this; omega
        · rw [hdc]
      -- the chunk is non-empty, which is what makes the measure decrease
      have htkpos : 0 < tk.val := by
        rw [htk]; split_ifs
        · clear * - hremv hstlt; omega
        · rw [hdc]; omega
      clear_value tk
      step as ⟨en, hen⟩
      have henv : en.val = st.val + tk.val := hen
      have hennU : en.val ≤ nU.val := by
        clear * - henv htkle hremv hstlt; omega
      have hsen : st.val ≤ en.val := by clear * - henv; omega
      have hL : en.val - st.val ≤ 32 := by clear * - henv htk32; omega
      have hbwe : ∀ u, u < en.val → HachiEquiv.Ring.Wf
          (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) :=
        fun u hu => hbw u (by omega)
      have hbe : en.val ≤ b.val.length := le_trans hennU hbn
      have hle : LimbsOf a a0 a1 en.val := by
        obtain ⟨q0, q1, q2, q3, q4⟩ := hl
        exact ⟨fun u hu => q0 u (by omega), fun u hu => q1 u (by omega),
          fun u hu => q2 u (by omega), fun u hu => q3 u (by omega),
          fun u hu => q4 u (by omega)⟩
      have hmono : ∀ (pf : alloc.vec.Vec Std.U64) (aa : alloc.vec.Vec ring.Rq),
          PrepAtLimb pf aa nU.val →
          en.val * N ≤ pf.val.length
          ∧ (∀ u ∈ pf.val, u.val < GP)
          ∧ ∀ j, j < en.val → ∀ t, t < N →
              resK GP pf (j * N + t)
                = NttMath.difRun (((ntt.GOLD_PSI.val : ℕ) : ZMod GP) ^ 2) 10 1
                    (NttMath.twistR ((ntt.GOLD_PSI.val : ℕ) : ZMod GP)
                      (entryK GP aa j)) t := by
        intro pf aa hpp
        exact ⟨le_trans (Nat.mul_le_mul_right N hennU) hpp.1, hpp.2.1,
          fun j hj t ht => hpp.2.2 j (by omega) t ht⟩
      obtain ⟨g0a, g0b, g0c⟩ := hmono prep.f0 a0 hp0
      obtain ⟨g1a, g1b, g1c⟩ := hmono prep.f1 a1 hp1
      step with limb_chunk_spec prep.f0 prep.f1 a0 a1 b st en g0a g1a g0b g1b
        g0c g1c hle.2.2.1 hle.2.2.2.1 hle.1 hle.2.1 hbwe hbe hsen hL
        as ⟨ws, hws0C, hws1C, hws0v, hws1v⟩
      obtain ⟨W0, W1⟩ := ws
      dsimp only at hws0C hws1C hws0v hws1v
      simp only [alloc.vec.Vec.with_capacity]
      step with limb_out_loop_spec degU qwU W0 W1 (alloc.vec.Vec.new cpoly.field.Fp)
        0#usize (fun k => offConvSumB 65536 a0 b st.val en.val k)
        (fun k => offConvSumB 65536 a1 b st.val en.val k)
        hdeg hqw hws0v hws1v hws0C hws1C (by simp) (by simp)
        (by intro x hx; simp at hx) (by intro k hk; simp at hk)
        as ⟨out1, ho1wf, ho1v⟩
      step with HachiEquiv.Ring.add_spec d out1 hdw ho1wf as ⟨acc1, hacwf, hacv⟩
      refine ⟨hennU, hacwf, ?_, by clear * - henv htkpos hennU hstlt; omega⟩
      intro k hk
      rw [hacv k hk, hdv k hk, ho1v k hk,
        limb_chunk_value a a0 a1 b st.val en.val k hk hle hbwe,
        Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.sum_Ico_consecutive _ (Nat.zero_le _) hsen]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : st.val = nU.val := by clear * - hlt hst; scalar_tac
      exact ⟨hdw, fun k hk => by rw [hdv k hk, heq]⟩
  · exact ⟨hs, hacc, hval⟩

/-- **`ring::dot_prepared_limbs2`.** The value `dot_prepared_spec` computes,
from one Goldilocks lane and two limbs instead of three primes and a CRT. The
statement is `dot_prepared_spec`'s word for word. -/
theorem dot_prepared_limbs2_spec (prep : ring.PreparedVecL2)
    (a a0 a1 b : alloc.vec.Vec ring.Rq) (nU : Std.Usize)
    (hbw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbn : nU.val ≤ b.val.length)
    (hl : LimbsOf a a0 a1 nU.val)
    (hp0 : PrepAtLimb prep.f0 a0 nU.val) (hp1 : PrepAtLimb prep.f1 a1 nU.val) :
    ring.dot_prepared_limbs2 prep b nU
      ⦃ z => HachiEquiv.Ring.Wf z ∧ ∀ k, k < N → HachiEquiv.Ring.coeffK z k
              = ∑ u ∈ Finset.range nU.val, HachiEquiv.Ring.negConv
                  (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                  (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k ⦄ := by
  rw [ring.dot_prepared_limbs2]
  have hcq : lift (UScalar.cast .U128 params.Q) ⦃ y => y.val = (params.Q).val ⦄ :=
    UScalar.cast_inBounds_spec .U128 params.Q (HachiEquiv.NttCRT.u64_le_u128_max _)
  step with hcq as ⟨qw, hqw⟩
  rw [HachiEquiv.Field.params_Q_val] at hqw
  step with HachiEquiv.Ring.zero_spec as ⟨z, hWz, hzv⟩
  exact limb_dot_loop_spec prep a a0 a1 b nU params.RING_DEGREE qw z 0#usize
    hbw hbn hl hp0 hp1 HachiEquiv.Ring.params_RING_DEGREE_val hqw (by simp) hWz
    (by intro k hk; rw [hzv k]; simp)

/-! ## Preparation

`limb_at` twice, then the landed single-lane preparation twice. The only new
content is assembling `LimbsOf` -- the two limbs reconstruct `a` -- out of
`limb_at_spec`'s division form through `coeffK_of_limbs`. -/

theorem prepare_vec_limbs2_spec (a : alloc.vec.Vec ring.Rq) (nU : Std.Usize)
    (haw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (han : nU.val ≤ a.val.length) (hmax : nU.val * N ≤ Std.Usize.max) :
    ring.prepare_vec_limbs2 a nU
      ⦃ prep => prep.len = nU ∧ ∃ a0 a1, LimbsOf a a0 a1 nU.val
          ∧ PrepAtLimb prep.f0 a0 nU.val ∧ PrepAtLimb prep.f1 a1 nU.val ⦄ := by
  have hq : (0 : ℕ) < HachiEquiv.NttProduct.q := by
    simp only [HachiEquiv.NttProduct.q]; norm_num
  have hbq : (65536 : ℕ) ≤ HachiEquiv.NttProduct.q := by
    simp only [HachiEquiv.NttProduct.q]; norm_num
  rw [ring.prepare_vec_limbs2]
  step with limb_at_spec a nU 1#u64 65536#u64 (by simp) (by simp) (by simpa using hbq)
    han haw as ⟨l0, hl0len, hl0wf, hl0bd, hl0v⟩
  step with limb_at_spec a nU 65536#u64 65536#u64 (by simp) (by simp)
    (by simpa using hbq) han haw as ⟨l1, hl1len, hl1wf, hl1bd, hl1v⟩
  have hmem : ∀ (v : alloc.vec.Vec ring.Rq), v.val.length = nU.val →
      (∀ x ∈ v.val, HachiEquiv.Ring.Wf x) →
      ∀ u, u < nU.val → HachiEquiv.Ring.Wf
        (v.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) := by
    intro v hvl hvw u hu
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hvw _ (List.getElem_mem (by omega))
  have hmemb : ∀ (v : alloc.vec.Vec ring.Rq), v.val.length = nU.val →
      (∀ x ∈ v.val, BoundedWf 65536 x) →
      ∀ u, u < nU.val → BoundedWf 65536
        (v.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) := by
    intro v hvl hvw u hu
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hvw _ (List.getElem_mem (by omega))
  have hw0 := hmem l0 hl0len hl0wf
  have hw1 := hmem l1 hl1len hl1wf
  have hb0 := hmemb l0 hl0len hl0bd
  have hb1 := hmemb l1 hl1len hl1bd
  step with HachiEquiv.GoldDot.prepare_one_gold_spec l0 nU hw0 (by omega) hmax
    as ⟨f0, hf0l, hf0c, hf0v⟩
  step with HachiEquiv.GoldDot.prepare_one_gold_spec l1 nU hw1 (by omega) hmax
    as ⟨f1, hf1l, hf1c, hf1v⟩
  have hrec : ∀ u, u < nU.val → ∀ t, HachiEquiv.Ring.coeffK
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) t
    = HachiEquiv.Ring.coeffK (l0.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) t
      + ((65536 : ℕ) : ZMod HachiEquiv.NttProduct.q)
        * HachiEquiv.Ring.coeffK (l1.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) t := by
    intro u hu t
    refine coeffK_of_limbs _ _ _ (haw u hu) ?_ ?_ ?_ ?_ t
    · exact (hw0 u hu).1
    · exact (hw1 u hu).1
    · intro t' ht'
      have := hl0v u hu t' ht'
      simpa using this
    · intro t' ht'
      have := hl1v u hu t' ht'
      simpa using this
  exact ⟨l0, l1, ⟨hw0, hw1, hb0, hb1, hrec⟩, ⟨by omega, hf0c, hf0v⟩,
    ⟨by omega, hf1c, hf1v⟩⟩

end HachiEquiv.RingLimb
