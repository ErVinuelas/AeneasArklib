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

/-! ## The two-lane chunk

[`GoldDot.gold_terms_spec`] with a second accumulator. The right operand is
transformed **once** and multiply-accumulated into both prepared tables, which
is the entire performance claim of card T35; on the proof side it means one
loop whose invariant is two copies of the same `termFwd` sum, not two loops.

The two prepared tables are the transforms of the two limbs, so the
conclusion is stated over two abstract left operands `a0`, `a1` -- layer 5
instantiates them at [`limb_at`]'s outputs. -/

-- The chunk's context runs to forty-odd hypotheses and the elaborator's
-- default depth does not survive it. `set_option` goes before the
-- declaration, not between a docstring and it.
set_option maxRecDepth 8000 in
theorem limb_terms_spec (f0 f1 : alloc.vec.Vec Std.U64)
    (a0 a1 b : alloc.vec.Vec ring.Rq) (startU endU nU : Std.Usize)
    (pt : alloc.vec.Vec Std.U64) (acc0 acc1 scratch buf : alloc.vec.Vec Std.U64)
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
    (hpc0 : ∀ u ∈ f0.val, u.val < GP) (hpc1 : ∀ u ∈ f1.val, u.val < GP)
    (hbwf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbe : endU.val ≤ b.val.length)
    (hjs : startU.val ≤ jU.val) (hje : jU.val ≤ endU.val)
    (hacc0C : Canon GP acc0) (hacc1C : Canon GP acc1) (hscC : Canon GP scratch)
    (hbufl : buf.val.length = N)
    (hval0 : ∀ t, t < N → resK GP acc0 t
              = ∑ u ∈ Finset.Ico startU.val jU.val, termFwd ps a0 b u t)
    (hval1 : ∀ t, t < N → resK GP acc1 t
              = ∑ u ∈ Finset.Ico startU.val jU.val, termFwd ps a1 b u t) :
    ring.dot_prep_chunk_limbs2_loop f0 f1 b endU nU pt acc0 acc1 scratch buf jU
      ⦃ z => Canon GP z.1 ∧ Canon GP z.2.1 ∧ Canon GP z.2.2
             ∧ (∀ t, t < N → resK GP z.1 t
                 = ∑ u ∈ Finset.Ico startU.val endU.val, termFwd ps a0 b u t)
             ∧ (∀ t, t < N → resK GP z.2.1 t
                 = ∑ u ∈ Finset.Ico startU.val endU.val, termFwd ps a1 b u t) ⦄ := by
  rw [ring.dot_prep_chunk_limbs2_loop]
  apply loop.spec_decr_nat (fun r => endU.val - r.2.2.2.2.val)
    (fun r => startU.val ≤ r.2.2.2.2.val ∧ r.2.2.2.2.val ≤ endU.val
      ∧ Canon GP r.1 ∧ Canon GP r.2.1 ∧ Canon GP r.2.2.1
      ∧ r.2.2.2.1.val.length = N
      ∧ (∀ t, t < N → resK GP r.1 t
              = ∑ u ∈ Finset.Ico startU.val r.2.2.2.2.val, termFwd ps a0 b u t)
      ∧ (∀ t, t < N → resK GP r.2.1 t
              = ∑ u ∈ Finset.Ico startU.val r.2.2.2.2.val, termFwd ps a1 b u t))
  · rintro ⟨d0, d1, sc, bf, jj⟩ ⟨hjjs, hjje, hcd0, hcd1, hcsc, hbfl, hw0, hw1⟩
    dsimp only at hjjs hjje hcd0 hcd1 hcsc hbfl hw0 hw1
    simp only [ring.dot_prep_chunk_limbs2_loop.body]
    by_cases hlt : jj < endU
    · rw [if_pos hlt]
      have hjjlt : jj.val < endU.val := by clear * - hlt; scalar_tac
      have hjb : jj.val < b.val.length := by omega
      step as ⟨rq, hrq⟩
      have hrqv : rq = b.val.getD jj.val (alloc.vec.Vec.new cpoly.field.Fp) := by
        rw [hrq, List.getD_eq_getElem _ _ hjb]
      step with load_twisted_into_spec bf rq pt ps
        (by rw [hrqv]; exact hbwf jj.val hjjlt) hbfl hptC hptv as ⟨tb, htbC, htbv⟩
      step with gold_forward_spec tb sc pt htbC hcsc hptC ps hptv
        as ⟨fw, hfw1, hfw2, hfwv⟩
      obtain ⟨v, v1⟩ := fw
      dsimp only at hfw1 hfw2 hfwv
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
      have hFB : ∀ t, t < N → resK GP v t
          = NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK GP b jj.val)) t := by
        intro t ht
        rw [hfwv t ht]
        refine difRun_congr (ps ^ 2) 10 (by norm_num) 1 (resK GP tb)
          (NttMath.twistR ps (entryK GP b jj.val)) ?_ t ht
        intro e he
        rw [htbv e he]
        simp only [NttMath.twistR, entryK, hrqv]
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
      step with gold_mac_off_spec d0 f0 v off nU 0#usize (resK GP d0)
        (fun t => NttMath.difRun (ps ^ 2) 10 1
          (NttMath.twistR ps (entryK GP a0 jj.val)) t)
        hn (by simp) (hsl f0 hpl0) hcd0 hfw1 hpc0 hFA0 (by intro t ht; simp)
        as ⟨e0, he0C, he0v⟩
      step with gold_mac_off_spec d1 f1 v off nU 0#usize (resK GP d1)
        (fun t => NttMath.difRun (ps ^ 2) 10 1
          (NttMath.twistR ps (entryK GP a1 jj.val)) t)
        hn (by simp) (hsl f1 hpl1) hcd1 hfw1 hpc1 hFA1 (by intro t ht; simp)
        as ⟨e1, he1C, he1v⟩
      step as ⟨jj1, hjj1⟩
      have hjj1v : jj1.val = jj.val + 1 := by clear * - hjj1; scalar_tac
      have hstep : ∀ (aa : alloc.vec.Vec ring.Rq) (dd ee : alloc.vec.Vec Std.U64),
          (∀ t, t < N → resK GP dd t
            = ∑ u ∈ Finset.Ico startU.val jj.val, termFwd ps aa b u t) →
          (∀ t, t < N → resK GP ee t = resK GP dd t
            + NttMath.difRun (ps ^ 2) 10 1
                (NttMath.twistR ps (entryK GP aa jj.val)) t
              * resK GP v t) →
          ∀ t, t < N → resK GP ee t
            = ∑ u ∈ Finset.Ico startU.val jj1.val, termFwd ps aa b u t := by
        intro aa dd ee hdd hee t ht
        rw [hjj1v, Finset.sum_Ico_succ_top (by omega), ← hdd t ht, hee t ht, hFB t ht]
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
      refine ⟨by omega, by omega, he0C, he1C, hfw2, hfw1.1, ?_, ?_, by omega⟩
      · exact hstep a0 d0 e0 hw0 he0v
      · exact hstep a1 d1 e1 hw1 he1v
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = endU.val := by clear * - hlt hjje; scalar_tac
      exact ⟨hcd0, hcd1, hcsc, by rw [heq] at hw0; exact hw0, by rw [heq] at hw1; exact hw1⟩
  · exact ⟨hjs, hje, hacc0C, hacc1C, hscC, hbufl, hval0, hval1⟩

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
    hpc0 hpc1 hbwf hbe (le_refl _) hse hz0C hz0C hz0C hz0C.1
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
