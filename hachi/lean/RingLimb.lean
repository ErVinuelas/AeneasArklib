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

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.RingLimb

open HachiEquiv.NttArith HachiEquiv.NttStage HachiEquiv.RingFused

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

end HachiEquiv.RingLimb
