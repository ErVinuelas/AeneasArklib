/-
Card T40's signed layer: what a *centred* coefficient is worth in the
Goldilocks lane, and why one lane suffices for the lift commitment.

The digit path (`RingFused`) bounds an operand by `BoundedWf B`, which reads
the **unsigned** word: `wordN b t < B`. The lift commitment's right operand is
`z ‖ digits(ρ)`, and its coefficients are *centred* below `CHAIN_GAMMA = 15`
-- so each word is either below `16` or above `q − 16`, and `BoundedWf 16` is
false for it. This file is the parallel development for that shape: the
encoding the Rust writes, the integer it denotes, and the identity between
them in `ZMod GP`.

The reason it is worth a layer of its own rather than a reinterpretation of
`RingFused`'s: the bound there is on a product of two naturals, here it is on
the absolute value of a signed integer, and `ℕ`-subtraction does not survive
the translation. Everything below is stated over `ℤ` where the sign matters
and over `ℕ` where it does not, and `sgnWord_cast` is the single bridge.
-/
import RingFused
import GoldDot

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.RingSigned

open HachiEquiv.Ring HachiEquiv.GoldArith
open HachiEquiv.NttProduct (q)

/-! ## The encoding

`ring::load_twisted_signed_into` branches on `v ≤ q / 2`: below, the word is
its own value; above, the coefficient is negative and the lane's
representative is `GOLD_P − (q − v)`. [`sgnWord`] is that branch and
[`sInt`] is the integer it is meant to denote. -/

/-- The Goldilocks word a reduced coefficient is loaded as. -/
def sgnWord (c : ℕ) : ℕ := if c ≤ q / 2 then c else GP - (q - c)

/-- The signed integer a reduced coefficient denotes. -/
def sInt (c : ℕ) : ℤ := if c ≤ q / 2 then (c : ℤ) else (c : ℤ) - (q : ℤ)

theorem q_lt_GP : q < GP := by
  simp only [HachiEquiv.NttProduct.q, GP]; norm_num

/-- **The bridge.** The word the Rust writes and the integer it denotes agree
in `ZMod GP`. Below `q / 2` both are the coefficient; above, the word is
`GP − (q − c)`, whose class is `−(q − c) = c − q`. -/
theorem sgnWord_cast {c : ℕ} (hc : c < q) :
    ((sgnWord c : ℕ) : ZMod GP) = ((sInt c : ℤ) : ZMod GP) := by
  unfold sgnWord sInt
  by_cases h : c ≤ q / 2
  · rw [if_pos h, if_pos h]; push_cast; ring
  · rw [if_neg h, if_neg h]
    have hqc : q - c ≤ GP := le_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) q_lt_GP)
    rw [Nat.cast_sub hqc, Nat.cast_sub (le_of_lt hc)]
    have : ((GP : ℕ) : ZMod GP) = 0 := ZMod.natCast_self GP
    rw [this]
    push_cast
    ring

/-- The magnitude of what a reduced coefficient denotes. -/
def sAbs (c : ℕ) : ℕ := (sInt c).natAbs

/-- Centred shortness at `G`: every coefficient denotes an integer of
magnitude at most `G`. This is what `endpiece::lift_short_check` tests and
what `ringswitch::lift_witness_short` guards on, and it is **not**
`RingFused.BoundedWf G` -- a coefficient just below `q` satisfies this and
fails that. -/
def CenteredWf (G : ℕ) (b : ring.Rq) : Prop := ∀ t, sAbs (wordN b t) ≤ G

/-- `centered_abs`, on the nose: the Rust returns `v` below the midpoint and
`q − v` above it, and that is `sAbs`. -/
theorem sAbs_eq {c : ℕ} (hc : c < q) :
    sAbs c = if c ≤ q / 2 then c else q - c := by
  unfold sAbs sInt
  by_cases h : c ≤ q / 2
  · rw [if_pos h, if_pos h]; simp
  · rw [if_neg h, if_neg h]
    have : ((c : ℤ) - (q : ℤ)) = -((q : ℤ) - (c : ℤ)) := by ring
    rw [this, Int.natAbs_neg]
    omega

/-- Below the midpoint the encoding is the identity, so a *small non-negative*
coefficient is loaded unchanged -- which is the case the honest digits take. -/
theorem sgnWord_of_le {c : ℕ} (h : c ≤ q / 2) : sgnWord c = c := if_pos h

/-- `|sInt c|` as an integer is `sAbs c`. The one place the `ℤ`-valued bound
and the `ℕ`-valued shortness predicate meet. -/
theorem abs_sInt (c : ℕ) : |sInt c| = (sAbs c : ℤ) := by
  simp only [sAbs, Int.abs_eq_natAbs]

/-! ## The bound

`RingFused.offConvSumB_lt` bounds a sum of products of naturals; this bounds
the absolute value of a sum of products where one factor is signed. The shape
of the argument is the same -- bound one term, multiply by the count -- and
the arithmetic is not, because `ℕ`-subtraction is not `ℤ`-negation. -/

/-- One output coefficient's signed negacyclic convolution, over `ℤ`.
The wrap contributes with a minus sign, which is what `X^N = −1` means. -/
def sConv (a b : ring.Rq) (k : ℕ) : ℤ :=
  ∑ t ∈ Finset.range N,
    if t ≤ k then (wordN a t : ℤ) * sInt (wordN b (k - t))
    else -((wordN a t : ℤ) * sInt (wordN b (N + k - t)))

/-- The per-term ceiling: a reduced left factor against a `G`-centred right
one is at most `q · G` in absolute value. -/
theorem sConv_term_abs_le {G : ℕ} {a b : ring.Rq} (ha : Wf a) (hb : CenteredWf G b)
    (k t : ℕ) :
    |if t ≤ k then (wordN a t : ℤ) * sInt (wordN b (k - t))
     else -((wordN a t : ℤ) * sInt (wordN b (N + k - t)))| ≤ (q : ℤ) * (G : ℤ) := by
  have hA0 : (0 : ℤ) ≤ (wordN a t : ℤ) := Int.natCast_nonneg _
  have hA : (wordN a t : ℤ) ≤ (q : ℤ) := by exact_mod_cast le_of_lt (wordN_lt ha t)
  have hG : ∀ j : ℕ, |sInt (wordN b j)| ≤ (G : ℤ) := by
    intro j; rw [abs_sInt]; exact_mod_cast hb j
  by_cases h : t ≤ k
  · rw [if_pos h, abs_mul, abs_of_nonneg hA0]
    exact mul_le_mul hA (hG _) (abs_nonneg _) (by positivity)
  · rw [if_neg h, abs_neg, abs_mul, abs_of_nonneg hA0]
    exact mul_le_mul hA (hG _) (abs_nonneg _) (by positivity)

/-- `N` terms, so `N · q · G`. -/
theorem sConv_abs_le {G : ℕ} {a b : ring.Rq} (ha : Wf a) (hb : CenteredWf G b) (k : ℕ) :
    |sConv a b k| ≤ (N : ℤ) * ((q : ℤ) * (G : ℤ)) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ t ∈ Finset.range N,
        |if t ≤ k then (wordN a t : ℤ) * sInt (wordN b (k - t))
         else -((wordN a t : ℤ) * sInt (wordN b (N + k - t)))|
      ≤ ∑ _t ∈ Finset.range N, (q : ℤ) * (G : ℤ) :=
        Finset.sum_le_sum (fun t _ => sConv_term_abs_le ha hb k t)
    _ = (N : ℤ) * ((q : ℤ) * (G : ℤ)) := by
        rw [Finset.sum_const, Finset.card_range]; push_cast; ring

/-- The whole row: the terms `u ∈ [st, en)` summed. -/
def sConvSum (a b : alloc.vec.Vec ring.Rq) (st en k : ℕ) : ℤ :=
  ∑ u ∈ Finset.Ico st en,
    sConv (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
          (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k

/-- The per-term offset of the signed path, `N · q · G`.
[`RingFused.BOUNDB`] is its unsigned counterpart and `ntt::GOLD_SOFF` is this
at `G = 15`. -/
def SBOUND (G : ℕ) : ℕ := N * (q * G)

theorem sbound_15_val : SBOUND 15 = 65970696145920 := by
  simp only [SBOUND, N, HachiEquiv.NttProduct.q]

/-- `ntt::GOLD_SOFF` is `SBOUND 15` -- the constant in the Rust is the bound
this layer proves, not a number beside it. -/
theorem gold_soff_val : (ntt.GOLD_SOFF).val = SBOUND 15 := by
  rw [sbound_15_val]; decide +kernel

/-- **The row's ceiling.** `(en − st)` terms, each `N · q · G`. -/
theorem sConvSum_abs_le {G : ℕ} (a b : alloc.vec.Vec ring.Rq) (st en k : ℕ)
    (ha : ∀ u, u < en → Wf (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hb : ∀ u, u < en → CenteredWf G (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))) :
    |sConvSum a b st en k| ≤ ((en - st : ℕ) : ℤ) * (SBOUND G : ℕ) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ u ∈ Finset.Ico st en,
        |sConv (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
               (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k|
      ≤ ∑ _u ∈ Finset.Ico st en, ((SBOUND G : ℕ) : ℤ) := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        have hue : u < en := (Finset.mem_Ico.mp hu).2
        have := sConv_abs_le (ha u hue) (hb u hue) k
        simpa only [SBOUND, Nat.cast_mul] using this
    _ = ((en - st : ℕ) : ℤ) * ((SBOUND G : ℕ) : ℤ) := by
        rw [Finset.sum_const, Nat.card_Ico]; simp

/-- **The card's fit.** At the pin's `LIFT_COLS = 57 384` terms and
`CHAIN_GAMMA = 15`, twice the row's ceiling is below `GOLD_P`: `2^62.72`
against `2^64`, margin x2.44. This is the one-chunk claim, and it is why
`lift_commit_row_gold` has no chunk loop. -/
theorem sbound_fit_lift : 2 * 57384 * SBOUND 15 < GP := by
  simp only [SBOUND, N, HachiEquiv.NttProduct.q, GP]; norm_num

end HachiEquiv.RingSigned
