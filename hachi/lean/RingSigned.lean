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

open HachiEquiv.GoldArith
open HachiEquiv.NttStage HachiEquiv.RingFused HachiEquiv.GoldTransform
open HachiEquiv.NttProduct (q)
open HachiEquiv.Ring (wordN Wf wordN_lt)

/-- `Ring.N` and `NttStage.N` are both `1024`; this file opens `NttStage`, so
`N` below is that one and the two are interchangeable by `rfl`. -/
theorem N_eq : N = HachiEquiv.Ring.N := rfl

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

/-! ## The loader

`ring::load_twisted_signed_into` is [`ring::load_twisted_into`] with the
branch of [`sgnWord`] on the read. The loop state is the same 3-tuple
`(a, w, t)` -- the borrowed operand rides along, as in `add_loop`. -/

/-- The word the loader forms before the twist IS [`sgnWord`] of the
coefficient: the Rust's `if v <= q/2 { v } else { GOLD_P - (q - v) }` and the
definition above are the same branch on the same test. -/
theorem sgnWord_lt {c : ℕ} (hc : c < q) : sgnWord c < GP := by
  unfold sgnWord
  by_cases h : c ≤ q / 2
  · rw [if_pos h]; exact lt_trans hc q_lt_GP
  · rw [if_neg h]
    have h1 : 0 < q - c := by omega
    have h2 : 0 < GP := by simp only [GP]; norm_num
    omega

/-- **The loader's branch.** The extracted `if v <= half then v else
GOLD_P - (q - v)` returns exactly [`sgnWord`] of the word. Factored out
because the two arms have different monadic shapes -- the second does two
checked subtractions -- and inlining them duplicates the whole tail of the
loop body. -/
theorem sgn_branch_spec (v qU halfU : Std.U64) (hq : qU.val = q)
    (hhalf : halfU.val = q / 2) (hv : v.val < q) :
    (if v ≤ halfU then ok v else do let i ← qU - v; ntt.GOLD_P - i)
      ⦃ g => g.val = sgnWord v.val ⦄ := by
  by_cases hvh : v ≤ halfU
  · rw [if_pos hvh, WP.spec_ok]
    have : v.val ≤ q / 2 := by scalar_tac
    unfold sgnWord; rw [if_pos this]
  · rw [if_neg hvh]
    have hgt : q / 2 < v.val := by scalar_tac
    step as ⟨i, hi⟩
    have hiGP : i.val ≤ (ntt.GOLD_P).val := by
      rw [hi, hq, GOLD_P_val]
      have := q_lt_GP
      omega
    step as ⟨g, hgv⟩
    unfold sgnWord
    rw [if_neg (by omega)]
    rw [hgv, hi, hq, GOLD_P_val]

theorem load_twisted_signed_into_loop_spec (a : ring.Rq)
    (pt : alloc.vec.Vec Std.U64) (nU : Std.Usize) (qU halfU : Std.U64)
    (w : alloc.vec.Vec Std.U64) (tU : Std.Usize) (ps : ZMod GP)
    (hn : nU.val = N) (hq : qU.val = q) (hhalf : halfU.val = q / 2)
    (hwf : HachiEquiv.Ring.Wf a)
    (hptC : Canon GP pt) (hptv : ∀ e, e < N → resK GP pt e = ps ^ e)
    (ht : tU.val ≤ N) (hwl : w.val.length = N)
    (hwc : ∀ e, e < tU.val → (wordAt w e) < GP)
    (hwv : ∀ e, e < tU.val → resK GP w e
      = NttMath.twistR ps (fun u => ((sgnWord (HachiEquiv.Ring.wordN a u) : ℕ) : ZMod GP)) e) :
    ring.load_twisted_signed_into_loop a pt nU qU halfU w tU
      ⦃ z => Canon GP z ∧ ∀ e, e < N → resK GP z e
               = NttMath.twistR ps
                   (fun u => ((sgnWord (HachiEquiv.Ring.wordN a u) : ℕ) : ZMod GP)) e ⦄ := by
  rw [ring.load_twisted_signed_into_loop]
  apply loop.spec_decr_nat (fun r => nU.val - r.2.2.val)
    (fun r => r.2.2.val ≤ N ∧ r.1 = a ∧ r.2.1.val.length = N
      ∧ (∀ e, e < r.2.2.val → (wordAt r.2.1 e) < GP)
      ∧ ∀ e, e < r.2.2.val → resK GP r.2.1 e
          = NttMath.twistR ps
              (fun u => ((sgnWord (HachiEquiv.Ring.wordN a u) : ℕ) : ZMod GP)) e)
  · rintro ⟨aa, d, tt⟩ ⟨htt, haa, hdl, hdc, hdv⟩
    dsimp only at htt haa hdl hdc hdv
    subst haa
    simp only [ring.load_twisted_signed_into_loop.body]
    by_cases hlt : tt < nU
    · rw [if_pos hlt]
      have httlt : tt.val < N := by rw [← hn]; scalar_tac
      have hab : tt.val < aa.val.length := by rw [hwf.1]; exact httlt
      have hpb : tt.val < pt.val.length := by rw [hptC.1]; exact httlt
      have hdb : tt.val < d.val.length := by rw [hdl]; exact httlt
      step as ⟨f, hf⟩
      step with HachiEquiv.Ring.to_u64_id f as ⟨v, hv⟩
      have hvv : v.val = HachiEquiv.Ring.wordN aa tt.val := by
        rw [hv, hf]
        unfold HachiEquiv.Ring.wordN
        rw [List.getD_eq_getElem _ _ hab]
      have hvq : v.val < q := by
        rw [hv, hf]; exact hwf.2 _ (List.getElem_mem hab)
      step with sgn_branch_spec v qU halfU hq hhalf hvq as ⟨g, hgv⟩
      have hglt : g.val < GP := by rw [hgv]; exact sgnWord_lt hvq
      step as ⟨y, hy⟩
      have hyv : y.val = wordAt pt tt.val := by
        rw [hy, ← wordAt_of_lt (v := pt) (t := tt.val) hpb]
      have hylt : y.val < GP := by rw [hyv]; exact wordAt_lt hptC GP_pos _
      step with gold_mul_spec g y as ⟨pr, hprv, hprlt⟩
      step as ⟨elem, back, helem, hback⟩
      step as ⟨tt1, htt1⟩
      rw [hback]
      refine ⟨by rw [htt1]; omega, ?_, ?_, ?_, by rw [htt1]; omega⟩
      · simpa using hdl
      · intro e he
        rw [htt1] at he
        by_cases heq : e = tt.val
        · rw [heq, wordAt_set_eq hdb]; exact hprlt
        · rw [wordAt_set_ne heq]; exact hdc e (by omega)
      · intro e he
        rw [htt1] at he
        by_cases heq : e = tt.val
        · rw [heq]
          simp only [resK]
          rw [wordAt_set_eq hdb, hprv, hgv, hvv, hyv]
          simp only [NttMath.twistR, resK] at hptv ⊢
          rw [ZMod.natCast_mod]
          push_cast
          rw [hptv tt.val httlt]
        · simp only [resK]
          rw [wordAt_set_ne heq]
          have := hdv e (by omega)
          simpa only [resK] using this
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : tt.val = N := by rw [← hn]; scalar_tac
      refine ⟨⟨hdl, ?_⟩, fun e he => hdv e (by rw [heq]; exact he)⟩
      intro u hu
      obtain ⟨e, he, hee⟩ := List.getElem_of_mem hu
      have := hdc e (by rw [heq]; omega)
      rw [wordAt_of_lt he] at this
      rw [← hee]; exact this
  · exact ⟨ht, rfl, hwl, hwc, hwv⟩

/-- [`load_twisted_signed_into`] at its entry point. -/
theorem load_twisted_signed_into_spec (w : alloc.vec.Vec Std.U64) (a : ring.Rq)
    (pt : alloc.vec.Vec Std.U64) (ps : ZMod GP)
    (hwf : Wf a) (hwl : w.val.length = N)
    (hptC : Canon GP pt) (hptv : ∀ e, e < N → resK GP pt e = ps ^ e) :
    ring.load_twisted_signed_into w a pt
      ⦃ z => Canon GP z ∧ ∀ e, e < N → resK GP z e
               = NttMath.twistR ps
                   (fun u => ((sgnWord (wordN a u) : ℕ) : ZMod GP)) e ⦄ := by
  rw [ring.load_twisted_signed_into]
  step as ⟨half, hhalf⟩
  exact load_twisted_signed_into_loop_spec a pt ntt.NTT_LEN params.Q half w 0#usize ps
    ntt_NTT_LEN_val HachiEquiv.Field.params_Q_val
    (by rw [hhalf, HachiEquiv.Field.params_Q_val]) hwf hptC hptv (by simp) hwl
    (by intro e he; simp at he) (by intro e he; simp at he)

/-- **The loader, in the form the bound layer wants.** The same statement with
[`sgnWord`] replaced by the integer it denotes -- [`sgnWord_cast`] applied
coefficientwise. Everything above this line is about words; everything below
is about the integers they stand for, and this is the seam. -/
theorem load_twisted_signed_into_sInt (w : alloc.vec.Vec Std.U64) (a : ring.Rq)
    (pt : alloc.vec.Vec Std.U64) (ps : ZMod GP)
    (hwf : Wf a) (hwl : w.val.length = N)
    (hptC : Canon GP pt) (hptv : ∀ e, e < N → resK GP pt e = ps ^ e) :
    ring.load_twisted_signed_into w a pt
      ⦃ z => Canon GP z ∧ ∀ e, e < N → resK GP z e
               = NttMath.twistR ps
                   (fun u => ((sInt (wordN a u) : ℤ) : ZMod GP)) e ⦄ := by
  apply spec_mono (load_twisted_signed_into_spec w a pt ps hwf hwl hptC hptv)
  rintro z ⟨hzC, hzv⟩
  refine ⟨hzC, fun e he => ?_⟩
  rw [hzv e he]
  congr 1
  funext u
  exact sgnWord_cast (wordN_lt hwf u)

end HachiEquiv.RingSigned
