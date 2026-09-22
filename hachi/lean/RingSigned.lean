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
open HachiEquiv.GoldDot
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
      have hylt : y.val < GP := by
        rw [hyv]; exact wordAt_lt hptC HachiEquiv.GoldTransform.GP_pos _
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

/-! ## The dot

The lane transforms the key entry and the witness entry, multiplies them
pointwise into the accumulator, and takes one inverse for the whole row.
`termFwdS` is [`RingFused.termFwd`] with the right operand read through
[`sInt`] instead of as an unsigned word; everything else about the transform
argument is the digit path's and is reused, `NttProduct.prod_difRun`
included. -/

/-- The `u`-th entry of a vector, coefficientwise as the *integers* its
coefficients denote. [`RingFused.entryK`]'s signed counterpart. -/
def sEntryK (b : alloc.vec.Vec ring.Rq) (u : ℕ) : ℕ → ZMod GP :=
  fun v => ((sInt (wordN (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) v) : ℤ) : ZMod GP)

/-- One ring element's coefficients as the integers they denote. -/
def sCoeff (b : ring.Rq) : ℕ → ZMod GP :=
  fun v => ((sInt (wordN b v) : ℤ) : ZMod GP)

theorem sEntryK_eq (b : alloc.vec.Vec ring.Rq) (u : ℕ) :
    sEntryK b u = sCoeff (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) := rfl

/-- One term's transform-domain contribution, from the two coefficient
functions directly. The `ρ`-digit segment needs this form: its right operand
is built per term by `rho_digit_as_rq` and there is no vector of digits to
index -- removing that vector was wall W3. -/
def termFwdF (ps : ZMod GP) (A B : ℕ → ZMod GP) : ℕ → ZMod GP :=
  NttMath.difRun (ps ^ 2) 10 1
    (NttMath.cyclicConv N (NttMath.twistR ps A) (NttMath.twistR ps B))

/-- One term's transform-domain contribution, right operand signed. -/
def termFwdS (ps : ZMod GP) (a b : alloc.vec.Vec ring.Rq) (u : ℕ) : ℕ → ZMod GP :=
  termFwdF ps (entryK GP a u) (sEntryK b u)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8000 in
/-- **The `z` segment's term loop.** Five-tuple state `(acc, b1, b2, b3, j)`:
the accumulator and the three recycled buffers. The buffers carry `Canon`
rather than a length, because `gold_forward` needs it of both arguments and
hands it back of both results, so the same predicate opens and closes the
body. -/
theorem lift_gold_loop0_spec (w : ringswitch.LiftedWitness) (row : linalg.PolyVec)
    (nU z_lenU : Std.Usize) (pt : alloc.vec.Vec Std.U64)
    (acc b1 b2 b3 : alloc.vec.Vec Std.U64) (jU : Std.Usize) (ps : ZMod GP)
    (hn : nU.val = N) (hord : ps ^ N = -1)
    (hptC : Canon GP pt) (hptv : ∀ e, e < N → resK GP pt e = ps ^ e)
    (hrown : z_lenU.val ≤ row.val.length)
    (hrowwf : ∀ u, u < z_lenU.val → Wf (row.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hzn : z_lenU.val ≤ w.z.val.length)
    (hzwf : ∀ u, u < z_lenU.val → Wf (w.z.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hj : jU.val ≤ z_lenU.val)
    (haccC : Canon GP acc) (hb1C : Canon GP b1) (hb2C : Canon GP b2) (hb3C : Canon GP b3)
    (hval : ∀ t, t < N → resK GP acc t
      = ∑ u ∈ Finset.range jU.val, termFwdS ps row w.z u t) :
    ringswitch.lift_commit_row_gold_loop0 w row nU z_lenU pt acc b1 b2 b3 jU
      ⦃ r => Canon GP r.1 ∧ Canon GP r.2.1 ∧ Canon GP r.2.2.1 ∧ Canon GP r.2.2.2
          ∧ ∀ t, t < N → resK GP r.1 t
              = ∑ u ∈ Finset.range z_lenU.val, termFwdS ps row w.z u t ⦄ := by
  rw [ringswitch.lift_commit_row_gold_loop0]
  apply loop.spec_decr_nat (fun r => z_lenU.val - r.2.2.2.2.val)
    (fun r => r.2.2.2.2.val ≤ z_lenU.val ∧ Canon GP r.1 ∧ Canon GP r.2.1
      ∧ Canon GP r.2.2.1 ∧ Canon GP r.2.2.2.1
      ∧ ∀ t, t < N → resK GP r.1 t
          = ∑ u ∈ Finset.range r.2.2.2.2.val, termFwdS ps row w.z u t)
  · rintro ⟨a1, c1, c2, c3, j1⟩ ⟨hj1, hA, hC1, hC2, hC3, hv1⟩
    dsimp only at hj1 hA hC1 hC2 hC3 hv1
    simp only [ringswitch.lift_commit_row_gold_loop0.body]
    by_cases hlt : j1 < z_lenU
    · rw [if_pos hlt]
      have hjlt : j1.val < z_lenU.val := by scalar_tac
      have hjrow : j1.val < row.val.length := by omega
      have hjz : j1.val < w.z.val.length := by omega
      simp only [linalg.PolyVec.get, ringswitch.LiftedWitness.impl.z, bind_tc_ok]
      step as ⟨r, hr⟩
      have hWr : Wf r := by
        rw [hr, ← List.getD_eq_getElem _ _ hjrow]; exact hrowwf _ hjlt
      step with load_twisted_into_spec c1 r pt ps hWr hC1.1 hptC hptv as ⟨kb, hkbC, hkbv⟩
      step with gold_forward_spec kb c2 pt hkbC hC2 hptC ps hptv
        as ⟨fk, hfk1, hfk2, hfkv⟩
      obtain ⟨kf, ksp⟩ := fk
      dsimp only at hfk1 hfk2 hfkv
      step as ⟨r1, hr1⟩
      have hWr1 : Wf r1 := by
        rw [hr1, ← List.getD_eq_getElem _ _ hjz]; exact hzwf _ hjlt
      step with load_twisted_signed_into_sInt c3 r1 pt ps hWr1 hC3.1 hptC hptv
        as ⟨wb, hwbC, hwbv⟩
      step with gold_forward_spec wb ksp pt hwbC hfk2 hptC ps hptv
        as ⟨wf, wsp, hfw1, hfw2, hfwv⟩
      -- the MAC, with the key's transform as the abstract left factor
      step with gold_mac_off_spec a1 kf wf 0#usize nU 0#usize (resK GP a1)
        (resK GP kf) hn (by simp) (by simp [hfk1.1]) hA hfw1 hfk1.2
        (by intro t _; simp [resK]) (by intro t _; simp)
        as ⟨a2, hA2, hA2v⟩
      step as ⟨j2, hj2⟩
      refine ⟨by scalar_tac, hA2, hfk1, hfw1, hfw2, ?_, by scalar_tac⟩
      intro t ht
      rw [hA2v t ht, hv1 t ht, hj2, Finset.sum_range_succ]
      congr 1
      -- the product of the two transforms IS the term's contribution
      have hprod := HachiEquiv.NttProduct.prod_difRun ps hord
        (entryK GP row j1.val) (sEntryK w.z j1.val)
        (resK GP kf) (resK GP wf)
        (fun t' => resK GP kf t' * resK GP wf t')
        (by
          intro t' ht'
          rw [hfkv t' ht']
          refine difRun_congr (ps ^ 2) 10 (by norm_num) 1 (resK GP kb)
            (NttMath.twistR ps (entryK GP row j1.val)) ?_ t' ht'
          intro e he
          rw [hkbv e he]
          congr 1
          funext u
          simp only [entryK, hr, List.getD_eq_getElem _ _ hjrow])
        (by
          intro t' ht'
          rw [hfwv t' ht']
          refine difRun_congr (ps ^ 2) 10 (by norm_num) 1 (resK GP wb)
            (NttMath.twistR ps (sEntryK w.z j1.val)) ?_ t' ht'
          intro e he
          rw [hwbv e he]
          congr 1
          funext u
          simp only [sEntryK, hr1, List.getD_eq_getElem _ _ hjz])
        (fun t' _ => rfl) t ht
      rw [hprod]
      simp only [termFwdS, termFwdF, sEntryK]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : j1.val = z_lenU.val := by scalar_tac
      exact ⟨hA, hC1, hC2, hC3, by intro t ht; rw [hv1 t ht, heq]⟩
  · exact ⟨hj, haccC, hb1C, hb2C, hb3C, hval⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8000 in
/-- **The `ρ`-digit segment's term loop.** The same body as
[`lift_gold_loop0_spec`] with the right operand built per term by
`rho_digit_as_rq` and the key index shifted by `z_len`.

The digit is abstracted as `DF` with `hD` supplying its spec, because there
is no vector of digits to index -- building one was wall W3 and removing it
was candidate E. That also keeps this file free of the ArkLib digit
machinery: the caller in `RingSwitch` discharges `hD` from
`rho_digit_as_rq_raw_spec`.

`init` is arbitrary, so this is a statement about accumulating in place on
top of whatever the `z` segment left. -/
theorem lift_gold_loop1_spec (w : ringswitch.LiftedWitness) (row : linalg.PolyVec)
    (nU z_lenU rho_lenU : Std.Usize) (pt : alloc.vec.Vec Std.U64)
    (acc b1 b2 b3 : alloc.vec.Vec Std.U64) (kU : Std.Usize) (ps : ZMod GP)
    (DF : ℕ → ℕ → ZMod GP) (init : ℕ → ZMod GP)
    (hn : nU.val = N) (hord : ps ^ N = -1)
    (hptC : Canon GP pt) (hptv : ∀ e, e < N → resK GP pt e = ps ^ e)
    (hmax : z_lenU.val + rho_lenU.val ≤ Std.Usize.max)
    (hrown : z_lenU.val + rho_lenU.val ≤ row.val.length)
    (hrowwf : ∀ u, u < z_lenU.val + rho_lenU.val →
      Wf (row.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hD : ∀ kk : Std.Usize, kk.val < rho_lenU.val →
      ringswitch.rho_digit_as_rq w.rho kk ⦃ d => Wf d ∧ sCoeff d = DF kk.val ⦄)
    (hk : kU.val ≤ rho_lenU.val)
    (haccC : Canon GP acc) (hb1C : Canon GP b1) (hb2C : Canon GP b2) (hb3C : Canon GP b3)
    (hval : ∀ t, t < N → resK GP acc t
      = init t + ∑ k ∈ Finset.range kU.val,
          termFwdF ps (entryK GP row (z_lenU.val + k)) (DF k) t) :
    ringswitch.lift_commit_row_gold_loop1 w row nU z_lenU rho_lenU pt acc b1 b2 b3 kU
      ⦃ r => Canon GP r.1 ∧ Canon GP r.2 ∧ ∀ t, t < N → resK GP r.1 t
          = init t + ∑ k ∈ Finset.range rho_lenU.val,
              termFwdF ps (entryK GP row (z_lenU.val + k)) (DF k) t ⦄ := by
  rw [ringswitch.lift_commit_row_gold_loop1]
  apply loop.spec_decr_nat (fun r => rho_lenU.val - r.2.2.2.2.val)
    (fun r => r.2.2.2.2.val ≤ rho_lenU.val ∧ Canon GP r.1 ∧ Canon GP r.2.1
      ∧ Canon GP r.2.2.1 ∧ Canon GP r.2.2.2.1
      ∧ ∀ t, t < N → resK GP r.1 t
          = init t + ∑ k ∈ Finset.range r.2.2.2.2.val,
              termFwdF ps (entryK GP row (z_lenU.val + k)) (DF k) t)
  · rintro ⟨a1, c1, c2, c3, k1⟩ ⟨hk1, hA, hC1, hC2, hC3, hv1⟩
    dsimp only at hk1 hA hC1 hC2 hC3 hv1
    simp only [ringswitch.lift_commit_row_gold_loop1.body]
    by_cases hlt : k1 < rho_lenU
    · rw [if_pos hlt]
      have hklt : k1.val < rho_lenU.val := by scalar_tac
      simp only [ringswitch.LiftedWitness.impl.rho, bind_tc_ok]
      step with hD k1 hklt as ⟨digit, hWd, hdv⟩
      step as ⟨idx, hidx⟩
      have hidxv : idx.val = z_lenU.val + k1.val := by scalar_tac
      have hjrow : idx.val < row.val.length := by omega
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by
        rw [hr, ← List.getD_eq_getElem _ _ hjrow]; exact hrowwf _ (by omega)
      step with load_twisted_into_spec c1 r pt ps hWr hC1.1 hptC hptv as ⟨kb, hkbC, hkbv⟩
      step with gold_forward_spec kb c2 pt hkbC hC2 hptC ps hptv
        as ⟨fk, hfk1, hfk2, hfkv⟩
      obtain ⟨kf, ksp⟩ := fk
      dsimp only at hfk1 hfk2 hfkv
      step with load_twisted_signed_into_sInt c3 digit pt ps hWd hC3.1 hptC hptv
        as ⟨wb, hwbC, hwbv⟩
      step with gold_forward_spec wb ksp pt hwbC hfk2 hptC ps hptv
        as ⟨wf, wsp, hfw1, hfw2, hfwv⟩
      step with gold_mac_off_spec a1 kf wf 0#usize nU 0#usize (resK GP a1)
        (resK GP kf) hn (by simp) (by simp [hfk1.1]) hA hfw1 hfk1.2
        (by intro t _; simp [resK]) (by intro t _; simp)
        as ⟨a2, hA2, hA2v⟩
      step as ⟨k2, hk2⟩
      refine ⟨by scalar_tac, hA2, hfk1, hfw1, hfw2, ?_, by scalar_tac⟩
      intro t ht
      rw [hA2v t ht, hv1 t ht, hk2, Finset.sum_range_succ, add_assoc]
      congr 1
      have hprod := HachiEquiv.NttProduct.prod_difRun ps hord
        (entryK GP row idx.val) (sCoeff digit)
        (resK GP kf) (resK GP wf)
        (fun t' => resK GP kf t' * resK GP wf t')
        (by
          intro t' ht'
          rw [hfkv t' ht']
          refine difRun_congr (ps ^ 2) 10 (by norm_num) 1 (resK GP kb)
            (NttMath.twistR ps (entryK GP row idx.val)) ?_ t' ht'
          intro e he
          rw [hkbv e he]
          congr 1
          funext u
          simp only [entryK, hr, List.getD_eq_getElem _ _ hjrow])
        (by
          intro t' ht'
          rw [hfwv t' ht']
          refine difRun_congr (ps ^ 2) 10 (by norm_num) 1 (resK GP wb)
            (NttMath.twistR ps (sCoeff digit)) ?_ t' ht'
          intro e he
          rw [hwbv e he]
          rfl)
        (fun t' _ => rfl) t ht
      rw [hprod, ← hidxv, ← hdv]
      simp only [termFwdF]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = rho_lenU.val := by scalar_tac
      exact ⟨hA, hC2, by intro t ht; rw [hv1 t ht, heq]⟩
  · exact ⟨hk, haccC, hb1C, hb2C, hb3C, hval⟩

/-- **The output loop**, `words[t] % q` pushed as an `Fp`.

`GoldDot.gold_out_loop_spec` for the other extracted copy of the same body:
the two loops are byte-identical in the Rust and distinct functions in the
model, so the lemma is repeated rather than reused. -/
theorem lift_gold_out_loop_spec (degU : Std.Usize) (qwU : Std.U64)
    (words : alloc.vec.Vec Std.U64) (out : alloc.vec.Vec cpoly.field.Fp)
    (tU : Std.Usize) (X : ℕ → ℕ)
    (hdeg : degU.val = N) (hqwv : qwU.val = q)
    (hv : ∀ k, k < N → wordAt words k = X k)
    (hl : words.val.length = N)
    (ht : tU.val ≤ N) (hlen : out.val.length = tU.val)
    (hred : ∀ u ∈ out.val, HachiEquiv.Field.Red u)
    (hval : ∀ k, k < tU.val → wordN out k = X k % q) :
    ringswitch.lift_commit_row_gold_loop2 degU qwU words out tU
      ⦃ z => Wf z ∧ ∀ k, k < N → wordN z k = X k % q ⦄ := by
  rw [ringswitch.lift_commit_row_gold_loop2]
  apply loop.spec_decr_nat (fun r => N - r.2.val)
    (fun r => r.2.val ≤ N ∧ r.1.val.length = r.2.val
      ∧ (∀ u ∈ r.1.val, HachiEquiv.Field.Red u)
      ∧ ∀ k, k < r.2.val → wordN r.1 k = X k % q)
  · rintro ⟨o1, tt⟩ ⟨htt, hlen1, hred1, hval1⟩
    dsimp only at htt hlen1 hred1 hval1
    simp only [ringswitch.lift_commit_row_gold_loop2.body]
    by_cases hlt : tt < degU
    · rw [if_pos hlt]
      have httlt : tt.val < N := by rw [← hdeg]; scalar_tac
      have hb1 : tt.val < words.val.length := by rw [hl]; exact httlt
      step as ⟨g, hg⟩
      have hgv : g.val = X tt.val := by
        rw [hg, ← wordAt_of_lt (v := words) (t := tt.val) hb1]; exact hv tt.val httlt
      step as ⟨md, hmd⟩
      have hmdv : md.val = X tt.val % q := by rw [hmd, hgv, hqwv]
      have hmdlt : md.val < q := by
        rw [hmdv]; exact Nat.mod_lt _ (by norm_num [HachiEquiv.NttProduct.q])
      step with HachiEquiv.Field.fp_new_spec md as ⟨f, hfred, hfval⟩
      step as ⟨o2, ho2⟩
      step as ⟨tt1, htt1⟩
      refine ⟨by rw [htt1]; omega, ?_, ?_, ?_, by rw [htt1]; omega⟩
      · rw [ho2, htt1, List.length_append, hlen1]; simp
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with hm | hm
        · exact hred1 u hm
        · rw [List.mem_singleton.mp hm]; exact hfred
      · intro k hk
        rw [htt1] at hk
        simp only [wordN] at hval1 ⊢
        rcases Nat.lt_or_ge k tt.val with hklt | hkge
        · rw [ho2, getD_append_lt' _ _ _ (by omega)]
          exact hval1 k hklt
        · have hkeq : k = o1.val.length := by omega
          rw [hkeq, ho2, getD_append_eq', hlen1]
          have hfv : f.val = md.val := by
            have h1 := HachiEquiv.NttProduct.natCast_inj_of_lt
              (n := q) (x := f.val) (y := md.val) hfred hfval
            rwa [Nat.mod_eq_of_lt hmdlt] at h1
          rw [hfv, hmdv]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : tt.val = N := by rw [← hdeg]; scalar_tac
      exact ⟨⟨by rw [hlen1, heq], hred1⟩,
        fun k hk => hval1 k (by rw [heq]; exact hk)⟩
  · exact ⟨ht, hlen, hred, hval⟩

/-! ## The row as one sum

The row's two segments are `z` and the `ρ` digits, and the digits are not a
vector -- that is wall W3, removed by candidate E. So the row is indexed by a
*function* into `ring.Rq`, and the sum runs over `range (z_len + rho_len)`
with the segment boundary inside the operand function rather than in the
index set. `sConvSum` above is this with both sides vectors; the two agree
where both apply and the function form is what the top-level spec uses. -/

/-- The row's signed value at coefficient `k`, over operands given as
functions. -/
def sConvSumF (KA WB : ℕ → ring.Rq) (n k : ℕ) : ℤ :=
  ∑ u ∈ Finset.range n, sConv (KA u) (WB u) k

theorem sConvSumF_abs_le {G : ℕ} (KA WB : ℕ → ring.Rq) (n k : ℕ)
    (ha : ∀ u, u < n → Wf (KA u)) (hb : ∀ u, u < n → CenteredWf G (WB u)) :
    |sConvSumF KA WB n k| ≤ (n : ℤ) * ((SBOUND G : ℕ) : ℤ) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ u ∈ Finset.range n, |sConv (KA u) (WB u) k|
      ≤ ∑ _u ∈ Finset.range n, ((SBOUND G : ℕ) : ℤ) := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        have hun : u < n := Finset.mem_range.mp hu
        have := sConv_abs_le (ha u hun) (hb u hun) k
        simpa only [SBOUND, Nat.cast_mul] using this
    _ = (n : ℤ) * ((SBOUND G : ℕ) : ℤ) := by
        rw [Finset.sum_const, Finset.card_range]; simp

/-! ## From the transform domain back to the integers

`RingFused.ordConv_entryK_pos` and `_neg` cast the ordinary convolution's two
halves to `posSum` and `negSum`, both naturals. With a signed right operand
the two halves do not split that way -- the wrap carries a minus sign into
the *value*, not just into the indexing -- so the pair collapses into one
lemma over `ℤ`. -/

theorem ordConvS_pos (x y : ring.Rq) (k : ℕ) (hk : k < N) :
    NttMath.ordConv N (fun v => ((wordN x v : ℕ) : ZMod GP)) (sCoeff y) k
      = (((∑ t ∈ Finset.range N,
            if t ≤ k then (wordN x t : ℤ) * sInt (wordN y (k - t)) else 0) : ℤ)
          : ZMod GP) := by
  unfold NttMath.ordConv sCoeff
  push_cast
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp only [Finset.mem_range] at hi
  by_cases hle : i ≤ k
  · rw [if_pos (And.intro hle (by omega : k - i < N)), if_pos hle]
  · rw [if_neg (by omega : ¬(i ≤ k ∧ k - i < N)), if_neg hle]

theorem ordConvS_neg (x y : ring.Rq) (k : ℕ) (hk : k < N) :
    NttMath.ordConv N (fun v => ((wordN x v : ℕ) : ZMod GP)) (sCoeff y) (N + k)
      = (((∑ t ∈ Finset.range N,
            if t ≤ k then 0 else (wordN x t : ℤ) * sInt (wordN y (N + k - t))) : ℤ)
          : ZMod GP) := by
  unfold NttMath.ordConv sCoeff
  push_cast
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp only [Finset.mem_range] at hi
  by_cases hle : i ≤ k
  · rw [if_neg (by omega : ¬(i ≤ N + k ∧ N + k - i < N)), if_pos hle]
  · rw [if_pos (And.intro (by omega) (by omega : N + k - i < N)), if_neg hle]

/-- **The seam, closed.** One output coefficient of the negacyclic
convolution in `ZMod GP` is the image of the signed integer [`sConv`]. -/
theorem negConvR_sConv (x y : ring.Rq) (k : ℕ) (hk : k < N) :
    NttMath.negConvR N (fun v => ((wordN x v : ℕ) : ZMod GP)) (sCoeff y) k
      = ((sConv x y k : ℤ) : ZMod GP) := by
  unfold NttMath.negConvR sConv
  rw [ordConvS_pos x y k hk, ordConvS_neg x y k hk]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hle : i ≤ k <;> simp [hle]

/-! ## Mod `q`, the sign is invisible

The whole signed apparatus exists to keep the *lane's* value inside
`GOLD_P`. Once the value is reduced mod `q` the encoding disappears, because
`sInt c` is `c` or `c − q` and `q ≡ 0`. That is why the headline statement
of the card is the digit path's, unchanged: `negConv` is a `ZMod q` notion
and cannot see the difference. -/

theorem sInt_cast_q (c : ℕ) : ((sInt c : ℤ) : ZMod q) = ((c : ℕ) : ZMod q) := by
  unfold sInt
  by_cases h : c ≤ q / 2
  · rw [if_pos h]; push_cast; ring
  · rw [if_neg h]
    push_cast
    ring

/-- **The card's conclusion, coefficientwise.** The signed convolution, read
mod `q`, is the ordinary `negConv` -- so nothing above this line has to know
the operand was centred. -/
theorem sConv_cast_q {x y : ring.Rq} (hx : Wf x) (hy : Wf y) {k : ℕ} (hk : k < N) :
    ((sConv x y k : ℤ) : ZMod q) = HachiEquiv.Ring.negConv x y k := by
  rw [HachiEquiv.Ring.negConv, ← HachiEquiv.Ring.posSum_cast hx hy hk,
    ← HachiEquiv.Ring.negSum_cast hx hy hk]
  unfold sConv HachiEquiv.Ring.posSum HachiEquiv.Ring.negSum
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hle : i ≤ k <;>
    simp [hle, sInt_cast_q, HachiEquiv.Ring.coeffK_eq_cast_wordN]

/-! ## The read-back

The lane's accumulator holds a *signed* integer; the words it is read out of
are naturals. [`offS`] is the bridge: add the row's ceiling, which layer 2
proved the value cannot exceed, so the sum is non-negative and below `GOLD_P`
-- and which is a multiple of `q`, so it vanishes in the final reduction.
The digit path does the same with `offConvSumD`, in `ℕ` throughout because
its operand is unsigned. -/

/-- The offset form of a signed row value. -/
def offS (terms G : ℕ) (S : ℤ) : ℕ := (S + (terms : ℤ) * (SBOUND G : ℕ)).toNat

theorem offS_cast (terms G : ℕ) (S : ℤ) (hS : |S| ≤ (terms : ℤ) * (SBOUND G : ℕ)) :
    ((offS terms G S : ℕ) : ℤ) = S + (terms : ℤ) * (SBOUND G : ℕ) := by
  unfold offS
  refine Int.toNat_of_nonneg ?_
  have := abs_le.mp hS
  omega

/-- **The offset fits.** Twice the ceiling below `GOLD_P` is exactly the
card's one-chunk condition, and [`sbound_fit_lift`] is its instance at the
pin. -/
theorem offS_lt (terms G : ℕ) (S : ℤ) (hS : |S| ≤ (terms : ℤ) * (SBOUND G : ℕ))
    (hfit : 2 * terms * SBOUND G < GP) : offS terms G S < GP := by
  -- `omega` is linear and `terms * SBOUND G` is a product of two variables,
  -- so the chain only closes once that product is a single atom. Same shape
  -- as `RingFused.offConvSumB_lt`.
  have hc := offS_cast terms G S hS
  have habs := abs_le.mp hS
  have hfitZ : 2 * ((terms : ℤ) * (SBOUND G : ℕ)) < (GP : ℤ) := by
    have : (2 : ℤ) * (terms : ℤ) * (SBOUND G : ℕ) < (GP : ℤ) := by exact_mod_cast hfit
    linarith
  set M : ℤ := (terms : ℤ) * (SBOUND G : ℕ) with hM
  omega

/-- **And it vanishes mod `q`.** `SBOUND G = N · q · G` is a multiple of `q`,
so reducing the offset word recovers the signed value itself. -/
theorem offS_mod_q (terms G : ℕ) (S : ℤ) (hS : |S| ≤ (terms : ℤ) * (SBOUND G : ℕ)) :
    ((offS terms G S % q : ℕ) : ZMod q) = ((S : ℤ) : ZMod q) := by
  rw [ZMod.natCast_mod]
  have hc : ((offS terms G S : ℕ) : ℤ) = S + (terms : ℤ) * (SBOUND G : ℕ) :=
    offS_cast terms G S hS
  have hz : ((offS terms G S : ℕ) : ZMod q) = (((offS terms G S : ℕ) : ℤ) : ZMod q) := by
    push_cast; ring
  rw [hz, hc]
  push_cast
  have hq0 : ((q : ℕ) : ZMod q) = 0 := ZMod.natCast_self q
  have : ((SBOUND G : ℕ) : ZMod q) = 0 := by
    simp only [SBOUND, Nat.cast_mul]
    rw [hq0]
    ring
  rw [this]
  ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
/-- **`lift_commit_row_gold` computes the row**, on one signed lane.

`RingSwitch.lift_commit_row_spec`'s value in this file's vocabulary: the two
segments' negacyclic convolution sums, coefficientwise in `ZMod q`. The
signed encoding does not appear in the conclusion, and `sConv_cast_q` is why
-- it is machinery for keeping the lane's value inside `GOLD_P`, not a change
to what is computed.

`D` is the digit function and `hD` its spec, for the same reason
[`lift_gold_loop1_spec`] takes them: there is no vector of digits. -/
theorem lift_commit_row_gold_spec (d_key : linalg.PolyMatrix)
    (w : ringswitch.LiftedWitness) (iU : Std.Usize) (z_len rho_len : ℕ)
    (D : ℕ → ring.Rq)
    (hi : iU.val < d_key.val.length)
    (hzlen : w.z.val.length = z_len)
    (hrholen : w.rho.val.length * 8 = rho_len)
    (hmax : z_len + rho_len ≤ Std.Usize.max)
    (hrowlen : z_len + rho_len
      ≤ (d_key.val.getD iU.val (alloc.vec.Vec.new ring.Rq)).val.length)
    (hrowwf : ∀ u, u < z_len + rho_len → Wf
      ((d_key.val.getD iU.val (alloc.vec.Vec.new ring.Rq)).val.getD u
        (alloc.vec.Vec.new cpoly.field.Fp)))
    (hzwf : ∀ u, u < z_len → Wf (w.z.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hzc : ∀ u, u < z_len → CenteredWf 15
      (w.z.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hDwf : ∀ j, j < rho_len → Wf (D j))
    (hDc : ∀ j, j < rho_len → CenteredWf 15 (D j))
    (hD : ∀ kk : Std.Usize, kk.val < rho_len →
      ringswitch.rho_digit_as_rq w.rho kk ⦃ d => d = D kk.val ⦄)
    (hfit : 2 * (z_len + rho_len) * SBOUND 15 < GP) :
    ringswitch.lift_commit_row_gold d_key w iU
      ⦃ z => Wf z ∧ ∀ k, k < N → HachiEquiv.Ring.coeffK z k
          = (∑ u ∈ Finset.range z_len, HachiEquiv.Ring.negConv
              ((d_key.val.getD iU.val (alloc.vec.Vec.new ring.Rq)).val.getD u
                (alloc.vec.Vec.new cpoly.field.Fp))
              (w.z.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k)
          + (∑ j ∈ Finset.range rho_len, HachiEquiv.Ring.negConv
              ((d_key.val.getD iU.val (alloc.vec.Vec.new ring.Rq)).val.getD (z_len + j)
                (alloc.vec.Vec.new cpoly.field.Fp)) (D j) k) ⦄ := by
  set ps : ZMod GP := ((ntt.GOLD_PSI.val : ℕ) : ZMod GP) with hpsdef
  set psii : ZMod GP := ((ntt.GOLD_PSIINV.val : ℕ) : ZMod GP) with hpsiidef
  have hord : ps ^ N = -1 := gpsi_ord
  have hpinv : ps * psii = 1 := gpsi_inv
  set KR : linalg.PolyVec := d_key.val.getD iU.val (alloc.vec.Vec.new ring.Rq) with hKR
  -- the witness, as one function over the two segments
  set WB : ℕ → ring.Rq := fun u =>
    if u < z_len then w.z.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)
    else D (u - z_len) with hWB
  set KA : ℕ → ring.Rq := fun u => KR.val.getD u (alloc.vec.Vec.new cpoly.field.Fp) with hKA
  have hKAwf : ∀ u, u < z_len + rho_len → Wf (KA u) := hrowwf
  have hWBwf : ∀ u, u < z_len + rho_len → Wf (WB u) := by
    intro u hu
    simp only [hWB]
    by_cases hlt : u < z_len
    · rw [if_pos hlt]; exact hzwf u hlt
    · rw [if_neg hlt]; exact hDwf (u - z_len) (by omega)
  have hWBc : ∀ u, u < z_len + rho_len → CenteredWf 15 (WB u) := by
    intro u hu
    simp only [hWB]
    by_cases hlt : u < z_len
    · rw [if_pos hlt]; exact hzc u hlt
    · rw [if_neg hlt]; exact hDc (u - z_len) (by omega)
  have hRN : params.RING_DEGREE = ntt.NTT_LEN := by decide +kernel
  rw [ringswitch.lift_commit_row_gold, hRN]
  simp only [linalg.PolyMatrix.row]
  step as ⟨row, hrowEq⟩
  have hrow : row = KR := by rw [hKR, List.getD_eq_getElem _ _ hi, hrowEq]
  simp only [ringswitch.LiftedWitness.impl.z, ringswitch.LiftedWitness.impl.rho,
    linalg.PolyVec.len, bind_tc_ok]
  have hgd : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  have hrhomax : w.rho.val.length * 8 ≤ Std.Usize.max := by omega
  step as ⟨rl, hrl⟩
  have hzlv : (alloc.vec.Vec.len w.z).val = z_len := by simpa using hzlen
  have hrlv : rl.val = rho_len := by rw [hrl, hgd, ← hrholen]; simp
  step with gold_psi_table_cast ntt.GOLD_PSI (by decide +kernel) as ⟨pt, hptC, hptv⟩
  step with gold_psi_table_cast ntt.GOLD_PSIINV (by decide +kernel) as ⟨it, hitC, hitv⟩
  step with zeros_canon_zero GP HachiEquiv.GoldTransform.GP_pos as ⟨acc0, hacc0C, hacc0v⟩
  step with lift_gold_loop0_spec w row ntt.NTT_LEN (alloc.vec.Vec.len w.z) pt
      acc0 acc0 acc0 acc0 0#usize ps ntt_NTT_LEN_val hord hptC hptv
      (by rw [hrow, hzlv]; omega)
      (by intro u hu; rw [hrow]; exact hrowwf u (by rw [hzlv] at hu; omega))
      (by rw [hzlv, hzlen])
      (by intro u hu; exact hzwf u (by rw [hzlv] at hu; exact hu))
      (by simp) hacc0C hacc0C hacc0C hacc0C
      (by intro t ht; rw [hacc0v t ht]; simp)
    as ⟨acc1, bb1, bb2, bb3, hA1, hB1, hB2, hB3, hA1v⟩
  step with lift_gold_loop1_spec w row ntt.NTT_LEN (alloc.vec.Vec.len w.z) rl pt
      acc1 bb1 bb2 bb3 0#usize ps (fun k => sCoeff (D k))
      (fun t => ∑ u ∈ Finset.range z_len, termFwdS ps row w.z u t)
      ntt_NTT_LEN_val hord hptC hptv
      (by rw [hzlv, hrlv]; exact hmax)
      (by rw [hrow, hzlv, hrlv]; exact hrowlen)
      (by intro u hu; rw [hrow]; exact hrowwf u (by rw [hzlv, hrlv] at hu; exact hu))
      (by
        intro kk hkk
        apply spec_mono (hD kk (by rw [hrlv] at hkk; exact hkk))
        intro d hd
        exact ⟨hd ▸ hDwf kk.val (by rw [hrlv] at hkk; exact hkk), by rw [hd]⟩)
      (by simp) hA1 hB1 hB2 hB3
      (by intro t ht; rw [hA1v t ht, hzlv]; simp only [hpsdef]; simp)
    as ⟨acc2, bb21, hA2, hB21, hA2v⟩
  simp only [← hpsdef, hzlv, hrlv] at hA2v
  -- the two segments, as one sum over `range (z_len + rho_len)`
  have hsplit : ∀ t, t < N → resK GP acc2 t
      = ∑ u ∈ Finset.range (z_len + rho_len),
          termFwdF ps (entryK GP row u) (sCoeff (WB u)) t := by
    intro t ht
    have h1 : ∑ u ∈ Finset.range z_len, termFwdS ps row w.z u t
        = ∑ u ∈ Finset.range z_len, termFwdF ps (entryK GP row u) (sCoeff (WB u)) t :=
      Finset.sum_congr rfl (fun u hu => by
        have hul : u < z_len := Finset.mem_range.mp hu
        simp only [termFwdS, sEntryK_eq, hWB, if_pos hul])
    have h2 : ∑ j ∈ Finset.range rho_len,
          termFwdF ps (entryK GP row (z_len + j)) (sCoeff (D j)) t
        = ∑ j ∈ Finset.range rho_len,
          termFwdF ps (entryK GP row (z_len + j)) (sCoeff (WB (z_len + j))) t :=
      Finset.sum_congr rfl (fun j _ => by
        simp only [hWB, if_neg (by omega : ¬ z_len + j < z_len), Nat.add_sub_cancel_left])
    rw [hA2v t ht, Finset.sum_range_add, h1, h2]
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = z_len + rho_len := by rw [hi2, hzlv, hrlv]
  have hcn : lift (UScalar.cast .U64 i2) ⦃ y => y.val = i2.val ⦄ :=
    UScalar.cast_inBounds_spec .U64 i2 (by
      -- the card's own fit already bounds the term count far below `2^64`
      have h := hfit
      simp only [SBOUND, N, HachiEquiv.NttProduct.q, GP] at h
      rw [hi2v]
      simp only [Std.UScalar.max, Std.UScalarTy.numBits]
      omega)
  step with hcn as ⟨terms, hterms⟩
  step with gold_mul_spec ntt.GOLD_SOFF terms as ⟨scaled, hscv, hsclt⟩
  have hKArow : ∀ u, entryK GP row u = fun v => ((wordN (KA u) v : ℕ) : ZMod GP) := by
    intro u; rw [hrow]; rfl
  -- the transform argument, unchanged from the digit path
  have hPR : ∀ t, t < N → resK GP acc2 t
      = NttMath.difRun (ps ^ 2) 10 1
          (fun t' => ∑ u ∈ Finset.range (z_len + rho_len),
            NttMath.cyclicConv N (NttMath.twistR ps (entryK GP row u))
              (NttMath.twistR ps (sCoeff (WB u))) t') t := by
    intro t ht
    rw [hsplit t ht, NttMath.difRun_sum (ps ^ 2) 10 1 (Finset.range (z_len + rho_len))
      (fun u => NttMath.cyclicConv N (NttMath.twistR ps (entryK GP row u))
        (NttMath.twistR ps (sCoeff (WB u))))]
    simp only [termFwdF]
  step with gold_inverse_spec acc2 bb21 it hA2 hB21 hitC psii hitv
    as ⟨v1, v2, hiv1, hiv2, hivv⟩
  have hIV := HachiEquiv.NttProduct.inv_value ps psii hpinv
    (fun t' => ∑ u ∈ Finset.range (z_len + rho_len),
      NttMath.cyclicConv N (NttMath.twistR ps (entryK GP row u))
        (NttMath.twistR ps (sCoeff (WB u))) t')
    (resK GP acc2) (resK GP v1) hPR hivv
  step with gold_untwist_cast v1 it scaled hiv1 hitC hsclt psii hitv
    as ⟨words, hwC, hwv⟩
  -- the offset is the row's ceiling, and it did not wrap
  have hsoff : scaled.val = (z_len + rho_len) * SBOUND 15 := by
    rw [hscv, hterms, hi2v, gold_soff_val]
    have hlt : SBOUND 15 * (z_len + rho_len) < GP := by
      -- `omega` is linear, so the product needs to be one atom (as in `offS_lt`)
      have h : 2 * ((z_len + rho_len) * SBOUND 15) < GP := by
        rw [← Nat.mul_assoc]; exact hfit
      rw [Nat.mul_comm]
      omega
    rw [Nat.mod_eq_of_lt hlt, Nat.mul_comm]
  have hbnd : ∀ t, |sConvSumF KA WB (z_len + rho_len) t|
      ≤ ((z_len + rho_len : ℕ) : ℤ) * ((SBOUND 15 : ℕ) : ℤ) :=
    fun t => sConvSumF_abs_le KA WB (z_len + rho_len) t hKAwf hWBc
  have hres : ∀ t, t < N → resK GP words t
      = (((offS (z_len + rho_len) 15 (sConvSumF KA WB (z_len + rho_len) t) : ℕ)) : ZMod GP) := by
    intro t ht
    rw [hwv t ht, hIV t ht,
      untwist_value_sum ps psii ((ntt.GOLD_NINV.val : ℕ) : ZMod GP) hord hpinv
        gninv_inv (Finset.range (z_len + rho_len)) (fun u => entryK GP row u)
        (fun u => sCoeff (WB u)) t ht]
    have hsum : ∑ u ∈ Finset.range (z_len + rho_len),
          NttMath.negConvR N (entryK GP row u) (sCoeff (WB u)) t
        = ((sConvSumF KA WB (z_len + rho_len) t : ℤ) : ZMod GP) := by
      unfold sConvSumF
      push_cast
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [hKArow u]
      exact negConvR_sConv (KA u) (WB u) t ht
    rw [hsum, hsoff]
    have hc := offS_cast (z_len + rho_len) 15 (sConvSumF KA WB (z_len + rho_len) t) (hbnd t)
    have : (((offS (z_len + rho_len) 15 (sConvSumF KA WB (z_len + rho_len) t) : ℕ)) : ZMod GP)
        = ((((offS (z_len + rho_len) 15 (sConvSumF KA WB (z_len + rho_len) t) : ℕ) : ℤ)) : ZMod GP) := by
      push_cast; ring
    rw [this, hc]
    push_cast
    ring
  have hwordv : ∀ k, k < N →
      wordAt words k = offS (z_len + rho_len) 15 (sConvSumF KA WB (z_len + rho_len) k) := by
    intro k hk
    have hlt : offS (z_len + rho_len) 15 (sConvSumF KA WB (z_len + rho_len) k) < GP := by
      exact offS_lt _ _ _ (hbnd k) hfit
    have h2 := HachiEquiv.NttProduct.natCast_inj_of_lt
      (wordAt_lt hwC HachiEquiv.GoldTransform.GP_pos k)
      (by simpa only [resK] using hres k hk)
    rwa [Nat.mod_eq_of_lt hlt] at h2
  have hfin := lift_gold_out_loop_spec ntt.NTT_LEN params.Q words
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize
    (fun k => offS (z_len + rho_len) 15 (sConvSumF KA WB (z_len + rho_len) k))
    ntt_NTT_LEN_val HachiEquiv.Field.params_Q_val hwordv hwC.1
    (by simp) (by simp) (by simp) (by simp)
  rw [alloc.vec.Vec.with_capacity]
  step with hfin as ⟨o1, ho1w, ho1v⟩
  step with HachiEquiv.Ring.from_coeffs_spec o1 ho1w.2 as ⟨z, hzw, hzv⟩
  refine ⟨hzw, fun k hk => ?_⟩
  rw [hzv k hk, HachiEquiv.Ring.coeffK_eq_cast_wordN, ho1v k hk]
  rw [offS_mod_q _ _ _ (hbnd k)]
  unfold sConvSumF
  push_cast
  rw [Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl (fun u hu => ?_)
    have hul : u < z_len := Finset.mem_range.mp hu
    rw [sConv_cast_q (hKAwf u (by omega)) (hWBwf u (by omega)) hk]
    simp only [hKA, hWB, hrow, if_pos hul]
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjl : j < rho_len := Finset.mem_range.mp hj
    rw [sConv_cast_q (hKAwf (z_len + j) (by omega)) (hWBwf (z_len + j) (by omega)) hk]
    simp only [hKA, hWB, hrow, if_neg (by omega : ¬ z_len + j < z_len),
      Nat.add_sub_cancel_left]

/-- `CenteredWf` quantifies over every index; past `N` the word is the
default `0`, so checking below `N` is enough. -/
theorem centeredWf_of_lt {G : ℕ} {b : ring.Rq} (hb : Wf b)
    (h : ∀ k, k < N → sAbs (wordN b k) ≤ G) : CenteredWf G b := by
  intro t
  by_cases ht : t < N
  · exact h t ht
  · have hlen : b.val.length ≤ t := by
      have hN := N_eq
      rw [hb.1]; omega
    have h0 : wordN b t = 0 := by
      unfold wordN
      rw [List.getD_eq_default _ _ hlen]
      decide +kernel
    rw [h0]
    have : sAbs 0 = 0 := by
      unfold sAbs sInt
      rw [if_pos (by omega)]
      simp
    rw [this]
    exact Nat.zero_le _

end HachiEquiv.RingSigned
