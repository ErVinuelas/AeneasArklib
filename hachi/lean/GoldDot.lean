/-
The **Goldilocks dot** (candidate T27), layer 3: the term accumulation, the
offset reconstruction, and the headline.

The structure is flatter than the two-prime path's. There, `dot_prepared_digits`
loops over chunks of `DOT_CHUNK_D = 2048` terms because `2·L·BOUND_D` has to
stay under `p1·p2`; here the same quantity is `1.153·10^18` against
`1.845·10^19` at the full 8192-term width, so there is **one chunk**, and the
chunk loop disappears entirely along with `garner2`.

What does not change is the offset: `gold_untwist_off` adds `L · BOUND_D` exactly
as `untwist` adds `L · boff`, so `RingFused`'s `offConvSumD` and its four bound
lemmas are reused verbatim. `BOUND_D` is a multiple of `q`, so the offset
vanishes in the final reduction — that is `offConvSumD_cast_q`, also reused.
Only the ceiling is restated, at the new radix.
-/
import RingFused
import GoldArith
import GoldTransform
import GoldFusedBoundary

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

set_option maxRecDepth 8192

namespace HachiEquiv.GoldDot

open HachiEquiv.NttStage HachiEquiv.RingFused HachiEquiv.GoldArith
open HachiEquiv.GoldTransform HachiEquiv.GoldFusedBoundary

theorem GP_pos : 0 < GP := by norm_num

theorem gold_mac_into_spec (acc af bf : alloc.vec.Vec Std.U64) (nU : Std.Usize)
    (kU : Std.Usize) (base : ℕ → ZMod GP)
    (hn : nU.val = N) (hk : kU.val ≤ N)
    (hacc : Canon GP acc) (haf : Canon GP af) (hbf : Canon GP bf)
    (hval : ∀ t, t < N → resK GP acc t
              = base t + (if t < kU.val then
                  resK GP af t * resK GP bf t else 0)) :
    ring.mac_into_gold_loop af bf nU acc kU
      ⦃ z => Canon GP z ∧ ∀ t, t < N → resK GP z t
              = base t + resK GP af t * resK GP bf t ⦄ := by
  rw [ring.mac_into_gold_loop]
  apply loop.spec_decr_nat (fun r => nU.val - r.2.val)
    (fun r => r.2.val ≤ N ∧ Canon GP r.1
      ∧ ∀ t, t < N → resK GP r.1 t
              = base t + (if t < r.2.val then
                  resK GP af t * resK GP bf t else 0))
  · rintro ⟨d, kk⟩ ⟨hkk, hcd, hw⟩
    dsimp only at hkk hcd hw
    simp only [ring.mac_into_gold_loop.body]
    by_cases hlt : kk < nU
    · rw [if_pos hlt]
      have hklt : kk.val < N := by rw [← hn]; scalar_tac
      have hab : kk.val < af.val.length := by rw [haf.1]; exact hklt
      have hbb : kk.val < bf.val.length := by rw [hbf.1]; exact hklt
      have hdb : kk.val < d.val.length := by rw [hcd.1]; exact hklt
      step as ⟨x, hx⟩
      step as ⟨y, hy⟩
      have hxv : x.val = wordAt af kk.val := by
        rw [hx, ← wordAt_of_lt (v := af) (t := kk.val) hab]
      have hyv : y.val = wordAt bf kk.val := by
        rw [hy, ← wordAt_of_lt (v := bf) (t := kk.val) hbb]
      have hxlt : x.val < GP := by rw [hxv]; exact wordAt_lt haf GP_pos _
      have hylt : y.val < GP := by rw [hyv]; exact wordAt_lt hbf GP_pos _
      step with gold_mul_spec x y as ⟨pr, hprv, hprlt⟩
      step as ⟨cur, hcur⟩
      have hcurv : cur.val = wordAt d kk.val := by
        rw [hcur, ← wordAt_of_lt (v := d) (t := kk.val) hdb]
      have hcurlt : cur.val < GP := by rw [hcurv]; exact wordAt_lt hcd GP_pos _
      step with gold_add_spec cur pr hcurlt hprlt as ⟨z, hzv, hzlt⟩
      step as ⟨elem, back, helem, hback⟩
      step as ⟨kk1, hkk1⟩
      rw [hback]
      refine ⟨by rw [hkk1]; omega, Canon_set hcd hzlt, ?_, by rw [hkk1]; omega⟩
      intro t ht
      rw [hkk1]
      by_cases heq : t = kk.val
      · rw [heq]
        simp only [resK]
        rw [wordAt_set_eq hdb, hzv, hprv]
        have hc1 : ((((cur.val + (x.val * y.val) % GP) % GP : ℕ)) : ZMod GP)
            = ((cur.val : ℕ) : ZMod GP)
              + ((x.val : ℕ) : ZMod GP) * ((y.val : ℕ) : ZMod GP) := by
          rw [ZMod.natCast_mod]; push_cast; rw [ZMod.natCast_mod]; push_cast; ring
        rw [hc1, hcurv, hxv, hyv]
        have hbase := hw kk.val hklt
        simp only [resK] at hbase
        rw [hbase, if_neg (by omega), add_zero, if_pos (by omega)]
      · simp only [resK]
        rw [wordAt_set_ne heq]
        have hbase := hw t ht
        simp only [resK] at hbase
        rw [hbase]
        by_cases hlt2 : t < kk.val
        · rw [if_pos hlt2, if_pos (by omega)]
        · rw [if_neg hlt2, if_neg (by omega)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : kk.val = N := by rw [← hn]; scalar_tac
      refine ⟨hcd, ?_⟩
      intro t ht
      rw [hw t ht, heq, if_pos ht]
  · exact ⟨hk, hacc, hval⟩

/-! ### Card T34: the loader and the offset MAC

The word gather used to be the two-prime path's loop verbatim, followed by
`gold_twist` over its result -- two passes and two 8 KiB allocations per
right-hand polynomial. Card T34 fuses them into `load_twisted_into`, writing
the twisted word where the coefficient is read, into a buffer the caller
recycles. `gold_words_eq`, which said the gather was `rfl`-equal to the
two-prime one, is gone with the loop it was about.

The two lemmas below are the whole proof cost of the card. Neither moves a
statement above it: `gold_terms_spec`'s conclusion is unchanged, and so is
everything that steps through it. -/

/-- The fused loader writes the ψ-twisted words of `a` into `w`.

One loop where there were two, so one lemma where there were two
(`prep_words_b_spec` then `gold_twist_cast`). The loop state is the 3-tuple
`(a, w, t)` -- the borrowed operand rides along, the shape `add_loop` and
`sub_loop` already have. -/
theorem load_twisted_into_loop_spec (a : ring.Rq) (pt : alloc.vec.Vec Std.U64)
    (nU : Std.Usize) (w : alloc.vec.Vec Std.U64) (tU : Std.Usize) (ps : ZMod GP)
    (hn : nU.val = N) (hwf : HachiEquiv.Ring.Wf a)
    (hptC : Canon GP pt) (hptv : ∀ e, e < N → resK GP pt e = ps ^ e)
    (ht : tU.val ≤ N) (hwl : w.val.length = N)
    (hwc : ∀ e, e < tU.val → (wordAt w e) < GP)
    (hwv : ∀ e, e < tU.val → resK GP w e
      = NttMath.twistR ps (fun u => ((HachiEquiv.Ring.wordN a u : ℕ) : ZMod GP)) e) :
    ring.load_twisted_into_loop a pt nU w tU
      ⦃ z => Canon GP z ∧ ∀ e, e < N → resK GP z e
               = NttMath.twistR ps
                   (fun u => ((HachiEquiv.Ring.wordN a u : ℕ) : ZMod GP)) e ⦄ := by
  rw [ring.load_twisted_into_loop]
  apply loop.spec_decr_nat (fun r => nU.val - r.2.2.val)
    (fun r => r.2.2.val ≤ N ∧ r.1 = a ∧ r.2.1.val.length = N
      ∧ (∀ e, e < r.2.2.val → (wordAt r.2.1 e) < GP)
      ∧ ∀ e, e < r.2.2.val → resK GP r.2.1 e
          = NttMath.twistR ps
              (fun u => ((HachiEquiv.Ring.wordN a u : ℕ) : ZMod GP)) e)
  · rintro ⟨aa, d, tt⟩ ⟨htt, haa, hdl, hdc, hdv⟩
    dsimp only at htt haa hdl hdc hdv
    subst haa
    simp only [ring.load_twisted_into_loop.body]
    by_cases hlt : tt < nU
    · rw [if_pos hlt]
      have httlt : tt.val < N := by rw [← hn]; scalar_tac
      have hab : tt.val < aa.val.length := by rw [hwf.1]; exact httlt
      have hpb : tt.val < pt.val.length := by rw [hptC.1]; exact httlt
      have hdb : tt.val < d.val.length := by rw [hdl]; exact httlt
      step as ⟨f, hf⟩
      step with HachiEquiv.Ring.to_u64_id f as ⟨x, hx⟩
      have hxv : x.val = HachiEquiv.Ring.wordN aa tt.val := by
        rw [hx, hf]
        unfold HachiEquiv.Ring.wordN
        rw [List.getD_eq_getElem _ _ hab]
      have hxlt : x.val < GP := by
        have hq : x.val < HachiEquiv.NttProduct.q := by
          rw [hx, hf]; exact hwf.2 _ (List.getElem_mem hab)
        have : (HachiEquiv.NttProduct.q : ℕ) < GP := by
          unfold HachiEquiv.NttProduct.q GP; norm_num
        omega
      step as ⟨y, hy⟩
      have hyv : y.val = wordAt pt tt.val := by
        rw [hy, ← wordAt_of_lt (v := pt) (t := tt.val) hpb]
      have hylt : y.val < GP := by rw [hyv]; exact wordAt_lt hptC GP_pos _
      step with gold_mul_spec x y as ⟨pr, hprv, hprlt⟩
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
          rw [wordAt_set_eq hdb, hprv, hxv, hyv]
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

/-- [`load_twisted_into`] at its entry point. -/
theorem load_twisted_into_spec (w : alloc.vec.Vec Std.U64) (a : ring.Rq)
    (pt : alloc.vec.Vec Std.U64) (ps : ZMod GP)
    (hwf : HachiEquiv.Ring.Wf a) (hwl : w.val.length = N)
    (hptC : Canon GP pt) (hptv : ∀ e, e < N → resK GP pt e = ps ^ e) :
    ring.load_twisted_into w a pt
      ⦃ z => Canon GP z ∧ ∀ e, e < N → resK GP z e
               = NttMath.twistR ps
                   (fun u => ((HachiEquiv.Ring.wordN a u : ℕ) : ZMod GP)) e ⦄ := by
  rw [ring.load_twisted_into]
  exact load_twisted_into_loop_spec a pt ntt.NTT_LEN w 0#usize ps
    ntt_NTT_LEN_val hwf hptC hptv (by simp) hwl
    (by intro e he; simp at he) (by intro e he; simp at he)

/-- The offset MAC: [`gold_mac_into_spec`] reading its left factor out of the
prepared table in place, at `base + k`, instead of out of an 8 KiB copy.

The left factor arrives as an abstract `A : ℕ → ZMod GP` with `hA` saying the
table holds it, because `prep.fwd` is `endU * N` long and `Canon` -- which
pins the length at `N` -- does not apply to it. That is the same reason
`gold_terms_spec` carried `hpc` separately for `slice_out`'s result. -/
theorem gold_mac_off_spec (acc pfwd bf : alloc.vec.Vec Std.U64)
    (baseU nU kU : Std.Usize) (base A : ℕ → ZMod GP)
    (hn : nU.val = N) (hk : kU.val ≤ N)
    (hb : baseU.val + N ≤ pfwd.val.length)
    (hacc : Canon GP acc) (hbf : Canon GP bf)
    (hpc : ∀ u ∈ pfwd.val, u.val < GP)
    (hA : ∀ t, t < N → ((wordAt pfwd (baseU.val + t) : ℕ) : ZMod GP) = A t)
    (hval : ∀ t, t < N → resK GP acc t
              = base t + (if t < kU.val then A t * resK GP bf t else 0)) :
    ring.mac_into_gold_off_loop pfwd baseU bf nU acc kU
      ⦃ z => Canon GP z ∧ ∀ t, t < N → resK GP z t
              = base t + A t * resK GP bf t ⦄ := by
  rw [ring.mac_into_gold_off_loop]
  apply loop.spec_decr_nat (fun r => nU.val - r.2.val)
    (fun r => r.2.val ≤ N ∧ Canon GP r.1
      ∧ ∀ t, t < N → resK GP r.1 t
              = base t + (if t < r.2.val then A t * resK GP bf t else 0))
  · rintro ⟨d, kk⟩ ⟨hkk, hcd, hw⟩
    dsimp only at hkk hcd hw
    simp only [ring.mac_into_gold_off_loop.body]
    by_cases hlt : kk < nU
    · rw [if_pos hlt]
      have hklt : kk.val < N := by rw [← hn]; scalar_tac
      have hbb : kk.val < bf.val.length := by rw [hbf.1]; exact hklt
      have hdb : kk.val < d.val.length := by rw [hcd.1]; exact hklt
      step as ⟨idx, hidx⟩
      have hidxb : idx.val < pfwd.val.length := by rw [hidx]; omega
      step as ⟨x, hx⟩
      step as ⟨y, hy⟩
      have hxv : x.val = wordAt pfwd (baseU.val + kk.val) := by
        rw [hx, ← wordAt_of_lt (v := pfwd) (t := idx.val) hidxb, hidx]
      have hyv : y.val = wordAt bf kk.val := by
        rw [hy, ← wordAt_of_lt (v := bf) (t := kk.val) hbb]
      have hxlt : x.val < GP := by
        rw [hx]; exact hpc _ (List.getElem_mem hidxb)
      have hylt : y.val < GP := by rw [hyv]; exact wordAt_lt hbf GP_pos _
      step with gold_mul_spec x y as ⟨pr, hprv, hprlt⟩
      step as ⟨cur, hcur⟩
      have hcurv : cur.val = wordAt d kk.val := by
        rw [hcur, ← wordAt_of_lt (v := d) (t := kk.val) hdb]
      have hcurlt : cur.val < GP := by rw [hcurv]; exact wordAt_lt hcd GP_pos _
      step with gold_add_spec cur pr hcurlt hprlt as ⟨z, hzv, hzlt⟩
      step as ⟨elem, back, helem, hback⟩
      step as ⟨kk1, hkk1⟩
      rw [hback]
      refine ⟨by rw [hkk1]; omega, Canon_set hcd hzlt, ?_, by rw [hkk1]; omega⟩
      intro t ht
      rw [hkk1]
      by_cases heq : t = kk.val
      · rw [heq]
        simp only [resK]
        rw [wordAt_set_eq hdb, hzv, hprv]
        have hc1 : ((((cur.val + (x.val * y.val) % GP) % GP : ℕ)) : ZMod GP)
            = ((cur.val : ℕ) : ZMod GP)
              + ((x.val : ℕ) : ZMod GP) * ((y.val : ℕ) : ZMod GP) := by
          rw [ZMod.natCast_mod]; push_cast; rw [ZMod.natCast_mod]; push_cast; ring
        rw [hc1, hcurv, hxv, hyv, hA kk.val hklt]
        have hbase := hw kk.val hklt
        simp only [resK] at hbase
        rw [hbase, if_neg (by omega), add_zero, if_pos (by omega)]
      · simp only [resK]
        rw [wordAt_set_ne heq]
        have hbase := hw t ht
        simp only [resK] at hbase
        rw [hbase]
        by_cases hlt2 : t < kk.val
        · rw [if_pos hlt2, if_pos (by omega)]
        · rw [if_neg hlt2, if_neg (by omega)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : kk.val = N := by rw [← hn]; scalar_tac
      refine ⟨hcd, ?_⟩
      intro t ht
      rw [hw t ht, heq, if_pos ht]
  · exact ⟨hk, hacc, hval⟩

/-- [`NttProduct.twist_cast`] in this lane: the twist in `ZMod GP`. -/
theorem gold_twist_cast (v pt : alloc.vec.Vec Std.U64)
    (hv : v.val.length = N) (hpt : Canon GP pt) (psi : ZMod GP)
    (hpsi : ∀ e, e < N → resK GP pt e = psi ^ e) :
    ntt.gold_twist v pt
      ⦃ z => Canon GP z
             ∧ ∀ t, t < N →
                 resK GP z t
                   = NttMath.twistR psi (fun u => ((wordAt v u : ℕ) : ZMod GP)) t ⦄ := by
  apply spec_mono (gold_twist_spec v pt hv hpt)
  rintro z ⟨hzc, hzval⟩
  refine ⟨hzc, ?_⟩
  intro t ht
  have hp : resK GP pt t = psi ^ t := hpsi t ht
  simp only [resK, NttMath.twistR] at hp ⊢
  rw [hzval t ht, ZMod.natCast_mod, Nat.cast_mul, hp]

theorem gold_terms_spec (prep : ring.PreparedVecG)
    (a b : alloc.vec.Vec ring.Rq) (startU endU : Std.Usize)
    (nU : Std.Usize) (pt : alloc.vec.Vec Std.U64)
    (acc scratch cur : alloc.vec.Vec Std.U64) (jU : Std.Usize) (ps : ZMod GP)
    (hn : nU.val = N) (hord : ps ^ N = -1)
    (hptC : Canon GP pt) (hptv : ∀ e, e < N → resK GP pt e = ps ^ e)
    (hpl : endU.val * N ≤ prep.fwd.val.length)
    (hpv : ∀ j, j < endU.val → ∀ t, t < N →
        resK GP prep.fwd (j * N + t)
          = NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK GP a j)) t)
    (hpc : ∀ u ∈ prep.fwd.val, u.val < GP)
    (hbwf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbe : endU.val ≤ b.val.length)
    (hjs : startU.val ≤ jU.val) (hje : jU.val ≤ endU.val)
    (haccC : Canon GP acc) (hscC : Canon GP scratch) (hcurC : Canon GP cur)
    (hval : ∀ t, t < N → resK GP acc t
              = ∑ u ∈ Finset.Ico startU.val jU.val, termFwd ps a b u t) :
    ring.dot_prepared_digits_gold_loop0 prep b endU nU pt acc scratch cur jU
      ⦃ z => Canon GP z.1 ∧ Canon GP z.2
             ∧ ∀ t, t < N → resK GP z.1 t
                 = ∑ u ∈ Finset.Ico startU.val endU.val, termFwd ps a b u t ⦄ := by
  rw [ring.dot_prepared_digits_gold_loop0]
  apply loop.spec_decr_nat (fun r => endU.val - r.2.2.2.val)
    (fun r => startU.val ≤ r.2.2.2.val ∧ r.2.2.2.val ≤ endU.val
      ∧ Canon GP r.1 ∧ Canon GP r.2.1 ∧ Canon GP r.2.2.1
      ∧ ∀ t, t < N → resK GP r.1 t
              = ∑ u ∈ Finset.Ico startU.val r.2.2.2.val, termFwd ps a b u t)
  · rintro ⟨d, sc, cu, jj⟩ ⟨hjjs, hjje, hcd, hcsc, hcuC, hw⟩
    dsimp only at hjjs hjje hcd hcsc hcuC hw
    simp only [ring.dot_prepared_digits_gold_loop0.body]
    by_cases hlt : jj < endU
    · rw [if_pos hlt]
      have hjjlt : jj.val < endU.val := by scalar_tac
      have hjb : jj.val < b.val.length := by omega
      step as ⟨rq, hrq⟩
      have hrqv : rq = b.val.getD jj.val (alloc.vec.Vec.new cpoly.field.Fp) := by
        rw [hrq, List.getD_eq_getElem _ _ hjb]
      step as ⟨off, hoff⟩
      have hoffv : off.val = jj.val * N := by rw [hoff, hn]
      have hslb : off.val + N ≤ prep.fwd.val.length := by
        rw [hoffv]
        have h1 : (jj.val + 1) * N ≤ endU.val * N := Nat.mul_le_mul_right N (by omega)
        have h2 : (jj.val + 1) * N = jj.val * N + N := by ring
        omega
      -- the table's entry IS this term's left transform; card T34 part 1B reads
      -- it in place, so it arrives as the abstract `A` of `gold_mac_off_spec`
      -- rather than as an 8 KiB copy
      have hFA : ∀ t, t < N → ((wordAt prep.fwd (off.val + t) : ℕ) : ZMod GP)
          = NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK GP a jj.val)) t := by
        intro t ht
        rw [hoffv]
        have := hpv jj.val hjjlt t ht
        simpa only [resK] using this
      -- card T37: twist, transform and multiply-accumulate in one fused term,
      -- with the first and last passes of the transform fused into their
      -- neighbours. One step where cards T34 and T27 took three.
      step with gold_dot_one_fused_spec rq cu sc d pt prep.fwd off ps
        (fun t => NttMath.difRun (ps ^ 2) 10 1
          (NttMath.twistR ps (entryK GP a jj.val)) t)
        (by rw [hrqv]; exact hbwf jj.val hjjlt) hcuC hcsc hcd hptC hptv hslb hFA
        as ⟨acc1, cur1, sc1, hac1C, hcu1C, hsc1C, hac1v⟩
      have hFB : NttMath.twistR ps
            (fun u => ((HachiEquiv.Ring.wordN rq u : ℕ) : ZMod GP))
          = NttMath.twistR ps (entryK GP b jj.val) := by
        rw [hrqv]; rfl
      step as ⟨jj1, hjj1⟩
      refine ⟨by rw [hjj1]; omega, by rw [hjj1]; omega, hac1C, hsc1C, hcu1C, ?_,
        by rw [hjj1]; omega⟩
      intro t ht
      rw [hjj1, Finset.sum_Ico_succ_top (by omega), ← hw t ht]
      rw [hac1v t ht, hFB]
      unfold termFwd
      rw [← HachiEquiv.NttProduct.prod_difRun ps hord (entryK GP a jj.val) (entryK GP b jj.val)
        (NttMath.difRun (ps ^ 2) 10 1 (NttMath.twistR ps (entryK GP a jj.val)))
        (NttMath.difRun (ps ^ 2) 10 1 (NttMath.twistR ps (entryK GP b jj.val)))
        (fun t' => NttMath.difRun (ps ^ 2) 10 1
            (NttMath.twistR ps (entryK GP a jj.val)) t'
          * NttMath.difRun (ps ^ 2) 10 1
            (NttMath.twistR ps (entryK GP b jj.val)) t')
        (fun t' _ => rfl) (fun t' _ => rfl) (fun t' _ => rfl) t ht]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = endU.val := by scalar_tac
      refine ⟨hcd, hcsc, ?_⟩
      intro t ht
      rw [hw t ht, heq]
  · exact ⟨hjs, hje, haccC, hscC, hcurC, hval⟩

theorem gold_out_loop_spec (degU : Std.Usize) (qwU : Std.U64)
    (words : alloc.vec.Vec Std.U64) (out : alloc.vec.Vec cpoly.field.Fp)
    (tU : Std.Usize) (X : ℕ → ℕ)
    (hdeg : degU.val = N) (hqwv : qwU.val = HachiEquiv.NttProduct.q)
    (hv : ∀ k, k < N → wordAt words k = X k)
    (hl : words.val.length = N)
    (ht : tU.val ≤ N) (hlen : out.val.length = tU.val)
    (hred : ∀ u ∈ out.val, HachiEquiv.Field.Red u)
    (hval : ∀ k, k < tU.val →
      HachiEquiv.Ring.wordN out k = X k % HachiEquiv.NttProduct.q) :
    ring.dot_prepared_digits_gold_loop1 degU qwU words out tU
      ⦃ z => HachiEquiv.Ring.Wf z ∧ ∀ k, k < N →
          HachiEquiv.Ring.wordN z k = X k % HachiEquiv.NttProduct.q ⦄ := by
  rw [ring.dot_prepared_digits_gold_loop1]
  apply loop.spec_decr_nat (fun r => N - r.2.val)
    (fun r => r.2.val ≤ N ∧ r.1.val.length = r.2.val
      ∧ (∀ u ∈ r.1.val, HachiEquiv.Field.Red u)
      ∧ ∀ k, k < r.2.val →
          HachiEquiv.Ring.wordN r.1 k = X k % HachiEquiv.NttProduct.q)
  · rintro ⟨o1, tt⟩ ⟨htt, hlen1, hred1, hval1⟩
    dsimp only at htt hlen1 hred1 hval1
    simp only [ring.dot_prepared_digits_gold_loop1.body]
    by_cases hlt : tt < degU
    · rw [if_pos hlt]
      have httlt : tt.val < N := by rw [← hdeg]; scalar_tac
      have hb1 : tt.val < words.val.length := by rw [hl]; exact httlt
      step as ⟨g, hg⟩
      have hgv : g.val = X tt.val := by
        rw [hg, ← wordAt_of_lt (v := words) (t := tt.val) hb1]; exact hv tt.val httlt
      step as ⟨md, hmd⟩
      have hmdv : md.val = X tt.val % HachiEquiv.NttProduct.q := by
        rw [hmd, hgv, hqwv]
      have hmdlt : md.val < HachiEquiv.NttProduct.q := by
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
        simp only [HachiEquiv.Ring.wordN] at hval1 ⊢
        rcases Nat.lt_or_ge k tt.val with hklt | hkge
        · rw [ho2, getD_append_lt' _ _ _ (by omega)]
          exact hval1 k hklt
        · have hkeq : k = o1.val.length := by omega
          rw [hkeq, ho2, getD_append_eq', hlen1]
          have hfv : f.val = md.val := by
            have h1 := HachiEquiv.NttProduct.natCast_inj_of_lt
              (n := HachiEquiv.NttProduct.q) (x := f.val) (y := md.val) hfred hfval
            rwa [Nat.mod_eq_of_lt hmdlt] at h1
          rw [hfv, hmdv]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : tt.val = N := by rw [← hdeg]; scalar_tac
      exact ⟨⟨by rw [hlen1, heq], hred1⟩,
        fun k hk => hval1 k (by rw [heq]; exact hk)⟩
  · exact ⟨ht, hlen, hred, hval⟩

theorem gold_untwist_loop_spec (src it : alloc.vec.Vec Std.U64) (off : Std.U64)
    (n : Std.Usize) (out : alloc.vec.Vec Std.U64) (t : Std.Usize)
    (hsrc : Canon GP src) (hit : Canon GP it)
    (hoff : off.val < GP)
    (hn : n.val ≤ N) (ht : t.val ≤ n.val) (hlen : out.val.length = t.val)
    (hred : ∀ u ∈ out.val, u.val < GP)
    (hval : ∀ k, k < t.val →
      wordAt out k
        = ((wordAt src k * wordAt it k % GP) * (ntt.GOLD_NINV).val % GP + off.val) % GP) :
    ntt.gold_untwist_off_loop src it off n out t
      ⦃ z => z.val.length = n.val ∧ (∀ u ∈ z.val, u.val < GP)
             ∧ ∀ k, k < n.val →
                 wordAt z k
                   = ((wordAt src k * wordAt it k % GP) * (ntt.GOLD_NINV).val % GP
                       + off.val) % GP ⦄ := by
  rw [ntt.gold_untwist_off_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧
      (∀ u ∈ s.1.val, u.val < GP) ∧
      ∀ k, k < s.2.val → wordAt s.1 k
        = ((wordAt src k * wordAt it k % GP) * (ntt.GOLD_NINV).val % GP + off.val) % GP)
  · rintro ⟨o1, t1⟩ ⟨ht1, hlen1, hred1, hval1⟩
    dsimp only at ht1 hlen1 hred1 hval1
    simp only [ntt.gold_untwist_off_loop.body]
    by_cases hlt : t1 < n
    · rw [if_pos hlt]
      have hisrc : t1.val < src.val.length := by rw [hsrc.1]; scalar_tac
      have hiit : t1.val < it.val.length := by rw [hit.1]; scalar_tac
      have hcap : o1.val.length < Usize.max := by scalar_tac
      step as ⟨i, hi⟩
      have hil : i.val < GP := hi ▸ hsrc.2 _ (List.getElem_mem hisrc)
      step as ⟨i1, hi1⟩
      have hi1l : i1.val < GP := hi1 ▸ hit.2 _ (List.getElem_mem hiit)
      step with gold_mul_spec i i1 as ⟨u, huv, hul⟩
      step with gold_mul_spec u ntt.GOLD_NINV as ⟨s, hsv, hsl⟩
      step with gold_add_spec s off hsl hoff as ⟨i2, hi2v, hi2l⟩
      step as ⟨o2, ho2⟩
      step as ⟨t2, ht2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, List.length_append, hlen1]; scalar_tac
      · intro w hw
        rw [ho2] at hw
        rcases List.mem_append.mp hw with hh | hh
        · exact hred1 w hh
        · rw [List.mem_singleton.mp hh]; exact hi2l
      · intro k hk
        rw [ht2] at hk
        rcases Nat.lt_or_ge k t1.val with hklt | hkge
        · rw [wordAt_pushed_lt ho2 (by omega), hval1 k hklt]
        · have hkeq : k = o1.val.length := by omega
          rw [hkeq, wordAt_pushed_eq ho2, hlen1, hi2v, hsv, huv,
            wordAt_of_lt hisrc, wordAt_of_lt hiit, hi, hi1]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : t1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hred1, by rw [← heq]; exact hval1⟩
  · exact ⟨ht, hlen, hred, hval⟩

theorem gold_untwist_spec (src it : alloc.vec.Vec Std.U64) (off : Std.U64)
    (hsrc : Canon GP src) (hit : Canon GP it)
    (hoff : off.val < GP) :
    ntt.gold_untwist_off src it off
      ⦃ z => Canon GP z
             ∧ ∀ t, t < N →
                 wordAt z t
                   = ((wordAt src t * wordAt it t % GP) * (ntt.GOLD_NINV).val % GP
                       + off.val) % GP ⦄ := by
  rw [ntt.gold_untwist_off]
  simp only [alloc.vec.Vec.with_capacity]
  apply spec_mono (gold_untwist_loop_spec src it off ntt.NTT_LEN
    (alloc.vec.Vec.new Std.U64) 0#usize hsrc hit hoff
    (by simp) (by simp) (by simp) (by intro u hu; simp at hu)
    (by intro k hk; simp at hk))
  rintro z ⟨hzlen, hzred, hzval⟩
  refine ⟨⟨by rw [hzlen, ntt_NTT_LEN_val], hzred⟩, ?_⟩
  intro k hk
  exact hzval k (by rw [ntt_NTT_LEN_val]; exact hk)

theorem gold_untwist_cast (src it : alloc.vec.Vec Std.U64) (off : Std.U64)
    (hsrc : Canon GP src) (hit : Canon GP it)
    (hoff : off.val < GP) (psii : ZMod GP)
    (hpsii : ∀ e, e < N → resK GP it e = psii ^ e) :
    ntt.gold_untwist_off src it off
      ⦃ z => Canon GP z
             ∧ ∀ t, t < N →
                 resK GP z t
                   = resK GP src t * psii ^ t * (((ntt.GOLD_NINV).val : ℕ) : ZMod GP)
                     + ((off.val : ℕ) : ZMod GP) ⦄ := by
  apply spec_mono (gold_untwist_spec src it off hsrc hit hoff)
  rintro z ⟨hzc, hzval⟩
  refine ⟨hzc, ?_⟩
  intro t ht
  have hp : resK GP it t = psii ^ t := hpsii t ht
  simp only [resK] at hp ⊢
  rw [hzval t ht, ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_mod, Nat.cast_mul,
    ZMod.natCast_mod, Nat.cast_mul, hp]

/-! ### The Goldilocks root data

The same four closed facts `NttProduct` proves for each 30-bit prime, at a
64-bit one. `decide +kernel` still does it: `ZMod p` is `Fin p`, the
exponentiation is by squaring, and the kernel's arithmetic is GMP's — the
modulus being 64 bits rather than 30 costs nothing it notices. -/

set_option maxRecDepth 100000 in
theorem gpsi_ord : ((ntt.GOLD_PSI.val : ℕ) : ZMod GP) ^ N = -1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gpsi_inv : ((ntt.GOLD_PSI.val : ℕ) : ZMod GP)
    * ((ntt.GOLD_PSIINV.val : ℕ) : ZMod GP) = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gninv_inv : ((N : ℕ) : ZMod GP) * ((ntt.GOLD_NINV.val : ℕ) : ZMod GP) = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gdoff_val : (ntt.GOLD_DOFF).val = BOUND_D := by
  decide +kernel

/-- The ceiling, at the new radix. Where the two-prime path must chunk at
`DOT_CHUNK_D = 2048` to keep `2·L·BOUND_D` under `p1·p2`, one Goldilocks lane
holds the **whole** 8192-term width: `1.153·10^18` against `1.845·10^19`, a
sixteenfold margin. That is why there is no chunk loop here. -/
theorem offConvSumD_lt_GP (a b : alloc.vec.Vec ring.Rq) (st en k : ℕ)
    (hawf : ∀ u, u < en → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbd : ∀ u, u < en → DigitWf (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hL : en - st ≤ 8192) :
    offConvSumD a b st en k < GP := by
  have hp := posQD_sum_le a b st en k hawf hbd
  have hnum : 2 * 8192 * BOUND_D < GP := by
    simp only [BOUND_D, HachiEquiv.NttProduct.q, GP]
    norm_num
  have hmul : (en - st) * BOUND_D ≤ 8192 * BOUND_D :=
    Nat.mul_le_mul_right BOUND_D hL
  simp only [offConvSumD]
  omega


/-- `prep.fwd` is a correct single-lane preparation of `a`'s first `n` entries.
[`RingFused.PrepAt`] with the prime fixed. -/
def PrepAtG (prep : ring.PreparedVecG) (a : alloc.vec.Vec ring.Rq) (n : ℕ) : Prop :=
  n * N ≤ prep.fwd.val.length
  ∧ (∀ u ∈ prep.fwd.val, u.val < GP)
  ∧ ∀ j, j < n → ∀ t, t < N →
      resK GP prep.fwd (j * N + t)
        = NttMath.difRun (((ntt.GOLD_PSI.val : ℕ) : ZMod GP) ^ 2) 10 1
            (NttMath.twistR ((ntt.GOLD_PSI.val : ℕ) : ZMod GP) (entryK GP a j)) t

set_option maxHeartbeats 4000000 in
/-- **`dot_prepared_digits_gold` computes the dot product**, in one lane.

`dot_prepared_digits_spec`'s conclusion word for word — the same negacyclic
convolution sum, in the same vocabulary. What the statement does *not* carry is
the two-prime path's apparatus: there is one `PrepAtG` where there are two
`PrepAt`s, and no chunk width anywhere, because the whole width fits
(`offConvSumD_lt_GP`). -/
theorem gold_dot_spec (prep : ring.PreparedVecG) (a b : alloc.vec.Vec ring.Rq)
    (nU : Std.Usize)
    (haw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbd : ∀ u, u < nU.val → DigitWf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (han : nU.val ≤ a.val.length) (hbn : nU.val ≤ b.val.length)
    (hwidth : nU.val ≤ 8192)
    (hp : PrepAtG prep a nU.val) :
    ring.dot_prepared_digits_gold prep b nU
      ⦃ z => HachiEquiv.Ring.Wf z ∧ ∀ k, k < N → HachiEquiv.Ring.coeffK z k
              = ∑ u ∈ Finset.range nU.val, HachiEquiv.Ring.negConv
                  (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                  (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k ⦄ := by
  obtain ⟨hpl, hpc, hpv⟩ := hp
  set ps : ZMod GP := ((ntt.GOLD_PSI.val : ℕ) : ZMod GP) with hpsdef
  set psii : ZMod GP := ((ntt.GOLD_PSIINV.val : ℕ) : ZMod GP) with hpsiidef
  have hord : ps ^ N = -1 := gpsi_ord
  have hpinv : ps * psii = 1 := gpsi_inv
  have hRN : params.RING_DEGREE = ntt.NTT_LEN := by decide +kernel
  rw [ring.dot_prepared_digits_gold, hRN]
  step with gold_psi_table_cast ntt.GOLD_PSI (by decide +kernel) as ⟨pt, hptC, hptv⟩
  step with gold_psi_table_cast ntt.GOLD_PSIINV (by decide +kernel) as ⟨it, hitC, hitv⟩
  step with zeros_canon_zero GP GP_pos as ⟨acc0, hacc0C, hacc0v⟩
  step with gold_terms_spec prep a b 0#usize nU ntt.NTT_LEN pt acc0 acc0 acc0
    0#usize ps ntt_NTT_LEN_val hord hptC hptv hpl hpv hpc hbw hbn
    (by simp) (by simp) hacc0C hacc0C hacc0C
    (by intro t ht; rw [hacc0v t ht]; simp)
    as ⟨acc1, scratch, hac1C, hac2C, hac1v⟩
  -- the offset, scaled by the term count
  have hcn : lift (UScalar.cast .U64 nU) ⦃ y => y.val = nU.val ⦄ :=
    UScalar.cast_inBounds_spec .U64 nU (by scalar_tac)
  step with hcn as ⟨nw, hnw⟩
  step with gold_mul_spec ntt.GOLD_DOFF nw as ⟨scaled, hscv, hsclt⟩
  -- the inverse transform, and the value it carries
  have hPR : ∀ t, t < N → resK GP acc1 t
      = NttMath.difRun (ps ^ 2) 10 1
          (fun t' => ∑ u ∈ Finset.Ico 0 nU.val,
            NttMath.cyclicConv N (NttMath.twistR ps (entryK GP a u))
              (NttMath.twistR ps (entryK GP b u)) t') t := by
    intro t ht
    rw [hac1v t ht, NttMath.difRun_sum (ps ^ 2) 10 1 (Finset.Ico 0 nU.val)
      (fun u => NttMath.cyclicConv N (NttMath.twistR ps (entryK GP a u))
        (NttMath.twistR ps (entryK GP b u)))]
    simp only [termFwd, hpsdef]
  step with gold_inverse_spec acc1 scratch it hac1C hac2C hitC psii hitv
    as ⟨v, v5, hiv1, hiv2, hivv⟩
  have hIV := HachiEquiv.NttProduct.inv_value ps psii hpinv
    (fun t' => ∑ u ∈ Finset.Ico 0 nU.val,
      NttMath.cyclicConv N (NttMath.twistR ps (entryK GP a u))
        (NttMath.twistR ps (entryK GP b u)) t')
    (resK GP acc1) (resK GP v) hPR hivv
  -- the untwist, with the offset
  step with gold_untwist_cast v it scaled hiv1 hitC hsclt psii hitv
    as ⟨words, hwC, hwv⟩
  -- the resK value of `words` is the offset convolution sum
  have hres : ∀ t, t < N → resK GP words t
      = (∑ u ∈ Finset.Ico 0 nU.val,
          NttMath.negConvR N (entryK GP a u) (entryK GP b u) t)
        + ((scaled.val : ℕ) : ZMod GP) := by
    intro t ht
    rw [hwv t ht, hIV t ht,
      untwist_value_sum ps psii ((ntt.GOLD_NINV.val : ℕ) : ZMod GP) hord hpinv
        gninv_inv (Finset.Ico 0 nU.val) (fun u => entryK GP a u)
        (fun u => entryK GP b u) t ht]
  -- and therefore its words are `offConvSumD`, which fits the prime whole
  have hwordv : ∀ k, k < N → wordAt words k = offConvSumD a b 0 nU.val k := by
    intro k hk
    have hlt : offConvSumD a b 0 nU.val k < GP :=
      offConvSumD_lt_GP a b 0 nU.val k haw hbd (by omega)
    have hcast : ((wordAt words k : ℕ) : ZMod GP)
        = ((offConvSumD a b 0 nU.val k : ℕ) : ZMod GP) := by
      have hle := negQD_sum_le a b 0 nU.val k haw hbd
      have hle' : (∑ u ∈ Finset.Ico 0 nU.val,
            HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                 (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
          ≤ (∑ u ∈ Finset.Ico 0 nU.val,
              HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                   (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
            + (nU.val - 0) * BOUND_D := le_trans hle (Nat.le_add_left _ _)
      have h1 := hres k hk
      rw [resK] at h1
      rw [h1]
      unfold offConvSumD
      rw [Nat.cast_sub hle', Nat.cast_add]
      have hterm : ∀ u, NttMath.negConvR N (entryK GP a u) (entryK GP b u) k
          = ((HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod GP)
            - ((HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod GP) := by
        intro u
        rw [NttMath.negConvR, ordConv_entryK_pos GP a b u k hk,
          ordConv_entryK_neg GP a b u k hk]
      rw [Finset.sum_congr rfl (fun u _ => hterm u), Finset.sum_sub_distrib]
      push_cast
      rw [hscv, hnw, gdoff_val, ZMod.natCast_mod, Nat.sub_zero]
      push_cast
      ring
    have h2 := HachiEquiv.NttProduct.natCast_inj_of_lt (wordAt_lt hwC GP_pos k) hcast
    rwa [Nat.mod_eq_of_lt hlt] at h2
  -- the reduce-and-pack loop, then the offset vanishing mod `q`
  have hfin := gold_out_loop_spec ntt.NTT_LEN params.Q words
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize (offConvSumD a b 0 nU.val)
    ntt_NTT_LEN_val HachiEquiv.Field.params_Q_val hwordv hwC.1
    (by simp) (by simp) (by simp) (by simp)
  rw [alloc.vec.Vec.with_capacity]
  step with hfin as ⟨z, hzw, hzv⟩
  refine ⟨hzw, fun k hk => ?_⟩
  have hqq : HachiEquiv.NttProduct.q = HachiEquiv.Field.q := rfl
  rw [HachiEquiv.Ring.coeffK_eq_cast_wordN, hzv k hk, hqq, ZMod.natCast_mod,
    offConvSumD_cast_q a b 0 nU.val k hk haw hbw hbd, Finset.range_eq_Ico]

/-! ## `ring::prepare_one_gold` -- the layout claim, in one lane

`prepare_one_spec`'s three proofs with the prime fixed. Aeneas names loops per
enclosing function, so the Goldilocks preparation's two inner loops are distinct
constants from the two-prime one's and need their own specs; the arguments are
the two-prime ones with `pw mw psi` deleted. -/

theorem gold_prep_words_spec (a : alloc.vec.Vec ring.Rq) (degU jU : Std.Usize)
    (w : alloc.vec.Vec Std.U64) (tU : Std.Usize)
    (hdeg : degU.val = N) (hjb : jU.val < a.val.length)
    (haj : HachiEquiv.Ring.Wf (a.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)))
    (ht : tU.val ≤ N) (hlen : w.val.length = tU.val)
    (hval : ∀ t, t < tU.val → wordAt w t
      = HachiEquiv.Ring.wordN (a.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) t) :
    ring.prepare_one_gold_loop0_loop0 a degU jU w tU
      ⦃ z => z.val.length = N ∧ ∀ t, t < N → wordAt z t
          = HachiEquiv.Ring.wordN
              (a.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) t ⦄ := by
  rw [ring.prepare_one_gold_loop0_loop0]
  apply loop.spec_decr_nat (fun r => degU.val - r.2.val)
    (fun r => r.2.val ≤ N ∧ r.1.val.length = r.2.val
      ∧ ∀ t, t < r.2.val → wordAt r.1 t
          = HachiEquiv.Ring.wordN
              (a.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) t)
  · rintro ⟨d, tt⟩ ⟨htt, hdl, hdv⟩
    dsimp only at htt hdl hdv
    simp only [ring.prepare_one_gold_loop0_loop0.body]
    by_cases hlt : tt < degU
    · rw [if_pos hlt]
      have httlt : tt.val < N := by rw [← hdeg]; scalar_tac
      step as ⟨r, hr⟩
      have hrv : r = a.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp) := by
        rw [hr, List.getD_eq_getElem _ _ hjb]
      have hrb : tt.val < r.val.length := by rw [hrv, haj.1]; exact httlt
      step as ⟨f, hf⟩
      step with HachiEquiv.Ring.to_u64_id f as ⟨x, hx⟩
      have hxv : x.val = HachiEquiv.Ring.wordN
          (a.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) tt.val := by
        rw [hx, hf, ← hrv]
        unfold HachiEquiv.Ring.wordN
        rw [List.getD_eq_getElem _ _ hrb]
      step as ⟨d1, hd1⟩
      step as ⟨tt1, htt1⟩
      refine ⟨by rw [htt1]; omega, ?_, ?_, by rw [htt1]; omega⟩
      · rw [hd1, htt1, List.length_append, hdl]; simp
      · intro t htl
        rw [htt1] at htl
        simp only [wordAt] at hdv ⊢
        rcases Nat.lt_or_ge t tt.val with hlt2 | hge
        · rw [hd1, getD_append_lt' _ _ _ (by omega)]
          exact hdv t hlt2
        · have hteq : t = d.val.length := by omega
          rw [hteq, hd1, getD_append_eq', hdl, hxv]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : tt.val = N := by rw [← hdeg]; scalar_tac
      exact ⟨by rw [hdl, heq], fun t htl => hdv t (by rw [heq]; exact htl)⟩
  · exact ⟨ht, hlen, hval⟩


/-- The append loop, for the Goldilocks table. -/
theorem gold_prep_append_spec (degU : Std.Usize) (out : alloc.vec.Vec Std.U64)
    (f : (alloc.vec.Vec Std.U64) × (alloc.vec.Vec Std.U64)) (kU : Std.Usize)
    (base : ℕ) (hdeg : degU.val = N) (hk : kU.val ≤ N)
    -- honest: the Rust would overflow-panic otherwise, and `prepare` is only
    -- ever called at `A`'s concrete width
    (hbase : base + N ≤ Std.Usize.max)
    (hfl : f.1.val.length = N)
    (hlen : out.val.length = base + kU.val)
    (hnew : ∀ t, t < kU.val → wordAt out (base + t) = wordAt f.1 t)
    (pwv : ℕ) (hfc : ∀ x ∈ f.1.val, x.val < pwv)
    (houtc : ∀ x ∈ out.val, x.val < pwv) :
    ring.prepare_one_gold_loop0_loop1 degU out f kU
      ⦃ z => z.val.length = base + N
             ∧ (∀ t, t < base → wordAt z t = wordAt out t)
             ∧ (∀ x ∈ z.val, x.val < pwv)
             ∧ ∀ t, t < N → wordAt z (base + t) = wordAt f.1 t ⦄ := by
  -- the body pattern-matches the pair, so it has to be in constructor form
  obtain ⟨f1, f2⟩ := f
  dsimp only at hfl hnew hfc ⊢
  rw [ring.prepare_one_gold_loop0_loop1]
  apply loop.spec_decr_nat (fun r => degU.val - r.2.val)
    (fun r => r.2.val ≤ N ∧ r.1.val.length = base + r.2.val
      ∧ (∀ t, t < base → wordAt r.1 t = wordAt out t)
      ∧ (∀ x ∈ r.1.val, x.val < pwv)
      ∧ ∀ t, t < r.2.val → wordAt r.1 (base + t) = wordAt f1 t)
  · rintro ⟨d, kk⟩ ⟨hkk, hdl, hdold, hdc, hdnew⟩
    dsimp only at hkk hdl hdold hdc hdnew
    simp only [ring.prepare_one_gold_loop0_loop1.body]
    by_cases hlt : kk < degU
    · rw [if_pos hlt]
      have hklt : kk.val < N := by rw [← hdeg]; scalar_tac
      have hfb : kk.val < f1.val.length := by rw [hfl]; exact hklt
      have hdmax : d.val.length < Std.Usize.max := by rw [hdl]; omega
      step as ⟨x, hx⟩
      have hxv : x.val = wordAt f1 kk.val := by
        rw [hx, ← wordAt_of_lt (v := f1) (t := kk.val) hfb]
      step as ⟨d1, hd1⟩
      step as ⟨kk1, hkk1⟩
      refine ⟨by rw [hkk1]; omega, ?_, ?_, ?_, ?_, by rw [hkk1]; omega⟩
      · rw [hd1, hkk1, List.length_append, hdl]; simp; omega
      · intro t ht
        simp only [wordAt] at hdold ⊢
        rw [hd1, getD_append_lt' _ _ _ (by rw [hdl]; omega)]
        exact hdold t ht
      · intro y hy
        rw [hd1] at hy
        rcases List.mem_append.mp hy with hm | hm
        · exact hdc y hm
        · rw [List.mem_singleton.mp hm, hx]
          exact hfc _ (List.getElem_mem hfb)
      · intro t ht
        rw [hkk1] at ht
        simp only [wordAt] at hdnew ⊢
        rcases Nat.lt_or_ge t kk.val with hlt2 | hge
        · rw [hd1, getD_append_lt' _ _ _ (by rw [hdl]; omega)]
          exact hdnew t hlt2
        · have hteq : base + t = d.val.length := by rw [hdl]; omega
          rw [hteq, hd1, getD_append_eq']
          have : t = kk.val := by omega
          rw [this] at *
          exact hxv
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : kk.val = N := by rw [← hdeg]; scalar_tac
      exact ⟨by rw [hdl, heq], hdold, hdc,
        fun t ht => hdnew t (by rw [heq]; exact ht)⟩
  · exact ⟨hk, hlen, fun t _ => rfl, houtc, hnew⟩


set_option maxHeartbeats 2000000 in
/-- **`prepare_one_gold`'s table.** [`prepare_one_spec`]'s claim at `GP`. -/
theorem prepare_one_gold_spec (a : alloc.vec.Vec ring.Rq) (nU : Std.Usize)
    (hawf : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (han : nU.val ≤ a.val.length)
    (hmax : nU.val * N ≤ Std.Usize.max) :
    ring.prepare_one_gold a nU
      ⦃ z => z.val.length = nU.val * N
             ∧ (∀ u ∈ z.val, u.val < GP)
             ∧ ∀ j, j < nU.val → ∀ t, t < N →
                 resK GP z (j * N + t)
                   = NttMath.difRun (((ntt.GOLD_PSI.val : ℕ) : ZMod GP) ^ 2) 10 1
                       (NttMath.twistR ((ntt.GOLD_PSI.val : ℕ) : ZMod GP)
                         (entryK GP a j)) t ⦄ := by
  have hRN : params.RING_DEGREE = ntt.NTT_LEN := by decide +kernel
  rw [ring.prepare_one_gold, hRN]
  set ps : ZMod GP := ((ntt.GOLD_PSI.val : ℕ) : ZMod GP) with hpsdef
  step with gold_psi_table_cast ntt.GOLD_PSI (by decide +kernel) as ⟨pt, hptC, hptv⟩
  rw [← hpsdef] at hptv
  step as ⟨i, hi⟩
  simp only [alloc.vec.Vec.with_capacity]
  -- the per-entry loop: after `j` entries the table is `j * N` long and every
  -- prepared entry below `j` reads back as its transform
  apply loop.spec_decr_nat (fun r => nU.val - r.2.val)
    (fun r => r.2.val ≤ nU.val ∧ r.1.val.length = r.2.val * N
      ∧ (∀ u ∈ r.1.val, u.val < GP)
      ∧ ∀ u, u < r.2.val → ∀ t, t < N →
          resK GP r.1 (u * N + t)
            = NttMath.difRun (ps ^ 2) 10 1
                (NttMath.twistR ps (entryK GP a u)) t)
  · rintro ⟨d, jj⟩ ⟨hjj, hdl, hdc, hdv⟩
    dsimp only at hjj hdl hdc hdv
    simp only [ring.prepare_one_gold_loop0.body]
    by_cases hlt : jj < nU
    · rw [if_pos hlt]
      have hjlt : jj.val < nU.val := by scalar_tac
      have hja : jj.val < a.val.length := by omega
      simp only [alloc.vec.Vec.with_capacity]
      step with gold_prep_words_spec a ntt.NTT_LEN jj (alloc.vec.Vec.new Std.U64) 0#usize
        ntt_NTT_LEN_val hja (hawf jj.val hjlt) (by simp) (by simp)
        (by intro t ht; simp at ht) as ⟨w, hwl, hwv⟩
      step with gold_twist_cast w pt hwl hptC ps hptv as ⟨tw, htwC, htwv⟩
      step with HachiEquiv.NttTransform.zeros_canon GP GP_pos as ⟨sc, hscC⟩
      step with gold_forward_spec tw sc pt htwC hscC hptC ps hptv
        as ⟨fw, hf1C, hf2C, hfv⟩
      obtain ⟨f1, f2⟩ := fw
      dsimp only at hf1C hf2C hfv
      have hbase : jj.val * N + N ≤ Std.Usize.max := by
        have h1 : (jj.val + 1) * N ≤ nU.val * N := Nat.mul_le_mul_right N (by omega)
        have h2 : (jj.val + 1) * N = jj.val * N + N := by ring
        omega
      step with gold_prep_append_spec ntt.NTT_LEN d (f1, f2) 0#usize (jj.val * N)
        ntt_NTT_LEN_val (by simp) hbase (by dsimp only; exact hf1C.1)
        (by rw [hdl]; simp) (by intro t ht; simp at ht)
        GP (by dsimp only; exact hf1C.2) hdc
        as ⟨o1, ho1l, ho1old, ho1c, ho1new⟩
      step as ⟨jj1, hjj1⟩
      refine ⟨by rw [hjj1]; omega, by rw [hjj1, ho1l]; ring, ho1c, ?_,
        by rw [hjj1]; omega⟩
      intro u hu t ht
      rw [hjj1] at hu
      rcases Nat.lt_or_ge u jj.val with hult | huge
      · -- an earlier entry: untouched by the append
        have hlt3 : u * N + t < jj.val * N := by
          have h1 : (u + 1) * N ≤ jj.val * N := Nat.mul_le_mul_right N (by omega)
          have h2 : (u + 1) * N = u * N + N := by ring
          omega
        have hsame : resK GP o1 (u * N + t) = resK GP d (u * N + t) := by
          simp only [resK]; rw [ho1old (u * N + t) hlt3]
        rw [hsame]
        exact hdv u hult t ht
      · -- this entry: the append wrote it, and it is the transform
        have hueq : u = jj.val := by omega
        rw [hueq]
        simp only [resK]
        rw [ho1new t ht]
        have hf := hfv t ht
        simp only [resK] at hf
        rw [hf]
        refine difRun_congr (ps ^ 2) 10 (by norm_num) 1 (resK GP tw)
          (NttMath.twistR ps (entryK GP a jj.val)) ?_ t ht
        intro e he
        rw [htwv e he]
        simp only [NttMath.twistR, entryK, hwv e he, hpsdef]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = nU.val := by scalar_tac
      exact ⟨by rw [hdl, heq], hdc, fun u hu => hdv u (by rw [heq]; exact hu)⟩
  · exact ⟨by simp, by simp, by intro u hu; simp at hu, by intro u hu; simp at hu⟩


/-- **`ring::prepare_vec_gold`.** One application of [`prepare_one_gold_spec`],
packaged as the [`PrepAtG`] the dot product consumes. -/
theorem prepare_vec_gold_spec (a : alloc.vec.Vec ring.Rq) (nU : Std.Usize)
    (hawf : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (han : nU.val ≤ a.val.length) (hmax : nU.val * N ≤ Std.Usize.max) :
    ring.prepare_vec_gold a nU
      ⦃ z => z.len = nU ∧ PrepAtG z a nU.val ⦄ := by
  rw [ring.prepare_vec_gold]
  step with prepare_one_gold_spec a nU hawf han hmax as ⟨f, hfl, hfc, hfv⟩
  exact ⟨le_of_eq hfl.symm, hfc, hfv⟩


/-! ## Card T51a: the digits read straight out of the compact rows

`dot_prepared_raw_digits_gold` is [`dot_prepared_digits_gold`] with its right
operand never built: term `j` is digit `j % 8` of compact row `j / 8`, filled
into one recycled scratch `Rq` from a buffer of the row's canonical words that
is refreshed once per row (at `j % 8 = 0`), and then handed to the unchanged
[`gold_dot_one_fused`].

The proofs keep the vocabulary of [`gold_dot_spec`] by carrying the digit block
as a **ghost** `B : Vec Rq` -- the vector `gadget_decompose` would have built --
tied to the rows by [`RawDigitsOf`], a pointwise equality of words. The terms
loop then accumulates `termFwd ps a B`, and everything after the loop is
[`gold_dot_spec`]'s proof over `B`. -/

/-- The canonical word `RawRq32::word` reads at index `i`: the raw `u32`
reduced mod `q` below the row's length, `0` past it -- which is exactly
`RawRq32::expand`'s coefficient `i` (its `Fp::new` and its zero padding). -/
def rawWordN (row : alloc.vec.Vec Std.U32) (i : ℕ) : ℕ :=
  if i < row.val.length then (row.val.getD i 0#u32).val % HachiEquiv.NttProduct.q else 0

theorem rawWordN_lt (row : alloc.vec.Vec Std.U32) (i : ℕ) :
    rawWordN row i < HachiEquiv.NttProduct.q := by
  unfold rawWordN
  split
  · exact Nat.mod_lt _ (by norm_num [HachiEquiv.NttProduct.q])
  · norm_num [HachiEquiv.NttProduct.q]

/-- **`RawRq32::word`**: the canonical word, with no precondition on the row --
a raw `u32` may lie in `[q, 2^32)` and a row may be short. -/
theorem word_spec (row : ring.RawRq32) (i : Std.Usize) :
    ring.RawRq32.word row i ⦃ w => w.val = rawWordN row i.val ⦄ := by
  rw [ring.RawRq32.word]
  by_cases hlt : i < alloc.vec.Vec.len row
  · rw [if_pos hlt]
    have hib : i.val < row.val.length := by scalar_tac
    step as ⟨x, hx⟩
    have hcast : lift (UScalar.cast .U64 x) ⦃ y => y.val = x.val ⦄ :=
      UScalar.cast_inBounds_spec .U64 x (by scalar_tac)
    step with hcast as ⟨y, hy⟩
    step as ⟨z, hz⟩
    rw [hz, hy, hx, HachiEquiv.Field.params_Q_val]
    unfold rawWordN
    rw [if_pos hib, List.getD_eq_getElem _ _ hib]
  · rw [if_neg hlt, WP.spec_ok]
    unfold rawWordN
    rw [if_neg (by scalar_tac)]
    rfl

/-- The loop of `load_raw_words`: after `i` steps the buffer holds the row's
first `i` canonical words. -/
theorem load_raw_words_loop_spec (row : ring.RawRq32) (nU : Std.Usize)
    (w : alloc.vec.Vec Std.U64) (iU : Std.Usize)
    (hn : nU.val = N) (hi : iU.val ≤ N) (hwl : w.val.length = N)
    (hwv : ∀ k, k < iU.val → wordAt w k = rawWordN row k) :
    ring.load_raw_words_loop row nU w iU
      ⦃ z => z.val.length = N ∧ ∀ k, k < N → wordAt z k = rawWordN row k ⦄ := by
  rw [ring.load_raw_words_loop]
  apply loop.spec_decr_nat (fun r => nU.val - r.2.val)
    (fun r => r.2.val ≤ N ∧ r.1.val.length = N
      ∧ ∀ k, k < r.2.val → wordAt r.1 k = rawWordN row k)
  · rintro ⟨d, ii⟩ ⟨hii, hdl, hdv⟩
    dsimp only at hii hdl hdv
    simp only [ring.load_raw_words_loop.body]
    by_cases hlt : ii < nU
    · rw [if_pos hlt]
      have hilt : ii.val < N := by rw [← hn]; scalar_tac
      have hdb : ii.val < d.val.length := by rw [hdl]; exact hilt
      step with word_spec row ii as ⟨x, hx⟩
      step as ⟨elem, back, helem, hback⟩
      step as ⟨ii1, hii1⟩
      rw [hback]
      refine ⟨by rw [hii1]; omega, ?_, ?_, by rw [hii1]; omega⟩
      · simpa using hdl
      · intro k hk
        rw [hii1] at hk
        by_cases heq : k = ii.val
        · rw [heq, wordAt_set_eq hdb, hx]
        · rw [wordAt_set_ne heq]; exact hdv k (by omega)
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ii.val = N := by rw [← hn]; scalar_tac
      exact ⟨hdl, fun k hk => hdv k (by rw [heq]; exact hk)⟩
  · exact ⟨hi, hwl, hwv⟩

/-- **`load_raw_words`**: the recycled buffer comes back holding the row's
canonical words, `RawRq32::word` pointwise. -/
theorem load_raw_words_spec (out : alloc.vec.Vec Std.U64) (row : ring.RawRq32)
    (hwl : out.val.length = N) :
    ring.load_raw_words out row
      ⦃ z => z.val.length = N ∧ ∀ k, k < N → wordAt z k = rawWordN row k ⦄ := by
  rw [ring.load_raw_words]
  exact load_raw_words_loop_spec row params.RING_DEGREE out 0#usize
    HachiEquiv.Ring.params_RING_DEGREE_val (by simp) hwl (by intro k hk; simp at hk)

theorem wordN_set_eq {v : alloc.vec.Vec cpoly.field.Fp} {t : Std.Usize} {x : cpoly.field.Fp}
    (ht : t.val < v.val.length) : HachiEquiv.Ring.wordN (v.set t x) t.val = x.val := by
  unfold HachiEquiv.Ring.wordN
  rw [alloc.vec.Vec.set_val_eq,
    List.getD_eq_getElem _ _ (by rw [List.length_set]; exact ht), List.getElem_set]
  simp

theorem wordN_set_ne {v : alloc.vec.Vec cpoly.field.Fp} {t : Std.Usize} {x : cpoly.field.Fp}
    {k : ℕ} (h : k ≠ t.val) : HachiEquiv.Ring.wordN (v.set t x) k = HachiEquiv.Ring.wordN v k := by
  unfold HachiEquiv.Ring.wordN
  rw [alloc.vec.Vec.set_val_eq]
  by_cases hk : k < v.val.length
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_set]; exact hk),
      List.getD_eq_getElem _ _ hk, List.getElem_set_ne (fun hh => h hh.symm)]
  · rw [List.getD_eq_default _ _ (by rw [List.length_set]; omega),
      List.getD_eq_default _ _ (by omega)]

theorem wordN_of_ge {v : ring.Rq} (hv : v.val.length = N) {k : ℕ} (hk : N ≤ k) :
    HachiEquiv.Ring.wordN v k = 0 := by
  unfold HachiEquiv.Ring.wordN
  rw [List.getD_eq_default _ _ (by rw [hv]; exact hk)]
  simp [cpoly.field.Fp.ZERO]

/-- The shift-and-mask is the base-16 digit: `(w >> 4e) & 15 = ⌊w / 16^e⌋ mod 16`. -/
theorem nibble_shift_mask (w e : ℕ) : (w >>> (4 * e)) &&& 15 = (w / 16 ^ e) % 16 := by
  rw [Nat.shiftRight_eq_div_pow, pow_mul,
    show (15 : ℕ) = 2 ^ 4 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  norm_num

/-- The loop of `fill_digit_from_words`: after `i` steps the scratch's first `i`
words are digit `e` of the buffer's. -/
theorem fill_digit_from_words_loop_spec (words : alloc.vec.Vec Std.U64)
    (nU shiftU : Std.Usize) (w : ring.Rq) (iU : Std.Usize) (e : ℕ)
    (hn : nU.val = N) (hsh : shiftU.val = 4 * e) (he : e < 16)
    (hwl : words.val.length = N) (hi : iU.val ≤ N) (hdl : w.val.length = N)
    (hval : ∀ k, k < iU.val →
      HachiEquiv.Ring.wordN w k = (wordAt words k / 16 ^ e) % 16) :
    ring.fill_digit_from_words_loop words nU shiftU w iU
      ⦃ z => z.val.length = N ∧ ∀ k, k < N →
          HachiEquiv.Ring.wordN z k = (wordAt words k / 16 ^ e) % 16 ⦄ := by
  rw [ring.fill_digit_from_words_loop]
  apply loop.spec_decr_nat (fun r => nU.val - r.2.val)
    (fun r => r.2.val ≤ N ∧ r.1.val.length = N
      ∧ ∀ k, k < r.2.val → HachiEquiv.Ring.wordN r.1 k = (wordAt words k / 16 ^ e) % 16)
  · rintro ⟨d, ii⟩ ⟨hii, hdl1, hdv⟩
    dsimp only at hii hdl1 hdv
    simp only [ring.fill_digit_from_words_loop.body]
    by_cases hlt : ii < nU
    · rw [if_pos hlt]
      have hilt : ii.val < N := by rw [← hn]; scalar_tac
      have hwb : ii.val < words.val.length := by rw [hwl]; exact hilt
      have hdb : ii.val < d.val.length := by rw [hdl1]; exact hilt
      step as ⟨x, hx⟩
      have hxv : x.val = wordAt words ii.val := by
        rw [hx, ← wordAt_of_lt (v := words) (t := ii.val) hwb]
      step as ⟨y, hy, _⟩
      step as ⟨dd, hdd⟩
      have hddv : dd.val = (wordAt words ii.val / 16 ^ e) % 16 := by
        rw [hdd, UScalar.val_and, hy, hsh, hxv]
        exact nibble_shift_mask _ _
      have hddlt : dd.val < HachiEquiv.Field.q := by
        rw [hddv]
        have := Nat.mod_lt (wordAt words ii.val / 16 ^ e) (by norm_num : 0 < 16)
        unfold HachiEquiv.Field.q; omega
      step with HachiEquiv.Field.fp_new_spec dd as ⟨f, hRf, hf⟩
      have hfv : f.val = dd.val := by
        have h1 := HachiEquiv.NttProduct.natCast_inj_of_lt
          (n := HachiEquiv.NttProduct.q) (x := f.val) (y := dd.val) hRf hf
        rwa [Nat.mod_eq_of_lt hddlt] at h1
      step as ⟨elem, back, helem, hback⟩
      step as ⟨ii1, hii1⟩
      rw [hback]
      refine ⟨by rw [hii1]; omega, ?_, ?_, by rw [hii1]; omega⟩
      · simpa using hdl1
      · intro k hk
        rw [hii1] at hk
        by_cases heq : k = ii.val
        · rw [heq, wordN_set_eq hdb, hfv, hddv]
        · rw [wordN_set_ne heq]; exact hdv k (by omega)
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ii.val = N := by rw [← hn]; scalar_tac
      exact ⟨hdl1, fun k hk => hdv k (by rw [heq]; exact hk)⟩
  · exact ⟨hi, hdl, hval⟩

/-- A digit word is a well-formed ring element: `N` entries, each below `16 < q`. -/
theorem wf_of_digit_words {z : ring.Rq} (hl : z.val.length = N) (f : ℕ → ℕ)
    (hv : ∀ k, k < N → HachiEquiv.Ring.wordN z k = f k % 16) : HachiEquiv.Ring.Wf z := by
  refine ⟨hl, fun u hu => ?_⟩
  obtain ⟨k, hk, hku⟩ := List.getElem_of_mem hu
  have hkN : k < N := by rw [← hl]; exact hk
  have h := hv k hkN
  unfold HachiEquiv.Ring.wordN at h
  rw [List.getD_eq_getElem _ _ hk, hku] at h
  unfold HachiEquiv.Field.Red
  rw [h]
  have := Nat.mod_lt (f k) (by norm_num : 0 < 16)
  unfold HachiEquiv.Field.q; omega

/-- **`fill_digit_from_words`**: with a length-`N` scratch and `e < 16` (the
shift `4e` stays below `64`), the scratch comes back well formed, holding digit
`e` of every buffered word. The scratch's previous contents are irrelevant --
every entry is overwritten. -/
theorem fill_digit_from_words_spec (out : ring.Rq) (words : alloc.vec.Vec Std.U64)
    (e : Std.Usize) (hout : out.val.length = N) (hwl : words.val.length = N)
    (he : e.val < 16) :
    ring.fill_digit_from_words out words e
      ⦃ z => HachiEquiv.Ring.Wf z ∧ ∀ k, k < N →
          HachiEquiv.Ring.wordN z k = (wordAt words k / 16 ^ e.val) % 16 ⦄ := by
  rw [ring.fill_digit_from_words]
  step as ⟨sh, hsh⟩
  apply spec_mono (fill_digit_from_words_loop_spec words params.RING_DEGREE sh out
    0#usize e.val HachiEquiv.Ring.params_RING_DEGREE_val hsh he hwl (by simp) hout
    (by intro k hk; simp at hk))
  rintro z ⟨hzl, hzv⟩
  exact ⟨wf_of_digit_words hzl _ hzv, hzv⟩

/-- `B` is the digit block the compact rows `raw` denote, on its first `n`
entries: entry `u` is well formed and its word at coefficient `k` is digit
`u % 8` of row `u / 8`'s canonical word -- the `finProdFinEquiv` layout
`gadget_decompose` writes (`8 · r + e`). -/
def RawDigitsOf (raw : alloc.vec.Vec ring.RawRq32) (B : alloc.vec.Vec ring.Rq) (n : ℕ) : Prop :=
  ∀ u, u < n → HachiEquiv.Ring.Wf (B.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
    ∧ ∀ k, k < N → HachiEquiv.Ring.wordN (B.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k
        = (rawWordN (raw.val.getD (u / 8) (alloc.vec.Vec.new Std.U32)) k / 16 ^ (u % 8)) % 16

/-- Such a block is digit-bounded: every word is below the base. -/
theorem RawDigitsOf.digitWf {raw : alloc.vec.Vec ring.RawRq32} {B : alloc.vec.Vec ring.Rq}
    {n : ℕ} (hB : RawDigitsOf raw B n) (u : ℕ) (hu : u < n) :
    DigitWf (B.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) := by
  intro t
  obtain ⟨hW, hv⟩ := hB u hu
  by_cases ht : t < N
  · rw [hv t ht]; exact Nat.mod_lt _ (by norm_num)
  · rw [wordN_of_ge hW.1 (by omega)]; norm_num

/-- The optional refresh at the top of the terms loop: at `j % 8 = 0` the
buffer is reloaded from row `j / 8`; otherwise it already holds that row, which
the previous turn loaded (`(j - 1) / 8 = j / 8`). -/
theorem raw_refresh_spec (raw : alloc.vec.Vec ring.RawRq32) (words : alloc.vec.Vec Std.U64)
    (jU digitsU e : Std.Usize) (hdig : digitsU.val = 8) (he : e.val = jU.val % 8)
    (hrow : jU.val / 8 < raw.val.length) (hwl : words.val.length = N)
    (hwv : 0 < jU.val → ∀ k, k < N → wordAt words k
        = rawWordN (raw.val.getD ((jU.val - 1) / 8) (alloc.vec.Vec.new Std.U32)) k) :
    (if e = 0#usize then do
        let i ← jU / digitsU
        let rr ← alloc.vec.Vec.index_usize raw i
        ring.load_raw_words words rr
      else ok words)
      ⦃ w1 => w1.val.length = N ∧ ∀ k, k < N → wordAt w1 k
          = rawWordN (raw.val.getD (jU.val / 8) (alloc.vec.Vec.new Std.U32)) k ⦄ := by
  by_cases he0 : e = 0#usize
  · rw [if_pos he0]
    step as ⟨i, hi⟩
    have hiv : i.val = jU.val / 8 := by rw [hi, hdig]
    have hib : i.val < raw.val.length := by rw [hiv]; exact hrow
    step as ⟨rr, hrr⟩
    step with load_raw_words_spec words rr hwl as ⟨w1, hw1l, hw1v⟩
    refine ⟨hw1l, fun k hk => ?_⟩
    rw [hw1v k hk, hrr, ← hiv, List.getD_eq_getElem _ _ hib]
  · rw [if_neg he0, WP.spec_ok]
    have hev : e.val ≠ 0 := fun h => he0 (UScalar.eq_of_val_eq (by simp [h]))
    have hpos : 0 < jU.val := by omega
    have hdiv : (jU.val - 1) / 8 = jU.val / 8 := by omega
    refine ⟨hwl, fun k hk => ?_⟩
    rw [hwv hpos k hk, hdiv]

/-- **The raw terms loop** -- [`gold_terms_spec`] with the right operand read
out of the compact rows. The ghost `B` is the digit block they denote
([`RawDigitsOf`]); the invariant gains the buffer (length `N`, and from the
first turn on holding row `(j - 1) / 8`) and the scratch's length, and
[`gold_dot_one_fused_spec`] is reused unchanged on the freshly filled scratch. -/
theorem gold_raw_terms_spec (prep : ring.PreparedVecG)
    (a B : alloc.vec.Vec ring.Rq) (raw : alloc.vec.Vec ring.RawRq32)
    (endU nU digitsU : Std.Usize) (pt : alloc.vec.Vec Std.U64)
    (acc scratch cur words : alloc.vec.Vec Std.U64) (dig : ring.Rq) (jU : Std.Usize)
    (ps : ZMod GP)
    (hn : nU.val = N) (hdig : digitsU.val = 8) (hord : ps ^ N = -1)
    (hptC : Canon GP pt) (hptv : ∀ e, e < N → resK GP pt e = ps ^ e)
    (hpl : endU.val * N ≤ prep.fwd.val.length)
    (hpv : ∀ j, j < endU.val → ∀ t, t < N →
        resK GP prep.fwd (j * N + t)
          = NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK GP a j)) t)
    (hB : RawDigitsOf raw B endU.val)
    (hraw : endU.val ≤ 8 * raw.val.length)
    (hje : jU.val ≤ endU.val)
    (haccC : Canon GP acc) (hscC : Canon GP scratch) (hcurC : Canon GP cur)
    (hwl : words.val.length = N)
    (hwv : 0 < jU.val → ∀ k, k < N → wordAt words k
        = rawWordN (raw.val.getD ((jU.val - 1) / 8) (alloc.vec.Vec.new Std.U32)) k)
    (hdl : dig.val.length = N)
    (hval : ∀ t, t < N → resK GP acc t
              = ∑ u ∈ Finset.Ico 0 jU.val, termFwd ps a B u t) :
    ring.dot_prepared_raw_digits_gold_loop0 prep raw endU nU digitsU pt acc scratch cur
      words dig jU
      ⦃ z => Canon GP z.1 ∧ Canon GP z.2
             ∧ ∀ t, t < N → resK GP z.1 t
                 = ∑ u ∈ Finset.Ico 0 endU.val, termFwd ps a B u t ⦄ := by
  rw [ring.dot_prepared_raw_digits_gold_loop0]
  apply loop.spec_decr_nat (fun r => endU.val - r.2.2.2.2.2.val)
    (fun r => r.2.2.2.2.2.val ≤ endU.val
      ∧ Canon GP r.1 ∧ Canon GP r.2.1 ∧ Canon GP r.2.2.1
      ∧ r.2.2.2.1.val.length = N
      ∧ (0 < r.2.2.2.2.2.val → ∀ k, k < N → wordAt r.2.2.2.1 k
          = rawWordN (raw.val.getD ((r.2.2.2.2.2.val - 1) / 8)
              (alloc.vec.Vec.new Std.U32)) k)
      ∧ r.2.2.2.2.1.val.length = N
      ∧ ∀ t, t < N → resK GP r.1 t
              = ∑ u ∈ Finset.Ico 0 r.2.2.2.2.2.val, termFwd ps a B u t)
  · rintro ⟨d, sc, cu, wd, dg, jj⟩ ⟨hjje, hcd, hcsc, hcuC, hwdl, hwdv, hdgl, hw⟩
    dsimp only at hjje hcd hcsc hcuC hwdl hwdv hdgl hw
    simp only [ring.dot_prepared_raw_digits_gold_loop0.body]
    by_cases hlt : jj < endU
    · rw [if_pos hlt]
      have hjjlt : jj.val < endU.val := by scalar_tac
      have hrow : jj.val / 8 < raw.val.length := by omega
      step as ⟨e, he⟩
      have hev : e.val = jj.val % 8 := by rw [he, hdig]
      step with raw_refresh_spec raw wd jj digitsU e hdig hev hrow hwdl hwdv
        as ⟨w1, hw1l, hw1v⟩
      step with fill_digit_from_words_spec dg w1 e hdgl hw1l (by omega)
        as ⟨dig1, hdig1W, hdig1v⟩
      step as ⟨off, hoff⟩
      have hoffv : off.val = jj.val * N := by rw [hoff, hn]
      have hslb : off.val + N ≤ prep.fwd.val.length := by
        rw [hoffv]
        have h1 : (jj.val + 1) * N ≤ endU.val * N := Nat.mul_le_mul_right N (by omega)
        have h2 : (jj.val + 1) * N = jj.val * N + N := by ring
        omega
      have hFA : ∀ t, t < N → ((wordAt prep.fwd (off.val + t) : ℕ) : ZMod GP)
          = NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK GP a jj.val)) t := by
        intro t ht
        rw [hoffv]
        have := hpv jj.val hjjlt t ht
        simpa only [resK] using this
      step with gold_dot_one_fused_spec dig1 cu sc d pt prep.fwd off ps
        (fun t => NttMath.difRun (ps ^ 2) 10 1
          (NttMath.twistR ps (entryK GP a jj.val)) t)
        hdig1W hcuC hcsc hcd hptC hptv hslb hFA
        as ⟨acc1, cur1, sc1, hac1C, hcu1C, hsc1C, hac1v⟩
      -- the scratch IS the ghost block's entry: same words below `N`, both
      -- zero past it
      have hFB : NttMath.twistR ps
            (fun u => ((HachiEquiv.Ring.wordN dig1 u : ℕ) : ZMod GP))
          = NttMath.twistR ps (entryK GP B jj.val) := by
        obtain ⟨hBW, hBv⟩ := hB jj.val hjjlt
        have hwords : ∀ u, HachiEquiv.Ring.wordN dig1 u
            = HachiEquiv.Ring.wordN (B.val.getD jj.val (alloc.vec.Vec.new cpoly.field.Fp)) u := by
          intro u
          by_cases hu : u < N
          · rw [hdig1v u hu, hw1v u hu, hBv u hu, hev]
          · rw [wordN_of_ge hdig1W.1 (by omega), wordN_of_ge hBW.1 (by omega)]
        unfold entryK
        simp only [hwords]
      step as ⟨jj1, hjj1⟩
      refine ⟨by rw [hjj1]; omega, hac1C, hsc1C, hcu1C, hw1l, ?_, hdig1W.1, ?_,
        by rw [hjj1]; omega⟩
      · intro _ k hk
        rw [hjj1, Nat.add_sub_cancel]
        exact hw1v k hk
      · intro t ht
        rw [hjj1, Finset.sum_Ico_succ_top (by omega), ← hw t ht]
        rw [hac1v t ht, hFB]
        unfold termFwd
        rw [← HachiEquiv.NttProduct.prod_difRun ps hord (entryK GP a jj.val)
          (entryK GP B jj.val)
          (NttMath.difRun (ps ^ 2) 10 1 (NttMath.twistR ps (entryK GP a jj.val)))
          (NttMath.difRun (ps ^ 2) 10 1 (NttMath.twistR ps (entryK GP B jj.val)))
          (fun t' => NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK GP a jj.val)) t'
            * NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK GP B jj.val)) t')
          (fun t' _ => rfl) (fun t' _ => rfl) (fun t' _ => rfl) t ht]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = endU.val := by scalar_tac
      refine ⟨hcd, hcsc, ?_⟩
      intro t ht
      rw [hw t ht, heq]
  · exact ⟨hje, haccC, hscC, hcurC, hwl, hwv, hdl, hval⟩

/-- The pack loop of the raw dot is the plain dot's, byte for byte. -/
theorem raw_out_loop_eq : ring.dot_prepared_raw_digits_gold_loop1
    = ring.dot_prepared_digits_gold_loop1 := rfl

set_option maxHeartbeats 4000000 in
/-- **`dot_prepared_raw_digits_gold` computes the dot product** with the digit
block the compact rows denote. [`gold_dot_spec`]'s conclusion word for word,
over the ghost `B`; its operand hypotheses (`Wf`, `DigitWf`) are [`RawDigitsOf`]'s,
and its length hypothesis on `b` becomes `nU ≤ 8 · raw.len`, which is what the
row index `j / 8` needs. -/
theorem gold_raw_dot_spec (prep : ring.PreparedVecG) (a B : alloc.vec.Vec ring.Rq)
    (raw : alloc.vec.Vec ring.RawRq32) (nU : Std.Usize)
    (haw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hB : RawDigitsOf raw B nU.val) (hraw : nU.val ≤ 8 * raw.val.length)
    (hwidth : nU.val ≤ 8192)
    (hp : PrepAtG prep a nU.val) :
    ring.dot_prepared_raw_digits_gold prep raw nU
      ⦃ z => HachiEquiv.Ring.Wf z ∧ ∀ k, k < N → HachiEquiv.Ring.coeffK z k
              = ∑ u ∈ Finset.range nU.val, HachiEquiv.Ring.negConv
                  (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                  (B.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k ⦄ := by
  obtain ⟨hpl, -, hpv⟩ := hp
  have hbw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (B.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) := fun u hu => (hB u hu).1
  have hbd : ∀ u, u < nU.val → DigitWf
      (B.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) := hB.digitWf
  set ps : ZMod GP := ((ntt.GOLD_PSI.val : ℕ) : ZMod GP) with hpsdef
  set psii : ZMod GP := ((ntt.GOLD_PSIINV.val : ℕ) : ZMod GP) with hpsiidef
  have hord : ps ^ N = -1 := gpsi_ord
  have hpinv : ps * psii = 1 := gpsi_inv
  have hRN : params.RING_DEGREE = ntt.NTT_LEN := by decide +kernel
  rw [ring.dot_prepared_raw_digits_gold, hRN, raw_out_loop_eq]
  step with gold_psi_table_cast ntt.GOLD_PSI (by decide +kernel) as ⟨pt, hptC, hptv⟩
  step with gold_psi_table_cast ntt.GOLD_PSIINV (by decide +kernel) as ⟨it, hitC, hitv⟩
  step with zeros_canon_zero GP GP_pos as ⟨acc0, hacc0C, hacc0v⟩
  step with HachiEquiv.Ring.zero_spec as ⟨dg0, hdg0W, _⟩
  step with gold_raw_terms_spec prep a B raw nU ntt.NTT_LEN params.GADGET_DIGITS pt
    acc0 acc0 acc0 acc0 dg0 0#usize ps ntt_NTT_LEN_val (by simp [params.GADGET_DIGITS])
    hord hptC hptv hpl hpv hB hraw (by simp) hacc0C hacc0C hacc0C hacc0C.1
    (by intro h; simp at h) hdg0W.1
    (by intro t ht; rw [hacc0v t ht]; simp)
    as ⟨acc1, scratch, hac1C, hac2C, hac1v⟩
  -- from here on, `gold_dot_spec`'s proof with `b := B`
  have hcn : lift (UScalar.cast .U64 nU) ⦃ y => y.val = nU.val ⦄ :=
    UScalar.cast_inBounds_spec .U64 nU (by scalar_tac)
  step with hcn as ⟨nw, hnw⟩
  step with gold_mul_spec ntt.GOLD_DOFF nw as ⟨scaled, hscv, hsclt⟩
  have hPR : ∀ t, t < N → resK GP acc1 t
      = NttMath.difRun (ps ^ 2) 10 1
          (fun t' => ∑ u ∈ Finset.Ico 0 nU.val,
            NttMath.cyclicConv N (NttMath.twistR ps (entryK GP a u))
              (NttMath.twistR ps (entryK GP B u)) t') t := by
    intro t ht
    rw [hac1v t ht, NttMath.difRun_sum (ps ^ 2) 10 1 (Finset.Ico 0 nU.val)
      (fun u => NttMath.cyclicConv N (NttMath.twistR ps (entryK GP a u))
        (NttMath.twistR ps (entryK GP B u)))]
    simp only [termFwd, hpsdef]
  step with gold_inverse_spec acc1 scratch it hac1C hac2C hitC psii hitv
    as ⟨v, v5, hiv1, hiv2, hivv⟩
  have hIV := HachiEquiv.NttProduct.inv_value ps psii hpinv
    (fun t' => ∑ u ∈ Finset.Ico 0 nU.val,
      NttMath.cyclicConv N (NttMath.twistR ps (entryK GP a u))
        (NttMath.twistR ps (entryK GP B u)) t')
    (resK GP acc1) (resK GP v) hPR hivv
  step with gold_untwist_cast v it scaled hiv1 hitC hsclt psii hitv
    as ⟨words, hwC, hwv⟩
  have hres : ∀ t, t < N → resK GP words t
      = (∑ u ∈ Finset.Ico 0 nU.val,
          NttMath.negConvR N (entryK GP a u) (entryK GP B u) t)
        + ((scaled.val : ℕ) : ZMod GP) := by
    intro t ht
    rw [hwv t ht, hIV t ht,
      untwist_value_sum ps psii ((ntt.GOLD_NINV.val : ℕ) : ZMod GP) hord hpinv
        gninv_inv (Finset.Ico 0 nU.val) (fun u => entryK GP a u)
        (fun u => entryK GP B u) t ht]
  have hwordv : ∀ k, k < N → wordAt words k = offConvSumD a B 0 nU.val k := by
    intro k hk
    have hlt : offConvSumD a B 0 nU.val k < GP :=
      offConvSumD_lt_GP a B 0 nU.val k haw hbd (by omega)
    have hcast : ((wordAt words k : ℕ) : ZMod GP)
        = ((offConvSumD a B 0 nU.val k : ℕ) : ZMod GP) := by
      have hle := negQD_sum_le a B 0 nU.val k haw hbd
      have hle' : (∑ u ∈ Finset.Ico 0 nU.val,
            HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                 (B.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
          ≤ (∑ u ∈ Finset.Ico 0 nU.val,
              HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                   (B.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
            + (nU.val - 0) * BOUND_D := le_trans hle (Nat.le_add_left _ _)
      have h1 := hres k hk
      rw [resK] at h1
      rw [h1]
      unfold offConvSumD
      rw [Nat.cast_sub hle', Nat.cast_add]
      have hterm : ∀ u, NttMath.negConvR N (entryK GP a u) (entryK GP B u) k
          = ((HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                (B.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod GP)
            - ((HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                (B.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod GP) := by
        intro u
        rw [NttMath.negConvR, ordConv_entryK_pos GP a B u k hk,
          ordConv_entryK_neg GP a B u k hk]
      rw [Finset.sum_congr rfl (fun u _ => hterm u), Finset.sum_sub_distrib]
      push_cast
      rw [hscv, hnw, gdoff_val, ZMod.natCast_mod, Nat.sub_zero]
      push_cast
      ring
    have h2 := HachiEquiv.NttProduct.natCast_inj_of_lt (wordAt_lt hwC GP_pos k) hcast
    rwa [Nat.mod_eq_of_lt hlt] at h2
  have hfin := gold_out_loop_spec ntt.NTT_LEN params.Q words
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize (offConvSumD a B 0 nU.val)
    ntt_NTT_LEN_val HachiEquiv.Field.params_Q_val hwordv hwC.1
    (by simp) (by simp) (by simp) (by simp)
  rw [alloc.vec.Vec.with_capacity]
  step with hfin as ⟨z, hzw, hzv⟩
  refine ⟨hzw, fun k hk => ?_⟩
  have hqq : HachiEquiv.NttProduct.q = HachiEquiv.Field.q := rfl
  rw [HachiEquiv.Ring.coeffK_eq_cast_wordN, hzv k hk, hqq, ZMod.natCast_mod,
    offConvSumD_cast_q a B 0 nU.val k hk haw hbw hbd, Finset.range_eq_Ico]

end HachiEquiv.GoldDot
