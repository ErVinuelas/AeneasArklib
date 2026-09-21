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

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

set_option maxRecDepth 8192

namespace HachiEquiv.GoldDot

open HachiEquiv.NttStage HachiEquiv.RingFused HachiEquiv.GoldArith
open HachiEquiv.GoldTransform

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

/-- The word gather is the *same loop* as the two-prime path's: it reads
`b[j]`'s coefficients and pushes their words, and nothing in it mentions a
prime. `ring.rs` writes both the same way deliberately, so this is `rfl` and
`RingFused.prep_words_b_spec` is reused rather than re-proved. -/
theorem gold_words_eq (b : alloc.vec.Vec ring.Rq) (n j : Std.Usize)
    (w : alloc.vec.Vec Std.U64) (u : Std.Usize) :
    ring.dot_prepared_digits_gold_loop0_loop0 b n j w u
      = ring.dot_prep_chunk_mod_p_loop0_loop0 b n j w u := rfl

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
    (acc scratch : alloc.vec.Vec Std.U64) (jU : Std.Usize) (ps : ZMod GP)
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
    (haccC : Canon GP acc) (hscC : Canon GP scratch)
    (hval : ∀ t, t < N → resK GP acc t
              = ∑ u ∈ Finset.Ico startU.val jU.val, termFwd ps a b u t) :
    ring.dot_prepared_digits_gold_loop0 prep b endU nU pt acc scratch jU
      ⦃ z => Canon GP z.1 ∧ Canon GP z.2
             ∧ ∀ t, t < N → resK GP z.1 t
                 = ∑ u ∈ Finset.Ico startU.val endU.val, termFwd ps a b u t ⦄ := by
  rw [ring.dot_prepared_digits_gold_loop0]
  apply loop.spec_decr_nat (fun r => endU.val - r.2.2.val)
    (fun r => startU.val ≤ r.2.2.val ∧ r.2.2.val ≤ endU.val
      ∧ Canon GP r.1 ∧ Canon GP r.2.1
      ∧ ∀ t, t < N → resK GP r.1 t
              = ∑ u ∈ Finset.Ico startU.val r.2.2.val, termFwd ps a b u t)
  · rintro ⟨d, sc, jj⟩ ⟨hjjs, hjje, hcd, hcsc, hw⟩
    dsimp only at hjjs hjje hcd hcsc hw
    simp only [ring.dot_prepared_digits_gold_loop0.body]
    by_cases hlt : jj < endU
    · rw [if_pos hlt]
      have hjjlt : jj.val < endU.val := by scalar_tac
      have hjb : jj.val < b.val.length := by omega
      simp only [alloc.vec.Vec.with_capacity]
      rw [gold_words_eq]
      step with prep_words_b_spec b nU jj (alloc.vec.Vec.new Std.U64) 0#usize hn hjb
        (hbwf jj.val hjjlt) (by simp) (by simp) (by intro u hu; simp at hu)
        (by intro t ht; simp at ht) as ⟨bw, hbwl, hbwr, hbwv⟩
      step with gold_twist_cast bw pt hbwl hptC ps hptv as ⟨tb, htbC, htbv⟩
      step with gold_forward_spec tb sc pt htbC hcsc hptC ps hptv
        as ⟨fw, hfw1, hfw2, hfwv⟩
      obtain ⟨v, v1⟩ := fw
      dsimp only at hfw1 hfw2 hfwv
      step as ⟨off, hoff⟩
      have hoffv : off.val = jj.val * N := by rw [hoff, hn]
      have hslb : off.val + N ≤ prep.fwd.val.length := by
        rw [hoffv]
        have h1 : (jj.val + 1) * N ≤ endU.val * N := Nat.mul_le_mul_right N (by omega)
        have h2 : (jj.val + 1) * N = jj.val * N + N := by ring
        omega
      step with slice_out_top_spec prep.fwd off nU hn hslb as ⟨af, hafl, hafv⟩
      -- `prep.fwd` is `endU * N` long, so `Canon` does not apply to it; the bound
      -- comes from `hpc` directly, with the out-of-range default handled
      have hafC : Canon GP af := ⟨hafl, fun x hx => by
        obtain ⟨t, ht, hteq⟩ := List.getElem_of_mem hx
        have hb : wordAt af t = wordAt prep.fwd (off.val + t) :=
          hafv t (by rw [← hafl]; exact ht)
        rw [wordAt_of_lt ht] at hb
        rw [← hteq, hb]
        unfold wordAt
        by_cases hin : off.val + t < prep.fwd.val.length
        · rw [List.getD_eq_getElem _ _ hin]
          exact hpc _ (List.getElem_mem hin)
        · rw [List.getD_eq_default _ _ (by omega)]
          simpa using GP_pos⟩
      -- the table's entry IS this term's left transform
      have hFA : ∀ t, t < N → resK GP af t
          = NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK GP a jj.val)) t := by
        intro t ht
        simp only [resK]
        rw [hafv t ht, hoffv]
        have := hpv jj.val hjjlt t ht
        simp only [resK] at this
        exact this
      have hFB : ∀ t, t < N → resK GP v t
          = NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK GP b jj.val)) t := by
        intro t ht
        rw [hfwv t ht]
        refine difRun_congr (ps ^ 2) 10 (by norm_num) 1 (resK GP tb)
          (NttMath.twistR ps (entryK GP b jj.val)) ?_ t ht
        intro e he
        rw [htbv e he]
        simp only [NttMath.twistR, entryK, hbwv e he]
      step with gold_mac_into_spec d af v nU 0#usize (resK GP d)
        hn (by simp) hcd hafC hfw1 (by intro t ht; simp) as ⟨acc1, hac1C, hac1v⟩
      step as ⟨jj1, hjj1⟩
      refine ⟨by rw [hjj1]; omega, by rw [hjj1]; omega, hac1C, hfw2, ?_,
        by rw [hjj1]; omega⟩
      intro t ht
      rw [hjj1, Finset.sum_Ico_succ_top (by omega), ← hw t ht]
      rw [hac1v t ht, hFA t ht, hFB t ht]
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
  · exact ⟨hjs, hje, haccC, hscC, hval⟩

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
  step with gold_terms_spec prep a b 0#usize nU ntt.NTT_LEN pt acc0 acc0
    0#usize ps ntt_NTT_LEN_val hord hptC hptv hpl hpv hpc hbw hbn
    (by simp) (by simp) hacc0C hacc0C (by intro t ht; rw [hacc0v t ht]; simp)
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


end HachiEquiv.GoldDot
