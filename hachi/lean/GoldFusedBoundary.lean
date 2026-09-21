/-
Card T37: the **boundary passes of the Goldilocks transform, fused** with the
operations on either side of them.

`gold_dot_one_fused` does one right-hand term of the prepared dot in five
passes where there were seven: the twist is folded into the first radix-4
pair stage (`ring::gold_dif_stage2_twist`, which also absorbs `to_u64`), the
multiply-accumulate into the last (`ntt::gold_dif_stage2_mac`), and the
three middle stages are `gold_forward`'s loop with its first and last
iterations peeled (`gold_dot_one_fused_loop`).

The proof is **three direct specs in the shape of `GoldFusedStage`**, not a
`Result` equality against the three functions the fusion replaced. That is a
deliberate choice against the note that specified this debt: a `Result`
equality between two loop programs with different loop structure has no
tactic support here, while the fused stage already has a proof whose only
inputs are "four reads, four writes at four distinct positions, a frame" --
exactly the shape both boundary passes have. So:

* the twist stage is [`gold_dif_stage2_loop0_loop0_spec`] with its four
  `src` reads replaced by `a.0[i].to_u64() · pt[i]`, so its conclusion is
  `difWord ∘ difWord` of [`twSrc`], the twisted words;
* the MAC stage is the same lemma with its four writes replaced by
  read-modify-writes into `acc`, so its conclusion is [`macAt`] of the
  composite stage -- the reads of `acc` between the writes are what the
  distinctness facts already in that proof were for;
* the middle loop is [`gold_forward_loop_spec`] with the exit condition moved
  from `len > 1` to `len > 4`, so it delivers `difRun … 2 (2^8)` rather than
  `difRun … 0`.

[`gold_dot_one_fused_spec`] then composes the three in the ring, exactly as
`gold_terms_spec` used to compose `load_twisted_into_spec`,
`gold_forward_spec` and `gold_mac_off_spec`, and has the conclusion those
three had in sequence. `gold_terms_spec` takes one step where it took three;
nothing above it moves.
-/
import GoldTransform
import RingFused

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.GoldFusedBoundary

open HachiEquiv.NttStage HachiEquiv.GoldArith HachiEquiv.GoldStage
open HachiEquiv.GoldFusedStage HachiEquiv.GoldTransform

theorem GP_pos : 0 < GP := by norm_num

/-! ## Part A: the twist stage

The words the fused first stage reads: the coefficient, as a word, times the
table entry at the same index, reduced. [`twSrc`] plays the role `wordAt src`
plays in `GoldFusedStage`. -/

/-- The ψ-twisted word of `a` at `u`: what `gold_mul(a.0[u].to_u64(), pt[u])` is. -/
def twSrc (a : ring.Rq) (pt : alloc.vec.Vec Std.U64) (u : ℕ) : ℕ :=
  (HachiEquiv.Ring.wordN a u * wordAt pt u) % GP

theorem twSrc_lt (a : ring.Rq) (pt : alloc.vec.Vec Std.U64) (u : ℕ) : twSrc a pt u < GP :=
  Nat.mod_lt _ GP_pos

/-- In the ring, the twisted word is the twist: `a_u · ψ^u`. -/
theorem twSrc_cast (a : ring.Rq) (pt : alloc.vec.Vec Std.U64) (ps : ZMod GP)
    (hptv : ∀ e, e < N → resK GP pt e = ps ^ e) (u : ℕ) (hu : u < N) :
    ((twSrc a pt u : ℕ) : ZMod GP)
      = NttMath.twistR ps (fun v => ((HachiEquiv.Ring.wordN a v : ℕ) : ZMod GP)) u := by
  simp only [twSrc, NttMath.twistR]
  rw [ZMod.natCast_mod, Nat.cast_mul]
  have := hptv u hu
  simp only [resK] at this
  rw [this]

/-- One block's worth of fused groups, reading the twisted operand. The loop
state is the 3-tuple `(a, dst, j)`: the borrowed `&Rq` rides along, the shape
`add_loop`, `sub_loop` and `load_twisted_into_loop` already have. -/
theorem twist_loop0_loop0_spec (a : ring.Rq) (tw pt dst : alloc.vec.Vec Std.U64)
    (half quarter step1 step2 start j : Std.Usize)
    (hwf : HachiEquiv.Ring.Wf a) (hpt : Canon GP pt) (hdst : Canon GP dst) (htw : Canon GP tw)
    (hhq : half.val = 2 * quarter.val) (hqpos : 0 < quarter.val)
    (hblk : start.val + 2 * half.val ≤ N) (hj : j.val ≤ quarter.val)
    (hs2 : step2.val = 2 * step1.val) (hstep : 0 < step1.val)
    (hebd : half.val * step1.val ≤ N)
    (hw0 : ∀ u, u < j.val →
      wordAt dst (start.val + u) = f0 (twSrc a pt) half.val quarter.val start.val u)
    (hw1 : ∀ u, u < j.val →
      wordAt dst (start.val + u + quarter.val)
        = f1 (twSrc a pt) (wordAt tw) half.val quarter.val step2.val start.val u)
    (hw2 : ∀ u, u < j.val →
      wordAt dst (start.val + half.val + u)
        = f2 (twSrc a pt) (wordAt tw) half.val quarter.val step1.val start.val u)
    (hw3 : ∀ u, u < j.val →
      wordAt dst (start.val + half.val + quarter.val + u)
        = f3 (twSrc a pt) (wordAt tw) half.val quarter.val step1.val step2.val start.val u) :
    ring.gold_dif_stage2_twist_loop0_loop0 a tw pt half quarter step1 step2 dst start j
      ⦃ z => z.1 = a ∧ Canon GP z.2
             ∧ (∀ u, u < quarter.val →
                 wordAt z.2 (start.val + u) = f0 (twSrc a pt) half.val quarter.val start.val u)
             ∧ (∀ u, u < quarter.val →
                 wordAt z.2 (start.val + u + quarter.val)
                   = f1 (twSrc a pt) (wordAt tw) half.val quarter.val step2.val start.val u)
             ∧ (∀ u, u < quarter.val →
                 wordAt z.2 (start.val + half.val + u)
                   = f2 (twSrc a pt) (wordAt tw) half.val quarter.val step1.val start.val u)
             ∧ (∀ u, u < quarter.val →
                 wordAt z.2 (start.val + half.val + quarter.val + u)
                   = f3 (twSrc a pt) (wordAt tw) half.val quarter.val step1.val step2.val
                       start.val u)
             ∧ (∀ k, (k < start.val ∨ start.val + 2 * half.val ≤ k) →
                 wordAt z.2 k = wordAt dst k) ⦄ := by
  rw [ring.gold_dif_stage2_twist_loop0_loop0]
  apply loop.spec_decr_nat (fun s => quarter.val - s.2.2.val)
    (fun s => s.2.2.val ≤ quarter.val ∧ s.1 = a ∧ Canon GP s.2.1
      ∧ (∀ u, u < s.2.2.val →
          wordAt s.2.1 (start.val + u) = f0 (twSrc a pt) half.val quarter.val start.val u)
      ∧ (∀ u, u < s.2.2.val →
          wordAt s.2.1 (start.val + u + quarter.val)
            = f1 (twSrc a pt) (wordAt tw) half.val quarter.val step2.val start.val u)
      ∧ (∀ u, u < s.2.2.val →
          wordAt s.2.1 (start.val + half.val + u)
            = f2 (twSrc a pt) (wordAt tw) half.val quarter.val step1.val start.val u)
      ∧ (∀ u, u < s.2.2.val →
          wordAt s.2.1 (start.val + half.val + quarter.val + u)
            = f3 (twSrc a pt) (wordAt tw) half.val quarter.val step1.val step2.val start.val u)
      ∧ (∀ k, (k < start.val ∨ start.val + 2 * half.val ≤ k) →
          wordAt s.2.1 k = wordAt dst k))
  · rintro ⟨aa, d, jj⟩ ⟨hjj, haa, hcd, hv0, hv1, hv2, hv3, hfr⟩
    dsimp only at hjj haa hcd hv0 hv1 hv2 hv3 hfr
    subst haa
    simp only [ring.gold_dif_stage2_twist_loop0_loop0.body]
    by_cases hlt : jj < quarter
    · rw [if_pos hlt]
      have hjlt : jj.val < quarter.val := by scalar_tac
      have hal : aa.val.length = N := hwf.1
      have hpl : pt.val.length = N := hpt.1
      have hdl : d.val.length = N := hcd.1
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
      -- the four indices
      step as ⟨i0, hi0⟩
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      step as ⟨i, hi⟩
      step as ⟨i3, hi3⟩
      have hi0b : i0.val < N := by rw [hi0]; omega
      have hi1b : i1.val < N := by rw [hi1, hi0]; omega
      have hi2b : i2.val < N := by rw [hi2, hi0]; omega
      have hi3b : i3.val < N := by rw [hi3, hi, hi0]; omega
      -- twisted read 0: `a.0[i0].to_u64() · pt[i0]`
      have hab0 : i0.val < aa.val.length := by rw [hal]; exact hi0b
      have hpb0 : i0.val < pt.val.length := by rw [hpl]; exact hi0b
      step as ⟨f0, hf0⟩
      step with HachiEquiv.Ring.to_u64_id f0 as ⟨x0, hx0⟩
      step as ⟨y0, hy0⟩
      have hx0v : x0.val = HachiEquiv.Ring.wordN aa i0.val := by
        rw [hx0, hf0]
        unfold HachiEquiv.Ring.wordN
        rw [List.getD_eq_getElem _ _ hab0]
      have hy0v : y0.val = wordAt pt i0.val := by
        rw [hy0, ← wordAt_of_lt (v := pt) (t := i0.val) hpb0]
      step with gold_mul_spec x0 y0 as ⟨a0, ha0m, h0lt⟩
      have ha0v : a0.val = twSrc aa pt i0.val := by rw [ha0m, hx0v, hy0v]; rfl
      -- twisted read 1: `a.0[i1].to_u64() · pt[i1]`
      have hab1 : i1.val < aa.val.length := by rw [hal]; exact hi1b
      have hpb1 : i1.val < pt.val.length := by rw [hpl]; exact hi1b
      step as ⟨f1, hf1⟩
      step with HachiEquiv.Ring.to_u64_id f1 as ⟨x1, hx1⟩
      step as ⟨y1, hy1⟩
      have hx1v : x1.val = HachiEquiv.Ring.wordN aa i1.val := by
        rw [hx1, hf1]
        unfold HachiEquiv.Ring.wordN
        rw [List.getD_eq_getElem _ _ hab1]
      have hy1v : y1.val = wordAt pt i1.val := by
        rw [hy1, ← wordAt_of_lt (v := pt) (t := i1.val) hpb1]
      step with gold_mul_spec x1 y1 as ⟨a1, ha1m, h1lt⟩
      have ha1v : a1.val = twSrc aa pt i1.val := by rw [ha1m, hx1v, hy1v]; rfl
      -- twisted read 2: `a.0[i2].to_u64() · pt[i2]`
      have hab2 : i2.val < aa.val.length := by rw [hal]; exact hi2b
      have hpb2 : i2.val < pt.val.length := by rw [hpl]; exact hi2b
      step as ⟨f2, hf2⟩
      step with HachiEquiv.Ring.to_u64_id f2 as ⟨x2, hx2⟩
      step as ⟨y2, hy2⟩
      have hx2v : x2.val = HachiEquiv.Ring.wordN aa i2.val := by
        rw [hx2, hf2]
        unfold HachiEquiv.Ring.wordN
        rw [List.getD_eq_getElem _ _ hab2]
      have hy2v : y2.val = wordAt pt i2.val := by
        rw [hy2, ← wordAt_of_lt (v := pt) (t := i2.val) hpb2]
      step with gold_mul_spec x2 y2 as ⟨a2, ha2m, h2lt⟩
      have ha2v : a2.val = twSrc aa pt i2.val := by rw [ha2m, hx2v, hy2v]; rfl
      -- twisted read 3: `a.0[i3].to_u64() · pt[i3]`
      have hab3 : i3.val < aa.val.length := by rw [hal]; exact hi3b
      have hpb3 : i3.val < pt.val.length := by rw [hpl]; exact hi3b
      step as ⟨f3, hf3⟩
      step with HachiEquiv.Ring.to_u64_id f3 as ⟨x3, hx3⟩
      step as ⟨y3, hy3⟩
      have hx3v : x3.val = HachiEquiv.Ring.wordN aa i3.val := by
        rw [hx3, hf3]
        unfold HachiEquiv.Ring.wordN
        rw [List.getD_eq_getElem _ _ hab3]
      have hy3v : y3.val = wordAt pt i3.val := by
        rw [hy3, ← wordAt_of_lt (v := pt) (t := i3.val) hpb3]
      step with gold_mul_spec x3 y3 as ⟨a3, ha3m, h3lt⟩
      have ha3v : a3.val = twSrc aa pt i3.val := by rw [ha3m, hx3v, hy3v]; rfl
      rw [hi0] at ha0v
      rw [hi1, hi0] at ha1v
      rw [hi2, hi0] at ha2v
      rw [hi3, hi, hi0] at ha3v
      have ha3v' : a3.val = twSrc aa pt (start.val + jj.val + quarter.val + half.val) := by
        rw [ha3v]; congr 1; omega
      -- the first stage's four values
      step with gold_add_spec a0 a2 h0lt h2lt as ⟨b0, hb0v, hb0lt⟩
      step with gold_add_spec a1 a3 h1lt h3lt as ⟨b1, hb1v, hb1lt⟩
      step with gold_sub_spec a0 a2 h0lt h2lt as ⟨d0, hd0v, hd0lt⟩
      step as ⟨i12, hi12⟩
      have hi12b : i12.val < tw.val.length := by rw [htl, hi12]; exact hbt1
      step as ⟨t1, ht1⟩
      have ht1v : t1.val = wordAt tw (jj.val * step1.val) := by
        rw [ht1, ← wordAt_of_lt (v := tw) (t := i12.val) hi12b, hi12]
      step with gold_mul_spec d0 t1 as ⟨b2, hb2v, hb2lt⟩
      step with gold_sub_spec a1 a3 h1lt h3lt as ⟨d1, hd1v, hd1lt⟩
      step as ⟨i14, hi14⟩
      step as ⟨i15, hi15⟩
      have hi15b : i15.val < tw.val.length := by rw [htl, hi15, hi14]; exact hbt2
      step as ⟨t2, ht2⟩
      have ht2v : t2.val = wordAt tw ((jj.val + quarter.val) * step1.val) := by
        rw [ht2, ← wordAt_of_lt (v := tw) (t := i15.val) hi15b, hi15, hi14]
      step with gold_mul_spec d1 t2 as ⟨b3, hb3v, hb3lt⟩
      -- the four intermediates, in the `bSum` / `bDif` form
      have hb0f : b0.val = bSum (twSrc aa pt) half.val (start.val + jj.val) := by
        rw [hb0v, ha0v, ha2v]; rfl
      have hb1f : b1.val
          = bSum (twSrc aa pt) half.val (start.val + jj.val + quarter.val) := by
        rw [hb1v, ha1v, ha3v']; rfl
      have hb2f : b2.val
          = bDif (twSrc aa pt) (wordAt tw) half.val (jj.val * step1.val)
              (start.val + jj.val) := by
        rw [hb2v, hd0v, ht1v, ha0v, ha2v]; rfl
      have hb3f : b3.val
          = bDif (twSrc aa pt) (wordAt tw) half.val ((jj.val + quarter.val) * step1.val)
              (start.val + jj.val + quarter.val) := by
        rw [hb3v, hd1v, ht2v, ha1v, ha3v']; rfl
      -- write 1: `start + jj`
      step with gold_add_spec b0 b1 hb0lt hb1lt as ⟨o0, ho0v, ho0lt⟩
      have hidb : i0.val < d.val.length := by rw [hdl]; exact hi0b
      step as ⟨elem, back, helem, hback⟩
      step with gold_sub_spec b0 b1 hb0lt hb1lt as ⟨e0, he0v, he0lt⟩
      step as ⟨i18, hi18⟩
      have hi18b : i18.val < tw.val.length := by rw [htl, hi18]; exact hbt3
      step as ⟨t3, ht3⟩
      have ht3v : t3.val = wordAt tw (jj.val * step2.val) := by
        rw [ht3, ← wordAt_of_lt (v := tw) (t := i18.val) hi18b, hi18]
      step with gold_mul_spec e0 t3 as ⟨o1, ho1v, ho1lt⟩
      rw [hback]
      -- write 2: `start + jj + quarter`
      have hc1 : Canon GP (d.set i0 o0) := Canon_set hcd ho0lt
      have hd1l : (d.set i0 o0).val.length = N := hc1.1
      step as ⟨i21, hi21⟩
      have hi21b : i21.val < (d.set i0 o0).val.length := by rw [hd1l, hi21, hi0]; omega
      step as ⟨elem1, back1, helem1, hback1⟩
      step with gold_add_spec b2 b3 hb2lt hb3lt as ⟨o2, ho2v, ho2lt⟩
      rw [hback1]
      -- write 3: `start + half + jj`
      have hc2 : Canon GP ((d.set i0 o0).set i21 o1) := Canon_set hc1 ho1lt
      have hd2l : ((d.set i0 o0).set i21 o1).val.length = N := hc2.1
      step as ⟨i23, hi23⟩
      step as ⟨i24, hi24⟩
      have hi24b : i24.val < ((d.set i0 o0).set i21 o1).val.length := by
        rw [hd2l, hi24, hi23]; omega
      step as ⟨elem2, back2, helem2, hback2⟩
      step with gold_sub_spec b2 b3 hb2lt hb3lt as ⟨e1, he1v, he1lt⟩
      step as ⟨t4, ht4⟩
      have ht4v : t4.val = wordAt tw (jj.val * step2.val) := by
        rw [ht4, ← wordAt_of_lt (v := tw) (t := i18.val) hi18b, hi18]
      step with gold_mul_spec e1 t4 as ⟨o3, ho3v, ho3lt⟩
      rw [hback2]
      -- write 4: `start + half + quarter + jj`
      have hc3 : Canon GP (((d.set i0 o0).set i21 o1).set i24 o2) := Canon_set hc2 ho2lt
      have hd3l : (((d.set i0 o0).set i21 o1).set i24 o2).val.length = N := hc3.1
      step as ⟨i27, hi27⟩
      have hi27b : i27.val + jj.val < N := by rw [hi27, hi23]; omega
      step as ⟨i28, hi28⟩
      case hmax => scalar_tac
      have hi28b : i28.val < (((d.set i0 o0).set i21 o1).set i24 o2).val.length := by
        rw [hd3l, hi28, hi27, hi23]; omega
      step as ⟨elem3, back3, helem3, hback3⟩
      step as ⟨j1, hj1⟩
      case hmax => scalar_tac
      rw [hback3]
      -- the four positions, as naturals
      have p0 : i0.val = start.val + jj.val := hi0
      have p1 : i21.val = start.val + jj.val + quarter.val := by rw [hi21, hi0]
      have p2 : i24.val = start.val + half.val + jj.val := by rw [hi24, hi23]
      have p3 : i28.val = start.val + half.val + quarter.val + jj.val := by
        rw [hi28, hi27, hi23]
      have hdisA : ∀ u, u < jj.val →
          (start.val + u ≠ i0.val ∧ start.val + u ≠ i21.val
            ∧ start.val + u ≠ i24.val ∧ start.val + u ≠ i28.val)
          ∧ (start.val + u + quarter.val ≠ i0.val
            ∧ start.val + u + quarter.val ≠ i21.val
            ∧ start.val + u + quarter.val ≠ i24.val
            ∧ start.val + u + quarter.val ≠ i28.val)
          ∧ (start.val + half.val + u ≠ i0.val
            ∧ start.val + half.val + u ≠ i21.val
            ∧ start.val + half.val + u ≠ i24.val
            ∧ start.val + half.val + u ≠ i28.val)
          ∧ (start.val + half.val + quarter.val + u ≠ i0.val
            ∧ start.val + half.val + quarter.val + u ≠ i21.val
            ∧ start.val + half.val + quarter.val + u ≠ i24.val
            ∧ start.val + half.val + quarter.val + u ≠ i28.val) := by
        clear * - p0 p1 p2 p3 hjlt hhq hqpos
        intro u hu
        refine ⟨⟨by omega, by omega, by omega, by omega⟩,
          ⟨by omega, by omega, by omega, by omega⟩,
          ⟨by omega, by omega, by omega, by omega⟩,
          ⟨by omega, by omega, by omega, by omega⟩⟩
      have hdisB :
          (start.val + jj.val ≠ i21.val ∧ start.val + jj.val ≠ i24.val
            ∧ start.val + jj.val ≠ i28.val)
          ∧ (start.val + jj.val + quarter.val ≠ i24.val
            ∧ start.val + jj.val + quarter.val ≠ i28.val)
          ∧ start.val + half.val + jj.val ≠ i28.val := by
        clear * - p0 p1 p2 p3 hjlt hhq hqpos
        exact ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, by omega⟩, by omega⟩
      have hdisF : ∀ k, (k < start.val ∨ start.val + 2 * half.val ≤ k) →
          k ≠ i0.val ∧ k ≠ i21.val ∧ k ≠ i24.val ∧ k ≠ i28.val := by
        clear * - p0 p1 p2 p3 hjlt hhq hqpos
        intro k hk
        exact ⟨by omega, by omega, by omega, by omega⟩
      -- `s.1 = a` became `aa = aa` under the `subst` and `simp only` closed it
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
            ← p1, wordAt_set_eq hi21b, ho1v, he0v, ht3v, hb0f, hb1f]
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
          rw [wordAt_set_ne n3, ← p2, wordAt_set_eq hi24b, ho2v, hb2f, hb3f]
          rfl
      · intro u hu
        rw [hj1] at hu
        rcases Nat.lt_or_ge u jj.val with hlt2 | hge
        · obtain ⟨-, -, -, ⟨n0, n1, n2, n3⟩⟩ := hdisA u hlt2
          rw [wordAt_set_ne n3, wordAt_set_ne n2, wordAt_set_ne n1, wordAt_set_ne n0]
          exact hv3 u hlt2
        · have heu : u = jj.val := by clear * - hu hge; omega
          subst heu
          rw [← p3, wordAt_set_eq hi28b, ho3v, he1v, ht4v, hb2f, hb3f]
          rfl
      · intro k hk
        obtain ⟨n0, n1, n2, n3⟩ := hdisF k hk
        rw [wordAt_set_ne n3, wordAt_set_ne n2, wordAt_set_ne n1, wordAt_set_ne n0]
        exact hfr k hk
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = quarter.val := by scalar_tac
      exact ⟨rfl, hcd, fun u hu => hv0 u (by rw [heq]; exact hu),
        fun u hu => hv1 u (by rw [heq]; exact hu),
        fun u hu => hv2 u (by rw [heq]; exact hu),
        fun u hu => hv3 u (by rw [heq]; exact hu), hfr⟩
  · exact ⟨hj, rfl, hdst, hw0, hw1, hw2, hw3, fun k _ => rfl⟩

/-- The outer loop of the twist stage: blocks in order, each filled by the inner
loop, the finished blocks carried by the frame condition. -/
theorem twist_loop0_spec (a : ring.Rq) (tw pt dst : alloc.vec.Vec Std.U64)
    (len half quarter step1 step2 start : Std.Usize)
    (hwf : HachiEquiv.Ring.Wf a) (hpt : Canon GP pt) (hdst : Canon GP dst) (htw : Canon GP tw)
    (hlen : len.val = 2 * half.val) (hhq : half.val = 2 * quarter.val)
    (hqpos : 0 < quarter.val) (hdvd : len.val ∣ N)
    (hs2 : step2.val = 2 * step1.val) (hstep : 0 < step1.val)
    (hebd : half.val * step1.val ≤ N)
    (hstart : start.val ≤ N) (hmod : start.val % len.val = 0)
    (hval : ∀ t, t < start.val →
      wordAt dst t = difWord GP quarter.val step2.val
        (difWord GP half.val step1.val (twSrc a pt) (wordAt tw)) (wordAt tw) t) :
    ring.gold_dif_stage2_twist_loop0 a len tw pt ntt.NTT_LEN half quarter step1 step2 dst start
      ⦃ z => Canon GP z
             ∧ ∀ t, t < N →
                 wordAt z t = difWord GP quarter.val step2.val
                   (difWord GP half.val step1.val (twSrc a pt) (wordAt tw))
                   (wordAt tw) t ⦄ := by
  rw [ring.gold_dif_stage2_twist_loop0]
  apply loop.spec_decr_nat (fun s => N - s.2.2.val)
    (fun s => s.2.2.val ≤ N ∧ s.1 = a ∧ s.2.2.val % len.val = 0 ∧ Canon GP s.2.1
      ∧ (∀ t, t < s.2.2.val →
          wordAt s.2.1 t = difWord GP quarter.val step2.val
            (difWord GP half.val step1.val (twSrc a pt) (wordAt tw)) (wordAt tw) t))
  · rintro ⟨aa, d, ss⟩ ⟨hss, haa, hmod1, hcd, hval1⟩
    dsimp only at hss haa hmod1 hcd hval1
    subst haa
    simp only [ring.gold_dif_stage2_twist_loop0.body]
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
      step with twist_loop0_loop0_spec aa tw pt d half quarter step1 step2
        ss 0#usize hwf hpt hcd htw hhq hqpos hblk2 (by simp) hs2 hstep hebd
        (by intro u hu; simp at hu) (by intro u hu; simp at hu)
        (by intro u hu; simp at hu) (by intro u hu; simp at hu)
        as ⟨aa1, d1, hr1, hc1, hwr0, hwr1, hwr2, hwr3, hfr1⟩
      have hr1' : aa = aa1 := hr1.symm
      subst hr1'
      step as ⟨ss1, hss1⟩
      refine ⟨by omega, ?_, hc1, ?_, by omega⟩
      · rw [hss1, Nat.add_mod_right, hmod1]
      · intro t ht
        rw [hss1] at ht
        rcases Nat.lt_or_ge t ss.val with h1 | h1
        · rw [hfr1 t (Or.inl h1)]
          exact hval1 t h1
        · rcases Nat.lt_or_ge (t - ss.val) quarter.val with h2 | h2
          · rw [show t = ss.val + (t - ss.val) by omega, hwr0 (t - ss.val) h2]
            exact (fusedA (twSrc aa pt) (wordAt tw) half.val quarter.val step1.val
              step2.val ss.val (t - ss.val) hhq h2 hsm).symm
          · rcases Nat.lt_or_ge (t - ss.val) half.val with h3 | h3
            · rw [show t = ss.val + (t - ss.val - quarter.val) + quarter.val by omega,
                hwr1 (t - ss.val - quarter.val) (by omega)]
              exact (fusedB (twSrc aa pt) (wordAt tw) half.val quarter.val step1.val
                step2.val ss.val (t - ss.val - quarter.val) hhq (by omega) hsm).symm
            · rcases Nat.lt_or_ge (t - ss.val) (half.val + quarter.val) with h4 | h4
              · rw [show t = ss.val + half.val + (t - ss.val - half.val) by omega,
                  hwr2 (t - ss.val - half.val) (by omega)]
                exact (fusedC (twSrc aa pt) (wordAt tw) half.val quarter.val step1.val
                  step2.val ss.val (t - ss.val - half.val) hhq (by omega) hsm).symm
              · rw [show t = ss.val + half.val + quarter.val
                      + (t - ss.val - half.val - quarter.val) by omega,
                  hwr3 (t - ss.val - half.val - quarter.val) (by omega)]
                exact (fusedD (twSrc aa pt) (wordAt tw) half.val quarter.val step1.val
                  step2.val ss.val (t - ss.val - half.val - quarter.val) hhq
                  (by omega) hsm).symm
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ss.val = N := by scalar_tac
      exact ⟨hcd, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · exact ⟨hstart, rfl, hmod, hdst, hval⟩

/-- The division facts for a block length `2 ^ (k+2)` dividing `N = 1024`
(`GoldFusedStage.fusedParams`, which is private there). -/
theorem fusedParams' (k : ℕ) (hk : k < 9) :
    N / 2 ^ (k + 1) = 2 ^ (9 - k) ∧ N / 2 ^ (k + 2) = 2 ^ (8 - k)
      ∧ 2 ^ (k + 2) ∣ N := by
  have hN : N = 2 ^ 10 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [hN, Nat.pow_div (by omega) (by norm_num)]; congr 1; omega
  · rw [hN, Nat.pow_div (by omega) (by norm_num)]; congr 1; omega
  · rw [hN]; exact pow_dvd_pow 2 (by omega)

/-- **The twist stage**: [`GoldFusedStage.gold_dif_stage2_spec`]'s conclusion
with the source words replaced by the twisted ones. -/
theorem gold_dif_stage2_twist_spec (a : ring.Rq) (out tw pt : alloc.vec.Vec Std.U64)
    (len : Std.Usize) (k : ℕ) (hk : k < 9) (hlen : len.val = 2 ^ (k + 2))
    (hwf : HachiEquiv.Ring.Wf a) (hout : Canon GP out) (htw : Canon GP tw) (hpt : Canon GP pt) :
    ring.gold_dif_stage2_twist a out len tw pt
      ⦃ z => Canon GP z
             ∧ ∀ t, t < N →
                 wordAt z t
                   = difWord GP (2 ^ k) (2 * (N / 2 ^ (k + 1)))
                       (difWord GP (2 ^ (k + 1)) (2 * (N / 2 ^ (k + 2)))
                         (twSrc a pt) (wordAt tw)) (wordAt tw) t ⦄ := by
  obtain ⟨hd1, hd2, hdvd⟩ := fusedParams' k hk
  have hlne : len.val ≠ 0 := by rw [hlen]; positivity
  rw [ring.gold_dif_stage2_twist]
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
  refine twist_loop0_spec a tw pt out len hf qq st1 st2 0#usize
    hwf hpt hout htw ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by simp) (by simp) (by intro t ht; simp at ht)
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

/-! ## Part B: the MAC stage

The fused last stage writes `acc[o] = acc[o] + pfwd[base + o] · v` where
`gold_dif_stage2` wrote `dst[o] = v`. [`macAt`] is that word; [`pfW`] is the
prepared table read at the term's offset, the `A` of `gold_mac_off_spec`
before the cast. -/

/-- The prepared table's word at `base + u`. -/
def pfW (pfwd : alloc.vec.Vec Std.U64) (base u : ℕ) : ℕ := wordAt pfwd (base + u)

/-- What the fused MAC leaves at `t`: the old word plus `pfw t · v`, reduced. -/
def macAt (aw pfw : ℕ → ℕ) (t v : ℕ) : ℕ := (aw t + (pfw t * v) % GP) % GP

theorem macAt_lt (aw pfw : ℕ → ℕ) (t v : ℕ) : macAt aw pfw t v < GP := Nat.mod_lt _ GP_pos

theorem macAt_cast (aw pfw : ℕ → ℕ) (t v : ℕ) :
    ((macAt aw pfw t v : ℕ) : ZMod GP)
      = ((aw t : ℕ) : ZMod GP) + ((pfw t : ℕ) : ZMod GP) * ((v : ℕ) : ZMod GP) := by
  simp only [macAt]
  rw [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_mod, Nat.cast_mul]

/-- One block's worth of fused groups, accumulating. `acc0` is the accumulator
at the loop's entry and `acc` the one at counter `j`; besides the four written
clauses (in [`macAt`] of `acc0`'s words) and the outer frame, the invariant
carries the four *pending* clauses -- the positions of this block not yet
written still hold `acc0`'s words -- which is what each group's four reads of
the accumulator need. -/
theorem mac_loop0_loop0_spec (src acc0 acc tw pfwd : alloc.vec.Vec Std.U64)
    (base half quarter step1 step2 start j : Std.Usize)
    (hsrc : Canon GP src) (hacc : Canon GP acc) (htw : Canon GP tw)
    (hb : base.val + N ≤ pfwd.val.length)
    (hhq : half.val = 2 * quarter.val) (hqpos : 0 < quarter.val)
    (hblk : start.val + 2 * half.val ≤ N) (hj : j.val ≤ quarter.val)
    (hs2 : step2.val = 2 * step1.val) (hstep : 0 < step1.val)
    (hebd : half.val * step1.val ≤ N)
    (hw0 : ∀ u, u < j.val →
      wordAt acc (start.val + u) = macAt (wordAt acc0) (pfW pfwd base.val) (start.val + u)
        (f0 (wordAt src) half.val quarter.val start.val u))
    (hw1 : ∀ u, u < j.val →
      wordAt acc (start.val + u + quarter.val)
        = macAt (wordAt acc0) (pfW pfwd base.val) (start.val + u + quarter.val)
            (f1 (wordAt src) (wordAt tw) half.val quarter.val step2.val start.val u))
    (hw2 : ∀ u, u < j.val →
      wordAt acc (start.val + half.val + u)
        = macAt (wordAt acc0) (pfW pfwd base.val) (start.val + half.val + u)
            (f2 (wordAt src) (wordAt tw) half.val quarter.val step1.val start.val u))
    (hw3 : ∀ u, u < j.val →
      wordAt acc (start.val + half.val + quarter.val + u)
        = macAt (wordAt acc0) (pfW pfwd base.val) (start.val + half.val + quarter.val + u)
            (f3 (wordAt src) (wordAt tw) half.val quarter.val step1.val step2.val start.val u))
    (hp0 : ∀ u, j.val ≤ u → u < quarter.val →
      wordAt acc (start.val + u) = wordAt acc0 (start.val + u))
    (hp1 : ∀ u, j.val ≤ u → u < quarter.val →
      wordAt acc (start.val + u + quarter.val) = wordAt acc0 (start.val + u + quarter.val))
    (hp2 : ∀ u, j.val ≤ u → u < quarter.val →
      wordAt acc (start.val + half.val + u) = wordAt acc0 (start.val + half.val + u))
    (hp3 : ∀ u, j.val ≤ u → u < quarter.val →
      wordAt acc (start.val + half.val + quarter.val + u)
        = wordAt acc0 (start.val + half.val + quarter.val + u)) :
    ntt.gold_dif_stage2_mac_loop0_loop0 src acc tw pfwd base half quarter step1 step2 start j
      ⦃ z => Canon GP z
             ∧ (∀ u, u < quarter.val →
                 wordAt z (start.val + u) = macAt (wordAt acc0) (pfW pfwd base.val) (start.val + u)
                   (f0 (wordAt src) half.val quarter.val start.val u))
             ∧ (∀ u, u < quarter.val →
                 wordAt z (start.val + u + quarter.val)
                   = macAt (wordAt acc0) (pfW pfwd base.val) (start.val + u + quarter.val)
                       (f1 (wordAt src) (wordAt tw) half.val quarter.val step2.val start.val u))
             ∧ (∀ u, u < quarter.val →
                 wordAt z (start.val + half.val + u)
                   = macAt (wordAt acc0) (pfW pfwd base.val) (start.val + half.val + u)
                       (f2 (wordAt src) (wordAt tw) half.val quarter.val step1.val start.val u))
             ∧ (∀ u, u < quarter.val →
                 wordAt z (start.val + half.val + quarter.val + u)
                   = macAt (wordAt acc0) (pfW pfwd base.val)
                       (start.val + half.val + quarter.val + u)
                       (f3 (wordAt src) (wordAt tw) half.val quarter.val step1.val step2.val
                         start.val u))
             ∧ (∀ k, (k < start.val ∨ start.val + 2 * half.val ≤ k) →
                 wordAt z k = wordAt acc k) ⦄ := by
  rw [ntt.gold_dif_stage2_mac_loop0_loop0]
  apply loop.spec_decr_nat (fun s => quarter.val - s.2.val)
    (fun s => s.2.val ≤ quarter.val ∧ Canon GP s.1
      ∧ (∀ u, u < s.2.val →
          wordAt s.1 (start.val + u) = macAt (wordAt acc0) (pfW pfwd base.val) (start.val + u)
            (f0 (wordAt src) half.val quarter.val start.val u))
      ∧ (∀ u, u < s.2.val →
          wordAt s.1 (start.val + u + quarter.val)
            = macAt (wordAt acc0) (pfW pfwd base.val) (start.val + u + quarter.val)
                (f1 (wordAt src) (wordAt tw) half.val quarter.val step2.val start.val u))
      ∧ (∀ u, u < s.2.val →
          wordAt s.1 (start.val + half.val + u)
            = macAt (wordAt acc0) (pfW pfwd base.val) (start.val + half.val + u)
                (f2 (wordAt src) (wordAt tw) half.val quarter.val step1.val start.val u))
      ∧ (∀ u, u < s.2.val →
          wordAt s.1 (start.val + half.val + quarter.val + u)
            = macAt (wordAt acc0) (pfW pfwd base.val) (start.val + half.val + quarter.val + u)
                (f3 (wordAt src) (wordAt tw) half.val quarter.val step1.val step2.val start.val u))
      ∧ (∀ u, s.2.val ≤ u → u < quarter.val →
          wordAt s.1 (start.val + u) = wordAt acc0 (start.val + u))
      ∧ (∀ u, s.2.val ≤ u → u < quarter.val →
          wordAt s.1 (start.val + u + quarter.val) = wordAt acc0 (start.val + u + quarter.val))
      ∧ (∀ u, s.2.val ≤ u → u < quarter.val →
          wordAt s.1 (start.val + half.val + u) = wordAt acc0 (start.val + half.val + u))
      ∧ (∀ u, s.2.val ≤ u → u < quarter.val →
          wordAt s.1 (start.val + half.val + quarter.val + u)
            = wordAt acc0 (start.val + half.val + quarter.val + u))
      ∧ (∀ k, (k < start.val ∨ start.val + 2 * half.val ≤ k) →
          wordAt s.1 k = wordAt acc k))
  · rintro ⟨d, jj⟩ ⟨hjj, hcd, hv0, hv1, hv2, hv3, hq0, hq1, hq2, hq3, hfr1⟩
    dsimp only at hjj hcd hv0 hv1 hv2 hv3 hq0 hq1 hq2 hq3 hfr1
    simp only [ntt.gold_dif_stage2_mac_loop0_loop0.body]
    by_cases hlt : jj < quarter
    · rw [if_pos hlt]
      have hjlt : jj.val < quarter.val := by scalar_tac
      have hsl : src.val.length = N := hsrc.1
      have hdl : d.val.length = N := hcd.1
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
      -- the four positions, as naturals, and the disequalities the writes need
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
      -- write 1: `start + jj`
      step with gold_add_spec b0 b1 hb0lt hb1lt as ⟨v0, hv0v, hv0lt⟩
      have hv0f : v0.val = f0 (wordAt src) half.val quarter.val start.val jj.val := by
        rw [hv0v, hb0f, hb1f]; rfl
      have hidb : i.val < d.val.length := by rw [hdl, hi]; omega
      step as ⟨c0, hc0⟩
      have hc0v : c0.val = wordAt acc0 (start.val + jj.val) := by
        rw [hc0, ← wordAt_of_lt (v := d) (t := i.val) hidb, hi]
        exact hq0 jj.val (le_refl _) hjlt
      have hc0lt : c0.val < GP := by
        rw [hc0, ← wordAt_of_lt (v := d) (t := i.val) hidb]; exact wordAt_lt hcd GP_pos _
      have hbi : base.val + i.val < pfwd.val.length := by rw [hi]; omega
      step as ⟨k0, hk0⟩
      try (case hmax => scalar_tac)
      have hk0b : k0.val < pfwd.val.length := by rw [hk0]; exact hbi
      step as ⟨w0, hw0'⟩
      have hw0v : w0.val = pfW pfwd base.val (start.val + jj.val) := by
        rw [hw0', ← wordAt_of_lt (v := pfwd) (t := k0.val) hk0b, hk0, hi]; rfl
      step with gold_mul_spec w0 v0 as ⟨m0, hm0v, hm0lt⟩
      step with gold_add_spec c0 m0 hc0lt hm0lt as ⟨o0, ho0v, ho0lt⟩
      have ho0f : o0.val = macAt (wordAt acc0) (pfW pfwd base.val) (start.val + jj.val)
          (f0 (wordAt src) half.val quarter.val start.val jj.val) := by
        rw [ho0v, hm0v, hc0v, hw0v, hv0f]; rfl
      step as ⟨elem, back, helem, hback⟩
      step as ⟨o1i, ho1i⟩
      try (case hmax => scalar_tac)
      have p1 : o1i.val = start.val + jj.val + quarter.val := by rw [ho1i, hi]
      step with gold_sub_spec b0 b1 hb0lt hb1lt as ⟨e0, he0v, he0lt⟩
      step as ⟨i15, hi15⟩
      try (case hmax => scalar_tac)
      have hi15b : i15.val < tw.val.length := by rw [htl, hi15]; exact hbt3
      step as ⟨t3, ht3⟩
      have ht3v : t3.val = wordAt tw (jj.val * step2.val) := by
        rw [ht3, ← wordAt_of_lt (v := tw) (t := i15.val) hi15b, hi15]
      step with gold_mul_spec e0 t3 as ⟨v1, hv1v, hv1lt⟩
      have hv1f : v1.val
          = f1 (wordAt src) (wordAt tw) half.val quarter.val step2.val start.val jj.val := by
        rw [hv1v, he0v, ht3v, hb0f, hb1f]; rfl
      rw [hback]
      -- write 2: `start + jj + quarter`
      have hc1 : Canon GP (d.set i o0) := Canon_set hcd ho0lt
      have hd1l : (d.set i o0).val.length = N := hc1.1
      have ho1b : o1i.val < (d.set i o0).val.length := by rw [hd1l, p1]; omega
      step as ⟨c1, hc1'⟩
      have hc1v : c1.val = wordAt acc0 (start.val + jj.val + quarter.val) := by
        rw [hc1', ← wordAt_of_lt (v := d.set i o0) (t := o1i.val) ho1b, p1,
          wordAt_set_ne (by rw [p0]; exact n01.symm)]
        exact hq1 jj.val (le_refl _) hjlt
      have hc1lt : c1.val < GP := by
        rw [hc1', ← wordAt_of_lt (v := d.set i o0) (t := o1i.val) ho1b]
        exact wordAt_lt hc1 GP_pos _
      have hbo1 : base.val + o1i.val < pfwd.val.length := by rw [p1]; omega
      step as ⟨k1, hk1⟩
      try (case hmax => scalar_tac)
      have hk1b : k1.val < pfwd.val.length := by rw [hk1]; exact hbo1
      step as ⟨w1, hw1'⟩
      have hw1v : w1.val = pfW pfwd base.val (start.val + jj.val + quarter.val) := by
        rw [hw1', ← wordAt_of_lt (v := pfwd) (t := k1.val) hk1b, hk1, p1]; rfl
      step with gold_mul_spec w1 v1 as ⟨m1, hm1v, hm1lt⟩
      step with gold_add_spec c1 m1 hc1lt hm1lt as ⟨o1, ho1v, ho1lt⟩
      have ho1f : o1.val = macAt (wordAt acc0) (pfW pfwd base.val)
          (start.val + jj.val + quarter.val)
          (f1 (wordAt src) (wordAt tw) half.val quarter.val step2.val start.val jj.val) := by
        rw [ho1v, hm1v, hc1v, hw1v, hv1f]; rfl
      step as ⟨elem1, back1, helem1, hback1⟩
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
      -- write 3: `start + half + jj`
      have hc2 : Canon GP ((d.set i o0).set o1i o1) := Canon_set hc1 ho1lt
      have hd2l : ((d.set i o0).set o1i o1).val.length = N := hc2.1
      have ho2b : o2i.val < ((d.set i o0).set o1i o1).val.length := by rw [hd2l, p2]; omega
      step as ⟨c2, hc2'⟩
      have hc2v : c2.val = wordAt acc0 (start.val + half.val + jj.val) := by
        rw [hc2', ← wordAt_of_lt (v := (d.set i o0).set o1i o1) (t := o2i.val) ho2b, p2,
          wordAt_set_ne (by rw [p1]; exact n12.symm), wordAt_set_ne (by rw [p0]; exact n02.symm)]
        exact hq2 jj.val (le_refl _) hjlt
      have hc2lt : c2.val < GP := by
        rw [hc2', ← wordAt_of_lt (v := (d.set i o0).set o1i o1) (t := o2i.val) ho2b]
        exact wordAt_lt hc2 GP_pos _
      have hbo2 : base.val + o2i.val < pfwd.val.length := by rw [p2]; omega
      step as ⟨k2, hk2⟩
      try (case hmax => scalar_tac)
      have hk2b : k2.val < pfwd.val.length := by rw [hk2]; exact hbo2
      step as ⟨w2, hw2'⟩
      have hw2v : w2.val = pfW pfwd base.val (start.val + half.val + jj.val) := by
        rw [hw2', ← wordAt_of_lt (v := pfwd) (t := k2.val) hk2b, hk2, p2]; rfl
      step with gold_mul_spec w2 v2 as ⟨m2, hm2v, hm2lt⟩
      step with gold_add_spec c2 m2 hc2lt hm2lt as ⟨o2, ho2v, ho2lt⟩
      have ho2f : o2.val = macAt (wordAt acc0) (pfW pfwd base.val)
          (start.val + half.val + jj.val)
          (f2 (wordAt src) (wordAt tw) half.val quarter.val step1.val start.val jj.val) := by
        rw [ho2v, hm2v, hc2v, hw2v, hv2f]; rfl
      step as ⟨elem2, back2, helem2, hback2⟩
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
      -- write 4: `start + half + quarter + jj`
      have hc3 : Canon GP (((d.set i o0).set o1i o1).set o2i o2) := Canon_set hc2 ho2lt
      have hd3l : (((d.set i o0).set o1i o1).set o2i o2).val.length = N := hc3.1
      have ho3b : o3i.val < (((d.set i o0).set o1i o1).set o2i o2).val.length := by
        rw [hd3l, p3]; omega
      step as ⟨c3, hc3'⟩
      have hc3v : c3.val = wordAt acc0 (start.val + half.val + quarter.val + jj.val) := by
        rw [hc3', ← wordAt_of_lt (v := ((d.set i o0).set o1i o1).set o2i o2) (t := o3i.val) ho3b,
          p3, wordAt_set_ne (by rw [p2]; exact n23.symm), wordAt_set_ne (by rw [p1]; exact n13.symm),
          wordAt_set_ne (by rw [p0]; exact n03.symm)]
        exact hq3 jj.val (le_refl _) hjlt
      have hc3lt : c3.val < GP := by
        rw [hc3', ← wordAt_of_lt (v := ((d.set i o0).set o1i o1).set o2i o2) (t := o3i.val) ho3b]
        exact wordAt_lt hc3 GP_pos _
      have hbo3 : base.val + o3i.val < pfwd.val.length := by rw [p3]; omega
      step as ⟨k3, hk3⟩
      try (case hmax => scalar_tac)
      have hk3b : k3.val < pfwd.val.length := by rw [hk3]; exact hbo3
      step as ⟨w3, hw3'⟩
      have hw3v : w3.val = pfW pfwd base.val (start.val + half.val + quarter.val + jj.val) := by
        rw [hw3', ← wordAt_of_lt (v := pfwd) (t := k3.val) hk3b, hk3, p3]; rfl
      step with gold_mul_spec w3 v3 as ⟨m3, hm3v, hm3lt⟩
      step with gold_add_spec c3 m3 hc3lt hm3lt as ⟨o3, ho3v, ho3lt⟩
      have ho3f : o3.val = macAt (wordAt acc0) (pfW pfwd base.val)
          (start.val + half.val + quarter.val + jj.val)
          (f3 (wordAt src) (wordAt tw) half.val quarter.val step1.val step2.val start.val
            jj.val) := by
        rw [ho3v, hm3v, hc3v, hw3v, hv3f]; rfl
      step as ⟨elem3, back3, helem3, hback3⟩
      step as ⟨j1, hj1⟩
      try (case hmax => scalar_tac)
      rw [hback3]
      -- distinctness against every other position, in a context of arithmetic alone
      have hdisA : ∀ u, u ≠ jj.val → u < quarter.val →
          (start.val + u ≠ i.val ∧ start.val + u ≠ o1i.val
            ∧ start.val + u ≠ o2i.val ∧ start.val + u ≠ o3i.val)
          ∧ (start.val + u + quarter.val ≠ i.val
            ∧ start.val + u + quarter.val ≠ o1i.val
            ∧ start.val + u + quarter.val ≠ o2i.val
            ∧ start.val + u + quarter.val ≠ o3i.val)
          ∧ (start.val + half.val + u ≠ i.val
            ∧ start.val + half.val + u ≠ o1i.val
            ∧ start.val + half.val + u ≠ o2i.val
            ∧ start.val + half.val + u ≠ o3i.val)
          ∧ (start.val + half.val + quarter.val + u ≠ i.val
            ∧ start.val + half.val + quarter.val + u ≠ o1i.val
            ∧ start.val + half.val + quarter.val + u ≠ o2i.val
            ∧ start.val + half.val + quarter.val + u ≠ o3i.val) := by
        clear * - p0 p1 p2 p3 hjlt hhq hqpos
        intro u hu hu2
        refine ⟨⟨by omega, by omega, by omega, by omega⟩,
          ⟨by omega, by omega, by omega, by omega⟩,
          ⟨by omega, by omega, by omega, by omega⟩,
          ⟨by omega, by omega, by omega, by omega⟩⟩
      have hdisF : ∀ k, (k < start.val ∨ start.val + 2 * half.val ≤ k) →
          k ≠ i.val ∧ k ≠ o1i.val ∧ k ≠ o2i.val ∧ k ≠ o3i.val := by
        clear * - p0 p1 p2 p3 hjlt hhq hqpos
        intro k hk
        exact ⟨by omega, by omega, by omega, by omega⟩
      have hself :
          (start.val + jj.val ≠ o1i.val ∧ start.val + jj.val ≠ o2i.val
            ∧ start.val + jj.val ≠ o3i.val)
          ∧ (start.val + jj.val + quarter.val ≠ o2i.val
            ∧ start.val + jj.val + quarter.val ≠ o3i.val)
          ∧ start.val + half.val + jj.val ≠ o3i.val := by
        clear * - p0 p1 p2 p3 hjlt hhq hqpos
        exact ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, by omega⟩, by omega⟩
      refine ⟨by clear * - hj1 hjlt; omega, Canon_set hc3 ho3lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        by clear * - hj1 hjlt hqpos; omega⟩
      · intro u hu
        rw [hj1] at hu
        rcases Nat.lt_or_ge u jj.val with hlt2 | hge
        · obtain ⟨⟨m0, m1, m2, m3⟩, -, -, -⟩ := hdisA u (by omega) (by omega)
          rw [wordAt_set_ne m3, wordAt_set_ne m2, wordAt_set_ne m1, wordAt_set_ne m0]
          exact hv0 u hlt2
        · have heu : u = jj.val := by clear * - hu hge; omega
          subst heu
          obtain ⟨⟨q1, q2, q3⟩, -, -⟩ := hself
          rw [wordAt_set_ne q3, wordAt_set_ne q2, wordAt_set_ne q1]
          conv_lhs => rw [← p0]
          rw [wordAt_set_eq hidb]
          exact ho0f
      · intro u hu
        rw [hj1] at hu
        rcases Nat.lt_or_ge u jj.val with hlt2 | hge
        · obtain ⟨-, ⟨m0, m1, m2, m3⟩, -, -⟩ := hdisA u (by omega) (by omega)
          rw [wordAt_set_ne m3, wordAt_set_ne m2, wordAt_set_ne m1, wordAt_set_ne m0]
          exact hv1 u hlt2
        · have heu : u = jj.val := by clear * - hu hge; omega
          subst heu
          obtain ⟨-, ⟨q2, q3⟩, -⟩ := hself
          rw [wordAt_set_ne q3, wordAt_set_ne q2]
          conv_lhs => rw [← p1]
          rw [wordAt_set_eq ho1b]
          exact ho1f
      · intro u hu
        rw [hj1] at hu
        rcases Nat.lt_or_ge u jj.val with hlt2 | hge
        · obtain ⟨-, -, ⟨m0, m1, m2, m3⟩, -⟩ := hdisA u (by omega) (by omega)
          rw [wordAt_set_ne m3, wordAt_set_ne m2, wordAt_set_ne m1, wordAt_set_ne m0]
          exact hv2 u hlt2
        · have heu : u = jj.val := by clear * - hu hge; omega
          subst heu
          obtain ⟨-, -, q3⟩ := hself
          rw [wordAt_set_ne q3]
          conv_lhs => rw [← p2]
          rw [wordAt_set_eq ho2b]
          exact ho2f
      · intro u hu
        rw [hj1] at hu
        rcases Nat.lt_or_ge u jj.val with hlt2 | hge
        · obtain ⟨-, -, -, ⟨m0, m1, m2, m3⟩⟩ := hdisA u (by omega) (by omega)
          rw [wordAt_set_ne m3, wordAt_set_ne m2, wordAt_set_ne m1, wordAt_set_ne m0]
          exact hv3 u hlt2
        · have heu : u = jj.val := by clear * - hu hge; omega
          subst heu
          conv_lhs => rw [← p3]
          rw [wordAt_set_eq ho3b]
          exact ho3f
      · intro u hu hu2
        rw [hj1] at hu
        obtain ⟨⟨m0, m1, m2, m3⟩, -, -, -⟩ := hdisA u (by omega) hu2
        rw [wordAt_set_ne m3, wordAt_set_ne m2, wordAt_set_ne m1, wordAt_set_ne m0]
        exact hq0 u (by omega) hu2
      · intro u hu hu2
        rw [hj1] at hu
        obtain ⟨-, ⟨m0, m1, m2, m3⟩, -, -⟩ := hdisA u (by omega) hu2
        rw [wordAt_set_ne m3, wordAt_set_ne m2, wordAt_set_ne m1, wordAt_set_ne m0]
        exact hq1 u (by omega) hu2
      · intro u hu hu2
        rw [hj1] at hu
        obtain ⟨-, -, ⟨m0, m1, m2, m3⟩, -⟩ := hdisA u (by omega) hu2
        rw [wordAt_set_ne m3, wordAt_set_ne m2, wordAt_set_ne m1, wordAt_set_ne m0]
        exact hq2 u (by omega) hu2
      · intro u hu hu2
        rw [hj1] at hu
        obtain ⟨-, -, -, ⟨m0, m1, m2, m3⟩⟩ := hdisA u (by omega) hu2
        rw [wordAt_set_ne m3, wordAt_set_ne m2, wordAt_set_ne m1, wordAt_set_ne m0]
        exact hq3 u (by omega) hu2
      · intro k hk
        obtain ⟨m0, m1, m2, m3⟩ := hdisF k hk
        rw [wordAt_set_ne m3, wordAt_set_ne m2, wordAt_set_ne m1, wordAt_set_ne m0]
        exact hfr1 k hk
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = quarter.val := by scalar_tac
      exact ⟨hcd, fun u hu => hv0 u (by rw [heq]; exact hu),
        fun u hu => hv1 u (by rw [heq]; exact hu),
        fun u hu => hv2 u (by rw [heq]; exact hu),
        fun u hu => hv3 u (by rw [heq]; exact hu), hfr1⟩
  · exact ⟨hj, hacc, hw0, hw1, hw2, hw3, hp0, hp1, hp2, hp3, fun k _ => rfl⟩

/-- The composite stage's word at `t`, the value the MAC multiplies in. -/
def stage2W (sw tww : ℕ → ℕ) (half quarter step1 step2 t : ℕ) : ℕ :=
  difWord GP quarter step2 (difWord GP half step1 sw tww) tww t

/-- The outer loop of the MAC stage. Two frames now: the finished blocks below
`start` hold their `macAt` value, and the untouched ones at and above it still
hold `acc0`'s words -- the latter is what each inner call reads. -/
theorem mac_loop0_spec (src acc0 acc tw pfwd : alloc.vec.Vec Std.U64) (len : Std.Usize)
    (base half quarter step1 step2 start : Std.Usize)
    (hsrc : Canon GP src) (hacc : Canon GP acc) (htw : Canon GP tw)
    (hb : base.val + N ≤ pfwd.val.length)
    (hlen : len.val = 2 * half.val) (hhq : half.val = 2 * quarter.val)
    (hqpos : 0 < quarter.val) (hdvd : len.val ∣ N)
    (hs2 : step2.val = 2 * step1.val) (hstep : 0 < step1.val)
    (hebd : half.val * step1.val ≤ N)
    (hstart : start.val ≤ N) (hmod : start.val % len.val = 0)
    (hval : ∀ t, t < start.val →
      wordAt acc t = macAt (wordAt acc0) (pfW pfwd base.val) t
        (stage2W (wordAt src) (wordAt tw) half.val quarter.val step1.val step2.val t))
    (hfr : ∀ t, start.val ≤ t → wordAt acc t = wordAt acc0 t) :
    ntt.gold_dif_stage2_mac_loop0 src acc len tw pfwd base ntt.NTT_LEN half quarter step1 step2
        start
      ⦃ z => Canon GP z
             ∧ ∀ t, t < N →
                 wordAt z t = macAt (wordAt acc0) (pfW pfwd base.val) t
                   (stage2W (wordAt src) (wordAt tw) half.val quarter.val step1.val step2.val
                     t) ⦄ := by
  rw [ntt.gold_dif_stage2_mac_loop0]
  apply loop.spec_decr_nat (fun s => N - s.2.val)
    (fun s => s.2.val ≤ N ∧ s.2.val % len.val = 0 ∧ Canon GP s.1
      ∧ (∀ t, t < s.2.val →
          wordAt s.1 t = macAt (wordAt acc0) (pfW pfwd base.val) t
            (stage2W (wordAt src) (wordAt tw) half.val quarter.val step1.val step2.val t))
      ∧ (∀ t, s.2.val ≤ t → wordAt s.1 t = wordAt acc0 t))
  · rintro ⟨d, ss⟩ ⟨hss, hmod1, hcd, hval1, hfr1⟩
    dsimp only at hss hmod1 hcd hval1 hfr1
    simp only [ntt.gold_dif_stage2_mac_loop0.body]
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
      -- inside the block the current buffer still holds `acc0`'s words
      have hpend : ∀ k, ss.val ≤ k → wordAt d k = wordAt acc0 k := hfr1
      step with mac_loop0_loop0_spec src acc0 d tw pfwd base half quarter step1 step2
        ss 0#usize hsrc hcd htw hb hhq hqpos hblk2 (by simp) hs2 hstep hebd
        (by intro u hu; simp at hu) (by intro u hu; simp at hu)
        (by intro u hu; simp at hu) (by intro u hu; simp at hu)
        (by intro u _ _; exact hpend _ (by omega)) (by intro u _ _; exact hpend _ (by omega))
        (by intro u _ _; exact hpend _ (by omega)) (by intro u _ _; exact hpend _ (by omega))
        as ⟨d1, hc1, hwr0, hwr1, hwr2, hwr3, hfr2⟩
      step as ⟨ss1, hss1⟩
      try (case hmax => scalar_tac)
      refine ⟨by omega, ?_, hc1, ?_, ?_, by omega⟩
      · rw [hss1, Nat.add_mod_right, hmod1]
      · intro t ht
        rw [hss1] at ht
        rcases Nat.lt_or_ge t ss.val with h1 | h1
        · rw [hfr2 t (Or.inl h1)]
          exact hval1 t h1
        · simp only [stage2W]
          rcases Nat.lt_or_ge (t - ss.val) quarter.val with h2 | h2
          · rw [show t = ss.val + (t - ss.val) by omega, hwr0 (t - ss.val) h2]
            congr 1
            exact (fusedA (wordAt src) (wordAt tw) half.val quarter.val step1.val
                step2.val ss.val (t - ss.val) hhq h2 hsm).symm
          · rcases Nat.lt_or_ge (t - ss.val) half.val with h3 | h3
            · rw [show t = ss.val + (t - ss.val - quarter.val) + quarter.val by omega,
                hwr1 (t - ss.val - quarter.val) (by omega)]
              congr 1
              exact (fusedB (wordAt src) (wordAt tw) half.val quarter.val step1.val
                  step2.val ss.val (t - ss.val - quarter.val) hhq (by omega) hsm).symm
            · rcases Nat.lt_or_ge (t - ss.val) (half.val + quarter.val) with h4 | h4
              · rw [show t = ss.val + half.val + (t - ss.val - half.val) by omega,
                  hwr2 (t - ss.val - half.val) (by omega)]
                congr 1
                exact (fusedC (wordAt src) (wordAt tw) half.val quarter.val step1.val
                    step2.val ss.val (t - ss.val - half.val) hhq (by omega) hsm).symm
              · rw [show t = ss.val + half.val + quarter.val
                      + (t - ss.val - half.val - quarter.val) by omega,
                  hwr3 (t - ss.val - half.val - quarter.val) (by omega)]
                congr 1
                exact (fusedD (wordAt src) (wordAt tw) half.val quarter.val step1.val
                    step2.val ss.val (t - ss.val - half.val - quarter.val) hhq
                    (by omega) hsm).symm
      · intro t ht
        rw [hss1] at ht
        rw [hfr2 t (Or.inr (by omega))]
        exact hfr1 t (by omega)
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ss.val = N := by scalar_tac
      exact ⟨hcd, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · exact ⟨hstart, hmod, hacc, hval, hfr⟩

/-- **The MAC stage**: `acc[t] += pfwd[base + t] · (difWord ∘ difWord)(src)[t]`, as
words. -/
theorem gold_dif_stage2_mac_spec (src acc tw pfwd : alloc.vec.Vec Std.U64)
    (len base : Std.Usize) (k : ℕ) (hk : k < 9) (hlen : len.val = 2 ^ (k + 2))
    (hsrc : Canon GP src) (hacc : Canon GP acc) (htw : Canon GP tw)
    (hb : base.val + N ≤ pfwd.val.length) :
    ntt.gold_dif_stage2_mac src acc len tw pfwd base
      ⦃ z => Canon GP z
             ∧ ∀ t, t < N →
                 wordAt z t
                   = macAt (wordAt acc) (pfW pfwd base.val) t
                       (difWord GP (2 ^ k) (2 * (N / 2 ^ (k + 1)))
                         (difWord GP (2 ^ (k + 1)) (2 * (N / 2 ^ (k + 2)))
                           (wordAt src) (wordAt tw)) (wordAt tw) t) ⦄ := by
  obtain ⟨hd1, hd2, hdvd⟩ := fusedParams' k hk
  have hlne : len.val ≠ 0 := by rw [hlen]; positivity
  rw [ntt.gold_dif_stage2_mac]
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
  refine mac_loop0_spec src acc acc tw pfwd len base hf qq st1 st2 0#usize
    hsrc hacc htw hb ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by simp) (by simp) (by intro t ht; simp at ht)
    (fun t _ => rfl)
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

/-! ## Part C: the middle loop

`gold_forward`'s loop with its first and last iterations peeled: it starts at
`len = N/4` and stops at `len = 4`, so it delivers the transform *up to its
last two stages* -- `difRun … 2 (2^8)` of its output is the answer, where
`gold_forward_loop_spec` delivers `difRun … 0`. The proof is that lemma's with
the exit case moved. -/
theorem gold_dot_one_fused_loop_spec (pt cur tmp : alloc.vec.Vec Std.U64)
    (len : Std.Usize) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 4) (hlen : len.val = 2 ^ (2 * k))
    (hcur : Canon GP cur) (htmp : Canon GP tmp) (hpt : Canon GP pt)
    (psi : ZMod GP) (hpsi : ∀ e, e < N → resK GP pt e = psi ^ e)
    (g : ℕ → ZMod GP)
    (hinv : ∀ t, t < N →
      NttMath.difRun (psi ^ 2) (2 * k) (2 ^ (10 - 2 * k)) (resK GP cur) t = g t) :
    ring.gold_dot_one_fused_loop pt cur tmp len
      ⦃ z => Canon GP z.1 ∧ Canon GP z.2
             ∧ ∀ t, t < N → NttMath.difRun (psi ^ 2) 2 (2 ^ 8) (resK GP z.1) t = g t ⦄ := by
  have hag : ∀ e, e < N → wordAt pt e = psiRep psi e := tw_agree' GP pt GP_pos hpt psi hpsi
  rw [ring.gold_dot_one_fused_loop]
  apply loop.spec_decr_nat (fun s => s.2.2.val)
    (fun s => Canon GP s.1 ∧ Canon GP s.2.1
      ∧ ∃ i, 1 ≤ i ∧ i ≤ 4 ∧ s.2.2.val = 2 ^ (2 * i)
        ∧ ∀ t, t < N →
            NttMath.difRun (psi ^ 2) (2 * i) (2 ^ (10 - 2 * i)) (resK GP s.1) t = g t)
  · rintro ⟨c, d, l⟩ ⟨hc, hd, i, hi1, hi, hli, hvi⟩
    dsimp only at hc hd hli hvi
    simp only [ring.gold_dot_one_fused_loop.body]
    by_cases hlt : l > 4#usize
    · rw [if_pos hlt]
      have hl4 : 4 < l.val := by scalar_tac
      have hi2 : 2 ≤ i := by
        by_contra hcon
        have hi1' : i = 1 := by omega
        rw [hi1'] at hli
        norm_num at hli
        omega
      obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      have hm1 : 1 ≤ m := by omega
      have hm3 : m ≤ 3 := by omega
      have hk9 : 2 * m < 9 := by omega
      have hlk : l.val = 2 ^ (2 * m + 2) := by rw [hli]; congr 1
      step with GoldFusedStage.gold_dif_stage2_spec c d pt l (2 * m) hk9 hlk hc hd hpt
        as ⟨fl, hcf, hwf⟩
      step as ⟨l2, hl2⟩
      have hswc : ∀ u, wordAt c u < GP := fun u => wordAt_lt hc GP_pos u
      have hstep1 : N / 2 ^ (2 * m + 1) = 2 ^ (9 - 2 * m) := N_div_pow (2 * m) (by omega)
      have hstep2 : N / 2 ^ (2 * m + 2) = 2 ^ (8 - 2 * m) := by
        have h := N_div_pow (2 * m + 1) (by omega)
        rw [show 9 - (2 * m + 1) = 8 - 2 * m by omega] at h
        rw [show 2 * m + 2 = 2 * m + 1 + 1 by ring]
        exact h
      have hinner : difWord GP (2 ^ (2 * m + 1)) (2 * (N / 2 ^ (2 * m + 2)))
            (wordAt c) (wordAt pt)
          = difWord GP (2 ^ (2 * m + 1)) (2 * (N / 2 ^ (2 * m + 2)))
            (wordAt c) (psiRep psi) :=
        funext (fun u => difWord_tw_congr GP (2 * m + 1) (by omega) (wordAt c)
          (wordAt pt) (psiRep psi) hag u)
      have hres : ∀ t, t < N →
          resK GP fl t
            = NttMath.difStage (2 ^ (2 * m)) (2 ^ (9 - 2 * m)) (psi ^ 2)
                (NttMath.difStage (2 ^ (2 * m + 1)) (2 ^ (8 - 2 * m)) (psi ^ 2)
                  (resK GP c)) t := by
        intro t ht
        have h1 : wordAt fl t
            = difWord GP (2 ^ (2 * m)) (2 * (N / 2 ^ (2 * m + 1)))
                (difWord GP (2 ^ (2 * m + 1)) (2 * (N / 2 ^ (2 * m + 2)))
                  (wordAt c) (psiRep psi)) (psiRep psi) t := by
          rw [hwf t ht, hinner]
          exact difWord_tw_congr GP (2 * m) (by omega) _ (wordAt pt) (psiRep psi) hag t
        have hmid : (fun u => ((difWord GP (2 ^ (2 * m + 1)) (2 * 2 ^ (8 - 2 * m))
              (wordAt c) (psiRep psi) u : ℕ) : ZMod GP))
            = NttMath.difStage (2 ^ (2 * m + 1)) (2 ^ (8 - 2 * m)) (psi ^ 2) (resK GP c) :=
          funext (fun u => difWord_cast GP (2 ^ (2 * m + 1)) (2 ^ (8 - 2 * m)) psi
            (wordAt c) (psiRep psi) (psiRep_cast GP_pos psi) hswc u)
        have hlt2 : ∀ u, difWord GP (2 ^ (2 * m + 1)) (2 * 2 ^ (8 - 2 * m))
            (wordAt c) (psiRep psi) u < GP :=
          fun u => difWord_lt GP _ _ GP_pos _ _ u
        rw [resK, h1, hstep1, hstep2,
          difWord_cast GP (2 ^ (2 * m)) (2 ^ (9 - 2 * m)) psi _ (psiRep psi)
            (psiRep_cast GP_pos psi) hlt2 t, hmid]
      have hnext : ∀ t, t < N →
          NttMath.difRun (psi ^ 2) (2 * m) (2 ^ (10 - 2 * m)) (resK GP fl) t = g t := by
        intro t ht
        have hdvd : (2 : ℕ) ^ (2 * m) ∣ N := by
          rw [show N = 2 ^ 10 by norm_num]
          exact pow_dvd_pow 2 (by omega)
        rw [difRun_congr (psi ^ 2) (2 * m) hdvd (2 ^ (10 - 2 * m)) (resK GP fl)
              (NttMath.difStage (2 ^ (2 * m)) (2 ^ (9 - 2 * m)) (psi ^ 2)
                (NttMath.difStage (2 ^ (2 * m + 1)) (2 ^ (8 - 2 * m)) (psi ^ 2)
                  (resK GP c))) hres t ht]
        rw [← hvi t ht, show 10 - 2 * (m + 1) = 8 - 2 * m by omega,
          show 2 * (m + 1) = 2 * m + 1 + 1 by ring, NttMath.difRun_succ,
          show (2 : ℕ) ^ (8 - 2 * m) * 2 = 2 ^ (9 - 2 * m) by
            rw [show 9 - 2 * m = (8 - 2 * m) + 1 by omega, pow_succ],
          NttMath.difRun_succ,
          show (2 : ℕ) ^ (9 - 2 * m) * 2 = 2 ^ (10 - 2 * m) by
            rw [show 10 - 2 * m = (9 - 2 * m) + 1 by omega, pow_succ]]
      have hl2v : l2.val = 2 ^ (2 * m) := by
        rw [hl2, hlk, show (2 : ℕ) ^ (2 * m + 2) = 2 ^ (2 * m) * 4 by rw [pow_add]; ring]
        omega
      refine ⟨hcf, hc, ⟨m, hm1, by omega, hl2v, hnext⟩, ?_⟩
      rw [hl2v, hlk, show (2 : ℕ) ^ (2 * m + 2) = 2 ^ (2 * m) * 4 by rw [pow_add]; ring]
      have hp : 0 < (2 : ℕ) ^ (2 * m) := Nat.two_pow_pos _
      omega
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hl4 : l.val ≤ 4 := by scalar_tac
      have hi1' : i = 1 := by
        rcases Nat.lt_or_ge i 2 with hh | hh
        · omega
        · exfalso
          have h2 : (2 : ℕ) ^ 4 ≤ 2 ^ (2 * i) := Nat.pow_le_pow_right (by norm_num) (by omega)
          rw [hli] at hl4
          norm_num at h2
          omega
      subst hi1'
      refine ⟨hc, hd, ?_⟩
      intro t ht
      have := hvi t ht
      norm_num at this
      exact this
  · exact ⟨hcur, htmp, k, hk1, hk, hlen, hinv⟩

/-! ## Part D: one fused term

The three specs composed in the ring. The conclusion is what
`load_twisted_into_spec`, `gold_forward_spec` and `gold_mac_off_spec` gave in
sequence: the accumulator gains `A · difRun (twist a)`, with `A` the prepared
table's entry read in place, and both buffers come back `Canon`. -/
theorem gold_dot_one_fused_spec (a : ring.Rq) (cur0 tmp0 acc0 pt pfwd : alloc.vec.Vec Std.U64)
    (baseU : Std.Usize) (ps : ZMod GP) (A : ℕ → ZMod GP)
    (hwf : HachiEquiv.Ring.Wf a) (hcur : Canon GP cur0) (htmp : Canon GP tmp0)
    (hacc : Canon GP acc0)
    (hptC : Canon GP pt) (hptv : ∀ e, e < N → resK GP pt e = ps ^ e)
    (hb : baseU.val + N ≤ pfwd.val.length)
    (hA : ∀ t, t < N → ((wordAt pfwd (baseU.val + t) : ℕ) : ZMod GP) = A t) :
    ring.gold_dot_one_fused a cur0 tmp0 acc0 pt pfwd baseU
      ⦃ z => Canon GP z.1 ∧ Canon GP z.2.1 ∧ Canon GP z.2.2
             ∧ ∀ t, t < N → resK GP z.1 t
                 = resK GP acc0 t
                   + A t * NttMath.difRun (ps ^ 2) 10 1
                       (NttMath.twistR ps
                         (fun u => ((HachiEquiv.Ring.wordN a u : ℕ) : ZMod GP))) t ⦄ := by
  have hag : ∀ e, e < N → wordAt pt e = psiRep ps e := tw_agree' GP pt GP_pos hptC ps hptv
  set F : ℕ → ZMod GP := fun u => ((twSrc a pt u : ℕ) : ZMod GP) with hF
  rw [ring.gold_dot_one_fused]
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
        (psiRep_cast GP_pos ps) (twSrc_lt a pt) u)
    have hlt2 : ∀ u, difWord GP (2 ^ (8 + 1)) (2 * 2 ^ 0) (twSrc a pt) (psiRep ps) u < GP :=
      fun u => difWord_lt GP _ _ GP_pos _ _ u
    rw [resK, h1, hstep1, hstep2,
      difWord_cast GP (2 ^ 8) (2 ^ 1) ps _ (psiRep ps) (psiRep_cast GP_pos ps) hlt2 t, hmid]
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
  -- (C) the middle loop, from `len = N/4` down to `len = 4`
  step as ⟨len, hlen⟩
  have hlenv : len.val = 2 ^ (2 * 4) := by rw [hlen, ntt_NTT_LEN_val]; norm_num
  step with gold_dot_one_fused_loop_spec pt c1 tmp0 len 4 (by norm_num) (le_refl 4) hlenv
    hc1C htmp hptC ps hptv (NttMath.difRun (ps ^ 2) 10 1 F) hinv0
    as ⟨c2, t2, hc2C, ht2C, hc2v⟩
  -- (B) the MAC stage, the last two stages at `len = 4`
  step with gold_dif_stage2_mac_spec c2 acc0 pt pfwd 4#usize baseU 0 (by norm_num)
    (by norm_num) hc2C hacc hptC hb as ⟨acc1, hacc1C, hacc1w⟩
  refine ⟨hacc1C, hc2C, ht2C, ?_⟩
  intro t ht
  have hstepM1 : N / 2 ^ (0 + 1) = 2 ^ 9 := by norm_num
  have hstepM2 : N / 2 ^ (0 + 2) = 2 ^ 8 := by norm_num
  have hinnerM : difWord GP (2 ^ (0 + 1)) (2 * (N / 2 ^ (0 + 2))) (wordAt c2) (wordAt pt)
      = difWord GP (2 ^ (0 + 1)) (2 * (N / 2 ^ (0 + 2))) (wordAt c2) (psiRep ps) :=
    funext (fun u => difWord_tw_congr GP (0 + 1) (by omega) (wordAt c2)
      (wordAt pt) (psiRep ps) hag u)
  have hswc : ∀ u, wordAt c2 u < GP := fun u => wordAt_lt hc2C GP_pos u
  have hmidM : (fun u => ((difWord GP (2 ^ (0 + 1)) (2 * 2 ^ 8) (wordAt c2) (psiRep ps) u
        : ℕ) : ZMod GP))
      = NttMath.difStage (2 ^ (0 + 1)) (2 ^ 8) (ps ^ 2) (resK GP c2) :=
    funext (fun u => difWord_cast GP (2 ^ (0 + 1)) (2 ^ 8) ps (wordAt c2) (psiRep ps)
      (psiRep_cast GP_pos ps) hswc u)
  have hlt2M : ∀ u, difWord GP (2 ^ (0 + 1)) (2 * 2 ^ 8) (wordAt c2) (psiRep ps) u < GP :=
    fun u => difWord_lt GP _ _ GP_pos _ _ u
  have hresM : ((difWord GP (2 ^ 0) (2 * (N / 2 ^ (0 + 1)))
        (difWord GP (2 ^ (0 + 1)) (2 * (N / 2 ^ (0 + 2))) (wordAt c2) (wordAt pt))
        (wordAt pt) t : ℕ) : ZMod GP)
      = NttMath.difRun (ps ^ 2) 2 (2 ^ 8) (resK GP c2) t := by
    rw [hinnerM, difWord_tw_congr GP 0 (by omega) _ (wordAt pt) (psiRep ps) hag t,
      hstepM1, hstepM2,
      difWord_cast GP (2 ^ 0) (2 ^ 9) ps _ (psiRep ps) (psiRep_cast GP_pos ps) hlt2M t, hmidM]
    rfl
  have hAt : ((pfW pfwd baseU.val t : ℕ) : ZMod GP) = A t := hA t ht
  -- the twisted words agree with the twist below `N`, which is all `difRun` reads
  have hFtw : NttMath.difRun (ps ^ 2) 10 1 F t
      = NttMath.difRun (ps ^ 2) 10 1
          (NttMath.twistR ps (fun u => ((HachiEquiv.Ring.wordN a u : ℕ) : ZMod GP))) t :=
    difRun_congr (ps ^ 2) 10 (by norm_num) 1 F _
      (fun u hu => twSrc_cast a pt ps hptv u hu) t ht
  rw [resK, hacc1w t ht, macAt_cast, hAt, hresM, hc2v t ht, hFtw]
  rfl

end HachiEquiv.GoldFusedBoundary
