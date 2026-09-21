/-
The **two-lane general dot** (candidate G2): one Goldilocks lane and one
31-bit Barrett lane in place of three 31-bit ones.

The general path cannot use a single Goldilocks lane -- its right operand is
the raw message, so one chunk reaches `N·cols·(q−1)² = 1.55·10^26` against a
lane's `1.84·10^19`. It was assumed to need two *64-bit* lanes, and therefore
a second prime without Goldilocks' free reduction, i.e. Montgomery, i.e. a
representation change. The bound says otherwise:

```text
  chunk bound     N·cols·(q−1)²  = 1.547·10^26  ≈ 2^87.0
  three 31-bit    p1·p2·p3       = 4.711·10^26  ≈ 2^88.6
  GOLD_P · p1                    = 8.666·10^27  ≈ 2^92.8
```

so two lanes clear it with more room than three did, and the second lane is
`AUX_P1`, already in the crate with its `Magic` instance already proved. This
file is the arithmetic that makes that substitution legitimate: the two-prime
Garner reconstruction.
-/
import NttCRT
import GoldArith
import GoldDot

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.RingTwoLane

open HachiEquiv.NttArith HachiEquiv.NttCRT HachiEquiv.GoldArith
open HachiEquiv.NttStage HachiEquiv.RingFused HachiEquiv.GoldTransform HachiEquiv.GoldDot

/-- The two-lane modulus, `GOLD_P · p1`. -/
abbrev PGA : ℕ := GP * p1

theorem PGA_val : PGA = 8665580291426793361116233729 := by norm_num [PGA, GP, p1]

/-- The bound one chunk of the general path actually reaches,
`N · cols · (q−1)²` at `N = 1024`, `cols = 8192`, `q = 2^32 − 99`. -/
abbrev ChunkBound : ℕ := 1024 * 8192 * (4294967196 * 4294967196)

/-- **Two lanes are enough.** This is the whole content of the card: the
reconstruction range covers what a chunk can produce, with 55× to spare. -/
theorem chunk_fits : ChunkBound < PGA := by norm_num [ChunkBound, PGA, GP, p1]

/-- `GOLD_P` is invertible mod `p1`, and `GA_GINV` is its inverse. -/
theorem gold_ginv : ((GP : ℕ) : ZMod p1) * ((4091113 : ℕ) : ZMod p1) = 1 := by
  have h : ((GP * 4091113 : ℕ) : ZMod p1) = ((1 : ℕ) : ZMod p1) := by
    rw [← ZMod.natCast_mod, show (GP * 4091113) % p1 = 1 by norm_num [GP, p1]]
  rw [Nat.cast_mul] at h
  simpa using h

@[simp, scalar_tac_simps] theorem GA_GINV_val : (ntt.GA_GINV).val = 4091113 := by
  simp only [ntt.GA_GINV]; decide +kernel

@[simp, scalar_tac_simps] theorem GOLD_P_val : (ntt.GOLD_P).val = GP := by
  simp only [ntt.GOLD_P]; decide +kernel

set_option maxRecDepth 100000 in
/-- **Two-prime Garner is exact.** Given the residues of a natural number
below `GOLD_P · p1`, `ntt.garner_ga` returns that number.

`x = rg + GOLD_P·q` with `q < p1`, and `q` is what the `p1` lane pins down:
`ra ≡ rg + GOLD_P·q (mod p1)`, so `(ra − rg)·GOLD_P⁻¹ ≡ q`, and both sides
are below `p1`. -/
theorem garner_ga_spec (rg ra : Std.U64) (x : ℕ) (hx : x < PGA)
    (hg : rg.val = x % GP) (ha : ra.val = x % p1) :
    ntt.garner_ga rg ra ⦃ z => z.val = x ⦄ := by
  have hp1pos : 0 < p1 := by norm_num [p1]
  have hgppos : 0 < GP := by norm_num [GP]
  have hrglt : rg.val < GP := by rw [hg]; exact Nat.mod_lt _ hgppos
  have hralt : ra.val < p1 := by rw [ha]; exact Nat.mod_lt _ hp1pos
  -- `x = rg + GOLD_P · q`, and `q < p1` because `x < GOLD_P · p1`
  set q : ℕ := x / GP with hqdef
  have hxq : x = rg.val + GP * q := by
    rw [hg, hqdef]; exact (Nat.mod_add_div x GP).symm
  have hxp : x < GP * p1 := hx
  have hqlt : q < p1 := by
    by_contra hcon
    have hge : p1 ≤ q := Nat.le_of_not_lt hcon
    have hmul : GP * p1 ≤ GP * q := Nat.mul_le_mul_left _ hge
    omega
  rw [ntt.garner_ga]
  -- `rgm = rg mod p1`
  step as ⟨rgm, hrgm⟩
  have hrgmv : rgm.val = rg.val % p1 := by rw [hrgm, AUX_P1_val]
  have hrgmlt : rgm.val < p1 := by rw [hrgmv]; exact Nat.mod_lt _ hp1pos
  -- the residues, read in `ZMod p1`
  have hrgmz : ((rgm.val : ℕ) : ZMod p1) = ((rg.val : ℕ) : ZMod p1) := by
    rw [hrgmv, ZMod.natCast_mod]
  have hraz : ((ra.val : ℕ) : ZMod p1) = ((rg.val : ℕ) : ZMod p1)
      + ((GP : ℕ) : ZMod p1) * ((q : ℕ) : ZMod p1) := by
    rw [ha, ZMod.natCast_mod, hxq, Nat.cast_add, Nat.cast_mul]
  -- `diff ≡ ra − rgm`, from either branch of the Rust
  have hstep : ∀ d : Std.U64,
      ((d.val : ℕ) : ZMod p1) = ((ra.val : ℕ) : ZMod p1) - ((rgm.val : ℕ) : ZMod p1) →
      ntt.aux_mul d ntt.GA_GINV ntt.AUX_P1 ntt.AUX_M1
        ⦃ z => z.val = x ⦄ → True := fun _ _ _ => trivial
  clear hstep
  have hfin : ∀ d : Std.U64, d.val < p1 →
      ((d.val : ℕ) : ZMod p1) = ((ra.val : ℕ) : ZMod p1) - ((rgm.val : ℕ) : ZMod p1) →
      (do let t ← ntt.aux_mul d ntt.GA_GINV ntt.AUX_P1 ntt.AUX_M1
          let g ← lift (UScalar.cast .U128 ntt.GOLD_P)
          let tw ← lift (UScalar.cast .U128 t)
          let i ← lift (UScalar.cast .U128 rg)
          let i1 ← g * tw
          i + i1) ⦃ z => z.val = x ⦄ := by
    intro d hdlt hdz
    step with aux_mul_spec d ntt.GA_GINV ntt.AUX_P1 ntt.AUX_M1 magic1
      (by rw [AUX_P1_val]; exact hdlt)
      (by rw [GA_GINV_val, AUX_P1_val]; norm_num [p1]) as ⟨t, htv⟩
    rw [AUX_P1_val] at htv
    have htlt : t.val < p1 := by rw [htv]; exact Nat.mod_lt _ hp1pos
    -- `t = q`: both are below `p1` and they agree in `ZMod p1`
    have htz : ((t.val : ℕ) : ZMod p1) = ((q : ℕ) : ZMod p1) := by
      rw [htv, GA_GINV_val, ZMod.natCast_mod, Nat.cast_mul, hdz, hraz, hrgmz]
      have : ((GP : ℕ) : ZMod p1) * ((q : ℕ) : ZMod p1) * ((4091113 : ℕ) : ZMod p1)
           = ((q : ℕ) : ZMod p1) * (((GP : ℕ) : ZMod p1) * ((4091113 : ℕ) : ZMod p1)) := by
        ring
      rw [add_sub_cancel_left, this, gold_ginv, mul_one]
    have hteq : t.val = q := by
      have h1 : (((t.val : ℕ) : ZMod p1)).val = t.val := ZMod.val_cast_of_lt htlt
      have h2 : (((q : ℕ) : ZMod p1)).val = q := ZMod.val_cast_of_lt hqlt
      rw [← h1, htz, h2]
    -- the three widenings and the final `rg + GOLD_P · t`
    step with UScalar.cast_inBounds_spec .U128 ntt.GOLD_P (u64_le_u128_max _) as ⟨g, hgv⟩
    step with UScalar.cast_inBounds_spec .U128 t (u64_le_u128_max _) as ⟨tw, htw⟩
    step with UScalar.cast_inBounds_spec .U128 rg (u64_le_u128_max _) as ⟨i, hi⟩
    have hprod : g.val * tw.val = GP * q := by
      rw [hgv, htw, GOLD_P_val, hteq]
    step as ⟨i1, hi1⟩
    step as ⟨r, hr⟩
    rw [hr, hi1, hi, hprod, ← hxq]
  by_cases hge : ra >= rgm
  · rw [if_pos hge]
    have hgev : rgm.val ≤ ra.val := by clear * - hge; scalar_tac
    step as ⟨d, hd⟩
    exact hfin d (by omega) (by
      rw [hd, Nat.cast_sub hgev])
  · rw [if_neg hge]
    have hltv : ra.val < rgm.val := by clear * - hge; scalar_tac
    step as ⟨i, hi⟩
    have hiv : i.val = ra.val + p1 := by rw [hi, AUX_P1_val]
    step as ⟨d, hd⟩
    refine hfin d (by omega) ?_
    rw [hd, hiv, Nat.cast_sub (by omega), Nat.cast_add]
    simp

/-! ## The Goldilocks lane of the general chunk

`dot_prep_chunk_gold` is `dot_prep_chunk_mod_p`'s body with the Goldilocks
operations in place of the Barrett ones, so its term loop is the digit
path's `gold_terms_spec` over a bare prepared table rather than a
`PreparedVecG`. This is that proof with `prep.fwd` read as `pfwd`. -/

/-- The word gather is again the *same loop*, so `prep_words_b_spec` is reused
rather than re-proved -- the chunk writes it exactly as the two-prime path
does, and nothing in it mentions a prime. -/
theorem gold_chunk_words_eq (b : alloc.vec.Vec ring.Rq) (n j : Std.Usize)
    (w : alloc.vec.Vec Std.U64) (u : Std.Usize) :
    ring.dot_prep_chunk_gold_loop0_loop0 b n j w u
      = ring.dot_prep_chunk_mod_p_loop0_loop0 b n j w u := rfl

set_option maxRecDepth 8192 in
theorem gold_chunk_terms_spec (pfwd : alloc.vec.Vec Std.U64)
    (a b : alloc.vec.Vec ring.Rq) (startU endU : Std.Usize)
    (nU : Std.Usize) (pt : alloc.vec.Vec Std.U64)
    (acc scratch : alloc.vec.Vec Std.U64) (jU : Std.Usize) (ps : ZMod GP)
    (hn : nU.val = N) (hord : ps ^ N = -1)
    (hptC : Canon GP pt) (hptv : ∀ e, e < N → resK GP pt e = ps ^ e)
    (hpl : endU.val * N ≤ pfwd.val.length)
    (hpv : ∀ j, j < endU.val → ∀ t, t < N →
        resK GP pfwd (j * N + t)
          = NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK GP a j)) t)
    (hpc : ∀ u ∈ pfwd.val, u.val < GP)
    (hbwf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbe : endU.val ≤ b.val.length)
    (hjs : startU.val ≤ jU.val) (hje : jU.val ≤ endU.val)
    (haccC : Canon GP acc) (hscC : Canon GP scratch)
    (hval : ∀ t, t < N → resK GP acc t
              = ∑ u ∈ Finset.Ico startU.val jU.val, termFwd ps a b u t) :
    ring.dot_prep_chunk_gold_loop0 pfwd b endU nU pt acc scratch jU
      ⦃ z => Canon GP z.1 ∧ Canon GP z.2
             ∧ ∀ t, t < N → resK GP z.1 t
                 = ∑ u ∈ Finset.Ico startU.val endU.val, termFwd ps a b u t ⦄ := by
  rw [ring.dot_prep_chunk_gold_loop0]
  apply loop.spec_decr_nat (fun r => endU.val - r.2.2.val)
    (fun r => startU.val ≤ r.2.2.val ∧ r.2.2.val ≤ endU.val
      ∧ Canon GP r.1 ∧ Canon GP r.2.1
      ∧ ∀ t, t < N → resK GP r.1 t
              = ∑ u ∈ Finset.Ico startU.val r.2.2.val, termFwd ps a b u t)
  · rintro ⟨d, sc, jj⟩ ⟨hjjs, hjje, hcd, hcsc, hw⟩
    dsimp only at hjjs hjje hcd hcsc hw
    simp only [ring.dot_prep_chunk_gold_loop0.body]
    by_cases hlt : jj < endU
    · rw [if_pos hlt]
      have hjjlt : jj.val < endU.val := by scalar_tac
      have hjb : jj.val < b.val.length := by omega
      simp only [alloc.vec.Vec.with_capacity]
      rw [gold_chunk_words_eq]
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
      have hslb : off.val + N ≤ pfwd.val.length := by
        rw [hoffv]
        have h1 : (jj.val + 1) * N ≤ endU.val * N := Nat.mul_le_mul_right N (by omega)
        have h2 : (jj.val + 1) * N = jj.val * N + N := by ring
        omega
      step with slice_out_top_spec pfwd off nU hn hslb as ⟨af, hafl, hafv⟩
      -- `pfwd` is `endU * N` long, so `Canon` does not apply to it; the bound
      -- comes from `hpc` directly, with the out-of-range default handled
      have hafC : Canon GP af := ⟨hafl, fun x hx => by
        obtain ⟨t, ht, hteq⟩ := List.getElem_of_mem hx
        have hb : wordAt af t = wordAt pfwd (off.val + t) :=
          hafv t (by rw [← hafl]; exact ht)
        rw [wordAt_of_lt ht] at hb
        rw [← hteq, hb]
        unfold wordAt
        by_cases hin : off.val + t < pfwd.val.length
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
