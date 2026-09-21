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

/-! ## The chunk

The Goldilocks counterpart of `RingFused.dot_prep_chunk_mod_p_spec`, with the
same conclusion at `GP`: the chunk's words are the negacyclic convolution sum
over `[start, end)`, offset by `boff · (end − start)`. The offset is what lets
the two lanes be reconstructed as a natural number; `BOUND = N·q²` is a
multiple of `q`, so it vanishes when the caller reduces. -/
set_option maxRecDepth 8192 in
theorem dot_prep_chunk_gold_spec (pfwd : alloc.vec.Vec Std.U64)
    (a b : alloc.vec.Vec ring.Rq) (startU endU : Std.Usize) (boff : Std.U64)
    (hboff : boff.val < GP)
    (hpl : endU.val * N ≤ pfwd.val.length)
    (hpv : ∀ j, j < endU.val → ∀ t, t < N →
        resK GP pfwd (j * N + t)
          = NttMath.difRun
              ((((ntt.GOLD_PSI.val : ℕ) : ZMod GP)) ^ 2) 10 1
              (NttMath.twistR ((ntt.GOLD_PSI.val : ℕ) : ZMod GP) (entryK GP a j)) t)
    (hpc : ∀ u ∈ pfwd.val, u.val < GP)
    (hbwf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbe : endU.val ≤ b.val.length) (hse : startU.val ≤ endU.val)
    (hwidth : endU.val ≤ 8192) :
    ring.dot_prep_chunk_gold pfwd b startU endU boff
      ⦃ z => Canon GP z ∧ ∀ t, t < N → resK GP z t
              = (∑ u ∈ Finset.Ico startU.val endU.val,
                  NttMath.negConvR N (entryK GP a u) (entryK GP b u) t)
                + ((boff.val : ℕ) : ZMod GP)
                    * (((endU.val - startU.val : ℕ)) : ZMod GP) ⦄ := by
  set ps : ZMod GP := ((ntt.GOLD_PSI.val : ℕ) : ZMod GP) with hpsdef
  set psii : ZMod GP := ((ntt.GOLD_PSIINV.val : ℕ) : ZMod GP) with hpsiidef
  have hord : ps ^ N = -1 := gpsi_ord
  have hpinv : ps * psii = 1 := gpsi_inv
  rw [ring.dot_prep_chunk_gold]
  step with gold_psi_table_cast ntt.GOLD_PSI (by decide +kernel) as ⟨pt, hptC, hptv⟩
  step with gold_psi_table_cast ntt.GOLD_PSIINV (by decide +kernel) as ⟨it, hitC, hitv⟩
  step with zeros_canon_zero GP GoldDot.GP_pos as ⟨acc0, hacc0C, hacc0v⟩
  step with gold_chunk_terms_spec pfwd a b startU endU ntt.NTT_LEN pt acc0 acc0
    startU ps ntt_NTT_LEN_val hord hptC hptv hpl hpv hpc hbwf hbe
    (le_refl _) hse hacc0C hacc0C
    (by intro t ht; rw [hacc0v t ht]; simp) as ⟨acc1, scratch, hac1C, hac2C, hac1v⟩
  -- the offset, scaled by this chunk's term count
  step as ⟨i, hi⟩
  have hcn : lift (UScalar.cast .U64 i) ⦃ y => y.val = i.val ⦄ :=
    UScalar.cast_inBounds_spec .U64 i (by scalar_tac)
  step with hcn as ⟨len, hlen⟩
  have hlenv : len.val = endU.val - startU.val := by rw [hlen, hi]
  step with gold_mul_spec boff len as ⟨scaled, hscv, hsclt⟩
  -- the inverse transform, and the value it carries
  have hPR : ∀ t, t < N → resK GP acc1 t
      = NttMath.difRun (ps ^ 2) 10 1
          (fun t' => ∑ u ∈ Finset.Ico startU.val endU.val,
            NttMath.cyclicConv N (NttMath.twistR ps (entryK GP a u))
              (NttMath.twistR ps (entryK GP b u)) t') t := by
    intro t ht
    rw [hac1v t ht, NttMath.difRun_sum (ps ^ 2) 10 1 (Finset.Ico startU.val endU.val)
      (fun u => NttMath.cyclicConv N (NttMath.twistR ps (entryK GP a u))
        (NttMath.twistR ps (entryK GP b u)))]
    simp only [termFwd, hpsdef]
  step with gold_inverse_spec acc1 scratch it hac1C hac2C hitC psii hitv
    as ⟨v, v5, hiv1, hiv2, hivv⟩
  have hIV := HachiEquiv.NttProduct.inv_value ps psii hpinv
    (fun t' => ∑ u ∈ Finset.Ico startU.val endU.val,
      NttMath.cyclicConv N (NttMath.twistR ps (entryK GP a u))
        (NttMath.twistR ps (entryK GP b u)) t')
    (resK GP acc1) (resK GP v) hPR hivv
  step with gold_untwist_cast v it scaled hiv1 hitC hsclt psii hitv
    as ⟨words, hwC, hwv⟩
  refine ⟨hwC, ?_⟩
  intro t ht
  rw [hwv t ht, hIV t ht,
    untwist_value_sum ps psii ((ntt.GOLD_NINV.val : ℕ) : ZMod GP) hord hpinv
      gninv_inv (Finset.Ico startU.val endU.val) (fun u => entryK GP a u)
      (fun u => entryK GP b u) t ht]
  congr 1
  rw [hscv, hlenv, ZMod.natCast_mod, Nat.cast_mul]

/-! ## Preparation

`PrepAtG` is stated over a `PreparedVecG`; the two-lane store keeps its
Goldilocks table in a differently named field, so the predicate is restated
over a bare table and `PrepAt` is reused unchanged for the Barrett lane. -/

/-- [`GoldDot.PrepAtG`] over a bare prepared table. -/
def PrepAtGV (pfwd : alloc.vec.Vec Std.U64) (a : alloc.vec.Vec ring.Rq) (n : ℕ) : Prop :=
  n * N ≤ pfwd.val.length
  ∧ (∀ u ∈ pfwd.val, u.val < GP)
  ∧ ∀ j, j < n → ∀ t, t < N →
      resK GP pfwd (j * N + t)
        = NttMath.difRun (((ntt.GOLD_PSI.val : ℕ) : ZMod GP) ^ 2) 10 1
            (NttMath.twistR ((ntt.GOLD_PSI.val : ℕ) : ZMod GP) (entryK GP a j)) t

/-- **Preparation in the two lanes.** Each lane is the preparation already
proved for it: the Goldilocks table by `prepare_one_gold_spec`, the Barrett
table by `prepare_one_spec` at `AUX_P1`. -/
theorem prepare_vec_ga_spec (a : alloc.vec.Vec ring.Rq) (nU : Std.Usize)
    (hawf : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (han : nU.val ≤ a.val.length) (hmax : nU.val * N ≤ Std.Usize.max) :
    ring.prepare_vec_ga a nU
      ⦃ z => z.len = nU ∧ PrepAtGV z.fwd_g a nU.val
             ∧ PrepAt z.fwd_a a nU.val ntt.AUX_P1 ntt.AUX_PSI1 ⦄ := by
  rw [ring.prepare_vec_ga]
  step with prepare_one_gold_spec a nU hawf han hmax as ⟨fg, hgl, hgc, hgv⟩
  have hpsi1 : (ntt.AUX_PSI1).val < (ntt.AUX_P1).val := by
    simp only [ntt.AUX_PSI1, ntt.AUX_P1]; decide +kernel
  step with prepare_one_spec a nU ntt.AUX_P1 ntt.AUX_M1 ntt.AUX_PSI1
    _ magic1 hpsi1 rfl hawf han hmax as ⟨fa, hal, hac, hav⟩
  exact ⟨show PrepAtGV fg a nU.val from ⟨le_of_eq hgl.symm, hgc, hgv⟩,
    le_of_eq hal.symm, hac, hav⟩

/-! ## The output loop

`RingFused.prep_garner_out_spec` with two residues instead of three and
`garner_ga` in place of `garner`; the Rust loops are otherwise the same. -/

theorem prep_garner_ga_out_spec (degU : Std.Usize) (qwU : Std.U128)
    (rg ra : alloc.vec.Vec Std.U64) (out : alloc.vec.Vec cpoly.field.Fp)
    (tU : Std.Usize) (X : ℕ → ℕ)
    (hdeg : degU.val = N) (hqwv : qwU.val = HachiEquiv.NttProduct.q)
    (hXP : ∀ k, k < N → X k < PGA)
    (hvg : ∀ k, k < N → wordAt rg k = X k % GP)
    (hva : ∀ k, k < N → wordAt ra k = X k % NttCRT.p1)
    (hlg : rg.val.length = N) (hla : ra.val.length = N)
    (ht : tU.val ≤ N) (hlen : out.val.length = tU.val)
    (hred : ∀ u ∈ out.val, HachiEquiv.Field.Red u)
    (hval : ∀ k, k < tU.val →
      HachiEquiv.Ring.wordN out k = X k % HachiEquiv.NttProduct.q) :
    ring.dot_prepared_ga_loop0_loop0 degU qwU rg ra out tU
      ⦃ z => HachiEquiv.Ring.Wf z ∧ ∀ k, k < N →
          HachiEquiv.Ring.wordN z k = X k % HachiEquiv.NttProduct.q ⦄ := by
  rw [ring.dot_prepared_ga_loop0_loop0]
  apply loop.spec_decr_nat (fun r => N - r.2.val)
    (fun r => r.2.val ≤ N ∧ r.1.val.length = r.2.val
      ∧ (∀ u ∈ r.1.val, HachiEquiv.Field.Red u)
      ∧ ∀ k, k < r.2.val →
          HachiEquiv.Ring.wordN r.1 k = X k % HachiEquiv.NttProduct.q)
  · rintro ⟨o1, tt⟩ ⟨htt, hlen1, hred1, hval1⟩
    dsimp only at htt hlen1 hred1 hval1
    simp only [ring.dot_prepared_ga_loop0_loop0.body]
    by_cases hlt : tt < degU
    · rw [if_pos hlt]
      have httlt : tt.val < N := by rw [← hdeg]; scalar_tac
      have hbg : tt.val < rg.val.length := by rw [hlg]; exact httlt
      have hba : tt.val < ra.val.length := by rw [hla]; exact httlt
      step as ⟨xg, hxg⟩
      step as ⟨xa, hxa⟩
      have hxgv : xg.val = X tt.val % GP := by
        rw [hxg, ← wordAt_of_lt (v := rg) (t := tt.val) hbg]; exact hvg tt.val httlt
      have hxav : xa.val = X tt.val % NttCRT.p1 := by
        rw [hxa, ← wordAt_of_lt (v := ra) (t := tt.val) hba]; exact hva tt.val httlt
      step with garner_ga_spec xg xa (X tt.val) (hXP tt.val httlt)
        hxgv hxav as ⟨g, hgv⟩
      step as ⟨md, hmd⟩
      have hmdv : md.val = X tt.val % HachiEquiv.NttProduct.q := by
        rw [hmd, hgv, hqwv]
      have hmdlt : md.val < HachiEquiv.NttProduct.q := by
        rw [hmdv]; exact Nat.mod_lt _ (by norm_num [HachiEquiv.NttProduct.q])
      have hcast : lift (UScalar.cast .U64 md) ⦃ y => y.val = md.val ⦄ :=
        UScalar.cast_inBounds_spec .U64 md (by
          have hq : md.val < 4294967197 := by
            have := hmdlt; simpa [HachiEquiv.NttProduct.q] using this
          simp only [UScalar.max, UScalarTy.numBits]
          omega)
      step with hcast as ⟨w, hw⟩
      step with HachiEquiv.Field.fp_new_spec w as ⟨f, hfred, hfval⟩
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
          have hwlt : w.val < HachiEquiv.NttProduct.q := by rw [hw]; exact hmdlt
          have hfv : f.val = w.val := by
            have h1 := HachiEquiv.NttProduct.natCast_inj_of_lt
              (n := HachiEquiv.NttProduct.q) (x := f.val) (y := w.val) hfred hfval
            rwa [Nat.mod_eq_of_lt hwlt] at h1
          rw [hfv, hw, hmdv]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : tt.val = N := by rw [← hdeg]; scalar_tac
      exact ⟨⟨by rw [hlen1, heq], hred1⟩,
        fun k hk => hval1 k (by rw [heq]; exact hk)⟩
  · exact ⟨ht, hlen, hred, hval⟩

/-! ## The chunk, at word level

`RingFused.dot_prep_chunk_word_spec`'s conversion applied to the Goldilocks
lane: the `ZMod GP` statement read back as a residue of `offConvSum`. The
argument is the prime-independent one -- `offConvSum` is a natural number, its
cast agrees with the lane's value, and the lane's words are canonical -- so
only the offset identity is specific. -/

@[simp] theorem GOLD_BOFF_val :
    (ntt.GOLD_BOFF).val = HachiEquiv.NttProduct.BOUND % GP := by
  simp only [ntt.GOLD_BOFF, HachiEquiv.NttProduct.BOUND]; decide +kernel

set_option maxRecDepth 8192 in
theorem dot_prep_chunk_gold_word_spec (pfwd : alloc.vec.Vec Std.U64)
    (a b : alloc.vec.Vec ring.Rq) (startU endU : Std.Usize)
    (hpl : endU.val * N ≤ pfwd.val.length)
    (hpv : ∀ j, j < endU.val → ∀ t, t < N →
        resK GP pfwd (j * N + t)
          = NttMath.difRun ((((ntt.GOLD_PSI.val : ℕ) : ZMod GP)) ^ 2) 10 1
              (NttMath.twistR ((ntt.GOLD_PSI.val : ℕ) : ZMod GP) (entryK GP a j)) t)
    (hpc : ∀ u ∈ pfwd.val, u.val < GP)
    (hawf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbwf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbe : endU.val ≤ b.val.length)
    (hse : startU.val ≤ endU.val) (hwidth : endU.val ≤ 8192) :
    ring.dot_prep_chunk_gold pfwd b startU endU ntt.GOLD_BOFF
      ⦃ z => Canon GP z ∧ ∀ k, k < N → wordAt z k
              = offConvSum a b startU.val endU.val k % GP ⦄ := by
  have hppos : 0 < GP := GoldDot.GP_pos
  have hboffl : (ntt.GOLD_BOFF).val < GP := by
    rw [GOLD_BOFF_val]; exact Nat.mod_lt _ GoldDot.GP_pos
  apply spec_mono (dot_prep_chunk_gold_spec pfwd a b startU endU ntt.GOLD_BOFF
    hboffl hpl hpv hpc hbwf hbe hse hwidth)
  rintro z ⟨hcanon, hval⟩
  refine ⟨hcanon, ?_⟩
  intro k hk
  have hnb := negQ_sum_le a b startU.val endU.val k hawf hbwf
  have hle : (∑ u ∈ Finset.Ico startU.val endU.val,
        HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
             (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
      ≤ (∑ u ∈ Finset.Ico startU.val endU.val,
          HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
               (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
        + (endU.val - startU.val) * HachiEquiv.NttProduct.BOUND :=
    le_trans hnb (Nat.le_add_left _ _)
  have hoff : ((offConvSum a b startU.val endU.val k : ℕ) : ZMod GP)
      = ((∑ u ∈ Finset.Ico startU.val endU.val,
            HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                 (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod GP)
        + (((endU.val - startU.val) * HachiEquiv.NttProduct.BOUND : ℕ) : ZMod GP)
        - ((∑ u ∈ Finset.Ico startU.val endU.val,
            HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                 (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod GP) := by
    unfold offConvSum
    rw [Nat.cast_sub hle, Nat.cast_add]
  have hcast : ((wordAt z k : ℕ) : ZMod GP)
      = ((offConvSum a b startU.val endU.val k : ℕ) : ZMod GP) := by
    have h1 := hval k hk
    rw [resK] at h1
    rw [h1, hoff]
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
    rw [GOLD_BOFF_val, ZMod.natCast_mod]
    push_cast
    ring
  exact HachiEquiv.NttProduct.natCast_inj_of_lt (wordAt_lt hcanon hppos k) hcast
