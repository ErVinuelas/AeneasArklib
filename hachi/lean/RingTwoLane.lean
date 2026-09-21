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

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.RingTwoLane

open HachiEquiv.NttArith HachiEquiv.NttCRT HachiEquiv.GoldArith

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
