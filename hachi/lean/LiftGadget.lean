/-
Card T45a: gadget contraction in the lifted witness's high-half row sum.

`c_row_sum_high` on the lazy `R^lin` representation walks row `i` band by
band and, wherever a run of entries is one ring element `f` times successive
field scalars `w_m`, pays one high-half product `f · Σ_m w_m ζ_m` instead of
one per entry. The identity behind it is **bilinearity** of the unreduced
`Zq[X]` product -- nothing about gadget digits, balanced reconstruction or
`Z_BOUND` enters:

  `Σ_m ((w_m · f) · ζ_m).coeff k = (f · Σ_m w_m · ζ_m).coeff k`.

This file holds the part of the proof that does not need `LiftProver`'s
carrier: the bilinearity lemmas (L1), the run-time structure check
`group_is_scaled` (L2), the witness recomposition `recompose` (L3), the two
weight tables and the zero accumulator. The product-carrying helpers
(`add_high_into`, `band_high`, `group_high`) and the lazy row sum are in
`LiftProver.lean`, which imports this file: they step through
`long_mul_high_spec`, which lives there.

Nothing here assumes any structure of the blocks. `group_is_scaled_spec` says
what a `true` answer *means*; a `false` answer carries no information and the
caller falls back to the per-entry walk.
-/
import ZeroCheck

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.LiftGadget

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme
open HachiEquiv.ZeroCheck

/-! ## L1: bilinearity of the unreduced product -/

/-- Multiplying by a constant does not reduce: the representative of
`constRq c * x` is `C c * x.1`. -/
theorem constRq_mul_val (c : ZMod q) (x : Rq Φ) :
    (Rq.constRq Φ c * x).1 = CPolynomial.C c * x.1 := by
  rw [CPolynomial.eq_iff_coeff]
  intro k
  rw [Rq.constRq_mul_coeff Φ (by rw [phi_natDegree]; norm_num), CPolynomial.coeff_C_mul]

/-- A scalar on the left factor comes out of every coefficient of the product. -/
theorem coeff_constRq_mul_left (c : ZMod q) (f ζ : Rq Φ) (k : ℕ) :
    ((Rq.constRq Φ c * f).1 * ζ.1).coeff k = c * (f.1 * ζ.1).coeff k := by
  rw [constRq_mul_val, mul_assoc, CPolynomial.coeff_C_mul]

/-- A scalar on the right factor comes out too. -/
theorem coeff_mul_constRq_right (c : ZMod q) (f ζ : Rq Φ) (k : ℕ) :
    (f.1 * (Rq.constRq Φ c * ζ).1).coeff k = c * (f.1 * ζ.1).coeff k := by
  rw [constRq_mul_val, mul_left_comm, CPolynomial.coeff_C_mul]

/-- The right factor's sum distributes over every coefficient of the product. -/
theorem coeff_mul_sum_right {ι : Type} (f : Rq Φ) (s : Finset ι) (g : ι → Rq Φ) (k : ℕ) :
    (f.1 * (∑ i ∈ s, g i).1).coeff k = ∑ i ∈ s, (f.1 * (g i).1).coeff k := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Rq.zero_val, mul_zero,
      CPolynomial.coeff_zero]
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, Rq.add_val, mul_add, CPolynomial.coeff_add, ih]

/-- **The contraction identity.** A run of entries `c_m · f` against witness
entries `g_m` has, at every coefficient of the unreduced product, the sum of
one product of `f` against the recomposed `Σ_m c_m · g_m`. -/
theorem sum_coeff_contract (f : Rq Φ) (c : ℕ → ZMod q) (g : ℕ → Rq Φ) (L k : ℕ) :
    ∑ m ∈ Finset.range L, ((Rq.constRq Φ (c m) * f).1 * (g m).1).coeff k
      = (f.1 * (∑ m ∈ Finset.range L, Rq.constRq Φ (c m) * g m).1).coeff k := by
  rw [coeff_mul_sum_right]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_constRq_mul_left, coeff_mul_constRq_right]

/-! ## The high-half partial row sum

What every accumulator in the lazy walk holds, relative to its start: the
coefficient `N + t` of `Σ_{lo ≤ j < hi} blk[j] · z[zoff + j]`, unreduced. -/

/-- Coefficient `N + t` of the unreduced `Σ_{j ∈ [lo, hi)} blk[j] · z[zoff + j]`,
summed coefficientwise. -/
def highSum (blk z : linalg.PolyVec) (zoff lo hi t : ℕ) : ZMod q :=
  ∑ j ∈ Finset.Ico lo hi, ((vecAt blk j).1 * (vecAt z (zoff + j)).1).coeff (N + t)

theorem highSum_self (blk z : linalg.PolyVec) (zoff lo t : ℕ) :
    highSum blk z zoff lo lo t = 0 := by
  simp [highSum]

theorem highSum_succ (blk z : linalg.PolyVec) (zoff lo j t : ℕ) (h : lo ≤ j) :
    highSum blk z zoff lo (j + 1) t
      = highSum blk z zoff lo j t + ((vecAt blk j).1 * (vecAt z (zoff + j)).1).coeff (N + t) := by
  unfold highSum
  rw [Finset.sum_Ico_succ_top h]

theorem highSum_consecutive (blk z : linalg.PolyVec) (zoff a b c t : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) :
    highSum blk z zoff a b t + highSum blk z zoff b c t = highSum blk z zoff a c t := by
  unfold highSum
  exact Finset.sum_Ico_consecutive _ hab hbc

/-- A whole group read through the contraction identity: if every entry
`base + m` of the group is the leader times `c m`, the group's contribution is
one product of the leader against the recomposed witness digits. -/
theorem highSum_contract (blk z : linalg.PolyVec) (zoff base g t : ℕ) (c : ℕ → ZMod q)
    (hs : ∀ m < g, vecAt blk (base + m) = Rq.constRq Φ (c m) * vecAt blk base) :
    highSum blk z zoff base (base + g) t
      = ((vecAt blk base).1 * (∑ m ∈ Finset.range g,
          Rq.constRq Φ (c m) * vecAt z (zoff + base + m)).1).coeff (N + t) := by
  unfold highSum
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left,
    ← sum_coeff_contract]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hs m (Finset.mem_range.mp hm), Nat.add_assoc]

/-- A group whose leader is zero and which passes the check contributes nothing. -/
theorem highSum_zero_group (blk z : linalg.PolyVec) (zoff base g t : ℕ) (c : ℕ → ZMod q)
    (hs : ∀ m < g, vecAt blk (base + m) = Rq.constRq Φ (c m) * vecAt blk base)
    (h0 : vecAt blk base = 0) :
    highSum blk z zoff base (base + g) t = 0 := by
  rw [highSum_contract blk z zoff base g t c hs, h0, Rq.zero_val, zero_mul,
    CPolynomial.coeff_zero]

/-! ## A lazy row, band by band

`blocksAt` (`ZeroCheck.lean`) is the matrix the seven blocks stand for. On a
fixed row it is one of five shapes, and each column band of that shape is
either a zero band or one block's row; `bandSum` is one band's share of the
row's high-half sum, and `blocks_row_split` cuts the row into its three
column bands. -/

/-- The high-half terms of row `i` of the block matrix over columns `[off, off + L)`. -/
def bandSum (b : ringswitch.RlinBlocks) (i : ℕ) (z : linalg.PolyVec) (off L t : ℕ) : ZMod q :=
  ∑ j ∈ Finset.range L, ((blocksAt b i (off + j)).1 * (vecAt z (off + j)).1).coeff (N + t)

theorem blocks_row_split (b : ringswitch.RlinBlocks) (i : ℕ) (z : linalg.PolyVec)
    (t cw ct cz : ℕ) :
    ∑ j ∈ Finset.range (cw + ct + cz), ((blocksAt b i j).1 * (vecAt z j).1).coeff (N + t)
      = bandSum b i z 0 cw t + bandSum b i z cw ct t + bandSum b i z (cw + ct) cz t := by
  rw [Finset.sum_range_add, Finset.sum_range_add]
  simp only [bandSum, zero_add]

/-- A band of zero entries contributes nothing. -/
theorem bandSum_zero (b : ringswitch.RlinBlocks) (i : ℕ) (z : linalg.PolyVec)
    (off L t : ℕ) (h : ∀ j < L, blocksAt b i (off + j) = 0) : bandSum b i z off L t = 0 := by
  unfold bandSum
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [h j (Finset.mem_range.mp hj), Rq.zero_val, zero_mul, CPolynomial.coeff_zero]

/-- A band that reads one block's row is that row's `highSum` against the
witness shifted to the band's offset. -/
theorem bandSum_eq (b : ringswitch.RlinBlocks) (i : ℕ) (z : linalg.PolyVec)
    (off L t : ℕ) (pv : linalg.PolyVec) (h : ∀ j < L, blocksAt b i (off + j) = vecAt pv j) :
    bandSum b i z off L t = highSum pv z off 0 L t := by
  unfold bandSum highSum
  rw [← Finset.range_eq_Ico]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [h j (Finset.mem_range.mp hj)]

/-! ### The five row shapes of `blocksAt` -/

theorem blocksAt_d {b : ringswitch.RlinBlocks} {i : ℕ} (h : i < b.d_rows.val) (j : ℕ) :
    blocksAt b i j = if j < b.cw.val then matAt b.d i j else 0 := by
  rw [blocksAt, if_pos h]

theorem blocksAt_b {b : ringswitch.RlinBlocks} {i : ℕ} (h1 : ¬ i < b.d_rows.val)
    (h2 : i < b.d_rows.val + b.b_rows.val) (j : ℕ) :
    blocksAt b i j = if j < b.cw.val then 0
      else if j < b.cw.val + b.ct.val then matAt b.bmat (i - b.d_rows.val) (j - b.cw.val)
      else 0 := by
  rw [blocksAt, if_neg h1, if_pos h2]

theorem blocksAt_gb {b : ringswitch.RlinBlocks} {i : ℕ}
    (h : i = b.d_rows.val + b.b_rows.val) (j : ℕ) :
    blocksAt b i j = if j < b.cw.val then vecAt b.g_b j else 0 := by
  rw [blocksAt, if_neg (by omega), if_neg (by omega), if_pos h]

theorem blocksAt_gc {b : ringswitch.RlinBlocks} {i : ℕ}
    (h : i = b.d_rows.val + b.b_rows.val + 1) (j : ℕ) :
    blocksAt b i j = if j < b.cw.val then vecAt b.g_c j
      else if j < b.cw.val + b.ct.val then 0
      else vecAt b.neg_jt_g_a (j - b.cw.val - b.ct.val) := by
  rw [blocksAt, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

theorem blocksAt_t {b : ringswitch.RlinBlocks} {i : ℕ}
    (h1 : ¬ i < b.d_rows.val + b.b_rows.val) (h2 : i ≠ b.d_rows.val + b.b_rows.val)
    (h3 : i ≠ b.d_rows.val + b.b_rows.val + 1) (j : ℕ) :
    blocksAt b i j = if j < b.cw.val then 0
      else if j < b.cw.val + b.ct.val then
        matAt b.tensor (i - b.d_rows.val - b.b_rows.val - 2) (j - b.cw.val)
      else matAt b.neg_aj (i - b.d_rows.val - b.b_rows.val - 2)
        (j - b.cw.val - b.ct.val) := by
  rw [blocksAt, if_neg (by omega), if_neg h1, if_neg h2, if_neg h3]

/-! ## Weight vectors -/

/-- Entry `m` of a weight vector, in `ZMod q`, total. -/
def wAt (w : alloc.vec.Vec cpoly.field.Fp) (m : ℕ) : ZMod q :=
  toK (w.val.getD m cpoly.field.Fp.ZERO)

/-- A weight vector with at least `len` reduced entries. -/
def WfWeights (len : ℕ) (w : alloc.vec.Vec cpoly.field.Fp) : Prop :=
  len ≤ w.val.length ∧ ∀ x ∈ w.val, Red x

theorem wAt_of_lt {w : alloc.vec.Vec cpoly.field.Fp} {m : ℕ} (h : m < w.val.length) :
    wAt w m = toK w.val[m] := by
  rw [wAt, List.getD_eq_getElem _ _ h]

/-! ## L2: the structure check -/

/-- The loop of `group_is_scaled`: a `true` flag after `m` turns means the
first `m` entries of the group are the leader scaled by their weights. -/
theorem group_is_scaled_loop_spec {kb : ℕ} (blk : linalg.PolyVec) (hblk : WfVec kb blk)
    (base len : Std.Usize) (w : alloc.vec.Vec cpoly.field.Fp) (hw : WfWeights len.val w)
    (hb : base.val + len.val ≤ kb) (f : ring.Rq) (hf : Wf f) (ok0 : Bool) (m : Std.Usize)
    (hm : m.val ≤ len.val)
    (hinv : ok0 = true → ∀ m' < m.val,
      vecAt blk (base.val + m') = Rq.constRq Φ (wAt w m') * toRq f) :
    ringswitch.group_is_scaled_loop blk base len w f ok0 m
      ⦃ r => r = true → ∀ m' < len.val,
          vecAt blk (base.val + m') = Rq.constRq Φ (wAt w m') * toRq f ⦄ := by
  rw [ringswitch.group_is_scaled_loop]
  apply loop.spec_decr_nat (fun s => len.val - s.2.val)
    (fun s => s.2.val ≤ len.val ∧ (s.1 = true → ∀ m' < s.2.val,
      vecAt blk (base.val + m') = Rq.constRq Φ (wAt w m') * toRq f))
  · rintro ⟨o1, m1⟩ ⟨hm1, hinv1⟩
    dsimp only at hm1 hinv1
    simp only [ringswitch.group_is_scaled_loop.body]
    by_cases hlt : m1 < len
    · rw [if_pos hlt]
      have hm1l : m1.val < len.val := by scalar_tac
      have hm1w : m1.val < w.val.length := by have := hw.1; omega
      step as ⟨c, hc⟩
      have hRc : Red c := by rw [hc]; exact hw.2 _ (List.getElem_mem hm1w)
      step with RqBridge.scalar_mul_spec f c hf hRc as ⟨want, hWwant, hwant⟩
      have hbm : base.val + m1.val < kb := by omega
      have hkb : kb ≤ Usize.max := by rw [← hblk.1]; exact blk.property
      step as ⟨i, hi⟩
      step with poly_vec_get_spec (k := kb) blk hblk i (by rw [hi]; exact hbm)
        as ⟨r, hWr, hr⟩
      step with RqBridge.equals_spec r want hWr hWwant as ⟨b, hbv⟩
      by_cases hbt : b = true
      · rw [if_pos hbt]
        step as ⟨m2, hm2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro ho m' hm'
        rw [hm2] at hm'
        by_cases hlast : m' = m1.val
        · subst hlast
          rw [← hi, ← hr, hbv.1 hbt, hwant, hc, ← wAt_of_lt hm1w]
        · exact hinv1 ho m' (by omega)
      · rw [if_neg hbt]
        step as ⟨m2, hm2⟩
        exact ⟨by scalar_tac, fun h => absurd h (by simp), by scalar_tac⟩
    · rw [if_neg hlt, WP.spec_ok]
      have heq : m1.val = len.val := by scalar_tac
      intro ho m' hm'
      exact hinv1 ho m' (by omega)
  · exact ⟨hm, hinv⟩

/-- **`group_is_scaled` means what it checks.** A `true` answer: every entry
`base + m` of the group, `m < len`, is the leader `blk[base]` times the
constant `w[m]`. `base < kb` because the leader is read unconditionally. -/
theorem group_is_scaled_spec {kb : ℕ} (blk : linalg.PolyVec) (hblk : WfVec kb blk)
    (base len : Std.Usize) (w : alloc.vec.Vec cpoly.field.Fp) (hw : WfWeights len.val w)
    (hb : base.val + len.val ≤ kb) (hbase : base.val < kb) :
    ringswitch.group_is_scaled blk base len w
      ⦃ r => r = true → ∀ m < len.val,
          vecAt blk (base.val + m) = Rq.constRq Φ (wAt w m) * vecAt blk base.val ⦄ := by
  rw [ringswitch.group_is_scaled]
  step with poly_vec_get_spec (k := kb) blk hblk base hbase as ⟨f, hWf, hf⟩
  rw [← hf]
  exact group_is_scaled_loop_spec blk hblk base len w hw hb f hWf true 0#usize (by simp)
    (by intro _ m' hm'; simp at hm')

/-! ## L3: recomposing the witness digits -/

/-- The loop of `recompose`. -/
theorem recompose_loop_spec {kz : ℕ} (z : linalg.PolyVec) (hz : WfVec kz z)
    (base len : Std.Usize) (w : alloc.vec.Vec cpoly.field.Fp) (hw : WfWeights len.val w)
    (hb : base.val + len.val ≤ kz) (acc : ring.Rq) (m : Std.Usize) (hacc : Wf acc)
    (hm : m.val ≤ len.val)
    (hval : toRq acc = ∑ m' ∈ Finset.range m.val,
      Rq.constRq Φ (wAt w m') * vecAt z (base.val + m')) :
    ringswitch.recompose_loop z base len w acc m
      ⦃ r => Wf r ∧ toRq r = ∑ m' ∈ Finset.range len.val,
          Rq.constRq Φ (wAt w m') * vecAt z (base.val + m') ⦄ := by
  rw [ringswitch.recompose_loop]
  apply loop.spec_decr_nat (fun s => len.val - s.2.val)
    (fun s => s.2.val ≤ len.val ∧ Wf s.1 ∧ toRq s.1 = ∑ m' ∈ Finset.range s.2.val,
      Rq.constRq Φ (wAt w m') * vecAt z (base.val + m'))
  · rintro ⟨a1, m1⟩ ⟨hm1, hW1, hv1⟩
    dsimp only at hm1 hW1 hv1
    simp only [ringswitch.recompose_loop.body]
    by_cases hlt : m1 < len
    · rw [if_pos hlt]
      have hm1l : m1.val < len.val := by scalar_tac
      have hm1w : m1.val < w.val.length := by have := hw.1; omega
      have hbm : base.val + m1.val < kz := by omega
      have hkz : kz ≤ Usize.max := by rw [← hz.1]; exact z.property
      step as ⟨i, hi⟩
      step with poly_vec_get_spec (k := kz) z hz i (by rw [hi]; exact hbm) as ⟨r, hWr, hr⟩
      step as ⟨c, hc⟩
      have hRc : Red c := by rw [hc]; exact hw.2 _ (List.getElem_mem hm1w)
      step with RqBridge.scalar_mul_spec r c hWr hRc as ⟨sc, hWsc, hsc⟩
      step with RqBridge.add_spec a1 sc hW1 hWsc as ⟨a2, hW2, ha2⟩
      step as ⟨m2, hm2⟩
      refine ⟨by scalar_tac, hW2, ?_, by scalar_tac⟩
      rw [ha2, hv1, hsc, hm2, Finset.sum_range_succ, hr, hi, hc, ← wAt_of_lt hm1w]
    · rw [if_neg hlt, WP.spec_ok]
      have heq : m1.val = len.val := by scalar_tac
      exact ⟨hW1, by rw [hv1, heq]⟩
  · exact ⟨hm, hacc, hval⟩

/-- **`recompose` is `Σ_m w[m] · z[base + m]`** in `Rq Φ`. -/
theorem recompose_spec {kz : ℕ} (z : linalg.PolyVec) (hz : WfVec kz z)
    (base len : Std.Usize) (w : alloc.vec.Vec cpoly.field.Fp) (hw : WfWeights len.val w)
    (hb : base.val + len.val ≤ kz) :
    ringswitch.recompose z base len w
      ⦃ r => Wf r ∧ toRq r = ∑ m ∈ Finset.range len.val,
          Rq.constRq Φ (wAt w m) * vecAt z (base.val + m) ⦄ := by
  rw [ringswitch.recompose]
  step with RqBridge.zero_spec as ⟨a0, hW0, h0⟩
  exact recompose_loop_spec z hz base len w hw hb a0 0#usize hW0 (by simp)
    (by rw [h0]; simp)

/-! ## The weight tables

Only their shape matters to the proof -- the contraction is sound for *any*
weights, since `group_is_scaled` checks the group against the very weights
`recompose` uses -- but the values are cheap and stated for the record. -/

/-- The loop of `gadget_weights`. -/
theorem gadget_weights_loop_spec (digits : Std.Usize) (w : alloc.vec.Vec cpoly.field.Fp)
    (e : Std.Usize) (he : e.val ≤ digits.val) (hlen : w.val.length = e.val)
    (hred : ∀ x ∈ w.val, Red x) (hval : ∀ m < e.val, wAt w m = (16 : ZMod q) ^ m) :
    ringswitch.gadget_weights_loop digits w e
      ⦃ r => r.val.length = digits.val ∧ (∀ x ∈ r.val, Red x) ∧
          ∀ m < digits.val, wAt r m = (16 : ZMod q) ^ m ⦄ := by
  rw [ringswitch.gadget_weights_loop]
  apply loop.spec_decr_nat (fun (s : alloc.vec.Vec cpoly.field.Fp × Std.Usize) => digits.val - s.2.val)
    (fun (s : alloc.vec.Vec cpoly.field.Fp × Std.Usize) => s.2.val ≤ digits.val ∧
      s.1.val.length = s.2.val ∧ (∀ x ∈ s.1.val, Red x) ∧
      ∀ m < s.2.val, wAt s.1 m = (16 : ZMod q) ^ m)
  · rintro ⟨w1, e1⟩ ⟨he1, hl1, hr1, hv1⟩
    dsimp only at he1 hl1 hr1 hv1
    simp only [ringswitch.gadget_weights_loop.body]
    by_cases hlt : e1 < digits
    · rw [if_pos hlt]
      step with HachiEquiv.Scheme.base_pow_spec e1 as ⟨f, hRf, hf⟩
      step as ⟨w2, hw2⟩
      step as ⟨e2, he2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
      · rw [hw2, List.length_append, hl1, he2]; simp
      · intro x hx
        rw [hw2] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hr1 x h
        · rw [List.mem_singleton.mp h]; exact hRf
      · intro m hm
        rw [he2] at hm
        by_cases hml : m < e1.val
        · rw [← hv1 m hml, wAt, wAt, hw2, List.getD_append _ _ _ _ (by omega)]
        · have hme : m = e1.val := by omega
          subst hme
          rw [wAt, hw2, List.getD_append_right _ _ _ _ (by omega), hl1, Nat.sub_self]
          simpa using hf
    · rw [if_neg hlt, WP.spec_ok]
      have heq : e1.val = digits.val := by scalar_tac
      exact ⟨by rw [hl1, heq], hr1, fun m hm => hv1 m (by omega)⟩
  · exact ⟨he, hlen, hred, hval⟩

/-- `gadget_weights(d)` is `[b⁰, …, b^(d−1)]`, reduced. -/
theorem gadget_weights_spec (digits : Std.Usize) :
    ringswitch.gadget_weights digits
      ⦃ r => r.val.length = digits.val ∧ (∀ x ∈ r.val, Red x) ∧
          ∀ m < digits.val, wAt r m = (16 : ZMod q) ^ m ⦄ := by
  rw [ringswitch.gadget_weights]
  simp only [alloc.vec.Vec.with_capacity]
  exact gadget_weights_loop_spec digits _ 0#usize (by simp) (by simp)
    (by intro x hx; simp at hx) (by intro m hm; simp at hm)

/-- The shape `group_high` needs, from a weight table's spec. -/
theorem WfWeights_of_table {d : ℕ} {r : alloc.vec.Vec cpoly.field.Fp}
    (hl : r.val.length = d) (hr : ∀ x ∈ r.val, Red x) : WfWeights d r :=
  ⟨by rw [hl], hr⟩

/-- The loop of `jt_gadget_weights`. -/
theorem jt_gadget_weights_loop_spec (zd len : Std.Usize) (hzd : zd.val = 5)
    (w : alloc.vec.Vec cpoly.field.Fp)
    (m : Std.Usize) (hm : m.val ≤ len.val) (hlen : w.val.length = m.val)
    (hred : ∀ x ∈ w.val, Red x) :
    ringswitch.jt_gadget_weights_loop zd len w m
      ⦃ r => r.val.length = len.val ∧ ∀ x ∈ r.val, Red x ⦄ := by
  rw [ringswitch.jt_gadget_weights_loop]
  apply loop.spec_decr_nat (fun s => len.val - s.2.val)
    (fun s => s.2.val ≤ len.val ∧ s.1.val.length = s.2.val ∧ ∀ x ∈ s.1.val, Red x)
  · rintro ⟨w1, m1⟩ ⟨hm1, hl1, hr1⟩
    dsimp only at hm1 hl1 hr1
    simp only [ringswitch.jt_gadget_weights_loop.body]
    by_cases hlt : m1 < len
    · rw [if_pos hlt]
      step as ⟨e, he⟩
      step with HachiEquiv.Scheme.base_pow_spec e as ⟨hi, hRhi, _⟩
      step as ⟨e', he'⟩
      step with HachiEquiv.Scheme.base_pow_spec e' as ⟨lo, hRlo, _⟩
      step with HachiEquiv.Field.fp_mul_spec hi lo hRhi hRlo as ⟨f, hRf, _⟩
      step as ⟨w2, hw2⟩
      step as ⟨m2, hm2⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [hw2, List.length_append, hl1, hm2]; simp
      · intro x hx
        rw [hw2] at hx
        rcases List.mem_append.mp hx with h | h
        · exact hr1 x h
        · rw [List.mem_singleton.mp h]; exact hRf
    · rw [if_neg hlt, WP.spec_ok]
      have heq : m1.val = len.val := by scalar_tac
      exact ⟨by rw [hl1, heq], hr1⟩
  · exact ⟨hm, hlen, hred⟩

/-- `jt_gadget_weights()` has `GADGET_DIGITS · Z_DIGITS` reduced entries. -/
theorem jt_gadget_weights_spec :
    ringswitch.jt_gadget_weights
      ⦃ r => r.val.length = 40 ∧ ∀ x ∈ r.val, Red x ⦄ := by
  have h8 : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  have h5 : (params.Z_DIGITS).val = 5 := by simp [params.Z_DIGITS]
  rw [ringswitch.jt_gadget_weights]
  simp only [alloc.vec.Vec.with_capacity]
  step as ⟨len, hlen⟩
  have hlv : len.val = 40 := by rw [hlen, h8, h5]
  rw [← hlv]
  exact jt_gadget_weights_loop_spec params.Z_DIGITS len h5 _
    0#usize (by simp) (by simp) (by intro x hx; simp at hx)

/-! ## The zero accumulator -/

/-- The loop of `high_zeros`. -/
theorem high_zeros_loop_spec (n : Std.Usize) (hn : n.val = N)
    (acc : alloc.vec.Vec cpoly.field.Fp) (k : Std.Usize) (hk : k.val ≤ N - 1)
    (hacc : acc.val = List.replicate k.val cpoly.field.Fp.ZERO) :
    ringswitch.high_zeros_loop n acc k
      ⦃ z => z.val = List.replicate (N - 1) cpoly.field.Fp.ZERO ⦄ := by
  rw [ringswitch.high_zeros_loop]
  apply loop.spec_decr_nat (fun s => N - 1 - s.2.val)
    (fun s => s.2.val ≤ N - 1 ∧ s.1.val = List.replicate s.2.val cpoly.field.Fp.ZERO)
  · rintro ⟨o1, i1⟩ ⟨hi1, ho1⟩
    dsimp only at hi1 ho1
    simp only [ringswitch.high_zeros_loop.body]
    step as ⟨nm1, hnm1⟩
    have hnm1v : nm1.val = N - 1 := by rw [hnm1, hn]
    by_cases hlt : i1 < nm1
    · rw [if_pos hlt]
      have hlen : o1.val.length = i1.val := by rw [ho1, List.length_replicate]
      have hib : i1.val < N - 1 := by have := hlt; scalar_tac
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by omega, ?_, by omega⟩
      rw [ho2, hi2, ho1, List.replicate_succ']
    · rw [if_neg hlt, WP.spec_ok]
      show o1.val = List.replicate (N - 1) cpoly.field.Fp.ZERO
      have heq : i1.val = N - 1 := by scalar_tac
      rw [ho1, heq]
  · exact ⟨hk, hacc⟩

/-- `high_zeros()` is `N − 1` zero words. -/
theorem high_zeros_spec :
    ringswitch.high_zeros ⦃ z => z.val = List.replicate (N - 1) cpoly.field.Fp.ZERO ⦄ := by
  rw [ringswitch.high_zeros]
  step as ⟨nm1, hnm1⟩
  simp only [alloc.vec.Vec.with_capacity]
  exact high_zeros_loop_spec params.RING_DEGREE params_RING_DEGREE_val _ 0#usize
    (by simp) (by simp)

end HachiEquiv.LiftGadget
