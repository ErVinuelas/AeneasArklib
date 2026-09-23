/-
Cards T46a, T46a': the bucketed round-0 sumcheck, **proved**.

`round_poly_zero_base` walks the `2^k` pairs of the round-0 table and runs one
Taylor shift per pair. On the honest lifted witness every entry lies in the
digit alphabet `[-8, 15]`: the balanced digits of `ŵ`, `ẑ` and `ρ` are in
`[-8, 7]`, and the inner commitment's `t̂` is decomposed into *unsigned* base-16
digits `[0, 15]` (T46a bucketed over the balanced box `[-8, 7]` alone, which
missed `t̂`'s digits `8..15`, so the bucketed path never fired at the pin;
T46a' widens the alphabet). A digit `d` gets the id `d + 8 ∈ [0, 24)`, so a
pair `(w[2y], w[2y+1])` has one of only `24 · 24 = 576` types `24·i + j`,
padded to the power of two `1024`, and the sum regroups by type:

  `Σ_y eq[y] · P(fold w T y) = Σ_t b[t] · P(fold R T t)`,

with `b[t]` the summed `eq` weight of the pairs of type `t` and `R` the table
of the 1024 representative pairs. The Rust (`hachi/src/sumcheck.rs`, grep
T46a) computes `b` (`bucket_pairs_base`), `R` (`pair_type_table_base`) and
runs the old per-pair body (`round_poly_zero_base_plain`) on `(R, b)`: 1024
shifts in place of `2^25` at the pin. The `448` padding types `t ≥ 576` have
empty fibres, so weight `0`, and their representatives in `R` are immaterial.
Any entry outside the alphabet makes the bucketing return `None` and the
per-pair body runs on `(w, eq)` itself.

This file carries the new items' specs and the one identity the headline needs:

* `digId` / `typK`, the pure digit id and pair type, and `digit_id_spec`;
* `digId_toK`, the value lemma: a reduced word with digit id `< 24` *is* that
  digit, `toK x = digId x − 8`;
* `typK_parts`: a decoded pair has type `< 576`, read back by `/ 24`, `% 24`;
* `bucket_zero_fill_spec`, `bucket_loop_spec`, `bucket_pairs_base_spec`: on
  `some b`, `b` has 1024 reduced entries, every pair decodes, and
  `b[t] = Σ_{y : typK w y = t} eq[y]` (empty for the padding types);
* `pair_type_loop_spec`, `pair_type_table_base_spec`: 2048 reduced words,
  entry `2t` the value `t / 24 − 8` and entry `2t + 1` the value `t % 24 − 8`,
  for every `t < 1024` (past `576` these are padding values);
* `sum_fiberwise_fold`, the generic regrouping identity over any `P : F → F`,
  and `bucket_sum_eq`, its instance at the two tables the code builds.

`lean/Sumcheck.lean` states `round_poly_zero_base_spec` unchanged and proves it
from these and `round_poly_zero_base_plain_spec` (at `k := 10`: `2^10` types).
-/
import SumcheckShift

set_option linter.style.longLine false
set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly CompPoly.CPolynomial CompPoly.Extension ArkLib.Lattices
open ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.SumcheckBucket

open HachiEquiv.Field HachiEquiv.Ext HachiEquiv.Ring HachiEquiv.ZeroCheck
open HachiEquiv.SumcheckShift

/-! ## The constants -/

theorem digit_alphabet_val : (sumcheck.DIGIT_ALPHABET).val = 24 := by
  simp only [sumcheck.DIGIT_ALPHABET]; decide

theorem pair_types_val : (sumcheck.PAIR_TYPES).val = 1024 := by
  simp only [sumcheck.PAIR_TYPES]; decide

theorem q_minus_half_val : (sumcheck.Q_MINUS_HALF).val = 4294967189 := by
  simp only [sumcheck.Q_MINUS_HALF]; decide

theorem half_base_val : (params.HALF_BASE).val = 8 := by
  simp only [params.HALF_BASE]; decide

theorem gadget_base_val : (params.GADGET_BASE).val = 16 := by
  simp only [params.GADGET_BASE]; decide

theorem bucket_min_pairs0_val : (sumcheck.BUCKET_MIN_PAIRS0).val = 2048 := by
  simp only [sumcheck.BUCKET_MIN_PAIRS0]; decide

/-- A `u64` below `2 ^ 32` survives the cast to `usize` on either platform. -/
theorem cast_usize_small (x : Std.U64) (h : x.val < 2 ^ 32) :
    (UScalar.cast .Usize x).val = x.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have h32 : 32 ≤ UScalarTy.Usize.numBits := by
    rcases System.Platform.numBits_eq with h' | h' <;> simp [UScalarTy.numBits, h']
  calc x.val < 2 ^ 32 := h
    _ ≤ 2 ^ UScalarTy.Usize.numBits := Nat.pow_le_pow_right (by norm_num) h32

/-- `Usize.max` is at least `2^32 - 1`; a local copy, as `SumcheckShift` has. -/
private theorem usize_max_ge32 : (4294967295 : ℕ) ≤ Std.Usize.max := by
  rw [Std.Usize.max_def]
  rcases System.Platform.numBits_eq with h | h <;> simp [Std.Usize.numBits, h]

/-- The `usize → u64` cast of `pair_type_table_base` is lossless. -/
theorem cast_u64_spec (i : Std.Usize) :
    lift (UScalar.cast .U64 i) ⦃ y => y.val = i.val ⦄ :=
  UScalar.cast_inBounds_spec .U64 i (by
    have h1 : i.val ≤ Usize.max := by scalar_tac
    have h3 : UScalar.max UScalarTy.U64 = 18446744073709551615 := by
      simp [UScalar.max_def, UScalarTy.numBits]
    have h2 : Usize.max ≤ 18446744073709551615 := by
      rw [Usize.max_def]
      rcases System.Platform.numBits_eq with h | h <;> simp [Usize.numBits, h]
    omega)

/-! ## Digit ids and pair types -/

/-- The digit id of a word: `d + 8` for the canonical word of a digit
`d ∈ [-8, 15]` (`v < 16` is `d = v`, `v ≥ q − 8` is `d = v − q`), and the
sentinel `24` for any other word. -/
def digId (x : cpoly.field.Fp) : ℕ :=
  if x.val < 16 then x.val + 8
  else if 4294967189 ≤ x.val then x.val - 4294967189 else 24

/-- The type of pair `y`: `24 · id(w[2y]) + id(w[2y + 1])`. -/
def typK (w : alloc.vec.Vec cpoly.field.Fp) (y : ℕ) : ℕ :=
  24 * digId (w.val.getD (2 * y) cpoly.field.Fp.ZERO)
    + digId (w.val.getD (2 * y + 1) cpoly.field.Fp.ZERO)

/-- `digit_id` computes `digId` on a reduced word. -/
theorem digit_id_spec (x : cpoly.field.Fp) (hx : Red x) :
    sumcheck.digit_id x ⦃ r => r.val = digId x ⦄ := by
  have hxq : x.val < 4294967197 := hx
  have hH := half_base_val
  have hQ := q_minus_half_val
  have hD := digit_alphabet_val
  have hG := gadget_base_val
  rw [sumcheck.digit_id]
  simp only [cpoly.field.Fp.to_u64, bind_tc_ok]
  by_cases h8 : x < params.GADGET_BASE
  · rw [if_pos h8]
    have h8v : x.val < 16 := by scalar_tac
    step as ⟨id, hid⟩
    rw [cast_usize_small id (by scalar_tac), hid, hH, digId, if_pos h8v]
  · rw [if_neg h8]
    have h8v : ¬ x.val < 16 := by scalar_tac
    by_cases hq : x >= sumcheck.Q_MINUS_HALF
    · rw [if_pos hq]
      have hqv : 4294967189 ≤ x.val := by scalar_tac
      step as ⟨id, hid⟩
      rw [cast_usize_small id (by scalar_tac), hid, hQ, digId, if_neg h8v,
        if_pos hqv]
    · have hqv : ¬ 4294967189 ≤ x.val := by scalar_tac
      rw [if_neg hq, WP.spec_ok, hD, digId, if_neg h8v, if_neg hqv]

/-- **The value lemma.** A reduced word whose digit id is in the alphabet is
the digit `id − 8`. -/
theorem digId_toK (x : cpoly.field.Fp) (hx : Red x) (h : digId x < 24) :
    toK x = ((digId x : ℕ) : ZMod q) - 8 := by
  have hxq : x.val < 4294967197 := hx
  unfold digId at h ⊢
  by_cases h8 : x.val < 16
  · rw [if_pos h8, toK]
    push_cast
    ring
  · rw [if_neg h8] at h ⊢
    by_cases hq : 4294967189 ≤ x.val
    · rw [if_pos hq, eq_sub_iff_add_eq, toK]
      have h8' : ((8 : ℕ) : ZMod q) = 8 := by norm_num
      rw [← h8', ← Nat.cast_add, ZMod.natCast_eq_natCast_iff']
      show (x.val + 8) % 4294967197 = (x.val - 4294967189) % 4294967197
      omega
    · rw [if_neg hq] at h
      omega

/-- A pair whose two ids are in the alphabet has type below `576 = 24²` (so a
real type, not one of the `1024 − 576` padding slots), with the two ids read
back as `typK / 24` and `typK % 24`. -/
theorem typK_parts (w : alloc.vec.Vec cpoly.field.Fp) (y : ℕ)
    (h1 : digId (w.val.getD (2 * y) cpoly.field.Fp.ZERO) < 24)
    (h2 : digId (w.val.getD (2 * y + 1) cpoly.field.Fp.ZERO) < 24) :
    typK w y < 576 ∧ typK w y / 24 = digId (w.val.getD (2 * y) cpoly.field.Fp.ZERO)
      ∧ typK w y % 24 = digId (w.val.getD (2 * y + 1) cpoly.field.Fp.ZERO) := by
  unfold typK
  refine ⟨by omega, by omega, by omega⟩

/-! ## `bucket_pairs_base` -/

/-- The zero fill: 1024 copies of `Ext4::ZERO`. -/
theorem bucket_zero_fill_spec (b : alloc.vec.Vec cpoly.field.Ext4) (t0 : Std.Usize)
    (ht : t0.val ≤ 1024) (hlen : b.val.length = t0.val) (hbr : VecReduced b)
    (hbv : ∀ t, t < t0.val → toExt (b.val.getD t cpoly.field.Ext4.ZERO) = 0) :
    sumcheck.bucket_pairs_base_loop0 b t0
      ⦃ z => z.val.length = 1024 ∧ VecReduced z ∧
          ∀ t, t < 1024 → toExt (z.val.getD t cpoly.field.Ext4.ZERO) = 0 ⦄ := by
  have hP := pair_types_val
  rw [sumcheck.bucket_pairs_base_loop0]
  apply loop.spec_decr_nat (fun r => 1024 - r.2.val)
    (fun r => r.2.val ≤ 1024 ∧ r.1.val.length = r.2.val ∧ VecReduced r.1
      ∧ ∀ t, t < r.2.val → toExt (r.1.val.getD t cpoly.field.Ext4.ZERO) = 0)
  · rintro ⟨a, ii⟩ ⟨hii, hal, har', hav'⟩
    dsimp only at hii hal har' hav'
    simp only [sumcheck.bucket_pairs_base_loop0.body]
    by_cases hlt : ii < sumcheck.PAIR_TYPES
    · rw [if_pos hlt]
      have hilt : ii.val < 1024 := by scalar_tac
      have hmax : a.val.length < Std.Usize.max := by
        have := usize_max_ge32; omega
      step as ⟨a1, ha1⟩
      step as ⟨ii1, hii1⟩
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · rw [ha1, hii1, List.length_append, hal]; simp
      · intro y hy
        rw [ha1] at hy
        rcases List.mem_append.mp hy with h | h
        · exact har' y h
        · rw [List.mem_singleton.mp h]; exact HachiEquiv.Ext.reduced_ZERO
      · intro t ht
        rw [hii1] at ht
        rcases Nat.lt_or_ge t ii.val with hc | hc
        · rw [ha1, HachiEquiv.GoldTransform.getD_append_lt' _ _ _ (by omega)]
          exact hav' t hc
        · have heq : t = a.val.length := by omega
          rw [heq, ha1, HachiEquiv.GoldTransform.getD_append_eq']
          exact HachiEquiv.Ext.toExt_ZERO
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ii.val = 1024 := by scalar_tac
      exact ⟨by rw [hal, heq], har', fun t ht => hav' t (by rw [heq]; exact ht)⟩
  · exact ⟨ht, hlen, hbr, hbv⟩

/-- The bucketing loop. On `some z`: 1024 reduced weights, every pair below
`half` decodes, and `z[t]` is the `eq` weight of the pairs of type `t`. -/
theorem bucket_loop_spec (w : alloc.vec.Vec cpoly.field.Fp)
    (eq : alloc.vec.Vec cpoly.field.Ext4) (half : Std.Usize)
    (b : alloc.vec.Vec cpoly.field.Ext4) (y : Std.Usize)
    (hhalf : half.val = eq.val.length) (hwl : w.val.length = 2 * eq.val.length)
    (hwr : ∀ a ∈ w.val, Red a) (her : VecReduced eq)
    (hy : y.val ≤ half.val) (hbl : b.val.length = 1024) (hbr : VecReduced b)
    (hdec : ∀ y', y' < y.val →
      digId (w.val.getD (2 * y') cpoly.field.Fp.ZERO) < 24
        ∧ digId (w.val.getD (2 * y' + 1) cpoly.field.Fp.ZERO) < 24)
    (hbv : ∀ t, t < 1024 → toExt (b.val.getD t cpoly.field.Ext4.ZERO)
      = ∑ y' ∈ (Finset.range y.val).filter (fun y' => typK w y' = t), eqF eq y') :
    sumcheck.bucket_pairs_base_loop1 w eq half b y
      ⦃ r => match r with
        | none => True
        | some z => z.val.length = 1024 ∧ VecReduced z ∧
            (∀ y', y' < half.val →
              digId (w.val.getD (2 * y') cpoly.field.Fp.ZERO) < 24
                ∧ digId (w.val.getD (2 * y' + 1) cpoly.field.Fp.ZERO) < 24) ∧
            ∀ t, t < 1024 → toExt (z.val.getD t cpoly.field.Ext4.ZERO)
              = ∑ y' ∈ (Finset.range half.val).filter (fun y' => typK w y' = t),
                  eqF eq y' ⦄ := by
  have hD := digit_alphabet_val
  rw [sumcheck.bucket_pairs_base_loop1]
  apply loop.spec_decr_nat (fun r => half.val - r.2.val)
    (fun r => r.2.val ≤ half.val ∧ r.1.val.length = 1024 ∧ VecReduced r.1
      ∧ (∀ y', y' < r.2.val →
          digId (w.val.getD (2 * y') cpoly.field.Fp.ZERO) < 24
            ∧ digId (w.val.getD (2 * y' + 1) cpoly.field.Fp.ZERO) < 24)
      ∧ ∀ t, t < 1024 → toExt (r.1.val.getD t cpoly.field.Ext4.ZERO)
          = ∑ y' ∈ (Finset.range r.2.val).filter (fun y' => typK w y' = t), eqF eq y')
  · rintro ⟨a, yy⟩ ⟨hyy, hal, har', hdec', hav'⟩
    dsimp only at hyy hal har' hdec' hav'
    simp only [sumcheck.bucket_pairs_base_loop1.body]
    by_cases hlt : yy < half
    · rw [if_pos hlt]
      have hylt : yy.val < eq.val.length := by rw [← hhalf]; scalar_tac
      have hb0 : 2 * yy.val < w.val.length := by rw [hwl]; omega
      have hb1 : 2 * yy.val + 1 < w.val.length := by rw [hwl]; omega
      step as ⟨i, hi⟩
      have hib : i.val < w.val.length := by rw [hi]; exact hb0
      step as ⟨f, hf⟩
      have hfv : f = w.val.getD (2 * yy.val) cpoly.field.Fp.ZERO := by
        rw [hf, ← hi, List.getD_eq_getElem _ _ hib]
      have hRf : Red f := by rw [hf]; exact hwr _ (List.getElem_mem hib)
      step with digit_id_spec f hRf as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      have hi2b : i2.val < w.val.length := by rw [hi2, hi]; exact hb1
      step as ⟨f1, hf1⟩
      have hf1v : f1 = w.val.getD (2 * yy.val + 1) cpoly.field.Fp.ZERO := by
        rw [hf1, show 2 * yy.val + 1 = i2.val by rw [hi2, hi], List.getD_eq_getElem _ _ hi2b]
      have hRf1 : Red f1 := by rw [hf1]; exact hwr _ (List.getElem_mem hi2b)
      step with digit_id_spec f1 hRf1 as ⟨j, hj⟩
      by_cases hc1 : i1 < sumcheck.DIGIT_ALPHABET
      · rw [if_pos hc1]
        by_cases hc2 : j < sumcheck.DIGIT_ALPHABET
        · rw [if_pos hc2]
          have hi1v : i1.val < 24 := by scalar_tac
          have hjv : j.val < 24 := by scalar_tac
          have hmul : sumcheck.DIGIT_ALPHABET.val * i1.val ≤ Std.Usize.max := by
            rw [hD]; have := usize_max_ge32; omega
          step as ⟨i3, hi3⟩
          have hi3v : i3.val = 24 * i1.val := by rw [hi3, hD]
          step as ⟨t, ht⟩
          have htv : t.val = typK w yy.val := by
            rw [ht, hi3v, hi1, hj, hfv, hf1v, typK]
          have htlt : t.val < 1024 := by rw [ht, hi3v]; omega
          have htb : t.val < a.val.length := by rw [hal]; exact htlt
          step as ⟨cur, hcur⟩
          have hRcur : Reduced cur := har' _ (by rw [hcur]; exact List.getElem_mem htb)
          step as ⟨e, he⟩
          have hRe : Reduced e := her _ (by rw [he]; exact List.getElem_mem hylt)
          step with HachiEquiv.Ext.ext_add_spec cur e hRcur hRe as ⟨e1, hRe1, he1⟩
          step as ⟨xa, back, hxa, hback⟩
          step as ⟨yy1, hyy1⟩
          have hset : back e1 = a.set t e1 := by rw [hback]
          have hyy1v : yy1.val = yy.val + 1 := by scalar_tac
          refine ⟨by scalar_tac, ?_, ?_, ?_, ?_, by scalar_tac⟩
          · rw [hset, alloc.vec.Vec.set_val_eq, List.length_set, hal]
          · intro u hu
            rw [hset, alloc.vec.Vec.set_val_eq] at hu
            rcases List.mem_or_eq_of_mem_set hu with h | h
            · exact har' u h
            · rw [h]; exact hRe1
          · intro y' hy'
            rw [hyy1v] at hy'
            rcases Nat.lt_or_ge y' yy.val with hc | hc
            · exact hdec' y' hc
            · have hye : y' = yy.val := by omega
              rw [hye, ← hfv, ← hf1v, ← hi1, ← hj]
              exact ⟨hi1v, hjv⟩
          · intro t' ht'
            have hold := hav' t' ht'
            rw [Finset.sum_filter] at hold
            rw [hset, alloc.vec.Vec.set_val_eq,
              List.getD_eq_getElem _ _ (by rw [List.length_set, hal]; exact ht'),
              hyy1v, Finset.sum_filter, Finset.sum_range_succ, ← hold]
            rcases eq_or_ne t' t.val with rfl | hne
            · rw [List.getElem_set_self, he1, if_pos htv.symm, hcur,
                List.getD_eq_getElem _ _ htb, he, eqF, List.getD_eq_getElem _ _ hylt]
            · rw [List.getElem_set_ne (by omega),
                ← List.getD_eq_getElem (l := a.val) (d := cpoly.field.Ext4.ZERO)
                  (by rw [hal]; exact ht'),
                if_neg (by omega), add_zero]
        · rw [if_neg hc2, WP.spec_ok]
          exact trivial
      · rw [if_neg hc1, WP.spec_ok]
        exact trivial
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hyeq : yy.val = half.val := by scalar_tac
      refine ⟨hal, har', fun y' hy' => hdec' y' (by omega), fun t ht => ?_⟩
      rw [hav' t ht, hyeq]
  · exact ⟨hy, hbl, hbr, hdec, hbv⟩

/-- `bucket_pairs_base`: `None`, or the 1024 pair-type weights of `(w, eq)`. -/
theorem bucket_pairs_base_spec (w : alloc.vec.Vec cpoly.field.Fp)
    (eq : alloc.vec.Vec cpoly.field.Ext4)
    (hwl : w.val.length = 2 * eq.val.length) (hwr : ∀ a ∈ w.val, Red a)
    (her : VecReduced eq) :
    sumcheck.bucket_pairs_base w eq
      ⦃ o => match o with
        | none => True
        | some b => b.val.length = 1024 ∧ VecReduced b ∧
            (∀ y, y < eq.val.length →
              digId (w.val.getD (2 * y) cpoly.field.Fp.ZERO) < 24
                ∧ digId (w.val.getD (2 * y + 1) cpoly.field.Fp.ZERO) < 24) ∧
            ∀ t, t < 1024 → toExt (b.val.getD t cpoly.field.Ext4.ZERO)
              = ∑ y' ∈ (Finset.range eq.val.length).filter (fun y' => typK w y' = t),
                  eqF eq y' ⦄ := by
  rw [sumcheck.bucket_pairs_base]
  simp only [alloc.vec.Vec.with_capacity]
  step with bucket_zero_fill_spec (alloc.vec.Vec.new cpoly.field.Ext4) 0#usize
    (by simp) (by simp) (by intro a ha; simp at ha) (by intro t ht; simp at ht)
    as ⟨b1, hb1l, hb1r, hb1v⟩
  have hhalf : (alloc.vec.Vec.len eq).val = eq.val.length := by simp
  apply spec_mono (bucket_loop_spec w eq (alloc.vec.Vec.len eq) b1 0#usize hhalf hwl hwr her
    (by simp) hb1l hb1r (by intro y' hy'; simp at hy')
    (by intro t ht; rw [hb1v t ht]; simp))
  rintro (_ | z) hz
  · exact trivial
  · obtain ⟨hzl, hzr, hzd, hzv⟩ := hz
    rw [hhalf] at hzd hzv
    exact ⟨hzl, hzr, hzd, hzv⟩

/-! ## `pair_type_table_base` -/

/-- The table loop: after `t` types, `2t` words, entry `2t'` the digit of id
`t' / 24` and entry `2t' + 1` that of id `t' % 24`. -/
theorem pair_type_loop_spec (out : alloc.vec.Vec cpoly.field.Fp) (eight : cpoly.field.Fp)
    (t : Std.Usize) (h8r : Red eight) (h8v : toK eight = 8) (ht : t.val ≤ 1024)
    (hlen : out.val.length = 2 * t.val) (hr : ∀ a ∈ out.val, Red a)
    (hv : ∀ t', t' < t.val →
      coeffK out (2 * t') = ((t' / 24 : ℕ) : ZMod q) - 8
        ∧ coeffK out (2 * t' + 1) = ((t' % 24 : ℕ) : ZMod q) - 8) :
    sumcheck.pair_type_table_base_loop out eight t
      ⦃ z => z.val.length = 2048 ∧ (∀ a ∈ z.val, Red a) ∧
          ∀ t', t' < 1024 →
            coeffK z (2 * t') = ((t' / 24 : ℕ) : ZMod q) - 8
              ∧ coeffK z (2 * t' + 1) = ((t' % 24 : ℕ) : ZMod q) - 8 ⦄ := by
  have hP := pair_types_val
  have hD := digit_alphabet_val
  rw [sumcheck.pair_type_table_base_loop]
  apply loop.spec_decr_nat (fun r => 1024 - r.2.val)
    (fun r => r.2.val ≤ 1024 ∧ r.1.val.length = 2 * r.2.val ∧ (∀ a ∈ r.1.val, Red a)
      ∧ ∀ t', t' < r.2.val →
          coeffK r.1 (2 * t') = ((t' / 24 : ℕ) : ZMod q) - 8
            ∧ coeffK r.1 (2 * t' + 1) = ((t' % 24 : ℕ) : ZMod q) - 8)
  · rintro ⟨o, tt⟩ ⟨htt, hol, hor, hov⟩
    dsimp only at htt hol hor hov
    simp only [sumcheck.pair_type_table_base_loop.body]
    by_cases hlt : tt < sumcheck.PAIR_TYPES
    · rw [if_pos hlt]
      have httv : tt.val < 1024 := by scalar_tac
      step as ⟨hi_id, hhi⟩
      step as ⟨lo_id, hlo⟩
      step with cast_u64_spec hi_id as ⟨i, hi⟩
      step with fp_new_spec i as ⟨f, hRf, hf⟩
      step with fp_sub_spec f eight hRf h8r as ⟨f1, hRf1, hf1⟩
      have hmax1 : o.val.length < Std.Usize.max := by
        have := usize_max_ge32; omega
      step as ⟨o1, ho1⟩
      step with cast_u64_spec lo_id as ⟨i1, hi1⟩
      step with fp_new_spec i1 as ⟨f2, hRf2, hf2⟩
      step with fp_sub_spec f2 eight hRf2 h8r as ⟨f3, hRf3, hf3⟩
      have ho1l : o1.val.length = 2 * tt.val + 1 := by
        rw [ho1, List.length_append, hol]; simp
      have hmax2 : o1.val.length < Std.Usize.max := by
        have := usize_max_ge32; omega
      step as ⟨o2, ho2⟩
      step as ⟨tt1, htt1⟩
      have htt1v : tt1.val = tt.val + 1 := by scalar_tac
      have hhiv : hi_id.val = tt.val / 24 := by rw [hhi, hD]
      have hlov : lo_id.val = tt.val % 24 := by rw [hlo, hD]
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · rw [ho2, List.length_append, ho1l, htt1v, List.length_singleton]; ring
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with h | h
        · rw [ho1] at h
          rcases List.mem_append.mp h with h' | h'
          · exact hor u h'
          · rw [List.mem_singleton.mp h']; exact hRf1
        · rw [List.mem_singleton.mp h]; exact hRf3
      · intro t' ht'
        rw [htt1v] at ht'
        rcases Nat.lt_or_ge t' tt.val with hc | hc
        · rw [coeffK_append_lt ho2 (by rw [ho1l]; omega),
            coeffK_append_lt ho2 (by rw [ho1l]; omega),
            coeffK_append_lt ho1 (by rw [hol]; omega),
            coeffK_append_lt ho1 (by rw [hol]; omega)]
          exact hov t' hc
        · have hte : t' = tt.val := by omega
          rw [hte]
          refine ⟨?_, ?_⟩
          · rw [coeffK_append_lt ho2 (by rw [ho1l]; omega),
              show 2 * tt.val = o.val.length by rw [hol], coeffK_append_eq ho1,
              hf1, hf, h8v, hi, hhiv]
          · rw [show 2 * tt.val + 1 = o1.val.length by rw [ho1l], coeffK_append_eq ho2,
              hf3, hf2, h8v, hi1, hlov]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : tt.val = 1024 := by scalar_tac
      exact ⟨by rw [hol, heq], hor, fun t' ht' => hov t' (by rw [heq]; exact ht')⟩
  · exact ⟨ht, hlen, hr, hv⟩

/-- `pair_type_table_base`: the 2048-word representative table. -/
theorem pair_type_table_base_spec :
    sumcheck.pair_type_table_base
      ⦃ v => v.val.length = 2048 ∧ (∀ a ∈ v.val, Red a) ∧
          ∀ t, t < 1024 →
            coeffK v (2 * t) = ((t / 24 : ℕ) : ZMod q) - 8
              ∧ coeffK v (2 * t + 1) = ((t % 24 : ℕ) : ZMod q) - 8 ⦄ := by
  have hP := pair_types_val
  have hH := half_base_val
  rw [sumcheck.pair_type_table_base]
  simp only [alloc.vec.Vec.with_capacity]
  step as ⟨i, hi⟩
  step with fp_new_spec params.HALF_BASE as ⟨eight, h8r, h8v⟩
  exact pair_type_loop_spec (alloc.vec.Vec.new cpoly.field.Fp) eight 0#usize h8r
    (by rw [h8v, hH]; norm_num) (by simp) (by simp) (by intro a ha; simp at ha)
    (by intro t' ht'; simp at ht')

/-! ## The regrouping -/

/-- **Fiberwise regrouping of a fold sum.** If every pair `y` of `W` equals
pair `typ y` of `R`, the `e`-weighted sum of any `P` of the fold regroups into
the sum over types of the fibre weights. -/
theorem sum_fiberwise_fold {k k' : ℕ} (W : Fin (2 ^ (k + 1)) → F)
    (R : Fin (2 ^ (k' + 1)) → F) (e : Fin (2 ^ k) → F) (P : F → F) (T : F)
    (typ : Fin (2 ^ k) → Fin (2 ^ k'))
    (hlo : ∀ y, W (lo y) = R (lo (typ y))) (hhi : ∀ y, W (hi y) = R (hi (typ y))) :
    ∑ y, e y * P (fold W T y)
      = ∑ t, (∑ y ∈ Finset.univ.filter (fun y => typ y = t), e y) * P (fold R T t) := by
  have hf : ∀ y, fold W T y = fold R T (typ y) := fun y => by rw [fold, fold, hlo, hhi]
  rw [← Finset.sum_fiberwise Finset.univ typ (fun y => e y * P (fold W T y))]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  rw [hf y, (Finset.mem_filter.mp hy).2]

/-- The regrouping at the two tables `bucket_pairs_base` and
`pair_type_table_base` build: the per-type sum over `(R, b)` is the per-pair
sum over `(w, eq)`, for any `P`. -/
theorem bucket_sum_eq {k : ℕ} (w v : alloc.vec.Vec cpoly.field.Fp)
    (eq b : alloc.vec.Vec cpoly.field.Ext4) (P : F → F) (x : F)
    (heql : eq.val.length = 2 ^ k) (hwl : w.val.length = 2 * eq.val.length)
    (hwr : ∀ a ∈ w.val, Red a)
    (hvv : ∀ t, t < 1024 →
      coeffK v (2 * t) = ((t / 24 : ℕ) : ZMod q) - 8
        ∧ coeffK v (2 * t + 1) = ((t % 24 : ℕ) : ZMod q) - 8)
    (hdec : ∀ y, y < eq.val.length →
      digId (w.val.getD (2 * y) cpoly.field.Fp.ZERO) < 24
        ∧ digId (w.val.getD (2 * y + 1) cpoly.field.Fp.ZERO) < 24)
    (hbv : ∀ t, t < 1024 → toExt (b.val.getD t cpoly.field.Ext4.ZERO)
      = ∑ y' ∈ (Finset.range eq.val.length).filter (fun y' => typK w y' = t), eqF eq y') :
    ∑ t : Fin (2 ^ 10), tableFn (m := 10) b t * P (fold (phiF ∘ tableFnFp (m := 10 + 1) v) x t)
      = ∑ y : Fin (2 ^ k),
          tableFn (m := k) eq y * P (fold (phiF ∘ tableFnFp (m := k + 1) w) x y) := by
  have hparts : ∀ y : Fin (2 ^ k), typK w y.val < 576
      ∧ typK w y.val / 24 = digId (w.val.getD (2 * y.val) cpoly.field.Fp.ZERO)
      ∧ typK w y.val % 24 = digId (w.val.getD (2 * y.val + 1) cpoly.field.Fp.ZERO) := by
    intro y
    obtain ⟨h1, h2⟩ := hdec y.val (by rw [heql]; exact y.isLt)
    exact typK_parts w y.val h1 h2
  have htyp : ∀ y : Fin (2 ^ k), typK w y.val < 2 ^ 10 := fun y =>
    (hparts y).1.trans (by norm_num)
  let typ : Fin (2 ^ k) → Fin (2 ^ 10) := fun y => ⟨typK w y.val, htyp y⟩
  have hred : ∀ n, n < w.val.length → Red (w.val.getD n cpoly.field.Fp.ZERO) := by
    intro n hn
    rw [List.getD_eq_getElem _ _ hn]
    exact hwr _ (List.getElem_mem hn)
  have hlo : ∀ y, (phiF ∘ tableFnFp (m := k + 1) w) (lo y)
      = (phiF ∘ tableFnFp (m := 10 + 1) v) (lo (typ y)) := by
    intro y
    show phiF (coeffK w (2 * y.val)) = phiF (coeffK v (2 * typK w y.val))
    have hy : y.val < eq.val.length := by rw [heql]; exact y.isLt
    obtain ⟨h1, _⟩ := hdec y.val hy
    obtain ⟨hlt, hdiv, _⟩ := hparts y
    rw [(hvv _ (by omega)).1, hdiv, coeffK,
      digId_toK _ (hred _ (by rw [hwl]; omega)) h1]
  have hhi : ∀ y, (phiF ∘ tableFnFp (m := k + 1) w) (hi y)
      = (phiF ∘ tableFnFp (m := 10 + 1) v) (hi (typ y)) := by
    intro y
    show phiF (coeffK w (2 * y.val + 1)) = phiF (coeffK v (2 * typK w y.val + 1))
    have hy : y.val < eq.val.length := by rw [heql]; exact y.isLt
    obtain ⟨_, h2⟩ := hdec y.val hy
    obtain ⟨hlt, _, hmod⟩ := hparts y
    rw [(hvv _ (by omega)).2, hmod, coeffK,
      digId_toK _ (hred _ (by rw [hwl]; omega)) h2]
  rw [sum_fiberwise_fold _ _ (tableFn (m := k) eq) P x typ hlo hhi]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have ht1024 : t.val < 1024 := t.isLt.trans_eq (by norm_num)
  have hfib : tableFn (m := 10) b t
      = ∑ y ∈ Finset.univ.filter (fun y => typ y = t), tableFn (m := k) eq y := by
    rw [tableFn_apply, hbv t.val ht1024, Finset.sum_filter, Finset.sum_filter, heql,
      ← Fin.sum_univ_eq_sum_range (fun y' => if typK w y' = t.val then eqF eq y' else 0) (2 ^ k)]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    show (if typK w y.val = t.val then eqF eq y.val else 0)
      = (if typ y = t then tableFn (m := k) eq y else 0)
    have hiff : typ y = t ↔ typK w y.val = t.val := Fin.ext_iff
    by_cases h : typK w y.val = t.val
    · rw [if_pos h, if_pos (hiff.mpr h), tableFn_apply, eqF]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]
  rw [hfib]

end HachiEquiv.SumcheckBucket
