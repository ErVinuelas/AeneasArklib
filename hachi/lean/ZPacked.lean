/-
`ZPacked.lean` -- the fused z kernel on SWAR-packed digit lanes (Stage 6 card
T47): `quadeval::z_terms`, `z_spread`, `z_pass_lanes`, `z_apply_terms_lanes`,
`z_row_lanes`, `z_lane_decode`, `z_lane_flush` and `z_lane_zero`, the word
level of `honest_z_from_raw_32`'s short branch.

# What changed, and what did not

Card T43 made the short branch read each coefficient of a message block once
and scatter its eight base-16 digits -- the eight *nibbles* of the word,
because the chain's decomposer is the unsigned one and every canonical word is
below `q < 2^32` -- into eight digit accumulators, one unreduced `u64` word per
digit per coefficient. Card T47 packs those eight accumulators, and a ninth
*record* lane, into three `u64` words of three 20-bit lanes each: slot
`(r, p)` -- message row `r`, coefficient `p` -- is the three words at
`3·(r·N + p)`, lane `e` sits in word `e / 3` at bit `20·(e % 3)`, and lane `8`
(word 2, bit 40) is the record.

A signed update `±dₑ` would borrow across lanes, so every pass adds `16 ± dₑ`
to lane `e`, and exactly `16` to the record -- whose "digit", the ninth nibble
of a word below `2^32`, is `0`. The value a lane carries is therefore read as a
*difference*, `lane_e − lane_8 = Σ ±dₑ` in `ZMod q` ([`laneD`]). The bound is
`31` per lane per pass, which the block loop's `Z_LANE_CHUNK` schedule keeps
below `2^20`, so a lane never carries into its neighbour: [`laneOf_add`] is the
file's one piece of bit arithmetic.

Nothing above the word level moves. The pure layer of `RingShort.lean` --
`applied`, `passed`, `termsSum`, `descCoeffW`, `sgn`, `srcOf`/`dstOf`,
`termsSum_eq_negConvF` -- is reused unchanged, and so are card T43's pinned
nibble lemma [`digitK_eq_nibble`], the digit polynomial [`digitRq`] and
[`coeff_toRq_mul_fin`]. What is new is:

* the packed-word layer -- [`pack3`], [`laneOf`], [`WB`] and the no-carry lemma;
* the slot layer -- [`slotIdx`], [`slotW`], [`lane`], [`laneD`], [`laneRq`] and
  the row frame [`FrameR`] -- in place of T43's regions;
* the per-lane pass invariant [`ProgL`] and its one-write lemma [`write_lane`]
  (T43's `write_one`, three writes a step where there were eight).

`honest_z_from_raw_32_spec`'s statement, in `QuadEvalProtocol.lean`, is carried
over verbatim; its proof is restated on the loop specs there, which end in the
theorems of this file.
-/
import RingShort
import Scheme
import Raw32

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.ZPacked

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme
open HachiEquiv.RingShort

/-! ## 1. The constants -/

@[simp, scalar_tac_simps] theorem z_lane_words_val : (quadeval.Z_LANE_WORDS).val = 3 := by
  simp only [quadeval.Z_LANE_WORDS]; decide

@[simp, scalar_tac_simps] theorem z_lane_1_val : (quadeval.Z_LANE_1).val = 1048576 := by
  simp only [quadeval.Z_LANE_1]; decide

@[simp, scalar_tac_simps] theorem z_lane_2_val : (quadeval.Z_LANE_2).val = 1099511627776 := by
  simp only [quadeval.Z_LANE_2]; decide

@[simp, scalar_tac_simps] theorem z_lane_mask_val : (quadeval.Z_LANE_MASK).val = 1048575 := by
  simp only [quadeval.Z_LANE_MASK]; decide

@[simp, scalar_tac_simps] theorem z_lane_bias_val :
    (quadeval.Z_LANE_BIAS).val = 17592202821648 := by
  simp only [quadeval.Z_LANE_BIAS]; decide

@[simp, scalar_tac_simps] theorem z_lane_chunk_val : (quadeval.Z_LANE_CHUNK).val = 32768 := by
  simp only [quadeval.Z_LANE_CHUNK]; decide

/-- `Usize.max` is at least `2^32 - 1` on either supported word size (a local
copy of `Scheme.usize_max_ge'`). -/
theorem usize_max_ge : (4294967295 : ℕ) ≤ Std.Usize.max := by
  rw [Std.Usize.max_def]
  rcases System.Platform.numBits_eq with h | h <;> simp [Std.Usize.numBits, h]

theorem u64_max_val : Std.U64.max = 18446744073709551615 := by
  simp only [Std.U64.max, Std.U64.numBits]; norm_num

/-! ## 2. Packed words

A word is three 20-bit lanes. [`laneOf_add`] is the no-carry argument: as long
as every lane stays below `2^20`, adding three lane increments to the word adds
them lanewise. -/

/-- Three lanes packed in one word: `a + b·2^20 + c·2^40`. -/
def pack3 (a b c : ℕ) : ℕ := a + b * 2 ^ 20 + c * 2 ^ 40

/-- Lane `m` of a word: bits `[20m, 20m + 20)`. -/
def laneOf (x m : ℕ) : ℕ := x / 2 ^ (20 * m) % 2 ^ 20

theorem laneOf_zero (x : ℕ) : laneOf x 0 = x % 1048576 := by
  unfold laneOf; norm_num

theorem laneOf_one (x : ℕ) : laneOf x 1 = x / 1048576 % 1048576 := by
  unfold laneOf; norm_num

theorem laneOf_two (x : ℕ) : laneOf x 2 = x / 1099511627776 % 1048576 := by
  unfold laneOf; norm_num

theorem laneOf_lt (x m : ℕ) : laneOf x m < 2 ^ 20 := Nat.mod_lt _ (by norm_num)

theorem pack3_lt {a b c : ℕ} (ha : a < 2 ^ 20) (hb : b < 2 ^ 20) (hc : c < 2 ^ 20) :
    pack3 a b c < 2 ^ 60 := by
  unfold pack3; norm_num at ha hb hc ⊢; omega

/-- The lanes of a packed word are what was packed. -/
theorem laneOf_pack3 {a b c : ℕ} (ha : a < 2 ^ 20) (hb : b < 2 ^ 20) (hc : c < 2 ^ 20) :
    laneOf (pack3 a b c) 0 = a ∧ laneOf (pack3 a b c) 1 = b ∧ laneOf (pack3 a b c) 2 = c := by
  rw [laneOf_zero, laneOf_one, laneOf_two]
  unfold pack3
  norm_num at ha hb hc ⊢
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- A word below `2^60` is the packing of its three lanes. -/
theorem pack3_laneOf {x : ℕ} (hx : x < 2 ^ 60) :
    x = pack3 (laneOf x 0) (laneOf x 1) (laneOf x 2) := by
  rw [laneOf_zero, laneOf_one, laneOf_two]
  unfold pack3
  norm_num at hx ⊢
  omega

/-- A word with nothing above lane `2` and every lane at most `b`. -/
def WB (x b : ℕ) : Prop := x < 2 ^ 60 ∧ ∀ m, m < 3 → laneOf x m ≤ b

theorem WB_mono {x b b' : ℕ} (h : WB x b) (hb : b ≤ b') : WB x b' :=
  ⟨h.1, fun m hm => le_trans (h.2 m hm) hb⟩

theorem WB_zero (b : ℕ) : WB 0 b :=
  ⟨by norm_num, fun m _ => by simp [laneOf]⟩

/-- **No carry.** Three lane increments of at most `31` added to a word whose
lanes are at most `b`, with `b + 31 < 2^20`, are added lanewise. -/
theorem laneOf_add (x b : ℕ) (A : ℕ → ℕ) (hx : WB x b) (hA : ∀ j, j < 3 → A j ≤ 31)
    (hb : b + 31 < 2 ^ 20) :
    WB (x + pack3 (A 0) (A 1) (A 2)) (b + 31)
      ∧ ∀ j, j < 3 → laneOf (x + pack3 (A 0) (A 1) (A 2)) j = laneOf x j + A j := by
  obtain ⟨hx60, hxl⟩ := hx
  have h0 := hxl 0 (by norm_num)
  have h1 := hxl 1 (by norm_num)
  have h2 := hxl 2 (by norm_num)
  have a0 := hA 0 (by norm_num)
  have a1 := hA 1 (by norm_num)
  have a2 := hA 2 (by norm_num)
  have hsum : x + pack3 (A 0) (A 1) (A 2)
      = pack3 (laneOf x 0 + A 0) (laneOf x 1 + A 1) (laneOf x 2 + A 2) := by
    conv_lhs => rw [pack3_laneOf hx60]
    unfold pack3; ring
  have hb' : b < 2 ^ 20 := by omega
  have l0 : laneOf x 0 + A 0 < 2 ^ 20 := by omega
  have l1 : laneOf x 1 + A 1 < 2 ^ 20 := by omega
  have l2 : laneOf x 2 + A 2 < 2 ^ 20 := by omega
  obtain ⟨e0, e1, e2⟩ := laneOf_pack3 l0 l1 l2
  rw [hsum]
  refine ⟨⟨pack3_lt l0 l1 l2, fun m hm => ?_⟩, fun j hj => ?_⟩
  · rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with h | h | h <;> subst h
    · rw [e0]; omega
    · rw [e1]; omega
    · rw [e2]; omega
  · rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with h | h | h <;> subst h
    · exact e0
    · exact e1
    · exact e2

/-! ## 3. The bias

A pass adds `BIAS + s` or `BIAS − s` to a word, `BIAS = 16` in every lane and
`s` the packed digits. Lanewise that is `16 ± dₑ` ([`addW`]), in `[1, 31]`. -/

/-- One lane's increment in a pass: `16 + d` for a positive contribution,
`16 − d` for a negative one. -/
def addW (pos : Bool) (d : ℕ) : ℕ := if pos then 16 + d else 16 - d

theorem addW_le (pos : Bool) {d : ℕ} (hd : d ≤ 15) : addW pos d ≤ 31 := by
  unfold addW; split <;> omega

/-- In `ZMod q` the increment is `16` plus the signed digit. -/
theorem addW_cast (pos : Bool) {d : ℕ} (hd : d ≤ 16) :
    ((addW pos d : ℕ) : ZMod q) = 16 + (if pos then 1 else -1) * ((d : ℕ) : ZMod q) := by
  unfold addW
  cases pos with
  | true => simp only [if_true]; push_cast; ring
  | false =>
    simp only [Bool.false_eq_true, if_false]
    rw [Nat.cast_sub hd]; push_cast; ring

theorem bias_add (a b c : ℕ) :
    17592202821648 + pack3 a b c = pack3 (16 + a) (16 + b) (16 + c) := by
  unfold pack3; norm_num; ring

theorem bias_sub {a b c : ℕ} (ha : a ≤ 16) (hb : b ≤ 16) (hc : c ≤ 16) :
    17592202821648 - pack3 a b c = pack3 (16 - a) (16 - b) (16 - c) := by
  unfold pack3; norm_num; omega

theorem pack3_le_bias {a b c : ℕ} (ha : a ≤ 16) (hb : b ≤ 16) (hc : c ≤ 16) :
    pack3 a b c ≤ 17592202821648 := by
  unfold pack3; norm_num; omega

/-- The low run's addend: `BIAS − s` for a negative term, `BIAS + s` for a
positive one. -/
theorem addend_lo_spec (negt : Bool) (s : Std.U64) {a b c : ℕ} (hs : s.val = pack3 a b c)
    (ha : a ≤ 15) (hb : b ≤ 15) (hc : c ≤ 15) :
    (if negt then quadeval.Z_LANE_BIAS - s else quadeval.Z_LANE_BIAS + s)
      ⦃ r => r.val = pack3 (addW (!negt) a) (addW (!negt) b) (addW (!negt) c) ⦄ := by
  have hle := pack3_le_bias (a := a) (b := b) (c := c) (by omega) (by omega) (by omega)
  rcases negt with _ | _
  · simp only [Bool.false_eq_true, if_false]
    have hadd : (quadeval.Z_LANE_BIAS).val + s.val ≤ Std.U64.max := by
      rw [z_lane_bias_val, hs, u64_max_val]; unfold pack3; norm_num; omega
    step as ⟨r, hr⟩
    rw [hr, z_lane_bias_val, hs, bias_add]
    rfl
  · simp only [if_true]
    have hsub : s.val ≤ (quadeval.Z_LANE_BIAS).val := by rw [z_lane_bias_val, hs]; exact hle
    step as ⟨r, hr⟩
    rw [hr, z_lane_bias_val, hs, bias_sub (by omega) (by omega) (by omega)]
    rfl

/-- The high run's addend: the sign flipped by the wrap. -/
theorem addend_hi_spec (negt : Bool) (s : Std.U64) {a b c : ℕ} (hs : s.val = pack3 a b c)
    (ha : a ≤ 15) (hb : b ≤ 15) (hc : c ≤ 15) :
    (if negt then quadeval.Z_LANE_BIAS + s else quadeval.Z_LANE_BIAS - s)
      ⦃ r => r.val = pack3 (addW negt a) (addW negt b) (addW negt c) ⦄ := by
  have hle := pack3_le_bias (a := a) (b := b) (c := c) (by omega) (by omega) (by omega)
  rcases negt with _ | _
  · simp only [Bool.false_eq_true, if_false]
    have hsub : s.val ≤ (quadeval.Z_LANE_BIAS).val := by rw [z_lane_bias_val, hs]; exact hle
    step as ⟨r, hr⟩
    rw [hr, z_lane_bias_val, hs, bias_sub (by omega) (by omega) (by omega)]
    rfl
  · simp only [if_true]
    have hadd : (quadeval.Z_LANE_BIAS).val + s.val ≤ Std.U64.max := by
      rw [z_lane_bias_val, hs, u64_max_val]; unfold pack3; norm_num; omega
    step as ⟨r, hr⟩
    rw [hr, z_lane_bias_val, hs, bias_add]
    rfl

/-! ## 4. Slots, lanes and the row frame

The accumulator is one `Vec Std.U64`; slot `(r, p)` is its three words at
`3·(r·N + p)`. Lane `e < 8` of the slot holds digit `e`'s biased sum, lane `8`
the record, and [`laneD`] their difference is the value. -/

/-- Index of word `l` of slot `(r, p)`. -/
def slotIdx (r p l : ℕ) : ℕ := 3 * (r * N + p) + l

/-- Two slot addresses coincide only when row, coefficient and word do. -/
theorem slot_index_inj {r r' p p' l l' : ℕ} (hp : p < N) (hp' : p' < N) (hl : l < 3)
    (hl' : l' < 3) (h : slotIdx r p l = slotIdx r' p' l') : r = r' ∧ p = p' ∧ l = l' := by
  have hN : N = 1024 := rfl
  unfold slotIdx at h
  rw [hN] at h hp hp'
  omega

theorem slotIdx_lt {r p l len : ℕ} (hp : p < N) (hl : l < 3)
    (hcap : 3 * ((r + 1) * N) ≤ len) : slotIdx r p l < len := by
  have hN : N = 1024 := rfl
  unfold slotIdx
  rw [hN] at hp hcap ⊢
  omega

/-- Word `l` of slot `(r, p)`. -/
def slotW (z : alloc.vec.Vec Std.U64) (r p l : ℕ) : ℕ := bufN z (slotIdx r p l)

theorem slotW_set_eq {buf : alloc.vec.Vec Std.U64} {tU : Std.Usize} {x : Std.U64}
    {r p l : ℕ} (ht : tU.val = slotIdx r p l) (hlt : tU.val < buf.val.length) :
    slotW (buf.set tU x) r p l = x.val := by
  unfold slotW; rw [← ht]; exact bufN_set_eq hlt

theorem slotW_set_ne {buf : alloc.vec.Vec Std.U64} {tU : Std.Usize} {x : Std.U64}
    {r p l : ℕ} (hne : slotIdx r p l ≠ tU.val) :
    slotW (buf.set tU x) r p l = slotW buf r p l := by
  unfold slotW; exact bufN_set_ne hne

/-- Lane `e` of slot `(r, p)`: word `e / 3`, bits `20·(e % 3)`. Lane `8` is the
record. -/
def lane (z : alloc.vec.Vec Std.U64) (r p e : ℕ) : ℕ := laneOf (slotW z r p (e / 3)) (e % 3)

/-- The value lane `e` of slot `(r, p)` carries: the lane less the record, in
`ZMod q`. -/
def laneD (z : alloc.vec.Vec Std.U64) (r p e : ℕ) : ZMod q :=
  ((lane z r p e : ℕ) : ZMod q) - ((lane z r p 8 : ℕ) : ZMod q)

/-- Digit `e`'s accumulator of row `r`, as a ring element. -/
def laneRq (z : alloc.vec.Vec Std.U64) (r e : ℕ) : Rq Φ :=
  Rq.ofFinCoeff Φ N (fun p => laneD z r p e)

/-- Words outside row `r0`'s slots agree. -/
def FrameR (buf z : alloc.vec.Vec Std.U64) (r0 : ℕ) : Prop :=
  ∀ t, (∀ p, p < N → ∀ l, l < 3 → t ≠ slotIdx r0 p l) → bufN z t = bufN buf t

theorem FrameR_refl (buf : alloc.vec.Vec Std.U64) (r0 : ℕ) : FrameR buf buf r0 :=
  fun _ _ => rfl

theorem FrameR_trans {a b c : alloc.vec.Vec Std.U64} {r0 : ℕ}
    (h1 : FrameR a b r0) (h2 : FrameR b c r0) : FrameR a c r0 :=
  fun t ht => by rw [h2 t ht, h1 t ht]

/-- The frame is preserved by a write inside one of the row's slots. -/
theorem FrameR_set {buf z : alloc.vec.Vec Std.U64} {r0 : ℕ} (h : FrameR buf z r0)
    {tU : Std.Usize} {x : Std.U64} {p l : ℕ} (hp : p < N) (hl : l < 3)
    (ht : tU.val = slotIdx r0 p l) : FrameR buf (z.set tU x) r0 := by
  intro t htn
  rw [bufN_set_ne (by intro hc; exact htn p hp l hl (by rw [hc, ht]))]
  exact h t htn

/-- Another row's slot is read unchanged through the frame. -/
theorem FrameR_slot {buf z : alloc.vec.Vec Std.U64} {r0 : ℕ} (h : FrameR buf z r0)
    {r p l : ℕ} (hr : r ≠ r0) (hp : p < N) (hl : l < 3) : slotW z r p l = slotW buf r p l := by
  unfold slotW
  apply h
  intro p' hp' l' hl' hc
  exact hr (slot_index_inj hp hp' hl hl' hc).1

theorem FrameR_laneRq {buf z : alloc.vec.Vec Std.U64} {r0 : ℕ} (h : FrameR buf z r0)
    {r : ℕ} (hr : r ≠ r0) (e : ℕ) (he : e < 8) : laneRq z r e = laneRq buf r e := by
  unfold laneRq
  refine ofFinCoeff_congr (fun p hp => ?_)
  unfold laneD lane
  rw [FrameR_slot h hr hp (by omega), FrameR_slot h hr hp (by norm_num)]

/-- A slot run of zeros is the zero ring element, lane by lane. -/
theorem laneRq_zero (buf : alloc.vec.Vec Std.U64) (r e : ℕ) (he : e < 8)
    (h : ∀ p, p < N → ∀ l, l < 3 → slotW buf r p l = 0) : laneRq buf r e = 0 := by
  unfold laneRq
  apply Subtype.ext
  rw [CompPoly.CPolynomial.eq_iff_coeff]
  intro k
  rw [Rq.ofFinCoeff_coeff Φ _ N_le_degree, Rq.zero_val, CompPoly.CPolynomial.coeff_zero]
  by_cases hk : k < N
  · rw [if_pos hk]
    unfold laneD lane
    rw [h k hk 2 (by norm_num), h k hk (e / 3) (by omega)]
    simp [laneOf]
  · rw [if_neg hk]

/-! ## 5. The digit polynomial, and the nibble lemma

The specification's `dd.digit c ⟨e, _⟩` is `(Nat.digits 16 c.val).getD e 0`
(`digitK`), and Mathlib's `Nat.getD_digits` says that is `c.val / 16^e % 16`.
For a canonical word `x < q` the value of `(x : ZMod q)` is `x` itself, so the
digit is the nibble. -/

/-- Digit `e` of each word of a word vector, as a coefficient function; `0`
past the end of the vector. -/
def nibW (words : alloc.vec.Vec Std.U64) (e : ℕ) : ℕ → ZMod q :=
  fun i => (((bufN words i / 16 ^ e) % 16 : ℕ) : ZMod q)

theorem nibW_of_ge (words : alloc.vec.Vec Std.U64) (e : ℕ) {i : ℕ}
    (hi : words.val.length ≤ i) : nibW words e i = 0 := by
  unfold nibW bufN
  rw [List.getD_eq_default _ _ hi]
  simp

/-- Digit `e` of each coefficient of a ring element, as a coefficient
function; `0` past `N`. -/
def nib (row : ring.Rq) (e : ℕ) : ℕ → ZMod q :=
  fun i => (((wordN row i / 16 ^ e) % 16 : ℕ) : ZMod q)

theorem nib_of_ge (row : ring.Rq) (hrow : Wf row) (e : ℕ) {i : ℕ} (hi : N ≤ i) :
    nib row e i = 0 := by
  unfold nib wordN
  rw [List.getD_eq_default _ _ (by rw [hrow.1]; exact hi)]
  simp

/-- The digit-`e` polynomial of a row: the ring element `gadget_decompose`
would have written at flat index `8r + e`, without writing it. -/
def digitRq (row : ring.Rq) (e : ℕ) : Rq Φ := Rq.ofFinCoeff Φ N (nib row e)

/-- **The pinned nibble lemma.** Every `e`, not only `e < 8`: past the eighth
nibble both sides are `0`, because `x < 2^32`. -/
theorem digitK_eq_nibble (x : ℕ) (hx : x < q) (e : ℕ) :
    digitK ((x : ℕ) : ZMod q) e = (((x / 16 ^ e) % 16 : ℕ) : ZMod q) := by
  unfold digitK
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.getD_digits _ _ (by norm_num)]

/-- `gadget::digit_at` at the word level: the digit is the nibble. The generic
`Scheme.digit_at_spec` is untouched; this is its instance on canonical words,
the form the fused kernel computes. -/
theorem digit_at_nibble_spec (c : cpoly.field.Fp) (e : Std.Usize) (hc : Red c)
    (he : e.val < 8) :
    gadget.digit_at c e ⦃ d => d.val = (c.val / 16 ^ e.val) % 16 ⦄ := by
  apply spec_mono (digit_at_spec c e hc he)
  rintro d ⟨hRd, hd⟩
  have hdv : (toK d).val = d.val := by
    simp only [toK, ZMod.val_natCast]; exact Nat.mod_eq_of_lt hRd
  have hnib : (c.val / 16 ^ e.val) % 16 < q := by
    have := Nat.mod_lt (c.val / 16 ^ e.val) (by norm_num : 0 < 16)
    unfold q; omega
  rw [← hdv, hd, dd_digit_eq, toK, digitK_eq_nibble c.val hc e.val, ZMod.val_natCast,
    Nat.mod_eq_of_lt hnib]

/-- `nibW` of a row's word vector is `nib` of the row. -/
theorem nibW_eq_nib (words : alloc.vec.Vec Std.U64) (row : ring.Rq) (hrow : Wf row)
    (hwl : words.val.length = N) (hwv : ∀ i, i < N → bufN words i = wordN row i)
    (e : ℕ) : nibW words e = nib row e := by
  funext i
  by_cases hi : i < N
  · unfold nibW nib; rw [hwv i hi]
  · rw [nibW_of_ge words e (by rw [hwl]; omega),
      nib_of_ge row hrow e (by omega)]

/-- `nib` of a well-formed row is the specification's digit of its
represented coefficient. -/
theorem nib_eq_digitK (row : ring.Rq) (hrow : Wf row) (e i : ℕ) :
    nib row e i = digitK ((toRq row).1.coeff i) e := by
  rw [toRq_coeff_eq_coeffK hrow, coeffK_eq_cast_wordN,
    digitK_eq_nibble (wordN row i) (wordN_lt hrow i) e]
  rfl

/-- **The digit polynomial is `gadget_decompose`'s block.** -/
theorem digitRq_eq_digitBlock (x : linalg.PolyVec) (r e : ℕ)
    (hx : Wf (x.val.getD r (alloc.vec.Vec.new cpoly.field.Fp))) :
    digitRq (x.val.getD r (alloc.vec.Vec.new cpoly.field.Fp)) e = digitBlock x r e := by
  unfold digitRq digitBlock
  exact ofFinCoeff_congr (fun t _ => nib_eq_digitK _ hx e t)

/-- The specification's decomposition, entrywise: entry `m` of
`gadgetDecompose Φ dd (toVec x)` is `digitBlock x (m / 8) (m % 8)`. The tail
of `gadget_decompose_spec`'s proof, as a lemma. -/
theorem gadgetDecompose_eq_digitBlock {rows : ℕ} (x : linalg.PolyVec) (m : Fin (rows * 8)) :
    gadgetDecompose Φ dd (toVec (k := rows) x) m = digitBlock x (m.val / 8) (m.val % 8) := by
  have hm : m.val < rows * 8 := m.isLt
  have he'lt : m.val % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hi'lt : m.val / 8 < rows := by omega
  have hfp : (finProdFinEquiv (⟨m.val / 8, hi'lt⟩, ⟨m.val % 8, he'lt⟩) : Fin (rows * 8))
      = m := by
    apply Fin.ext
    show m.val % 8 + 8 * (m.val / 8) = m.val
    omega
  have hgd : gadgetDecompose Φ dd (toVec (k := rows) x)
      (finProdFinEquiv (⟨m.val / 8, hi'lt⟩, ⟨m.val % 8, he'lt⟩))
      = Rq.ofFinCoeff Φ Φ.φ.natDegree
          (fun k => dd.digit ((toVec (k := rows) x ⟨m.val / 8, hi'lt⟩).1.coeff k)
            ⟨m.val % 8, he'lt⟩) :=
    gadgetDecomposeFun_apply Φ dd.digit (toVec (k := rows) x) _ _
  rw [hfp] at hgd
  rw [hgd, digitBlock, RqBridge.phi_natDegree]
  rfl

/-! ## 4. The lift: a product against an `ofFinCoeff`

`RqBridge.coeff_toRq_mul` needs both operands to be extracted vectors. The
digit polynomial never is one, so the same six lines are repeated with
`Rq.ofFinCoeff_coeff` on the right. -/

theorem coeff_toRq_mul_fin (a : ring.Rq) (ha : Wf a) (f : ℕ → ZMod q)
    (hf : ∀ i, N ≤ i → f i = 0) {k : ℕ} (hk : k < N) :
    (toRq a * Rq.ofFinCoeff Φ N f).1.coeff k = negConvF (coeffK a) f k := by
  have hfc : ∀ p : ℕ, (Rq.ofFinCoeff Φ N f).1.toPoly.coeff p = f p := by
    intro p
    rw [← CPolynomial.coeff_toPoly, Rq.ofFinCoeff_coeff Φ _ N_le_degree]
    by_cases hp : p < N
    · rw [if_pos hp]
    · rw [if_neg hp, hf p (by omega)]
  have hsum : ∀ m : ℕ,
      (∑ p ∈ Finset.antidiagonal m,
        (toRq a).1.toPoly.coeff p.1 * (Rq.ofFinCoeff Φ N f).1.toPoly.coeff p.2)
      = ∑ p ∈ Finset.antidiagonal m, coeffK a p.1 * f p.2 := by
    intro m
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← CPolynomial.coeff_toPoly, toRq_coeff_eq_coeffK ha, hfc]
  rw [mul_two_block _ _ hk, Polynomial.coeff_mul, Polynomial.coeff_mul, hsum, hsum, negConvF]


/-- Digit `e` of coefficient `i` of a row, in `ℕ`: what `z_spread` packs. -/
def nibN (row : ring.Rq) (e i : ℕ) : ℕ := wordN row i / 16 ^ e % 16

theorem nibN_le (row : ring.Rq) (e i : ℕ) : nibN row e i ≤ 15 :=
  Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))

/-- The ninth nibble of a canonical word is `0`: the record lane's "digit". -/
theorem nibN_eight (row : ring.Rq) (hrow : Wf row) (i : ℕ) : nibN row 8 i = 0 := by
  unfold nibN
  have h := wordN_lt hrow i
  have hq : q = 4294967197 := rfl
  rw [hq] at h
  rw [Nat.div_eq_of_lt (by norm_num; omega)]

/-- **A row's digit accumulator that gained the fused product, at the `Rq`
level.** If lane `e` of row `r` of `z` carries lane `e` of `buf` plus
`negConvF (coeffK ci) (nib row e)` coefficientwise, then as ring elements it
gained `toRq ci * digitRq row e`. -/
theorem laneRq_gain (z buf : alloc.vec.Vec Std.U64) (r : ℕ) (ci row : ring.Rq)
    (hci : Wf ci) (hrow : Wf row) (e : ℕ)
    (h : ∀ p, p < N → laneD z r p e = laneD buf r p e + negConvF (coeffK ci) (nib row e) p) :
    laneRq z r e = laneRq buf r e + toRq ci * digitRq row e := by
  apply Subtype.ext
  rw [CompPoly.CPolynomial.eq_iff_coeff]
  intro k
  rw [Rq.add_val, CompPoly.CPolynomial.coeff_add]
  unfold laneRq digitRq
  rw [Rq.ofFinCoeff_coeff Φ _ N_le_degree, Rq.ofFinCoeff_coeff Φ _ N_le_degree]
  by_cases hk : k < N
  · rw [if_pos hk, if_pos hk, h k hk,
      coeff_toRq_mul_fin ci hci (nib row e) (fun i hi => nib_of_ge row hrow e hi) hk]
  · rw [if_neg hk, if_neg hk, zero_add]
    exact (Rq.coeff_eq_zero_of_natDegree_le Φ (toRq ci * Rq.ofFinCoeff Φ N (nib row e))
      (by rw [phi_natDegree]; omega)).symm

/-! ## 6. `z_spread`: a row's digits, packed once

Word `l` of coefficient `i` is `pack3` of digits `3l, 3l + 1, 3l + 2`. Digit `8`
is `0` ([`nibN_eight`]), so word `2` is `d₆ + d₇·2^20` exactly as the Rust
writes it, and every word has the same shape. -/

/-- `src` holds, at `3i + l`, the packed digits `3l, 3l + 1, 3l + 2` of `D` at
coefficient `i`. -/
def SpreadOf (src : alloc.vec.Vec Std.U64) (D : ℕ → ℕ → ℕ) : Prop :=
  src.val.length = 3 * N ∧ ∀ i, i < N → ∀ l, l < 3 →
    bufN src (3 * i + l) = pack3 (D (3 * l) i) (D (3 * l + 1) i) (D (3 * l + 2) i)

theorem bufN_push_lt {v v' : alloc.vec.Vec Std.U64} {x : Std.U64} (h : v'.val = v.val ++ [x])
    {t : ℕ} (ht : t < v.val.length) : bufN v' t = bufN v t := by
  unfold bufN; rw [h, getD_append_lt _ _ _ ht]

theorem bufN_push_eq {v v' : alloc.vec.Vec Std.U64} {x : Std.U64} (h : v'.val = v.val ++ [x]) :
    bufN v' v.val.length = x.val := by
  unfold bufN; rw [h, getD_append_eq]

set_option maxHeartbeats 2000000 in
/-- The spread loop: coefficient by coefficient, three packed words each. -/
theorem z_spread_loop_spec (row : ring.Rq) (nU : Std.Usize) (out : alloc.vec.Vec Std.U64)
    (iU : Std.Usize) (hrow : Wf row) (hn : nU.val = N) (hi : iU.val ≤ N)
    (hlen : out.val.length = 3 * iU.val)
    (hval : ∀ i, i < iU.val → ∀ l, l < 3 → bufN out (3 * i + l)
      = pack3 (nibN row (3 * l) i) (nibN row (3 * l + 1) i) (nibN row (3 * l + 2) i)) :
    quadeval.z_spread_loop row nU out iU ⦃ z => SpreadOf z (nibN row) ⦄ := by
  rw [quadeval.z_spread_loop]
  apply loop.spec_decr_nat (fun t => nU.val - t.2.val)
    (fun t => t.2.val ≤ N ∧ t.1.val.length = 3 * t.2.val
      ∧ ∀ i, i < t.2.val → ∀ l, l < 3 → bufN t.1 (3 * i + l)
          = pack3 (nibN row (3 * l) i) (nibN row (3 * l + 1) i) (nibN row (3 * l + 2) i))
  · rintro ⟨ws, ii⟩ ⟨hii, hwl, hwv⟩
    dsimp only at hii hwl hwv
    simp only [quadeval.z_spread_loop.body]
    by_cases hlt : ii < nU
    · rw [if_pos hlt]
      have hiilt : ii.val < N := by rw [← hn]; scalar_tac
      step with Raw32.coeff_word_spec row ii hrow hiilt as ⟨f, hf⟩
      step with to_u64_id f as ⟨x, hx⟩
      have hxv : x.val = wordN row ii.val := by rw [hx, hf]; rfl
      step as ⟨d0, hd0⟩
      step as ⟨q1, hq1⟩
      step as ⟨d1, hd1⟩
      step as ⟨q2, hq2⟩
      step as ⟨d2, hd2⟩
      step as ⟨q3, hq3⟩
      step as ⟨d3, hd3⟩
      step as ⟨q4, hq4⟩
      step as ⟨d4, hd4⟩
      step as ⟨q5, hq5⟩
      step as ⟨d5, hd5⟩
      step as ⟨q6, hq6⟩
      step as ⟨d6, hd6⟩
      step as ⟨q7, hq7⟩
      step as ⟨d7, hd7⟩
      have hd0v : d0.val = nibN row 0 ii.val := by unfold nibN; rw [hd0, hxv]; simp
      have hd1v : d1.val = nibN row 1 ii.val := by unfold nibN; rw [hd1, hq1, hxv]; norm_num
      have hd2v : d2.val = nibN row 2 ii.val := by unfold nibN; rw [hd2, hq2, hxv]; norm_num
      have hd3v : d3.val = nibN row 3 ii.val := by unfold nibN; rw [hd3, hq3, hxv]; norm_num
      have hd4v : d4.val = nibN row 4 ii.val := by unfold nibN; rw [hd4, hq4, hxv]; norm_num
      have hd5v : d5.val = nibN row 5 ii.val := by unfold nibN; rw [hd5, hq5, hxv]; norm_num
      have hd6v : d6.val = nibN row 6 ii.val := by unfold nibN; rw [hd6, hq6, hxv]; norm_num
      have hd7v : d7.val = nibN row 7 ii.val := by unfold nibN; rw [hd7, hq7, hxv]; norm_num
      have hb1 := nibN_le row 1 ii.val
      have hb2 := nibN_le row 2 ii.val
      have hb4 := nibN_le row 4 ii.val
      have hb5 := nibN_le row 5 ii.val
      have hb7 := nibN_le row 7 ii.val
      have hb0 := nibN_le row 0 ii.val
      have hb3 := nibN_le row 3 ii.val
      have hb6 := nibN_le row 6 ii.val
      step as ⟨i8, hi8⟩
      step as ⟨i9, hi9⟩
      step as ⟨i10, hi10⟩
      step as ⟨s0, hs0⟩
      step as ⟨i11, hi11⟩
      step as ⟨i12, hi12⟩
      step as ⟨i13, hi13⟩
      step as ⟨s1, hs1⟩
      step as ⟨i14, hi14⟩
      step as ⟨s2, hs2⟩
      have hs0v : s0.val = pack3 (nibN row 0 ii.val) (nibN row 1 ii.val) (nibN row 2 ii.val) := by
        rw [hs0, hi9, hi10, hi8, z_lane_1_val, z_lane_2_val, hd0v, hd1v, hd2v]; unfold pack3; norm_num
      have hs1v : s1.val = pack3 (nibN row 3 ii.val) (nibN row 4 ii.val) (nibN row 5 ii.val) := by
        rw [hs1, hi12, hi13, hi11, z_lane_1_val, z_lane_2_val, hd3v, hd4v, hd5v]; unfold pack3; norm_num
      have hs2v : s2.val = pack3 (nibN row 6 ii.val) (nibN row 7 ii.val) (nibN row 8 ii.val) := by
        rw [hs2, hi14, z_lane_1_val, hd6v, hd7v, nibN_eight row hrow]; unfold pack3; norm_num
      have hmax : ws.val.length + 3 ≤ Std.Usize.max := by
        rw [hwl]; have := usize_max_ge; have h3 : N = 1024 := rfl; omega
      step as ⟨o1, ho1⟩
      have hl1 : o1.val.length = ws.val.length + 1 := by rw [ho1]; simp
      have hm1 : o1.val.length < Std.Usize.max := by omega
      step as ⟨o2, ho2⟩
      have hl2 : o2.val.length = ws.val.length + 2 := by rw [ho2, List.length_append, hl1]; simp
      have hm2 : o2.val.length < Std.Usize.max := by omega
      step as ⟨o3, ho3⟩
      step as ⟨ii1, hii1⟩
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [ho3, List.length_append, hl2, hwl, hii1]; simp; ring
      · intro i hi l hl
        rw [hii1] at hi
        rcases Nat.lt_or_ge i ii.val with hlt2 | hge
        · have hidx : 3 * i + l < ws.val.length := by rw [hwl]; omega
          rw [bufN_push_lt ho3 (by omega), bufN_push_lt ho2 (by omega), bufN_push_lt ho1 hidx]
          exact hwv i hlt2 l hl
        · have hieq : i = ii.val := by omega
          subst hieq
          rcases (show l = 0 ∨ l = 1 ∨ l = 2 by omega) with h | h | h <;> subst h
          · have h0 : 3 * ii.val + 0 = ws.val.length := by omega
            rw [h0, bufN_push_lt ho3 (by omega), bufN_push_lt ho2 (by omega), bufN_push_eq ho1,
              hs0v]
          · have h0 : 3 * ii.val + 1 = o1.val.length := by omega
            rw [h0, bufN_push_lt ho3 (by omega), bufN_push_eq ho2, hs1v]
          · have h0 : 3 * ii.val + 2 = o2.val.length := by omega
            rw [h0, bufN_push_eq ho3, hs2v]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ii.val = N := by rw [← hn]; scalar_tac
      exact ⟨by rw [hwl, heq], fun i hi l hl => hwv i (by rw [heq]; exact hi) l hl⟩
  · exact ⟨hi, hlen, hval⟩

/-- **`z_spread`.** The row's digits, packed three to a word, three words to a
coefficient. -/
theorem z_spread_spec (row : ring.Rq) (hrow : Wf row) :
    quadeval.z_spread row ⦃ src => SpreadOf src (nibN row) ⦄ := by
  rw [quadeval.z_spread]
  step as ⟨i, hi⟩
  simp only [alloc.vec.Vec.with_capacity]
  exact z_spread_loop_spec row params.RING_DEGREE (alloc.vec.Vec.new Std.U64) 0#usize hrow
    params_RING_DEGREE_val (by simp) (by simp) (by intro i hi; simp at hi)

/-! ## 7. `z_pass_lanes`: one signed pass over a row's slots

The invariant is per lane: lane `e` of slot `(r0, w)` has gained
`16 + sgn · Dₑ(srcOf k w)` once source index `srcOf k w` has been processed
([`appliedB`]). The record's digit `D 8` is `0`, so it gains exactly `16`, and
the difference [`laneD`] ends up with `applied`'s signed digit -- the same pure
function T43's regions and `short_pass_off` were proved against. -/

/-- `applied` with the bias: every processed position also gained `16`. -/
def appliedB (base sc : ℕ → ZMod q) (k : ℕ) (negt : Bool) (i : ℕ) : ℕ → ZMod q :=
  fun w => base w + (if srcOf k w < i then 16 + sgn negt k w * sc (srcOf k w) else 0)

theorem appliedB_succ (base sc : ℕ → ZMod q) (k : ℕ) (negt : Bool) (i w : ℕ) :
    appliedB base sc k negt (i + 1) w
      = appliedB base sc k negt i w
        + (if srcOf k w = i then 16 + sgn negt k w * sc (srcOf k w) else 0) := by
  unfold appliedB
  by_cases h : srcOf k w = i
  · rw [if_pos h, if_pos (by omega), if_neg (by omega)]; ring
  · by_cases h2 : srcOf k w < i
    · rw [if_neg h, if_pos (by omega), if_pos h2]; ring
    · rw [if_neg h, if_neg (by omega), if_neg h2]; ring

/-- A position whose source is not the current index does not move. -/
theorem appliedB_ite_skip (base sc : ℕ → ZMod q) (k : ℕ) (negt : Bool) {ii w : ℕ}
    (h : srcOf k w ≠ ii) (c : Prop) [Decidable c] :
    appliedB base sc k negt (if c then ii + 1 else ii) w = appliedB base sc k negt ii w := by
  by_cases hc : c
  · rw [if_pos hc, appliedB_succ, if_neg h, add_zero]
  · rw [if_neg hc]

theorem ite_src_skip {s ii : ℕ} (h : s ≠ ii) (c : Prop) [Decidable c] {α : Type} (X Y : α) :
    (if s < (if c then ii + 1 else ii) then X else Y) = (if s < ii then X else Y) := by
  by_cases hc : c
  · rw [if_pos hc]
    by_cases hs : s < ii
    · rw [if_pos hs, if_pos (by omega)]
    · rw [if_neg hs, if_neg (by omega)]
  · rw [if_neg hc]

/-- The digits of `D`, in `ZMod q`. -/
def dgZ (D : ℕ → ℕ → ℕ) (e : ℕ) : ℕ → ZMod q := fun i => ((D e i : ℕ) : ZMod q)

/-- **Progress through one step's three writes.** Words `l < m` of the step's
slot have absorbed source index `ii`, words `l ≥ m` have not; every other slot
is at `ii`. At `m = 0` this is the loop invariant at `ii`; at `m = 3` it is the
invariant at `ii + 1` ([`ProgL_three`]). -/
def ProgL (D : ℕ → ℕ → ℕ) (kk : ℕ) (negt : Bool) (r0 : ℕ) (base : ℕ → ℕ → ZMod q)
    (B ii m : ℕ) (z : alloc.vec.Vec Std.U64) : Prop :=
  ∀ p, p < N →
    (∀ l, l < 3 → WB (slotW z r0 p l)
        (if srcOf kk p < (if l < m then ii + 1 else ii) then B + 31 else B))
    ∧ ∀ e, e < 9 → ((lane z r0 p e : ℕ) : ZMod q)
        = appliedB (base e) (dgZ D e) kk negt (if e / 3 < m then ii + 1 else ii) p

theorem ProgL_three {D : ℕ → ℕ → ℕ} {kk : ℕ} {negt : Bool} {r0 : ℕ} {base : ℕ → ℕ → ZMod q}
    {B ii : ℕ} {z : alloc.vec.Vec Std.U64} (h : ProgL D kk negt r0 base B ii 3 z) :
    ProgL D kk negt r0 base B (ii + 1) 0 z := by
  intro p hp
  obtain ⟨hb, hv⟩ := h p hp
  refine ⟨fun l hl => ?_, fun e he => ?_⟩
  · have := hb l hl
    rw [if_pos hl] at this
    rw [if_neg (Nat.not_lt_zero l)]
    exact this
  · have := hv e he
    rw [if_pos (by omega)] at this
    rw [if_neg (Nat.not_lt_zero _)]
    exact this

/-- The step's current word is still within `B`. -/
theorem ProgL_cur {D : ℕ → ℕ → ℕ} {kk : ℕ} {negt : Bool} {r0 : ℕ} {base : ℕ → ℕ → ZMod q}
    {B ii m : ℕ} {d : alloc.vec.Vec Std.U64} (hprog : ProgL D kk negt r0 base B ii m d)
    (hk : kk < N) (hii : ii < N) (hm : m < 3) : WB (slotW d r0 (dstOf kk ii) m) B := by
  have := (hprog (dstOf kk ii) (dstOf_lt hk hii)).1 m hm
  rwa [if_neg (Nat.lt_irrefl m), srcOf_dstOf hk hii, if_neg (Nat.lt_irrefl ii)] at this

/-- **One write** of the three: word `m` of slot `(r0, dstOf kk ii)` gains the
biased signed digits, lanewise and without carry; every other word is
untouched. -/
theorem write_lane (D : ℕ → ℕ → ℕ) (kk : ℕ) (negt pos : Bool) (r0 : ℕ)
    (base : ℕ → ℕ → ZMod q) (B ii m : ℕ) (d : alloc.vec.Vec Std.U64)
    (wU : Std.Usize) (aU nvU : Std.U64)
    (hk : kk < N) (hii : ii < N) (hm : m < 3) (hB : B + 31 < 2 ^ 20)
    (hD : ∀ e i, D e i ≤ 15)
    (hpos : sgn negt kk (dstOf kk ii) = if pos then 1 else -1)
    (hprog : ProgL D kk negt r0 base B ii m d)
    (hwv : wU.val = slotIdx r0 (dstOf kk ii) m) (hwlt : wU.val < d.val.length)
    (hav : aU.val = pack3 (addW pos (D (3 * m) ii)) (addW pos (D (3 * m + 1) ii))
      (addW pos (D (3 * m + 2) ii)))
    (hnvv : nvU.val = slotW d r0 (dstOf kk ii) m + aU.val) :
    ProgL D kk negt r0 base B ii (m + 1) (d.set wU nvU) := by
  have hdst : dstOf kk ii < N := dstOf_lt hk hii
  have hsrc : srcOf kk (dstOf kk ii) = ii := srcOf_dstOf hk hii
  have hAle : ∀ j, j < 3 → (fun j => addW pos (D (3 * m + j) ii)) j ≤ 31 :=
    fun j _ => addW_le pos (hD _ _)
  have hav' : aU.val = pack3 ((fun j => addW pos (D (3 * m + j) ii)) 0)
      ((fun j => addW pos (D (3 * m + j) ii)) 1) ((fun j => addW pos (D (3 * m + j) ii)) 2) := by
    rw [hav]; simp only [Nat.add_zero]
  obtain ⟨hnewB, hnewL⟩ := laneOf_add _ B (fun j => addW pos (D (3 * m + j) ii))
    (ProgL_cur hprog hk hii hm) hAle hB
  intro p hp
  obtain ⟨hb, hv⟩ := hprog p hp
  by_cases hpd : p = dstOf kk ii
  · subst hpd
    refine ⟨fun l hl => ?_, fun e he => ?_⟩
    · by_cases hlm : l = m
      · subst hlm
        rw [slotW_set_eq hwv hwlt, hnvv, hav', if_pos (Nat.lt_succ_self l), hsrc,
          if_pos (Nat.lt_succ_self ii)]
        exact hnewB
      · rw [slotW_set_ne (by rw [hwv]; intro hc; exact hlm (slot_index_inj hp hp hl hm hc).2.2)]
        have := hb l hl
        by_cases hlt : l < m
        · rw [if_pos hlt] at this; rw [if_pos (show l < m + 1 by omega)]; exact this
        · rw [if_neg hlt] at this; rw [if_neg (show ¬ (l < m + 1) by omega)]; exact this
    · have hv' := hv e he
      unfold lane at hv' ⊢
      by_cases hem : e / 3 = m
      · rw [hem] at hv' ⊢
        rw [if_neg (Nat.lt_irrefl m)] at hv'
        rw [slotW_set_eq hwv hwlt, hnvv, hav', hnewL (e % 3) (Nat.mod_lt _ (by norm_num)),
          if_pos (Nat.lt_succ_self m), appliedB_succ, hsrc, if_pos rfl, Nat.cast_add, hv']
        have he3 : 3 * m + e % 3 = e := by omega
        simp only [he3]
        rw [addW_cast pos (by have := hD e ii; omega), hpos]
        rfl
      · rw [slotW_set_ne (by
          rw [hwv]; intro hc; exact hem (slot_index_inj hp hp (by omega) hm hc).2.2)]
        by_cases hlt : e / 3 < m
        · rw [if_pos hlt] at hv'; rw [if_pos (show e / 3 < m + 1 by omega)]; exact hv'
        · rw [if_neg hlt] at hv'; rw [if_neg (show ¬ (e / 3 < m + 1) by omega)]; exact hv'
  · have hne : ∀ l, l < 3 → slotIdx r0 p l ≠ wU.val := by
      intro l hl hc; rw [hwv] at hc; exact hpd (slot_index_inj hp hdst hl hm hc).2.1
    have hsne : srcOf kk p ≠ ii := by
      intro hc; exact hpd (by rw [← hc, dstOf_srcOf hk hp])
    refine ⟨fun l hl => ?_, fun e he => ?_⟩
    · rw [slotW_set_ne (hne l hl), ite_src_skip hsne]
      have := hb l hl
      rwa [ite_src_skip hsne] at this
    · have hv' := hv e he
      unfold lane at hv' ⊢
      rw [slotW_set_ne (hne _ (by omega)), hv', appliedB_ite_skip _ _ _ _ hsne,
        appliedB_ite_skip _ _ _ _ hsne]

/-- A `u64` add of two words below `2^60` does not overflow. -/
theorem add_ok {c a : ℕ} (hc : c < 2 ^ 60) (ha : a < 2 ^ 60) : c + a ≤ Std.U64.max := by
  rw [u64_max_val]; norm_num at hc ha ⊢; omega

theorem addend_lt (pos : Bool) {a b c : ℕ} (ha : a ≤ 15) (hb : b ≤ 15) (hc : c ≤ 15) :
    pack3 (addW pos a) (addW pos b) (addW pos c) < 2 ^ 60 := by
  have h1 := addW_le pos ha
  have h2 := addW_le pos hb
  have h3 := addW_le pos hc
  exact pack3_lt (by omega) (by omega) (by omega)

theorem set_length {buf : alloc.vec.Vec Std.U64} {tU : Std.Usize} {x : Std.U64} :
    (buf.set tU x).val.length = buf.val.length := by
  rw [alloc.vec.Vec.set_val_eq, List.length_set]

set_option maxHeartbeats 4000000 in
/-- **The low run** of `z_pass_lanes`: `i < N - k`, destination `k + i`, sign
`negt`'s alone. -/
theorem z_pass_lanes_loop0_spec (src : alloc.vec.Vec Std.U64) (kU : Std.Usize) (negt : Bool)
    (rbU limU : Std.Usize) (out : alloc.vec.Vec Std.U64) (iU : Std.Usize)
    (buf0 : alloc.vec.Vec Std.U64) (r0 : ℕ) (D : ℕ → ℕ → ℕ) (base : ℕ → ℕ → ZMod q) (B : ℕ)
    (hsrc : SpreadOf src D) (hD : ∀ e i, D e i ≤ 15)
    (hlim : limU.val = N - kU.val) (hk : kU.val < N) (hrb : rbU.val = 3 * (r0 * N))
    (hi : iU.val ≤ limU.val) (hlen : out.val.length = buf0.val.length)
    (hcap : 3 * ((r0 + 1) * N) ≤ buf0.val.length) (hB : B + 31 < 2 ^ 20)
    (hprog : ProgL D kU.val negt r0 base B iU.val 0 out) (hfr : FrameR buf0 out r0) :
    quadeval.z_pass_lanes_loop0 src kU negt rbU out limU iU
      ⦃ z => z.val.length = buf0.val.length ∧ ProgL D kU.val negt r0 base B limU.val 0 z
        ∧ FrameR buf0 z r0 ⦄ := by
  obtain ⟨hsl, hsv⟩ := hsrc
  rw [quadeval.z_pass_lanes_loop0]
  apply loop.spec_decr_nat (fun t => limU.val - t.2.val)
    (fun t => t.2.val ≤ limU.val ∧ t.1.val.length = buf0.val.length
      ∧ ProgL D kU.val negt r0 base B t.2.val 0 t.1 ∧ FrameR buf0 t.1 r0)
  · rintro ⟨d, ii⟩ ⟨hii, hdl, hdp, hdf⟩
    dsimp only at hii hdl hdp hdf
    simp only [quadeval.z_pass_lanes_loop0.body]
    by_cases hlt : ii < limU
    · rw [if_pos hlt]
      have hiilim : ii.val < limU.val := by scalar_tac
      have hiilt : ii.val < N := by omega
      have hnowrap : ¬ N ≤ kU.val + ii.val := by omega
      have hdst : dstOf kU.val ii.val = kU.val + ii.val := by
        unfold dstOf; rw [if_pos (by omega)]
      have hdstN : dstOf kU.val ii.val < N := dstOf_lt hk hiilt
      have hpos : sgn negt kU.val (dstOf kU.val ii.val) = if !negt then 1 else -1 := by
        rw [sgn_eq negt _ _ hk hiilt]
        unfold wrapped
        rw [decide_eq_false hnowrap]
        cases negt <;> simp
      have hcapd : 3 * ((r0 + 1) * N) ≤ d.val.length := by rw [hdl]; exact hcap
      have hdmax : d.val.length ≤ Std.Usize.max := d.property
      have hsl3 : 3 * ii.val + 2 < src.val.length := by rw [hsl]; omega
      have hw2lt : slotIdx r0 (dstOf kU.val ii.val) 2 < d.val.length :=
        slotIdx_lt hdstN (by norm_num) hcapd
      step as ⟨si, hsi⟩
      have hsiv : si.val = 3 * ii.val := by rw [hsi, z_lane_words_val]
      step as ⟨s0, hs0⟩
      step as ⟨i1, hi1⟩
      step as ⟨s1, hs1⟩
      step as ⟨i2, hi2⟩
      step as ⟨s2, hs2⟩
      have hs0v : s0.val = pack3 (D 0 ii.val) (D 1 ii.val) (D 2 ii.val) := by
        have h := hsv ii.val hiilt 0 (by norm_num)
        rw [hs0, ← bufN_of_lt (v := src) (w := si.val) (by omega), hsiv]
        simpa using h
      have hs1v : s1.val = pack3 (D 3 ii.val) (D 4 ii.val) (D 5 ii.val) := by
        have h := hsv ii.val hiilt 1 (by norm_num)
        rw [hs1, ← bufN_of_lt (v := src) (w := i1.val) (by omega), hi1, hsiv]
        simpa using h
      have hs2v : s2.val = pack3 (D 6 ii.val) (D 7 ii.val) (D 8 ii.val) := by
        have h := hsv ii.val hiilt 2 (by norm_num)
        rw [hs2, ← bufN_of_lt (v := src) (w := i2.val) (by omega), hi2, hsiv]
        simpa using h
      step with addend_lo_spec negt s0 hs0v (hD _ _) (hD _ _) (hD _ _) as ⟨a0, ha0⟩
      step with addend_lo_spec negt s1 hs1v (hD _ _) (hD _ _) (hD _ _) as ⟨a1, ha1⟩
      step with addend_lo_spec negt s2 hs2v (hD _ _) (hD _ _) (hD _ _) as ⟨a2, ha2⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      have hi4v : i4.val = 3 * (kU.val + ii.val) := by rw [hi4, hi3, z_lane_words_val]
      have hw0v' : rbU.val + i4.val = slotIdx r0 (dstOf kU.val ii.val) 0 := by
        rw [hrb, hi4v, hdst]; unfold slotIdx; ring
      have hw0max : rbU.val + i4.val ≤ Std.Usize.max := by
        have := slotIdx_lt hdstN (by norm_num : (0 : ℕ) < 3) hcapd
        rw [hw0v']; omega
      step as ⟨w0, hw0⟩
      have hwv0 : w0.val = slotIdx r0 (dstOf kU.val ii.val) 0 := by rw [hw0, hw0v']
      have hwv1' : w0.val + 1 = slotIdx r0 (dstOf kU.val ii.val) 1 := by
        rw [hwv0]; unfold slotIdx; ring
      have hwv2' : w0.val + 2 = slotIdx r0 (dstOf kU.val ii.val) 2 := by
        rw [hwv0]; unfold slotIdx; ring
      have hw1max : w0.val + 1 ≤ Std.Usize.max := by omega
      step as ⟨w1, hw1⟩
      have hw2max : w0.val + 2 ≤ Std.Usize.max := by omega
      step as ⟨w2, hw2⟩
      have hwv1 : w1.val = slotIdx r0 (dstOf kU.val ii.val) 1 := by rw [hw1, hwv1']
      have hwv2 : w2.val = slotIdx r0 (dstOf kU.val ii.val) 2 := by rw [hw2, hwv2']
      -- write 0
      have hwlt0 : w0.val < d.val.length := by
        rw [hwv0]; exact slotIdx_lt hdstN (by norm_num) hcapd
      step as ⟨c0, hc0⟩
      have hc0v : c0.val = slotW d r0 (dstOf kU.val ii.val) 0 := by
        unfold slotW; rw [hc0, ← bufN_of_lt (v := d) (w := w0.val) hwlt0, hwv0]
      have hov0 : c0.val + a0.val ≤ Std.U64.max := by
        rw [hc0v, ha0]
        exact add_ok (ProgL_cur hdp hk hiilt (by norm_num)).1
          (addend_lt _ (hD _ _) (hD _ _) (hD _ _))
      step as ⟨v0, hv0⟩
      step as ⟨xw0, back0, hxw0, hback0⟩
      rw [hback0]
      have hp1 := write_lane D kU.val negt (!negt) r0 base B ii.val 0 d w0 a0 v0 hk hiilt
        (by norm_num) hB hD hpos hdp hwv0 hwlt0 (by rw [ha0]) (by rw [hv0, hc0v])
      have hl1 : (d.set w0 v0).val.length = buf0.val.length := by rw [set_length, hdl]
      have hf1 : FrameR buf0 (d.set w0 v0) r0 := FrameR_set hdf hdstN (by norm_num) hwv0
      -- write 1
      have hwlt1 : w1.val < (d.set w0 v0).val.length := by
        rw [set_length, hwv1]; exact slotIdx_lt hdstN (by norm_num) hcapd
      step as ⟨c1, hc1⟩
      have hc1v : c1.val = slotW (d.set w0 v0) r0 (dstOf kU.val ii.val) 1 := by
        unfold slotW; rw [hc1, ← bufN_of_lt (v := d.set w0 v0) (w := w1.val) hwlt1, hwv1]
      have hov1 : c1.val + a1.val ≤ Std.U64.max := by
        rw [hc1v, ha1]
        exact add_ok (ProgL_cur hp1 hk hiilt (by norm_num)).1
          (addend_lt _ (hD _ _) (hD _ _) (hD _ _))
      step as ⟨v1, hv1⟩
      step as ⟨xw1, back1, hxw1, hback1⟩
      rw [hback1]
      have hp2 := write_lane D kU.val negt (!negt) r0 base B ii.val 1 (d.set w0 v0) w1 a1 v1
        hk hiilt (by norm_num) hB hD hpos hp1 hwv1 hwlt1 (by rw [ha1]) (by rw [hv1, hc1v])
      have hl2 : ((d.set w0 v0).set w1 v1).val.length = buf0.val.length := by
        rw [set_length, hl1]
      have hf2 : FrameR buf0 ((d.set w0 v0).set w1 v1) r0 :=
        FrameR_set hf1 hdstN (by norm_num) hwv1
      -- write 2
      have hwlt2 : w2.val < ((d.set w0 v0).set w1 v1).val.length := by
        rw [set_length, set_length, hwv2]; exact slotIdx_lt hdstN (by norm_num) hcapd
      step as ⟨c2, hc2⟩
      have hc2v : c2.val = slotW ((d.set w0 v0).set w1 v1) r0 (dstOf kU.val ii.val) 2 := by
        unfold slotW
        rw [hc2, ← bufN_of_lt (v := (d.set w0 v0).set w1 v1) (w := w2.val) hwlt2, hwv2]
      have hov2 : c2.val + a2.val ≤ Std.U64.max := by
        rw [hc2v, ha2]
        exact add_ok (ProgL_cur hp2 hk hiilt (by norm_num)).1
          (addend_lt _ (hD _ _) (hD _ _) (hD _ _))
      step as ⟨v2, hv2⟩
      step as ⟨xw2, back2, hxw2, hback2⟩
      have hmaxb : ii.val + 1 ≤ Std.Usize.max := by
        have := usize_max_ge; have h3 : N = 1024 := rfl; omega
      step as ⟨ii1, hii1⟩
      rw [hback2]
      have hp3 := write_lane D kU.val negt (!negt) r0 base B ii.val 2 ((d.set w0 v0).set w1 v1)
        w2 a2 v2 hk hiilt (by norm_num) hB hD hpos hp2 hwv2 hwlt2 (by rw [ha2])
        (by rw [hv2, hc2v])
      refine ⟨by omega, by rw [set_length, hl2], by rw [hii1]; exact ProgL_three hp3,
        FrameR_set hf2 hdstN (by norm_num) hwv2, by omega⟩
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ii.val = limU.val := by scalar_tac
      exact ⟨hdl, by rw [← heq]; exact hdp, hdf⟩
  · exact ⟨hi, hlen, hprog, hfr⟩

set_option maxHeartbeats 4000000 in
/-- **The high run** of `z_pass_lanes`: `j ≥ N - k`, every term wraps to
`j - lim` and carries the opposite sign. -/
theorem z_pass_lanes_loop1_spec (src : alloc.vec.Vec Std.U64) (negt : Bool)
    (rbU nU limU : Std.Usize) (out : alloc.vec.Vec Std.U64) (jU : Std.Usize)
    (buf0 : alloc.vec.Vec Std.U64) (r0 k : ℕ) (D : ℕ → ℕ → ℕ) (base : ℕ → ℕ → ZMod q) (B : ℕ)
    (hsrc : SpreadOf src D) (hD : ∀ e i, D e i ≤ 15)
    (hn : nU.val = N) (hlim : limU.val = N - k) (hk : k < N) (hrb : rbU.val = 3 * (r0 * N))
    (hj1 : limU.val ≤ jU.val) (hj2 : jU.val ≤ N) (hlen : out.val.length = buf0.val.length)
    (hcap : 3 * ((r0 + 1) * N) ≤ buf0.val.length) (hB : B + 31 < 2 ^ 20)
    (hprog : ProgL D k negt r0 base B jU.val 0 out) (hfr : FrameR buf0 out r0) :
    quadeval.z_pass_lanes_loop1 src negt rbU nU out limU jU
      ⦃ z => z.val.length = buf0.val.length ∧ ProgL D k negt r0 base B N 0 z
        ∧ FrameR buf0 z r0 ⦄ := by
  obtain ⟨hsl, hsv⟩ := hsrc
  rw [quadeval.z_pass_lanes_loop1]
  apply loop.spec_decr_nat (fun t => nU.val - t.2.val)
    (fun t => limU.val ≤ t.2.val ∧ t.2.val ≤ N ∧ t.1.val.length = buf0.val.length
      ∧ ProgL D k negt r0 base B t.2.val 0 t.1 ∧ FrameR buf0 t.1 r0)
  · rintro ⟨d, ii⟩ ⟨hjl, hii, hdl, hdp, hdf⟩
    dsimp only at hjl hii hdl hdp hdf
    simp only [quadeval.z_pass_lanes_loop1.body]
    by_cases hlt : ii < nU
    · rw [if_pos hlt]
      have hiilt : ii.val < N := by rw [← hn]; scalar_tac
      have hwrap : N ≤ k + ii.val := by omega
      have hdst : dstOf k ii.val = ii.val - limU.val := by
        unfold dstOf; rw [if_neg (by omega)]; omega
      have hdstN : dstOf k ii.val < N := dstOf_lt hk hiilt
      have hpos : sgn negt k (dstOf k ii.val) = if negt then 1 else -1 := by
        rw [sgn_eq negt _ _ hk hiilt]
        unfold wrapped
        rw [decide_eq_true hwrap]
        cases negt <;> simp
      have hcapd : 3 * ((r0 + 1) * N) ≤ d.val.length := by rw [hdl]; exact hcap
      have hdmax : d.val.length ≤ Std.Usize.max := d.property
      have hsl3 : 3 * ii.val + 2 < src.val.length := by rw [hsl]; omega
      have hw2lt : slotIdx r0 (dstOf k ii.val) 2 < d.val.length :=
        slotIdx_lt hdstN (by norm_num) hcapd
      step as ⟨si, hsi⟩
      have hsiv : si.val = 3 * ii.val := by rw [hsi, z_lane_words_val]
      step as ⟨s0, hs0⟩
      step as ⟨i1, hi1⟩
      step as ⟨s1, hs1⟩
      step as ⟨i2, hi2⟩
      step as ⟨s2, hs2⟩
      have hs0v : s0.val = pack3 (D 0 ii.val) (D 1 ii.val) (D 2 ii.val) := by
        have h := hsv ii.val hiilt 0 (by norm_num)
        rw [hs0, ← bufN_of_lt (v := src) (w := si.val) (by omega), hsiv]
        simpa using h
      have hs1v : s1.val = pack3 (D 3 ii.val) (D 4 ii.val) (D 5 ii.val) := by
        have h := hsv ii.val hiilt 1 (by norm_num)
        rw [hs1, ← bufN_of_lt (v := src) (w := i1.val) (by omega), hi1, hsiv]
        simpa using h
      have hs2v : s2.val = pack3 (D 6 ii.val) (D 7 ii.val) (D 8 ii.val) := by
        have h := hsv ii.val hiilt 2 (by norm_num)
        rw [hs2, ← bufN_of_lt (v := src) (w := i2.val) (by omega), hi2, hsiv]
        simpa using h
      step with addend_hi_spec negt s0 hs0v (hD _ _) (hD _ _) (hD _ _) as ⟨a0, ha0⟩
      step with addend_hi_spec negt s1 hs1v (hD _ _) (hD _ _) (hD _ _) as ⟨a1, ha1⟩
      step with addend_hi_spec negt s2 hs2v (hD _ _) (hD _ _) (hD _ _) as ⟨a2, ha2⟩
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      have hi4v : i4.val = 3 * (ii.val - limU.val) := by rw [hi4, hi3, z_lane_words_val]
      have hw0v' : rbU.val + i4.val = slotIdx r0 (dstOf k ii.val) 0 := by
        rw [hrb, hi4v, hdst]; unfold slotIdx; ring
      have hw0max : rbU.val + i4.val ≤ Std.Usize.max := by
        have := slotIdx_lt hdstN (by norm_num : (0 : ℕ) < 3) hcapd
        rw [hw0v']; omega
      step as ⟨w0, hw0⟩
      have hwv0 : w0.val = slotIdx r0 (dstOf k ii.val) 0 := by rw [hw0, hw0v']
      have hwv1' : w0.val + 1 = slotIdx r0 (dstOf k ii.val) 1 := by
        rw [hwv0]; unfold slotIdx; ring
      have hwv2' : w0.val + 2 = slotIdx r0 (dstOf k ii.val) 2 := by
        rw [hwv0]; unfold slotIdx; ring
      have hw1max : w0.val + 1 ≤ Std.Usize.max := by omega
      step as ⟨w1, hw1⟩
      have hw2max : w0.val + 2 ≤ Std.Usize.max := by omega
      step as ⟨w2, hw2⟩
      have hwv1 : w1.val = slotIdx r0 (dstOf k ii.val) 1 := by rw [hw1, hwv1']
      have hwv2 : w2.val = slotIdx r0 (dstOf k ii.val) 2 := by rw [hw2, hwv2']
      -- write 0
      have hwlt0 : w0.val < d.val.length := by
        rw [hwv0]; exact slotIdx_lt hdstN (by norm_num) hcapd
      step as ⟨c0, hc0⟩
      have hc0v : c0.val = slotW d r0 (dstOf k ii.val) 0 := by
        unfold slotW; rw [hc0, ← bufN_of_lt (v := d) (w := w0.val) hwlt0, hwv0]
      have hov0 : c0.val + a0.val ≤ Std.U64.max := by
        rw [hc0v, ha0]
        exact add_ok (ProgL_cur hdp hk hiilt (by norm_num)).1
          (addend_lt _ (hD _ _) (hD _ _) (hD _ _))
      step as ⟨v0, hv0⟩
      step as ⟨xw0, back0, hxw0, hback0⟩
      rw [hback0]
      have hp1 := write_lane D k negt negt r0 base B ii.val 0 d w0 a0 v0 hk hiilt
        (by norm_num) hB hD hpos hdp hwv0 hwlt0 (by rw [ha0]) (by rw [hv0, hc0v])
      have hl1 : (d.set w0 v0).val.length = buf0.val.length := by rw [set_length, hdl]
      have hf1 : FrameR buf0 (d.set w0 v0) r0 := FrameR_set hdf hdstN (by norm_num) hwv0
      -- write 1
      have hwlt1 : w1.val < (d.set w0 v0).val.length := by
        rw [set_length, hwv1]; exact slotIdx_lt hdstN (by norm_num) hcapd
      step as ⟨c1, hc1⟩
      have hc1v : c1.val = slotW (d.set w0 v0) r0 (dstOf k ii.val) 1 := by
        unfold slotW; rw [hc1, ← bufN_of_lt (v := d.set w0 v0) (w := w1.val) hwlt1, hwv1]
      have hov1 : c1.val + a1.val ≤ Std.U64.max := by
        rw [hc1v, ha1]
        exact add_ok (ProgL_cur hp1 hk hiilt (by norm_num)).1
          (addend_lt _ (hD _ _) (hD _ _) (hD _ _))
      step as ⟨v1, hv1⟩
      step as ⟨xw1, back1, hxw1, hback1⟩
      rw [hback1]
      have hp2 := write_lane D k negt negt r0 base B ii.val 1 (d.set w0 v0) w1 a1 v1
        hk hiilt (by norm_num) hB hD hpos hp1 hwv1 hwlt1 (by rw [ha1]) (by rw [hv1, hc1v])
      have hl2 : ((d.set w0 v0).set w1 v1).val.length = buf0.val.length := by
        rw [set_length, hl1]
      have hf2 : FrameR buf0 ((d.set w0 v0).set w1 v1) r0 :=
        FrameR_set hf1 hdstN (by norm_num) hwv1
      -- write 2
      have hwlt2 : w2.val < ((d.set w0 v0).set w1 v1).val.length := by
        rw [set_length, set_length, hwv2]; exact slotIdx_lt hdstN (by norm_num) hcapd
      step as ⟨c2, hc2⟩
      have hc2v : c2.val = slotW ((d.set w0 v0).set w1 v1) r0 (dstOf k ii.val) 2 := by
        unfold slotW
        rw [hc2, ← bufN_of_lt (v := (d.set w0 v0).set w1 v1) (w := w2.val) hwlt2, hwv2]
      have hov2 : c2.val + a2.val ≤ Std.U64.max := by
        rw [hc2v, ha2]
        exact add_ok (ProgL_cur hp2 hk hiilt (by norm_num)).1
          (addend_lt _ (hD _ _) (hD _ _) (hD _ _))
      step as ⟨v2, hv2⟩
      step as ⟨xw2, back2, hxw2, hback2⟩
      have hmaxb : ii.val + 1 ≤ Std.Usize.max := by
        have := usize_max_ge; have h3 : N = 1024 := rfl; omega
      step as ⟨ii1, hii1⟩
      rw [hback2]
      have hp3 := write_lane D k negt negt r0 base B ii.val 2 ((d.set w0 v0).set w1 v1)
        w2 a2 v2 hk hiilt (by norm_num) hB hD hpos hp2 hwv2 hwlt2 (by rw [ha2])
        (by rw [hv2, hc2v])
      refine ⟨by omega, by omega, by rw [set_length, hl2], by rw [hii1]; exact ProgL_three hp3,
        FrameR_set hf2 hdstN (by norm_num) hwv2, by omega⟩
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ii.val = N := by rw [← hn]; scalar_tac
      exact ⟨hdl, by rw [← heq]; exact hdp, hdf⟩
  · exact ⟨hj1, hj2, hlen, hprog, hfr⟩

/-- **`z_pass_lanes`.** Every lane of the row's slots gains `16 ± dₑ` -- so the
bound grows by `31` -- and the value of lane `e`, less the record, gains one
shifted, signed copy of digit `e`: `short_pass_off_spec` eight times over, with
`applied` unchanged. Every other word of the buffer is untouched. -/
theorem z_pass_lanes_spec (src : alloc.vec.Vec Std.U64) (kU : Std.Usize) (negt : Bool)
    (buf : alloc.vec.Vec Std.U64) (rbU : Std.Usize) (r0 : ℕ) (D : ℕ → ℕ → ℕ)
    (base : ℕ → ℕ → ZMod q) (B : ℕ)
    (hsrc : SpreadOf src D) (hD : ∀ e i, D e i ≤ 15) (hD8 : ∀ i, D 8 i = 0)
    (hk : kU.val < N) (hrb : rbU.val = 3 * (r0 * N))
    (hcap : 3 * ((r0 + 1) * N) ≤ buf.val.length) (hB : B + 31 < 2 ^ 20)
    (hbnd : ∀ p, p < N → ∀ l, l < 3 → WB (slotW buf r0 p l) B)
    (hval : ∀ p, p < N → ∀ e, e < 8 → laneD buf r0 p e = base e p) :
    quadeval.z_pass_lanes src kU negt buf rbU
      ⦃ z => z.val.length = buf.val.length
        ∧ (∀ p, p < N → ∀ l, l < 3 → WB (slotW z r0 p l) (B + 31))
        ∧ (∀ p, p < N → ∀ e, e < 8 →
            laneD z r0 p e = applied (base e) (dgZ D e) kU.val negt N p)
        ∧ FrameR buf z r0 ⦄ := by
  rw [quadeval.z_pass_lanes]
  step as ⟨limU, hlimU⟩
  have hlim : limU.val = N - kU.val := by rw [hlimU, params_RING_DEGREE_val]
  have hp0 : ProgL D kU.val negt r0 (fun e w => ((lane buf r0 w e : ℕ) : ZMod q)) B 0 0 buf := by
    intro p hp
    refine ⟨fun l hl => ?_, fun e _ => ?_⟩
    · rw [if_neg (Nat.not_lt_zero _), if_neg (Nat.not_lt_zero _)]; exact hbnd p hp l hl
    · rw [if_neg (Nat.not_lt_zero _)]; unfold appliedB; simp
  step with z_pass_lanes_loop0_spec src kU negt rbU limU buf 0#usize buf r0 D
    (fun e w => ((lane buf r0 w e : ℕ) : ZMod q)) B hsrc hD hlim hk hrb (by simp) rfl hcap hB
    hp0 (FrameR_refl buf r0) as ⟨out1, ho1, ho2, ho3⟩
  apply spec_mono (z_pass_lanes_loop1_spec src negt rbU params.RING_DEGREE limU out1 limU buf r0
    kU.val D (fun e w => ((lane buf r0 w e : ℕ) : ZMod q)) B hsrc hD params_RING_DEGREE_val hlim
    hk hrb (le_refl _) (by omega) ho1 hcap hB ho2 ho3)
  rintro z ⟨h1, h2, h3⟩
  refine ⟨h1, ?_, ?_, h3⟩
  · intro p hp l hl
    have := (h2 p hp).1 l hl
    rwa [if_neg (Nat.not_lt_zero _), if_pos (srcOf_lt hk hp)] at this
  · intro p hp e he
    have hv := (h2 p hp).2 e (by omega)
    have h8 := (h2 p hp).2 8 (by norm_num)
    rw [if_neg (Nat.not_lt_zero _)] at hv h8
    unfold laneD
    rw [hv, h8]
    unfold appliedB applied dgZ
    rw [if_pos (srcOf_lt hk hp), if_pos (srcOf_lt hk hp), if_pos (srcOf_lt hk hp), hD8,
      ← hval p hp e he]
    unfold laneD
    push_cast
    ring

/-! ## 8. `z_apply_terms_lanes`: the terms and passes of one row

No chunk counter here: `z_terms` admits at most `OMEGA = 16` passes per block,
and the block loop's `Z_LANE_CHUNK` schedule reserves `16 · 31` of lane
headroom for them before the row is touched. The bound therefore just grows by
`31` per pass. -/

/-- The first `t` magnitudes, summed: the pass count. -/
def magSum (vm : alloc.vec.Vec Std.U64) (t : ℕ) : ℕ := ∑ u ∈ Finset.range t, magAt vm u

theorem magSum_succ (vm : alloc.vec.Vec Std.U64) (t : ℕ) :
    magSum vm (t + 1) = magSum vm t + magAt vm t := by
  unfold magSum; rw [Finset.sum_range_succ]

/-- The pass loop: `m` passes of the term `(k, negt)`. -/
theorem z_apply_terms_lanes_loop0_loop0_spec (src : alloc.vec.Vec Std.U64) (rbU : Std.Usize)
    (out : alloc.vec.Vec Std.U64) (kU : Std.Usize) (mU : Std.U64) (negt : Bool)
    (passU : Std.U64) (buf0 : alloc.vec.Vec Std.U64) (r0 : ℕ) (D : ℕ → ℕ → ℕ)
    (base : ℕ → ℕ → ZMod q) (B : ℕ)
    (hsrc : SpreadOf src D) (hD : ∀ e i, D e i ≤ 15) (hD8 : ∀ i, D 8 i = 0)
    (hk : kU.val < N) (hrb : rbU.val = 3 * (r0 * N))
    (hcap : 3 * ((r0 + 1) * N) ≤ buf0.val.length) (hlen : out.val.length = buf0.val.length)
    (hp : passU.val ≤ mU.val) (hB : B + 31 * mU.val < 2 ^ 20)
    (hbnd : ∀ p, p < N → ∀ l, l < 3 → WB (slotW out r0 p l) (B + 31 * passU.val))
    (hval : ∀ p, p < N → ∀ e, e < 8 →
      laneD out r0 p e = passed (base e) (dgZ D e) kU.val negt passU.val p)
    (hfr : FrameR buf0 out r0) :
    quadeval.z_apply_terms_lanes_loop0_loop0 src rbU out kU mU negt passU
      ⦃ z => z.val.length = buf0.val.length
        ∧ (∀ p, p < N → ∀ l, l < 3 → WB (slotW z r0 p l) (B + 31 * mU.val))
        ∧ (∀ p, p < N → ∀ e, e < 8 →
            laneD z r0 p e = passed (base e) (dgZ D e) kU.val negt mU.val p)
        ∧ FrameR buf0 z r0 ⦄ := by
  rw [quadeval.z_apply_terms_lanes_loop0_loop0]
  apply loop.spec_decr_nat (fun t => mU.val - t.2.val)
    (fun t => t.2.val ≤ mU.val ∧ t.1.val.length = buf0.val.length
      ∧ (∀ p, p < N → ∀ l, l < 3 → WB (slotW t.1 r0 p l) (B + 31 * t.2.val))
      ∧ (∀ p, p < N → ∀ e, e < 8 →
          laneD t.1 r0 p e = passed (base e) (dgZ D e) kU.val negt t.2.val p)
      ∧ FrameR buf0 t.1 r0)
  · rintro ⟨d, pp⟩ ⟨hpp, hdl, hdb, hdv, hdf⟩
    dsimp only at hpp hdl hdb hdv hdf
    simp only [quadeval.z_apply_terms_lanes_loop0_loop0.body]
    by_cases hlt : pp < mU
    · rw [if_pos hlt]
      have hppm : pp.val < mU.val := by scalar_tac
      have hBq : B + 31 * pp.val + 31 < 2 ^ 20 := by omega
      step with z_pass_lanes_spec src kU negt d rbU r0 D
        (fun e => passed (base e) (dgZ D e) kU.val negt pp.val) (B + 31 * pp.val)
        hsrc hD hD8 hk hrb (by rw [hdl]; exact hcap) hBq hdb hdv
        as ⟨z, hzl, hzb, hzv, hzf⟩
      step as ⟨pp1, hpp1⟩
      refine ⟨by omega, by rw [hzl]; exact hdl, ?_, ?_, FrameR_trans hdf hzf, by omega⟩
      · intro p hp l hl
        rw [hpp1]
        have h2 : B + 31 * (pp.val + 1) = B + 31 * pp.val + 31 := by ring
        rw [h2]; exact hzb p hp l hl
      · intro p hp e he
        rw [hpp1, hzv p hp e he,
          applied_passed (base e) (dgZ D e) kU.val negt pp.val p hk hp]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : pp.val = mU.val := by scalar_tac
      rw [heq] at hdb hdv
      exact ⟨hdl, hdb, hdv, hdf⟩
  · exact ⟨hp, hlen, hbnd, hval, hfr⟩

theorem magSum_mono (vm : alloc.vec.Vec Std.U64) {a b : ℕ} (h : a ≤ b) :
    magSum vm a ≤ magSum vm b := by
  unfold magSum
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem termsSum_succ (sc : ℕ → ZMod q) (vi : alloc.vec.Vec Std.Usize)
    (vm : alloc.vec.Vec Std.U64) (vn : alloc.vec.Vec Bool) (t w : ℕ) :
    termsSum sc vi vm vn (t + 1) w
      = termsSum sc vi vm vn t w + contribW sc (idxAt vi t) (magAt vm t) (negAt vn t) w := by
  unfold termsSum; rw [Finset.sum_range_succ]

/-- The terms loop. -/
theorem z_apply_terms_lanes_loop0_spec (vi : alloc.vec.Vec Std.Usize)
    (vm : alloc.vec.Vec Std.U64) (vn : alloc.vec.Vec Bool) (src : alloc.vec.Vec Std.U64)
    (rbU : Std.Usize) (countU : Std.Usize) (out : alloc.vec.Vec Std.U64) (tU : Std.Usize)
    (buf0 : alloc.vec.Vec Std.U64) (r0 : ℕ) (D : ℕ → ℕ → ℕ) (base : ℕ → ℕ → ZMod q) (B : ℕ)
    (hsrc : SpreadOf src D) (hD : ∀ e i, D e i ≤ 15) (hD8 : ∀ i, D 8 i = 0)
    (hrb : rbU.val = 3 * (r0 * N)) (hcap : 3 * ((r0 + 1) * N) ≤ buf0.val.length)
    (hlen : out.val.length = buf0.val.length)
    (hcnt : vi.val.length = countU.val)
    (hmlen : countU.val ≤ vm.val.length) (hnlen : countU.val ≤ vn.val.length)
    (hidx : ∀ u, u < countU.val → idxAt vi u < N)
    (ht : tU.val ≤ countU.val)
    (hB : B + 31 * magSum vm countU.val < 2 ^ 20)
    (hbnd : ∀ p, p < N → ∀ l, l < 3 → WB (slotW out r0 p l) (B + 31 * magSum vm tU.val))
    (hval : ∀ p, p < N → ∀ e, e < 8 →
      laneD out r0 p e = base e p + termsSum (dgZ D e) vi vm vn tU.val p)
    (hfr : FrameR buf0 out r0) :
    quadeval.z_apply_terms_lanes_loop0 vi vm vn src rbU countU out tU
      ⦃ z => z.val.length = buf0.val.length
        ∧ (∀ p, p < N → ∀ l, l < 3 → WB (slotW z r0 p l) (B + 31 * magSum vm countU.val))
        ∧ (∀ p, p < N → ∀ e, e < 8 →
            laneD z r0 p e = base e p + termsSum (dgZ D e) vi vm vn countU.val p)
        ∧ FrameR buf0 z r0 ⦄ := by
  rw [quadeval.z_apply_terms_lanes_loop0]
  apply loop.spec_decr_nat (fun r => countU.val - r.2.val)
    (fun r => r.2.val ≤ countU.val ∧ r.1.val.length = buf0.val.length
      ∧ (∀ p, p < N → ∀ l, l < 3 → WB (slotW r.1 r0 p l) (B + 31 * magSum vm r.2.val))
      ∧ (∀ p, p < N → ∀ e, e < 8 →
          laneD r.1 r0 p e = base e p + termsSum (dgZ D e) vi vm vn r.2.val p)
      ∧ FrameR buf0 r.1 r0)
  · rintro ⟨d, tt⟩ ⟨htt, hdl, hdb, hdv, hdf⟩
    dsimp only at htt hdl hdb hdv hdf
    simp only [quadeval.z_apply_terms_lanes_loop0.body]
    by_cases hlt : tt < countU
    · rw [if_pos hlt]
      have httc : tt.val < countU.val := by scalar_tac
      have hti : tt.val < vi.val.length := by rw [hcnt]; exact httc
      have htm : tt.val < vm.val.length := by omega
      have htn : tt.val < vn.val.length := by omega
      step as ⟨kk, hkk⟩
      step as ⟨mm, hmm⟩
      step as ⟨nn, hnn⟩
      have hkv : kk.val = idxAt vi tt.val := by
        unfold idxAt; rw [hkk, List.getD_eq_getElem _ _ hti]
      have hmv : mm.val = magAt vm tt.val := by
        unfold magAt; rw [hmm, List.getD_eq_getElem _ _ htm]
      have hnv : nn = negAt vn tt.val := by
        unfold negAt; rw [hnn, List.getD_eq_getElem _ _ htn]
      have hkN : kk.val < N := by rw [hkv]; exact hidx tt.val httc
      have hBt : B + 31 * magSum vm tt.val + 31 * mm.val < 2 ^ 20 := by
        have h1 : magSum vm (tt.val + 1) ≤ magSum vm countU.val := magSum_mono vm (by omega)
        rw [magSum_succ, ← hmv] at h1
        omega
      step with z_apply_terms_lanes_loop0_loop0_spec src rbU d kk mm nn 0#u64 buf0 r0 D
        (fun e w => base e w + termsSum (dgZ D e) vi vm vn tt.val w)
        (B + 31 * magSum vm tt.val) hsrc hD hD8 hkN hrb hcap hdl (by simp) hBt
        (by intro p hp l hl; simpa using hdb p hp l hl)
        (by
          intro p hp e he
          rw [hdv p hp e he]
          unfold passed; simp)
        hdf
        as ⟨z, hzl, hzb, hzv, hzf⟩
      step as ⟨tt1, htt1⟩
      refine ⟨by omega, hzl, ?_, ?_, hzf, by omega⟩
      · intro p hp l hl
        have := hzb p hp l hl
        rw [htt1, magSum_succ, ← hmv]
        have h3 : B + 31 * (magSum vm tt.val + mm.val)
            = B + 31 * magSum vm tt.val + 31 * mm.val := by ring
        rw [h3]; exact this
      · intro p hp e he
        rw [htt1, hzv p hp e he, termsSum_succ, hkv, hmv, hnv,
          passed_eq_contribW, add_assoc]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : tt.val = countU.val := by scalar_tac
      rw [heq] at hdb hdv
      exact ⟨hdl, hdb, hdv, hdf⟩
  · exact ⟨ht, hlen, hbnd, hval, hfr⟩

/-- **`z_apply_terms_lanes`.** Lane `e` of each slot of the row gains the terms
sum of digit `e`; the bound grows by `31` per pass. -/
theorem z_apply_terms_lanes_spec (terms : quadeval.ZTerms) (src : alloc.vec.Vec Std.U64)
    (buf : alloc.vec.Vec Std.U64) (rbU : Std.Usize) (r0 : ℕ) (D : ℕ → ℕ → ℕ) (B : ℕ)
    (hsrc : SpreadOf src D) (hD : ∀ e i, D e i ≤ 15) (hD8 : ∀ i, D 8 i = 0)
    (hrb : rbU.val = 3 * (r0 * N)) (hcap : 3 * ((r0 + 1) * N) ≤ buf.val.length)
    (hmlen : terms.idx.val.length ≤ terms.mag.val.length)
    (hnlen : terms.idx.val.length ≤ terms.neg.val.length)
    (hidx : ∀ u, u < terms.idx.val.length → idxAt terms.idx u < N)
    (hB : B + 31 * magSum terms.mag terms.idx.val.length < 2 ^ 20)
    (hbnd : ∀ p, p < N → ∀ l, l < 3 → WB (slotW buf r0 p l) B) :
    quadeval.z_apply_terms_lanes terms src buf rbU
      ⦃ z => z.val.length = buf.val.length
        ∧ (∀ p, p < N → ∀ l, l < 3 →
            WB (slotW z r0 p l) (B + 31 * magSum terms.mag terms.idx.val.length))
        ∧ (∀ p, p < N → ∀ e, e < 8 → laneD z r0 p e
            = laneD buf r0 p e
              + termsSum (dgZ D e) terms.idx terms.mag terms.neg terms.idx.val.length p)
        ∧ FrameR buf z r0 ⦄ := by
  rw [quadeval.z_apply_terms_lanes]
  apply spec_mono (z_apply_terms_lanes_loop0_spec terms.idx terms.mag terms.neg src rbU
    (alloc.vec.Vec.len terms.idx) buf 0#usize buf r0 D (fun e p => laneD buf r0 p e) B
    hsrc hD hD8 hrb hcap rfl (by simp) (by simpa using hmlen) (by simpa using hnlen)
    (by simpa using hidx) (by simp) (by simpa using hB)
    (by intro p hp l hl; simpa [magSum] using hbnd p hp l hl)
    (by intro p hp e he; simp [termsSum])
    (FrameR_refl buf r0))
  rintro z ⟨h1, h2, h3, h4⟩
  refine ⟨h1, by simpa using h2, by simpa using h3, h4⟩

/-! ## 9. `z_terms`: the description, budgeted

`classify_short_loop_spec` at this module's type, with two more conjuncts: the
pass count is the running total, and the total is within the budget -- which is
what the block loop's flush schedule leans on. -/

theorem magSum_append {dm dm' : alloc.vec.Vec Std.U64} {mx : Std.U64} (t : ℕ)
    (hm : dm'.val = dm.val ++ [mx]) (ht : t = dm.val.length) :
    magSum dm' (t + 1) = magSum dm t + mx.val := by
  rw [magSum_succ]
  congr 1
  · unfold magSum
    refine Finset.sum_congr rfl (fun u hu => ?_)
    have hu' : u < t := Finset.mem_range.mp hu
    exact magAt_append_lt hm (by omega)
  · rw [ht]; exact magAt_append_eq hm

theorem z_terms_loop_spec (c : ring.Rq) (nU : Std.Usize) (qU halfU budgetU : Std.U64)
    (vi : alloc.vec.Vec Std.Usize) (vm : alloc.vec.Vec Std.U64) (vn : alloc.vec.Vec Bool)
    (totalU : Std.U64) (kU : Std.Usize)
    (hc : Wf c) (hn : nU.val = N) (hq : qU.val = q) (hhalf : halfU.val = q / 2)
    (htot : totalU.val ≤ budgetU.val) (hbud : budgetU.val < 2 ^ 32)
    (hk : kU.val ≤ nU.val) (hcnt : vi.val.length ≤ kU.val)
    (him : vi.val.length = vm.val.length) (hin : vi.val.length = vn.val.length)
    (hidx : ∀ u, u < vi.val.length → idxAt vi u < N)
    (hsum : magSum vm vi.val.length = totalU.val)
    (hden : ∀ j, descCoeffW vi vm vn vi.val.length j
      = if j < kU.val then coeffK c j else 0) :
    quadeval.z_terms_loop c nU qU halfU budgetU vi vm vn totalU kU
      ⦃ r => ∀ t, r = some t →
        t.idx.val.length = t.mag.val.length
        ∧ t.idx.val.length = t.neg.val.length
        ∧ (∀ u, u < t.idx.val.length → idxAt t.idx u < N)
        ∧ magSum t.mag t.idx.val.length ≤ budgetU.val
        ∧ ∀ j, descCoeffW t.idx t.mag t.neg t.idx.val.length j
            = if j < N then coeffK c j else 0 ⦄ := by
  rw [quadeval.z_terms_loop]
  apply loop.spec_decr_nat (fun t => nU.val - t.2.2.2.2.val)
    (fun t => t.2.2.2.2.val ≤ nU.val ∧ t.2.2.2.1.val ≤ budgetU.val
      ∧ t.1.val.length ≤ t.2.2.2.2.val
      ∧ t.1.val.length = t.2.1.val.length
      ∧ t.1.val.length = t.2.2.1.val.length
      ∧ (∀ u, u < t.1.val.length → idxAt t.1 u < N)
      ∧ magSum t.2.1 t.1.val.length = t.2.2.2.1.val
      ∧ ∀ j, descCoeffW t.1 t.2.1 t.2.2.1 t.1.val.length j
              = if j < t.2.2.2.2.val then coeffK c j else 0)
  · rintro ⟨di, dm, dn, dt, dk⟩ ⟨h1, h1b, h1c, h2, h3, h4, h4s, h5⟩
    dsimp only at h1 h1b h1c h2 h3 h4 h4s h5
    simp only [quadeval.z_terms_loop.body]
    by_cases hlt : dk < nU
    · rw [if_pos hlt]
      have hdkn : dk.val < nU.val := (Std.UScalar.lt_equiv dk nU).mp hlt
      have hdklt : dk.val < N := by rw [← hn]; exact hdkn
      step with HachiEquiv.Ring.coeff_spec c dk hc as ⟨f, hfred, hfval⟩
      step with to_u64_id f as ⟨cw, hcf⟩
      have hclt : cw.val < q := by rw [hcf]; exact hfred
      have hcval : ((cw.val : ℕ) : ZMod q) = coeffK c dk.val := by
        rw [hcf]; exact hfval
      by_cases hc0 : cw = 0#u64
      · rw [if_neg (by simp [hc0])]
        step as ⟨dk1, hdk1⟩
        refine ⟨by rw [hdk1, hn]; omega, h1b, by rw [hdk1]; omega, h2, h3, h4, h4s, ?_,
          by rw [hdk1]; omega⟩
        intro j
        rw [h5 j, hdk1]
        by_cases hj : j < dk.val
        · rw [if_pos hj, if_pos (show j < dk.val + 1 by omega)]
        · by_cases hje : j = dk.val
          · rw [if_neg hj, if_pos (show j < dk.val + 1 by omega), hje, ← hcval, hc0]
            simp
          · rw [if_neg hj, if_neg (show ¬(j < dk.val + 1) by omega)]
      · rw [if_pos (by simp [hc0])]
        have hsign : (decide (cw > halfU)) = decide (q / 2 < cw.val) := by
          simp only [decide_eq_decide]
          rw [← hhalf]
          exact ⟨fun h => by scalar_tac, fun h => by scalar_tac⟩
        by_cases hch : cw.val ≤ halfU.val
        · rw [if_pos (show cw ≤ halfU by scalar_tac)]
          step as ⟨t1, ht1⟩
          have hmv : cw.val = (if cw.val ≤ q / 2 then cw.val else q - cw.val) := by
            rw [if_pos (by rw [← hhalf]; exact hch)]
          by_cases hbg : budgetU.val < t1.val
          · rw [if_pos ((Std.UScalar.lt_equiv budgetU t1).mpr hbg), WP.spec_ok]
            dsimp only
            intro t ht
            simp at ht
          · rw [if_neg (fun hcon =>
              hbg ((Std.UScalar.lt_equiv budgetU t1).mp hcon))]
            step as ⟨di1, hdi1⟩
            step as ⟨dm1, hdm1⟩
            step as ⟨dn1, hdn1⟩
            step as ⟨dk1, hdk1⟩
            obtain ⟨p2, p3, p4, p5⟩ := classify_push_invariant c hdi1 hdm1 hdn1
              h2 h3 h4 h5 hdklt hcval
              (termValW_of_word cw.val cw.val _ hclt hmv hsign)
            have hlen1 : di1.val.length = di.val.length + 1 := by rw [hdi1]; simp
            have hb3 : di1.val.length ≤ dk1.val := by rw [hlen1, hdk1]; omega
            refine ⟨by rw [hdk1, hn]; omega, by omega, hb3, p2, p3, p4, ?_, ?_,
              by rw [hdk1]; omega⟩
            · rw [hlen1, magSum_append di.val.length hdm1 h2, h4s, ht1]
            · intro j; rw [hdk1]; exact p5 j
        · rw [if_neg (show ¬ (cw ≤ halfU) by scalar_tac)]
          step as ⟨m, hm⟩
          step as ⟨t1, ht1⟩
          have hmv : m.val = (if cw.val ≤ q / 2 then cw.val else q - cw.val) := by
            rw [if_neg (by rw [← hhalf]; exact hch)]
            scalar_tac
          by_cases hbg : budgetU.val < t1.val
          · rw [if_pos ((Std.UScalar.lt_equiv budgetU t1).mpr hbg), WP.spec_ok]
            dsimp only
            intro t ht
            simp at ht
          · rw [if_neg (fun hcon =>
              hbg ((Std.UScalar.lt_equiv budgetU t1).mp hcon))]
            step as ⟨di1, hdi1⟩
            step as ⟨dm1, hdm1⟩
            step as ⟨dn1, hdn1⟩
            step as ⟨dk1, hdk1⟩
            obtain ⟨p2, p3, p4, p5⟩ := classify_push_invariant c hdi1 hdm1 hdn1
              h2 h3 h4 h5 hdklt hcval
              (termValW_of_word cw.val m.val _ hclt hmv hsign)
            have hlen1 : di1.val.length = di.val.length + 1 := by rw [hdi1]; simp
            have hb3 : di1.val.length ≤ dk1.val := by rw [hlen1, hdk1]; omega
            refine ⟨by rw [hdk1, hn]; omega, by omega, hb3, p2, p3, p4, ?_, ?_,
              by rw [hdk1]; omega⟩
            · rw [hlen1, magSum_append di.val.length hdm1 h2, h4s, ht1]
            · intro j; rw [hdk1]; exact p5 j
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      intro t ht
      have heq : dk.val = nU.val := by scalar_tac
      injection ht with hd
      subst hd
      dsimp only
      refine ⟨h2, h3, h4, by rw [h4s]; exact h1b, ?_⟩
      intro j
      rw [h5 j, heq, hn]
  · exact ⟨hk, htot, hcnt, him, hin, hidx, hsum, hden⟩

/-- **`z_terms`.** Either it declines, or the three vectors denote `c` and
their magnitudes sum to at most `OMEGA`. -/
theorem z_terms_spec (c : ring.Rq) (hc : Wf c) :
    quadeval.z_terms c
      ⦃ r => ∀ t, r = some t →
        t.idx.val.length ≤ t.mag.val.length
        ∧ t.idx.val.length ≤ t.neg.val.length
        ∧ (∀ u, u < t.idx.val.length → idxAt t.idx u < N)
        ∧ magSum t.mag t.idx.val.length ≤ 16
        ∧ ∀ j, j < N →
            coeffK c j = descCoeffW t.idx t.mag t.neg t.idx.val.length j ⦄ := by
  rw [quadeval.z_terms]
  step as ⟨half, hhalf⟩
  have hhv : half.val = q / 2 := by rw [hhalf, params_Q_val]
  apply spec_mono (z_terms_loop_spec c params.RING_DEGREE params.Q half params.OMEGA
    (alloc.vec.Vec.new Std.Usize) (alloc.vec.Vec.new Std.U64) (alloc.vec.Vec.new Bool)
    0#u64 0#usize hc params_RING_DEGREE_val params_Q_val hhv (by simp [params.OMEGA])
    (by simp [params.OMEGA]) (by simp [params_RING_DEGREE_val]) (by simp) (by simp) (by simp)
    (by intro u hu; simp at hu) (by simp [magSum]) (by intro j; simp [descCoeffW]))
  intro r hr t ht
  obtain ⟨e1, e2, e3, e4, e5⟩ := hr t ht
  refine ⟨by omega, by omega, e3, ?_, ?_⟩
  · have : (params.OMEGA).val = 16 := by simp [params.OMEGA]
    omega
  · intro j hj
    rw [e5 j, if_pos hj]


/-! ## 10. `z_row_lanes`: the spread, then the terms -/

/-- **`z_row_lanes`.** Each of the row's eight digit accumulators gains the
product of the challenge with that digit polynomial, as a ring element; the
bound grows by `31` per pass; nothing outside the row's slots moves. -/
theorem z_row_lanes_spec (terms : quadeval.ZTerms) (row : ring.Rq)
    (buf : alloc.vec.Vec Std.U64) (rbU : Std.Usize) (r0 : ℕ) (ci : ring.Rq) (B : ℕ)
    (hrow : Wf row) (hci : Wf ci)
    (hrb : rbU.val = 3 * (r0 * N)) (hcap : 3 * ((r0 + 1) * N) ≤ buf.val.length)
    (hmlen : terms.idx.val.length ≤ terms.mag.val.length)
    (hnlen : terms.idx.val.length ≤ terms.neg.val.length)
    (hidx : ∀ u, u < terms.idx.val.length → idxAt terms.idx u < N)
    (hden : ∀ j, j < N →
      coeffK ci j = descCoeffW terms.idx terms.mag terms.neg terms.idx.val.length j)
    (hB : B + 31 * magSum terms.mag terms.idx.val.length < 2 ^ 20)
    (hbnd : ∀ p, p < N → ∀ l, l < 3 → WB (slotW buf r0 p l) B) :
    quadeval.z_row_lanes terms row buf rbU
      ⦃ z => z.val.length = buf.val.length
        ∧ (∀ p, p < N → ∀ l, l < 3 →
            WB (slotW z r0 p l) (B + 31 * magSum terms.mag terms.idx.val.length))
        ∧ (∀ e, e < 8 → laneRq z r0 e = laneRq buf r0 e + toRq ci * digitRq row e)
        ∧ FrameR buf z r0 ⦄ := by
  rw [quadeval.z_row_lanes]
  step with z_spread_spec row hrow as ⟨src, hsrc⟩
  apply spec_mono (z_apply_terms_lanes_spec terms src buf rbU r0 (nibN row) B hsrc
    (nibN_le row) (nibN_eight row hrow) hrb hcap hmlen hnlen hidx hB hbnd)
  rintro z ⟨h1, h2, h3, h4⟩
  refine ⟨h1, h2, ?_, h4⟩
  intro e he
  have hdenall : ∀ j, coeffK ci j
      = descCoeffW terms.idx terms.mag terms.neg terms.idx.val.length j := by
    intro j
    by_cases hj : j < N
    · exact hden j hj
    · rw [coeffK_of_ge (by rw [hci.1]; omega)]
      unfold descCoeffW
      refine (Finset.sum_eq_zero (fun u hu => ?_)).symm
      unfold single
      rw [if_neg (by have := hidx u (by simpa using hu); omega)]
  apply laneRq_gain z buf r0 ci row hci hrow e
  intro p hp
  rw [h3 p hp e he]
  have hdg : dgZ (nibN row) e = nib row e := rfl
  rw [hdg, termsSum_eq_negConvF (nib row e) terms.idx terms.mag terms.neg
      terms.idx.val.length p hidx hp (fun i hi => nib_of_ge row hrow e hi)]
  congr 2
  exact (funext hdenall).symm

/-! ## 11. Decoding, flushing and zeroing the packed accumulator

The decode reads lane `e` and the record with a shift and a mask -- total, and
exact whatever the words hold, because a lane is *defined* as those bits
([`lane`]) -- and returns `lane_e + q − record`, which `Fp::new` reduces to
[`laneD`]. The record is below `2^20 < q`, so the `u64` subtraction never
borrows. -/

theorem vgetD_set_eq {α : Type} {v : alloc.vec.Vec α} {t : Std.Usize} {x d : α}
    (ht : t.val < v.val.length) : (v.set t x).val.getD t.val d = x := by
  rw [alloc.vec.Vec.set_val_eq,
    List.getD_eq_getElem _ _ (by rw [List.length_set]; exact ht), List.getElem_set]
  simp

theorem vgetD_set_ne {α : Type} {v : alloc.vec.Vec α} {t : Std.Usize} {x d : α}
    {k : ℕ} (h : k ≠ t.val) : (v.set t x).val.getD k d = v.val.getD k d := by
  rw [alloc.vec.Vec.set_val_eq]
  by_cases hk : k < v.val.length
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_set]; exact hk),
      List.getD_eq_getElem _ _ hk, List.getElem_set_ne (fun hh => h hh.symm)]
  · rw [List.getD_eq_default _ _ (by rw [List.length_set]; omega),
      List.getD_eq_default _ _ (by omega)]

theorem all_set {α : Type} {P : α → Prop} {v : alloc.vec.Vec α}
    {t : Std.Usize} {y : α} (hv : ∀ x ∈ v.val, P x) (hy : P y) :
    ∀ x ∈ (v.set t y).val, P x := by
  intro x hx
  rw [alloc.vec.Vec.set_val_eq] at hx
  rcases List.mem_or_eq_of_mem_set hx with h | h
  · exact hv x h
  · rw [h]; exact hy

theorem vset_length {α : Type} {v : alloc.vec.Vec α} {t : Std.Usize} {x : α} :
    (v.set t x).val.length = v.val.length := by
  rw [alloc.vec.Vec.set_val_eq, List.length_set]

/-- The decode loop: coefficient `p` is `laneD zp r p e`, reduced. -/
theorem z_lane_decode_loop_spec (zp : alloc.vec.Vec Std.U64) (baseU nU : Std.Usize)
    (qU : Std.U64) (wordU shiftU : Std.Usize) (out : alloc.vec.Vec cpoly.field.Fp)
    (pU : Std.Usize) (r e : ℕ)
    (hbase : baseU.val = 3 * (r * N)) (hn : nU.val = N) (hq : qU.val = q) (he : e < 8)
    (hword : wordU.val = e / 3) (hshift : shiftU.val = 20 * (e % 3))
    (hcap : 3 * ((r + 1) * N) ≤ zp.val.length)
    (hp : pU.val ≤ N) (hlen : out.val.length = pU.val) (hred : ∀ u ∈ out.val, Red u)
    (hval : ∀ p, p < pU.val → coeffK out p = laneD zp r p e) :
    quadeval.z_lane_decode_loop zp baseU nU qU wordU shiftU out pU
      ⦃ cs => cs.val.length = N ∧ (∀ u ∈ cs.val, Red u)
        ∧ ∀ p, p < N → coeffK cs p = laneD zp r p e ⦄ := by
  rw [quadeval.z_lane_decode_loop]
  apply loop.spec_decr_nat (fun t => nU.val - t.2.val)
    (fun t => t.2.val ≤ N ∧ t.1.val.length = t.2.val ∧ (∀ u ∈ t.1.val, Red u)
      ∧ ∀ p, p < t.2.val → coeffK t.1 p = laneD zp r p e)
  · rintro ⟨o, pp⟩ ⟨hpp, hol, hor, hov⟩
    dsimp only at hpp hol hor hov
    simp only [quadeval.z_lane_decode_loop.body]
    by_cases hlt : pp < nU
    · rw [if_pos hlt]
      have hpl : pp.val < N := by rw [← hn]; scalar_tac
      have hzmax : zp.val.length ≤ Std.Usize.max := zp.property
      have hat2 : slotIdx r pp.val 2 < zp.val.length := slotIdx_lt hpl (by norm_num) hcap
      have hatw : slotIdx r pp.val (e / 3) < zp.val.length := slotIdx_lt hpl (by omega) hcap
      step as ⟨i, hi⟩
      have hat1v' : baseU.val + i.val = slotIdx r pp.val 0 := by
        rw [hbase, hi, z_lane_words_val]; unfold slotIdx; ring
      have hat1max : baseU.val + i.val ≤ Std.Usize.max := by
        have := slotIdx_lt hpl (by norm_num : (0 : ℕ) < 3) hcap; omega
      step as ⟨at1, hat1⟩
      have hat1v : at1.val = slotIdx r pp.val 0 := by rw [hat1, hat1v']
      have hi1v' : at1.val + wordU.val = slotIdx r pp.val (e / 3) := by
        rw [hat1v, hword]; unfold slotIdx; ring
      have hi1max : at1.val + wordU.val ≤ Std.Usize.max := by omega
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = slotIdx r pp.val (e / 3) := by rw [hi1, hi1v']
      step as ⟨w, hw⟩
      have hi2v' : at1.val + 2 = slotIdx r pp.val 2 := by rw [hat1v]; unfold slotIdx; ring
      have hi2max : at1.val + 2 ≤ Std.Usize.max := by omega
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = slotIdx r pp.val 2 := by rw [hi2, hi2v']
      step as ⟨c, hc⟩
      have hwv : w.val = slotW zp r pp.val (e / 3) := by
        unfold slotW; rw [hw, ← bufN_of_lt (v := zp) (w := i1.val) (by omega), hi1v]
      have hcv : c.val = slotW zp r pp.val 2 := by
        unfold slotW; rw [hc, ← bufN_of_lt (v := zp) (w := i2.val) (by omega), hi2v]
      have hsh : shiftU.val < 64 := by rw [hshift]; omega
      step as ⟨i3, hi3, _⟩
      step as ⟨ln, hln, _⟩
      step as ⟨i4, hi4, _⟩
      step as ⟨rec, hrec, _⟩
      have hmask : (1048575 : ℕ) = 2 ^ 20 - 1 := by norm_num
      have hlnv : ln.val = lane zp r pp.val e := by
        rw [hln, UScalar.val_and, hi3, z_lane_mask_val, hwv, hshift, hmask,
          Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
        rfl
      have hrecv : rec.val = lane zp r pp.val 8 := by
        rw [hrec, UScalar.val_and, hi4, z_lane_mask_val, hcv, hmask,
          Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
        rfl
      have hlnlt : ln.val < 2 ^ 20 := by rw [hlnv]; exact laneOf_lt _ _
      have hreclt : rec.val < 2 ^ 20 := by rw [hrecv]; exact laneOf_lt _ _
      have hqv : q = 4294967197 := rfl
      have hi5max : ln.val + qU.val ≤ Std.U64.max := by
        rw [hq, u64_max_val, hqv]; norm_num at hlnlt; omega
      step as ⟨i5, hi5⟩
      have hrecle : rec.val ≤ i5.val := by
        rw [hi5, hq, hqv]; norm_num at hreclt; omega
      step as ⟨v, hv⟩
      step with fp_new_spec v as ⟨f, hRf, hfv⟩
      have hmax : o.val.length < Std.Usize.max := by
        rw [hol]; have := usize_max_ge; have h3 : N = 1024 := rfl; omega
      step as ⟨o1, ho1⟩
      step as ⟨pp1, hpp1⟩
      have hkey : coeffK o1 pp.val = toK f := by
        unfold coeffK; rw [ho1, ← hol, getD_append_eq]
      refine ⟨by omega, by rw [ho1, hpp1, List.length_append, hol]; simp, ?_, ?_, by omega⟩
      · intro u hu
        rw [ho1, List.mem_append, List.mem_singleton] at hu
        rcases hu with h | h
        · exact hor u h
        · rw [h]; exact hRf
      · intro p hp
        rw [hpp1] at hp
        rcases Nat.lt_or_ge p pp.val with hlt2 | hge
        · unfold coeffK; rw [ho1, getD_append_lt _ _ _ (by omega)]; exact hov p hlt2
        · have hpeq : p = pp.val := by omega
          rw [hpeq, hkey, hfv, hv, hi5, hlnv, hrecv, hq]
          unfold laneD
          rw [← hlnv, ← hrecv]
          rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self]
          ring
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : pp.val = N := by rw [← hn]; scalar_tac
      exact ⟨by rw [hol, heq], hor, fun p hp => hov p (by rw [heq]; exact hp)⟩
  · exact ⟨hp, hlen, hred, hval⟩

/-- **`z_lane_decode`.** Digit `e`'s polynomial of row `r`: coefficient `p` is
`laneD zp r p e`, as a reduced field element. No hypothesis on the words. -/
theorem z_lane_decode_spec (zp : alloc.vec.Vec Std.U64) (baseU eU : Std.Usize) (r : ℕ)
    (hbase : baseU.val = 3 * (r * N)) (he : eU.val < 8)
    (hcap : 3 * ((r + 1) * N) ≤ zp.val.length) :
    quadeval.z_lane_decode zp baseU eU
      ⦃ cs => cs.val.length = N ∧ (∀ u ∈ cs.val, Red u)
        ∧ ∀ p, p < N → coeffK cs p = laneD zp r p eU.val ⦄ := by
  rw [quadeval.z_lane_decode]
  step as ⟨word, hword⟩
  step as ⟨i, hi⟩
  step as ⟨shift, hshift⟩
  simp only [alloc.vec.Vec.with_capacity]
  exact z_lane_decode_loop_spec zp baseU params.RING_DEGREE params.Q word shift
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize r eU.val hbase params_RING_DEGREE_val
    params_Q_val he (by rw [hword]) (by rw [hshift, hi]) hcap (by simp) (by simp)
    (by intro u hu; simp at hu) (by intro p hp; simp at hp)

/-- The flush loop: `out[j] = acc[j] + laneRq zp (j / 8) (j % 8)` for `j` done,
`out[j] = acc[j]` for `j` to go. -/
theorem z_lane_flush_loop_spec (zp : alloc.vec.Vec Std.U64) (nU digitsU widthU : Std.Usize)
    (out : alloc.vec.Vec ring.Rq) (jU : Std.Usize) (acc : alloc.vec.Vec ring.Rq)
    (hn : nU.val = N) (hd : digitsU.val = 8) (hw : widthU.val = 2 ^ 10 * 8)
    (hzl : zp.val.length = 3 * (2 ^ 10 * N))
    (hj : jU.val ≤ 2 ^ 10 * 8) (hol : out.val.length = 2 ^ 10 * 8)
    (howf : ∀ x ∈ out.val, Wf x)
    (hdone : ∀ t, t < jU.val → toRq (out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
      = toRq (acc.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) + laneRq zp (t / 8) (t % 8))
    (hrest : ∀ t, jU.val ≤ t → out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
      = acc.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) :
    quadeval.z_lane_flush_loop zp nU digitsU widthU out jU
      ⦃ z => z.val.length = 2 ^ 10 * 8 ∧ (∀ x ∈ z.val, Wf x)
        ∧ ∀ t, t < 2 ^ 10 * 8 → toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = toRq (acc.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
              + laneRq zp (t / 8) (t % 8) ⦄ := by
  have h1024 : (2 : ℕ) ^ 10 = 1024 := by norm_num
  rw [quadeval.z_lane_flush_loop]
  apply loop.spec_decr_nat (fun r => 2 ^ 10 * 8 - r.2.val)
    (fun r => r.2.val ≤ 2 ^ 10 * 8 ∧ r.1.val.length = 2 ^ 10 * 8 ∧ (∀ x ∈ r.1.val, Wf x)
      ∧ (∀ t, t < r.2.val → toRq (r.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq (acc.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            + laneRq zp (t / 8) (t % 8))
      ∧ ∀ t, r.2.val ≤ t → r.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)
          = acc.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
  · rintro ⟨o, jj⟩ ⟨hjj, hol, how, hov, hor⟩
    dsimp only at hjj hol how hov hor
    simp only [quadeval.z_lane_flush_loop.body]
    by_cases hlt : jj < widthU
    · rw [if_pos hlt]
      have hjl : jj.val < 2 ^ 10 * 8 := by rw [← hw]; scalar_tac
      have hd0 : digitsU.val ≠ 0 := by rw [hd]; norm_num
      step as ⟨rr, hrr⟩
      step as ⟨ee, hee⟩
      have hrrv : rr.val = jj.val / 8 := by rw [hrr, hd]
      have heev : ee.val = jj.val % 8 := by rw [hee, hd]
      have hrr1024 : rr.val < 1024 := by rw [hrrv]; rw [h1024] at hjl; omega
      step as ⟨i, hi⟩
      have hmulmax : i.val * nU.val ≤ Std.Usize.max := by
        rw [hi, hn, z_lane_words_val]
        have := usize_max_ge; have h3 : N = 1024 := rfl; rw [h3]; nlinarith
      step as ⟨base, hbase⟩
      have hbv : base.val = 3 * (rr.val * N) := by
        rw [hbase, hi, hn, z_lane_words_val]; ring
      have hcapz : 3 * ((rr.val + 1) * N) ≤ zp.val.length := by
        rw [hzl, h1024]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      step with z_lane_decode_spec zp base ee rr.val hbv (by rw [heev]; omega) hcapz
        as ⟨cs, hcsl, hcsr, hcsv⟩
      step with RqBridge.from_coeffs_spec cs hcsr as ⟨zr, hzrwf, hzrval⟩
      have hzrl : toRq zr = laneRq zp (jj.val / 8) (jj.val % 8) := by
        rw [hzrval, ← hrrv, ← heev]
        unfold laneRq
        exact ofFinCoeff_congr (fun t ht => hcsv t ht)
      have hob : jj.val < o.val.length := by rw [hol]; exact hjl
      step as ⟨r1, hr1⟩
      have hr1g : r1 = acc.val.getD jj.val (alloc.vec.Vec.new cpoly.field.Fp) := by
        rw [hr1, ← hor jj.val (le_refl _), List.getD_eq_getElem _ _ hob]
      have hr1wf : Wf r1 := by rw [hr1]; exact how _ (List.getElem_mem hob)
      step with RqBridge.add_spec r1 zr hr1wf hzrwf as ⟨r2, hr2wf, hr2val⟩
      step as ⟨xa, back, hxa, hback⟩
      step as ⟨jj1, hjj1⟩
      rw [hback]
      refine ⟨by omega, by rw [vset_length, hol], all_set how hr2wf, ?_, ?_, by omega⟩
      · intro t ht
        rw [hjj1] at ht
        by_cases hte : t = jj.val
        · subst hte
          rw [vgetD_set_eq hob, hr2val, hzrl, hr1g]
        · rw [vgetD_set_ne hte]; exact hov t (by omega)
      · intro t ht
        rw [hjj1] at ht
        rw [vgetD_set_ne (by omega)]; exact hor t (by omega)
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = 2 ^ 10 * 8 := by rw [← hw]; scalar_tac
      exact ⟨hol, how, fun t ht => hov t (by rw [heq]; exact ht)⟩
  · exact ⟨hj, hol, howf, hdone, hrest⟩

/-- **`z_lane_flush`.** `acc[8r + e]` gains digit `e`'s accumulator of row `r`
as a ring element; `zp` is read, never written. -/
theorem z_lane_flush_spec (acc : alloc.vec.Vec ring.Rq) (zp : alloc.vec.Vec Std.U64)
    (hacc : acc.val.length = 2 ^ 10 * 8) (hwf : ∀ x ∈ acc.val, Wf x)
    (hzl : zp.val.length = 3 * (2 ^ 10 * N)) :
    quadeval.z_lane_flush acc zp
      ⦃ z => z.val.length = 2 ^ 10 * 8 ∧ (∀ x ∈ z.val, Wf x)
        ∧ ∀ t, t < 2 ^ 10 * 8 → toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = toRq (acc.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
              + laneRq zp (t / 8) (t % 8) ⦄ := by
  rw [quadeval.z_lane_flush]
  step as ⟨width, hwidth⟩
  case hmax => simp [params.MESSAGE_ROWS, params.GADGET_DIGITS]; scalar_tac
  have hwv : width.val = 2 ^ 10 * 8 := by
    have h : (2 : ℕ) ^ 10 * 8 = 8192 := by norm_num
    rw [h]
    simp only [params.MESSAGE_ROWS, params.GADGET_DIGITS] at hwidth
    scalar_tac
  exact z_lane_flush_loop_spec zp params.RING_DEGREE params.GADGET_DIGITS width acc 0#usize acc
    params_RING_DEGREE_val (by simp [params.GADGET_DIGITS]) hwv hzl (by simp) hacc hwf
    (by intro t ht; simp at ht) (fun _ _ => rfl)

/-- The zeroing loop. -/
theorem z_lane_zero_loop_spec (out : alloc.vec.Vec Std.U64) (lenU iU : Std.Usize)
    (buf0 : alloc.vec.Vec Std.U64)
    (hlen : lenU.val = buf0.val.length) (hi : iU.val ≤ lenU.val)
    (hol : out.val.length = buf0.val.length)
    (hdone : ∀ t, t < iU.val → bufN out t = 0) :
    quadeval.z_lane_zero_loop out lenU iU
      ⦃ z => z.val.length = buf0.val.length ∧ ∀ t, bufN z t = 0 ⦄ := by
  rw [quadeval.z_lane_zero_loop]
  apply loop.spec_decr_nat (fun t => lenU.val - t.2.val)
    (fun t => t.2.val ≤ lenU.val ∧ t.1.val.length = buf0.val.length
      ∧ ∀ u, u < t.2.val → bufN t.1 u = 0)
  · rintro ⟨o, ii⟩ ⟨hii, hol, hod⟩
    dsimp only at hii hol hod
    simp only [quadeval.z_lane_zero_loop.body]
    by_cases hlt : ii < lenU
    · rw [if_pos hlt]
      have hiilt : ii.val < lenU.val := by scalar_tac
      have hib : ii.val < o.val.length := by rw [hol, ← hlen]; exact hiilt
      step as ⟨xw, back, hxw, hback⟩
      step as ⟨i1, hi1⟩
      rw [hback]
      refine ⟨by omega, by rw [set_length]; exact hol, ?_, by omega⟩
      intro u hu
      rw [hi1] at hu
      by_cases hue : u = ii.val
      · subst hue; rw [bufN_set_eq hib]; rfl
      · rw [bufN_set_ne hue]; exact hod u (by omega)
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ii.val = lenU.val := by scalar_tac
      refine ⟨hol, fun u => ?_⟩
      by_cases hu : u < o.val.length
      · exact hod u (by rw [heq, hlen, ← hol]; exact hu)
      · unfold bufN; rw [List.getD_eq_default _ _ (by omega)]; rfl
  · exact ⟨hi, hol, hdone⟩

/-- **`z_lane_zero`.** Every word `0`, length kept. -/
theorem z_lane_zero_spec (buf : alloc.vec.Vec Std.U64) :
    quadeval.z_lane_zero buf ⦃ z => z.val.length = buf.val.length ∧ ∀ t, bufN z t = 0 ⦄ := by
  rw [quadeval.z_lane_zero]
  exact z_lane_zero_loop_spec buf (alloc.vec.Vec.len buf) 0#usize buf (by simp) (by simp) rfl
    (by intro t ht; simp at ht)

end HachiEquiv.ZPacked
