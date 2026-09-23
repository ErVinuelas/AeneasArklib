/-
`ZPacked.lean` -- the fused z kernel of Stage 6 card T43: `quadeval::z_terms`,
`z_pass`, `z_reduce`, `z_apply_terms` and `z_row`, the word level of
`honest_z_from_raw_32`'s short branch.

# What changed, and what did not

`honest_z_from_raw_32` used to decompose every message block into its 8192
digit ring elements (`gadget_decompose`) and multiply each by the challenge
with `ring::mul_short_add_into`. It now reads each coefficient of the block
once, splits it into its eight base-16 digits -- the eight *nibbles* of the
word, because the chain's decomposer is the unsigned one and every canonical
word is below `q < 2^32` -- and scatters them, signed and shifted, into the
eight digit accumulators of the row directly. The accumulator is one flat
unreduced `u64` buffer for the whole of `z`, region `j` at `j · S` with
`S = N + Z_PAD`, carried across all the blocks.

Nothing above the word level moves. The pure layer of `RingShort.lean` --
`applied`, `passed`, `termsSum`, `descCoeffW`, `sgn`, `srcOf`/`dstOf`,
`offStep`, `termsSum_eq_negConvF` -- is stated over `ℕ → ZMod q` and knows
nothing about which buffer holds the coefficients or how many regions it has,
so it is reused unchanged. What is new is:

* [`digitK_eq_nibble`], the pinned nibble lemma: the specification's digit of a
  canonical word `x < q` at `e` is `(x / 16^e) % 16`;
* the region layer -- [`reg`], [`regRq`], [`nib`] -- and the frame conjunct
  every loop spec carries, saying the other rows' regions are untouched;
* [`coeff_toRq_mul_fin`], `RqBridge.coeff_toRq_mul` with an `ofFinCoeff` right
  operand, which is how the digit polynomial enters without ever being an
  extracted `Rq`.

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

/-! ## 1. The two constants -/

@[simp] theorem z_pad_val : (quadeval.Z_PAD).val = 16 := by
  simp only [quadeval.Z_PAD]; decide

@[simp] theorem z_chunk_val : (quadeval.Z_CHUNK).val = 16777216 := by
  simp only [quadeval.Z_CHUNK]; decide

/-- The region stride: `RING_DEGREE + Z_PAD`. -/
abbrev S : ℕ := N + 16

theorem S_val : S = 1040 := rfl

/-- `Usize.max` is at least `2^32 - 1` on either supported word size (a local
copy of `Scheme.usize_max_ge'`). -/
theorem usize_max_ge : (4294967295 : ℕ) ≤ Std.Usize.max := by
  rw [Std.Usize.max_def]
  rcases System.Platform.numBits_eq with h | h <;> simp [Std.Usize.numBits, h]

theorem u64_max_val : Std.U64.max = 18446744073709551615 := by
  simp only [Std.U64.max, Std.U64.numBits]; norm_num

/-! ## 2. Regions, and the digit polynomial

The accumulator is one `Vec Std.U64`; [`reg`] reads it as regions of `S` words.
Only the first `N` words of a region carry a coefficient; the pad is never
read. -/

/-- Word `w` of region `g`. -/
def reg (buf : alloc.vec.Vec Std.U64) (g w : ℕ) : ℕ := bufN buf (g * S + w)

/-- Two in-region addresses coincide only when region and offset do. -/
theorem reg_index_inj {g g' w w' : ℕ} (hw : w < S) (hw' : w' < S)
    (h : g * S + w = g' * S + w') : g = g' ∧ w = w' := by
  have hS : 0 < S := by decide
  have h1 : (g * S + w) / S = g := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt hw]; simp
  have h2 : (g' * S + w') / S = g' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt hw']; simp
  have hg : g = g' := by rw [← h1, ← h2, h]
  subst hg
  exact ⟨rfl, by omega⟩

theorem reg_set_eq {buf : alloc.vec.Vec Std.U64} {tU : Std.Usize} {x : Std.U64}
    {g w : ℕ} (ht : tU.val = g * S + w) (hlt : tU.val < buf.val.length) :
    reg (buf.set tU x) g w = x.val := by
  unfold reg; rw [← ht]; exact bufN_set_eq hlt

theorem reg_set_ne {buf : alloc.vec.Vec Std.U64} {tU : Std.Usize} {x : Std.U64}
    {g w : ℕ} (hne : g * S + w ≠ tU.val) :
    reg (buf.set tU x) g w = reg buf g w := by
  unfold reg; exact bufN_set_ne hne

/-- Region `g` of the accumulator, as a ring element. -/
def regRq (buf : alloc.vec.Vec Std.U64) (g : ℕ) : Rq Φ :=
  Rq.ofFinCoeff Φ N (fun w => ((reg buf g w : ℕ) : ZMod q))

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

/-! ## 3. The nibble lemma

The specification's `dd.digit c ⟨e, _⟩` is `(Nat.digits 16 c.val).getD e 0`
(`digitK`), and Mathlib's `Nat.getD_digits` says that is `c.val / 16^e % 16`.
For a canonical word `x < q` the value of `(x : ZMod q)` is `x` itself, so the
digit is the nibble. -/

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

/-- **A region that gained the fused product, at the `Rq` level.** If region
`g` of `z` is region `g` of `buf` plus `negConvF (coeffK ci) (nib row e)`
coefficientwise, then as ring elements it gained `toRq ci * digitRq row e`. -/
theorem regRq_gain (z buf : alloc.vec.Vec Std.U64) (g : ℕ) (ci row : ring.Rq)
    (hci : Wf ci) (hrow : Wf row) (e : ℕ)
    (h : ∀ w, w < N → ((reg z g w : ℕ) : ZMod q)
      = ((reg buf g w : ℕ) : ZMod q) + negConvF (coeffK ci) (nib row e) w) :
    regRq z g = regRq buf g + toRq ci * digitRq row e := by
  apply Subtype.ext
  rw [CompPoly.CPolynomial.eq_iff_coeff]
  intro k
  rw [Rq.add_val, CompPoly.CPolynomial.coeff_add]
  unfold regRq digitRq
  rw [Rq.ofFinCoeff_coeff Φ _ N_le_degree, Rq.ofFinCoeff_coeff Φ _ N_le_degree]
  by_cases hk : k < N
  · rw [if_pos hk, if_pos hk, h k hk,
      coeff_toRq_mul_fin ci hci (nib row e) (fun i hi => nib_of_ge row hrow e hi) hk]
  · rw [if_neg hk, if_neg hk, zero_add]
    exact (Rq.coeff_eq_zero_of_natDegree_le Φ (toRq ci * Rq.ofFinCoeff Φ N (nib row e))
      (by rw [phi_natDegree]; omega)).symm

/-- A region whose words did not move did not move as a ring element. -/
theorem regRq_congr (z buf : alloc.vec.Vec Std.U64) (g : ℕ)
    (h : ∀ w, w < N → reg z g w = reg buf g w) : regRq z g = regRq buf g := by
  unfold regRq
  exact ofFinCoeff_congr (fun w hw => by rw [h w hw])

/-- Reducing every word mod `q` does not move a region as a ring element. -/
theorem regRq_congr_mod (z buf : alloc.vec.Vec Std.U64) (g : ℕ)
    (h : ∀ w, w < N → ((reg z g w : ℕ) : ZMod q) = ((reg buf g w : ℕ) : ZMod q)) :
    regRq z g = regRq buf g := by
  unfold regRq
  exact ofFinCoeff_congr (fun w hw => h w hw)

/-! ## 5. `z_pass`: one signed pass over the eight regions of a row

The invariant is `short_pass_off_loop*_spec`'s, once per region, plus a frame:
every word outside the row's eight regions is unchanged. `Frame buf z g0` says
exactly that. -/

/-- Words outside regions `[g0, g0 + 8)` agree. -/
def Frame (buf z : alloc.vec.Vec Std.U64) (g0 : ℕ) : Prop :=
  ∀ t, (∀ e, e < 8 → ∀ w, w < N → t ≠ (g0 + e) * S + w) → bufN z t = bufN buf t

theorem Frame_refl (buf : alloc.vec.Vec Std.U64) (g0 : ℕ) : Frame buf buf g0 :=
  fun _ _ => rfl

theorem Frame_trans {a b c : alloc.vec.Vec Std.U64} {g0 : ℕ}
    (h1 : Frame a b g0) (h2 : Frame b c g0) : Frame a c g0 :=
  fun t ht => by rw [h2 t ht, h1 t ht]

/-- The frame is preserved by a write inside one of the row's regions. -/
theorem Frame_set {buf z : alloc.vec.Vec Std.U64} {g0 : ℕ} (h : Frame buf z g0)
    {tU : Std.Usize} {x : Std.U64} {e w : ℕ} (he : e < 8) (hw : w < N)
    (ht : tU.val = (g0 + e) * S + w) : Frame buf (z.set tU x) g0 := by
  intro t htn
  rw [bufN_set_ne (by intro hc; exact htn e he w hw (by rw [hc, ht]))]
  exact h t htn

/-- A region outside the row is read unchanged through the frame. -/
theorem Frame_reg {buf z : alloc.vec.Vec Std.U64} {g0 : ℕ} (h : Frame buf z g0) {g w : ℕ}
    (hg : g < g0 ∨ g0 + 8 ≤ g) (hw : w < N) : reg z g w = reg buf g w := by
  unfold reg
  apply h
  intro e he w' hw' hc
  have hS : w < S := by unfold S; omega
  have hS' : w' < S := by unfold S; omega
  have := reg_index_inj hS hS' hc
  omega

/-- A region of zeros is the zero ring element. -/
theorem regRq_zero (buf : alloc.vec.Vec Std.U64) (g : ℕ)
    (h : ∀ w, w < N → reg buf g w = 0) : regRq buf g = 0 := by
  unfold regRq
  apply Subtype.ext
  rw [CompPoly.CPolynomial.eq_iff_coeff]
  intro k
  rw [Rq.ofFinCoeff_coeff Φ _ N_le_degree, Rq.zero_val, CompPoly.CPolynomial.coeff_zero]
  by_cases hk : k < N
  · rw [if_pos hk, h k hk]; simp
  · rw [if_neg hk]

/-- **Progress through one step's eight writes.** Regions `[g0, g0 + m)` of
`z` have absorbed source index `ii`, regions `[g0 + m, g0 + 8)` have not. At
`m = 0` this is the loop invariant at `ii`; at `m = 8` it is the invariant at
`ii + 1`. -/
def Prog (words : alloc.vec.Vec Std.U64) (kk : ℕ) (negt : Bool) (g0 : ℕ)
    (base : ℕ → ℕ → ZMod q) (B ii m : ℕ) (z : alloc.vec.Vec Std.U64) : Prop :=
  ∀ e, e < 8 → ∀ w, w < N →
    reg z (g0 + e) w ≤ (if srcOf kk w < (if e < m then ii + 1 else ii) then B + q else B)
    ∧ ((reg z (g0 + e) w : ℕ) : ZMod q)
        = applied (base e) (nibW words e) kk negt (if e < m then ii + 1 else ii) w

theorem Prog_zero_iff (words : alloc.vec.Vec Std.U64) (kk : ℕ) (negt : Bool) (g0 : ℕ)
    (base : ℕ → ℕ → ZMod q) (B ii : ℕ) (z : alloc.vec.Vec Std.U64) :
    Prog words kk negt g0 base B ii 0 z ↔
      (∀ e, e < 8 → ∀ w, w < N →
        reg z (g0 + e) w ≤ (if srcOf kk w < ii then B + q else B))
      ∧ ∀ e, e < 8 → ∀ w, w < N → ((reg z (g0 + e) w : ℕ) : ZMod q)
          = applied (base e) (nibW words e) kk negt ii w := by
  unfold Prog
  simp only [Nat.not_lt_zero, if_false]
  exact ⟨fun h => ⟨fun e he w hw => (h e he w hw).1, fun e he w hw => (h e he w hw).2⟩,
    fun h e he w hw => ⟨h.1 e he w hw, h.2 e he w hw⟩⟩

theorem Prog_eight (words : alloc.vec.Vec Std.U64) (kk : ℕ) (negt : Bool) (g0 : ℕ)
    (base : ℕ → ℕ → ZMod q) (B ii : ℕ) (z : alloc.vec.Vec Std.U64)
    (h : Prog words kk negt g0 base B ii 8 z) :
    (∀ e, e < 8 → ∀ w, w < N →
        reg z (g0 + e) w ≤ (if srcOf kk w < ii + 1 then B + q else B))
      ∧ ∀ e, e < 8 → ∀ w, w < N → ((reg z (g0 + e) w : ℕ) : ZMod q)
          = applied (base e) (nibW words e) kk negt (ii + 1) w := by
  refine ⟨fun e he w hw => ?_, fun e he w hw => ?_⟩
  · have := (h e he w hw).1; rwa [if_pos he] at this
  · have := (h e he w hw).2; rwa [if_pos he] at this

/-- **One write** of the eight: region `g0 + m` at `dstOf kk ii` gains the
signed digit, every other word is untouched, and the progress counter
advances. `offWrite_step` at a region offset, for a buffer of `8` regions. -/
theorem write_one (words : alloc.vec.Vec Std.U64) (kk : ℕ) (negt : Bool) (g0 : ℕ)
    (base : ℕ → ℕ → ZMod q) (B ii m : ℕ) (d : alloc.vec.Vec Std.U64)
    (wU : Std.Usize) (addU nvU : Std.U64) (dv : ℕ)
    (hk : kk < N) (hii : ii < N) (hm : m < 8)
    (hdv : dv < q) (hdval : ((dv : ℕ) : ZMod q) = nibW words m ii)
    (hprog : Prog words kk negt g0 base B ii m d)
    (hwv : wU.val = (g0 + m) * S + dstOf kk ii)
    (hwlt : wU.val < d.val.length)
    (haddv : addU.val = offStep negt kk ii dv)
    (hnvv : nvU.val = reg d (g0 + m) (dstOf kk ii) + addU.val) :
    Prog words kk negt g0 base B ii (m + 1) (d.set wU nvU) := by
  have hdst : dstOf kk ii < N := dstOf_lt hk hii
  have hsrc : srcOf kk (dstOf kk ii) = ii := srcOf_dstOf hk hii
  have haddq : addU.val ≤ q := by rw [haddv]; exact offStep_le negt kk ii dv hdv
  intro e he w hw
  obtain ⟨hb, hv⟩ := hprog e he w hw
  by_cases hem : e = m
  · subst hem
    rw [if_neg (Nat.lt_irrefl e)] at hb hv
    rw [if_pos (Nat.lt_succ_self e)]
    by_cases hwd : w = dstOf kk ii
    · subst hwd
      rw [reg_set_eq hwv hwlt, hnvv]
      refine ⟨?_, ?_⟩
      · rw [if_pos (by rw [hsrc]; omega)]
        rw [if_neg (by rw [hsrc]; omega)] at hb
        omega
      · rw [applied_succ, hsrc, if_pos rfl]
        push_cast
        rw [hv, haddv, offStep_cast negt kk ii dv hk hii hdv, hdval]
    · have hne : (g0 + e) * S + w ≠ wU.val := by
        rw [hwv]; intro hc; exact hwd (by omega)
      rw [reg_set_ne hne]
      have hsne : srcOf kk w ≠ ii := by
        intro hc; exact hwd (by rw [← hc, dstOf_srcOf hk hw])
      refine ⟨?_, ?_⟩
      · by_cases hlt : srcOf kk w < ii
        · rw [if_pos (by omega)]; rwa [if_pos hlt] at hb
        · rw [if_neg (by omega)]; rwa [if_neg hlt] at hb
      · rw [applied_succ, if_neg hsne, add_zero]; exact hv
  · have hne : (g0 + e) * S + w ≠ wU.val := by
      rw [hwv]; intro hc
      have hS : w < S := by unfold S; omega
      have hS' : dstOf kk ii < S := by unfold S; omega
      exact hem (by have := reg_index_inj hS hS' hc; omega)
    rw [reg_set_ne hne]
    rcases Nat.lt_or_ge e m with hlt | hge
    · have h1 : (if e < m + 1 then ii + 1 else ii) = ii + 1 := if_pos (by omega)
      rw [if_pos hlt] at hb hv; rw [h1]; exact ⟨hb, hv⟩
    · have hnl : ¬ e < m := by omega
      have h1 : (if e < m + 1 then ii + 1 else ii) = ii := if_neg (by omega)
      rw [if_neg hnl] at hb hv; rw [h1]; exact ⟨hb, hv⟩

/-- What one write needs from `Prog`: its address is inside the buffer and the
word there is still within `B`. -/
theorem write_facts (words : alloc.vec.Vec Std.U64) (kk : ℕ) (negt : Bool) (g0 : ℕ)
    (base : ℕ → ℕ → ZMod q) (B ii m : ℕ) (d : alloc.vec.Vec Std.U64)
    (hprog : Prog words kk negt g0 base B ii m d)
    (hk : kk < N) (hii : ii < N) (hm : m < 8) (hcap : (g0 + 8) * S ≤ d.val.length) :
    (g0 + m) * S + dstOf kk ii < d.val.length ∧ reg d (g0 + m) (dstOf kk ii) ≤ B := by
  have hdst : dstOf kk ii < N := dstOf_lt hk hii
  have hsrc : srcOf kk (dstOf kk ii) = ii := srcOf_dstOf hk hii
  refine ⟨?_, ?_⟩
  · have h1 : (g0 + m) * S + dstOf kk ii < (g0 + m + 1) * S := by
      rw [Nat.succ_mul]; unfold S; omega
    have h2 : (g0 + m + 1) * S ≤ (g0 + 8) * S := Nat.mul_le_mul_right _ (by omega)
    omega
  · have := (hprog m hm (dstOf kk ii) hdst).1
    rw [if_neg (Nat.lt_irrefl m), hsrc, if_neg (Nat.lt_irrefl ii)] at this
    exact this

set_option maxHeartbeats 2000000 in
/-- **The low run** of `z_pass`: `i < N - k`, destination `k + i` in each region,
sign `negt`'s alone. -/
theorem z_pass_loop0_spec (words : alloc.vec.Vec Std.U64) (kU : Std.Usize) (negt : Bool)
    (rbU : Std.Usize) (qU : Std.U64) (strideU limU : Std.Usize)
    (out : alloc.vec.Vec Std.U64) (iU : Std.Usize)
    (buf0 : alloc.vec.Vec Std.U64) (g0 : ℕ) (base : ℕ → ℕ → ZMod q) (B : ℕ)
    (hwl : words.val.length = N) (hwlt : ∀ i, i < N → bufN words i < q)
    (hq : qU.val = q) (hstride : strideU.val = S) (hlim : limU.val = N - kU.val)
    (hk : kU.val < N) (hrb : rbU.val = g0 * S)
    (hi : iU.val ≤ limU.val) (hlen : out.val.length = buf0.val.length)
    (hcap : (g0 + 8) * S ≤ buf0.val.length) (hB : B + q ≤ Std.U64.max)
    (hbnd : ∀ e, e < 8 → ∀ w, w < N →
      reg out (g0 + e) w ≤ (if srcOf kU.val w < iU.val then B + q else B))
    (hval : ∀ e, e < 8 → ∀ w, w < N → ((reg out (g0 + e) w : ℕ) : ZMod q)
      = applied (base e) (nibW words e) kU.val negt iU.val w)
    (hfr : Frame buf0 out g0) :
    quadeval.z_pass_loop0 words kU negt rbU qU strideU out limU iU
      ⦃ z => z.val.length = buf0.val.length
        ∧ (∀ e, e < 8 → ∀ w, w < N →
            reg z (g0 + e) w ≤ (if srcOf kU.val w < limU.val then B + q else B))
        ∧ (∀ e, e < 8 → ∀ w, w < N → ((reg z (g0 + e) w : ℕ) : ZMod q)
            = applied (base e) (nibW words e) kU.val negt limU.val w)
        ∧ Frame buf0 z g0 ⦄ := by
  have hS : S = 1040 := rfl
  have hq16 : 16 ≤ q := by norm_num [HachiEquiv.Field.q]
  rw [quadeval.z_pass_loop0]
  apply loop.spec_decr_nat (fun t => limU.val - t.2.val)
    (fun t => t.2.val ≤ limU.val ∧ t.1.val.length = buf0.val.length
      ∧ (∀ e, e < 8 → ∀ w, w < N →
          reg t.1 (g0 + e) w ≤ (if srcOf kU.val w < t.2.val then B + q else B))
      ∧ (∀ e, e < 8 → ∀ w, w < N → ((reg t.1 (g0 + e) w : ℕ) : ZMod q)
          = applied (base e) (nibW words e) kU.val negt t.2.val w)
      ∧ Frame buf0 t.1 g0)
  · rintro ⟨d, ii⟩ ⟨hii, hdl, hdb, hdv, hdf⟩
    dsimp only at hii hdl hdb hdv hdf
    simp only [quadeval.z_pass_loop0.body]
    by_cases hlt : ii < limU
    · rw [if_pos hlt]
      have hiilim : ii.val < limU.val := by scalar_tac
      have hiilt : ii.val < N := by omega
      have hnowrap : ¬ N ≤ kU.val + ii.val := by omega
      have hdst : dstOf kU.val ii.val = kU.val + ii.val := by
        unfold dstOf; rw [if_pos (by omega)]
      have hcapd : (g0 + 8) * S ≤ d.val.length := by rw [hdl]; exact hcap
      have hrb' : rbU.val = g0 * 1040 := by rw [hrb, hS]
      have hstride' : strideU.val = 1040 := by rw [hstride, hS]
      have hwb : ii.val < words.val.length := by rw [hwl]; exact hiilt
      step as ⟨x, hx⟩
      have hxv : x.val = bufN words ii.val := by
        rw [hx, ← bufN_of_lt (v := words) (w := ii.val) hwb]
      have hxlt : x.val < q := by rw [hxv]; exact hwlt ii.val hiilt
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
      have hd0v : d0.val = x.val / 16 ^ 0 % 16 := by rw [hd0]; simp
      have hd1v : d1.val = x.val / 16 ^ 1 % 16 := by rw [hd1, hq1]; norm_num
      have hd2v : d2.val = x.val / 16 ^ 2 % 16 := by rw [hd2, hq2]; norm_num
      have hd3v : d3.val = x.val / 16 ^ 3 % 16 := by rw [hd3, hq3]; norm_num
      have hd4v : d4.val = x.val / 16 ^ 4 % 16 := by rw [hd4, hq4]; norm_num
      have hd5v : d5.val = x.val / 16 ^ 5 % 16 := by rw [hd5, hq5]; norm_num
      have hd6v : d6.val = x.val / 16 ^ 6 % 16 := by rw [hd6, hq6]; norm_num
      have hd7v : d7.val = x.val / 16 ^ 7 % 16 := by rw [hd7, hq7]; norm_num
      have hd0lt : d0.val < 16 := by rw [hd0v]; exact Nat.mod_lt _ (by norm_num)
      have hd0q : d0.val < q := by have := hd0lt; omega
      have hd0nib : ((d0.val : ℕ) : ZMod q) = nibW words 0 ii.val := by
        unfold nibW; rw [hd0v, hxv]
      have hd1lt : d1.val < 16 := by rw [hd1v]; exact Nat.mod_lt _ (by norm_num)
      have hd1q : d1.val < q := by have := hd1lt; omega
      have hd1nib : ((d1.val : ℕ) : ZMod q) = nibW words 1 ii.val := by
        unfold nibW; rw [hd1v, hxv]
      have hd2lt : d2.val < 16 := by rw [hd2v]; exact Nat.mod_lt _ (by norm_num)
      have hd2q : d2.val < q := by have := hd2lt; omega
      have hd2nib : ((d2.val : ℕ) : ZMod q) = nibW words 2 ii.val := by
        unfold nibW; rw [hd2v, hxv]
      have hd3lt : d3.val < 16 := by rw [hd3v]; exact Nat.mod_lt _ (by norm_num)
      have hd3q : d3.val < q := by have := hd3lt; omega
      have hd3nib : ((d3.val : ℕ) : ZMod q) = nibW words 3 ii.val := by
        unfold nibW; rw [hd3v, hxv]
      have hd4lt : d4.val < 16 := by rw [hd4v]; exact Nat.mod_lt _ (by norm_num)
      have hd4q : d4.val < q := by have := hd4lt; omega
      have hd4nib : ((d4.val : ℕ) : ZMod q) = nibW words 4 ii.val := by
        unfold nibW; rw [hd4v, hxv]
      have hd5lt : d5.val < 16 := by rw [hd5v]; exact Nat.mod_lt _ (by norm_num)
      have hd5q : d5.val < q := by have := hd5lt; omega
      have hd5nib : ((d5.val : ℕ) : ZMod q) = nibW words 5 ii.val := by
        unfold nibW; rw [hd5v, hxv]
      have hd6lt : d6.val < 16 := by rw [hd6v]; exact Nat.mod_lt _ (by norm_num)
      have hd6q : d6.val < q := by have := hd6lt; omega
      have hd6nib : ((d6.val : ℕ) : ZMod q) = nibW words 6 ii.val := by
        unfold nibW; rw [hd6v, hxv]
      have hd7lt : d7.val < 16 := by rw [hd7v]; exact Nat.mod_lt _ (by norm_num)
      have hd7q : d7.val < q := by have := hd7lt; omega
      have hd7nib : ((d7.val : ℕ) : ZMod q) = nibW words 7 ii.val := by
        unfold nibW; rw [hd7v, hxv]
      cases negt with
      | true =>
        simp only [↓reduceIte]
        step as ⟨a0, ha0⟩
        have ha0v : a0.val = offStep true kU.val ii.val d0.val := by
          unfold offStep; simp only [hnowrap, ↓reduceIte, ha0, hq]
        step as ⟨a1, ha1⟩
        have ha1v : a1.val = offStep true kU.val ii.val d1.val := by
          unfold offStep; simp only [hnowrap, ↓reduceIte, ha1, hq]
        step as ⟨a2, ha2⟩
        have ha2v : a2.val = offStep true kU.val ii.val d2.val := by
          unfold offStep; simp only [hnowrap, ↓reduceIte, ha2, hq]
        step as ⟨a3, ha3⟩
        have ha3v : a3.val = offStep true kU.val ii.val d3.val := by
          unfold offStep; simp only [hnowrap, ↓reduceIte, ha3, hq]
        step as ⟨a4, ha4⟩
        have ha4v : a4.val = offStep true kU.val ii.val d4.val := by
          unfold offStep; simp only [hnowrap, ↓reduceIte, ha4, hq]
        step as ⟨a5, ha5⟩
        have ha5v : a5.val = offStep true kU.val ii.val d5.val := by
          unfold offStep; simp only [hnowrap, ↓reduceIte, ha5, hq]
        step as ⟨a6, ha6⟩
        have ha6v : a6.val = offStep true kU.val ii.val d6.val := by
          unfold offStep; simp only [hnowrap, ↓reduceIte, ha6, hq]
        step as ⟨a7, ha7⟩
        have ha7v : a7.val = offStep true kU.val ii.val d7.val := by
          unfold offStep; simp only [hnowrap, ↓reduceIte, ha7, hq]
        step as ⟨i8, hi8⟩
        step as ⟨w0, hw0⟩
        have hwv0' : w0.val = (g0 + 0) * 1040 + dstOf kU.val ii.val := by omega
        have hwv0 : w0.val = (g0 + 0) * S + dstOf kU.val ii.val := by rw [hS]; exact hwv0'
        step as ⟨w1, hw1⟩
        have hwv1' : w1.val = (g0 + 1) * 1040 + dstOf kU.val ii.val := by omega
        have hwv1 : w1.val = (g0 + 1) * S + dstOf kU.val ii.val := by rw [hS]; exact hwv1'
        step as ⟨w2, hw2⟩
        have hwv2' : w2.val = (g0 + 2) * 1040 + dstOf kU.val ii.val := by omega
        have hwv2 : w2.val = (g0 + 2) * S + dstOf kU.val ii.val := by rw [hS]; exact hwv2'
        step as ⟨w3, hw3⟩
        have hwv3' : w3.val = (g0 + 3) * 1040 + dstOf kU.val ii.val := by omega
        have hwv3 : w3.val = (g0 + 3) * S + dstOf kU.val ii.val := by rw [hS]; exact hwv3'
        step as ⟨w4, hw4⟩
        have hwv4' : w4.val = (g0 + 4) * 1040 + dstOf kU.val ii.val := by omega
        have hwv4 : w4.val = (g0 + 4) * S + dstOf kU.val ii.val := by rw [hS]; exact hwv4'
        step as ⟨w5, hw5⟩
        have hwv5' : w5.val = (g0 + 5) * 1040 + dstOf kU.val ii.val := by omega
        have hwv5 : w5.val = (g0 + 5) * S + dstOf kU.val ii.val := by rw [hS]; exact hwv5'
        step as ⟨w6, hw6⟩
        have hwv6' : w6.val = (g0 + 6) * 1040 + dstOf kU.val ii.val := by omega
        have hwv6 : w6.val = (g0 + 6) * S + dstOf kU.val ii.val := by rw [hS]; exact hwv6'
        step as ⟨w7, hw7⟩
        have hwv7' : w7.val = (g0 + 7) * 1040 + dstOf kU.val ii.val := by omega
        have hwv7 : w7.val = (g0 + 7) * S + dstOf kU.val ii.val := by rw [hS]; exact hwv7'
        have hp0 : Prog words kU.val true g0 base B ii.val 0 d :=
          (Prog_zero_iff words kU.val true g0 base B ii.val d).mpr ⟨hdb, hdv⟩
        have hlen0 : d.val.length = d.val.length := rfl
        obtain ⟨hidx0, hcur0⟩ := write_facts words kU.val true g0 base B ii.val 0 d hp0 hk hiilt (by decide) (by rw [hlen0]; exact hcapd)
        have hwlt0 : w0.val < d.val.length := by rw [hwv0]; exact hidx0
        step as ⟨c0, hc0⟩
        have hc0v : c0.val = reg d (g0 + 0) (dstOf kU.val ii.val) := by
          unfold reg; rw [hc0, ← bufN_of_lt (v := d) (w := w0.val) hwlt0, hwv0]
        have hbnd0 : c0.val + a0.val ≤ Std.U64.max := by
          rw [hc0v]; have := offStep_le true kU.val ii.val d0.val hd0q; rw [← ha0v] at this; omega
        step as ⟨v0, hv0⟩
        step as ⟨xw0, back0, hxw0, hback0⟩
        rw [hback0]
        have hp1 : Prog words kU.val true g0 base B ii.val 1 (d.set w0 v0) :=
          write_one words kU.val true g0 base B ii.val 0 d w0 a0 v0 d0.val hk hiilt (by decide) hd0q hd0nib hp0 hwv0 hwlt0 ha0v (by omega)
        have hlen1 : (d.set w0 v0).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]
        have hfr1 : Frame buf0 (d.set w0 v0) g0 :=
          Frame_set hdf (by norm_num : (0 : ℕ) < 8) (dstOf_lt hk hiilt) hwv0
        obtain ⟨hidx1, hcur1⟩ := write_facts words kU.val true g0 base B ii.val 1 (d.set w0 v0) hp1 hk hiilt (by decide) (by rw [hlen1]; exact hcapd)
        have hwlt1 : w1.val < (d.set w0 v0).val.length := by rw [hwv1]; exact hidx1
        step as ⟨c1, hc1⟩
        have hc1v : c1.val = reg (d.set w0 v0) (g0 + 1) (dstOf kU.val ii.val) := by
          unfold reg; rw [hc1, ← bufN_of_lt (v := (d.set w0 v0)) (w := w1.val) hwlt1, hwv1]
        have hbnd1 : c1.val + a1.val ≤ Std.U64.max := by
          rw [hc1v]; have := offStep_le true kU.val ii.val d1.val hd1q; rw [← ha1v] at this; omega
        step as ⟨v1, hv1⟩
        step as ⟨xw1, back1, hxw1, hback1⟩
        rw [hback1]
        have hp2 : Prog words kU.val true g0 base B ii.val 2 ((d.set w0 v0).set w1 v1) :=
          write_one words kU.val true g0 base B ii.val 1 (d.set w0 v0) w1 a1 v1 d1.val hk hiilt (by decide) hd1q hd1nib hp1 hwv1 hwlt1 ha1v (by omega)
        have hlen2 : ((d.set w0 v0).set w1 v1).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen1
        have hfr2 : Frame buf0 ((d.set w0 v0).set w1 v1) g0 :=
          Frame_set hfr1 (by norm_num : (1 : ℕ) < 8) (dstOf_lt hk hiilt) hwv1
        obtain ⟨hidx2, hcur2⟩ := write_facts words kU.val true g0 base B ii.val 2 ((d.set w0 v0).set w1 v1) hp2 hk hiilt (by decide) (by rw [hlen2]; exact hcapd)
        have hwlt2 : w2.val < ((d.set w0 v0).set w1 v1).val.length := by rw [hwv2]; exact hidx2
        step as ⟨c2, hc2⟩
        have hc2v : c2.val = reg ((d.set w0 v0).set w1 v1) (g0 + 2) (dstOf kU.val ii.val) := by
          unfold reg; rw [hc2, ← bufN_of_lt (v := ((d.set w0 v0).set w1 v1)) (w := w2.val) hwlt2, hwv2]
        have hbnd2 : c2.val + a2.val ≤ Std.U64.max := by
          rw [hc2v]; have := offStep_le true kU.val ii.val d2.val hd2q; rw [← ha2v] at this; omega
        step as ⟨v2, hv2⟩
        step as ⟨xw2, back2, hxw2, hback2⟩
        rw [hback2]
        have hp3 : Prog words kU.val true g0 base B ii.val 3 (((d.set w0 v0).set w1 v1).set w2 v2) :=
          write_one words kU.val true g0 base B ii.val 2 ((d.set w0 v0).set w1 v1) w2 a2 v2 d2.val hk hiilt (by decide) hd2q hd2nib hp2 hwv2 hwlt2 ha2v (by omega)
        have hlen3 : (((d.set w0 v0).set w1 v1).set w2 v2).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen2
        have hfr3 : Frame buf0 (((d.set w0 v0).set w1 v1).set w2 v2) g0 :=
          Frame_set hfr2 (by norm_num : (2 : ℕ) < 8) (dstOf_lt hk hiilt) hwv2
        obtain ⟨hidx3, hcur3⟩ := write_facts words kU.val true g0 base B ii.val 3 (((d.set w0 v0).set w1 v1).set w2 v2) hp3 hk hiilt (by decide) (by rw [hlen3]; exact hcapd)
        have hwlt3 : w3.val < (((d.set w0 v0).set w1 v1).set w2 v2).val.length := by rw [hwv3]; exact hidx3
        step as ⟨c3, hc3⟩
        have hc3v : c3.val = reg (((d.set w0 v0).set w1 v1).set w2 v2) (g0 + 3) (dstOf kU.val ii.val) := by
          unfold reg; rw [hc3, ← bufN_of_lt (v := (((d.set w0 v0).set w1 v1).set w2 v2)) (w := w3.val) hwlt3, hwv3]
        have hbnd3 : c3.val + a3.val ≤ Std.U64.max := by
          rw [hc3v]; have := offStep_le true kU.val ii.val d3.val hd3q; rw [← ha3v] at this; omega
        step as ⟨v3, hv3⟩
        step as ⟨xw3, back3, hxw3, hback3⟩
        rw [hback3]
        have hp4 : Prog words kU.val true g0 base B ii.val 4 ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) :=
          write_one words kU.val true g0 base B ii.val 3 (((d.set w0 v0).set w1 v1).set w2 v2) w3 a3 v3 d3.val hk hiilt (by decide) hd3q hd3nib hp3 hwv3 hwlt3 ha3v (by omega)
        have hlen4 : ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen3
        have hfr4 : Frame buf0 ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) g0 :=
          Frame_set hfr3 (by norm_num : (3 : ℕ) < 8) (dstOf_lt hk hiilt) hwv3
        obtain ⟨hidx4, hcur4⟩ := write_facts words kU.val true g0 base B ii.val 4 ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) hp4 hk hiilt (by decide) (by rw [hlen4]; exact hcapd)
        have hwlt4 : w4.val < ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).val.length := by rw [hwv4]; exact hidx4
        step as ⟨c4, hc4⟩
        have hc4v : c4.val = reg ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) (g0 + 4) (dstOf kU.val ii.val) := by
          unfold reg; rw [hc4, ← bufN_of_lt (v := ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3)) (w := w4.val) hwlt4, hwv4]
        have hbnd4 : c4.val + a4.val ≤ Std.U64.max := by
          rw [hc4v]; have := offStep_le true kU.val ii.val d4.val hd4q; rw [← ha4v] at this; omega
        step as ⟨v4, hv4⟩
        step as ⟨xw4, back4, hxw4, hback4⟩
        rw [hback4]
        have hp5 : Prog words kU.val true g0 base B ii.val 5 (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) :=
          write_one words kU.val true g0 base B ii.val 4 ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) w4 a4 v4 d4.val hk hiilt (by decide) hd4q hd4nib hp4 hwv4 hwlt4 ha4v (by omega)
        have hlen5 : (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen4
        have hfr5 : Frame buf0 (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) g0 :=
          Frame_set hfr4 (by norm_num : (4 : ℕ) < 8) (dstOf_lt hk hiilt) hwv4
        obtain ⟨hidx5, hcur5⟩ := write_facts words kU.val true g0 base B ii.val 5 (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) hp5 hk hiilt (by decide) (by rw [hlen5]; exact hcapd)
        have hwlt5 : w5.val < (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).val.length := by rw [hwv5]; exact hidx5
        step as ⟨c5, hc5⟩
        have hc5v : c5.val = reg (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) (g0 + 5) (dstOf kU.val ii.val) := by
          unfold reg; rw [hc5, ← bufN_of_lt (v := (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4)) (w := w5.val) hwlt5, hwv5]
        have hbnd5 : c5.val + a5.val ≤ Std.U64.max := by
          rw [hc5v]; have := offStep_le true kU.val ii.val d5.val hd5q; rw [← ha5v] at this; omega
        step as ⟨v5, hv5⟩
        step as ⟨xw5, back5, hxw5, hback5⟩
        rw [hback5]
        have hp6 : Prog words kU.val true g0 base B ii.val 6 ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) :=
          write_one words kU.val true g0 base B ii.val 5 (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) w5 a5 v5 d5.val hk hiilt (by decide) hd5q hd5nib hp5 hwv5 hwlt5 ha5v (by omega)
        have hlen6 : ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen5
        have hfr6 : Frame buf0 ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) g0 :=
          Frame_set hfr5 (by norm_num : (5 : ℕ) < 8) (dstOf_lt hk hiilt) hwv5
        obtain ⟨hidx6, hcur6⟩ := write_facts words kU.val true g0 base B ii.val 6 ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) hp6 hk hiilt (by decide) (by rw [hlen6]; exact hcapd)
        have hwlt6 : w6.val < ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).val.length := by rw [hwv6]; exact hidx6
        step as ⟨c6, hc6⟩
        have hc6v : c6.val = reg ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) (g0 + 6) (dstOf kU.val ii.val) := by
          unfold reg; rw [hc6, ← bufN_of_lt (v := ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5)) (w := w6.val) hwlt6, hwv6]
        have hbnd6 : c6.val + a6.val ≤ Std.U64.max := by
          rw [hc6v]; have := offStep_le true kU.val ii.val d6.val hd6q; rw [← ha6v] at this; omega
        step as ⟨v6, hv6⟩
        step as ⟨xw6, back6, hxw6, hback6⟩
        rw [hback6]
        have hp7 : Prog words kU.val true g0 base B ii.val 7 (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) :=
          write_one words kU.val true g0 base B ii.val 6 ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) w6 a6 v6 d6.val hk hiilt (by decide) hd6q hd6nib hp6 hwv6 hwlt6 ha6v (by omega)
        have hlen7 : (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen6
        have hfr7 : Frame buf0 (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) g0 :=
          Frame_set hfr6 (by norm_num : (6 : ℕ) < 8) (dstOf_lt hk hiilt) hwv6
        obtain ⟨hidx7, hcur7⟩ := write_facts words kU.val true g0 base B ii.val 7 (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) hp7 hk hiilt (by decide) (by rw [hlen7]; exact hcapd)
        have hwlt7 : w7.val < (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).val.length := by rw [hwv7]; exact hidx7
        step as ⟨c7, hc7⟩
        have hc7v : c7.val = reg (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) (g0 + 7) (dstOf kU.val ii.val) := by
          unfold reg; rw [hc7, ← bufN_of_lt (v := (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6)) (w := w7.val) hwlt7, hwv7]
        have hbnd7 : c7.val + a7.val ≤ Std.U64.max := by
          rw [hc7v]; have := offStep_le true kU.val ii.val d7.val hd7q; rw [← ha7v] at this; omega
        step as ⟨v7, hv7⟩
        step as ⟨xw7, back7, hxw7, hback7⟩
        rw [hback7]
        have hp8 : Prog words kU.val true g0 base B ii.val 8 ((((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).set w7 v7) :=
          write_one words kU.val true g0 base B ii.val 7 (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) w7 a7 v7 d7.val hk hiilt (by decide) hd7q hd7nib hp7 hwv7 hwlt7 ha7v (by omega)
        have hlen8 : ((((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).set w7 v7).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen7
        have hfr8 : Frame buf0 ((((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).set w7 v7) g0 :=
          Frame_set hfr7 (by norm_num : (7 : ℕ) < 8) (dstOf_lt hk hiilt) hwv7
        have hmaxb : ii.val + 1 ≤ Std.Usize.max := by have := usize_max_ge; have h3 : N = 1024 := rfl; omega
        step as ⟨ii1, hii1⟩
        obtain ⟨hfb, hfv⟩ := Prog_eight words kU.val true g0 base B ii.val ((((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).set w7 v7) hp8
        refine ⟨by omega, by rw [hlen8]; exact hdl, by rw [hii1]; exact hfb, by rw [hii1]; exact hfv, hfr8, by omega⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, bind_tc_ok]
        have ha0v : d0.val = offStep false kU.val ii.val d0.val := by
          unfold offStep; simp only [hnowrap, ↓reduceIte, Bool.false_eq_true]
        have ha1v : d1.val = offStep false kU.val ii.val d1.val := by
          unfold offStep; simp only [hnowrap, ↓reduceIte, Bool.false_eq_true]
        have ha2v : d2.val = offStep false kU.val ii.val d2.val := by
          unfold offStep; simp only [hnowrap, ↓reduceIte, Bool.false_eq_true]
        have ha3v : d3.val = offStep false kU.val ii.val d3.val := by
          unfold offStep; simp only [hnowrap, ↓reduceIte, Bool.false_eq_true]
        have ha4v : d4.val = offStep false kU.val ii.val d4.val := by
          unfold offStep; simp only [hnowrap, ↓reduceIte, Bool.false_eq_true]
        have ha5v : d5.val = offStep false kU.val ii.val d5.val := by
          unfold offStep; simp only [hnowrap, ↓reduceIte, Bool.false_eq_true]
        have ha6v : d6.val = offStep false kU.val ii.val d6.val := by
          unfold offStep; simp only [hnowrap, ↓reduceIte, Bool.false_eq_true]
        have ha7v : d7.val = offStep false kU.val ii.val d7.val := by
          unfold offStep; simp only [hnowrap, ↓reduceIte, Bool.false_eq_true]
        step as ⟨i8, hi8⟩
        step as ⟨w0, hw0⟩
        have hwv0' : w0.val = (g0 + 0) * 1040 + dstOf kU.val ii.val := by omega
        have hwv0 : w0.val = (g0 + 0) * S + dstOf kU.val ii.val := by rw [hS]; exact hwv0'
        step as ⟨w1, hw1⟩
        have hwv1' : w1.val = (g0 + 1) * 1040 + dstOf kU.val ii.val := by omega
        have hwv1 : w1.val = (g0 + 1) * S + dstOf kU.val ii.val := by rw [hS]; exact hwv1'
        step as ⟨w2, hw2⟩
        have hwv2' : w2.val = (g0 + 2) * 1040 + dstOf kU.val ii.val := by omega
        have hwv2 : w2.val = (g0 + 2) * S + dstOf kU.val ii.val := by rw [hS]; exact hwv2'
        step as ⟨w3, hw3⟩
        have hwv3' : w3.val = (g0 + 3) * 1040 + dstOf kU.val ii.val := by omega
        have hwv3 : w3.val = (g0 + 3) * S + dstOf kU.val ii.val := by rw [hS]; exact hwv3'
        step as ⟨w4, hw4⟩
        have hwv4' : w4.val = (g0 + 4) * 1040 + dstOf kU.val ii.val := by omega
        have hwv4 : w4.val = (g0 + 4) * S + dstOf kU.val ii.val := by rw [hS]; exact hwv4'
        step as ⟨w5, hw5⟩
        have hwv5' : w5.val = (g0 + 5) * 1040 + dstOf kU.val ii.val := by omega
        have hwv5 : w5.val = (g0 + 5) * S + dstOf kU.val ii.val := by rw [hS]; exact hwv5'
        step as ⟨w6, hw6⟩
        have hwv6' : w6.val = (g0 + 6) * 1040 + dstOf kU.val ii.val := by omega
        have hwv6 : w6.val = (g0 + 6) * S + dstOf kU.val ii.val := by rw [hS]; exact hwv6'
        step as ⟨w7, hw7⟩
        have hwv7' : w7.val = (g0 + 7) * 1040 + dstOf kU.val ii.val := by omega
        have hwv7 : w7.val = (g0 + 7) * S + dstOf kU.val ii.val := by rw [hS]; exact hwv7'
        have hp0 : Prog words kU.val false g0 base B ii.val 0 d :=
          (Prog_zero_iff words kU.val false g0 base B ii.val d).mpr ⟨hdb, hdv⟩
        have hlen0 : d.val.length = d.val.length := rfl
        obtain ⟨hidx0, hcur0⟩ := write_facts words kU.val false g0 base B ii.val 0 d hp0 hk hiilt (by decide) (by rw [hlen0]; exact hcapd)
        have hwlt0 : w0.val < d.val.length := by rw [hwv0]; exact hidx0
        step as ⟨c0, hc0⟩
        have hc0v : c0.val = reg d (g0 + 0) (dstOf kU.val ii.val) := by
          unfold reg; rw [hc0, ← bufN_of_lt (v := d) (w := w0.val) hwlt0, hwv0]
        have hbnd0 : c0.val + d0.val ≤ Std.U64.max := by
          rw [hc0v]; have := offStep_le false kU.val ii.val d0.val hd0q; rw [← ha0v] at this; omega
        step as ⟨v0, hv0⟩
        step as ⟨xw0, back0, hxw0, hback0⟩
        rw [hback0]
        have hp1 : Prog words kU.val false g0 base B ii.val 1 (d.set w0 v0) :=
          write_one words kU.val false g0 base B ii.val 0 d w0 d0 v0 d0.val hk hiilt (by decide) hd0q hd0nib hp0 hwv0 hwlt0 ha0v (by omega)
        have hlen1 : (d.set w0 v0).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]
        have hfr1 : Frame buf0 (d.set w0 v0) g0 :=
          Frame_set hdf (by norm_num : (0 : ℕ) < 8) (dstOf_lt hk hiilt) hwv0
        obtain ⟨hidx1, hcur1⟩ := write_facts words kU.val false g0 base B ii.val 1 (d.set w0 v0) hp1 hk hiilt (by decide) (by rw [hlen1]; exact hcapd)
        have hwlt1 : w1.val < (d.set w0 v0).val.length := by rw [hwv1]; exact hidx1
        step as ⟨c1, hc1⟩
        have hc1v : c1.val = reg (d.set w0 v0) (g0 + 1) (dstOf kU.val ii.val) := by
          unfold reg; rw [hc1, ← bufN_of_lt (v := (d.set w0 v0)) (w := w1.val) hwlt1, hwv1]
        have hbnd1 : c1.val + d1.val ≤ Std.U64.max := by
          rw [hc1v]; have := offStep_le false kU.val ii.val d1.val hd1q; rw [← ha1v] at this; omega
        step as ⟨v1, hv1⟩
        step as ⟨xw1, back1, hxw1, hback1⟩
        rw [hback1]
        have hp2 : Prog words kU.val false g0 base B ii.val 2 ((d.set w0 v0).set w1 v1) :=
          write_one words kU.val false g0 base B ii.val 1 (d.set w0 v0) w1 d1 v1 d1.val hk hiilt (by decide) hd1q hd1nib hp1 hwv1 hwlt1 ha1v (by omega)
        have hlen2 : ((d.set w0 v0).set w1 v1).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen1
        have hfr2 : Frame buf0 ((d.set w0 v0).set w1 v1) g0 :=
          Frame_set hfr1 (by norm_num : (1 : ℕ) < 8) (dstOf_lt hk hiilt) hwv1
        obtain ⟨hidx2, hcur2⟩ := write_facts words kU.val false g0 base B ii.val 2 ((d.set w0 v0).set w1 v1) hp2 hk hiilt (by decide) (by rw [hlen2]; exact hcapd)
        have hwlt2 : w2.val < ((d.set w0 v0).set w1 v1).val.length := by rw [hwv2]; exact hidx2
        step as ⟨c2, hc2⟩
        have hc2v : c2.val = reg ((d.set w0 v0).set w1 v1) (g0 + 2) (dstOf kU.val ii.val) := by
          unfold reg; rw [hc2, ← bufN_of_lt (v := ((d.set w0 v0).set w1 v1)) (w := w2.val) hwlt2, hwv2]
        have hbnd2 : c2.val + d2.val ≤ Std.U64.max := by
          rw [hc2v]; have := offStep_le false kU.val ii.val d2.val hd2q; rw [← ha2v] at this; omega
        step as ⟨v2, hv2⟩
        step as ⟨xw2, back2, hxw2, hback2⟩
        rw [hback2]
        have hp3 : Prog words kU.val false g0 base B ii.val 3 (((d.set w0 v0).set w1 v1).set w2 v2) :=
          write_one words kU.val false g0 base B ii.val 2 ((d.set w0 v0).set w1 v1) w2 d2 v2 d2.val hk hiilt (by decide) hd2q hd2nib hp2 hwv2 hwlt2 ha2v (by omega)
        have hlen3 : (((d.set w0 v0).set w1 v1).set w2 v2).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen2
        have hfr3 : Frame buf0 (((d.set w0 v0).set w1 v1).set w2 v2) g0 :=
          Frame_set hfr2 (by norm_num : (2 : ℕ) < 8) (dstOf_lt hk hiilt) hwv2
        obtain ⟨hidx3, hcur3⟩ := write_facts words kU.val false g0 base B ii.val 3 (((d.set w0 v0).set w1 v1).set w2 v2) hp3 hk hiilt (by decide) (by rw [hlen3]; exact hcapd)
        have hwlt3 : w3.val < (((d.set w0 v0).set w1 v1).set w2 v2).val.length := by rw [hwv3]; exact hidx3
        step as ⟨c3, hc3⟩
        have hc3v : c3.val = reg (((d.set w0 v0).set w1 v1).set w2 v2) (g0 + 3) (dstOf kU.val ii.val) := by
          unfold reg; rw [hc3, ← bufN_of_lt (v := (((d.set w0 v0).set w1 v1).set w2 v2)) (w := w3.val) hwlt3, hwv3]
        have hbnd3 : c3.val + d3.val ≤ Std.U64.max := by
          rw [hc3v]; have := offStep_le false kU.val ii.val d3.val hd3q; rw [← ha3v] at this; omega
        step as ⟨v3, hv3⟩
        step as ⟨xw3, back3, hxw3, hback3⟩
        rw [hback3]
        have hp4 : Prog words kU.val false g0 base B ii.val 4 ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) :=
          write_one words kU.val false g0 base B ii.val 3 (((d.set w0 v0).set w1 v1).set w2 v2) w3 d3 v3 d3.val hk hiilt (by decide) hd3q hd3nib hp3 hwv3 hwlt3 ha3v (by omega)
        have hlen4 : ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen3
        have hfr4 : Frame buf0 ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) g0 :=
          Frame_set hfr3 (by norm_num : (3 : ℕ) < 8) (dstOf_lt hk hiilt) hwv3
        obtain ⟨hidx4, hcur4⟩ := write_facts words kU.val false g0 base B ii.val 4 ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) hp4 hk hiilt (by decide) (by rw [hlen4]; exact hcapd)
        have hwlt4 : w4.val < ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).val.length := by rw [hwv4]; exact hidx4
        step as ⟨c4, hc4⟩
        have hc4v : c4.val = reg ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) (g0 + 4) (dstOf kU.val ii.val) := by
          unfold reg; rw [hc4, ← bufN_of_lt (v := ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3)) (w := w4.val) hwlt4, hwv4]
        have hbnd4 : c4.val + d4.val ≤ Std.U64.max := by
          rw [hc4v]; have := offStep_le false kU.val ii.val d4.val hd4q; rw [← ha4v] at this; omega
        step as ⟨v4, hv4⟩
        step as ⟨xw4, back4, hxw4, hback4⟩
        rw [hback4]
        have hp5 : Prog words kU.val false g0 base B ii.val 5 (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) :=
          write_one words kU.val false g0 base B ii.val 4 ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) w4 d4 v4 d4.val hk hiilt (by decide) hd4q hd4nib hp4 hwv4 hwlt4 ha4v (by omega)
        have hlen5 : (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen4
        have hfr5 : Frame buf0 (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) g0 :=
          Frame_set hfr4 (by norm_num : (4 : ℕ) < 8) (dstOf_lt hk hiilt) hwv4
        obtain ⟨hidx5, hcur5⟩ := write_facts words kU.val false g0 base B ii.val 5 (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) hp5 hk hiilt (by decide) (by rw [hlen5]; exact hcapd)
        have hwlt5 : w5.val < (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).val.length := by rw [hwv5]; exact hidx5
        step as ⟨c5, hc5⟩
        have hc5v : c5.val = reg (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) (g0 + 5) (dstOf kU.val ii.val) := by
          unfold reg; rw [hc5, ← bufN_of_lt (v := (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4)) (w := w5.val) hwlt5, hwv5]
        have hbnd5 : c5.val + d5.val ≤ Std.U64.max := by
          rw [hc5v]; have := offStep_le false kU.val ii.val d5.val hd5q; rw [← ha5v] at this; omega
        step as ⟨v5, hv5⟩
        step as ⟨xw5, back5, hxw5, hback5⟩
        rw [hback5]
        have hp6 : Prog words kU.val false g0 base B ii.val 6 ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) :=
          write_one words kU.val false g0 base B ii.val 5 (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) w5 d5 v5 d5.val hk hiilt (by decide) hd5q hd5nib hp5 hwv5 hwlt5 ha5v (by omega)
        have hlen6 : ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen5
        have hfr6 : Frame buf0 ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) g0 :=
          Frame_set hfr5 (by norm_num : (5 : ℕ) < 8) (dstOf_lt hk hiilt) hwv5
        obtain ⟨hidx6, hcur6⟩ := write_facts words kU.val false g0 base B ii.val 6 ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) hp6 hk hiilt (by decide) (by rw [hlen6]; exact hcapd)
        have hwlt6 : w6.val < ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).val.length := by rw [hwv6]; exact hidx6
        step as ⟨c6, hc6⟩
        have hc6v : c6.val = reg ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) (g0 + 6) (dstOf kU.val ii.val) := by
          unfold reg; rw [hc6, ← bufN_of_lt (v := ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5)) (w := w6.val) hwlt6, hwv6]
        have hbnd6 : c6.val + d6.val ≤ Std.U64.max := by
          rw [hc6v]; have := offStep_le false kU.val ii.val d6.val hd6q; rw [← ha6v] at this; omega
        step as ⟨v6, hv6⟩
        step as ⟨xw6, back6, hxw6, hback6⟩
        rw [hback6]
        have hp7 : Prog words kU.val false g0 base B ii.val 7 (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) :=
          write_one words kU.val false g0 base B ii.val 6 ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) w6 d6 v6 d6.val hk hiilt (by decide) hd6q hd6nib hp6 hwv6 hwlt6 ha6v (by omega)
        have hlen7 : (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen6
        have hfr7 : Frame buf0 (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) g0 :=
          Frame_set hfr6 (by norm_num : (6 : ℕ) < 8) (dstOf_lt hk hiilt) hwv6
        obtain ⟨hidx7, hcur7⟩ := write_facts words kU.val false g0 base B ii.val 7 (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) hp7 hk hiilt (by decide) (by rw [hlen7]; exact hcapd)
        have hwlt7 : w7.val < (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).val.length := by rw [hwv7]; exact hidx7
        step as ⟨c7, hc7⟩
        have hc7v : c7.val = reg (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) (g0 + 7) (dstOf kU.val ii.val) := by
          unfold reg; rw [hc7, ← bufN_of_lt (v := (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6)) (w := w7.val) hwlt7, hwv7]
        have hbnd7 : c7.val + d7.val ≤ Std.U64.max := by
          rw [hc7v]; have := offStep_le false kU.val ii.val d7.val hd7q; rw [← ha7v] at this; omega
        step as ⟨v7, hv7⟩
        step as ⟨xw7, back7, hxw7, hback7⟩
        rw [hback7]
        have hp8 : Prog words kU.val false g0 base B ii.val 8 ((((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).set w7 v7) :=
          write_one words kU.val false g0 base B ii.val 7 (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) w7 d7 v7 d7.val hk hiilt (by decide) hd7q hd7nib hp7 hwv7 hwlt7 ha7v (by omega)
        have hlen8 : ((((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).set w7 v7).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen7
        have hfr8 : Frame buf0 ((((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).set w7 v7) g0 :=
          Frame_set hfr7 (by norm_num : (7 : ℕ) < 8) (dstOf_lt hk hiilt) hwv7
        have hmaxb : ii.val + 1 ≤ Std.Usize.max := by have := usize_max_ge; have h3 : N = 1024 := rfl; omega
        step as ⟨ii1, hii1⟩
        obtain ⟨hfb, hfv⟩ := Prog_eight words kU.val false g0 base B ii.val ((((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).set w7 v7) hp8
        refine ⟨by omega, by rw [hlen8]; exact hdl, by rw [hii1]; exact hfb, by rw [hii1]; exact hfv, hfr8, by omega⟩
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ii.val = limU.val := by scalar_tac
      exact ⟨hdl, by rw [← heq]; exact hdb, by rw [← heq]; exact hdv, hdf⟩
  · exact ⟨hi, hlen, hbnd, hval, hfr⟩

set_option maxHeartbeats 2000000 in
/-- **The high run** of `z_pass`: `j ≥ N - k`, every term wraps to `j - lim`
and carries the opposite sign. -/
theorem z_pass_loop1_spec (words : alloc.vec.Vec Std.U64) (negt : Bool)
    (rbU : Std.Usize) (nU : Std.Usize) (qU : Std.U64) (strideU limU : Std.Usize)
    (out : alloc.vec.Vec Std.U64) (jU : Std.Usize)
    (buf0 : alloc.vec.Vec Std.U64) (g0 k : ℕ) (base : ℕ → ℕ → ZMod q) (B : ℕ)
    (hwl : words.val.length = N) (hwlt : ∀ i, i < N → bufN words i < q)
    (hn : nU.val = N) (hq : qU.val = q) (hstride : strideU.val = S)
    (hlim : limU.val = N - k) (hk : k < N) (hrb : rbU.val = g0 * S)
    (hj1 : limU.val ≤ jU.val) (hj2 : jU.val ≤ N) (hlen : out.val.length = buf0.val.length)
    (hcap : (g0 + 8) * S ≤ buf0.val.length) (hB : B + q ≤ Std.U64.max)
    (hbnd : ∀ e, e < 8 → ∀ w, w < N →
      reg out (g0 + e) w ≤ (if srcOf k w < jU.val then B + q else B))
    (hval : ∀ e, e < 8 → ∀ w, w < N → ((reg out (g0 + e) w : ℕ) : ZMod q)
      = applied (base e) (nibW words e) k negt jU.val w)
    (hfr : Frame buf0 out g0) :
    quadeval.z_pass_loop1 words negt rbU nU qU strideU out limU jU
      ⦃ z => z.val.length = buf0.val.length
        ∧ (∀ e, e < 8 → ∀ w, w < N → reg z (g0 + e) w ≤ B + q)
        ∧ (∀ e, e < 8 → ∀ w, w < N → ((reg z (g0 + e) w : ℕ) : ZMod q)
            = applied (base e) (nibW words e) k negt N w)
        ∧ Frame buf0 z g0 ⦄ := by
  have hS : S = 1040 := rfl
  have hq16 : 16 ≤ q := by norm_num [HachiEquiv.Field.q]
  rw [quadeval.z_pass_loop1]
  apply loop.spec_decr_nat (fun t => nU.val - t.2.val)
    (fun t => limU.val ≤ t.2.val ∧ t.2.val ≤ N ∧ t.1.val.length = buf0.val.length
      ∧ (∀ e, e < 8 → ∀ w, w < N →
          reg t.1 (g0 + e) w ≤ (if srcOf k w < t.2.val then B + q else B))
      ∧ (∀ e, e < 8 → ∀ w, w < N → ((reg t.1 (g0 + e) w : ℕ) : ZMod q)
          = applied (base e) (nibW words e) k negt t.2.val w)
      ∧ Frame buf0 t.1 g0)
  · rintro ⟨d, ii⟩ ⟨hjl, hii, hdl, hdb, hdv, hdf⟩
    dsimp only at hjl hii hdl hdb hdv hdf
    simp only [quadeval.z_pass_loop1.body]
    by_cases hlt : ii < nU
    · rw [if_pos hlt]
      have hiilt : ii.val < N := by rw [← hn]; scalar_tac
      have hwrap : N ≤ k + ii.val := by omega
      have hdst : dstOf k ii.val = ii.val - limU.val := by
        unfold dstOf; rw [if_neg (by omega)]; omega
      have hk' : k < N := hk
      have hcapd : (g0 + 8) * S ≤ d.val.length := by rw [hdl]; exact hcap
      have hrb' : rbU.val = g0 * 1040 := by rw [hrb, hS]
      have hstride' : strideU.val = 1040 := by rw [hstride, hS]
      have hwb : ii.val < words.val.length := by rw [hwl]; exact hiilt
      step as ⟨x, hx⟩
      have hxv : x.val = bufN words ii.val := by
        rw [hx, ← bufN_of_lt (v := words) (w := ii.val) hwb]
      have hxlt : x.val < q := by rw [hxv]; exact hwlt ii.val hiilt
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
      have hd0v : d0.val = x.val / 16 ^ 0 % 16 := by rw [hd0]; simp
      have hd1v : d1.val = x.val / 16 ^ 1 % 16 := by rw [hd1, hq1]; norm_num
      have hd2v : d2.val = x.val / 16 ^ 2 % 16 := by rw [hd2, hq2]; norm_num
      have hd3v : d3.val = x.val / 16 ^ 3 % 16 := by rw [hd3, hq3]; norm_num
      have hd4v : d4.val = x.val / 16 ^ 4 % 16 := by rw [hd4, hq4]; norm_num
      have hd5v : d5.val = x.val / 16 ^ 5 % 16 := by rw [hd5, hq5]; norm_num
      have hd6v : d6.val = x.val / 16 ^ 6 % 16 := by rw [hd6, hq6]; norm_num
      have hd7v : d7.val = x.val / 16 ^ 7 % 16 := by rw [hd7, hq7]; norm_num
      have hd0lt : d0.val < 16 := by rw [hd0v]; exact Nat.mod_lt _ (by norm_num)
      have hd0q : d0.val < q := by have := hd0lt; omega
      have hd0nib : ((d0.val : ℕ) : ZMod q) = nibW words 0 ii.val := by
        unfold nibW; rw [hd0v, hxv]
      have hd1lt : d1.val < 16 := by rw [hd1v]; exact Nat.mod_lt _ (by norm_num)
      have hd1q : d1.val < q := by have := hd1lt; omega
      have hd1nib : ((d1.val : ℕ) : ZMod q) = nibW words 1 ii.val := by
        unfold nibW; rw [hd1v, hxv]
      have hd2lt : d2.val < 16 := by rw [hd2v]; exact Nat.mod_lt _ (by norm_num)
      have hd2q : d2.val < q := by have := hd2lt; omega
      have hd2nib : ((d2.val : ℕ) : ZMod q) = nibW words 2 ii.val := by
        unfold nibW; rw [hd2v, hxv]
      have hd3lt : d3.val < 16 := by rw [hd3v]; exact Nat.mod_lt _ (by norm_num)
      have hd3q : d3.val < q := by have := hd3lt; omega
      have hd3nib : ((d3.val : ℕ) : ZMod q) = nibW words 3 ii.val := by
        unfold nibW; rw [hd3v, hxv]
      have hd4lt : d4.val < 16 := by rw [hd4v]; exact Nat.mod_lt _ (by norm_num)
      have hd4q : d4.val < q := by have := hd4lt; omega
      have hd4nib : ((d4.val : ℕ) : ZMod q) = nibW words 4 ii.val := by
        unfold nibW; rw [hd4v, hxv]
      have hd5lt : d5.val < 16 := by rw [hd5v]; exact Nat.mod_lt _ (by norm_num)
      have hd5q : d5.val < q := by have := hd5lt; omega
      have hd5nib : ((d5.val : ℕ) : ZMod q) = nibW words 5 ii.val := by
        unfold nibW; rw [hd5v, hxv]
      have hd6lt : d6.val < 16 := by rw [hd6v]; exact Nat.mod_lt _ (by norm_num)
      have hd6q : d6.val < q := by have := hd6lt; omega
      have hd6nib : ((d6.val : ℕ) : ZMod q) = nibW words 6 ii.val := by
        unfold nibW; rw [hd6v, hxv]
      have hd7lt : d7.val < 16 := by rw [hd7v]; exact Nat.mod_lt _ (by norm_num)
      have hd7q : d7.val < q := by have := hd7lt; omega
      have hd7nib : ((d7.val : ℕ) : ZMod q) = nibW words 7 ii.val := by
        unfold nibW; rw [hd7v, hxv]
      cases negt with
      | true =>
        simp only [↓reduceIte, bind_tc_ok]
        have ha0v : d0.val = offStep true k ii.val d0.val := by
          unfold offStep; simp only [hwrap, ↓reduceIte]
        have ha1v : d1.val = offStep true k ii.val d1.val := by
          unfold offStep; simp only [hwrap, ↓reduceIte]
        have ha2v : d2.val = offStep true k ii.val d2.val := by
          unfold offStep; simp only [hwrap, ↓reduceIte]
        have ha3v : d3.val = offStep true k ii.val d3.val := by
          unfold offStep; simp only [hwrap, ↓reduceIte]
        have ha4v : d4.val = offStep true k ii.val d4.val := by
          unfold offStep; simp only [hwrap, ↓reduceIte]
        have ha5v : d5.val = offStep true k ii.val d5.val := by
          unfold offStep; simp only [hwrap, ↓reduceIte]
        have ha6v : d6.val = offStep true k ii.val d6.val := by
          unfold offStep; simp only [hwrap, ↓reduceIte]
        have ha7v : d7.val = offStep true k ii.val d7.val := by
          unfold offStep; simp only [hwrap, ↓reduceIte]
        step as ⟨i8, hi8⟩
        step as ⟨w0, hw0⟩
        have hwv0' : w0.val = (g0 + 0) * 1040 + dstOf k ii.val := by omega
        have hwv0 : w0.val = (g0 + 0) * S + dstOf k ii.val := by rw [hS]; exact hwv0'
        step as ⟨w1, hw1⟩
        have hwv1' : w1.val = (g0 + 1) * 1040 + dstOf k ii.val := by omega
        have hwv1 : w1.val = (g0 + 1) * S + dstOf k ii.val := by rw [hS]; exact hwv1'
        step as ⟨w2, hw2⟩
        have hwv2' : w2.val = (g0 + 2) * 1040 + dstOf k ii.val := by omega
        have hwv2 : w2.val = (g0 + 2) * S + dstOf k ii.val := by rw [hS]; exact hwv2'
        step as ⟨w3, hw3⟩
        have hwv3' : w3.val = (g0 + 3) * 1040 + dstOf k ii.val := by omega
        have hwv3 : w3.val = (g0 + 3) * S + dstOf k ii.val := by rw [hS]; exact hwv3'
        step as ⟨w4, hw4⟩
        have hwv4' : w4.val = (g0 + 4) * 1040 + dstOf k ii.val := by omega
        have hwv4 : w4.val = (g0 + 4) * S + dstOf k ii.val := by rw [hS]; exact hwv4'
        step as ⟨w5, hw5⟩
        have hwv5' : w5.val = (g0 + 5) * 1040 + dstOf k ii.val := by omega
        have hwv5 : w5.val = (g0 + 5) * S + dstOf k ii.val := by rw [hS]; exact hwv5'
        step as ⟨w6, hw6⟩
        have hwv6' : w6.val = (g0 + 6) * 1040 + dstOf k ii.val := by omega
        have hwv6 : w6.val = (g0 + 6) * S + dstOf k ii.val := by rw [hS]; exact hwv6'
        step as ⟨w7, hw7⟩
        have hwv7' : w7.val = (g0 + 7) * 1040 + dstOf k ii.val := by omega
        have hwv7 : w7.val = (g0 + 7) * S + dstOf k ii.val := by rw [hS]; exact hwv7'
        have hp0 : Prog words k true g0 base B ii.val 0 d :=
          (Prog_zero_iff words k true g0 base B ii.val d).mpr ⟨hdb, hdv⟩
        have hlen0 : d.val.length = d.val.length := rfl
        obtain ⟨hidx0, hcur0⟩ := write_facts words k true g0 base B ii.val 0 d hp0 hk hiilt (by decide) (by rw [hlen0]; exact hcapd)
        have hwlt0 : w0.val < d.val.length := by rw [hwv0]; exact hidx0
        step as ⟨c0, hc0⟩
        have hc0v : c0.val = reg d (g0 + 0) (dstOf k ii.val) := by
          unfold reg; rw [hc0, ← bufN_of_lt (v := d) (w := w0.val) hwlt0, hwv0]
        have hbnd0 : c0.val + d0.val ≤ Std.U64.max := by
          rw [hc0v]; have := offStep_le true k ii.val d0.val hd0q; rw [← ha0v] at this; omega
        step as ⟨v0, hv0⟩
        step as ⟨xw0, back0, hxw0, hback0⟩
        rw [hback0]
        have hp1 : Prog words k true g0 base B ii.val 1 (d.set w0 v0) :=
          write_one words k true g0 base B ii.val 0 d w0 d0 v0 d0.val hk hiilt (by decide) hd0q hd0nib hp0 hwv0 hwlt0 ha0v (by omega)
        have hlen1 : (d.set w0 v0).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]
        have hfr1 : Frame buf0 (d.set w0 v0) g0 :=
          Frame_set hdf (by norm_num : (0 : ℕ) < 8) (dstOf_lt hk hiilt) hwv0
        obtain ⟨hidx1, hcur1⟩ := write_facts words k true g0 base B ii.val 1 (d.set w0 v0) hp1 hk hiilt (by decide) (by rw [hlen1]; exact hcapd)
        have hwlt1 : w1.val < (d.set w0 v0).val.length := by rw [hwv1]; exact hidx1
        step as ⟨c1, hc1⟩
        have hc1v : c1.val = reg (d.set w0 v0) (g0 + 1) (dstOf k ii.val) := by
          unfold reg; rw [hc1, ← bufN_of_lt (v := (d.set w0 v0)) (w := w1.val) hwlt1, hwv1]
        have hbnd1 : c1.val + d1.val ≤ Std.U64.max := by
          rw [hc1v]; have := offStep_le true k ii.val d1.val hd1q; rw [← ha1v] at this; omega
        step as ⟨v1, hv1⟩
        step as ⟨xw1, back1, hxw1, hback1⟩
        rw [hback1]
        have hp2 : Prog words k true g0 base B ii.val 2 ((d.set w0 v0).set w1 v1) :=
          write_one words k true g0 base B ii.val 1 (d.set w0 v0) w1 d1 v1 d1.val hk hiilt (by decide) hd1q hd1nib hp1 hwv1 hwlt1 ha1v (by omega)
        have hlen2 : ((d.set w0 v0).set w1 v1).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen1
        have hfr2 : Frame buf0 ((d.set w0 v0).set w1 v1) g0 :=
          Frame_set hfr1 (by norm_num : (1 : ℕ) < 8) (dstOf_lt hk hiilt) hwv1
        obtain ⟨hidx2, hcur2⟩ := write_facts words k true g0 base B ii.val 2 ((d.set w0 v0).set w1 v1) hp2 hk hiilt (by decide) (by rw [hlen2]; exact hcapd)
        have hwlt2 : w2.val < ((d.set w0 v0).set w1 v1).val.length := by rw [hwv2]; exact hidx2
        step as ⟨c2, hc2⟩
        have hc2v : c2.val = reg ((d.set w0 v0).set w1 v1) (g0 + 2) (dstOf k ii.val) := by
          unfold reg; rw [hc2, ← bufN_of_lt (v := ((d.set w0 v0).set w1 v1)) (w := w2.val) hwlt2, hwv2]
        have hbnd2 : c2.val + d2.val ≤ Std.U64.max := by
          rw [hc2v]; have := offStep_le true k ii.val d2.val hd2q; rw [← ha2v] at this; omega
        step as ⟨v2, hv2⟩
        step as ⟨xw2, back2, hxw2, hback2⟩
        rw [hback2]
        have hp3 : Prog words k true g0 base B ii.val 3 (((d.set w0 v0).set w1 v1).set w2 v2) :=
          write_one words k true g0 base B ii.val 2 ((d.set w0 v0).set w1 v1) w2 d2 v2 d2.val hk hiilt (by decide) hd2q hd2nib hp2 hwv2 hwlt2 ha2v (by omega)
        have hlen3 : (((d.set w0 v0).set w1 v1).set w2 v2).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen2
        have hfr3 : Frame buf0 (((d.set w0 v0).set w1 v1).set w2 v2) g0 :=
          Frame_set hfr2 (by norm_num : (2 : ℕ) < 8) (dstOf_lt hk hiilt) hwv2
        obtain ⟨hidx3, hcur3⟩ := write_facts words k true g0 base B ii.val 3 (((d.set w0 v0).set w1 v1).set w2 v2) hp3 hk hiilt (by decide) (by rw [hlen3]; exact hcapd)
        have hwlt3 : w3.val < (((d.set w0 v0).set w1 v1).set w2 v2).val.length := by rw [hwv3]; exact hidx3
        step as ⟨c3, hc3⟩
        have hc3v : c3.val = reg (((d.set w0 v0).set w1 v1).set w2 v2) (g0 + 3) (dstOf k ii.val) := by
          unfold reg; rw [hc3, ← bufN_of_lt (v := (((d.set w0 v0).set w1 v1).set w2 v2)) (w := w3.val) hwlt3, hwv3]
        have hbnd3 : c3.val + d3.val ≤ Std.U64.max := by
          rw [hc3v]; have := offStep_le true k ii.val d3.val hd3q; rw [← ha3v] at this; omega
        step as ⟨v3, hv3⟩
        step as ⟨xw3, back3, hxw3, hback3⟩
        rw [hback3]
        have hp4 : Prog words k true g0 base B ii.val 4 ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) :=
          write_one words k true g0 base B ii.val 3 (((d.set w0 v0).set w1 v1).set w2 v2) w3 d3 v3 d3.val hk hiilt (by decide) hd3q hd3nib hp3 hwv3 hwlt3 ha3v (by omega)
        have hlen4 : ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen3
        have hfr4 : Frame buf0 ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) g0 :=
          Frame_set hfr3 (by norm_num : (3 : ℕ) < 8) (dstOf_lt hk hiilt) hwv3
        obtain ⟨hidx4, hcur4⟩ := write_facts words k true g0 base B ii.val 4 ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) hp4 hk hiilt (by decide) (by rw [hlen4]; exact hcapd)
        have hwlt4 : w4.val < ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).val.length := by rw [hwv4]; exact hidx4
        step as ⟨c4, hc4⟩
        have hc4v : c4.val = reg ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) (g0 + 4) (dstOf k ii.val) := by
          unfold reg; rw [hc4, ← bufN_of_lt (v := ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3)) (w := w4.val) hwlt4, hwv4]
        have hbnd4 : c4.val + d4.val ≤ Std.U64.max := by
          rw [hc4v]; have := offStep_le true k ii.val d4.val hd4q; rw [← ha4v] at this; omega
        step as ⟨v4, hv4⟩
        step as ⟨xw4, back4, hxw4, hback4⟩
        rw [hback4]
        have hp5 : Prog words k true g0 base B ii.val 5 (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) :=
          write_one words k true g0 base B ii.val 4 ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) w4 d4 v4 d4.val hk hiilt (by decide) hd4q hd4nib hp4 hwv4 hwlt4 ha4v (by omega)
        have hlen5 : (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen4
        have hfr5 : Frame buf0 (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) g0 :=
          Frame_set hfr4 (by norm_num : (4 : ℕ) < 8) (dstOf_lt hk hiilt) hwv4
        obtain ⟨hidx5, hcur5⟩ := write_facts words k true g0 base B ii.val 5 (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) hp5 hk hiilt (by decide) (by rw [hlen5]; exact hcapd)
        have hwlt5 : w5.val < (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).val.length := by rw [hwv5]; exact hidx5
        step as ⟨c5, hc5⟩
        have hc5v : c5.val = reg (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) (g0 + 5) (dstOf k ii.val) := by
          unfold reg; rw [hc5, ← bufN_of_lt (v := (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4)) (w := w5.val) hwlt5, hwv5]
        have hbnd5 : c5.val + d5.val ≤ Std.U64.max := by
          rw [hc5v]; have := offStep_le true k ii.val d5.val hd5q; rw [← ha5v] at this; omega
        step as ⟨v5, hv5⟩
        step as ⟨xw5, back5, hxw5, hback5⟩
        rw [hback5]
        have hp6 : Prog words k true g0 base B ii.val 6 ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) :=
          write_one words k true g0 base B ii.val 5 (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) w5 d5 v5 d5.val hk hiilt (by decide) hd5q hd5nib hp5 hwv5 hwlt5 ha5v (by omega)
        have hlen6 : ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen5
        have hfr6 : Frame buf0 ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) g0 :=
          Frame_set hfr5 (by norm_num : (5 : ℕ) < 8) (dstOf_lt hk hiilt) hwv5
        obtain ⟨hidx6, hcur6⟩ := write_facts words k true g0 base B ii.val 6 ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) hp6 hk hiilt (by decide) (by rw [hlen6]; exact hcapd)
        have hwlt6 : w6.val < ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).val.length := by rw [hwv6]; exact hidx6
        step as ⟨c6, hc6⟩
        have hc6v : c6.val = reg ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) (g0 + 6) (dstOf k ii.val) := by
          unfold reg; rw [hc6, ← bufN_of_lt (v := ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5)) (w := w6.val) hwlt6, hwv6]
        have hbnd6 : c6.val + d6.val ≤ Std.U64.max := by
          rw [hc6v]; have := offStep_le true k ii.val d6.val hd6q; rw [← ha6v] at this; omega
        step as ⟨v6, hv6⟩
        step as ⟨xw6, back6, hxw6, hback6⟩
        rw [hback6]
        have hp7 : Prog words k true g0 base B ii.val 7 (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) :=
          write_one words k true g0 base B ii.val 6 ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) w6 d6 v6 d6.val hk hiilt (by decide) hd6q hd6nib hp6 hwv6 hwlt6 ha6v (by omega)
        have hlen7 : (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen6
        have hfr7 : Frame buf0 (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) g0 :=
          Frame_set hfr6 (by norm_num : (6 : ℕ) < 8) (dstOf_lt hk hiilt) hwv6
        obtain ⟨hidx7, hcur7⟩ := write_facts words k true g0 base B ii.val 7 (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) hp7 hk hiilt (by decide) (by rw [hlen7]; exact hcapd)
        have hwlt7 : w7.val < (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).val.length := by rw [hwv7]; exact hidx7
        step as ⟨c7, hc7⟩
        have hc7v : c7.val = reg (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) (g0 + 7) (dstOf k ii.val) := by
          unfold reg; rw [hc7, ← bufN_of_lt (v := (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6)) (w := w7.val) hwlt7, hwv7]
        have hbnd7 : c7.val + d7.val ≤ Std.U64.max := by
          rw [hc7v]; have := offStep_le true k ii.val d7.val hd7q; rw [← ha7v] at this; omega
        step as ⟨v7, hv7⟩
        step as ⟨xw7, back7, hxw7, hback7⟩
        rw [hback7]
        have hp8 : Prog words k true g0 base B ii.val 8 ((((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).set w7 v7) :=
          write_one words k true g0 base B ii.val 7 (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) w7 d7 v7 d7.val hk hiilt (by decide) hd7q hd7nib hp7 hwv7 hwlt7 ha7v (by omega)
        have hlen8 : ((((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).set w7 v7).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen7
        have hfr8 : Frame buf0 ((((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).set w7 v7) g0 :=
          Frame_set hfr7 (by norm_num : (7 : ℕ) < 8) (dstOf_lt hk hiilt) hwv7
        have hmaxb : ii.val + 1 ≤ Std.Usize.max := by have := usize_max_ge; have h3 : N = 1024 := rfl; omega
        step as ⟨ii1, hii1⟩
        obtain ⟨hfb, hfv⟩ := Prog_eight words k true g0 base B ii.val ((((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).set w7 v7) hp8
        refine ⟨by omega, by omega, by rw [hlen8]; exact hdl, by rw [hii1]; exact hfb, by rw [hii1]; exact hfv, hfr8, by omega⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        step as ⟨a0, ha0⟩
        have ha0v : a0.val = offStep false k ii.val d0.val := by
          unfold offStep; simp only [hwrap, ↓reduceIte, Bool.false_eq_true, ha0, hq]
        step as ⟨a1, ha1⟩
        have ha1v : a1.val = offStep false k ii.val d1.val := by
          unfold offStep; simp only [hwrap, ↓reduceIte, Bool.false_eq_true, ha1, hq]
        step as ⟨a2, ha2⟩
        have ha2v : a2.val = offStep false k ii.val d2.val := by
          unfold offStep; simp only [hwrap, ↓reduceIte, Bool.false_eq_true, ha2, hq]
        step as ⟨a3, ha3⟩
        have ha3v : a3.val = offStep false k ii.val d3.val := by
          unfold offStep; simp only [hwrap, ↓reduceIte, Bool.false_eq_true, ha3, hq]
        step as ⟨a4, ha4⟩
        have ha4v : a4.val = offStep false k ii.val d4.val := by
          unfold offStep; simp only [hwrap, ↓reduceIte, Bool.false_eq_true, ha4, hq]
        step as ⟨a5, ha5⟩
        have ha5v : a5.val = offStep false k ii.val d5.val := by
          unfold offStep; simp only [hwrap, ↓reduceIte, Bool.false_eq_true, ha5, hq]
        step as ⟨a6, ha6⟩
        have ha6v : a6.val = offStep false k ii.val d6.val := by
          unfold offStep; simp only [hwrap, ↓reduceIte, Bool.false_eq_true, ha6, hq]
        step as ⟨a7, ha7⟩
        have ha7v : a7.val = offStep false k ii.val d7.val := by
          unfold offStep; simp only [hwrap, ↓reduceIte, Bool.false_eq_true, ha7, hq]
        step as ⟨i8, hi8⟩
        step as ⟨w0, hw0⟩
        have hwv0' : w0.val = (g0 + 0) * 1040 + dstOf k ii.val := by omega
        have hwv0 : w0.val = (g0 + 0) * S + dstOf k ii.val := by rw [hS]; exact hwv0'
        step as ⟨w1, hw1⟩
        have hwv1' : w1.val = (g0 + 1) * 1040 + dstOf k ii.val := by omega
        have hwv1 : w1.val = (g0 + 1) * S + dstOf k ii.val := by rw [hS]; exact hwv1'
        step as ⟨w2, hw2⟩
        have hwv2' : w2.val = (g0 + 2) * 1040 + dstOf k ii.val := by omega
        have hwv2 : w2.val = (g0 + 2) * S + dstOf k ii.val := by rw [hS]; exact hwv2'
        step as ⟨w3, hw3⟩
        have hwv3' : w3.val = (g0 + 3) * 1040 + dstOf k ii.val := by omega
        have hwv3 : w3.val = (g0 + 3) * S + dstOf k ii.val := by rw [hS]; exact hwv3'
        step as ⟨w4, hw4⟩
        have hwv4' : w4.val = (g0 + 4) * 1040 + dstOf k ii.val := by omega
        have hwv4 : w4.val = (g0 + 4) * S + dstOf k ii.val := by rw [hS]; exact hwv4'
        step as ⟨w5, hw5⟩
        have hwv5' : w5.val = (g0 + 5) * 1040 + dstOf k ii.val := by omega
        have hwv5 : w5.val = (g0 + 5) * S + dstOf k ii.val := by rw [hS]; exact hwv5'
        step as ⟨w6, hw6⟩
        have hwv6' : w6.val = (g0 + 6) * 1040 + dstOf k ii.val := by omega
        have hwv6 : w6.val = (g0 + 6) * S + dstOf k ii.val := by rw [hS]; exact hwv6'
        step as ⟨w7, hw7⟩
        have hwv7' : w7.val = (g0 + 7) * 1040 + dstOf k ii.val := by omega
        have hwv7 : w7.val = (g0 + 7) * S + dstOf k ii.val := by rw [hS]; exact hwv7'
        have hp0 : Prog words k false g0 base B ii.val 0 d :=
          (Prog_zero_iff words k false g0 base B ii.val d).mpr ⟨hdb, hdv⟩
        have hlen0 : d.val.length = d.val.length := rfl
        obtain ⟨hidx0, hcur0⟩ := write_facts words k false g0 base B ii.val 0 d hp0 hk hiilt (by decide) (by rw [hlen0]; exact hcapd)
        have hwlt0 : w0.val < d.val.length := by rw [hwv0]; exact hidx0
        step as ⟨c0, hc0⟩
        have hc0v : c0.val = reg d (g0 + 0) (dstOf k ii.val) := by
          unfold reg; rw [hc0, ← bufN_of_lt (v := d) (w := w0.val) hwlt0, hwv0]
        have hbnd0 : c0.val + a0.val ≤ Std.U64.max := by
          rw [hc0v]; have := offStep_le false k ii.val d0.val hd0q; rw [← ha0v] at this; omega
        step as ⟨v0, hv0⟩
        step as ⟨xw0, back0, hxw0, hback0⟩
        rw [hback0]
        have hp1 : Prog words k false g0 base B ii.val 1 (d.set w0 v0) :=
          write_one words k false g0 base B ii.val 0 d w0 a0 v0 d0.val hk hiilt (by decide) hd0q hd0nib hp0 hwv0 hwlt0 ha0v (by omega)
        have hlen1 : (d.set w0 v0).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]
        have hfr1 : Frame buf0 (d.set w0 v0) g0 :=
          Frame_set hdf (by norm_num : (0 : ℕ) < 8) (dstOf_lt hk hiilt) hwv0
        obtain ⟨hidx1, hcur1⟩ := write_facts words k false g0 base B ii.val 1 (d.set w0 v0) hp1 hk hiilt (by decide) (by rw [hlen1]; exact hcapd)
        have hwlt1 : w1.val < (d.set w0 v0).val.length := by rw [hwv1]; exact hidx1
        step as ⟨c1, hc1⟩
        have hc1v : c1.val = reg (d.set w0 v0) (g0 + 1) (dstOf k ii.val) := by
          unfold reg; rw [hc1, ← bufN_of_lt (v := (d.set w0 v0)) (w := w1.val) hwlt1, hwv1]
        have hbnd1 : c1.val + a1.val ≤ Std.U64.max := by
          rw [hc1v]; have := offStep_le false k ii.val d1.val hd1q; rw [← ha1v] at this; omega
        step as ⟨v1, hv1⟩
        step as ⟨xw1, back1, hxw1, hback1⟩
        rw [hback1]
        have hp2 : Prog words k false g0 base B ii.val 2 ((d.set w0 v0).set w1 v1) :=
          write_one words k false g0 base B ii.val 1 (d.set w0 v0) w1 a1 v1 d1.val hk hiilt (by decide) hd1q hd1nib hp1 hwv1 hwlt1 ha1v (by omega)
        have hlen2 : ((d.set w0 v0).set w1 v1).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen1
        have hfr2 : Frame buf0 ((d.set w0 v0).set w1 v1) g0 :=
          Frame_set hfr1 (by norm_num : (1 : ℕ) < 8) (dstOf_lt hk hiilt) hwv1
        obtain ⟨hidx2, hcur2⟩ := write_facts words k false g0 base B ii.val 2 ((d.set w0 v0).set w1 v1) hp2 hk hiilt (by decide) (by rw [hlen2]; exact hcapd)
        have hwlt2 : w2.val < ((d.set w0 v0).set w1 v1).val.length := by rw [hwv2]; exact hidx2
        step as ⟨c2, hc2⟩
        have hc2v : c2.val = reg ((d.set w0 v0).set w1 v1) (g0 + 2) (dstOf k ii.val) := by
          unfold reg; rw [hc2, ← bufN_of_lt (v := ((d.set w0 v0).set w1 v1)) (w := w2.val) hwlt2, hwv2]
        have hbnd2 : c2.val + a2.val ≤ Std.U64.max := by
          rw [hc2v]; have := offStep_le false k ii.val d2.val hd2q; rw [← ha2v] at this; omega
        step as ⟨v2, hv2⟩
        step as ⟨xw2, back2, hxw2, hback2⟩
        rw [hback2]
        have hp3 : Prog words k false g0 base B ii.val 3 (((d.set w0 v0).set w1 v1).set w2 v2) :=
          write_one words k false g0 base B ii.val 2 ((d.set w0 v0).set w1 v1) w2 a2 v2 d2.val hk hiilt (by decide) hd2q hd2nib hp2 hwv2 hwlt2 ha2v (by omega)
        have hlen3 : (((d.set w0 v0).set w1 v1).set w2 v2).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen2
        have hfr3 : Frame buf0 (((d.set w0 v0).set w1 v1).set w2 v2) g0 :=
          Frame_set hfr2 (by norm_num : (2 : ℕ) < 8) (dstOf_lt hk hiilt) hwv2
        obtain ⟨hidx3, hcur3⟩ := write_facts words k false g0 base B ii.val 3 (((d.set w0 v0).set w1 v1).set w2 v2) hp3 hk hiilt (by decide) (by rw [hlen3]; exact hcapd)
        have hwlt3 : w3.val < (((d.set w0 v0).set w1 v1).set w2 v2).val.length := by rw [hwv3]; exact hidx3
        step as ⟨c3, hc3⟩
        have hc3v : c3.val = reg (((d.set w0 v0).set w1 v1).set w2 v2) (g0 + 3) (dstOf k ii.val) := by
          unfold reg; rw [hc3, ← bufN_of_lt (v := (((d.set w0 v0).set w1 v1).set w2 v2)) (w := w3.val) hwlt3, hwv3]
        have hbnd3 : c3.val + a3.val ≤ Std.U64.max := by
          rw [hc3v]; have := offStep_le false k ii.val d3.val hd3q; rw [← ha3v] at this; omega
        step as ⟨v3, hv3⟩
        step as ⟨xw3, back3, hxw3, hback3⟩
        rw [hback3]
        have hp4 : Prog words k false g0 base B ii.val 4 ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) :=
          write_one words k false g0 base B ii.val 3 (((d.set w0 v0).set w1 v1).set w2 v2) w3 a3 v3 d3.val hk hiilt (by decide) hd3q hd3nib hp3 hwv3 hwlt3 ha3v (by omega)
        have hlen4 : ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen3
        have hfr4 : Frame buf0 ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) g0 :=
          Frame_set hfr3 (by norm_num : (3 : ℕ) < 8) (dstOf_lt hk hiilt) hwv3
        obtain ⟨hidx4, hcur4⟩ := write_facts words k false g0 base B ii.val 4 ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) hp4 hk hiilt (by decide) (by rw [hlen4]; exact hcapd)
        have hwlt4 : w4.val < ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).val.length := by rw [hwv4]; exact hidx4
        step as ⟨c4, hc4⟩
        have hc4v : c4.val = reg ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) (g0 + 4) (dstOf k ii.val) := by
          unfold reg; rw [hc4, ← bufN_of_lt (v := ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3)) (w := w4.val) hwlt4, hwv4]
        have hbnd4 : c4.val + a4.val ≤ Std.U64.max := by
          rw [hc4v]; have := offStep_le false k ii.val d4.val hd4q; rw [← ha4v] at this; omega
        step as ⟨v4, hv4⟩
        step as ⟨xw4, back4, hxw4, hback4⟩
        rw [hback4]
        have hp5 : Prog words k false g0 base B ii.val 5 (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) :=
          write_one words k false g0 base B ii.val 4 ((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3) w4 a4 v4 d4.val hk hiilt (by decide) hd4q hd4nib hp4 hwv4 hwlt4 ha4v (by omega)
        have hlen5 : (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen4
        have hfr5 : Frame buf0 (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) g0 :=
          Frame_set hfr4 (by norm_num : (4 : ℕ) < 8) (dstOf_lt hk hiilt) hwv4
        obtain ⟨hidx5, hcur5⟩ := write_facts words k false g0 base B ii.val 5 (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) hp5 hk hiilt (by decide) (by rw [hlen5]; exact hcapd)
        have hwlt5 : w5.val < (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).val.length := by rw [hwv5]; exact hidx5
        step as ⟨c5, hc5⟩
        have hc5v : c5.val = reg (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) (g0 + 5) (dstOf k ii.val) := by
          unfold reg; rw [hc5, ← bufN_of_lt (v := (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4)) (w := w5.val) hwlt5, hwv5]
        have hbnd5 : c5.val + a5.val ≤ Std.U64.max := by
          rw [hc5v]; have := offStep_le false k ii.val d5.val hd5q; rw [← ha5v] at this; omega
        step as ⟨v5, hv5⟩
        step as ⟨xw5, back5, hxw5, hback5⟩
        rw [hback5]
        have hp6 : Prog words k false g0 base B ii.val 6 ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) :=
          write_one words k false g0 base B ii.val 5 (((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4) w5 a5 v5 d5.val hk hiilt (by decide) hd5q hd5nib hp5 hwv5 hwlt5 ha5v (by omega)
        have hlen6 : ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen5
        have hfr6 : Frame buf0 ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) g0 :=
          Frame_set hfr5 (by norm_num : (5 : ℕ) < 8) (dstOf_lt hk hiilt) hwv5
        obtain ⟨hidx6, hcur6⟩ := write_facts words k false g0 base B ii.val 6 ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) hp6 hk hiilt (by decide) (by rw [hlen6]; exact hcapd)
        have hwlt6 : w6.val < ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).val.length := by rw [hwv6]; exact hidx6
        step as ⟨c6, hc6⟩
        have hc6v : c6.val = reg ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) (g0 + 6) (dstOf k ii.val) := by
          unfold reg; rw [hc6, ← bufN_of_lt (v := ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5)) (w := w6.val) hwlt6, hwv6]
        have hbnd6 : c6.val + a6.val ≤ Std.U64.max := by
          rw [hc6v]; have := offStep_le false k ii.val d6.val hd6q; rw [← ha6v] at this; omega
        step as ⟨v6, hv6⟩
        step as ⟨xw6, back6, hxw6, hback6⟩
        rw [hback6]
        have hp7 : Prog words k false g0 base B ii.val 7 (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) :=
          write_one words k false g0 base B ii.val 6 ((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5) w6 a6 v6 d6.val hk hiilt (by decide) hd6q hd6nib hp6 hwv6 hwlt6 ha6v (by omega)
        have hlen7 : (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen6
        have hfr7 : Frame buf0 (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) g0 :=
          Frame_set hfr6 (by norm_num : (6 : ℕ) < 8) (dstOf_lt hk hiilt) hwv6
        obtain ⟨hidx7, hcur7⟩ := write_facts words k false g0 base B ii.val 7 (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) hp7 hk hiilt (by decide) (by rw [hlen7]; exact hcapd)
        have hwlt7 : w7.val < (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).val.length := by rw [hwv7]; exact hidx7
        step as ⟨c7, hc7⟩
        have hc7v : c7.val = reg (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) (g0 + 7) (dstOf k ii.val) := by
          unfold reg; rw [hc7, ← bufN_of_lt (v := (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6)) (w := w7.val) hwlt7, hwv7]
        have hbnd7 : c7.val + a7.val ≤ Std.U64.max := by
          rw [hc7v]; have := offStep_le false k ii.val d7.val hd7q; rw [← ha7v] at this; omega
        step as ⟨v7, hv7⟩
        step as ⟨xw7, back7, hxw7, hback7⟩
        rw [hback7]
        have hp8 : Prog words k false g0 base B ii.val 8 ((((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).set w7 v7) :=
          write_one words k false g0 base B ii.val 7 (((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6) w7 a7 v7 d7.val hk hiilt (by decide) hd7q hd7nib hp7 hwv7 hwlt7 ha7v (by omega)
        have hlen8 : ((((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).set w7 v7).val.length = d.val.length := by
          rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hlen7
        have hfr8 : Frame buf0 ((((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).set w7 v7) g0 :=
          Frame_set hfr7 (by norm_num : (7 : ℕ) < 8) (dstOf_lt hk hiilt) hwv7
        have hmaxb : ii.val + 1 ≤ Std.Usize.max := by have := usize_max_ge; have h3 : N = 1024 := rfl; omega
        step as ⟨ii1, hii1⟩
        obtain ⟨hfb, hfv⟩ := Prog_eight words k false g0 base B ii.val ((((((((d.set w0 v0).set w1 v1).set w2 v2).set w3 v3).set w4 v4).set w5 v5).set w6 v6).set w7 v7) hp8
        refine ⟨by omega, by omega, by rw [hlen8]; exact hdl, by rw [hii1]; exact hfb, by rw [hii1]; exact hfv, hfr8, by omega⟩
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ii.val = N := by rw [← hn]; scalar_tac
      refine ⟨hdl, ?_, by intro e he w hw; rw [← heq]; exact hdv e he w hw, hdf⟩
      intro e he w hw
      have := hdb e he w hw
      split at this <;> omega
  · exact ⟨hj1, hj2, hlen, hbnd, hval, hfr⟩

/-- **`z_pass`.** Eight `short_pass_off_spec`s at once: each region of the row
gains one shifted, signed copy of its digit polynomial; every other word of the
buffer is untouched. -/
theorem z_pass_spec (words : alloc.vec.Vec Std.U64) (kU : Std.Usize) (negt : Bool)
    (buf : alloc.vec.Vec Std.U64) (rbU : Std.Usize) (g0 : ℕ)
    (base : ℕ → ℕ → ZMod q) (B : ℕ)
    (hwl : words.val.length = N) (hwlt : ∀ i, i < N → bufN words i < q)
    (hk : kU.val < N) (hrb : rbU.val = g0 * S) (hcap : (g0 + 8) * S ≤ buf.val.length)
    (hB : B + q ≤ Std.U64.max)
    (hbnd : ∀ e, e < 8 → ∀ w, w < N → reg buf (g0 + e) w ≤ B)
    (hval : ∀ e, e < 8 → ∀ w, w < N → ((reg buf (g0 + e) w : ℕ) : ZMod q) = base e w) :
    quadeval.z_pass words kU negt buf rbU
      ⦃ z => z.val.length = buf.val.length
        ∧ (∀ e, e < 8 → ∀ w, w < N → reg z (g0 + e) w ≤ B + q)
        ∧ (∀ e, e < 8 → ∀ w, w < N → ((reg z (g0 + e) w : ℕ) : ZMod q)
            = applied (base e) (nibW words e) kU.val negt N w)
        ∧ Frame buf z g0 ⦄ := by
  rw [quadeval.z_pass]
  have hadd : (params.RING_DEGREE).val + (quadeval.Z_PAD).val ≤ Std.Usize.max := by
    rw [params_RING_DEGREE_val, z_pad_val]; have := usize_max_ge; have h3 : N = 1024 := rfl; omega
  step as ⟨strideU, hstrideU⟩
  have hstride : strideU.val = S := by
    rw [hstrideU, params_RING_DEGREE_val, z_pad_val]
  step as ⟨limU, hlimU⟩
  have hlim : limU.val = N - kU.val := by rw [hlimU, params_RING_DEGREE_val]
  step with z_pass_loop0_spec words kU negt rbU params.Q strideU limU buf 0#usize buf g0
    base B hwl hwlt params_Q_val hstride hlim hk hrb (by simp) rfl hcap hB
    (by intro e he w hw; rw [if_neg (by simp)]; exact hbnd e he w hw)
    (by
      intro e he w hw
      have hz : applied (base e) (nibW words e) kU.val negt ((0#usize : Std.Usize).val) w
          = base e w := by unfold applied; simp
      rw [hz]; exact hval e he w hw)
    (Frame_refl buf g0)
    as ⟨out1, ho1, ho2, ho3, ho4⟩
  exact z_pass_loop1_spec words negt rbU params.RING_DEGREE params.Q strideU limU out1 limU
    buf g0 kU.val base B hwl hwlt params_RING_DEGREE_val params_Q_val hstride hlim hk hrb
    (le_refl _) (by omega) ho1 hcap hB ho2 ho3 ho4

/-! ## 6. `z_reduce`: every word mod `q` -/

theorem z_reduce_loop_spec (qU : Std.U64) (out : alloc.vec.Vec Std.U64) (lenU iU : Std.Usize)
    (buf0 : alloc.vec.Vec Std.U64)
    (hq : qU.val = q) (hlen : lenU.val = buf0.val.length) (hi : iU.val ≤ lenU.val)
    (hol : out.val.length = buf0.val.length)
    (hdone : ∀ t, t < iU.val → bufN out t < q)
    (hval : ∀ t, ((bufN out t : ℕ) : ZMod q) = ((bufN buf0 t : ℕ) : ZMod q))
    (hrest : ∀ t, iU.val ≤ t → bufN out t = bufN buf0 t) :
    quadeval.z_reduce_loop qU out lenU iU
      ⦃ z => z.val.length = buf0.val.length ∧ (∀ t, t < buf0.val.length → bufN z t < q)
        ∧ ∀ t, ((bufN z t : ℕ) : ZMod q) = ((bufN buf0 t : ℕ) : ZMod q) ⦄ := by
  rw [quadeval.z_reduce_loop]
  apply loop.spec_decr_nat (fun t => lenU.val - t.2.val)
    (fun t => t.2.val ≤ lenU.val ∧ t.1.val.length = buf0.val.length
      ∧ (∀ u, u < t.2.val → bufN t.1 u < q)
      ∧ (∀ u, ((bufN t.1 u : ℕ) : ZMod q) = ((bufN buf0 u : ℕ) : ZMod q))
      ∧ ∀ u, t.2.val ≤ u → bufN t.1 u = bufN buf0 u)
  · rintro ⟨o, ii⟩ ⟨hii, hol, hod, hov, hor⟩
    dsimp only at hii hol hod hov hor
    simp only [quadeval.z_reduce_loop.body]
    by_cases hlt : ii < lenU
    · rw [if_pos hlt]
      have hiilt : ii.val < lenU.val := by scalar_tac
      have hib : ii.val < o.val.length := by rw [hol, ← hlen]; exact hiilt
      step as ⟨cur, hcur⟩
      have hqne : qU.val ≠ 0 := by rw [hq]; norm_num [HachiEquiv.Field.q]
      step as ⟨nv, hnv⟩
      step as ⟨xw, back, hxw, hback⟩
      step as ⟨i1, hi1⟩
      rw [hback]
      have hcurv : cur.val = bufN o ii.val := by
        rw [hcur, ← bufN_of_lt (v := o) (w := ii.val) hib]
      have hqpos : 0 < q := by norm_num [HachiEquiv.Field.q]
      refine ⟨by omega, ?_, ?_, ?_, ?_, by omega⟩
      · rw [alloc.vec.Vec.set_val_eq, List.length_set]; exact hol
      · intro u hu
        rw [hi1] at hu
        by_cases hue : u = ii.val
        · subst hue; rw [bufN_set_eq hib, hnv, hq, hcurv]; exact Nat.mod_lt _ hqpos
        · rw [bufN_set_ne hue]; exact hod u (by omega)
      · intro u
        by_cases hue : u = ii.val
        · subst hue
          rw [bufN_set_eq hib, hnv, hq, hcurv, ZMod.natCast_mod]
          exact hov ii.val
        · rw [bufN_set_ne hue]; exact hov u
      · intro u hu
        rw [hi1] at hu
        rw [bufN_set_ne (by omega)]
        exact hor u (by omega)
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ii.val = lenU.val := by scalar_tac
      exact ⟨hol, fun u hu => hod u (by rw [heq, hlen]; exact hu), hov⟩
  · exact ⟨hi, hol, hdone, hval, hrest⟩

/-- **`z_reduce`.** Length kept, every word canonical, every word unchanged in
`ZMod q` -- so every region is unchanged as a ring element. -/
theorem z_reduce_spec (buf : alloc.vec.Vec Std.U64) :
    quadeval.z_reduce buf
      ⦃ z => z.val.length = buf.val.length ∧ (∀ t, t < buf.val.length → bufN z t < q)
        ∧ ∀ t, ((bufN z t : ℕ) : ZMod q) = ((bufN buf t : ℕ) : ZMod q) ⦄ := by
  rw [quadeval.z_reduce]
  exact z_reduce_loop_spec params.Q buf (alloc.vec.Vec.len buf) 0#usize buf params_Q_val
    (by simp) (by simp) rfl (by intro t ht; simp at ht) (fun _ => rfl) (fun _ _ => rfl)

/-! ## 7. `z_apply_terms`: the terms and passes of one row

No chunk counter here (compare `mul_short_add_into_loop1_loop0`): `z_terms`
admits at most `OMEGA = 16` passes per block, and the block loop's `Z_CHUNK`
schedule reserves `16 · q` of headroom for them before the row is touched. The
bound therefore just grows by `q` per pass. -/

/-- The first `t` magnitudes, summed: the pass count. -/
def magSum (vm : alloc.vec.Vec Std.U64) (t : ℕ) : ℕ := ∑ u ∈ Finset.range t, magAt vm u

theorem magSum_succ (vm : alloc.vec.Vec Std.U64) (t : ℕ) :
    magSum vm (t + 1) = magSum vm t + magAt vm t := by
  unfold magSum; rw [Finset.sum_range_succ]

/-- The pass loop: `m` passes of the term `(k, negt)`. -/
theorem z_apply_terms_loop0_loop0_spec (words : alloc.vec.Vec Std.U64) (rbU : Std.Usize)
    (out : alloc.vec.Vec Std.U64) (kU : Std.Usize) (mU : Std.U64) (negt : Bool)
    (passU : Std.U64) (buf0 : alloc.vec.Vec Std.U64) (g0 : ℕ)
    (base : ℕ → ℕ → ZMod q) (B : ℕ)
    (hwl : words.val.length = N) (hwlt : ∀ i, i < N → bufN words i < q)
    (hk : kU.val < N) (hrb : rbU.val = g0 * S) (hcap : (g0 + 8) * S ≤ buf0.val.length)
    (hlen : out.val.length = buf0.val.length)
    (hp : passU.val ≤ mU.val) (hB : B + mU.val * q ≤ Std.U64.max)
    (hbnd : ∀ e, e < 8 → ∀ w, w < N → reg out (g0 + e) w ≤ B + passU.val * q)
    (hval : ∀ e, e < 8 → ∀ w, w < N → ((reg out (g0 + e) w : ℕ) : ZMod q)
      = passed (base e) (nibW words e) kU.val negt passU.val w)
    (hfr : Frame buf0 out g0) :
    quadeval.z_apply_terms_loop0_loop0 words rbU out kU mU negt passU
      ⦃ z => z.val.length = buf0.val.length
        ∧ (∀ e, e < 8 → ∀ w, w < N → reg z (g0 + e) w ≤ B + mU.val * q)
        ∧ (∀ e, e < 8 → ∀ w, w < N → ((reg z (g0 + e) w : ℕ) : ZMod q)
            = passed (base e) (nibW words e) kU.val negt mU.val w)
        ∧ Frame buf0 z g0 ⦄ := by
  rw [quadeval.z_apply_terms_loop0_loop0]
  apply loop.spec_decr_nat (fun t => mU.val - t.2.val)
    (fun t => t.2.val ≤ mU.val ∧ t.1.val.length = buf0.val.length
      ∧ (∀ e, e < 8 → ∀ w, w < N → reg t.1 (g0 + e) w ≤ B + t.2.val * q)
      ∧ (∀ e, e < 8 → ∀ w, w < N → ((reg t.1 (g0 + e) w : ℕ) : ZMod q)
          = passed (base e) (nibW words e) kU.val negt t.2.val w)
      ∧ Frame buf0 t.1 g0)
  · rintro ⟨d, pp⟩ ⟨hpp, hdl, hdb, hdv, hdf⟩
    dsimp only at hpp hdl hdb hdv hdf
    simp only [quadeval.z_apply_terms_loop0_loop0.body]
    by_cases hlt : pp < mU
    · rw [if_pos hlt]
      have hppm : pp.val < mU.val := by scalar_tac
      have hBq : B + pp.val * q + q ≤ Std.U64.max := by
        have h1 : (pp.val + 1) * q ≤ mU.val * q := Nat.mul_le_mul_right _ (by omega)
        have h2 : (pp.val + 1) * q = pp.val * q + q := by ring
        omega
      step with z_pass_spec words kU negt d rbU g0
        (fun e => passed (base e) (nibW words e) kU.val negt pp.val) (B + pp.val * q)
        hwl hwlt hk hrb (by rw [hdl]; exact hcap) hBq hdb hdv
        as ⟨z, hzl, hzb, hzv, hzf⟩
      step as ⟨pp1, hpp1⟩
      refine ⟨by omega, by rw [hzl]; exact hdl, ?_, ?_, Frame_trans hdf hzf, by omega⟩
      · intro e he w hw
        have := hzb e he w hw
        rw [hpp1]
        have h2 : (pp.val + 1) * q = pp.val * q + q := by ring
        omega
      · intro e he w hw
        rw [hpp1, hzv e he w hw,
          applied_passed (base e) (nibW words e) kU.val negt pp.val w hk hw]
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
theorem z_apply_terms_loop0_spec (vi : alloc.vec.Vec Std.Usize) (vm : alloc.vec.Vec Std.U64)
    (vn : alloc.vec.Vec Bool) (words : alloc.vec.Vec Std.U64) (rbU : Std.Usize)
    (countU : Std.Usize) (out : alloc.vec.Vec Std.U64) (tU : Std.Usize)
    (buf0 : alloc.vec.Vec Std.U64) (g0 : ℕ) (base : ℕ → ℕ → ZMod q) (B : ℕ)
    (hwl : words.val.length = N) (hwlt : ∀ i, i < N → bufN words i < q)
    (hrb : rbU.val = g0 * S) (hcap : (g0 + 8) * S ≤ buf0.val.length)
    (hlen : out.val.length = buf0.val.length)
    (hcnt : vi.val.length = countU.val)
    (hmlen : countU.val ≤ vm.val.length) (hnlen : countU.val ≤ vn.val.length)
    (hidx : ∀ u, u < countU.val → idxAt vi u < N)
    (ht : tU.val ≤ countU.val)
    (hB : B + magSum vm countU.val * q ≤ Std.U64.max)
    (hbnd : ∀ e, e < 8 → ∀ w, w < N → reg out (g0 + e) w ≤ B + magSum vm tU.val * q)
    (hval : ∀ e, e < 8 → ∀ w, w < N → ((reg out (g0 + e) w : ℕ) : ZMod q)
      = base e w + termsSum (nibW words e) vi vm vn tU.val w)
    (hfr : Frame buf0 out g0) :
    quadeval.z_apply_terms_loop0 vi vm vn words rbU countU out tU
      ⦃ z => z.val.length = buf0.val.length
        ∧ (∀ e, e < 8 → ∀ w, w < N → reg z (g0 + e) w ≤ B + magSum vm countU.val * q)
        ∧ (∀ e, e < 8 → ∀ w, w < N → ((reg z (g0 + e) w : ℕ) : ZMod q)
            = base e w + termsSum (nibW words e) vi vm vn countU.val w)
        ∧ Frame buf0 z g0 ⦄ := by
  rw [quadeval.z_apply_terms_loop0]
  apply loop.spec_decr_nat (fun r => countU.val - r.2.val)
    (fun r => r.2.val ≤ countU.val ∧ r.1.val.length = buf0.val.length
      ∧ (∀ e, e < 8 → ∀ w, w < N → reg r.1 (g0 + e) w ≤ B + magSum vm r.2.val * q)
      ∧ (∀ e, e < 8 → ∀ w, w < N → ((reg r.1 (g0 + e) w : ℕ) : ZMod q)
          = base e w + termsSum (nibW words e) vi vm vn r.2.val w)
      ∧ Frame buf0 r.1 g0)
  · rintro ⟨d, tt⟩ ⟨htt, hdl, hdb, hdv, hdf⟩
    dsimp only at htt hdl hdb hdv hdf
    simp only [quadeval.z_apply_terms_loop0.body]
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
      have hBt : B + magSum vm tt.val * q + mm.val * q ≤ Std.U64.max := by
        have h1 : magSum vm (tt.val + 1) ≤ magSum vm countU.val := magSum_mono vm (by omega)
        rw [magSum_succ, ← hmv] at h1
        have h2 : (magSum vm tt.val + mm.val) * q ≤ magSum vm countU.val * q :=
          Nat.mul_le_mul_right _ h1
        have h3 : (magSum vm tt.val + mm.val) * q = magSum vm tt.val * q + mm.val * q := by ring
        omega
      step with z_apply_terms_loop0_loop0_spec words rbU d kk mm nn 0#u64 buf0 g0
        (fun e w => base e w + termsSum (nibW words e) vi vm vn tt.val w)
        (B + magSum vm tt.val * q) hwl hwlt hkN hrb hcap hdl (by simp) hBt
        (by intro e he w hw; simpa using hdb e he w hw)
        (by
          intro e he w hw
          rw [hdv e he w hw]
          unfold passed; simp)
        hdf
        as ⟨z, hzl, hzb, hzv, hzf⟩
      step as ⟨tt1, htt1⟩
      refine ⟨by omega, hzl, ?_, ?_, hzf, by omega⟩
      · intro e he w hw
        have := hzb e he w hw
        rw [htt1, magSum_succ, ← hmv]
        have h3 : (magSum vm tt.val + mm.val) * q = magSum vm tt.val * q + mm.val * q := by ring
        omega
      · intro e he w hw
        rw [htt1, hzv e he w hw, termsSum_succ, hkv, hmv, hnv,
          passed_eq_contribW, add_assoc]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : tt.val = countU.val := by scalar_tac
      rw [heq] at hdb hdv
      exact ⟨hdl, hdb, hdv, hdf⟩
  · exact ⟨ht, hlen, hbnd, hval, hfr⟩

/-- **`z_apply_terms`.** Each region of the row gains the terms sum of its digit
polynomial; the bound grows by the pass count times `q`. -/
theorem z_apply_terms_spec (terms : quadeval.ZTerms) (words : alloc.vec.Vec Std.U64)
    (buf : alloc.vec.Vec Std.U64) (rbU : Std.Usize) (g0 : ℕ) (B : ℕ)
    (hwl : words.val.length = N) (hwlt : ∀ i, i < N → bufN words i < q)
    (hrb : rbU.val = g0 * S) (hcap : (g0 + 8) * S ≤ buf.val.length)
    (hmlen : terms.idx.val.length ≤ terms.mag.val.length)
    (hnlen : terms.idx.val.length ≤ terms.neg.val.length)
    (hidx : ∀ u, u < terms.idx.val.length → idxAt terms.idx u < N)
    (hB : B + magSum terms.mag terms.idx.val.length * q ≤ Std.U64.max)
    (hbnd : ∀ e, e < 8 → ∀ w, w < N → reg buf (g0 + e) w ≤ B) :
    quadeval.z_apply_terms terms words buf rbU
      ⦃ z => z.val.length = buf.val.length
        ∧ (∀ e, e < 8 → ∀ w, w < N →
            reg z (g0 + e) w ≤ B + magSum terms.mag terms.idx.val.length * q)
        ∧ (∀ e, e < 8 → ∀ w, w < N → ((reg z (g0 + e) w : ℕ) : ZMod q)
            = ((reg buf (g0 + e) w : ℕ) : ZMod q)
              + termsSum (nibW words e) terms.idx terms.mag terms.neg
                  terms.idx.val.length w)
        ∧ Frame buf z g0 ⦄ := by
  rw [quadeval.z_apply_terms]
  apply spec_mono (z_apply_terms_loop0_spec terms.idx terms.mag terms.neg words rbU
    (alloc.vec.Vec.len terms.idx) buf 0#usize buf g0
    (fun e w => ((reg buf (g0 + e) w : ℕ) : ZMod q)) B
    hwl hwlt hrb hcap rfl (by simp) (by simpa using hmlen) (by simpa using hnlen)
    (by simpa using hidx) (by simp) (by simpa using hB)
    (by intro e he w hw; simp only [magSum, Finset.range_zero, Finset.sum_empty]; simpa using hbnd e he w hw)
    (by intro e he w hw; simp only [termsSum, Finset.range_zero, Finset.sum_empty]; simp)
    (Frame_refl buf g0))
  rintro z ⟨h1, h2, h3, h4⟩
  refine ⟨h1, by simpa using h2, by simpa using h3, h4⟩

/-! ## 8. `z_terms`: the description, budgeted

`classify_short_loop_spec` at this module's type, with two more conjuncts: the
pass count is the running total, and the total is within the budget -- which is
what the block loop's reduction schedule leans on. -/

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

/-! ## 9. `z_row`: the words, then the terms -/

/-- The words loop: the row's coefficients, as `u64`, in order. -/
theorem z_row_loop_spec (row : ring.Rq) (nU : Std.Usize) (words : alloc.vec.Vec Std.U64)
    (iU : Std.Usize)
    (hrow : Wf row) (hn : nU.val = N) (hi : iU.val ≤ N) (hlen : words.val.length = iU.val)
    (hval : ∀ i, i < iU.val → bufN words i = wordN row i) :
    quadeval.z_row_loop row nU words iU
      ⦃ z => z.val.length = N ∧ ∀ i, i < N → bufN z i = wordN row i ⦄ := by
  rw [quadeval.z_row_loop]
  apply loop.spec_decr_nat (fun t => nU.val - t.2.val)
    (fun t => t.2.val ≤ N ∧ t.1.val.length = t.2.val
      ∧ ∀ i, i < t.2.val → bufN t.1 i = wordN row i)
  · rintro ⟨ws, ii⟩ ⟨hii, hwl, hwv⟩
    dsimp only at hii hwl hwv
    simp only [quadeval.z_row_loop.body]
    by_cases hlt : ii < nU
    · rw [if_pos hlt]
      have hiilt : ii.val < N := by rw [← hn]; scalar_tac
      have hmax : ws.val.length < Std.Usize.max := by
        rw [hwl]; have := usize_max_ge; have h3 : N = 1024 := rfl; omega
      step with Raw32.coeff_word_spec row ii hrow hiilt as ⟨f, hf⟩
      step with to_u64_id f as ⟨x, hx⟩
      step as ⟨ws1, hws1⟩
      step as ⟨ii1, hii1⟩
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [hws1, hii1, List.length_append, hwl]; simp
      · intro i hi
        rw [hii1] at hi
        rcases Nat.lt_or_ge i ii.val with hlt2 | hge
        · unfold bufN
          rw [hws1, getD_append_lt _ _ _ (by omega)]
          exact hwv i hlt2
        · have hieq : i = ws.val.length := by omega
          unfold bufN wordN
          rw [hieq, hws1, getD_append_eq, hx, hf, hwl]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ii.val = N := by rw [← hn]; scalar_tac
      exact ⟨by rw [hwl, heq], fun i hi => hwv i (by rw [heq]; exact hi)⟩
  · exact ⟨hi, hlen, hval⟩

/-- **`z_row`.** Each of the row's eight regions gains the product of the
challenge with that digit polynomial, as a ring element; the bound grows by
the pass count times `q`; nothing else moves. -/
theorem z_row_spec (terms : quadeval.ZTerms) (row : ring.Rq) (buf : alloc.vec.Vec Std.U64)
    (rbU : Std.Usize) (g0 : ℕ) (ci : ring.Rq) (B : ℕ)
    (hrow : Wf row) (hci : Wf ci)
    (hrb : rbU.val = g0 * S) (hcap : (g0 + 8) * S ≤ buf.val.length)
    (hmlen : terms.idx.val.length ≤ terms.mag.val.length)
    (hnlen : terms.idx.val.length ≤ terms.neg.val.length)
    (hidx : ∀ u, u < terms.idx.val.length → idxAt terms.idx u < N)
    (hden : ∀ j, j < N →
      coeffK ci j = descCoeffW terms.idx terms.mag terms.neg terms.idx.val.length j)
    (hB : B + magSum terms.mag terms.idx.val.length * q ≤ Std.U64.max)
    (hbnd : ∀ e, e < 8 → ∀ w, w < N → reg buf (g0 + e) w ≤ B) :
    quadeval.z_row terms row buf rbU
      ⦃ z => z.val.length = buf.val.length
        ∧ (∀ e, e < 8 → ∀ w, w < N →
            reg z (g0 + e) w ≤ B + magSum terms.mag terms.idx.val.length * q)
        ∧ (∀ e, e < 8 → regRq z (g0 + e) = regRq buf (g0 + e) + toRq ci * digitRq row e)
        ∧ Frame buf z g0 ⦄ := by
  rw [quadeval.z_row]
  simp only [alloc.vec.Vec.with_capacity]
  step with z_row_loop_spec row params.RING_DEGREE (alloc.vec.Vec.new Std.U64) 0#usize hrow
    params_RING_DEGREE_val (by simp) (by simp) (by intro i hi; simp at hi)
    as ⟨words, hwl, hwv⟩
  have hwlt : ∀ i, i < N → bufN words i < q := fun i hi => by
    rw [hwv i hi]; exact wordN_lt hrow i
  apply spec_mono (z_apply_terms_spec terms words buf rbU g0 B hwl hwlt hrb hcap hmlen hnlen
    hidx hB hbnd)
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
  apply regRq_gain z buf (g0 + e) ci row hci hrow e
  intro w hw
  rw [h3 e he w hw, nibW_eq_nib words row hrow hwl hwv e,
    termsSum_eq_negConvF (nib row e) terms.idx terms.mag terms.neg terms.idx.val.length w
      hidx hw (fun i hi => nib_of_ge row hrow e hi)]
  congr 2
  exact (funext hdenall).symm

end HachiEquiv.ZPacked
