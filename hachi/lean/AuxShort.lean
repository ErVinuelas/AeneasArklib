/-
`AuxShort.lean` -- the word level of multiplication by a short element.

`ring::mul_short_desc` multiplies by a challenge of bounded centred `ℓ₁` norm
using signed negacyclic shifts, never a product. Its correctness is settled in
two layers: the algebra lives in `Opt.lean` § "Candidate T17 Change 1"
(`HachiEquiv.Opt.MulShort`), stated between pure functions against
`Ring.negConv`; this file is the *word* level, which is where the extracted
loops actually live.

# Why a file of its own

The same reason `AuxCode` and `AuxProduct` are files of their own: the
development below is about a `Vec Std.U64` scratch buffer and the mod-`q`
branches the Rust writes by hand, none of which `Ring.lean`'s statements
mention. `Ring.lean` gets one spec out of it.

# The one awkward thing, named up front

The inner loop does **not** write in index order. Source index `i` lands at
`w = k + i`, folded to `k + i - N` when that reaches `N`, so after `i₀` steps
the touched positions are a *rotation* of `[0, i₀)`. Every invariant here is
therefore stated through the inverse rotation [`srcOf`], which sends a buffer
position back to the source index that writes it. That is the whole reason this
file is longer than the loop it describes.

Arithmetic is carried in `ZMod q` (`valAt`), not in `ℕ`: the Rust's four
branches (`cur - sv` / `cur + q - sv`, `cur + sv` / `cur + sv - q`) are each
shown **once**, by [`subBranch`] and [`addBranch`], to be the canonical
representative of `cur ∓ sv`. Nothing above that point sees a branch.
-/
import AuxCode
import Ring

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.AuxShort

open HachiEquiv.Field HachiEquiv.Ring

/-! ## 1. The two mod-`q` branches

`cur` and `sv` are canonical residues, so each branch is exact in `ℕ` and needs
no `%`. Both lemmas deliver canonicity *and* the `ZMod q` value, because every
caller needs both and proving them together shares the case split. -/

/-- The Rust's subtraction branch: `if cur >= sv then cur - sv else cur + q - sv`. -/
def subW (cur sv : ℕ) : ℕ := if sv ≤ cur then cur - sv else cur + q - sv

/-- The Rust's addition branch: `if cur + sv >= q then cur + sv - q else cur + sv`. -/
def addW (cur sv : ℕ) : ℕ := if q ≤ cur + sv then cur + sv - q else cur + sv

theorem subBranch (cur sv : ℕ) (hcur : cur < q) (hsv : sv < q) :
    subW cur sv < q ∧ ((subW cur sv : ℕ) : ZMod q) = (cur : ZMod q) - (sv : ZMod q) := by
  unfold subW
  by_cases h : sv ≤ cur
  · rw [if_pos h]
    refine ⟨by omega, ?_⟩
    rw [Nat.cast_sub h]
  · rw [if_neg h]
    refine ⟨by omega, ?_⟩
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring

theorem addBranch (cur sv : ℕ) (hcur : cur < q) (hsv : sv < q) :
    addW cur sv < q ∧ ((addW cur sv : ℕ) : ZMod q) = (cur : ZMod q) + (sv : ZMod q) := by
  unfold addW
  by_cases h : q ≤ cur + sv
  · rw [if_pos h]
    refine ⟨by omega, ?_⟩
    rw [Nat.cast_sub h]
    push_cast
    ring
  · rw [if_neg h]
    refine ⟨by omega, ?_⟩
    push_cast
    ring

/-- The signed branch, as one function: `negt` says subtract. -/
def stepW (negt : Bool) (cur sv : ℕ) : ℕ := if negt then subW cur sv else addW cur sv

theorem stepBranch (negt : Bool) (cur sv : ℕ) (hcur : cur < q) (hsv : sv < q) :
    stepW negt cur sv < q ∧
      ((stepW negt cur sv : ℕ) : ZMod q)
        = (cur : ZMod q) + (if negt then -(sv : ZMod q) else (sv : ZMod q)) := by
  unfold stepW
  by_cases h : negt
  · simp only [h, if_pos]
    obtain ⟨h1, h2⟩ := subBranch cur sv hcur hsv
    exact ⟨h1, by rw [h2]; ring⟩
  · simp only [h, Bool.false_eq_true, if_false]
    obtain ⟨h1, h2⟩ := addBranch cur sv hcur hsv
    exact ⟨h1, by rw [h2]⟩

/-! ## 2. The rotation

`w = k + i` folded by `N`. [`srcOf`] inverts it, and the two lemmas say the
two maps are mutually inverse on `[0, N)` -- which is what lets an invariant
quantified over buffer positions be read as one over source indices. -/

/-- Where source index `i` lands, for a term at index `k`. -/
def dstOf (k i : ℕ) : ℕ := if k + i < N then k + i else k + i - N

/-- Which source index writes buffer position `w`. -/
def srcOf (k w : ℕ) : ℕ := if k ≤ w then w - k else N + w - k

/-- The write wrapped, i.e. `X^N = -1` applied, exactly when `k + i` reached `N`. -/
def wrapped (k i : ℕ) : Bool := decide (N ≤ k + i)

theorem dstOf_lt {k i : ℕ} (hk : k < N) (hi : i < N) : dstOf k i < N := by
  unfold dstOf; split <;> omega

theorem srcOf_lt {k w : ℕ} (hk : k < N) (hw : w < N) : srcOf k w < N := by
  unfold srcOf; split <;> omega

theorem srcOf_dstOf {k i : ℕ} (hk : k < N) (hi : i < N) : srcOf k (dstOf k i) = i := by
  unfold srcOf dstOf; split <;> split <;> omega

theorem dstOf_srcOf {k w : ℕ} (hk : k < N) (hw : w < N) : dstOf k (srcOf k w) = w := by
  unfold srcOf dstOf; split <;> split <;> omega

/-- `dstOf k i = w` iff `i` is the source of `w`: the form invariants are used at. -/
theorem dstOf_eq_iff {k i w : ℕ} (hk : k < N) (hi : i < N) (hw : w < N) :
    dstOf k i = w ↔ i = srcOf k w := by
  constructor
  · intro h; rw [← h, srcOf_dstOf hk hi]
  · intro h; rw [h, dstOf_srcOf hk hw]

/-- The wrap flag, read off the destination: the write at `w` wrapped exactly when
`w < k`, i.e. when the fold moved it below the term's own index. -/
theorem wrapped_srcOf {k w : ℕ} (_hk : k < N) (hw : w < N) :
    wrapped k (srcOf k w) = decide (w < k) := by
  unfold wrapped srcOf
  by_cases h : k ≤ w
  · rw [if_pos h]; simp only [decide_eq_decide]; omega
  · rw [if_neg h]; simp only [decide_eq_decide]; omega

/-! ## 3. One pass of the inner loop

The inner loop walks the *source* index `i` and writes to `dstOf k i`. Its
invariant is therefore stated over buffer positions and read back through
[`srcOf`]: position `w` has been written exactly when `srcOf k w < i`. -/

/-- The sign the fold gives buffer position `w`, for a term at index `k` whose own
centred coefficient is negative iff `negt`. `X^N = -1` flips the sign of exactly
the writes the shift wrapped, and [`wrapped_srcOf`] says those are precisely the
positions `w < k`. -/
def sgn (negt : Bool) (k w : ℕ) : ZMod q :=
  if xor negt (decide (w < k)) then -1 else 1

/-- The buffer once the source indices `[0, i)` of one pass have been applied to
`base`. At `i = N` every position has been written exactly once. -/
def applied (base sc : ℕ → ZMod q) (k : ℕ) (negt : Bool) (i : ℕ) : ℕ → ZMod q :=
  fun w => base w + (if srcOf k w < i then sgn negt k w * sc (srcOf k w) else 0)

theorem applied_zero (base sc : ℕ → ZMod q) (k : ℕ) (negt : Bool) :
    applied base sc k negt 0 = base := by
  funext w; unfold applied; simp

/-- One source index's worth of progress: position `w` gains its term exactly at
the step `i = srcOf k w`, and is untouched at every other step. This is the only
lemma the loop's step case needs about [`applied`]. -/
theorem applied_succ (base sc : ℕ → ZMod q) (k : ℕ) (negt : Bool) (i w : ℕ) :
    applied base sc k negt (i + 1) w
      = applied base sc k negt i w
        + (if srcOf k w = i then sgn negt k w * sc (srcOf k w) else 0) := by
  unfold applied
  by_cases h : srcOf k w = i
  · rw [if_pos h, if_pos (by omega), if_neg (by omega)]; ring
  · by_cases h2 : srcOf k w < i
    · rw [if_neg h, if_pos (by omega), if_pos h2]; ring
    · rw [if_neg h, if_neg (by omega), if_neg h2]; ring

/-- **The Rust's sign flag *is* `sgn`.** The body subtracts exactly when
`negt != (pos >= n)`, and that boolean is the folded sign at the destination.
This is the one place `X^N = -1` enters the word level. -/
theorem sgn_eq (negt : Bool) (k i : ℕ) (hk : k < N) (hi : i < N) :
    sgn negt k (dstOf k i) = (if xor negt (wrapped k i) then -1 else 1) := by
  unfold sgn
  rw [← wrapped_srcOf hk (dstOf_lt hk hi), srcOf_dstOf hk hi]

/-- **The effect of one write.** The buffer gains `sgn * sc i` at `dstOf k i` and
is unchanged everywhere else.

Factored out because the inner loop's step case has *four* leaves -- wrapped or
not, crossed with sign-flipped or not -- which differ only in which `ℕ` branch
computed the stored word. Everything after that word is known is this lemma. -/
theorem write_invariant (d : alloc.vec.Vec Std.U64) (base sc : ℕ → ZMod q)
    (k i : ℕ) (negt : Bool) (wU : Std.Usize) (x : Std.U64)
    (hk : k < N) (hi : i < N) (hdl : d.val.length = N) (hcd : AuxCode.Canon q d)
    (hwv : wU.val = dstOf k i) (hxlt : x.val < q)
    (hxval : ((x.val : ℕ) : ZMod q)
      = ((AuxCode.wordAt d wU.val : ℕ) : ZMod q) + sgn negt k wU.val * sc i)
    (hw : ∀ w, w < N → ((AuxCode.wordAt d w : ℕ) : ZMod q) = applied base sc k negt i w) :
    AuxCode.Canon q (d.set wU x) ∧
      ∀ w, w < N → ((AuxCode.wordAt (d.set wU x) w : ℕ) : ZMod q)
        = applied base sc k negt (i + 1) w := by
  refine ⟨AuxCode.Canon_set hcd hxlt, ?_⟩
  intro w hwlt
  rw [applied_succ]
  by_cases heq : w = wU.val
  · have hsrceq : srcOf k wU.val = i := by rw [hwv]; exact srcOf_dstOf hk hi
    have hwltU : wU.val < N := by rw [← heq]; exact hwlt
    rw [heq, AuxCode.wordAt_set_eq (by rw [hdl]; exact hwltU), hxval,
      hw wU.val hwltU, hsrceq, if_pos rfl]
  · have hne : srcOf k w ≠ i := by
      intro hcon
      have hwd : w = dstOf k i := by rw [← hcon, dstOf_srcOf hk hwlt]
      rw [← hwv] at hwd
      exact heq hwd
    rw [AuxCode.wordAt_set_ne heq, hw w hwlt, if_neg hne, add_zero]

/-- **The inner loop.** One pass: add (or subtract) the `k`-shifted `s`, with the
sign folded on wrap. -/
theorem inner_spec (s : ring.Rq) (nU : Std.Usize) (qU : Std.U64)
    (out : alloc.vec.Vec Std.U64) (kU : Std.Usize) (negt : Bool) (iU : Std.Usize)
    (base : ℕ → ZMod q)
    (hs : Wf s) (hn : nU.val = N) (hq : qU.val = q) (hk : kU.val < N)
    (hi : iU.val ≤ N) (hc : AuxCode.Canon q out)
    (hval : ∀ w, w < N → ((AuxCode.wordAt out w : ℕ) : ZMod q)
              = applied base (coeffK s) kU.val negt iU.val w) :
    ring.mul_short_desc_loop1_loop0_loop0 s nU qU out kU negt iU
      ⦃ z => AuxCode.Canon q z ∧ ∀ w, w < N → ((AuxCode.wordAt z w : ℕ) : ZMod q)
              = applied base (coeffK s) kU.val negt N w ⦄ := by
  rw [ring.mul_short_desc_loop1_loop0_loop0]
  apply loop.spec_decr_nat (fun t => nU.val - t.2.val)
    (fun t => t.2.val ≤ N ∧ AuxCode.Canon q t.1
      ∧ ∀ w, w < N → ((AuxCode.wordAt t.1 w : ℕ) : ZMod q)
              = applied base (coeffK s) kU.val negt t.2.val w)
  · rintro ⟨d, ii⟩ ⟨hii, hcd, hw⟩
    dsimp only at hii hcd hw
    simp only [ring.mul_short_desc_loop1_loop0_loop0.body]
    by_cases hlt : ii < nU
    · rw [if_pos hlt]
      have hiilt : ii.val < N := by rw [← hn]; scalar_tac
      have hdl : d.val.length = N := hcd.1
      step with coeff_spec s ii hs as ⟨f, hfred, hfval⟩
      step with to_u64_id f as ⟨sv, hsvf⟩
      have hsvlt : sv.val < q := by rw [hsvf]; exact hfred
      have hsvval : ((sv.val : ℕ) : ZMod q) = coeffK s ii.val := by
        rw [hsvf]; exact hfval
      by_cases hsv0 : sv = 0#u64
      · -- `s`'s coefficient here is zero, so the step writes nothing, and the
        -- term it would have added is `sgn * 0 = 0`
        have hzero : coeffK s ii.val = 0 := by rw [← hsvval, hsv0]; simp
        rw [if_neg (by simp [hsv0])]
        step as ⟨i1, hi1⟩
        refine ⟨by scalar_tac, hcd, ?_, by scalar_tac⟩
        intro w hwlt
        rw [hi1, applied_succ, hw w hwlt]
        by_cases hsrc : srcOf kU.val w = ii.val
        · rw [if_pos hsrc, hsrc, hzero, mul_zero, add_zero]
        · rw [if_neg hsrc, add_zero]
      · rw [if_pos (by simp [hsv0])]
        step as ⟨pos, hpos⟩
        by_cases hge : N ≤ kU.val + ii.val
        · -- the shift wrapped: `X^N = -1` flips this write's sign
          have hpge : pos ≥ nU := by scalar_tac
          rw [if_pos hpge]
          step as ⟨wU, hwU⟩
          have hwv : wU.val = dstOf kU.val ii.val := by
            unfold dstOf; rw [if_neg (by omega)]; omega
          have hwltN : wU.val < N := by rw [hwv]; exact dstOf_lt hk hiilt
          have hdf : decide (pos ≥ nU) = true := by simp [hpge]
          have hsgnbase : sgn negt kU.val wU.val = (if xor negt true then -1 else 1) := by
            rw [hwv, sgn_eq negt kU.val ii.val hk hiilt]
            unfold wrapped
            rw [decide_eq_true hge]
          step as ⟨cur, hcurg⟩
          have hcurv : cur.val = AuxCode.wordAt d wU.val := by
            rw [hcurg, ← AuxCode.wordAt_of_lt (v := d) (t := wU.val)
              (by rw [hdl]; exact hwltN)]
          have hcurlt : cur.val < q := by
            rw [hcurv]; exact AuxCode.wordAt_lt hcd (by norm_num [HachiEquiv.Field.q]) _
          rw [hdf]
          cases negt with
          | false =>
            -- the term is positive but the write wrapped, so it SUBTRACTS
            have hsgnv : sgn false kU.val wU.val = -1 := by
              rw [hsgnbase]; simp
            simp only [bne_iff_ne, ne_eq, Bool.false_eq_true, not_false_eq_true,
              ite_true]
            have hsub : ∀ z : Std.U64, z.val = subW cur.val sv.val →
                ((z.val : ℕ) : ZMod q)
                  = ((AuxCode.wordAt d wU.val : ℕ) : ZMod q)
                    + sgn false kU.val wU.val * coeffK s ii.val := by
              intro z hz
              rw [hz, (subBranch cur.val sv.val hcurlt hsvlt).2, hcurv, hsgnv,
                ← hsvval]
              ring
            by_cases hcs : sv.val ≤ cur.val
            · rw [if_pos (show cur ≥ sv by scalar_tac)]
              step as ⟨x, hx⟩
              have hxs : x.val = subW cur.val sv.val := by
                unfold subW; rw [if_pos hcs]; scalar_tac
              step as ⟨pr, hpr1, hpr2⟩
              obtain ⟨e, bk⟩ := pr
              dsimp only at hpr2 ⊢
              rw [hpr2]
              step as ⟨i1, hi1⟩
              obtain ⟨hcan, hvals⟩ := write_invariant d base (coeffK s) kU.val ii.val
                false wU x hk hiilt hdl hcd hwv
                (by rw [hxs]; exact (subBranch cur.val sv.val hcurlt hsvlt).1)
                (hsub x hxs) hw
              exact ⟨by scalar_tac, hcan, by rw [hi1]; exact hvals, by scalar_tac⟩
            · rw [if_neg (show ¬ (cur ≥ sv) by scalar_tac)]
              step as ⟨i2, hi2⟩
              step as ⟨x, hx⟩
              have hxs : x.val = subW cur.val sv.val := by
                unfold subW; rw [if_neg hcs, ← hq]; scalar_tac
              step as ⟨pr, hpr1, hpr2⟩
              obtain ⟨e, bk⟩ := pr
              dsimp only at hpr2 ⊢
              rw [hpr2]
              step as ⟨i1, hi1⟩
              obtain ⟨hcan, hvals⟩ := write_invariant d base (coeffK s) kU.val ii.val
                false wU x hk hiilt hdl hcd hwv
                (by rw [hxs]; exact (subBranch cur.val sv.val hcurlt hsvlt).1)
                (hsub x hxs) hw
              exact ⟨by scalar_tac, hcan, by rw [hi1]; exact hvals, by scalar_tac⟩
          | true =>
            -- the term is negative AND the write wrapped: the two flips cancel,
            -- so it ADDS
            have hsgnv : sgn true kU.val wU.val = 1 := by
              rw [hsgnbase]; simp
            simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
            have hadd : ∀ z : Std.U64, z.val = addW cur.val sv.val →
                ((z.val : ℕ) : ZMod q)
                  = ((AuxCode.wordAt d wU.val : ℕ) : ZMod q)
                    + sgn true kU.val wU.val * coeffK s ii.val := by
              intro z hz
              rw [hz, (addBranch cur.val sv.val hcurlt hsvlt).2, hcurv, hsgnv,
                ← hsvval]
              ring
            step as ⟨sum, hsum⟩
            by_cases hcq : q ≤ cur.val + sv.val
            · rw [if_pos (show sum ≥ qU by scalar_tac)]
              step as ⟨x, hx⟩
              have hxs : x.val = addW cur.val sv.val := by
                unfold addW; rw [if_pos hcq, ← hq]; scalar_tac
              step as ⟨pr, hpr1, hpr2⟩
              obtain ⟨e, bk⟩ := pr
              dsimp only at hpr2 ⊢
              rw [hpr2]
              step as ⟨i1, hi1⟩
              obtain ⟨hcan, hvals⟩ := write_invariant d base (coeffK s) kU.val ii.val
                true wU x hk hiilt hdl hcd hwv
                (by rw [hxs]; exact (addBranch cur.val sv.val hcurlt hsvlt).1)
                (hadd x hxs) hw
              exact ⟨by scalar_tac, hcan, by rw [hi1]; exact hvals, by scalar_tac⟩
            · rw [if_neg (show ¬ (sum ≥ qU) by scalar_tac)]
              have hxs : sum.val = addW cur.val sv.val := by
                unfold addW; rw [if_neg hcq]; scalar_tac
              -- one `step` consumes both the `ok sum` bind and the `index_mut`
              step as ⟨pr, hpr1, hpr2⟩
              obtain ⟨e, bk⟩ := pr
              dsimp only at hpr2 ⊢
              rw [hpr2]
              step as ⟨i1, hi1⟩
              obtain ⟨hcan, hvals⟩ := write_invariant d base (coeffK s) kU.val ii.val
                true wU sum hk hiilt hdl hcd hwv
                (by rw [hxs]; exact (addBranch cur.val sv.val hcurlt hsvlt).1)
                (hadd sum hxs) hw
              exact ⟨by scalar_tac, hcan, by rw [hi1]; exact hvals, by scalar_tac⟩
        · -- the shift stayed inside the ring: no sign fold, `pos` is the target
          have hpge : ¬ (pos ≥ nU) := by scalar_tac
          rw [if_neg hpge]
          have hwv : pos.val = dstOf kU.val ii.val := by
            unfold dstOf; rw [if_pos (by omega)]; exact hpos
          have hwltN : pos.val < N := by rw [hwv]; exact dstOf_lt hk hiilt
          have hdf : decide (pos ≥ nU) = false := by simp [hpge]
          have hsgnbase : sgn negt kU.val pos.val = (if xor negt false then -1 else 1) := by
            rw [hwv, sgn_eq negt kU.val ii.val hk hiilt]
            unfold wrapped
            rw [decide_eq_false (by omega : ¬ (N ≤ kU.val + ii.val))]
          -- `ok pos` is a bind, so this one `step` also consumes the read
          step as ⟨cur, hcurg⟩
          have hcurv : cur.val = AuxCode.wordAt d pos.val := by
            rw [hcurg, ← AuxCode.wordAt_of_lt (v := d) (t := pos.val)
              (by rw [hdl]; exact hwltN)]
          have hcurlt : cur.val < q := by
            rw [hcurv]; exact AuxCode.wordAt_lt hcd (by norm_num [HachiEquiv.Field.q]) _
          rw [hdf]
          cases negt with
          | false =>
            -- positive term, no wrap: it ADDS
            have hsgnv : sgn false kU.val pos.val = 1 := by rw [hsgnbase]; simp
            simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
            have hadd : ∀ z : Std.U64, z.val = addW cur.val sv.val →
                ((z.val : ℕ) : ZMod q)
                  = ((AuxCode.wordAt d pos.val : ℕ) : ZMod q)
                    + sgn false kU.val pos.val * coeffK s ii.val := by
              intro z hz
              rw [hz, (addBranch cur.val sv.val hcurlt hsvlt).2, hcurv, hsgnv, ← hsvval]
              ring
            step as ⟨sum, hsum⟩
            by_cases hcq : q ≤ cur.val + sv.val
            · rw [if_pos (show sum ≥ qU by scalar_tac)]
              step as ⟨x, hx⟩
              have hxs : x.val = addW cur.val sv.val := by
                unfold addW; rw [if_pos hcq, ← hq]; scalar_tac
              step as ⟨pr, hpr1, hpr2⟩
              obtain ⟨e, bk⟩ := pr
              dsimp only at hpr2 ⊢
              rw [hpr2]
              step as ⟨i1, hi1⟩
              obtain ⟨hcan, hvals⟩ := write_invariant d base (coeffK s) kU.val ii.val
                false pos x hk hiilt hdl hcd hwv
                (by rw [hxs]; exact (addBranch cur.val sv.val hcurlt hsvlt).1)
                (hadd x hxs) hw
              exact ⟨by scalar_tac, hcan, by rw [hi1]; exact hvals, by scalar_tac⟩
            · rw [if_neg (show ¬ (sum ≥ qU) by scalar_tac)]
              have hxs : sum.val = addW cur.val sv.val := by
                unfold addW; rw [if_neg hcq]; scalar_tac
              step as ⟨pr, hpr1, hpr2⟩
              obtain ⟨e, bk⟩ := pr
              dsimp only at hpr2 ⊢
              rw [hpr2]
              step as ⟨i1, hi1⟩
              obtain ⟨hcan, hvals⟩ := write_invariant d base (coeffK s) kU.val ii.val
                false pos sum hk hiilt hdl hcd hwv
                (by rw [hxs]; exact (addBranch cur.val sv.val hcurlt hsvlt).1)
                (hadd sum hxs) hw
              exact ⟨by scalar_tac, hcan, by rw [hi1]; exact hvals, by scalar_tac⟩
          | true =>
            -- negative term, no wrap: it SUBTRACTS
            have hsgnv : sgn true kU.val pos.val = -1 := by rw [hsgnbase]; simp
            simp only [bne_iff_ne, ne_eq, Bool.true_eq_false, not_false_eq_true,
              ite_true]
            have hsub : ∀ z : Std.U64, z.val = subW cur.val sv.val →
                ((z.val : ℕ) : ZMod q)
                  = ((AuxCode.wordAt d pos.val : ℕ) : ZMod q)
                    + sgn true kU.val pos.val * coeffK s ii.val := by
              intro z hz
              rw [hz, (subBranch cur.val sv.val hcurlt hsvlt).2, hcurv, hsgnv, ← hsvval]
              ring
            by_cases hcs : sv.val ≤ cur.val
            · rw [if_pos (show cur ≥ sv by scalar_tac)]
              step as ⟨x, hx⟩
              have hxs : x.val = subW cur.val sv.val := by
                unfold subW; rw [if_pos hcs]; scalar_tac
              step as ⟨pr, hpr1, hpr2⟩
              obtain ⟨e, bk⟩ := pr
              dsimp only at hpr2 ⊢
              rw [hpr2]
              step as ⟨i1, hi1⟩
              obtain ⟨hcan, hvals⟩ := write_invariant d base (coeffK s) kU.val ii.val
                true pos x hk hiilt hdl hcd hwv
                (by rw [hxs]; exact (subBranch cur.val sv.val hcurlt hsvlt).1)
                (hsub x hxs) hw
              exact ⟨by scalar_tac, hcan, by rw [hi1]; exact hvals, by scalar_tac⟩
            · rw [if_neg (show ¬ (cur ≥ sv) by scalar_tac)]
              step as ⟨i2, hi2⟩
              step as ⟨x, hx⟩
              have hxs : x.val = subW cur.val sv.val := by
                unfold subW; rw [if_neg hcs, ← hq]; scalar_tac
              step as ⟨pr, hpr1, hpr2⟩
              obtain ⟨e, bk⟩ := pr
              dsimp only at hpr2 ⊢
              rw [hpr2]
              step as ⟨i1, hi1⟩
              obtain ⟨hcan, hvals⟩ := write_invariant d base (coeffK s) kU.val ii.val
                true pos x hk hiilt hdl hcd hwv
                (by rw [hxs]; exact (subBranch cur.val sv.val hcurlt hsvlt).1)
                (hsub x hxs) hw
              exact ⟨by scalar_tac, hcan, by rw [hi1]; exact hvals, by scalar_tac⟩
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ii.val = N := by
        have : nU.val ≤ ii.val := by scalar_tac
        omega
      -- rewrite the HYPOTHESIS: `rw [← heq]` in the goal would also turn the
      -- bound `w < N` into `w < ii`, which is the collision `Ring.lean` warns of
      rw [heq] at hw
      exact ⟨hcd, hw⟩
  · exact ⟨hi, hc, hval⟩

/-! ## 4. The `pass` loop: `m` copies, and no multiplication

`mul_short_desc` never multiplies. It adds the shifted operand `m` times, and
`Σ mag ≤ OMEGA` is what bounds the total at 16 passes. At the word level that
repetition is simply multiplication by `m` in `ZMod q`. -/

/-- The buffer after `p` complete passes of the term `(k, negt)` over `base`. -/
def passed (base sc : ℕ → ZMod q) (k : ℕ) (negt : Bool) (p : ℕ) : ℕ → ZMod q :=
  fun w => base w + (p : ZMod q) * (sgn negt k w * sc (srcOf k w))

theorem passed_zero (base sc : ℕ → ZMod q) (k : ℕ) (negt : Bool) :
    passed base sc k negt 0 = base := by
  funext w; unfold passed; simp

/-- One complete pass advances the pass count by one. Every position is written
exactly once per pass, because [`srcOf`] lands inside `[0, N)` for every `w`. -/
theorem applied_passed (base sc : ℕ → ZMod q) (k : ℕ) (negt : Bool) (p w : ℕ)
    (hk : k < N) (hw : w < N) :
    applied (passed base sc k negt p) sc k negt N w = passed base sc k negt (p + 1) w := by
  unfold applied passed
  rw [if_pos (srcOf_lt hk hw)]
  push_cast
  ring

/-- **The pass loop.** `m` repetitions of one shifted add. -/
theorem pass_spec (s : ring.Rq) (nU : Std.Usize) (qU : Std.U64)
    (out : alloc.vec.Vec Std.U64) (kU : Std.Usize) (mU : Std.U64) (negt : Bool)
    (passU : Std.U64) (base : ℕ → ZMod q)
    (hs : Wf s) (hn : nU.val = N) (hq : qU.val = q) (hk : kU.val < N)
    (hp : passU.val ≤ mU.val) (hc : AuxCode.Canon q out)
    (hval : ∀ w, w < N → ((AuxCode.wordAt out w : ℕ) : ZMod q)
              = passed base (coeffK s) kU.val negt passU.val w) :
    ring.mul_short_desc_loop1_loop0 s nU qU out kU mU negt passU
      ⦃ z => AuxCode.Canon q z ∧ ∀ w, w < N → ((AuxCode.wordAt z w : ℕ) : ZMod q)
              = passed base (coeffK s) kU.val negt mU.val w ⦄ := by
  rw [ring.mul_short_desc_loop1_loop0]
  apply loop.spec_decr_nat (fun t => mU.val - t.2.val)
    (fun t => t.2.val ≤ mU.val ∧ AuxCode.Canon q t.1
      ∧ ∀ w, w < N → ((AuxCode.wordAt t.1 w : ℕ) : ZMod q)
              = passed base (coeffK s) kU.val negt t.2.val w)
  · rintro ⟨d, pp⟩ ⟨hpp, hcd, hw⟩
    dsimp only at hpp hcd hw
    simp only [ring.mul_short_desc_loop1_loop0.body]
    by_cases hlt : pp < mU
    · rw [if_pos hlt]
      step with inner_spec s nU qU d kU negt 0#usize
        (passed base (coeffK s) kU.val negt pp.val) hs hn hq hk (by simp) hcd
        (by
          intro w hwlt
          unfold applied
          simpa using hw w hwlt) as ⟨z, hzc, hzv⟩
      step as ⟨pp1, hpp1⟩
      refine ⟨by scalar_tac, hzc, ?_, by scalar_tac⟩
      intro w hwlt
      rw [hpp1, ← applied_passed base (coeffK s) kU.val negt pp.val w hk hwlt]
      exact hzv w hwlt
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : pp.val = mU.val := by scalar_tac
      rw [heq] at hw
      exact ⟨hcd, hw⟩
  · exact ⟨hp, hc, hval⟩

/-! ## 5. The terms loop

One term contributes `mag · sgn · s(srcOf k ·)` to every position. Note this
*is* `Opt.lean`'s `MulShort.contrib` written at the word level: for `k ≤ w` both
read `termVal * sc (w - k)`, and for `k > w` both read `-(termVal * sc (N + w - k))`,
the sign coming from `sgn`'s wrap flag on one side and from `negConv`'s
subtraction on the other. The two files cannot import each other -- `Opt` is last
in the Lake root order -- so the agreement is by construction, not by a shared
lemma. -/

/-- The three parallel vectors of a `ShortMul`, read positionally. -/
def idxAt (v : alloc.vec.Vec Std.Usize) (u : ℕ) : ℕ := (v.val.getD u 0#usize).val
def magAt (v : alloc.vec.Vec Std.U64) (u : ℕ) : ℕ := (v.val.getD u 0#u64).val
def negAt (v : alloc.vec.Vec Bool) (u : ℕ) : Bool := v.val.getD u false

/-- One described term's contribution to buffer position `w`. -/
def contribW (sc : ℕ → ZMod q) (kk mm : ℕ) (negt : Bool) (w : ℕ) : ZMod q :=
  (mm : ZMod q) * (sgn negt kk w * sc (srcOf kk w))

/-- The first `t` terms' total contribution to position `w`. -/
def termsSum (sc : ℕ → ZMod q) (vi : alloc.vec.Vec Std.Usize)
    (vm : alloc.vec.Vec Std.U64) (vn : alloc.vec.Vec Bool) (t w : ℕ) : ZMod q :=
  ∑ u ∈ Finset.range t, contribW sc (idxAt vi u) (magAt vm u) (negAt vn u) w

/-- `passed` over a term *is* that term's `contribW`. -/
theorem passed_eq_contribW (base sc : ℕ → ZMod q) (kk mm : ℕ) (negt : Bool) (w : ℕ) :
    passed base sc kk negt mm w = base w + contribW sc kk mm negt w := by
  unfold passed contribW; ring

/-- **The terms loop.** -/
theorem terms_spec (vi : alloc.vec.Vec Std.Usize) (vm : alloc.vec.Vec Std.U64)
    (vn : alloc.vec.Vec Bool) (s : ring.Rq) (nU : Std.Usize) (qU : Std.U64)
    (termsU : Std.Usize) (out : alloc.vec.Vec Std.U64) (tU : Std.Usize)
    (base : ℕ → ZMod q)
    (hs : Wf s) (hn : nU.val = N) (hq : qU.val = q)
    (hlen : vi.val.length = termsU.val)
    (hmlen : termsU.val ≤ vm.val.length) (hnlen : termsU.val ≤ vn.val.length)
    (hidx : ∀ u, u < termsU.val → idxAt vi u < N)
    (ht : tU.val ≤ termsU.val) (hc : AuxCode.Canon q out)
    (hval : ∀ w, w < N → ((AuxCode.wordAt out w : ℕ) : ZMod q)
              = base w + termsSum (coeffK s) vi vm vn tU.val w) :
    ring.mul_short_desc_loop1 vi vm vn s nU qU termsU out tU
      ⦃ z => AuxCode.Canon q z ∧ ∀ w, w < N → ((AuxCode.wordAt z w : ℕ) : ZMod q)
              = base w + termsSum (coeffK s) vi vm vn termsU.val w ⦄ := by
  rw [ring.mul_short_desc_loop1]
  apply loop.spec_decr_nat (fun r => termsU.val - r.2.val)
    (fun r => r.2.val ≤ termsU.val ∧ AuxCode.Canon q r.1
      ∧ ∀ w, w < N → ((AuxCode.wordAt r.1 w : ℕ) : ZMod q)
              = base w + termsSum (coeffK s) vi vm vn r.2.val w)
  · rintro ⟨d, tt⟩ ⟨htt, hcd, hw⟩
    dsimp only at htt hcd hw
    simp only [ring.mul_short_desc_loop1.body]
    by_cases hlt : tt < termsU
    · rw [if_pos hlt]
      have httlt : tt.val < termsU.val := by scalar_tac
      step as ⟨kk, hkk⟩
      step as ⟨mm, hmm⟩
      step as ⟨nn, hnn⟩
      have hkkv : kk.val = idxAt vi tt.val := by
        unfold idxAt; rw [hkk, List.getD_eq_getElem _ _ (by rw [hlen]; exact httlt)]
      have hmmv : mm.val = magAt vm tt.val := by
        unfold magAt; rw [hmm, List.getD_eq_getElem _ _ (by omega)]
      have hnnv : nn = negAt vn tt.val := by
        unfold negAt; rw [hnn, List.getD_eq_getElem _ _ (by omega)]
      have hkN : kk.val < N := by rw [hkkv]; exact hidx tt.val httlt
      step with pass_spec s nU qU d kk mm nn 0#u64
        (fun w => base w + termsSum (coeffK s) vi vm vn tt.val w)
        hs hn hq hkN (by simp) hcd
        (by
          intro w hwlt
          unfold passed
          simpa using hw w hwlt) as ⟨z, hzc, hzv⟩
      step as ⟨tt1, htt1⟩
      refine ⟨by scalar_tac, hzc, ?_, by scalar_tac⟩
      intro w hwlt
      rw [htt1, hzv w hwlt, passed_eq_contribW]
      unfold termsSum
      rw [Finset.sum_range_succ, hkkv, hmmv, hnnv]
      ring
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : tt.val = termsU.val := by scalar_tac
      rw [heq] at hw
      exact ⟨hcd, hw⟩
  · exact ⟨ht, hc, hval⟩

/-! ## 6. The two push loops

The zero-fill that creates the accumulator, and the conversion that wraps the
finished words back as `Fp`. Both are the `Vec.push` shape `Ring.mul_loop0`
already uses; the two `getD` lemmas are copies because that file's are
`private`. -/

private theorem getD_append_lt' {α : Type} (l : List α) (x d : α) {j : ℕ}
    (hj : j < l.length) : (l ++ [x]).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hj,
    List.getElem_append_left hj]

private theorem getD_append_eq' {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
  simp

/-- **The zero-fill.** The accumulator starts as `N` zero words. -/
theorem zerofill_spec (nU : Std.Usize) (out : alloc.vec.Vec Std.U64) (zU : Std.Usize)
    (hn : nU.val = N) (hz : zU.val ≤ nU.val) (hlen : out.val.length = zU.val)
    (hzero : ∀ u, u < zU.val → AuxCode.wordAt out u = 0) :
    ring.mul_short_desc_loop0 nU out zU
      ⦃ r => r.val.length = N ∧ ∀ u, u < N → AuxCode.wordAt r u = 0 ⦄ := by
  rw [ring.mul_short_desc_loop0]
  apply loop.spec_decr_nat (fun t => nU.val - t.2.val)
    (fun t => t.2.val ≤ nU.val ∧ t.1.val.length = t.2.val
      ∧ ∀ u, u < t.2.val → AuxCode.wordAt t.1 u = 0)
  · rintro ⟨d, zz⟩ ⟨hzz, hdl, hdz⟩
    dsimp only at hzz hdl hdz
    simp only [ring.mul_short_desc_loop0.body]
    by_cases hlt : zz < nU
    · rw [if_pos hlt]
      step as ⟨d1, hd1⟩
      step as ⟨zz1, hzz1⟩
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [hd1, hzz1, List.length_append, hdl]; simp
      · intro u hu
        rw [hzz1] at hu
        simp only [AuxCode.wordAt] at hdz ⊢
        rcases Nat.lt_or_ge u zz.val with hult | huge
        · rw [hd1, getD_append_lt' _ _ _ (by omega)]
          exact hdz u hult
        · have hueq : u = d.val.length := by omega
          rw [hueq, hd1, getD_append_eq']
          simp
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : zz.val = nU.val := by scalar_tac
      exact ⟨by rw [hdl, heq, hn], fun u hu => hdz u (by rw [heq, hn]; exact hu)⟩
  · exact ⟨hz, hlen, hzero⟩

/-- **The conversion.** The finished words, wrapped back as `Fp`. -/
theorem convert_spec (nU : Std.Usize) (out : alloc.vec.Vec Std.U64)
    (res : alloc.vec.Vec cpoly.field.Fp) (jU : Std.Usize)
    (hn : nU.val = N) (hj : jU.val ≤ nU.val) (hol : out.val.length = N)
    (hlen : res.val.length = jU.val) (hred : ∀ u ∈ res.val, Red u)
    (hval : ∀ t, t < jU.val → coeffK res t = ((AuxCode.wordAt out t : ℕ) : ZMod q)) :
    ring.mul_short_desc_loop2 nU out res jU
      ⦃ r => Wf r ∧ ∀ t, t < N → coeffK r t = ((AuxCode.wordAt out t : ℕ) : ZMod q) ⦄ := by
  rw [ring.mul_short_desc_loop2]
  apply loop.spec_decr_nat (fun t => nU.val - t.2.val)
    (fun t => t.2.val ≤ nU.val ∧ t.1.val.length = t.2.val
      ∧ (∀ u ∈ t.1.val, Red u)
      ∧ ∀ v, v < t.2.val → coeffK t.1 v = ((AuxCode.wordAt out v : ℕ) : ZMod q))
  · rintro ⟨d, jj⟩ ⟨hjj, hdl, hdr, hdv⟩
    dsimp only at hjj hdl hdr hdv
    simp only [ring.mul_short_desc_loop2.body]
    by_cases hlt : jj < nU
    · rw [if_pos hlt]
      have hjb : jj.val < out.val.length := by rw [hol, ← hn]; scalar_tac
      step as ⟨x, hx⟩
      have hxv : x.val = AuxCode.wordAt out jj.val := by
        rw [hx, ← AuxCode.wordAt_of_lt (v := out) (t := jj.val) hjb]
      step with fp_new_spec x as ⟨f, hfred, hfval⟩
      step as ⟨d1, hd1⟩
      step as ⟨jj1, hjj1⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
      · rw [hd1, hjj1, List.length_append, hdl]; simp
      · intro u hu
        rw [hd1] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hdr u h
        · rw [List.mem_singleton.mp h]; exact hfred
      · intro v hv
        rw [hjj1] at hv
        simp only [coeffK] at hdv ⊢
        rcases Nat.lt_or_ge v jj.val with hvlt | hvge
        · rw [hd1, getD_append_lt' _ _ _ (by omega)]
          exact hdv v hvlt
        · have hveq : v = d.val.length := by omega
          rw [hveq, hd1, getD_append_eq', hdl]
          rw [← hxv]
          exact hfval
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = nU.val := by scalar_tac
      exact ⟨⟨by rw [hdl, heq, hn], hdr⟩,
        fun v hv => hdv v (by rw [heq, hn]; exact hv)⟩
  · exact ⟨hj, hlen, hred, hval⟩

/-! ## 7. The shared algebra

These seven items were first written inside `Opt.lean`'s `MulShort` section and
live here instead so that **both** layers use one copy: `Opt.lean` imports this
file (it is last in the Lake root order, so that direction is available while
the reverse is not), and the extracted specs below need the same lemmas to reach
`Ring.negConv`. `Ring.lean` § `to_u64_id` states the principle -- one shared
lemma beats two copies. -/

/-- The coefficient function of a single signed monomial `v · X^j`. -/
def single (j : ℕ) (v : ZMod q) : ℕ → ZMod q := fun i => if i = j then v else 0

/-- [`Ring.negConv`] over bare coefficient functions. -/
def negConvF (a sc : ℕ → ZMod q) (w : ℕ) : ZMod q :=
  (∑ p ∈ Finset.antidiagonal w, a p.1 * sc p.2)
    - ∑ p ∈ Finset.antidiagonal (N + w), a p.1 * sc p.2

/-- One monomial's contribution to coefficient `w`: the plain write when the
shift stays in the ring, the sign-flipped one when it does not. -/
def contrib (sc : ℕ → ZMod q) (j : ℕ) (v : ZMod q) (w : ℕ) : ZMod q :=
  if j ≤ w then v * sc (w - j) else -(v * sc (N + w - j))

theorem negConvF_add_left (a b sc : ℕ → ZMod q) (w : ℕ) :
    negConvF (fun i => a i + b i) sc w = negConvF a sc w + negConvF b sc w := by
  unfold negConvF
  simp only [add_mul, Finset.sum_add_distrib]
  ring

theorem negConvF_zero_left (sc : ℕ → ZMod q) (w : ℕ) :
    negConvF (fun _ => 0) sc w = 0 := by
  unfold negConvF; simp

/-- **The monomial case: multiplying by `v · X^j` is a sign-folded shift.**

`j ≤ w`: the `w`-th antidiagonal contains `(j, w - j)` and nothing else the
monomial is supported at, while the `(N + w)`-th reads `sc` at `N + w - j ≥ N`,
off the end and therefore zero.

`j > w`: the `w`-th antidiagonal has no pair with first component `j`, and the
`(N + w)`-th contributes `v · sc (N + w - j)` with `N + w - j < N`. The
subtraction in [`negConvF`] is where the sign flip comes from. -/
theorem negConvF_single (j : ℕ) (v : ZMod q) (sc : ℕ → ZMod q) (w : ℕ)
    (hj : j < N) (_hw : w < N) (hsc : ∀ i, N ≤ i → sc i = 0) :
    negConvF (single j v) sc w = contrib sc j v w := by
  unfold negConvF contrib single
  by_cases h : j ≤ w
  · have h1 : (∑ p ∈ Finset.antidiagonal w,
        (if p.1 = j then v else 0) * sc p.2) = v * sc (w - j) := by
      rw [Finset.sum_eq_single_of_mem (j, w - j)
        (by simp only [Finset.mem_antidiagonal]; omega)]
      · simp
      · intro b hb hne
        simp only [Finset.mem_antidiagonal] at hb
        by_cases hb1 : b.1 = j
        · exact absurd (Prod.ext hb1 (by omega)) hne
        · rw [if_neg hb1, zero_mul]
    have h2 : (∑ p ∈ Finset.antidiagonal (N + w),
        (if p.1 = j then v else 0) * sc p.2) = 0 := by
      refine Finset.sum_eq_zero (fun b hb => ?_)
      simp only [Finset.mem_antidiagonal] at hb
      by_cases hb1 : b.1 = j
      · rw [if_pos hb1, hsc b.2 (by omega), mul_zero]
      · rw [if_neg hb1, zero_mul]
    rw [h1, h2, if_pos h, sub_zero]
  · have h1 : (∑ p ∈ Finset.antidiagonal w,
        (if p.1 = j then v else 0) * sc p.2) = 0 := by
      refine Finset.sum_eq_zero (fun b hb => ?_)
      simp only [Finset.mem_antidiagonal] at hb
      rw [if_neg (by omega), zero_mul]
    have h2 : (∑ p ∈ Finset.antidiagonal (N + w),
        (if p.1 = j then v else 0) * sc p.2) = v * sc (N + w - j) := by
      rw [Finset.sum_eq_single_of_mem (j, N + w - j)
        (by simp only [Finset.mem_antidiagonal]; omega)]
      · simp
      · intro b hb hne
        simp only [Finset.mem_antidiagonal] at hb
        by_cases hb1 : b.1 = j
        · exact absurd (Prod.ext hb1 (by omega)) hne
        · rw [if_neg hb1, zero_mul]
    rw [h1, h2, if_neg h, zero_sub]

/-- The bridge to the extracted model: [`negConvF`] over `coeffK` *is*
[`Ring.negConv`], definitionally. -/
theorem negConvF_coeffK (a b : ring.Rq) (w : ℕ) :
    negConvF (coeffK a) (coeffK b) w = negConv a b w := rfl

/-! ## 8. From the terms sum to `negConv`

The last step: the buffer the loops build is `Ring.negConv` against the element
the description denotes. `contribW` and `contrib` are shown equal, and then the
sum over terms is matched to `negConvF` by linearity. -/

/-- The centred coefficient one described term denotes. -/
def termValW (mm : ℕ) (negt : Bool) : ZMod q :=
  if negt then -((mm : ℕ) : ZMod q) else ((mm : ℕ) : ZMod q)

/-- The coefficient function the first `t` terms of a description denote. -/
def descCoeffW (vi : alloc.vec.Vec Std.Usize) (vm : alloc.vec.Vec Std.U64)
    (vn : alloc.vec.Vec Bool) (t : ℕ) : ℕ → ZMod q :=
  fun j => ∑ u ∈ Finset.range t,
    single (idxAt vi u) (termValW (magAt vm u) (negAt vn u)) j

/-- The word-level contribution *is* the algebra's [`contrib`]. This is the
identification the whole file exists to make: on one side the sign comes from
`sgn`'s wrap flag, on the other from `negConvF`'s subtraction. -/
theorem contribW_eq_contrib (sc : ℕ → ZMod q) (kk mm : ℕ) (negt : Bool) (w : ℕ) :
    contribW sc kk mm negt w = contrib sc kk (termValW mm negt) w := by
  unfold contribW contrib termValW sgn srcOf
  by_cases h : kk ≤ w
  · rw [if_pos h, if_pos h, decide_eq_false (by omega : ¬ (w < kk))]
    cases negt <;> simp
  · rw [if_neg h, if_neg h, decide_eq_true (by omega : w < kk)]
    cases negt <;> simp

/-- **The terms sum is `negConvF` against the denoted element.** -/
theorem termsSum_eq_negConvF (sc : ℕ → ZMod q) (vi : alloc.vec.Vec Std.Usize)
    (vm : alloc.vec.Vec Std.U64) (vn : alloc.vec.Vec Bool) (t w : ℕ)
    (hidx : ∀ u, u < t → idxAt vi u < N) (hw : w < N)
    (hsc : ∀ i, N ≤ i → sc i = 0) :
    termsSum sc vi vm vn t w = negConvF (descCoeffW vi vm vn t) sc w := by
  induction t with
  | zero =>
    unfold termsSum descCoeffW
    simp only [Finset.range_zero, Finset.sum_empty]
    exact (negConvF_zero_left sc w).symm
  | succ n ih =>
    have hfun : descCoeffW vi vm vn (n + 1)
        = fun j => descCoeffW vi vm vn n j
            + single (idxAt vi n) (termValW (magAt vm n) (negAt vn n)) j := by
      funext j
      unfold descCoeffW
      rw [Finset.sum_range_succ]
    rw [hfun, negConvF_add_left,
      negConvF_single (idxAt vi n) (termValW (magAt vm n) (negAt vn n)) sc w
        (hidx n (by omega)) hw hsc,
      ← ih (fun u hu => hidx u (by omega)),
      ← contribW_eq_contrib]
    unfold termsSum
    rw [Finset.sum_range_succ]

/-! ## 9. `ring::mul_short_desc`

The five loops composed. The statement is `Ring.mul_spec`'s -- coefficientwise
`negConv` -- which is the point: the implementation is signed shifts and the
specification did not move with it. -/

/-- **`mul_short_desc` computes the negacyclic product.**

`hden` is the description's side of the contract: the three parallel vectors
denote `a`. It is `classify_short`'s obligation to supply it, and nothing here
depends on the `ℓ₁` budget -- the identity holds for any `a`, so a description
that is not short would only be slow, never wrong. -/
theorem mul_short_desc_spec (desc : ring.ShortMul) (s a : ring.Rq)
    (hs : Wf s) (ha : Wf a)
    (hmlen : desc.idx.val.length ≤ desc.mag.val.length)
    (hnlen : desc.idx.val.length ≤ desc.neg.val.length)
    (hidx : ∀ u, u < desc.idx.val.length → idxAt desc.idx u < N)
    (hden : ∀ j, j < N →
      coeffK a j = descCoeffW desc.idx desc.mag desc.neg desc.idx.val.length j) :
    ring.mul_short_desc desc s
      ⦃ z => Wf z ∧ ∀ w, w < N → coeffK z w = negConv a s w ⦄ := by
  -- the denotation extends past `N`, where both sides are zero
  have hdenall : ∀ j,
      coeffK a j = descCoeffW desc.idx desc.mag desc.neg desc.idx.val.length j := by
    intro j
    by_cases hj : j < N
    · exact hden j hj
    · rw [coeffK_of_ge (by rw [ha.1]; omega)]
      unfold descCoeffW
      refine (Finset.sum_eq_zero (fun u hu => ?_)).symm
      unfold single
      rw [if_neg (by
        have := hidx u (by simpa using hu)
        omega)]
  have hscz : ∀ i, N ≤ i → coeffK s i = 0 :=
    fun i hi => coeffK_of_ge (by rw [hs.1]; exact hi)
  rw [ring.mul_short_desc]
  simp only [alloc.vec.Vec.with_capacity]
  step with zerofill_spec params.RING_DEGREE (alloc.vec.Vec.new Std.U64) 0#usize
    params_RING_DEGREE_val (by simp) (by simp) (by intro u hu; simp at hu)
    as ⟨o1, ho1len, ho1zero⟩
  have hco1 : AuxCode.Canon q o1 := by
    refine ⟨ho1len, ?_⟩
    intro u hu
    obtain ⟨t, ht, hteq⟩ := List.getElem_of_mem hu
    have : AuxCode.wordAt o1 t = 0 := ho1zero t (by rw [← ho1len]; exact ht)
    rw [AuxCode.wordAt_of_lt ht] at this
    rw [← hteq, this]
    norm_num [HachiEquiv.Field.q]
  step with terms_spec desc.idx desc.mag desc.neg s params.RING_DEGREE params.Q
    (alloc.vec.Vec.len desc.idx) o1 0#usize (fun _ => 0)
    hs params_RING_DEGREE_val params_Q_val rfl hmlen hnlen hidx (by simp) hco1
    (by
      intro w hwlt
      rw [ho1zero w hwlt]
      unfold termsSum
      simp) as ⟨o2, hco2, ho2val⟩
  step with convert_spec params.RING_DEGREE o2 (alloc.vec.Vec.new cpoly.field.Fp)
    0#usize params_RING_DEGREE_val (by simp) hco2.1 (by simp)
    (by intro u hu; simp at hu) (by intro t ht; simp at ht) as ⟨res, hreswf, hresval⟩
  refine ⟨hreswf, ?_⟩
  intro w hwlt
  rw [show (alloc.vec.Vec.len desc.idx).val = desc.idx.val.length from by simp] at ho2val
  rw [hresval w hwlt, ho2val w hwlt, zero_add,
    termsSum_eq_negConvF (coeffK s) desc.idx desc.mag desc.neg
      desc.idx.val.length w hidx hwlt hscz,
    ← negConvF_coeffK a s w]
  exact congrArg (fun f => negConvF f (coeffK s) w) (funext hdenall).symm

/-! ## 10. `ring::classify_short`

The classification walks the coefficients once and pushes a term for each
nonzero one, declining as soon as the running centred `ℓ₁` total passes the
budget. Its obligation is exactly `mul_short_desc_spec`'s `hden`: the three
vectors it builds denote `a`.

The invariant is one equation --
`descCoeffW … j = if j < k then coeffK a j else 0` -- which carries both halves
at once: the positions already walked are described, and the positions not yet
reached contribute nothing. -/

/-- `Vec.push` is monadic here, so these are stated over the append equation
`step` hands back rather than over a `push` term. -/
theorem idxAt_append_lt {v v' : alloc.vec.Vec Std.Usize} {x : Std.Usize} {u : ℕ}
    (hv : v'.val = v.val ++ [x]) (hu : u < v.val.length) : idxAt v' u = idxAt v u := by
  unfold idxAt; rw [hv, getD_append_lt' _ _ _ hu]

theorem idxAt_append_eq {v v' : alloc.vec.Vec Std.Usize} {x : Std.Usize}
    (hv : v'.val = v.val ++ [x]) : idxAt v' v.val.length = x.val := by
  unfold idxAt; rw [hv, getD_append_eq']

theorem magAt_append_lt {v v' : alloc.vec.Vec Std.U64} {x : Std.U64} {u : ℕ}
    (hv : v'.val = v.val ++ [x]) (hu : u < v.val.length) : magAt v' u = magAt v u := by
  unfold magAt; rw [hv, getD_append_lt' _ _ _ hu]

theorem magAt_append_eq {v v' : alloc.vec.Vec Std.U64} {x : Std.U64}
    (hv : v'.val = v.val ++ [x]) : magAt v' v.val.length = x.val := by
  unfold magAt; rw [hv, getD_append_eq']

theorem negAt_append_lt {v v' : alloc.vec.Vec Bool} {x : Bool} {u : ℕ}
    (hv : v'.val = v.val ++ [x]) (hu : u < v.val.length) : negAt v' u = negAt v u := by
  unfold negAt; rw [hv, getD_append_lt' _ _ _ hu]

theorem negAt_append_eq {v v' : alloc.vec.Vec Bool} {x : Bool}
    (hv : v'.val = v.val ++ [x]) : negAt v' v.val.length = x := by
  unfold negAt; rw [hv, getD_append_eq']

/-- Pushing one term onto all three vectors adds exactly that monomial. -/
theorem descCoeffW_append {vi vi' : alloc.vec.Vec Std.Usize}
    {vm vm' : alloc.vec.Vec Std.U64} {vn vn' : alloc.vec.Vec Bool}
    {kx : Std.Usize} {mx : Std.U64} {nx : Bool} {t : ℕ}
    (hi : vi'.val = vi.val ++ [kx]) (hm : vm'.val = vm.val ++ [mx])
    (hnn : vn'.val = vn.val ++ [nx])
    (hti : t = vi.val.length) (htm : t = vm.val.length) (htn : t = vn.val.length)
    (j : ℕ) :
    descCoeffW vi' vm' vn' (t + 1) j
      = descCoeffW vi vm vn t j + single kx.val (termValW mx.val nx) j := by
  unfold descCoeffW
  rw [Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl (fun u hu => ?_)
    simp only [Finset.mem_range] at hu
    rw [idxAt_append_lt hi (by omega), magAt_append_lt hm (by omega),
      negAt_append_lt hnn (by omega)]
  · rw [hti, idxAt_append_eq hi, ← hti, htm, magAt_append_eq hm, ← htm, htn,
      negAt_append_eq hnn]

/-- **The centred representative.** The Rust stores `(magnitude, sign)` rather
than the word: `c` when `c ≤ q/2`, else `q - c` flagged negative. Either way the
term denotes `c` in `ZMod q`, because `q ≡ 0`. -/
theorem termValW_of_word (cv mv : ℕ) (negt : Bool) (hc : cv < q)
    (hm : mv = if cv ≤ q / 2 then cv else q - cv)
    (hneg : negt = decide (q / 2 < cv)) :
    termValW mv negt = (cv : ZMod q) := by
  unfold termValW
  by_cases h : cv ≤ q / 2
  · rw [hm, if_pos h, hneg, decide_eq_false (by omega), if_neg (by simp)]
  · rw [hm, if_neg h, hneg, decide_eq_true (by omega), if_pos rfl,
      Nat.cast_sub (by omega)]
    push_cast
    ring_nf

/-- **The invariant after describing one coefficient.** Shared by the
classification loop's push leaves, which differ only in how the magnitude was
computed. -/
theorem classify_push_invariant (a : ring.Rq) {di di' : alloc.vec.Vec Std.Usize}
    {dm dm' : alloc.vec.Vec Std.U64} {dn dn' : alloc.vec.Vec Bool}
    {dk : Std.Usize} {mx : Std.U64} {nx : Bool} {cv : ℕ}
    (hi : di'.val = di.val ++ [dk]) (hm : dm'.val = dm.val ++ [mx])
    (hnn : dn'.val = dn.val ++ [nx])
    (h2 : di.val.length = dm.val.length) (h3 : di.val.length = dn.val.length)
    (h4 : ∀ u, u < di.val.length → idxAt di u < N)
    (h5 : ∀ j, descCoeffW di dm dn di.val.length j
            = if j < dk.val then coeffK a j else 0)
    (hdklt : dk.val < N)
    (hcval : ((cv : ℕ) : ZMod q) = coeffK a dk.val)
    (hterm : termValW mx.val nx = ((cv : ℕ) : ZMod q)) :
    di'.val.length = dm'.val.length ∧ di'.val.length = dn'.val.length
    ∧ (∀ u, u < di'.val.length → idxAt di' u < N)
    ∧ ∀ j, descCoeffW di' dm' dn' di'.val.length j
        = if j < dk.val + 1 then coeffK a j else 0 := by
  have hlen : di'.val.length = di.val.length + 1 := by rw [hi]; simp
  refine ⟨by rw [hlen, hm]; simp [h2], by rw [hlen, hnn]; simp [h3], ?_, ?_⟩
  · intro u hu
    rw [hlen] at hu
    rcases Nat.lt_or_ge u di.val.length with hult | huge
    · rw [idxAt_append_lt hi hult]; exact h4 u hult
    · have hueq : u = di.val.length := by omega
      rw [hueq, idxAt_append_eq hi]; exact hdklt
  · intro j
    rw [hlen, descCoeffW_append hi hm hnn rfl h2 h3 j, h5 j]
    unfold single
    by_cases hj : j < dk.val
    · rw [if_pos hj, if_neg (show ¬(j = dk.val) by omega),
        if_pos (show j < dk.val + 1 by omega), add_zero]
    · by_cases hje : j = dk.val
      · rw [if_neg hj, if_pos hje, if_pos (show j < dk.val + 1 by omega),
          zero_add, hterm, hcval, hje]
      · rw [if_neg hj, if_neg hje,
          if_neg (show ¬(j < dk.val + 1) by omega), add_zero]

/-- **The classification loop.** `none` carries no obligation; `some desc` says
the three vectors denote `a`.

Two invariant components exist only for *totality*, not correctness: the running
total is bounded by the budget (so `total + m` fits a `u64`), and the described
count is bounded by the position reached (so `Vec.push_spec`'s
`length < Usize.max` is dischargeable). -/
theorem classify_short_loop_spec (a : ring.Rq) (nU : Std.Usize)
    (qU halfU budgetU : Std.U64)
    (vi : alloc.vec.Vec Std.Usize) (vm : alloc.vec.Vec Std.U64)
    (vn : alloc.vec.Vec Bool) (totalU : Std.U64) (kU : Std.Usize)
    (ha : Wf a) (hn : nU.val = N) (hq : qU.val = q) (hhalf : halfU.val = q / 2)
    (htot : totalU.val ≤ budgetU.val) (hbud : budgetU.val < 2 ^ 32)
    (hk : kU.val ≤ nU.val) (hcnt : vi.val.length ≤ kU.val)
    (him : vi.val.length = vm.val.length) (hin : vi.val.length = vn.val.length)
    (hidx : ∀ u, u < vi.val.length → idxAt vi u < N)
    (hden : ∀ j, descCoeffW vi vm vn vi.val.length j
              = if j < kU.val then coeffK a j else 0) :
    ring.classify_short_loop a nU qU halfU budgetU vi vm vn totalU kU
      ⦃ r => ∀ desc, r = some desc →
          desc.idx.val.length = desc.mag.val.length
          ∧ desc.idx.val.length = desc.neg.val.length
          ∧ (∀ u, u < desc.idx.val.length → idxAt desc.idx u < N)
          ∧ ∀ j, descCoeffW desc.idx desc.mag desc.neg desc.idx.val.length j
              = if j < N then coeffK a j else 0 ⦄ := by
  rw [ring.classify_short_loop]
  apply loop.spec_decr_nat (fun t => nU.val - t.2.2.2.2.val)
    (fun t => t.2.2.2.2.val ≤ nU.val ∧ t.2.2.2.1.val ≤ budgetU.val
      ∧ t.1.val.length ≤ t.2.2.2.2.val
      ∧ t.1.val.length = t.2.1.val.length
      ∧ t.1.val.length = t.2.2.1.val.length
      ∧ (∀ u, u < t.1.val.length → idxAt t.1 u < N)
      ∧ ∀ j, descCoeffW t.1 t.2.1 t.2.2.1 t.1.val.length j
              = if j < t.2.2.2.2.val then coeffK a j else 0)
  · rintro ⟨di, dm, dn, dt, dk⟩ ⟨h1, h1b, h1c, h2, h3, h4, h5⟩
    dsimp only at h1 h1b h1c h2 h3 h4 h5
    simp only [ring.classify_short_loop.body]
    by_cases hlt : dk < nU
    · rw [if_pos hlt]
      have hdkn : dk.val < nU.val := (Std.UScalar.lt_equiv dk nU).mp hlt
      have hdklt : dk.val < N := by rw [← hn]; exact hdkn
      step with coeff_spec a dk ha as ⟨f, hfred, hfval⟩
      step with to_u64_id f as ⟨c, hcf⟩
      have hclt : c.val < q := by rw [hcf]; exact hfred
      have hcval : ((c.val : ℕ) : ZMod q) = coeffK a dk.val := by
        rw [hcf]; exact hfval
      by_cases hc0 : c = 0#u64
      · rw [if_neg (by simp [hc0])]
        step as ⟨dk1, hdk1⟩
        refine ⟨by rw [hdk1, hn]; omega, h1b, by rw [hdk1]; omega, h2, h3, h4, ?_,
          by rw [hdk1]; omega⟩
        intro j
        rw [h5 j, hdk1]
        by_cases hj : j < dk.val
        · rw [if_pos hj, if_pos (show j < dk.val + 1 by omega)]
        · by_cases hje : j = dk.val
          · rw [if_neg hj, if_pos (show j < dk.val + 1 by omega), hje, ← hcval,
              hc0]
            simp
          · rw [if_neg hj, if_neg (show ¬(j < dk.val + 1) by omega)]
      · rw [if_pos (by simp [hc0])]
        have hsign : (decide (c > halfU)) = decide (q / 2 < c.val) := by
          simp only [decide_eq_decide]
          rw [← hhalf]
          exact ⟨fun h => by scalar_tac, fun h => by scalar_tac⟩
        by_cases hch : c.val ≤ halfU.val
        · -- `c` is already its own centred magnitude
          rw [if_pos (show c ≤ halfU by scalar_tac)]
          step as ⟨t1, ht1⟩
          have hmv : c.val = (if c.val ≤ q / 2 then c.val else q - c.val) := by
            rw [if_pos (by rw [← hhalf]; exact hch)]
          by_cases hbg : budgetU.val < t1.val
          · rw [if_pos ((Std.UScalar.lt_equiv budgetU t1).mpr hbg), WP.spec_ok]
            dsimp only
            intro desc hdesc
            simp at hdesc
          · rw [if_neg (fun hcon =>
              hbg ((Std.UScalar.lt_equiv budgetU t1).mp hcon))]
            step as ⟨di1, hdi1⟩
            step as ⟨dm1, hdm1⟩
            step as ⟨dn1, hdn1⟩
            step as ⟨dk1, hdk1⟩
            obtain ⟨p2, p3, p4, p5⟩ := classify_push_invariant a hdi1 hdm1 hdn1
              h2 h3 h4 h5 hdklt hcval
              (termValW_of_word c.val c.val _ hclt hmv hsign)
            have hb3 : di1.val.length ≤ dk1.val := by
              rw [hdi1, List.length_append, hdk1]
              simp only [List.length_singleton]
              omega
            refine ⟨by rw [hdk1, hn]; omega, by omega, hb3, p2, p3, p4, ?_,
              by rw [hdk1]; omega⟩
            intro j; rw [hdk1]; exact p5 j
        · -- the centred magnitude is `q - c`, flagged negative
          rw [if_neg (show ¬ (c ≤ halfU) by scalar_tac)]
          step as ⟨m, hm⟩
          step as ⟨t1, ht1⟩
          have hmv : m.val = (if c.val ≤ q / 2 then c.val else q - c.val) := by
            rw [if_neg (by rw [← hhalf]; exact hch)]
            scalar_tac
          by_cases hbg : budgetU.val < t1.val
          · rw [if_pos ((Std.UScalar.lt_equiv budgetU t1).mpr hbg), WP.spec_ok]
            dsimp only
            intro desc hdesc
            simp at hdesc
          · rw [if_neg (fun hcon =>
              hbg ((Std.UScalar.lt_equiv budgetU t1).mp hcon))]
            step as ⟨di1, hdi1⟩
            step as ⟨dm1, hdm1⟩
            step as ⟨dn1, hdn1⟩
            step as ⟨dk1, hdk1⟩
            obtain ⟨p2, p3, p4, p5⟩ := classify_push_invariant a hdi1 hdm1 hdn1
              h2 h3 h4 h5 hdklt hcval
              (termValW_of_word c.val m.val _ hclt hmv hsign)
            have hb3 : di1.val.length ≤ dk1.val := by
              rw [hdi1, List.length_append, hdk1]
              simp only [List.length_singleton]
              omega
            refine ⟨by rw [hdk1, hn]; omega, by omega, hb3, p2, p3, p4, ?_,
              by rw [hdk1]; omega⟩
            intro j; rw [hdk1]; exact p5 j
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      intro desc hdesc
      have heq : dk.val = nU.val := by scalar_tac
      injection hdesc with hd
      subst hd
      dsimp only
      refine ⟨h2, h3, h4, ?_⟩
      intro j
      rw [h5 j, heq, hn]
  · exact ⟨hk, htot, hcnt, him, hin, hidx, hden⟩

/-- **`ring::classify_short`.** Either it declines, or the description it returns
denotes `a` -- which is exactly `mul_short_desc_spec`'s `hden`.

Note what is *not* here: any claim about the `ℓ₁` budget. Declining is a
performance decision, and the caller's `None` branch is the already-proved
generic product, so the budget cannot affect what `honest_z` computes. -/
theorem classify_short_spec (a : ring.Rq) (ha : Wf a) :
    ring.classify_short a
      ⦃ r => ∀ desc, r = some desc →
          desc.idx.val.length ≤ desc.mag.val.length
          ∧ desc.idx.val.length ≤ desc.neg.val.length
          ∧ (∀ u, u < desc.idx.val.length → idxAt desc.idx u < N)
          ∧ ∀ j, j < N →
              coeffK a j
                = descCoeffW desc.idx desc.mag desc.neg desc.idx.val.length j ⦄ := by
  rw [ring.classify_short]
  step as ⟨half, hhalf⟩
  have hhv : half.val = q / 2 := by rw [hhalf, params_Q_val]
  apply spec_mono (classify_short_loop_spec a params.RING_DEGREE params.Q half
    params.OMEGA (alloc.vec.Vec.new Std.Usize) (alloc.vec.Vec.new Std.U64)
    (alloc.vec.Vec.new Bool) 0#u64 0#usize
    ha params_RING_DEGREE_val params_Q_val hhv (by simp [params.OMEGA])
    (by simp [params.OMEGA]) (by simp [params_RING_DEGREE_val]) (by simp)
    (by simp) (by simp) (by intro u hu; simp at hu)
    (by intro j; simp [descCoeffW]))
  intro r hr desc hdesc
  obtain ⟨e2, e3, e4, e5⟩ := hr desc hdesc
  refine ⟨by omega, by omega, e4, ?_⟩
  intro j hj
  rw [e5 j, if_pos hj]

end HachiEquiv.AuxShort
