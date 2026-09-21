/-
`OptFold.lean` -- the generic fold lemmas the optimized variants share.

List-level facts about `List.foldl` with a push or an addition as the step,
stated for an arbitrary type or additive monoid. They were candidate C's § 0 when
`Opt.lean` was one file; candidate E (`OptRingSwitch.lean`) and candidate I
(`OptSumcheck.lean`) use them too, so they live below every part.
-/
import ZeroCheck

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly CompPoly.Extension CompPoly.Extension.Ext ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.Opt

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme
open HachiEquiv.RingSwitch HachiEquiv.Ext HachiEquiv.ZeroCheck

/-! ## 0. The push-fold shape

Every table below is one `List.foldl` over `List.range k` that appends a single
element per step -- the Lean image of `let mut out = Vec::with_capacity(k); let
mut j = 0; while j < k { out.push(…); j += 1 }`. These two lemmas are the whole
reasoning interface: length and entrywise value. -/

/-- A push-fold over `List.range k` is `List.map` over it. -/
theorem foldl_push_eq_map {β : Type*} (f : ℕ → β) (k : ℕ) :
    (List.range k).foldl (fun acc j => acc ++ [f j]) ([] : List β) = (List.range k).map f := by
  induction k with
  | zero => simp
  | succ t ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp

/-- The length of a push-fold table. -/
theorem foldl_push_length {β : Type*} (f : ℕ → β) (k : ℕ) :
    ((List.range k).foldl (fun acc j => acc ++ [f j]) ([] : List β)).length = k := by
  rw [foldl_push_eq_map]; simp

/-- Entry `j` of a push-fold table, for `j` in range. -/
theorem foldl_push_getD {β : Type*} (f : ℕ → β) (k : ℕ) (d : β) {j : ℕ} (hj : j < k) :
    ((List.range k).foldl (fun acc t => acc ++ [f t]) ([] : List β)).getD j d = f j := by
  rw [foldl_push_eq_map, List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

/-- Out-of-range reads are the default -- this is what lets the `u ≥ μ + n·δ`
columns of `mAlphaTable` be *absent* rather than stored as zeros. -/
theorem getD_of_length_le {β : Type*} (l : List β) (d : β) {j : ℕ} (h : l.length ≤ j) :
    l.getD j d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

/-- A `List.range` fold that accumulates a sum is `Finset.sum` -- the invariant
of every `acc = acc + …` counter loop in `hachi/src`. -/
theorem foldl_add_range_eq_sum (g : ℕ → F) (k : ℕ) :
    (List.range k).foldl (fun s i => s + g i) (0 : F) = ∑ i ∈ Finset.range k, g i := by
  have key : ∀ (t : ℕ) (a : F),
      (List.range t).foldl (fun s i => s + g i) a = a + ∑ i ∈ Finset.range t, g i := by
    intro t
    induction t with
    | zero => intro a; simp
    | succ t ih =>
        intro a
        rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
        simp [add_assoc]
  rw [key, zero_add]


end HachiEquiv.Opt
