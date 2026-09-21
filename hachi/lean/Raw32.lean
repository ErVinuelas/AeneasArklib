/-
The **compact raw-message carrier**: the message held as `u32` words.

`hachi/src/ring.rs` § "The compact raw carrier" is the design; this file is its
equivalence. Every coefficient of a well-formed `Rq` is a canonical residue
below `q = 2^32 - 99`, so a `u32` holds it exactly, and the raw message -- the
one input the prover keeps resident for the whole protocol, 8 GiB at the
paper's parameters -- halves.

## What is proved here, and why in this shape

Nothing computes in the compact representation: `RawRq32::expand` is the only
way out of it, and each `_32` consumer expands one block per iteration and
drops it. That is a *representation* change with no arithmetic in it, and the
proofs are shaped to say exactly that:

* `rawrq32_round_trip` and `rawvec32_round_trip` are the losslessness claims --
  `expand ∘ compact = id`, as an equality of extracted values rather than of
  denotations. The narrowing in `compact` is fallible in the model
  (`lift (UScalar.cast .U32 …)`), and its side condition is exactly
  `Field.Red`, which every `Wf` operand already carries: no new precondition,
  which is the whole reason the carrier is admissible.
* each `_32` consumer is proved **equal to its `_64` original** on the message
  it denotes (`ExpandsTo`), and its specification is then the original's,
  inherited rather than re-derived. This is not a weaker claim than re-proving
  each one: composed with the `_64` spec it gives the same conclusion in the
  same vocabulary, and it is the honest one, because "the compact carrier
  changes nothing" is the theorem the change actually asserts.

The two tools that make the second point cheap are `eq_ok_of_spec` -- a
deterministic postcondition *is* an equation, since `theta` sends `fail` and
`div` to `False` -- and `loop_congr`, which is just `congrArg`: `loop` is an
ordinary function of its body, so bodies equal pointwise give equal loops. The
`_32` and `_64` loop bodies differ by one inserted `expand`, and the inner
loops are byte-identical, so the pointwise equality is the only content.
-/
import Scheme

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.Raw32

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme

/-! ## Three tools

General, and none of them about this carrier; they are here because this is the
first change whose content is an *equality between two extracted functions*
rather than a denotation. -/

/-- A deterministic specification is an equation. `theta` sends `fail` and `div`
to `False`, so a postcondition that pins the result to one value also rules out
both -- which is what lets the rest of this file rewrite with extracted
functions instead of stepping through them. -/
theorem eq_ok_of_spec {α : Type} {m : Result α} {a : α} (h : m ⦃ fun z => z = a ⦄) :
    m = ok a := by
  revert h
  unfold WP.spec WP.theta WP.wp_return
  cases m <;> grind

/-- `loop` is an ordinary function of its body, so equal bodies give equal
loops. The `@[rust_loop]` defs are all `loop (fun st => body …) init`, so this
is how a body-level equality reaches the whole loop. -/
theorem loop_congr {α β : Type} {f g : α → Result (ControlFlow α β)} {x : α}
    (h : ∀ a, f a = g a) : loop f x = loop g x := by
  rw [funext h]

/-- An in-range index, as an equation. -/
theorem index_eq {α : Type} (v : alloc.vec.Vec α) (i : Std.Usize) (d : α)
    (h : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i
      = ok (v.val.getD i.val d) := by
  apply eq_ok_of_spec
  step as ⟨z, hz⟩
  rw [hz, List.getD_eq_getElem _ _ h]

/-- Reading a `push` below the old length, and at it. `NttProduct.lean` has the
same two facts privately; restated here rather than exported, as that file's
own header says. -/
theorem getD_push_lt {α : Type} (l : List α) (x d : α) {j : ℕ} (hj : j < l.length) :
    (l ++ [x]).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hj,
    List.getElem_append_left hj]

theorem getD_push_eq {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
  simp

/-- Two containers of the same length have the same `len`. -/
theorem len_congr {α β : Type} (u : alloc.vec.Vec α) (v : alloc.vec.Vec β)
    (h : u.val.length = v.val.length) :
    alloc.vec.Vec.len u = alloc.vec.Vec.len v :=
  UScalar.eq_of_val_eq (by simpa using h)

/-! ## The field boundary, at the representation

`Field.lean`'s `fp_new_spec` says what `Fp::new` means in `ZMod q`; the round
trip needs what it does to the *word*, and that it is the identity on a word
already reduced. -/

/-- `Fp::new` reduces the word. -/
theorem fp_new_rep (v : Std.U64) : cpoly.field.Fp.new v ⦃ c => c.val = v.val % q ⦄ := by
  rw [cpoly.field.Fp.new]
  step as ⟨c, hc⟩
  rw [hc, cpoly_P_val]

/-- `Fp::new` is the identity on a reduced word -- the step that makes the
carrier lossless rather than merely coefficientwise-correct. -/
theorem fp_new_id (v : Std.U64) (h : v.val < q) : cpoly.field.Fp.new v = ok v := by
  apply eq_ok_of_spec
  apply spec_mono (fp_new_rep v)
  intro c hc
  exact UScalar.eq_of_val_eq (by rw [hc, Nat.mod_eq_of_lt h])

/-- `Rq::coeff` in range, as an equation. -/
theorem coeff_rep (a : ring.Rq) (k : Std.Usize) (ha : Wf a) (hk : k.val < N) :
    ring.Rq.coeff a k = ok (a.val.getD k.val cpoly.field.Fp.ZERO) := by
  have hkb : k.val < a.val.length := by rw [ha.1]; exact hk
  have hlt : k < alloc.vec.Vec.len a := by scalar_tac
  rw [ring.Rq.coeff, if_pos hlt, index_eq a k cpoly.field.Fp.ZERO hkb]

/-- and as a specification, so `step` can use it. -/
theorem coeff_word_spec (a : ring.Rq) (k : Std.Usize) (ha : Wf a) (hk : k.val < N) :
    ring.Rq.coeff a k ⦃ f => f = a.val.getD k.val cpoly.field.Fp.ZERO ⦄ := by
  rw [coeff_rep a k ha hk, WP.spec_ok]

/-! ## `from_coeffs` at the representation

`Ring.lean`'s `from_coeffs_spec` is a statement about `coeffK`, which is all the
arithmetic ever needs. The round trip needs more: that on an input already of
length `N` the function is the *identity*, because the loop pushes the input's
entries verbatim. -/

theorem from_coeffs_loop_rep (coeffs : alloc.vec.Vec cpoly.field.Fp)
    (n m : Std.Usize) (out : alloc.vec.Vec cpoly.field.Fp) (i : Std.Usize)
    (hn : n.val = coeffs.val.length) (hm : m.val = coeffs.val.length)
    (hi : i.val ≤ coeffs.val.length)
    (hout : out.val = coeffs.val.take i.val) :
    ring.Rq.from_coeffs_loop coeffs n m out i ⦃ z => z.val = coeffs.val ⦄ := by
  rw [ring.Rq.from_coeffs_loop]
  apply loop.spec_decr_nat (fun s => coeffs.val.length - s.2.val)
    (fun s => s.2.val ≤ coeffs.val.length ∧ s.1.val = coeffs.val.take s.2.val)
  · rintro ⟨o1, i1⟩ ⟨hi1, ho1⟩
    dsimp only at hi1 ho1
    simp only [ring.Rq.from_coeffs_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hib : i1.val < coeffs.val.length := by rw [← hn]; scalar_tac
      have hlt2 : i1 < m := by scalar_tac
      rw [if_pos hlt2, index_eq coeffs i1 cpoly.field.Fp.ZERO hib]
      simp only [bind_tc_ok]
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [ho2, ho1, hi2, List.getD_eq_getElem _ _ hib]
        exact List.take_concat_get' _ _ hib
      · omega
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = coeffs.val.length := by scalar_tac
      rw [ho1, heq, List.take_length]
  · exact ⟨hi, hout⟩

/-- `Rq::from_coeffs` is the identity on an input of the ring's own length. -/
theorem from_coeffs_id (coeffs : alloc.vec.Vec cpoly.field.Fp)
    (hlen : coeffs.val.length = N) :
    ring.Rq.from_coeffs coeffs = ok coeffs := by
  apply eq_ok_of_spec
  rw [ring.Rq.from_coeffs]
  simp only [bind_ok_id]
  apply spec_mono (from_coeffs_loop_rep coeffs params.RING_DEGREE
    (alloc.vec.Vec.len coeffs) (alloc.vec.Vec.new cpoly.field.Fp) 0#usize
    (by rw [params_RING_DEGREE_val, hlen]) (by simp) (by simp) (by simp))
  intro z hz
  exact Subtype.ext hz

/-! ## The element round trip -/

/-- The `t`-th word of a compact element. -/
def word32 (v : alloc.vec.Vec Std.U32) (t : ℕ) : ℕ := (v.val.getD t 0#u32).val

theorem compact_loop_spec (a : ring.Rq) (n : Std.Usize)
    (words : alloc.vec.Vec Std.U32) (i : Std.Usize)
    (ha : Wf a) (hn : n.val = N) (hi : i.val ≤ N)
    (hlen : words.val.length = i.val)
    (hval : ∀ t, t < i.val → word32 words t = wordN a t) :
    ring.RawRq32.compact_loop a n words i
      ⦃ z => z.val.length = N ∧ ∀ t, t < N → word32 z t = wordN a t ⦄ := by
  rw [ring.RawRq32.compact_loop]
  apply loop.spec_decr_nat (fun s => N - s.2.val)
    (fun s => s.2.val ≤ N ∧ s.1.val.length = s.2.val ∧
      ∀ t, t < s.2.val → word32 s.1 t = wordN a t)
  · rintro ⟨w1, i1⟩ ⟨hi1, hl1, hv1⟩
    dsimp only at hi1 hl1 hv1
    simp only [ring.RawRq32.compact_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hib : i1.val < N := by rw [← hn]; scalar_tac
      have hia : i1.val < a.val.length := by rw [ha.1]; exact hib
      step with coeff_word_spec a i1 ha hib as ⟨f, hf⟩
      -- the coefficient is reduced, so it fits a `u32`: the side condition the
      -- whole representation rests on
      have hfq : f.val < q := by
        rw [hf, List.getD_eq_getElem _ _ hia]
        exact Red_getElem ha.2 hia
      step with to_u64_id f as ⟨w, hw⟩
      have hwq : w.val < q := by rw [hw]; exact hfq
      have hcast : lift (UScalar.cast .U32 w) ⦃ y => y.val = w.val ⦄ :=
        UScalar.cast_inBounds_spec .U32 w (by
          simp only [UScalar.max, UScalarTy.numBits]
          have : q = 4294967197 := rfl
          omega)
      step with hcast as ⟨u, hu⟩
      step as ⟨w2, hw2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · rw [hw2]; simp [hl1, hi2]
      · intro t ht
        rw [hi2] at ht
        unfold word32 wordN
        rw [hw2]
        by_cases hte : t < i1.val
        · rw [getD_push_lt _ _ _ (by rw [hl1]; exact hte)]
          have hprev := hv1 t hte
          unfold word32 wordN at hprev
          exact hprev
        · have htv : t = i1.val := by omega
          subst htv
          -- only the INDEX is `w1`'s length; rewriting `i1.val` everywhere would
          -- move it on the right-hand side too
          have hgd : (w1.val ++ [u]).getD i1.val 0#u32 = u := by
            rw [← hl1]; exact getD_push_eq _ _ _
          rw [hgd, hu, hw, hf]
      · omega
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = N := by scalar_tac
      rw [heq] at hl1 hv1
      exact ⟨hl1, hv1⟩
  · exact ⟨hi, hlen, hval⟩

theorem expand_loop_rep (v : alloc.vec.Vec Std.U32) (a : ring.Rq) (n : Std.Usize)
    (cs : alloc.vec.Vec cpoly.field.Fp) (i : Std.Usize)
    (hn : n.val = v.val.length) (hlenv : v.val.length = a.val.length)
    (hword : ∀ t, t < v.val.length → word32 v t = wordN a t)
    (hred : ∀ u ∈ a.val, Red u)
    (hi : i.val ≤ v.val.length) (hcs : cs.val = a.val.take i.val) :
    ring.RawRq32.expand_loop v n cs i ⦃ z => z.val = a.val ⦄ := by
  rw [ring.RawRq32.expand_loop]
  apply loop.spec_decr_nat (fun s => v.val.length - s.2.val)
    (fun s => s.2.val ≤ v.val.length ∧ s.1.val = a.val.take s.2.val)
  · rintro ⟨c1, i1⟩ ⟨hi1, hc1⟩
    dsimp only at hi1 hc1
    simp only [ring.RawRq32.expand_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hib : i1.val < v.val.length := by rw [← hn]; scalar_tac
      have hia : i1.val < a.val.length := by rw [← hlenv]; exact hib
      rw [index_eq v i1 0#u32 hib]
      simp only [bind_tc_ok]
      -- the widening is total; the word is the coefficient's, so `Fp::new`
      -- leaves it alone
      have hcast : lift (UScalar.cast .U64 (v.val.getD i1.val 0#u32))
          ⦃ y => y.val = (v.val.getD i1.val 0#u32).val ⦄ :=
        UScalar.cast_inBounds_spec .U64 _ (by scalar_tac)
      step with hcast as ⟨w, hw⟩
      have hwv : w.val = wordN a i1.val := by
        rw [hw]; exact hword i1.val hib
      have hwq : w.val < q := by
        rw [hwv]
        unfold wordN
        rw [List.getD_eq_getElem _ _ hia]
        exact hred _ (List.getElem_mem hia)
      have hcoef : a.val.getD i1.val cpoly.field.Fp.ZERO = w :=
        (UScalar.eq_of_val_eq (by rw [hwv]; unfold wordN; rfl)).symm
      rw [fp_new_id w hwq]
      simp only [bind_tc_ok]
      step as ⟨c2, hc2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [hc2, hc1, hi2, ← hcoef, List.getD_eq_getElem _ _ hia]
        exact List.take_concat_get' _ _ hia
      · omega
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = v.val.length := by scalar_tac
      rw [hc1, heq, hlenv, List.take_length]
  · exact ⟨hi, hcs⟩

/-- **The element round trip.** `RawRq32::compact` loses nothing: what it
produces expands back to exactly the ring element it read. -/
theorem rawrq32_round_trip (a : ring.Rq) (ha : Wf a) :
    ring.RawRq32.compact a ⦃ rv => ring.RawRq32.expand rv = ok a ⦄ := by
  rw [ring.RawRq32.compact]
  simp only [alloc.vec.Vec.with_capacity, bind_ok_id]
  apply spec_mono (compact_loop_spec a params.RING_DEGREE
    (alloc.vec.Vec.new Std.U32) 0#usize ha params_RING_DEGREE_val (by simp)
    (by simp) (by intro t ht; simp at ht))
  rintro rv ⟨hlen, hword⟩
  -- `expand` reads `rv.val.length = N = a.val.length` words back
  rw [ring.RawRq32.expand]
  simp only [alloc.vec.Vec.with_capacity]
  have hla : rv.val.length = a.val.length := by rw [hlen, ha.1]
  have hloop := expand_loop_rep rv a (alloc.vec.Vec.len rv)
    (alloc.vec.Vec.new cpoly.field.Fp) 0#usize (by simp) hla
    (by intro t ht; exact hword t (by rw [hlen] at ht; exact ht)) ha.2
    (by simp) (by simp)
  have hz := eq_ok_of_spec (spec_mono hloop (fun z hz => Subtype.ext hz))
  rw [hz]
  simp only [bind_tc_ok]
  exact from_coeffs_id a ha.1

/-! ## The block round trip -/

/-- `rv` expands to the vector `v`: same length, and each compact element
expands to the corresponding ring element. -/
def ExpandsBlocks (rv : linalg.RawVec32) (v : linalg.PolyVec) : Prop :=
  rv.val.length = v.val.length ∧
  ∀ t, t < rv.val.length →
    ring.RawRq32.expand (rv.val.getD t (alloc.vec.Vec.new Std.U32))
      = ok (v.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))

theorem rawvec32_compact_loop_spec (v : linalg.PolyVec) (n : Std.Usize)
    (out : alloc.vec.Vec ring.RawRq32) (i : Std.Usize)
    (hv : ∀ x ∈ v.val, Wf x) (hn : n.val = v.val.length) (hi : i.val ≤ v.val.length)
    (hlen : out.val.length = i.val)
    (hval : ∀ t, t < i.val →
      ring.RawRq32.expand (out.val.getD t (alloc.vec.Vec.new Std.U32))
        = ok (v.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))) :
    linalg.RawVec32.compact_loop v n out i
      ⦃ z => z.val.length = v.val.length ∧ ∀ t, t < v.val.length →
        ring.RawRq32.expand (z.val.getD t (alloc.vec.Vec.new Std.U32))
          = ok (v.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [linalg.RawVec32.compact_loop]
  apply loop.spec_decr_nat (fun s => v.val.length - s.2.val)
    (fun s => s.2.val ≤ v.val.length ∧ s.1.val.length = s.2.val ∧
      ∀ t, t < s.2.val →
        ring.RawRq32.expand (s.1.val.getD t (alloc.vec.Vec.new Std.U32))
          = ok (v.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hl1, hv1⟩
    dsimp only at hi1 hl1 hv1
    simp only [linalg.RawVec32.compact_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hib : i1.val < v.val.length := by rw [← hn]; scalar_tac
      rw [index_eq v i1 (alloc.vec.Vec.new cpoly.field.Fp) hib]
      simp only [bind_tc_ok]
      have hWi : Wf (v.val.getD i1.val (alloc.vec.Vec.new cpoly.field.Fp)) := by
        rw [List.getD_eq_getElem _ _ hib]
        exact hv _ (List.getElem_mem hib)
      step with rawrq32_round_trip _ hWi as ⟨rr, hrr⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · rw [ho2]; simp [hl1, hi2]
      · intro t ht
        rw [hi2] at ht
        rw [ho2]
        by_cases hte : t < i1.val
        · rw [getD_push_lt _ _ _ (by rw [hl1]; exact hte)]
          exact hv1 t hte
        · have htv : t = i1.val := by omega
          subst htv
          have hgd : (o1.val ++ [rr]).getD i1.val (alloc.vec.Vec.new Std.U32) = rr := by
            rw [← hl1]; exact getD_push_eq _ _ _
          rw [hgd]
          exact hrr
      · omega
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = v.val.length := by scalar_tac
      rw [heq] at hl1 hv1
      exact ⟨hl1, hv1⟩
  · exact ⟨hi, hlen, hval⟩

/-- **The block round trip.** -/
theorem rawvec32_round_trip (v : linalg.PolyVec) (hv : ∀ x ∈ v.val, Wf x) :
    linalg.RawVec32.compact v ⦃ rv => ExpandsBlocks rv v ⦄ := by
  rw [linalg.RawVec32.compact]
  simp only [alloc.vec.Vec.with_capacity, bind_ok_id]
  apply spec_mono (rawvec32_compact_loop_spec v (alloc.vec.Vec.len v)
    (alloc.vec.Vec.new ring.RawRq32) 0#usize hv (by simp) (by simp)
    (by simp) (by intro t ht; simp at ht))
  rintro rv ⟨hlen, hval⟩
  exact ⟨hlen, fun t ht => hval t (by rw [hlen] at ht; exact ht)⟩

/-- `RawVec32::expand` returns the vector its blocks expand to. -/
theorem rawvec32_expand_eq (rv : linalg.RawVec32) (v : linalg.PolyVec)
    (h : ExpandsBlocks rv v) : linalg.RawVec32.expand rv = ok v := by
  obtain ⟨hlen, hval⟩ := h
  apply eq_ok_of_spec
  rw [linalg.RawVec32.expand]
  simp only [alloc.vec.Vec.with_capacity, bind_ok_id]
  have hloop : linalg.RawVec32.expand_loop rv (alloc.vec.Vec.len rv)
      (alloc.vec.Vec.new ring.Rq) 0#usize ⦃ z => z.val = v.val ⦄ := by
    rw [linalg.RawVec32.expand_loop]
    apply loop.spec_decr_nat (fun s => rv.val.length - s.2.val)
      (fun s => s.2.val ≤ rv.val.length ∧ s.1.val = v.val.take s.2.val)
    · rintro ⟨o1, i1⟩ ⟨hi1, ho1⟩
      dsimp only at hi1 ho1
      simp only [linalg.RawVec32.expand_loop.body]
      by_cases hlt : i1 < alloc.vec.Vec.len rv
      · rw [if_pos hlt]
        have hib : i1.val < rv.val.length := by scalar_tac
        have hiv : i1.val < v.val.length := by rw [← hlen]; exact hib
        rw [index_eq rv i1 (alloc.vec.Vec.new Std.U32) hib]
        simp only [bind_tc_ok]
        rw [hval i1.val hib]
        simp only [bind_tc_ok]
        step as ⟨o2, ho2⟩
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, ?_⟩
        · rw [ho2, ho1, hi2, List.getD_eq_getElem _ _ hiv]
          exact List.take_concat_get' _ _ hiv
        · omega
      · rw [if_neg hlt, WP.spec_ok]
        dsimp only
        have heq : i1.val = rv.val.length := by scalar_tac
        rw [ho1, heq, hlen, List.take_length]
    · exact ⟨by simp, by simp⟩
  apply spec_mono hloop
  intro z hz
  exact Subtype.ext hz

/-! ## The message

`ExpandsTo raw32 raw` is the hypothesis every `_32` consumer's specification
carries: `raw` is the message `raw32`'s words denote. It is not an extra
assumption about the world -- `expand` is total, so such a `raw` always exists,
and `msg_compact_expands` produces it for a compacted message. -/

/-- The message `raw32` denotes. -/
def ExpandsTo (raw32 : alloc.vec.Vec linalg.RawVec32)
    (raw : alloc.vec.Vec linalg.PolyVec) : Prop :=
  raw32.val.length = raw.val.length ∧
  ∀ i, i < raw32.val.length →
    linalg.RawVec32.expand (raw32.val.getD i (alloc.vec.Vec.new ring.RawRq32))
      = ok (raw.val.getD i (alloc.vec.Vec.new ring.Rq))

theorem ExpandsTo.len_eq {raw32 : alloc.vec.Vec linalg.RawVec32}
    {raw : alloc.vec.Vec linalg.PolyVec} (h : ExpandsTo raw32 raw) :
    alloc.vec.Vec.len raw32 = alloc.vec.Vec.len raw :=
  len_congr _ _ h.1

/-! ## The consumers, equal to their originals

Each `_32` item is the `_64` item with one `expand` inserted, and the inner
loops are byte-identical. So each proof below is the same three moves: discharge
the two indexes, rewrite the `expand` with the `ExpandsTo` hypothesis, and let
the identical remainder close by reflexivity. No arithmetic appears, which is
the point -- the carrier change has none. -/

/-- `honest_z`'s two inner loops are the same function under either carrier:
their extracted bodies are byte-identical, the outer loop is where the message
is read. -/
theorem honest_z_inner0_eq (width : Std.Usize) (acc scaled : alloc.vec.Vec ring.Rq)
    (j : Std.Usize) :
    quadeval.honest_z_from_raw_32_loop1_loop0 width acc scaled j
      = quadeval.honest_z_from_raw_loop1_loop0 width acc scaled j := rfl

theorem honest_z_inner1_eq (width : Std.Usize) (acc s : alloc.vec.Vec ring.Rq)
    (desc : ring.ShortMul) (j : Std.Usize) :
    quadeval.honest_z_from_raw_32_loop1_loop1 width acc s desc j
      = quadeval.honest_z_from_raw_loop1_loop1 width acc s desc j := rfl

theorem honest_z_loop0_eq (width : Std.Usize) (acc : alloc.vec.Vec ring.Rq)
    (z : Std.Usize) :
    quadeval.honest_z_from_raw_32_loop0 width acc z
      = quadeval.honest_z_from_raw_loop0 width acc z := rfl

theorem resp_inner_loop_eq (inner_decomp inner : alloc.vec.Vec linalg.PolyVec)
    (i : Std.Usize) :
    quadeval.honest_compute_resp_from_raw_32_loop inner_decomp inner i
      = quadeval.honest_compute_resp_from_raw_loop inner_decomp inner i := rfl

/-- **`commit_streamed_32` is `commit_streamed` on the message it denotes.** -/
theorem commit_streamed_32_loop_eq {raw32 : alloc.vec.Vec linalg.RawVec32}
    {raw : alloc.vec.Vec linalg.PolyVec} (blocks : Std.Usize)
    (prep : linalg.PreparedMatrixG) (ts : alloc.vec.Vec linalg.PolyVec) (i : Std.Usize)
    (hex : ExpandsTo raw32 raw) (hb : blocks.val ≤ raw.val.length) :
    commit.commit_streamed_32_loop raw32 blocks prep ts i
      = commit.commit_streamed_loop raw blocks prep ts i := by
  rw [commit.commit_streamed_32_loop, commit.commit_streamed_loop]
  refine loop_congr (fun st => ?_)
  obtain ⟨t1, i1⟩ := st
  simp only [commit.commit_streamed_32_loop.body, commit.commit_streamed_loop.body]
  by_cases hlt : i1 < blocks
  · have hir : i1.val < raw.val.length := by scalar_tac
    have hib : i1.val < raw32.val.length := by rw [hex.1]; exact hir
    rw [if_pos hlt, if_pos hlt,
      index_eq raw32 i1 (alloc.vec.Vec.new ring.RawRq32) hib,
      index_eq raw i1 (alloc.vec.Vec.new ring.Rq) hir]
    simp only [bind_tc_ok]
    rw [hex.2 i1.val hib]
    simp only [bind_tc_ok]
  · rw [if_neg hlt, if_neg hlt]

theorem commit_streamed_32_eq {raw32 : alloc.vec.Vec linalg.RawVec32}
    {raw : alloc.vec.Vec linalg.PolyVec} (pp : commit.PublicParams)
    (hex : ExpandsTo raw32 raw) :
    commit.commit_streamed_32 pp raw32 = commit.commit_streamed pp raw := by
  have hL : ∀ prep : linalg.PreparedMatrixG,
      commit.commit_streamed_32_loop raw32 (alloc.vec.Vec.len raw) prep
          (alloc.vec.Vec.new linalg.PolyVec) 0#usize
        = commit.commit_streamed_loop raw (alloc.vec.Vec.len raw) prep
            (alloc.vec.Vec.new linalg.PolyVec) 0#usize :=
    fun prep => commit_streamed_32_loop_eq _ prep _ _ hex (by simp)
  rw [commit.commit_streamed_32, commit.commit_streamed, hex.len_eq]
  simp only [hL]

/-- **`carrier_from_raw_32` is `carrier_from_raw` on the message it denotes.** -/
theorem carrier_from_raw_32_loop_eq {raw32 : alloc.vec.Vec linalg.RawVec32}
    {raw : alloc.vec.Vec linalg.PolyVec} (blocks : Std.Usize)
    (prep : linalg.PreparedMatrix) (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hex : ExpandsTo raw32 raw) (hb : blocks.val ≤ raw.val.length) :
    quadeval.carrier_from_raw_32_loop raw32 blocks prep out i
      = quadeval.carrier_from_raw_loop raw blocks prep out i := by
  rw [quadeval.carrier_from_raw_32_loop, quadeval.carrier_from_raw_loop]
  refine loop_congr (fun st => ?_)
  obtain ⟨o1, i1⟩ := st
  simp only [quadeval.carrier_from_raw_32_loop.body, quadeval.carrier_from_raw_loop.body]
  by_cases hlt : i1 < blocks
  · have hir : i1.val < raw.val.length := by scalar_tac
    have hib : i1.val < raw32.val.length := by rw [hex.1]; exact hir
    rw [if_pos hlt, if_pos hlt,
      index_eq raw32 i1 (alloc.vec.Vec.new ring.RawRq32) hib,
      index_eq raw i1 (alloc.vec.Vec.new ring.Rq) hir]
    simp only [bind_tc_ok]
    rw [hex.2 i1.val hib]
    simp only [bind_tc_ok]
  · rw [if_neg hlt, if_neg hlt]

theorem carrier_from_raw_32_eq {raw32 : alloc.vec.Vec linalg.RawVec32}
    {raw : alloc.vec.Vec linalg.PolyVec} (a : linalg.PolyVec)
    (hex : ExpandsTo raw32 raw) :
    quadeval.carrier_from_raw_32 a raw32 = quadeval.carrier_from_raw a raw := by
  have hL : ∀ prep : linalg.PreparedMatrix,
      quadeval.carrier_from_raw_32_loop raw32 (alloc.vec.Vec.len raw) prep
          (alloc.vec.Vec.new ring.Rq) 0#usize
        = quadeval.carrier_from_raw_loop raw (alloc.vec.Vec.len raw) prep
            (alloc.vec.Vec.new ring.Rq) 0#usize :=
    fun prep => carrier_from_raw_32_loop_eq _ prep _ _ hex (by simp)
  rw [quadeval.carrier_from_raw_32, quadeval.carrier_from_raw, hex.len_eq]
  simp only [hL]

theorem carrier_decomp_from_raw_32_eq {raw32 : alloc.vec.Vec linalg.RawVec32}
    {raw : alloc.vec.Vec linalg.PolyVec} (a : linalg.PolyVec)
    (hex : ExpandsTo raw32 raw) :
    quadeval.carrier_decomp_from_raw_32 a raw32
      = quadeval.carrier_decomp_from_raw a raw := by
  rw [quadeval.carrier_decomp_from_raw_32, quadeval.carrier_decomp_from_raw,
    carrier_from_raw_32_eq a hex]

theorem carrier_commit_from_raw_32_eq {raw32 : alloc.vec.Vec linalg.RawVec32}
    {raw : alloc.vec.Vec linalg.PolyVec} (d_matrix : linalg.PolyMatrix)
    (a : linalg.PolyVec) (hex : ExpandsTo raw32 raw) :
    quadeval.carrier_commit_from_raw_32 d_matrix a raw32
      = quadeval.carrier_commit_from_raw d_matrix a raw := by
  rw [quadeval.carrier_commit_from_raw_32, quadeval.carrier_commit_from_raw,
    carrier_decomp_from_raw_32_eq a hex]

theorem honest_compute_v_from_raw_32_eq {raw32 : alloc.vec.Vec linalg.RawVec32}
    {raw : alloc.vec.Vec linalg.PolyVec} (pp : quadeval.PublicParamsD)
    (stmt : quadeval.QuadEvalStatement) (hex : ExpandsTo raw32 raw) :
    quadeval.honest_compute_v_from_raw_32 pp stmt raw32
      = quadeval.honest_compute_v_from_raw pp stmt raw := by
  have hL : ∀ (pm : linalg.PolyMatrix) (pv : linalg.PolyVec),
      quadeval.carrier_commit_from_raw_32 pm pv raw32
        = quadeval.carrier_commit_from_raw pm pv raw :=
    fun pm pv => carrier_commit_from_raw_32_eq pm pv hex
  rw [quadeval.honest_compute_v_from_raw_32, quadeval.honest_compute_v_from_raw]
  simp only [hL]

/-- **`honest_z_from_raw_32` is `honest_z_from_raw` on the message it denotes.** -/
theorem honest_z_from_raw_32_loop1_eq {raw32 : alloc.vec.Vec linalg.RawVec32}
    {raw : alloc.vec.Vec linalg.PolyVec} (c : linalg.PolyVec)
    (blocks width : Std.Usize) (acc : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hex : ExpandsTo raw32 raw) (hb : blocks.val ≤ raw.val.length) :
    quadeval.honest_z_from_raw_32_loop1 raw32 c blocks width acc i
      = quadeval.honest_z_from_raw_loop1 raw c blocks width acc i := by
  rw [quadeval.honest_z_from_raw_32_loop1, quadeval.honest_z_from_raw_loop1]
  refine loop_congr (fun st => ?_)
  obtain ⟨a1, i1⟩ := st
  simp only [quadeval.honest_z_from_raw_32_loop1.body,
    quadeval.honest_z_from_raw_loop1.body]
  by_cases hlt : i1 < blocks
  · have hir : i1.val < raw.val.length := by scalar_tac
    have hib : i1.val < raw32.val.length := by rw [hex.1]; exact hir
    rw [if_pos hlt, if_pos hlt,
      index_eq raw32 i1 (alloc.vec.Vec.new ring.RawRq32) hib,
      index_eq raw i1 (alloc.vec.Vec.new ring.Rq) hir]
    simp only [bind_tc_ok]
    rw [hex.2 i1.val hib]
    simp only [bind_tc_ok, honest_z_inner0_eq, honest_z_inner1_eq]
  · rw [if_neg hlt, if_neg hlt]

theorem honest_z_from_raw_32_eq {raw32 : alloc.vec.Vec linalg.RawVec32}
    {raw : alloc.vec.Vec linalg.PolyVec} (c : linalg.PolyVec)
    (hex : ExpandsTo raw32 raw) :
    quadeval.honest_z_from_raw_32 raw32 c = quadeval.honest_z_from_raw raw c := by
  have hL : ∀ (width : Std.Usize) (acc : alloc.vec.Vec ring.Rq),
      quadeval.honest_z_from_raw_32_loop1 raw32 c (alloc.vec.Vec.len raw) width acc 0#usize
        = quadeval.honest_z_from_raw_loop1 raw c (alloc.vec.Vec.len raw) width acc 0#usize :=
    fun width acc => honest_z_from_raw_32_loop1_eq c _ width acc _ hex (by simp)
  rw [quadeval.honest_z_from_raw_32, quadeval.honest_z_from_raw, hex.len_eq]
  simp only [honest_z_loop0_eq, hL]

-- `honest_compute_resp_from_raw_32_eq` lived here until candidate T28 changed
-- that item's signature: it now takes the carrier decomposition instead of
-- computing it, so it is no longer the `_64` item on a re-carriered message and
-- the equality no longer even typechecks. Its specification is proved directly
-- in `QuadEvalProtocol.lean`, from `honest_z_from_raw_32_eq` -- which is still
-- exactly this shape -- plus the supplied decomposition.
/-! ## The inherited specification

`commit_streamed_32`'s, composed from the equality above and the original. The
other six consumers' are in `QuadEvalProtocol.lean`, beside the specifications
they inherit. -/

/-- General form of `commit_streamed_32_spec` (arbitrary `ir mr or bl`); the pinned statement below is its instance at `1 1024 1 1024`.
**`commit_streamed_32` commits the message its words denote.** -/
theorem commit_streamed_32_specG (ir mr or bl : ℕ) (pp : commit.PublicParams)
    (raw32 : alloc.vec.Vec linalg.RawVec32) (m : alloc.vec.Vec linalg.PolyVec)
    (hex : ExpandsTo raw32 m) (hpp : WfParamsG ir mr or bl pp)
    (hm : m.val.length = bl ∧ ∀ x ∈ m.val, WfVec mr x)
    (hir : 0 < ir) (hmr8 : mr * 8 ≤ 8192) (hir8 : 8 * ir ≤ Usize.max) (hsz : bl * (ir * 8) ≤ Usize.max) :
    commit.commit_streamed_32 pp raw32
      ⦃ z => WfVec or z.1 ∧ z.2.val.length = bl
        ∧ (∀ y ∈ z.2.val, WfVec (ir * 8) y)
        ∧ (∀ j : Fin bl,
            toVec (k := ir * 8) (z.2.val.getD j.val (alloc.vec.Vec.new ring.Rq))
              = (InnerOuter.generateDecomps Φ
                  (InnerOuter.Decomposition.ofDigits Φ dd dd) (toParamsG ir mr or bl pp)
                  (fun i : Fin bl => toVec (k := mr)
                    (m.val.getD i.val (alloc.vec.Vec.new ring.Rq)))).innerDecomp j)
        ∧ toVec (k := or) z.1
            = InnerOuter.commitWithDecomps Φ (toParamsG ir mr or bl pp)
                (InnerOuter.generateDecomps Φ
                  (InnerOuter.Decomposition.ofDigits Φ dd dd) (toParamsG ir mr or bl pp)
                  (fun i : Fin bl => toVec (k := mr)
                    (m.val.getD i.val (alloc.vec.Vec.new ring.Rq)))) ⦄ := by
  rw [commit_streamed_32_eq pp hex]
  exact commit_streamed_specG ir mr or bl pp m hpp hm hir hmr8 hir8 hsz

/-- **`commit_streamed_32` commits the message its words denote.** -/
theorem commit_streamed_32_spec (pp : commit.PublicParams)
    (raw32 : alloc.vec.Vec linalg.RawVec32) (m : alloc.vec.Vec linalg.PolyVec)
    (hex : ExpandsTo raw32 m) (hpp : WfParams pp)
    (hm : m.val.length = 1024 ∧ ∀ x ∈ m.val, WfVec 1024 x) :
    commit.commit_streamed_32 pp raw32
      ⦃ z => WfVec 1 z.1 ∧ z.2.val.length = 1024
        ∧ (∀ y ∈ z.2.val, WfVec (1 * 8) y)
        ∧ (∀ j : Fin 1024,
            toVec (k := 1 * 8) (z.2.val.getD j.val (alloc.vec.Vec.new ring.Rq))
              = (InnerOuter.generateDecomps Φ
                  (InnerOuter.Decomposition.ofDigits Φ dd dd) (toParams pp)
                  (fun i : Fin 1024 => toVec (k := 1024)
                    (m.val.getD i.val (alloc.vec.Vec.new ring.Rq)))).innerDecomp j)
        ∧ toVec (k := 1) z.1
            = InnerOuter.commitWithDecomps Φ (toParams pp)
                (InnerOuter.generateDecomps Φ
                  (InnerOuter.Decomposition.ofDigits Φ dd dd) (toParams pp)
                  (fun i : Fin 1024 => toVec (k := 1024)
                    (m.val.getD i.val (alloc.vec.Vec.new ring.Rq)))) ⦄ := by
  exact commit_streamed_32_specG 1 1024 1 1024 pp raw32 m hex hpp hm (by norm_num) (by norm_num)
    (by have := usize_max_ge'; omega) (by have := usize_max_ge'; omega)

end HachiEquiv.Raw32
