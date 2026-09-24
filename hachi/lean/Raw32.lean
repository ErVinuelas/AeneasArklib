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
The exception is `commit_streamed_32` since Stage 6 card T51a: its loop no
longer expands a block at all -- it reads the gadget digits straight out of the
compact words -- so it is proved directly (§ "The raw-digit commit"), against a
ghost decomposition, and its headline statements did not move.
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

-- `honest_z_inner0_eq`, `honest_z_inner1_eq` and `honest_z_loop0_eq` lived here
-- until Stage 6 card T43 (2026-09-22) gave `honest_z_from_raw_32` a short branch
-- of its own -- the fused nibble scatter of `quadeval::z_row` -- so its loops
-- are no longer `honest_z_from_raw`'s and the equalities no longer typecheck.
-- Its specification is proved directly in `QuadEvalProtocol.lean` § "The fused
-- z pass", on `ZPacked.lean`.
theorem resp_inner_loop_eq (inner_decomp inner : alloc.vec.Vec linalg.PolyVec)
    (i : Std.Usize) :
    quadeval.honest_compute_resp_from_raw_32_loop inner_decomp inner i
      = quadeval.honest_compute_resp_from_raw_loop inner_decomp inner i := rfl

-- `commit_streamed_32_loop_eq` and `commit_streamed_32_eq` -- "`commit_streamed_32`
-- is `commit_streamed` on the message it denotes" -- lived here until Stage 6
-- card T51a (2026-09-24). Its loop no longer expands and decomposes a block: it
-- reads the digits straight out of the compact rows
-- (`PreparedMatrixG::apply_raw_digits_gold`), so the two loops are different
-- programs and the equalities are false as statements about them. Its
-- specification is proved directly below, § "The raw-digit commit".
/-- **`carrier_from_raw_32` is `carrier_from_raw` on the message it denotes.** -/
theorem carrier_from_raw_32_loop_eq {raw32 : alloc.vec.Vec linalg.RawVec32}
    {raw : alloc.vec.Vec linalg.PolyVec} (blocks : Std.Usize)
    (prep : linalg.PreparedMatrixL2) (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
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
  have hL : ∀ prep : linalg.PreparedMatrixL2,
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

-- `honest_z_from_raw_32_loop1_eq` and `honest_z_from_raw_32_eq` -- "the `_32`
-- z pass is the `_64` one on the message it denotes" -- lived here until card
-- T43 (2026-09-22). The `_32` item now has its own short branch and the
-- equality is false as a statement about programs, so it is gone; see
-- `QuadEvalProtocol.lean` § "The fused z pass".
-- `honest_compute_resp_from_raw_32_eq` lived here until candidate T28 changed
-- that item's signature: it now takes the carrier decomposition instead of
-- computing it, so it is no longer the `_64` item on a re-carriered message and
-- the equality no longer even typechecks. Its specification is proved directly
-- in `QuadEvalProtocol.lean`, from `honest_z_from_raw_32_spec` plus the
-- supplied decomposition.
/-! ## The raw-digit commit (Stage 6 card T51a)

`commit_streamed_32`'s loop computes `A · G⁻¹(xᵢ)` without building `xᵢ` or
`G⁻¹(xᵢ)`: `apply_raw_digits_gold` reads digit `j % 8` of compact row `j / 8`
straight out of the words (`GoldDot.gold_raw_dot_spec`). The bridge back to the
specification's vocabulary is a *ghost* decomposition `s`: the block the rows
expand to is some `x` (`ExpandsTo`), `gadget_decompose x` succeeds with some `s`
(`gadget_decompose_spec`), and `s`'s words are the nibbles of the rows'
canonical words (`raw_digits_of_expand`) -- which is `GoldDot.RawDigitsOf`, the
hypothesis the raw dot consumes. Everything above the dot is then
`apply_digits_gold_spec` over `s`, and everything above that is
`commit_streamed_loop_specG` with `apply_digits_gold` replaced.

`expand` is total on *every* compact row -- a raw word may lie in `[q, 2^32)`
and a row may be short or long -- so the two expand specifications below carry
no hypothesis on the row, and `GoldDot.rawWordN` (`RawRq32::word`) is exactly
`expand`'s coefficient. -/

/-- The loop of `RawRq32::expand`, on any row: entry `t` is the raw word
reduced mod `q`. -/
theorem expand_loop_spec (v : alloc.vec.Vec Std.U32) (n : Std.Usize)
    (cs : alloc.vec.Vec cpoly.field.Fp) (i : Std.Usize)
    (hn : n.val = v.val.length) (hi : i.val ≤ v.val.length) (hlen : cs.val.length = i.val)
    (hred : ∀ u ∈ cs.val, Red u)
    (hval : ∀ t, t < i.val → wordN cs t = HachiEquiv.GoldDot.rawWordN v t) :
    ring.RawRq32.expand_loop v n cs i
      ⦃ z => z.val.length = v.val.length ∧ (∀ u ∈ z.val, Red u)
        ∧ ∀ t, t < v.val.length → wordN z t = HachiEquiv.GoldDot.rawWordN v t ⦄ := by
  rw [ring.RawRq32.expand_loop]
  apply loop.spec_decr_nat (fun s => v.val.length - s.2.val)
    (fun s => s.2.val ≤ v.val.length ∧ s.1.val.length = s.2.val ∧ (∀ u ∈ s.1.val, Red u)
      ∧ ∀ t, t < s.2.val → wordN s.1 t = HachiEquiv.GoldDot.rawWordN v t)
  · rintro ⟨c1, i1⟩ ⟨hi1, hl1, hr1, hv1⟩
    dsimp only at hi1 hl1 hr1 hv1
    simp only [ring.RawRq32.expand_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hib : i1.val < v.val.length := by rw [← hn]; scalar_tac
      rw [index_eq v i1 0#u32 hib]
      simp only [bind_tc_ok]
      have hcast : lift (UScalar.cast .U64 (v.val.getD i1.val 0#u32))
          ⦃ y => y.val = (v.val.getD i1.val 0#u32).val ⦄ :=
        UScalar.cast_inBounds_spec .U64 _ (by scalar_tac)
      step with hcast as ⟨w, hw⟩
      have hf := HachiEquiv.NttStage.spec_and (fp_new_rep w) (HachiEquiv.Field.fp_new_spec w)
      step with hf as ⟨f, hfv, hRf, _⟩
      have hcap : c1.val.length < Usize.max := by
        have := v.property; scalar_tac
      step as ⟨c2, hc2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [hc2, hi2, List.length_append, hl1]; simp
      · intro u hu
        rw [hc2] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hr1 u h
        · rw [List.mem_singleton.mp h]; exact hRf
      · intro t ht
        rw [hi2] at ht
        unfold wordN
        rw [hc2]
        by_cases hte : t < i1.val
        · rw [getD_push_lt _ _ _ (by rw [hl1]; exact hte)]
          have hprev := hv1 t hte
          unfold wordN at hprev
          exact hprev
        · have htv : t = i1.val := by omega
          subst htv
          have hgd : (c1.val ++ [f]).getD i1.val cpoly.field.Fp.ZERO = f := by
            rw [← hl1]; exact getD_push_eq _ _ _
          rw [hgd, hfv, hw]
          unfold HachiEquiv.GoldDot.rawWordN
          rw [if_pos hib]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = v.val.length := by scalar_tac
      rw [heq] at hl1 hv1
      exact ⟨hl1, hr1, hv1⟩
  · exact ⟨hi, hlen, hred, hval⟩

/-- **`RawRq32::expand` on any row**: well formed, and its word at every
coefficient is the row's canonical word `RawRq32::word` reads. -/
theorem rawrq32_expand_spec (row : alloc.vec.Vec Std.U32) :
    ring.RawRq32.expand row
      ⦃ y => Wf y ∧ ∀ k, k < N → wordN y k = HachiEquiv.GoldDot.rawWordN row k ⦄ := by
  rw [ring.RawRq32.expand]
  simp only [alloc.vec.Vec.with_capacity]
  step with expand_loop_spec row (alloc.vec.Vec.len row) (alloc.vec.Vec.new cpoly.field.Fp)
    0#usize (by simp) (by simp) (by simp) (by intro u hu; simp at hu)
    (by intro t ht; simp at ht) as ⟨cs, hcsl, hcsr, hcsv⟩
  step with HachiEquiv.Ring.from_coeffs_spec cs hcsr as ⟨y, hWy, hyv⟩
  refine ⟨hWy, fun k hk => ?_⟩
  -- `cs` reads the canonical word everywhere: in range by the loop, past the
  -- row's end as `Fp.ZERO`, which is where `rawWordN` is `0`
  have hcsk : wordN cs k = HachiEquiv.GoldDot.rawWordN row k := by
    by_cases hkl : k < row.val.length
    · exact hcsv k hkl
    · unfold wordN HachiEquiv.GoldDot.rawWordN
      rw [List.getD_eq_default _ _ (by rw [hcsl]; omega), if_neg hkl]
      simp [cpoly.field.Fp.ZERO]
  have hc := hyv k hk
  rw [coeffK_eq_cast_wordN, coeffK_eq_cast_wordN, hcsk] at hc
  have h1 := HachiEquiv.NttProduct.natCast_inj_of_lt (wordN_lt hWy k) hc
  rwa [Nat.mod_eq_of_lt (HachiEquiv.GoldDot.rawWordN_lt row k)] at h1

/-- **`RawVec32::expand` on any compact block**: one well-formed ring element
per row, each reading its row's canonical words. -/
theorem rawvec32_expand_spec (rv : linalg.RawVec32) :
    linalg.RawVec32.expand rv
      ⦃ z => z.val.length = rv.val.length ∧ ∀ t, t < rv.val.length →
          Wf (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          ∧ ∀ k, k < N → wordN (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) k
              = HachiEquiv.GoldDot.rawWordN (rv.val.getD t (alloc.vec.Vec.new Std.U32)) k ⦄ := by
  rw [linalg.RawVec32.expand]
  simp only [alloc.vec.Vec.with_capacity, bind_ok_id]
  rw [linalg.RawVec32.expand_loop]
  apply loop.spec_decr_nat (fun s => rv.val.length - s.2.val)
    (fun s => s.2.val ≤ rv.val.length ∧ s.1.val.length = s.2.val ∧ ∀ t, t < s.2.val →
      Wf (s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
      ∧ ∀ k, k < N → wordN (s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) k
          = HachiEquiv.GoldDot.rawWordN (rv.val.getD t (alloc.vec.Vec.new Std.U32)) k)
  · rintro ⟨o1, i1⟩ ⟨hi1, hl1, hv1⟩
    dsimp only at hi1 hl1 hv1
    simp only [linalg.RawVec32.expand_loop.body]
    by_cases hlt : i1 < alloc.vec.Vec.len rv
    · rw [if_pos hlt]
      have hib : i1.val < rv.val.length := by scalar_tac
      rw [index_eq rv i1 (alloc.vec.Vec.new Std.U32) hib]
      simp only [bind_tc_ok]
      step with rawrq32_expand_spec (rv.val.getD i1.val (alloc.vec.Vec.new Std.U32))
        as ⟨r, hWr, hrv⟩
      have hcap : o1.val.length < Usize.max := by
        have := rv.property; scalar_tac
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hl1]; simp
      · intro t ht
        rw [hi2] at ht
        rw [ho2]
        by_cases hte : t < i1.val
        · rw [getD_push_lt _ _ _ (by rw [hl1]; exact hte)]
          exact hv1 t hte
        · have htv : t = i1.val := by omega
          subst htv
          have hgd : (o1.val ++ [r]).getD i1.val (alloc.vec.Vec.new cpoly.field.Fp) = r := by
            rw [← hl1]; exact getD_push_eq _ _ _
          rw [hgd]
          exact ⟨hWr, hrv⟩
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = rv.val.length := by scalar_tac
      rw [heq] at hl1 hv1
      exact ⟨hl1, hv1⟩
  · exact ⟨by simp, by simp, by intro t ht; simp at ht⟩

/-- **`gadget_decompose`'s words are nibbles.** Whatever represents
`gadgetDecompose Φ dd (toVec x)` holds, at entry `u` and coefficient `k`, digit
`u % 8` of block row `u / 8`'s canonical word -- `digitBlock`'s layout, read
through `digitK_eq_nibble`. A statement about any such `s`, so the caller can
take `s` to be the ghost `gadget_decompose_spec` produces. -/
theorem gadgetDecompose_words {rows : ℕ} (x s : linalg.PolyVec) (hx : WfVec rows x)
    (hs : WfVec (rows * 8) s)
    (hsx : toVec (k := rows * 8) s = gadgetDecompose Φ dd (toVec (k := rows) x))
    (u : ℕ) (hu : u < rows * 8) (k : ℕ) (hk : k < N) :
    wordN (s.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k
      = (wordN (x.val.getD (u / 8) (alloc.vec.Vec.new cpoly.field.Fp)) k / 16 ^ (u % 8)) % 16 := by
  have he'lt : u % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hi'lt : u / 8 < rows := by omega
  have hfp : (finProdFinEquiv (⟨u / 8, hi'lt⟩, ⟨u % 8, he'lt⟩) : Fin (rows * 8))
      = ⟨u, hu⟩ := by
    apply Fin.ext
    show u % 8 + 8 * (u / 8) = u
    omega
  have hgd : gadgetDecompose Φ dd (toVec (k := rows) x) ⟨u, hu⟩
      = Rq.ofFinCoeff Φ Φ.φ.natDegree
          (fun k => dd.digit ((toVec (k := rows) x ⟨u / 8, hi'lt⟩).1.coeff k)
            ⟨u % 8, he'lt⟩) := by
    rw [← hfp]
    exact gadgetDecomposeFun_apply Φ dd.digit (toVec (k := rows) x) _ _
  have hWs : Wf (s.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) := wf_getD hs hu
  have hWx : Wf (x.val.getD (u / 8) (alloc.vec.Vec.new cpoly.field.Fp)) := wf_getD hx hi'lt
  have hcoeff : coeffK (s.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k
      = dd.digit ((toVec (k := rows) x ⟨u / 8, hi'lt⟩).1.coeff k) ⟨u % 8, he'lt⟩ := by
    have h1 : (toVec (k := rows * 8) s ⟨u, hu⟩).1.coeff k
        = coeffK (s.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k := by
      simp only [toVec]
      rw [toRq_coeff_eq_coeffK hWs]
    rw [← h1, hsx, hgd, Rq.ofFinCoeff_coeff Φ _ (Rq.phi_natDegree_le_degree Φ) k,
      if_pos (by rw [RqBridge.phi_natDegree]; exact hk)]
  have hxk : (toVec (k := rows) x ⟨u / 8, hi'lt⟩).1.coeff k
      = ((wordN (x.val.getD (u / 8) (alloc.vec.Vec.new cpoly.field.Fp)) k : ℕ) : ZMod q) := by
    simp only [toVec]
    rw [toRq_coeff_eq_coeffK hWx, coeffK_eq_cast_wordN]
  rw [hxk, dd_digit_eq, digitK_eq_nibble _ (wordN_lt hWx k), coeffK_eq_cast_wordN] at hcoeff
  have hnib : (wordN (x.val.getD (u / 8) (alloc.vec.Vec.new cpoly.field.Fp)) k
      / 16 ^ (u % 8)) % 16 < q := by
    have := Nat.mod_lt (wordN (x.val.getD (u / 8) (alloc.vec.Vec.new cpoly.field.Fp)) k
      / 16 ^ (u % 8)) (by norm_num : 0 < 16)
    unfold q; omega
  have h2 := HachiEquiv.NttProduct.natCast_inj_of_lt (wordN_lt hWs k) hcoeff
  rwa [Nat.mod_eq_of_lt hnib] at h2

/-- **The bridge.** A compact block `rv` that expands to `x`, and any `s`
representing `G⁻¹(x)`: then `rv` has `rows` rows and `s` is the digit block the
raw dot reads out of them (`GoldDot.RawDigitsOf`). -/
theorem raw_digits_of_expand {rows : ℕ} (rv : linalg.RawVec32) (x s : linalg.PolyVec)
    (hexp : linalg.RawVec32.expand rv = ok x) (hx : WfVec rows x)
    (hs : WfVec (rows * 8) s)
    (hsx : toVec (k := rows * 8) s = gadgetDecompose Φ dd (toVec (k := rows) x)) :
    rv.val.length = rows ∧ HachiEquiv.GoldDot.RawDigitsOf rv s (rows * 8) := by
  have he := rawvec32_expand_spec rv
  rw [hexp, WP.spec_ok] at he
  obtain ⟨hxl, hxv⟩ := he
  have hrl : rv.val.length = rows := by rw [← hxl, hx.1]
  refine ⟨hrl, fun u hu => ⟨wf_getD hs hu, fun k hk => ?_⟩⟩
  have hr : u / 8 < rv.val.length := by rw [hrl]; omega
  rw [gadgetDecompose_words x s hx hs hsx u hu k hk, (hxv (u / 8) hr).2 k hk]

/-- `dot_prepared_raw_digits_gold` at the `Rq` level: the dot product of the
prepared row with the ghost digit block. `Scheme.dot_prep_digits_gold_spec`'s
conclusion over `s`. -/
theorem dot_prep_raw_digits_gold_spec {k : ℕ} (prep : ring.PreparedVecG)
    (u s : linalg.PolyVec) (raw : alloc.vec.Vec ring.RawRq32) (nU : Std.Usize)
    (hn : nU.val = k) (hu : WfVec k u) (hs : HachiEquiv.GoldDot.RawDigitsOf raw s k)
    (hraw : k ≤ 8 * raw.val.length) (hwidth : k ≤ 8192) (hprep : PrepRowG k prep u) :
    ring.dot_prepared_raw_digits_gold prep raw nU
      ⦃ z => Wf z ∧ toRq z
        = ArkLib.Lattices.dot (toVec (k := k) u) (toVec (k := k) s) ⦄ := by
  obtain ⟨-, hp⟩ := hprep
  have haw : ∀ j, j < nU.val → Wf (u.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) :=
    fun j hj => wf_getD hu (by rw [← hn]; exact hj)
  have hbw : ∀ j, j < nU.val → Wf (s.val.getD j (alloc.vec.Vec.new cpoly.field.Fp)) :=
    fun j hj => (hs j (by rw [← hn]; exact hj)).1
  apply spec_mono (HachiEquiv.GoldDot.gold_raw_dot_spec prep u s raw nU haw
    (by rw [hn]; exact hs) (by rw [hn]; exact hraw) (by rw [hn]; exact hwidth)
    (by rw [hn]; exact hp))
  rintro z ⟨hzwf, hzval⟩
  refine ⟨hzwf, ?_⟩
  rw [RqBridge.dot_sum_toRq u s nU haw hbw z hzval, hn, ArkLib.Lattices.dot_eq_sum]
  exact (Fin.sum_univ_eq_sum_range
    (fun j => toRq (u.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
      * toRq (s.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))) k).symm

/-- The loop of `PreparedMatrixG::apply_raw_digits_gold`:
`Scheme.apply_digits_gold_loop_spec` over the ghost digit block `s`. -/
theorem apply_raw_digits_gold_loop_spec {rows cols : ℕ} (pm : linalg.PreparedMatrixG)
    (m : linalg.PolyMatrix) (raw : alloc.vec.Vec ring.RawRq32) (s : linalg.PolyVec)
    (n w : Std.Usize) (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (ha : WfMat rows cols m) (hs : HachiEquiv.GoldDot.RawDigitsOf raw s cols)
    (hraw : cols ≤ 8 * raw.val.length)
    (hp : WfPrepG rows cols pm m) (hwidth : cols ≤ 8192)
    (hn : n.val = rows) (hw : w.val = cols)
    (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hwf : ∀ z ∈ out.val, Wf z)
    (hval : ∀ j, j < i.val →
      toRq (out.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ArkLib.Lattices.dot (toVec (k := cols) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))
            (toVec (k := cols) s)) :
    linalg.PreparedMatrixG.apply_raw_digits_gold_loop pm.rows raw n w out i
      ⦃ z => z.val.length = rows ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ j, j < rows → toRq (z.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
          = ArkLib.Lattices.dot (toVec (k := cols) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))
              (toVec (k := cols) s) ⦄ := by
  rw [linalg.PreparedMatrixG.apply_raw_digits_gold_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun st => st.2.val ≤ n.val ∧ st.1.val.length = st.2.val ∧ (∀ y ∈ st.1.val, Wf y) ∧
      ∀ j, j < st.2.val → toRq (st.1.val.getD j (alloc.vec.Vec.new cpoly.field.Fp))
        = ArkLib.Lattices.dot (toVec (k := cols) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))
            (toVec (k := cols) s))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [linalg.PreparedMatrixG.apply_raw_digits_gold_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hip : i1.val < pm.rows.val.length := by rw [hp.2.1, ← hn]; scalar_tac
      have him : i1.val < m.val.length := by rw [ha.1, ← hn]; scalar_tac
      step as ⟨pv, hpv⟩
      have hprow : PrepRowG cols pv (m.val.getD i1.val (alloc.vec.Vec.new ring.Rq)) := by
        have := hp.2.2 i1.val (by rw [← hn]; scalar_tac)
        rwa [List.getD_eq_getElem _ _ hip, ← hpv] at this
      have hWrow : WfVec cols (m.val.getD i1.val (alloc.vec.Vec.new ring.Rq)) := by
        rw [List.getD_eq_getElem _ _ him]; exact ha.2 _ (List.getElem_mem him)
      step with dot_prep_raw_digits_gold_spec (k := cols) pv
        (m.val.getD i1.val (alloc.vec.Vec.new ring.Rq)) s raw w hw hWrow hs hraw
        hwidth hprow
        as ⟨r, hWr, hr⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 j hjlt]
        · have hjeq : j = o1.val.length := by omega
          rw [hjeq, ho2, getD_append_eq, hr, hlen1]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq, hn], hwf1, by intro j hj; exact hval1 j (by rw [heq, hn]; exact hj)⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- General form (arbitrary `rows mr`).
**`PreparedMatrixG::apply_raw_digits_gold` = `A · G⁻¹(x)`** for the block `x`
the compact rows expand to, with neither `x` nor `G⁻¹(x)` built. The value is
`apply_digits_gold_spec`'s on `gadget_decompose x`; that decomposition exists
only in the proof. -/
theorem apply_raw_digits_gold_specG {rows mr : ℕ} (pm : linalg.PreparedMatrixG)
    (m : linalg.PolyMatrix) (raw : linalg.RawVec32) (x : linalg.PolyVec)
    (ha : WfMat rows (mr * 8) m) (hp : WfPrepG rows (mr * 8) pm m) (hmr8 : mr * 8 ≤ 8192)
    (hx : WfVec mr x) (hexp : linalg.RawVec32.expand raw = ok x) :
    linalg.PreparedMatrixG.apply_raw_digits_gold pm raw
      ⦃ z => WfVec rows z ∧ toVec (k := rows) z
        = ArkLib.Lattices.matVecMul (toMat (rows := rows) (cols := mr * 8) m)
            (gadgetDecompose Φ dd (toVec (k := mr) x)) ⦄ := by
  have hmax : 8 * mr ≤ Usize.max := by have := usize_max_ge'; omega
  -- the ghost: `G⁻¹(x)` as `gadget_decompose` would have built it
  obtain ⟨s, -, hWs, hsx⟩ := spec_imp_exists (gadget_decompose_spec (rows := mr) x hx hmax)
  obtain ⟨hrl, hB⟩ := raw_digits_of_expand raw x s hexp hx hWs hsx
  have hcl : pm.cols.val = mr * 8 := hp.1
  rw [linalg.PreparedMatrixG.apply_raw_digits_gold]
  have hdig : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  step as ⟨terms, hterms⟩
  have htv : terms.val = mr * 8 := by rw [hterms, hdig]; simp [hrl]
  simp only [if_pos (by scalar_tac : pm.cols ≤ terms), bind_ok_id]
  apply spec_mono (apply_raw_digits_gold_loop_spec pm m raw s (alloc.vec.Vec.len pm.rows)
    pm.cols (alloc.vec.Vec.new ring.Rq) 0#usize ha hB (by rw [hrl]; omega) hp hmr8
    (by simp [hp.2.1]) hcl (by simp) (by simp) (by intro y hy; simp at hy)
    (by intro j hj; simp at hj))
  rintro z ⟨hzlen, hzwf, hzval⟩
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  rw [← hsx]
  funext i
  rw [ArkLib.Lattices.matVecMul_apply, toMat_apply]
  exact hzval i.val i.isLt

/-- General form of the loop of `commit::commit_streamed_32` (arbitrary
`ir mr or bl`): `Scheme.commit_streamed_loop_specG` on the message the words
denote, with the block's `A · G⁻¹(xᵢ)` from `apply_raw_digits_gold_specG`. -/
theorem commit_streamed_32_loop_specG (ir mr or bl : ℕ) (pp : commit.PublicParams)
    (raw32 : alloc.vec.Vec linalg.RawVec32) (m : alloc.vec.Vec linalg.PolyVec)
    (blocks : Std.Usize)
    (prep : linalg.PreparedMatrixG) (ts : alloc.vec.Vec linalg.PolyVec) (i : Std.Usize)
    (hex : ExpandsTo raw32 m)
    (hpp : WfParamsG ir mr or bl pp) (hprep : WfPrepG ir (mr * 8) prep pp.inner_matrix)
    (hm : m.val.length = bl ∧ ∀ x ∈ m.val, WfVec mr x)
    (hb : blocks.val = bl) (hi : i.val ≤ bl)
    (hts : ts.val.length = i.val) (hWts : ∀ y ∈ ts.val, WfVec (ir * 8) y)
    (hvts : ∀ j < i.val, toVec (k := ir * 8) (ts.val.getD j (alloc.vec.Vec.new ring.Rq))
      = gadgetDecompose Φ dd (ArkLib.Lattices.matVecMul
          (toMat (rows := ir) (cols := mr * 8) pp.inner_matrix)
          (gadgetDecompose Φ dd
            (toVec (k := mr) (m.val.getD j (alloc.vec.Vec.new ring.Rq))))))
    (hmr8 : mr * 8 ≤ 8192) (hir8 : 8 * ir ≤ Usize.max) :
    commit.commit_streamed_32_loop raw32 blocks prep ts i
      ⦃ r => r.val.length = bl ∧ (∀ y ∈ r.val, WfVec (ir * 8) y) ∧
        ∀ j < bl, toVec (k := ir * 8) (r.val.getD j (alloc.vec.Vec.new ring.Rq))
          = gadgetDecompose Φ dd (ArkLib.Lattices.matVecMul
              (toMat (rows := ir) (cols := mr * 8) pp.inner_matrix)
              (gadgetDecompose Φ dd
                (toVec (k := mr) (m.val.getD j (alloc.vec.Vec.new ring.Rq))))) ⦄ := by
  rw [commit.commit_streamed_32_loop]
  apply loop.spec_decr_nat (fun s => blocks.val - s.2.val)
    (fun s => s.2.val ≤ bl ∧ s.1.val.length = s.2.val ∧
      (∀ y ∈ s.1.val, WfVec (ir * 8) y) ∧
      (∀ j < s.2.val, toVec (k := ir * 8) (s.1.val.getD j (alloc.vec.Vec.new ring.Rq))
        = gadgetDecompose Φ dd (ArkLib.Lattices.matVecMul
            (toMat (rows := ir) (cols := mr * 8) pp.inner_matrix)
            (gadgetDecompose Φ dd
              (toVec (k := mr) (m.val.getD j (alloc.vec.Vec.new ring.Rq)))))))
  · rintro ⟨t1, i1⟩ ⟨hi1, ht1, hWt1, hvt1⟩
    dsimp only at hi1 ht1 hWt1 hvt1
    simp only [commit.commit_streamed_32_loop.body]
    by_cases hlt : i1 < blocks
    · rw [if_pos hlt]
      have hilt : i1.val < m.val.length := by rw [hm.1, ← hb]; scalar_tac
      have hi32 : i1.val < raw32.val.length := by rw [hex.1]; exact hilt
      step as ⟨rv, hrv⟩
      have hexp : linalg.RawVec32.expand rv
          = ok (m.val.getD i1.val (alloc.vec.Vec.new ring.Rq)) := by
        have h := hex.2 i1.val hi32
        rwa [List.getD_eq_getElem _ _ hi32, ← hrv] at h
      have hWpv : WfVec mr (m.val.getD i1.val (alloc.vec.Vec.new ring.Rq)) := by
        rw [List.getD_eq_getElem _ _ hilt]; exact hm.2 _ (List.getElem_mem hilt)
      step with apply_raw_digits_gold_specG (rows := ir) (mr := mr) prep pp.inner_matrix rv
        (m.val.getD i1.val (alloc.vec.Vec.new ring.Rq)) hpp.1 hprep hmr8 hWpv hexp
        as ⟨inner, hWinner, hinner⟩
      step with gadget_decompose_spec (rows := ir) inner hWinner hir8
        as ⟨t, hWt, ht⟩
      step as ⟨t2, ht2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ht2, hi2, List.length_append, ht1]; simp
      · intro y hy
        rw [ht2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hWt1 y h
        · rw [List.mem_singleton.mp h]; exact hWt
      · intro j hj
        rw [hi2] at hj
        rcases Nat.lt_or_ge j i1.val with hjlt | hjge
        · rw [ht2, getD_append_lt _ _ _ (by omega), hvt1 j hjlt]
        · have hjeq : j = t1.val.length := by omega
          rw [hjeq, ht2, getD_append_eq, ht, hinner, ht1]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = bl := by rw [← hb] at hi1 ⊢; scalar_tac
      rw [heq] at ht1 hvt1
      exact ⟨ht1, hWt1, hvt1⟩
  · exact ⟨hi, hts, hWts, hvts⟩

/-! ## The specification

`commit_streamed_32`'s. Until card T51a it was inherited from `commit_streamed`
through the program equality; it is now `commit_streamed_specG`'s proof with
`commit_streamed_32_loop_specG` in place of `commit_streamed_loop_specG`, and
its statement is unchanged. The other six consumers' are in
`QuadEvalProtocol.lean`, beside the specifications they inherit. -/

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
  rw [commit.commit_streamed_32]
  simp only [commit.PublicParams.impl.inner_matrix, commit.PublicParams.impl.outer_matrix]
  step with prepare_digits_gold_spec (rows := ir) (cols := mr * 8) pp.inner_matrix hpp.1 hir
    (by have h := usize_max_ge'; norm_num [N]; omega) as ⟨prep, hprep⟩
  step with commit_streamed_32_loop_specG ir mr or bl pp raw32 m (alloc.vec.Vec.len raw32)
    prep (alloc.vec.Vec.new linalg.PolyVec) 0#usize hex hpp hprep hm
    (by simpa [hex.1] using hm.1)
    (by simp) (by simp) (by intro y hy; simp at hy) (by intro j hj; simp at hj) hmr8 hir8
    as ⟨ts, htl, hWts, hvts⟩
  step with flatten_blocks_spec (blocks := bl) (width := ir * 8) ts
    hsz ⟨htl, hWts⟩ as ⟨flat, hWflat, hflat⟩
  step with mat_vec_mul_spec (rows := or) (cols := bl * (ir * 8))
    pp.outer_matrix flat hpp.2 hWflat as ⟨u, hWu, hu⟩
  -- the `t̂` half, once: both remaining components are this equality
  have hts : (fun j : Fin bl =>
        toVec (k := ir * 8) (ts.val.getD j.val (alloc.vec.Vec.new ring.Rq)))
      = (InnerOuter.generateDecomps Φ
          (InnerOuter.Decomposition.ofDigits Φ dd dd) (toParamsG ir mr or bl pp)
          (fun i : Fin bl => toVec (k := mr)
            (m.val.getD i.val (alloc.vec.Vec.new ring.Rq)))).innerDecomp := by
    funext j
    rw [hvts j.val j.isLt]
    rfl
  refine ⟨hWu, htl, hWts, fun j => by rw [← hts], ?_⟩
  rw [hu, hflat, hts]
  rfl

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
