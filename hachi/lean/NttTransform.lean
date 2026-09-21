/-
The rest of the **extracted transform**: the push and in-place loops around the
stages, the two stage runs, and the per-prime pipeline.

`NttStage.lean` proves the DIF stage; this file proves the DIT stage (its mirror)
and everything that is not a stage: the twiddle table, the twist, the pointwise
product, the untwist, and the two loops that compose stages into transforms.

## The shape of a transform spec

`ntt_forward`'s loop carries `(cur, tmp, len)` and swaps the two buffers. Its
invariant is the *conserved-value* form rather than a pointwise one:

```text
difRun om k (2 ^ (10 - k)) (resK cur) = difRun om 10 1 (resK cur₀)
```

with `len = 2 ^ k`. One stage turns `difRun om k step` into
`difRun om (k-1) (2·step)` applied to the stage's output, which is exactly what
the loop body does, so the invariant is preserved by `rfl`-like rewriting; and at
`len = 1` it *is* the conclusion. A pointwise invariant would need the whole
block structure re-derived at every stage.

## Where the factor of two lives

The twiddle table holds powers of `ψ`, a root of order `2N`; the transform runs
on `ω = ψ²`, of order `N`. The code therefore steps the table index by
`2 · (N / len)` where the ring-level stage steps the exponent by `N / len`.
`NttStage.difWord_cast` and [`ditWord_cast`] are where that factor is discharged,
once each, and nothing above them mentions `ψ` again.
-/
import NttStage

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.NttTransform

open HachiEquiv.NttArith HachiEquiv.NttStage

/-! ## `ntt::zeros` -/

/-! ### Reading a coefficient out of a pushed buffer

The `wordAt` analogues of `Ring.lean`'s `coeffK_append_lt` / `coeffK_append_eq`:
every push loop needs the same two facts about `out.val ++ [x]`. -/

private theorem wordAt_append_lt {v w : alloc.vec.Vec Std.U64} {x : Std.U64}
    (hw : w.val = v.val ++ [x]) {k : ℕ} (hk : k < v.val.length) :
    wordAt w k = wordAt v k := by
  unfold wordAt
  rw [hw, List.getD_eq_getElem _ _ (by simp only [List.length_append,
      List.length_cons, List.length_nil]; omega),
    List.getD_eq_getElem _ _ hk, List.getElem_append_left hk]

private theorem wordAt_append_eq {v w : alloc.vec.Vec Std.U64} {x : Std.U64}
    (hw : w.val = v.val ++ [x]) : wordAt w v.val.length = x.val := by
  unfold wordAt
  rw [hw, List.getD_eq_getElem _ _ (by simp),
    List.getElem_append_right (Nat.le_refl _)]
  simp

/-- The push loop: `out` is already `i` zeros, and stays a `replicate`. -/
theorem zeros_loop_spec (n : Std.Usize) (out : alloc.vec.Vec Std.U64) (i : Std.Usize)
    (hi : i.val ≤ n.val) (hout : out.val = List.replicate i.val 0#u64) :
    ntt.zeros_loop n out i ⦃ z => z.val = List.replicate n.val 0#u64 ⦄ := by
  rw [ntt.zeros_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val = List.replicate s.2.val 0#u64)
  · rintro ⟨o1, i1⟩ ⟨hi1, ho1⟩
    dsimp only at hi1 ho1
    simp only [ntt.zeros_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hlen : o1.val.length = i1.val := by rw [ho1, List.length_replicate]
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [ho2, hi2, ho1, List.replicate_succ']
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      show o1.val = List.replicate n.val 0#u64
      have heq : i1.val = n.val := by scalar_tac
      rw [ho1, heq]
  · exact ⟨hi, hout⟩

/-- The scratch buffer. Its *contents* are irrelevant -- every entry is
overwritten by the first stage that writes into it -- but its length and
canonicality are not, so both are stated. -/
theorem zeros_spec (n : Std.Usize) :
    ntt.zeros n ⦃ z => z.val = List.replicate n.val 0#u64 ⦄ := by
  rw [ntt.zeros]
  simp only [alloc.vec.Vec.with_capacity]
  exact zeros_loop_spec n (alloc.vec.Vec.new Std.U64) 0#usize (by simp) (by simp)

theorem zeros_canon (p : ℕ) (hp : 0 < p) :
    ntt.zeros ntt.NTT_LEN ⦃ z => Canon p z ⦄ := by
  apply spec_mono (zeros_spec ntt.NTT_LEN)
  intro z hz
  refine ⟨?_, ?_⟩
  · rw [hz, List.length_replicate, ntt_NTT_LEN_val]
  · intro u hu
    rw [hz] at hu
    rw [List.eq_of_mem_replicate hu]
    simpa using hp

/-! ## `ntt::psi_table` -/

/-- The push loop, with the running accumulator `cur = ψ^i mod p` alongside the
counter. The invariant is the length, canonicality, the accumulator's value and
the entries written so far. -/
theorem psi_table_loop_spec (psi pw mw : Std.U64) (n : Std.Usize)
    (out : alloc.vec.Vec Std.U64) (cur : Std.U64) (i : Std.Usize)
    (h : Magic pw mw) (hpsi : psi.val < pw.val)
    (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hcan : ∀ u ∈ out.val, u.val < pw.val)
    (hcur : cur.val = psi.val ^ i.val % pw.val)
    (hvals : ∀ e, e < i.val → wordAt out e = psi.val ^ e % pw.val) :
    ntt.psi_table_loop psi pw mw n out cur i
      ⦃ z => z.val.length = n.val ∧ (∀ u ∈ z.val, u.val < pw.val)
             ∧ ∀ e, e < n.val → wordAt z e = psi.val ^ e % pw.val ⦄ := by
  have hppos : 0 < pw.val := h.pos
  rw [ntt.psi_table_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.2.val)
    (fun s => s.2.2.val ≤ n.val ∧ s.1.val.length = s.2.2.val
      ∧ (∀ u ∈ s.1.val, u.val < pw.val)
      ∧ s.2.1.val = psi.val ^ s.2.2.val % pw.val
      ∧ ∀ e, e < s.2.2.val → wordAt s.1 e = psi.val ^ e % pw.val)
  · rintro ⟨o1, c1, i1⟩ ⟨hi1, hlen1, hcan1, hc1, hv1⟩
    dsimp only at hi1 hlen1 hcan1 hc1 hv1
    simp only [ntt.psi_table_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hclt : c1.val < pw.val := by rw [hc1]; exact Nat.mod_lt _ hppos
      step as ⟨o2, ho2⟩
      step with aux_mul_lt c1 psi pw mw h hclt hpsi as ⟨c2, hc2, hc2lt⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_, ?_⟩
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with hh | hh
        · exact hcan1 u hh
        · rw [List.mem_singleton.mp hh]; exact hclt
      · rw [hc2, hc1, hi2, pow_succ, Nat.mod_mul_mod]
      · intro e he
        rw [hi2] at he
        rcases Nat.lt_or_ge e i1.val with helt | hege
        · rw [wordAt_append_lt ho2 (by omega), hv1 e helt]
        · have heq : e = o1.val.length := by omega
          rw [heq, wordAt_append_eq ho2, hc1, hlen1]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hcan1, by rw [← heq]; exact hv1⟩
  · exact ⟨hi, hlen, hcan, hcur, hvals⟩

/-- The table is the powers of `ψ`. That is the whole correctness rule, and it is
why no pinned constant table appears anywhere in `ntt.rs`. -/
theorem psi_table_spec (psi pw mw : Std.U64) (h : Magic pw mw) (hpsi : psi.val < pw.val) :
    ntt.psi_table psi pw mw
      ⦃ z => Canon pw.val z ∧ ∀ e, e < N → wordAt z e = psi.val ^ e % pw.val ⦄ := by
  have h1 : 1 < pw.val := by have := h.two_le; omega
  rw [ntt.psi_table]
  simp only [alloc.vec.Vec.with_capacity]
  apply spec_mono (psi_table_loop_spec psi pw mw ntt.NTT_LEN
    (alloc.vec.Vec.new Std.U64) 1#u64 0#usize h hpsi (by simp) (by simp)
    (by intro u hu; simp at hu)
    (by show (1 : ℕ) = psi.val ^ 0 % pw.val
        rw [pow_zero, Nat.mod_eq_of_lt h1])
    (by intro e he; simp at he))
  rintro z ⟨hzlen, hzcan, hzvals⟩
  refine ⟨⟨?_, hzcan⟩, ?_⟩
  · rw [hzlen, ntt_NTT_LEN_val]
  · intro e he
    exact hzvals e (by rw [ntt_NTT_LEN_val]; exact he)

/-- The table read as `ZMod p`, which is the form every stage spec wants. -/
theorem psi_table_cast (psi pw mw : Std.U64) (h : Magic pw mw) (hpsi : psi.val < pw.val) :
    ntt.psi_table psi pw mw
      ⦃ z => Canon pw.val z
             ∧ ∀ e, e < N → resK pw.val z e = ((psi.val : ℕ) : ZMod pw.val) ^ e ⦄ := by
  apply spec_mono (psi_table_spec psi pw mw h hpsi)
  rintro z ⟨hz, hzvals⟩
  refine ⟨hz, ?_⟩
  intro e he
  simp only [resK]
  rw [hzvals e he, ZMod.natCast_mod, Nat.cast_pow]

/-! ## `ntt::twist`, `ntt::pointwise`, `ntt::untwist`

Three passes of the same shape: read one or two buffers at the same index, do a
constant amount of modular arithmetic, write index `t`. `twist` and `untwist`
push into a fresh buffer; `pointwise` writes its first operand in place.
-/

/-! ### Reading a pushed buffer

The `wordAt` form of `Ring.lean`'s `coeffK_append_lt` / `coeffK_append_eq`: the
two facts a `push` loop needs about the buffer it has just extended. The raw
`List.getD` pair is transcribed here for the same reason `Ring.lean` primes its
copy -- the carrier differs, so nothing can be shared. -/

private theorem getD_append_lt' {α : Type} (l : List α) (x d : α) {j : ℕ}
    (hj : j < l.length) : (l ++ [x]).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hj,
    List.getElem_append_left hj]

private theorem getD_append_eq' {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
  simp

/-- Reading a pushed buffer below the join. -/
private theorem wordAt_pushed_lt {o o1 : alloc.vec.Vec Std.U64} {x : Std.U64} {j : ℕ}
    (ho : o1.val = o.val ++ [x]) (hj : j < o.val.length) : wordAt o1 j = wordAt o j := by
  unfold wordAt; rw [ho, getD_append_lt' _ _ _ hj]

/-- Reading the pushed entry itself. -/
private theorem wordAt_pushed_eq {o o1 : alloc.vec.Vec Std.U64} {x : Std.U64}
    (ho : o1.val = o.val ++ [x]) : wordAt o1 o.val.length = x.val := by
  unfold wordAt; rw [ho, getD_append_eq']

/-- `ntt::twist`'s loop: `out` grows by one reduced-and-scaled entry per step, so
its length *is* the counter and its entries below the counter hold the product.
`v` is only assumed long enough -- not canonical -- because the body reduces
every word it reads before multiplying. -/
theorem twist_loop_spec (v pt : alloc.vec.Vec Std.U64) (pw mw : Std.U64) (n : Std.Usize)
    (out : alloc.vec.Vec Std.U64) (t : Std.Usize) (h : Magic pw mw)
    (hnv : n.val ≤ v.val.length) (hnp : n.val ≤ pt.val.length)
    (hptr : ∀ u ∈ pt.val, u.val < pw.val)
    (ht : t.val ≤ n.val) (hlen : out.val.length = t.val)
    (hred : ∀ u ∈ out.val, u.val < pw.val)
    (hval : ∀ k, k < t.val →
      wordAt out k = (wordAt v k % pw.val * wordAt pt k) % pw.val) :
    ntt.twist_loop v pt pw mw n out t
      ⦃ z => z.val.length = n.val ∧ (∀ u ∈ z.val, u.val < pw.val)
             ∧ ∀ k, k < n.val →
                 wordAt z k = (wordAt v k % pw.val * wordAt pt k) % pw.val ⦄ := by
  rw [ntt.twist_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧
      (∀ u ∈ s.1.val, u.val < pw.val) ∧
      ∀ k, k < s.2.val → wordAt s.1 k = (wordAt v k % pw.val * wordAt pt k) % pw.val)
  · rintro ⟨o1, t1⟩ ⟨ht1, hlen1, hred1, hval1⟩
    dsimp only at ht1 hlen1 hred1 hval1
    simp only [ntt.twist_loop.body]
    by_cases hlt : t1 < n
    · rw [if_pos hlt]
      have hiv : t1.val < v.val.length := by scalar_tac
      have hip : t1.val < pt.val.length := by scalar_tac
      have hcap : o1.val.length < Usize.max := by scalar_tac
      step as ⟨i, hi⟩
      step with aux_reduce_lt i pw mw h as ⟨i1, hi1v, hi1l⟩
      step as ⟨i2, hi2⟩
      have hi2l : i2.val < pw.val := hi2 ▸ hptr _ (List.getElem_mem hip)
      step with aux_mul_lt i1 i2 pw mw h hi1l hi2l as ⟨i3, hi3v, hi3l⟩
      step as ⟨o2, ho2⟩
      step as ⟨t2, ht2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, List.length_append, hlen1]; scalar_tac
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with hh | hh
        · exact hred1 u hh
        · rw [List.mem_singleton.mp hh]; exact hi3l
      · intro k hk
        rw [ht2] at hk
        rcases Nat.lt_or_ge k t1.val with hklt | hkge
        · rw [wordAt_pushed_lt ho2 (by omega), hval1 k hklt]
        · have hkeq : k = o1.val.length := by omega
          rw [hkeq, wordAt_pushed_eq ho2, hlen1, hi3v, hi1v,
            wordAt_of_lt hiv, wordAt_of_lt hip, hi, hi2]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : t1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hred1, by rw [← heq]; exact hval1⟩
  · exact ⟨ht, hlen, hred, hval⟩

theorem twist_spec (v pt : alloc.vec.Vec Std.U64) (pw mw : Std.U64) (h : Magic pw mw)
    (hv : v.val.length = N) (hpt : Canon pw.val pt) :
    ntt.twist v pt pw mw
      ⦃ z => Canon pw.val z
             ∧ ∀ t, t < N →
                 wordAt z t = (wordAt v t % pw.val * wordAt pt t) % pw.val ⦄ := by
  rw [ntt.twist]
  simp only [alloc.vec.Vec.with_capacity]
  apply spec_mono (twist_loop_spec v pt pw mw ntt.NTT_LEN
    (alloc.vec.Vec.new Std.U64) 0#usize h
    (by simp [hv]) (by simp [hpt.1]) hpt.2
    (by simp) (by simp) (by intro u hu; simp at hu) (by intro k hk; simp at hk))
  rintro z ⟨hzlen, hzred, hzval⟩
  refine ⟨⟨by rw [hzlen, ntt_NTT_LEN_val], hzred⟩, ?_⟩
  intro k hk
  exact hzval k (by rw [ntt_NTT_LEN_val]; exact hk)

/-- `ntt::pointwise`'s loop: an in-place pass, so the invariant has to name both
halves of the buffer -- the prefix already overwritten with the product, and the
*suffix still holding the original `a`*. The suffix conjunct is not bookkeeping:
it is what identifies the word the body reads at index `i` with `wordAt a i`, and
without it the conclusion does not mention `a` at all. -/
theorem pointwise_loop_spec (a b acc : alloc.vec.Vec Std.U64) (pw mw : Std.U64)
    (n i : Std.Usize) (h : Magic pw mw) (hb : Canon pw.val b)
    (hn : n.val ≤ N) (hi : i.val ≤ n.val) (hacc : Canon pw.val acc)
    (hdone : ∀ t, t < i.val → wordAt acc t = (wordAt a t * wordAt b t) % pw.val)
    (htodo : ∀ t, i.val ≤ t → wordAt acc t = wordAt a t) :
    ntt.pointwise_loop acc b pw mw n i
      ⦃ z => Canon pw.val z
             ∧ ∀ t, t < n.val → wordAt z t = (wordAt a t * wordAt b t) % pw.val ⦄ := by
  rw [ntt.pointwise_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ Canon pw.val s.1 ∧
      (∀ t, t < s.2.val → wordAt s.1 t = (wordAt a t * wordAt b t) % pw.val) ∧
      (∀ t, s.2.val ≤ t → wordAt s.1 t = wordAt a t))
  · rintro ⟨c1, i1⟩ ⟨hi1, hc1, hdone1, htodo1⟩
    dsimp only at hi1 hc1 hdone1 htodo1
    simp only [ntt.pointwise_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hic : i1.val < c1.val.length := by rw [hc1.1]; scalar_tac
      have hib : i1.val < b.val.length := by rw [hb.1]; scalar_tac
      step as ⟨x, hx⟩
      have hxl : x.val < pw.val := hx ▸ hc1.2 _ (List.getElem_mem hic)
      have hxv : x.val = wordAt a i1.val := by
        rw [hx, ← wordAt_of_lt hic]; exact htodo1 i1.val (Nat.le_refl _)
      step as ⟨y, hy⟩
      have hyl : y.val < pw.val := hy ▸ hb.2 _ (List.getElem_mem hib)
      have hyv : y.val = wordAt b i1.val := by rw [hy, ← wordAt_of_lt hib]
      step with aux_mul_lt x y pw mw h hxl hyl as ⟨z, hzv, hzl⟩
      step as ⟨elem, back, helem, hback⟩
      rw [hback]
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, Canon_set hc1 hzl, ?_, ?_, ?_⟩
      · intro t htlt
        rw [hi2] at htlt
        rcases Nat.lt_or_ge t i1.val with h1 | h1
        · rw [wordAt_set_ne (by omega)]; exact hdone1 t h1
        · have hteq : t = i1.val := by omega
          rw [hteq, wordAt_set_eq hic, hzv, hxv, hyv]
      · intro t htge
        rw [hi2] at htge
        rw [wordAt_set_ne (by omega)]
        exact htodo1 t (by omega)
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n.val := by scalar_tac
      exact ⟨hc1, by rw [← heq]; exact hdone1⟩
  · exact ⟨hi, hacc, hdone, htodo⟩

theorem pointwise_spec (a b : alloc.vec.Vec Std.U64) (pw mw : Std.U64) (h : Magic pw mw)
    (ha : Canon pw.val a) (hb : Canon pw.val b) :
    ntt.pointwise a b pw mw
      ⦃ z => Canon pw.val z
             ∧ ∀ t, t < N → wordAt z t = (wordAt a t * wordAt b t) % pw.val ⦄ := by
  rw [ntt.pointwise]
  apply spec_mono (pointwise_loop_spec a b a pw mw ntt.NTT_LEN 0#usize h hb
    (by simp) (by simp) ha (by intro t ht; simp at ht) (fun t _ => rfl))
  rintro z ⟨hzc, hzval⟩
  exact ⟨hzc, fun k hk => hzval k (by rw [ntt_NTT_LEN_val]; exact hk)⟩

/-- `ntt::untwist`'s loop: the same push shape as `twist`'s, with three modular
operations in the body instead of two. -/
theorem untwist_loop_spec (src it : alloc.vec.Vec Std.U64) (ninv boff pw mw : Std.U64)
    (n : Std.Usize) (out : alloc.vec.Vec Std.U64) (t : Std.Usize) (h : Magic pw mw)
    (hsrc : Canon pw.val src) (hit : Canon pw.val it)
    (hninv : ninv.val < pw.val) (hboff : boff.val < pw.val)
    (hn : n.val ≤ N) (ht : t.val ≤ n.val) (hlen : out.val.length = t.val)
    (hred : ∀ u ∈ out.val, u.val < pw.val)
    (hval : ∀ k, k < t.val →
      wordAt out k
        = ((wordAt src k * wordAt it k % pw.val) * ninv.val % pw.val + boff.val) % pw.val) :
    ntt.untwist_loop src it ninv boff pw mw n out t
      ⦃ z => z.val.length = n.val ∧ (∀ u ∈ z.val, u.val < pw.val)
             ∧ ∀ k, k < n.val →
                 wordAt z k
                   = ((wordAt src k * wordAt it k % pw.val) * ninv.val % pw.val
                       + boff.val) % pw.val ⦄ := by
  rw [ntt.untwist_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧
      (∀ u ∈ s.1.val, u.val < pw.val) ∧
      ∀ k, k < s.2.val → wordAt s.1 k
        = ((wordAt src k * wordAt it k % pw.val) * ninv.val % pw.val + boff.val) % pw.val)
  · rintro ⟨o1, t1⟩ ⟨ht1, hlen1, hred1, hval1⟩
    dsimp only at ht1 hlen1 hred1 hval1
    simp only [ntt.untwist_loop.body]
    by_cases hlt : t1 < n
    · rw [if_pos hlt]
      have hisrc : t1.val < src.val.length := by rw [hsrc.1]; scalar_tac
      have hiit : t1.val < it.val.length := by rw [hit.1]; scalar_tac
      have hcap : o1.val.length < Usize.max := by scalar_tac
      step as ⟨i, hi⟩
      have hil : i.val < pw.val := hi ▸ hsrc.2 _ (List.getElem_mem hisrc)
      step as ⟨i1, hi1⟩
      have hi1l : i1.val < pw.val := hi1 ▸ hit.2 _ (List.getElem_mem hiit)
      step with aux_mul_lt i i1 pw mw h hil hi1l as ⟨u, huv, hul⟩
      step with aux_mul_lt u ninv pw mw h hul hninv as ⟨s, hsv, hsl⟩
      step with aux_add_lt s boff pw h.lt_pow hsl hboff as ⟨i2, hi2v, hi2l⟩
      step as ⟨o2, ho2⟩
      step as ⟨t2, ht2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, List.length_append, hlen1]; scalar_tac
      · intro w hw
        rw [ho2] at hw
        rcases List.mem_append.mp hw with hh | hh
        · exact hred1 w hh
        · rw [List.mem_singleton.mp hh]; exact hi2l
      · intro k hk
        rw [ht2] at hk
        rcases Nat.lt_or_ge k t1.val with hklt | hkge
        · rw [wordAt_pushed_lt ho2 (by omega), hval1 k hklt]
        · have hkeq : k = o1.val.length := by omega
          rw [hkeq, wordAt_pushed_eq ho2, hlen1, hi2v, hsv, huv,
            wordAt_of_lt hisrc, wordAt_of_lt hiit, hi, hi1]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : t1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hred1, by rw [← heq]; exact hval1⟩
  · exact ⟨ht, hlen, hred, hval⟩

theorem untwist_spec (src it : alloc.vec.Vec Std.U64) (ninv boff pw mw : Std.U64)
    (h : Magic pw mw) (hsrc : Canon pw.val src) (hit : Canon pw.val it)
    (hninv : ninv.val < pw.val) (hboff : boff.val < pw.val) :
    ntt.untwist src it ninv boff pw mw
      ⦃ z => Canon pw.val z
             ∧ ∀ t, t < N →
                 wordAt z t
                   = ((wordAt src t * wordAt it t % pw.val) * ninv.val % pw.val
                       + boff.val) % pw.val ⦄ := by
  rw [ntt.untwist]
  simp only [alloc.vec.Vec.with_capacity]
  apply spec_mono (untwist_loop_spec src it ninv boff pw mw ntt.NTT_LEN
    (alloc.vec.Vec.new Std.U64) 0#usize h hsrc hit hninv hboff
    (by simp) (by simp) (by simp) (by intro u hu; simp at hu)
    (by intro k hk; simp at hk))
  rintro z ⟨hzlen, hzred, hzval⟩
  refine ⟨⟨by rw [hzlen, ntt_NTT_LEN_val], hzred⟩, ?_⟩
  intro k hk
  exact hzval k (by rw [ntt_NTT_LEN_val]; exact hk)

/-! ## `ntt::dit_stage`

The mirror of `NttStage`'s DIF stage, loop for loop. The one asymmetry is that the
twiddle product is computed twice, once in each inner loop -- a deliberate
performance choice (`ntt.rs`, module header), and on the proof side simply two
occurrences of the same expression.
-/

theorem dit_stage_loop0_loop0_spec (src dst tw : alloc.vec.Vec Std.U64)
    (pw mw : Std.U64) (half step start j e : Std.Usize) (h : Magic pw mw)
    (hsrc : Canon pw.val src) (hdst : Canon pw.val dst) (htw : Canon pw.val tw)
    (hblk : start.val + 2 * half.val ≤ N) (hj : j.val ≤ half.val)
    (hev : e.val = j.val * step.val) (hstep : 0 < step.val)
    (hebd : half.val * step.val ≤ N)
    (hwrit : ∀ t, t < j.val →
      wordAt dst (start.val + t)
        = (wordAt src (start.val + t)
            + wordAt src (start.val + t + half.val) * wordAt tw (t * step.val) % pw.val)
          % pw.val) :
    ntt.dit_stage_loop0_loop0 src dst tw pw mw half step start j e
      ⦃ z => Canon pw.val z
             ∧ (∀ t, t < half.val →
                 wordAt z (start.val + t)
                   = (wordAt src (start.val + t)
                       + wordAt src (start.val + t + half.val)
                         * wordAt tw (t * step.val) % pw.val) % pw.val)
             ∧ (∀ k, (k < start.val ∨ start.val + half.val ≤ k) →
                 wordAt z k = wordAt dst k) ⦄ := by
  have hp : pw.val < 2 ^ 32 := h.lt_pow
  have hppos : 0 < pw.val := h.pos
  rw [ntt.dit_stage_loop0_loop0]
  apply loop.spec_decr_nat (fun s => half.val - s.2.1.val)
    (fun s => s.2.1.val ≤ half.val ∧ s.2.2.val = s.2.1.val * step.val
      ∧ Canon pw.val s.1
      ∧ (∀ t, t < s.2.1.val →
          wordAt s.1 (start.val + t)
            = (wordAt src (start.val + t)
                + wordAt src (start.val + t + half.val)
                  * wordAt tw (t * step.val) % pw.val) % pw.val)
      ∧ (∀ k, (k < start.val ∨ start.val + half.val ≤ k) →
          wordAt s.1 k = wordAt dst k))
  · rintro ⟨dd, jj, ee⟩ ⟨hjj, hev1, hcd, hw, hfr⟩
    dsimp only at hjj hev1 hcd hw hfr
    simp only [ntt.dit_stage_loop0_loop0.body]
    by_cases hlt : jj < half
    · rw [if_pos hlt]
      have hjjlt : jj.val < half.val := by scalar_tac
      have hsl : src.val.length = N := hsrc.1
      have hdl : dd.val.length = N := hcd.1
      have htl : tw.val.length = N := htw.1
      step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      have hi1b : i1.val < src.val.length := by rw [hsl, hi1, hi]; omega
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = wordAt src (start.val + jj.val + half.val) := by
        rw [hi2, ← wordAt_of_lt (v := src) (t := i1.val) hi1b, hi1, hi]
      have heeb : ee.val < tw.val.length := by
        have hmul : jj.val * step.val < half.val * step.val :=
          Nat.mul_lt_mul_of_pos_right hjjlt hstep
        rw [htl]; omega
      step as ⟨i3, hi3⟩
      have hi3v : i3.val = wordAt tw (jj.val * step.val) := by
        rw [hi3, ← wordAt_of_lt (v := tw) (t := ee.val) heeb, hev1]
      have h2lt : i2.val < pw.val := by rw [hi2v]; exact wordAt_lt hsrc hppos _
      have h3lt : i3.val < pw.val := by rw [hi3v]; exact wordAt_lt htw hppos _
      step with aux_mul_lt i2 i3 pw mw h h2lt h3lt as ⟨v, hvv, hvlt⟩
      have hib : i.val < src.val.length := by rw [hsl, hi]; omega
      step as ⟨i4, hi4⟩
      have hi4v : i4.val = wordAt src (start.val + jj.val) := by
        rw [hi4, ← wordAt_of_lt (v := src) (t := i.val) hib, hi]
      have h4lt : i4.val < pw.val := by rw [hi4v]; exact wordAt_lt hsrc hppos _
      step with aux_add_lt i4 v pw hp h4lt hvlt as ⟨i5, hi5v, hi5lt⟩
      have hidb : i.val < dd.val.length := by rw [hdl, hi]; omega
      have hebnd : ee.val + step.val ≤ N := by
        have hh1 : (jj.val + 1) * step.val ≤ half.val * step.val :=
          Nat.mul_le_mul_right _ (by omega)
        have hh2 : (jj.val + 1) * step.val = jj.val * step.val + step.val := by ring
        omega
      step as ⟨elem, back, helem, hback⟩
      rw [hback]
      step as ⟨j1, hj1⟩
      step as ⟨e1, he1⟩
      refine ⟨by scalar_tac, by rw [he1, hev1, hj1]; ring, Canon_set hcd hi5lt, ?_, ?_,
        by scalar_tac⟩
      · intro t ht
        rw [hj1] at ht
        rcases Nat.lt_or_ge t jj.val with htlt | htge
        · rw [wordAt_set_ne (by omega)]
          exact hw t htlt
        · have hteq : t = jj.val := by omega
          subst hteq
          rw [← hi, wordAt_set_eq hidb, hi5v, hvv, hi2v, hi3v, hi4v, hi]
      · intro k hk
        rw [wordAt_set_ne (by omega)]
        exact hfr k hk
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = half.val := by scalar_tac
      refine ⟨hcd, ?_, hfr⟩
      intro t ht
      exact hw t (by rw [heq]; exact ht)
  · exact ⟨hj, hev, hdst, hwrit, fun k _ => rfl⟩

theorem dit_stage_loop0_loop1_spec (src dst tw : alloc.vec.Vec Std.U64)
    (pw mw : Std.U64) (half step start i e : Std.Usize) (h : Magic pw mw)
    (hsrc : Canon pw.val src) (hdst : Canon pw.val dst) (htw : Canon pw.val tw)
    (hblk : start.val + 2 * half.val ≤ N) (hi : i.val ≤ half.val)
    (hev : e.val = i.val * step.val) (hstep : 0 < step.val)
    (hebd : half.val * step.val ≤ N)
    (hwrit : ∀ t, t < i.val →
      wordAt dst (start.val + half.val + t)
        = (wordAt src (start.val + t) + pw.val
            - wordAt src (start.val + t + half.val) * wordAt tw (t * step.val) % pw.val)
          % pw.val) :
    ntt.dit_stage_loop0_loop1 src dst tw pw mw half step start i e
      ⦃ z => Canon pw.val z
             ∧ (∀ t, t < half.val →
                 wordAt z (start.val + half.val + t)
                   = (wordAt src (start.val + t) + pw.val
                       - wordAt src (start.val + t + half.val)
                         * wordAt tw (t * step.val) % pw.val) % pw.val)
             ∧ (∀ k, (k < start.val + half.val ∨ start.val + 2 * half.val ≤ k) →
                 wordAt z k = wordAt dst k) ⦄ := by
  have hp : pw.val < 2 ^ 32 := h.lt_pow
  have hppos : 0 < pw.val := h.pos
  rw [ntt.dit_stage_loop0_loop1]
  apply loop.spec_decr_nat (fun s => half.val - s.2.1.val)
    (fun s => s.2.1.val ≤ half.val ∧ s.2.2.val = s.2.1.val * step.val
      ∧ Canon pw.val s.1
      ∧ (∀ t, t < s.2.1.val →
          wordAt s.1 (start.val + half.val + t)
            = (wordAt src (start.val + t) + pw.val
                - wordAt src (start.val + t + half.val)
                  * wordAt tw (t * step.val) % pw.val) % pw.val)
      ∧ (∀ k, (k < start.val + half.val ∨ start.val + 2 * half.val ≤ k) →
          wordAt s.1 k = wordAt dst k))
  · rintro ⟨dd, ii, ee⟩ ⟨hii, hev1, hcd, hw, hfr⟩
    dsimp only at hii hev1 hcd hw hfr
    simp only [ntt.dit_stage_loop0_loop1.body]
    by_cases hlt : ii < half
    · rw [if_pos hlt]
      have hiilt : ii.val < half.val := by scalar_tac
      have hsl : src.val.length = N := hsrc.1
      have hdl : dd.val.length = N := hcd.1
      have htl : tw.val.length = N := htw.1
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      have hi2b : i2.val < src.val.length := by rw [hsl, hi2, hi1]; omega
      step as ⟨i3, hi3⟩
      have hi3v : i3.val = wordAt src (start.val + ii.val + half.val) := by
        rw [hi3, ← wordAt_of_lt (v := src) (t := i2.val) hi2b, hi2, hi1]
      have heeb : ee.val < tw.val.length := by
        have hmul : ii.val * step.val < half.val * step.val :=
          Nat.mul_lt_mul_of_pos_right hiilt hstep
        rw [htl]; omega
      step as ⟨i4, hi4⟩
      have hi4v : i4.val = wordAt tw (ii.val * step.val) := by
        rw [hi4, ← wordAt_of_lt (v := tw) (t := ee.val) heeb, hev1]
      have h3lt : i3.val < pw.val := by rw [hi3v]; exact wordAt_lt hsrc hppos _
      have h4lt : i4.val < pw.val := by rw [hi4v]; exact wordAt_lt htw hppos _
      step with aux_mul_lt i3 i4 pw mw h h3lt h4lt as ⟨v, hvv, hvlt⟩
      have hi1b : i1.val < src.val.length := by rw [hsl, hi1]; omega
      step as ⟨i5, hi5⟩
      have hi5v : i5.val = wordAt src (start.val + ii.val) := by
        rw [hi5, ← wordAt_of_lt (v := src) (t := i1.val) hi1b, hi1]
      have h5lt : i5.val < pw.val := by rw [hi5v]; exact wordAt_lt hsrc hppos _
      step with aux_sub_lt i5 v pw hp h5lt hvlt as ⟨i6, hi6v, hi6lt⟩
      have hebnd : ee.val + step.val ≤ N := by
        have hh1 : (ii.val + 1) * step.val ≤ half.val * step.val :=
          Nat.mul_le_mul_right _ (by omega)
        have hh2 : (ii.val + 1) * step.val = ii.val * step.val + step.val := by ring
        omega
      step as ⟨i7, hi7⟩
      step as ⟨i8, hi8⟩
      have hi8v : i8.val = start.val + half.val + ii.val := by rw [hi8, hi7]
      have hidb : i8.val < dd.val.length := by rw [hdl, hi8v]; omega
      step as ⟨elem, back, helem, hback⟩
      rw [hback]
      step as ⟨i9, hi9⟩
      step as ⟨e1, he1⟩
      refine ⟨by scalar_tac, by rw [he1, hev1, hi9]; ring, Canon_set hcd hi6lt, ?_, ?_,
        by scalar_tac⟩
      · intro t ht
        rw [hi9] at ht
        rcases Nat.lt_or_ge t ii.val with htlt | htge
        · rw [wordAt_set_ne (by omega)]
          exact hw t htlt
        · have hteq : t = ii.val := by omega
          subst hteq
          rw [← hi8v, wordAt_set_eq hidb, hi6v, hvv, hi3v, hi4v, hi5v]
      · intro k hk
        rw [wordAt_set_ne (by omega)]
        exact hfr k hk
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ii.val = half.val := by scalar_tac
      refine ⟨hcd, ?_, hfr⟩
      intro t ht
      exact hw t (by rw [heq]; exact ht)
  · exact ⟨hi, hev, hdst, hwrit, fun k _ => rfl⟩

/-- The three numeric facts about `len = 2 ^ (k+1)` dividing `N = 1024` that the
stage's parameter bookkeeping needs: the block length divides the buffer, the
twiddle stride is positive, and `half · step` is exactly `N`. The mirror of
`NttStage`'s `difParams`, restated rather than shared because that one is
`private` to its file. -/
private theorem ditParams (k : ℕ) (hk : k < 10) :
    2 ^ (k + 1) ∣ N ∧ 0 < 2 * (N / 2 ^ (k + 1))
      ∧ 2 ^ k * (2 * (N / 2 ^ (k + 1))) = N := by
  have hN : N = 2 ^ 10 := by norm_num
  have hdiv : N / 2 ^ (k + 1) = 2 ^ (9 - k) := by
    rw [hN, Nat.pow_div (by omega) (by norm_num)]
    congr 1
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hN]; exact pow_dvd_pow 2 (by omega)
  · rw [hdiv]; positivity
  · rw [hdiv]
    have h9 : k + (9 - k) = 9 := by omega
    calc 2 ^ k * (2 * 2 ^ (9 - k)) = 2 * (2 ^ k * 2 ^ (9 - k)) := by ring
      _ = 2 * 2 ^ (k + (9 - k)) := by rw [pow_add]
      _ = 2 * 2 ^ 9 := by rw [h9]
      _ = N := by norm_num

/-- The outer loop of `dit_stage`: block starts below `start` already hold the
stage's value, and the loop finishes the buffer. The mirror of
`NttStage.dif_stage_loop0_spec`. -/
theorem dit_stage_loop0_spec (src dst tw : alloc.vec.Vec Std.U64) (len : Std.Usize)
    (pw mw : Std.U64) (half step start : Std.Usize) (h : Magic pw mw)
    (hsrc : Canon pw.val src) (hdst : Canon pw.val dst) (htw : Canon pw.val tw)
    (hlen : len.val = 2 * half.val) (hhalf : 0 < half.val) (hdvd : len.val ∣ N)
    (hstep : 0 < step.val) (hebd : half.val * step.val ≤ N)
    (hstart : start.val ≤ N) (hmod : start.val % len.val = 0)
    (hval : ∀ t, t < start.val →
      wordAt dst t = ditWord pw.val half.val step.val (wordAt src) (wordAt tw) t) :
    ntt.dit_stage_loop0 src dst len tw pw mw ntt.NTT_LEN half step start
      ⦃ z => Canon pw.val z
             ∧ ∀ t, t < N →
                 wordAt z t = ditWord pw.val half.val step.val (wordAt src) (wordAt tw) t ⦄ := by
  have hp : pw.val < 2 ^ 32 := h.lt_pow
  have hppos : 0 < pw.val := h.pos
  rw [ntt.dit_stage_loop0]
  apply loop.spec_decr_nat (fun s => N - s.2.val)
    (fun s => s.2.val ≤ N ∧ s.2.val % len.val = 0 ∧ Canon pw.val s.1
      ∧ (∀ t, t < s.2.val →
          wordAt s.1 t = ditWord pw.val half.val step.val (wordAt src) (wordAt tw) t))
  · rintro ⟨d, ss⟩ ⟨hss, hmod1, hcd, hval1⟩
    dsimp only at hss hmod1 hcd hval1
    simp only [ntt.dit_stage_loop0.body]
    by_cases hlt : ss < ntt.NTT_LEN
    · rw [if_pos hlt]
      have hsslt : ss.val < N := by scalar_tac
      have hlenpos : 0 < len.val := by omega
      have hblk : ss.val + len.val ≤ N := by
        obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hmod1
        obtain ⟨m0, hm0⟩ := hdvd
        have hcm : c < m0 := by
          have hlm : len.val * c < len.val * m0 := by rw [← hc, ← hm0]; exact hsslt
          exact Nat.lt_of_mul_lt_mul_left hlm
        have hle : len.val * (c + 1) ≤ len.val * m0 :=
          Nat.mul_le_mul (Nat.le_refl _) (by omega)
        rw [Nat.mul_add, Nat.mul_one] at hle
        omega
      have hblk2 : ss.val + 2 * half.val ≤ N := by omega
      have hmm : ∀ t, ss.val ≤ t → t < ss.val + len.val → t % len.val = t - ss.val := by
        intro t ha hb
        obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hmod1
        have ht : t = (t - ss.val) + len.val * c := by omega
        conv_lhs => rw [ht]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      step with dit_stage_loop0_loop0_spec src d tw pw mw half step ss 0#usize 0#usize
        h hsrc hcd htw hblk2 (by simp) (by simp) hstep hebd
        (by intro t ht; simp at ht) as ⟨d1, hc1, hwr1, hfr1⟩
      step with dit_stage_loop0_loop1_spec src d1 tw pw mw half step ss 0#usize 0#usize
        h hsrc hc1 htw hblk2 (by simp) (by simp) hstep hebd
        (by intro t ht; simp at ht) as ⟨d2, hc2, hwr2, hfr2⟩
      step as ⟨ss1, hss1⟩
      refine ⟨by omega, ?_, hc2, ?_, by omega⟩
      · rw [hss1, Nat.add_mod_right, hmod1]
      · intro t ht
        rw [hss1] at ht
        rcases Nat.lt_or_ge t ss.val with h1 | h1
        · rw [hfr2 t (Or.inl (by omega)), hfr1 t (Or.inl (by omega))]
          exact hval1 t h1
        · have hmd : t % (2 * half.val) = t - ss.val := by
            rw [← hlen]; exact hmm t h1 (by omega)
          rcases Nat.lt_or_ge t (ss.val + half.val) with h2 | h2
          · have hr : ss.val + (t - ss.val) = t := by omega
            have e1 := hwr1 (t - ss.val) (by omega)
            rw [hr] at e1
            rw [hfr2 t (Or.inl (by omega)), e1]
            unfold ditWord
            rw [if_pos (by rw [hmd]; omega), hmd]
          · have hr2 : ss.val + half.val + (t - ss.val - half.val) = t := by omega
            have e2 := hwr2 (t - ss.val - half.val) (by omega)
            rw [hr2] at e2
            have a1 : ss.val + (t - ss.val - half.val) = t - half.val := by omega
            rw [a1] at e2
            have a2 : t - half.val + half.val = t := by omega
            rw [a2] at e2
            have a3 : t - ss.val - half.val = t % (2 * half.val) - half.val := by
              rw [hmd]
            rw [a3] at e2
            rw [e2]
            unfold ditWord
            rw [if_neg (by rw [hmd]; omega)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : ss.val = N := by scalar_tac
      exact ⟨hcd, fun t ht => hval1 t (by rw [heq]; exact ht)⟩
  · exact ⟨hstart, hmod, hdst, hval⟩

theorem dit_stage_spec (src dst tw : alloc.vec.Vec Std.U64) (len : Std.Usize)
    (pw mw : Std.U64) (h : Magic pw mw) (k : ℕ) (hk : k < 10)
    (hlen : len.val = 2 ^ (k + 1))
    (hsrc : Canon pw.val src) (hdst : Canon pw.val dst) (htw : Canon pw.val tw) :
    ntt.dit_stage src dst len tw pw mw
      ⦃ z => Canon pw.val z
             ∧ ∀ t, t < N →
                 wordAt z t = ditWord pw.val (2 ^ k) (2 * (N / 2 ^ (k + 1)))
                   (wordAt src) (wordAt tw) t ⦄ := by
  obtain ⟨hdvd, hsteppos, hprod⟩ := ditParams k hk
  have hlen2 : len.val = 2 * 2 ^ k := by rw [hlen]; ring
  have hlne : len.val ≠ 0 := by omega
  rw [ntt.dit_stage]
  step as ⟨hf, hhf⟩
  have hhfv : hf.val = 2 ^ k := by rw [hhf, hlen2]; omega
  step as ⟨qq, hqq⟩
  have hqqv : qq.val = N / 2 ^ (k + 1) := by rw [hqq, ntt_NTT_LEN_val, hlen]
  have hqqle : qq.val ≤ N := by rw [hqqv]; exact Nat.div_le_self _ _
  step as ⟨st, hst⟩
  have hstv : st.val = 2 * (N / 2 ^ (k + 1)) := by rw [hst, hqqv]
  rw [← hhfv, ← hstv]
  exact dit_stage_loop0_spec src dst tw len pw mw hf st 0#usize h hsrc hdst htw
    (by rw [hlen2, hhfv]) (by rw [hhfv]; positivity) (by rw [hlen]; exact hdvd)
    (by rw [hstv]; exact hsteppos)
    (by rw [hhfv, hstv]; exact Nat.le_of_eq hprod)
    (by simp) (by simp) (by intro t ht; simp at ht)

/-- The word-level DIT stage is the ring-level one, given a table of powers of
`ψ` and `ω = ψ²`. Needs canonicality for the same reason
`NttStage.difWord_cast` does: the `+ p - x` numerator is a truncating `ℕ`
subtraction, and only `x < p` makes it the subtraction it is meant to be. -/
-- The doc-comment above it in NttTransform.lean is unchanged and not repeated.

theorem ditWord_cast (p half step : ℕ) (psi : ZMod p) (sw tww : ℕ → ℕ)
    (htw : ∀ e, ((tww e : ℕ) : ZMod p) = psi ^ e) (hsw : ∀ u, sw u < p)
    (_htwl : ∀ e, tww e < p) (t : ℕ) :
    ((ditWord p half (2 * step) sw tww t : ℕ) : ZMod p)
      = NttMath.ditStage half step (psi ^ 2) (fun u => ((sw u : ℕ) : ZMod p)) t := by
  have hppos : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) (hsw 0)
  unfold ditWord NttMath.ditStage
  by_cases hc : t % (2 * half) < half
  · rw [if_pos hc, if_pos hc, ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_mod,
      Nat.cast_mul, htw, ← pow_mul]
    congr 2
    ring
  · rw [if_neg hc, if_neg hc, ZMod.natCast_mod]
    have hlt : sw t * tww ((t % (2 * half) - half) * (2 * step)) % p < p :=
      Nat.mod_lt _ hppos
    rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero,
      ZMod.natCast_mod, Nat.cast_mul, htw, ← pow_mul]
    congr 2
    ring

-- Insert after `ditWord_cast`, before the `## The two transforms` header.

/-! ## Bookkeeping for the two transform loops

The two loops below compose the ten stages, and three kinds of bookkeeping stand
between a stage's specification and a whole run:

* the code's twiddle stride `2 · (N / 2^(k+1))` has to be recognised as
  `2 · 2^(9-k)`, which is what [`NttStage.difWord_cast`] and [`ditWord_cast`] are
  stated against ([`N_div_pow`]);
* those two lemmas want a table that is `ψ^e` at *every* exponent, while `Canon`
  says nothing above `N`. Every table index a stage reads is below `N`
  ([`tw_idx_lt`]), so the read is first moved onto the total table
  [`psiRep`] ([`difWord_tw_congr`], [`ditWord_tw_congr`]);
* a stage spec constrains its output only below `N`, and a run applied to two
  buffers agreeing only below `N` need not agree anywhere -- unless one knows
  that a stage reads only below `N`, which is [`stage_idx_lt`] and the
  congruence lemmas built on it.
-/

/-- The code's twiddle stride, in closed form. -/
private theorem N_div_pow (k : ℕ) (hk : k < 10) : N / 2 ^ (k + 1) = 2 ^ (9 - k) := by
  have hN : N = 2 ^ 10 := by norm_num
  rw [hN, Nat.pow_div (by omega) (by norm_num)]
  congr 1
  omega

/-- Every twiddle index a stage at block length `2^(k+1)` reads is below `N`:
the index is `r · 2·(N/2^(k+1))` with `r < 2^k`, and `2^k · 2·(N/2^(k+1)) = N`. -/
private theorem tw_idx_lt (k r : ℕ) (hk : k < 10) (hr : r < 2 ^ k) :
    r * (2 * (N / 2 ^ (k + 1))) < N := by
  have hd := N_div_pow k hk
  have hpos : 0 < 2 * (N / 2 ^ (k + 1)) := by rw [hd]; positivity
  have hfull : 2 ^ k * (2 * (N / 2 ^ (k + 1))) = N := by
    rw [hd]
    have h9 : k + (9 - k) = 9 := by omega
    calc 2 ^ k * (2 * 2 ^ (9 - k)) = 2 * (2 ^ k * 2 ^ (9 - k)) := by ring
      _ = 2 * 2 ^ (k + (9 - k)) := by rw [pow_add]
      _ = N := by rw [h9]; norm_num
  calc r * (2 * (N / 2 ^ (k + 1)))
      < 2 ^ k * (2 * (N / 2 ^ (k + 1))) := Nat.mul_lt_mul_of_pos_right hr hpos
    _ = N := hfull

/-- `difWord` at block length `2^(k+1)` reads its table only below `N`. -/
private theorem difWord_tw_congr (p k : ℕ) (hk : k < 10) (sw tww tww' : ℕ → ℕ)
    (hag : ∀ e, e < N → tww e = tww' e) (t : ℕ) :
    difWord p (2 ^ k) (2 * (N / 2 ^ (k + 1))) sw tww t
      = difWord p (2 ^ k) (2 * (N / 2 ^ (k + 1))) sw tww' t := by
  have hmod : t % (2 * 2 ^ k) < 2 * 2 ^ k := Nat.mod_lt _ (by positivity)
  unfold difWord
  by_cases hc : t % (2 * 2 ^ k) < 2 ^ k
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc, hag _ (tw_idx_lt k _ hk (by omega))]

/-- `ditWord` at block length `2^(k+1)` reads its table only below `N`. -/
private theorem ditWord_tw_congr (p k : ℕ) (hk : k < 10) (sw tww tww' : ℕ → ℕ)
    (hag : ∀ e, e < N → tww e = tww' e) (t : ℕ) :
    ditWord p (2 ^ k) (2 * (N / 2 ^ (k + 1))) sw tww t
      = ditWord p (2 ^ k) (2 * (N / 2 ^ (k + 1))) sw tww' t := by
  have hmod : t % (2 * 2 ^ k) < 2 * 2 ^ k := Nat.mod_lt _ (by positivity)
  unfold ditWord
  by_cases hc : t % (2 * 2 ^ k) < 2 ^ k
  · rw [if_pos hc, if_pos hc, hag _ (tw_idx_lt k _ hk hc)]
  · rw [if_neg hc, if_neg hc, hag _ (tw_idx_lt k _ hk (by omega))]

/-- The twiddle table as a *total* function of the exponent: the canonical
representative of `ψ^e`. A real table is `Canon`, so it carries no information
above `N`, while the two `*Word_cast` lemmas ask for `ψ^e` at every exponent;
this is the table they are applied to, and [`tw_agree`] says it is the real one
wherever the real one is read. -/
private def psiRep {p : ℕ} (psi : ZMod p) (e : ℕ) : ℕ := (psi ^ e).val

private theorem psiRep_cast {p : ℕ} (hp : 0 < p) (psi : ZMod p) (e : ℕ) :
    ((psiRep psi e : ℕ) : ZMod p) = psi ^ e := by
  have : NeZero p := ⟨by omega⟩
  exact ZMod.natCast_rightInverse _

private theorem psiRep_lt {p : ℕ} (hp : 0 < p) (psi : ZMod p) (e : ℕ) :
    psiRep psi e < p := by
  have : NeZero p := ⟨by omega⟩
  exact ZMod.val_lt _

/-- A canonical table of powers of `ψ` *is* [`psiRep`] below `N`: both are
residues below `p` and their casts agree. -/
private theorem tw_agree (pw : Std.U64) (tw : alloc.vec.Vec Std.U64) (hp : 0 < pw.val)
    (htw : Canon pw.val tw) (psi : ZMod pw.val)
    (hpsi : ∀ e, e < N → resK pw.val tw e = psi ^ e) :
    ∀ e, e < N → wordAt tw e = psiRep psi e := by
  intro e he
  have h1 : ((wordAt tw e : ℕ) : ZMod pw.val) = ((psiRep psi e : ℕ) : ZMod pw.val) := by
    rw [psiRep_cast hp psi e]
    exact hpsi e he
  calc wordAt tw e = (((wordAt tw e : ℕ) : ZMod pw.val)).val :=
        (ZMod.val_cast_of_lt (wordAt_lt htw hp e)).symm
    _ = (((psiRep psi e : ℕ) : ZMod pw.val)).val := by rw [h1]
    _ = psiRep psi e := ZMod.val_cast_of_lt (psiRep_lt hp psi e)

/-- A stage reads only inside the buffer: the butterfly partner of an index
below `N` is below `N` too, because the block length divides `N`. -/
private theorem stage_idx_lt (half t : ℕ) (hh : 0 < half) (hdvd : 2 * half ∣ N)
    (ht : t < N) (hc : t % (2 * half) < half) : t + half < N := by
  obtain ⟨m, hm⟩ := hdvd
  set c := 2 * half with hcdef
  have hcpos : 0 < c := by omega
  have hq : c * (t / c) + t % c = t := Nat.div_add_mod t c
  generalize hQ : t / c = q at hq
  have hqm : q < m := by
    have h1 : c * q < c * m := by
      have hle : c * q ≤ t := by omega
      have hlt : t < c * m := by omega
      omega
    exact Nat.lt_of_mul_lt_mul_left h1
  have h2 : c * (q + 1) ≤ c * m := Nat.mul_le_mul_left c (by omega)
  have h3 : c * (q + 1) = c * q + c := by ring
  omega

/-- One DIF stage of two buffers that agree below `N` agrees below `N`. -/
private theorem difStage_congr {R : Type*} [CommRing R] (half step : ℕ) (om : R)
    (hh : 0 < half) (hdvd : 2 * half ∣ N) (f f' : ℕ → R)
    (hff : ∀ u, u < N → f u = f' u) (t : ℕ) (ht : t < N) :
    NttMath.difStage half step om f t = NttMath.difStage half step om f' t := by
  unfold NttMath.difStage
  by_cases hc : t % (2 * half) < half
  · rw [if_pos hc, if_pos hc, hff t ht, hff (t + half) (stage_idx_lt half t hh hdvd ht hc)]
  · rw [if_neg hc, if_neg hc, hff t ht, hff (t - half) (by omega)]

/-- One DIT stage of two buffers that agree below `N` agrees below `N`. -/
private theorem ditStage_congr {R : Type*} [CommRing R] (half step : ℕ) (omi : R)
    (hh : 0 < half) (hdvd : 2 * half ∣ N) (f f' : ℕ → R)
    (hff : ∀ u, u < N → f u = f' u) (t : ℕ) (ht : t < N) :
    NttMath.ditStage half step omi f t = NttMath.ditStage half step omi f' t := by
  unfold NttMath.ditStage
  by_cases hc : t % (2 * half) < half
  · rw [if_pos hc, if_pos hc, hff t ht, hff (t + half) (stage_idx_lt half t hh hdvd ht hc)]
  · rw [if_neg hc, if_neg hc, hff t ht, hff (t - half) (by omega)]

/-- **A whole DIF run of two buffers that agree below `N` agrees below `N`.**

This is what lets a stage's specification -- which pins the output only below
`N` -- be substituted *inside* a run, and it is the one thing the forward loop's
conserved-value invariant needs beyond [`NttMath.difRun_succ`]. The hypothesis is
that the outermost block length divides `N`; every later one divides that. -/
private theorem difRun_congr {R : Type*} [CommRing R] (om : R) :
    ∀ (k : ℕ), 2 ^ k ∣ N → ∀ (step : ℕ) (f f' : ℕ → R), (∀ u, u < N → f u = f' u) →
      ∀ t, t < N → NttMath.difRun om k step f t = NttMath.difRun om k step f' t := by
  intro k
  induction k with
  | zero => intro _ step f f' hff t ht; simpa using hff t ht
  | succ k ih =>
      intro hdvd step f f' hff t ht
      have hd2 : 2 * 2 ^ k ∣ N := by rw [show 2 * 2 ^ k = 2 ^ (k + 1) by ring]; exact hdvd
      have hdk : (2 : ℕ) ^ k ∣ N := dvd_trans (pow_dvd_pow 2 (Nat.le_succ k)) hdvd
      rw [NttMath.difRun_succ, NttMath.difRun_succ]
      refine ih hdk (step * 2) _ _ ?_ t ht
      intro u hu
      exact difStage_congr (2 ^ k) step om (Nat.two_pow_pos k) hd2 f f' hff u hu

-- The existing section header, kept for orientation, then the forward loop
-- lemma; insert the lemma between the header and `ntt_forward_spec`.

/-! ## The two transforms -/

/-- The forward loop, with the *conserved-value* invariant: whatever remains to
be done to the live buffer is the final answer. `len = 2^k` is the block length
the next stage will use, and `2^(10-k)` the twiddle stride that goes with it, so
one stage turns `difRun … k` into `difRun … (k-1)` of the stage's output and the
invariant is preserved; at `len = 1` the invariant *is* the conclusion.

The buffer swap is why both buffers have to stay `Canon`: the old live buffer
becomes the next stage's scratch. -/

theorem ntt_forward_loop_spec (tw cur tmp : alloc.vec.Vec Std.U64) (pw mw : Std.U64)
    (h : Magic pw mw) (len : Std.Usize) (k : ℕ) (hk : k ≤ 10) (hlen : len.val = 2 ^ k)
    (hcur : Canon pw.val cur) (htmp : Canon pw.val tmp) (htw : Canon pw.val tw)
    (psi : ZMod pw.val) (hpsi : ∀ e, e < N → resK pw.val tw e = psi ^ e)
    (g : ℕ → ZMod pw.val)
    (hinv : ∀ t, t < N →
      NttMath.difRun (psi ^ 2) k (2 ^ (10 - k)) (resK pw.val cur) t = g t) :
    ntt.ntt_forward_loop tw pw mw cur tmp len
      ⦃ z => Canon pw.val z.1 ∧ Canon pw.val z.2
             ∧ ∀ t, t < N → resK pw.val z.1 t = g t ⦄ := by
  have hppos : 0 < pw.val := h.pos
  have hag : ∀ e, e < N → wordAt tw e = psiRep psi e := tw_agree pw tw hppos htw psi hpsi
  rw [ntt.ntt_forward_loop]
  apply loop.spec_decr_nat (fun s => s.2.2.val)
    (fun s => Canon pw.val s.1 ∧ Canon pw.val s.2.1
      ∧ ∃ i, i ≤ 10 ∧ s.2.2.val = 2 ^ i
        ∧ ∀ t, t < N →
            NttMath.difRun (psi ^ 2) i (2 ^ (10 - i)) (resK pw.val s.1) t = g t)
  · rintro ⟨c, d, l⟩ ⟨hc, hd, i, hi, hli, hvi⟩
    dsimp only at hc hd hli hvi
    simp only [ntt.ntt_forward_loop.body]
    by_cases hlt : l > 1#usize
    · rw [if_pos hlt]
      have hl1 : 1 < l.val := by scalar_tac
      have hipos : 0 < i := by
        rcases Nat.eq_zero_or_pos i with rfl | hp
        · rw [pow_zero] at hli; omega
        · exact hp
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj9 : j < 10 := by omega
      step with dif_stage_spec c d tw l pw mw h j hj9 hli hc hd htw as ⟨fl, hcf, hwf⟩
      step as ⟨l2, hl2⟩
      -- the stage, read in the ring
      have hswc : ∀ u, wordAt c u < pw.val := fun u => wordAt_lt hc hppos u
      have hstride : N / 2 ^ (j + 1) = 2 ^ (9 - j) := N_div_pow j hj9
      have hres : ∀ t, t < N →
          resK pw.val fl t
            = NttMath.difStage (2 ^ j) (2 ^ (9 - j)) (psi ^ 2) (resK pw.val c) t := by
        intro t ht
        have h1 : wordAt fl t
            = difWord pw.val (2 ^ j) (2 * (N / 2 ^ (j + 1))) (wordAt c) (psiRep psi) t := by
          rw [hwf t ht]
          exact difWord_tw_congr pw.val j hj9 (wordAt c) (wordAt tw) (psiRep psi) hag t
        rw [resK, h1, hstride]
        exact difWord_cast pw.val (2 ^ j) (2 ^ (9 - j)) psi (wordAt c) (psiRep psi)
          (psiRep_cast hppos psi) hswc t
      -- the invariant, advanced by one stage
      have hnext : ∀ t, t < N →
          NttMath.difRun (psi ^ 2) j (2 ^ (10 - j)) (resK pw.val fl) t = g t := by
        intro t ht
        have hdvd : (2 : ℕ) ^ j ∣ N := by
          rw [show N = 2 ^ 10 by norm_num]
          exact pow_dvd_pow 2 (by omega)
        rw [difRun_congr (psi ^ 2) j hdvd (2 ^ (10 - j)) (resK pw.val fl)
              (NttMath.difStage (2 ^ j) (2 ^ (9 - j)) (psi ^ 2) (resK pw.val c)) hres t ht]
        have he1 : (2 : ℕ) ^ (9 - j) * 2 = 2 ^ (10 - j) := by
          rw [show 10 - j = (9 - j) + 1 by omega, pow_succ]
        have hv := hvi t ht
        rw [show 10 - (j + 1) = 9 - j by omega] at hv
        rw [← hv, NttMath.difRun_succ, he1]
      have hp2 : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by ring
      have h2j : 0 < (2 : ℕ) ^ j := Nat.two_pow_pos j
      have hl2v : l2.val = 2 ^ j := by rw [hl2, hli, hp2]; omega
      exact ⟨hcf, hc, ⟨j, by omega, hl2v, hnext⟩, by rw [hl2v, hli, hp2]; omega⟩
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hl1 : l.val ≤ 1 := by scalar_tac
      have hi0 : i = 0 := by
        rcases Nat.eq_zero_or_pos i with rfl | hp
        · rfl
        · exfalso
          have h2 : (2 : ℕ) ^ 1 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hp
          rw [hli] at hl1
          norm_num at h2
          omega
      subst hi0
      refine ⟨hc, hd, ?_⟩
      intro t ht
      simpa using hvi t ht
  · exact ⟨hcur, htmp, k, hk, hlen, hinv⟩

-- Replaces the `ntt_forward_spec` stub (statement verbatim).

theorem ntt_forward_spec (cur tmp tw : alloc.vec.Vec Std.U64) (pw mw : Std.U64)
    (h : Magic pw mw) (hcur : Canon pw.val cur) (htmp : Canon pw.val tmp)
    (htw : Canon pw.val tw) (psi : ZMod pw.val)
    (hpsi : ∀ e, e < N → resK pw.val tw e = psi ^ e) :
    ntt.ntt_forward cur tmp tw pw mw
      ⦃ z => Canon pw.val z.1 ∧ Canon pw.val z.2
             ∧ ∀ t, t < N →
                 resK pw.val z.1 t
                   = NttMath.difRun (psi ^ 2) 10 1 (resK pw.val cur) t ⦄ := by
  rw [ntt.ntt_forward]
  exact ntt_forward_loop_spec tw cur tmp pw mw h ntt.NTT_LEN 10 (le_refl 10)
    (by rw [ntt_NTT_LEN_val]; norm_num) hcur htmp htw psi hpsi
    (NttMath.difRun (psi ^ 2) 10 1 (resK pw.val cur)) (by intro t _; norm_num)

-- Insert before `ntt_inverse_spec`.

/-- The inverse loop. The orientation of the invariant is the other way round
from the forward one: `ditRun` builds its answer from the innermost stage out,
so after `i` stages the live buffer *is* `ditRun … i` of the original input,
rather than holding an intermediate whose remaining stages are the answer.

`len` doubles, so the measure counts down from `2·NTT_LEN`. -/
theorem ntt_inverse_loop_spec (tw cur tmp : alloc.vec.Vec Std.U64) (pw mw : Std.U64)
    (h : Magic pw mw) (len : Std.Usize) (k : ℕ) (hk : k ≤ 10)
    (hlen : len.val = 2 ^ (k + 1))
    (hcur : Canon pw.val cur) (htmp : Canon pw.val tmp) (htw : Canon pw.val tw)
    (psii : ZMod pw.val) (hpsi : ∀ e, e < N → resK pw.val tw e = psii ^ e)
    (f : ℕ → ZMod pw.val)
    (hinv : ∀ t, t < N →
      resK pw.val cur t = NttMath.ditRun (psii ^ 2) k (2 ^ (10 - k)) f t) :
    ntt.ntt_inverse_loop tw pw mw cur tmp len
      ⦃ z => Canon pw.val z.1 ∧ Canon pw.val z.2
             ∧ ∀ t, t < N →
                 resK pw.val z.1 t = NttMath.ditRun (psii ^ 2) 10 1 f t ⦄ := by
  have hppos : 0 < pw.val := h.pos
  have hag : ∀ e, e < N → wordAt tw e = psiRep psii e := tw_agree pw tw hppos htw psii hpsi
  rw [ntt.ntt_inverse_loop]
  apply loop.spec_decr_nat (fun s => 2 * N - s.2.2.val)
    (fun s => Canon pw.val s.1 ∧ Canon pw.val s.2.1
      ∧ ∃ i, i ≤ 10 ∧ s.2.2.val = 2 ^ (i + 1)
        ∧ ∀ t, t < N →
            resK pw.val s.1 t = NttMath.ditRun (psii ^ 2) i (2 ^ (10 - i)) f t)
  · rintro ⟨c, d, l⟩ ⟨hc, hd, i, hi, hli, hvi⟩
    dsimp only at hc hd hli hvi
    simp only [ntt.ntt_inverse_loop.body]
    have hlpos : 0 < l.val := by rw [hli]; positivity
    have hNv : N = 1024 := rfl
    by_cases hlt : l ≤ ntt.NTT_LEN
    · rw [if_pos hlt]
      have hlN : l.val ≤ N := by scalar_tac
      have hi9 : i < 10 := by
        rcases Nat.lt_or_ge i 10 with hh | hh
        · exact hh
        · exfalso
          have h2 : (2 : ℕ) ^ 11 ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          rw [hli] at hlN
          norm_num at h2
          omega
      step with dit_stage_spec c d tw l pw mw h i hi9 hli hc hd htw as ⟨fl, hcf, hwf⟩
      step as ⟨l2, hl2⟩
      have hswc : ∀ u, wordAt c u < pw.val := fun u => wordAt_lt hc hppos u
      have hstride : N / 2 ^ (i + 1) = 2 ^ (9 - i) := N_div_pow i hi9
      have hres : ∀ t, t < N →
          resK pw.val fl t
            = NttMath.ditStage (2 ^ i) (2 ^ (9 - i)) (psii ^ 2) (resK pw.val c) t := by
        intro t ht
        have h1 : wordAt fl t
            = ditWord pw.val (2 ^ i) (2 * (N / 2 ^ (i + 1))) (wordAt c) (psiRep psii) t := by
          rw [hwf t ht]
          exact ditWord_tw_congr pw.val i hi9 (wordAt c) (wordAt tw) (psiRep psii) hag t
        rw [resK, h1, hstride]
        exact ditWord_cast pw.val (2 ^ i) (2 ^ (9 - i)) psii (wordAt c) (psiRep psii)
          (psiRep_cast hppos psii) hswc (psiRep_lt hppos psii) t
      have hnext : ∀ t, t < N →
          resK pw.val fl t = NttMath.ditRun (psii ^ 2) (i + 1) (2 ^ (10 - (i + 1))) f t := by
        intro t ht
        have hd2 : 2 * 2 ^ i ∣ N := by
          rw [show 2 * 2 ^ i = 2 ^ (i + 1) by ring, show N = 2 ^ 10 by norm_num]
          exact pow_dvd_pow 2 (by omega)
        have he1 : (2 : ℕ) ^ (9 - i) * 2 = 2 ^ (10 - i) := by
          rw [show 10 - i = (9 - i) + 1 by omega, pow_succ]
        rw [hres t ht, show 10 - (i + 1) = 9 - i by omega, NttMath.ditRun_succ, he1]
        exact ditStage_congr (2 ^ i) (2 ^ (9 - i)) (psii ^ 2) (Nat.two_pow_pos i) hd2
          (resK pw.val c) (NttMath.ditRun (psii ^ 2) i (2 ^ (10 - i)) f) hvi t ht
      have hp2 : (2 : ℕ) ^ (i + 1 + 1) = 2 * 2 ^ (i + 1) := by ring
      have hl2v : l2.val = 2 ^ (i + 1 + 1) := by rw [hl2, hli]; ring
      exact ⟨hcf, hc, ⟨i + 1, by omega, hl2v, hnext⟩, by
        rw [hl2v, hp2, ← hli]; omega⟩
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hlN : N < l.val := by scalar_tac
      have hi10 : i = 10 := by
        rcases Nat.lt_or_ge i 10 with hh | hh
        · exfalso
          have h2 : (2 : ℕ) ^ (i + 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
          rw [hli] at hlN
          norm_num at h2
          omega
        · omega
      subst hi10
      refine ⟨hc, hd, ?_⟩
      intro t ht
      simpa using hvi t ht
  · exact ⟨hcur, htmp, k, hk, hlen, hinv⟩

-- Replaces the `ntt_inverse_spec` stub (statement verbatim).

theorem ntt_inverse_spec (cur tmp tw : alloc.vec.Vec Std.U64) (pw mw : Std.U64)
    (h : Magic pw mw) (hcur : Canon pw.val cur) (htmp : Canon pw.val tmp)
    (htw : Canon pw.val tw) (psii : ZMod pw.val)
    (hpsi : ∀ e, e < N → resK pw.val tw e = psii ^ e) :
    ntt.ntt_inverse cur tmp tw pw mw
      ⦃ z => Canon pw.val z.1 ∧ Canon pw.val z.2
             ∧ ∀ t, t < N →
                 resK pw.val z.1 t
                   = NttMath.ditRun (psii ^ 2) 10 1 (resK pw.val cur) t ⦄ := by
  rw [ntt.ntt_inverse]
  exact ntt_inverse_loop_spec tw cur tmp pw mw h 2#usize 0 (by norm_num)
    (by simp) hcur htmp htw psii hpsi (resK pw.val cur) (by intro t _; simp)

end HachiEquiv.NttTransform
