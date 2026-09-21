/-
The **Goldilocks transform** (candidate T27): `NttTransform.lean`'s twiddle
table, twist, DIT stage and the two transform loops, ported to the single
64-bit lane.

As in `GoldStage.lean`, nothing structural is restated: `wordAt`, `Canon`,
`resK`, `difWord`, `ditWord` and the two ring-level bridges `difWord_cast` and
`ditWord_cast` are already generic in the prime and are used here unchanged.
What this file supplies is the arithmetic, which moves from `aux_*_lt` at a
`Magic` prime to `GoldArith`'s specs at `GP`.

The untwist is the one function with no counterpart above: the two-prime path
untwists and then reconstructs with `garner2` against an offset, while one lane
holds the signed coefficient whole and lifts it centred. It is specified in
`GoldDot.lean`, beside the dot that is its only caller.
-/
import NttTransform
import GoldArith
import GoldStage
import GoldFusedStage

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.GoldTransform

open HachiEquiv.NttStage HachiEquiv.NttTransform HachiEquiv.GoldArith
open HachiEquiv.GoldStage

theorem GP_pos : 0 < GP := by norm_num
theorem GP_two_le : 2 ≤ GP := by norm_num

/-! ## `NttTransform`'s private helpers, restated in source order

Every one is already generic in the prime; they are `private` there, so they
are repeated verbatim rather than generalised. -/

theorem wordAt_append_lt {v w : alloc.vec.Vec Std.U64} {x : Std.U64}
    (hw : w.val = v.val ++ [x]) {k : ℕ} (hk : k < v.val.length) :
    wordAt w k = wordAt v k := by
  unfold wordAt
  rw [hw, List.getD_eq_getElem _ _ (by simp only [List.length_append,
      List.length_cons, List.length_nil]; omega),
    List.getD_eq_getElem _ _ hk, List.getElem_append_left hk]

theorem wordAt_append_eq {v w : alloc.vec.Vec Std.U64} {x : Std.U64}
    (hw : w.val = v.val ++ [x]) : wordAt w v.val.length = x.val := by
  unfold wordAt
  rw [hw, List.getD_eq_getElem _ _ (by simp),
    List.getElem_append_right (Nat.le_refl _)]
  simp

theorem getD_append_lt' {α : Type} (l : List α) (x d : α) {j : ℕ}
    (hj : j < l.length) : (l ++ [x]).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hj,
    List.getElem_append_left hj]

theorem getD_append_eq' {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
  simp

/-- Reading a pushed buffer below the join. -/
theorem wordAt_pushed_lt {o o1 : alloc.vec.Vec Std.U64} {x : Std.U64} {j : ℕ}
    (ho : o1.val = o.val ++ [x]) (hj : j < o.val.length) : wordAt o1 j = wordAt o j := by
  unfold wordAt; rw [ho, getD_append_lt' _ _ _ hj]

/-- Reading the pushed entry itself. -/
theorem wordAt_pushed_eq {o o1 : alloc.vec.Vec Std.U64} {x : Std.U64}
    (ho : o1.val = o.val ++ [x]) : wordAt o1 o.val.length = x.val := by
  unfold wordAt; rw [ho, getD_append_eq']

theorem ditParams (k : ℕ) (hk : k < 10) :
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

/-- The code's twiddle stride, in closed form. -/
theorem N_div_pow (k : ℕ) (hk : k < 10) : N / 2 ^ (k + 1) = 2 ^ (9 - k) := by
  have hN : N = 2 ^ 10 := by norm_num
  rw [hN, Nat.pow_div (by omega) (by norm_num)]
  congr 1
  omega

theorem tw_idx_lt (k r : ℕ) (hk : k < 10) (hr : r < 2 ^ k) :
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
theorem difWord_tw_congr (p k : ℕ) (hk : k < 10) (sw tww tww' : ℕ → ℕ)
    (hag : ∀ e, e < N → tww e = tww' e) (t : ℕ) :
    difWord p (2 ^ k) (2 * (N / 2 ^ (k + 1))) sw tww t
      = difWord p (2 ^ k) (2 * (N / 2 ^ (k + 1))) sw tww' t := by
  have hmod : t % (2 * 2 ^ k) < 2 * 2 ^ k := Nat.mod_lt _ (by positivity)
  unfold difWord
  by_cases hc : t % (2 * 2 ^ k) < 2 ^ k
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc, hag _ (tw_idx_lt k _ hk (by omega))]

/-- `ditWord` at block length `2^(k+1)` reads its table only below `N`. -/
theorem ditWord_tw_congr (p k : ℕ) (hk : k < 10) (sw tww tww' : ℕ → ℕ)
    (hag : ∀ e, e < N → tww e = tww' e) (t : ℕ) :
    ditWord p (2 ^ k) (2 * (N / 2 ^ (k + 1))) sw tww t
      = ditWord p (2 ^ k) (2 * (N / 2 ^ (k + 1))) sw tww' t := by
  have hmod : t % (2 * 2 ^ k) < 2 * 2 ^ k := Nat.mod_lt _ (by positivity)
  unfold ditWord
  by_cases hc : t % (2 * 2 ^ k) < 2 ^ k
  · rw [if_pos hc, if_pos hc, hag _ (tw_idx_lt k _ hk hc)]
  · rw [if_neg hc, if_neg hc, hag _ (tw_idx_lt k _ hk (by omega))]

def psiRep {p : ℕ} (psi : ZMod p) (e : ℕ) : ℕ := (psi ^ e).val

theorem psiRep_cast {p : ℕ} (hp : 0 < p) (psi : ZMod p) (e : ℕ) :
    ((psiRep psi e : ℕ) : ZMod p) = psi ^ e := by
  have : NeZero p := ⟨by omega⟩
  exact ZMod.natCast_rightInverse _

theorem psiRep_lt {p : ℕ} (hp : 0 < p) (psi : ZMod p) (e : ℕ) :
    psiRep psi e < p := by
  have : NeZero p := ⟨by omega⟩
  exact ZMod.val_lt _

theorem tw_agree (pw : Std.U64) (tw : alloc.vec.Vec Std.U64) (hp : 0 < pw.val)
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

/-- [`tw_agree`] over a raw modulus. Its proof never mentions `pw` itself,
only `pw.val`, so the `Std.U64` wrapper was never load-bearing — and this lane
has no `Std.U64` prime to instantiate it at. -/
theorem tw_agree' (p : ℕ) (tw : alloc.vec.Vec Std.U64) (hp : 0 < p)
    (htw : Canon p tw) (psi : ZMod p)
    (hpsi : ∀ e, e < N → resK p tw e = psi ^ e) :
    ∀ e, e < N → wordAt tw e = psiRep psi e := by
  intro e he
  have h1 : ((wordAt tw e : ℕ) : ZMod p) = ((psiRep psi e : ℕ) : ZMod p) := by
    rw [psiRep_cast hp psi e]
    exact hpsi e he
  calc wordAt tw e = (((wordAt tw e : ℕ) : ZMod p)).val :=
        (ZMod.val_cast_of_lt (wordAt_lt htw hp e)).symm
    _ = (((psiRep psi e : ℕ) : ZMod p)).val := by rw [h1]
    _ = psiRep psi e := ZMod.val_cast_of_lt (psiRep_lt hp psi e)

theorem stage_idx_lt (half t : ℕ) (hh : 0 < half) (hdvd : 2 * half ∣ N)
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
theorem difStage_congr {R : Type*} [CommRing R] (half step : ℕ) (om : R)
    (hh : 0 < half) (hdvd : 2 * half ∣ N) (f f' : ℕ → R)
    (hff : ∀ u, u < N → f u = f' u) (t : ℕ) (ht : t < N) :
    NttMath.difStage half step om f t = NttMath.difStage half step om f' t := by
  unfold NttMath.difStage
  by_cases hc : t % (2 * half) < half
  · rw [if_pos hc, if_pos hc, hff t ht, hff (t + half) (stage_idx_lt half t hh hdvd ht hc)]
  · rw [if_neg hc, if_neg hc, hff t ht, hff (t - half) (by omega)]

/-- One DIT stage of two buffers that agree below `N` agrees below `N`. -/
theorem ditStage_congr {R : Type*} [CommRing R] (half step : ℕ) (omi : R)
    (hh : 0 < half) (hdvd : 2 * half ∣ N) (f f' : ℕ → R)
    (hff : ∀ u, u < N → f u = f' u) (t : ℕ) (ht : t < N) :
    NttMath.ditStage half step omi f t = NttMath.ditStage half step omi f' t := by
  unfold NttMath.ditStage
  by_cases hc : t % (2 * half) < half
  · rw [if_pos hc, if_pos hc, hff t ht, hff (t + half) (stage_idx_lt half t hh hdvd ht hc)]
  · rw [if_neg hc, if_neg hc, hff t ht, hff (t - half) (by omega)]

theorem difRun_congr {R : Type*} [CommRing R] (om : R) :
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


/-- The push loop, with the running accumulator `cur = ψ^i mod p` alongside the
counter. The invariant is the length, canonicality, the accumulator's value and
the entries written so far. -/
theorem gold_psi_table_loop_spec (psi : Std.U64) (n : Std.Usize)
    (out : alloc.vec.Vec Std.U64) (cur : Std.U64) (i : Std.Usize)
    (hpsi : psi.val < GP)
    (hi : i.val ≤ n.val) (hlen : out.val.length = i.val)
    (hcan : ∀ u ∈ out.val, u.val < GP)
    (hcur : cur.val = psi.val ^ i.val % GP)
    (hvals : ∀ e, e < i.val → wordAt out e = psi.val ^ e % GP) :
    ntt.gold_psi_table_loop psi n out cur i
      ⦃ z => z.val.length = n.val ∧ (∀ u ∈ z.val, u.val < GP)
             ∧ ∀ e, e < n.val → wordAt z e = psi.val ^ e % GP ⦄ := by
  rw [ntt.gold_psi_table_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.2.val)
    (fun s => s.2.2.val ≤ n.val ∧ s.1.val.length = s.2.2.val
      ∧ (∀ u ∈ s.1.val, u.val < GP)
      ∧ s.2.1.val = psi.val ^ s.2.2.val % GP
      ∧ ∀ e, e < s.2.2.val → wordAt s.1 e = psi.val ^ e % GP)
  · rintro ⟨o1, c1, i1⟩ ⟨hi1, hlen1, hcan1, hc1, hv1⟩
    dsimp only at hi1 hlen1 hcan1 hc1 hv1
    simp only [ntt.gold_psi_table_loop.body]
    by_cases hlt : i1 < n
    · rw [if_pos hlt]
      have hclt : c1.val < GP := by rw [hc1]; exact Nat.mod_lt _ GP_pos
      step as ⟨o2, ho2⟩
      step with gold_mul_spec c1 psi as ⟨c2, hc2, hc2lt⟩
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
theorem gold_psi_table_spec (psi : Std.U64) (hpsi : psi.val < GP) :
    ntt.gold_psi_table psi
      ⦃ z => Canon GP z ∧ ∀ e, e < N → wordAt z e = psi.val ^ e % GP ⦄ := by
  have h1 : 1 < GP := by have := GP_two_le; omega
  rw [ntt.gold_psi_table]
  simp only [alloc.vec.Vec.with_capacity]
  apply spec_mono (gold_psi_table_loop_spec psi ntt.NTT_LEN
    (alloc.vec.Vec.new Std.U64) 1#u64 0#usize hpsi (by simp) (by simp)
    (by intro u hu; simp at hu)
    (by show (1 : ℕ) = psi.val ^ 0 % GP
        rw [pow_zero, Nat.mod_eq_of_lt h1])
    (by intro e he; simp at he))
  rintro z ⟨hzlen, hzcan, hzvals⟩
  refine ⟨⟨?_, hzcan⟩, ?_⟩
  · rw [hzlen, ntt_NTT_LEN_val]
  · intro e he
    exact hzvals e (by rw [ntt_NTT_LEN_val]; exact he)

/-- The table read as `ZMod p`, which is the form every stage spec wants. -/
theorem gold_psi_table_cast (psi : Std.U64) (hpsi : psi.val < GP) :
    ntt.gold_psi_table psi
      ⦃ z => Canon GP z
             ∧ ∀ e, e < N → resK GP z e = ((psi.val : ℕ) : ZMod GP) ^ e ⦄ := by
  apply spec_mono (gold_psi_table_spec psi hpsi)
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



/-- `ntt::twist`'s loop: `out` grows by one reduced-and-scaled entry per step, so
its length *is* the counter and its entries below the counter hold the product.
`v` is only assumed long enough -- not canonical -- because the body reduces
every word it reads before multiplying. -/
theorem gold_twist_loop_spec (v pt : alloc.vec.Vec Std.U64) (n : Std.Usize)
    (out : alloc.vec.Vec Std.U64) (t : Std.Usize) 
    (hnv : n.val ≤ v.val.length) (hnp : n.val ≤ pt.val.length)
    (hptr : ∀ u ∈ pt.val, u.val < GP)
    (ht : t.val ≤ n.val) (hlen : out.val.length = t.val)
    (hred : ∀ u ∈ out.val, u.val < GP)
    (hval : ∀ k, k < t.val →
      wordAt out k = (wordAt v k * wordAt pt k) % GP) :
    ntt.gold_twist_loop v pt n out t
      ⦃ z => z.val.length = n.val ∧ (∀ u ∈ z.val, u.val < GP)
             ∧ ∀ k, k < n.val →
                 wordAt z k = (wordAt v k * wordAt pt k) % GP ⦄ := by
  rw [ntt.gold_twist_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧
      (∀ u ∈ s.1.val, u.val < GP) ∧
      ∀ k, k < s.2.val → wordAt s.1 k = (wordAt v k * wordAt pt k) % GP)
  · rintro ⟨o1, t1⟩ ⟨ht1, hlen1, hred1, hval1⟩
    dsimp only at ht1 hlen1 hred1 hval1
    simp only [ntt.gold_twist_loop.body]
    by_cases hlt : t1 < n
    · rw [if_pos hlt]
      have hiv : t1.val < v.val.length := by scalar_tac
      have hip : t1.val < pt.val.length := by scalar_tac
      have hcap : o1.val.length < Usize.max := by scalar_tac
      step as ⟨i, hi⟩
      step as ⟨i2, hi2⟩
      have hi2l : i2.val < GP := hi2 ▸ hptr _ (List.getElem_mem hip)
      step with gold_mul_spec i i2 as ⟨i3, hi3v, hi3l⟩
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
          rw [hkeq, wordAt_pushed_eq ho2, hlen1, hi3v,
            wordAt_of_lt hiv, wordAt_of_lt hip, hi, hi2]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : t1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq], hred1, by rw [← heq]; exact hval1⟩
  · exact ⟨ht, hlen, hred, hval⟩

theorem gold_twist_spec (v pt : alloc.vec.Vec Std.U64) 
    (hv : v.val.length = N) (hpt : Canon GP pt) :
    ntt.gold_twist v pt
      ⦃ z => Canon GP z
             ∧ ∀ t, t < N →
                 wordAt z t = (wordAt v t * wordAt pt t) % GP ⦄ := by
  rw [ntt.gold_twist]
  simp only [alloc.vec.Vec.with_capacity]
  apply spec_mono (gold_twist_loop_spec v pt ntt.NTT_LEN
    (alloc.vec.Vec.new Std.U64) 0#usize
    (by simp [hv]) (by simp [hpt.1]) hpt.2
    (by simp) (by simp) (by intro u hu; simp at hu) (by intro k hk; simp at hk))
  rintro z ⟨hzlen, hzred, hzval⟩
  refine ⟨⟨by rw [hzlen, ntt_NTT_LEN_val], hzred⟩, ?_⟩
  intro k hk
  exact hzval k (by rw [ntt_NTT_LEN_val]; exact hk)

theorem gold_dit_stage_loop0_loop0_spec (src dst tw : alloc.vec.Vec Std.U64)
    (half step start j e : Std.Usize) 
    (hsrc : Canon GP src) (hdst : Canon GP dst) (htw : Canon GP tw)
    (hblk : start.val + 2 * half.val ≤ N) (hj : j.val ≤ half.val)
    (hev : e.val = j.val * step.val) (hstep : 0 < step.val)
    (hebd : half.val * step.val ≤ N)
    (hwrit : ∀ t, t < j.val →
      wordAt dst (start.val + t)
        = (wordAt src (start.val + t)
            + wordAt src (start.val + t + half.val) * wordAt tw (t * step.val) % GP)
          % GP) :
    ntt.gold_dit_stage_loop0_loop0 src dst tw half step start j e
      ⦃ z => Canon GP z
             ∧ (∀ t, t < half.val →
                 wordAt z (start.val + t)
                   = (wordAt src (start.val + t)
                       + wordAt src (start.val + t + half.val)
                         * wordAt tw (t * step.val) % GP) % GP)
             ∧ (∀ k, (k < start.val ∨ start.val + half.val ≤ k) →
                 wordAt z k = wordAt dst k) ⦄ := by
  rw [ntt.gold_dit_stage_loop0_loop0]
  apply loop.spec_decr_nat (fun s => half.val - s.2.1.val)
    (fun s => s.2.1.val ≤ half.val ∧ s.2.2.val = s.2.1.val * step.val
      ∧ Canon GP s.1
      ∧ (∀ t, t < s.2.1.val →
          wordAt s.1 (start.val + t)
            = (wordAt src (start.val + t)
                + wordAt src (start.val + t + half.val)
                  * wordAt tw (t * step.val) % GP) % GP)
      ∧ (∀ k, (k < start.val ∨ start.val + half.val ≤ k) →
          wordAt s.1 k = wordAt dst k))
  · rintro ⟨dd, jj, ee⟩ ⟨hjj, hev1, hcd, hw, hfr⟩
    dsimp only at hjj hev1 hcd hw hfr
    simp only [ntt.gold_dit_stage_loop0_loop0.body]
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
      have h2lt : i2.val < GP := by rw [hi2v]; exact wordAt_lt hsrc GP_pos _
      have h3lt : i3.val < GP := by rw [hi3v]; exact wordAt_lt htw GP_pos _
      step with gold_mul_spec i2 i3 as ⟨v, hvv, hvlt⟩
      have hib : i.val < src.val.length := by rw [hsl, hi]; omega
      step as ⟨i4, hi4⟩
      have hi4v : i4.val = wordAt src (start.val + jj.val) := by
        rw [hi4, ← wordAt_of_lt (v := src) (t := i.val) hib, hi]
      have h4lt : i4.val < GP := by rw [hi4v]; exact wordAt_lt hsrc GP_pos _
      step with gold_add_spec i4 v h4lt hvlt as ⟨i5, hi5v, hi5lt⟩
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

theorem gold_dit_stage_loop0_loop1_spec (src dst tw : alloc.vec.Vec Std.U64)
    (half step start i e : Std.Usize) 
    (hsrc : Canon GP src) (hdst : Canon GP dst) (htw : Canon GP tw)
    (hblk : start.val + 2 * half.val ≤ N) (hi : i.val ≤ half.val)
    (hev : e.val = i.val * step.val) (hstep : 0 < step.val)
    (hebd : half.val * step.val ≤ N)
    (hwrit : ∀ t, t < i.val →
      wordAt dst (start.val + half.val + t)
        = (wordAt src (start.val + t) + GP
            - wordAt src (start.val + t + half.val) * wordAt tw (t * step.val) % GP)
          % GP) :
    ntt.gold_dit_stage_loop0_loop1 src dst tw half step start i e
      ⦃ z => Canon GP z
             ∧ (∀ t, t < half.val →
                 wordAt z (start.val + half.val + t)
                   = (wordAt src (start.val + t) + GP
                       - wordAt src (start.val + t + half.val)
                         * wordAt tw (t * step.val) % GP) % GP)
             ∧ (∀ k, (k < start.val + half.val ∨ start.val + 2 * half.val ≤ k) →
                 wordAt z k = wordAt dst k) ⦄ := by
  rw [ntt.gold_dit_stage_loop0_loop1]
  apply loop.spec_decr_nat (fun s => half.val - s.2.1.val)
    (fun s => s.2.1.val ≤ half.val ∧ s.2.2.val = s.2.1.val * step.val
      ∧ Canon GP s.1
      ∧ (∀ t, t < s.2.1.val →
          wordAt s.1 (start.val + half.val + t)
            = (wordAt src (start.val + t) + GP
                - wordAt src (start.val + t + half.val)
                  * wordAt tw (t * step.val) % GP) % GP)
      ∧ (∀ k, (k < start.val + half.val ∨ start.val + 2 * half.val ≤ k) →
          wordAt s.1 k = wordAt dst k))
  · rintro ⟨dd, ii, ee⟩ ⟨hii, hev1, hcd, hw, hfr⟩
    dsimp only at hii hev1 hcd hw hfr
    simp only [ntt.gold_dit_stage_loop0_loop1.body]
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
      have h3lt : i3.val < GP := by rw [hi3v]; exact wordAt_lt hsrc GP_pos _
      have h4lt : i4.val < GP := by rw [hi4v]; exact wordAt_lt htw GP_pos _
      step with gold_mul_spec i3 i4 as ⟨v, hvv, hvlt⟩
      have hi1b : i1.val < src.val.length := by rw [hsl, hi1]; omega
      step as ⟨i5, hi5⟩
      have hi5v : i5.val = wordAt src (start.val + ii.val) := by
        rw [hi5, ← wordAt_of_lt (v := src) (t := i1.val) hi1b, hi1]
      have h5lt : i5.val < GP := by rw [hi5v]; exact wordAt_lt hsrc GP_pos _
      step with gold_sub_spec i5 v h5lt hvlt as ⟨i6, hi6v, hi6lt⟩
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


/-- The outer loop of `dit_stage`: block starts below `start` already hold the
stage's value, and the loop finishes the buffer. The mirror of
`NttStage.dif_stage_loop0_spec`. -/
theorem gold_dit_stage_loop0_spec (src dst tw : alloc.vec.Vec Std.U64) (len : Std.Usize)
    (half step start : Std.Usize) 
    (hsrc : Canon GP src) (hdst : Canon GP dst) (htw : Canon GP tw)
    (hlen : len.val = 2 * half.val) (hhalf : 0 < half.val) (hdvd : len.val ∣ N)
    (hstep : 0 < step.val) (hebd : half.val * step.val ≤ N)
    (hstart : start.val ≤ N) (hmod : start.val % len.val = 0)
    (hval : ∀ t, t < start.val →
      wordAt dst t = ditWord GP half.val step.val (wordAt src) (wordAt tw) t) :
    ntt.gold_dit_stage_loop0 src dst len tw ntt.NTT_LEN half step start
      ⦃ z => Canon GP z
             ∧ ∀ t, t < N →
                 wordAt z t = ditWord GP half.val step.val (wordAt src) (wordAt tw) t ⦄ := by
  rw [ntt.gold_dit_stage_loop0]
  apply loop.spec_decr_nat (fun s => N - s.2.val)
    (fun s => s.2.val ≤ N ∧ s.2.val % len.val = 0 ∧ Canon GP s.1
      ∧ (∀ t, t < s.2.val →
          wordAt s.1 t = ditWord GP half.val step.val (wordAt src) (wordAt tw) t))
  · rintro ⟨d, ss⟩ ⟨hss, hmod1, hcd, hval1⟩
    dsimp only at hss hmod1 hcd hval1
    simp only [ntt.gold_dit_stage_loop0.body]
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
      step with gold_dit_stage_loop0_loop0_spec src d tw half step ss 0#usize 0#usize
        hsrc hcd htw hblk2 (by simp) (by simp) hstep hebd
        (by intro t ht; simp at ht) as ⟨d1, hc1, hwr1, hfr1⟩
      step with gold_dit_stage_loop0_loop1_spec src d1 tw half step ss 0#usize 0#usize
        hsrc hc1 htw hblk2 (by simp) (by simp) hstep hebd
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

theorem gold_dit_stage_spec (src dst tw : alloc.vec.Vec Std.U64) (len : Std.Usize)
    (k : ℕ) (hk : k < 10)
    (hlen : len.val = 2 ^ (k + 1))
    (hsrc : Canon GP src) (hdst : Canon GP dst) (htw : Canon GP tw) :
    ntt.gold_dit_stage src dst len tw
      ⦃ z => Canon GP z
             ∧ ∀ t, t < N →
                 wordAt z t = ditWord GP (2 ^ k) (2 * (N / 2 ^ (k + 1)))
                   (wordAt src) (wordAt tw) t ⦄ := by
  obtain ⟨hdvd, hsteppos, hprod⟩ := ditParams k hk
  have hlen2 : len.val = 2 * 2 ^ k := by rw [hlen]; ring
  have hlne : len.val ≠ 0 := by omega
  rw [ntt.gold_dit_stage]
  step as ⟨hf, hhf⟩
  have hhfv : hf.val = 2 ^ k := by rw [hhf, hlen2]; omega
  step as ⟨qq, hqq⟩
  have hqqv : qq.val = N / 2 ^ (k + 1) := by rw [hqq, ntt_NTT_LEN_val, hlen]
  have hqqle : qq.val ≤ N := by rw [hqqv]; exact Nat.div_le_self _ _
  step as ⟨st, hst⟩
  have hstv : st.val = 2 * (N / 2 ^ (k + 1)) := by rw [hst, hqqv]
  rw [← hhfv, ← hstv]
  exact gold_dit_stage_loop0_spec src dst tw len hf st 0#usize hsrc hdst htw
    (by rw [hlen2, hhfv]) (by rw [hhfv]; positivity) (by rw [hlen]; exact hdvd)
    (by rw [hstv]; exact hsteppos)
    (by rw [hhfv, hstv]; exact Nat.le_of_eq hprod)
    (by simp) (by simp) (by intro t ht; simp at ht)

/-- The forward transform's loop, in the conserved-value form: one stage turns
`difRun … k` into `difRun … (k-1)` of the stage's output, so the invariant is
preserved, and at `len = 1` the invariant *is* the conclusion.

The buffer swap is why both buffers have to stay `Canon`: the old live buffer
becomes the next stage's scratch. -/

theorem gold_forward_loop_spec (tw cur tmp : alloc.vec.Vec Std.U64) 
    (len : Std.Usize) (k : ℕ) (hk : k ≤ 5) (hlen : len.val = 2 ^ (2 * k))
    (hcur : Canon GP cur) (htmp : Canon GP tmp) (htw : Canon GP tw)
    (psi : ZMod GP) (hpsi : ∀ e, e < N → resK GP tw e = psi ^ e)
    (g : ℕ → ZMod GP)
    (hinv : ∀ t, t < N →
      NttMath.difRun (psi ^ 2) (2 * k) (2 ^ (10 - 2 * k)) (resK GP cur) t = g t) :
    ntt.gold_forward_loop tw cur tmp len
      ⦃ z => Canon GP z.1 ∧ Canon GP z.2
             ∧ ∀ t, t < N → resK GP z.1 t = g t ⦄ := by
  have hag : ∀ e, e < N → wordAt tw e = psiRep psi e := tw_agree' GP tw GP_pos htw psi hpsi
  rw [ntt.gold_forward_loop]
  apply loop.spec_decr_nat (fun s => s.2.2.val)
    (fun s => Canon GP s.1 ∧ Canon GP s.2.1
      ∧ ∃ i, i ≤ 5 ∧ s.2.2.val = 2 ^ (2 * i)
        ∧ ∀ t, t < N →
            NttMath.difRun (psi ^ 2) (2 * i) (2 ^ (10 - 2 * i)) (resK GP s.1) t = g t)
  · rintro ⟨c, d, l⟩ ⟨hc, hd, i, hi, hli, hvi⟩
    dsimp only at hc hd hli hvi
    simp only [ntt.gold_forward_loop.body]
    by_cases hlt : l > 1#usize
    · rw [if_pos hlt]
      have hl1 : 1 < l.val := by scalar_tac
      have hipos : 0 < i := by
        rcases Nat.eq_zero_or_pos i with rfl | hp
        · rw [show 2 * 0 = 0 from rfl, pow_zero] at hli; omega
        · exact hp
      obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      have hm4 : m ≤ 4 := by omega
      have hk9 : 2 * m < 9 := by omega
      have hlk : l.val = 2 ^ (2 * m + 2) := by rw [hli]; congr 1
      step with GoldFusedStage.gold_dif_stage2_spec c d tw l (2 * m) hk9 hlk hc hd htw
        as ⟨fl, hcf, hwf⟩
      step as ⟨l2, hl2⟩
      have hswc : ∀ u, wordAt c u < GP := fun u => wordAt_lt hc GP_pos u
      have hstep1 : N / 2 ^ (2 * m + 1) = 2 ^ (9 - 2 * m) := N_div_pow (2 * m) (by omega)
      have hstep2 : N / 2 ^ (2 * m + 2) = 2 ^ (8 - 2 * m) := by
        have h := N_div_pow (2 * m + 1) (by omega)
        rw [show 9 - (2 * m + 1) = 8 - 2 * m by omega] at h
        rw [show 2 * m + 2 = 2 * m + 1 + 1 by ring]
        exact h
      -- the twiddle table, replaced by the ring's powers, in both stages
      have hinner : difWord GP (2 ^ (2 * m + 1)) (2 * (N / 2 ^ (2 * m + 2)))
            (wordAt c) (wordAt tw)
          = difWord GP (2 ^ (2 * m + 1)) (2 * (N / 2 ^ (2 * m + 2)))
            (wordAt c) (psiRep psi) :=
        funext (fun u => difWord_tw_congr GP (2 * m + 1) (by omega) (wordAt c)
          (wordAt tw) (psiRep psi) hag u)
      -- the fused pass, read in the ring: two stages, not one
      have hres : ∀ t, t < N →
          resK GP fl t
            = NttMath.difStage (2 ^ (2 * m)) (2 ^ (9 - 2 * m)) (psi ^ 2)
                (NttMath.difStage (2 ^ (2 * m + 1)) (2 ^ (8 - 2 * m)) (psi ^ 2)
                  (resK GP c)) t := by
        intro t ht
        have h1 : wordAt fl t
            = difWord GP (2 ^ (2 * m)) (2 * (N / 2 ^ (2 * m + 1)))
                (difWord GP (2 ^ (2 * m + 1)) (2 * (N / 2 ^ (2 * m + 2)))
                  (wordAt c) (psiRep psi)) (psiRep psi) t := by
          rw [hwf t ht, hinner]
          exact difWord_tw_congr GP (2 * m) (by omega) _ (wordAt tw) (psiRep psi) hag t
        have hmid : (fun u => ((difWord GP (2 ^ (2 * m + 1)) (2 * 2 ^ (8 - 2 * m))
              (wordAt c) (psiRep psi) u : ℕ) : ZMod GP))
            = NttMath.difStage (2 ^ (2 * m + 1)) (2 ^ (8 - 2 * m)) (psi ^ 2) (resK GP c) :=
          funext (fun u => difWord_cast GP (2 ^ (2 * m + 1)) (2 ^ (8 - 2 * m)) psi
            (wordAt c) (psiRep psi) (psiRep_cast GP_pos psi) hswc u)
        have hlt2 : ∀ u, difWord GP (2 ^ (2 * m + 1)) (2 * 2 ^ (8 - 2 * m))
            (wordAt c) (psiRep psi) u < GP :=
          fun u => difWord_lt GP _ _ GP_pos _ _ u
        rw [resK, h1, hstep1, hstep2,
          difWord_cast GP (2 ^ (2 * m)) (2 ^ (9 - 2 * m)) psi _ (psiRep psi)
            (psiRep_cast GP_pos psi) hlt2 t, hmid]
      -- the invariant, advanced by TWO stages
      have hnext : ∀ t, t < N →
          NttMath.difRun (psi ^ 2) (2 * m) (2 ^ (10 - 2 * m)) (resK GP fl) t = g t := by
        intro t ht
        have hdvd : (2 : ℕ) ^ (2 * m) ∣ N := by
          rw [show N = 2 ^ 10 by norm_num]
          exact pow_dvd_pow 2 (by omega)
        rw [difRun_congr (psi ^ 2) (2 * m) hdvd (2 ^ (10 - 2 * m)) (resK GP fl)
              (NttMath.difStage (2 ^ (2 * m)) (2 ^ (9 - 2 * m)) (psi ^ 2)
                (NttMath.difStage (2 ^ (2 * m + 1)) (2 ^ (8 - 2 * m)) (psi ^ 2)
                  (resK GP c))) hres t ht]
        rw [← hvi t ht, show 10 - 2 * (m + 1) = 8 - 2 * m by omega,
          show 2 * (m + 1) = 2 * m + 1 + 1 by ring, NttMath.difRun_succ,
          show (2 : ℕ) ^ (8 - 2 * m) * 2 = 2 ^ (9 - 2 * m) by
            rw [show 9 - 2 * m = (8 - 2 * m) + 1 by omega, pow_succ],
          NttMath.difRun_succ,
          show (2 : ℕ) ^ (9 - 2 * m) * 2 = 2 ^ (10 - 2 * m) by
            rw [show 10 - 2 * m = (9 - 2 * m) + 1 by omega, pow_succ]]
      have hl2v : l2.val = 2 ^ (2 * m) := by
        rw [hl2, hlk, show (2 : ℕ) ^ (2 * m + 2) = 2 ^ (2 * m) * 4 by rw [pow_add]; ring]
        omega
      refine ⟨hcf, hc, ⟨m, by omega, hl2v, hnext⟩, ?_⟩
      rw [hl2v, hlk, show (2 : ℕ) ^ (2 * m + 2) = 2 ^ (2 * m) * 4 by rw [pow_add]; ring]
      have hp : 0 < (2 : ℕ) ^ (2 * m) := Nat.two_pow_pos _
      omega
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have hl1 : l.val ≤ 1 := by scalar_tac
      have hi0 : i = 0 := by
        rcases Nat.eq_zero_or_pos i with rfl | hp
        · rfl
        · exfalso
          have h2 : (2 : ℕ) ^ 2 ≤ 2 ^ (2 * i) := Nat.pow_le_pow_right (by norm_num) (by omega)
          rw [hli] at hl1
          norm_num at h2
          omega
      subst hi0
      refine ⟨hc, hd, ?_⟩
      intro t ht
      simpa using hvi t ht
  · exact ⟨hcur, htmp, k, hk, hlen, hinv⟩

-- Replaces the `gold_forward_spec` stub (statement verbatim).

theorem gold_forward_spec (cur tmp tw : alloc.vec.Vec Std.U64) 
    (hcur : Canon GP cur) (htmp : Canon GP tmp)
    (htw : Canon GP tw) (psi : ZMod GP)
    (hpsi : ∀ e, e < N → resK GP tw e = psi ^ e) :
    ntt.gold_forward cur tmp tw
      ⦃ z => Canon GP z.1 ∧ Canon GP z.2
             ∧ ∀ t, t < N →
                 resK GP z.1 t
                   = NttMath.difRun (psi ^ 2) 10 1 (resK GP cur) t ⦄ := by
  rw [ntt.gold_forward]
  exact gold_forward_loop_spec tw cur tmp ntt.NTT_LEN 5 (le_refl 5)
    (by rw [ntt_NTT_LEN_val]; norm_num) hcur htmp htw psi hpsi
    (NttMath.difRun (psi ^ 2) 10 1 (resK GP cur)) (by intro t _; norm_num)

-- Insert before `gold_inverse_spec`.

/-- The inverse loop. The orientation of the invariant is the other way round
from the forward one: `ditRun` builds its answer from the innermost stage out,
so after `i` stages the live buffer *is* `ditRun … i` of the original input,
rather than holding an intermediate whose remaining stages are the answer.

`len` doubles, so the measure counts down from `2·NTT_LEN`. -/
theorem gold_inverse_loop_spec (tw cur tmp : alloc.vec.Vec Std.U64) 
    (len : Std.Usize) (k : ℕ) (hk : k ≤ 10)
    (hlen : len.val = 2 ^ (k + 1))
    (hcur : Canon GP cur) (htmp : Canon GP tmp) (htw : Canon GP tw)
    (psii : ZMod GP) (hpsi : ∀ e, e < N → resK GP tw e = psii ^ e)
    (f : ℕ → ZMod GP)
    (hinv : ∀ t, t < N →
      resK GP cur t = NttMath.ditRun (psii ^ 2) k (2 ^ (10 - k)) f t) :
    ntt.gold_inverse_loop tw cur tmp len
      ⦃ z => Canon GP z.1 ∧ Canon GP z.2
             ∧ ∀ t, t < N →
                 resK GP z.1 t = NttMath.ditRun (psii ^ 2) 10 1 f t ⦄ := by
  have hag : ∀ e, e < N → wordAt tw e = psiRep psii e := tw_agree' GP tw GP_pos htw psii hpsi
  rw [ntt.gold_inverse_loop]
  apply loop.spec_decr_nat (fun s => 2 * N - s.2.2.val)
    (fun s => Canon GP s.1 ∧ Canon GP s.2.1
      ∧ ∃ i, i ≤ 10 ∧ s.2.2.val = 2 ^ (i + 1)
        ∧ ∀ t, t < N →
            resK GP s.1 t = NttMath.ditRun (psii ^ 2) i (2 ^ (10 - i)) f t)
  · rintro ⟨c, d, l⟩ ⟨hc, hd, i, hi, hli, hvi⟩
    dsimp only at hc hd hli hvi
    simp only [ntt.gold_inverse_loop.body]
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
      step with gold_dit_stage_spec c d tw l i hi9 hli hc hd htw as ⟨fl, hcf, hwf⟩
      step as ⟨l2, hl2⟩
      have hswc : ∀ u, wordAt c u < GP := fun u => wordAt_lt hc GP_pos u
      have hstride : N / 2 ^ (i + 1) = 2 ^ (9 - i) := N_div_pow i hi9
      have hres : ∀ t, t < N →
          resK GP fl t
            = NttMath.ditStage (2 ^ i) (2 ^ (9 - i)) (psii ^ 2) (resK GP c) t := by
        intro t ht
        have h1 : wordAt fl t
            = ditWord GP (2 ^ i) (2 * (N / 2 ^ (i + 1))) (wordAt c) (psiRep psii) t := by
          rw [hwf t ht]
          exact ditWord_tw_congr GP i hi9 (wordAt c) (wordAt tw) (psiRep psii) hag t
        rw [resK, h1, hstride]
        exact ditWord_cast GP (2 ^ i) (2 ^ (9 - i)) psii (wordAt c) (psiRep psii)
          (psiRep_cast GP_pos psii) hswc (psiRep_lt GP_pos psii) t
      have hnext : ∀ t, t < N →
          resK GP fl t = NttMath.ditRun (psii ^ 2) (i + 1) (2 ^ (10 - (i + 1))) f t := by
        intro t ht
        have hd2 : 2 * 2 ^ i ∣ N := by
          rw [show 2 * 2 ^ i = 2 ^ (i + 1) by ring, show N = 2 ^ 10 by norm_num]
          exact pow_dvd_pow 2 (by omega)
        have he1 : (2 : ℕ) ^ (9 - i) * 2 = 2 ^ (10 - i) := by
          rw [show 10 - i = (9 - i) + 1 by omega, pow_succ]
        rw [hres t ht, show 10 - (i + 1) = 9 - i by omega, NttMath.ditRun_succ, he1]
        exact ditStage_congr (2 ^ i) (2 ^ (9 - i)) (psii ^ 2) (Nat.two_pow_pos i) hd2
          (resK GP c) (NttMath.ditRun (psii ^ 2) i (2 ^ (10 - i)) f) hvi t ht
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

-- Replaces the `gold_inverse_spec` stub (statement verbatim).

theorem gold_inverse_spec (cur tmp tw : alloc.vec.Vec Std.U64) 
    (hcur : Canon GP cur) (htmp : Canon GP tmp)
    (htw : Canon GP tw) (psii : ZMod GP)
    (hpsi : ∀ e, e < N → resK GP tw e = psii ^ e) :
    ntt.gold_inverse cur tmp tw
      ⦃ z => Canon GP z.1 ∧ Canon GP z.2
             ∧ ∀ t, t < N →
                 resK GP z.1 t
                   = NttMath.ditRun (psii ^ 2) 10 1 (resK GP cur) t ⦄ := by
  rw [ntt.gold_inverse]
  exact gold_inverse_loop_spec tw cur tmp 2#usize 0 (by norm_num)
    (by simp) hcur htmp htw psii hpsi (resK GP cur) (by intro t _; simp)



end HachiEquiv.GoldTransform
