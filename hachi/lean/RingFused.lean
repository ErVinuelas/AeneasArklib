/-
`RingFused.lean` -- the fused dot product.

`linalg::PolyVec::dot` used to call `ring::Rq::mul` per term, and each of those
ran a complete three-prime transform pipeline. `ring::dot_fused` keeps the
accumulator in the *transform domain*: the two ψ tables are built once per
chunk instead of per product, and there is one inverse transform and one Garner
pass per chunk rather than one per term.

# What is new here, and what is not

Almost nothing about the transform argument changes, which is the point of how
`NttProduct` was written:

* `inv_value` already takes an **arbitrary** buffer `C`, so it applies verbatim
  once the accumulator is known to be `difRun … C` for the summed `C`;
* `untwist_value` is per-term, and the summed form is a `Finset.sum`
  distribution over it ([`untwist_value_sum`] below);
* `twist_cast`, `ntt_forward_spec`, `pointwise_cast`, `ntt_inverse_spec`,
  `untwist_cast`, `zeros_canon` are reused unchanged.

The one genuinely new *mathematical* fact is that the inverse transform
commutes with a finite sum -- `NttMath.ditRun_sum` -- which had to be proved
because the transforms here are butterfly networks rather than explicit sums.
With it, every term of the accumulator reduces to the single-product argument.

# The offset, which is the trap

`untwist` adds `boff = BOUND mod p` **once per coefficient**, and that is what
makes a single product's reconstructed integer non-negative. A fused dot
accumulates `L` products, so a single offset leaves

    Σⱼ posSumⱼ + BOUND − Σⱼ negSumⱼ

which is negative as soon as the negative antidiagonal dominates -- and Garner
reconstructs no negatives. The Rust therefore scales the offset by the chunk
length, and `DOT_CHUNK = 8192` is forced by `2·L·BOUND < P`, i.e. `L ≤ 12468`.
The Rust-side oracle was checked to fail at exactly `n = 5` with the scaling
removed, which is where the arithmetic says it must.
-/
import NttProduct
import Ring

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.RingFused

open HachiEquiv.NttArith HachiEquiv.NttStage HachiEquiv.NttTransform HachiEquiv.NttCRT
open HachiEquiv.NttProduct

/-! ## 1. The untwist, over a sum

`untwist_value` per term, distributed. The `N ·` and the `ψ'^t · n⁻¹` scaling are
both linear, so this is `Finset.mul_sum`/`Finset.sum_mul` and nothing else. -/

theorem untwist_value_sum {p : ℕ} {ι : Type*} (psi psii ninvK : ZMod p)
    (hord : psi ^ N = -1) (hpinv : psi * psii = 1)
    (hNinv : ((N : ℕ) : ZMod p) * ninvK = 1)
    (s : Finset ι) (A B : ι → ℕ → ZMod p) (t : ℕ) (ht : t < N) :
    ((N : ℕ) : ZMod p)
          * (∑ j ∈ s, NttMath.cyclicConv N (NttMath.twistR psi (A j))
              (NttMath.twistR psi (B j)) t)
        * psii ^ t * ninvK
      = ∑ j ∈ s, NttMath.negConvR N (A j) (B j) t := by
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact untwist_value psi psii ninvK hord hpinv hNinv (A j) (B j) t ht

/-! ## 2. The accumulate loop

`acc[k] += prod[k]` for every `k < N`, in `ZMod p`. `base` is what the
accumulator held before this term. -/

theorem accum_spec (pw mw : Std.U64) (nU : Std.Usize) (acc prod : alloc.vec.Vec Std.U64)
    (kU : Std.Usize) (base : ℕ → ZMod pw.val)
    (h : Magic pw mw) (hn : nU.val = N) (hk : kU.val ≤ N)
    (hacc : Canon pw.val acc) (hprod : Canon pw.val prod)
    (hval : ∀ t, t < N → resK pw.val acc t
              = base t + (if t < kU.val then resK pw.val prod t else 0)) :
    ring.dot_chunk_mod_p_loop0_loop2 pw nU acc prod kU
      ⦃ z => Canon pw.val z ∧ ∀ t, t < N → resK pw.val z t
              = base t + resK pw.val prod t ⦄ := by
  have hppos : 0 < pw.val := h.pos
  rw [ring.dot_chunk_mod_p_loop0_loop2]
  apply loop.spec_decr_nat (fun r => nU.val - r.2.val)
    (fun r => r.2.val ≤ N ∧ Canon pw.val r.1
      ∧ ∀ t, t < N → resK pw.val r.1 t
              = base t + (if t < r.2.val then resK pw.val prod t else 0))
  · rintro ⟨d, kk⟩ ⟨hkk, hcd, hw⟩
    dsimp only at hkk hcd hw
    simp only [ring.dot_chunk_mod_p_loop0_loop2.body]
    by_cases hlt : kk < nU
    · rw [if_pos hlt]
      have hklt : kk.val < N := by rw [← hn]; scalar_tac
      have hdb : kk.val < d.val.length := by rw [hcd.1]; exact hklt
      have hpb : kk.val < prod.val.length := by rw [hprod.1]; exact hklt
      step as ⟨x, hx⟩
      have hxv : x.val = wordAt d kk.val := by
        rw [hx, ← wordAt_of_lt (v := d) (t := kk.val) hdb]
      step as ⟨y, hy⟩
      have hyv : y.val = wordAt prod kk.val := by
        rw [hy, ← wordAt_of_lt (v := prod) (t := kk.val) hpb]
      have hxlt : x.val < pw.val := by rw [hxv]; exact wordAt_lt hcd hppos _
      have hylt : y.val < pw.val := by rw [hyv]; exact wordAt_lt hprod hppos _
      step with aux_add_lt x y pw h.lt_pow hxlt hylt as ⟨z, hzv, hzlt⟩
      step as ⟨elem, back, helem, hback⟩
      step as ⟨kk1, hkk1⟩
      rw [hback]
      refine ⟨by rw [hkk1]; omega, Canon_set hcd hzlt, ?_, by rw [hkk1]; omega⟩
      intro t ht
      rw [hkk1]
      by_cases heq : t = kk.val
      · rw [heq]
        simp only [resK]
        rw [wordAt_set_eq hdb, hzv]
        have hcast : ((((x.val + y.val) % pw.val : ℕ)) : ZMod pw.val)
            = ((x.val : ℕ) : ZMod pw.val) + ((y.val : ℕ) : ZMod pw.val) := by
          rw [ZMod.natCast_mod]; push_cast; ring
        rw [hcast, hxv, hyv]
        have hbase := hw kk.val hklt
        simp only [resK] at hbase
        rw [hbase, if_neg (by omega), add_zero, if_pos (by omega)]
      · simp only [resK]
        rw [wordAt_set_ne heq]
        have hbase := hw t ht
        simp only [resK] at hbase
        rw [hbase]
        by_cases hlt2 : t < kk.val
        · rw [if_pos hlt2, if_pos (by omega)]
        · rw [if_neg hlt2, if_neg (by omega)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : kk.val = N := by rw [← hn]; scalar_tac
      refine ⟨hcd, ?_⟩
      intro t ht
      rw [hw t ht, heq, if_pos ht]
  · exact ⟨hk, hacc, hval⟩

/-! ## 3. The two word-copy loops

`Ring.mul_loop0`'s shape with one extra index: the words of `a[j]`, copied into
a fresh `u64` buffer. Two near-identical specs because they are two extracted
constants; the bodies differ only in which vector they read. -/

private theorem getD_append_lt' {α : Type} (l : List α) (x d : α) {j : ℕ}
    (hj : j < l.length) : (l ++ [x]).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hj,
    List.getElem_append_left hj]

private theorem getD_append_eq' {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
  simp

theorem words_a_spec (a : alloc.vec.Vec ring.Rq) (nU jU : Std.Usize)
    (aw : alloc.vec.Vec Std.U64) (tU : Std.Usize)
    (hn : nU.val = N) (hjb : jU.val < a.val.length)
    (haj : HachiEquiv.Ring.Wf (a.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)))
    (ht : tU.val ≤ N) (hlen : aw.val.length = tU.val)
    (hred : ∀ u ∈ aw.val, u.val < HachiEquiv.NttProduct.q)
    (hval : ∀ t, t < tU.val → wordAt aw t
      = HachiEquiv.Ring.wordN (a.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) t) :
    ring.dot_chunk_mod_p_loop0_loop0 a nU jU aw tU
      ⦃ z => z.val.length = N ∧ (∀ u ∈ z.val, u.val < HachiEquiv.NttProduct.q)
             ∧ ∀ t, t < N → wordAt z t
                 = HachiEquiv.Ring.wordN
                     (a.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) t ⦄ := by
  rw [ring.dot_chunk_mod_p_loop0_loop0]
  apply loop.spec_decr_nat (fun r => nU.val - r.2.val)
    (fun r => r.2.val ≤ N ∧ r.1.val.length = r.2.val
      ∧ (∀ u ∈ r.1.val, u.val < HachiEquiv.NttProduct.q)
      ∧ ∀ t, t < r.2.val → wordAt r.1 t
          = HachiEquiv.Ring.wordN
              (a.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) t)
  · rintro ⟨d, tt⟩ ⟨htt, hdl, hdr, hdv⟩
    dsimp only at htt hdl hdr hdv
    simp only [ring.dot_chunk_mod_p_loop0_loop0.body]
    by_cases hlt : tt < nU
    · rw [if_pos hlt]
      have httlt : tt.val < N := by rw [← hn]; scalar_tac
      step as ⟨r, hr⟩
      have hrv : r = a.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp) := by
        rw [hr, List.getD_eq_getElem _ _ hjb]
      have hrb : tt.val < r.val.length := by rw [hrv, haj.1]; exact httlt
      step as ⟨f, hf⟩
      step with HachiEquiv.Ring.to_u64_id f as ⟨w, hw⟩
      have hwlt : w.val < HachiEquiv.NttProduct.q := by
        rw [hw, hf]; exact haj.2 _ (by rw [← hrv]; exact List.getElem_mem hrb)
      have hwv : w.val = HachiEquiv.Ring.wordN
          (a.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) tt.val := by
        rw [hw, hf, ← hrv]
        unfold HachiEquiv.Ring.wordN
        rw [List.getD_eq_getElem _ _ hrb]
      step as ⟨d1, hd1⟩
      step as ⟨tt1, htt1⟩
      refine ⟨by rw [htt1]; omega, ?_, ?_, ?_, by rw [htt1]; omega⟩
      · rw [hd1, htt1, List.length_append, hdl]; simp
      · intro u hu
        rw [hd1] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hdr u h
        · rw [List.mem_singleton.mp h]; exact hwlt
      · intro t htl
        rw [htt1] at htl
        simp only [wordAt] at hdv ⊢
        rcases Nat.lt_or_ge t tt.val with hlt2 | hge
        · rw [hd1, getD_append_lt' _ _ _ (by omega)]
          exact hdv t hlt2
        · have hteq : t = d.val.length := by omega
          rw [hteq, hd1, getD_append_eq', hdl, hwv]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : tt.val = N := by rw [← hn]; scalar_tac
      exact ⟨by rw [hdl, heq], hdr, fun t htl => hdv t (by rw [heq]; exact htl)⟩
  · exact ⟨ht, hlen, hred, hval⟩

theorem words_b_spec (b : alloc.vec.Vec ring.Rq) (nU jU : Std.Usize)
    (bw : alloc.vec.Vec Std.U64) (tU : Std.Usize)
    (hn : nU.val = N) (hjb : jU.val < b.val.length)
    (hbj : HachiEquiv.Ring.Wf (b.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)))
    (ht : tU.val ≤ N) (hlen : bw.val.length = tU.val)
    (hred : ∀ u ∈ bw.val, u.val < HachiEquiv.NttProduct.q)
    (hval : ∀ t, t < tU.val → wordAt bw t
      = HachiEquiv.Ring.wordN (b.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) t) :
    ring.dot_chunk_mod_p_loop0_loop1 b nU jU bw tU
      ⦃ z => z.val.length = N ∧ (∀ u ∈ z.val, u.val < HachiEquiv.NttProduct.q)
             ∧ ∀ t, t < N → wordAt z t
                 = HachiEquiv.Ring.wordN
                     (b.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) t ⦄ := by
  rw [ring.dot_chunk_mod_p_loop0_loop1]
  apply loop.spec_decr_nat (fun r => nU.val - r.2.val)
    (fun r => r.2.val ≤ N ∧ r.1.val.length = r.2.val
      ∧ (∀ u ∈ r.1.val, u.val < HachiEquiv.NttProduct.q)
      ∧ ∀ t, t < r.2.val → wordAt r.1 t
          = HachiEquiv.Ring.wordN
              (b.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) t)
  · rintro ⟨d, tt⟩ ⟨htt, hdl, hdr, hdv⟩
    dsimp only at htt hdl hdr hdv
    simp only [ring.dot_chunk_mod_p_loop0_loop1.body]
    by_cases hlt : tt < nU
    · rw [if_pos hlt]
      have httlt : tt.val < N := by rw [← hn]; scalar_tac
      step as ⟨r, hr⟩
      have hrv : r = b.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp) := by
        rw [hr, List.getD_eq_getElem _ _ hjb]
      have hrb : tt.val < r.val.length := by rw [hrv, hbj.1]; exact httlt
      step as ⟨f, hf⟩
      step with HachiEquiv.Ring.to_u64_id f as ⟨w, hw⟩
      have hwlt : w.val < HachiEquiv.NttProduct.q := by
        rw [hw, hf]; exact hbj.2 _ (by rw [← hrv]; exact List.getElem_mem hrb)
      have hwv : w.val = HachiEquiv.Ring.wordN
          (b.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) tt.val := by
        rw [hw, hf, ← hrv]
        unfold HachiEquiv.Ring.wordN
        rw [List.getD_eq_getElem _ _ hrb]
      step as ⟨d1, hd1⟩
      step as ⟨tt1, htt1⟩
      refine ⟨by rw [htt1]; omega, ?_, ?_, ?_, by rw [htt1]; omega⟩
      · rw [hd1, htt1, List.length_append, hdl]; simp
      · intro u hu
        rw [hd1] at hu
        rcases List.mem_append.mp hu with h | h
        · exact hdr u h
        · rw [List.mem_singleton.mp h]; exact hwlt
      · intro t htl
        rw [htt1] at htl
        simp only [wordAt] at hdv ⊢
        rcases Nat.lt_or_ge t tt.val with hlt2 | hge
        · rw [hd1, getD_append_lt' _ _ _ (by omega)]
          exact hdv t hlt2
        · have hteq : t = d.val.length := by omega
          rw [hteq, hd1, getD_append_eq', hdl, hwv]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : tt.val = N := by rw [← hn]; scalar_tac
      exact ⟨by rw [hdl, heq], hdr, fun t htl => hdv t (by rw [heq]; exact htl)⟩
  · exact ⟨ht, hlen, hred, hval⟩

/-! ## 4. The terms loop

Per term: copy both operands' words, twist and forward-transform each, multiply
pointwise, and add the result into the transform-domain accumulator. By
`NttProduct.prod_difRun` that pointwise product *is* the forward transform of
the term's cyclic convolution, so the accumulator is a sum of forward
transforms -- and `NttMath.difRun_sum` will later pull the `difRun` outside the
sum so that one inverse transform serves the whole chunk. -/

/-- The `u`-th entry of a vector of ring elements, coefficientwise in `ZMod p`. -/
def entryK (pw : ℕ) (a : alloc.vec.Vec ring.Rq) (u : ℕ) : ℕ → ZMod pw :=
  fun v => ((HachiEquiv.Ring.wordN
    (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) v : ℕ) : ZMod pw)

/-- One term's transform-domain contribution. -/
def termFwd {pw : ℕ} (ps : ZMod pw) (a b : alloc.vec.Vec ring.Rq) (u : ℕ) : ℕ → ZMod pw :=
  NttMath.difRun (ps ^ 2) 10 1
    (NttMath.cyclicConv N (NttMath.twistR ps (entryK pw a u))
      (NttMath.twistR ps (entryK pw b u)))

theorem terms_chunk_spec (a b : alloc.vec.Vec ring.Rq) (startU endU : Std.Usize)
    (pw mw : Std.U64) (nU : Std.Usize) (pt : alloc.vec.Vec Std.U64)
    (acc scratch : alloc.vec.Vec Std.U64) (jU : Std.Usize) (ps : ZMod pw.val)
    (h : Magic pw mw) (hn : nU.val = N) (hord : ps ^ N = -1)
    (hptC : Canon pw.val pt) (hptv : ∀ e, e < N → resK pw.val pt e = ps ^ e)
    (hawf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbwf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hae : endU.val ≤ a.val.length) (hbe : endU.val ≤ b.val.length)
    (hjs : startU.val ≤ jU.val) (hje : jU.val ≤ endU.val)
    (haccC : Canon pw.val acc) (hscC : Canon pw.val scratch)
    (hval : ∀ t, t < N → resK pw.val acc t
              = ∑ u ∈ Finset.Ico startU.val jU.val, termFwd ps a b u t) :
    ring.dot_chunk_mod_p_loop0 a b endU pw mw nU pt acc scratch jU
      ⦃ z => Canon pw.val z.1 ∧ Canon pw.val z.2
             ∧ ∀ t, t < N → resK pw.val z.1 t
                 = ∑ u ∈ Finset.Ico startU.val endU.val, termFwd ps a b u t ⦄ := by
  have hppos : 0 < pw.val := h.pos
  rw [ring.dot_chunk_mod_p_loop0]
  apply loop.spec_decr_nat (fun r => endU.val - r.2.2.val)
    (fun r => startU.val ≤ r.2.2.val ∧ r.2.2.val ≤ endU.val
      ∧ Canon pw.val r.1 ∧ Canon pw.val r.2.1
      ∧ ∀ t, t < N → resK pw.val r.1 t
              = ∑ u ∈ Finset.Ico startU.val r.2.2.val, termFwd ps a b u t)
  · rintro ⟨d, sc, jj⟩ ⟨hjjs, hjje, hcd, hcsc, hw⟩
    dsimp only at hjjs hjje hcd hcsc hw
    simp only [ring.dot_chunk_mod_p_loop0.body]
    by_cases hlt : jj < endU
    · rw [if_pos hlt]
      have hjjlt : jj.val < endU.val := by scalar_tac
      have hja : jj.val < a.val.length := by omega
      have hjb : jj.val < b.val.length := by omega
      simp only [alloc.vec.Vec.with_capacity]
      step with words_a_spec a nU jj (alloc.vec.Vec.new Std.U64) 0#usize hn hja
        (hawf jj.val hjjlt) (by simp) (by simp) (by intro u hu; simp at hu)
        (by intro t ht; simp at ht) as ⟨aw, hawl, hawr, hawv⟩
      step with words_b_spec b nU jj (alloc.vec.Vec.new Std.U64) 0#usize hn hjb
        (hbwf jj.val hjjlt) (by simp) (by simp) (by intro u hu; simp at hu)
        (by intro t ht; simp at ht) as ⟨bw, hbwl, hbwr, hbwv⟩
      -- `twist` takes an *unreduced* buffer (length `N` only) and returns a
      -- canonical one, which is why the words being `< q` rather than `< p`
      -- costs nothing here
      step with twist_cast aw pt pw mw h hawl hptC ps hptv as ⟨ta, htaC, htav⟩
      step with ntt_forward_spec ta sc pt pw mw h htaC hcsc hptC ps hptv
        as ⟨fwa, hfw1, hfw2, hfwv⟩
      obtain ⟨v, v1⟩ := fwa
      dsimp only at hfw1 hfw2 hfwv
      step with twist_cast bw pt pw mw h hbwl hptC ps hptv as ⟨tb, htbC, htbv⟩
      step with ntt_forward_spec tb v1 pt pw mw h htbC hfw2 hptC ps hptv
        as ⟨v2, v3, hgw1, hgw2, hgwv⟩
      step with pointwise_cast v v2 pw mw h hfw1 hgw1 as ⟨prod, hprC, hprv⟩
      -- the copied words *are* this term's coefficients, so the transforms are
      -- the ones `termFwd` names
      have hFA : ∀ t, t < N → resK pw.val v t
          = NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK pw.val a jj.val)) t := by
        intro t ht
        rw [hfwv t ht]
        refine difRun_congr (ps ^ 2) 10 (by norm_num) 1 (resK pw.val ta)
          (NttMath.twistR ps (entryK pw.val a jj.val)) ?_ t ht
        intro e he
        rw [htav e he]
        simp only [NttMath.twistR, entryK, hawv e he]
      have hFB : ∀ t, t < N → resK pw.val v2 t
          = NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK pw.val b jj.val)) t := by
        intro t ht
        rw [hgwv t ht]
        refine difRun_congr (ps ^ 2) 10 (by norm_num) 1 (resK pw.val tb)
          (NttMath.twistR ps (entryK pw.val b jj.val)) ?_ t ht
        intro e he
        rw [htbv e he]
        simp only [NttMath.twistR, entryK, hbwv e he]
      have hprod : ∀ t, t < N → resK pw.val prod t = termFwd ps a b jj.val t := by
        intro t ht
        exact prod_difRun ps hord (entryK pw.val a jj.val) (entryK pw.val b jj.val)
          (resK pw.val v) (resK pw.val v2) (resK pw.val prod) hFA hFB hprv t ht
      step with accum_spec pw mw nU d prod 0#usize (resK pw.val d)
        h hn (by simp) hcd hprC (by intro t ht; simp) as ⟨acc1, hac1C, hac1v⟩
      step as ⟨jj1, hjj1⟩
      refine ⟨by rw [hjj1]; omega, by rw [hjj1]; omega, hac1C, hgw2, ?_,
        by rw [hjj1]; omega⟩
      intro t ht
      rw [hjj1, Finset.sum_Ico_succ_top (by omega), ← hw t ht, ← hprod t ht]
      exact hac1v t ht
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = endU.val := by scalar_tac
      refine ⟨hcd, hcsc, ?_⟩
      intro t ht
      rw [hw t ht, heq]
  · exact ⟨hjs, hje, haccC, hscC, hval⟩

/-- `zeros` with its *values*, which `NttTransform.zeros_canon` does not give:
the fused chunk's initial accumulator has to be known zero, not merely
canonical, because the invariant starts at an empty sum. -/
theorem zeros_canon_zero (pp : ℕ) (hp : 0 < pp) :
    ntt.zeros ntt.NTT_LEN ⦃ z => Canon pp z ∧ ∀ t, t < N → resK pp z t = 0 ⦄ := by
  apply spec_mono (zeros_spec ntt.NTT_LEN)
  intro z hz
  refine ⟨⟨by rw [hz, List.length_replicate, ntt_NTT_LEN_val], ?_⟩, ?_⟩
  · intro u hu
    rw [hz, List.mem_replicate] at hu
    rw [hu.2]; simpa using hp
  · intro t ht
    simp only [resK, wordAt, hz]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate, ntt_NTT_LEN_val]; exact ht),
      List.getElem_replicate]
    simp

/-! ## 5. One chunk, at one prime

The whole per-prime pipeline, fused. Three things happen here that
`NttProduct.negconv_mod_p_spec` does not do:

* `NttMath.difRun_sum` turns the accumulated pointwise products into **one**
  forward transform of the summed convolution, so `NttProduct.inv_value` -- which
  already takes an arbitrary buffer -- applies verbatim;
* [`untwist_value_sum`] distributes the untwist over the sum;
* the offset is `L · boff` rather than `boff`, `L` being the chunk length. That
  is the correctness-critical difference: `untwist` adds its offset once per
  coefficient, and a single `BOUND` leaves the reconstructed integer negative
  once the negative antidiagonal dominates. -/

theorem dot_chunk_mod_p_spec (a b : alloc.vec.Vec ring.Rq) (startU endU : Std.Usize)
    (pw mw psi psiinv ninv boff : Std.U64) (h : Magic pw mw)
    (hpsi : psi.val < pw.val) (hpsii : psiinv.val < pw.val)
    (hninv : ninv.val < pw.val) (hboff : boff.val < pw.val)
    (hord : ((psi.val : ℕ) : ZMod pw.val) ^ N = -1)
    (hpinv : ((psi.val : ℕ) : ZMod pw.val) * ((psiinv.val : ℕ) : ZMod pw.val) = 1)
    (hNinv : ((N : ℕ) : ZMod pw.val) * ((ninv.val : ℕ) : ZMod pw.val) = 1)
    (hawf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbwf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hae : endU.val ≤ a.val.length) (hbe : endU.val ≤ b.val.length)
    (hse : startU.val ≤ endU.val) (hlenp : endU.val - startU.val < pw.val) :
    ring.dot_chunk_mod_p a b startU endU pw mw psi psiinv ninv boff
      ⦃ z => Canon pw.val z ∧ ∀ t, t < N → resK pw.val z t
              = (∑ u ∈ Finset.Ico startU.val endU.val,
                  NttMath.negConvR N (entryK pw.val a u) (entryK pw.val b u) t)
                + ((boff.val : ℕ) : ZMod pw.val)
                    * (((endU.val - startU.val : ℕ)) : ZMod pw.val) ⦄ := by
  have hppos : 0 < pw.val := h.pos
  set ps : ZMod pw.val := ((psi.val : ℕ) : ZMod pw.val) with hpsdef
  set psii : ZMod pw.val := ((psiinv.val : ℕ) : ZMod pw.val) with hpsiidef
  rw [ring.dot_chunk_mod_p]
  step with psi_table_cast psi pw mw h hpsi as ⟨pt, hptC, hptv⟩
  step with psi_table_cast psiinv pw mw h hpsii as ⟨it, hitC, hitv⟩
  step with zeros_canon_zero pw.val hppos as ⟨acc0, hacc0C, hacc0v⟩
  step with terms_chunk_spec a b startU endU pw mw ntt.NTT_LEN pt acc0 acc0 startU ps
    h ntt_NTT_LEN_val hord hptC hptv hawf hbwf hae hbe (le_refl _) hse hacc0C hacc0C
    (by intro t ht; rw [hacc0v t ht]; simp)
    as ⟨acc1, scratch, hac1C, hac2C, hac1v⟩
  step as ⟨i, hi⟩
  step as ⟨len, hlen⟩
  have hlenv : len.val = endU.val - startU.val := by
    have hc : len.val = i.val := by rw [hlen]; simp
    rw [hc, hi]
  have hlenlt : len.val < pw.val := by rw [hlenv]; exact hlenp
  step with aux_mul_lt boff len pw mw h hboff hlenlt as ⟨scaled, hscv, hsclt⟩
  -- the accumulated products are ONE forward transform of the summed
  -- convolution: `difRun_sum` is what moves the transform outside the sum
  have hPR : ∀ t, t < N → resK pw.val acc1 t
      = NttMath.difRun (ps ^ 2) 10 1
          (fun t' => ∑ u ∈ Finset.Ico startU.val endU.val,
            NttMath.cyclicConv N (NttMath.twistR ps (entryK pw.val a u))
              (NttMath.twistR ps (entryK pw.val b u)) t') t := by
    intro t ht
    -- the arguments are supplied because `fun t => ∑ j ∈ s, F j t` is a
    -- higher-order pattern and `rw` cannot solve for `F`
    rw [hac1v t ht, NttMath.difRun_sum (ps ^ 2) 10 1
      (Finset.Ico startU.val endU.val)
      (fun u => NttMath.cyclicConv N (NttMath.twistR ps (entryK pw.val a u))
        (NttMath.twistR ps (entryK pw.val b u)))]
    simp only [termFwd, hpsdef]
  step with ntt_inverse_spec acc1 scratch it pw mw h hac1C hac2C hitC psii hitv
    as ⟨v, v5, hiv1, hiv2, hivv⟩
  have hIV := inv_value ps psii hpinv
    (fun t' => ∑ u ∈ Finset.Ico startU.val endU.val,
      NttMath.cyclicConv N (NttMath.twistR ps (entryK pw.val a u))
        (NttMath.twistR ps (entryK pw.val b u)) t')
    (resK pw.val acc1) (resK pw.val v) hPR hivv
  apply spec_mono (untwist_cast v it ninv scaled pw mw h hiv1 hitC hninv hsclt psii hitv)
  rintro z ⟨hzC, hzv⟩
  refine ⟨hzC, ?_⟩
  intro t ht
  rw [hzv t ht, hIV t ht,
    untwist_value_sum ps psii ((ninv.val : ℕ) : ZMod pw.val) hord hpinv hNinv
      (Finset.Ico startU.val endU.val) (fun u => entryK pw.val a u)
      (fun u => entryK pw.val b u) t ht]
  -- the offset: `aux_mul` gives `(boff * L) mod p`, which is `boff * L` in `ZMod p`
  congr 1
  rw [hscv]
  rw [ZMod.natCast_mod]
  push_cast
  rw [hlenv]

/-! ## 6. The conversion loop, over an abstract reconstructed value

`NttCRT.garner_spec` is already stated for an arbitrary `x` with `x < P` as a
hypothesis, so nothing about the CRT step needs generalizing -- only this loop,
which is a different extracted constant from `ntt::negconv_mod_q_loop`. Stating
it over an abstract `X` keeps the *bound* a hypothesis rather than baking in a
single product's `offConvW`, which is what lets the fused caller supply the
summed value. -/

theorem garner_out_spec (degU : Std.Usize) (qwU : Std.U128)
    (r1 r2 r3 : alloc.vec.Vec Std.U64) (out : alloc.vec.Vec cpoly.field.Fp)
    (tU : Std.Usize) (X : ℕ → ℕ)
    (hdeg : degU.val = N) (hqwv : qwU.val = HachiEquiv.NttProduct.q)
    (hXP : ∀ k, k < N → X k < NttCRT.P)
    (hv1 : ∀ k, k < N → wordAt r1 k = X k % NttCRT.p1)
    (hv2 : ∀ k, k < N → wordAt r2 k = X k % NttCRT.p2)
    (hv3 : ∀ k, k < N → wordAt r3 k = X k % NttCRT.p3)
    (hl1 : r1.val.length = N) (hl2 : r2.val.length = N) (hl3 : r3.val.length = N)
    (ht : tU.val ≤ N) (hlen : out.val.length = tU.val)
    (hred : ∀ u ∈ out.val, HachiEquiv.Field.Red u)
    (hval : ∀ k, k < tU.val →
      HachiEquiv.Ring.wordN out k = X k % HachiEquiv.NttProduct.q) :
    ring.dot_fused_loop0_loop0 degU qwU r1 r2 r3 out tU
      ⦃ z => HachiEquiv.Ring.Wf z ∧ ∀ k, k < N →
          HachiEquiv.Ring.wordN z k = X k % HachiEquiv.NttProduct.q ⦄ := by
  rw [ring.dot_fused_loop0_loop0]
  apply loop.spec_decr_nat (fun r => N - r.2.val)
    (fun r => r.2.val ≤ N ∧ r.1.val.length = r.2.val
      ∧ (∀ u ∈ r.1.val, HachiEquiv.Field.Red u)
      ∧ ∀ k, k < r.2.val →
          HachiEquiv.Ring.wordN r.1 k = X k % HachiEquiv.NttProduct.q)
  · rintro ⟨o1, tt⟩ ⟨htt, hlen1, hred1, hval1⟩
    dsimp only at htt hlen1 hred1 hval1
    simp only [ring.dot_fused_loop0_loop0.body]
    by_cases hlt : tt < degU
    · rw [if_pos hlt]
      have httlt : tt.val < N := by rw [← hdeg]; scalar_tac
      have hb1 : tt.val < r1.val.length := by rw [hl1]; exact httlt
      have hb2 : tt.val < r2.val.length := by rw [hl2]; exact httlt
      have hb3 : tt.val < r3.val.length := by rw [hl3]; exact httlt
      step as ⟨x1, hx1⟩
      step as ⟨x2, hx2⟩
      step as ⟨x3, hx3⟩
      have hx1v : x1.val = X tt.val % NttCRT.p1 := by
        rw [hx1, ← wordAt_of_lt (v := r1) (t := tt.val) hb1]; exact hv1 tt.val httlt
      have hx2v : x2.val = X tt.val % NttCRT.p2 := by
        rw [hx2, ← wordAt_of_lt (v := r2) (t := tt.val) hb2]; exact hv2 tt.val httlt
      have hx3v : x3.val = X tt.val % NttCRT.p3 := by
        rw [hx3, ← wordAt_of_lt (v := r3) (t := tt.val) hb3]; exact hv3 tt.val httlt
      step with NttCRT.garner_spec x1 x2 x3 (X tt.val) (hXP tt.val httlt)
        hx1v hx2v hx3v as ⟨g, hgv⟩
      step as ⟨md, hmd⟩
      have hmdv : md.val = X tt.val % HachiEquiv.NttProduct.q := by
        rw [hmd, hgv, hqwv]
      have hmdlt : md.val < HachiEquiv.NttProduct.q := by
        rw [hmdv]; exact Nat.mod_lt _ (by norm_num [HachiEquiv.NttProduct.q])
      have hcast : lift (UScalar.cast .U64 md)
          ⦃ y => y.val = md.val ⦄ :=
        UScalar.cast_inBounds_spec .U64 md (by
          have hq : md.val < 4294967197 := by
            have := hmdlt; simpa [HachiEquiv.NttProduct.q] using this
          simp only [UScalar.max, UScalarTy.numBits]
          omega)
      step with hcast as ⟨w, hw⟩
      step with HachiEquiv.Field.fp_new_spec w as ⟨f, hfred, hfval⟩
      step as ⟨o2, ho2⟩
      step as ⟨tt1, htt1⟩
      refine ⟨by rw [htt1]; omega, ?_, ?_, ?_, by rw [htt1]; omega⟩
      · rw [ho2, htt1, List.length_append, hlen1]; simp
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with hm | hm
        · exact hred1 u hm
        · rw [List.mem_singleton.mp hm]; exact hfred
      · intro k hk
        rw [htt1] at hk
        simp only [HachiEquiv.Ring.wordN] at hval1 ⊢
        rcases Nat.lt_or_ge k tt.val with hklt | hkge
        · rw [ho2, getD_append_lt' _ _ _ (by omega)]
          exact hval1 k hklt
        · have hkeq : k = o1.val.length := by omega
          rw [hkeq, ho2, getD_append_eq', hlen1]
          -- `Fp.new` on an already-reduced word is the identity on `.val`
          have hwlt : w.val < HachiEquiv.NttProduct.q := by rw [hw]; exact hmdlt
          have hfv : f.val = w.val := by
            have h1 := HachiEquiv.NttProduct.natCast_inj_of_lt
              (n := HachiEquiv.NttProduct.q) (x := f.val) (y := w.val) hfred hfval
            rwa [Nat.mod_eq_of_lt hwlt] at h1
          rw [hfv, hw, hmdv]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : tt.val = N := by rw [← hdeg]; scalar_tac
      exact ⟨⟨by rw [hlen1, heq], hred1⟩,
        fun k hk => hval1 k (by rw [heq]; exact hk)⟩
  · exact ⟨ht, hlen, hred, hval⟩

/-! ## 7. The antidiagonals, at the ring level

`NttProduct`'s `posW`/`negW` are over `Vec Std.U64` buffers read by `wordAt`;
the fused dot's operands are `ring.Rq` entries read by `Ring.wordN`. Same
definitions, same two cast lemmas, one type across. -/

theorem ordConvQ_cast_pos (pp : ℕ) (x y : ring.Rq) (k : ℕ) (hk : k < N) :
    NttMath.ordConv N (fun u => ((HachiEquiv.Ring.wordN x u : ℕ) : ZMod pp))
        (fun u => ((HachiEquiv.Ring.wordN y u : ℕ) : ZMod pp)) k
      = ((HachiEquiv.Ring.posSum x y k N : ℕ) : ZMod pp) := by
  unfold NttMath.ordConv HachiEquiv.Ring.posSum
  push_cast
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp only [Finset.mem_range] at hi
  by_cases hle : i ≤ k
  · rw [if_pos (And.intro hle (by omega : k - i < N)), if_pos hle]
  · rw [if_neg (by omega : ¬(i ≤ k ∧ k - i < N)), if_neg hle]

theorem ordConvQ_cast_neg (pp : ℕ) (x y : ring.Rq) (k : ℕ) (hk : k < N) :
    NttMath.ordConv N (fun u => ((HachiEquiv.Ring.wordN x u : ℕ) : ZMod pp))
        (fun u => ((HachiEquiv.Ring.wordN y u : ℕ) : ZMod pp)) (N + k)
      = ((HachiEquiv.Ring.negSum x y k N : ℕ) : ZMod pp) := by
  unfold NttMath.ordConv HachiEquiv.Ring.negSum
  push_cast
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp only [Finset.mem_range] at hi
  by_cases hle : i ≤ k
  · rw [if_neg (by omega : ¬(i ≤ N + k ∧ N + k - i < N)), if_pos hle]
  · rw [if_pos (And.intro (by omega) (by omega : N + k - i < N)), if_neg hle]

/-- The offset value a fused chunk reconstructs: the summed antidiagonals with
**one** `BOUND` per term.

`Ring.posSum`/`Ring.negSum` are reused rather than restated -- they are exactly
these antidiagonals at `m = N`, and reusing them also brings
`Ring.posSum_cast`/`negSum_cast` (the antidiagonal conversions mod `q`) into
reach for free. -/
def offConvSum (a b : alloc.vec.Vec ring.Rq) (st en k : ℕ) : ℕ :=
  (∑ u ∈ Finset.Ico st en,
      HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
           (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
    + (en - st) * HachiEquiv.NttProduct.BOUND
  - ∑ u ∈ Finset.Ico st en,
      HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
           (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N

/-- [`ordConvQ_cast_pos`] phrased through [`entryK`], which is definitionally the
operand shape but does not unfold under `simp` (it is a plain `def` returning a
function). -/
theorem ordConv_entryK_pos (pp : ℕ) (a b : alloc.vec.Vec ring.Rq) (u k : ℕ) (hk : k < N) :
    NttMath.ordConv N (entryK pp a u) (entryK pp b u) k
      = ((HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
            (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod pp) :=
  ordConvQ_cast_pos pp _ _ k hk

theorem ordConv_entryK_neg (pp : ℕ) (a b : alloc.vec.Vec ring.Rq) (u k : ℕ) (hk : k < N) :
    NttMath.ordConv N (entryK pp a u) (entryK pp b u) (N + k)
      = ((HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
            (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod pp) :=
  ordConvQ_cast_neg pp _ _ k hk

theorem negQ_sum_le (a b : alloc.vec.Vec ring.Rq) (st en k : ℕ)
    (hawf : ∀ u, u < en → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbwf : ∀ u, u < en → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))) :
    (∑ u ∈ Finset.Ico st en,
        HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
             (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
      ≤ (en - st) * HachiEquiv.NttProduct.BOUND := by
  calc (∑ u ∈ Finset.Ico st en,
          HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
               (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
      ≤ ∑ _u ∈ Finset.Ico st en, HachiEquiv.NttProduct.BOUND := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        simp only [Finset.mem_Ico] at hu
        exact HachiEquiv.Ring.negSum_le (hawf u hu.2) (hbwf u hu.2) k N
    _ = (en - st) * HachiEquiv.NttProduct.BOUND := by
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]

theorem posQ_sum_le (a b : alloc.vec.Vec ring.Rq) (st en k : ℕ)
    (hawf : ∀ u, u < en → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbwf : ∀ u, u < en → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))) :
    (∑ u ∈ Finset.Ico st en,
        HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
             (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
      ≤ (en - st) * HachiEquiv.NttProduct.BOUND := by
  calc (∑ u ∈ Finset.Ico st en,
          HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
               (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
      ≤ ∑ _u ∈ Finset.Ico st en, HachiEquiv.NttProduct.BOUND := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        simp only [Finset.mem_Ico] at hu
        exact HachiEquiv.Ring.posSum_le (hawf u hu.2) (hbwf u hu.2) k N
    _ = (en - st) * HachiEquiv.NttProduct.BOUND := by
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]

/-- **The CRT fit.** `offConvSum ≤ 2 · L · BOUND`, and `2 · DOT_CHUNK · BOUND < P`
with 1.52x to spare. This inequality is what pins `DOT_CHUNK = 8192`: at
`L = 12469` it fails, and the reconstruction would return a different integer. -/
theorem offConvSum_lt_P (a b : alloc.vec.Vec ring.Rq) (st en k : ℕ)
    (hawf : ∀ u, u < en → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbwf : ∀ u, u < en → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hL : en - st ≤ 8192) :
    offConvSum a b st en k < NttCRT.P := by
  have hp := posQ_sum_le a b st en k hawf hbwf
  have hnum : 2 * 8192 * HachiEquiv.NttProduct.BOUND < NttCRT.P := by
    simp only [HachiEquiv.NttProduct.BOUND, HachiEquiv.NttProduct.q, NttCRT.P,
      NttCRT.p1, NttCRT.p2, NttCRT.p3]
    norm_num
  have hmul : (en - st) * HachiEquiv.NttProduct.BOUND
      ≤ 8192 * HachiEquiv.NttProduct.BOUND := Nat.mul_le_mul_right _ hL
  unfold offConvSum
  omega

/-! ## 8. One chunk, at the word level

The summed analogue of `NttProduct.negconv_mod_p_word`: the `ZMod p` statement
[`dot_chunk_mod_p_spec`] delivers, read back as a residue of the natural number
[`offConvSum`]. The one new step is the offset: `boff · L` on the `ZMod` side
against `L · BOUND` in the natural, which agree because `boff = BOUND % p`. -/

theorem dot_chunk_word_spec (a b : alloc.vec.Vec ring.Rq) (startU endU : Std.Usize)
    (pw mw psi psiinv ninv boff : Std.U64) (h : Magic pw mw)
    (hpsi : psi.val < pw.val) (hpsii : psiinv.val < pw.val)
    (hninv : ninv.val < pw.val) (hboff : boff.val < pw.val)
    (hord : ((psi.val : ℕ) : ZMod pw.val) ^ N = -1)
    (hpinv : ((psi.val : ℕ) : ZMod pw.val) * ((psiinv.val : ℕ) : ZMod pw.val) = 1)
    (hNinv : ((N : ℕ) : ZMod pw.val) * ((ninv.val : ℕ) : ZMod pw.val) = 1)
    (hboffv : boff.val = HachiEquiv.NttProduct.BOUND % pw.val)
    (hawf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbwf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hae : endU.val ≤ a.val.length) (hbe : endU.val ≤ b.val.length)
    (hse : startU.val ≤ endU.val) (hlenp : endU.val - startU.val < pw.val) :
    ring.dot_chunk_mod_p a b startU endU pw mw psi psiinv ninv boff
      ⦃ z => Canon pw.val z ∧ ∀ k, k < N → wordAt z k
              = offConvSum a b startU.val endU.val k % pw.val ⦄ := by
  have hppos : 0 < pw.val := h.pos
  apply spec_mono (dot_chunk_mod_p_spec a b startU endU pw mw psi psiinv ninv boff
    h hpsi hpsii hninv hboff hord hpinv hNinv hawf hbwf hae hbe hse hlenp)
  rintro z ⟨hcanon, hval⟩
  refine ⟨hcanon, ?_⟩
  intro k hk
  -- the truncating subtraction in `offConvSum` is honest
  have hnb := negQ_sum_le a b startU.val endU.val k hawf hbwf
  have hle : (∑ u ∈ Finset.Ico startU.val endU.val,
        HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
             (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
      ≤ (∑ u ∈ Finset.Ico startU.val endU.val,
          HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
               (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
        + (endU.val - startU.val) * HachiEquiv.NttProduct.BOUND :=
    le_trans hnb (Nat.le_add_left _ _)
  have hoff : ((offConvSum a b startU.val endU.val k : ℕ) : ZMod pw.val)
      = ((∑ u ∈ Finset.Ico startU.val endU.val,
            HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                 (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod pw.val)
        + (((endU.val - startU.val) * HachiEquiv.NttProduct.BOUND : ℕ) : ZMod pw.val)
        - ((∑ u ∈ Finset.Ico startU.val endU.val,
            HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                 (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod pw.val) := by
    unfold offConvSum
    rw [Nat.cast_sub hle, Nat.cast_add]
  have hcast : ((wordAt z k : ℕ) : ZMod pw.val)
      = ((offConvSum a b startU.val endU.val k : ℕ) : ZMod pw.val) := by
    have h1 := hval k hk
    rw [resK] at h1
    rw [h1, hoff]
    -- each term's `negConvR` is its two antidiagonals
    have hterm : ∀ u, NttMath.negConvR N (entryK pw.val a u) (entryK pw.val b u) k
        = ((HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
              (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod pw.val)
          - ((HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
              (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod pw.val) := by
      intro u
      rw [NttMath.negConvR, ordConv_entryK_pos pw.val a b u k hk,
        ordConv_entryK_neg pw.val a b u k hk]
    rw [Finset.sum_congr rfl (fun u _ => hterm u), Finset.sum_sub_distrib]
    push_cast
    rw [hboffv, ZMod.natCast_mod]
    push_cast
    ring
  exact HachiEquiv.NttProduct.natCast_inj_of_lt (wordAt_lt hcanon hppos k) hcast

/-! ## 9. The chunk, read mod `q`

`BOUND = N · q²` is divisible by `q`, so the per-term offsets vanish mod `q`
however many of them there are -- which is why scaling the offset by the chunk
length costs the caller nothing to correct. `Ring.posSum_cast`/`negSum_cast`
then turn each term's antidiagonals into its `Ring.negConv`. -/

theorem offConvSum_cast_q (a b : alloc.vec.Vec ring.Rq) (st en k : ℕ) (hk : k < N)
    (hawf : ∀ u, u < en → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbwf : ∀ u, u < en → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))) :
    ((offConvSum a b st en k : ℕ) : ZMod HachiEquiv.Field.q)
      = ∑ u ∈ Finset.Ico st en, HachiEquiv.Ring.negConv
          (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
          (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k := by
  have hle := negQ_sum_le a b st en k hawf hbwf
  have hle' : (∑ u ∈ Finset.Ico st en,
        HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
             (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
      ≤ (∑ u ∈ Finset.Ico st en,
          HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
               (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
        + (en - st) * HachiEquiv.NttProduct.BOUND := le_trans hle (Nat.le_add_left _ _)
  unfold offConvSum
  rw [Nat.cast_sub hle', Nat.cast_add, Nat.cast_sum, Nat.cast_sum]
  -- `BOUND` is a multiple of `q`, so `L · BOUND` vanishes mod `q`
  have hB : (((en - st) * HachiEquiv.NttProduct.BOUND : ℕ) : ZMod HachiEquiv.Field.q) = 0 := by
    have : HachiEquiv.NttProduct.BOUND = 1024 * HachiEquiv.Field.q * HachiEquiv.Field.q := by
      simp only [HachiEquiv.NttProduct.BOUND, HachiEquiv.NttProduct.q, HachiEquiv.Field.q]
    rw [this]
    push_cast
    simp [ZMod.natCast_self]
  rw [hB, add_zero, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  simp only [Finset.mem_Ico] at hu
  rw [HachiEquiv.Ring.negConv,
    ← HachiEquiv.Ring.posSum_cast (hawf u hu.2) (hbwf u hu.2) hk,
    ← HachiEquiv.Ring.negSum_cast (hawf u hu.2) (hbwf u hu.2) hk]

/-! ## 10. The chunk loop

One chunk per iteration: three per-prime pipelines, one Garner reconstruction,
one ring-level addition. The invariant is the partial fold
`∑_{u < start} negConv aᵤ bᵤ`, and the step extends it by the chunk's own
`Finset.Ico start end`, which `Finset.sum_Ico_consecutive` splices on. -/

theorem chunk_loop_spec (a b : alloc.vec.Vec ring.Rq) (nU degU : Std.Usize)
    (qwU : Std.U128) (acc : ring.Rq) (startU : Std.Usize)
    (haw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (han : nU.val ≤ a.val.length) (hbn : nU.val ≤ b.val.length)
    (hdeg : degU.val = N) (hqw : qwU.val = HachiEquiv.NttProduct.q)
    (hs : startU.val ≤ nU.val) (hacc : HachiEquiv.Ring.Wf acc)
    (hval : ∀ k, k < N → HachiEquiv.Ring.coeffK acc k
              = ∑ u ∈ Finset.range startU.val, HachiEquiv.Ring.negConv
                  (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                  (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k) :
    ring.dot_fused_loop0 a b nU degU qwU acc startU
      ⦃ z => HachiEquiv.Ring.Wf z ∧ ∀ k, k < N → HachiEquiv.Ring.coeffK z k
              = ∑ u ∈ Finset.range nU.val, HachiEquiv.Ring.negConv
                  (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                  (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k ⦄ := by
  rw [ring.dot_fused_loop0]
  apply loop.spec_decr_nat (fun r => nU.val - r.2.val)
    (fun r => r.2.val ≤ nU.val ∧ HachiEquiv.Ring.Wf r.1
      ∧ ∀ k, k < N → HachiEquiv.Ring.coeffK r.1 k
              = ∑ u ∈ Finset.range r.2.val, HachiEquiv.Ring.negConv
                  (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                  (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k)
  · rintro ⟨d, st⟩ ⟨hst, hdw, hdv⟩
    dsimp only at hst hdw hdv
    simp only [ring.dot_fused_loop0.body]
    by_cases hlt : st < nU
    · rw [if_pos hlt]
      have hstlt : st.val < nU.val := by scalar_tac
      -- `remaining`, then `take`, then `start + take`: the sum is bounded by
      -- `n`, so the add needs no headroom from the caller
      step as ⟨rem, hrem⟩
      have hite : (if rem < ring.DOT_CHUNK then ok rem else ok ring.DOT_CHUNK)
          = ok (if rem < ring.DOT_CHUNK then rem else ring.DOT_CHUNK) := by
        split_ifs <;> rfl
      rw [hite]
      set tk : Std.Usize := if rem < ring.DOT_CHUNK then rem else ring.DOT_CHUNK with htk
      have hdc : (ring.DOT_CHUNK).val = 8192 := by simp only [ring.DOT_CHUNK]; rfl
      have hremv : rem.val = nU.val - st.val := hrem
      have htkle : tk.val ≤ rem.val := by
        rw [htk]; split_ifs with hc
        · exact le_refl _
        · have : ¬ (rem.val < (ring.DOT_CHUNK).val) := by scalar_tac
          omega
      have htk8 : tk.val ≤ 8192 := by
        rw [htk]; split_ifs with hc
        · have : rem.val < (ring.DOT_CHUNK).val := by scalar_tac
          rw [hdc] at this; omega
        · rw [hdc]
      have htkpos : 0 < tk.val := by
        rw [htk]; split_ifs
        · rw [hremv]; omega
        · rw [hdc]; omega
      clear_value tk
      step as ⟨en, hen⟩
      have henv : en.val = st.val + tk.val := hen
      have hennU : en.val ≤ nU.val := by rw [henv, hremv] at *; omega
      have hsen : st.val ≤ en.val := by rw [henv]; omega
      have hsen' : st.val < en.val := by rw [henv]; omega
      have hL : en.val - st.val ≤ 8192 := by rw [henv]; omega
      have hawe : ∀ u, u < en.val → HachiEquiv.Ring.Wf
          (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) :=
        fun u hu => haw u (by omega)
      have hbwe : ∀ u, u < en.val → HachiEquiv.Ring.Wf
          (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) :=
        fun u hu => hbw u (by omega)
      have hae : en.val ≤ a.val.length := le_trans hennU han
      have hbe : en.val ≤ b.val.length := le_trans hennU hbn
      obtain ⟨hp1, hpi1, hn1, hb1⟩ := HachiEquiv.NttProduct.aux1_lt
      obtain ⟨hp2, hpi2, hn2, hb2⟩ := HachiEquiv.NttProduct.aux2_lt
      obtain ⟨hp3, hpi3, hn3, hb3⟩ := HachiEquiv.NttProduct.aux3_lt
      step with dot_chunk_word_spec a b st en ntt.AUX_P1 ntt.AUX_M1 ntt.AUX_PSI1
        ntt.AUX_PSIINV1 ntt.AUX_NINV1 ntt.AUX_BOFF1 NttCRT.magic1 hp1 hpi1 hn1 hb1
        HachiEquiv.NttProduct.psi1_ord HachiEquiv.NttProduct.psi1_inv
        HachiEquiv.NttProduct.ninv1_inv HachiEquiv.NttProduct.boff1_val
        hawe hbwe hae hbe hsen
        (by rw [NttCRT.AUX_P1_val]; exact lt_of_le_of_lt hL (by norm_num))
        as ⟨r1, hc1, hw1⟩
      step with dot_chunk_word_spec a b st en ntt.AUX_P2 ntt.AUX_M2 ntt.AUX_PSI2
        ntt.AUX_PSIINV2 ntt.AUX_NINV2 ntt.AUX_BOFF2 NttCRT.magic2 hp2 hpi2 hn2 hb2
        HachiEquiv.NttProduct.psi2_ord HachiEquiv.NttProduct.psi2_inv
        HachiEquiv.NttProduct.ninv2_inv HachiEquiv.NttProduct.boff2_val
        hawe hbwe hae hbe hsen
        (by rw [NttCRT.AUX_P2_val]; exact lt_of_le_of_lt hL (by norm_num))
        as ⟨r2, hc2, hw2⟩
      step with dot_chunk_word_spec a b st en ntt.AUX_P3 ntt.AUX_M3 ntt.AUX_PSI3
        ntt.AUX_PSIINV3 ntt.AUX_NINV3 ntt.AUX_BOFF3 NttCRT.magic3 hp3 hpi3 hn3 hb3
        HachiEquiv.NttProduct.psi3_ord HachiEquiv.NttProduct.psi3_inv
        HachiEquiv.NttProduct.ninv3_inv HachiEquiv.NttProduct.boff3_val
        hawe hbwe hae hbe hsen
        (by rw [NttCRT.AUX_P3_val]; exact lt_of_le_of_lt hL (by norm_num))
        as ⟨r3, hc3, hw3⟩
      rw [NttCRT.AUX_P1_val] at hw1
      rw [NttCRT.AUX_P2_val] at hw2
      rw [NttCRT.AUX_P3_val] at hw3
      simp only [alloc.vec.Vec.with_capacity]
      step with garner_out_spec degU qwU r1 r2 r3 (alloc.vec.Vec.new cpoly.field.Fp)
        0#usize (fun k => offConvSum a b st.val en.val k) hdeg hqw
        (fun k _ => offConvSum_lt_P a b st.val en.val k hawe hbwe hL)
        hw1 hw2 hw3 hc1.1 hc2.1 hc3.1 (by simp) (by simp)
        (by intro u hu; simp at hu) (by intro k hk; simp at hk)
        as ⟨out1, ho1wf, ho1v⟩
      step with HachiEquiv.Ring.add_spec d out1 hdw ho1wf as ⟨acc1, hacwf, hacv⟩
      refine ⟨by omega, hacwf, ?_, by omega⟩
      intro k hk
      -- `NttProduct.q` and `Field.q` are the same numeral under two names, which
      -- `ZMod.natCast_mod` needs aligned before it will fire
      have hqq : HachiEquiv.NttProduct.q = HachiEquiv.Field.q := rfl
      rw [hacv k hk, hdv k hk, HachiEquiv.Ring.coeffK_eq_cast_wordN, ho1v k hk,
        hqq, ZMod.natCast_mod,
        offConvSum_cast_q a b st.val en.val k hk hawe hbwe,
        Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.sum_Ico_consecutive _ (Nat.zero_le _) hsen]

    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : st.val = nU.val := by scalar_tac
      exact ⟨hdw, fun k hk => by rw [hdv k hk, heq]⟩
  · exact ⟨hs, hacc, hval⟩

/-! ## 11. `ring::dot_fused`

The chunk loop from a zero accumulator, with the empty fold as its initial
invariant. -/

theorem dot_fused_spec (a b : alloc.vec.Vec ring.Rq) (nU : Std.Usize)
    (haw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (han : nU.val ≤ a.val.length) (hbn : nU.val ≤ b.val.length) :
    ring.dot_fused a b nU
      ⦃ z => HachiEquiv.Ring.Wf z ∧ ∀ k, k < N → HachiEquiv.Ring.coeffK z k
              = ∑ u ∈ Finset.range nU.val, HachiEquiv.Ring.negConv
                  (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                  (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k ⦄ := by
  rw [ring.dot_fused]
  have hcq : lift (UScalar.cast .U128 params.Q) ⦃ y => y.val = (params.Q).val ⦄ :=
    UScalar.cast_inBounds_spec .U128 params.Q (NttCRT.u64_le_u128_max _)
  step with hcq as ⟨qw, hqw⟩
  rw [HachiEquiv.Field.params_Q_val] at hqw
  step with HachiEquiv.Ring.zero_spec as ⟨z0, hz0wf, hz0v⟩
  exact chunk_loop_spec a b nU params.RING_DEGREE qw z0 0#usize haw hbw han hbn
    HachiEquiv.Ring.params_RING_DEGREE_val hqw (by simp) hz0wf
    (by intro k hk; rw [hz0v k]; simp)

/-! ## 12. `ring::slice_out` and `ring::mac_into`

Candidate T19 Change 4's two leaf functions. They exist as separate functions
for an *extraction* reason, not a mathematical one: reading a borrowed buffer
inside a loop that also writes an accumulator makes the pinned Aeneas abort in
`filter_loop_useless_inputs_outputs`, and hoisting the read without flattening
the nesting does not help. See the ceiling table in the `aeneas-extract` skill.

`mac_into` is [`accum_spec`] with a multiply in front; `slice_out` is a push
loop over a shifted index. -/

theorem slice_out_spec (pfwd : alloc.vec.Vec Std.U64) (baseU nU : Std.Usize)
    (out : alloc.vec.Vec Std.U64) (cU : Std.Usize)
    (hn : nU.val = N) (hc : cU.val ≤ N) (hlen : out.val.length = cU.val)
    (hb : baseU.val + N ≤ pfwd.val.length)
    (hval : ∀ t, t < cU.val → wordAt out t = wordAt pfwd (baseU.val + t)) :
    ring.slice_out_loop pfwd baseU nU out cU
      ⦃ z => z.val.length = N
             ∧ ∀ t, t < N → wordAt z t = wordAt pfwd (baseU.val + t) ⦄ := by
  rw [ring.slice_out_loop]
  apply loop.spec_decr_nat (fun r => nU.val - r.2.val)
    (fun r => r.2.val ≤ N ∧ r.1.val.length = r.2.val
      ∧ ∀ t, t < r.2.val → wordAt r.1 t = wordAt pfwd (baseU.val + t))
  · rintro ⟨d, cc⟩ ⟨hcc, hdl, hdv⟩
    dsimp only at hcc hdl hdv
    simp only [ring.slice_out_loop.body]
    by_cases hlt : cc < nU
    · rw [if_pos hlt]
      have hcclt : cc.val < N := by rw [← hn]; scalar_tac
      step as ⟨idx, hidx⟩
      step as ⟨x, hx⟩
      have hib : idx.val = baseU.val + cc.val := hidx
      -- rewrite the index BEFORE bridging to `getElem`; the other order leaves
      -- the motive ill-typed, since the bound proof depends on the index
      have hxv : x.val = wordAt pfwd (baseU.val + cc.val) := by
        simp only [wordAt]
        rw [← hib, List.getD_eq_getElem _ _ (by rw [hib]; omega), hx]
      step as ⟨d1, hd1⟩
      step as ⟨cc1, hcc1⟩
      refine ⟨by rw [hcc1]; omega, ?_, ?_, by rw [hcc1]; omega⟩
      · rw [hd1, hcc1, List.length_append, hdl]; simp
      · intro t ht
        rw [hcc1] at ht
        simp only [wordAt] at hdv ⊢
        rcases Nat.lt_or_ge t cc.val with hlt2 | hge
        · rw [hd1, getD_append_lt' _ _ _ (by omega)]
          exact hdv t hlt2
        · have hteq : t = d.val.length := by omega
          rw [hteq, hd1, getD_append_eq', hdl, hxv]
          rfl
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : cc.val = N := by rw [← hn]; scalar_tac
      exact ⟨by rw [hdl, heq], fun t ht => hdv t (by rw [heq]; exact ht)⟩
  · exact ⟨hc, hlen, hval⟩

theorem mac_into_spec (acc af bf : alloc.vec.Vec Std.U64) (nU : Std.Usize)
    (pw mw : Std.U64) (kU : Std.Usize) (base : ℕ → ZMod pw.val)
    (h : Magic pw mw) (hn : nU.val = N) (hk : kU.val ≤ N)
    (hacc : Canon pw.val acc) (haf : Canon pw.val af) (hbf : Canon pw.val bf)
    (hval : ∀ t, t < N → resK pw.val acc t
              = base t + (if t < kU.val then
                  resK pw.val af t * resK pw.val bf t else 0)) :
    ring.mac_into_loop af bf nU pw mw acc kU
      ⦃ z => Canon pw.val z ∧ ∀ t, t < N → resK pw.val z t
              = base t + resK pw.val af t * resK pw.val bf t ⦄ := by
  have hppos : 0 < pw.val := h.pos
  rw [ring.mac_into_loop]
  apply loop.spec_decr_nat (fun r => nU.val - r.2.val)
    (fun r => r.2.val ≤ N ∧ Canon pw.val r.1
      ∧ ∀ t, t < N → resK pw.val r.1 t
              = base t + (if t < r.2.val then
                  resK pw.val af t * resK pw.val bf t else 0))
  · rintro ⟨d, kk⟩ ⟨hkk, hcd, hw⟩
    dsimp only at hkk hcd hw
    simp only [ring.mac_into_loop.body]
    by_cases hlt : kk < nU
    · rw [if_pos hlt]
      have hklt : kk.val < N := by rw [← hn]; scalar_tac
      have hab : kk.val < af.val.length := by rw [haf.1]; exact hklt
      have hbb : kk.val < bf.val.length := by rw [hbf.1]; exact hklt
      have hdb : kk.val < d.val.length := by rw [hcd.1]; exact hklt
      step as ⟨x, hx⟩
      step as ⟨y, hy⟩
      have hxv : x.val = wordAt af kk.val := by
        rw [hx, ← wordAt_of_lt (v := af) (t := kk.val) hab]
      have hyv : y.val = wordAt bf kk.val := by
        rw [hy, ← wordAt_of_lt (v := bf) (t := kk.val) hbb]
      have hxlt : x.val < pw.val := by rw [hxv]; exact wordAt_lt haf hppos _
      have hylt : y.val < pw.val := by rw [hyv]; exact wordAt_lt hbf hppos _
      step with aux_mul_lt x y pw mw h hxlt hylt as ⟨pr, hprv, hprlt⟩
      step as ⟨cur, hcur⟩
      have hcurv : cur.val = wordAt d kk.val := by
        rw [hcur, ← wordAt_of_lt (v := d) (t := kk.val) hdb]
      have hcurlt : cur.val < pw.val := by rw [hcurv]; exact wordAt_lt hcd hppos _
      step with aux_add_lt cur pr pw h.lt_pow hcurlt hprlt as ⟨z, hzv, hzlt⟩
      step as ⟨elem, back, helem, hback⟩
      step as ⟨kk1, hkk1⟩
      rw [hback]
      refine ⟨by rw [hkk1]; omega, Canon_set hcd hzlt, ?_, by rw [hkk1]; omega⟩
      intro t ht
      rw [hkk1]
      by_cases heq : t = kk.val
      · rw [heq]
        simp only [resK]
        rw [wordAt_set_eq hdb, hzv, hprv]
        have hc1 : ((((cur.val + (x.val * y.val) % pw.val) % pw.val : ℕ)) : ZMod pw.val)
            = ((cur.val : ℕ) : ZMod pw.val)
              + ((x.val : ℕ) : ZMod pw.val) * ((y.val : ℕ) : ZMod pw.val) := by
          rw [ZMod.natCast_mod]; push_cast; rw [ZMod.natCast_mod]; push_cast; ring
        rw [hc1, hcurv, hxv, hyv]
        have hbase := hw kk.val hklt
        simp only [resK] at hbase
        rw [hbase, if_neg (by omega), add_zero, if_pos (by omega)]
      · simp only [resK]
        rw [wordAt_set_ne heq]
        have hbase := hw t ht
        simp only [resK] at hbase
        rw [hbase]
        by_cases hlt2 : t < kk.val
        · rw [if_pos hlt2, if_pos (by omega)]
        · rw [if_neg hlt2, if_neg (by omega)]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : kk.val = N := by rw [← hn]; scalar_tac
      refine ⟨hcd, ?_⟩
      intro t ht
      rw [hw t ht, heq, if_pos ht]
  · exact ⟨hk, hacc, hval⟩

/-! ## 13. `ring::prepare_one` -- the layout claim

The only genuinely new fact Change 4 needs: the table holds what the forward
transform would have produced, at **absolute** offset `j * NTT_LEN`.

The offset being absolute rather than per-chunk is the one mistake preparation
can make that the unprepared path cannot, so it is stated that way on purpose.
The Rust-side oracle was checked to catch the per-chunk version: it fails at
exactly `n = 8193`, the first width that runs the chunk loop twice, and passes
at every single-chunk width. -/

/-- Entry `j`'s words, copied into a fresh buffer. [`words_a_spec`]'s shape, for
a different extracted constant. -/
theorem prep_words_spec (a : alloc.vec.Vec ring.Rq) (degU jU : Std.Usize)
    (w : alloc.vec.Vec Std.U64) (tU : Std.Usize)
    (hdeg : degU.val = N) (hjb : jU.val < a.val.length)
    (haj : HachiEquiv.Ring.Wf (a.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)))
    (ht : tU.val ≤ N) (hlen : w.val.length = tU.val)
    (hval : ∀ t, t < tU.val → wordAt w t
      = HachiEquiv.Ring.wordN (a.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) t) :
    ring.prepare_one_loop0_loop0 a degU jU w tU
      ⦃ z => z.val.length = N ∧ ∀ t, t < N → wordAt z t
          = HachiEquiv.Ring.wordN
              (a.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) t ⦄ := by
  rw [ring.prepare_one_loop0_loop0]
  apply loop.spec_decr_nat (fun r => degU.val - r.2.val)
    (fun r => r.2.val ≤ N ∧ r.1.val.length = r.2.val
      ∧ ∀ t, t < r.2.val → wordAt r.1 t
          = HachiEquiv.Ring.wordN
              (a.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) t)
  · rintro ⟨d, tt⟩ ⟨htt, hdl, hdv⟩
    dsimp only at htt hdl hdv
    simp only [ring.prepare_one_loop0_loop0.body]
    by_cases hlt : tt < degU
    · rw [if_pos hlt]
      have httlt : tt.val < N := by rw [← hdeg]; scalar_tac
      step as ⟨r, hr⟩
      have hrv : r = a.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp) := by
        rw [hr, List.getD_eq_getElem _ _ hjb]
      have hrb : tt.val < r.val.length := by rw [hrv, haj.1]; exact httlt
      step as ⟨f, hf⟩
      step with HachiEquiv.Ring.to_u64_id f as ⟨x, hx⟩
      have hxv : x.val = HachiEquiv.Ring.wordN
          (a.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) tt.val := by
        rw [hx, hf, ← hrv]
        unfold HachiEquiv.Ring.wordN
        rw [List.getD_eq_getElem _ _ hrb]
      step as ⟨d1, hd1⟩
      step as ⟨tt1, htt1⟩
      refine ⟨by rw [htt1]; omega, ?_, ?_, by rw [htt1]; omega⟩
      · rw [hd1, htt1, List.length_append, hdl]; simp
      · intro t htl
        rw [htt1] at htl
        simp only [wordAt] at hdv ⊢
        rcases Nat.lt_or_ge t tt.val with hlt2 | hge
        · rw [hd1, getD_append_lt' _ _ _ (by omega)]
          exact hdv t hlt2
        · have hteq : t = d.val.length := by omega
          rw [hteq, hd1, getD_append_eq', hdl, hxv]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : tt.val = N := by rw [← hdeg]; scalar_tac
      exact ⟨by rw [hdl, heq], fun t htl => hdv t (by rw [heq]; exact htl)⟩
  · exact ⟨ht, hlen, hval⟩

/-- The append loop: entry `j`'s transform, pushed onto the table's tail. The
positions below `out`'s original length are untouched, which is what makes the
layout *absolute*. -/
theorem prep_append_spec (degU : Std.Usize) (out : alloc.vec.Vec Std.U64)
    (f : (alloc.vec.Vec Std.U64) × (alloc.vec.Vec Std.U64)) (kU : Std.Usize)
    (base : ℕ) (hdeg : degU.val = N) (hk : kU.val ≤ N)
    -- honest: the Rust would overflow-panic otherwise, and `prepare` is only
    -- ever called at `A`'s concrete width
    (hbase : base + N ≤ Std.Usize.max)
    (hfl : f.1.val.length = N)
    (hlen : out.val.length = base + kU.val)
    (hnew : ∀ t, t < kU.val → wordAt out (base + t) = wordAt f.1 t)
    (pwv : ℕ) (hfc : ∀ x ∈ f.1.val, x.val < pwv)
    (houtc : ∀ x ∈ out.val, x.val < pwv) :
    ring.prepare_one_loop0_loop1 degU out f kU
      ⦃ z => z.val.length = base + N
             ∧ (∀ t, t < base → wordAt z t = wordAt out t)
             ∧ (∀ x ∈ z.val, x.val < pwv)
             ∧ ∀ t, t < N → wordAt z (base + t) = wordAt f.1 t ⦄ := by
  -- the body pattern-matches the pair, so it has to be in constructor form
  obtain ⟨f1, f2⟩ := f
  dsimp only at hfl hnew hfc ⊢
  rw [ring.prepare_one_loop0_loop1]
  apply loop.spec_decr_nat (fun r => degU.val - r.2.val)
    (fun r => r.2.val ≤ N ∧ r.1.val.length = base + r.2.val
      ∧ (∀ t, t < base → wordAt r.1 t = wordAt out t)
      ∧ (∀ x ∈ r.1.val, x.val < pwv)
      ∧ ∀ t, t < r.2.val → wordAt r.1 (base + t) = wordAt f1 t)
  · rintro ⟨d, kk⟩ ⟨hkk, hdl, hdold, hdc, hdnew⟩
    dsimp only at hkk hdl hdold hdc hdnew
    simp only [ring.prepare_one_loop0_loop1.body]
    by_cases hlt : kk < degU
    · rw [if_pos hlt]
      have hklt : kk.val < N := by rw [← hdeg]; scalar_tac
      have hfb : kk.val < f1.val.length := by rw [hfl]; exact hklt
      have hdmax : d.val.length < Std.Usize.max := by rw [hdl]; omega
      step as ⟨x, hx⟩
      have hxv : x.val = wordAt f1 kk.val := by
        rw [hx, ← wordAt_of_lt (v := f1) (t := kk.val) hfb]
      step as ⟨d1, hd1⟩
      step as ⟨kk1, hkk1⟩
      refine ⟨by rw [hkk1]; omega, ?_, ?_, ?_, ?_, by rw [hkk1]; omega⟩
      · rw [hd1, hkk1, List.length_append, hdl]; simp; omega
      · intro t ht
        simp only [wordAt] at hdold ⊢
        rw [hd1, getD_append_lt' _ _ _ (by rw [hdl]; omega)]
        exact hdold t ht
      · intro y hy
        rw [hd1] at hy
        rcases List.mem_append.mp hy with hm | hm
        · exact hdc y hm
        · rw [List.mem_singleton.mp hm, hx]
          exact hfc _ (List.getElem_mem hfb)
      · intro t ht
        rw [hkk1] at ht
        simp only [wordAt] at hdnew ⊢
        rcases Nat.lt_or_ge t kk.val with hlt2 | hge
        · rw [hd1, getD_append_lt' _ _ _ (by rw [hdl]; omega)]
          exact hdnew t hlt2
        · have hteq : base + t = d.val.length := by rw [hdl]; omega
          rw [hteq, hd1, getD_append_eq']
          have : t = kk.val := by omega
          rw [this] at *
          exact hxv
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : kk.val = N := by rw [← hdeg]; scalar_tac
      exact ⟨by rw [hdl, heq], hdold, hdc,
        fun t ht => hdnew t (by rw [heq]; exact ht)⟩
  · exact ⟨hk, hlen, fun t _ => rfl, houtc, hnew⟩

/-- **`prepare_one`'s table.** Entry `j`'s residues occupy `[j·N, (j+1)·N)` and
are the forward transform of that entry's twisted coefficients -- exactly the
`hFA` that `terms_chunk_spec` computes on the fly. -/
theorem prepare_one_spec (a : alloc.vec.Vec ring.Rq) (nU : Std.Usize)
    (pw mw psi : Std.U64) (ps : ZMod pw.val)
    (h : Magic pw mw) (hpsi : psi.val < pw.val)
    (hpsdef : ps = ((psi.val : ℕ) : ZMod pw.val))
    (hawf : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (han : nU.val ≤ a.val.length)
    (hmax : nU.val * N ≤ Std.Usize.max) :
    ring.prepare_one a nU pw mw psi
      ⦃ z => z.val.length = nU.val * N
             ∧ (∀ u ∈ z.val, u.val < pw.val)
             ∧ ∀ j, j < nU.val → ∀ t, t < N →
                 resK pw.val z (j * N + t)
                   = NttMath.difRun (ps ^ 2) 10 1
                       (NttMath.twistR ps (entryK pw.val a j)) t ⦄ := by
  have hppos : 0 < pw.val := h.pos
  rw [ring.prepare_one]
  step with psi_table_cast psi pw mw h hpsi as ⟨pt, hptC, hptv⟩
  rw [← hpsdef] at hptv
  step as ⟨i, hi⟩
  simp only [alloc.vec.Vec.with_capacity]
  -- the per-entry loop: after `j` entries the table is `j * N` long and every
  -- prepared entry below `j` reads back as its transform
  apply loop.spec_decr_nat (fun r => nU.val - r.2.val)
    (fun r => r.2.val ≤ nU.val ∧ r.1.val.length = r.2.val * N
      ∧ (∀ u ∈ r.1.val, u.val < pw.val)
      ∧ ∀ u, u < r.2.val → ∀ t, t < N →
          resK pw.val r.1 (u * N + t)
            = NttMath.difRun (ps ^ 2) 10 1
                (NttMath.twistR ps (entryK pw.val a u)) t)
  · rintro ⟨d, jj⟩ ⟨hjj, hdl, hdc, hdv⟩
    dsimp only at hjj hdl hdc hdv
    simp only [ring.prepare_one_loop0.body]
    by_cases hlt : jj < nU
    · rw [if_pos hlt]
      have hjlt : jj.val < nU.val := by scalar_tac
      have hja : jj.val < a.val.length := by omega
      simp only [alloc.vec.Vec.with_capacity]
      step with prep_words_spec a ntt.NTT_LEN jj (alloc.vec.Vec.new Std.U64) 0#usize
        ntt_NTT_LEN_val hja (hawf jj.val hjlt) (by simp) (by simp)
        (by intro t ht; simp at ht) as ⟨w, hwl, hwv⟩
      step with zeros_canon pw.val hppos as ⟨sc, hscC⟩
      step with twist_cast w pt pw mw h hwl hptC ps hptv as ⟨tw, htwC, htwv⟩
      step with ntt_forward_spec tw sc pt pw mw h htwC hscC hptC ps hptv
        as ⟨fw, hf1C, hf2C, hfv⟩
      obtain ⟨f1, f2⟩ := fw
      dsimp only at hf1C hf2C hfv
      have hbase : jj.val * N + N ≤ Std.Usize.max := by
        have h1 : (jj.val + 1) * N ≤ nU.val * N := Nat.mul_le_mul_right N (by omega)
        have h2 : (jj.val + 1) * N = jj.val * N + N := by ring
        omega
      step with prep_append_spec ntt.NTT_LEN d (f1, f2) 0#usize (jj.val * N)
        ntt_NTT_LEN_val (by simp) hbase (by dsimp only; exact hf1C.1)
        (by rw [hdl]; simp) (by intro t ht; simp at ht)
        pw.val (by dsimp only; exact hf1C.2) hdc
        as ⟨o1, ho1l, ho1old, ho1c, ho1new⟩
      step as ⟨jj1, hjj1⟩
      refine ⟨by rw [hjj1]; omega, by rw [hjj1, ho1l]; ring, ho1c, ?_,
        by rw [hjj1]; omega⟩
      intro u hu t ht
      rw [hjj1] at hu
      rcases Nat.lt_or_ge u jj.val with hult | huge
      · -- an earlier entry: untouched by the append
        have hlt3 : u * N + t < jj.val * N := by
          have h1 : (u + 1) * N ≤ jj.val * N := Nat.mul_le_mul_right N (by omega)
          have h2 : (u + 1) * N = u * N + N := by ring
          omega
        have hsame : resK pw.val o1 (u * N + t) = resK pw.val d (u * N + t) := by
          simp only [resK]; rw [ho1old (u * N + t) hlt3]
        rw [hsame]
        exact hdv u hult t ht
      · -- this entry: the append wrote it, and it is the transform
        have hueq : u = jj.val := by omega
        rw [hueq]
        simp only [resK]
        rw [ho1new t ht]
        have hf := hfv t ht
        simp only [resK] at hf
        rw [hf]
        refine difRun_congr (ps ^ 2) 10 (by norm_num) 1 (resK pw.val tw)
          (NttMath.twistR ps (entryK pw.val a jj.val)) ?_ t ht
        intro e he
        rw [htwv e he]
        simp only [NttMath.twistR, entryK, hwv e he]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = nU.val := by scalar_tac
      exact ⟨by rw [hdl, heq], hdc, fun u hu => hdv u (by rw [heq]; exact hu)⟩
  · exact ⟨by simp, by simp, by intro u hu; simp at hu, by intro u hu; simp at hu⟩

/-- `ring::slice_out` itself (the loop's wrapper). -/
theorem slice_out_top_spec (pfwd : alloc.vec.Vec Std.U64) (baseU nU : Std.Usize)
    (hn : nU.val = N) (hb : baseU.val + N ≤ pfwd.val.length) :
    ring.slice_out pfwd baseU nU
      ⦃ z => z.val.length = N
             ∧ ∀ t, t < N → wordAt z t = wordAt pfwd (baseU.val + t) ⦄ := by
  rw [ring.slice_out]
  simp only [alloc.vec.Vec.with_capacity]
  exact slice_out_spec pfwd baseU nU (alloc.vec.Vec.new Std.U64) 0#usize hn
    (by simp) (by simp) hb (by intro t ht; simp at ht)

/-- `b[j]`'s words, for the *prepared* chunk's loop.

The fourth copy of this proof (`words_a_spec`, `words_b_spec`,
`prep_words_spec`, this). Aeneas names loops per enclosing function, so four
byte-identical Rust loops become four distinct constants, and a spec is keyed to
the constant. The duplication is the extraction's, not the development's. -/
theorem prep_words_b_spec (b : alloc.vec.Vec ring.Rq) (nU jU : Std.Usize)
    (bw : alloc.vec.Vec Std.U64) (uU : Std.Usize)
    (hn : nU.val = N) (hjb : jU.val < b.val.length)
    (hbj : HachiEquiv.Ring.Wf (b.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)))
    (hu : uU.val ≤ N) (hlen : bw.val.length = uU.val)
    (hred : ∀ x ∈ bw.val, x.val < HachiEquiv.NttProduct.q)
    (hval : ∀ t, t < uU.val → wordAt bw t
      = HachiEquiv.Ring.wordN (b.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) t) :
    ring.dot_prep_chunk_mod_p_loop0_loop0 b nU jU bw uU
      ⦃ z => z.val.length = N ∧ (∀ x ∈ z.val, x.val < HachiEquiv.NttProduct.q)
             ∧ ∀ t, t < N → wordAt z t
                 = HachiEquiv.Ring.wordN
                     (b.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) t ⦄ := by
  rw [ring.dot_prep_chunk_mod_p_loop0_loop0]
  apply loop.spec_decr_nat (fun r => nU.val - r.2.val)
    (fun r => r.2.val ≤ N ∧ r.1.val.length = r.2.val
      ∧ (∀ x ∈ r.1.val, x.val < HachiEquiv.NttProduct.q)
      ∧ ∀ t, t < r.2.val → wordAt r.1 t
          = HachiEquiv.Ring.wordN
              (b.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) t)
  · rintro ⟨d, tt⟩ ⟨htt, hdl, hdr, hdv⟩
    dsimp only at htt hdl hdr hdv
    simp only [ring.dot_prep_chunk_mod_p_loop0_loop0.body]
    by_cases hlt : tt < nU
    · rw [if_pos hlt]
      have httlt : tt.val < N := by rw [← hn]; scalar_tac
      step as ⟨r, hr⟩
      have hrv : r = b.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp) := by
        rw [hr, List.getD_eq_getElem _ _ hjb]
      have hrb : tt.val < r.val.length := by rw [hrv, hbj.1]; exact httlt
      step as ⟨f, hf⟩
      step with HachiEquiv.Ring.to_u64_id f as ⟨w, hw⟩
      have hwlt : w.val < HachiEquiv.NttProduct.q := by
        rw [hw, hf]; exact hbj.2 _ (by rw [← hrv]; exact List.getElem_mem hrb)
      have hwv : w.val = HachiEquiv.Ring.wordN
          (b.val.getD jU.val (alloc.vec.Vec.new cpoly.field.Fp)) tt.val := by
        rw [hw, hf, ← hrv]
        unfold HachiEquiv.Ring.wordN
        rw [List.getD_eq_getElem _ _ hrb]
      step as ⟨d1, hd1⟩
      step as ⟨tt1, htt1⟩
      refine ⟨by rw [htt1]; omega, ?_, ?_, ?_, by rw [htt1]; omega⟩
      · rw [hd1, htt1, List.length_append, hdl]; simp
      · intro x hx
        rw [hd1] at hx
        rcases List.mem_append.mp hx with hm | hm
        · exact hdr x hm
        · rw [List.mem_singleton.mp hm]; exact hwlt
      · intro t htl
        rw [htt1] at htl
        simp only [wordAt] at hdv ⊢
        rcases Nat.lt_or_ge t tt.val with hlt2 | hge
        · rw [hd1, getD_append_lt' _ _ _ (by omega)]
          exact hdv t hlt2
        · have hteq : t = d.val.length := by omega
          rw [hteq, hd1, getD_append_eq', hdl, hwv]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : tt.val = N := by rw [← hn]; scalar_tac
      exact ⟨by rw [hdl, heq], hdr, fun t htl => hdv t (by rw [heq]; exact htl)⟩
  · exact ⟨hu, hlen, hred, hval⟩

/-! ## 14. The prepared terms loop

[`terms_chunk_spec`] with `hFA` read out of the table by [`prepare_one_spec`]
instead of computed by `twist_cast` + `ntt_forward_spec`. The invariant, the
`prod_difRun` step and the conclusion are identical, which is the whole point:
Change 4 moves *where* the left transform comes from and nothing else. -/

theorem prep_terms_chunk_spec (pfwd : alloc.vec.Vec Std.U64)
    (a b : alloc.vec.Vec ring.Rq) (startU endU : Std.Usize)
    (pw mw : Std.U64) (nU : Std.Usize) (pt : alloc.vec.Vec Std.U64)
    (acc scratch : alloc.vec.Vec Std.U64) (jU : Std.Usize) (ps : ZMod pw.val)
    (h : Magic pw mw) (hn : nU.val = N) (hord : ps ^ N = -1)
    (hptC : Canon pw.val pt) (hptv : ∀ e, e < N → resK pw.val pt e = ps ^ e)
    (hpl : endU.val * N ≤ pfwd.val.length)
    (hpv : ∀ j, j < endU.val → ∀ t, t < N →
        resK pw.val pfwd (j * N + t)
          = NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK pw.val a j)) t)
    (hpc : ∀ u ∈ pfwd.val, u.val < pw.val)
    (hbwf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbe : endU.val ≤ b.val.length)
    (hjs : startU.val ≤ jU.val) (hje : jU.val ≤ endU.val)
    (haccC : Canon pw.val acc) (hscC : Canon pw.val scratch)
    (hval : ∀ t, t < N → resK pw.val acc t
              = ∑ u ∈ Finset.Ico startU.val jU.val, termFwd ps a b u t) :
    ring.dot_prep_chunk_mod_p_loop0 pfwd b endU pw mw nU pt acc scratch jU
      ⦃ z => Canon pw.val z.1 ∧ Canon pw.val z.2
             ∧ ∀ t, t < N → resK pw.val z.1 t
                 = ∑ u ∈ Finset.Ico startU.val endU.val, termFwd ps a b u t ⦄ := by
  have hppos : 0 < pw.val := h.pos
  rw [ring.dot_prep_chunk_mod_p_loop0]
  apply loop.spec_decr_nat (fun r => endU.val - r.2.2.val)
    (fun r => startU.val ≤ r.2.2.val ∧ r.2.2.val ≤ endU.val
      ∧ Canon pw.val r.1 ∧ Canon pw.val r.2.1
      ∧ ∀ t, t < N → resK pw.val r.1 t
              = ∑ u ∈ Finset.Ico startU.val r.2.2.val, termFwd ps a b u t)
  · rintro ⟨d, sc, jj⟩ ⟨hjjs, hjje, hcd, hcsc, hw⟩
    dsimp only at hjjs hjje hcd hcsc hw
    simp only [ring.dot_prep_chunk_mod_p_loop0.body]
    by_cases hlt : jj < endU
    · rw [if_pos hlt]
      have hjjlt : jj.val < endU.val := by scalar_tac
      have hjb : jj.val < b.val.length := by omega
      simp only [alloc.vec.Vec.with_capacity]
      step with prep_words_b_spec b nU jj (alloc.vec.Vec.new Std.U64) 0#usize hn hjb
        (hbwf jj.val hjjlt) (by simp) (by simp) (by intro u hu; simp at hu)
        (by intro t ht; simp at ht) as ⟨bw, hbwl, hbwr, hbwv⟩
      step with twist_cast bw pt pw mw h hbwl hptC ps hptv as ⟨tb, htbC, htbv⟩
      step with ntt_forward_spec tb sc pt pw mw h htbC hcsc hptC ps hptv
        as ⟨fw, hfw1, hfw2, hfwv⟩
      obtain ⟨v, v1⟩ := fw
      dsimp only at hfw1 hfw2 hfwv
      step as ⟨off, hoff⟩
      have hoffv : off.val = jj.val * N := by rw [hoff, hn]
      have hslb : off.val + N ≤ pfwd.val.length := by
        rw [hoffv]
        have h1 : (jj.val + 1) * N ≤ endU.val * N := Nat.mul_le_mul_right N (by omega)
        have h2 : (jj.val + 1) * N = jj.val * N + N := by ring
        omega
      step with slice_out_top_spec pfwd off nU hn hslb as ⟨af, hafl, hafv⟩
      -- `pfwd` is `endU * N` long, so `Canon` does not apply to it; the bound
      -- comes from `hpc` directly, with the out-of-range default handled
      have hafC : Canon pw.val af := ⟨hafl, fun x hx => by
        obtain ⟨t, ht, hteq⟩ := List.getElem_of_mem hx
        have hb : wordAt af t = wordAt pfwd (off.val + t) :=
          hafv t (by rw [← hafl]; exact ht)
        rw [wordAt_of_lt ht] at hb
        rw [← hteq, hb]
        unfold wordAt
        by_cases hin : off.val + t < pfwd.val.length
        · rw [List.getD_eq_getElem _ _ hin]
          exact hpc _ (List.getElem_mem hin)
        · rw [List.getD_eq_default _ _ (by omega)]
          simpa using hppos⟩
      -- the table's entry IS this term's left transform
      have hFA : ∀ t, t < N → resK pw.val af t
          = NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK pw.val a jj.val)) t := by
        intro t ht
        simp only [resK]
        rw [hafv t ht, hoffv]
        have := hpv jj.val hjjlt t ht
        simp only [resK] at this
        exact this
      have hFB : ∀ t, t < N → resK pw.val v t
          = NttMath.difRun (ps ^ 2) 10 1
              (NttMath.twistR ps (entryK pw.val b jj.val)) t := by
        intro t ht
        rw [hfwv t ht]
        refine difRun_congr (ps ^ 2) 10 (by norm_num) 1 (resK pw.val tb)
          (NttMath.twistR ps (entryK pw.val b jj.val)) ?_ t ht
        intro e he
        rw [htbv e he]
        simp only [NttMath.twistR, entryK, hbwv e he]
      step with mac_into_spec d af v nU pw mw 0#usize (resK pw.val d)
        h hn (by simp) hcd hafC hfw1 (by intro t ht; simp) as ⟨acc1, hac1C, hac1v⟩
      step as ⟨jj1, hjj1⟩
      refine ⟨by rw [hjj1]; omega, by rw [hjj1]; omega, hac1C, hfw2, ?_,
        by rw [hjj1]; omega⟩
      intro t ht
      rw [hjj1, Finset.sum_Ico_succ_top (by omega), ← hw t ht]
      rw [hac1v t ht, hFA t ht, hFB t ht]
      unfold termFwd
      rw [← prod_difRun ps hord (entryK pw.val a jj.val) (entryK pw.val b jj.val)
        (NttMath.difRun (ps ^ 2) 10 1 (NttMath.twistR ps (entryK pw.val a jj.val)))
        (NttMath.difRun (ps ^ 2) 10 1 (NttMath.twistR ps (entryK pw.val b jj.val)))
        (fun t' => NttMath.difRun (ps ^ 2) 10 1
            (NttMath.twistR ps (entryK pw.val a jj.val)) t'
          * NttMath.difRun (ps ^ 2) 10 1
            (NttMath.twistR ps (entryK pw.val b jj.val)) t')
        (fun t' _ => rfl) (fun t' _ => rfl) (fun t' _ => rfl) t ht]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : jj.val = endU.val := by scalar_tac
      refine ⟨hcd, hcsc, ?_⟩
      intro t ht
      rw [hw t ht, heq]
  · exact ⟨hjs, hje, haccC, hscC, hval⟩

/-! ## 15. The prepared chunk, at one prime

[`dot_chunk_mod_p_spec`] verbatim, with [`prep_terms_chunk_spec`] in place of
[`terms_chunk_spec`]. Because the two terms loops have the *same* conclusion,
everything after them -- `difRun_sum`, `inv_value`, `untwist_value_sum`, the
`L · boff` offset -- is reused without change. -/

theorem dot_prep_chunk_mod_p_spec (pfwd : alloc.vec.Vec Std.U64)
    (a b : alloc.vec.Vec ring.Rq) (startU endU : Std.Usize)
    (pw mw psi psiinv ninv boff : Std.U64) (h : Magic pw mw)
    (hpsi : psi.val < pw.val) (hpsii : psiinv.val < pw.val)
    (hninv : ninv.val < pw.val) (hboff : boff.val < pw.val)
    (hord : ((psi.val : ℕ) : ZMod pw.val) ^ N = -1)
    (hpinv : ((psi.val : ℕ) : ZMod pw.val) * ((psiinv.val : ℕ) : ZMod pw.val) = 1)
    (hNinv : ((N : ℕ) : ZMod pw.val) * ((ninv.val : ℕ) : ZMod pw.val) = 1)
    (hpl : endU.val * N ≤ pfwd.val.length)
    (hpv : ∀ j, j < endU.val → ∀ t, t < N →
        resK pw.val pfwd (j * N + t)
          = NttMath.difRun ((((psi.val : ℕ) : ZMod pw.val)) ^ 2) 10 1
              (NttMath.twistR ((psi.val : ℕ) : ZMod pw.val) (entryK pw.val a j)) t)
    (hpc : ∀ u ∈ pfwd.val, u.val < pw.val)
    (hbwf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbe : endU.val ≤ b.val.length)
    (hse : startU.val ≤ endU.val) (hlenp : endU.val - startU.val < pw.val) :
    ring.dot_prep_chunk_mod_p pfwd b startU endU pw mw psi psiinv ninv boff
      ⦃ z => Canon pw.val z ∧ ∀ t, t < N → resK pw.val z t
              = (∑ u ∈ Finset.Ico startU.val endU.val,
                  NttMath.negConvR N (entryK pw.val a u) (entryK pw.val b u) t)
                + ((boff.val : ℕ) : ZMod pw.val)
                    * (((endU.val - startU.val : ℕ)) : ZMod pw.val) ⦄ := by
  have hppos : 0 < pw.val := h.pos
  set ps : ZMod pw.val := ((psi.val : ℕ) : ZMod pw.val) with hpsdef
  set psii : ZMod pw.val := ((psiinv.val : ℕ) : ZMod pw.val) with hpsiidef
  rw [ring.dot_prep_chunk_mod_p]
  step with psi_table_cast psi pw mw h hpsi as ⟨pt, hptC, hptv⟩
  step with psi_table_cast psiinv pw mw h hpsii as ⟨it, hitC, hitv⟩
  step with zeros_canon_zero pw.val hppos as ⟨acc0, hacc0C, hacc0v⟩
  step with prep_terms_chunk_spec pfwd a b startU endU pw mw ntt.NTT_LEN pt acc0 acc0
    startU ps h ntt_NTT_LEN_val hord hptC hptv hpl hpv hpc hbwf hbe (le_refl _) hse
    hacc0C hacc0C (by intro t ht; rw [hacc0v t ht]; simp)
    as ⟨acc1, scratch, hac1C, hac2C, hac1v⟩
  step as ⟨i, hi⟩
  step as ⟨len, hlen⟩
  have hlenv : len.val = endU.val - startU.val := by
    have hc : len.val = i.val := by rw [hlen]; simp
    rw [hc, hi]
  have hlenlt : len.val < pw.val := by rw [hlenv]; exact hlenp
  step with aux_mul_lt boff len pw mw h hboff hlenlt as ⟨scaled, hscv, hsclt⟩
  have hPR : ∀ t, t < N → resK pw.val acc1 t
      = NttMath.difRun (ps ^ 2) 10 1
          (fun t' => ∑ u ∈ Finset.Ico startU.val endU.val,
            NttMath.cyclicConv N (NttMath.twistR ps (entryK pw.val a u))
              (NttMath.twistR ps (entryK pw.val b u)) t') t := by
    intro t ht
    rw [hac1v t ht, NttMath.difRun_sum (ps ^ 2) 10 1
      (Finset.Ico startU.val endU.val)
      (fun u => NttMath.cyclicConv N (NttMath.twistR ps (entryK pw.val a u))
        (NttMath.twistR ps (entryK pw.val b u)))]
    simp only [termFwd, hpsdef]
  step with ntt_inverse_spec acc1 scratch it pw mw h hac1C hac2C hitC psii hitv
    as ⟨v, v5, hiv1, hiv2, hivv⟩
  have hIV := inv_value ps psii hpinv
    (fun t' => ∑ u ∈ Finset.Ico startU.val endU.val,
      NttMath.cyclicConv N (NttMath.twistR ps (entryK pw.val a u))
        (NttMath.twistR ps (entryK pw.val b u)) t')
    (resK pw.val acc1) (resK pw.val v) hPR hivv
  apply spec_mono (untwist_cast v it ninv scaled pw mw h hiv1 hitC hninv hsclt psii hitv)
  rintro z ⟨hzC, hzv⟩
  refine ⟨hzC, ?_⟩
  intro t ht
  rw [hzv t ht, hIV t ht,
    untwist_value_sum ps psii ((ninv.val : ℕ) : ZMod pw.val) hord hpinv hNinv
      (Finset.Ico startU.val endU.val) (fun u => entryK pw.val a u)
      (fun u => entryK pw.val b u) t ht]
  congr 1
  rw [hscv, ZMod.natCast_mod]
  push_cast
  rw [hlenv]

/-! ## 16. `ring::dot_prepared`

The chunk loop again, with the prepared chunk in place of the fused one. A
per-prime predicate keeps the three layout facts from swamping the signature. -/

/-- `pfwd` is a correct preparation of `a`'s first `n` entries at prime `pw`. -/
def PrepAt (pfwd : alloc.vec.Vec Std.U64) (a : alloc.vec.Vec ring.Rq) (n : ℕ)
    (pw psi : Std.U64) : Prop :=
  n * N ≤ pfwd.val.length
  ∧ (∀ u ∈ pfwd.val, u.val < pw.val)
  ∧ ∀ j, j < n → ∀ t, t < N →
      resK pw.val pfwd (j * N + t)
        = NttMath.difRun ((((psi.val : ℕ) : ZMod pw.val)) ^ 2) 10 1
            (NttMath.twistR ((psi.val : ℕ) : ZMod pw.val) (entryK pw.val a j)) t

/-- The Garner conversion loop, for `dot_prepared`'s constant. [`garner_out_spec`]'s
proof for the fifth byte-identical Rust loop in this development. -/
theorem prep_garner_out_spec (degU : Std.Usize) (qwU : Std.U128)
    (r1 r2 r3 : alloc.vec.Vec Std.U64) (out : alloc.vec.Vec cpoly.field.Fp)
    (tU : Std.Usize) (X : ℕ → ℕ)
    (hdeg : degU.val = N) (hqwv : qwU.val = HachiEquiv.NttProduct.q)
    (hXP : ∀ k, k < N → X k < NttCRT.P)
    (hv1 : ∀ k, k < N → wordAt r1 k = X k % NttCRT.p1)
    (hv2 : ∀ k, k < N → wordAt r2 k = X k % NttCRT.p2)
    (hv3 : ∀ k, k < N → wordAt r3 k = X k % NttCRT.p3)
    (hl1 : r1.val.length = N) (hl2 : r2.val.length = N) (hl3 : r3.val.length = N)
    (ht : tU.val ≤ N) (hlen : out.val.length = tU.val)
    (hred : ∀ u ∈ out.val, HachiEquiv.Field.Red u)
    (hval : ∀ k, k < tU.val →
      HachiEquiv.Ring.wordN out k = X k % HachiEquiv.NttProduct.q) :
    ring.dot_prepared_loop0_loop0 degU qwU r1 r2 r3 out tU
      ⦃ z => HachiEquiv.Ring.Wf z ∧ ∀ k, k < N →
          HachiEquiv.Ring.wordN z k = X k % HachiEquiv.NttProduct.q ⦄ := by
  rw [ring.dot_prepared_loop0_loop0]
  apply loop.spec_decr_nat (fun r => N - r.2.val)
    (fun r => r.2.val ≤ N ∧ r.1.val.length = r.2.val
      ∧ (∀ u ∈ r.1.val, HachiEquiv.Field.Red u)
      ∧ ∀ k, k < r.2.val →
          HachiEquiv.Ring.wordN r.1 k = X k % HachiEquiv.NttProduct.q)
  · rintro ⟨o1, tt⟩ ⟨htt, hlen1, hred1, hval1⟩
    dsimp only at htt hlen1 hred1 hval1
    simp only [ring.dot_prepared_loop0_loop0.body]
    by_cases hlt : tt < degU
    · rw [if_pos hlt]
      have httlt : tt.val < N := by rw [← hdeg]; scalar_tac
      have hb1 : tt.val < r1.val.length := by rw [hl1]; exact httlt
      have hb2 : tt.val < r2.val.length := by rw [hl2]; exact httlt
      have hb3 : tt.val < r3.val.length := by rw [hl3]; exact httlt
      step as ⟨x1, hx1⟩
      step as ⟨x2, hx2⟩
      step as ⟨x3, hx3⟩
      have hx1v : x1.val = X tt.val % NttCRT.p1 := by
        rw [hx1, ← wordAt_of_lt (v := r1) (t := tt.val) hb1]; exact hv1 tt.val httlt
      have hx2v : x2.val = X tt.val % NttCRT.p2 := by
        rw [hx2, ← wordAt_of_lt (v := r2) (t := tt.val) hb2]; exact hv2 tt.val httlt
      have hx3v : x3.val = X tt.val % NttCRT.p3 := by
        rw [hx3, ← wordAt_of_lt (v := r3) (t := tt.val) hb3]; exact hv3 tt.val httlt
      step with NttCRT.garner_spec x1 x2 x3 (X tt.val) (hXP tt.val httlt)
        hx1v hx2v hx3v as ⟨g, hgv⟩
      step as ⟨md, hmd⟩
      have hmdv : md.val = X tt.val % HachiEquiv.NttProduct.q := by
        rw [hmd, hgv, hqwv]
      have hmdlt : md.val < HachiEquiv.NttProduct.q := by
        rw [hmdv]; exact Nat.mod_lt _ (by norm_num [HachiEquiv.NttProduct.q])
      have hcast : lift (UScalar.cast .U64 md) ⦃ y => y.val = md.val ⦄ :=
        UScalar.cast_inBounds_spec .U64 md (by
          have hq : md.val < 4294967197 := by
            have := hmdlt; simpa [HachiEquiv.NttProduct.q] using this
          simp only [UScalar.max, UScalarTy.numBits]
          omega)
      step with hcast as ⟨w, hw⟩
      step with HachiEquiv.Field.fp_new_spec w as ⟨f, hfred, hfval⟩
      step as ⟨o2, ho2⟩
      step as ⟨tt1, htt1⟩
      refine ⟨by rw [htt1]; omega, ?_, ?_, ?_, by rw [htt1]; omega⟩
      · rw [ho2, htt1, List.length_append, hlen1]; simp
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with hm | hm
        · exact hred1 u hm
        · rw [List.mem_singleton.mp hm]; exact hfred
      · intro k hk
        rw [htt1] at hk
        simp only [HachiEquiv.Ring.wordN] at hval1 ⊢
        rcases Nat.lt_or_ge k tt.val with hklt | hkge
        · rw [ho2, getD_append_lt' _ _ _ (by omega)]
          exact hval1 k hklt
        · have hkeq : k = o1.val.length := by omega
          rw [hkeq, ho2, getD_append_eq', hlen1]
          have hwlt : w.val < HachiEquiv.NttProduct.q := by rw [hw]; exact hmdlt
          have hfv : f.val = w.val := by
            have h1 := HachiEquiv.NttProduct.natCast_inj_of_lt
              (n := HachiEquiv.NttProduct.q) (x := f.val) (y := w.val) hfred hfval
            rwa [Nat.mod_eq_of_lt hwlt] at h1
          rw [hfv, hw, hmdv]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : tt.val = N := by rw [← hdeg]; scalar_tac
      exact ⟨⟨by rw [hlen1, heq], hred1⟩,
        fun k hk => hval1 k (by rw [heq]; exact hk)⟩
  · exact ⟨ht, hlen, hred, hval⟩

/-- [`dot_chunk_word_spec`] for the prepared chunk: the same `ZMod p` statement
read back as a residue of [`offConvSum`]. -/
theorem dot_prep_chunk_word_spec (pfwd : alloc.vec.Vec Std.U64)
    (a b : alloc.vec.Vec ring.Rq) (startU endU : Std.Usize)
    (pw mw psi psiinv ninv boff : Std.U64) (h : Magic pw mw)
    (hpsi : psi.val < pw.val) (hpsii : psiinv.val < pw.val)
    (hninv : ninv.val < pw.val) (hboff : boff.val < pw.val)
    (hord : ((psi.val : ℕ) : ZMod pw.val) ^ N = -1)
    (hpinv : ((psi.val : ℕ) : ZMod pw.val) * ((psiinv.val : ℕ) : ZMod pw.val) = 1)
    (hNinv : ((N : ℕ) : ZMod pw.val) * ((ninv.val : ℕ) : ZMod pw.val) = 1)
    (hboffv : boff.val = HachiEquiv.NttProduct.BOUND % pw.val)
    (hpl : endU.val * N ≤ pfwd.val.length)
    (hpv : ∀ j, j < endU.val → ∀ t, t < N →
        resK pw.val pfwd (j * N + t)
          = NttMath.difRun ((((psi.val : ℕ) : ZMod pw.val)) ^ 2) 10 1
              (NttMath.twistR ((psi.val : ℕ) : ZMod pw.val) (entryK pw.val a j)) t)
    (hpc : ∀ u ∈ pfwd.val, u.val < pw.val)
    (hawf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbwf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbe : endU.val ≤ b.val.length)
    (hse : startU.val ≤ endU.val) (hlenp : endU.val - startU.val < pw.val) :
    ring.dot_prep_chunk_mod_p pfwd b startU endU pw mw psi psiinv ninv boff
      ⦃ z => Canon pw.val z ∧ ∀ k, k < N → wordAt z k
              = offConvSum a b startU.val endU.val k % pw.val ⦄ := by
  have hppos : 0 < pw.val := h.pos
  apply spec_mono (dot_prep_chunk_mod_p_spec pfwd a b startU endU pw mw psi psiinv
    ninv boff h hpsi hpsii hninv hboff hord hpinv hNinv hpl hpv hpc hbwf hbe hse hlenp)
  rintro z ⟨hcanon, hval⟩
  refine ⟨hcanon, ?_⟩
  intro k hk
  have hnb := negQ_sum_le a b startU.val endU.val k hawf hbwf
  have hle : (∑ u ∈ Finset.Ico startU.val endU.val,
        HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
             (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
      ≤ (∑ u ∈ Finset.Ico startU.val endU.val,
          HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
               (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
        + (endU.val - startU.val) * HachiEquiv.NttProduct.BOUND :=
    le_trans hnb (Nat.le_add_left _ _)
  have hoff : ((offConvSum a b startU.val endU.val k : ℕ) : ZMod pw.val)
      = ((∑ u ∈ Finset.Ico startU.val endU.val,
            HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                 (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod pw.val)
        + (((endU.val - startU.val) * HachiEquiv.NttProduct.BOUND : ℕ) : ZMod pw.val)
        - ((∑ u ∈ Finset.Ico startU.val endU.val,
            HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                 (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod pw.val) := by
    unfold offConvSum
    rw [Nat.cast_sub hle, Nat.cast_add]
  have hcast : ((wordAt z k : ℕ) : ZMod pw.val)
      = ((offConvSum a b startU.val endU.val k : ℕ) : ZMod pw.val) := by
    have h1 := hval k hk
    rw [resK] at h1
    rw [h1, hoff]
    have hterm : ∀ u, NttMath.negConvR N (entryK pw.val a u) (entryK pw.val b u) k
        = ((HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
              (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod pw.val)
          - ((HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
              (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod pw.val) := by
      intro u
      rw [NttMath.negConvR, ordConv_entryK_pos pw.val a b u k hk,
        ordConv_entryK_neg pw.val a b u k hk]
    rw [Finset.sum_congr rfl (fun u _ => hterm u), Finset.sum_sub_distrib]
    push_cast
    rw [hboffv, ZMod.natCast_mod]
    push_cast
    ring
  exact HachiEquiv.NttProduct.natCast_inj_of_lt (wordAt_lt hcanon hppos k) hcast

/-- **The prepared chunk loop.** [`chunk_loop_spec`] with the prepared chunk. -/
theorem prep_chunk_loop_spec (prep : ring.PreparedVec) (a b : alloc.vec.Vec ring.Rq)
    (nU degU : Std.Usize) (qwU : Std.U128) (acc : ring.Rq) (startU : Std.Usize)
    (haw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (han : nU.val ≤ a.val.length) (hbn : nU.val ≤ b.val.length)
    (hp1 : PrepAt prep.fwd1 a nU.val ntt.AUX_P1 ntt.AUX_PSI1)
    (hp2 : PrepAt prep.fwd2 a nU.val ntt.AUX_P2 ntt.AUX_PSI2)
    (hp3 : PrepAt prep.fwd3 a nU.val ntt.AUX_P3 ntt.AUX_PSI3)
    (hdeg : degU.val = N) (hqw : qwU.val = HachiEquiv.NttProduct.q)
    (hs : startU.val ≤ nU.val) (hacc : HachiEquiv.Ring.Wf acc)
    (hval : ∀ k, k < N → HachiEquiv.Ring.coeffK acc k
              = ∑ u ∈ Finset.range startU.val, HachiEquiv.Ring.negConv
                  (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                  (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k) :
    ring.dot_prepared_loop0 prep b nU degU qwU acc startU
      ⦃ z => HachiEquiv.Ring.Wf z ∧ ∀ k, k < N → HachiEquiv.Ring.coeffK z k
              = ∑ u ∈ Finset.range nU.val, HachiEquiv.Ring.negConv
                  (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                  (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k ⦄ := by
  rw [ring.dot_prepared_loop0]
  apply loop.spec_decr_nat (fun r => nU.val - r.2.val)
    (fun r => r.2.val ≤ nU.val ∧ HachiEquiv.Ring.Wf r.1
      ∧ ∀ k, k < N → HachiEquiv.Ring.coeffK r.1 k
              = ∑ u ∈ Finset.range r.2.val, HachiEquiv.Ring.negConv
                  (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                  (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k)
  · rintro ⟨d, st⟩ ⟨hst, hdw, hdv⟩
    dsimp only at hst hdw hdv
    simp only [ring.dot_prepared_loop0.body]
    by_cases hlt : st < nU
    · rw [if_pos hlt]
      have hstlt : st.val < nU.val := by scalar_tac
      step as ⟨rem, hrem⟩
      have hite : (if rem < ring.DOT_CHUNK then ok rem else ok ring.DOT_CHUNK)
          = ok (if rem < ring.DOT_CHUNK then rem else ring.DOT_CHUNK) := by
        split_ifs <;> rfl
      rw [hite]
      set tk : Std.Usize := if rem < ring.DOT_CHUNK then rem else ring.DOT_CHUNK with htk
      have hdc : (ring.DOT_CHUNK).val = 8192 := by simp only [ring.DOT_CHUNK]; rfl
      have hremv : rem.val = nU.val - st.val := hrem
      have htkle : tk.val ≤ rem.val := by
        rw [htk]; split_ifs with hc
        · exact le_refl _
        · have : ¬ (rem.val < (ring.DOT_CHUNK).val) := by scalar_tac
          omega
      have htk8 : tk.val ≤ 8192 := by
        rw [htk]; split_ifs with hc
        · have : rem.val < (ring.DOT_CHUNK).val := by scalar_tac
          rw [hdc] at this; omega
        · rw [hdc]
      have htkpos : 0 < tk.val := by
        rw [htk]; split_ifs
        · rw [hremv]; omega
        · rw [hdc]; omega
      clear_value tk
      step as ⟨en, hen⟩
      have henv : en.val = st.val + tk.val := hen
      have hennU : en.val ≤ nU.val := by rw [henv, hremv] at *; omega
      have hsen : st.val ≤ en.val := by rw [henv]; omega
      have hsen' : st.val < en.val := by rw [henv]; omega
      have hL : en.val - st.val ≤ 8192 := by rw [henv]; omega
      have hawe : ∀ u, u < en.val → HachiEquiv.Ring.Wf
          (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) :=
        fun u hu => haw u (by omega)
      have hbwe : ∀ u, u < en.val → HachiEquiv.Ring.Wf
          (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) :=
        fun u hu => hbw u (by omega)
      have hbe : en.val ≤ b.val.length := le_trans hennU hbn
      have hmono : ∀ (pf : alloc.vec.Vec Std.U64) (pw psi : Std.U64),
          PrepAt pf a nU.val pw psi →
          (en.val * N ≤ pf.val.length
           ∧ (∀ u ∈ pf.val, u.val < pw.val)
           ∧ ∀ j, j < en.val → ∀ t, t < N →
               resK pw.val pf (j * N + t)
                 = NttMath.difRun ((((psi.val : ℕ) : ZMod pw.val)) ^ 2) 10 1
                     (NttMath.twistR ((psi.val : ℕ) : ZMod pw.val)
                       (entryK pw.val a j)) t) := by
        intro pf pw psi hpp
        refine ⟨le_trans (Nat.mul_le_mul_right N hennU) hpp.1, hpp.2.1, ?_⟩
        intro j hj t ht
        exact hpp.2.2 j (by omega) t ht
      obtain ⟨q1a, q1b, q1c⟩ := hmono prep.fwd1 ntt.AUX_P1 ntt.AUX_PSI1 hp1
      obtain ⟨q2a, q2b, q2c⟩ := hmono prep.fwd2 ntt.AUX_P2 ntt.AUX_PSI2 hp2
      obtain ⟨q3a, q3b, q3c⟩ := hmono prep.fwd3 ntt.AUX_P3 ntt.AUX_PSI3 hp3
      obtain ⟨o1, oi1, on1, ob1⟩ := HachiEquiv.NttProduct.aux1_lt
      obtain ⟨o2, oi2, on2, ob2⟩ := HachiEquiv.NttProduct.aux2_lt
      obtain ⟨o3, oi3, on3, ob3⟩ := HachiEquiv.NttProduct.aux3_lt
      step with dot_prep_chunk_word_spec prep.fwd1 a b st en ntt.AUX_P1 ntt.AUX_M1
        ntt.AUX_PSI1 ntt.AUX_PSIINV1 ntt.AUX_NINV1 ntt.AUX_BOFF1 NttCRT.magic1
        o1 oi1 on1 ob1 HachiEquiv.NttProduct.psi1_ord HachiEquiv.NttProduct.psi1_inv
        HachiEquiv.NttProduct.ninv1_inv HachiEquiv.NttProduct.boff1_val
        q1a q1c q1b hawe hbwe hbe hsen
        (by rw [NttCRT.AUX_P1_val]; exact lt_of_le_of_lt hL (by norm_num))
        as ⟨r1, hc1, hw1⟩
      step with dot_prep_chunk_word_spec prep.fwd2 a b st en ntt.AUX_P2 ntt.AUX_M2
        ntt.AUX_PSI2 ntt.AUX_PSIINV2 ntt.AUX_NINV2 ntt.AUX_BOFF2 NttCRT.magic2
        o2 oi2 on2 ob2 HachiEquiv.NttProduct.psi2_ord HachiEquiv.NttProduct.psi2_inv
        HachiEquiv.NttProduct.ninv2_inv HachiEquiv.NttProduct.boff2_val
        q2a q2c q2b hawe hbwe hbe hsen
        (by rw [NttCRT.AUX_P2_val]; exact lt_of_le_of_lt hL (by norm_num))
        as ⟨r2, hc2, hw2⟩
      step with dot_prep_chunk_word_spec prep.fwd3 a b st en ntt.AUX_P3 ntt.AUX_M3
        ntt.AUX_PSI3 ntt.AUX_PSIINV3 ntt.AUX_NINV3 ntt.AUX_BOFF3 NttCRT.magic3
        o3 oi3 on3 ob3 HachiEquiv.NttProduct.psi3_ord HachiEquiv.NttProduct.psi3_inv
        HachiEquiv.NttProduct.ninv3_inv HachiEquiv.NttProduct.boff3_val
        q3a q3c q3b hawe hbwe hbe hsen
        (by rw [NttCRT.AUX_P3_val]; exact lt_of_le_of_lt hL (by norm_num))
        as ⟨r3, hc3, hw3⟩
      rw [NttCRT.AUX_P1_val] at hw1
      rw [NttCRT.AUX_P2_val] at hw2
      rw [NttCRT.AUX_P3_val] at hw3
      simp only [alloc.vec.Vec.with_capacity]
      step with prep_garner_out_spec degU qwU r1 r2 r3
        (alloc.vec.Vec.new cpoly.field.Fp) 0#usize
        (fun k => offConvSum a b st.val en.val k) hdeg hqw
        (fun k _ => offConvSum_lt_P a b st.val en.val k hawe hbwe hL)
        hw1 hw2 hw3 hc1.1 hc2.1 hc3.1 (by simp) (by simp)
        (by intro u hu; simp at hu) (by intro k hk; simp at hk)
        as ⟨out1, ho1wf, ho1v⟩
      step with HachiEquiv.Ring.add_spec d out1 hdw ho1wf as ⟨acc1, hacwf, hacv⟩
      refine ⟨by omega, hacwf, ?_, by omega⟩
      intro k hk
      have hqq : HachiEquiv.NttProduct.q = HachiEquiv.Field.q := rfl
      rw [hacv k hk, hdv k hk, HachiEquiv.Ring.coeffK_eq_cast_wordN, ho1v k hk,
        hqq, ZMod.natCast_mod,
        offConvSum_cast_q a b st.val en.val k hk hawe hbwe,
        Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.sum_Ico_consecutive _ (Nat.zero_le _) hsen]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : st.val = nU.val := by scalar_tac
      exact ⟨hdw, fun k hk => by rw [hdv k hk, heq]⟩
  · exact ⟨hs, hacc, hval⟩

/-- **`ring::dot_prepared`.** The same value [`dot_fused_spec`] computes. -/
theorem dot_prepared_spec (prep : ring.PreparedVec) (a b : alloc.vec.Vec ring.Rq)
    (nU : Std.Usize)
    (haw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (han : nU.val ≤ a.val.length) (hbn : nU.val ≤ b.val.length)
    (hp1 : PrepAt prep.fwd1 a nU.val ntt.AUX_P1 ntt.AUX_PSI1)
    (hp2 : PrepAt prep.fwd2 a nU.val ntt.AUX_P2 ntt.AUX_PSI2)
    (hp3 : PrepAt prep.fwd3 a nU.val ntt.AUX_P3 ntt.AUX_PSI3) :
    ring.dot_prepared prep b nU
      ⦃ z => HachiEquiv.Ring.Wf z ∧ ∀ k, k < N → HachiEquiv.Ring.coeffK z k
              = ∑ u ∈ Finset.range nU.val, HachiEquiv.Ring.negConv
                  (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                  (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k ⦄ := by
  rw [ring.dot_prepared]
  have hcq : lift (UScalar.cast .U128 params.Q) ⦃ y => y.val = (params.Q).val ⦄ :=
    UScalar.cast_inBounds_spec .U128 params.Q (NttCRT.u64_le_u128_max _)
  step with hcq as ⟨qw, hqw⟩
  rw [HachiEquiv.Field.params_Q_val] at hqw
  step with HachiEquiv.Ring.zero_spec as ⟨z0, hz0wf, hz0v⟩
  exact prep_chunk_loop_spec prep a b nU params.RING_DEGREE qw z0 0#usize
    haw hbw han hbn hp1 hp2 hp3 HachiEquiv.Ring.params_RING_DEGREE_val hqw
    (by simp) hz0wf (by intro k hk; rw [hz0v k]; simp)

/-! ## 17. `ring::prepare_vec`

Three applications of [`prepare_one_spec`], packaged as the three [`PrepAt`]
facts [`dot_prepared_spec`] consumes. -/

theorem prepare_vec_spec (a : alloc.vec.Vec ring.Rq) (nU : Std.Usize)
    (hawf : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (han : nU.val ≤ a.val.length) (hmax : nU.val * N ≤ Std.Usize.max) :
    ring.prepare_vec a nU
      ⦃ z => z.len = nU
             ∧ PrepAt z.fwd1 a nU.val ntt.AUX_P1 ntt.AUX_PSI1
             ∧ PrepAt z.fwd2 a nU.val ntt.AUX_P2 ntt.AUX_PSI2
             ∧ PrepAt z.fwd3 a nU.val ntt.AUX_P3 ntt.AUX_PSI3 ⦄ := by
  obtain ⟨hp1, _, _, _⟩ := HachiEquiv.NttProduct.aux1_lt
  obtain ⟨hp2, _, _, _⟩ := HachiEquiv.NttProduct.aux2_lt
  obtain ⟨hp3, _, _, _⟩ := HachiEquiv.NttProduct.aux3_lt
  rw [ring.prepare_vec]
  step with prepare_one_spec a nU ntt.AUX_P1 ntt.AUX_M1 ntt.AUX_PSI1
    (((ntt.AUX_PSI1).val : ℕ) : ZMod (ntt.AUX_P1).val) NttCRT.magic1 hp1 rfl
    hawf han hmax as ⟨f1, hf1l, hf1c, hf1v⟩
  step with prepare_one_spec a nU ntt.AUX_P2 ntt.AUX_M2 ntt.AUX_PSI2
    (((ntt.AUX_PSI2).val : ℕ) : ZMod (ntt.AUX_P2).val) NttCRT.magic2 hp2 rfl
    hawf han hmax as ⟨f2, hf2l, hf2c, hf2v⟩
  step with prepare_one_spec a nU ntt.AUX_P3 ntt.AUX_M3 ntt.AUX_PSI3
    (((ntt.AUX_PSI3).val : ℕ) : ZMod (ntt.AUX_P3).val) NttCRT.magic3 hp3 rfl
    hawf han hmax as ⟨f3, hf3l, hf3c, hf3v⟩
  exact ⟨⟨le_of_eq hf1l.symm, hf1c, hf1v⟩, ⟨le_of_eq hf2l.symm, hf2c, hf2v⟩,
    ⟨le_of_eq hf3l.symm, hf3c, hf3v⟩⟩

/-! ## 18. The digit-bounded offset, and why two primes are enough

Everything above needs three primes because a generic ring product's exact
convolution coefficient can reach `N · q²`, which is `2^73` -- more than `p1·p2`
can hold even for a single term. The Ajtai product is not generic: one operand
is `G⁻¹(m)`, whose coefficients are unsigned gadget digits below
`GADGET_BASE = 16`. Its exact coefficient is then at most `N · q · 16 = 2^46`,
so thousands of terms fit `p1 · p2` and the third prime is pure waste.

This section is that bound and nothing else. The transforms are untouched:
[`dot_prep_chunk_mod_p_spec`] is already generic in `(p, m, psi, psiinv, ninv,
boff)` and states its offset as `boff · L`, with no mention of `BOUND` or `P`, so
instantiating it at the digit offsets costs nothing. -/

/-- The digit-bounded operand condition, in the form the bound proofs consume:
every word is below the gadget base. Stated for all `t` rather than `t < N`
because `wordN` is `0` past the end, so the unbounded form is no stronger. -/
def DigitWf (b : ring.Rq) : Prop := ∀ t, HachiEquiv.Ring.wordN b t < 16

/-- `DigitWf` from the membership form a decomposition spec produces. -/
theorem digitWf_of_mem {b : ring.Rq} (h : ∀ u ∈ b.val, u.val < 16) : DigitWf b := by
  intro t
  simp only [HachiEquiv.Ring.wordN]
  rcases Nat.lt_or_ge t b.val.length with hlt | hge
  · rw [List.getD_eq_getElem _ _ hlt]
    exact h _ (List.getElem_mem hlt)
  · rw [List.getD_eq_default _ _ hge]
    simp only [cpoly.field.Fp.ZERO]
    norm_num

/-- The digit-bounded offset, `N · q · 16`.

Like [`HachiEquiv.NttProduct.BOUND`] it is asked for exactly two things, and is
this number rather than the tighter `N · (q−1) · 15` for exactly those reasons:
it is the ceiling [`posSumD_le`]/[`negSumD_le`] prove, and `q ∣ BOUND_D`, so it
is invisible mod `q` and the caller needs no correction term. -/
abbrev BOUND_D : ℕ := 1024 * (HachiEquiv.NttProduct.q * 16)

/-- Each `+` antidiagonal term is below `q · 16`, so `m` of them are below
`m · (q · 16)`. [`HachiEquiv.Ring.posSum_le`]'s proof with the digit bound in
place of the second `wordN_lt`. -/
theorem posSumD_le {a b : ring.Rq} (ha : HachiEquiv.Ring.Wf a) (hb : DigitWf b) (k m : ℕ) :
    HachiEquiv.Ring.posSum a b k m ≤ m * (HachiEquiv.NttProduct.q * 16) := by
  unfold HachiEquiv.Ring.posSum
  calc ∑ t ∈ Finset.range m,
        (if t ≤ k then HachiEquiv.Ring.wordN a t * HachiEquiv.Ring.wordN b (k - t) else 0)
      ≤ ∑ _t ∈ Finset.range m, HachiEquiv.NttProduct.q * 16 := by
        refine Finset.sum_le_sum (fun t _ => ?_)
        by_cases h : t ≤ k
        · rw [if_pos h]
          exact Nat.mul_le_mul (Nat.le_of_lt (HachiEquiv.Ring.wordN_lt ha t))
            (Nat.le_of_lt (hb _))
        · rw [if_neg h]; exact Nat.zero_le _
    _ = m * (HachiEquiv.NttProduct.q * 16) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem negSumD_le {a b : ring.Rq} (ha : HachiEquiv.Ring.Wf a) (hb : DigitWf b) (k m : ℕ) :
    HachiEquiv.Ring.negSum a b k m ≤ m * (HachiEquiv.NttProduct.q * 16) := by
  unfold HachiEquiv.Ring.negSum
  calc ∑ t ∈ Finset.range m,
        (if t ≤ k then 0 else HachiEquiv.Ring.wordN a t * HachiEquiv.Ring.wordN b (N + k - t))
      ≤ ∑ _t ∈ Finset.range m, HachiEquiv.NttProduct.q * 16 := by
        refine Finset.sum_le_sum (fun t _ => ?_)
        by_cases h : t ≤ k
        · rw [if_pos h]; exact Nat.zero_le _
        · rw [if_neg h]
          exact Nat.mul_le_mul (Nat.le_of_lt (HachiEquiv.Ring.wordN_lt ha t))
            (Nat.le_of_lt (hb _))
    _ = m * (HachiEquiv.NttProduct.q * 16) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The digit-bounded twin of [`offConvSum`]: the same shifted convolution sum,
offset by `L · BOUND_D` instead of `L · BOUND`. -/
def offConvSumD (a b : alloc.vec.Vec ring.Rq) (st en k : ℕ) : ℕ :=
  (∑ u ∈ Finset.Ico st en,
      HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
           (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
    + (en - st) * BOUND_D
  - ∑ u ∈ Finset.Ico st en,
      HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
           (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N

theorem negQD_sum_le (a b : alloc.vec.Vec ring.Rq) (st en k : ℕ)
    (hawf : ∀ u, u < en → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbd : ∀ u, u < en → DigitWf (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))) :
    (∑ u ∈ Finset.Ico st en,
        HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
             (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
      ≤ (en - st) * BOUND_D := by
  calc (∑ u ∈ Finset.Ico st en,
          HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
               (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
      ≤ ∑ _u ∈ Finset.Ico st en, BOUND_D := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        simp only [Finset.mem_Ico] at hu
        exact negSumD_le (hawf u hu.2) (hbd u hu.2) k N
    _ = (en - st) * BOUND_D := by
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]

theorem posQD_sum_le (a b : alloc.vec.Vec ring.Rq) (st en k : ℕ)
    (hawf : ∀ u, u < en → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbd : ∀ u, u < en → DigitWf (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))) :
    (∑ u ∈ Finset.Ico st en,
        HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
             (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
      ≤ (en - st) * BOUND_D := by
  calc (∑ u ∈ Finset.Ico st en,
          HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
               (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
      ≤ ∑ _u ∈ Finset.Ico st en, BOUND_D := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        simp only [Finset.mem_Ico] at hu
        exact posSumD_le (hawf u hu.2) (hbd u hu.2) k N
    _ = (en - st) * BOUND_D := by
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]

/-- **The two-prime CRT fit.** `offConvSumD ≤ 2 · L · BOUND_D`, and
`2 · DOT_CHUNK_D · BOUND_D < p1 · p2` with 1.6x to spare.

This inequality is what pins `DOT_CHUNK_D = 2048`. The ceiling is `L ≤ 3332`: at
that width the shifted value reaches `454 283 009 702 445 056` against a radix of
`468 937 312 667 959 297`, and one term more overflows it. 2048 is the largest
power of two below the ceiling, and the margin is deliberate -- the ceiling moves
with `q` and the gadget base. -/
theorem offConvSumD_lt_P12 (a b : alloc.vec.Vec ring.Rq) (st en k : ℕ)
    (hawf : ∀ u, u < en → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbd : ∀ u, u < en → DigitWf (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hL : en - st ≤ 2048) :
    offConvSumD a b st en k < NttCRT.P12 := by
  have hp := posQD_sum_le a b st en k hawf hbd
  have hnum : 2 * 2048 * BOUND_D < NttCRT.P12 := by
    simp only [BOUND_D, HachiEquiv.NttProduct.q, NttCRT.P12, NttCRT.p1, NttCRT.p2]
    norm_num
  have hmul : (en - st) * BOUND_D ≤ 2048 * BOUND_D :=
    Nat.mul_le_mul_right BOUND_D hL
  simp only [offConvSumD]
  omega

/-- And the offset vanishes mod `q`: `BOUND_D = N · q · 16` is a multiple of `q`,
so the reconstructed integer reduces to the convolution the caller wanted. The
same argument as [`offConvSum_cast_q`], with the smaller offset. -/
theorem offConvSumD_cast_q (a b : alloc.vec.Vec ring.Rq) (st en k : ℕ) (hk : k < N)
    (hawf : ∀ u, u < en → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbwf : ∀ u, u < en → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbd : ∀ u, u < en → DigitWf (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))) :
    ((offConvSumD a b st en k : ℕ) : ZMod HachiEquiv.Field.q)
      = ∑ u ∈ Finset.Ico st en, HachiEquiv.Ring.negConv
          (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
          (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k := by
  have hle := negQD_sum_le a b st en k hawf hbd
  have hle' : (∑ u ∈ Finset.Ico st en,
        HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
             (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
      ≤ (∑ u ∈ Finset.Ico st en,
          HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
               (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
        + (en - st) * BOUND_D := le_trans hle (Nat.le_add_left _ _)
  unfold offConvSumD
  rw [Nat.cast_sub hle', Nat.cast_add, Nat.cast_sum, Nat.cast_sum]
  -- `BOUND_D = N · q · 16` is a multiple of `q`, so `L · BOUND_D` vanishes mod `q`
  have hB : (((en - st) * BOUND_D : ℕ) : ZMod HachiEquiv.Field.q) = 0 := by
    have : BOUND_D = 1024 * HachiEquiv.Field.q * 16 := by
      simp only [BOUND_D, HachiEquiv.NttProduct.q, HachiEquiv.Field.q]
    rw [this]
    push_cast
    simp [ZMod.natCast_self]
  rw [hB, add_zero, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  simp only [Finset.mem_Ico] at hu
  rw [HachiEquiv.Ring.negConv,
    ← HachiEquiv.Ring.posSum_cast (hawf u hu.2) (hbwf u hu.2) hk,
    ← HachiEquiv.Ring.negSum_cast (hawf u hu.2) (hbwf u hu.2) hk]

/-! ## 19. The two-prime prepared dot

The transforms are reused verbatim: [`dot_prep_chunk_mod_p_spec`] is generic in
`(p, m, psi, psiinv, ninv, boff)` and states its offset as `boff · L`, so
instantiating it at [`ntt.AUX_DOFF1`]/[`ntt.AUX_DOFF2`] costs nothing. What is
genuinely different is below the transforms:

* the reconstruction is [`NttCRT.garner2_spec`], whose `hx` asks for `< p1·p2`
  rather than `< P` -- that is [`offConvSumD_lt_P12`], the whole content of the
  change;
* the remainder is taken in `u64`, because `garner2` returns a `u64`, so the
  `u128` cast the three-prime loop needs is simply absent. -/

/-- [`dot_prep_chunk_word_spec`] at the digit offset. -/
theorem dot_prep_chunk_word_digits_spec (pfwd : alloc.vec.Vec Std.U64)
    (a b : alloc.vec.Vec ring.Rq) (startU endU : Std.Usize)
    (pw mw psi psiinv ninv boff : Std.U64) (h : Magic pw mw)
    (hpsi : psi.val < pw.val) (hpsii : psiinv.val < pw.val)
    (hninv : ninv.val < pw.val) (hboff : boff.val < pw.val)
    (hord : ((psi.val : ℕ) : ZMod pw.val) ^ N = -1)
    (hpinv : ((psi.val : ℕ) : ZMod pw.val) * ((psiinv.val : ℕ) : ZMod pw.val) = 1)
    (hNinv : ((N : ℕ) : ZMod pw.val) * ((ninv.val : ℕ) : ZMod pw.val) = 1)
    (hboffv : boff.val = BOUND_D % pw.val)
    (hpl : endU.val * N ≤ pfwd.val.length)
    (hpv : ∀ j, j < endU.val → ∀ t, t < N →
        resK pw.val pfwd (j * N + t)
          = NttMath.difRun ((((psi.val : ℕ) : ZMod pw.val)) ^ 2) 10 1
              (NttMath.twistR ((psi.val : ℕ) : ZMod pw.val) (entryK pw.val a j)) t)
    (hpc : ∀ u ∈ pfwd.val, u.val < pw.val)
    (hawf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbwf : ∀ u, u < endU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbd : ∀ u, u < endU.val → DigitWf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbe : endU.val ≤ b.val.length)
    (hse : startU.val ≤ endU.val) (hlenp : endU.val - startU.val < pw.val) :
    ring.dot_prep_chunk_mod_p pfwd b startU endU pw mw psi psiinv ninv boff
      ⦃ z => Canon pw.val z ∧ ∀ k, k < N → wordAt z k
              = offConvSumD a b startU.val endU.val k % pw.val ⦄ := by
  have hppos : 0 < pw.val := h.pos
  apply spec_mono (dot_prep_chunk_mod_p_spec pfwd a b startU endU pw mw psi psiinv
    ninv boff h hpsi hpsii hninv hboff hord hpinv hNinv hpl hpv hpc hbwf hbe hse hlenp)
  rintro z ⟨hcanon, hval⟩
  refine ⟨hcanon, ?_⟩
  intro k hk
  have hnb := negQD_sum_le a b startU.val endU.val k hawf hbd
  have hle : (∑ u ∈ Finset.Ico startU.val endU.val,
        HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
             (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
      ≤ (∑ u ∈ Finset.Ico startU.val endU.val,
          HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
               (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N)
        + (endU.val - startU.val) * BOUND_D :=
    le_trans hnb (Nat.le_add_left _ _)
  have hoff : ((offConvSumD a b startU.val endU.val k : ℕ) : ZMod pw.val)
      = ((∑ u ∈ Finset.Ico startU.val endU.val,
            HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                 (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod pw.val)
        + (((endU.val - startU.val) * BOUND_D : ℕ) : ZMod pw.val)
        - ((∑ u ∈ Finset.Ico startU.val endU.val,
            HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                 (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod pw.val) := by
    unfold offConvSumD
    rw [Nat.cast_sub hle, Nat.cast_add]
  have hcast : ((wordAt z k : ℕ) : ZMod pw.val)
      = ((offConvSumD a b startU.val endU.val k : ℕ) : ZMod pw.val) := by
    have h1 := hval k hk
    rw [resK] at h1
    rw [h1, hoff]
    have hterm : ∀ u, NttMath.negConvR N (entryK pw.val a u) (entryK pw.val b u) k
        = ((HachiEquiv.Ring.posSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
              (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod pw.val)
          - ((HachiEquiv.Ring.negSum (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
              (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k N : ℕ) : ZMod pw.val) := by
      intro u
      rw [NttMath.negConvR, ordConv_entryK_pos pw.val a b u k hk,
        ordConv_entryK_neg pw.val a b u k hk]
    rw [Finset.sum_congr rfl (fun u _ => hterm u), Finset.sum_sub_distrib]
    push_cast
    rw [hboffv, ZMod.natCast_mod]
    push_cast
    ring
  exact HachiEquiv.NttProduct.natCast_inj_of_lt (wordAt_lt hcanon hppos k) hcast

/-- The two-prime Garner conversion loop. [`prep_garner_out_spec`] with two
residues, and without the `u128` cast: `garner2` already returns a `u64`, so the
remainder is taken there. -/
theorem prep2_garner_out_spec (degU : Std.Usize) (qwU : Std.U64)
    (r1 r2 : alloc.vec.Vec Std.U64) (out : alloc.vec.Vec cpoly.field.Fp)
    (tU : Std.Usize) (X : ℕ → ℕ)
    (hdeg : degU.val = N) (hqwv : qwU.val = HachiEquiv.NttProduct.q)
    (hXP : ∀ k, k < N → X k < NttCRT.P12)
    (hv1 : ∀ k, k < N → wordAt r1 k = X k % NttCRT.p1)
    (hv2 : ∀ k, k < N → wordAt r2 k = X k % NttCRT.p2)
    (hl1 : r1.val.length = N) (hl2 : r2.val.length = N)
    (ht : tU.val ≤ N) (hlen : out.val.length = tU.val)
    (hred : ∀ u ∈ out.val, HachiEquiv.Field.Red u)
    (hval : ∀ k, k < tU.val →
      HachiEquiv.Ring.wordN out k = X k % HachiEquiv.NttProduct.q) :
    ring.dot_prepared_digits_loop0_loop0 degU qwU r1 r2 out tU
      ⦃ z => HachiEquiv.Ring.Wf z ∧ ∀ k, k < N →
          HachiEquiv.Ring.wordN z k = X k % HachiEquiv.NttProduct.q ⦄ := by
  rw [ring.dot_prepared_digits_loop0_loop0]
  apply loop.spec_decr_nat (fun r => N - r.2.val)
    (fun r => r.2.val ≤ N ∧ r.1.val.length = r.2.val
      ∧ (∀ u ∈ r.1.val, HachiEquiv.Field.Red u)
      ∧ ∀ k, k < r.2.val →
          HachiEquiv.Ring.wordN r.1 k = X k % HachiEquiv.NttProduct.q)
  · rintro ⟨o1, tt⟩ ⟨htt, hlen1, hred1, hval1⟩
    dsimp only at htt hlen1 hred1 hval1
    simp only [ring.dot_prepared_digits_loop0_loop0.body]
    by_cases hlt : tt < degU
    · rw [if_pos hlt]
      have httlt : tt.val < N := by rw [← hdeg]; scalar_tac
      have hb1 : tt.val < r1.val.length := by rw [hl1]; exact httlt
      have hb2 : tt.val < r2.val.length := by rw [hl2]; exact httlt
      step as ⟨x1, hx1⟩
      step as ⟨x2, hx2⟩
      have hx1v : x1.val = X tt.val % NttCRT.p1 := by
        rw [hx1, ← wordAt_of_lt (v := r1) (t := tt.val) hb1]; exact hv1 tt.val httlt
      have hx2v : x2.val = X tt.val % NttCRT.p2 := by
        rw [hx2, ← wordAt_of_lt (v := r2) (t := tt.val) hb2]; exact hv2 tt.val httlt
      step with NttCRT.garner2_spec x1 x2 (X tt.val) (hXP tt.val httlt)
        hx1v hx2v as ⟨g, hgv⟩
      step as ⟨md, hmd⟩
      have hmdv : md.val = X tt.val % HachiEquiv.NttProduct.q := by
        rw [hmd, hgv, hqwv]
      have hmdlt : md.val < HachiEquiv.NttProduct.q := by
        rw [hmdv]; exact Nat.mod_lt _ (by norm_num [HachiEquiv.NttProduct.q])
      step with HachiEquiv.Field.fp_new_spec md as ⟨f, hfred, hfval⟩
      step as ⟨o2, ho2⟩
      step as ⟨tt1, htt1⟩
      refine ⟨by rw [htt1]; omega, ?_, ?_, ?_, by rw [htt1]; omega⟩
      · rw [ho2, htt1, List.length_append, hlen1]; simp
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with hm | hm
        · exact hred1 u hm
        · rw [List.mem_singleton.mp hm]; exact hfred
      · intro k hk
        rw [htt1] at hk
        simp only [HachiEquiv.Ring.wordN] at hval1 ⊢
        rcases Nat.lt_or_ge k tt.val with hklt | hkge
        · rw [ho2, getD_append_lt' _ _ _ (by omega)]
          exact hval1 k hklt
        · have hkeq : k = o1.val.length := by omega
          rw [hkeq, ho2, getD_append_eq', hlen1]
          have hfv : f.val = md.val := by
            have h1 := HachiEquiv.NttProduct.natCast_inj_of_lt
              (n := HachiEquiv.NttProduct.q) (x := f.val) (y := md.val) hfred hfval
            rwa [Nat.mod_eq_of_lt hmdlt] at h1
          rw [hfv, hmdv]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : tt.val = N := by rw [← hdeg]; scalar_tac
      exact ⟨⟨by rw [hlen1, heq], hred1⟩,
        fun k hk => hval1 k (by rw [heq]; exact hk)⟩
  · exact ⟨ht, hlen, hred, hval⟩

/-- `AUX_DOFF1` is `BOUND_D mod p1`. The kernel checks the literal, as
`NttProduct.boff1_val` does for the generic offset. -/
theorem doff1_val : (ntt.AUX_DOFF1).val = BOUND_D % (ntt.AUX_P1).val := by
  decide +kernel

theorem doff2_val : (ntt.AUX_DOFF2).val = BOUND_D % (ntt.AUX_P2).val := by
  decide +kernel

/-- **The two-prime chunk loop.** [`prep_chunk_loop_spec`] with two primes, the
digit offsets, and `DOT_CHUNK_D` in place of `DOT_CHUNK`. -/
theorem prep2_chunk_loop_spec (prep : ring.PreparedVec) (a b : alloc.vec.Vec ring.Rq)
    (nU degU : Std.Usize) (qwU : Std.U64) (acc : ring.Rq) (startU : Std.Usize)
    (haw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbd : ∀ u, u < nU.val → DigitWf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (han : nU.val ≤ a.val.length) (hbn : nU.val ≤ b.val.length)
    (hp1 : PrepAt prep.fwd1 a nU.val ntt.AUX_P1 ntt.AUX_PSI1)
    (hp2 : PrepAt prep.fwd2 a nU.val ntt.AUX_P2 ntt.AUX_PSI2)
    (hdeg : degU.val = N) (hqw : qwU.val = HachiEquiv.NttProduct.q)
    (hs : startU.val ≤ nU.val) (hacc : HachiEquiv.Ring.Wf acc)
    (hval : ∀ k, k < N → HachiEquiv.Ring.coeffK acc k
              = ∑ u ∈ Finset.range startU.val, HachiEquiv.Ring.negConv
                  (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                  (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k) :
    ring.dot_prepared_digits_loop0 prep b nU degU qwU acc startU
      ⦃ z => HachiEquiv.Ring.Wf z ∧ ∀ k, k < N → HachiEquiv.Ring.coeffK z k
              = ∑ u ∈ Finset.range nU.val, HachiEquiv.Ring.negConv
                  (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                  (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k ⦄ := by
  rw [ring.dot_prepared_digits_loop0]
  apply loop.spec_decr_nat (fun r => nU.val - r.2.val)
    (fun r => r.2.val ≤ nU.val ∧ HachiEquiv.Ring.Wf r.1
      ∧ ∀ k, k < N → HachiEquiv.Ring.coeffK r.1 k
              = ∑ u ∈ Finset.range r.2.val, HachiEquiv.Ring.negConv
                  (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                  (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k)
  · rintro ⟨d, st⟩ ⟨hst, hdw, hdv⟩
    dsimp only at hst hdw hdv
    simp only [ring.dot_prepared_digits_loop0.body]
    by_cases hlt : st < nU
    · rw [if_pos hlt]
      have hstlt : st.val < nU.val := by scalar_tac
      step as ⟨rem, hrem⟩
      have hite : (if rem < ring.DOT_CHUNK_D then ok rem else ok ring.DOT_CHUNK_D)
          = ok (if rem < ring.DOT_CHUNK_D then rem else ring.DOT_CHUNK_D) := by
        split_ifs <;> rfl
      rw [hite]
      set tk : Std.Usize := if rem < ring.DOT_CHUNK_D then rem else ring.DOT_CHUNK_D with htk
      have hdc : (ring.DOT_CHUNK_D).val = 2048 := by simp only [ring.DOT_CHUNK_D]; rfl
      have hremv : rem.val = nU.val - st.val := hrem
      have htkle : tk.val ≤ rem.val := by
        rw [htk]; split_ifs with hc
        · exact le_refl _
        · have : ¬ (rem.val < (ring.DOT_CHUNK_D).val) := by scalar_tac
          omega
      have htk8 : tk.val ≤ 2048 := by
        rw [htk]; split_ifs with hc
        · have : rem.val < (ring.DOT_CHUNK_D).val := by scalar_tac
          rw [hdc] at this; omega
        · rw [hdc]
      have htkpos : 0 < tk.val := by
        rw [htk]; split_ifs
        · rw [hremv]; omega
        · rw [hdc]; omega
      clear_value tk
      step as ⟨en, hen⟩
      have henv : en.val = st.val + tk.val := hen
      have hennU : en.val ≤ nU.val := by rw [henv, hremv] at *; omega
      have hsen : st.val ≤ en.val := by rw [henv]; omega
      have hL : en.val - st.val ≤ 2048 := by rw [henv]; omega
      have hawe : ∀ u, u < en.val → HachiEquiv.Ring.Wf
          (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) :=
        fun u hu => haw u (by omega)
      have hbwe : ∀ u, u < en.val → HachiEquiv.Ring.Wf
          (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) :=
        fun u hu => hbw u (by omega)
      have hbde : ∀ u, u < en.val → DigitWf
          (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) :=
        fun u hu => hbd u (by omega)
      have hbe : en.val ≤ b.val.length := le_trans hennU hbn
      have hmono : ∀ (pf : alloc.vec.Vec Std.U64) (pw psi : Std.U64),
          PrepAt pf a nU.val pw psi →
          (en.val * N ≤ pf.val.length
           ∧ (∀ u ∈ pf.val, u.val < pw.val)
           ∧ ∀ j, j < en.val → ∀ t, t < N →
               resK pw.val pf (j * N + t)
                 = NttMath.difRun ((((psi.val : ℕ) : ZMod pw.val)) ^ 2) 10 1
                     (NttMath.twistR ((psi.val : ℕ) : ZMod pw.val)
                       (entryK pw.val a j)) t) := by
        intro pf pw psi hpp
        refine ⟨le_trans (Nat.mul_le_mul_right N hennU) hpp.1, hpp.2.1, ?_⟩
        intro j hj t ht
        exact hpp.2.2 j (by omega) t ht
      obtain ⟨q1a, q1b, q1c⟩ := hmono prep.fwd1 ntt.AUX_P1 ntt.AUX_PSI1 hp1
      obtain ⟨q2a, q2b, q2c⟩ := hmono prep.fwd2 ntt.AUX_P2 ntt.AUX_PSI2 hp2
      obtain ⟨o1, oi1, on1, _⟩ := HachiEquiv.NttProduct.aux1_lt
      obtain ⟨o2, oi2, on2, _⟩ := HachiEquiv.NttProduct.aux2_lt
      have od1 : (ntt.AUX_DOFF1).val < (ntt.AUX_P1).val := by
        rw [doff1_val]; exact Nat.mod_lt _ (by rw [NttCRT.AUX_P1_val]; norm_num)
      have od2 : (ntt.AUX_DOFF2).val < (ntt.AUX_P2).val := by
        rw [doff2_val]; exact Nat.mod_lt _ (by rw [NttCRT.AUX_P2_val]; norm_num)
      step with dot_prep_chunk_word_digits_spec prep.fwd1 a b st en ntt.AUX_P1 ntt.AUX_M1
        ntt.AUX_PSI1 ntt.AUX_PSIINV1 ntt.AUX_NINV1 ntt.AUX_DOFF1 NttCRT.magic1
        o1 oi1 on1 od1 HachiEquiv.NttProduct.psi1_ord HachiEquiv.NttProduct.psi1_inv
        HachiEquiv.NttProduct.ninv1_inv doff1_val
        q1a q1c q1b hawe hbwe hbde hbe hsen
        (by rw [NttCRT.AUX_P1_val]; exact lt_of_le_of_lt hL (by norm_num))
        as ⟨r1, hc1, hw1⟩
      step with dot_prep_chunk_word_digits_spec prep.fwd2 a b st en ntt.AUX_P2 ntt.AUX_M2
        ntt.AUX_PSI2 ntt.AUX_PSIINV2 ntt.AUX_NINV2 ntt.AUX_DOFF2 NttCRT.magic2
        o2 oi2 on2 od2 HachiEquiv.NttProduct.psi2_ord HachiEquiv.NttProduct.psi2_inv
        HachiEquiv.NttProduct.ninv2_inv doff2_val
        q2a q2c q2b hawe hbwe hbde hbe hsen
        (by rw [NttCRT.AUX_P2_val]; exact lt_of_le_of_lt hL (by norm_num))
        as ⟨r2, hc2, hw2⟩
      rw [NttCRT.AUX_P1_val] at hw1
      rw [NttCRT.AUX_P2_val] at hw2
      simp only [alloc.vec.Vec.with_capacity]
      step with prep2_garner_out_spec degU qwU r1 r2
        (alloc.vec.Vec.new cpoly.field.Fp) 0#usize
        (fun k => offConvSumD a b st.val en.val k) hdeg hqw
        (fun k _ => offConvSumD_lt_P12 a b st.val en.val k hawe hbde hL)
        hw1 hw2 hc1.1 hc2.1 (by simp) (by simp)
        (by intro u hu; simp at hu) (by intro k hk; simp at hk)
        as ⟨out1, ho1wf, ho1v⟩
      step with HachiEquiv.Ring.add_spec d out1 hdw ho1wf as ⟨acc1, hacwf, hacv⟩
      refine ⟨by omega, hacwf, ?_, by omega⟩
      intro k hk
      have hqq : HachiEquiv.NttProduct.q = HachiEquiv.Field.q := rfl
      rw [hacv k hk, hdv k hk, HachiEquiv.Ring.coeffK_eq_cast_wordN, ho1v k hk,
        hqq, ZMod.natCast_mod,
        offConvSumD_cast_q a b st.val en.val k hk hawe hbwe hbde,
        Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.sum_Ico_consecutive _ (Nat.zero_le _) hsen]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : st.val = nU.val := by scalar_tac
      exact ⟨hdw, fun k hk => by rw [hdv k hk, heq]⟩
  · exact ⟨hs, hacc, hval⟩

/-- **`ring::dot_prepared_digits`.** The same value [`dot_prepared_spec`] and
[`dot_fused_spec`] compute, for a `b` whose words are gadget digits. -/
theorem dot_prepared_digits_spec (prep : ring.PreparedVec) (a b : alloc.vec.Vec ring.Rq)
    (nU : Std.Usize)
    (haw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbw : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (hbd : ∀ u, u < nU.val → DigitWf
      (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (han : nU.val ≤ a.val.length) (hbn : nU.val ≤ b.val.length)
    (hp1 : PrepAt prep.fwd1 a nU.val ntt.AUX_P1 ntt.AUX_PSI1)
    (hp2 : PrepAt prep.fwd2 a nU.val ntt.AUX_P2 ntt.AUX_PSI2) :
    ring.dot_prepared_digits prep b nU
      ⦃ z => HachiEquiv.Ring.Wf z ∧ ∀ k, k < N → HachiEquiv.Ring.coeffK z k
              = ∑ u ∈ Finset.range nU.val, HachiEquiv.Ring.negConv
                  (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
                  (b.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)) k ⦄ := by
  rw [ring.dot_prepared_digits]
  step with HachiEquiv.Ring.zero_spec as ⟨z0, hz0wf, hz0v⟩
  exact prep2_chunk_loop_spec prep a b nU params.RING_DEGREE params.Q z0 0#usize
    haw hbw hbd han hbn hp1 hp2 HachiEquiv.Ring.params_RING_DEGREE_val
    HachiEquiv.Field.params_Q_val (by simp) hz0wf (by intro k hk; rw [hz0v k]; simp)

/-- **`ring::prepare_vec_two`.** Two applications of [`prepare_one_spec`]; `fwd3`
is left empty and is never read. -/
theorem prepare_vec_two_spec (a : alloc.vec.Vec ring.Rq) (nU : Std.Usize)
    (hawf : ∀ u, u < nU.val → HachiEquiv.Ring.Wf
      (a.val.getD u (alloc.vec.Vec.new cpoly.field.Fp)))
    (han : nU.val ≤ a.val.length) (hmax : nU.val * N ≤ Std.Usize.max) :
    ring.prepare_vec_two a nU
      ⦃ z => z.len = nU
             ∧ PrepAt z.fwd1 a nU.val ntt.AUX_P1 ntt.AUX_PSI1
             ∧ PrepAt z.fwd2 a nU.val ntt.AUX_P2 ntt.AUX_PSI2 ⦄ := by
  obtain ⟨hp1, _, _, _⟩ := HachiEquiv.NttProduct.aux1_lt
  obtain ⟨hp2, _, _, _⟩ := HachiEquiv.NttProduct.aux2_lt
  rw [ring.prepare_vec_two]
  step with prepare_one_spec a nU ntt.AUX_P1 ntt.AUX_M1 ntt.AUX_PSI1
    (((ntt.AUX_PSI1).val : ℕ) : ZMod (ntt.AUX_P1).val) NttCRT.magic1 hp1 rfl
    hawf han hmax as ⟨f1, hf1l, hf1c, hf1v⟩
  step with prepare_one_spec a nU ntt.AUX_P2 ntt.AUX_M2 ntt.AUX_PSI2
    (((ntt.AUX_PSI2).val : ℕ) : ZMod (ntt.AUX_P2).val) NttCRT.magic2 hp2 rfl
    hawf han hmax as ⟨f2, hf2l, hf2c, hf2v⟩
  exact ⟨⟨le_of_eq hf1l.symm, hf1c, hf1v⟩, ⟨le_of_eq hf2l.symm, hf2c, hf2v⟩⟩

end HachiEquiv.RingFused
