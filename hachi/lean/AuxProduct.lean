/-
The **per-prime pipeline and the CRT reconstruction**: `hachi.ntt`'s two entry
points, `negconv_mod_p` and `negconv_mod_q`.

This is where the pieces meet. `AuxTransform` gives the two transforms as
`AuxNTT.difRun`/`ditRun`; `AuxNTT` gives the three mathematical facts about them
(the forward transform evaluates, evaluation is multiplicative for cyclic
convolution, the inverse undoes the forward up to `N`); `AuxCRT` gives the exact
reconstruction. Composing them is [`negconv_mod_p_spec`] and
[`negconv_mod_q_spec`].

## The shape of the argument, per prime

Write `A t` and `B t` for the two operands read as elements of `ZMod p`, `ψ` for
the table's root and `ω = ψ²`.

```text
twist       ↦ twistR ψ A,  twistR ψ B
forward ×2  ↦ difRun ω 10 1 (twistR ψ A),  difRun ω 10 1 (twistR ψ B)
pointwise   ↦ their product, which by difRun_blockVal and cyclicConv_eval
              is  difRun ω 10 1 (cyclicConv N (twistR ψ A) (twistR ψ B))
inverse     ↦ ditRun ω⁻¹ 10 1 of that, which by ditRun_difRun is
              N · cyclicConv N (twistR ψ A) (twistR ψ B)
untwist     ↦ multiply by ψ^(−t) and N⁻¹, which by twistConv is
              negConvR N A B t
offset      ↦ + (BOUND mod p)
```

Every step is one of the imported theorems; the work is the bookkeeping, and the
one subtlety is that each stage spec constrains its output only *below* `N`, so
the composition needs the congruence lemmas `AuxTransform` carries.

## The word-level sums, and why they are here

[`posW`] and [`negW`] are `Ring.lean`'s `posSum`/`negSum` over a `u64` buffer
instead of over an `Rq`. They exist so that this file can state
[`negconv_mod_q_spec`] without importing `Ring.lean` -- which imports *this*
file, because the new `Rq::mul` proof is the one consumer of it. The two are
identified in `Ring.lean` by a one-line `Finset.sum_congr`, since the extraction
loop copies word for word.
-/
import AuxTransform
import AuxCRT

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open hachi

namespace HachiEquiv.AuxProduct

open HachiEquiv.AuxArith HachiEquiv.AuxCode HachiEquiv.AuxTransform HachiEquiv.AuxCRT

/-- The Hachi modulus, as a plain natural. -/
abbrev q : ℕ := 4294967197

/-- The CRT offset, `N · q²`.

Two properties are all that is asked of it, and they are why it is this number
rather than the tighter `N · (q−1)²`: it is the ceiling `Ring.lean`'s
`posSum_le`/`negSum_le` already prove, and `q ∣ BOUND`, so it is invisible mod
`q` and the caller needs no correction term. -/
abbrev BOUND : ℕ := 1024 * (q * q)

/-! ## The word-level antidiagonals -/

/-- The `+` antidiagonal of the word-level product, over the first `m` indices. -/
def posW (a b : alloc.vec.Vec Std.U64) (k m : ℕ) : ℕ :=
  ∑ t ∈ Finset.range m, if t ≤ k then wordAt a t * wordAt b (k - t) else 0

/-- The `−` antidiagonal. -/
def negW (a b : alloc.vec.Vec Std.U64) (k m : ℕ) : ℕ :=
  ∑ t ∈ Finset.range m, if t ≤ k then 0 else wordAt a t * wordAt b (N + k - t)

/-- The offset coefficient the reconstruction recovers: a natural number, with no
sign and no branch on the coefficient's value. -/
def offConvW (a b : alloc.vec.Vec Std.U64) (k : ℕ) : ℕ :=
  posW a b k N + BOUND - negW a b k N

theorem negW_le_bound (a b : alloc.vec.Vec Std.U64)
    (hqa : ∀ t, wordAt a t < q) (hqb : ∀ t, wordAt b t < q) (k : ℕ) :
    negW a b k N ≤ BOUND := by
  unfold negW
  calc ∑ t ∈ Finset.range N, (if t ≤ k then 0 else wordAt a t * wordAt b (N + k - t))
      ≤ ∑ _t ∈ Finset.range N, q * q := by
        refine Finset.sum_le_sum (fun t _ => ?_)
        by_cases h : t ≤ k
        · rw [if_pos h]; exact Nat.zero_le _
        · rw [if_neg h]
          exact Nat.mul_le_mul (Nat.le_of_lt (hqa t)) (Nat.le_of_lt (hqb _))
    _ = BOUND := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem posW_le_bound (a b : alloc.vec.Vec Std.U64)
    (hqa : ∀ t, wordAt a t < q) (hqb : ∀ t, wordAt b t < q) (k : ℕ) :
    posW a b k N ≤ BOUND := by
  unfold posW
  calc ∑ t ∈ Finset.range N, (if t ≤ k then wordAt a t * wordAt b (k - t) else 0)
      ≤ ∑ _t ∈ Finset.range N, q * q := by
        refine Finset.sum_le_sum (fun t _ => ?_)
        by_cases h : t ≤ k
        · rw [if_pos h]
          exact Nat.mul_le_mul (Nat.le_of_lt (hqa t)) (Nat.le_of_lt (hqb _))
        · rw [if_neg h]; exact Nat.zero_le _
    _ = BOUND := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem offConvW_lt_P (a b : alloc.vec.Vec Std.U64)
    (hqa : ∀ t, wordAt a t < q) (hqb : ∀ t, wordAt b t < q) (k : ℕ) :
    offConvW a b k < AuxCRT.P := by
  have hpos : posW a b k N ≤ BOUND := posW_le_bound a b hqa hqb k
  have hB : BOUND = 18889465060665381692416 := by norm_num
  have hP : AuxCRT.P = 471064322751194440790966273 := AuxCRT.P_val
  unfold offConvW
  rw [hB] at hpos ⊢
  omega

/-! ## The word-level antidiagonals *are* the ring-level convolution

`AuxNTT.ordConv` over the casts of the words is the cast of the `ℕ` sum. Both
directions of the negacyclic fold are instances of the same lemma, at `k` and at
`N + k`. -/

theorem ordConv_cast_pos (p : ℕ) (a b : alloc.vec.Vec Std.U64) (k : ℕ) (hk : k < N) :
    AuxNTT.ordConv N (fun u => ((wordAt a u : ℕ) : ZMod p))
        (fun u => ((wordAt b u : ℕ) : ZMod p)) k
      = ((posW a b k N : ℕ) : ZMod p) := by
  unfold AuxNTT.ordConv posW
  push_cast
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp only [Finset.mem_range] at hi
  by_cases h : i ≤ k
  · rw [if_pos (And.intro h (by omega : k - i < N)), if_pos h]
  · rw [if_neg (by omega : ¬(i ≤ k ∧ k - i < N)), if_neg h]

theorem ordConv_cast_neg (p : ℕ) (a b : alloc.vec.Vec Std.U64) (k : ℕ) (hk : k < N) :
    AuxNTT.ordConv N (fun u => ((wordAt a u : ℕ) : ZMod p))
        (fun u => ((wordAt b u : ℕ) : ZMod p)) (N + k)
      = ((negW a b k N : ℕ) : ZMod p) := by
  have hkN : k < N := hk
  unfold AuxNTT.ordConv negW
  push_cast
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp only [Finset.mem_range] at hi
  by_cases h : i ≤ k
  · rw [if_neg (by omega : ¬(i ≤ N + k ∧ N + k - i < N)), if_pos h]
  · rw [if_pos (And.intro (by omega : i ≤ N + k) (by omega : N + k - i < N)), if_neg h]

/-! ## Helpers for the composition

Three groups, all of them additions of this file:

* the *congruence* lemmas for the two stage runs -- each stage spec constrains
  its output only below `N`, so composing them needs to know that `difRun` and
  `ditRun` read their input only below `N` too;
* the three *cast bridges* for the word-level passes (`twist`, `pointwise`,
  `untwist`), which are `AuxCode.difWord_cast`'s pattern applied to a `% p`
  equation instead of a stage;
* the pure `ZMod p` steps of the argument, stated on extracted equations so that
  no algebra happens inside the monadic part.
-/

/-! ### The two run congruences -/

/-- Inside a block, the butterfly's partner is still inside the buffer: if the
block length `2·half` divides `N` and `t < N` sits in a block's *low* half, then
`t + half < N`. This is the only index fact the congruences need. -/
private theorem blk_add_lt (half n t : ℕ) (hdvd : 2 * half ∣ n) (ht : t < n)
    (hlt : t % (2 * half) < half) : t + half < n := by
  obtain ⟨c, hc⟩ := hdvd
  have hd : 0 < 2 * half := by
    rcases Nat.eq_zero_or_pos (2 * half) with h0 | h0
    · rw [h0, Nat.zero_mul] at hc; omega
    · exact h0
  have hqc : t / (2 * half) < c := by
    rw [Nat.div_lt_iff_lt_mul hd]
    calc t < n := ht
      _ = 2 * half * c := hc
      _ = c * (2 * half) := by ring
  have hkey : 2 * half * (t / (2 * half) + 1) ≤ n := by
    rw [hc]; exact Nat.mul_le_mul_left _ (by omega)
  have hdm := Nat.div_add_mod t (2 * half)
  rw [Nat.mul_add, Nat.mul_one] at hkey
  obtain ⟨M, hM⟩ : ∃ M, 2 * half * (t / (2 * half)) = M := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, t % (2 * half) = r := ⟨_, rfl⟩
  rw [hM] at hkey hdm
  rw [hr] at hdm hlt
  omega

/-- One DIF stage reads its input only below `N`. -/
theorem difStage_congr {R : Type*} [CommRing R] (half step : ℕ) (om : R) (f f' : ℕ → R)
    (hdvd : 2 * half ∣ N) (hag : ∀ u, u < N → f u = f' u) (t : ℕ) (ht : t < N) :
    AuxNTT.difStage half step om f t = AuxNTT.difStage half step om f' t := by
  unfold AuxNTT.difStage
  by_cases hc : t % (2 * half) < half
  · rw [if_pos hc, if_pos hc, hag t ht, hag (t + half) (blk_add_lt half N t hdvd ht hc)]
  · rw [if_neg hc, if_neg hc, hag t ht, hag (t - half) (by omega)]

/-- One DIT stage reads its input only below `N`. -/
theorem ditStage_congr {R : Type*} [CommRing R] (half step : ℕ) (omi : R) (f f' : ℕ → R)
    (hdvd : 2 * half ∣ N) (hag : ∀ u, u < N → f u = f' u) (t : ℕ) (ht : t < N) :
    AuxNTT.ditStage half step omi f t = AuxNTT.ditStage half step omi f' t := by
  unfold AuxNTT.ditStage
  by_cases hc : t % (2 * half) < half
  · rw [if_pos hc, if_pos hc, hag t ht, hag (t + half) (blk_add_lt half N t hdvd ht hc)]
  · rw [if_neg hc, if_neg hc, hag t ht, hag (t - half) (by omega)]

/-- The block length of the `j`-th stage divides `N`. -/
private theorem two_pow_succ_dvd_N (k : ℕ) (hk : k + 1 ≤ 10) : 2 * 2 ^ k ∣ N := by
  rw [show (2 : ℕ) * 2 ^ k = 2 ^ (k + 1) by ring, show N = 2 ^ 10 by norm_num]
  exact pow_dvd_pow 2 hk

/-- **`difRun` reads its input only below `N`.** Needed because
`ntt_forward_spec` concludes about `resK` of the *whole* input buffer while the
pass that produced it is pinned only below `N`. -/
theorem difRun_congr {R : Type*} [CommRing R] (om : R) :
    ∀ (k : ℕ), k ≤ 10 → ∀ (step : ℕ) (f f' : ℕ → R), (∀ u, u < N → f u = f' u) →
      ∀ t, t < N → AuxNTT.difRun om k step f t = AuxNTT.difRun om k step f' t := by
  intro k
  induction k with
  | zero => intro _ step f f' hag t ht; simpa using hag t ht
  | succ k ih =>
      intro hk step f f' hag t ht
      rw [AuxNTT.difRun_succ, AuxNTT.difRun_succ]
      exact ih (by omega) (step * 2) _ _
        (fun u hu => difStage_congr (2 ^ k) step om f f'
          (two_pow_succ_dvd_N k hk) hag u hu) t ht

/-- **`ditRun` reads its input only below `N`.** -/
theorem ditRun_congr {R : Type*} [CommRing R] (omi : R) :
    ∀ (k : ℕ), k ≤ 10 → ∀ (step : ℕ) (f f' : ℕ → R), (∀ u, u < N → f u = f' u) →
      ∀ t, t < N → AuxNTT.ditRun omi k step f t = AuxNTT.ditRun omi k step f' t := by
  intro k
  induction k with
  | zero => intro _ step f f' hag t ht; simpa using hag t ht
  | succ k ih =>
      intro hk step f f' hag t ht
      rw [AuxNTT.ditRun_succ, AuxNTT.ditRun_succ]
      exact ditStage_congr (2 ^ k) step omi _ _ (two_pow_succ_dvd_N k hk)
        (fun u hu => ih (by omega) (step * 2) f f' hag u hu) t ht

/-! ### The three cast bridges

`twist_spec`, `pointwise_spec` and `untwist_spec` are stated on words with `% p`;
the two transform specs are stated in `ZMod p` through `resK`. These three
lemmas are the translation, and each is `ZMod.natCast_mod` plus `Nat.cast_mul` /
`Nat.cast_add` on the word equation -- `AuxCode.difWord_cast`'s pattern, with a
pass in place of a stage. -/

/-- `ntt::twist` in `ZMod p`: the buffer scaled by the powers of `ψ`, i.e.
`AuxNTT.twistR`. No canonicality of `v` is needed -- the body reduces every word
it reads, and `ZMod.natCast_mod` throws that reduction away. -/
theorem twist_cast (v pt : alloc.vec.Vec Std.U64) (pw mw : Std.U64) (h : Magic pw mw)
    (hv : v.val.length = N) (hpt : Canon pw.val pt) (psi : ZMod pw.val)
    (hpsi : ∀ e, e < N → resK pw.val pt e = psi ^ e) :
    ntt.twist v pt pw mw
      ⦃ z => Canon pw.val z
             ∧ ∀ t, t < N →
                 resK pw.val z t
                   = AuxNTT.twistR psi (fun u => ((wordAt v u : ℕ) : ZMod pw.val)) t ⦄ := by
  apply spec_mono (twist_spec v pt pw mw h hv hpt)
  rintro z ⟨hzc, hzval⟩
  refine ⟨hzc, ?_⟩
  intro t ht
  have hp : resK pw.val pt t = psi ^ t := hpsi t ht
  simp only [resK, AuxNTT.twistR] at hp ⊢
  rw [hzval t ht, ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod, hp]

/-- `ntt::pointwise` in `ZMod p`. -/
theorem pointwise_cast (a b : alloc.vec.Vec Std.U64) (pw mw : Std.U64) (h : Magic pw mw)
    (ha : Canon pw.val a) (hb : Canon pw.val b) :
    ntt.pointwise a b pw mw
      ⦃ z => Canon pw.val z
             ∧ ∀ t, t < N → resK pw.val z t = resK pw.val a t * resK pw.val b t ⦄ := by
  apply spec_mono (pointwise_spec a b pw mw h ha hb)
  rintro z ⟨hzc, hzval⟩
  refine ⟨hzc, ?_⟩
  intro t ht
  simp only [resK]
  rw [hzval t ht, ZMod.natCast_mod, Nat.cast_mul]

/-- `ntt::untwist` in `ZMod p`: scale by the powers of `ψ'`, by `N⁻¹`, and add the
offset. -/
theorem untwist_cast (src it : alloc.vec.Vec Std.U64) (ninv boff pw mw : Std.U64)
    (h : Magic pw mw) (hsrc : Canon pw.val src) (hit : Canon pw.val it)
    (hninv : ninv.val < pw.val) (hboff : boff.val < pw.val) (psii : ZMod pw.val)
    (hpsii : ∀ e, e < N → resK pw.val it e = psii ^ e) :
    ntt.untwist src it ninv boff pw mw
      ⦃ z => Canon pw.val z
             ∧ ∀ t, t < N →
                 resK pw.val z t
                   = resK pw.val src t * psii ^ t * ((ninv.val : ℕ) : ZMod pw.val)
                     + ((boff.val : ℕ) : ZMod pw.val) ⦄ := by
  apply spec_mono (untwist_spec src it ninv boff pw mw h hsrc hit hninv hboff)
  rintro z ⟨hzc, hzval⟩
  refine ⟨hzc, ?_⟩
  intro t ht
  have hp : resK pw.val it t = psii ^ t := hpsii t ht
  simp only [resK] at hp ⊢
  rw [hzval t ht, ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_mod, Nat.cast_mul,
    ZMod.natCast_mod, Nat.cast_mul, hp]

/-! ### The three facts about `ω = ψ²`

`AuxNTT`'s transform lemmas ask for `ω^N = 1`, `ω^(N/2) = −1` and `ω·ω' = 1`;
all three come from `ψ^N = −1` and `ψ·ψ' = 1`, which is the whole reason the
table holds powers of a `2N`-th root. -/

theorem om_pow {p : ℕ} (psi : ZMod p) (hord : psi ^ N = -1) : (psi ^ 2) ^ N = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hord]
  exact neg_one_sq

theorem om_neg {p : ℕ} (psi : ZMod p) (hord : psi ^ N = -1) : (psi ^ 2) ^ (N / 2) = -1 := by
  rw [show N / 2 = 512 from by norm_num, ← pow_mul,
    show 2 * 512 = N from by norm_num]
  exact hord

theorem om_inv {p : ℕ} (psi psii : ZMod p) (hpinv : psi * psii = 1) :
    (psi ^ 2) * (psii ^ 2) = 1 := by
  rw [← mul_pow, hpinv, one_pow]

/-! ### The three pure `ZMod p` steps -/

/-- **The pointwise product of the two forward transforms is the forward
transform of the cyclic convolution.** `difRun_blockVal` turns each of the three
runs into an evaluation, and `cyclicConv_eval` multiplies two of them into the
third. -/
theorem prod_difRun {p : ℕ} (psi : ZMod p) (hord : psi ^ N = -1)
    (A B FA FB PR : ℕ → ZMod p)
    (hFA : ∀ t, t < N → FA t = AuxNTT.difRun (psi ^ 2) 10 1 (AuxNTT.twistR psi A) t)
    (hFB : ∀ t, t < N → FB t = AuxNTT.difRun (psi ^ 2) 10 1 (AuxNTT.twistR psi B) t)
    (hPR : ∀ t, t < N → PR t = FA t * FB t) :
    ∀ t, t < N → PR t = AuxNTT.difRun (psi ^ 2) 10 1
        (AuxNTT.cyclicConv N (AuxNTT.twistR psi A) (AuxNTT.twistR psi B)) t := by
  intro t ht
  have hpow := om_pow psi hord
  have hneg := om_neg psi hord
  have hN : N = 2 ^ 10 := by norm_num
  have he : ((psi ^ 2) ^ AuxNTT.brev 10 t) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hpow, one_pow]
  rw [hPR t ht, hFA t ht, hFB t ht,
    AuxNTT.difRun_blockVal 10 (psi ^ 2) N hN hpow hneg (AuxNTT.twistR psi A) t ht,
    AuxNTT.difRun_blockVal 10 (psi ^ 2) N hN hpow hneg (AuxNTT.twistR psi B) t ht,
    AuxNTT.difRun_blockVal 10 (psi ^ 2) N hN hpow hneg
      (AuxNTT.cyclicConv N (AuxNTT.twistR psi A) (AuxNTT.twistR psi B)) t ht]
  exact (AuxNTT.cyclicConv_eval N (psi ^ 2) (AuxNTT.brev 10 t) he _ _).symm

/-- **The inverse transform undoes the forward one, up to `N`.** -/
theorem inv_value {p : ℕ} (psi psii : ZMod p) (hpinv : psi * psii = 1)
    (C PR IV : ℕ → ZMod p)
    (hPR : ∀ t, t < N → PR t = AuxNTT.difRun (psi ^ 2) 10 1 C t)
    (hIV : ∀ t, t < N → IV t = AuxNTT.ditRun (psii ^ 2) 10 1 PR t) :
    ∀ t, t < N → IV t = ((N : ℕ) : ZMod p) * C t := by
  intro t ht
  have hdd : AuxNTT.ditRun (psii ^ 2) 10 1 (AuxNTT.difRun (psi ^ 2) 10 1 C) t
      = (2 : ZMod p) ^ 10 * C t := by
    rw [AuxNTT.ditRun_difRun (psi ^ 2) (psii ^ 2) (om_inv psi psii hpinv) 10 1 C]
  have h2N : (2 : ZMod p) ^ 10 = ((N : ℕ) : ZMod p) := by
    rw [show ((N : ℕ) : ZMod p) = ((1024 : ℕ) : ZMod p) from rfl]
    push_cast
    norm_num
  rw [hIV t ht, ditRun_congr (psii ^ 2) 10 (by norm_num) 1 PR
    (AuxNTT.difRun (psi ^ 2) 10 1 C) hPR t ht, hdd, h2N]

/-- **The untwist.** `twistConv` removes the twist, `hNinv` the factor `N`, and
`hpinv` the remaining `(ψ·ψ')^t`. -/
theorem untwist_value {p : ℕ} (psi psii ninvK : ZMod p) (hord : psi ^ N = -1)
    (hpinv : psi * psii = 1) (hNinv : ((N : ℕ) : ZMod p) * ninvK = 1)
    (A B : ℕ → ZMod p) (t : ℕ) (ht : t < N) :
    ((N : ℕ) : ZMod p)
          * AuxNTT.cyclicConv N (AuxNTT.twistR psi A) (AuxNTT.twistR psi B) t
        * psii ^ t * ninvK
      = AuxNTT.negConvR N A B t := by
  have hpp : psi ^ t * psii ^ t = 1 := by rw [← mul_pow, hpinv, one_pow]
  rw [AuxNTT.twistConv N psi hord A B t ht]
  calc ((N : ℕ) : ZMod p) * (psi ^ t * AuxNTT.negConvR N A B t) * psii ^ t * ninvK
      = AuxNTT.negConvR N A B t * (psi ^ t * psii ^ t)
          * (((N : ℕ) : ZMod p) * ninvK) := by ring
    _ = AuxNTT.negConvR N A B t := by rw [hpp, hNinv, mul_one, mul_one]


/-! ## `ntt::negconv_mod_p` -/

/-- One prime's pipeline: the offset negacyclic coefficient, mod `p`. -/
theorem negconv_mod_p_spec
    (a b : alloc.vec.Vec Std.U64) (pw mw psi psiinv ninv boff : Std.U64)
    (h : Magic pw mw) (ha : a.val.length = N) (hb : b.val.length = N)
    (hpsi : psi.val < pw.val) (hpsii : psiinv.val < pw.val)
    (hninv : ninv.val < pw.val) (hboff : boff.val < pw.val)
    (hord : ((psi.val : ℕ) : ZMod pw.val) ^ N = -1)
    (hpinv : ((psi.val : ℕ) : ZMod pw.val) * ((psiinv.val : ℕ) : ZMod pw.val) = 1)
    (hNinv : ((N : ℕ) : ZMod pw.val) * ((ninv.val : ℕ) : ZMod pw.val) = 1) :
    ntt.negconv_mod_p a b pw mw psi psiinv ninv boff
      ⦃ z => Canon pw.val z
             ∧ ∀ t, t < N →
                 resK pw.val z t
                   = AuxNTT.negConvR N (fun u => ((wordAt a u : ℕ) : ZMod pw.val))
                       (fun u => ((wordAt b u : ℕ) : ZMod pw.val)) t
                     + ((boff.val : ℕ) : ZMod pw.val) ⦄ := by
  have hppos : 0 < pw.val := h.pos
  rw [ntt.negconv_mod_p]
  step with psi_table_cast psi pw mw h hpsi as ⟨pt, hptC, hptv⟩
  step with psi_table_cast psiinv pw mw h hpsii as ⟨it, hitC, hitv⟩
  step with zeros_canon pw.val hppos as ⟨scratch, hscC⟩
  step with twist_cast a pt pw mw h ha hptC ((psi.val : ℕ) : ZMod pw.val) hptv
    as ⟨ta, htaC, htav⟩
  step with ntt_forward_spec ta scratch pt pw mw h htaC hscC hptC
    ((psi.val : ℕ) : ZMod pw.val) hptv as ⟨fwa, hfw1, hfw2, hfwv⟩
  obtain ⟨v, v1⟩ := fwa
  dsimp only at hfw1 hfw2 hfwv
  step with twist_cast b pt pw mw h hb hptC ((psi.val : ℕ) : ZMod pw.val) hptv
    as ⟨tb, htbC, htbv⟩
  step with ntt_forward_spec tb v1 pt pw mw h htbC hfw2 hptC
    ((psi.val : ℕ) : ZMod pw.val) hptv as ⟨v2, v3, hgw1, hgw2, hgwv⟩
  step with pointwise_cast v v2 pw mw h hfw1 hgw1 as ⟨prod, hprC, hprv⟩
  step with ntt_inverse_spec prod v3 it pw mw h hprC hgw2 hitC
    ((psiinv.val : ℕ) : ZMod pw.val) hitv as ⟨v4, v5, hin1, hin2, hinv⟩
  -- ψ, ψ', and the two operands read in `ZMod p`
  set ps : ZMod pw.val := ((psi.val : ℕ) : ZMod pw.val) with hps
  set psii : ZMod pw.val := ((psiinv.val : ℕ) : ZMod pw.val) with hpsiiv
  set A : ℕ → ZMod pw.val := fun u => ((wordAt a u : ℕ) : ZMod pw.val) with hA
  set B : ℕ → ZMod pw.val := fun u => ((wordAt b u : ℕ) : ZMod pw.val) with hB
  -- the two forward transforms, restated on the *twisted* ring-level buffers
  have hFA : ∀ t, t < N →
      resK pw.val v t = AuxNTT.difRun (ps ^ 2) 10 1 (AuxNTT.twistR ps A) t := by
    intro t ht
    rw [hfwv t ht]
    exact difRun_congr (ps ^ 2) 10 (by norm_num) 1 (resK pw.val ta) _ htav t ht
  have hFB : ∀ t, t < N →
      resK pw.val v2 t = AuxNTT.difRun (ps ^ 2) 10 1 (AuxNTT.twistR ps B) t := by
    intro t ht
    rw [hgwv t ht]
    exact difRun_congr (ps ^ 2) 10 (by norm_num) 1 (resK pw.val tb) _ htbv t ht
  -- the pointwise product is the forward transform of the cyclic convolution
  have hsum := prod_difRun ps hord A B (resK pw.val v) (resK pw.val v2)
    (resK pw.val prod) hFA hFB hprv
  -- the inverse transform recovers `N ·` that convolution
  have hIV := inv_value ps psii hpinv
    (AuxNTT.cyclicConv N (AuxNTT.twistR ps A) (AuxNTT.twistR ps B))
    (resK pw.val prod) (resK pw.val v4) hsum hinv
  -- the untwist
  apply spec_mono (untwist_cast v4 it ninv boff pw mw h hin1 hitC hninv hboff psii hitv)
  rintro z ⟨hzC, hzv⟩
  refine ⟨hzC, ?_⟩
  intro t ht
  rw [hzv t ht, hIV t ht,
    untwist_value ps psii ((ninv.val : ℕ) : ZMod pw.val) hord hpinv hNinv A B t ht]

/-! ### Reading back a cast equality

`Field.lean`'s `toK_inj_of_Red`, in the raw `ℕ` form this file needs: two
naturals with equal casts agree once the reduced one is compared to the other's
residue. -/

theorem natCast_inj_of_lt {n x y : ℕ} (hx : x < n)
    (hc : ((x : ℕ) : ZMod n) = ((y : ℕ) : ZMod n)) : x = y % n := by
  have h := (ZMod.natCast_eq_natCast_iff' x y n).mp hc
  rwa [Nat.mod_eq_of_lt hx] at h

/-- The same, read back as a residue of the *natural* number `offConvW`. This is
the form the CRT step needs: three residues of one natural number. -/
theorem negconv_mod_p_word
    (a b : alloc.vec.Vec Std.U64) (pw mw psi psiinv ninv boff : Std.U64)
    (h : Magic pw mw) (ha : a.val.length = N) (hb : b.val.length = N)
    (hqa : ∀ t, wordAt a t < q) (hqb : ∀ t, wordAt b t < q)
    (hpsi : psi.val < pw.val) (hpsii : psiinv.val < pw.val)
    (hninv : ninv.val < pw.val) (hboff : boff.val < pw.val)
    (hord : ((psi.val : ℕ) : ZMod pw.val) ^ N = -1)
    (hpinv : ((psi.val : ℕ) : ZMod pw.val) * ((psiinv.val : ℕ) : ZMod pw.val) = 1)
    (hNinv : ((N : ℕ) : ZMod pw.val) * ((ninv.val : ℕ) : ZMod pw.val) = 1)
    (hboffv : boff.val = BOUND % pw.val) :
    ntt.negconv_mod_p a b pw mw psi psiinv ninv boff
      ⦃ z => Canon pw.val z ∧ ∀ t, t < N → wordAt z t = offConvW a b t % pw.val ⦄ := by
  have hppos : 0 < pw.val := h.pos
  apply spec_mono (negconv_mod_p_spec a b pw mw psi psiinv ninv boff h ha hb
    hpsi hpsii hninv hboff hord hpinv hNinv)
  rintro z ⟨hcanon, hval⟩
  refine ⟨hcanon, ?_⟩
  intro t ht
  -- the truncating subtraction in `offConvW` is honest
  have hnb : negW a b t N ≤ BOUND := negW_le_bound a b hqa hqb t
  have hle : negW a b t N ≤ posW a b t N + BOUND := le_trans hnb (Nat.le_add_left _ _)
  have hoff : ((offConvW a b t : ℕ) : ZMod pw.val)
      = ((posW a b t N : ℕ) : ZMod pw.val) + ((BOUND : ℕ) : ZMod pw.val)
        - ((negW a b t N : ℕ) : ZMod pw.val) := by
    unfold offConvW
    rw [Nat.cast_sub hle, Nat.cast_add]
  -- and the spec's `ZMod` equation is exactly that
  have hcast : ((wordAt z t : ℕ) : ZMod pw.val) = ((offConvW a b t : ℕ) : ZMod pw.val) := by
    have h1 := hval t ht
    rw [resK] at h1
    rw [h1, hoff, AuxNTT.negConvR, ordConv_cast_pos pw.val a b t ht,
      ordConv_cast_neg pw.val a b t ht, hboffv, ZMod.natCast_mod]
    ring
  exact natCast_inj_of_lt (wordAt_lt hcanon hppos t) hcast

--
--   B1  the three primes' root data      (candidate for AuxCRT.lean)
--   B2  params.Q's value
--   B3  the pushed-buffer getD pair      (local restatement: AuxTransform's
--       copies are `private`)
--   B4  two `q` numeral facts
--   B5  the reconstruction loop spec

/-! ### The three primes' root data

`AuxCRT` carries the `Magic` pairs and the `P`/`M`/`GARNER_*` values; the four
root facts per prime are here. Each is a closed statement about a 30-bit
modulus, so `decide +kernel` is the whole proof -- and it is the cheapest one
available, since `ZMod p` is `Fin p` and the exponentiation is by squaring in
the kernel's GMP arithmetic. -/

set_option maxRecDepth 100000 in
theorem psi1_ord : ((ntt.AUX_PSI1.val : ℕ) : ZMod (ntt.AUX_P1).val) ^ N = -1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem psi1_inv : ((ntt.AUX_PSI1.val : ℕ) : ZMod (ntt.AUX_P1).val)
    * ((ntt.AUX_PSIINV1.val : ℕ) : ZMod (ntt.AUX_P1).val) = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ninv1_inv : ((N : ℕ) : ZMod (ntt.AUX_P1).val)
    * ((ntt.AUX_NINV1.val : ℕ) : ZMod (ntt.AUX_P1).val) = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem boff1_val : (ntt.AUX_BOFF1).val = BOUND % (ntt.AUX_P1).val := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem psi2_ord : ((ntt.AUX_PSI2.val : ℕ) : ZMod (ntt.AUX_P2).val) ^ N = -1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem psi2_inv : ((ntt.AUX_PSI2.val : ℕ) : ZMod (ntt.AUX_P2).val)
    * ((ntt.AUX_PSIINV2.val : ℕ) : ZMod (ntt.AUX_P2).val) = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ninv2_inv : ((N : ℕ) : ZMod (ntt.AUX_P2).val)
    * ((ntt.AUX_NINV2.val : ℕ) : ZMod (ntt.AUX_P2).val) = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem boff2_val : (ntt.AUX_BOFF2).val = BOUND % (ntt.AUX_P2).val := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem psi3_ord : ((ntt.AUX_PSI3.val : ℕ) : ZMod (ntt.AUX_P3).val) ^ N = -1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem psi3_inv : ((ntt.AUX_PSI3.val : ℕ) : ZMod (ntt.AUX_P3).val)
    * ((ntt.AUX_PSIINV3.val : ℕ) : ZMod (ntt.AUX_P3).val) = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ninv3_inv : ((N : ℕ) : ZMod (ntt.AUX_P3).val)
    * ((ntt.AUX_NINV3.val : ℕ) : ZMod (ntt.AUX_P3).val) = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem boff3_val : (ntt.AUX_BOFF3).val = BOUND % (ntt.AUX_P3).val := by
  decide +kernel

/-! The four `< p` side conditions, per prime, in one bundle each. -/
set_option maxRecDepth 100000 in
theorem aux1_lt : (ntt.AUX_PSI1).val < (ntt.AUX_P1).val
    ∧ (ntt.AUX_PSIINV1).val < (ntt.AUX_P1).val
    ∧ (ntt.AUX_NINV1).val < (ntt.AUX_P1).val
    ∧ (ntt.AUX_BOFF1).val < (ntt.AUX_P1).val := by decide +kernel

set_option maxRecDepth 100000 in
theorem aux2_lt : (ntt.AUX_PSI2).val < (ntt.AUX_P2).val
    ∧ (ntt.AUX_PSIINV2).val < (ntt.AUX_P2).val
    ∧ (ntt.AUX_NINV2).val < (ntt.AUX_P2).val
    ∧ (ntt.AUX_BOFF2).val < (ntt.AUX_P2).val := by decide +kernel

set_option maxRecDepth 100000 in
theorem aux3_lt : (ntt.AUX_PSI3).val < (ntt.AUX_P3).val
    ∧ (ntt.AUX_PSIINV3).val < (ntt.AUX_P3).val
    ∧ (ntt.AUX_NINV3).val < (ntt.AUX_P3).val
    ∧ (ntt.AUX_BOFF3).val < (ntt.AUX_P3).val := by decide +kernel

/-- `params::Q` is this file's `q`. -/
@[simp, scalar_tac_simps] theorem params_Q_val' : (params.Q).val = q := by
  simp only [params.Q]; decide

/-! ### Reading a pushed buffer

`AuxTransform`'s pair of the same name is `private`, so the two `List.getD`
facts are transcribed. -/

private theorem getD_append_lt'' {α : Type} (l : List α) (x d : α) {j : ℕ}
    (hj : j < l.length) : (l ++ [x]).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hj,
    List.getElem_append_left hj]

private theorem getD_append_eq'' {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
  simp

private theorem wordAt_push_lt {o o1 : alloc.vec.Vec Std.U64} {x : Std.U64} {j : ℕ}
    (ho : o1.val = o.val ++ [x]) (hj : j < o.val.length) : wordAt o1 j = wordAt o j := by
  unfold wordAt; rw [ho, getD_append_lt'' _ _ _ hj]

private theorem wordAt_push_eq {o o1 : alloc.vec.Vec Std.U64} {x : Std.U64}
    (ho : o1.val = o.val ++ [x]) : wordAt o1 o.val.length = x.val := by
  unfold wordAt; rw [ho, getD_append_eq'']

/-- `q` fits in a `u64`. -/
theorem q_le_u64_max : q ≤ UScalar.max UScalarTy.U64 := by
  simp only [q, UScalar.max, UScalarTy.numBits]; norm_num

theorem q_pos : 0 < q := by norm_num

/-! ### The reconstruction loop

The push loop of `negconv_mod_q`: one Garner reconstruction and one `% q` per
index. `garner_spec` makes the body exact, so the invariant is the plain
"entries below the counter hold `offConvW … % q`". -/

theorem negconv_mod_q_loop_spec (a b : alloc.vec.Vec Std.U64)
    (r1 r2 r3 : alloc.vec.Vec Std.U64) (qw : Std.U128) (n : Std.Usize)
    (out : alloc.vec.Vec Std.U64) (t : Std.Usize)
    (hqa : ∀ t, wordAt a t < q) (hqb : ∀ t, wordAt b t < q)
    (hn : n.val = N) (hqwv : qw.val = q)
    (hl1 : r1.val.length = N) (hl2 : r2.val.length = N) (hl3 : r3.val.length = N)
    (hv1 : ∀ k, k < N → wordAt r1 k = offConvW a b k % AuxCRT.p1)
    (hv2 : ∀ k, k < N → wordAt r2 k = offConvW a b k % AuxCRT.p2)
    (hv3 : ∀ k, k < N → wordAt r3 k = offConvW a b k % AuxCRT.p3)
    (ht : t.val ≤ n.val) (hlen : out.val.length = t.val)
    (hred : ∀ u ∈ out.val, u.val < q)
    (hval : ∀ k, k < t.val → wordAt out k = offConvW a b k % q) :
    ntt.negconv_mod_q_loop r1 r2 r3 qw n out t
      ⦃ z => z.val.length = N ∧ (∀ u ∈ z.val, u.val < q)
             ∧ ∀ k, k < N → wordAt z k = offConvW a b k % q ⦄ := by
  rw [ntt.negconv_mod_q_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val.length = s.2.val ∧
      (∀ u ∈ s.1.val, u.val < q) ∧
      ∀ k, k < s.2.val → wordAt s.1 k = offConvW a b k % q)
  · rintro ⟨o1, t1⟩ ⟨ht1, hlen1, hred1, hval1⟩
    dsimp only at ht1 hlen1 hred1 hval1
    simp only [ntt.negconv_mod_q_loop.body]
    by_cases hlt : t1 < n
    · rw [if_pos hlt]
      have htN : t1.val < N := by rw [← hn]; scalar_tac
      have hib1 : t1.val < r1.val.length := by rw [hl1]; exact htN
      have hib2 : t1.val < r2.val.length := by rw [hl2]; exact htN
      have hib3 : t1.val < r3.val.length := by rw [hl3]; exact htN
      have hcap : o1.val.length < Usize.max := by scalar_tac
      step as ⟨i, hi⟩
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      -- the three residues of one natural number
      have he1 : i.val = offConvW a b t1.val % AuxCRT.p1 := by
        rw [hi, ← wordAt_of_lt hib1]; exact hv1 t1.val htN
      have he2 : i1.val = offConvW a b t1.val % AuxCRT.p2 := by
        rw [hi1, ← wordAt_of_lt hib2]; exact hv2 t1.val htN
      have he3 : i2.val = offConvW a b t1.val % AuxCRT.p3 := by
        rw [hi2, ← wordAt_of_lt hib3]; exact hv3 t1.val htN
      have hxP : offConvW a b t1.val < AuxCRT.P := offConvW_lt_P a b hqa hqb t1.val
      step with AuxCRT.garner_spec i i1 i2 (offConvW a b t1.val) hxP he1 he2 he3
        as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      have hi4lt : i4.val < q := by
        rw [hi4, hqwv]; exact Nat.mod_lt _ q_pos
      have hcast : lift (UScalar.cast .U64 i4) ⦃ y => y.val = i4.val ⦄ :=
        UScalar.cast_inBounds_spec .U64 i4 (by
          have := q_le_u64_max
          omega)
      step with hcast as ⟨i5, hi5⟩
      have hi5lt : i5.val < q := by rw [hi5]; exact hi4lt
      step as ⟨o2, ho2⟩
      step as ⟨t2, ht2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [ho2, List.length_append, hlen1]; scalar_tac
      · intro u hu
        rw [ho2] at hu
        rcases List.mem_append.mp hu with hh | hh
        · exact hred1 u hh
        · rw [List.mem_singleton.mp hh]; exact hi5lt
      · intro k hk
        rw [ht2] at hk
        rcases Nat.lt_or_ge k t1.val with hklt | hkge
        · rw [wordAt_push_lt ho2 (by omega), hval1 k hklt]
        · have hkeq : k = o1.val.length := by omega
          rw [hkeq, wordAt_push_eq ho2, hlen1, hi5, hi4, hi3, hqwv]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : t1.val = n.val := by scalar_tac
      exact ⟨by rw [hlen1, heq, hn], hred1, by
        intro k hk; exact hval1 k (by rw [heq, hn]; exact hk)⟩
  · exact ⟨ht, hlen, hred, hval⟩


theorem negconv_mod_q_spec (a b : alloc.vec.Vec Std.U64)
    (ha : a.val.length = N) (hb : b.val.length = N)
    (hqa : ∀ t, wordAt a t < q) (hqb : ∀ t, wordAt b t < q) :
    ntt.negconv_mod_q a b
      ⦃ z => z.val.length = N ∧ (∀ u ∈ z.val, u.val < q)
             ∧ ∀ k, k < N → wordAt z k = offConvW a b k % q ⦄ := by
  rw [ntt.negconv_mod_q]
  obtain ⟨hp1, hpi1, hn1, hb1⟩ := aux1_lt
  obtain ⟨hp2, hpi2, hn2, hb2⟩ := aux2_lt
  obtain ⟨hp3, hpi3, hn3, hb3⟩ := aux3_lt
  step with negconv_mod_p_word a b ntt.AUX_P1 ntt.AUX_M1 ntt.AUX_PSI1 ntt.AUX_PSIINV1
      ntt.AUX_NINV1 ntt.AUX_BOFF1 AuxCRT.magic1 ha hb hqa hqb hp1 hpi1 hn1 hb1
      psi1_ord psi1_inv ninv1_inv boff1_val as ⟨r1, hc1, hw1⟩
  step with negconv_mod_p_word a b ntt.AUX_P2 ntt.AUX_M2 ntt.AUX_PSI2 ntt.AUX_PSIINV2
      ntt.AUX_NINV2 ntt.AUX_BOFF2 AuxCRT.magic2 ha hb hqa hqb hp2 hpi2 hn2 hb2
      psi2_ord psi2_inv ninv2_inv boff2_val as ⟨r2, hc2, hw2⟩
  step with negconv_mod_p_word a b ntt.AUX_P3 ntt.AUX_M3 ntt.AUX_PSI3 ntt.AUX_PSIINV3
      ntt.AUX_NINV3 ntt.AUX_BOFF3 AuxCRT.magic3 ha hb hqa hqb hp3 hpi3 hn3 hb3
      psi3_ord psi3_inv ninv3_inv boff3_val as ⟨r3, hc3, hw3⟩
  rw [AuxCRT.AUX_P1_val] at hw1
  rw [AuxCRT.AUX_P2_val] at hw2
  rw [AuxCRT.AUX_P3_val] at hw3
  -- the modulus, widened
  have hcq : lift (UScalar.cast .U128 params.Q) ⦃ y => y.val = (params.Q).val ⦄ :=
    UScalar.cast_inBounds_spec .U128 params.Q (AuxCRT.u64_le_u128_max _)
  step with hcq as ⟨qw, hqw⟩
  rw [params_Q_val'] at hqw
  simp only [alloc.vec.Vec.with_capacity]
  exact negconv_mod_q_loop_spec a b r1 r2 r3 qw ntt.NTT_LEN
    (alloc.vec.Vec.new Std.U64) 0#usize hqa hqb (by simp) hqw
    hc1.1 hc2.1 hc3.1 hw1 hw2 hw3 (by simp) (by simp)
    (by intro u hu; simp at hu) (by intro k hk; simp at hk)

end HachiEquiv.AuxProduct


