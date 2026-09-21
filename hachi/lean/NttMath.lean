/-
The **mathematics of the transform**, with no reference to the extracted code.

Everything here is about an arbitrary commutative ring and an arbitrary root of
unity in it. That is deliberate: the transform argument is the same at all three
auxiliary primes, and separating it from `ZMod p` means the induction is stated
once and instantiated three times, with no `NeZero` instance threaded through it.
`NttStage.lean` is the other half -- the extracted `hachi.ntt` functions shown to
compute these functions.

## The model

A buffer is a function `ℕ → R`. Real buffers have length `n`, and every
definition below reads index `t` only from indices `< n` when `t < n`, so the
model's behaviour above `n` never matters and is never constrained.

A stage is parametrised by `half` (the butterfly stride) and `step` (the twiddle
stride), with the standing relation `2 · half · step = n`. Carrying both rather
than deriving them from a block length avoids a `len / 2` in every statement, and
it is what makes [`difRun`] structurally recursive.

## What is proved here

1. `ditStage` undoes `difStage` at the same block length, up to a factor of two
   ([`ditStage_difStage`]). Applied once per stage from the innermost out, that
   gives `ditRun ∘ difRun = n • id` ([`ditRun_difRun`]) -- the inverse transform,
   with no orthogonality sum anywhere.
2. The forward transform evaluates: after `j` stages, block `B` holds the
   coefficients of `f(ω^(brev j B) · Y) mod (Y^m − 1)` ([`difRun_blockVal`]), so
   at the end entry `k` is `f` evaluated at `ω^(brev L k)`.
3. Evaluation at an `n`-th root of unity is multiplicative for cyclic
   convolution ([`cyclicConv_eval`]), so the pointwise product of two forward
   transforms is the forward transform of the cyclic convolution.
4. The twist `a_t ↦ a_t · ψ^t` carries the negacyclic product to the cyclic one
   ([`twistConv`]), which is what a length-`n` transform of a degree-`n`
   negacyclic product needs.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace HachiEquiv.NttMath

variable {R : Type*} [CommRing R]

/-! ## Stages -/

/-- One decimation-in-frequency stage.

`half` is the butterfly stride and `step` the twiddle stride; the block length is
`2 · half`. Output `t`, with `idx = t % (2·half)`, is the sum of the butterfly's
two inputs when `idx < half` and their twiddled difference otherwise. -/
def difStage (half step : ℕ) (om : R) (f : ℕ → R) : ℕ → R := fun t =>
  if t % (2 * half) < half then f t + f (t + half)
  else (f (t - half) - f t) * om ^ ((t % (2 * half) - half) * step)

/-- One decimation-in-time stage: the inverse of [`difStage`] at the same block
length, given the inverse root. -/
def ditStage (half step : ℕ) (omi : R) (f : ℕ → R) : ℕ → R := fun t =>
  if t % (2 * half) < half then f t + f (t + half) * omi ^ ((t % (2 * half)) * step)
  else f (t - half) - f t * omi ^ ((t % (2 * half) - half) * step)

/-- `difRun om k step f`: the last `k` forward stages, the first of them at block
length `2^k` with twiddle stride `step`, each subsequent one halving the block and
doubling the stride.

For `n = 2^L` the whole forward transform is `difRun om L 1`. -/
def difRun (om : R) : ℕ → ℕ → (ℕ → R) → (ℕ → R)
  | 0, _step, f => f
  | k + 1, step, f => difRun om k (step * 2) (difStage (2 ^ k) step om f)

/-- `ditRun omi k step f`: the mirror image of [`difRun`] -- the same `k` block
lengths in the opposite order, so that `ditRun` and `difRun` at the same `k` and
`step` nest, block length by block length. -/
def ditRun (omi : R) : ℕ → ℕ → (ℕ → R) → (ℕ → R)
  | 0, _step, f => f
  | k + 1, step, f => ditStage (2 ^ k) step omi (ditRun omi k (step * 2) f)

@[simp] theorem difRun_zero (om : R) (step : ℕ) (f : ℕ → R) : difRun om 0 step f = f := rfl

@[simp] theorem ditRun_zero (omi : R) (step : ℕ) (f : ℕ → R) : ditRun omi 0 step f = f := rfl

theorem difRun_succ (om : R) (k step : ℕ) (f : ℕ → R) :
    difRun om (k + 1) step f = difRun om k (step * 2) (difStage (2 ^ k) step om f) := rfl

theorem ditRun_succ (omi : R) (k step : ℕ) (f : ℕ → R) :
    ditRun omi (k + 1) step f = ditStage (2 ^ k) step omi (ditRun omi k (step * 2) f) := rfl

/-! ## The inverse transform

`ditStage` composed with `difStage` at the same block length is multiplication by
two, pointwise and with no hypothesis on the index. Everything about the inverse
transform follows from that one identity and the homogeneity of `ditStage`.
-/

/-! ### Helpers for [`ditStage_difStage`] -/

private theorem aux_mod_add_half (h t : ℕ) (hlt : t % (2 * h) < h) :
    (t + h) % (2 * h) = t % (2 * h) + h := by
  rw [← Nat.mod_add_mod t (2 * h) h]
  exact Nat.mod_eq_of_lt (by omega)

private theorem aux_mod_sub_half (h t : ℕ) (hh : 0 < h) (hge : ¬ (t % (2 * h) < h)) :
    (t - h) % (2 * h) = t % (2 * h) - h := by
  have hle : h ≤ t := le_trans (by omega) (Nat.mod_le t (2 * h))
  have hb : (t - h) % (2 * h) < 2 * h := Nat.mod_lt _ (by omega)
  have key : t % (2 * h) = ((t - h) % (2 * h) + h) % (2 * h) := by
    rw [Nat.mod_add_mod]
    congr 1
    omega
  rcases Nat.lt_or_ge ((t - h) % (2 * h) + h) (2 * h) with hcs | hcs
  · rw [Nat.mod_eq_of_lt hcs] at key; omega
  · have hmod2 : ((t - h) % (2 * h) + h) % (2 * h) = (t - h) % (2 * h) + h - 2 * h := by
      rw [Nat.mod_eq_sub_mod hcs]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmod2] at key
    omega

private theorem aux_butterfly_add (om omi : R) (hinv : om * omi = 1) (u v : R) (e : ℕ) :
    u + v + (u - v) * om ^ e * omi ^ e = 2 * u := by
  rw [mul_assoc, ← mul_pow, hinv, one_pow, mul_one]; ring

private theorem aux_butterfly_sub (om omi : R) (hinv : om * omi = 1) (u v : R) (e : ℕ) :
    u + v - (u - v) * om ^ e * omi ^ e = 2 * v := by
  rw [mul_assoc, ← mul_pow, hinv, one_pow, mul_one]; ring

/-- The butterfly identity: with `A = u + v` and `B = (u − v)·ω^e`, the inverse
butterfly returns `A + B·ω^(−e) = 2u` and `A − B·ω^(−e) = 2v`.

The `idx < half` branch of the composite reads its partner *above* and the other
branch reads it *below*, which is why the two cases need the two different
`% (2·half)` facts about `t + half` and `t − half`. -/
theorem ditStage_difStage (half step : ℕ) (hhalf : 0 < half) (om omi : R)
    (hinv : om * omi = 1) (f : ℕ → R) (t : ℕ) :
    ditStage half step omi (difStage half step om f) t = 2 * f t := by
  have h2h : 0 < 2 * half := by omega
  by_cases hc : t % (2 * half) < half
  · have h1 : (t + half) % (2 * half) = t % (2 * half) + half := aux_mod_add_half half t hc
    have h1' : ¬ ((t + half) % (2 * half) < half) := by rw [h1]; omega
    simp only [ditStage, difStage]
    rw [if_pos hc, if_pos hc, if_neg h1', h1, Nat.add_sub_cancel, Nat.add_sub_cancel]
    exact aux_butterfly_add om omi hinv (f t) (f (t + half)) _
  · have hmt : t % (2 * half) < 2 * half := Nat.mod_lt t h2h
    have hle : half ≤ t := le_trans (by omega) (Nat.mod_le t (2 * half))
    have h1 : (t - half) % (2 * half) = t % (2 * half) - half := aux_mod_sub_half half t hhalf hc
    have h1' : (t - half) % (2 * half) < half := by rw [h1]; omega
    have hts : t - half + half = t := by omega
    simp only [ditStage, difStage]
    rw [if_neg hc, if_neg hc, if_pos h1', hts]
    exact aux_butterfly_sub om omi hinv (f (t - half)) (f t) _

/-- `ditStage` is homogeneous: it commutes with scaling by a ring element. Needed
to pull the `2^k` produced by the inner stages out through the outer one. -/
theorem ditStage_smul (half step : ℕ) (omi : R) (c : R) (f : ℕ → R) :
    ditStage half step omi (fun t => c * f t) = fun t => c * ditStage half step omi f t := by
  funext t
  unfold ditStage
  by_cases h : t % (2 * half) < half
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

/-- The inverse transform, up to the factor `2^k` that the `k` stages accumulate.

This is the whole `INTT(NTT(x)) = n·x` statement: the two runs nest block length
by block length, and each pair contributes one factor of two. -/
theorem ditRun_difRun (om omi : R) (hinv : om * omi = 1) (k step : ℕ) (f : ℕ → R) :
    ditRun omi k step (difRun om k step f) = fun t => (2 : R) ^ k * f t := by
  induction k generalizing step f with
  | zero => funext t; simp
  | succ k ih =>
      rw [difRun_succ, ditRun_succ, ih, ditStage_smul]
      funext t
      have hstep : (0 : ℕ) < 2 ^ k := Nat.two_pow_pos k
      show (2 : R) ^ k * ditStage (2 ^ k) step omi (difStage (2 ^ k) step om f) t
        = (2 : R) ^ (k + 1) * f t
      rw [ditStage_difStage (2 ^ k) step hstep om omi hinv]
      ring

/-! ## The forward transform evaluates

`brev j b` is `b`'s low `j` bits in reverse order, and it is the exponent block
`b` carries after `j` stages. It is defined recursively and never unfolded to a
closed form: what the induction needs is only how it changes when a block splits,
which is exactly its recursion equation.
-/

/-! ## The transforms are additive

Needed by the *fused* dot product (Stage 6 candidate T18): it accumulates
`Σⱼ fwd(aⱼ) ∘ fwd(bⱼ)` in the transform domain and inverts **once**, so the
correctness argument has to move the inverse transform through a sum. The
transforms here are butterfly networks rather than explicit sums, so this is not
free -- but it is one `split_ifs; ring` per stage and one induction per run.

Stated for `ditRun` (the inverse direction, which is what the fused dot needs)
and for `difRun` alongside it, since the proof is the same three lines and a
one-directional lemma would be a trap for the next reader. -/

theorem difStage_add (half step : ℕ) (om : R) (f g : ℕ → R) :
    difStage half step om (fun t => f t + g t)
      = fun t => difStage half step om f t + difStage half step om g t := by
  funext t; unfold difStage; split_ifs <;> ring

theorem ditStage_add (half step : ℕ) (omi : R) (f g : ℕ → R) :
    ditStage half step omi (fun t => f t + g t)
      = fun t => ditStage half step omi f t + ditStage half step omi g t := by
  funext t; unfold ditStage; split_ifs <;> ring

theorem difStage_zero_fun (half step : ℕ) (om : R) :
    difStage half step om (fun _ => (0 : R)) = fun _ => (0 : R) := by
  funext t; unfold difStage; split_ifs <;> ring

theorem ditStage_zero_fun (half step : ℕ) (omi : R) :
    ditStage half step omi (fun _ => (0 : R)) = fun _ => (0 : R) := by
  funext t; unfold ditStage; split_ifs <;> ring

theorem difRun_add (om : R) (k step : ℕ) (f g : ℕ → R) :
    difRun om k step (fun t => f t + g t)
      = fun t => difRun om k step f t + difRun om k step g t := by
  induction k generalizing step f g with
  | zero => rfl
  | succ n ih => rw [difRun_succ, difRun_succ, difRun_succ, difStage_add, ih]

theorem ditRun_add (omi : R) (k step : ℕ) (f g : ℕ → R) :
    ditRun omi k step (fun t => f t + g t)
      = fun t => ditRun omi k step f t + ditRun omi k step g t := by
  induction k generalizing step with
  | zero => rfl
  | succ n ih => rw [ditRun_succ, ditRun_succ, ditRun_succ, ih, ditStage_add]

theorem ditRun_zero_fun (omi : R) (k step : ℕ) :
    ditRun omi k step (fun _ => (0 : R)) = fun _ => (0 : R) := by
  induction k generalizing step with
  | zero => rfl
  | succ n ih => rw [ditRun_succ, ih, ditStage_zero_fun]

theorem difRun_zero_fun (om : R) (k step : ℕ) :
    difRun om k step (fun _ => (0 : R)) = fun _ => (0 : R) := by
  induction k generalizing step with
  | zero => rfl
  | succ n ih => rw [difRun_succ, difStage_zero_fun, ih]

/-- **The forward transform commutes with a finite sum.** The companion to
[`ditRun_sum`]: the fused dot needs this direction to see its accumulated
pointwise products as *one* forward transform. -/
theorem difRun_sum {ι : Type*} (om : R) (k step : ℕ) (s : Finset ι) (F : ι → ℕ → R) :
    difRun om k step (fun t => ∑ j ∈ s, F j t)
      = fun t => ∑ j ∈ s, difRun om k step (F j) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using difRun_zero_fun om k step
  | insert a s ha ih =>
    have hexp : (fun t => ∑ j ∈ insert a s, F j t)
        = fun t => F a t + ∑ j ∈ s, F j t := by
      funext t; rw [Finset.sum_insert ha]
    rw [hexp, difRun_add, ih]
    funext t
    rw [Finset.sum_insert ha]

/-- **The inverse transform commutes with a finite sum.** This is the lemma the
fused dot rests on: one inverse transform of the accumulated pointwise products
is the sum of the per-term inverse transforms, so every term reduces to the
single-product argument already proved. -/
theorem ditRun_sum {ι : Type*} (omi : R) (k step : ℕ) (s : Finset ι) (F : ι → ℕ → R) :
    ditRun omi k step (fun t => ∑ j ∈ s, F j t)
      = fun t => ∑ j ∈ s, ditRun omi k step (F j) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ditRun_zero_fun omi k step
  | insert a s ha ih =>
    have hexp : (fun t => ∑ j ∈ insert a s, F j t)
        = fun t => F a t + ∑ j ∈ s, F j t := by
      funext t; rw [Finset.sum_insert ha]
    rw [hexp, ditRun_add, ih]
    funext t
    rw [Finset.sum_insert ha]

/-- The low `j` bits of `b`, reversed. -/
def brev : ℕ → ℕ → ℕ
  | 0, _ => 0
  | j + 1, b => (b % 2) * 2 ^ j + brev j (b / 2)

@[simp] theorem brev_zero (b : ℕ) : brev 0 b = 0 := rfl

theorem brev_succ (j b : ℕ) : brev (j + 1) b = (b % 2) * 2 ^ j + brev j (b / 2) := rfl

/-- `brev` on an even argument drops the new bit, and on an odd one adds `2^j`.
These two equations are the only thing the stage induction knows about it. -/
theorem brev_two_mul (j b : ℕ) : brev (j + 1) (2 * b) = brev j b := by
  rw [brev_succ]
  simp [Nat.mul_mod_right, Nat.mul_div_cancel_left b (show 0 < 2 by norm_num)]

theorem brev_two_mul_add_one (j b : ℕ) : brev (j + 1) (2 * b + 1) = 2 ^ j + brev j b := by
  rw [brev_succ]
  have h1 : (2 * b + 1) % 2 = 1 := by omega
  have h2 : (2 * b + 1) / 2 = b := by omega
  rw [h1, h2, one_mul]

/-- Coefficient `r` of `f(ω^a · Y) mod (Y^m − 1)`, for a buffer `f` of length `n`.

This is what block `B` of the buffer holds after `j` forward stages, with
`m = n / 2^j` and `a = brev j B`. At `j = 0` it is `f` itself; at `j = L` the
block length is `1` and it is `f` evaluated at `ω^a`. -/
def blockVal (n m : ℕ) (om : R) (a : ℕ) (f : ℕ → R) (r : ℕ) : R :=
  ∑ t ∈ Finset.range n, if t % m = r then f t * om ^ (a * t) else 0

/-- At block length `n` there is one block and it holds the input unchanged. -/
theorem blockVal_full (n : ℕ) (om : R) (f : ℕ → R) (r : ℕ) (hr : r < n) :
    blockVal n n om 0 f r = f r := by
  unfold blockVal
  rw [Finset.sum_eq_single r]
  · rw [if_pos (Nat.mod_eq_of_lt hr)]; simp
  · intro t ht htr
    simp only [Finset.mem_range] at ht
    rw [if_neg (by rw [Nat.mod_eq_of_lt ht]; exact htr)]
  · intro h; simp only [Finset.mem_range] at h; omega

/-- At block length `1` the block index *is* the buffer index, and the value is an
evaluation: `blockVal n 1 om a f 0 = ∑_t f t · ω^(a·t)`. -/
theorem blockVal_one (n : ℕ) (om : R) (a : ℕ) (f : ℕ → R) :
    blockVal n 1 om a f 0 = ∑ t ∈ Finset.range n, f t * om ^ (a * t) := by
  unfold blockVal
  exact Finset.sum_congr rfl (fun t _ => by rw [if_pos (Nat.mod_one t)])

/-! ### Helpers for [`difStage_blockVal`]

The stage argument is, at bottom, one fact about residues (`t % (2·h)` refines
`t % h` into two classes) and two facts about powers of `ω` (the block stride
`step·2h` is `n`, and half of it is `n/2`). The four lemmas below isolate those,
so that the two cases of the stage lemma are a handful of rewrites each.
-/

/-- `t % (2·h)` is `t % h` or `t % h + h`: reducing mod `2·h` keeps one more bit
than reducing mod `h`. -/
theorem mod_two_mul_cases (h : ℕ) (hh : 0 < h) (t : ℕ) :
    t % (2 * h) = t % h ∨ t % (2 * h) = t % h + h := by
  have h5 : t % (2 * h) % h = t % h := Nat.mod_mod_of_dvd t ⟨2, by ring⟩
  have h3 : t % (2 * h) < 2 * h := Nat.mod_lt t (by omega)
  have h6 := Nat.div_add_mod (t % (2 * h)) h
  have h7 : t % (2 * h) / h < 2 := by
    rw [Nat.div_lt_iff_lt_mul hh]; omega
  obtain ⟨c, hc0, hc1⟩ : ∃ c, c < 2 ∧ h * c + t % h = t % (2 * h) := by
    refine ⟨t % (2 * h) / h, h7, ?_⟩
    rw [h5] at h6
    exact h6
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> omega

/-- The residue split, as the `if`-condition rewriting rule the sums need. -/
theorem mod_split_iff (h r t : ℕ) (hh : 0 < h) (hr : r < h) :
    t % h = r ↔ (t % (2 * h) = r ∨ t % (2 * h) = r + h) := by
  have h4 : t % h < h := Nat.mod_lt t hh
  rcases mod_two_mul_cases h hh t with hs | hs <;> omega

/-- Half the block stride is `n/2`. -/
theorem half_stride (n step h : ℕ) (hn : n = step * (2 * h)) : n / 2 = step * h := by
  subst hn
  rw [show step * (2 * h) = 2 * (step * h) by ring]
  omega

/-- `ω^(step·t)` depends only on `t % (2·h)` when `step·2h = n` and `ω^n = 1`. -/
theorem pow_step_shift (n step h : ℕ) (om : R) (hn : n = step * (2 * h))
    (hpow : om ^ n = 1) (c r : ℕ) :
    om ^ (step * (2 * h * c + r)) = om ^ (step * r) := by
  have he : step * (2 * h * c + r) = n * c + step * r := by rw [hn]; ring
  rw [he, pow_add, pow_mul, hpow, one_pow, one_mul]

/-- Moving up by `h` inside a block flips the sign, because `ω^(step·h) = ω^(n/2) = −1`. -/
theorem pow_step_shift_neg (n step h : ℕ) (om : R) (hn : n = step * (2 * h))
    (hpow : om ^ n = 1) (hneg : om ^ (n / 2) = -1) (c r : ℕ) :
    om ^ (step * (2 * h * c + r + h)) = -om ^ (step * r) := by
  have he : step * (2 * h * c + r + h) = n * c + step * r + n / 2 := by
    rw [half_stride n step h hn, hn]; ring
  rw [he, pow_add, pow_add, pow_mul, hpow, one_pow, one_mul, hneg]
  ring

/-- **The `+` half of the butterfly is reduction mod `Y^h − 1`.** Adding the two
length-`2h` coefficients whose index agrees mod `h` gives the length-`h` one. -/
theorem blockVal_split (n h : ℕ) (om : R) (a : ℕ) (f : ℕ → R) (r : ℕ)
    (hh : 0 < h) (hr : r < h) :
    blockVal n (2 * h) om a f r + blockVal n (2 * h) om a f (r + h)
      = blockVal n h om a f r := by
  unfold blockVal
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hc : t % h = r
  · rcases (mod_split_iff h r t hh hr).mp hc with hs | hs
    · rw [if_pos hs, if_neg (show ¬ t % (2 * h) = r + h by omega), if_pos hc, add_zero]
    · rw [if_neg (show ¬ t % (2 * h) = r by omega), if_pos hs, if_pos hc, zero_add]
  · have hno : ¬(t % (2 * h) = r ∨ t % (2 * h) = r + h) := fun hx =>
      hc ((mod_split_iff h r t hh hr).mpr hx)
    rw [if_neg (fun hx => hno (Or.inl hx)), if_neg (fun hx => hno (Or.inr hx)),
      if_neg hc, add_zero]

/-- **The `−` half of the butterfly, twiddled, is reduction mod `Y^h − 1` again.**
Raising the exponent by `step` turns the difference of the two length-`2h`
coefficients into the length-`h` coefficient at exponent `step + a`; the factor
`ω^(step·r)` is exactly the twiddle `difStage` applies. -/
theorem blockVal_twist (n step h : ℕ) (om : R) (a : ℕ) (f : ℕ → R) (r : ℕ)
    (hh : 0 < h) (hr : r < h) (hn : n = step * (2 * h))
    (hpow : om ^ n = 1) (hneg : om ^ (n / 2) = -1) :
    blockVal n h om (step + a) f r
      = om ^ (step * r)
        * (blockVal n (2 * h) om a f r - blockVal n (2 * h) om a f (r + h)) := by
  unfold blockVal
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hc : t % h = r
  · rcases (mod_split_iff h r t hh hr).mp hc with hs | hs
    · rw [if_pos hc, if_pos hs, if_neg (show ¬ t % (2 * h) = r + h by omega), sub_zero]
      have ht : 2 * h * (t / (2 * h)) + r = t := by
        have := Nat.div_add_mod t (2 * h); omega
      have hst : step * (2 * h * (t / (2 * h)) + r) = step * t := by rw [ht]
      have hkey : om ^ (step * t) = om ^ (step * r) := by
        rw [← hst]; exact pow_step_shift n step h om hn hpow (t / (2 * h)) r
      rw [show (step + a) * t = a * t + step * t by ring, pow_add, hkey]
      ring
    · rw [if_pos hc, if_neg (show ¬ t % (2 * h) = r by omega), if_pos hs, zero_sub]
      have ht : 2 * h * (t / (2 * h)) + r + h = t := by
        have := Nat.div_add_mod t (2 * h); omega
      have hst : step * (2 * h * (t / (2 * h)) + r + h) = step * t := by rw [ht]
      have hkey : om ^ (step * t) = -om ^ (step * r) := by
        rw [← hst]; exact pow_step_shift_neg n step h om hn hpow hneg (t / (2 * h)) r
      rw [show (step + a) * t = a * t + step * t by ring, pow_add, hkey]
      ring
  · have hno : ¬(t % (2 * h) = r ∨ t % (2 * h) = r + h) := fun hx =>
      hc ((mod_split_iff h r t hh hr).mpr hx)
    rw [if_neg hc, if_neg (fun hx => hno (Or.inl hx)), if_neg (fun hx => hno (Or.inr hx))]
    ring

/-- **One stage advances the block invariant.**

If the buffer holds, in each of its `2^j` blocks of length `m = 2·half`, the
coefficients of `f(ω^(brev j B)·Y) mod (Y^m − 1)`, then after one more stage it
holds in each of its `2^(j+1)` blocks of length `half` the coefficients of
`f(ω^(brev (j+1) B')·Y) mod (Y^half − 1)`.

The `+` half of the butterfly is reduction mod `Y^half − 1` and the `−` half is
reduction mod `Y^half + 1` followed by the substitution `Y ↦ ω^step · Y`; the two
facts about `ω` are what make the second one land on `Y^half − 1` again. -/
theorem difStage_blockVal (n j half step : ℕ) (om : R)
    (hn : n = 2 ^ j * (2 * half)) (hstep : step = 2 ^ j) (hhalf : 0 < half)
    (hpow : om ^ n = 1) (hneg : om ^ (n / 2) = -1)
    (f cur : ℕ → R)
    (hcur : ∀ B r, B < 2 ^ j → r < 2 * half →
      cur (B * (2 * half) + r) = blockVal n (2 * half) om (brev j B) f r) :
    ∀ B' r', B' < 2 ^ (j + 1) → r' < half →
      difStage half step om cur (B' * half + r')
        = blockVal n half om (brev (j + 1) B') f r' := by
  intro B' r' hB' hr'
  have hnst : n = step * (2 * half) := by rw [hstep]; exact hn
  obtain ⟨B, hB2, hcase⟩ : ∃ B, B < 2 ^ j ∧ (B' = 2 * B ∨ B' = 2 * B + 1) := by
    refine ⟨B' / 2, ?_, by omega⟩
    have h1 : B' < 2 * 2 ^ j := by rw [pow_succ] at hB'; omega
    omega
  rcases hcase with hcase | hcase
  · -- the even block: the `+` half of the butterfly
    subst hcase
    have hm1 : (B * (2 * half) + r') % (2 * half) = r' := by
      rw [show B * (2 * half) + r' = r' + 2 * half * B by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [brev_two_mul, show 2 * B * half + r' = B * (2 * half) + r' by ring]
    simp only [difStage]
    rw [hm1, if_pos hr', show B * (2 * half) + r' + half = B * (2 * half) + (r' + half) by ring,
      hcur B r' hB2 (by omega), hcur B (r' + half) hB2 (by omega)]
    exact blockVal_split n half om (brev j B) f r' hhalf hr'
  · -- the odd block: the twiddled `−` half
    subst hcase
    have hm1 : (B * (2 * half) + (half + r')) % (2 * half) = half + r' := by
      rw [show B * (2 * half) + (half + r') = half + r' + 2 * half * B by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [brev_two_mul_add_one, ← hstep,
      show (2 * B + 1) * half + r' = B * (2 * half) + (half + r') by ring]
    simp only [difStage]
    rw [hm1, if_neg (by omega : ¬ half + r' < half),
      show B * (2 * half) + (half + r') - half = B * (2 * half) + r' by omega,
      show half + r' - half = r' by omega,
      hcur B r' hB2 (by omega), hcur B (half + r') hB2 (by omega),
      blockVal_twist n step half om (brev j B) f r' hhalf hr' hnst hpow hneg,
      show half + r' = r' + half by omega, Nat.mul_comm r' step]
    ring

/-- The stage invariant, carried through the `k` remaining stages.

`j` is the number of stages already done and `k` the number left, so `j + k = L`
throughout and the block length is `2^k`. The statement is what an induction on
`k` needs: [`difStage_blockVal`] advances `(j, k+1)` to `(j+1, k)`, and the base
case reads the invariant off at block length `1`. -/
theorem difRun_blockVal_aux (om : R) (n : ℕ) (hpow : om ^ n = 1)
    (hneg : om ^ (n / 2) = -1) (f : ℕ → R) :
    ∀ (k j : ℕ) (cur : ℕ → R), n = 2 ^ j * 2 ^ k →
      (∀ B r, B < 2 ^ j → r < 2 ^ k →
        cur (B * 2 ^ k + r) = blockVal n (2 ^ k) om (brev j B) f r) →
      ∀ B, B < 2 ^ (j + k) →
        difRun om k (2 ^ j) cur B = blockVal n 1 om (brev (j + k) B) f 0 := by
  intro k
  induction k with
  | zero =>
      intro j cur _hn hcur B hB
      have := hcur B 0 (by simpa using hB) (by norm_num)
      simpa using this
  | succ k ih =>
      intro j cur hn hcur B hB
      have hhalf : (0 : ℕ) < 2 ^ k := Nat.two_pow_pos k
      have hn' : n = 2 ^ j * (2 * 2 ^ k) := by rw [hn]; ring
      have hstep := difStage_blockVal n j (2 ^ k) (2 ^ j) om hn' rfl hhalf hpow hneg f cur
        (by
          intro B' r' hB' hr'
          have := hcur B' r' hB' (by simpa [pow_succ, Nat.mul_comm] using hr')
          simpa [pow_succ, Nat.mul_comm] using this)
      have hnext : n = 2 ^ (j + 1) * 2 ^ k := by rw [hn]; ring
      have hidx : j + 1 + k = j + (k + 1) := by omega
      have := ih (j + 1) (difStage (2 ^ k) (2 ^ j) om cur) hnext
        (fun B' r' hB' hr' => hstep B' r' hB' hr')
        B (by rw [hidx]; exact hB)
      rw [difRun_succ, show (2 : ℕ) ^ j * 2 = 2 ^ (j + 1) by ring, this, hidx]

/-- The forward transform, unrolled: after all `L` stages the buffer holds `f`
evaluated at the `n` powers `ω^(brev L k)`. -/
theorem difRun_blockVal (L : ℕ) (om : R) (n : ℕ) (hn : n = 2 ^ L)
    (hpow : om ^ n = 1) (hneg : om ^ (n / 2) = -1) (f : ℕ → R) (k : ℕ) (hk : k < n) :
    difRun om L 1 f k = ∑ t ∈ Finset.range n, f t * om ^ (brev L k * t) := by
  have hbase : ∀ B r, B < 2 ^ 0 → r < 2 ^ L →
      f (B * 2 ^ L + r) = blockVal n (2 ^ L) om (brev 0 B) f r := by
    intro B r hB hr
    have hB0 : B = 0 := by simpa using hB
    subst hB0
    rw [brev_zero, ← hn] at *
    simpa using (blockVal_full n om f r (by omega)).symm
  have := difRun_blockVal_aux om n hpow hneg f L 0
    f (by rw [hn]; ring) (by simpa using hbase) k (by simpa [← hn] using hk)
  simpa [blockVal_one] using this

/-! ## Convolution

Evaluation at an `n`-th root of unity is a ring homomorphism out of
`R[X]/(X^n − 1)`, which is the only thing the pointwise product needs.
-/

/-- The cyclic convolution of two length-`n` buffers. -/
def cyclicConv (n : ℕ) (a b : ℕ → R) : ℕ → R := fun t =>
  ∑ i ∈ Finset.range n, a i * b ((t + n - i % n) % n)

/-- The ordinary convolution of two length-`n` buffers, as a length-`2n` buffer:
`ordConv n a b t = ∑_{i+j=t, i,j<n} a i · b j`. -/
def ordConv (n : ℕ) (a b : ℕ → R) : ℕ → R := fun t =>
  ∑ i ∈ Finset.range n, if i ≤ t ∧ t - i < n then a i * b (t - i) else 0

/-- The rotation `t ↦ (t + n - d) % n` of `Finset.range n` is undone by
`u ↦ (u + d) % n`. -/
theorem rot_left_inv (n d t : ℕ) (hd : d < n) (ht : t < n) :
    ((t + n - d) % n + d) % n = t := by
  by_cases h : d ≤ t
  · have h1 : t + n - d = (t - d) + n := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (show t - d < n by omega),
      show t - d + d = t by omega, Nat.mod_eq_of_lt ht]
  · rw [Nat.mod_eq_of_lt (show t + n - d < n by omega),
      show t + n - d + d = t + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt ht]

/-- The other half of the rotation bijection of [`rot_left_inv`]. -/
theorem rot_right_inv (n d u : ℕ) (hd : d < n) (hu : u < n) :
    ((u + d) % n + n - d) % n = u := by
  by_cases h : u + d < n
  · rw [Nat.mod_eq_of_lt h, show u + d + n - d = u + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hu]
  · have h2 : (u + d) % n = u + d - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (show u + d - n < n by omega)]
    rw [h2, show u + d - n + n - d = u by omega, Nat.mod_eq_of_lt hu]

/-- Evaluating a cyclic convolution at an `n`-th root of unity multiplies the
evaluations. -/
theorem cyclicConv_eval (n : ℕ) (om : R) (e : ℕ) (hpow : (om ^ e) ^ n = 1)
    (a b : ℕ → R) :
    (∑ t ∈ Finset.range n, cyclicConv n a b t * om ^ (e * t))
      = (∑ t ∈ Finset.range n, a t * om ^ (e * t))
        * ∑ t ∈ Finset.range n, b t * om ^ (e * t) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  obtain ⟨x, hxdef⟩ : ∃ x : R, x = om ^ e := ⟨_, rfl⟩
  rw [← hxdef] at hpow
  -- `x ^ ·` only sees the residue mod `n`.
  have hx : ∀ s : ℕ, x ^ (s % n) = x ^ s := by
    intro s
    conv_rhs => rw [← Nat.div_add_mod s n]
    rw [pow_add, pow_mul, hpow, one_pow, one_mul]
  -- `i % n = i` inside the convolution, since `i` ranges over `Finset.range n`.
  have hconv : ∀ t : ℕ,
      cyclicConv n a b t = ∑ d ∈ Finset.range n, a d * b ((t + n - d) % n) := by
    intro t
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hd)]
  -- the rotation, for one fixed shift `d`
  have key : ∀ d ∈ Finset.range n,
      (∑ t ∈ Finset.range n, b ((t + n - d) % n) * x ^ t)
        = ∑ u ∈ Finset.range n, x ^ d * (b u * x ^ u) := by
    intro d hd
    have hdn : d < n := Finset.mem_range.mp hd
    refine Finset.sum_nbij' (fun t => (t + n - d) % n) (fun u => (u + d) % n)
      (fun t _ => Finset.mem_range.mpr (Nat.mod_lt _ hn))
      (fun u _ => Finset.mem_range.mpr (Nat.mod_lt _ hn))
      (fun t ht => rot_left_inv n d t hdn (Finset.mem_range.mp ht))
      (fun u hu => rot_right_inv n d u hdn (Finset.mem_range.mp hu))
      ?_
    intro t ht
    have htn : t < n := Finset.mem_range.mp ht
    have hexp : x ^ ((t + n - d) % n + d) = x ^ t := by
      rw [← hx ((t + n - d) % n + d), rot_left_inv n d t hdn htn]
    rw [← hexp, pow_add]
    ring
  simp only [pow_mul, ← hxdef]
  calc (∑ t ∈ Finset.range n, cyclicConv n a b t * x ^ t)
      = ∑ t ∈ Finset.range n, ∑ d ∈ Finset.range n,
          a d * (b ((t + n - d) % n) * x ^ t) := by
        refine Finset.sum_congr rfl ?_
        intro t _
        rw [hconv t, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun d _ => by ring)
    _ = ∑ d ∈ Finset.range n, ∑ t ∈ Finset.range n,
          a d * (b ((t + n - d) % n) * x ^ t) := Finset.sum_comm
    _ = ∑ d ∈ Finset.range n, a d * ∑ t ∈ Finset.range n, b ((t + n - d) % n) * x ^ t :=
        Finset.sum_congr rfl (fun d _ => (Finset.mul_sum _ _ _).symm)
    _ = ∑ d ∈ Finset.range n, a d * ∑ u ∈ Finset.range n, x ^ d * (b u * x ^ u) :=
        Finset.sum_congr rfl (fun d hd => by rw [key d hd])
    _ = ∑ d ∈ Finset.range n, (a d * x ^ d) * ∑ u ∈ Finset.range n, b u * x ^ u := by
        refine Finset.sum_congr rfl ?_
        intro d _
        rw [← Finset.mul_sum, mul_assoc]
    _ = (∑ t ∈ Finset.range n, a t * x ^ t) * ∑ t ∈ Finset.range n, b t * x ^ t :=
        (Finset.sum_mul _ _ _).symm

/-! ## The twist

`X ↦ ψ·Y` is a ring isomorphism `R[X]/(X^n + 1) → R[Y]/(Y^n − 1)` when
`ψ^n = −1`, and on coefficients it is `a_t ↦ a_t · ψ^t`. So the negacyclic
product of `a` and `b` is the untwisted cyclic product of their twists, which is
what lets a *cyclic* transform of length `n` compute a *negacyclic* product of
length `n`.
-/

/-- The negacyclic convolution of two length-`n` buffers: the ordinary product's
low block minus its high block. -/
def negConvR (n : ℕ) (a b : ℕ → R) : ℕ → R := fun t =>
  ordConv n a b t - ordConv n a b (n + t)

/-- The twist. -/
def twistR (psi : R) (a : ℕ → R) : ℕ → R := fun t => a t * psi ^ t

/-- **The twist carries the negacyclic product to the cyclic one.**

`cyclicConv n (twist a) (twist b) t = ψ^t · negConv n a b t`, so dividing the
cyclic product's coefficient `t` by `ψ^t` recovers the negacyclic one. -/
theorem twistConv (n : ℕ) (psi : R) (hpsi : psi ^ n = -1) (a b : ℕ → R)
    (t : ℕ) (ht : t < n) :
    cyclicConv n (twistR psi a) (twistR psi b) t = psi ^ t * negConvR n a b t := by
  simp only [cyclicConv, negConvR, ordConv, twistR]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Finset.mem_range] at hi
  rw [Nat.mod_eq_of_lt hi]
  by_cases hit : i ≤ t
  · have h1 : t + n - i = n + (t - i) := by omega
    rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (show t - i < n by omega)]
    rw [if_pos (show i ≤ t ∧ t - i < n from ⟨hit, by omega⟩),
      if_neg (show ¬(i ≤ n + t ∧ n + t - i < n) from by omega)]
    have hp : psi ^ i * psi ^ (t - i) = psi ^ t := by
      rw [← pow_add, show i + (t - i) = t from by omega]
    rw [sub_zero, ← hp]
    ring
  · have h1 : t + n - i = n + t - i := by omega
    rw [h1, Nat.mod_eq_of_lt (show n + t - i < n by omega)]
    rw [if_neg (show ¬(i ≤ t ∧ t - i < n) from by omega),
      if_pos (show i ≤ n + t ∧ n + t - i < n from ⟨by omega, by omega⟩)]
    have hp : psi ^ i * psi ^ (n + t - i) = - psi ^ t := by
      rw [← pow_add, show i + (n + t - i) = n + t from by omega, pow_add, hpsi]
      ring
    have hp' : psi ^ t = -(psi ^ i * psi ^ (n + t - i)) := by rw [hp]; ring
    rw [hp']
    ring

end HachiEquiv.NttMath

