/-
`Opt.lean` -- the optimized variants and their `opt_eq_spec` lemmas.

Every `Foo.opt` here is a pure Lean definition in the shape `lean-to-rust`
translates trivially (one fold = one `while` loop, explicit tuple state,
ascending indices), named after the **Rust item** it replaces, and paired in the
same change with a proved `opt_eq_spec` lemma against the ArkLib definition that
item mirrors. The lemma is stated between pure functions: at candidate time no
Rust exists, so the algebra is settled here and the Aeneas triple over the
extracted model (the outer verification pass) only has to route through it.
`Check.lean` § 4 prints the axioms of every lemma below, which is what makes a
`sorry` here a build failure rather than silent debt (`lean-opt` § "The
opt-contract").

# Stage 6, iteration 1 (zerocheck; brief `briefs/target-4-zero-check.md`)

## Candidate A -- `ringswitch::c_eval_at`, `ringswitch::c_eval_at_modulus`
Strategy `opt-algo-swap`, "running state instead of recomputation". The frozen
translation is the specification's power sum with the power *recomputed* per
term: `hachi/src/ringswitch.rs:280` calls `ext_pow alpha k` (`:254`) inside the
`k`-loop, so term `k` costs `k` extension multiplications and the call costs
`Σ_{k<N} k = N(N-1)/2 ≈ 524 000` of them at `N = 1024`. The same shape appears
at `:308` for the modulus `φ = X^N + 1`, over `N + 1` terms. Both variants thread
the power through the loop state instead: `2N` multiplications for `c_eval_at`,
`N` for the modulus.
-/
import ZeroCheck
import Sumcheck

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly CompPoly.Extension CompPoly.Extension.Ext ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.Opt

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme
open HachiEquiv.RingSwitch HachiEquiv.Ext HachiEquiv.ZeroCheck HachiEquiv.Sumcheck

/-! ## 1. `cEvalAt` with a running power

State `(acc, pw)`, initial `(0, 1)`; step `k` reads coefficient `k`, adds
`φF (p.coeff k) * pw` to the accumulator and advances `pw` by one factor of
`a`. Both components stay explicit so the Rust translation is
`acc = acc + from_base(p.coeff(k)) * pw; pw = pw * alpha; k += 1` in that
order. -/

/-- The loop of `c_eval_at.opt`: `d` ascending steps over the state `(acc, pw)`. -/
def c_eval_at.optLoop (φF : ZMod q →+* F) (a : F) (p : CPolynomial (ZMod q)) (d : ℕ) : F × F :=
  (List.range d).foldl (fun s k => (s.1 + φF (p.coeff k) * s.2, s.2 * a)) (0, 1)

/-- `cEvalAt` evaluated over the first `d` coefficients with one multiplication
per term instead of a fresh power loop per term. -/
def c_eval_at.opt (φF : ZMod q →+* F) (a : F) (p : CPolynomial (ZMod q)) (d : ℕ) : F :=
  (c_eval_at.optLoop φF a p d).1

/-- The loop invariant: after `d` steps the accumulator is the partial power sum
and the running power is `a ^ d`. -/
theorem c_eval_at.optLoop_eq (φF : ZMod q →+* F) (a : F) (p : CPolynomial (ZMod q)) (d : ℕ) :
    c_eval_at.optLoop φF a p d
      = (∑ l ∈ Finset.range d, φF (p.coeff l) * a ^ l, a ^ d) := by
  induction d with
  | zero =>
      unfold c_eval_at.optLoop
      simp
  | succ n ih =>
      unfold c_eval_at.optLoop at ih ⊢
      rw [List.range_succ, List.foldl_append, ih]
      simp [Finset.sum_range_succ, pow_succ]

/-- **The candidate's lemma.** The running-power loop computes the
specification's evaluation, for any `d` above the degree. -/
theorem c_eval_at.opt_eq_spec (φF : ZMod q →+* F) (a : F) (p : CPolynomial (ZMod q)) {d : ℕ}
    (hp : p.natDegree < d) :
    c_eval_at.opt φF a p d = InnerOuter.cEvalAt φF a p := by
  unfold c_eval_at.opt
  rw [c_eval_at.optLoop_eq, InnerOuter.cEvalAt_eq_sum_range φF a hp]

/-- The instantiation at this crate's carrier that the later Aeneas proof needs:
a represented `Rq` has `CPolynomial` degree `< N` (`toRq_natDegree_lt`), so `N`
steps suffice. -/
theorem c_eval_at.opt_eq_spec_toRq (alpha : cpoly.field.Ext4) (p : ring.Rq) :
    c_eval_at.opt phiF (toExt alpha) (toRq p).1 N
      = InnerOuter.cEvalAt phiF (toExt alpha) (toRq p).1 :=
  c_eval_at.opt_eq_spec phiF (toExt alpha) (toRq p).1 (toRq_natDegree_lt p)

/-! ## 2. The modulus, `φ = X^N + 1`

`Φ.φ` has coefficient `1` at `0` and at `N` and `0` everywhere else
(`phi_coeff`), so the specification's `N + 1`-term sum is `a ^ N + 1`. A plain
running-power loop of `d` steps, then `+ 1`: `d` multiplications and one
addition, no coefficient branch and no `from_base` at all. -/

/-- The running-power loop: state `pw`, initial `1`, `d` steps of `pw * a`. -/
def c_eval_at_modulus.optPow (a : F) (d : ℕ) : F :=
  (List.range d).foldl (fun pw _ => pw * a) 1

/-- `cEvalAt φF a (X^d + 1)` with `d` multiplications and one addition. -/
def c_eval_at_modulus.opt (a : F) (d : ℕ) : F :=
  c_eval_at_modulus.optPow a d + 1

/-- The loop invariant of the running-power loop. -/
theorem c_eval_at_modulus.optPow_eq (a : F) (d : ℕ) : c_eval_at_modulus.optPow a d = a ^ d := by
  induction d with
  | zero =>
      unfold c_eval_at_modulus.optPow
      simp
  | succ n ih =>
      unfold c_eval_at_modulus.optPow at ih ⊢
      rw [List.range_succ, List.foldl_append, ih]
      simp [pow_succ]

/-- The generic closed form, stated for the record: the loop is `a ^ d + 1`. -/
theorem c_eval_at_modulus.opt_eq_pow_add_one (a : F) (d : ℕ) :
    c_eval_at_modulus.opt a d = a ^ d + 1 := by
  unfold c_eval_at_modulus.opt
  rw [c_eval_at_modulus.optPow_eq]

/-- **The candidate's lemma**, at this crate's `phiF`, `Φ` and `N`: the
running-power loop computes `cEvalAt φF α Φ.φ`, the `φ(α)` factor of
`mAlphaTilde` (`ZeroCheck/Constraints.lean:519`). Same route as
`c_eval_at_modulus_spec`: `cEvalAt_eq_sum_range` at `d = N + 1` (licensed by
`phi_natDegree`), then `phi_coeff` collapses the sum to `1 + a ^ N`. -/
theorem c_eval_at_modulus.opt_eq_spec (a : F) :
    c_eval_at_modulus.opt a N = InnerOuter.cEvalAt phiF a Φ.φ := by
  have hdeg : Φ.φ.natDegree < N + 1 := by rw [phi_natDegree]; omega
  have hN0 : N ≠ 0 := by norm_num [N]
  have hcN : Φ.φ.coeff N = 1 := by rw [phi_coeff]; simp [hN0]
  have htail : phiF (Φ.φ.coeff N) * a ^ N = a ^ N := by rw [hcN, map_one, one_mul]
  have hhead : ∑ l ∈ Finset.range N, phiF (Φ.φ.coeff l) * a ^ l = 1 := by
    have hmem : (0 : ℕ) ∈ Finset.range N := Finset.mem_range.mpr (by norm_num [N])
    have hzero : ∀ l ∈ Finset.range N, l ≠ 0 →
        phiF (Φ.φ.coeff l) * a ^ l = 0 := by
      intro l hl hl0
      have hlN : l ≠ N := by
        have := Finset.mem_range.mp hl
        omega
      rw [phi_coeff]
      simp [hl0, hlN]
    rw [Finset.sum_eq_single_of_mem 0 hmem hzero, phi_coeff]
    simp
  unfold c_eval_at_modulus.opt
  rw [InnerOuter.cEvalAt_eq_sum_range phiF a hdeg, Finset.sum_range_succ, hhead, htail,
    c_eval_at_modulus.optPow_eq]
  exact add_comm _ _

/-! # Candidate B -- `zerocheck::c_w_table_mle`, `h_zero`, `h_zero_is_zero`, `w_table_mle_eval`

Strategy `opt-algo-swap`: "running state instead of recomputation" (brief item 5)
plus the proved `evalMle` swap (brief item 1). The frozen translation builds the
`2^m₀` table by calling `w_table` at every flat index, and in the digit branch
each call rebuilds the whole `rhoDigits` polynomial to read one coefficient
(`hachi/src/zerocheck.rs:155-176`, `:179-190`): a `d = 1024`× waste on the digit
block. Here the row is computed **once** (`wTableRow`) and its `N` coefficients
streamed; `blockLoop`'s second guard truncates the last block, so the traversal
emits exactly `2^m₀` entries for every `m₀`, `μ`, `n` -- no hypothesis the
specification does not have. The evaluation is `CMlPolynomialEval.evalMle`, the
`O(2^m₀)` layer fold, equal to the specification's Lagrange dot by CompPoly's
`eval_mle_eq_eval` (`CompPoly/Multilinear/Basic.lean:574`). -/

variable {μ n : ℕ}

/-! ## The row of the table, computed once

`wTable` reads entry `idx` as row `u = idx / d`, coefficient `ℓ = idx % d`
(`Constraints.lean:140`). The row is a *polynomial*, and it is the same
polynomial for all `d` values of `ℓ`; the shipped code rebuilt it `d` times.

`wTableRow`, `wTableFlat_eq_row` and `wTable_symm_eq_row` used to live here and
now live in `lean/ZeroCheck.lean` § "The row of the table, computed once",
beside `wTableFlat`: the Aeneas triples for the accepted champion are stated
with them, and this file **imports** `ZeroCheck`, so they cannot be below it.
They are in scope unqualified through the `open HachiEquiv.ZeroCheck` above. -/

/-- The flat index of coefficient `l` of row `u`, decoded back. -/
private theorem div_mod_of_block {u l : ℕ} (hl : l < N) :
    (N * u + l) / N = u ∧ (N * u + l) % N = l := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by norm_num : 0 < N),
      Nat.div_eq_of_lt hl, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]

/-- The row stride, for the one place the running base index has to be
identified with a product. -/
private theorem N_mul_succ (u : ℕ) : N * (u + 1) = N * u + N := by ring

/-! ## The two nested loops

One Lean loop = one Rust `while`. Both are counter loops over ascending indices
with an explicit state tuple: the outer state is `(u, base, acc)`, the inner
`(l, acc)`. -/

/-- Inner loop: push `φ (phiF (r.coeff l))` for ascending `l`, stopping at the
row width `N` or at the table end `size`, whichever comes first. The second
guard is what truncates the final block, so the traversal never overshoots
`size` and never needs padding. -/
def blockLoop (φ : F → F) (size : ℕ) (r : CPolynomial (ZMod q)) (base : ℕ)
    (l : ℕ) (acc : List F) : List F :=
  if _h : l < N ∧ base + l < size then
    blockLoop φ size r base (l + 1) (acc ++ [φ (phiF (r.coeff l))])
  else acc
termination_by N - l
decreasing_by omega

/-- Outer loop: for ascending rows `u` while the row's base index is inside the
table, compute `wTableRow sw u` **once** and push its coefficient block. -/
def rowLoop (φ : F → F) (size : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n)
    (u : ℕ) (base : ℕ) (acc : List F) : List F :=
  if _h : base < size then
    rowLoop φ size sw (u + 1) (base + N) (blockLoop φ size (wTableRow sw u) base 0 acc)
  else acc
termination_by size - base
decreasing_by
  have hN : 0 < N := by norm_num
  omega

/-- The optimized committed table `w̃` in Lagrange form, as a list of `2 ^ m₀`
entries (spec: `cWTableMle`, `Constraints.lean:328`). -/
def c_w_table_mle.opt (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n) : List F :=
  rowLoop (fun v => v) (2 ^ m₀) sw 0 0 []

/-- The optimized range-constraint block `H₀` in Lagrange form
(spec: `hZero`, `Constraints.lean:204`). -/
def h_zero.opt (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n) : List F :=
  rowLoop (InnerOuter.rangeProduct (F := F) 16) (2 ^ m₀) sw 0 0 []

/-! ## The traversal covers `[0, size)` exactly

Both loops are proved by induction on an upper bound `k` of their own
termination measure, which is the shape an Aeneas `loop.spec_decr_nat` proof
takes on the Rust side. -/

/-- Inner-loop invariant: on entry `acc` holds the entries below `base + l`; on
exit it holds the entries below `min (base + N) size`. -/
theorem blockLoop_spec (φ : F → F) (size : ℕ) (r : CPolynomial (ZMod q)) (base : ℕ)
    (g : ℕ → F) (hg : ∀ l' < N, g (base + l') = φ (phiF (r.coeff l'))) (k : ℕ) :
    ∀ (l : ℕ) (acc : List F), N - l ≤ k → l ≤ N → base + l ≤ size →
      acc.length = base + l → (∀ t < base + l, acc.getD t 0 = g t) →
      (blockLoop φ size r base l acc).length = min (base + N) size ∧
        ∀ t < min (base + N) size, (blockLoop φ size r base l acc).getD t 0 = g t := by
  induction k with
  | zero =>
    intro l acc hk hl hbl hlen hval
    rw [blockLoop, dif_neg (by omega)]
    exact ⟨by omega, fun t ht => hval t (by omega)⟩
  | succ k ih =>
    intro l acc hk hl hbl hlen hval
    by_cases hgo : l < N ∧ base + l < size
    · rw [blockLoop, dif_pos hgo]
      refine ih (l + 1) (acc ++ [φ (phiF (r.coeff l))]) (by omega) (by omega) (by omega)
        (by rw [List.length_append, hlen]; simp; omega) ?_
      intro t ht
      rcases Nat.lt_or_ge t (base + l) with htlt | htge
      · rw [getD_append_lt _ _ _ (by omega), hval t htlt]
      · have hteq : t = acc.length := by omega
        rw [hteq, getD_append_eq, hlen, hg l hgo.1]
    · rw [blockLoop, dif_neg hgo]
      exact ⟨by omega, fun t ht => hval t (by omega)⟩

/-- Outer-loop invariant: on entry `acc` holds the entries below
`min base size`; on exit it is the whole table. `base = N * u` is the running
state's own invariant. -/
theorem rowLoop_spec (φ : F → F) (size : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n) (k : ℕ) :
    ∀ (u base : ℕ) (acc : List F), size - base ≤ k → base = N * u →
      acc.length = min base size →
      (∀ t < min base size,
        acc.getD t 0 = φ (phiF ((wTableRow sw (t / N)).coeff (t % N)))) →
      (rowLoop φ size sw u base acc).length = size ∧
        ∀ t < size, (rowLoop φ size sw u base acc).getD t 0 =
          φ (phiF ((wTableRow sw (t / N)).coeff (t % N))) := by
  induction k with
  | zero =>
    intro u base acc hk hbase hlen hval
    rw [rowLoop, dif_neg (by omega)]
    exact ⟨by omega, fun t ht => hval t (by omega)⟩
  | succ k ih =>
    intro u base acc hk hbase hlen hval
    by_cases hgo : base < size
    · rw [rowLoop, dif_pos hgo]
      have hN : 0 < N := by norm_num
      have hblock := blockLoop_spec φ size (wTableRow sw u) base
        (fun t => φ (phiF ((wTableRow sw (t / N)).coeff (t % N))))
        (by
          intro l' hl'
          obtain ⟨hd, hm⟩ := div_mod_of_block (u := u) hl'
          rw [hbase, hd, hm])
        N 0 acc (by omega) (by omega) (by omega) (by omega)
        (by intro t ht; exact hval t (by omega))
      refine ih (u + 1) (base + N) _ (by omega) (by rw [hbase, N_mul_succ]) hblock.1 ?_
      intro t ht
      exact hblock.2 t ht
    · rw [rowLoop, dif_neg hgo]
      exact ⟨by omega, fun t ht => hval t (by omega)⟩

/-- Both list candidates have the length the specification's `Vector` has. -/
theorem rowLoop_length (φ : F → F) (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n) :
    (rowLoop φ (2 ^ m₀) sw 0 0 []).length = 2 ^ m₀ :=
  (rowLoop_spec φ (2 ^ m₀) sw (2 ^ m₀) 0 0 [] (Nat.sub_le _ _) (by simp) (by simp)
    (by intro t ht; exact absurd ht (by omega))).1

/-- Entrywise value of either list candidate, in terms of the audited
`wTableFlat` (`lean/ZeroCheck.lean:522`). -/
theorem rowLoop_getD (φ : F → F) (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n)
    (t : ℕ) (ht : t < 2 ^ m₀) :
    (rowLoop φ (2 ^ m₀) sw 0 0 []).getD t 0 = φ (wTableFlat m₀ sw t) := by
  have h := (rowLoop_spec φ (2 ^ m₀) sw (2 ^ m₀) 0 0 [] (Nat.sub_le _ _) (by simp) (by simp)
    (by intro t ht; exact absurd ht (by omega))).2 t ht
  rw [h, wTableFlat_eq_row sw t ht]

/-! ## The candidates against the specification -/

theorem c_w_table_mle.opt_length (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n) :
    (c_w_table_mle.opt m₀ sw).length = 2 ^ m₀ :=
  rowLoop_length _ m₀ sw

theorem c_w_table_mle.opt_getD (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n)
    (t : ℕ) (ht : t < 2 ^ m₀) :
    (c_w_table_mle.opt m₀ sw).getD t 0 = wTableFlat m₀ sw t :=
  rowLoop_getD _ m₀ sw t ht

/-- **Candidate 2's lemma.** Entry `t` of the row-hoisted table is entry `t` of
`cWTableMle` (`Constraints.lean:328`). Entrywise at every `t < 2 ^ m₀`, which is
the shape `c_w_table_mle_spec`'s `toEvals = Vector.ofFn (getD …)` conclusion
consumes (`lean/ZeroCheck.lean:599`). -/
theorem c_w_table_mle.opt_eq_spec (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n)
    (t : ℕ) (h : t < 2 ^ m₀) :
    (c_w_table_mle.opt m₀ sw).getD t 0 = (InnerOuter.cWTableMle Φ m₀ phiF 16 sw).get ⟨t, h⟩ := by
  rw [c_w_table_mle.opt_getD m₀ sw t h, InnerOuter.cWTableMle, Vector.get_ofFn,
    wTableFlat, dif_pos h]

theorem h_zero.opt_length (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n) :
    (h_zero.opt m₀ sw).length = 2 ^ m₀ :=
  rowLoop_length _ m₀ sw

theorem h_zero.opt_getD (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n)
    (t : ℕ) (ht : t < 2 ^ m₀) :
    (h_zero.opt m₀ sw).getD t 0 = InnerOuter.rangeProduct 16 (wTableFlat m₀ sw t) :=
  rowLoop_getD _ m₀ sw t ht

/-- **Candidate 3's lemma.** Entry `t` of the row-hoisted `H₀` is entry `t` of
`hZero` (`Constraints.lean:204`). -/
theorem h_zero.opt_eq_spec (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n)
    (t : ℕ) (h : t < 2 ^ m₀) :
    (h_zero.opt m₀ sw).getD t 0 = (InnerOuter.hZero Φ m₀ phiF 16 sw).get ⟨t, h⟩ := by
  rw [h_zero.opt_getD m₀ sw t h, InnerOuter.hZero, Vector.get_ofFn, wTableFlat, dif_pos h]

/-! ## The verdict, as a branchless fold

Same traversal, `Bool` state instead of a list: `zero && (P_b(entry) == 0)`,
running to the end rather than returning early -- the shape
`h_zero_is_zero_loop_spec` mirrors (`lean/ZeroCheck.lean:1038`). The comparison
is `decide (… = 0)`; `F` has `DecidableEq`
(`CompPoly/Fields/Extension/Defs.lean:282`), which is the Lean side of
`Ext4::is_zero` as `ext_is_zero_spec` states it. -/

/-- Inner loop of the verdict. -/
def zeroBlockLoop (size : ℕ) (r : CPolynomial (ZMod q)) (base : ℕ)
    (l : ℕ) (zero : Bool) : Bool :=
  if _h : l < N ∧ base + l < size then
    zeroBlockLoop size r base (l + 1)
      (zero && decide (InnerOuter.rangeProduct 16 (phiF (r.coeff l)) = 0))
  else zero
termination_by N - l
decreasing_by omega

/-- Outer loop of the verdict: one `wTableRow` per row. -/
def zeroRowLoop (size : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n)
    (u : ℕ) (base : ℕ) (zero : Bool) : Bool :=
  if _h : base < size then
    zeroRowLoop size sw (u + 1) (base + N)
      (zeroBlockLoop size (wTableRow sw u) base 0 zero)
  else zero
termination_by size - base
decreasing_by
  have hN : 0 < N := by norm_num
  omega

/-- The zero-check's verdict: is every entry of `H₀` zero? -/
def h_zero_is_zero.opt (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n) : Bool :=
  zeroRowLoop (2 ^ m₀) sw 0 0 true

theorem zeroBlockLoop_spec (size : ℕ) (r : CPolynomial (ZMod q)) (base : ℕ)
    (P : ℕ → Prop)
    (hg : ∀ l' < N, (InnerOuter.rangeProduct 16 (phiF (r.coeff l')) = 0) ↔ P (base + l'))
    (k : ℕ) :
    ∀ (l : ℕ) (zero : Bool), N - l ≤ k → l ≤ N → base + l ≤ size →
      (zero = true ↔ ∀ t < base + l, P t) →
      (zeroBlockLoop size r base l zero = true ↔ ∀ t < min (base + N) size, P t) := by
  induction k with
  | zero =>
    intro l zero hk hl hbl hz
    rw [zeroBlockLoop, dif_neg (by omega), hz]
    exact ⟨fun h t ht => h t (by omega), fun h t ht => h t (by omega)⟩
  | succ k ih =>
    intro l zero hk hl hbl hz
    by_cases hgo : l < N ∧ base + l < size
    · rw [zeroBlockLoop, dif_pos hgo]
      refine ih (l + 1) _ (by omega) (by omega) (by omega) ?_
      rw [Bool.and_eq_true, decide_eq_true_iff, hz]
      constructor
      · rintro ⟨hall, hlast⟩ t ht
        rcases Nat.lt_or_ge t (base + l) with htlt | htge
        · exact hall t htlt
        · have hteq : t = base + l := by omega
          rw [hteq]
          exact (hg l hgo.1).mp hlast
      · intro h
        exact ⟨fun t ht => h t (by omega), (hg l hgo.1).mpr (h (base + l) (by omega))⟩
    · rw [zeroBlockLoop, dif_neg hgo, hz]
      exact ⟨fun h t ht => h t (by omega), fun h t ht => h t (by omega)⟩

theorem zeroRowLoop_spec (size : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n) (k : ℕ) :
    ∀ (u base : ℕ) (zero : Bool), size - base ≤ k → base = N * u →
      (zero = true ↔ ∀ t < min base size,
        InnerOuter.rangeProduct 16 (phiF ((wTableRow sw (t / N)).coeff (t % N))) = 0) →
      (zeroRowLoop size sw u base zero = true ↔ ∀ t < size,
        InnerOuter.rangeProduct 16 (phiF ((wTableRow sw (t / N)).coeff (t % N))) = 0) := by
  induction k with
  | zero =>
    intro u base zero hk hbase hz
    rw [zeroRowLoop, dif_neg (by omega), hz]
    exact ⟨fun h t ht => h t (by omega), fun h t ht => h t (by omega)⟩
  | succ k ih =>
    intro u base zero hk hbase hz
    by_cases hgo : base < size
    · rw [zeroRowLoop, dif_pos hgo]
      have hN : 0 < N := by norm_num
      have hblock := zeroBlockLoop_spec size (wTableRow sw u) base
        (fun t => InnerOuter.rangeProduct 16 (phiF ((wTableRow sw (t / N)).coeff (t % N))) = 0)
        (by
          intro l' hl'
          obtain ⟨hd, hm⟩ := div_mod_of_block (u := u) hl'
          rw [hbase, hd, hm])
        N 0 zero (by omega) (by omega) (by omega)
        (by rw [hz]
            exact ⟨fun h t ht => h t (by omega), fun h t ht => h t (by omega)⟩)
      refine ih (u + 1) (base + N) _ (by omega) (by rw [hbase, N_mul_succ]) ?_
      rw [hblock]
    · rw [zeroRowLoop, dif_neg hgo, hz]
      exact ⟨fun h t ht => h t (by omega), fun h t ht => h t (by omega)⟩

/-- **Candidate 4's lemma.** The row-hoisted branchless fold decides
`hZero = 0`, in the statement shape of `h_zero_is_zero_spec`
(`lean/ZeroCheck.lean:1038`) -- an `↔`, so the rejection path is covered too. -/
theorem h_zero_is_zero.opt_eq_spec (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n) :
    h_zero_is_zero.opt m₀ sw = true ↔ InnerOuter.hZero Φ m₀ phiF 16 sw = 0 := by
  rw [h_zero_is_zero.opt,
    zeroRowLoop_spec (2 ^ m₀) sw (2 ^ m₀) 0 0 true (Nat.sub_le _ _) (by simp)
      (by exact ⟨fun _ t ht => absurd ht (by omega), fun _ => rfl⟩),
    InnerOuter.hZero_eq_zero_iff,
    forall_cube_iff_forall_flat
      (fun x => InnerOuter.rangeProduct 16 (InnerOuter.wTable Φ m₀ phiF 16 sw x) = 0)]
  constructor
  · intro h t ht
    rw [wTable_symm_eq_row sw t ht]
    exact h t ht
  · intro h t ht
    rw [← wTable_symm_eq_row sw t ht]
    exact h t ht

/-! ## The evaluation swap

`cpoly`'s `MultilinearEvals::eval` is the `O(m₀·2^m₀)` Lagrange dot;
`CMlPolynomialEval.evalMle` is the `O(2^m₀)` layer fold, and CompPoly proves
them equal (`eval_mle_eq_eval`, `CompPoly/Multilinear/Basic.lean:574`). -/

/-- The optimized table read as ArkLib's `CMlPolynomialEval F m₀`, through the
same `Vector.ofFn (getD …)` shape `toEvals` uses (`lean/ZeroCheck.lean:129`). -/
def optEvals (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n) : CMlPolynomialEval F m₀ :=
  Vector.ofFn (fun i : Fin (2 ^ m₀) => (c_w_table_mle.opt m₀ sw).getD i.val 0)

theorem optEvals_eq_spec (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n) :
    optEvals m₀ sw = InnerOuter.cWTableMle Φ m₀ phiF 16 sw := by
  rw [optEvals, InnerOuter.cWTableMle]
  refine congrArg Vector.ofFn (funext fun j => ?_)
  rw [c_w_table_mle.opt_getD m₀ sw j.val j.isLt, wTableFlat, dif_pos j.isLt, Fin.eta]

/-- The optimized evaluation claim `mle[w̃](a)`: the row-hoisted table, folded
layer by layer. -/
def w_table_mle_eval.opt (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n) (a : Fin m₀ → F) : F :=
  CMlPolynomialEval.evalMle (optEvals m₀ sw) (Vector.ofFn a)

/-- **Candidate 5's lemma.** The layer fold over the row-hoisted table is
`wTableMleEval` (`Constraints.lean:335`). -/
theorem w_table_mle_eval.opt_eq_spec (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n)
    (a : Fin m₀ → F) :
    w_table_mle_eval.opt m₀ sw a = InnerOuter.wTableMleEval Φ m₀ phiF 16 sw a := by
  rw [w_table_mle_eval.opt, CMlPolynomialEval.eval_mle_eq_eval, optEvals_eq_spec,
    InnerOuter.wTableMleEval]

/-! # Candidate C -- `sumcheck::alpha_public_table`

Strategy `opt-algo-swap`, "precomputed tables" (brief `target-4-zero-check.md`
§ Strategy candidates, items 3 and 4).

The frozen translation (`hachi/src/sumcheck.rs:436`) calls
`zerocheck::alpha_public_evals` (`hachi/src/zerocheck.rs:466`) once per flat cube
index. That call re-derives, for **every** one of the `2 ^ m₀` entries, data that
depends only on `u = idx / d` and `ℓ = idx % d`:

* `alpha_tilde(α, ℓ)` (`zerocheck.rs:350`) -- up to `d - 1 = 1023` multiplications;
* `eq_weight(τ₁, i)` (`zerocheck.rs:383`) -- `m₁` multiplications, `n` times;
* `m_alpha_tilde(s, α, i, u)` (`zerocheck.rs:426`) -- one `c_eval_at` (`2N`
  multiplications with candidate A, `N(N-1)/2` without) or one
  `c_eval_at_modulus` plus a `base_pow(e)`, `n` times.

All of it is a function of `(i, u)` and `ℓ` alone. This candidate builds the
three tables once and reduces each entry to `n` multiplications, `n` additions
and a handful of lookups. -/

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

/-! ## 1. The power table `α^ℓ`

State `(acc, pw)`, initial `([], 1)`; step `ℓ` pushes `pw` and advances it by one
factor of `α`. `d` multiplications for the whole table, against the
`Σ_{ℓ<d} ℓ = d(d−1)/2 ≈ 524 000` the per-entry `alpha_tilde` costs at `d = N`. -/

/-- `[α^0, …, α^(d-1)]`, one multiplication per entry. -/
def alphaPowTable (α : F) (d : ℕ) : List F :=
  ((List.range d).foldl (fun s _ => (s.1 ++ [s.2], s.2 * α)) (([] : List F), (1 : F))).1

/-- The loop invariant: after `k` steps the list holds `α^0 … α^(k-1)` and the
running power is `α^k`. -/
theorem alphaPowLoop_eq (α : F) (d : ℕ) :
    (List.range d).foldl (fun s _ => (s.1 ++ [s.2], s.2 * α)) (([] : List F), (1 : F))
      = ((List.range d).map (fun l => α ^ l), α ^ d) := by
  induction d with
  | zero => simp
  | succ t ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp [pow_succ]

theorem alphaPowTable_length (α : F) (d : ℕ) : (alphaPowTable α d).length = d := by
  rw [alphaPowTable, alphaPowLoop_eq]; simp

/-- Entry `ℓ` of the power table is `α ^ ℓ` -- the specification's `alphaTilde`
(`ZeroCheck/Constraints.lean:502`). -/
theorem alphaPowTable_getD (α : F) {d ℓ : ℕ} (h : ℓ < d) :
    (alphaPowTable α d).getD ℓ 0 = α ^ ℓ := by
  rw [alphaPowTable, alphaPowLoop_eq, List.getD_eq_getElem _ _ (by simpa using h)]
  simp

/-! ## 2. The equality-weight table `eq̃(τ₁, i)`

`n` entries, entry `i` the `∏ j : Fin m₁` factor of `alphaPublicEvals`
(`Constraints.lean:845-847`) when `i < 2^m₁` and `0` otherwise. The bits of `i`
are read by a **running quotient**, exactly as `zerocheck::eq_weight`
(`zerocheck.rs:383`) does, so no power of two is ever formed and the statement
needs no `2 ^ m₁ ≤ Usize.max`. The cube guard is decided the same way, mirroring
`zerocheck::below_two_pow`. -/

/-- `i < 2 ^ m`, decided by halving `i` `m` times -- the specification's cube
guard without materializing the cube size. -/
def belowTwoPow (i m : ℕ) : Bool :=
  decide ((List.range m).foldl (fun qq _ => qq / 2) i = 0)

theorem halveLoop_eq (i m : ℕ) : (List.range m).foldl (fun qq _ => qq / 2) i = i / 2 ^ m := by
  induction m with
  | zero => simp
  | succ t ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp [Nat.div_div_eq_div_mul, pow_succ]

theorem belowTwoPow_eq_true_iff (i m : ℕ) : belowTwoPow i m = true ↔ i < 2 ^ m := by
  have hp : 0 < 2 ^ m := by positivity
  rw [belowTwoPow, decide_eq_true_eq, halveLoop_eq]
  constructor
  · intro hd
    by_contra hc
    rw [Nat.not_lt] at hc
    have := Nat.div_pos hc hp
    omega
  · intro hlt
    exact Nat.div_eq_of_lt hlt

/-- The running-quotient bit product: state `(q, acc)`, initial `(i, 1)`; step
`j` multiplies by `f j` or `1 - f j` according to the low bit of `q`, then
halves `q`. -/
def bitProd (f : ℕ → F) (m i : ℕ) : F :=
  ((List.range m).foldl
    (fun s j => (s.1 / 2, s.2 * (if s.1 % 2 = 1 then f j else 1 - f j))) (i, (1 : F))).2

theorem bitProdLoop_eq (f : ℕ → F) (m i : ℕ) :
    (List.range m).foldl
        (fun s j => (s.1 / 2, s.2 * (if s.1 % 2 = 1 then f j else 1 - f j))) (i, (1 : F))
      = (i / 2 ^ m,
          ∏ s ∈ Finset.range m, (if i / 2 ^ s % 2 = 1 then f s else 1 - f s)) := by
  induction m with
  | zero => simp
  | succ t ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp [Finset.prod_range_succ, Nat.div_div_eq_div_mul, pow_succ]

theorem bitProd_eq_prod (f : ℕ → F) (m i : ℕ) :
    bitProd f m i = ∏ s ∈ Finset.range m, (if Nat.testBit i s then f s else 1 - f s) := by
  rw [bitProd, bitProdLoop_eq]
  show (∏ s ∈ Finset.range m, (if i / 2 ^ s % 2 = 1 then f s else 1 - f s)) = _
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp

/-- `τ₁` read as a total function on `ℕ` -- the Rust side indexes a `Vec`, so the
out-of-range branch is never taken. -/
def tauAt {m₁ : ℕ} (τ₁ : Fin m₁ → F) (j : ℕ) : F :=
  if h : j < m₁ then τ₁ ⟨j, h⟩ else 0

/-- The `n`-entry table of `m₁`-cube equality weights, built once. -/
def eqWeightTable {m₁ : ℕ} (τ₁ : Fin m₁ → F) (n : ℕ) : List F :=
  (List.range n).foldl
    (fun acc i => acc ++ [if belowTwoPow i m₁ then bitProd (tauAt τ₁) m₁ i else 0]) []

theorem eqWeightTable_length {m₁ : ℕ} (τ₁ : Fin m₁ → F) (n : ℕ) :
    (eqWeightTable τ₁ n).length = n :=
  foldl_push_length _ n

/-- Entry `i` of the weight table is the specification's `∏ j : Fin m₁` factor
under its own `i < 2 ^ m₁` guard (`Constraints.lean:845-847`). -/
theorem eqWeightTable_getD {m₁ : ℕ} (τ₁ : Fin m₁ → F) {n i : ℕ} (hi : i < n) :
    (eqWeightTable τ₁ n).getD i 0
      = if h : i < 2 ^ m₁ then
          (∏ j : Fin m₁, if (finFunctionFinEquiv.symm ⟨i, h⟩) j = 1 then τ₁ j else 1 - τ₁ j)
        else 0 := by
  rw [eqWeightTable, foldl_push_getD _ n _ hi]
  by_cases hb : i < 2 ^ m₁
  · rw [if_pos ((belowTwoPow_eq_true_iff i m₁).mpr hb), dif_pos hb, bitProd_eq_prod,
      ← Fin.prod_univ_eq_prod_range
        (fun s => if Nat.testBit i s then tauAt τ₁ s else 1 - tauAt τ₁ s) m₁]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hfj : tauAt τ₁ (j : ℕ) = τ₁ j := by
      rw [tauAt, dif_pos j.isLt, Fin.eta]
    rw [hfj]
    exact (if_congr (cube_coord_eq_one_iff i hb j) rfl rfl).symm
  · rw [if_neg (fun hc => hb ((belowTwoPow_eq_true_iff i m₁).mp hc)), dif_neg hb]

/-! ## 3. The public matrix table `M̃_α(i, u)`

`n` rows of `μ + n·δ` columns at `δ = 8`, computed once. Two things are hoisted
out of the `2^m₀`-entry traversal:

* `φ(α) = cEvalAt φF α Φ.φ` -- one `c_eval_at_modulus` for the whole call
  instead of one per digit column per entry;
* the `δ`-entry base-power table `b^e`, which is `alphaPowTable` at
  `φF (b : ZMod q)`, replacing the `Σ_{e<8} e = 28` multiplications
  `gadget::base_pow` costs per row per entry.

Columns `u ≥ μ + n·δ` are **not stored**: `mAlphaTilde` is `0` there
(`mAlphaTilde_eq_zero_of_ge`) and a `getD` past the end of the row returns `0`
already. -/

/-- The `δ`-entry table `[φF b^0, …, φF b^(δ-1)]`, at this crate's base `b = 16`. -/
noncomputable def basePowTable (d : ℕ) : List F :=
  alphaPowTable (phiF ((16 : ℕ) : ZMod q)) d

theorem basePowTable_getD {d e : ℕ} (h : e < d) :
    (basePowTable d).getD e 0 = phiF (((16 : ℕ) : ZMod q) ^ e) := by
  rw [basePowTable, alphaPowTable_getD _ h, map_pow]

/-- One entry of the matrix table, in the specification's three cases, with
`φ(α)` and the base-power table supplied by the caller. -/
noncomputable def mAlphaEntry {n μ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ)
    (α φα : F) (bp : List F) (i u : ℕ) : F :=
  if hu : u < μ then
    (if hi : i < n then InnerOuter.cEvalAt phiF α (rs.M ⟨i, hi⟩ ⟨u, hu⟩).1 else 0)
  else if u < μ + n * 8 ∧ (u - μ) / 8 = i then
    -φα * bp.getD ((u - μ) % 8) 0
  else 0

/-- Row `i` of the matrix table: `μ + n·δ` entries. -/
noncomputable def mAlphaRow {n μ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ)
    (α φα : F) (bp : List F) (i : ℕ) : List F :=
  (List.range (μ + n * 8)).foldl (fun acc u => acc ++ [mAlphaEntry rs α φα bp i u]) []

/-- The whole `n × (μ + n·δ)` public matrix table, with `φ(α)` and `b^e` built
once before the row loop. -/
noncomputable def mAlphaTable {n μ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ) (α : F) :
    List (List F) :=
  let φα : F := InnerOuter.cEvalAt phiF α Φ.φ
  let bp : List F := basePowTable 8
  (List.range n).foldl (fun acc i => acc ++ [mAlphaRow rs α φα bp i]) []

/- Outside the stored columns the specification's matrix is zero; that fact is
   `HachiEquiv.ZeroCheck.mAlphaTilde_eq_zero_of_ge` (`lean/ZeroCheck.lean`).
   It moved there because the spec layer needs it and cannot import this file
   (`Opt.lean` imports `ZeroCheck`, not the other way round); it is used just
   below by `mAlphaTable_getD_eq` and resolves through `open
   HachiEquiv.ZeroCheck`. -/

/-- One entry of the table is the specification's `mAlphaTilde`. -/
theorem mAlphaEntry_eq {n μ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ) (α : F)
    {i : ℕ} (hi : i < n) (u : ℕ) :
    mAlphaEntry rs α (InnerOuter.cEvalAt phiF α Φ.φ) (basePowTable 8) i u
      = InnerOuter.mAlphaTilde Φ phiF 16 rs α ⟨i, hi⟩ u := by
  rw [mAlphaEntry, InnerOuter.mAlphaTilde, rhoDigitCount_eq]
  by_cases hu : u < μ
  · rw [dif_pos hu, dif_pos hu, dif_pos hi]
  · rw [dif_neg hu, dif_neg hu]
    by_cases hd : u < μ + n * 8 ∧ (u - μ) / 8 = i
    · rw [if_pos hd, if_pos hd, basePowTable_getD (Nat.mod_lt _ (by norm_num))]
    · rw [if_neg hd, if_neg hd]

theorem mAlphaRow_length {n μ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ)
    (α φα : F) (bp : List F) (i : ℕ) : (mAlphaRow rs α φα bp i).length = μ + n * 8 :=
  foldl_push_length _ _

theorem mAlphaTable_length {n μ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ) (α : F) :
    (mAlphaTable rs α).length = n :=
  foldl_push_length _ n

/-- The row of the table, for a row index in range. -/
theorem mAlphaTable_getD_row {n μ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ) (α : F)
    {i : ℕ} (hi : i < n) :
    (mAlphaTable rs α).getD i []
      = mAlphaRow rs α (InnerOuter.cEvalAt phiF α Φ.φ) (basePowTable 8) i :=
  foldl_push_getD _ n _ hi

/-- **Stored columns.** Entry `(i, u)` of the table is `mAlphaTilde`. -/
theorem mAlphaTable_getD {n μ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ) (α : F)
    {i u : ℕ} (hi : i < n) (hu : u < μ + n * 8) :
    ((mAlphaTable rs α).getD i []).getD u 0
      = InnerOuter.mAlphaTilde Φ phiF 16 rs α ⟨i, hi⟩ u := by
  rw [mAlphaTable_getD_row rs α hi, mAlphaRow, foldl_push_getD _ _ _ hu, mAlphaEntry_eq rs α hi]

/-- **Absent columns.** A read past the end of a row is `0`, which is what
`mAlphaTilde` is there -- so the table may be `μ + n·δ` wide and nothing else
has to know. -/
theorem mAlphaTable_getD_eq {n μ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ) (α : F)
    {i : ℕ} (hi : i < n) (u : ℕ) :
    ((mAlphaTable rs α).getD i []).getD u 0
      = InnerOuter.mAlphaTilde Φ phiF 16 rs α ⟨i, hi⟩ u := by
  by_cases hu : u < μ + n * 8
  · exact mAlphaTable_getD rs α hi hu
  · rw [mAlphaTable_getD_row rs α hi,
      getD_of_length_le _ _ (by rw [mAlphaRow_length]; omega),
      mAlphaTilde_eq_zero_of_ge rs α ⟨i, hi⟩ (by omega)]

/-! ## 4. The table itself

Three table builds, then one `2^m₀`-step traversal whose body is `n`
multiplications, `n` additions and four lookups. -/

/-- The inner row sum `∑_{i<n} eq̃(τ₁,i) · M̃_α(i,u)`, as an `acc = acc + …`
counter loop. Column `u ≥ μ + n·δ` reads `0` out of the short rows. -/
def apRowSum (eqw : List F) (mt : List (List F)) (n u : ℕ) : F :=
  (List.range n).foldl (fun s i => s + eqw.getD i 0 * (mt.getD i []).getD u 0) 0

/-- **The candidate.** `alpha_public_table` with the three tables hoisted out of
the cube traversal. -/
noncomputable def alpha_public_table.opt {n μ m₁ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ)
    (α : F) (τ₁ : Fin m₁ → F) (m₀ : ℕ) : List F :=
  let pw : List F := alphaPowTable α N
  let eqw : List F := eqWeightTable τ₁ n
  let mt : List (List F) := mAlphaTable rs α
  (List.range (2 ^ m₀)).foldl
    (fun acc idx => acc ++ [pw.getD (idx % N) 0 * apRowSum eqw mt n (idx / N)]) []

theorem alpha_public_table.opt_length {n μ m₁ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ)
    (α : F) (τ₁ : Fin m₁ → F) (m₀ : ℕ) :
    (alpha_public_table.opt rs α τ₁ m₀).length = 2 ^ m₀ :=
  foldl_push_length _ _

/-- **The candidate's lemma.** Entry `idx` of the hoisted table is
`alphaPublicEvals` at the cube point `finFunctionFinEquiv.symm idx`
(`ZeroCheck/Constraints.lean:840`) -- the entrywise shape
`alpha_public_table_spec` consumes (`lean/Sumcheck.lean:2459`).

Unconditional in `m₀`, `n`, `μ` and `m₁`: the `i < 2^m₁` guard is carried, not
assumed, and the absent columns are handled by `mAlphaTable_getD_eq`. -/
theorem alpha_public_table.opt_eq_spec {n μ m₁ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ)
    (α : F) (τ₁ : Fin m₁ → F) (m₀ : ℕ) (idx : ℕ) (h : idx < 2 ^ m₀) :
    (alpha_public_table.opt rs α τ₁ m₀).getD idx 0
      = InnerOuter.alphaPublicEvals Φ m₀ m₁ phiF 16 rs α τ₁
          (finFunctionFinEquiv.symm ⟨idx, h⟩) := by
  have hN : 0 < N := by norm_num
  have hlhs : (alpha_public_table.opt rs α τ₁ m₀).getD idx 0
      = α ^ (idx % N) * ∑ t ∈ Finset.range n,
          (eqWeightTable τ₁ n).getD t 0 *
            ((mAlphaTable rs α).getD t []).getD (idx / N) 0 := by
    rw [alpha_public_table.opt]
    rw [foldl_push_getD _ _ _ h, alphaPowTable_getD α (Nat.mod_lt _ hN), apRowSum,
      foldl_add_range_eq_sum]
  rw [hlhs, InnerOuter.alphaPublicEvals]
  simp only [Equiv.apply_symm_apply, RqBridge.phi_natDegree, InnerOuter.alphaTilde]
  congr 1
  rw [sum_fin_eq_sum_range_dite]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htn : t < n := Finset.mem_range.mp ht
  rw [dif_pos htn, eqWeightTable_getD τ₁ htn, mAlphaTable_getD_eq rs α htn]
  by_cases hb : t < 2 ^ m₁
  · rw [dif_pos hb, dif_pos hb]
  · rw [dif_neg hb, dif_neg hb, zero_mul]

/-! # Candidate E -- `ringswitch::lift_commit` (a wall removal, W3)

Strategy `opt-inplace-buffers`, pass fusion. The frozen translation is
`d_key.mat_vec_mul(&lift_message(w))`: `liftMessage` materializes the
concatenation `z ‖ digits(ρ)` -- 57 384 ring elements, 448 MiB at the pin,
57 344 `Rq::copy` calls -- and `mat_vec_mul` consumes it exactly once. Here each
output row is accumulated in place, first over the `μ` columns of `z`, then over
the `n·δ` digit columns, so the concatenation never exists: the column analogue
of ArkLib's `matVecMul_append_rows`, by `Fin.sum_univ_add` and
`Fin.append_left`/`_right`. Operation count unchanged (`dRows · (μ + n·δ)`
products and adds); peak memory inside `lift_commit` ≈ 1.3 GiB → ≈ 896 MiB at
the pin. Accepted under `perf-loop`'s `accepted-wall` clause, not as a speedup.
The lemma is kept symbolic in the digit base `b`: stating it at the literal
width `μ + n * 8` makes `whnf` re-run `rhoDigitCount q 16 = 8` per unification
and time out; `rhoDigitCount_eq` bridges at the triple, as the hachi specs do. -/

/-! ## 0. The accumulate-fold shape

Candidate C's `foldl_add_range_eq_sum` is the same statement over `F` and over
`List.range`; the two lemmas here are its `Fin`-indexed sibling, because this
candidate's loops index a `PolyMatrix`/`PolyVec` and so need the bound at every
read. The `Fin` index is `lean-to-rust`'s `usize` + structural bound row, i.e.
the Rust is a plain `while j < mu` counter loop with `d_key.row(i).get(j)`
re-establishing `j < len`.

`foldl_add_eq_sum` is stated with an *arbitrary* initial accumulator, which is
what lets the digit loop start from the value the `z` loop left behind -- the
whole point of accumulating in place rather than adding two totals. -/

/-- An `acc = acc + g x` fold over any list is the initial accumulator plus the
sum of the images. -/
theorem foldl_add_eq_sum {β : Type*} {M : Type*} [AddCommMonoid M] (g : β → M) :
    ∀ (l : List β) (a : M), l.foldl (fun s x => s + g x) a = a + (l.map g).sum := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons x t ih =>
      intro a
      rw [List.foldl_cons, ih]
      simp [add_assoc]

/-- The `Fin`-indexed accumulate-fold from zero is `Finset.univ`'s sum. -/
theorem foldl_add_finRange_eq_sum {M : Type*} [AddCommMonoid M] (k : ℕ) (g : Fin k → M) :
    (List.finRange k).foldl (fun s j => s + g j) (0 : M) = ∑ j : Fin k, g j := by
  rw [foldl_add_eq_sum g, zero_add, ← Fin.sum_univ_def]

/-! ## 1. The fused row

Two loops over one accumulator. The first walks `j < μ` and reads `z j`; the
second walks `j < n·δ` and reads digit `j`, continuing from the accumulator the
first left. Column `j` of the second loop is `Fin.natAdd μ j`, i.e. the flat
column `μ + j` of `D` -- exactly the index the materialized concatenation used
to be read at, which is why no `Fin.append` survives in the definition.

The digit width is left as `InnerOuter.rhoDigitCount q b` rather than the
literal `8`: it is `Nat.clog b q` (`RhoDigits.lean:66`), which the brief records
as not translatable, and `HachiEquiv.RingSwitch.rhoDigitCount_eq` is where the
crate's `RHO_DIGIT_COUNT = 8` literal is already tied to it. Keeping the width
symbolic makes every lemma below unconditional in `b`, and the crate
instantiation is the application at `b = 16` (§ 3). -/

variable {dRows μ n b : ℕ}

/-- The first fused loop: `acc := 0`, then `μ` ascending steps
`acc := acc + D i (castAdd _ j) * z j`. Translation: the `z` block of the old
`mat_vec_mul` row, reading `d_key` at its own flat column `j`. -/
def lift_commit.rowZLoop
    (D : Simple.PublicParams Φ dRows (μ + n * InnerOuter.rhoDigitCount q b))
    (sw : InnerOuter.LiftedWitness Φ μ n) (i : Fin dRows) : Rq Φ :=
  (List.finRange μ).foldl
    (fun s j => s + D i (Fin.castAdd (n * InnerOuter.rhoDigitCount q b) j) * sw.z j) 0

/-- The second fused loop: `n·δ` ascending steps
`acc := acc + D i (natAdd μ j) * rhoDigitAsRq Φ b ρ j`, starting from the
accumulator `rowZLoop` left. No concatenation is materialized: digit `j` is
produced, multiplied and dropped. -/
def lift_commit.rowDigLoop
    (D : Simple.PublicParams Φ dRows (μ + n * InnerOuter.rhoDigitCount q b))
    (sw : InnerOuter.LiftedWitness Φ μ n) (i : Fin dRows) : Rq Φ :=
  (List.finRange (n * InnerOuter.rhoDigitCount q b)).foldl
    (fun s j => s + D i (Fin.natAdd μ j) * InnerOuter.rhoDigitAsRq Φ b sw.ρ j)
    (lift_commit.rowZLoop D sw i)

/-- Row `i` of the fused lift commitment: the two loops above over one
accumulator. -/
def liftCommitRow (D : Simple.PublicParams Φ dRows (μ + n * InnerOuter.rhoDigitCount q b))
    (sw : InnerOuter.LiftedWitness Φ μ n) (i : Fin dRows) : Rq Φ :=
  lift_commit.rowDigLoop D sw i

/-- **The candidate.** `lift_commit` with `lift_message` fused away: the output
is `dRows` entries, each one fused row. The Rust builds them into a
`Vec::with_capacity(rows)` by `push`, so the `Fin dRows → Rq Φ` shape here is the
`toVec` image of that vector (`hachi/lean/Scheme.lean:63`), the same shape
`mat_vec_mul_spec`'s conclusion already has. -/
def lift_commit.opt (D : Simple.PublicParams Φ dRows (μ + n * InnerOuter.rhoDigitCount q b))
    (sw : InnerOuter.LiftedWitness Φ μ n) : PolyVec (Rq Φ) dRows :=
  fun i => liftCommitRow D sw i

/-! ## 2. The two loop invariants, then the column split

`rowZLoop` and `rowDigLoop` each become a `Finset.sum` by § 0. The
specification side is `dot (D i) (Fin.append z digits)`, which `dot_eq_sum`
(`Vectors.lean:118`) turns into `∑ j : Fin (μ + n·δ)` and `Fin.sum_univ_add`
splits at the cut; `Fin.append_left`/`Fin.append_right` then collapse the two
halves. This is the *column* analogue of ArkLib's row-direction
`matVecMul_append_rows` (`Vectors.lean:342`), which is not at the pin. -/

/-- The `z` loop computes the `z` half of the row. -/
theorem lift_commit.rowZLoop_eq
    (D : Simple.PublicParams Φ dRows (μ + n * InnerOuter.rhoDigitCount q b))
    (sw : InnerOuter.LiftedWitness Φ μ n) (i : Fin dRows) :
    lift_commit.rowZLoop D sw i
      = ∑ j : Fin μ, D i (Fin.castAdd (n * InnerOuter.rhoDigitCount q b) j) * sw.z j :=
  foldl_add_finRange_eq_sum _ _

/-- The fused row is the sum of the two halves -- the in-place accumulator is
accounted for by `foldl_add_eq_sum`'s arbitrary initial value. -/
theorem lift_commit.rowDigLoop_eq
    (D : Simple.PublicParams Φ dRows (μ + n * InnerOuter.rhoDigitCount q b))
    (sw : InnerOuter.LiftedWitness Φ μ n) (i : Fin dRows) :
    lift_commit.rowDigLoop D sw i
      = (∑ j : Fin μ, D i (Fin.castAdd (n * InnerOuter.rhoDigitCount q b) j) * sw.z j)
        + ∑ j : Fin (n * InnerOuter.rhoDigitCount q b),
            D i (Fin.natAdd μ j) * InnerOuter.rhoDigitAsRq Φ b sw.ρ j := by
  rw [lift_commit.rowDigLoop, foldl_add_eq_sum, lift_commit.rowZLoop_eq, ← Fin.sum_univ_def]

-- ArkLib's row-direction `matVecMul_append_rows` needs
-- `set_option backward.isDefEq.respectTransparency false` for its `Fin.append_left`
-- `rw`s (`Vectors.lean:340`). The column analogue below does not: the rewrites go
-- through `simp only`, whose default reducibility sees through the `abbrev`s
-- `PolyMatrix`/`PolyVec`. Checked by removing the guard, not assumed.
/-- **The candidate's lemma.** The fused row loops compute the concrete Ajtai
lift commitment, with no concatenation in sight.

Unconditional: no hypothesis on `dRows`, `μ`, `n`, the digit base `b` or the
shortness bound, and nothing about `sw` beyond its type. `bound` does not occur
in `hachiLiftCom`'s `com` field at all -- it only names the `liftShort`
predicate the `LiftCom` bundles -- so the equation holds for every `bound`. -/
theorem lift_commit.opt_eq_spec (bound : ℕ)
    (D : Simple.PublicParams Φ dRows (μ + n * InnerOuter.rhoDigitCount q b))
    (sw : InnerOuter.LiftedWitness Φ μ n) :
    lift_commit.opt D sw = (InnerOuter.hachiLiftCom Φ bound b D).com sw := by
  funext i
  show lift_commit.rowDigLoop D sw i
    = ArkLib.Lattices.dot (D i) (InnerOuter.liftMessage Φ b sw)
  rw [lift_commit.rowDigLoop_eq, ArkLib.Lattices.dot_eq_sum, InnerOuter.liftMessage,
    Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-! ## 3. The crate's instantiation

`hachi::ringswitch::lift_commit` is called at `(bound, bDig) = (15, 16)`, which
is the pair `hachi/lean/RingSwitch.lean:353`'s `lift_commit_spec` states, and at
`b = 16` the digit count is the crate's `8` (`rhoDigitCount_eq`,
`hachi/lean/RingSwitch.lean:48`). -/

/-- The candidate at the crate's `(15, 16)`: the form the eventual Aeneas triple
for the fused Rust routes through, replacing `lift_commit_spec`'s current
`lift_message_spec` + `mat_vec_mul_spec` composition. -/
theorem lift_commit.opt_eq_spec_hachi
    (D : Simple.PublicParams Φ dRows (μ + n * InnerOuter.rhoDigitCount q 16))
    (sw : InnerOuter.LiftedWitness Φ μ n) :
    lift_commit.opt D sw = (InnerOuter.hachiLiftCom Φ 15 16 D).com sw :=
  lift_commit.opt_eq_spec 15 D sw

/-! ### Why there is no literal-`8` restatement here

`lift_message_spec` and `lift_commit_spec` (`hachi/lean/RingSwitch.lean:311, 353`)
are stated at the *literal* width `μ + n * 8`, and that elaborates: the unifier
whnfs `InnerOuter.rhoDigitCount q 16 = Nat.clog 16 4294967197` down to `8`
(`rhoDigitCount q 16 = 8` is even `rfl`, at a raised heartbeat budget). But a
term-mode restatement of `opt_eq_spec` whose *binders* are written at `μ + n * 8`
re-runs that `whnf` once per unification subproblem and does **not** terminate
inside 1 000 000 heartbeats -- see NOTE.md § "What did not work". The width
literal therefore stays where the audited specs already put it, at the Aeneas
triple, and this file's lemmas stay symbolic in `b`; `rhoDigitCount_eq`
(`hachi/lean/RingSwitch.lean:48`) is the bridge, exactly as it is today. -/


/-! ## 4. Axiom audit (the `Check.lean` § 4 lines this candidate owns) -/

/-! # Candidate F -- `zerocheck::range_product` (brief 5's S5)

Strategy `opt-algo-swap`. `rangeProduct b v = v · ∏_{j=1}^{b-1} (v − j)(v + j)`
costs the frozen translation two extension multiplications and one addition
per factor. With `(v − j)(v + j) = v² − j²` the square `v²` is computed once
and each factor is one multiplication by `v² − j²`, the `j²` a base-field
literal: `1 + (b − 1) = 16` multiplications instead of `2(b − 1) = 30` at
`b = 16`, and no additions. The range factor is ~90% of a sumcheck round's
multiplications (brief 5, re-based 2026-09-14), so this is the prover's
largest single lever. Unconditional in `b` (both index sets are empty at
`b = 0`). Candidate B's table builders take `rangeProduct 16` as a function, so
the two compose. -/

/-! # Candidate F -- `zerocheck::range_product`

Strategy `opt-algo-swap`, "different algorithm / fewer field operations"
(brief `briefs/target-5-sumcheck.md` § Strategy candidates, **S5**, rank 1).

The frozen translation (`hachi/src/zerocheck.rs:100-112`) walks the
specification's factorisation literally: for each `1 ≤ j < b` it forms
`v - j` and `v + j` and folds **both** into the accumulator, so the call costs
`2(b - 1) = 30` extension multiplications at `GADGET_BASE = 16` (the chain has
`1 + 2(b-1) = 31` factors, hence 30 products -- brief § "The range factor is 30
multiplications, not 31"). Since `(v - j)(v + j) = v² - j²` in any commutative
ring, one squaring of `v` plus one multiplication per `j` suffices:
`1 + (b - 1) = 16` multiplications, a 1.72× cut on the count.

The square `j²` is a **natural-number** product, cast once: `(j * j : ℕ)`
embeds through `Ext4::from_base(Fp::new(j * j))`, so it costs no extension
multiplication -- the reason the step below is written
`acc * (v2 - ((j * j : ℕ) : F))` and not `acc * (v2 - (j : F) * (j : F))`.

The brief's accept-rule note carries over verbatim: `zerocheck/range_product/16`
measures 469 ns, inside the 100 ns - 2 µs band that `perf-loop`'s band rule
gives no verdict, so the evidence rows are the callers (§ NOTE.md). -/

/-! ## 1. The loop

One `while j < b` with a running accumulator, in the shape `lean-to-rust`
translates 1:1 and the shape `range_product_loop_spec`
(`hachi/lean/ZeroCheck.lean:362`) already reasons about: `if _h : j < b then …`
with `termination_by b - j`, exactly like `blockLoop`/`rowLoop` above. `v2` is
threaded as an argument rather than recomputed, so the squaring happens once per
call and not once per step. -/

/-- The loop of `range_product.opt`: ascending `j`, one multiplication per step
by `v² - j²`, with `j²` formed in `ℕ`. -/
def range_product.optLoop (b : ℕ) (v2 : F) (acc : F) (j : ℕ) : F :=
  if _h : j < b then
    range_product.optLoop b v2 (acc * (v2 - ((j * j : ℕ) : F))) (j + 1)
  else acc
termination_by b - j
decreasing_by omega

/-- **The candidate.** `P_b(v)` with the two symmetric factors contracted:
`let v2 := v * v` once, then `b - 1` multiplications instead of `2(b - 1)`.
`acc` starts at `v`, the leading factor of `rangeProduct`. -/
def range_product.opt (b : ℕ) (v : F) : F :=
  let v2 := v * v
  range_product.optLoop b v2 v 1

/-! ## 2. The loop invariant

Induction on an upper bound `k` of the termination measure `b - j` -- the shape
an Aeneas `loop.spec_decr_nat` proof takes on the Rust side, so this is also the
skeleton `range_product_loop_spec` will be restated with. Stated for an
arbitrary entry accumulator and an arbitrary `j`, hence usable at `j = 1`
without a case split on `b`. -/

/-- After the loop, `acc` has been multiplied by `v² - k²` for every
`k ∈ [j, b)`. -/
theorem range_product.optLoop_eq (b : ℕ) (v2 : F) (k : ℕ) :
    ∀ (j : ℕ) (acc : F), b - j ≤ k →
      range_product.optLoop b v2 acc j
        = acc * ∏ l ∈ Finset.Ico j b, (v2 - ((l * l : ℕ) : F)) := by
  induction k with
  | zero =>
    intro j acc hk
    rw [range_product.optLoop, dif_neg (by omega),
      Finset.Ico_eq_empty (by omega), Finset.prod_empty, mul_one]
  | succ k ih =>
    intro j acc hk
    by_cases hgo : j < b
    · rw [range_product.optLoop, dif_pos hgo, ih (j + 1) _ (by omega),
        Finset.prod_eq_prod_Ico_succ_bot hgo]
      ring
    · rw [range_product.optLoop, dif_neg hgo,
        Finset.Ico_eq_empty (by omega), Finset.prod_empty, mul_one]

/-! ## 3. The candidate's lemma

`Finset.Icc 1 (b - 1) = Finset.Ico 1 b` for every `b` (at `b = 0` both sides are
empty -- `Icc 1 0 = ∅` and `Ico 1 0 = ∅` -- so the statement needs no `1 ≤ b`
hypothesis, which matters because `rangeProduct` has none either and the digest
oracle compares the two at whatever `b` the crate is built at). The factorwise
step is `(v - l)(v + l) = v·v - l·l` by `ring`, after `Nat.cast_mul` turns the
single base-field literal `(l * l : ℕ)` back into `(l : F) * (l : F)`. -/

/-- The two index sets of § 3, as `Finset`s over `ℕ`. -/
private theorem Icc_pred_eq_Ico (b : ℕ) : Finset.Icc 1 (b - 1) = Finset.Ico 1 b := by
  cases b with
  | zero => rfl
  | succ m => rw [Nat.add_sub_cancel, Finset.Ico_add_one_right_eq_Icc]

/-- **The candidate's lemma.** The contracted loop computes the specification's
range factor `P_b(v) = v·∏_{j=1}^{b-1} (v - j)(v + j)`
(`rangeProduct`, `ArkLib/Commitments/Functional/Hachi/ZeroCheck/Constraints.lean:96`).

Unconditional in `b` and in `v`: no hypothesis on the base, no invertibility, no
range assumption on `v`. The identity used is `(v - j)(v + j) = v² - j²`, valid
in any commutative ring, so nothing here depends on `F` being a field. -/
theorem range_product.opt_eq_spec (b : ℕ) (v : F) :
    range_product.opt b v = InnerOuter.rangeProduct b v := by
  show range_product.optLoop b (v * v) v 1 = InnerOuter.rangeProduct b v
  rw [range_product.optLoop_eq b (v * v) b 1 v (by omega),
    InnerOuter.rangeProduct, Icc_pred_eq_Ico]
  refine congrArg (fun t => v * t) (Finset.prod_congr rfl ?_)
  intro l _
  rw [Nat.cast_mul]
  ring

/-- The candidate at the crate's gadget base: the form the eventual Aeneas
triple for the contracted Rust routes through, replacing
`range_product_loop_spec`'s `(v - j)·(v + j)` invariant
(`hachi/lean/ZeroCheck.lean:362`). 16 extension multiplications instead of 30. -/
theorem range_product.opt_eq_spec_16 (v : F) :
    range_product.opt 16 v = InnerOuter.rangeProduct 16 v :=
  range_product.opt_eq_spec 16 v

/-! # Candidate G -- `zerocheck::h_zero`, `h_zero_is_zero`: the range factor in the base field

Strategy `opt-algo-swap`. Every entry the table builders feed to the range
factor is `φF` of a base-field coefficient, and `φF` is a ring homomorphism,
so `rangeProduct b (φF x) = φF (rangeProduct_base b x)`: the product is computed
in `ZMod q` (sixteen base-field multiplications, candidate F's `x² − j²` shape)
and embedded once; the zero test needs no embedding at all (`φF` is injective).
Found through candidate F's mixed verdict (NOTES.md § "I5 opens with a mixed
verdict"). Candidate B's loops apply their map after `φF`, so `blockLoopBase` /
`rowLoopBase` take a `ZMod q → F` map applied to the coefficient itself. -/

/-! # Candidate G -- `zerocheck::range_product_base`, `h_zero`, `h_zero_is_zero`

Strategy `opt-algo-swap`, "compute in the base field, embed once" (brief
`briefs/target-4-zero-check.md`; brief 5's S5 is the same factor at the
sumcheck callers).

**Why there is a candidate G at all.** Candidate F contracts
`rangeProduct b v = v · ∏_{j=1}^{b-1} (v - j)(v + j)` to
`v · ∏_{j=1}^{b-1} (v² - j²)`: 16 extension multiplications instead of 30 at
`b = GADGET_BASE = 16`. Applied at the *sumcheck* callers that is the prover's
largest single lever. Applied inside the zero-check table builders it measured
as a **regression**: ledger row `rejected-mixed`, run
`20260914T2014+0200-708424de`, `zerocheck/h_zero/14` 1.05 ms -> 5.75 ms. The
diagnosis in that row is that the frozen body's per-entry `Ext4` chain was
being folded by the compiler on the *zero* coordinates of an embedded base
value, and candidate F's body lost that fold.

The fix is not to tune the extension chain, it is to not be in the extension
field. `h_zero` / `h_zero_is_zero` (`hachi/src/zerocheck.rs:275-335`) call
`range_product(Ext4::from_base(r.coeff(l)))`: the argument is **always**
`φF x` for a base-field `x`, never a general element of `F`. Since
`φF = Ext.ofBaseRingHom …` (`phiF`, `lean/ZeroCheck.lean:88`) is a ring
homomorphism,

  `rangeProduct b (φF x) = φF (rangeProduct_base b x)`,

so the whole product may be computed in `ZMod q` and embedded **once** per
entry: 16 base-field multiplications (`Fp::mul`, one 64-bit multiply plus a
reduction) instead of 16 extension ones (each 16 base multiplies plus the `W`
folding), and for the verdict no embedding at all -- `φF y = 0 ↔ y = 0`,
because a ring homomorphism out of a field is injective.

`range_product.opt` (candidate F) and all of its lemmas stay exactly as they
are: the `Ext4` range factor is still what the sumcheck callers need, where the
argument genuinely is an extension element. This candidate adds a sibling for
the one call site whose argument is an embedding.

## What is new here versus candidate B

Candidate B's `blockLoop` / `rowLoop` take `φ : F → F` and apply it to
`phiF (r.coeff l)` -- the embedding happens *before* the per-entry function, so
they cannot express "map the coefficient itself". This file therefore adds
`blockLoopBase` / `rowLoopBase`, parameterised by `g : ZMod q → F` applied to
`r.coeff l` directly, with the same two counter loops, the same truncating
second guard and the same induction-on-a-bound proofs; and the same for the
`Bool` verdict (`zeroBlockLoopBase` / `zeroRowLoopBase`, whose fold stays
entirely in `ZMod q`). The row hoist itself is unchanged and still routes
through `wTableRow` / `wTableFlat_eq_row` (`lean/ZeroCheck.lean:536`, `:547`).

## Op counts (per table entry, `b = 16`)

| | multiplications | embeddings | field |
|---|---|---|---|
| frozen | 30 | 1 | `Ext4` |
| candidate F | 16 | 1 | `Ext4` |
| candidate G | 16 | 1 | `ZMod q` |
| candidate G, verdict | 16 | 0 | `ZMod q` |

`Ext4::mul` is a degree-4 schoolbook product plus the `W`-reduction, so one
extension multiplication is ~15-16 base multiplications (`Ext.lean:387`'s
`ext_mul_spec` reduction table is the Lean image of exactly that): the
arithmetic goes from ~480 base multiplies per entry to 16.
-/

/-! ## 1. The range factor in the base field

The loop is `range_product.optLoop`'s loop with `F` replaced by `ZMod q`,
**monomorphically**: I did not generalise candidate F's loop to a
`CommRing`-polymorphic helper and instantiate it twice. The reason is the
translation, not the proof -- `lean-to-rust` translates the def it is handed,
and a monomorphic loop over `ZMod q` lands on `while j < base { … }` over `Fp`
with nothing to instantiate, in the same shape `range_product_loop_spec`
(`lean/ZeroCheck.lean:362`) already reasons about. The cost is that the
`Finset.Ico` invariant below is proved twice in this file's history (once at
`F` in candidate F, once here); it is ten lines of `induction k` either way. -/

/-- The loop of `range_product_base.opt`: ascending `j`, one **base-field**
multiplication per step by `x² - j²`, with `j²` formed in `ℕ` (so it is a
single `Fp::new(j * j)` literal and not a field multiplication). -/
def range_product_base.optLoop (b : ℕ) (x2 : ZMod q) (acc : ZMod q) (j : ℕ) : ZMod q :=
  if _h : j < b then
    range_product_base.optLoop b x2 (acc * (x2 - ((j * j : ℕ) : ZMod q))) (j + 1)
  else acc
termination_by b - j
decreasing_by omega

/-- **The candidate.** `P_b(x)` computed entirely in `ZMod q`: `let x2 := x * x`
once, then `b - 1` base-field multiplications. `acc` starts at `x`, the leading
factor of `rangeProduct`. -/
def range_product_base.opt (b : ℕ) (x : ZMod q) : ZMod q :=
  let x2 := x * x
  range_product_base.optLoop b x2 x 1

/-- The loop invariant, by induction on an upper bound `k` of the termination
measure `b - j` -- the shape an Aeneas `loop.spec_decr_nat` proof takes, so this
is also the skeleton the new `range_product_base_loop_spec` will be stated
with. -/
theorem range_product_base.optLoop_eq (b : ℕ) (x2 : ZMod q) (k : ℕ) :
    ∀ (j : ℕ) (acc : ZMod q), b - j ≤ k →
      range_product_base.optLoop b x2 acc j
        = acc * ∏ l ∈ Finset.Ico j b, (x2 - ((l * l : ℕ) : ZMod q)) := by
  induction k with
  | zero =>
    intro j acc hk
    rw [range_product_base.optLoop, dif_neg (by omega),
      Finset.Ico_eq_empty (by omega), Finset.prod_empty, mul_one]
  | succ k ih =>
    intro j acc hk
    by_cases hgo : j < b
    · rw [range_product_base.optLoop, dif_pos hgo, ih (j + 1) _ (by omega),
        Finset.prod_eq_prod_Ico_succ_bot hgo]
      ring
    · rw [range_product_base.optLoop, dif_neg hgo,
        Finset.Ico_eq_empty (by omega), Finset.prod_empty, mul_one]

/-- The two index sets, as in candidate F (at `b = 0` both are empty, so no
`1 ≤ b` hypothesis is needed anywhere below). Candidate F's copy of this is
`private` to `lean/Opt.lean`, hence invisible here; on paste into that file this
declaration is redundant and should be dropped in favour of its
`Icc_pred_eq_Ico`. -/
private theorem Icc_pred_eq_Ico_base (b : ℕ) : Finset.Icc 1 (b - 1) = Finset.Ico 1 b := by
  cases b with
  | zero => rfl
  | succ m => rw [Nat.add_sub_cancel, Finset.Ico_add_one_right_eq_Icc]

/-- **The base-field shape.** The contracted base-field loop computes the
`rangeProduct` expression over `ZMod q`:
`x · ∏_{j=1}^{b-1} (x - j)(x + j)`. Unconditional in `b` and in `x`; the only
identity used is `(x - j)(x + j) = x² - j²`, valid in any commutative ring. -/
theorem range_product_base.opt_eq (b : ℕ) (x : ZMod q) :
    range_product_base.opt b x
      = x * ∏ j ∈ Finset.Icc 1 (b - 1), ((x - (j : ZMod q)) * (x + (j : ZMod q))) := by
  show range_product_base.optLoop b (x * x) x 1 = _
  rw [range_product_base.optLoop_eq b (x * x) b 1 x (by omega), Icc_pred_eq_Ico_base]
  refine congrArg (fun t => x * t) (Finset.prod_congr rfl ?_)
  intro l _
  rw [Nat.cast_mul]
  ring

/-! ## 2. The bridge: `φF` is a ring homomorphism

This is the whole algebraic content of the candidate. `phiF` is a bundled
`RingHom` (`lean/ZeroCheck.lean:88` -- bundled precisely so that `map_*` fires),
so the product, the difference, the sum and the natural-number literals all
commute with it. -/

/-- **The candidate's bridge lemma.** The base-field range factor, embedded, is
the specification's extension range factor at the embedded argument
(`rangeProduct`,
`ArkLib/Commitments/Functional/Hachi/ZeroCheck/Constraints.lean:96`). This is
what licenses computing the factor in `Fp` at every call site whose argument is
an `Ext4::from_base`. -/
theorem phiF_range_product_base (b : ℕ) (x : ZMod q) :
    phiF (range_product_base.opt b x) = InnerOuter.rangeProduct b (phiF x) := by
  rw [range_product_base.opt_eq, InnerOuter.rangeProduct, map_mul, map_prod]
  refine congrArg (fun t => phiF x * t) (Finset.prod_congr rfl ?_)
  intro j _
  rw [map_mul, map_sub, map_add, map_natCast]

/- `phiF_eq_zero_iff` -- `φF` is injective, so it reflects zero -- used to live
here; it moved to `lean/ZeroCheck.lean` (next to `phiF_apply`) when
`range_product_base_spec` needed it, and is visible below through
`open HachiEquiv.ZeroCheck`. -/

/-- The verdict form of the bridge: the base-field factor vanishes exactly when
the specification's extension factor does. -/
theorem range_product_base_eq_zero_iff (b : ℕ) (x : ZMod q) :
    range_product_base.opt b x = 0 ↔ InnerOuter.rangeProduct b (phiF x) = 0 := by
  rw [← phiF_range_product_base, phiF_eq_zero_iff]

/-- Stated for the record: candidates F and G compute the same value, F in the
extension and G in the base field. Nothing below uses this -- it is the
statement that says candidate G is a *placement* change and not a different
algorithm. -/
theorem range_product_base.opt_eq_range_product (b : ℕ) (x : ZMod q) :
    phiF (range_product_base.opt b x) = range_product.opt b (phiF x) := by
  rw [phiF_range_product_base, range_product.opt_eq_spec]

/-! ## 3. The table traversal with a base-field per-entry map

Candidate B's `blockLoop` / `rowLoop` apply `φ : F → F` to
`phiF (r.coeff l)`; the embedding is *inside* the loop and *before* the
per-entry function, so they cannot express "compute on the coefficient". These
are the same two loops with the per-entry map taken as `g : ZMod q → F` applied
to `r.coeff l` -- one Lean loop = one Rust `while`, outer state `(u, base, acc)`,
inner state `(l, acc)`, and the same second guard truncating the last block so
that exactly `2 ^ m₀` entries are emitted for every `m₀`, `μ`, `n`. -/

/-- The flat index of coefficient `l` of row `u`, decoded back (`omega` does not
unfold the `abbrev` `N`). Candidate B's copy is `private`. -/
private theorem div_mod_of_block_base {u l : ℕ} (hl : l < N) :
    (N * u + l) / N = u ∧ (N * u + l) % N = l := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by norm_num : 0 < N),
      Nat.div_eq_of_lt hl, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]

/-- The row stride, for the one place the running base index is identified with
a product. -/
private theorem N_mul_succ_base (u : ℕ) : N * (u + 1) = N * u + N := by ring

/-- Inner loop: push `g (r.coeff l)` for ascending `l`, stopping at the row
width `N` or at the table end `size`, whichever comes first. -/
def blockLoopBase (g : ZMod q → F) (size : ℕ) (r : CPolynomial (ZMod q)) (base : ℕ)
    (l : ℕ) (acc : List F) : List F :=
  if _h : l < N ∧ base + l < size then
    blockLoopBase g size r base (l + 1) (acc ++ [g (r.coeff l)])
  else acc
termination_by N - l
decreasing_by omega

/-- Outer loop: for ascending rows `u` while the row's base index is inside the
table, compute `wTableRow sw u` **once** and push its mapped coefficient
block. -/
def rowLoopBase {μ n : ℕ} (g : ZMod q → F) (size : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n)
    (u : ℕ) (base : ℕ) (acc : List F) : List F :=
  if _h : base < size then
    rowLoopBase g size sw (u + 1) (base + N) (blockLoopBase g size (wTableRow sw u) base 0 acc)
  else acc
termination_by size - base
decreasing_by
  have hN : 0 < N := by norm_num
  omega

/-- Inner-loop invariant: on entry `acc` holds the entries below `base + l`; on
exit it holds the entries below `min (base + N) size`. Same induction as
`blockLoop_spec`. -/
theorem blockLoopBase_spec (g : ZMod q → F) (size : ℕ) (r : CPolynomial (ZMod q)) (base : ℕ)
    (h : ℕ → F) (hg : ∀ l' < N, h (base + l') = g (r.coeff l')) (k : ℕ) :
    ∀ (l : ℕ) (acc : List F), N - l ≤ k → l ≤ N → base + l ≤ size →
      acc.length = base + l → (∀ t < base + l, acc.getD t 0 = h t) →
      (blockLoopBase g size r base l acc).length = min (base + N) size ∧
        ∀ t < min (base + N) size, (blockLoopBase g size r base l acc).getD t 0 = h t := by
  induction k with
  | zero =>
    intro l acc hk hl hbl hlen hval
    rw [blockLoopBase, dif_neg (by omega)]
    exact ⟨by omega, fun t ht => hval t (by omega)⟩
  | succ k ih =>
    intro l acc hk hl hbl hlen hval
    by_cases hgo : l < N ∧ base + l < size
    · rw [blockLoopBase, dif_pos hgo]
      refine ih (l + 1) (acc ++ [g (r.coeff l)]) (by omega) (by omega) (by omega)
        (by rw [List.length_append, hlen]; simp; omega) ?_
      intro t ht
      rcases Nat.lt_or_ge t (base + l) with htlt | htge
      · rw [getD_append_lt _ _ _ (by omega), hval t htlt]
      · have hteq : t = acc.length := by omega
        rw [hteq, getD_append_eq, hlen, hg l hgo.1]
    · rw [blockLoopBase, dif_neg hgo]
      exact ⟨by omega, fun t ht => hval t (by omega)⟩

/-- Outer-loop invariant: on entry `acc` holds the entries below `min base size`;
on exit it is the whole table. `base = N * u` is the running state's own
invariant. Same induction as `rowLoop_spec`. -/
theorem rowLoopBase_spec {μ n : ℕ} (g : ZMod q → F) (size : ℕ)
    (sw : InnerOuter.LiftedWitness Φ μ n) (k : ℕ) :
    ∀ (u base : ℕ) (acc : List F), size - base ≤ k → base = N * u →
      acc.length = min base size →
      (∀ t < min base size,
        acc.getD t 0 = g ((wTableRow sw (t / N)).coeff (t % N))) →
      (rowLoopBase g size sw u base acc).length = size ∧
        ∀ t < size, (rowLoopBase g size sw u base acc).getD t 0 =
          g ((wTableRow sw (t / N)).coeff (t % N)) := by
  induction k with
  | zero =>
    intro u base acc hk hbase hlen hval
    rw [rowLoopBase, dif_neg (by omega)]
    exact ⟨by omega, fun t ht => hval t (by omega)⟩
  | succ k ih =>
    intro u base acc hk hbase hlen hval
    by_cases hgo : base < size
    · rw [rowLoopBase, dif_pos hgo]
      have hN : 0 < N := by norm_num
      have hblock := blockLoopBase_spec g size (wTableRow sw u) base
        (fun t => g ((wTableRow sw (t / N)).coeff (t % N)))
        (by
          intro l' hl'
          obtain ⟨hd, hm⟩ := div_mod_of_block_base (u := u) hl'
          rw [hbase, hd, hm])
        N 0 acc (by omega) (by omega) (by omega) (by omega)
        (by intro t ht; exact hval t (by omega))
      refine ih (u + 1) (base + N) _ (by omega) (by rw [hbase, N_mul_succ_base]) hblock.1 ?_
      intro t ht
      exact hblock.2 t ht
    · rw [rowLoopBase, dif_neg hgo]
      exact ⟨by omega, fun t ht => hval t (by omega)⟩

/-- The traversal has the length the specification's `Vector` has. -/
theorem rowLoopBase_length {μ n : ℕ} (g : ZMod q → F) (m₀ : ℕ)
    (sw : InnerOuter.LiftedWitness Φ μ n) :
    (rowLoopBase g (2 ^ m₀) sw 0 0 []).length = 2 ^ m₀ :=
  (rowLoopBase_spec g (2 ^ m₀) sw (2 ^ m₀) 0 0 [] (Nat.sub_le _ _) (by simp) (by simp)
    (by intro t ht; exact absurd ht (by omega))).1

/-- Entrywise value of the traversal: the per-entry map applied to coefficient
`t % N` of row `t / N`. Unlike `rowLoop_getD` this cannot be phrased through
`wTableFlat` (which already contains the embedding) -- `wTableFlat_eq_row` is
applied at the call site instead, once `g` has been fixed. -/
theorem rowLoopBase_getD {μ n : ℕ} (g : ZMod q → F) (m₀ : ℕ)
    (sw : InnerOuter.LiftedWitness Φ μ n) (t : ℕ) (ht : t < 2 ^ m₀) :
    (rowLoopBase g (2 ^ m₀) sw 0 0 []).getD t 0
      = g ((wTableRow sw (t / N)).coeff (t % N)) :=
  (rowLoopBase_spec g (2 ^ m₀) sw (2 ^ m₀) 0 0 [] (Nat.sub_le _ _) (by simp) (by simp)
    (by intro t ht; exact absurd ht (by omega))).2 t ht

/-! ## 4. `h_zero`, computed in the base field and embedded once -/

/-- **The candidate.** The range-constraint block `H₀` in Lagrange form
(spec: `hZero`, `Constraints.lean:204`), with the range factor computed in
`ZMod q` and embedded once per entry:
`Ext4::from_base(range_product_base(r.coeff(l)))`. -/
def h_zero.opt2 {μ n : ℕ} (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n) : List F :=
  rowLoopBase (fun c => phiF (range_product_base.opt 16 c)) (2 ^ m₀) sw 0 0 []

theorem h_zero.opt2_length {μ n : ℕ} (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n) :
    (h_zero.opt2 m₀ sw).length = 2 ^ m₀ :=
  rowLoopBase_length _ m₀ sw

/-- Entry `t`, still in the "embed the base-field factor" form. -/
theorem h_zero.opt2_getD {μ n : ℕ} (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n)
    (t : ℕ) (ht : t < 2 ^ m₀) :
    (h_zero.opt2 m₀ sw).getD t 0
      = phiF (range_product_base.opt 16 ((wTableRow sw (t / N)).coeff (t % N))) :=
  rowLoopBase_getD _ m₀ sw t ht

/-- **The candidate's lemma.** Entry `t` of the base-field-computed table is
entry `t` of `hZero` (`Constraints.lean:204`), entrywise at every `t < 2 ^ m₀` --
the shape `h_zero_spec`'s conclusion consumes (`lean/ZeroCheck.lean:775`). The
route is: the row hoist (`wTableFlat_eq_row`) composed with the bridge
(`phiF_range_product_base`). -/
theorem h_zero.opt2_eq_spec {μ n : ℕ} (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n)
    (t : ℕ) (h : t < 2 ^ m₀) :
    (h_zero.opt2 m₀ sw).getD t 0 = (InnerOuter.hZero Φ m₀ phiF 16 sw).get ⟨t, h⟩ := by
  rw [h_zero.opt2_getD m₀ sw t h, phiF_range_product_base, ← wTableFlat_eq_row sw t h,
    InnerOuter.hZero, Vector.get_ofFn, wTableFlat, dif_pos h]

/-! ## 5. The verdict, with no embedding at all

Same traversal, `Bool` state, and the test performed in `ZMod q`:
`zero && (range_product_base(coeff) == 0)`, running to the end rather than
returning early -- the shape `h_zero_is_zero_loop_spec` mirrors
(`lean/ZeroCheck.lean:1038`). `ZMod q` has `DecidableEq`, which is the Lean side
of `Fp::is_zero` (`fp_is_zero_spec`, `lean/Ext.lean:212`). The soundness of
dropping the embedding is `phiF_eq_zero_iff`. -/

/-- Inner loop of the verdict, folding entirely in the base field. -/
def zeroBlockLoopBase (size : ℕ) (r : CPolynomial (ZMod q)) (base : ℕ)
    (l : ℕ) (zero : Bool) : Bool :=
  if _h : l < N ∧ base + l < size then
    zeroBlockLoopBase size r base (l + 1)
      (zero && decide (range_product_base.opt 16 (r.coeff l) = 0))
  else zero
termination_by N - l
decreasing_by omega

/-- Outer loop of the verdict: one `wTableRow` per row. -/
def zeroRowLoopBase {μ n : ℕ} (size : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n)
    (u : ℕ) (base : ℕ) (zero : Bool) : Bool :=
  if _h : base < size then
    zeroRowLoopBase size sw (u + 1) (base + N)
      (zeroBlockLoopBase size (wTableRow sw u) base 0 zero)
  else zero
termination_by size - base
decreasing_by
  have hN : 0 < N := by norm_num
  omega

/-- **The candidate.** Is every entry of `H₀` zero? Decided without ever
building an `Ext4`. -/
def h_zero_is_zero.opt2 {μ n : ℕ} (m₀ : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n) : Bool :=
  zeroRowLoopBase (2 ^ m₀) sw 0 0 true

theorem zeroBlockLoopBase_spec (size : ℕ) (r : CPolynomial (ZMod q)) (base : ℕ)
    (P : ℕ → Prop)
    (hg : ∀ l' < N, (range_product_base.opt 16 (r.coeff l') = 0) ↔ P (base + l'))
    (k : ℕ) :
    ∀ (l : ℕ) (zero : Bool), N - l ≤ k → l ≤ N → base + l ≤ size →
      (zero = true ↔ ∀ t < base + l, P t) →
      (zeroBlockLoopBase size r base l zero = true ↔ ∀ t < min (base + N) size, P t) := by
  induction k with
  | zero =>
    intro l zero hk hl hbl hz
    rw [zeroBlockLoopBase, dif_neg (by omega), hz]
    exact ⟨fun h t ht => h t (by omega), fun h t ht => h t (by omega)⟩
  | succ k ih =>
    intro l zero hk hl hbl hz
    by_cases hgo : l < N ∧ base + l < size
    · rw [zeroBlockLoopBase, dif_pos hgo]
      refine ih (l + 1) _ (by omega) (by omega) (by omega) ?_
      rw [Bool.and_eq_true, decide_eq_true_iff, hz]
      constructor
      · rintro ⟨hall, hlast⟩ t ht
        rcases Nat.lt_or_ge t (base + l) with htlt | htge
        · exact hall t htlt
        · have hteq : t = base + l := by omega
          rw [hteq]
          exact (hg l hgo.1).mp hlast
      · intro h
        exact ⟨fun t ht => h t (by omega), (hg l hgo.1).mpr (h (base + l) (by omega))⟩
    · rw [zeroBlockLoopBase, dif_neg hgo, hz]
      exact ⟨fun h t ht => h t (by omega), fun h t ht => h t (by omega)⟩

theorem zeroRowLoopBase_spec {μ n : ℕ} (size : ℕ) (sw : InnerOuter.LiftedWitness Φ μ n)
    (k : ℕ) :
    ∀ (u base : ℕ) (zero : Bool), size - base ≤ k → base = N * u →
      (zero = true ↔ ∀ t < min base size,
        range_product_base.opt 16 ((wTableRow sw (t / N)).coeff (t % N)) = 0) →
      (zeroRowLoopBase size sw u base zero = true ↔ ∀ t < size,
        range_product_base.opt 16 ((wTableRow sw (t / N)).coeff (t % N)) = 0) := by
  induction k with
  | zero =>
    intro u base zero hk hbase hz
    rw [zeroRowLoopBase, dif_neg (by omega), hz]
    exact ⟨fun h t ht => h t (by omega), fun h t ht => h t (by omega)⟩
  | succ k ih =>
    intro u base zero hk hbase hz
    by_cases hgo : base < size
    · rw [zeroRowLoopBase, dif_pos hgo]
      have hN : 0 < N := by norm_num
      have hblock := zeroBlockLoopBase_spec size (wTableRow sw u) base
        (fun t => range_product_base.opt 16 ((wTableRow sw (t / N)).coeff (t % N)) = 0)
        (by
          intro l' hl'
          obtain ⟨hd, hm⟩ := div_mod_of_block_base (u := u) hl'
          rw [hbase, hd, hm])
        N 0 zero (by omega) (by omega) (by omega)
        (by rw [hz]
            exact ⟨fun h t ht => h t (by omega), fun h t ht => h t (by omega)⟩)
      refine ih (u + 1) (base + N) _ (by omega) (by rw [hbase, N_mul_succ_base]) ?_
      rw [hblock]
    · rw [zeroRowLoopBase, dif_neg hgo, hz]
      exact ⟨fun h t ht => h t (by omega), fun h t ht => h t (by omega)⟩

/-- **The candidate's lemma.** The base-field branchless fold decides
`hZero = 0`, in the statement shape of `h_zero_is_zero_spec`
(`lean/ZeroCheck.lean:1038`) -- an `↔`, so the rejection path is covered too.
The extra step over candidate B's proof is `range_product_base_eq_zero_iff`,
which is where the embedding is dropped. -/
theorem h_zero_is_zero.opt2_eq_spec {μ n : ℕ} (m₀ : ℕ)
    (sw : InnerOuter.LiftedWitness Φ μ n) :
    h_zero_is_zero.opt2 m₀ sw = true ↔ InnerOuter.hZero Φ m₀ phiF 16 sw = 0 := by
  rw [h_zero_is_zero.opt2,
    zeroRowLoopBase_spec (2 ^ m₀) sw (2 ^ m₀) 0 0 true (Nat.sub_le _ _) (by simp)
      (by exact ⟨fun _ t ht => absurd ht (by omega), fun _ => rfl⟩),
    InnerOuter.hZero_eq_zero_iff,
    forall_cube_iff_forall_flat
      (fun x => InnerOuter.rangeProduct 16 (InnerOuter.wTable Φ m₀ phiF 16 sw x) = 0)]
  constructor
  · intro h t ht
    rw [wTable_symm_eq_row sw t ht, ← range_product_base_eq_zero_iff]
    exact h t ht
  · intro h t ht
    rw [range_product_base_eq_zero_iff, ← wTable_symm_eq_row sw t ht]
    exact h t ht

/-! # Candidate I -- round 0 of the sumcheck in the base field (brief 5's S7')

Strategy `opt-word-arith`. At round 0 every entry of the folded table `w~` is
`φF` of a `ZMod q` coefficient (`ZeroCheck/Constraints.lean:146,148`;
`Ext4::from_base` at `hachi/src/zerocheck.rs`), every interpolation node is an
embedded integer (`round_node i = Ext4::from_base (Fp::new i)`) and
`rangeProduct`'s constants are embedded integers too. So the round-0 zero side
`Σ_y eq[y] · P_b((1 − T)·w[2y] + T·w[2y+1])` performs base-field arithmetic
through the full quartic multiply: 19 `Fp` multiplications where 1 would do,
18 of them multiplying zeros. Only `eq[y]` is a genuine extension element (`τ₀`
is a challenge), and `Fp × Ext4` is four `Fp` multiplications
(`impl Mul<Ext4> for Fp`, `cpoly/src/field.rs:332`).

What follows is the pure algebra that licenses the base-field path: the fold,
the range factor (candidate G's `range_product_base.opt`), the 33 node values,
the first layer fold and the α side, each stated in `ZMod q` / mixed form and
each proved equal to the extension-field expression the existing hachi spec
already concludes. From round 1 on the challenge is a genuine `Ext4` and
nothing here applies. The peeled `honest_round_messages` loop and the
`honestComputeG` bridge are the campaign's, not the candidate's.

Op counts as delivered (per cube point, round 0, zero side): frozen `1 089`
`Ext4` = `20 691` `Fp` multiplications; here `2 + 16` `Fp` per node plus the
`Fp × Ext4` scaling, `726` `Fp` -- S5 and S7' stacked, since the range factor
is candidate G's 16-multiply form. Rounds `1..` unchanged. -/

/-! ## 1. The fold, in the base field

`foldBase` mirrors `fold` (`lean/ZeroCheck.lean:1230`) with `F` replaced by
`ZMod q`, **monomorphically** and in the same operand order -- `(1 − T)·w[2y] +
T·w[2y+1]`, the orientation `evalMleStep` fixes
(`CompPoly/Multilinear/Basic.lean:467`). `lo`/`hi` are shared: they are
index arithmetic and carry no field. -/

/-- One multilinear fold step performed entirely in `ZMod q`: the table's value
at the base-field node `T` in its first free coordinate. Two `Fp`
multiplications per entry against `fold`'s two `Ext4::mul`s. -/
def foldBase {k : ℕ} (wf : Fin (2 ^ (k + 1)) → ZMod q) (T : ZMod q) (y : Fin (2 ^ k)) : ZMod q :=
  (1 - T) * wf (lo y) + T * wf (hi y)

/-- **The fold bridge.** `φF` is a bundled `RingHom` (`phiF`,
`lean/ZeroCheck.lean:88`), so the base-field fold embeds to the extension fold
at the embedded node. This is the whole content of "the fold is base-field
arithmetic at round 0". -/
theorem phiF_foldBase {k : ℕ} (wf : Fin (2 ^ (k + 1)) → ZMod q) (T : ZMod q)
    (y : Fin (2 ^ k)) :
    phiF (foldBase wf T y) = fold (phiF ∘ wf) (phiF T) y := by
  rw [foldBase, fold, map_add, map_mul, map_mul, map_sub, map_one]
  rfl

/-! ## 2. The range summand at one node

The value `round_value_zero` returns, with the range factor computed in
`ZMod q` (candidate G's `range_product_base.opt`, one squaring plus fifteen
base-field multiplications) and **one** `Fp × Ext4` scaling by `eq y` per cube
point: `1056 + 33·4 = 1188` `Fp` multiplications per point against the frozen
path's `1089` `Ext4` multiplications = `20 691` `Fp` ones.

Two shapes are given. `rangeSumZeroBase` is the `∑ y : Fin (2 ^ k)` form, so
that it sits beside `rangeSumZero` (`lean/Sumcheck.lean:706`) and the bridge
lemma is one `Finset.sum_congr`. `rangeSumZeroBase.loop` is the counter loop
with explicit state `acc : F` that `lean-to-rust` lands on a
`while y < half { … }`, and it fixes the two orders the Rust must keep: the
product is `p * eq[y]` (`Fp` on the left, i.e. `Mul<Ext4> for Fp`), and the
accumulation is `acc + …`. -/

/-- **The candidate, round 0's zero side at one node.** `eq y` is the only
extension element in sight. -/
def rangeSumZeroBase {k : ℕ} (wf : Fin (2 ^ (k + 1)) → ZMod q) (eq : Fin (2 ^ k) → F)
    (T : ZMod q) : F :=
  ∑ y : Fin (2 ^ k), phiF (range_product_base.opt 16 (foldBase wf T y)) * eq y

/-- The counter loop the Rust `round_value_zero_base` is: ascending `y`, state
`acc : F`, step `acc + φF (P_b (fold)) * eq[y]` -- product order `p * eq[y]`
(`Fp × Ext4`), accumulator on the left of the `+`. Both tables are read at
natural indices, which is the shape the extracted loop's invariant is about
(cf. `rangeSumZero_eq_sum_range`, `lean/Sumcheck.lean:1726`). -/
def rangeSumZeroBase.loop (wn : ℕ → ZMod q) (eqn : ℕ → F) (T : ZMod q) (half : ℕ) : F :=
  (List.range half).foldl
    (fun acc y =>
      acc + phiF (range_product_base.opt 16 ((1 - T) * wn (2 * y) + T * wn (2 * y + 1)))
        * eqn y)
    0

/-- The loop invariant: after `half` steps the accumulator is the partial sum. -/
theorem rangeSumZeroBase.loop_eq (wn : ℕ → ZMod q) (eqn : ℕ → F) (T : ZMod q) (half : ℕ) :
    rangeSumZeroBase.loop wn eqn T half
      = ∑ y ∈ Finset.range half,
          phiF (range_product_base.opt 16 ((1 - T) * wn (2 * y) + T * wn (2 * y + 1)))
            * eqn y := by
  induction half with
  | zero => simp [rangeSumZeroBase.loop]
  | succ n ih =>
      unfold rangeSumZeroBase.loop at ih ⊢
      rw [List.range_succ, List.foldl_append, ih]
      simp [Finset.sum_range_succ]

/-- The counter loop computes the `Fin`-indexed sum, for any pair of
natural-index readers agreeing with the two tables. -/
theorem rangeSumZeroBase_eq_loop {k : ℕ} (wf : Fin (2 ^ (k + 1)) → ZMod q)
    (eq : Fin (2 ^ k) → F) (T : ZMod q) (wn : ℕ → ZMod q) (eqn : ℕ → F)
    (hw : ∀ y : Fin (2 ^ (k + 1)), wn y.val = wf y)
    (he : ∀ y : Fin (2 ^ k), eqn y.val = eq y) :
    rangeSumZeroBase.loop wn eqn T (2 ^ k) = rangeSumZeroBase wf eq T := by
  rw [rangeSumZeroBase.loop_eq, rangeSumZeroBase,
    ← Fin.sum_univ_eq_sum_range (fun y : ℕ =>
      phiF (range_product_base.opt 16 ((1 - T) * wn (2 * y) + T * wn (2 * y + 1)))
        * eqn y) (2 ^ k)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [he y, foldBase, ← hw (lo y), ← hw (hi y)]
  rfl

/-- **The candidate's lemma.** The base-field node value is the extension-field
node value the existing `round_value_zero_spec` concludes
(`lean/Sumcheck.lean:1765`, conclusion
`toExt out = rangeSumZero (tableFn w) (tableFn eq) (toExt node)`), at
`tableFn w = φF ∘ wf` and `toExt node = φF T`. Two steps: the range-factor
bridge `phiF_range_product_base` (candidate G) and the fold bridge above; the
`mul_comm` is the product-order difference between the Rust's
`p * eq[y]` (`Fp × Ext4`) and `rangeSumZero`'s `eq y * rangeProduct …`. -/
theorem rangeSumZeroBase_eq {k : ℕ} (wf : Fin (2 ^ (k + 1)) → ZMod q)
    (eq : Fin (2 ^ k) → F) (T : ZMod q) :
    rangeSumZeroBase wf eq T = rangeSumZero (phiF ∘ wf) eq (phiF T) := by
  rw [rangeSumZeroBase, rangeSumZero]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [phiF_range_product_base, phiF_foldBase, mul_comm]

/-! ## 3. The `33` node values

`round_values_zero` (`hachi/src/sumcheck.rs:219`) walks `t < ROUND_NODES = 33`
and pushes `round_value_zero(w, eq, round_node t)`. In the base-field path the
node is `Fp::new(t)`, i.e. `(t : ZMod q)`, and the value `round_node t`
represents is `(t : F)` -- which is exactly the node `round_values_zero_spec`
(`lean/Sumcheck.lean:1830`) states its conclusion at. -/

/-- One `push` per node, ascending `t`, `acc ++ [·]`: the shape the extracted
`round_values_zero` loop already has. -/
def roundValuesZeroBase {k : ℕ} (wf : Fin (2 ^ (k + 1)) → ZMod q)
    (eq : Fin (2 ^ k) → F) : List F :=
  (List.range 33).foldl (fun acc t => acc ++ [rangeSumZeroBase wf eq ((t : ℕ) : ZMod q)]) []

/- The push-fold reasoning interface -- `foldl_push_eq_map`,
`foldl_push_length`, `foldl_push_getD` -- is candidate C's, already in
`lean/Opt.lean` § 0 and generic in the element type, so nothing is re-proved
here. -/

theorem roundValuesZeroBase_length {k : ℕ} (wf : Fin (2 ^ (k + 1)) → ZMod q)
    (eq : Fin (2 ^ k) → F) : (roundValuesZeroBase wf eq).length = 33 :=
  foldl_push_length _ 33

/-- Entry `t`, still in base-field form. -/
theorem roundValuesZeroBase_getD {k : ℕ} (wf : Fin (2 ^ (k + 1)) → ZMod q)
    (eq : Fin (2 ^ k) → F) (t : ℕ) (ht : t < 33) :
    (roundValuesZeroBase wf eq).getD t 0 = rangeSumZeroBase wf eq ((t : ℕ) : ZMod q) :=
  foldl_push_getD _ 33 0 ht

/-- The node the base-field path uses is the node the specification uses:
`φF (t : ZMod q) = (t : F)`. `Fp::new(t)` embeds through `Ext4::from_base`, and
`phiF_apply` / `ofBase_natCast` (`lean/ZeroCheck.lean:129`, `:133`) say that
composite is the natural-number cast. -/
theorem phiF_natCast_node (t : ℕ) : phiF ((t : ℕ) : ZMod q) = ((t : ℕ) : F) := by
  rw [phiF_apply, ofBase_natCast]

/-- **The candidate's lemma.** Entry `t` of the base-field node-value list is
the `t`-th node value of `rangeSumZero` -- the statement shape
`round_values_zero_spec`'s conclusion consumes
(`lean/Sumcheck.lean:1830`: `… = rangeSumZero (tableFn w) (tableFn eq) (t.val : F)`). -/
theorem roundValuesZeroBase_eq {k : ℕ} (wf : Fin (2 ^ (k + 1)) → ZMod q)
    (eq : Fin (2 ^ k) → F) (t : ℕ) (ht : t < 33) :
    (roundValuesZeroBase wf eq).getD t 0
      = rangeSumZero (phiF ∘ wf) eq ((t : ℕ) : F) := by
  rw [roundValuesZeroBase_getD wf eq t ht, rangeSumZeroBase_eq, phiF_natCast_node]

/-! ## 4. The first layer fold, out of the base field

Round 0's challenge `a` **is** a genuine extension element, so the table it
produces is an `Ext4` table and rounds 1.. proceed through the existing specs
unchanged. What this def captures is the one mixed layer: the input entries are
base-field, so each output entry is two `Fp × Ext4` scalings (8 `Fp`
multiplications) instead of two `Ext4::mul`s (38).

**The operand order fixed here**, and the Rust must keep it:
`lo * one_minus + hi * x0` -- the `Fp` factor on the **left** of each product,
which is what selects `impl Mul<Ext4> for Fp` (`cpoly/src/field.rs:332`). In
Lean that is `phiF (wf (lo y)) * (1 - a) + phiF (wf (hi y)) * a`; the
`mul_comm`s to `fold`'s `(1 - a) * … + a * …` are inside the lemma below and
nowhere in the code. -/

/-- **The candidate.** `eval_mle_layer_base(values : &Vec<Fp>, x0 : Ext4) ->
Vec<Ext4>`: fold the least-significant variable of a base-field table at an
extension challenge. -/
def evalMleLayerBase {k : ℕ} (wf : Fin (2 ^ (k + 1)) → ZMod q) (a : F) : Fin (2 ^ k) → F :=
  fun y => phiF (wf (lo y)) * (1 - a) + phiF (wf (hi y)) * a

/-- **The candidate's lemma.** The mixed layer fold is the specification's
`fold` on the embedded table -- the conclusion `eval_mle_layer_spec`
(`lean/ZeroCheck.lean:1321`) already delivers, so round 1's table satisfies the
same hypothesis `honest_compute_g_spec` consumes. -/
theorem evalMleLayerBase_eq {k : ℕ} (wf : Fin (2 ^ (k + 1)) → ZMod q) (a : F) :
    evalMleLayerBase wf a = fold (phiF ∘ wf) a := by
  funext y
  rw [evalMleLayerBase, fold, mul_comm (phiF (wf (lo y))), mul_comm (phiF (wf (hi y)))]
  rfl

/-! ## 5. The α side at round 0

`round_poly_alpha` (`hachi/src/sumcheck.rs`, spec `round_poly_alpha_spec`,
`lean/Sumcheck.lean:2426`) folds **both** tables at the node and multiplies. At
round 0 the `w̃` fold is base-field and the `Ã` fold is not (`Ã` carries `α`
and `τ₁`), so the product is again one `Fp × Ext4` scaling: the `Fp` fold of
`w` scaling the `Ext4` fold of `a`. Three `Fp` multiplications per node and
point (two for `foldBase`, four for the scaling) replace five `Ext4` ones.

Order fixed the same way: the `Fp` factor on the left. -/

/-- **The candidate.** Round 0's linear summand at one node, with the `w̃` fold
in `ZMod q`. -/
def linSumAlphaBase {k : ℕ} (wf : Fin (2 ^ (k + 1)) → ZMod q) (a : Fin (2 ^ (k + 1)) → F)
    (T : ZMod q) : F :=
  ∑ y : Fin (2 ^ k), phiF (foldBase wf T y) * fold a (phiF T) y

/-- **The candidate's lemma.** The mixed α summand is `linSumAlpha`
(`lean/Sumcheck.lean:710`) on the embedded table at the embedded node -- what
`round_poly_alpha_spec` concludes. -/
theorem linSumAlphaBase_eq {k : ℕ} (wf : Fin (2 ^ (k + 1)) → ZMod q)
    (a : Fin (2 ^ (k + 1)) → F) (T : ZMod q) :
    linSumAlphaBase wf a T = linSumAlpha (phiF ∘ wf) a (phiF T) := by
  rw [linSumAlphaBase, linSumAlpha]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [phiF_foldBase]

/-! ## 6. Stated for the record: the two sides at round 0 together

Nothing below uses these; they are the statements that say candidate I is a
*placement* change and not a different computation, in the exact form the
campaign will splice into `honest_round_messages_spec`
(`lean/Sumcheck.lean:3856`) when it peels round 0. -/

/-- At round 0 the whole zero side -- node values and all -- agrees with the
extension path entrywise. -/
theorem roundValuesZeroBase_eq_all {k : ℕ} (wf : Fin (2 ^ (k + 1)) → ZMod q)
    (eq : Fin (2 ^ k) → F) :
    (roundValuesZeroBase wf eq).length = 33 ∧
      ∀ t : Fin 33, (roundValuesZeroBase wf eq).getD t.val 0
        = rangeSumZero (phiF ∘ wf) eq ((t.val : ℕ) : F) :=
  ⟨roundValuesZeroBase_length wf eq, fun t => roundValuesZeroBase_eq wf eq t.val t.isLt⟩

/-! # Candidate J -- the tensor split of the public table Ã, verifier half (brief 5's S4) -/
/-!
-- (merged into Opt.lean 2026-09-15; the pure tensor-split lemmas moved down into Sumcheck.lean by the campaign)

# Candidate J -- `sumcheck::final_check`'s `mle[Ã](a)` (brief 5's S4, verifier half)

Strategy `opt-algo-swap`, "different algorithm": the tensor split of the public
table `Ã`.

`final_check` (`hachi/src/sumcheck.rs:877`) evaluates the multilinear extension
of `alphaPublicEvals` at the sumcheck point by **building the whole `2 ^ m₀`
table** (`alpha_public_table`) and taking cpoly's Lagrange dot against a
`2 ^ m₀`-entry basis. At the pin (`m₀ = 26`) that is 12.6 s of table plus
~86 s of dot with a 2 GiB basis, i.e. the 99 s `final_check`
(`NOTES.md` § "The overnight runs").

But `alphaPublicEvals` (`ZeroCheck/Constraints.lean:840`) reads the flat index
`idx = finFunctionFinEquiv x` only through `idx % d` and `idx / d`, with
`d = Φ.φ.natDegree = N = 1024 = 2 ^ 10` at the pin
(`phi_natDegree`, `lean/RqBridge.lean:96`). `finFunctionFinEquiv` is
little-endian (`finFunctionFinEquiv_apply`), so `idx % 2 ^ 10` is the number of
the **low** 10 bits of the cube point and `idx / 2 ^ 10` the number of the high
`m₀ − 10`. Hence `Ã` is a tensor product `L(x_low) · H(x_high)` and its
multilinear extension factorizes:

  `mle[Ã](a) = mle[L](a_low) · mle[H](a_high)`

with `L` the `2 ^ 10 = 1024`-entry power table `α^ℓ` (candidate C's
`alphaPowTable`) and `H` the `2 ^ 16 = 65 536`-entry row-contraction table
`∑ᵢ eq̃(τ₁,i)·M̃_α(i,u)` (candidate C's `eqWeightTable` / `mAlphaTable`). Two
folds of `2 ^ 10 + 2 ^ 16` entries replace a `2 ^ 26` table and a `2 ^ 26`
Lagrange dot.

This section is the candidate's own definition and the two bridges to candidate
C's list builders. The pure algebra of the split -- the cube decomposition, the
tensor-split lemma, the two tables and `alphaSplit_eval_eq` -- lives in
`lean/Sumcheck.lean` § "`alpha_public_mle_eval`: the tensor split of `Ã`",
because the spec layer there needs it and this file **imports** it. The loops
that build the two tables and the two folds are candidate C's and
`eval_mle_layer`'s respectively; the `Reduced`/`toExt` triple is the campaign's.
-/

/-! ## 1. The two tables against candidate C's list builders -/

/-- The low factor is candidate C's `alphaPowTable` read at its natural index --
so the Rust builds it with `alpha_pow_table(alpha, 1 << k)` and nothing new. -/
theorem alphaLowTable_eq_alphaPowTable (α : F) (k : ℕ) (l : Fin (2 ^ k)) :
    alphaLowTable α k l = (alphaPowTable α (2 ^ k)).getD (l : ℕ) 0 :=
  (alphaPowTable_getD α l.isLt).symm

/-- The high factor is candidate C's row sum over the two hoisted tables
(`eqWeightTable`, `mAlphaTable`) -- so the Rust builds it with
`apRowSum eqw mt n u` per column and nothing new. -/
theorem alphaHighTable_eq_apRowSum {n μ m₁ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ)
    (α : F) (τ₁ : Fin m₁ → F) (j : ℕ) (u : Fin (2 ^ j)) :
    alphaHighTable rs α τ₁ j u
      = apRowSum (eqWeightTable τ₁ n) (mAlphaTable rs α) n (u : ℕ) := by
  rw [alphaHighTable, apRowSum, foldl_add_range_eq_sum, sum_fin_eq_sum_range_dite]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htn : t < n := Finset.mem_range.mp ht
  rw [dif_pos htn, eqWeightTable_getD τ₁ htn, mAlphaTable_getD_eq rs α htn]
  by_cases hb : t < 2 ^ m₁
  · rw [dif_pos hb, dif_pos hb]
  · rw [dif_neg hb, dif_neg hb, zero_mul]

/-! ## 2. The candidate

`k = min m₀ 10`: the low block is the `d = 2 ^ 10` coefficient coordinates, or
the whole cube when `m₀ < 10`. At the pin `m₀ = 26`, so `k = 10` and the high
block is `16` coordinates. -/

/-- **The candidate.** `mle[Ã]` at the sumcheck point, as the product of a
`2 ^ 10`-entry fold and a `2 ^ (m₀ − 10)`-entry fold, with no `2 ^ m₀` table
and no `2 ^ m₀` Lagrange dot anywhere. -/
noncomputable def alpha_public_mle_eval.opt {n μ m₁ : ℕ}
    (rs : InnerOuter.RlinStatement Φ n μ) (α : F) (τ₁ : Fin m₁ → F) (m₀ : ℕ)
    (a : Fin m₀ → F) : F :=
  MvPolynomial.eval (splitLowPoint (alphaSplit_le m₀) a)
      (MvPolynomial.MLE' (alphaLowTable α (min m₀ 10)))
    * MvPolynomial.eval (splitHighPoint (alphaSplit_le m₀) a)
      (MvPolynomial.MLE' (alphaHighTable rs α τ₁ (m₀ - min m₀ 10)))

/-! ## 3. The candidate's lemma -/

/-- **The candidate's lemma.** The two-fold product is the specification's
multilinear extension of `alphaPublicEvals` at the point -- the exact value
`alpha_public_mle_eval_spec` (`lean/Sumcheck.lean`) concludes with, which is the
value `final_check` used to reach through `alpha_public_table` and a Lagrange
dot. The argument is `HachiEquiv.Sumcheck.alphaSplit_eval_eq`, stated there over
the same two factors; this is it at the candidate's own definition.

Unconditional in `m₀`, `n`, `μ` and `m₁`: the `i < 2 ^ m₁` guard is carried by
`alphaHighTable` verbatim and the `m₀ < 10` regime is discharged in
`split_mod_div`. -/
theorem alpha_public_mle_eval.opt_eq_spec {n μ m₁ : ℕ}
    (rs : InnerOuter.RlinStatement Φ n μ) (α : F) (τ₁ : Fin m₁ → F) (m₀ : ℕ)
    (a : Fin m₀ → F) :
    alpha_public_mle_eval.opt rs α τ₁ m₀ a
      = (InnerOuter.cMultilinearExtension m₀
          (InnerOuter.alphaPublicEvals Φ m₀ m₁ phiF 16 rs α τ₁)).eval a := by
  rw [alpha_public_mle_eval.opt]
  exact alphaSplit_eval_eq rs α τ₁ m₀ a

/-! ## 4. The shape the campaign's fold specs deliver

`fold_natTable_eq_mle` / `fold_tableFn_eq_mle` (`lean/Sumcheck.lean:3328`,
`:3380`) phrase one fold step as
`fold (tableFn t) x … = (cMultilinearExtension (M+1) evals).eval (hypercubePoint
(M+1) (i+1) (Fin.snoc cs x) z)`, i.e. the iterated fold of a table over a point
lands on `cMultilinearExtension`, not on `MvPolynomial.eval … (MLE' …)`. This
corollary restates the candidate in exactly that spelling, so each factor
splices onto one instance of those lemmas: the low fold at
`evals := alphaLowTable α k ∘ finFunctionFinEquiv` over `M + 1 = k` variables,
the high fold at `evals := alphaHighTable rs α τ₁ (m₀ − k) ∘ finFunctionFinEquiv`
over `M + 1 = m₀ − k`. -/

/-- **The corollary the campaign splices.** Both factors in the fold specs'
own spelling. -/
theorem alpha_public_mle_eval.opt_eq_spec' {n μ m₁ : ℕ}
    (rs : InnerOuter.RlinStatement Φ n μ) (α : F) (τ₁ : Fin m₁ → F) (m₀ : ℕ)
    (a : Fin m₀ → F) :
    (InnerOuter.cMultilinearExtension (min m₀ 10)
          (alphaLowTable α (min m₀ 10) ∘ finFunctionFinEquiv)).eval
        (splitLowPoint (alphaSplit_le m₀) a)
      * (InnerOuter.cMultilinearExtension (m₀ - min m₀ 10)
          (alphaHighTable rs α τ₁ (m₀ - min m₀ 10) ∘ finFunctionFinEquiv)).eval
        (splitHighPoint (alphaSplit_le m₀) a)
      = (InnerOuter.cMultilinearExtension m₀
          (InnerOuter.alphaPublicEvals Φ m₀ m₁ phiF 16 rs α τ₁)).eval a := by
  rw [cMLE_flat_eq_MLE', cMLE_flat_eq_MLE', ← alpha_public_mle_eval.opt_eq_spec rs α τ₁ m₀ a,
    alpha_public_mle_eval.opt]

/-! # Candidate L -- the α table carried as two factors through the rounds (brief 5's S4, prover half; wall W1) -/
/-!
# Candidate L -- the tensor split of the α table, prover half (brief 5's S4)

Strategy `opt-algo-swap`, "different algorithm", judged under `accepted-wall`
(wall W1).

`honest_round_messages` (`hachi/src/sumcheck.rs:1075`) builds the whole `2 ^ m₀`
public table `a_tab` with `alpha_public_table` and folds it once per round with
`eval_mle_layer` (`:1095`, `:1103`). At the pin (`m₀ = 26`) that vector is
`2 ^ 26 · 32 B = 2 GiB` -- wall W1.

Candidate J already showed that the round-0 table is a **tensor product**: at the
flat cube index `idx`, `alphaPublicEvals` (`ZeroCheck/Constraints.lean:840`)
reads only `idx % d` and `idx / d` with `d = Φ.φ.natDegree = 2 ^ 10`
(`phi_natDegree_eq_two_pow`), and `finFunctionFinEquiv` is little-endian, so
`Ã(idx) = L(idx % 2 ^ k) · H(idx / 2 ^ k)` with `k = min m₀ 10`,
`L = alphaLowTable α k` and `H = alphaHighTable rs α τ₁ (m₀ − k)`.

The prover's half of the same observation is that the *layer fold* commutes with
the tensor structure. Folding the least significant coordinate touches only the
low factor while the low factor still has more than one entry, and only the high
factor once it has one:

* `fold (L ⊗ H) a = (fold L) ⊗ H`   while `|L| = 2 ^ (k+1) > 1`;
* `fold (L ⊗ H) a = L ⊗ (fold H a)` when `|L| = 2 ^ 0 = 1`.

So the prover carries `(low, high)` instead of `a_tab` and reads
`a_tab[j] = low[j % low.len()] * high[j / low.len()]`. The Rust it translates to:

```
// tensor read:  a_tab[j] = low[j % L] * high[j / L],   L = low.len() = 2^k (k may be 0)
round_value_alpha_split(w, low, high, node): half = w.len()/2; one_minus = 1 − node;
   for y < half: w_folded = one_minus*w[2y] + node*w[2y+1];
                 lo_a = low[(2y) % L] * high[(2y) / L];  hi_a = low[(2y+1) % L] * high[(2y+1) / L];
                 a_folded = one_minus*lo_a + node*hi_a;  acc = acc + w_folded * a_folded
alpha_split_fold(low, high, a) -> (low', high'):  if 1 < low.len() { (eval_mle_layer(low, a), high) }
                                                  else { (low, eval_mle_layer(high, a)) }
```

`2 ^ m₀ · 32 B = 2 GiB` becomes `(2 ^ 10 + 2 ^ 16) · 32 B = 2.06 MiB`, and the
read is written as the *product of the two entries and then folded* -- never as
`(fold low) * high` -- so `round_value_alpha_split` is literally
`round_value_alpha` on the tensor table and `linSumAlpha_tensor` (now in
`lean/Sumcheck.lean`) is the
only thing the round-value spec needs.

The pure tensor-split algebra of the *verifier* half (`cubeSplit`,
`mle_tensor_split`, `alphaLowTable`, `alphaHighTable`, `alphaSplit_eval_eq`,
`split_mod_div`, `phi_natDegree_eq_two_pow`) lives in `lean/Sumcheck.lean` and is
reused verbatim here.

**And so does this candidate's own algebra now.** `tensorTable`, the two
fold-commutation lemmas, `alphaPublicEvals_eq_tensorTable`, `linSumAlpha_tensor`,
the two split reads, `reidx` / `foldIter` and `foldIter_tensorTable` were moved
verbatim **down into `lean/Sumcheck.lean`** § "The α table as two factors
(candidate L …)" by the verification campaign: `Opt.lean` imports `Sumcheck`, so
the spec layer that consumes them cannot import them from here. Campaign J did
the same with `mle_tensor_split`. What stays below is the candidate's contract --
`honest_round_messages.opt_eq_spec` -- stated over those names, which are in
scope through `open HachiEquiv.Sumcheck` above; `Check.lean` § 4 prints the moved
lemmas under `HachiEquiv.Sumcheck`.
-/



/-! ## 7. The candidate's lemma

The three facts the translated prover needs, in one statement: the round-0 table
is the tensor table, and each round's fold keeps it one -- in the low factor
while the low factor has more than one entry, in the high factor afterwards. -/

/-- **Candidate L's `opt_eq_spec`.** The `(low, high)` pair the champion carries
represents the `2 ^ m₀` public table at round `0` and stays a representation of
it under every layer fold. -/
theorem honest_round_messages.opt_eq_spec {n μ m₁ : ℕ} (rs : InnerOuter.RlinStatement Φ n μ)
    (α : F) (τ₁ : Fin m₁ → F) (m₀ : ℕ) (a : F) :
    (∀ (x : Fin m₀ → Fin 2) (idx : Fin (2 ^ ((m₀ - min m₀ 10) + min m₀ 10))),
        (idx : ℕ) = ((finFunctionFinEquiv x : Fin (2 ^ m₀)) : ℕ) →
        InnerOuter.alphaPublicEvals Φ m₀ m₁ phiF 16 rs α τ₁ x
          = tensorTable (alphaLowTable α (min m₀ 10))
              (alphaHighTable rs α τ₁ (m₀ - min m₀ 10)) idx)
      ∧ (∀ (j k : ℕ) (L : Fin (2 ^ (k + 1)) → F) (H : Fin (2 ^ j) → F),
          fold (tensorTable (j := j) (k := k + 1) L H) a
            = tensorTable (j := j) (k := k) (fold L a) H)
      ∧ (∀ (j : ℕ) (L : Fin (2 ^ 0) → F) (H : Fin (2 ^ (j + 1)) → F),
          fold (tensorTable (j := j + 1) (k := 0) L H) a
            = tensorTable (j := j) (k := 0) L (fold H a)) :=
  ⟨fun x idx hidx => alphaPublicEvals_eq_tensorTable rs α τ₁ m₀ x idx hidx,
    fun _ _ L H => fold_tensorTable_low L H a,
    fun _ L H => fold_tensorTable_scalar L H a⟩

end HachiEquiv.Opt
