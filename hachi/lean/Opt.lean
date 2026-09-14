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

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly CompPoly.Extension CompPoly.Extension.Ext ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.Opt

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme
open HachiEquiv.RingSwitch HachiEquiv.Ext HachiEquiv.ZeroCheck

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

/-! ## § 4 audit lines -/

end HachiEquiv.Opt
