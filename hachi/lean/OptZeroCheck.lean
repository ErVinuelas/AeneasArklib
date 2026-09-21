/-
`OptZeroCheck.lean` -- the optimized variants of `hachi/src/zerocheck.rs` and
the two `ringswitch` evaluations the α side introduced, with their `opt_eq_spec` lemmas.

Every `Foo.opt` here is a pure Lean definition in the shape `lean-to-rust`
translates trivially (one fold = one `while` loop, explicit tuple state,
ascending indices), named after the **Rust item** it replaces, and paired in the
same change with a proved `opt_eq_spec` lemma against the ArkLib definition that
item mirrors. The lemma is stated between pure functions: at candidate time no
Rust exists, so the algebra is settled here and the Aeneas triple over the
extracted model (the outer verification pass) only has to route through it.
`Check.lean` § 4 prints the axioms of every lemma below, which is what makes a
`sorry` here a build failure rather than silent debt (`lean-opt` § "The
opt-contract"). Every part keeps `namespace HachiEquiv.Opt`, so a lemma's
fully qualified name is the same whichever file it lives in; `Opt.lean` imports
all the parts, and `import Opt` still brings the whole layer.

# Stage 6, iteration 1 (zerocheck; brief `briefs/target-4-zero-check.md`)

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
import ZeroCheck
-/
import ZeroCheck
import OptFold

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

/-! # Candidate T2a -- `zerocheck::range_product`: Paterson--Stockmeyer, block 4

Strategy `opt-algo-swap`, on top of candidate F.  F contracted the two symmetric
factors and evaluates `∏_{j=1}^{15} (v² − j²)` one factor at a time: fifteen
*full* extension multiplications, and fifteen `Fp::new` + `Ext4::from_base`
embeddings, per call.  T2a expands that product once and for all into its
sixteen coefficients -- pinned in `params::RANGE_Q_COEFFS`, which is a `const`
table, so the expansion costs nothing at run time -- and then evaluates the
degree-15 polynomial by Paterson--Stockmeyer at block width 4.

The arithmetic: with `y = v²` and `y², y³, y⁴` precomputed (3 multiplications),
four blocks of four coefficients cost 3 Horner multiplications by `y⁴` and 12
**mixed** `Fp × Ext4` multiplications.  A mixed multiply is four base
multiplications (`fp_ext_mul_spec`, `hachi/lean/Ext.lean:403`) where a full
extension multiply is nineteen, so the coefficient work drops from 15 × 19 to
12 × 4 base multiplications -- and the fifteen embeddings become twelve
`Fp::new`s on table words that are already reduced.

Measured (run `20260916T1530+0200-ad543615`): `−43.0 / −42.6 / −43.6 / −44.5 /
−44.0 %` on the five caller rows, `zerocheck/range_product/16` itself `−50.1 %`
(in the 100 ns - 2 µs band, so no verdict of its own -- the callers are the
evidence, per `perf-loop`'s band rule).  `h_zero` / `h_zero_is_zero` moved
`+1.6 %`, i.e. noise: those route through `range_product_base`, which T2a
deliberately does **not** touch (rule 12 -- the `Fp` variant is its own
candidate).  That cross-check is exactly the one candidate F failed
(`rejected-mixed`), and it did not recur.

The table is verified twice over, from both ends and independently:
`params_semantics.rs`'s `range_q_coeffs_are_the_product_form` rebuilds all
sixteen literals in `u128` from `GADGET_BASE`, and `rangeQ_eq_prod`
(`hachi/lean/ZeroCheck.lean`) proves the same claim in Lean.

## The loop

The extracted loop descends `i` from 3 to 0 and is stated generically in the
coefficient sequence, because the *rearrangement* is what this candidate is --
the particular sixteen words belong to `rc` and to `rangeQ_eq_prod`. -/

/-- The loop of `range_product`'s candidate: Horner over blocks of four, `y⁴` per
step, descending. Mirrors the extracted `zerocheck.range_product_loop` argument
for argument. -/
def range_product.optPS (c : ℕ → F) (y y2 y3 y4 : F) (acc : F) (i : ℕ) : F :=
  if _h : 0 < i then
    range_product.optPS c y y2 y3 y4
      (acc * y4 + (c (4 * (i - 1)) + c (4 * (i - 1) + 1) * y
        + c (4 * (i - 1) + 2) * y2 + c (4 * (i - 1) + 3) * y3)) (i - 1)
  else acc
termination_by i
decreasing_by omega

/-- The loop invariant, as induction on an upper bound of the measure -- the
shape `loop.spec_decr_nat` takes on the Rust side, so this is the skeleton
`range_product_loop_spec` (`hachi/lean/ZeroCheck.lean`) is restated with.

The accumulator holds the top `16 − 4·i` coefficients; one step prepends four
more, which is the index shift
`∑_{t<4+M} a_{b+t} y^t = (∑_{t<4} a_{b+t} y^t) + y⁴ · ∑_{t<M} a_{b+4+t} y^t`. -/
theorem range_product.optPS_eq (c : ℕ → F) (y : F) (k : ℕ) :
    ∀ (i : ℕ) (acc : F), i ≤ k → 4 * i ≤ 16 →
      acc = ∑ t ∈ Finset.range (16 - 4 * i), c (4 * i + t) * y ^ t →
      range_product.optPS c y (y ^ 2) (y ^ 3) (y ^ 4) acc i
        = ∑ t ∈ Finset.range 16, c t * y ^ t := by
  induction k with
  | zero =>
    intro i acc hik _ hacc
    have hz : i = 0 := by omega
    rw [range_product.optPS, dif_neg (by omega), hacc, hz]
    norm_num
  | succ m ih =>
    intro i acc hik hi4 hacc
    by_cases hpos : 0 < i
    · rw [range_product.optPS, dif_pos hpos]
      refine ih (i - 1) _ (by omega) (by omega) ?_
      have hshift : 16 - 4 * (i - 1) = 4 + (16 - 4 * i) := by omega
      rw [hshift, Finset.sum_range_add]
      have hsnd : ∑ t ∈ Finset.range (16 - 4 * i),
            c (4 * (i - 1) + (4 + t)) * y ^ (4 + t)
          = (∑ t ∈ Finset.range (16 - 4 * i), c (4 * i + t) * y ^ t) * y ^ 4 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [show 4 * (i - 1) + (4 + t) = 4 * i + t by omega, pow_add]
        ring
      rw [hsnd, ← hacc]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.add_zero]
      ring
    · rw [range_product.optPS, dif_neg hpos, hacc, show i = 0 by omega]
      norm_num

/-- **The candidate's lemma.** The Paterson--Stockmeyer evaluation of the pinned
coefficient table, times the leading `v`, is the specification's range factor.

Two independent halves, composed: `optPS_eq` above is the *rearrangement* (true
for any coefficient sequence, no characteristic used), and
`rangeQ_sq_eq_rangeProduct` (`hachi/lean/ZeroCheck.lean`) is the *table*
(sixteen `decide`s in `ZMod q` plus one `ring`).  A wrong table entry fails the
second and cannot be absorbed by the first. -/
theorem range_product.optPS_eq_spec (v : F) :
    v * range_product.optPS rc (v * v) ((v * v) ^ 2) ((v * v) ^ 3) ((v * v) ^ 4)
        (rc 12 + rc 13 * (v * v) + rc 14 * (v * v) ^ 2 + rc 15 * (v * v) ^ 3) 3
      = InnerOuter.rangeProduct 16 v := by
  have hentry : rc 12 + rc 13 * (v * v) + rc 14 * (v * v) ^ 2 + rc 15 * (v * v) ^ 3
      = ∑ t ∈ Finset.range (16 - 4 * 3), rc (4 * 3 + t) * (v * v) ^ t := by
    simp only [show (4 : ℕ) * 3 = 12 by norm_num, show (16 : ℕ) - 12 = 4 by norm_num,
      Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  rw [range_product.optPS_eq rc (v * v) 3 3 _ (by omega) (by omega) hentry]
  exact rangeQ_sq_eq_rangeProduct v


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


end HachiEquiv.Opt
