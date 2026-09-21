/-
`OptSumcheck.lean` -- the optimized variants of `hachi/src/sumcheck.rs` (the α
table, round 0 in the base field, the tensor split, the two-factor α table),
with their `opt_eq_spec` lemmas.

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

Candidate I's base-field round rests on candidate G's base-field range factor,
which is why this part imports `OptZeroCheck`.
-/
import Sumcheck
import OptZeroCheck

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly CompPoly.Extension CompPoly.Extension.Ext ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.Opt

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme
open HachiEquiv.RingSwitch HachiEquiv.Ext HachiEquiv.ZeroCheck
open HachiEquiv.Sumcheck

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


/-! # Candidate T2c -- `sumcheck::round_values_zero`: the fold's scalars in the base field

Strategy `rust-direct`.  The specification's two-point fold is
`fold w T y = (1 - T)·w(lo y) + T·w(hi y)`, and the crate evaluates it at the
`33` nodes `T = 0 … 32`.  `round_value_zero` takes `T` as an arbitrary `Ext4`
and so must pay two **full** quartic multiplications per pair per node --
nineteen base multiplications apiece.  But `round_values_zero` knows its node is
`Fp::new(t)`, and therefore that `1 - T` is `Fp::ONE - Fp::new(t)`: *both*
scalars are in `ofBase`'s image, so each product is the **mixed**
`Mul<Ext4> for Fp` impl -- four base multiplications (`fp_ext_mul_spec`,
`lean/Ext.lean:403`).  30 of ~257 base multiplications per node per pair.

This is a *representation* change on the scalars, not an algorithmic one: the
sum computed is identical termwise, which is why `round_values_zero_spec`'s
statement did not move and only its proof was restated around the new inner
loop.  The one line of content is below -- `ofBase` is a ring homomorphism, so
subtracting before embedding is subtracting after.

Measured (run `20260916T1708+0200-... run 2`, exit 0, A/B bias 4.0%):
`round_values_zero` **-13.9%**, `round_poly_zero` -13.5%, `honest_compute_g`
-13.1%, `honest_compute_g_split` -13.1%; and `sumcheck/round_value_zero`
**-0.7%, noise** -- that row is the arbitrary-node function, left untouched on
purpose, so it is this candidate's built-in control, exactly as
`zerocheck/h_zero` was T2a's.

Why the fold was inlined into `round_values_zero` rather than
`round_value_zero`'s signature being changed: `benches/*.rs` instantiates one
case body against all three variant crates, and the frozen `hachi-genesis` copy
would stop compiling if a benched item's parameter types moved.  Recorded in
`perf-loop` § "Before the first iteration". -/

/-- Candidate T2c's fold: the scalars formed in `ZMod q` and embedded, rather
than formed in the extension. -/
def round_values_zero.optFold (t : ZMod q) (a b : F) : F :=
  Ext.ofBase (1 - t) * a + Ext.ofBase t * b

/-- **The candidate's lemma.**  The base-field fold *is* the specification's
fold at the embedded node: `φF` is a bundled `RingHom`, so `map_sub` and
`map_one` carry `ofBase (1 - t)` to `1 - ofBase t` and the two expressions are
equal term for term.  Unconditional in `t`, `a` and `b`.

The right-hand side is the body of `fold w (ofBase t) y` with
`a = w (lo y)`, `b = w (hi y)`, so `rangeSumZero` -- and hence every node value,
the interpolated round polynomial, and `honest_compute_g` -- is unchanged. -/
theorem round_values_zero.optFold_eq_spec (t : ZMod q) (a b : F) :
    round_values_zero.optFold t a b = (1 - Ext.ofBase t) * a + Ext.ofBase t * b := by
  rw [round_values_zero.optFold, ← phiF_apply, ← phiF_apply, map_sub, map_one]


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
