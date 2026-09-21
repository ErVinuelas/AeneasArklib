/-
`OptRingSwitch.lean` -- the optimized variant of `ringswitch::lift_commit`
(candidate E, wall W2), with its `opt_eq_spec` lemma.

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


end HachiEquiv.Opt
