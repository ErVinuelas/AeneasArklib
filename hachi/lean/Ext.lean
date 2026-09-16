/-
The extension field `Ext4`, the carrier of the zero-check layer.

**Ported, not re-derived.** The statements and proof skeletons below come from
the `cpoly` crate's own equivalence development (`cpoly/lean/Field.lean`, its
`Ext4` section), which proves the *same extracted code*: hachi's `--include
'cpoly::_'` whitelist and cpoly's own extraction produce `cpoly.field.Ext4` and
its operator impls identically -- verified by diffing the two `Generated.lean`
bodies, which agree instruction for instruction and even in generated variable
names (`t0`, `f`, … `f23`), both under the fully-qualified `cpoly.field.*`
names. So a `step` sequence written there walks the same monadic body here.

Importing them instead was not possible: cpoly's specs are stated about *its*
`Generated` module, and hachi extracts its own copy of the same items, so the
two are distinct declarations that merely share a name. `hachi/lean/Field.lean`
re-derives the `Fp` layer for exactly this reason; this file does the same for
`Ext4`, except that it can bring the proofs along.

**What the port cost.** cpoly is built against CompPoly `c0fcf450`, Mathlib
`81a5d257` and Lean **v4.32.0**; hachi pins CompPoly `a09455a2`, Mathlib
`0df444a3` and Lean **v4.33.1**. The statements cross that gap unchanged --
they are about identical extracted code -- but the proof scripts do not, and
the ones that break do so where `Ext`'s API and Mathlib's automation moved.
Those eight are now discharged: each follows its upstream script, with the
adaptations the version gap forces recorded at the local helpers below and at
the two proofs that needed more than a change of rewrite -- `ext_mul_spec`,
where the reduction table has to be supplied exponent by exponent, and
`ext_is_zero_spec`, whose base-field ingredient (`fp_is_zero_spec`) is not part
of `lean/Field.lean` and is proved here.

Promoted from `lean-wip/` on 2026-09-09 (Aristotle
session `63ebbc60`, eight obligations to zero); its eight headline specs are
audited in `Check.lean` § 4.

`K = Hachi.Field = ZMod Hachi.fieldSize` and hachi's `q` are the same modulus:
`Check.lean` § 2's `cpoly.field.P = params.Q` is what pins that.
-/

import Field
import CompPoly.Fields.Hachi.Ext4
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false
set_option maxRecDepth 8192

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly CompPoly.Extension
open hachi

namespace HachiEquiv.Ext

open HachiEquiv.Field

/-- `q` is prime, which is what makes `ZMod q` a field and hence `Ext4`'s
reference operations well typed. The same instance `lean/RqBridge.lean:72`
supplies, and it needs `Mathlib.Tactic.NormNum.Prime`: ArkLib's imports do not
reach norm_num's primality extension. -/
instance : Fact (Nat.Prime q) := ⟨by norm_num⟩

/-- The base field, as cpoly's development names it. -/
abbrev K := Hachi.Field

/-- The extension field: `CompPoly.Extension.Ext Hachi.ext4Params`, a dense
little-endian coefficient vector of length four. -/
abbrev F := Hachi.Ext4

/-! ## Scope: the operations hachi's model contains

cpoly's development also specifies `Ext4::new`, `clone`, `default`, `eq`,
`from_fp`, `from_u64`, `smul`, `add_assign`, `sub_assign`, `mul_assign`, `neg`
and the `GEN` constant.
**None of those are in hachi's `Generated.lean`**, and that is not a whitelist
gap: `--include 'cpoly::_'` decides which foreign items *may* be translated,
while what lands is what the local crate reaches -- and `--lib` extraction does
not see `benches/`, which is the only place `Ext4::new` is used. Their specs are
dropped rather than stubbed, because a statement about a name that does not
exist is the `autoImplicit` trap in another costume, and this file sets
`autoImplicit false` so that such a statement fails loudly instead. What
remains is exactly what `zerocheck.rs` and `ringswitch.rs` compute with:
`from_base`, `is_zero`, `add`, `sub`, `mul`, `ZERO` and `ONE`. **`W` left the
model in the 2026-09-16 cpoly bump**: the new `Ext4::mul` folds the `Y^4 = 2`
wrap into `add_double_product` rather than multiplying by a `W` constant, and
the only remaining reader of `W` upstream is `mul_by_w`, which this crate does
not reach. `cpoly_W_val`, `red_W` and `toK_W` went with it, and so did
`Check.lean` § 2's `cpoly.field.W = params.EXT_W` pin -- the `2` is now asserted
by `add_double_product_spec` instead. The two
assign forms were here until `final_check` stopped calling
`cpoly::multilinear::eq_tilde`: the `+=`/`*=` operators were reached only from
inside `lagrange_basis` and `dot`, so the champion that routed the kernel
through hachi's own `eq_prefix` took all three out of the model at once, and
`ext_add_assign_spec` and `ext_mul_assign_spec` went with them. See NOTES.md
§ "The model contains what the crate reaches". -/

/-! ## Compatibility with `HachiEquiv.Field` -/

theorem red_Fp_ZERO : Red cpoly.field.Fp.ZERO := by
  unfold Red; rw [cpoly_Fp_ZERO_val]; decide

theorem red_Fp_ONE : Red cpoly.field.Fp.ONE := by
  unfold Red; rw [cpoly_Fp_ONE_val]; decide

def extCoeff (a : cpoly.field.Ext4) : ℕ → K
  | 0 => toK a.c0
  | 1 => toK a.c1
  | 2 => toK a.c2
  | _ => toK a.c3

/-- An extracted `Ext4` struct read as an element of `Hachi.Ext4`. -/
def toExt (a : cpoly.field.Ext4) : F := Ext.ofFn (fun i => extCoeff a i.val)

/-- Representation invariant for one extension element: all four coefficients
are reduced base-field words. -/
def Reduced (a : cpoly.field.Ext4) : Prop :=
  Red a.c0 ∧ Red a.c1 ∧ Red a.c2 ∧ Red a.c3

/-- Representation invariant for a polynomial: every coefficient is reduced.

Stated about `alloc.vec.Vec`, which is what `cpoly.univariate.UnivariatePoly`,
`cpoly.multilinear.MultilinearPoly` and `cpoly.multilinear.MultilinearEvals` all reduce to. -/
def VecReduced (v : alloc.vec.Vec cpoly.field.Ext4) : Prop := ∀ a ∈ v.val, Reduced a

/-- The same, for a `&[Ext4]` parameter — the evaluation points of the
multilinear layer are slices. -/
def SliceReduced (s : Slice cpoly.field.Ext4) : Prop := ∀ a ∈ s.val, Reduced a

/-- `Vec::deref` — the `&Vec<T>` to `&[T]` coercion — is the identity on the
underlying list, so it moves the invariant across for free.  The multilinear
layer needs this at every call that passes a table where a `&[Ext4]` is expected. -/
@[simp] theorem deref_val (v : alloc.vec.Vec cpoly.field.Ext4) :
    (alloc.vec.Vec.deref v).val = v.val := rfl

theorem sliceReduced_deref {v : alloc.vec.Vec cpoly.field.Ext4} (h : VecReduced v) :
    SliceReduced (alloc.vec.Vec.deref v) := h

theorem vecReduced_of_sliceReduced {v : alloc.vec.Vec cpoly.field.Ext4}
    (h : SliceReduced (alloc.vec.Vec.deref v)) : VecReduced v := h

@[simp] theorem deref_len (v : alloc.vec.Vec cpoly.field.Ext4) :
    Slice.len (alloc.vec.Vec.deref v) = alloc.vec.Vec.len v := rfl

@[simp] theorem coeff_toExt (a : cpoly.field.Ext4) (i : Fin Hachi.ext4Params.d) :
    Ext.coeff (toExt a) i = extCoeff a i.val := Ext.coeff_ofFn _ _

/-- Every coefficient index of `Ext4` is one of the four literals.  Together with
`sum_univ_four'` this is all the `Fin ext4Params.d` reasoning the file needs. -/
theorem fin_four_cases (i : Fin Hachi.ext4Params.d) :
    (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 := by
  have := i.isLt
  have h4 : Hachi.ext4Params.d = 4 := Hachi.ext4Params_d
  omega

/-- `Fin.sum_univ_four` for an index type whose bound is only *provably* `4`.
Stating it with the equation as a hypothesis lets `subst` fix up the dependent
`Fin n`, which is what `simp only [Hachi.ext4Params_d]` cannot do. -/
theorem sum_univ_four' {M : Type*} [AddCommMonoid M] {n : ℕ} (h : n = 4) (f : Fin n → M) :
    ∑ i : Fin n, f i
      = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ + f ⟨2, by omega⟩ + f ⟨3, by omega⟩ := by
  subst h; exact Fin.sum_univ_four f

/-! ### Local helpers the ported scripts need at this version

`Hachi.ext4Params.d` and `Hachi.ext4Params.toExtensionParams.d` are definitionally
equal but not syntactically so, and `Ext`'s index type is spelled with the second.
`simp` and `rw` match only up to reducible unfolding, so a rewrite stated at the
first spelling -- `coeff_toExt` above, which is where the upstream scripts go
through -- no longer fires on a goal produced by `Ext.ext`.  `coeff_toExt'` is
that same fact at the spelling the goals use, and it is what the proofs below
rewrite with; `coeff_toExt` is left in place, being part of this file's API. -/

/-- `coeff_toExt` at the index type an `Ext.ext` goal presents. -/
private theorem coeff_toExt' (a : cpoly.field.Ext4)
    (i : Fin Hachi.ext4Params.toExtensionParams.d) :
    Ext.coeff (toExt a) i = extCoeff a i.val := Ext.coeff_ofFn _ _

/-- `fin_four_cases` as an equation on the index itself rather than on its value,
so that `rcases … with rfl` substitutes it and leaves a closed index behind.  The
`rw [h]` of the upstream scripts, which rewrote `↑i` only, is not enough for
`ext_mul_spec`: there the index also occurs bare, as the second argument of
`Ext.coeff (Ext.monomialMod _) i`. -/
private theorem fin_four_eq (i : Fin Hachi.ext4Params.toExtensionParams.d) :
    i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ ∨ i = ⟨2, by decide⟩ ∨ i = ⟨3, by decide⟩ := by
  have hlt := i.isLt
  have hcases : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 := by
    have h4 : Hachi.ext4Params.toExtensionParams.d = 4 := rfl
    omega
  rcases hcases with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

/-- The reduction table of `X^4 - 2`: `X^k mod (X^4 - 2)` is `X^k` itself for
`k < 4`, and `2 · X^(k-4)` for `4 ≤ k ≤ 6`.  Those seven exponents are all a
product of two reduced elements reaches, and they are what `Ext.coeff_mul`'s
double sum leaves behind.  Each of the twenty-eight cases is a closed
computation, so `decide` settles it. -/
private theorem coeff_monomialMod_val (k : ℕ) (m : Fin Hachi.ext4Params.toExtensionParams.d)
    (hk : k < 7 := by norm_num) :
    Ext.coeff (Ext.monomialMod k : F) m =
      if k < 4 then (if (m : ℕ) = k then 1 else 0) else (if (m : ℕ) + 4 = k then 2 else 0) := by
  rcases fin_four_eq m with rfl | rfl | rfl | rfl <;> interval_cases k <;> decide

/-- `Fp::is_zero` decides whether a reduced word is the zero of the base field.
`lean/Field.lean` specifies `Fp`'s operators and its construction boundary but
not this predicate, and `Ext4::is_zero` below is four calls to it; reducedness is
what makes the word test sound, exactly as in the extension-level statement.

Public, where this file's other three helpers are `private`: it is the only
statement anywhere in the development about `cpoly::field::Fp::is_zero`, so it
is a headline spec rather than a local convenience, and `Check.lean` § 4 pins
it. `private` would put it beyond that audit's reach -- which is how it was
first written, and `make build` caught it as an unknown constant. -/
@[step]
theorem fp_is_zero_spec (a : cpoly.field.Fp) (ha : Red a) :
    cpoly.field.Fp.is_zero a ⦃ b => (b = true ↔ toK a = 0) ⦄ := by
  rw [cpoly.field.Fp.is_zero]
  simp only [spec_ok, decide_eq_true_eq]
  rw [show (0 : ZMod q) = toK cpoly.field.Fp.ZERO by simp, toK_inj_of_Red ha Red_zero,
    cpoly_Fp_ZERO_val]
  constructor
  · intro h; rw [h]; rfl
  · intro h; scalar_tac

/-- `toExt` is injective on the four coefficients: this is what makes the
representation faithful. -/
theorem toExt_eq_iff (a b : cpoly.field.Ext4) :
    toExt a = toExt b ↔ (toK a.c0 = toK b.c0 ∧ toK a.c1 = toK b.c1 ∧
      toK a.c2 = toK b.c2 ∧ toK a.c3 = toK b.c3) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := congrArg
        (fun z => Ext.coeff z (⟨0, by decide⟩ : Fin Hachi.ext4Params.toExtensionParams.d)) h
      simp only [coeff_toExt'] at this; simpa [extCoeff] using this
    · have := congrArg
        (fun z => Ext.coeff z (⟨1, by decide⟩ : Fin Hachi.ext4Params.toExtensionParams.d)) h
      simp only [coeff_toExt'] at this; simpa [extCoeff] using this
    · have := congrArg
        (fun z => Ext.coeff z (⟨2, by decide⟩ : Fin Hachi.ext4Params.toExtensionParams.d)) h
      simp only [coeff_toExt'] at this; simpa [extCoeff] using this
    · have := congrArg
        (fun z => Ext.coeff z (⟨3, by decide⟩ : Fin Hachi.ext4Params.toExtensionParams.d)) h
      simp only [coeff_toExt'] at this; simpa [extCoeff] using this
  · rintro ⟨h0, h1, h2, h3⟩
    apply Ext.ext; intro i
    simp only [coeff_toExt']
    rcases fin_four_eq i with rfl | rfl | rfl | rfl <;> simpa [extCoeff]

theorem reduced_ZERO : Reduced cpoly.field.Ext4.ZERO := by
  simp only [cpoly.field.Ext4.ZERO, Reduced]
  exact ⟨red_Fp_ZERO, red_Fp_ZERO, red_Fp_ZERO, red_Fp_ZERO⟩

theorem reduced_ONE : Reduced cpoly.field.Ext4.ONE := by
  simp only [cpoly.field.Ext4.ONE, Reduced]
  exact ⟨red_Fp_ONE, red_Fp_ZERO, red_Fp_ZERO, red_Fp_ZERO⟩

@[simp] theorem toExt_ZERO : toExt cpoly.field.Ext4.ZERO = 0 := by
  apply Ext.ext; intro i
  simp only [coeff_toExt', Ext.coeff_zero]
  rcases fin_four_eq i with rfl | rfl | rfl | rfl <;>
    simp [extCoeff, cpoly.field.Ext4.ZERO]

@[simp] theorem toExt_ONE : toExt cpoly.field.Ext4.ONE = 1 := by
  apply Ext.ext; intro i
  simp only [coeff_toExt', Ext.coeff_one]
  rcases fin_four_eq i with rfl | rfl | rfl | rfl <;>
    simp [extCoeff, cpoly.field.Ext4.ONE]

/-- `impl Add for Ext4`, coefficient-wise. -/
@[step]
theorem ext_add_spec (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    cpoly.field.Ext4.Insts.CoreOpsArithAddExt4Ext4.add a b
      ⦃ c => Reduced c ∧ toExt c = toExt a + toExt b ⦄ := by
  obtain ⟨a0, a1, a2, a3⟩ := ha
  obtain ⟨b0, b1, b2, b3⟩ := hb
  rw [cpoly.field.Ext4.Insts.CoreOpsArithAddExt4Ext4.add]
  step as ⟨u0, r0, e0⟩
  step as ⟨u1, r1, e1⟩
  step as ⟨u2, r2, e2⟩
  step as ⟨u3, r3, e3⟩
  refine ⟨⟨r0, r1, r2, r3⟩, ?_⟩
  apply Ext.ext; intro i
  simp only [Ext.coeff_add, coeff_toExt']
  rcases fin_four_eq i with rfl | rfl | rfl | rfl <;>
    simp only [extCoeff, e0, e1, e2, e3]

/-- `impl Sub for Ext4`, coefficient-wise. -/
@[step]
theorem ext_sub_spec (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    cpoly.field.Ext4.Insts.CoreOpsArithSubExt4Ext4.sub a b
      ⦃ c => Reduced c ∧ toExt c = toExt a - toExt b ⦄ := by
  obtain ⟨a0, a1, a2, a3⟩ := ha
  obtain ⟨b0, b1, b2, b3⟩ := hb
  rw [cpoly.field.Ext4.Insts.CoreOpsArithSubExt4Ext4.sub]
  step as ⟨u0, r0, e0⟩
  step as ⟨u1, r1, e1⟩
  step as ⟨u2, r2, e2⟩
  step as ⟨u3, r3, e3⟩
  refine ⟨⟨r0, r1, r2, r3⟩, ?_⟩
  apply Ext.ext; intro i
  simp only [Ext.coeff_sub, coeff_toExt']
  rcases fin_four_eq i with rfl | rfl | rfl | rfl <;>
    simp only [extCoeff, e0, e1, e2, e3]

/-- `impl Mul for Ext4`.

**Rewritten by the 2026-09-16 cpoly bump, statement unchanged.** The old body
formed the seven schoolbook coefficients `t0 .. t6`, reducing after every base
multiplication, and folded the high half back by multiplying by `W = 2`. The new
body accumulates the sixteen products into four unreduced two-word `(low, high)`
pairs -- using `add_double_product` exactly where the old one multiplied by `W`,
which is why `cpoly.field.W` is no longer in the model at all -- and calls
`reduce_wide` four times, once per output coefficient.

So the proof splits cleanly in two. The **body** half is the sixteen accumulator
steps and the four reductions, and it lives on `wideK`: `ec0 .. ec3` say what
each finished accumulator denotes, with the `2`s coming from
`add_double_product_spec`. The `≤ 7` contract of `reduce_wide_spec` is
discharged from the carry bounds the accumulator steps thread along -- four
`add_product`s contribute at most `1` each and the `add_double_product`s at most
`2`, so the worst high word here is `6`.

The **specification** half is untouched from the pre-bump proof: `Ext.coeff_mul`
sums the two-branch kernel over all `(i, j) : Fin 4 × Fin 4`, `sum_univ_four'`
expands both double sums, and `coeff_monomialMod_val` supplies the reduction
table -- which already carries the spec-side `2` as a numeral, so it never
needed `toK_W`. `ring` closes the eight-coefficient algebra. -/
@[step]
theorem ext_mul_spec (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    cpoly.field.Ext4.Insts.CoreOpsArithMulExt4Ext4.mul a b
      ⦃ c => Reduced c ∧ toExt c = toExt a * toExt b ⦄ := by
  obtain ⟨a0, a1, a2, a3⟩ := ha
  obtain ⟨b0, b1, b2, b3⟩ := hb
  rw [cpoly.field.Ext4.Insts.CoreOpsArithMulExt4Ext4.mul]
  step as ⟨c0, hc0bound, hc0⟩
  step as ⟨c1, hc1bound, hc1⟩
  step as ⟨c2, hc2bound, hc2⟩
  step as ⟨c3, hc3bound, hc3⟩
  step as ⟨c01, hc01bound, hc01⟩
  step as ⟨c11, hc11bound, hc11⟩
  step as ⟨c21, hc21bound, hc21⟩
  step as ⟨c31, hc31bound, hc31⟩
  step as ⟨c02, hc02bound, hc02⟩
  step as ⟨c12, hc12bound, hc12⟩
  step as ⟨c22, hc22bound, hc22⟩
  step as ⟨c32, hc32bound, hc32⟩
  step as ⟨c03, hc03bound, hc03⟩
  step as ⟨c13, hc13bound, hc13⟩
  step as ⟨c23, hc23bound, hc23⟩
  step as ⟨c33, hc33bound, hc33⟩
  change (do
    let f ← cpoly.field.reduce_wide c03.1 c03.2
    let f1 ← cpoly.field.reduce_wide c13.1 c13.2
    let f2 ← cpoly.field.reduce_wide c23.1 c23.2
    let f3 ← cpoly.field.reduce_wide c33.1 c33.2
    ok ({ c0 := f, c1 := f1, c2 := f2, c3 := f3 } : cpoly.field.Ext4)) ⦃ c =>
      Reduced c ∧ toExt c = toExt a * toExt b ⦄
  step as ⟨f0, rf0, ef0⟩
  step as ⟨f1, rf1, ef1⟩
  step as ⟨f2, rf2, ef2⟩
  step as ⟨f3, rf3, ef3⟩
  have ec0 : wideK c03 = toK a.c0 * toK b.c0 +
      2 * toK a.c1 * toK b.c3 + 2 * toK a.c2 * toK b.c2 + 2 * toK a.c3 * toK b.c1 := by
    rw [hc03, hc02, hc01, hc0]
    simp only [wideK]
    norm_num
  have ec1 : wideK c13 = toK a.c0 * toK b.c1 + toK a.c1 * toK b.c0 +
      2 * toK a.c2 * toK b.c3 + 2 * toK a.c3 * toK b.c2 := by
    rw [hc13, hc12, hc11, hc1]
    simp only [wideK]
    norm_num
  have ec2 : wideK c23 = toK a.c0 * toK b.c2 + toK a.c1 * toK b.c1 +
      toK a.c2 * toK b.c0 + 2 * toK a.c3 * toK b.c3 := by
    rw [hc23, hc22, hc21, hc2]
    simp only [wideK]
    norm_num
  have ec3 : wideK c33 = toK a.c0 * toK b.c3 + toK a.c1 * toK b.c2 +
      toK a.c2 * toK b.c1 + toK a.c3 * toK b.c0 := by
    rw [hc33, hc32, hc31, hc3]
    simp only [wideK]
    norm_num
  refine ⟨⟨rf0, rf1, rf2, rf3⟩, ?_⟩
  apply Ext.ext; intro i
  rw [Ext.coeff_mul, sum_univ_four' (rfl : Hachi.ext4Params.toExtensionParams.d = 4)]
  simp only [sum_univ_four' (rfl : Hachi.ext4Params.toExtensionParams.d = 4), coeff_toExt']
  rcases fin_four_eq i with rfl | rfl | rfl | rfl <;>
    simp only [extCoeff, ef0, ef1, ef2, ef3, ec0, ec1, ec2, ec3] <;>
    norm_num <;>
    simp only [coeff_monomialMod_val 1, coeff_monomialMod_val 2, coeff_monomialMod_val 3,
      coeff_monomialMod_val 4, coeff_monomialMod_val 5, coeff_monomialMod_val 6] <;>
    norm_num <;>
    ring

/-! ### Extension construction and comparison -/

/-- `Ext4::from_base` embeds a base-field element as the constant coefficient;
this is CompPoly's `Ext.ofBase`. -/
@[step]
theorem ext_from_base_spec (a : cpoly.field.Fp) (ha : Red a) :
    cpoly.field.Ext4.from_base a ⦃ c => Reduced c ∧ toExt c = Ext.ofBase (toK a) ⦄ := by
  rw [cpoly.field.Ext4.from_base]
  simp only [spec_ok]
  refine ⟨⟨ha, red_Fp_ZERO, red_Fp_ZERO, red_Fp_ZERO⟩, ?_⟩
  apply Ext.ext; intro i
  simp only [coeff_toExt', Ext.coeff_ofBase]
  rcases fin_four_eq i with rfl | rfl | rfl | rfl <;> simp [extCoeff]

/-- Coefficient `i` of `ofBase c * x` is `c * coeff x i`: `ofBase` **is** the
algebra map, so the product is the scalar action and `Ext.coeff_smul` applies.
This is the whole content of the mixed multiply below. -/
theorem coeff_ofBase_mul (c : K) (x : F) (i : Fin Hachi.ext4Params.toExtensionParams.d) :
    Ext.coeff (Ext.ofBase c * x) i = c * Ext.coeff x i := by
  rw [show (Ext.ofBase c : F) = algebraMap K F c from rfl, ← Algebra.smul_def, Ext.coeff_smul]

/-- `impl Mul<Ext4> for Fp` -- the **mixed** product, `Fp` on the left.  Four base
multiplications, one per coefficient, where the quartic multiply would do nineteen;
on the specification side that is `ofBase c * x`, i.e. `c • x`.

Only the extension operand needs `Reduced`; the base operand needs `Red`, and the
pairing is fixed by the impl's argument order, which is also what selects this impl
over `Ext4`'s own -- two declarations whose mangled names differ only in their
namespace. `Check.lean` § 2 pins this one's body, four `Fp` multiplies against the
quartic multiply's nineteen. -/
@[step]
theorem fp_ext_mul_spec (a : cpoly.field.Fp) (b : cpoly.field.Ext4)
    (ha : Red a) (hb : Reduced b) :
    cpoly.field.Fp.Insts.CoreOpsArithMulExt4Ext4.mul a b
      ⦃ c => Reduced c ∧ toExt c = Ext.ofBase (toK a) * toExt b ⦄ := by
  obtain ⟨b0, b1, b2, b3⟩ := hb
  rw [cpoly.field.Fp.Insts.CoreOpsArithMulExt4Ext4.mul]
  step as ⟨u0, r0, e0⟩
  step as ⟨u1, r1, e1⟩
  step as ⟨u2, r2, e2⟩
  step as ⟨u3, r3, e3⟩
  refine ⟨⟨r0, r1, r2, r3⟩, ?_⟩
  apply Ext.ext; intro i
  rw [coeff_ofBase_mul]
  simp only [coeff_toExt']
  rcases fin_four_eq i with rfl | rfl | rfl | rfl <;>
    simp only [extCoeff, e0, e1, e2, e3]

/-- `Ext4::is_zero` decides whether the represented element is `0`.  Reducedness
is needed in both directions: without it a word congruent to `0` but not equal to
it would make the test unsound. -/
@[step]
theorem ext_is_zero_spec (a : cpoly.field.Ext4) (ha : Reduced a) :
    cpoly.field.Ext4.is_zero a ⦃ b => (b = true ↔ toExt a = 0) ⦄ := by
  obtain ⟨h0, h1, h2, h3⟩ := ha
  have hcoeffs : toExt a = 0 ↔ (toK a.c0 = 0 ∧ toK a.c1 = 0 ∧ toK a.c2 = 0 ∧ toK a.c3 = 0) := by
    rw [← toExt_ZERO, toExt_eq_iff]
    simp only [cpoly.field.Ext4.ZERO, toK_zero]
  rw [cpoly.field.Ext4.is_zero, hcoeffs]
  apply spec_bind (fp_is_zero_spec a.c0 h0); intro b0 hb0
  by_cases e0 : b0 = true
  · rw [if_pos e0]
    apply spec_bind (fp_is_zero_spec a.c1 h1); intro b1 hb1
    by_cases e1 : b1 = true
    · rw [if_pos e1]
      apply spec_bind (fp_is_zero_spec a.c2 h2); intro b2 hb2
      by_cases e2 : b2 = true
      · rw [if_pos e2]
        apply spec_mono (fp_is_zero_spec a.c3 h3); intro b3 hb3
        rw [hb3, hb0.mp e0, hb1.mp e1, hb2.mp e2]
        simp
      · rw [if_neg e2]
        simp only [spec_ok, Bool.false_eq_true, false_iff, not_and]
        intro _ _ hc
        exact absurd (hb2.mpr hc) e2
    · rw [if_neg e1]
      simp only [spec_ok, Bool.false_eq_true, false_iff, not_and]
      intro _ hc
      exact absurd (hb1.mpr hc) e1
  · rw [if_neg e0]
    simp only [spec_ok, Bool.false_eq_true, false_iff, not_and]
    intro hc
    exact absurd (hb0.mpr hc) e0
