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

The file carries no `sorry`; what remains before it can move to `lean/` is the
promotion checklist in `lean-wip/README.md`.

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
`from_fp`, `from_u64`, `smul`, `sub_assign`, `neg` and the `GEN` constant.
**None of those are in hachi's `Generated.lean`**, and that is not a whitelist
gap: `--include 'cpoly::_'` decides which foreign items *may* be translated,
while what lands is what the local crate reaches -- and `--lib` extraction does
not see `benches/`, which is the only place `Ext4::new` is used. Their specs are
dropped rather than stubbed, because a statement about a name that does not
exist is the `autoImplicit` trap in another costume, and this file sets
`autoImplicit false` so that such a statement fails loudly instead. What
remains is exactly what `zerocheck.rs` and `ringswitch.rs` compute with:
`from_base`, `is_zero`, `add`, `sub`, `mul`, the two assign forms, `ZERO`,
`ONE` and `W`. See NOTES.md § "The model contains what the crate reaches". -/

/-! ## Compatibility with `HachiEquiv.Field` -/

theorem cpoly_W_val : (cpoly.field.W).val = 2 := by simp only [cpoly.field.W]; decide

theorem red_Fp_ZERO : Red cpoly.field.Fp.ZERO := by
  unfold Red; rw [cpoly_Fp_ZERO_val]; decide

theorem red_Fp_ONE : Red cpoly.field.Fp.ONE := by
  unfold Red; rw [cpoly_Fp_ONE_val]; decide

/-- The extension constant `W = 2` is reduced, so `Fp`'s `Mul` spec applies to
`W * _`. -/
theorem red_W : Red cpoly.field.W := by unfold Red; rw [cpoly_W_val]; decide

/-- ... and denotes the `W` of `Hachi.ext4Params`. -/
@[simp] theorem toK_W : toK cpoly.field.W = 2 := by simp only [toK, cpoly_W_val]; norm_num

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

The Rust code forms the seven schoolbook coefficients `t0 .. t6` and folds the
high half back with a factor of `W = 2` (`Y^4 = 2`); the reference `Ext.mul`
sums the two-branch kernel over all `(i, j) : Fin 4 × Fin 4`.  Expanding both
double sums with `sum_univ_four'` turns the identity into commutative-ring
algebra in the eight coefficients, which `ring` closes. -/
@[step]
theorem ext_mul_spec (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    cpoly.field.Ext4.Insts.CoreOpsArithMulExt4Ext4.mul a b
      ⦃ c => Reduced c ∧ toExt c = toExt a * toExt b ⦄ := by
  obtain ⟨a0, a1, a2, a3⟩ := ha
  obtain ⟨b0, b1, b2, b3⟩ := hb
  have hW : Red cpoly.field.W := red_W
  rw [cpoly.field.Ext4.Insts.CoreOpsArithMulExt4Ext4.mul]
  step as ⟨t0, rt0, et0⟩
  step as ⟨m01, rm01, em01⟩
  step as ⟨m10, rm10, em10⟩
  step as ⟨t1, rt1, et1⟩
  step as ⟨m02, rm02, em02⟩
  step as ⟨m11, rm11, em11⟩
  step as ⟨s2, rs2, es2⟩
  step as ⟨m20, rm20, em20⟩
  step as ⟨t2, rt2, et2⟩
  step as ⟨m03, rm03, em03⟩
  step as ⟨m12, rm12, em12⟩
  step as ⟨s3a, rs3a, es3a⟩
  step as ⟨m21, rm21, em21⟩
  step as ⟨s3b, rs3b, es3b⟩
  step as ⟨m30, rm30, em30⟩
  step as ⟨t3, rt3, et3⟩
  step as ⟨m13, rm13, em13⟩
  step as ⟨m22, rm22, em22⟩
  step as ⟨s4, rs4, es4⟩
  step as ⟨m31, rm31, em31⟩
  step as ⟨t4, rt4, et4⟩
  step as ⟨m23, rm23, em23⟩
  step as ⟨m32, rm32, em32⟩
  step as ⟨t5, rt5, et5⟩
  step as ⟨t6, rt6, et6⟩
  step as ⟨w4, rw4, ew4⟩
  step as ⟨c0, rc0, ec0⟩
  step as ⟨w5, rw5, ew5⟩
  step as ⟨c1, rc1, ec1⟩
  step as ⟨w6, rw6, ew6⟩
  step as ⟨c2, rc2, ec2⟩
  refine ⟨⟨rc0, rc1, rc2, rt3⟩, ?_⟩
  apply Ext.ext; intro i
  rw [Ext.coeff_mul, sum_univ_four' (rfl : Hachi.ext4Params.toExtensionParams.d = 4)]
  simp only [sum_univ_four' (rfl : Hachi.ext4Params.toExtensionParams.d = 4), coeff_toExt']
  -- The reduction table has to be supplied one exponent at a time: with `k` still
  -- a metavariable, `simp` will not match `Ext.coeff (Ext.monomialMod k) ⟨_, _⟩`
  -- here, the index being a `Fin` whose bound is a non-reducible projection.
  rcases fin_four_eq i with rfl | rfl | rfl | rfl <;>
    simp only [extCoeff, ec0, ec1, ec2, et3, ew4, ew5, ew6, et0, et1, et2, et4, et5, et6,
      es2, es3a, es3b, es4, em01, em10, em02, em11, em20, em03, em12, em21, em30,
      em13, em22, em31, em23, em32, toK_W] <;>
    norm_num <;>
    simp only [coeff_monomialMod_val 1, coeff_monomialMod_val 2, coeff_monomialMod_val 3,
      coeff_monomialMod_val 4, coeff_monomialMod_val 5, coeff_monomialMod_val 6] <;>
    norm_num <;>
    ring

/-- `impl AddAssign for Ext4`. -/
@[step]
theorem ext_add_assign_spec (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    cpoly.field.Ext4.Insts.CoreOpsArithAddAssignExt4.add_assign a b
      ⦃ c => Reduced c ∧ toExt c = toExt a + toExt b ⦄ := by
  rw [cpoly.field.Ext4.Insts.CoreOpsArithAddAssignExt4.add_assign]
  exact ext_add_spec a b ha hb

/-- `impl MulAssign for Ext4`. -/
@[step]
theorem ext_mul_assign_spec (a b : cpoly.field.Ext4) (ha : Reduced a) (hb : Reduced b) :
    cpoly.field.Ext4.Insts.CoreOpsArithMulAssignExt4.mul_assign a b
      ⦃ c => Reduced c ∧ toExt c = toExt a * toExt b ⦄ := by
  rw [cpoly.field.Ext4.Insts.CoreOpsArithMulAssignExt4.mul_assign]
  exact ext_mul_spec a b ha hb

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

