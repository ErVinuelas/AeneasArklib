import Generated
import Field
import Ring
import ArkLib.Data.Lattices.CyclotomicRing.Core.Modulus

/-!
Audit file: not part of the development, only a machine-checked review of what
this repository currently claims.

Nothing imports this file and nothing here is used by a proof; it is a root of
the library in its own right (see `lakefile.lean`), which is what gets it checked
by `lake build`. Its eventual job is the one `Check.lean` does in AeneasCompPoly:
catch the failure mode that a `_spec` theorem is *true but vacuous*, and print
the axiom dependencies of the headline specs so that a reader can confirm no
`sorryAx` hides under one.

What it audits, in four sections:

1. the extracted parameters are the ones `src/params.rs` names, and they satisfy
   every side condition the generic ArkLib statements carry as a hypothesis --
   including the two that the *derived* bounds rest on (`b - 1 ≤ q/2` for the digit
   bound, `q % 8 = 5` and `κ² < q` for challenge invertibility);
2. the `cpoly` field layer arrives *transparently*, not as axioms -- the question
   Workstream 0 existed to settle;
   2b. all four modules of the scheme are present in the model, with the shapes the
   equivalence proofs need: the container newtypes are `Vec` aliases, and every
   operation is `Result`-valued (so each spec owes a totality proof, not just an
   equality);
3. the ArkLib specification side is reachable from this package at all, and the
   ring degree the Rust fixes is the degree ArkLib's modulus actually has;
4. the axiom dependencies of every proved spec, which is what makes a `sorryAx`
   a build failure rather than a silent debt.

§ 4 is the one that grows: it lists the base-field specs (`lean/Field.lean`), which
are proved. The ring, gadget and commitment obligations are *stated* in
`lean-wip/` and not proved, so they are deliberately absent from it -- see
`lean-wip/README.md` for the promotion procedure.
-/

-- Off, and load-bearing for an audit file specifically. With `autoImplicit` on (the
-- Lean default; ArkLib turns it off repository-wide for the same reason), an
-- unknown identifier appearing in a *binder type* is silently auto-bound as an
-- implicit variable rather than reported. An assertion about an extracted name that
-- has since left `Generated.lean` then keeps compiling, about a universally
-- quantified nothing -- which is exactly the "true but vacuous" failure this file
-- exists to catch, applied to the file itself. Found the hard way: the `Ext4`
-- examples below outlived the item they were about, and only the one that used the
-- name in a *term* position failed the build.
set_option autoImplicit false

open Aeneas Aeneas.Std
open ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus

-- Aeneas wraps the whole extracted model in a namespace named after the crate,
-- so every generated name is `hachi.…` -- including the `cpoly` items the
-- `--include` whitelist pulled in, which land at `hachi.cpoly.field.…` rather
-- than at a top-level `cpoly`. Opening it lets this file spell them the way
-- `Generated.lean` reads.
open hachi

namespace HachiEquiv.Check

/-! ## 1. The parameters are what `params.rs` says, and they are legal -/

-- The extracted constants. `simp` rather than `rfl`: Aeneas marks each global
-- `irreducible`, so the equation lemma is the way in.
example : params.Q = 4294967197#u64 := by simp [params.Q]
example : params.EXT_DEGREE = 4#usize := by simp [params.EXT_DEGREE]
example : params.EXT_W = 2#u64 := by simp [params.EXT_W]
example : params.RING_LOG_DEGREE = 6#usize := by simp [params.RING_LOG_DEGREE]
example : params.RING_DEGREE = 64#usize := by simp [params.RING_DEGREE]
example : params.GADGET_BASE = 2#u64 := by simp [params.GADGET_BASE]
example : params.GADGET_DIGITS = 32#usize := by simp [params.GADGET_DIGITS]
example : params.MESSAGE_ROWS = 4#usize := by simp [params.MESSAGE_ROWS]
example : params.INNER_ROWS = 2#usize := by simp [params.INNER_ROWS]
example : params.OUTER_ROWS = 2#usize := by simp [params.OUTER_ROWS]
example : params.BLOCKS = 2#usize := by simp [params.BLOCKS]
example : params.GAMMA = 1#u64 := by simp [params.GAMMA]
example : params.BETA_SQ = 8192#u128 := by simp [params.BETA_SQ]
example : params.KAPPA = 65535#u64 := by simp [params.KAPPA]

-- `RING_DEGREE` is a literal in Rust (a shift would extract as a `Result`; see
-- the docstring in `params.rs`), so the relation to `RING_LOG_DEGREE` is not
-- true by construction on this side and has to be checked.
example : params.RING_DEGREE.val = 2 ^ params.RING_LOG_DEGREE.val := by
  simp [params.RING_DEGREE, params.RING_LOG_DEGREE]

-- `zmodDigitDecomposition` (Gadget/Core.lean) needs `1 < b` and `q ≤ b ^ digits`.
-- Without these two the gadget layer has no instance at all, so they are checked
-- before any of it is written.
example : 1 < params.GADGET_BASE.val := by simp [params.GADGET_BASE]
example : params.Q.val ≤ params.GADGET_BASE.val ^ params.GADGET_DIGITS.val := by
  simp [params.Q, params.GADGET_BASE, params.GADGET_DIGITS]

-- ... and `digits` is minimal: one fewer would not cover the modulus, which is
-- what pins it to 32 rather than merely permitting it.
example : params.GADGET_BASE.val ^ (params.GADGET_DIGITS.val - 1) < params.Q.val := by
  simp [params.Q, params.GADGET_BASE, params.GADGET_DIGITS]

-- `Gadget/Norms.lean`'s `zmodDigit_natAbs_le` -- the single analytic input to
-- every honest-case shortness bound -- additionally needs `b - 1 ≤ q/2`, which is
-- what stops a small non-negative digit from wrapping to a negative centered
-- representative.
example : params.GADGET_BASE.val - 1 ≤ params.Q.val / 2 := by
  simp [params.Q, params.GADGET_BASE]

-- `GAMMA` is that same bound `b - 1`, and `BETA_SQ` is
-- `(messageRows · digits) · (deg φ) · (b-1)²` --
-- `gadgetDecompose_zmod_vecLInftyNorm_le` and
-- `gadgetDecompose_zmod_vecL2NormSq_le` at these dimensions. Both are literals in
-- `params.rs` (Aeneas models `const` arithmetic as fallible, so the derived forms
-- would extract as `Result`s), so the derivation is checked rather than structural.
example : params.GAMMA.val = params.GADGET_BASE.val - 1 := by
  simp [params.GAMMA, params.GADGET_BASE]

example : params.BETA_SQ.val
    = params.MESSAGE_ROWS.val * params.GADGET_DIGITS.val * params.RING_DEGREE.val
        * (params.GADGET_BASE.val - 1) ^ 2 := by
  simp [params.BETA_SQ, params.MESSAGE_ROWS, params.GADGET_DIGITS, params.RING_DEGREE,
    params.GADGET_BASE]

-- `KAPPA` is capped by `isUnit_of_l1Norm_le` (`NormBounds/LyubashevskySeiler.lean`),
-- which turns the verifier's `0 < ‖c‖₁ ≤ κ` into the invertibility a weak opening
-- actually requires -- given `q % 8 = 5` and `κ² < q`. Both halves, and the fact
-- that `params.rs` sits on the ceiling rather than near it:
example : params.Q.val % 8 = 5 := by simp [params.Q]
example : params.KAPPA.val ^ 2 < params.Q.val := by simp [params.KAPPA, params.Q]
example : params.Q.val ≤ (params.KAPPA.val + 1) ^ 2 := by simp [params.KAPPA, params.Q]

-- The honest challenge is `c = 1`, and `Rq.l1Norm_one` gives `‖1‖₁ = 1`; the
-- verifier's upper bound has to admit it or nothing this crate produces verifies.
example : 1 ≤ params.KAPPA.val := by simp [params.KAPPA]

-- `Y^4 - W` is irreducible over `F_q` for non-square `W` exactly when `q ≡ 1 mod
-- 4`, which is what makes the quartic extension a field.
example : params.Q.val % 4 = 1 := by simp [params.Q]

/-! ## 2. The `cpoly` field layer is transparent, not axiomatized

This is the finding of Workstream 0 and the reason the field is a cargo
dependency rather than a vendored copy of `field.rs`. Charon's default whitelist
is the local crate, so a plain `charon cargo --preset=aeneas` puts

    axiom cpoly.field.Fp : Type
    axiom cpoly.field.Fp.ZERO : Result cpoly.field.Fp
    axiom cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add : ...

in `Generated.lean` -- an uninterpreted field with an uninterpreted addition,
about which nothing can be proved, and three `axiom`s that would show up under
every `#print axioms` in § 4 forever. `make extract` passes `--include 'cpoly::_'`
instead, and the examples below are what would break if that flag were ever
dropped: an `axiom` has no body and no projections, so not one of them would
typecheck against one. -/

-- The newtype is free on this side: Aeneas extracts a single-field tuple struct
-- as a `@[reducible]` abbreviation, so `Fp` *is* `U64` as far as proofs care.
example : cpoly.field.Fp = Std.U64 := rfl

-- The modulus travelled across the crate boundary as a value, not a symbol.
example : cpoly.field.P = 4294967197#u64 := by simp [cpoly.field.P]

-- ... and it is the same modulus this crate's own parameter names. If these two
-- ever disagree, every proof bridging the two layers is about two fields.
example : cpoly.field.P = params.Q := by simp [cpoly.field.P, params.Q]

-- The addition has a body, and it is the Rust one: `(self + rhs) % P`, in
-- Aeneas's fallible form. This is the example that an axiom could not satisfy.
example (a b : cpoly.field.Fp) :
    cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add a b
      = (do let s ← a + b; let r ← s % cpoly.field.P; Result.ok r) := by
  simp [cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add]

-- The other three operator impls, for the same reason: each has a body, and it is
-- the Rust one. `sub` adds the modulus before subtracting (so the `u64` cannot go
-- negative) and `neg`'s outer `% P` is what sends `0` to `0` rather than to `P` --
-- both visible here, which is what "transparent" means in practice.
example (a b : cpoly.field.Fp) :
    cpoly.field.Fp.Insts.CoreOpsArithSubFpFp.sub a b
      = (do let s ← a + cpoly.field.P; let d ← s - b; let r ← d % cpoly.field.P;
            Result.ok r) := by
  simp [cpoly.field.Fp.Insts.CoreOpsArithSubFpFp.sub]

example (a b : cpoly.field.Fp) :
    cpoly.field.Fp.Insts.CoreOpsArithMulFpFp.mul a b
      = (do let p ← a * b; let r ← p % cpoly.field.P; Result.ok r) := by
  simp [cpoly.field.Fp.Insts.CoreOpsArithMulFpFp.mul]

-- `Ext4` -- the quartic extension, the case a one-field newtype does not cover --
-- is deliberately *not* asserted here any more, and the reason is a finding rather
-- than a retreat.
--
-- Workstream 0 checked it, because `smoke.rs` (the extraction probe) used it. The
-- probe is gone and no module of the scheme touches the extension field yet: the
-- ring, the gadget and the commitment are all over `Z_q`, and `Ext4` enters with
-- the *protocol* layer, which commits to multilinear polynomials over the
-- extension and is out of scope until its ArkLib specification is frozen.
--
-- So `Ext4` is no longer in `Generated.lean` at all -- charon's `--include
-- 'cpoly::_'` whitelist decides which foreign items *may* be translated, not which
-- are: it still only follows what the local crate reaches. Asserting anything
-- about it here would be asserting about a name that does not exist, and this
-- section's claim -- that the field layer arrives transparently rather than as
-- axioms -- is made by the `Fp` items above, which are the ones the scheme
-- actually computes with. See NOTES.md § "The model contains what the crate
-- reaches".

-- Deliberately *not* asserted here: that `add 1 2` evaluates to `ok 3`. It is
-- true, but `simp` and `decide` do not get there on their own -- the checked
-- `U64` arithmetic needs Aeneas's `progress`/`scalar_tac` machinery, which
-- arrives with the first real spec. The structural equality above is the claim
-- that matters for § 2 anyway: it is the one an `axiom` cannot satisfy.

/-! ## 2b. The four modules arrived, with the shapes the proofs will need

Structural, not mathematical: each check below is a type ascription or an `rfl`,
and what it rules out is a module that silently failed to extract, or extracted
behind a wrapper that the equivalence file would then have to unfold. Two facts
are worth having on record:

* the three container newtypes (`Rq`, `PolyVec`, `PolyMatrix`) are `@[reducible]`
  aliases for `Vec`, so a statement about a `Rq` *is* a statement about a
  `Vec cpoly.field.Fp` and nothing has to be transported across a wrapper;
* every operation is `Result`-valued, i.e. fallible in the model, so each spec has
  a totality obligation to discharge and not merely an equality to prove. -/

example : ring.Rq = alloc.vec.Vec cpoly.field.Fp := rfl
example : linalg.PolyVec = alloc.vec.Vec ring.Rq := rfl
example : linalg.PolyMatrix = alloc.vec.Vec linalg.PolyVec := rfl

-- The ring layer.
example : Result ring.Rq := ring.Rq.zero
example (a b : ring.Rq) : Result ring.Rq := ring.Rq.add a b
example (a b : ring.Rq) : Result ring.Rq := ring.Rq.mul a b
example (a : ring.Rq) (k : Std.Usize) : Result cpoly.field.Fp := ring.Rq.coeff a k

-- The linear algebra layer.
example (u v : linalg.PolyVec) : Result ring.Rq := linalg.PolyVec.dot u v
example (a : linalg.PolyMatrix) (v : linalg.PolyVec) : Result linalg.PolyVec :=
  linalg.PolyMatrix.mat_vec_mul a v
example (xs : alloc.vec.Vec linalg.PolyVec) : Result linalg.PolyVec := linalg.flatten_blocks xs

-- The gadget layer.
example (c : cpoly.field.Fp) (e : Std.Usize) : Result cpoly.field.Fp := gadget.digit_at c e
example (rows : Std.Usize) (v : linalg.PolyVec) : Result linalg.PolyVec :=
  gadget.gadget_mul rows v
example (x : linalg.PolyVec) : Result linalg.PolyVec := gadget.gadget_decompose x

-- The commitment layer. `verify_weak` returning a `Bool` inside `Result` is the
-- shape the specification's own `verify_weak` has (a `Bool`, not a `Prop`), which
-- is what makes the equivalence statement an equality of decisions.
example (pp : commit.PublicParams) (m : alloc.vec.Vec linalg.PolyVec) :
    Result (linalg.PolyVec × commit.Decomp) := commit.commit pp m
example (pp : commit.PublicParams) (u : linalg.PolyVec) (o : commit.Opening) : Result Bool :=
  commit.verify_weak pp u o

-- The `ℓ₂²` norm is `u128`-valued, and that is load-bearing rather than
-- defensive: one centered coefficient can reach `q/2`, so a `u64` accumulator
-- would overflow -- i.e. *fail* in this model -- on inputs the verifier is
-- supposed to reject rather than crash on.
example (a : ring.Rq) : Result Std.U128 := commit.l2_norm_sq a
example : params.BETA_SQ.val = 8192 := by simp [params.BETA_SQ]

/-! ## 3. The specification side is reachable, and agrees on the ring degree

The point of this section is not the mathematics -- `powTwoCyclotomic_natDegree`
is ArkLib's theorem and is proved there -- but that this package can *see* it.
The ArkLib dependency is the riskiest edge of the build (a Lean/Mathlib pin
shared with aeneas, resolved from a different repository), so the scaffold states
one fact that fails to compile if that edge is broken.

Kept generic in the coefficient ring `R`. Instantiating at `ZMod q` would need
`Fact (Nat.Prime q)` plus `BEq`/`LawfulBEq` instances that ArkLib's own
statements take as explicit parameters, and supplying them is the gadget layer's
job, not the scaffold's. -/

-- The ring this crate fixes -- degree `RING_DEGREE = 64` -- is the degree ArkLib's
-- power-of-two cyclotomic modulus has at `α = RING_LOG_DEGREE = 6`. This is the
-- one line that ties `params.rs` to the specification rather than to itself.
example {R : Type} [Field R] [BEq R] [LawfulBEq R] :
    (powTwoCyclotomic (R := R) params.RING_LOG_DEGREE.val).φ.natDegree
      = params.RING_DEGREE.val := by
  rw [powTwoCyclotomic_natDegree]
  simp [params.RING_LOG_DEGREE, params.RING_DEGREE]

-- The conductor is `2^(α+1)`, i.e. the modulus really is the `128`th cyclotomic
-- polynomial at our `α` -- recorded because the Hachi norm bounds are stated
-- about `X^{2^α} + 1` specifically and would not hold of another modulus.
example {R : Type} [Field R] [BEq R] [LawfulBEq R] :
    (powTwoCyclotomic (R := R) params.RING_LOG_DEGREE.val).conductor = 128 := by
  simp [powTwoCyclotomic, params.RING_LOG_DEGREE]

/-! ## 4. Axiom audit

One `#print axioms` line per headline spec. This is how a reader confirms that no
`sorryAx` hides under a `_spec` -- and, given § 2, that no stray `axiom` from an
un-whitelisted dependency crept in either.

`make build` greps the build log for `sorryAx`, so a `sorry` reached from any line
printed here is a build failure rather than a silent debt. The expected output is
the three Lean kernel axioms and nothing else: `propext`, `Classical.choice`,
`Quot.sound`, which are the ones the README's trusted computing base names.

What is here: the base field (`lean/Field.lean`), and the whole coefficient level of
the ring (`lean/Ring.lean`), `mul` included. What is not: everything about `Rq Φ`,
`linalg`, `gadget` and `commit` -- those are stated in `lean-wip/` and not proved, and
each adds its `#print axioms` line here as it lands, which is step 3 of the promotion
procedure in `lean-wip/README.md`. -/

#print axioms HachiEquiv.Field.fp_add_spec
#print axioms HachiEquiv.Field.fp_sub_spec
#print axioms HachiEquiv.Field.fp_mul_spec
#print axioms HachiEquiv.Field.fp_neg_spec
#print axioms HachiEquiv.Field.fp_new_spec
#print axioms HachiEquiv.Field.toK_inj_of_Red

-- The ring layer, at the coefficient level (`lean/Ring.lean`): each operation
-- total, length-preserving, and coefficientwise equal to `ZMod q` arithmetic.
-- `mul` is the negacyclic convolution, so its coefficientwise statement is `negConv`:
-- the `k`-th antidiagonal of the raw product minus its `(N + k)`-th, which is
-- `(a * b) mod (X^N + 1)` written out.
#print axioms HachiEquiv.Ring.zero_spec
#print axioms HachiEquiv.Ring.add_spec
#print axioms HachiEquiv.Ring.sub_spec
#print axioms HachiEquiv.Ring.neg_spec
#print axioms HachiEquiv.Ring.scalar_mul_spec
#print axioms HachiEquiv.Ring.mul_spec

end HachiEquiv.Check
