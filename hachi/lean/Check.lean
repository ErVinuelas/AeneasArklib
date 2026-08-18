import Generated
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

There are no specs yet -- Workstream 0 built the scaffold and no operation of the
scheme is implemented. What this file audits today is the scaffold's three load-
bearing claims, each of which a later workstream would otherwise discover the
hard way:

1. the extracted parameters are the ones `src/params.rs` names, and they satisfy
   the side conditions the generic ArkLib statements carry as hypotheses;
2. the `cpoly` field layer arrives *transparently*, not as axioms -- the whole
   question Workstream 0 existed to settle;
3. the ArkLib specification side is reachable from this package at all, and the
   ring degree the Rust fixes is the degree ArkLib's modulus actually has.
-/

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

-- `Ext4` is the case a one-field newtype does not cover: a foreign struct with
-- four private fields. It survives as a real structure, with real projections and
-- a real constant.
example (a : cpoly.field.Ext4) : Std.U64 := a.c0
example : cpoly.field.Ext4.ZERO.c0 = 0#u64 := by
  simp [cpoly.field.Ext4.ZERO, cpoly.field.Fp.ZERO]

-- Deliberately *not* asserted here: that `add 1 2` evaluates to `ok 3`. It is
-- true, but `simp` and `decide` do not get there on their own -- the checked
-- `U64` arithmetic needs Aeneas's `progress`/`scalar_tac` machinery, which
-- arrives with the first real spec. The structural equality above is the claim
-- that matters for § 2 anyway: it is the one an `axiom` cannot satisfy.

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

Empty by construction: there is no headline spec yet. Each equivalence proof adds
one `#print axioms` line here, which is how a reader confirms that no `sorryAx`
hides under a `_spec` -- and, given § 2, that no stray `axiom` from an
un-whitelisted dependency crept in either.

`make build` greps the build log for `sorryAx`, so a `sorry` reached from any
line printed here is a build failure rather than a silent debt. -/

end HachiEquiv.Check
