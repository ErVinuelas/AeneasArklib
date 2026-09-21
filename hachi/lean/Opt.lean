/-
`Opt.lean` -- the optimized variants and their `opt_eq_spec` lemmas: the umbrella.

The layer is split one part per `hachi/src` module it optimizes, and this file
imports them all so that `import Opt` (which `Check.lean` does) still brings the
whole layer. A new candidate's `Foo.opt` goes into the part for its module:

  OptFold.lean         the generic fold lemmas the parts share
  OptZeroCheck.lean    zerocheck, and the two ringswitch evaluations of the α side
  OptSumcheck.lean     sumcheck (imports OptZeroCheck for the base-field range factor)
  OptRingSwitch.lean   ringswitch::lift_commit
  OptEvalSplit.lean    evalsplit's two Rq-valued bases
  OptRingShort.lean    ring::mul_short_desc's algebra (MulShort)

Every part keeps `namespace HachiEquiv.Opt`, so no lemma's fully qualified name
moved in the split (the ledger's `opt:` fields and the `#print axioms` lines in
`Check.lean` § 4 are unchanged).
Every `Foo.opt` here is a pure Lean definition in the shape `lean-to-rust`
translates trivially (one fold = one `while` loop, explicit tuple state,
ascending indices), named after the **Rust item** it replaces, and paired in the
same change with a proved `opt_eq_spec` lemma against the ArkLib definition that
item mirrors. The lemma is stated between pure functions: at candidate time no
Rust exists, so the algebra is settled here and the Aeneas triple over the
extracted model (the outer verification pass) only has to route through it.
`Check.lean` § 4 prints the axioms of every lemma below, which is what makes a
`sorry` here a build failure rather than silent debt (`lean-opt` § "The
-/
import OptFold
import OptZeroCheck
import OptSumcheck
import OptRingSwitch
import OptEvalSplit
import OptRingShort
