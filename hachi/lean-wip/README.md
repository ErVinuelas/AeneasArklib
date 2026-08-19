# `lean-wip/` — the equivalence obligations that are not proved yet

**Everything here typechecks; nothing here is proved.** Those are different claims,
and keeping them apart is the point of this directory.

* *Typechecks*: `lake env lean` elaborates both files against the pinned ArkLib
  specification with no errors. So every statement is well-formed at this crate's
  parameters, and each one is about the specification's own definitions rather than
  a paraphrase of them — a mistranslation would show up here as a type error.
* *Not proved*: each theorem's proof is `sorry` (37 of them at the time of
  writing). That is why this directory is **not** a source root of the `HachiEquiv`
  Lake library (see `hachi/lakefile.lean`): `lake build` does not look at it, so
  `make build`'s "no errors, no `sorry`" cannot be diluted by anything here. Hard
  rule 5 of this project is that no `sorry` may sit anywhere `Check.lean` reaches.

What *is* proved lives in `lean/` and is audited: the base field
(`lean/Field.lean`) and the coefficient level of the ring (`lean/Ring.lean`,
everything but `mul`). `lean/Check.lean` § 4 prints the axiom dependencies of each,
and they come out as the three Lean kernel axioms and nothing else.

## The files

**`RqBridge.lean`** — the bridge from the proved coefficient layer to ArkLib's
`CyclotomicModulus.Rq Φ`, plus one obligation per `src/ring.rs` operation.

Its *definitions* are proved, and they are the useful part: `toRq` (a coefficient
vector read as an element of `Rq Φ`), `toRq_coeff` (its coefficients, via ArkLib's
`ofFinCoeff_coeff`), and `toRq_eq_iff` (two represented elements are equal exactly
when their coefficients agree below `N`). Given those, most of the `sorry`s below
them are short: `add_spec` is `Ring.add_spec` plus ArkLib's `add_val`. The
exception is `mul_spec`, whose plan is written out at the end of the file.

**`Scheme.lean`** — the same for `linalg`, `gadget` and `commit`, including the
structure bridges (`toParams`, `toDecompSpec`, `toOpening`) that let
`verify_weak_spec` be stated against the specification's own `verify_weak` rather
than a restatement of its checks.

## Two statements worth reading before they are proved

* `gadget_mul_spec` says the Rust's per-block digit sum equals ArkLib's `gadgetMul`,
  which is a *matrix* product. They agree by the specification's own
  `gadgetMul_apply` — so that lemma is a load-bearing step of the proof, not an
  optimization footnote, and it is what licenses `gadget_mul` wherever the
  specification writes `Simple.commit Φ (gadgetMatrix …)`.
* `verify_weak_spec` is an *equality of decisions*, not an implication. A verifier
  that rejected everything would satisfy the accepting direction; only the equality
  makes the rejection paths part of the claim.

## Promoting a file out of here

1. finish its proofs, and check with `lake env lean lean-wip/<File>.lean` that there
   are no errors *and* no `declaration uses 'sorry'` warnings;
2. move it to `lean/<File>.lean`;
3. add its module name to `roots` in `hachi/lakefile.lean` (Lake counts a module as
   part of a library only when a root is a prefix of its name, so an unlisted file
   is silently not built) **and** `import` it from `lean/Check.lean`, without which
   its constants are unknown there;
4. add a `#print axioms` line per headline spec to `lean/Check.lean` § 4 — that is
   what makes a `sorryAx` a build failure rather than a silent debt;
5. re-run `make build` and confirm both halves: no errors, and no `sorry`.

## Working here

`lean-wip` is not on the module search path, so a file that imports another one in
this directory needs it built first:

```sh
cd hachi
lake env lean -o /tmp/wiplib/RqBridge.olean lean-wip/RqBridge.lean
LEAN_PATH="$(lake env printenv LEAN_PATH):/tmp/wiplib" lake env lean lean-wip/Scheme.lean
```

Set `autoImplicit false` in every file here. Both files needed it: with it on, an
unknown identifier in a binder becomes an implicitly bound variable, so a missing
`open` turns a statement about `q` into a statement about *any* natural number.
That is how a spec silently becomes vacuous, and it has already happened once in
this repository (NOTES.md § "The model contains what the crate reaches").
