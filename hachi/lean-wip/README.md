# `lean-wip/` — the equivalence obligations that are not proved yet

**Everything here typechecks; nothing here is proved.** Typechecking and proving are
different claims, and keeping them apart is the point of this directory.

* *Typechecks*: `lake env lean` elaborates the file against the pinned ArkLib
  specification with no errors. So every statement is well-formed at this crate's
  parameters, and each one is about the specification's own definitions rather than
  a paraphrase of them — a mistranslation would show up here as a type error.
* *Not proved*: 23 `sorry`s remain, all in `Scheme.lean`. That is why this directory
  is **not** a source root of the `HachiEquiv` Lake library (see `hachi/lakefile.lean`):
  `lake build` does not look at it, so `make build`'s "no errors, no `sorry`" cannot be
  diluted by anything here. Hard rule 5 of this project is that no `sorry` may sit
  anywhere `Check.lean` reaches.

What is proved *and audited* lives in `lean/`: the base field (`lean/Field.lean`), the
whole coefficient level of the ring (`lean/Ring.lean`, `mul` included — all thirteen
operations), and those thirteen lifted to ArkLib's `Rq Φ` (`lean/RqBridge.lean`, promoted
out of this directory by the procedure below). `lean/Check.lean` § 4 prints the axiom
dependencies of each, and they come out as the three Lean kernel axioms and nothing else.

## The file

**`Scheme.lean`** — the obligations for `linalg`, `gadget` and `commit`, including the
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

`Scheme.lean`'s `import RqBridge` now resolves through the built library (RqBridge
was promoted), so checking it is just:

```sh
cd hachi
lake build   # so the library's .oleans are current
lake env lean lean-wip/Scheme.lean
```

(Before the promotion this needed a `/tmp/wiplib` `LEAN_PATH` detour to build
`RqBridge.olean` by hand — a file here importing another file here still would.)

Set `autoImplicit false` in every file here. Both original files needed it: with it on, an
unknown identifier in a binder becomes an implicitly bound variable, so a missing
`open` turns a statement about `q` into a statement about *any* natural number.
That is how a spec silently becomes vacuous, and it has already happened once in
this repository (NOTES.md § "The model contains what the crate reaches").
