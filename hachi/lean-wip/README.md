# `lean-wip/` — the staging area for statements that are not proved yet

**Currently empty.** Everything that passed through here has been promoted: the
representation bridge (`lean/RqBridge.lean`), the scheme layer
(`lean/Scheme.lean`), the scheme-gap statements (`SchemeGaps.lean`, folded
into `lean/Scheme.lean` beside their siblings), the multilinear evaluation
layer (`lean/EvalSplit.lean`, proved by Aristotle session `cc7674ce`), and, on
2026-09-04, Stage 3's first two targets: the balanced digit layer
(`lean/Balanced.lean`, Aristotle session `58843236`, nine obligations to zero)
and the QuadEval fold (`lean/QuadEval.lean`, Aristotle session `14b9bf77`,
eight obligations to zero). The audited library now covers the base field, both
levels of the ring, `linalg`/`gadget`/`commit` up to `honest_verifies_full` —
perfect correctness of the extracted scheme at its top-level API,
`commit::verify` itself — the `evalsplit` module against ArkLib's split
evaluation, the balanced committer (`commit_balanced_spec`: the honest Hachi
commitment, `Hachi.commit`), and the QuadEval fold's `z`-side gadget, carrier,
`tensorG1` and Eq. (20) decisions. `lean/Check.lean` § 4 prints the axiom
dependencies of all ninety-one headline specs, and they come out as the three
Lean kernel axioms and nothing else.

Two things the QuadEval passage through here established, worth keeping:

* a wip file **can** import a promoted file — `QuadEval.lean` imported
  `Balanced` the day the latter was promoted — but not another wip file (see
  "Working here" below), so two staged files at once still means promoting the
  lower one first;
* four of its statements are **iffs** rather than equalities, because ArkLib
  states `InSb`, `vecInSb`, `relOut` and `paperRelOut` as `Prop`s where the Rust
  returns a `Bool`, so the obligation is "the decision procedure decides the
  proposition". That shape is not in `STAGE2_SCOPING.md`'s erasure catalogue;
  it proved low-risk, and `lean/QuadEval.lean`'s header records how.

The directory stays because the distinction it exists for still matters, and the
next operation to be specified will want it.

## What the distinction is

Typechecking and proving are different claims, and keeping them in different
directories is the point of this one.

* *Typechecks*: `lake env lean` elaborates the file against the pinned ArkLib
  specification with no errors. So every statement is well-formed at this crate's
  parameters, and each one is about the specification's own definitions rather than
  a paraphrase of them — a mistranslation would show up here as a type error.
* *Not proved*: `sorry`s remain. That is why this directory is **not** a source root
  of the `HachiEquiv` Lake library (see `hachi/lakefile.lean`): `lake build` does not
  look at it, so `make build`'s "no errors, no `sorry`" cannot be diluted by anything
  here. Hard rule 5 of this project is that no `sorry` may sit anywhere `Check.lean`
  reaches — a file staged here is outside that reach by construction, and the moment
  it is promoted it is inside it.

A file only earns `lean/` by being proved, and once there it is *checked*: a change
under it — to a lower layer, to the ArkLib pin — becomes a build failure rather than
a silent break.

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

A new file importing only the built library needs no `LEAN_PATH` detour:

```sh
cd hachi
lake build   # so the library's .oleans are current
lake env lean lean-wip/<File>.lean
```

A file here importing *another* file here still would — `lake build` produces no
`.olean` for anything in this directory, so the importer cannot resolve it. Two
staged files at once therefore means building the lower one by hand into a scratch
`LEAN_PATH`; one staged file at a time avoids the problem entirely, and is how both
promotions so far were done.

Set `autoImplicit false` in every file here. Both promoted files needed it: with it
on, an unknown identifier in a binder becomes an implicitly bound variable, so a
missing `open` turns a statement about `q` into a statement about *any* natural
number. That is how a spec silently becomes vacuous, and it has already happened
once in this repository (NOTES.md § "The model contains what the crate reaches").
