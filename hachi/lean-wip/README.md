# `lean-wip/` — the staging area for statements that are not proved yet

**Current debt:** `Ext.lean`, the `Ext4` extension-field layer ported from
cpoly's own equivalence development, eight `sorry`s where the upstream proof
scripts did not survive the Lean v4.32 → v4.33.1 gap (the statements are about
identical extracted code and were proved upstream). Everything earlier that
passed through here has been promoted: the
representation bridge (`lean/RqBridge.lean`), the scheme layer
(`lean/Scheme.lean`), the scheme-gap statements (`SchemeGaps.lean`, folded
into `lean/Scheme.lean` beside their siblings), the multilinear evaluation
layer (`lean/EvalSplit.lean`, proved by Aristotle session `cc7674ce`), and, on
2026-09-04, Stage 3's first two targets: the balanced digit layer
(`lean/Balanced.lean`, Aristotle session `58843236`, nine obligations to zero)
and the QuadEval fold (`lean/QuadEval.lean`, Aristotle session `14b9bf77`,
eight obligations to zero), and, on 2026-09-08, target 3's full ring-switch link
(`lean/RingSwitch.lean`, Aristotle sessions `8d26c89e` and `90c5c852`, six
obligations to zero -- the second session after a Rust fix removed the flat
index the first one had to hypothesise around). The audited library now covers the base field, both
levels of the ring, `linalg`/`gadget`/`commit` up to `honest_verifies_full` —
perfect correctness of the extracted scheme at its top-level API,
`commit::verify` itself — the `evalsplit` module against ArkLib's split
evaluation, the balanced committer (`commit_balanced_spec`: the honest Hachi
commitment, `Hachi.commit`), and the QuadEval fold's `z`-side gadget, carrier,
`tensorG1` and Eq. (20) decisions, and the ring-switch lift, commitment and
shortness decisions. `lean/Check.lean` § 4 prints the axiom
dependencies of all ninety-nine headline specs, and they come out as the three
Lean kernel axioms and nothing else.

Two things the QuadEval passage through here established, worth keeping:

* a wip file **can** import a promoted file — `QuadEval.lean` imported
  `Balanced` the day the latter was promoted — but not another wip file (see
  "Working here" below), so two staged files at once still means promoting the
  lower one first;
* some of its statements are **iffs** rather than equalities, because ArkLib
  states `InSb` and `vecInSb` as `Prop`s where the Rust returns a `Bool`, so the
  obligation is "the decision procedure decides the proposition".
  ⊗ This bullet used to name `relOut` and `paperRelOut` here too. It was wrong:
  neither `quadeval::rel_out` nor `quadeval::paper_rel_out` is specified
  anywhere, and the theorem called `paper_rel_out_implies_rel_out_spec` is about
  `quadeval.vec_in_sb`'s norm implication rather than either of them. Corrected
  2026-09-08, when `make spec-check` was written and reported them owed. That shape is not in the Stage 2 scoping document's erasure catalogue;
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

**Second staged file (2026-09-08):** `ZeroCheck.lean`, twenty-four statements
covering target 4's zero-check link (sixteen `zerocheck` items), the three
`ringswitch` items the α side introduced (`c_eval_at`, `c_eval_at_modulus`,
`RlinStatement`) and target 6's four `endpiece` items. It imports `Ext.lean`,
which is the case this README's "Working here" warns about, so it is checked
with the `LEAN_PATH` detour:

```sh
cd hachi
lake env lean -o /tmp/wiplean/Ext.olean lean-wip/Ext.lean
LEAN_PATH="$(lake env printenv LEAN_PATH):/tmp/wiplean" lake env lean lean-wip/ZeroCheck.lean
```

Zero errors, twenty-four `sorry`s. Promotion order is forced: `Ext.lean` first
(it is the lower layer), then `ZeroCheck.lean`.

**Third staged file (2026-09-09):** `QuadEvalProtocol.lean`, eleven statements
closing target 2's statement debt -- the three QuadEval carriers
(`PublicParamsD`, `QuadEvalStatement`, `QuadEvalResponse`), the two gadget-level
helpers (`carrierDecomp`, `carrierCommit`, plus `jMatrix` applied to `ẑ`), the
honest prover's three functions (`honestZ`, `honestComputeV`,
`honestComputeResp`) and the two output relations (`relOut`, `paperRelOut`).

It is the one staged file that needs **no `LEAN_PATH` detour**, because it
imports only the promoted `QuadEval.lean`:

```sh
cd hachi
lake build
lake env lean lean-wip/QuadEvalProtocol.lean
```

Zero errors, eleven `sorry`s. It is also, for the same reason, the only proof
work currently **not** gated on `Ext.lean`: it rests on a promoted file, so it
can be proved and promoted while the extension-field layer is still red.

Two things in it worth knowing:

* `toChals` takes the `ℓ₁` bound as an **argument**, because
  `ShortChallenge Φ ω` is the subtype `{c // ‖c‖₁ ≤ ω}`
  (`QuadEval/Reduction.lean:151`). That bound then appears as a hypothesis on
  the two relation specs. It is not a weakening: `relOut` checks no challenge
  norm precisely *because* the type carries it (`:148-150`), so a faithful
  statement about the extracted verifier -- which also checks none -- has to say
  the challenges are short somewhere, and this is where.
* both relation specs are **iffs**, the third instance of the shape this README
  already records for `InSb`/`vecInSb`. `paperRelOut` is the strictly stronger
  check (`paperRelOut ⊆ relOut` under `β/2 ≤ γ`, i.e. `8 ≤ 15` here), so the two
  are not interchangeable and neither statement implies the other.

Three conventions in it worth knowing before touching it:

* every statement is against a **computable** ArkLib definition — the α side
  goes through `alphaDefect`, with the bridge to the noncomputable
  `hAlphaEvals` stated as its own obligation
  (`h_alpha_evals_eq_hAlphaEvals_spec`) rather than assumed;
* arities (`m₀`, `m₁`, `μ`, `n`) are arguments, so each statement is the generic
  ArkLib one at arbitrary width rather than an instantiation at `M_ZERO`;
* `end_piece_check_spec` takes `BEq`/`LawfulBEq` on the commitment carrier as
  instance *hypotheses*, which is ArkLib's own convention for `endPieceCheck`
  (`Composition.lean:287`) — `K.TCom` is a function type, so there is no
  instance to find, and the binders sit on the `.TCom` projection because
  instance search will not unfold it.
