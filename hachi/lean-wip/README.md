# `lean-wip/` — the staging area for statements that are not proved yet

**Current debt (2026-09-10): `Sumcheck.lean`**, target 5's paired sumcheck
(chain rows 6 and 8): twenty-four `sumcheck` statements plus the univariate
carrier they rest on (`toRaw`/`toUni`, ported from cpoly's own `Univariate.lean`
with every ported proof intact -- `zero`, `from_coeffs`, `trim`, `eval` and
both `Mul` impls). **0 errors, 32 `sorry`s** for the prover: the twenty-four
items and eight scaffolding lemmas (`toUni_eval`, the kernel identity, the two
degree lemmas, `cube_size`, the two weight identities). It imports only promoted files (`EndPiece`), so the
plain `lake env lean lean-wip/Sumcheck.lean` validates it. Beside it,
`Chain.lean` (2026-09-10): the two composed-chain rows -- `chain_verify` against
the composed verifier's verdict (`chainVerdict`: `verifyRounds`, then
`finalCheck` and `endPieceCheck`) and `chain_open` against the honest prover's
four wire messages -- **proved locally, 0 errors, 0 `sorry`s**, statements
unchanged. It imports `Sumcheck`, so it is the two-staged-files case: validate
it with the `LEAN_PATH` detour under "Working here", and promote `Sumcheck.lean`
first -- its two headline closures carry `sorryAx` only through Sumcheck's
still-open `honest_compute_g_spec` and `honest_round_messages_spec`. And
`LiftProver.lean` (2026-09-11): the honest lift prover's five statements
(`honest_lift_witness`, `c_quotient`, `c_row_sum` and the two private helpers),
0 errors, 5 `sorry`s, importing promoted files only. Everything before both has been promoted, and
the ones that landed last are Stage 3's targets 4 and 6 — `lean/ZeroCheck.lean`
(twenty-five headline specs) and `lean/EndPiece.lean` (four), Aristotle session
`2266ab16`, thirteen obligations to zero. `Check.lean` § 4 now prints **one
hundred and sixty** headline specs and they all come out as the three
Lean kernel axioms.

That is worth a note rather than a celebration: the next translated operation
puts debt back here, and the directory exists for that. The 2 items
`make spec-check` currently reports owed — the two `chain` rows — are
*unstated*, not unproved; when they are written they will be staged here first.

Everything earlier that passed through here has been promoted: the
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
shortness decisions. On 2026-09-09 two more were promoted together: the `Ext4`
extension-field layer (`lean/Ext.lean`, Aristotle session `63ebbc60`, eight
obligations to zero — its predecessor `be85dad4` returned non-compiling proofs,
and the difference was one bridging lemma between `ext4Params.d` and
`ext4Params.toExtensionParams.d`, definitionally equal and syntactically
distinct) and target 2's QuadEval protocol layer
(`lean/QuadEvalProtocol.lean`, session `982bd0af`, eleven obligations to zero
with no headline signature changed). `lean/Check.lean` § 4 prints the axiom
dependencies of all **one hundred and eighteen** headline specs, and they come
out as the three Lean kernel axioms and nothing else.

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
`LEAN_PATH`; one staged file at a time avoids the problem entirely. The detour has
been needed twice: `ZeroCheck.lean`/`EndPiece.lean` over the then-staged `Ext.lean`
(2026-09-09), and `Chain.lean` over the staged `Sumcheck.lean` (2026-09-10), whose
recipe is under "Fourth staged file" below.

Set `autoImplicit false` in every file here. Both promoted files needed it: with it
on, an unknown identifier in a binder becomes an implicitly bound variable, so a
missing `open` turns a statement about `q` into a statement about *any* natural
number. That is how a spec silently becomes vacuous, and it has already happened
once in this repository (NOTES.md § "The model contains what the crate reaches").

**Second staged file (2026-09-08):** `ZeroCheck.lean`, twenty-four statements
covering target 4's zero-check link (sixteen `zerocheck` items), the three
`ringswitch` items the α side introduced (`c_eval_at`, `c_eval_at_modulus`,
`RlinStatement`) and target 6's four `endpiece` items. It imports `Ext`, which **was** the case this
README's "Working here" warns about; since `Ext.lean`'s promotion on
2026-09-09 that import resolves from the built library and no detour is needed:

```sh
cd hachi
lake build
lake env lean lean-wip/ZeroCheck.lean
```

That promotion also fixed a real tooling failure. `aristotle_check.py`
validates a returned file with a plain `lake env lean`, which cannot build a
staged file that imports another staged file — and it refused session
`396eb25b`'s otherwise-good ZeroCheck proofs for exactly that reason
(NOTES.md § "`aristotle-check` cannot validate a wip file that imports a wip
file"). With `Ext` promoted the helper's own command is correct. The historical
detour, for the next time two files are staged at once:

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

**Fourth staged file (2026-09-09 → 2026-09-10):** `Rlin.lean`, thirteen
statements for the `R^lin` adapter (`gadget_transpose_mul`, the five dimension
abbrevs, `unflatten`, `tensor_g_matrix`, `stack`, `unstack`, `rlin_stmt`) and
the polynomial-level bridge (`PolyEvalStatement`, `to_quad_eval_statement`).
Imported only promoted files, so it needed no detour and the helper's own
validation worked on the return -- the first session this week that the helper
integrated without manual rescue. Four dimension specs were proved in place;
Aristotle `4d70f965` took the other nine to zero (`OUT_OF_BUDGET` with nothing
left open -- read `after_sorries`, not the status). Statement audit: fourteen
declarations compared hypothesis-by-hypothesis to the submitted baseline, none
changed; forty-one helper/loop lemmas added; one `set_option maxHeartbeats
2000000 in` on `rlin_stmt_spec`. Pre-flight lesson recorded in NOTES.md:
`make extract` before submitting -- the staged `Generated.lean` was stale
because a new module reorders the whole extraction.
