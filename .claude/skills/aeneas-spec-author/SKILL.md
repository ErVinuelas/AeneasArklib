---
name: aeneas-spec-author
description: Stating the ⦃·⦄ spec layer for Aeneas-extracted functions in hachi/lean and hachi/lean-wip — the two-level split (coefficient level against ZMod q, then the lift to ArkLib's Rq Φ), representation functions and invariants, headline triples stated against the ArkLib definition instantiated at params.rs, loop-spec decomposition, typechecked sorry stubs for prove-sorry, Check.lean § 4 audit lines; use when a new operation needs specs (after op-genesis/extraction), when an accepted champion regenerates Generated.lean and the old specs go stale, or whenever a `_spec` theorem must be written or restated
---

# Authoring Aeneas Specs

For the **statement layer** only: what the `_spec` theorems in `hachi/lean/`
and `hachi/lean-wip/` claim, not how they are proved (`prove-sorry` proves;
this skill hands it typechecked `sorry` stubs). Read this **before** writing
or repairing any `_spec`. The triple form `m ⦃ r => post r ⦄` and how it
composes are documented in `hachi/lean/Field.lean`'s header; the translation
model and `@[step]` machinery in the `aeneas-lean-core` skill; the loop-spec
template in the `proof-patterns` skill. The proved files `lean/Field.lean`
and `lean/Ring.lean` are the style exemplars — a new spec should read as if
it always lived beside them — and `lean-wip/RqBridge.lean` is the exemplar
for the lift. When the representation-function pattern below stops fitting,
read the `aeneas-equivalence-bridges` skill before inventing anything.

## Invocation

**Human invocation:** start with the bare command `/aeneas-spec-author`; do
not put an operation on the command line. Ask first: **“Which extracted
operation should I specify, and against which ArkLib definition?”** Resolve
the named original definition and its extracted counterpart, using the
current conversation when it already identifies them. Ask one follow-up only
if the destination Lean module or reference definition remains ambiguous,
then confirm the resolved request before writing stubs. The command authors
theorem statements only; it leaves their bodies as typechecked `sorry`s for
`/prove-sorry`.

**Agent invocation:** accept this complete named request:

```yaml
agent_request:
  target: ArkLib.<fully-qualified-definition>
  trigger: onboarding | regeneration
```

Validate that `target` resolves in the pinned copy at
`hachi/.lake/packages/Arklib/` and that `Generated.lean` is freshly extracted
before work starts. If either field is missing or invalid, return the missing
field to the invoking agent; do not turn an agent-to-agent call into a
question for the human.

## The one rule: the headline spec states the ArkLib definition

Every headline triple has the shape

```
theorem op_spec (inputs …) (hinv : invariants …) :
    extracted_op inputs ⦃ r => Inv r ∧ rep r = ArkLib.<op> (rep inputs) ⦄
```

with an `ArkLib.*` reference name on the right-hand side — never an
optimized variant (`Foo.opt`), never a description of what the extracted
code structurally does. When `perf-loop` lands a faster champion, **the
statement does not move**: the proof reroutes through the variant's
`Foo.opt_eq_spec` lemma (the opt-contract, see the `lean-opt` skill) to land
on the unchanged right-hand side. The trusted statement is what readers and
downstream proofs consume; if it tracked champions it would churn on every
accept, and the `Check.lean` § 4 audit prints would stop pinning anything.

**Two things are local and neither is an exception to the rule.**

*The statement is instantiated, not generic.* ArkLib is generic in all four
of `(q, α, b, digits)` and pins none of them; this crate is concrete, with
every parameter a `const` in `hachi/src/params.rs`. So each headline
statement instantiates a generic ArkLib statement at those values —
`RqBridge.lean` is the pattern: `abbrev α : ℕ := 6`,
`abbrev Φ : CyclotomicModulus (ZMod q) := Ajtai.InnerOuter.hachiModulus q α`,
and the `Fact (Nat.Prime q)` / `NeZero q` / `BEq`+`LawfulBEq` instances
supplied once at the top. `lean/Check.lean` § 1 is what proves those
instantiations *legal* (`1 < b`, `q ≤ b ^ digits`, `b - 1 ≤ q/2`,
`q % 8 = 5`, `κ² < q`), so a new parameter side condition gets a line there
before any spec leans on it.

*The development splits at the coefficient level.* `lean/Ring.lean` states
each operation total, length-preserving and coefficientwise correct against
`ZMod q` arithmetic (`coeffK`, `negConv`), importing `Generated` and `Field`
and **no ArkLib at all**; `lean-wip/RqBridge.lean` lifts each of those to
`Rq Φ` via `toRq`. That is deliberate — the hard half is checkable against a
tiny import surface and could therefore be audited before the bridge existed
(`NOTES.md` § "Two things that made the proofs go through"). A
coefficient-level spec with no `ZMod q`-side ArkLib name is therefore **not**
a violation of the one rule; it is the lower half of a two-part statement.
What *is* a violation is stopping there: an operation whose coefficient spec
has no bridge statement above it is not specified against the specification.
Author both halves, and say in the deliverable which of the two is proved.

## The procedure

1. **Extract first, then author.** Specs are stated only against a freshly
   extracted, determinism-checked `Generated.lean` (the `aeneas-extract`
   skill; even comment-only Rust edits shift `Source` spans and regenerate
   the file, so a stale copy is easy to hold without knowing). The cheap
   probe is `make extract` followed by
   `git diff -- hachi/lean/Generated.lean`; a session that cannot run the
   extraction treats the file as unverified and says so in its deliverable.
2. **Read the extracted name off `Generated.lean`; do not predict it.**
   Most of this crate is inherent methods, so the names are already
   readable — `ring.Rq.add`, `ring.Rq.add_loop`, `linalg.PolyVec.dot`,
   `gadget.digit_at`, `commit.verify_weak` — and the house style states
   specs about them directly, with **no `abbrev` alias layer**. There are
   currently zero `Shared<n><T>` names in the model. The only mangled names
   are the four `cpoly` operator impls
   (`cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add`, …), which `Field.lean`
   also writes out in full; `Check.lean` § 2 pins their **bodies** with
   structural `example`s, which is stronger than a name `rfl` and is the
   assertion an `axiom` could not satisfy. If a by-reference operator impl
   is ever added to `hachi`, the `Shared<n><T>` mangling returns and with it
   the alias-plus-`rfl`-pin discipline — and `Check.lean` has no
   alias-pin section, so the pins need one added.
3. **Representation layer before any statement.** Reuse the house
   functions, bottom-up: `toK` / `Red` on field words (`lean/Field.lean`),
   `coeffK` / `Wf` on coefficient vectors (`lean/Ring.lean`), `toRq`
   (`lean-wip/RqBridge.lean`), `toVec` / `WfVec` / `toMat` / `WfMat`
   (`lean-wip/Scheme.lean`). A genuinely new extracted type gets, in this
   order and before its first spec: a representation **function**, its
   invariant predicate, the coefficient kit (`coeffK_of_lt`,
   `coeffK_of_ge`, `coeffK_append_lt`, `coeffK_append_eq`, `coeffK_set`,
   `Red_set`, `Red_getElem` are the template — the `append` pair is the
   whole of the `push` reasoning and `coeffK_set` the whole of the
   `index_mut` reasoning), and `Check.lean` entries showing the invariant is
   not `True` and the function does not collapse (§ 2b's term-position
   ascriptions for shape, § 1's `example`s for legality; the non-degeneracy
   witnesses in the proved files are `toK_inj_of_Red` and `toRq_eq_iff`).
   If no total representation function can exist, stop and read
   `aeneas-equivalence-bridges`.
4. **Hypotheses: invariants plus earned value bounds, nothing else.** Each
   input contributes its representation invariant, and here that invariant
   is what makes the triple *total*: `Wf a` gives `Red` on every word the
   loop reads, which is what discharges the `u64` no-overflow obligation
   inside `Fp::add` (`add_spec`'s docstring says exactly this). A *value*
   hypothesis is admitted only when a concrete fail point in the generated
   code forces it — walk every checked scalar op, `Vec.push`, and index on
   every path. Recognize the fail points that discharge under the
   invariants alone and do NOT hypothesize for them: `Rq::mul`'s `i + j`,
   because both are below `N = 64` (`ring.rs` says so); a `Vec.push` whose
   output length is bounded by an input's (the `Vec` type itself carries
   `≤ Usize.max`); a counter's checked `i + 1` under the loop guard
   `i < n`; guarded indexing pinned to `Vec.len`; `Vec.len` / `Vec.new`,
   which are pure. The canonical *earned* bound in this repository is
   `dot_spec`'s equal-length hypothesis: the Rust takes the shorter of the
   two vectors, which is what makes it total, and the specification's `dot`
   is only defined when the lengths match. The theorem's docstring records
   the walk either way: for a value bound, the fail point and why the bound
   is minimal; when no bound is needed, one or two lines saying why the walk
   closes (this is what a reviewer disputing a *missing* hypothesis reads).
   Constructing the disproof and gating any weakening is `prove-sorry`
   Phase 1's job — the author's job is to draft the minimal set and leave
   the justification trail.

   A related trap: a *type* that should have been an invariant. `u128` in
   `commit::l2_norm_sq` is not defensive — one centered coefficient reaches
   `q/2`, so a `u64` accumulator would make the extracted verifier **fail**
   on exactly the long inputs it is supposed to reject, and the totality
   half of its spec would simply be false. When the honest spec needs a
   bound the caller cannot supply, the Rust is wrong, not the statement.
5. **Postcondition: success, invariant, commutation.** The triple is
   `Aeneas.Std.spec`, definitionally `∃ r, m = ok r ∧ post r` — total
   correctness, so success is asserted by the form itself; the postcondition
   states invariant preservation and the `rep`-commutation equality, with
   the **named** ArkLib def on the right (`ArkLib.Lattices.dot`,
   `PolyVec.flattenBlocks`, `gadgetMul`), not the instance notation. A
   caller must be able to chain the theorem, so whatever the proof needs
   about inputs must be reestablished about outputs (a precondition without
   the matching postcondition breaks self-composition) — but add an explicit
   clause only when it is *not derivable* from the commutation equality.
   And **decision procedures are stated as equalities of decisions, never
   as implications**: `equals_spec`, `is_zero_spec` and `verify_weak_spec`
   are `↔` / `=` because a verifier that rejected everything would satisfy
   the accepting direction alone. The rejection paths are the half a broken
   implementation still passes, and `Simple.verify` rests on them.
6. **One loop spec per generated `*_loop`.** Nested loops are named
   positionally (`mul_loop0`, `mul_loop1`, `mul_loop1_loop0`) and that
   naming is the proof plan. Stated general in the loop state, proved by
   `loop.spec_decr_nat` with measure `n - i` and an invariant of the house
   shape — counter bounded, accumulator length equals the counter, entries
   reduced, coefficients so far correct — shaped so the headline spec
   composes via `spec_mono`. Where Aeneas threads a borrowed operand
   through the state (`add_loop`, `sub_loop` carry `rhs`), the invariant
   needs a conjunct saying that component never moves. Keep the loop-state
   components last so the headline instantiates them. Pure mathematics is
   factored into plain defs with step lemmas, kept free of the monadic
   plumbing: `contrib`, `rowsSum` and `negConv` in `Ring.lean` are the
   template, and `negConv` is what makes `mul_spec`'s right-hand side a
   statement rather than a description of the loop.
7. **`@[step]` policy, per the proved files:** the base-field specs in
   `Field.lean` are `@[step]`, which is what lets the ring layer walk
   through generated code without naming them; everything proved via a loop
   spec — and every headline operation spec in `Ring.lean` — is a plain
   theorem, composed explicitly. `bind_ok_id` is `@[simp]`; the
   parameter-value lemmas (`params_RING_DEGREE_val`, `cpoly_P_val`) are
   `@[simp, scalar_tac_simps]` so the generated arithmetic side conditions
   can use them.
8. **Deliver stubs, and put them where a `sorry` is legal.** This is the
   sharpest local difference: `make build` **fails** on any declaration
   under `hachi/lean/` that uses `sorry`, and hard rule 5 of the project is
   that no `sorry` may sit anywhere `Check.lean` reaches. So new statements
   are born in **`hachi/lean-wip/`**, which is deliberately not a Lake root
   and not audited — that is what the directory is for, and
   `hachi/lean-wip/README.md` is its contract. The gate is mechanical: from
   `hachi/`, `lake env lean lean-wip/<File>.lean` (no Lake lock taken);
   success is zero `error:` lines, with `declaration uses 'sorry'` warnings
   expected on every stub. A wip file importing another wip file needs it
   built first — `lean-wip/README.md` § "Working here" has the `LEAN_PATH`
   recipe. Set `set_option autoImplicit false` in every file; it is not
   style here (see the failure modes).
9. **Promotion is a deliberate step with the audit attached.** Moving a
   finished file from `lean-wip/` into `lean/` is the five-step procedure in
   `hachi/lean-wip/README.md`: prove it out, move it, add its module to
   `roots` in `hachi/lakefile.lean` **and** `import` it from
   `lean/Check.lean`, add one `#print axioms <full name>` line per headline
   spec to `Check.lean` § 4, then `make build` and confirm both halves (no
   errors, no `sorry`). The expected § 4 output is
   `[propext, Classical.choice, Quot.sound]` and nothing else — that is
   what makes a hidden `sorryAx` build-visible, and it is also the check
   that no stray `axiom` from an un-whitelisted `cpoly` item crept in.
   Until promotion, "proved" means less than it sounds: nothing re-checks
   the file, so a change to `lean/Ring.lean` can break it silently.
   `lean-wip/RqBridge.lean` is exactly in that state today.
10. **Champion re-spec** (accepted optimization, regenerated
    `Generated.lean`): headline statement text is carried over verbatim (the
    one rule); extracted names are re-read off `Generated.lean`, since a
    changed impl shape can re-mangle them; the *loop* specs are new and
    follow the opt definition's structure (a Karatsuba champion gets
    recursion-shaped sub-specs, not the schoolbook loops'), with
    `Foo.opt_eq_spec` splicing the proof onto the unchanged right-hand side.
    `hachi/lean/Opt.lean` **does not exist yet**: the first `lean-opt` run
    creates it and must add `Opt` to `roots` in `hachi/lakefile.lean`, or it
    is silently not built. Any new hypothesis on a carried-over headline is
    a weakening and goes through `prove-sorry`'s approval gate.

## Failure modes with teeth

* **A spec over an axiomatized `cpoly` symbol.** If `make extract` ever runs
  without `--include 'cpoly::_'`, `Fp` becomes an uninterpreted type with an
  uninterpreted `+`, and every spec above it quantifies over a symbol that
  says nothing — provable, green, and empty. `Check.lean` § 2 exists to make
  that a build failure; whitelist *completeness* is in the repository's
  trusted computing base because nothing checks it. Before authoring, know
  that `cpoly.field.Fp = Std.U64` still holds.
* **`autoImplicit` turning a statement into a statement about nothing.** It
  has bitten twice in this repository. In `Check.lean`, an assertion about
  `Ext4` outlived the item and kept compiling as a claim about a universally
  quantified nothing. In `Scheme.lean`, a missing `open HachiEquiv.Field`
  turned `q`, `Red` and `toK` into auto-bound implicits, so a side condition
  became `⊢ q ≤ 4294967296` for an *arbitrary* `q` — unprovable, which was
  the lucky case; a statement needing no side condition would have compiled
  as a theorem about every natural number. `set_option autoImplicit false`
  in every file, and prefer term-position ascriptions in the audit, since a
  name mentioned only in a binder is not pinned by compiling.
* **A hypothesis added for provability.** Every hypothesis weakens the
  theorem for every caller, and "add the bound, move on" is how a spec
  quietly stops covering real inputs. The gate is a concrete fail point in
  the generated code, machine-checked when disputed.
* **A true-but-vacuous spec.** A triple can typecheck and prove while
  claiming nothing — degenerate parameters, invariant secretly `True`,
  collapsed representation. `Check.lean` is the countermeasure: § 1 for the
  parameters, § 2/§ 2b for the model's shape, § 3 for the specification
  being reachable and agreeing on the ring degree, § 4 for the axioms. A new
  representation layer without its non-degeneracy entries is not done.
* **Stating what the code does.** A postcondition that mirrors the extracted
  structure ("returns the vec built by this loop") proves easily and pins
  nothing. The right-hand side is the ArkLib reference operation, or — at
  the coefficient level — the `ZMod q` arithmetic that the bridge above
  turns into one. `gadget_mul_spec` is the exemplar of getting this right:
  ArkLib's `gadgetMul` is a *matrix* product while the Rust computes a
  per-block digit sum, and stating agreement with the matrix product is
  what makes the specification's own `gadgetMul_apply` a load-bearing step
  of the proof rather than a footnote.
* **A statement typechecking against the wrong `Fp`.** `cpoly.field.Fp`
  *is* `Std.U64` in Lean, so an arbitrary word and a reduced field element
  are the same type and nothing will complain. `Red` is the only thing that
  separates them, and it travels as a hypothesis because Aeneas cannot see
  Rust's privacy boundary. Check the pairing by hand.
* **Authoring against a stale `Generated.lean`.** A committed extraction can
  lag the Rust after comment-only edits (Source-span drift); specs written
  against it bind names and shapes that no longer exist. Triage lives in the
  `aeneas-extract` skill — re-extract, then author.
* **A missing import that reads like a hard problem.** `Fact (Nat.Prime q)`
  fails with a bare `⊢ Nat.Prime 4294967197` unless
  `Mathlib.Tactic.NormNum.Prime` is imported; ArkLib's imports do not reach
  norm_num's primality extension.

## Invariants to keep green

* Every headline `_spec`: right-hand side is an `ArkLib.*` name (or the
  `ZMod q` half of a two-part statement whose bridge carries one);
  hypotheses are representation invariants plus counterexample-earned value
  bounds only; every value bound carries its docstring justification.
* Every operation has **both** halves — coefficient level and `Rq Φ` lift —
  and the deliverable says which are proved, which typecheck, and which are
  neither.
* Every extracted name a spec mentions is read off `Generated.lean`, and
  anything mangled is pinned in `Check.lean`.
* Every promoted headline spec has its `#print axioms` line in
  `Check.lean` § 4, reporting exactly
  `[propext, Classical.choice, Quot.sound]`.
* Every file sets `autoImplicit false`.
* Stub files typecheck under `lake env lean` before `prove-sorry` launches.
* Loop specs compose: the headline proof is `spec_mono`/`spec_bind` over the
  stated sub-specs, never a monolith.
* A `sorry` in `hachi/lean/` never reaches main. Stubs live in
  `hachi/lean-wip/` until `verify-campaign` clears them and the promotion
  procedure moves them.
