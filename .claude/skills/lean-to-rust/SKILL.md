---
name: lean-to-rust
description: Translating a targeted Lean definition (ArkLib spec or optimized variant) into Rust in hachi/src — the conventions table and the trivial-grade checklist, idiomatic shell (newtypes, inherent methods, the cpoly field layer) around a trivial body (counter loops, named intermediates, bind-order-preserving straight-line code)
---

# Translating a Lean Definition to Rust

For turning a *targeted* Lean definition — the ArkLib spec itself, or an
optimized `Foo.opt` variant that already carries its `Foo.opt_eq_spec` lemma —
into Rust under `hachi/src/`. The target arrives from upstream (user,
`perf-loop`, a route skill); choosing it is not this skill's job. Read this
**before** writing the Rust, together with the brief from `arklib-analyze`;
the idiom/axiom boundary is owned by the `aeneas-idiomatic-rust` skill and the
post-landing obligations by `rust-bench` and `aeneas-extract`.

## The one rule: the translation must be provably boring

Translation distance is proof distance — that is the project's core bet. So
every place the Rust deviates from the Lean definition's syntactic structure
must be one of the enumerated moves in the checklist below, and anything
else — an algorithm change, a data-structure change, loop fusion, hoisting,
precomputation — is an *optimization*, and optimizations belong in Lean (an
`opt-*` rewrite with its equivalence lemma), never in the translator. When
you catch yourself improving the code while translating: stop, file the idea
for the Lean side, translate the definition you were given.

The checklist is a dial, not a doctrine: it moves on ledger evidence of proof
effort — how hard the equivalence proofs turn out to be — not on taste. This
repository's `logs/ledger.jsonl` is empty, so the dial starts where
AeneasCompPoly's proof-effort evidence left it; the first campaigns here are
what will move it.

## The field layer is a dependency, not a translation target

`Fp` (the Hachi prime `2^32 - 99`) and `Ext4` come from the `cpoly` crate and
are **never** reimplemented — that is a hard rule of the project
(`hachi/src/lib.rs`, README § "The field layer comes from cpoly"), and the
extraction depends on it: `make extract` passes `--include 'cpoly::_'` so the
field arrives transparently instead of as an `axiom`, and `hachi/lean/Check.lean`
§ 2 asserts the transparent form. A translation that finds itself writing field
arithmetic has taken a wrong turn; it should be calling `cpoly::Fp`.

## Conventions: types

| Lean | Rust | Why this shape |
|---|---|---|
| `ZMod q`, reduced representative | `cpoly::Fp` — imported, never rewritten | the `Red` invariant holds by construction: the inner `u64` is private and `Fp::new` reduces (`hachi/lean/Field.lean` header) |
| the quartic extension | `cpoly::Ext4` — imported | same rule; `Ext4`'s named-fields struct keeps its operations straight-line in the extracted model |
| `Rq Φ`, i.e. `{ p : CPolynomial R // Φ.reduce p = p }` | `Rq(Vec<Fp>)`, exactly `RING_DEGREE` coefficients, little-endian | `deg φ = N`, so "fixed by reduction" and "fewer than `N` coefficients" are the same condition; the fixed length is what makes every operation a straight loop with no reduction step (`hachi/src/ring.rs` § "Representation, and how it lines up with the spec") |
| `Fin k → P`, Mathlib `Matrix` | `PolyVec(Vec<Rq>)`, `PolyMatrix(Vec<PolyVec>)` | the spec's function types are a computability choice; here the index arithmetic is written out, following `finProdFinEquiv (i, e) = e + width · i` (`Gadget/Core.lean:166`) |
| `Vector F d`, small known `d` | named-fields struct | keeps every operation straight-line in the extracted model: no loops, no bounds checks |
| `List F` / `Array F`, dynamic | `Vec<T>` newtype; `&Vec<T>` for borrowed arguments | `alloc.vec.Vec` (with `len`, `index`, `index_mut`, `push`) is what `Generated.lean` is written against; a slice argument adds a coercion at every call site for the proofs to carry, which is why `ptr_arg` is `allow`ed in `hachi/Cargo.toml` |
| `Fin n` | `usize` + the structural bound (`i < v.len()`) | never a stored index type; the bound is re-established where used |
| `UInt32` / `UInt64` | `u32` / `u64`; `as`-casts for widening/narrowing | `x as u128` extracts as `lift (UScalar.cast .U128 x)`, which Aeneas models directly, where `u128::from(x)` is a trait call to step through (`hachi/Cargo.toml`, `cast_lossless`) |
| subtype with a Prop | newtype whose constructors enforce the invariant | the proofs get the invariant from the type — but Aeneas cannot see a Rust privacy boundary, so it *also* travels as a hypothesis on each `_spec` (`Wf` in `hachi/lean/Ring.lean`, `Red` one layer down) |

## Conventions: terms and structure

| Lean shape | Rust shape |
|---|---|
| `let x := e; body` | `let x = e;` — **statement order is bind order**; never collapse intermediates into one expression |
| `ofFn` / `∑` over `Fin d`, `d` known small | unroll to named lets, with the index regrouping justified in the doc comment |
| fold / map / structural recursion over a list | counter loop: `let n: usize = …; let mut out: Vec<Fp> = Vec::new(); let mut i: usize = 0; while i < n { out.push(…); i += 1; }` |
| shared sub-definition | helper `fn` over the container the callers hold |
| `if` / `match` | `if` / `match` with the same nesting |
| a bit test or power-of-two split | `/` and `%`, never `>>` and `&` — plain `Usize` arithmetic is what `scalar_tac` and `omega` see through (`hachi/src/lib.rs` § "Style notes") |
| one `def` | one `fn`, with a ``Mirrors ArkLib's `<exact name>` `` doc line and the `(spec: …, file:line)` citation |

**Every `let` in a translated body carries an explicit type**
(`let mut i: usize = 0;`, `let a: Fp = self.0[i];`) — extraction is insensitive
to it, but the binds stay legible and reviewable. `hachi/src` holds to this
without exception today; keep it that way. The counter `while` is deliberate:
`for i in 0..n` *is* modelled but puts a `Range<usize>` in every loop
invariant, and the invariant is what the Lean side is written about — see
`hachi/src/lib.rs` § "Style notes" and "Deliberately declined" in
`aeneas-idiomatic-rust`. Iterator adaptors (`.map`, `.zip`, `.fold`,
`.collect`) have no model at all.

The unroll-and-regroup move (row 2 of the table), stated generically rather
than by example: collect terms into columns by output index, columns in
ascending order, products within a column in ascending first-operand index;
when a wrap/fold constant scales a whole column, factor it **once** —
distributivity, exact in the field — with the constant on the left, and the
direct column first in the fold add. Per-term scaling (the literal Lean shape)
and per-column factoring extract to *different bind sequences*; the checklist
picks per-column, justified in the doc comment. The negacyclic product is the
same phenomenon at loop scale: `Rq::mul` folds the `X^N ≡ -1` sign into the
inner loop instead of reducing afterwards, and says so in its doc comment.

## Conventions: the shell

The public surface is the house API from day one:

* **Inherent methods, one body per operation.** `hachi/src` has no `core::ops`
  impls at all: the ring's arithmetic is `Rq::add`, `Rq::mul`, … Adding an
  `impl Add for Rq` beside `Rq::add` would extract as a *second* body saying
  the same thing, which is the same objection that keeps `equals` hand-written
  rather than derived (`Rq::equals`'s doc comment) and that makes
  `acc = acc + x` the house form rather than `acc += x`
  (`hachi/Cargo.toml`, `assign_op_pattern`). Field-level operators are used
  freely — they are `cpoly`'s impls, and they are the operations the field
  specs are about.
* If a by-reference operator impl is ever introduced, keep type names distinct
  across modules (`Rq`, `PolyVec`, `PolyMatrix` already are): AeneasCompPoly
  found that such impls mangle to `Shared<n><TypeName>` *without* module
  qualification, and a collision is a hard extraction failure.
* Parameters as `const` in `hachi/src/params.rs`, and a derived-looking one
  written as a literal with the relation checked elsewhere — Aeneas models a
  `const` shift or subtraction as fallible, so `1 << RING_LOG_DEGREE` or
  `GADGET_BASE - 1` would extract as a `Result` with a side condition in every
  use (`params.rs`, `RING_DEGREE` and `GAMMA`; the relations are checked in
  `tests/params_semantics.rs` and `lean/Check.lean` § 1).
* No `Vec::is_empty`, `Vec::truncate`, `Vec::clone` or `#[derive(Default)]` on
  a `Vec`-holding struct: none is modelled, and each puts an `axiom` in
  `Generated.lean` (`hachi/src/lib.rs` § "Style notes"; `Rq::copy` is the
  hand-rolled `push` loop that replaces `clone`).
* Doc comments carry the semantics the reviewer needs, and both spec-citation
  forms are load-bearing, so a new public operation carries both: the house
  line ``Mirrors ArkLib's `<name>` `` is what `make bench-coverage` scans for
  when pairing an item with its bench row or its `exclusions.toml` entry, and
  `(spec: \`<name>\`, \`<file>:<line>\`)` is what a reviewer follows into the
  pinned specification. An item with neither is invisible to the coverage gate
  rather than gated by it. Whenever new word arithmetic appears, the
  overflow-headroom bounds go in the doc comment too, numerically.
  `missing_docs` is `deny` and `unsafe_code` `forbid` in `hachi/src/lib.rs`,
  so documentation is enforced, not encouraged.

## Trivial-grade checklist — the enumerated moves

A translation may do exactly these, and nothing else:

1. Unroll a fixed-size `ofFn`/`∑` (known small `d`), regrouping indices, with
   the regrouping stated in the doc comment.
2. Turn fold/map/recursion into the counter-`while` + `Vec::new()`/`push`
   accumulator shape.
3. Introduce *more* named intermediates than the Lean has (never fewer).
4. Extract a shared helper `fn`.
5. Pick representations per the type table above — which for the field layer
   means *calling* `cpoly`, not choosing anything.
6. Keep arithmetic on reduced representatives with the headroom argument
   stated (`q < 2^32`, so a sum of two reduced words is below `2^33` and a
   product at most `(q-1)² < 2^64`, and its friends at wider types).

If the improvement you want is not on this list, it is an optimization:
return it to the Lean side (an `opt-*` rewrite + its `opt_eq_spec` lemma), then
translate *that* definition with these same six moves.

## What a translation owes before it is done

* `make test` green, with the module's semantics tests extended to cover the
  new item against non-degenerate inputs — and, where a norm bound is
  involved, *on* the bound, since `GAMMA` and `BETA_SQ` are tight.
* `cargo clippy --all-targets` clean under pedantic; `#[allow]` only with a
  one-line reason at the narrowest scope. The crate-level allows are not a
  precedent to extend casually: each one in `hachi/Cargo.toml` records why
  clippy's suggestion is worse *for the extraction* (`ptr_arg`,
  `assign_op_pattern`, `cast_lossless`, `needless_range_loop`, and
  `len_zero` / `len_without_is_empty` for the unmodelled `Vec::is_empty`).
* The bench obligations of the `rust-bench` skill: freeze the item into
  `hachi/benches/genesis/`, then a case or a by-name exclusion with a
  checkable reason — `make bench-check` enforces this.
* An extraction pass per the `aeneas-extract` skill: zero axioms, loop-state
  shapes diffed, names skimmed. `--include 'cpoly::_'` is not optional.
* **A new public operation owes its Aeneas obligation, written down.** What
  the audited library covers today is `Fp`, the whole coefficient level of
  `ring`, and its lift to ArkLib's `Rq Φ` (`hachi/lean/RqBridge.lean`) —
  thirty-two `#print axioms` lines in `hachi/lean/Check.lean` § 4 — while
  `hachi/lean-wip/Scheme.lean` is stated only. So the invariant to protect is
  not "every operation has a proved spec" but "no operation arrives without
  its statement": land the Rust together with at least a *typechecked*
  statement in `hachi/lean-wip/`, and flag the proof debt to the outer
  verification pass explicitly. Unproved Lean goes in `lean-wip/`, never in
  `lean/` — and promoting a file into `lean/` means adding its module to
  `roots` in `hachi/lakefile.lean` and a `#print axioms` line to `Check.lean`
  § 4 (`hachi/lean-wip/README.md` § "Promoting a file out of here").
* **Helper visibility is a three-way trade, decided at translation time.**
  A helper `fn` of one public operation should stay private: `pub` hands it
  the obligation above for no caller's benefit. But a bench target is an
  *external* crate, so a private item cannot be benched individually — it
  gets a structural exclusion ("private; measured through `<op>`'s rows") and
  its genesis freeze still happens (first translation, same commit).
  Re-optimizing such a helper in isolation is the moment to revisit its
  visibility. (No item here has been re-optimized yet; the rule is inherited
  from AeneasCompPoly, where private helpers of an optimized operation were
  the case that produced it.)

## Failure modes with teeth

These are `aeneas-idiomatic-rust` lessons restated as translation rules —
that skill is the source of truth for all four:

* **Collapsing binds.** Merging `let lo = c[2*j]; let hi = c[2*j+1];
  out.push(lo + x0*hi)` into one expression reorders the extracted binds and
  invalidates every `step as ⟨…⟩` walk. Same for `+=` vs `x = x + y` — they
  extract differently; here `x = x + y` is the deliberate pick.
* **Fattening a loop's state.** A binary operation whose loop runs inline over
  `self` *and* `rhs` carries `rhs` in the extracted loop state; upstream's fix
  was a helper over slices, restoring a 2-tuple. This repository took the
  other branch knowingly — `Rq::add`'s loop is inline, so
  `Ring.add_loop_spec` quantifies over `rhs` — and paid for it in the proof:
  `NOTES.md` § "Two things that made the proofs go through" records that
  `subst` on the invariant's `s.1 = rhs` conjunct eliminates `rhs`, forcing
  the body proof to name the loop-state variable and changing the arity of the
  `refine`. Either shape is translatable; pick it on purpose, and expect that
  cost if you keep the fat state.
* **Two newtypes over the same inner type are the same Lean type.** A spec
  pairing the wrong reading still typechecks. `Rq`, `PolyVec` and
  `PolyMatrix` are all `Vec` newtypes, and `Check.lean` § 2b exists partly to
  pin their shapes; after translating into a module with two readings of one
  container, check the pairings by hand.
* **Reflexive tidying.** `vec![a, b]` (list form), `v.is_empty()`,
  `derive(Default)` / `derive(Clone)` on a `Vec`-holding struct — each drags
  an axiom in. The verdict tables decide, not Rust habit.

## Invariants to keep green

* Statement order = bind order; every deviation from the Lean is one of the
  six moves, and moves 1 and 6 are justified in doc comments.
* The field layer is called, never rewritten.
* The doc line names the exact, current ArkLib identifier at the pinned
  `Arklib` rev, with its `file:line`.
* Zero axioms and zero `sorry` in the audited library after the extraction
  pass; anything not yet proved is a typechecked statement in `lean-wip/`.
* The spec debt of a new public op is flagged, never silent.
* This checklist changes only with ledger evidence (proof-effort rows),
  and the change lands here, in this file.
