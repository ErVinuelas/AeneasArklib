---
name: opt-list-to-array
description: Optimization strategy — replacing List, Fin-function and append-chain shapes in a targeted ArkLib definition with the indexed Vec loops the translation subset supports, killing per-element allocation and O(n) appends, as Foo.opt + its proved opt_eq_spec lemma; run only when the brief shows an actual List, append chain, or per-element allocation on the hot path
---

# Strategy: Spec Containers → Indexed `Vec`

One strategy of the optimization loop. Invoked by the `lean-opt` driver with a
target definition and its `arklib-analyze` brief; delivers a candidate under
the opt-contract that `lean-opt` owns: `Foo.opt` in `hachi/lean/Opt.lean` plus
the proved `Foo.opt_eq_spec`.

## The one rule: fire on brief evidence, not on reflex

The crate side is already the target shape. `Rq`, `PolyVec` and `PolyMatrix`
are single-field newtypes that arrive as `@[reducible] def`s over the Aeneas
`Vec` model — `def ring.Rq := alloc.vec.Vec cpoly.field.Fp` — so a statement
about an `Rq` *is* a statement about a vector of field words, with no wrapper to
transport across (`Check.lean` § 2b asserts all three, so a change that turned
one into a real `structure` fails the audit). If the brief shows no `List`
shape, no append chain and no per-element allocation, report
`no-strategy-applies` and stop: that outcome is expected and costs the loop
nothing, while a forced rewrite of an already-indexed def costs a candidate slot
and a bench run.

Note also what *is not* the trigger: the extracted `Vec` is a `List`
underneath — `hachi/lean/Ring.lean` reasons about `v.val` with `List.length`,
`List.getD` and `List.getElem` throughout — so a `List` in the model is not by
itself a problem. What is untranslatable is the *operations*: `++` chains and
non-indexed recursion have no counterpart in the trivial translation subset.

## Where the shapes actually come from: the specification side

The mismatch this strategy resolves is spec-shaped, not crate-shaped:

* `ArkLib.Lattices.PolyVec P k` is `Fin k → P`, and `dot` is computed as
  `List.sum ∘ List.ofFn` rather than `Matrix.mulVec` — for computability, since
  `Rq`'s `CommRing` instance routes through a noncomputable transport
  (`Vectors.lean:20-23`). `linalg::dot`'s docstring records the residue: the
  spec sums right-nested over a `List`, the crate accumulates left, and the
  equivalence proof has to say they agree rather than match syntactically.
* `Rq Φ` is a subtype of CompPoly's `CPolynomial R`, itself a subtype of
  `CPolynomial.Raw R = Array R` carrying `IsCanonical` — trailing zeros
  trimmed. The crate's `Rq` is instead exactly `N` coefficients with no trim,
  which is what makes every operation a straight loop with no reduction step
  (`hachi/src/ring.rs` § "Representation").
* The gadget's digits come from `Nat.digits` on the canonical representative.

So a `Foo.opt` derived from a spec definition arrives `Fin`-indexed, `List`-
folded or trim-carrying, and has to be moved onto the indexed `Vec` model before
it is translatable. **Do not import the trim**: a variant that trims is a
different representation, not an optimization, and it belongs to
`opt-word-arith`'s gated route.

## What it attempts

* `List`-recursive or `Fin`-function definitions → an index loop over the `Vec`
  model with an explicit counter;
* append accumulation (`acc ++ [x]`, `List.concat`) → `push` accumulation;
* container interconversions inside a computation → staying in the `Vec` model
  end to end, converting once at the boundary.

Not available as a move: slices. `hachi/Cargo.toml` allows clippy's `ptr_arg`
deliberately, because `Generated.lean` is written against the `Vec` model and a
`&[T]` argument would add a coercion at every call site for the proofs to carry.

The lemma side is already stocked: `Ring.lean`'s `coeffK`, `coeffK_of_lt`,
`coeffK_of_ge`, `coeffK_append_lt` and `coeffK_append_eq` are the indexing
bridge between a `List`-shaped statement and a push loop, and every one of them
is proved.

## Invariants to keep green

* The opt-contract (owned by `lean-opt`) is met in full.
* The candidate note cites the brief's `file:line` for the container shape it
  removed — no citation, no candidate.
* A variant that changes the representation (trimmed, variable-length) is not
  this strategy's output; it is a gated proposal.
