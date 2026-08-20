---
name: opt-tailrec-loops
description: Optimization strategy — rewriting structural or non-tail recursion in a targeted ArkLib definition into a tail-recursive accumulator loop or fold that lands 1:1 on a Rust counter while loop, as Foo.opt + its proved opt_eq_spec lemma; run when the brief shows non-tail recursion or per-call allocation on the hot path
---

# Strategy: Tail-Recursion / Loop Shape

One strategy of the optimization loop. Invoked by the `lean-opt` driver with a
target definition and its `arklib-analyze` brief; delivers a candidate under
the opt-contract that `lean-opt` owns: `Foo.opt` in `hachi/lean/Opt.lean` plus
the proved `Foo.opt_eq_spec`.

## The one rule: the target shape is the one `lean-to-rust` already translates

The point is not that tail calls are fast in Lean — Lean's cost model is
explicitly not the fitness function. A tail-recursive accumulator def is the
*Lean image* of the counter-`while` row of `lean-to-rust`'s conventions table,
which is this crate's house shape for a reason that is documented and
load-bearing: `for i in 0..n` *is* modelled, but it turns the loop state from a
`usize` counter into a `Range<usize>` iterator, and the loop state is what every
invariant on the Lean side is written about (`hachi/src/lib.rs` § "Style notes",
and NOTES.md § "What the extraction of the four modules actually looks like",
which records the same finding from the extraction side). Iterator adaptors —
`.map`, `.zip`,
`.fold`, `.collect` — have no model at all. A rewrite that lands outside that
table has left this strategy's mandate: file it as a different strategy or drop
it.

## Why the state, and its nesting, are the expensive part to change

The extracted loops here carry small tuples — `(out, i)` for `neg` and
`scalar_mul`, `(rhs, out, i)` for `add` and `sub`, `(a, b, out, i)` for `mul`'s
outer pass — and `hachi/lean/Ring.lean` writes every invariant as projections of
exactly those tuples (`s.2.2.val ≤ n.val`, and so on), discharged by
`loop.spec_decr_nat` with the measure `n.val - <counter>`. Two consequences a
candidate note has to price:

* a fattened loop state moves every projection index in every invariant that
  mentions it;
* Aeneas names nested loops **positionally** — `Rq::mul`'s passes are
  `mul_loop0`, `mul_loop1` and `mul_loop1_loop0` — so changing the nesting
  renames the extracted definitions, and every proof that mentions them by name
  moves with it. NOTES.md § "What the extraction of the four modules actually
  looks like" reads that naming as the proof plan, and it is.

A variant whose measure is not `bound − counter` needs its own termination
argument; say which in the note rather than discovering it in the build.

## What it attempts

* structural (non-tail) recursion → tail recursion with an accumulator
  argument, or an explicit index loop over the container;
* recursion whose call tree re-traverses data → a single forward pass with
  named intermediate state.

The proof side: `Foo.induct` for the original's induction principle, the
generalize-the-accumulator pattern, and `termination_by` for the variant when
its recursion is no longer structural. The vendored `proof-patterns` and
`aeneas-lean-core` skills carry the loop-invariant idioms; `Ring.lean`'s
`add_loop_spec` is the worked local example of one.

## Scope: this fires on what other strategies introduce

Nothing in `hachi/src` is non-tail recursive — every operation is already a
counter loop — so on the corpus as it stands the honest outcome is usually
`no-strategy-applies`, and that costs the loop nothing. Where it does have work
is the recursion a *higher tier* introduces: a divide-and-conquer convolution
split from `opt-algo-swap` is naturally non-tail, and a Lean def written
structurally there does not land on the counter-loop row. That path is
untraveled in this repository; the first candidate to walk it grows this
section.

## Invariants to keep green

* The opt-contract (owned by `lean-opt`) is met in full.
* The variant's loop shape maps onto conventions-table rows with no new
  translation move required — if it would need one, say so in the candidate
  note instead of smuggling it.
* Renamed or re-nested extracted loops are named in the note, with the proofs
  that have to move.
