---
name: rust-direct
description: Optimization strategy — rewriting the Rust translation of a targeted ArkLib definition directly in hachi/src (algorithm swaps, buffer shapes, loop restructuring) while staying inside the Aeneas-supported ceiling; the candidate stage of route-r2, where no Lean opt lemma exists and the equivalence proof relates the extracted model straight to the original ArkLib definition; use when running the Rust-first route or when a Rust-level rewrite of a targeted operation is proposed
---

# Rust-Direct Optimization (the R2 candidate stage)

The candidate stage of the `route-r2` composition: candidates are written as
Rust diffs against the current champion in `hachi/src`, not as Lean `Foo.opt`
definitions. Read this **before** writing any such candidate. The bench,
accept rule, and ledger mechanics are `perf-loop`'s and apply unchanged — a
rust-direct candidate enters that procedure at the semantics-test step, since
it is already Rust. Idiom/axiom boundaries are `aeneas-idiomatic-rust`'s; the
supported-constructs ceiling is `aeneas-extract`'s. Neither table is repeated
here.

## The one rule: never write a construct without a green ceiling row

Extraction is checked once, at champion landing — not per candidate. A
candidate that uses a construct absent from `aeneas-extract`'s measured
ceiling table gambles the whole bench-and-accept effort on an extraction
failure discovered last. So: every construct in a candidate either has a
green row in the table, or gets probed first by that skill's recipe (which
grows the table one measured row per contact). `unsafe` and SIMD are the
hard cap — no probe changes that, and here it is mechanical rather than
advisory: `hachi/src/lib.rs` carries `#![forbid(unsafe_code)]`, and so do both
slot crates. This rule is the whole difference between "optimize within the
ceiling" and "write Rust and hope".

This repository's own contacts with the ceiling are recorded in `NOTES.md` and
are worth reading before the table, because they are about *this* crate's
constructs: § "Aeneas surprises" (a `<<` in a `const` extracts as a `Result`,
so `params.rs` holds literals and checks the relations instead), § "What the
extraction of the four modules actually looks like" (single-field newtypes are
free; `u128` and its cast work; the `Vec` model covers `new`/`push`/`len`/
`index`/`index_mut` and **not** `clone`/`truncate`/`is_empty`; nested loops are
named positionally; counter loops, not `for`), and § "Derives extract, and are
still not worth it" — the one that matters most for judgement, because it is a
case where the construct extracted *cleanly, axiom-free* and was reverted
anyway, for model hygiene. "It extracts" is a necessary condition, not a
sufficient one. `hachi/src/lib.rs` § "Style notes" is the same list as house
rules, and `hachi/Cargo.toml`'s `[lints.clippy]` block records four places
where clippy's suggestion is *worse* for the extraction — do not "fix" those.

## The candidate contract

* **Input** — the target's `arklib-analyze` brief (its cost model reads on
  the Rust hot path too) and the current champion's `hachi/src`.
* **Output** — a candidate diff in an isolated worktree, plus a candidate
  note stating: the predicted win and why, and the list of constructs used
  that are near the ceiling's edge, each pointed at its table row (or the
  probe that just added one). The prediction ranks candidates for benching and
  never accepts one.
* **Gates before benching** (replacing the opt-contract of the Lean-side
  strategies — there is no `Foo.opt` and no `opt_eq_spec` here):
  * ceiling audit per the one rule;
  * `cargo clippy --all-targets` clean at the mechanical level the inner
    loop uses (this crate sets `pedantic = warn` with a documented
    allow-list, so "clean" means no *new* warning, not an empty log);
  * `cargo test` semantics pass — the suites in `hachi/tests/` are written
    deliberately unlike the crate, so they are a real filter;
  * the item's **spec reference stays pointed at the original ArkLib
    definition**. Locally that is the `(spec: …)` clause in the item's
    docstring (`hachi::ring::Rq::mul` reads "spec: the `Mul (Rq Φ)` instance,
    `Rq.lean:110`") plus the type-level ``Mirrors `CyclotomicModulus.Rq Φ` ``
    line on the carrier. A rust-direct champion still mirrors that definition
    semantically and there is no opt variant to rename to — so unlike the
    `lean-opt` path, *nothing* in the docstring changes except the description
    of how the body works.
* **Verdict** — `perf-loop`'s recentered `CANDIDATE=1` accept rule, verbatim,
  including its single-row clause: every `ring/*` case has exactly one row
  (`params::RING_DEGREE` is a `const`), so an accept there needs two
  independent runs agreeing. The ledger row is a standard candidate row with
  `"strategy": "rust-direct"`.

## Proof-debt pricing — what this strategy deliberately forgoes

An accepted rust-direct champion carries **no Lean lemma chain**: the
`verify-campaign` for it proves the extracted model against the original
ArkLib definition directly, with no `opt_eq_spec` to splice onto the
right-hand side. That cost difference is not a defect — it is the R2 datum
the bake-off exists to measure (the with/without-lemma question the plan
keeps open).

Price it with this crate's specifics rather than in general. The audited proofs
are Aeneas triples about *positionally named* extracted loops: `Rq::mul` is
`ring.Rq.mul_loop0` (the zero-fill), `ring.Rq.mul_loop1` and
`ring.Rq.mul_loop1_loop0` (the convolution's two passes), and
`hachi/lean/Ring.lean` proves one `_spec` per loop about exactly those names,
with the invariant written in terms of `contrib` / `rowsSum` / `negConv`
(`NOTES.md` § "What the extraction of the four modules actually looks like"
calls the naming "the proof plan"). A Rust-side loop restructuring therefore
renames and reshapes the very definitions the existing proof is about: the
debt is not "add a lemma on top", it is "rewrite the loop invariants", and
`make build` will refuse the champion until that is done. Say so in the note,
with the list of `_spec`s the diff invalidates — that list *is* the R2 price,
measured rather than estimated.

A representation change (different coefficient layout, packed words, an NTT
domain) goes through `aeneas-equivalence-bridges` before any relation is
invented; its decision tree ("a function beats a relation") applies with
extra force here, because there is no Lean-side variant to anchor one. And
check feasibility before the diff: at these parameters `F_q` has no primitive
`2N`-th root of unity (`lean-opt` § "Upstream first" works the arithmetic out),
so an "NTT" candidate has to say where its transform lives.

## Invariants to keep green

* Every construct in an accepted champion has a green ceiling row dated no
  later than the accept.
* No `unsafe`, no SIMD, no iterator adaptors beyond the table's green rows.
* Spec references truthful to the original ArkLib definition; semantics
  tests extended per `lean-to-rust`'s obligations when behavior surface
  grows.
* The candidate note lists the `hachi/lean/` `_spec`s the diff breaks. A
  champion whose proof debt was never written down is indistinguishable from
  one whose debt was overlooked.
* Every candidate that reached the bench has a ledger row with
  `"strategy": "rust-direct"`, whatever its fate.
