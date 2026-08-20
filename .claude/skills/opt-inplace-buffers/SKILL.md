---
name: opt-inplace-buffers
description: Optimization strategy — pre-sized buffers, loop/pass fusion, and in-place mutation shapes for a targeted ArkLib definition, expressed in Lean so the translation stays trivial, as Foo.opt + its proved opt_eq_spec lemma; run when the brief shows reallocation growth, repeated passes over the same vector, or an output the size of the input
---

# Strategy: In-Place / Pre-Sized Buffers

One strategy of the optimization loop. Invoked by the `lean-opt` driver with a
target definition and its `arklib-analyze` brief; delivers a candidate under
the opt-contract that `lean-opt` owns: `Foo.opt` in `hachi/lean/Opt.lean` plus
the proved `Foo.opt_eq_spec`.

## The one rule: the buffer discipline is expressed in Lean, or it does not exist

`Vec::new()` + `push` is the *deliberate* trivial shape (`lean-to-rust`'s fold
row, and the reason `Rq::copy` is a push loop rather than a `clone`) — a
translator that quietly adds `with_capacity` or fuses two loops has made an
optimization, and optimizations live in Lean. What this strategy adds is the
Lean-side def whose trivial translation produces the better shape, plus the
lemma that says it computes the same thing. A correspondence not yet in
`lean-to-rust`'s conventions table is a one-row extension of that table: name
it in the candidate note; the row lands in `lean-to-rust` (its owner) when the
candidate is accepted.

## What the extraction actually supports here

Checked against the pinned Aeneas backend
(`hachi/.lake/packages/aeneas/backends/lean/Aeneas/Std/Vec.lean`) and the
current model, rather than assumed:

* `hachi/lean/Generated.lean` uses exactly five `Vec` operations — `new`,
  `push`, `len`, `index`, `index_mut`. `clone`, `truncate` and `is_empty` have
  no model at all and would arrive as opaque items (NOTES.md § "What the
  extraction of the four modules actually looks like").
* **`with_capacity` is modelled, total, and erased.**
  `alloc.vec.Vec.with_capacity T _ = Vec.new T` by definition, flagged
  `-canFail`. So pre-sizing is extraction-safe *and* free on the proof side:
  the capacity argument does not survive into the model, and the `opt_eq_spec`
  of a pure pre-sizing change has nothing to prove. The whole win is in the
  Rust — which also means the bench is the only evidence it did anything.
* **`vec![x; n]` is modelled** as `alloc.vec.from_elem`, and Aeneas ships its
  spec (`v.val = List.replicate n.val x`) — which is exactly what
  `Ring.lean`'s `zero_loop_spec` proves by induction over a push loop. It
  needs `Clone` on the element; `Fp` derives `Copy, Clone` in `cpoly`, but that
  impl is not in the model today. Run `make extract` and read the new items
  before a note claims this one.
* **In-place writes through `index_mut` are modelled and already proved
  against.** `Rq::mul` is the one place in the crate whose accumulator moves by
  `Vec.set` rather than by `push`, and `hachi/lean/Ring.lean` carries the two
  lemmas that made it work: `coeffK_set` (the cell written is the new value,
  every other cell is unchanged) and `Red_set` (overwriting with a reduced word
  keeps every word reduced). Reuse them; that pair *is* the invariant shape for
  a `set!` loop.

## What it attempts

* **Pre-sizing**: output length known up front — `N`, `rows`, `rows · digits`,
  `x.len() · digits` are every case in this crate — becomes a pre-sized buffer
  plus a push or index loop.
* **Pass fusion**: consecutive traversals of the same vector become one loop
  with named per-iteration intermediates. The local instance is `Rq::mul`,
  which zero-fills the accumulator in one pass (`mul_loop0`) and then
  accumulates in another; a fused version writes each slot's first contribution
  instead. Price it honestly: `mul_loop0_spec` is currently *free*, discharged
  by `zero_loop_spec` because Aeneas extracts the two while bodies to
  definitionally equal terms, and fusing it means a new invariant of its own.
  (Computing *fewer* field operations is `opt-algo-swap`'s side of the
  boundary; this skill only changes how memory moves.)
* **In-place accumulation**: `acc = f acc x` chains that rebuild a container
  become writes into one buffer. `linalg` is where this pays: `PolyVec::dot`
  allocates a fresh 64-word `Rq` for the product and another for the running
  sum on *every* entry — 256 allocations for the 128-entry case NOTES.md § "The
  first benchmark run" timed at 1.16 ms — and `mat_vec_mul` repeats that per
  row. `flatten_blocks` copies every entry through `Rq::copy`, and
  `gadget::gadget_decompose` builds `rows · digits` fresh coefficient vectors.

## Invariants to keep green

* The opt-contract (owned by `lean-opt`) is met in full.
* Reallocation and pass-count claims in the candidate note are counted from the
  def and cited to the brief — never "should allocate less". A change the model
  erases (pre-sizing) says so, so nobody reads its `rfl` lemma as evidence of a
  speedup.
* Any new Lean↔Rust correspondence is named explicitly for `lean-to-rust` to
  adopt; it is never applied silently in the translation.
