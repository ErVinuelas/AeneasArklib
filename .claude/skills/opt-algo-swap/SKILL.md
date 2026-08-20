---
name: opt-algo-swap
description: Optimization strategy — substituting the algorithm behind a targeted ArkLib definition (a convolution split for the negacyclic product, running-quotient digit extraction, precomputed power tables) as a Lean Foo.opt variant with its proved opt_eq_spec lemma; run when the brief shows an operation-count or complexity-class win
---

# Strategy: Algorithm Substitution

One strategy of the optimization loop. Invoked by the `lean-opt` driver with a
target definition and its `arklib-analyze` brief; delivers a candidate under
the opt-contract that `lean-opt` owns: `Foo.opt` in `hachi/lean/Opt.lean`,
written inside `lean-to-rust`'s translatable subset, plus the proved
`Foo.opt_eq_spec`. This is the strategy the driver tries **first**: a
complexity-class or operation-count win dwarfs constant-factor tuning, and it
changes which constants are worth tuning afterwards. It is also the tier most
likely to clear this harness's noise floor: NOTES.md § "The first benchmark
run" found byte-identical crates reading up to 59% apart on the host it
measured, so a few-percent win is indistinguishable from placement there.

Being the first tier means this strategy is likely to produce the *first*
candidate, and `hachi/lean/Opt.lean` does not exist yet: creating it is
`lean-opt`'s step zero (new module, `` `Opt `` in `roots`, imported by
`Check.lean`), and skipping it leaves a lemma that is never checked. Do not
re-derive that procedure here — follow it there.

## The one rule: the algorithm changes in Lean, never in the translation

`gadget::gadget_mul` is what doing this right looks like. It computes the
per-block digit sum directly rather than the general matrix product its spec
line names, which is `O(rows · digits)` instead of `O(rows² · digits)` — and
that is legitimate only because ArkLib *proves* the two equal in
`gadgetMul_apply` (`Gadget/Core.lean:177`), which the docstring cites. The
obligation is still owed on this side: it is one of the statements
`hachi/lean-wip/Scheme.lean` makes and does not yet prove.

AeneasCompPoly carries the counterexample. Its `eval` is Horner's method while
its `Mirrors` line names the naive fold, because the swap was made during
translation; the Aeneas equivalence proof then had to absorb an algorithm gap
that a pure-Lean lemma the spec library already ships would have carried, and
the Rust could no longer be regenerated from the def it claimed to mirror. A
swap lands as `Foo.opt` + lemma first; the translation of it stays trivial.

## Upstream first

ArkLib ships optimized forms with their lemmas — check the pinned copy
(`hachi/.lake/packages/Arklib/`, rev per `hachi/lake-manifest.json`) before
writing one. That is the only copy of the spec here, so it is also the one to
read. Exemplar pair: `ArkLib.Lattices.Ajtai.gadgetMul` with `gadgetMul_apply`.
The `Rq` layer ships the same kind of lemma for its reductions (`add_val`,
`sub_val`, `neg_val`, `constRq_mul_coeff` in
`Data/Lattices/CyclotomicRing/Rq.lean`) — those are why the coefficientwise
loops in `hachi/src/ring.rs` need no reduction pass. When ArkLib has the
variant, the candidate is "mirror the spec's own lemma" and nothing lands in
`Opt.lean`.

## The moves this strategy owns

* **Splitting the negacyclic convolution.** `ring::Rq::mul` is the schoolbook
  `O(N²)` product at `N = 64` — 4096 coefficient multiplications, each with a
  reduction — and everything above it is that in a loop (`linalg::dot` over
  128 entries is 128 of them). Karatsuba over `a = a₀ + X^{N/2}a₁` gives 3
  half-length products instead of 4 per level, so `(3/4)^k` of the
  multiplications at depth `k`: −25% at one level, −44% at two. `X^N ≡ −1`
  makes the recombination *cheaper* than in the plain-polynomial case, since
  the high half folds back with a minus sign instead of extending the output.
  Subtraction is free here: `Fp` has a proved `sub` (`hachi/lean/Field.lean`),
  and the crate is concrete, so none of upstream's typeclass-strengthening
  bookkeeping applies.
* **Running state instead of recomputation.** `gadget::digit_at(c, e)` divides
  `e` times from scratch, so `digit_decompose` spends `Σ_{e<32} e = 496`
  divisions where one running quotient costs 32 — and `gadget_decompose` pays
  that once per coefficient of every entry (`rows · 64` times).
* **Precomputed tables** for values recomputed inside a loop.
  `gadget::base_pow(e)` costs `e` multiplications and is called once per digit
  per row inside `gadget_mul` and `gadget_matrix`: 496 multiplications per row
  where a table built once costs 31 for the whole call. The table construction
  must itself be a translatable def.

Loop/pass *fusion* is not this skill: memory-traffic restructuring belongs to
`opt-inplace-buffers`. The boundary: this skill changes *what* is computed
(fewer field operations); that one changes *how memory moves*.

## The NTT is not available at these parameters

Arithmetic, checkable rather than measured: the modulus is `cpoly`'s
`P = 2^32 − 99`, and `P − 1 = 2² · 3 · 13 · 67 · 163 · 2521` has two-adicity
**2**. A radix-2 negacyclic transform of length 64 needs a primitive 128th
root of unity; `F_P` has none, and neither does the quartic extension —
`P⁴ − 1` has two-adicity 4, so 16 is the largest power-of-two order anywhere in
`Ext4`. `hachi/benches/ring.rs` is right that `ring/mul` is "the operation an
NTT would replace"; what it cannot be is a radix-2 one. A proposal has to name
a transform that does not need that root (Bluestein, Nussbaumer, a CRT split of
`X^64 + 1`) and show the root it does use. `P` is pinned by the `cpoly`
dependency, so a friendlier prime is not on the table.

## Inherited lesson: count the recombination, not only the multiplications

AeneasCompPoly's accepted Karatsuba candidate (2026-08-11) predicted
−58%/−25% from multiplication counts at n = 256/64 and measured −48.8%/−18.2%
recentered: the recombination's linear passes and allocations cost about 10
points at depth 3 and 7 at depth 1. Their numbers are not ours, but the shape
transfers — a multiplication-count prediction overshoots. Quantify both the
multiplication count and the added passes/allocations in the candidate note,
and expect the second to eat part of the first.

The proof route to plan for: state the splitting identity at the coefficient
level against `negConv`, the closed form `hachi/lean/Ring.lean` already proves
`Rq::mul` computes, and lift to ArkLib's `Mul (Rq Φ)` through
`hachi/lean/RqBridge.lean` only if the `Rq Φ`-level statement is what the
candidate claims.

## Invariants to keep green

* The opt-contract (owned by `lean-opt`) is met in full — def, proved lemma,
  candidate note with the op-count claim cited from the brief.
* The `Mirrors` line of the translated Rust names `Foo.opt` (or the ArkLib
  lemma that licenses the form), never the definition the algorithm no longer
  matches — that line is also what `coverage` binds a bench case to.
* Every operation-count claim is counted from the def and reproducible by
  reading it; a claim that a transform exists names its root of unity.
