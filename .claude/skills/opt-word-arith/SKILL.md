---
name: opt-word-arith
description: Optimization strategy — word-level arithmetic rewrites of a targeted ArkLib definition (delayed reduction with stated headroom, conditional-subtract folds, u128 accumulators over Rq coefficient vectors) as Foo.opt + its proved opt_eq_spec lemma; run when the brief shows reduction or widening work on the hot path. Representation changes (Montgomery/Barrett) touch the cpoly dependency and are gated, not free
---

# Strategy: Word Arithmetic

One strategy of the optimization loop. Invoked by the `lean-opt` driver with a
target definition and its `arklib-analyze` brief; delivers a candidate under
the opt-contract that `lean-opt` owns: `Foo.opt` in `hachi/lean/Opt.lean` plus
the proved `Foo.opt_eq_spec`. A word-level variant usually lives on a word
carrier, so its lemma takes the commutes-through-representation form the
opt-contract allows (`toK (Foo.opt w) = Foo (toK w)` under `Red`), using the
representation maps `hachi/lean/` already owns: `toK` and `Red` in `Field.lean`,
`coeffK` and `Wf` in `Ring.lean`.

## The one rule: the field is a dependency, so the words to work on are `Rq`'s

`Fp` is not this crate's to change. It comes from `cpoly`, pinned by `rev`, and
it arrives with its own Lean equivalence proofs; reusing rather than
reimplementing it is a hard rule of the project (`hachi/src/lib.rs`, NOTES.md
§ "The cpoly dependency"). So this strategy's material is the layer *above* the
word: the coefficient vectors of `Rq`, where `hachi/src/ring.rs` performs one
`Fp` operation — and therefore one reduction — per coefficient pair, and where
the accumulator is this crate's own. `Rq::mul` at `N = 64` does 4096
multiplications and 4096 additions or subtractions, each carrying its own
`% P`: about 8192 divisions per product, all of them ours to restructure.

A variant that changes what the *words mean* — Montgomery form, Barrett with a
different stored range — changes `Red` and `toK` for every operation at once,
and here it does so inside a pinned dependency whose Lean layer would have to
be re-proved and whose `rev` bump is a bench re-baseline
(`hachi/Cargo.toml` § dependencies). Propose it only as a flagged,
driver-gated proposal (ledger tag `TODO(P3)`), never as a normal candidate.

## Checked arithmetic: the headroom claim is a proof obligation

Aeneas models Rust arithmetic as **checked**. Every `+`, `*`, cast and index in
the extracted model returns `Result`, so a variant that widens or delays
reduction owes a proof that each of those steps is `ok` — and the headroom
inequality is not documentation, it is the hypothesis that proof consumes. The
pattern is already in the audited library: `Ring.lean`'s specs carry `Wf`/`Red`
precisely to discharge the `u64` no-overflow obligation inside `Fp::add`, and
`mul_spec` needs one more fact the others do not — that `i + j` cannot overflow
`Usize`, because both indices are below `N = 64`.

Four obligations to expect, and to name in the candidate note:

1. every accumulation step is `ok` at the widened width;
2. the final reduction lands back in `Red`, so the result is a legal `Fp`;
3. index arithmetic stays inside `Usize`;
4. each `as u128` is a modelled cast (`lift (UScalar.cast .U128 …)`) and still
   a step the proof walks through.

**Unsigned subtraction is a failure, not a wraparound.** `X^N ≡ −1` means the
negacyclic product subtracts half its terms, and an unsigned accumulator cannot
hold that: `acc - term` with `acc < term` is `Result.fail` in the model. The
honest shapes are two accumulators (a plus pile and a minus pile, differenced
once at the end) or an additive bias large enough to keep every partial sum
non-negative — and the `ok` proof covers whichever is chosen.

## Headroom for the Hachi prime, from arithmetic rather than measurement

`P = 2^32 − 99 = 4294967197` (`cpoly`'s `field::P`; the same value as
`params::Q`).

* `(P−1)² = 18446743214716102416 < 2^64`, with about `2^40` to spare — so one
  product of two reduced representatives fits `u64`. This is `Fp::mul`'s own
  no-overflow argument, stated in its docstring.
* `2·(P−1)² > 2^64` — **two** unreduced products already overflow `u64`. Any
  delayed-reduction accumulation therefore goes to `u128`.
* `64·(P−1)² ≈ 2^70` and `4096·(P−1)² ≈ 2^76`: one convolution slot, and even
  the whole product, accumulate in `u128` with more than 50 bits unused.
* `u128` is not a guess here. `commit::l2_norm_sq` already accumulates in it
  because it must, and NOTES.md § "What the extraction of the four modules
  actually looks like" shows the extracted form — checked `mul`, checked `add`,
  an explicit modelled cast.

## What it attempts

* **Delayed reduction.** Accumulate a slot's contributions at `u128` and reduce
  once: for `Rq::mul` that is 64 terms per output slot, replacing about 8192
  reductions with 64 slots' worth. The headroom inequality goes in the note,
  and becomes a lemma hypothesis when it depends on input sizes rather than on
  `Red` alone.
* **Conditional-subtract folds** in place of a modular operation on a value
  whose range the brief bounds. `commit::centered_abs` is the shape already in
  the crate: `if v <= q/2 { v } else { q - v }`, no `%` at all.
* **Widening discipline** chosen from stated inequalities, not defensively.
  Both directions are already exemplified: `l2_norm_sq` *needs* `u128` (a
  centered coefficient reaches `q/2 ≈ 2^31`, so 64 squares overflow `u64`),
  while `l1_norm` does not (64 terms below `2^31` sum below `2^37`). Each
  docstring states its inequality; that is the standard a note here meets.

## Invariants to keep green

* The opt-contract (owned by `lean-opt`) is met; word-carrier lemmas go
  through the *existing* representation maps only.
* `Red` and `Wf` stay the invariants they are — no candidate changes what a
  newtype stores, and nothing edits the `cpoly` field layer, without the
  gated-proposal route.
* Every headroom claim in the note is an inequality with numbers and a stated
  `ok` obligation, never "fits".
