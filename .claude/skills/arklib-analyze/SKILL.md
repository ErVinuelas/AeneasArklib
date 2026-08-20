---
name: arklib-analyze
description: Producing the optimization brief for a targeted ArkLib definition — the definition chain behind the notation, the parameter values the brief is computed at, the semantics risks (overflow headroom, partiality, checked-arithmetic traps), the cost model, and which opt-* strategies apply; the target is handed in, never chosen here
---

# Analyzing an ArkLib Definition

For the first stage of the loop: a *targeted* Lean definition goes in, an
optimization brief comes out. The target arrives from upstream — the user, the
`perf-loop` driver, a route skill. **Choosing what to translate or optimize is
not this skill's job**; if no target is named, stop and ask, do not scan for
one.

Read the definition from the pinned copy the proofs actually build against:
`hachi/.lake/packages/Arklib/`, at the rev `hachi/lake-manifest.json` records
for `Arklib` (`e92dc315f453db88dd7351c88e889caf0e6bf269` today, matching the
commit in `hachi/lakefile.lean`). There is no second checkout — no browsing
clone at the repo root — so the pinned copy is both the readable one and the
authoritative one. Note the two spellings: the *package* directory is
`Arklib`, the *library* inside it is `ArkLib`, so paths read
`hachi/.lake/packages/Arklib/ArkLib/…` and imports read `import ArkLib.…`.

## The one rule: every claim in the brief cites the line it was read from

The brief is what the optimization agents act on. An asymptotic bound, a "this
cannot overflow", or a "the inner sum is the hot path" that was guessed rather
than read sends the optimization agents optimizing fiction — and unlike a wrong
benchmark, a wrong brief fails silently twice (the candidates it inspires still
measure honestly, but the strategies never aim at the real cost). Cite
`file:line` of the pinned copy for every claim; if a claim needs a lemma (a
value range, an invariant), name the lemma.

`hachi/src/` already cites the specification per item (`/// … (spec:
\`Rq.constRq\`, \`Rq.lean:353\`)`). Those citations are at the same pinned rev,
so they are worth reading first — and a brief that *disagrees* with one says so
explicitly rather than quietly picking a side.

## Producing the brief

1. **Unfold the notation.** Write down the chain from the surface syntax to
   the computation: which instance `*` resolves to, what the definition's body
   really is after the subtype/`ofFn`/`Finset.sum`/typeclass layers. The ring
   product is the worked shape: `a * b : Rq Φ` → `Mul (Rq Φ)` instance
   (`ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:110`) → `Rq.mk Φ (a.1 * b.1)`
   (`Rq.lean:96`) → `Φ.reduce (a.1 * b.1)`, and `reduce p = p.modByMonic Φ.φ`
   (`CyclotomicRing/Core/Basic.lean:67`), the inner product being CompPoly's
   `CPolynomial` multiplication. The translation layer works from this chain,
   not from the pretty notation.
2. **Parameters — say what the brief is computed at.** ArkLib is generic in
   all four of `(q, α, b, digits)` and in the six `PublicParams` shapes, and
   pins none of them (`NOTES.md` § "Chosen parameters"). `hachi` is the
   opposite by design: no type parameters over ring or field, every parameter a
   `const` in `hachi/src/params.rs`, so each equivalence proof instantiates a
   generic statement at fixed values. A cost model or an overflow bound is
   therefore a claim *at particular numbers*, and the brief names them:
   `Q = 2^32 - 99` (the Hachi prime, **pinned** by the `cpoly` dependency's
   `Fp`), `RING_DEGREE = 64` (α = 6, **chosen**, spec-unconstrained),
   `GADGET_BASE = 2` / `GADGET_DIGITS = 32` (**chosen**, and 32 forced by
   `q ≤ b ^ digits`), the four dimensions 4/2/2/2 (**chosen** smallest
   non-degenerate), `GAMMA = 1` and `BETA_SQ = 8192` (**derived** from the
   spec's norm lemmas). The pinned/chosen/derived split is recorded per
   constant in `params.rs` and summarized in `NOTES.md` § "Chosen parameters"
   and § "The dimensions and the norm bounds" — carry it, because a *chosen*
   value moving is a one-line diff and a *derived* one must be re-derived.
3. **Semantics risks — the section that must never be thin.**
   * *Value ranges and overflow headroom.* Aeneas models Rust arithmetic as
     checked: every `+`/`*`/index returns `Result`, and a spec triple
     `m ⦃ r => post r ⦄` already asserts `∃ r, m = ok r`
     (`hachi/lean/Field.lean`, header § "What a spec says"). So an overflow
     that "cannot happen in practice" is a *proof obligation*, and the brief
     writes the arithmetic out in numbers rather than adjectives. The base
     case is stated there: `Red u` is `u.val < q`, `q < 2^32`, so a sum of two
     reduced words is below `2^33` and a product at most
     `(q-1)² < 2^64`. Where a new width appears, do the same work —
     `commit::vec_l2_norm_sq` is `u128` because a centered coefficient can
     reach `q/2`, so one squared coefficient approaches `2^62` and a vector of
     them overflows `u64` (`hachi/src/params.rs`, `BETA_SQ`).
   * *Partiality.* Division, `Fin` arithmetic, subtraction on `ℕ`, functions
     defined by well-founded recursion — anything whose Lean totality is
     non-obvious becomes a precondition or a representation choice downstream.
     Locally this also covers *constants*: Aeneas models a `const` shift or
     subtraction as fallible, which is why `RING_DEGREE` is the literal `64`
     and not `1 << RING_LOG_DEGREE`, and `GAMMA` the literal `1` and not
     `GADGET_BASE - 1` (`params.rs`, `RING_DEGREE` and `GAMMA`). A derived-looking
     constant in a translation is a `Result` in every Lean use of it.
   * *Exactness traps.* Note where the definition branches on equality of
     field elements (`Rq::equals` compares words through `Fp::to_u64` so that
     exactly one notion of equality exists per type), on degenerate sizes
     (`n = 0`, empty vectors, one block), or on a norm threshold. The two
     derived bounds here are **tight** — an honest opening sits exactly on
     `GAMMA` and on `BETA_SQ` (`NOTES.md` § "The dimensions and the norm
     bounds") — so a corpus that stays comfortably inside them tests nothing.
     Two spec-shape traps are already documented and must not be
     re-guessed: the digit decomposition is *not* balanced (plain base-`b`
     digits of the canonical representative; the centering is in the *norm*,
     and the side condition `b - 1 ≤ q/2` is the tell — `NOTES.md` § "The
     digits are not balanced"), and the specification's two digit counts
     coincide here at `b = 2` (`NOTES.md` § "One digit count, not two").
4. **Cost model.** Count ring and field operations as a function of the size
   parameters; name what dominates and what allocates. Above the ring
   everything is `ring::mul` in a loop: `mul` is the schoolbook `O(N²)`
   negacyclic convolution at `N = 64` (`hachi/src/ring.rs`, `Rq::mul`), a
   matrix-vector product is `rows · cols` of those, and the norms are
   invisible beside it. Say it in the terms the bench thinks in
   (`<module>/<op>` cases). For sizing, `NOTES.md` § "The first benchmark run,
   and what it says about the harness" is the only measurement this repository
   has — `ring/mul` ≈ 8.5 µs, `linalg/mat_vec_mul` ≈ 2.29 ms — and the same
   section says plainly that these are sizing information and *not* a baseline
   to compare a future candidate against, because on that host byte-identical
   crates read up to 59% apart. So a cost model here is an operation count
   with a first-principles floor behind it (the floor method is `rust-bench`'s)
   and never a predicted percentage.
5. **Strategy candidates.** Name which `opt-*` strategy skills plausibly
   apply (tail-recursion shaping, list→array, word arithmetic, algorithm
   substitution, in-place buffers) and *why*, one line each. Pointers only:
   the strategies themselves live in their skills, and the brief must not
   duplicate them. A promising direction that matches no existing `opt-*`
   skill is still named, in the same one-line form, marked `(no skill yet)` —
   never invent a pointer to a skill that does not exist. Where the
   specification itself flags the direction, cite it: `Core/Basic.lean:72`
   carries `TODO add proper NTT multiplication here`, and `hachi/src/ring.rs`
   § "What is deliberately not here" says the schoolbook product is
   deliberate and that an NTT carries an equivalence obligation of its own.
6. **Representation notes.** Which existing Rust types the translation slots
   into: `Rq` (a `Vec<Fp>` newtype, exactly `RING_DEGREE` coefficients by
   construction), `PolyVec` / `PolyMatrix`, and `Fp` / `Ext4` **taken from the
   `cpoly` dependency, never reimplemented** — reuse of that field layer is a
   hard rule of the project (`hachi/src/lib.rs`, README § "The field layer
   comes from cpoly"). For a genuinely new carrier, propose with the reasoning
   pattern of the existing ones: small fixed dimension → named-fields struct
   so the extracted model is straight-line; dynamic length → `Vec` newtype
   whose constructors establish the shape invariant, since Aeneas cannot see a
   Rust privacy boundary and the invariant must also travel as a hypothesis on
   each `_spec` (`Wf` in `hachi/lean/Ring.lean`).

## Brief format

One markdown block, fixed headings, handed verbatim to `lean-opt` and
`lean-to-rust`:

```markdown
# Brief: <full ArkLib name>       (ArkLib @ <lake-manifest rev>)
## Definition chain               (notation → instances → body, file:line)
## Parameters                     (const values used, pinned/chosen/derived)
## Semantics risks                (ranges + headroom, partiality, traps)
## Cost model                     (op counts, allocations, dominant term)
## Strategy candidates            (opt-* names + one-line why)
## Representation                 (existing types to slot into, or proposal)
```

## Invariants to keep green

* The brief names the `lake-manifest.json` rev it was read at; a brief against
  another checkout is invalid.
* Every claim carries its `file:line` in `hachi/.lake/packages/Arklib/`, or a
  lemma name.
* The `## Parameters` section is never empty: a generic ArkLib statement has no
  cost and no headroom until it is instantiated, and this repository is
  concrete on purpose.
* When word representations are in play, the overflow-headroom arithmetic is
  written out — numbers, not adjectives — because Aeneas makes it an obligation.
* Strategy detail stays in the `opt-*` skills; the brief only points.
* No target selection. A brief exists because something upstream targeted the
  definition.
