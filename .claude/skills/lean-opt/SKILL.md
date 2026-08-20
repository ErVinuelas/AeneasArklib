---
name: lean-opt
description: Driver for the Lean-side optimization stage — given a targeted ArkLib definition and its arklib-analyze brief, select opt-* strategies (highest tier first), fan out one prover agent per strategy, and enforce the opt-contract (Foo.opt in hachi/lean/Opt.lean + proved Foo.opt_eq_spec, axiom-clean) on every candidate; produces candidates for perf-loop to translate and bench
---

# Driving the Lean-Side Optimization

For stage B of the loop: a target definition and its brief (`arklib-analyze`)
come in; contract-satisfying candidates come out, ready for `lean-to-rust`.
The target arrives from upstream (`perf-loop`, a route skill, the user);
choosing it is not this skill's job. This driver selects and sequences the
`opt-*` strategy skills and **contains no strategy of its own** — anything
procedural about a rewrite belongs in the strategy skill, or the ledger
cannot attribute wins.

## The one rule: no lemma, no candidate

A fast def without its proved `opt_eq_spec` is not a candidate, it is a
liability — the lemma is the down payment that keeps the eventual Aeneas
proof at trivial-translation distance (the project's R3 bet). Reject outright
(`lemma-failed`), record the ledger row, move on. Never forward an unlemma'd
def to translation "to see how fast it would be": the bench slot it burns is
cheap, but the precedent — champions the proof layer cannot pay for — is the
exact debt spiral the inner loop exists to prevent. In this repository the
debt is unusually concrete: an accepted champion's Rust swap breaks the
`_spec`s in `hachi/lean/Ring.lean` that are written about the *current* loop
structure, and `make build` is a hard gate, so the proof layer is the thing
standing between a champion and main.

## `Opt.lean` does not exist yet — creating it is step zero

`hachi/lean/` holds `Generated`, `Field`, `Ring`, `Check` and nothing else.
The first candidate this skill produces therefore does two things upstream
never had to:

1. **Create `hachi/lean/Opt.lean`** — importing `Field` and `Ring` (it is
   stated against their `toK` / `coeffK` / `Wf` / `negConv`), with
   `set_option autoImplicit false` at the top like every other file here.
2. **Add `` `Opt `` to `roots` in `hachi/lakefile.lean`**, between `` `Ring ``
   and `` `Check ``, and `import Opt` from `hachi/lean/Check.lean`.

Step 2 is not bookkeeping. Lake counts a module as part of a library only when
one of the `roots` is a *prefix* of its name, and this library's modules are
flat under `srcDir := "lean"` with no module named after the library to reach
the rest through — so an unlisted `Opt.lean` is **silently not built**. The
failure that produces is the worst available: a lemma that looks proved,
sits in the audited directory, and is never checked again. It is the same
mistake `hachi/lean-wip/` exists to keep visible (see its `README.md`, whose
promotion procedure is exactly root + import + `#print axioms` line), and the
lakefile's own comment on `roots` spells the rule out. Verify by reading
`lake build`'s output for the module, not by assuming it compiled.

## The opt-contract (source of truth)

Every candidate consists of a change to `hachi/lean/Opt.lean`, its
`hachi/lean/Check.lean` § 4 audit line, and a candidate note. In full:

1. **Placement + naming.** `Foo.opt` is declared in `hachi/lean/Opt.lean`,
   inside `namespace HachiEquiv.Opt`, its name extending the **item** it
   replaces rather than the spec (`Rq.mul.opt` for `hachi::ring::Rq::mul`).
   That is a deliberate difference from upstream, where spec def and Rust item
   shared a name: here the spec is ArkLib's generic `Mul (Rq Φ)` and its name
   is not a legal prefix for ours. There is also no typeclass to strengthen —
   this crate is concrete by design (no type parameters over ring or field,
   every parameter a `const` in `hachi/src/params.rs`), so the corresponding
   gate is about *representation* instead: a candidate that wants a different
   carrier (packed words, Montgomery form, an NTT domain) goes through
   `aeneas-equivalence-bridges` before any relation is invented, and its note
   names the representation map and its round-trip lemma.
2. **The lemma.** `Foo.opt_eq_spec` connects the new def to the specification
   side **this repository's proofs actually reach**. Two accepted shapes:
   * *direct*: `Rq.mul.opt … = <audited definition> …`, when the opt def is
     written on the carrier an existing audited definition already uses;
   * *commutes-through-representation* (the usual one here): the opt def
     preserves the representation invariant and agrees coefficientwise with
     the audited characterization — for `mul`, `Wf`-preservation plus
     `∀ k, k < N → coeffK (Rq.mul.opt a b) k = negConv a b k`, where `Wf`,
     `coeffK` and `negConv` are `hachi/lean/Ring.lean`'s own
     (`negConv` is the `k`-th antidiagonal of the raw product minus its
     `(N + k)`-th — `(a·b) mod (X^N + 1)` written out). Use only the
     representation maps the audited files already own: `toK`, `Red`
     (`Field.lean`), `coeffK`, `Wf`, `contrib`, `rowsSum`, `negConv`
     (`Ring.lean`). `toRq` / `toRq_coeff` / `toRq_eq_iff` in
     `hachi/lean-wip/RqBridge.lean` are proved but **not yet audited**, so a
     lemma resting on them rests on unchecked ground: prefer the `Ring.lean`
     level, and if the `Rq Φ` level is genuinely needed, say so in the note
     and treat the bridge's promotion as a prerequisite.

   Note what this lemma is *not*. The audited statements about the shipped
   code are Aeneas triples over the extracted monadic model
   (`ring.Rq.mul a b ⦃ z => Wf z ∧ ∀ k, k < N → coeffK z k = negConv a b k ⦄`).
   At candidate time no Rust exists yet, so `opt_eq_spec` is an equation
   between *pure* Lean functions — the algebra, settled early and cheaply.
   The triple is the outer pass's obligation (`verify-campaign`), and it is
   cheap only because this lemma already exists.
3. **Proof discipline.** Sorry-free; `#print axioms Foo.opt_eq_spec` shows at
   most `[propext, Classical.choice, Quot.sound]` — the three the README's
   trusted-computing-base table names, and the exact set `Check.lean` § 4
   already reports for Field and Ring. `native_decide`
   (`Lean.ofReduceBool` / `Lean.trustCompiler`) is banned: it would add the
   Lean compiler to a TCB that table does not include. The `#print axioms`
   line lands in `Check.lean` § 4 in the same change — that is what makes a
   `sorryAx` a build failure (`make build` greps the log for it) rather than
   silent debt.
4. **Translatable body.** The def stays inside `lean-to-rust`'s conventions
   table — it will be translated *unchanged* — and inside this crate's own
   extraction-facing style rules, which are narrower than general idiomatic
   Rust and are written down in `hachi/src/lib.rs` § "Style notes":
   index-based `while` loops with an explicit `usize` counter (a `for` is
   modelled but turns the loop state into a `Range` iterator, and the loop
   state is what every invariant is about), no iterator adaptors, no
   `Vec::is_empty` / `truncate` / derived `Default`, bit tests written with
   `/` and `%`. `NOTES.md` § "What the extraction of the four modules actually
   looks like" is the measured version of the same list: `Vec::new`, `push`,
   `len`, `index`, `index_mut` are modelled and `clone` is not. A shape needing
   a new correspondence names it in the note (the row lands in `lean-to-rust`
   on acceptance); a shape that cannot be trivially translated is
   `not-translatable`, rejected.
5. **No new value-level preconditions without a gate.** A variant equal to
   the spec only under an input hypothesis the original does not have makes
   the eventual composed theorem weaker, and it will also fail the bench's
   digest equality on the seeded corpus (`case!` asserts `cand` and `now`
   agree *before* timing anything). `Wf` — exactly `N` coefficients, every
   word reduced — is the precondition the audited specs already carry and may
   be assumed; anything beyond it is, like `prove-sorry`'s weakening gate, a
   flagged proposal requiring explicit user sign-off, never a normal
   candidate.
6. **The candidate note.** Strategy skill used, what changed, expected effect
   quantified from the brief (op counts, allocation counts — with the brief's
   `file:line` citations), representation-change rationale, any
   new-correspondence request. The quantified prediction is a **ranking**
   input only: `perf-loop`'s accept rule never reads it.

## Upstream first — and what "upstream" means here

Before any rewrite, read the pinned specification at
`hachi/.lake/packages/Arklib/` (rev per `hachi/lake-manifest.json`) for work
already done: an alternative characterization of the target, or the algebraic
identity your candidate needs. If ArkLib proves that identity, cite it as a
step of `opt_eq_spec` instead of re-proving it.

What does **not** transfer is upstream's "upstream-variant candidate" — a
reference to a ready-made faster definition, no `Opt.lean` change. CompPoly is
an executable spec library, so `eval₂Horner` was itself a translation target.
ArkLib is a mathematical library: its definitions are generic in
`(q, α, b, digits)` and written through `Polynomial`, `modByMonic` and
subtypes, which is a specification, not a candidate. So expect the def to be
yours and the *lemma* to be where reuse happens. Where the specification flags
a direction it has not taken, that is a pointer and not a gift:
`ArkLib/…/CyclotomicRing/Core/Basic.lean` carries
`TODO add proper NTT multiplication here`.

One feasibility check the running example needs, because it kills the obvious
tier-1 move: a radix-2 negacyclic NTT at `N = 64` needs a primitive
`2N = 128`-th root of unity, hence `128 | q - 1`. Here `q = 2^32 - 99`, so
`q - 1 = 4294967196` has 2-adic valuation **2** — the largest 2-power root of
unity in `F_q` has order 4, and moving to `cpoly`'s quartic extension does not
rescue it (`v₂(q⁴ - 1) = 4`). A candidate proposing "NTT" must therefore say
where its root of unity comes from; the transform-free routes (Karatsuba,
Toom, Nussbaumer) do not need one, and a parameter change is a spec-side
decision that `Check.lean` § 1 would have to re-discharge. Check this kind of
claim rather than inheriting it — the numbers above are `params::Q` and
arithmetic, not a measurement.

## Procedure

1. **Inputs**: target def, brief, and the set of strategies already tried on
   this target (from `perf-loop` / the ledger — which starts empty, so on a
   first target the answer is "none").
2. **Upstream check** (above).
3. **Tier selection** — high-level first, as a general rule: a
   complexity-class win dwarfs constant-factor tuning and changes which
   constants are worth tuning afterwards.
   * Tier 1 `opt-algo-swap` — different algorithm.
   * Tier 2 `opt-inplace-buffers`, `opt-tailrec-loops`, `opt-list-to-array`
     — same algorithm, better shape (parallel, they rarely collide).
   * Tier 3 `opt-word-arith` — word-level arithmetic under the fixed
     representation (last: it tunes whatever algorithm survived tiers 1–2).
   Each round emits the applicable-and-untried strategies of the highest
   tier that still has any; "applicable" is read from the brief's strategy
   section, never guessed. Prune harder than upstream would: every candidate
   costs a serialized `lake build` (next step), so a tier of four strategies
   is four sequential builds before anything is benched.
4. **Fan-out**: one Opus agent per selected strategy, each in its own git
   worktree (parallel candidates edit the same `Opt.lean`). The agents *write*
   in parallel; their **builds are serialized** — one `lake build` at a time,
   repo-wide, sharing the machine with any criterion session (`perf-loop`
   step 4). Hand out a build token rather than letting four `lake build`s
   contend: on this host `hachi/.lake` is 8.5 GB and a from-scratch check is
   hours (`NOTES.md` § "The Lean side does build here, it just takes hours":
   ~2700 Mathlib modules).
   A fresh worktree has no `.lake` at all, so transplant the cache before the
   first build. Upstream cloned it in seconds with `cp -Rc` (APFS clonefile);
   there is no equivalent here — this checkout is on **ext4**, where
   `--reflink` is unsupported and `cp` silently falls back to a full copy. So
   budget a real 8.5 GB copy per worktree (`cp -a hachi/.lake
   <worktree>/hachi/.lake`), check `df` first, and confirm it worked by
   reading the job count of the worktree's first `lake build`: it should be
   all-cached (upstream's transplanted worktree reported 2336 jobs, every one
   cached). Do not improvise a hardlink farm to save the space unless you have
   checked that nothing rewrites an olean in place — a corrupted parent cache
   costs hours to rebuild.
   Overlay uncommitted work with `git diff HEAD | git -C <worktree> apply`
   **plus** explicit copies of untracked files — `Opt.lean` before its first
   commit, and the `hachi/lakefile.lean` edit that lists it, which *is*
   tracked but is the one line without which the worktree builds nothing.
   Each agent gets: its strategy skill, the brief, the target's definition
   chain, this contract, and builds with `lake build` in `hachi/` until green
   (use `lean-lsp-mcp` when the MCP server is available; build-loop
   otherwise). Capture the `#print axioms` output as evidence.
5. **Contract enforcement** — mechanical, on evidence, before anything is
   forwarded: `Opt` in `roots` and imported by `Check.lean`, lemma present and
   sorry-free, axiom set exact, note complete, body inside the conventions
   table. Verdicts for the ledger: `contract-ok`, `lemma-failed`,
   `not-translatable`, `no-strategy-applies`, `contract-violation`,
   `build-failed`.
6. **Hand off** contract-ok candidates to `perf-loop` (translation, tests,
   bench are its pipeline, via `lean-to-rust` and the `rust-bench`
   candidate mode).

## Invariants to keep green

* `Opt.lean` never gains a def without its proved lemma and its `Check.lean`
  § 4 `#print axioms` line in the same change.
* `Opt` stays in `roots` and stays imported by `Check.lean`: an audited file
  that Lake does not build is worse than no file.
* No `sorry` under `hachi/lean/` at any point. Work that is not finished, or
  finished but not yet audited, belongs in `hachi/lean-wip/` under that
  directory's `README.md`.
* Every candidate's ledger row names exactly one strategy skill.
* Tier order is only ever advanced, never skipped downward mid-target, and
  "applicable" always cites the brief.
* Gated proposals (weakening, representation change) reach the user
  explicitly or die; they never ride along as normal candidates.
* Lean building and benching never overlap, and neither runs twice at once.
