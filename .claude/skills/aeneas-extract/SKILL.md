---
name: aeneas-extract
description: Running and triaging the Rust→Lean extraction (make extract) — the charon+aeneas pin discipline, the `--include 'cpoly::_'` whitelist, the determinism check, the post-extract audits (axioms, whitelist transparency, loop-state shapes, name collisions), and the supported-constructs ceiling table with the probe procedure that grows it
---

# Extracting Rust to Lean

For regenerating `hachi/lean/Generated.lean` from `hachi/src/`, and for
diagnosing what went wrong when that fails. Read this **before** running
`make extract` as part of the loop, and read the Makefile's comments — they
are the design, this file is the procedure. `Generated.lean` is derived
output: **never hand-edit it**; every change to it goes through the Rust and
a re-extraction.

## The one rule: the extraction is deterministic, or it is broken

`make extract` on unchanged Rust must report
`==> lean/Generated.lean unchanged` — the target copies the previous
`Generated.lean` aside and `cmp`s after regenerating. That check is the
contract everything downstream leans on: the proofs are about *this*
extraction, and an extraction that drifts without a Rust change means the
toolchain moved. If `unchanged` unexpectedly becomes `regenerated`, stop and
find out which binary changed (`make check-toolchain` verifies the pin — the
`aeneas` binary self-reports its commit) before trusting anything else.
Determinism is also the last step of every idiomatization pass: re-run
`make extract` and demand `unchanged`.

Verified in this repository on 2026-08-20: charon + aeneas at
`nightly-2026.07.26-3a8586f`, run over the committed `hachi/src/`, reproduced
the committed `Generated.lean` **byte for byte** (2263 lines, zero diff),
including the ten `Source:` doc lines that name the `cpoly` git checkout.
Those are written as
`/cargo/git/checkouts/<url-hash>/<short-rev>/cpoly/src/field.rs` — a path
charon normalizes rather than the local `CARGO_HOME`, so the cross-crate
whitelist does not cost determinism across machines. It does mean the
`cpoly` **rev is visible in the artifact**: bumping the `rev` in
`hachi/Cargo.toml` regenerates those ten lines with no code change.

## Mechanics

```
make extract                # charon → generated.llbc → aeneas → hachi/lean/Generated.lean
make extract CHARON=<path> AENEAS=<path>   # e.g. from a worktree, pointing at the
                                           # main checkout's ./toolchain binaries
```

* The pin is `AENEAS_TAG` / `AENEAS_COMMIT` in the Makefile
  (`nightly-2026.07.26-3a8586f`, commit `3a8586f`); `make setup` downloads
  the release binaries into `./toolchain/`, and `check-toolchain` fails on
  any mismatch between pin and binary. `make setup` additionally checks the
  *other* direction: the aeneas Lean backend Lake checked out at
  `hachi/.lake/packages/aeneas` must be a descendant of `AENEAS_COMMIT`.
  `Generated.lean` is only valid against the Aeneas version that produced
  it, so the binaries, `AENEAS_TAG` and the `require aeneas` in
  `hachi/lakefile.lean` move together or not at all.
* **Aeneas here is upstream and unforked**, unlike AeneasCompPoly's. This
  nightly's Lean backend requires Lean/Mathlib v4.31.0, which is exactly
  ArkLib's pin; AeneasCompPoly needs a fork only because CompPoly moved to
  v4.32.0. So there is no fork to patch and no fork policy to pay back —
  see `NOTES.md` § "Upstream aeneas, no fork". An ArkLib bump to v4.32.0
  would flip this repository into AeneasCompPoly's situation and require an
  aeneas release on that Mathlib.
* `--include 'cpoly::_'` is not optional. See the next section.
* Aeneas names the Lean module after the `.llbc` basename —
  `generated.llbc` is what makes `import Generated` resolve. Renaming the
  file renames the module the proofs import.
* charon resolves its rustc from the `rust-toolchain` file *beside the
  charon binary*, not from the repo — overriding `CHARON=` moves that too.
  `BENCH_TOOLCHAIN` in the Makefile is checked against that same file, so a
  charon bump that moves the channel is also a benchmark re-baseline.
* After a successful extraction: `make build` re-checks every proof. Adding
  a module under `hachi/lean/` also means adding it to `roots` in
  `hachi/lakefile.lean`, or Lake silently does not build it.

## The `cpoly` whitelist — the local hazard with no upstream analogue

The field layer is a *cargo dependency*, not vendored source, so charon has
to be told to follow it: charon's default whitelist is the local crate.
Without `--include 'cpoly::_'` the extraction still **succeeds** and produces
a model that is worse than useless —

```lean
axiom cpoly.field.Fp : Type
axiom cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add : ...
```

an uninterpreted field with an uninterpreted addition, about which nothing
can be proved, plus axioms that would appear under every `#print axioms` in
`Check.lean` § 4 forever. charon warns (`extracted external, unknown
definitions`) and exits 0. `hachi/lean/Check.lean` § 2 asserts the
transparent form — `cpoly.field.Fp = Std.U64 := rfl`, and the exact `do`
body of each of the four `Fp` operator impls — so dropping the flag breaks
the build instead of quietly re-axiomatizing the field.

Two things to know before touching it:

* It is **not** `--extract-opaque-bodies`. That flag was the obvious first
  guess and is the wrong tool: it is global, so it also un-opaques
  `alloc::vec` and the rest of std, and aeneas then dies on mixed
  recursive declaration groups with no Lean file produced at all.
  `NOTES.md` § "The cpoly dependency" records all three extractions.
* The whitelist says which foreign items charon *may* translate, not which
  it does — it still only follows what the local crate **reaches**.
  Deleting the last caller of a foreign item removes it from the model, and
  an assertion in `Check.lean` about the vanished name may keep compiling
  (see § "The model contains what the crate *reaches*" in `NOTES.md`; this
  is why every file here sets `autoImplicit false`).
* Whitelist **completeness** is in the repository's trusted computing base
  (`README.md`): nothing checks it. A missed item becomes an `axiom`, which
  is visible only if someone reads for it. Audit 1 below is that reading.

## Post-extract audits — before `make build`, every time

<!-- ⚠️ SYNC RULE: source of truth is aeneas-idiomatic-rust "Staged workflow" step 3 -->

1. `grep -c '^axiom' hachi/lean/Generated.lean` — must be **0**. Any axiom
   means either a construct dragged an unmodelled `std` item into the
   trusted base, or the `cpoly` whitelist stopped covering something the
   crate reaches.
2. `cd hachi && lake env lean lean/Check.lean` (or the full `make build`) —
   § 2 is the whitelist-transparency assertion and § 2b the four modules'
   shapes. § 2 failing means the flag was lost; § 2b failing means a
   container newtype stopped being a `@[reducible]` `Vec` alias.
3. Diff the loop-state shapes against the previous generation:
   ```bash
   grep -oE "^ +\(fun \([a-z0-9_, ]+\)" hachi/lean/Generated.lean \
     | sed 's/^ *//' | sort | uniq -c | sort -rn
   ```
   Most states here are 2-tuples `(out1, i1)`; the known 3-tuples are the
   loops that carry a borrowed operand (`add_loop`, `sub_loop` thread `rhs`)
   and `mul_loop1_loop0`, which threads the accumulator vector. A tuple that
   grew breaks every invariant written about that loop — see the
   `aeneas-idiomatic-rust` failure modes.
4. Skim the new names for `Shared<n><T>` prefixes that collide across
   modules. The current model has **zero** of them, because every `hachi`
   operation is an inherent method rather than a by-reference trait impl;
   the hazard is latent and an `impl Add<&Rq> for &Rq` is what wakes it.
   A collision is a hard aeneas error, but near-misses deserve a rename
   before they become one.
5. `git diff -- hachi/lean/Generated.lean`. The file is tracked, so the
   regeneration is reviewable; read it rather than assuming it.

## Triage, by failure shape

* **Hard error: "The chosen name is already in the names set" —**
  `Shared<n><T>` collision from by-reference trait impls on same-named types
  in different modules. Fix by making the *type names* distinct, never by
  contorting the API.
* **Warning: `could not find the information for item 'X'` / output
  "contains extracted external, unknown definitions" —** either the
  construct has no Aeneas model, or a foreign item fell outside
  `--include 'cpoly::_'`. Check which: a `cpoly::` name means the
  whitelist; anything else means the construct. For a construct, consult
  the ceiling table below and reshape the Rust per the `lean-to-rust`
  conventions so it disappears. There is **no aeneas fork here to patch** —
  adding a local model would mean creating one, which is a much larger
  decision than the reshape it dodges.
* **`unchanged` became `regenerated` with no Rust change —** read the diff
  before alarming. Three causes, in order of likelihood:
  1. *Doc-comment drift.* Every changed line is a `Source: '…', lines N`
     comment: the committed artifact is stale, because a comment-only Rust
     edit landed without a re-extraction. The fix is to commit the
     regeneration. This is the common case and it is cheap to confirm —
     `diff … | grep '^[<>]' | grep -v "Source: "` must come back empty.
     (AeneasCompPoly measured this shape on 2026-08-10: 174 changed
     line-pairs, all `Source:` spans. Measured here on 2026-08-20 after
     `Mirrors` docstring lines were added to `hachi/src/`: 304 changed
     line-pairs, all `Source:` spans, zero code lines, zero axioms.)
  2. *A `cpoly` rev bump.* The ten `Source:` lines for `cpoly::field` carry
     the short rev, so bumping `hachi/Cargo.toml` regenerates them. That
     bump is also a bench re-baseline (`hachi/Cargo.toml` says why).
  3. *Toolchain drift.* Extracted **code** changed: `make check-toolchain`,
     compare `AENEAS_TAG`, find which binary moved.

## The ceiling table

What the pinned toolchain supports, **measured, not guessed**. The
idiom-level verdicts live in `aeneas-idiomatic-rust` (free idioms, strict
simplifications, and the forbidden list: iterator adaptors,
`Vec::is_empty`, `derive(Default)` on `Vec`-holding structs, `vec![a, b]`
list form, `truncate`/`pop`/`last`/`first`/`clear`/`extend`,
`checked_shl`).

### Inherited from AeneasCompPoly

Probed there on 2026-08-10 and 2026-08-12 against
`nightly-2026.07.26-3a8586f` — **the same aeneas nightly this repository
pins**, one construct per item, all four checks green. The dates and the
machine are upstream's; the toolchain is ours, which is why the rows carry
over rather than needing a re-probe.

| Construct | Extracts to | Note |
|---|---|---|
| `Vec::with_capacity(n)` | `alloc.vec.Vec.with_capacity` | pre-sizing accumulators is free |
| local `[u64; 4]`: repeat-init, index read/write | `Array Std.U64 4#usize`, `Array.index_usize` / update | fixed-size accumulators work |
| `pub const TABLE: [u64; 4]` + indexing | `Array Std.U64 4#usize` def + `index_usize` | precomputed tables work |
| `(a as u64) * (b as u64)` widening, `a as u32` narrowing | `UScalar.cast` | the word-arith primitive |
| `>>`, `&` on `u64` | pure/`ok` scalar ops | shifts and masks fine |
| write through `&mut [u64]`: `v[i] = …` in a counter loop | `@[rust_loop]` defs, state `(Slice U64) × Usize` | in-place mutation keeps the 2-tuple |
| `&mut Vec<u64>` parameter + `push` | ordinary `Vec.push` calls | out-parameters work |
| `break` from a counter loop | `ControlFlow` loop encoding | |
| early `return` inside a loop | `ControlFlow` loop encoding | |
| `a.wrapping_mul(b)` | `ok (core.num.U64.wrapping_mul a b)` — **pure** | wrap-around arithmetic without `Result` friction |
| `u128` intermediates: cast, `*`, `>> 64`, cast back | `UScalar.cast .U128` + U128 scalar ops | Barrett/Montgomery high-half pattern available |
| `a.checked_add(b)` + `match` on the `Option` | `U64.checked_add` | `checked_shl` is the axiom, not the whole `checked_*` family |
| self-recursive `fn` | `def … partial_fixpoint` | extracts clean, zero axioms — but it is a **different proof shape**: fixpoint unfold/induction, not the `@[rust_loop]` template |
| `a + b` on `u128` | monadic `Std.U128` add in `Result` | standard overflow-checked shape |
| `<` / `>=` on `u128` | **pure** boolean comparisons | no `Result` friction in guards |
| `a & mask`, `a >> 32` on `u128` | pure lifted `&&&` + monadic `>>>` (shift RHS is an `#i32` literal) | mid-shifts work, not just `>> 64` |
| `a % b` on `u128`, constant divisor | monadic `%` with `#u128` literal | divisor-nonzero side condition trivially dischargeable |
| guarded `usize` sub in a counter loop: `if j <= k { k - j }` | monadic sub under a pure guard; loop state stays a **2-tuple** | the k-outer convolution shape is safe |
| range subslices `&p[..end]`, `&p[start..]` | `core.slice.index.SliceIndexRange{To,From}UsizeSlice.index` | modelled instances with `step_spec` lemmas in the Aeneas Std; out-of-range indices `fail` in the model where Lean's `Array.extract` clamps — clamp explicitly first |

### Observed in this repository

From the extraction of the four modules; `NOTES.md` §§ "Aeneas surprises",
"What the extraction of the four modules actually looks like", "Derives
extract, and are still not worth it", "The cpoly dependency" are the record.

| Construct | Extracts to | Note |
|---|---|---|
| `pub struct Rq(Vec<Fp>)` — single-field newtype over `Vec` | `@[reducible] def ring.Rq := alloc.vec.Vec cpoly.field.Fp` | free: a statement about an `Rq` *is* one about the `Vec`. `Check.lean` § 2b asserts all three container newtypes |
| `<<` in a `const` | `def params.RING_DEGREE : Result Std.Usize := 1#usize <<< …` | **fallible**, so unusable as a constant. Also true of `-` (`GAMMA`) and `*` (`BETA_SQ`): in `params.rs`, values are literals and relations are checked |
| `u128` accumulator + `x as u128` | `lift (UScalar.cast .U128 i)` then checked `*`, `+` | load-bearing in `commit::l2_norm_sq`: a `u64` accumulator would *fail* on the long inputs the verifier must reject |
| nested counter loops | `mul_loop0`, `mul_loop1`, `mul_loop1_loop0` — positional | the naming is the proof plan; the inner state is `ControlFlow (Rq × Vec Fp × Usize)` |
| `#[derive(Debug, PartialEq)]` on a newtype | transparent `fmt` via `Dyn.mk` / `debug_tuple_field1_finish` | **zero axioms** (Aeneas models `core::fmt`); opaque-function count 11 → 16. Declined anyway, for model hygiene and one-equality-per-type |
| `Vec::new`, `push`, `len`, `index`, `index_mut` | modelled operations | `clone`, `truncate`, `is_empty` are **not**, which is why `Rq::copy` is a `push` loop |
| cross-crate foreign newtype with a *private* field, under `--include` | `@[reducible] def cpoly.field.Fp := Std.U64`, real bodies | the Workstream 0 finding; § 2 of `Check.lean` pins it |
| cross-crate foreign multi-field struct, under `--include` | a real `structure` with real projections | measured on `Ext4`, which has since left the model — the whitelist follows only what the crate reaches |
| `--extract-opaque-bodies` | **nothing** — "Mixed declaration groups … are not supported yet" | aeneas fails outright; use the scoped `--include` |

Unprobed (add a measured row on first contact — closures, const generics,
generic functions, `match` on custom enums, `u128` division, trait objects,
…). And the permanent ceiling: no `unsafe` (the crate `forbid`s it), no SIMD
intrinsics, no inline asm — nothing without a model, ever.

## Growing the table: the probe recipe

<!-- ⚠️ SYNC RULE: source of truth is aeneas-idiomatic-rust "The one rule: probe, do not reason" -->

The recipe is `aeneas-idiomatic-rust`'s: a scratch crate in the session
scratchpad, **one construct per item** plus a `use_all()` caller so charon
cannot drop anything as dead code, then charon + aeneas + the four checks.
Two minutes, decisive. Probing a *cross-crate* construct means giving the
probe the `cpoly` dependency **and** the `--include 'cpoly::_'` flag —
without it the probe reports an axiom the real extraction would not produce.
Every probe's verdict lands in the "Observed in this repository" table with
its date and toolchain tag; every extraction failure on a new construct is a
probe that hasn't been written yet.

## Invariants to keep green

* `Generated.lean` is never hand-edited; it **is** tracked, so a
  regeneration shows up in `git diff` — read that diff.
* A no-op re-extraction reports `unchanged`.
* Zero `^axiom` lines in `Generated.lean`, always.
* `--include 'cpoly::_'` is never dropped, and `Check.lean` § 2 is never
  weakened to accommodate its loss.
* `make build` green after every regeneration — a regeneration without a
  proof re-check is half-done. It also re-checks nothing under
  `hachi/lean-wip/`, which is not a Lake root: statements there that a
  re-extraction invalidated fail silently, so `lake env lean
  lean-wip/<File>.lean` on each of them belongs to the same pass.
  (A worktree without the `.lake` package cache cannot run either; the
  re-check is then *deferred to the main checkout*, and it still blocks
  "done".)
* Every new-construct contact adds a measured row to the ceiling table, with
  date and toolchain tag.
* No local Aeneas model is ever added to dodge a reshape — that would mean
  forking upstream aeneas, which this repository deliberately does not do.
