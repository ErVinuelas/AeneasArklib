---
name: aeneas-idiomatic-rust
description: Making an Aeneas-extracted Rust crate idiomatic (newtypes, core::ops operators, methods, slices) without breaking extraction or the Lean equivalence proofs — which idioms are free, which inject axioms, where clippy's advice is wrong for the extraction, and how to repair the specs
---

# Idiomatic Rust Under Aeneas

For work on `hachi/src/` — turning transliterated-Lean Rust into Rust, while
`make build` stays green and no `sorry` appears. Read this **before** touching
`src/`, and read `README.md` § "Concrete, not generic" plus `src/lib.rs`'s
§ "Style notes" and the `[lints.clippy]` block in `hachi/Cargo.toml`, which
record the decisions this skill explains how to make.

## The one rule: probe, do not reason

Every prediction about what Aeneas does with a Rust idiom was wrong at least
once — including confident ones about newtypes, trait names, and loop shapes. A
probe takes two minutes and is decisive. Do it for **every** idiom you are unsure
about.

```bash
S=<session scratchpad>/probe             # never /tmp, never inside the repo
T=$(git rev-parse --show-toplevel)/toolchain
mkdir -p $S/src && cd $S
printf '[package]\nname = "probe"\nversion = "0.1.0"\nedition = "2021"\n[lib]\nname = "probe"\npath = "src/lib.rs"\n' > Cargo.toml
# ... write src/lib.rs exercising ONE idiom per item, with a `pub fn use_all()`
#     caller so charon cannot drop it as dead code ...
$T/charon cargo --preset=aeneas --dest-file p.llbc -- --lib
mkdir -p out && $T/aeneas -backend lean -dest out p.llbc
```

Check **all four** things, in this order — each catches a different failure:

1. **Did aeneas error?** A name collision is a hard failure, not a warning.
2. **Did aeneas warn** `could not find the information for item 'X'`, or
   `contains extracted external, unknown definitions`? Then `X` has no model and
   the idiom is off-limits.
3. `grep -n '^axiom' out/P.lean` — **any** axiom means the idiom drags an
   unmodelled `std` item into the trusted base. `hachi/lean/Generated.lean` has
   **zero** axioms; keep it that way.
4. **Does the output typecheck?** `cd hachi && lake env lean $S/out/P.lean`.
   Warnings are fine; errors mean the model is unusable.

Probing a **cross-crate** construct means giving the probe crate the `cpoly`
dependency *and* passing `--include 'cpoly::_'`, the way `make extract` does.
Without the flag the probe reports an axiom the real extraction would not
produce, and you will "discover" a ceiling that is not there.

## Idiom verdicts (measured, not guessed)

The tables below are AeneasCompPoly's, established there against
`nightly-2026.07.26-3a8586f` — **the aeneas nightly this repository also
pins**, which is why they carry over rather than needing a re-probe. The
this-repository rows are marked; `NOTES.md` §§ "Aeneas surprises", "What the
extraction of the four modules actually looks like" and "Derives extract, and
are still not worth it" are their record.

### Free — the Lean model is unchanged or only renamed

| Rust | Extracted Lean | Proof cost |
|---|---|---|
| `pub struct Fp(u64);` — even with a **private** field | `@[reducible] def Fp := Std.U64` | none, it is reducibly the inner type |
| `pub struct Rq(Vec<Fp>);` *(here)* | `@[reducible] def ring.Rq := alloc.vec.Vec cpoly.field.Fp` | none; `Check.lean` § 2b asserts all three container newtypes |
| two distinct newtypes over the same inner type | two reducible aliases — **note they are then the same Lean type** | none |
| `type Alias = Vec<Ext4>;` | vanishes entirely | none, and no Lean-side gain either |
| `impl Add for Ext4` | `def Ext4.Insts.CoreOpsArithAddExt4Ext4.add (self rhs : Ext4) : Result Ext4`, **body identical to the free function's** | rename |
| `impl Mul<Ext4> for Fp` (heterogeneous) | `Fp.Insts.CoreOpsArithMulExt4Ext4.mul` | rename |
| `impl Add<&T> for &T` | `Shared1T.Insts.CoreOpsArithAddShared0TT.add (self rhs : T)` — refs erased | rename (but see collisions below) |
| `impl T { const ZERO: T }` | `@[global_simps, irreducible] def T.ZERO` — same shape as a module-level `const` | rename, and `irreducible` means `simp [T.ZERO]` is the way in, not `rfl` |
| inherent `fn is_zero(self)` | `def T.is_zero (self : T) : Result Bool` | rename |
| `impl Index<usize> for T` | one extra def unfolding to `alloc.vec.Vec.index …` | one `@[step]` lemma |
| `&[T]` parameter | `Slice T`, indexed by `Slice.index_usize` (has `@[step]`) | domain change, mechanical |
| `&Vec<T>` → `&[T]` at a call site | `alloc.vec.Vec.deref` — a **pure** function, not monadic | free |
| `#[derive(Debug)]` | transparent `fmt` def via `Dyn.mk` / `debug_tuple_field1_finish`; **no axioms** *(re-measured here: opaque-function count 11 → 16)* | none, and declined anyway — see below |
| `u128` accumulator with `x as u128` *(here)* | `lift (UScalar.cast .U128 x)` then checked `*`, `+` | none, and load-bearing in `commit::l2_norm_sq` |

### Strict simplifications — a loop disappears, so a proof gets *shorter*

| Rust | Extracted Lean |
|---|---|
| `vec![x; n]` (repeat form) | `alloc.vec.from_elem`, `@[step]` spec |
| `v.resize(n, x)` | `alloc.vec.Vec.resize`, `@[step]` spec. Pads **and** truncates, so it does pad-or-drop in one call |
| `v.clone()` | `alloc.vec.CloneVec.clone`; with `Ext4::clone = id` it collapses via `Slice.clone_spec` |
| `1usize << n` | `1#usize <<< n`. Fails iff `n ≥ numBits`, i.e. **exactly** where a checked-doubling `pow2` loop fails — same precondition, no loop |

### Forbidden — breaks extraction or adds an axiom

* **Iterator adaptors** — `.map`, `.zip`, `.fold`, `.collect` have no model.
  Aeneas warns and emits unknown definitions. Plain `for x in slice` and
  `for i in 0..n` *are* modelled.
* **`Vec::is_empty`** → `axiom alloc.vec.Vec.is_empty`. Write `self.len() == 0`.
  (`<[T]>::is_empty` on a **slice** *is* modelled — the asymmetry is real.)
  This is why `len_zero` and `len_without_is_empty` are `allow`ed in
  `hachi/Cargo.toml`.
* **`#[derive(Default)]` on a `Vec`-holding struct** → needs `Vec::default`,
  → axiom. Write the impl by hand.
* **The list form of `vec!`** — `vec![a, b]` goes through a stack array and
  `Slice::into_vec`, dragging in `axiom core.mem.maybe_uninit.MaybeUninit`. The
  *repeat* form `vec![x; n]` is fine. Use `Vec::new()` + `push` for short literals
  and `#[allow(clippy::vec_init_then_push)]` with a comment saying why.
* **`Vec::truncate`, `pop`, `last`, `first`, `clear`, `extend`** — no model, and
  `clone` is not in this model either. `Rq::copy` is a `push` loop for that
  reason: a copy arriving as an opaque function is a copy about which nothing is
  known, in the middle of a proof that needs to know it is a copy.
* **`checked_shl`** → axiom. Its family does **not** share its fate:
  `checked_add` extracts to `U64.checked_add`, modelled and axiom-free —
  probe the specific intrinsic, per construct.
* **`unsafe`, SIMD intrinsics, inline asm** — the permanent ceiling.
  `src/lib.rs` carries `#![forbid(unsafe_code)]`.

### `const` arithmetic is fallible *(this repository, three times over)*

`pub const RING_DEGREE: usize = 1 << RING_LOG_DEGREE` extracts as
`def params.RING_DEGREE : Result Std.Usize`, so every Lean use would have to
bind it and discharge a side condition that is plainly true. Same for `GAMMA`
(`GADGET_BASE - 1`) and `BETA_SQ` (a product). Three occurrences make it a
rule: **in `params.rs`, values are literals and relations are checked** — in
`tests/params_semantics.rs` and again in `lean/Check.lean` § 1.

### Deliberately declined: `for i in 0..n`

It *works*. But it replaces a `usize` counter with a `Range<usize>` iterator in
the loop's **state**, and that state is what every loop invariant in
`lean/Ring.lean` is written about. The extracted bodies there are `(out, i)`
pairs precisely because of this. Keep the counter `while` loops and keep the
justification pointed at the theorem files — `src/lib.rs` § "Style notes" and
`needless_range_loop = "allow"` in `Cargo.toml` are the same decision.

### Deliberately declined: derives

`#[derive(Debug, PartialEq)]` on `Rq` was added, extracted, and reverted. It
extracts *cleanly* — zero axioms. Reverted for two reasons that are about the
model rather than the extraction: formatting plumbing is four items per type
that no proof will mention (and the crate has four such types), and a derived
`PartialEq` would be a **second notion of equality** beside `Rq::equals`, so
every spec would have to say which one it meant. `Rq::equals` is the operation
the specification's `decide (commit Φ A s = c)` corresponds to.

## The idiom/axiom boundary is the `[lints.clippy]` block

`hachi/Cargo.toml` is where this skill's judgement calls are already recorded,
and it is the artifact to cite when justifying a Rust choice. Six lints are
`allow`ed **because clippy's suggestion is worse for the extraction** — each
with its reason inline:

| Lint | clippy wants | why the code does otherwise |
|---|---|---|
| `ptr_arg` | `&[T]` | the Aeneas `Vec` model is what `Generated.lean` is written against; a slice arg adds a coercion at every call site for the proofs to carry (`Rq::from_coeffs`, `flatten_blocks`, `commit`) |
| `assign_op_pattern` | `acc += x` | `acc = acc + x` extracts as a call to the field's `Add` impl, the operation the specs are about; `+=` routes through `AddAssign`, a second extracted body saying the same thing |
| `cast_lossless` | `u128::from(x)` | `x as u128` extracts as `lift (UScalar.cast .U128 x)`, modelled directly; `From` is a trait call to step through |
| `needless_range_loop` | iterator adaptors | no Aeneas model at all |
| `len_without_is_empty` | add `is_empty` | it would always answer `false`, and `Vec::is_empty` has no model |
| `len_zero` | `Vec::is_empty` | same |

The rest of the block (`doc_markdown`, `if_not_else`,
`return_self_not_must_use`, `many_single_char_names`, …) is naming and
documentation opinion the crate does not share, also with reasons. Two rules
follow:

* **`pedantic` is `warn`, not `deny`, on purpose.** `make extract` builds this
  crate with charon's own rustc, and a lint that is only a style opinion must
  never be able to stop the extraction. The two that *do* matter —
  `unsafe_code` and `missing_docs` — are `forbid`/`deny` in `src/lib.rs`, where
  they travel with the source.
* **A new `allow` gets a one-line reason naming the extraction consequence**,
  at the narrowest scope: crate-wide policy in `Cargo.toml`, a local exception
  at the item. `src/lib.rs`'s `allow(missing_debug_implementations)` is the
  shape — the reason is a measurement, not a preference.

## Who reads what — how to justify a Rust choice

The reviewer reads `hachi/lean/{Field,Ring,Check}.lean`, and
`hachi/lean-wip/{RqBridge,Scheme}.lean` for the unaudited half. They do **not**
read `Generated.lean`. Never argue "the generated model would be uglier"; ask
what the *theorem statement and its invariant* look like. Two consequences:

* Idioms that only make `Generated.lean` noisier (extra trait impls that are
  pure delegation) are fine.
* Idioms that complicate a loop's state or a spec's domain are expensive even
  when the generated file looks tidy.

## Three failure modes that cost real time

### 1. `Shared<n><T>` name collisions — a hard extraction failure

Aeneas mangles `impl Trait for &T` into a prefix `Shared<n><T>` that is **not
module-qualified**. AeneasCompPoly hit this with `univariate::Poly` and
`multilinear::Poly` both producing
`Shared1Poly.Insts.CoreOpsArithAddShared0PolyPoly`, and extraction *failed*:

```
Error when registering the name for id: trait_impl_id: 56:
The chosen name is already in the names set: Shared1Poly.Insts.CoreOpsArithAddShared0PolyPoly
```

**This model currently has zero `Shared` names**, because every `hachi`
operation is an inherent method (`ring.Rq.add`, `linalg.PolyVec.dot`) rather
than a by-reference trait impl. The hazard is latent, and adding
`impl Add<&Rq> for &Rq` is what wakes it. If it wakes: **fix by making the
type names distinct, not by contorting the API.** Two things make that cheap:
`clippy::module_name_repetitions` does not fire in this toolchain, and a
*by-value* `impl Add for T` is module-qualified
(`m.T.Insts.CoreOpsArithAddTT.add`) and never collides.

### 2. A loop's state shape can change silently

Upstream's incident: `impl Add for &Coeffs` written as
`out.push(self.0[i] + rhs.0[i])` made Aeneas carry `rhs` in the loop state as a
**3-tuple** `(rhs, out, i)`, which breaks every `rintro ⟨r1, i1⟩` and `s.2.val`
in the invariant. Factoring the body into a helper over slices restored the
2-tuple **and** deduplicated the Rust.

Here that 3-tuple is the *status quo* for `ring.Rq.add_loop` and `sub_loop` —
`Ring.lean`'s header says so, and the invariant carries an `s.1 = rhs`
conjunct to pin the component that never moves. `mul_loop1_loop0` threads the
accumulator vector through its `ControlFlow` state, which is the only place in
the development where an accumulator moves by `Vec.set` rather than by `push`.
So the rule is not "keep 2-tuples" but **know the current census and diff it
after every re-extraction**:

```bash
grep -oE "^ +\(fun \([a-z0-9_, ]+\)" hachi/lean/Generated.lean \
  | sed 's/^ *//' | sort | uniq -c | sort -rn
```

### 3. Statement order in Rust is bind order in Lean

Collapsing named intermediates into one expression reorders the extracted binds
and invalidates the whole `step as ⟨…⟩` sequence that walks it. Naming them
costs nothing and reads better anyway — `ring.rs::mul` binds `term`, `s` and
`t` before the indexed assignment for exactly this reason.

Corollary: `out[k] = out[k] + prod` and `out[k] += prod` extract **differently**
(the second goes through `IndexMut` and a write-back closure). This crate has
already picked the first, and pinned the choice with
`assign_op_pattern = "allow"` in `Cargo.toml`. Do not "fix" it.

## Staged workflow

Never do the Rust rewrite and the proof repair as one step.

1. **Probe** every uncertain idiom (above).
2. **Write the new Rust.** Get `cargo clippy --all-targets` clean under
   `pedantic` and doc-tests passing *before* extracting. Note `--all-targets`
   includes `benches/`, and that `benches/genesis/` and `benches/candidate/`
   are separate packages. Doc examples are free — they are not extracted.
3. **`make extract`.** Then: `grep -c '^axiom'` must be 0; `Check.lean` § 2
   and § 2b must still hold; diff the loop-state shapes; skim the new names.
4. **Mechanical rename pass** on the Lean files. Build the map
   **longest-first** — `ring.Rq.mul` is a prefix of `ring.Rq.mul_loop0`, and
   replacing the short one first silently corrupts the long one. Assert every
   replacement landed; a silent no-op `str.replace` is the main way this goes
   wrong. **Never rename inside `benches/genesis/`** — see below.
5. **Fix the structural changes one at a time**, checking with
   `lake env lean lean/<File>.lean` — not a full `lake build`. `lean-wip/`
   files are not on the module search path; `hachi/lean-wip/README.md`
   § "Working here" has the `LEAN_PATH` recipe for a wip file importing
   another.
6. **`make build` && `make test`**, then re-run `make extract`: it must report
   `unchanged`, which is the determinism check. `make build` does **not** look
   at `lean-wip/`, so re-check those files by hand in the same pass.

## Lean-side repair kit

Things the repaired proofs need that are not obvious:

* **`bind_ok_id`.** Methods whose Rust tail is a local they just bound extract as
  `let x ← m; ok x`, which blocks `spec_mono` from seeing the last call as the
  whole body. `Field.lean` defines `@[simp] theorem bind_ok_id (m : Result α) :
  (do let x ← m; ok x) = m`; open such a proof with `simp only [bind_ok_id]`.
  It is most of them.
* **Aeneas marks every global `irreducible`.** `params.RING_DEGREE`,
  `cpoly.field.P`, `Fp::ZERO` do not unfold by `rfl` or `decide`;
  `simp only [params.RING_DEGREE]; decide` is the way in, and the house style
  is to prove one `@[simp, scalar_tac_simps]` value lemma per constant
  (`params_RING_DEGREE_val`, `cpoly_P_val`) so the generated arithmetic side
  conditions can use it.
* **`Slice α` and `Vec α` are the same subtype** (`{ l : List α // l.length ≤
  Usize.max }`), so a predicate written about `alloc.vec.Vec` applies to a `Slice`
  and `.val` works on both. `Vec.deref` is the identity.
* **The loop-invariant mechanics**, from the five coefficientwise proofs:
  the invariant arrives phrased in projections of the state tuple
  (`↑(o1, i1).1`), so `dsimp only at` the hypotheses before rewriting with
  them; `subst` on the `s.1 = rhs` conjunct eliminates **`rhs`**, so the rest
  of the body proof must name the loop-state variable instead — and that
  conjunct is then already discharged for the successor state, which changes
  the arity of the `refine`; and a triple over `ok (done x)` needs
  `WP.spec_ok` *and* a reduction of the `ControlFlow` match (`show` the
  postcondition, or `dsimp only`), or the rewrite fails with a
  type-correctness note that does not name the real problem.
* **Stale `.olean` trap.** `lake env lean lean/Ring.lean` uses whatever
  `Field.olean` exists. After editing `Field.lean`, run `lake build Field` first —
  otherwise you get a screen of bogus `unknown identifier` errors and waste time
  hunting a rename that was already correct.
* **`Usize.numBits` is opaque**, not definitionally `System.Platform.numBits`; the
  bridge is `Std.Usize.numBits_eq`, and `Usize.max_def` / `Usize.size_def` open the
  `irreducible_def`s. State shift side conditions in terms of
  `System.Platform.numBits`, not `64`, so they do not assume the platform.
* **`import Mathlib.Tactic.NormNum.Prime`** if the file needs
  `Fact (Nat.Prime q)`; ArkLib's imports do not reach norm_num's primality
  extension, and without it the instance fails with a bare
  `⊢ Nat.Prime 4294967197`, which reads like a hard problem.
* **`set_option autoImplicit false` in every file.** Not style: with it on, an
  unknown identifier in a *binder type* is auto-bound as an implicit, so a
  statement about a name that no longer exists keeps compiling as a statement
  about nothing. It has happened twice here — `Check.lean`'s `Ext4`
  assertions, and `Scheme.lean`'s missing `open HachiEquiv.Field`.

## The trap a mechanical rename sets

Two newtypes over the same inner type are **the same Lean type**, and no amount
of `lake build` will catch a spec that pairs the wrong two. The live instance
here is the bottom of the stack: `cpoly.field.Fp` *is* `Std.U64`, so an
arbitrary word and a reduced field element are indistinguishable to Lean.
`Red` is the only thing that separates them, and it travels as a hypothesis
because Aeneas cannot see Rust's privacy boundary (`Field.lean`'s header says
so). `Rq`, `PolyVec` and `PolyMatrix` are nested `Vec`s of *distinct* inner
types today, so they do not collide — a change that flattened two of them
would create exactly this trap.

After any rename touching the representation layer, check every pairing by
hand:

```bash
for t in $(grep -oE '^theorem [a-z_0-9]+_spec' hachi/lean/Ring.lean | awk '{print $2}'); do
  printf '%-22s ' "$t"
  sed -n "/^theorem $t /,/:= by/p" hachi/lean/Ring.lean \
    | grep -oE 'coeffK|negConv|rowsSum|Wf|Red' | sort -u | tr '\n' ' '
  echo
done
```

Every `_spec` must mention the invariant of each of its inputs, and `mul_spec`
is the only one whose right-hand side is `negConv`. `Check.lean` records which
separations are enforced by rustc and *not* by the proofs — that belongs in the
trusted-computing-base table, because it is a real limitation.

## Watch for capability regressions

Splitting one type into two removes every operation the callers used to get from
the shared type. AeneasCompPoly's split of `Poly` into
`MultilinearPoly`/`MultilinearEvals` silently removed *negation and scalar
multiplication* from the multilinear layer — they had been the univariate
operations applied to a shared `Vec<Ext4>` — and left two specs proving things
about operations no caller could invoke any more. After a type split, enumerate
what the old shared type could do and check each capability survived.

## What a change to `src/` owes the benchmarks

`hachi/benches/` measures every operation here against `benches/genesis/`, a
frozen copy of its *first* translation. Three obligations follow, and
`make bench-check` enforces all three — run it before you call a refactor done.

**Never apply a rename inside `benches/genesis/`.** This is the trap, because the
mechanical rename pass above trains exactly the wrong reflex. Genesis is
append-only and byte-exact: every item is verified against the git blob of the
commit its `// @genesis` annotation names, so "fixing" it to match a rename
breaks the check *and*, if the check were somehow satisfied, would silently
rewrite what every past measurement was compared against. Genesis records what
the code used to be. That is the whole point of it.

**A renamed or split item needs a new frozen entry.** `bench-check` lists items
in `src/` with no counterpart in genesis, and a rename produces exactly that: the
new path is unfrozen while the old one sits in genesis forever. Copy the item's
current text in, `make bench-stamp`, and leave the old entry alone. (Note the
stamp stores its own commit sha, so the content commit and the stamps commit are
two commits — never `--amend` the first.)

**A renamed item also orphans its coverage markers.** `// @covers <path>` lines in
`benches/*.rs` and keys in `benches/exclusions.toml` are full item paths, so a
rename dangles them. `bench-check` fails on a `@covers` path that names no item,
which is how you find them; grep the old name in `benches/` and fix both places.

The reverse direction matters too: **adding a public operation** means freezing it
and, if its docstring carries a ``Mirrors `<ArkLib name>` `` line, benching it or
excluding it by name with a reason. `.claude/skills/rust-bench` is the procedure.

## Invariants to keep green

* **Zero axioms** in `Generated.lean`, and `--include 'cpoly::_'` never
  dropped (`Check.lean` § 2 is the guard; see `aeneas-extract`).
* **Zero `sorry` under `hachi/lean/`** — `make build` greps for it and fails, so
  a `sorry` is not a usable placeholder there. Unproved statements live in
  `hachi/lean-wip/`, which is not a Lake root; promotion is the five-step
  procedure in `hachi/lean-wip/README.md`, and it includes adding the module to
  `roots` in `hachi/lakefile.lean` and a `#print axioms` line to `Check.lean`
  § 4.
* **Every public operation has a spec**, at both levels — the coefficient level
  and the `Rq Φ` lift. This holds today for `ring` (thirteen operations, proved
  and audited; the lift proved but unchecked) and for nothing above it:
  `linalg`, `gadget` and `commit` are *stated only*, in `lean-wip/Scheme.lean`.
  Adding API adds obligations to both files.
* **`cargo clippy --all-targets` clean** under `pedantic`. Where a lint is wrong
  for this crate, `allow` it **with a one-line reason** naming the extraction
  consequence, at the narrowest scope.
* **`make bench-check` passes.** Touching `src/` has benchmark obligations; see
  the section above.
* **Never weaken a spec to make it pass.** If a statement cannot be proved,
  the interesting possibilities are that the Rust is wrong, the reference is a
  different ArkLib operation, or a hypothesis is genuinely needed — say which,
  do not quietly add a hypothesis or drop a conjunct. `commit::l2_norm_sq`'s
  `u128` accumulator is the exemplar of the first case: with `u64` the totality
  half of its spec would be false on exactly the inputs the verifier must
  reject, and no proof effort would have fixed that.
