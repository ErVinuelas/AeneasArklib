# NOTES

Decisions, spec-mismatch observations, and Aeneas surprises. Append; do not
rewrite history. Each entry says what was decided, what the evidence was, and
what would have to change to revisit it.

Written during Workstream 0 (the scaffold), so several entries are about the
build rather than about Hachi.

---

## Upstream aeneas, no fork

**Decision.** `hachi/lakefile.lean` requires `AeneasVerif/aeneas` at
`nightly-2026.07.26-3a8586f` — upstream, not a fork.

AeneasCompPoly, the repository this one is modelled on, requires a *fork* of
aeneas (`tobias-rothmann/aeneas @ lean-4.32.0`), and its README explains why:
CompPoly had moved to Lean v4.32.0, upstream aeneas's Lean backend hard-requires
Mathlib v4.31.0, and no upstream nightly had caught up. Copying that arrangement
here would have been the default, and it would have been wrong.

The specification this repository is proved against is **ArkLib**, and ArkLib is
on v4.31.0:

| | Lean / Mathlib |
|---|---|
| ArkLib `lean-toolchain`, `lake-manifest.json` | v4.31.0 |
| upstream aeneas `backends/lean/lakefile.lean` @ `nightly-2026.07.26-3a8586f` | v4.31.0 |

So the two agree already and the fork buys nothing. `AENEAS_TAG` in the `Makefile`
and the `require` in `hachi/lakefile.lean` are the same upstream commit, which is
the invariant `make setup` and `make extract` both check: `Generated.lean` is only
valid against the Aeneas version that produced it.

**To revisit:** if ArkLib bumps to v4.32.0, this flips to AeneasCompPoly's
situation and the fork (or a later upstream nightly) comes back. Move
`lean-toolchain`, the `aeneas` rev and `AENEAS_TAG` together.

---

## The cpoly dependency

**Decision.** The field layer stays a **cargo dependency** on AeneasCompPoly's
`cpoly` crate, pinned by `rev`. `field.rs` is *not* vendored. `make extract`
passes `--include 'cpoly::_'` to charon, and that flag is load-bearing.

The brief anticipated vendoring as the likely outcome ("if charon chokes on
cross-crate extraction, vendor the needed `field.rs` code"). Charon does not
choke, but it does need telling. Three extractions, in the order they were run:

**1. Plain `charon cargo --preset=aeneas -- --lib`.** Succeeds, and produces a
model that is worse than useless. Charon's default whitelist is the local crate,
so every `cpoly` item arrives as an axiom:

```lean
axiom cpoly.field.Fp : Type
axiom cpoly.field.Fp.ZERO : Result cpoly.field.Fp
axiom cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add
  : cpoly.field.Fp → cpoly.field.Fp → Result cpoly.field.Fp
```

An uninterpreted type with an uninterpreted addition. A Lean proof about a
function that sums such a thing proves nothing, and the three `axiom`s would
appear under every `#print axioms` in `lean/Check.lean` forever. Charon warns
about it — `The crate contains extracted external, unknown definitions` — but it
is a warning, and the build is green.

**2. `--extract-opaque-bodies` (the obvious first guess).** The flag's
description fits the symptom exactly: *"Usually we skip the bodies of foreign
methods and structs with private fields. When this flag is on, we don't."* `Fp` is
a struct with a private field. It is nonetheless the wrong tool, because it is
**global**: it also un-opaques `alloc::vec::Vec`, `alloc::raw_vec::RawVec` and the
rest of std, whose bodies Aeneas models by name rather than by translation. Aeneas
then fails outright:

```
Error: Detected groups of mixed mutually recursive definitions ...
Error: Mixed declaration groups ... are not supported yet: [7, 20, 17, 19, 18]
Error: Internal error: please file an issue
Warn : Could not translate type decl 'alloc::vec::Vec because of previous error
```

No Lean file is produced at all.

**3. `--include 'cpoly::_'`, with no `--extract-opaque-bodies`.** Correct. The
whitelist is *scoped*, so `cpoly` becomes transparent while std stays modelled.
Zero axioms, zero opaque definitions, and the bodies are real:

```lean
def cpoly.field.P : Std.U64 := 4294967197#u64
@[reducible] def cpoly.field.Fp := Std.U64
def cpoly.field.Fp.ZERO : cpoly.field.Fp := 0#u64
def cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add
  (self : cpoly.field.Fp) (rhs : cpoly.field.Fp) : Result cpoly.field.Fp := do
  let i ← self + rhs
  let i1 ← i % cpoly.field.P
  ok i1
```

`Ext4` — the case a one-field newtype does not cover, being a foreign struct with
four private fields — comes through as a real `structure` with real projections,
and its sixteen-term `mul` as a real definition. `lean/Check.lean` § 2 asserts all
of this, so dropping the flag breaks the build rather than quietly re-axiomatizing
the field.

> **Amended in Workstream 1 — see § "The model contains what the crate reaches".**
> The `Ext4` half of this is no longer true, and for an instructive reason: the
> whitelist says which foreign items charon *may* translate, not which it does, and
> the only thing that ever reached `Ext4` was the extraction probe. With the probe
> deleted, `Ext4` is absent from the model and § 2 asserts about the four `Fp`
> operator impls instead. The `Fp` half above, and the conclusion that the flag is
> load-bearing, stand unchanged.

**Why `rev` rather than a branch.** Not for build reproducibility — `Cargo.lock`
gives that — but for the frozen bench baseline. `benches/genesis/` is append-only
and must never change behaviour or speed once frozen; a field layer that could
move under it would break that guarantee silently. Bumping the rev is a
deliberate act with a re-baseline attached.

**To revisit:** if a later `cpoly` bump makes charon's whitelist insufficient (a
generic item, a `dyn Trait`, an inline-assembly intrinsic), vendoring is still the
fallback and this entry is the reason it was not needed first.

---

## What the cpoly dependency does *not* buy: its Lean proofs

**Observation, and a cost to plan for.** The Rust reuse works (above). The *Lean*
reuse does not, and cannot today.

`cpoly/lean/Field.lean` proves its field operations equivalent to CompPoly's
`Hachi.ext4Params` / `CompPoly.Extension.Ext`. Those definitions live in
`CompPoly/Fields/Hachi.lean` and `CompPoly/Fields/Extension/`, which exist **only
after CompPoly's Lean v4.32.0 bump**. Checked at both pins:

| CompPoly revision | reached from | `Fields/Hachi.lean`, `Fields/Extension/` |
|---|---|---|
| `e95ba1b1` (v4.31.0) | ArkLib | absent |
| `c0fcf450` (v4.32.0) | AeneasCompPoly | present |

So the field theory cpoly proves against needs v4.32.0, while the Hachi
specification this repository targets needs v4.31.0, and one Lake package cannot
have both.

This is survivable because **ArkLib's Hachi specs do not depend on those files**.
The Hachi and `CyclotomicRing` trees import only `CompPoly.Multilinear.Basic`,
`CompPoly.Multivariate.Operations`, `CompPoly.Univariate.Linear` and
`CompPoly.Univariate.ToPoly.Impl` — all present at v4.31.0 — and reference
`Hachi.ext4Params`, `CompPoly.Hachi` and `Extension.Ext` nowhere at all. The
target specs are self-contained at v4.31.0.

The consequence is a real item of work rather than a blocker: the bridge from the
extracted `cpoly.field.Fp` (which *is* `Std.U64`) to the coefficient ring the
ArkLib specs use — the `Red` invariant and a `toK`-style map into `ZMod q` — has
to be re-derived in this repository. It is not large, but it is not free, and it
is not the same as importing cpoly's `Field.lean`.

**To revisit:** an ArkLib bump to v4.32.0 collapses this entry and the fork entry
into each other, and the field proofs become importable.

---

## Chosen parameters

**Observation.** The ArkLib specification is generic in **all four** of
`(q, α, b, digits)`, and pins none of them anywhere. Searched: no concrete
modulus, no concrete `α`, no concrete gadget base or digit count appears in
`Commitments/Functional/Hachi/` or `Data/Lattices/`, and neither does the Hachi
prime `4294967197` in any form. Every parameter relation travels as a hypothesis
(`Fact (Nat.Prime q)`, `1 < b`, `q ≤ b ^ digits`).

Hard rule 3 of this project is the opposite — concrete, not generic, all
parameters as `const`s in one `params.rs` — so the values are this repository's
choice and each equivalence proof will instantiate a generic statement at them.
`hachi/src/params.rs` records the provenance of each; the split is:

| | value | why |
|---|---|---|
| `Q` | `2^32 - 99` | **Pinned** by `cpoly`'s `Fp`, whose proofs this builds on. Prime; `< 2^32` (the no-overflow argument); `≡ 1 mod 4` (so `Y^4 - 2` is irreducible) |
| `EXT_DEGREE`, `EXT_W` | `4`, `2` | **Pinned** by `cpoly`'s `Ext4` |
| `GADGET_BASE` | `2` | **Chosen**, constrained to `1 < b`. Binary gives the shortest digits |
| `GADGET_DIGITS` | `32` | **Chosen**, and forced given `b = 2`: `zmodDigitDecomposition` needs `q ≤ b^digits`, and `2^32 = 4294967296 ≥ 4294967197 = q` with 99 to spare — so 32 is enough and 31 is not |
| `RING_LOG_DEGREE` (`α`) | `6` | **Chosen**, unconstrained by the spec. Degree-64 ring, per the Greyhound/Hachi line of work |

`α = 6` is the one value here with no spec-side or dependency-side justification —
it is a performance and security parameter both, and it is the most likely of the
five to be revised once the concrete parameter set of [NOZ26] is fixed. It is
checked in two places (`tests/params_semantics.rs`, `lean/Check.lean` § 1 and § 3)
but nothing *derives* it.

**Open question for whoever has the paper to hand:** the brief's later
workstreams, which would name the concrete specs and presumably the parameter
set, were not included in the brief as received. `α`, and the commitment matrix
dimensions that are not in `params.rs` at all yet, need that input.

---

## Aeneas surprises

**A `<<` in a `const` extracts as a `Result`.** `pub const RING_DEGREE: usize = 1
<< RING_LOG_DEGREE` is the natural way to write the ring degree and keep it tied
to `α`. Aeneas models a shift as fallible, so it extracts as

```lean
def params.RING_DEGREE : Result Std.Usize := 1#usize <<< params.RING_LOG_DEGREE
```

and every Lean use of the constant would then have to bind it and discharge a
side condition that is plainly true. `params.rs` writes the literal `64` instead,
which extracts as `def params.RING_DEGREE : Std.Usize := 64#usize`, and the
relation to `RING_LOG_DEGREE` is checked rather than structural — in
`tests/params_semantics.rs` and again in `lean/Check.lean` § 1.

This is the same shape as AeneasCompPoly's `table_len` (`1usize << vars`), which
carries a `pow2_spec` side condition for exactly this reason. The difference is
that `table_len` is a runtime function where the condition is real, and
`RING_DEGREE` is a compile-time constant where it is noise.

---

## Deferred from Workstream 0, deliberately

Neither is a blocker; both are recorded so they are not mistaken for oversights.

**The bench harness's checkers.** AeneasCompPoly's `benches/harness.py` (~1100
lines) implements `check-genesis`, `check-candidate`, `coverage`, `stamp-genesis`
and the recentred `cand vs now` report, and the `Makefile` exposes them as
`bench-check` / `bench-stamp` / `ledger-check`. Every one of those operates on
`@genesis`-annotated functions and `bench_case!` invocations, and this repository
has neither yet: `benches/genesis/` and `benches/candidate/` are empty on purpose.

What *is* in place is the part that cannot be added retroactively: both baseline
crates exist as siblings with the same compilation path, the `candidate` feature
is wired, and `profile.bench` carries AeneasCompPoly's measured `lto = "fat"` /
`codegen-units = 1` settings. `make run-bench` runs criterion on the pinned
toolchain. The checkers land with the first real module, which is the first thing
they would have anything to say about.

The one irreversible rule is already being obeyed: **nothing is frozen into
`benches/genesis/` yet**, because the only function in the crate is a throwaway
extraction probe, and freezing a throwaway into an append-only baseline is the
single mistake in this harness that cannot be undone.

**`.claude/skills/` and `INSTRUCTIONS.md`.** AeneasCompPoly carries 39 skill files
and a catalogue describing them. They are not in Workstream 0's deliverable list,
and porting them verbatim would import ~40 documents that all reference CompPoly,
`cpoly`, and an optimization loop this repository does not yet have a corpus for —
stale on arrival. They should be ported when there is work for them to drive, and
adapted rather than copied.

---

## `hachi/src/smoke.rs` is temporary

It implements no part of the scheme. It exists so that the cross-crate extraction
question above could be answered with a measurement instead of a guess, and it is
written to touch exactly what the boundary has to carry: a foreign newtype, a
foreign associated constant, a foreign operator impl, a foreign multi-field
struct, and a `Vec` walked by an index-counter loop.

Delete it — with its bench case and its `Cargo.toml` bench target — when the first
real module lands. It must never be frozen into `benches/genesis/`.

---

# Workstream 1: the four bottom-layer modules

Entries below were written while translating `ring`, `linalg`, `gadget` and
`commit`. The first one is about this session's environment rather than about
Hachi, and it is first because it bounds what every other claim here rests on.

---

## What this environment could and could not check

> **Partly superseded, later the same session — see § "The Lean side does build
> here, it just takes hours".** The diagnosis below is accurate and the egress
> block is real, but the conclusion ("the Lean half is not checked *at all*") was
> overtaken by the source build finishing: `make build` now passes. The scoring
> table in that later entry is the current one. This entry is kept because the
> evidence in it — which hosts fail, and how — is what the next person needs.

**Observation, and a limit on the evidence for this commit.** The Rust half of
this workstream is fully checked. The Lean half is not checked *at all*, and the
reason is an egress policy rather than a property of the code.

What ran, and what it showed:

| step | status | evidence |
|---|---|---|
| `cargo build --lib` | ✔ | clean, no warnings |
| `cargo test` (66 tests) | ✔ | all pass, including perfect correctness and every rejection path |
| `make extract` | ✔ | `lean/Generated.lean` regenerated, 160 definitions, **zero `axiom`s**, zero `opaque` bodies |
| `cargo bench` (all four targets) | ✔ | compile and run; see the caveat below on the numbers |
| `make build` (the Lean proofs) | ✘ | **could not be run** |

`make build` needs Lean, Mathlib and ArkLib. Lean itself was installable: the
`elan` installer host (`elan.lean-lang.org`) is blocked, but the release tarballs
on `github.com` are not, so `elan` v4.2.3 and the `leanprover/lean4` v4.31.0
toolchain were fetched from GitHub and unpacked into
`~/.elan/toolchains/leanprover--lean4---v4.31.0`, which `elan` then resolves
without contacting its own host.

The *oleans* were the wall. `lake exe cache get` failed on every single object:

```
… .ltar.part: Transfer failed (error code: 0): CONNECT tunnel failed, response 403
Decompressed 0 file(s)
8542 download(s) failed
```

`cache.lean-lang.org`, `lakecache.blob.core.windows.net` and every other
`lean-lang.org` host answer 403 through this session's proxy; only GitHub is
reachable. So Mathlib and ArkLib have to be compiled from source — on 4 cores,
which is hours — and a `lake build` started in the background got roughly halfway
through Mathlib before this commit was written.

**What that means for the audit.** `make build`'s guarantee is that the proofs
check and contain no `sorry`. Nothing in this commit relies on that guarantee,
because nothing in this commit adds a proof to the audited library:

* `lean/Check.lean` grew new claims (§ 1 for the new parameters, § 2b for the four
  extracted modules), and they are all `simp`/`rfl`/type-ascription claims — but
  they are **unverified in this session** and will be checked the first time
  `make build` runs anywhere with a Mathlib cache.
* the equivalence development is in `hachi/lean-wip/`, which is deliberately not a
  source root of the Lake library, so it cannot make `make build` pass or fail. It
  contains `sorry`s, legitimately, per hard rule 5 and the brief's "an equivalence
  proof that isn't finished stays in a scratch file outside the audit".

**Definition of done, honestly scored, per module.** (a) unit tests pass: ✔ for
all four. (b) `make extract` succeeds and the module appears in `Generated.lean`:
✔ for all four. (c) equivalence lemmas compile under the `Check.lean` audit: ✘ for
all four — the lemmas are *stated*, not proved, and not compiled. (d) a criterion
bench exists: ✔ for all four.

**To revisit:** on any machine that can reach `cache.lean-lang.org`, `make setup &&
make build` is the whole of the missing step for the `Check.lean` half. The
equivalence proofs are real work regardless of the network (see
`lean-wip/README.md`).

---

## The digits are not balanced

**Spec-mismatch observation — the brief is wrong here, and the specification is
what it is.** The brief for this workstream says of `zmodDigitDecomposition`:
"note it is a CENTERED/balanced digit decomposition", and asks for a test that
"every digit's centered absolute value ≤ B/2". Neither is true of the pinned
specification, and the code follows the specification (hard rule 1).

`Gadget/Core.lean:113` reads:

```lean
def zmodDigitDecomposition (b digits : ℕ) (hb : 1 < b) (hq : q ≤ b ^ digits) :
    DigitDecomposition (R := ZMod q) (b : ZMod q) digits where
  digit c e := ((Nat.digits b c.val).getD (e : ℕ) 0 : ZMod q)
```

`Nat.digits b c.val` is the ordinary base-`b` expansion of the *canonical*
representative `c.val ∈ [0, q)`. Every digit is in `{0, …, b-1}`: non-negative,
never balanced.

What *is* centered is the norm. `Rq.lInftyNorm` measures each coefficient through
`ZMod.valMinAbs`, and `Gadget/Norms.lean:68`'s `zmodDigit_natAbs_le` then bounds
each digit's centered absolute value by **`b - 1`**, not `b/2` —

```lean
theorem zmodDigit_natAbs_le {b digits : ℕ} (hb : 1 < b) (hq : q ≤ b ^ digits)
    (hbq : b - 1 ≤ q / 2) (c : ZMod q) (e : Fin digits) :
    ((zmodDigitDecomposition b digits hb hq).digit c e).valMinAbs.natAbs ≤ b - 1
```

— and it needs the extra side condition `b - 1 ≤ q/2`, whose whole job is to stop
a small non-negative digit from wrapping *to* a negative centered representative.
On a balanced decomposition that hypothesis would be unnecessary; its presence is
the tell.

At `b = 2` the two bounds coincide numerically (`b - 1 = 1`, `b/2 = 1`), so the
distinction costs nothing today and would cost correctness at any larger base.
`tests/gadget_semantics.rs::digits_are_the_plain_base_b_digits_of_the_representative`
pins the digits to the non-negative form against an independent computation, and
`params.rs`'s `GAMMA` is `b - 1` with the side condition checked in
`params_semantics.rs` and `lean/Check.lean` § 1.

---

## One digit count, not two

**Decision.** `GADGET_DIGITS` serves as both of the specification's digit counts.

`InnerOuter/Scheme.lean` carries `messageDigits` and `innerDigits` separately, and
`Decomposition.ofDigits` takes a `DigitDecomposition` for each, so the
specification genuinely admits different values. They cannot differ here: both
decompositions are of `Rq` elements over the same `ZMod q`, so both need
`q ≤ b ^ digits` for their reconstruction law, and at `b = 2` that forces 32 on
each. A second constant would be a second name for 32.

The consequence for the equivalence proofs is recorded in `commit.rs`:
`Decomposition.ofDigits` has no computational content left to translate once its
two slots hold the same function, which is why `generate_decomps` calls one
`gadget_decompose` twice rather than carrying a decomposition record.

**To revisit:** a parameter set with `b > 2` could make the two digit counts differ
(a wider gadget for the inner step trades digits for norm), at which point this
becomes two constants and `generate_decomps` takes them as arguments.

---

## Derives extract, and are still not worth it

**Measured, then decided against.** `#[derive(Debug, PartialEq)]` on `Rq` was
added, extracted, and reverted.

It extracts *cleanly* — this was the surprise. No axioms appear; charon translates
the derived impls and Aeneas has real models for what they reach:

```lean
def cpoly.field.Fp.Insts.CoreFmtDebug.fmt
  (self : cpoly.field.Fp) (f : core.fmt.Formatter) :
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)
  := do
  let dyn := Dyn.mk _ (core.fmt.DebugShared core.fmt.DebugU64) self
  core.fmt.Formatter.debug_tuple_field1_finish f (toStr "Fp") dyn
```

and `core.fmt.Formatter.debug_tuple_field1_finish`, `core.fmt.DebugShared` and
`Dyn.mk` are all in `Aeneas/Std/Core/Fmt.lean`. The opaque-function count went
from 11 to 16 and the build stayed axiom-free.

Reverted anyway, for two reasons that are about the model rather than the
extraction:

1. **Model hygiene.** `Generated.lean` is the object the equivalence proofs are
   about. Formatting plumbing in it is four items per type that no proof will ever
   mention, and the crate has four such types.
2. **One equality, not two.** `Rq::equals` is the operation the specification's
   `decide (commit Φ A s = c)` corresponds to. A derived `PartialEq` alongside it
   would be a second notion of equality on the same type, and every spec would
   then have to say which one it meant.

`#![allow(missing_debug_implementations)]` in `src/lib.rs` is that decision, with
the reasoning inline. The test helpers print through the public API instead
(`tests/support/mod.rs`), which costs nothing and keeps assertion messages useful.

---

## What the extraction of the four modules actually looks like

**Findings, in the order they mattered while writing the Rust.**

**Single-field newtypes are free, and that is worth designing around.** `Rq`,
`PolyVec` and `PolyMatrix` are `pub struct T(Vec<…>)`, and each arrives as a
`@[reducible] def`:

```lean
def ring.Rq := alloc.vec.Vec cpoly.field.Fp
def linalg.PolyVec := alloc.vec.Vec ring.Rq
def linalg.PolyMatrix := alloc.vec.Vec linalg.PolyVec
```

So a statement about an `Rq` *is* a statement about a `Vec` of field words — no
wrapper to transport across, no projection to unfold. The newtypes are therefore
pure gain: they give the Rust its type discipline and the Lean side nothing to pay
for it. `lean/Check.lean` § 2b asserts all three, so a change that turned one into
a real `structure` would fail the audit rather than quietly complicate every
proof.

**`u128` works, including the cast.** `commit::l2_norm_sq` accumulates in `u128`
because it has to (one centered coefficient reaches `q/2 ≈ 2^31`, so 64 squares
overflow `u64`). It extracts as ordinary checked arithmetic with an explicit cast:

```lean
let x ← lift (UScalar.cast .U128 i)
let i1 ← x * x
let acc1 ← acc + i1
```

This is the difference between a spec that holds only for short inputs and one
that holds everywhere. A `u64` accumulator would make the extracted verifier
*fail* on exactly the long inputs it is supposed to reject, and no amount of
proving would fix that — the totality half of the spec would simply be false.

**Nested loops are named positionally, and the naming is the proof plan.**
`Rq::mul`'s two loops become `ring.Rq.mul_loop0` (the zero-fill) and
`ring.Rq.mul_loop1` / `ring.Rq.mul_loop1_loop0` (the convolution's outer and inner
passes). The inner body threads the accumulator vector through its `ControlFlow`
state:

```lean
Result (ControlFlow (ring.Rq × (alloc.vec.Vec cpoly.field.Fp) × Std.Usize)
  (ring.Rq × (alloc.vec.Vec cpoly.field.Fp)))
```

which says exactly what the invariant has to be about: a partial convolution held
in a `Vec` that is being written through `index_mut`. That is the shape
`Ring.mul_loop1_loop0_spec` proves, and the only place in the development where the
accumulator moves by `Vec.set` rather than by `push`.

**The `Vec` model covers what these modules use, and nothing more.**
`alloc.vec.Vec.new`, `.push`, `.len`, `.index` and `.index_mut` all appear in
`Generated.lean` as modelled operations. `clone`, `truncate` and `is_empty` do
not, which is why `Rq::copy` is a `push` loop (see its docstring) — a copy that
arrived as an opaque function would be a copy about which nothing is known, in the
middle of a proof that needs to know the copy is a copy.

**`const` arithmetic is fallible, again.** Workstream 0 hit this with
`RING_DEGREE = 1 << RING_LOG_DEGREE`. It applies to `GAMMA` (`GADGET_BASE - 1`)
and `BETA_SQ` (a product) too, so both are literals with the derivation checked in
`tests/params_semantics.rs` and `lean/Check.lean` § 1 rather than expressed in the
`const`. Three occurrences make it a rule: **in `params.rs`, values are literals
and relations are checked.**

**Counter loops, not `for`.** The brief asks for "plain `for`-loops over index
ranges"; every loop here is a `while` with an explicit `usize` counter, which is
`src/lib.rs`'s established convention and the reason it gives is the right one: a
`for` loop is modelled, but it turns the loop state from a `usize` into a
`Range<usize>` iterator, and the loop state is what every invariant is written
about. The extracted bodies above are `(acc, i)` pairs precisely because of this.

---

## The genesis slot takes the `cpoly` dependency

**Decision, resolving the open question `benches/genesis/src/lib.rs` recorded.**
Both bench slots now depend on `cpoly`, pinned to the same `rev` as
`hachi/Cargo.toml`.

The slot crates' rule was "no dependencies, ever", and the frozen modules cannot
compile without the field. What the rule protects against is *drift* — a baseline
whose speed changes without anyone freezing anything — and a `rev` pin cannot
drift: moving it is an edit to `hachi/Cargo.toml`, which this file already
designates a deliberate act with a re-baseline attached.

The alternatives were worse. Vendoring `field.rs` into `hachi/src/` would undo
Workstream 0's finding that the field can be a dependency rather than a copy.
Freezing a *second* copy of the field into `benches/genesis/` would put two
implementations of `Fp` in one bench binary, free to diverge silently, which is
the failure the "no dependencies" rule exists to prevent in the first place.

Editing `benches/genesis/src/lib.rs` to say so did not violate contract point 1
("nothing here is ever edited"): nothing had been frozen yet, so there was no
measurement whose history the edit could rewrite. From this commit on, the file is
append-only.

---

## Benchmark numbers from this session are not measurement-grade

> **Superseded — see § "The first benchmark run, and what it says about the
> harness".** A full run on an idle machine followed, and it found something larger
> than the competing build: two byte-identical crates read up to 59% apart, so the
> A/B comparison itself needs work before it can accept or reject a candidate.

**Caveat, so nobody quotes them.** The bench targets compile and run — that is
what was verified. The numbers they produced here were taken while a
4-core-saturating Lean build was running in the same container, which is exactly
the condition `Makefile` § `run-bench` says to wait out. For the record, and as an
order of magnitude only: `ring/mul` (the 64×64 schoolbook negacyclic convolution)
read ≈ 8.3 µs, `ring/scalar_mul` ≈ 210 ns, `ring/equals` ≈ 21 ns.

The `_control` case in each group exists for this reason: it times an operation
that is byte-identical in all three crates, so any spread it reports is the
harness's own bias and is the noise floor for reading the rest of the group. A
first real baseline should be taken on an idle machine.

---

## The dimensions and the norm bounds

**Decisions, with the same pinned/chosen split as Workstream 0's parameters.**

| | value | why |
|---|---|---|
| `MESSAGE_ROWS`, `INNER_ROWS`, `OUTER_ROWS`, `BLOCKS` | 4, 2, 2, 2 | **Chosen.** The specification's `PublicParams` is generic in all six shapes. These are the smallest values that still exercise every index computation — more than one row, more than one block, a gadget expansion worth flattening |
| `GAMMA` | 1 | **Derived** from `gadgetDecompose_zmod_vecLInftyNorm_le`: the honest decomposition's `ℓ∞` norm is `b - 1` |
| `BETA_SQ` | 8192 | **Derived** from `gadgetDecompose_zmod_vecL2NormSq_le`: `(messageRows·digits)·(deg φ)·(b-1)²` |
| `KAPPA` | 65535 | **Chosen at its ceiling**, forced by `isUnit_of_l1Norm_le`'s `κ² < q` (with `q % 8 = 5`, which holds). `κ` is a rejection threshold, so the ceiling is the most permissive legal value |

The two derived bounds are *tight*: an honest opening sits exactly on both, which
is what makes the correctness tests meaningful — a slacker bound would accept
honest openings for the wrong reason. That tightness is also a hazard to know
about: any change to `MESSAGE_ROWS`, `GADGET_DIGITS` or `RING_DEGREE` changes
`BETA_SQ`, and `params_semantics::beta_sq_is_the_honest_l2_bound` is what turns
that into a failing test rather than a verifier that silently rejects honest work.

**Open question, unchanged from Workstream 0 and now more pressing:** the concrete
parameter set of [NOZ26] (the ℓ=30 table) was not available in this session. `α`,
the four dimensions and `κ` all want it. Everything downstream reads only
`params.rs`, so each is a one-line diff — but `BETA_SQ` and `GAMMA` must be
re-derived from the formulas above when the dimensions move, not carried over.

---

## Where the equivalence work stands

**Status.** `hachi/lean-wip/` holds the representation bridge and the statement of
every equivalence obligation the four modules owe:

* `Ring.lean` (renamed `RqBridge.lean` when its proofs landed; the name below is the
  one it had when this entry was written) — the parameters as Lean numbers with
  their instances, the base-field
  bridge (`toK`, `Red`, and the four `Fp` operator specs re-derived because
  `cpoly`'s `Field.lean` is not importable at v4.31.0 — see the Workstream 0 entry
  on that), the ring bridge (`Wf`, `coeffFun`, `toRq`, `toRq_coeff`,
  `toRq_eq_iff`), and one theorem per operation of `src/ring.rs`.
* `Scheme.lean` — the same for `linalg`, `gadget` and `commit`, including the
  structure bridges (`toParams`, `toDecompSpec`, `toOpening`) that let
  `verify_weak_spec` be stated against the specification's own `verify_weak`
  rather than against a paraphrase of it.

Two statements are worth reading even before they are proved, because writing them
down is what settled a question in the Rust:

* `gadget_mul_spec` says the structured per-block digit sum equals `gadgetMul`,
  which is a *matrix* product. They agree by the specification's own
  `gadgetMul_apply`, so that lemma is a load-bearing step of the proof and not an
  optimization footnote. This is what licenses `gadget_mul` wherever the
  specification writes `Simple.commit Φ (gadgetMatrix …)`, which both
  `derived_message` and `verify_weak` do.
* `verify_weak_spec` is an *equality of decisions*. A one-way implication would be
  satisfied by a verifier that rejects everything — the one failure mode no
  correctness test can see.

The hard obligation was `mul_spec`: a schoolbook convolution with the `X^N = -1`
sign folded into the inner loop, against `reduce (a.val * b.val)` via `modByMonic`.
It is proved — the coefficient half in `lean/Ring.lean` and audited, the `modByMonic`
half here. Nothing else in this file is checked; see the first entry of this section,
and `lean-wip/README.md` for the promotion procedure.

---

## `make setup` learned to install Lean without `lean-lang.org`

**Decision, and the one piece of the egress problem that *is* fixable.**
`scripts/install-lean.sh` now does the elan/toolchain half of `make setup`, and it
falls back to GitHub release assets when the usual hosts are refused.

The normal path is right and stays first: `elan.lean-lang.org/elan-init.sh`, then
`elan toolchain install`, which fetches from `release.lean-lang.org`. Both hosts
are separate from GitHub, and this session's egress policy allows GitHub and
nothing else — so the normal path died on `curl: (22) … error: 403` before Lean was
even installed. The fallback needs no host `make setup` does not already require
for the charon/aeneas binaries, which is what makes it a fallback rather than a
second dependency: if the aeneas half of setup can run, so can this.

Two details worth keeping:

* **How elan is persuaded.** No flag redirects its downloads, but it *looks before
  it fetches*: a directory under `$ELAN_HOME/toolchains` named in elan's own
  mangled form (`leanprover/lean4:v4.31.0` → `leanprover--lean4---v4.31.0`) is
  adopted as installed. Unpacking the release tarball there is the layout elan
  itself would have produced, not a trick played on it.
* **A capability has to be attempted, not detected.** The Lean tarballs are
  zstd-compressed. `tar --help` advertises `--zstd` on any modern tar, but tar
  implements it by exec'ing the `zstd` *binary*, so on a machine without that
  binary the flag is present and the extraction still fails:

  ```
  tar (child): zstd: Cannot exec: No such file or directory
  ```

  Found by running the script, not by reading it. The three decompression routes
  are now each tried and judged by exit status.

**What it does not fix, and cannot:** the Mathlib olean cache. `lake exe cache
get` downloads from `cache.lean-lang.org` and there is no GitHub mirror, so on
such a host Mathlib and ArkLib compile from source. `make setup` already warns and
continues; the warning now says so explicitly, so the next person reads a
diagnosis instead of 8542 identical 403s.

**Tested:** end to end against a scratch `ELAN_HOME` (elan from the GitHub
release, toolchain unpacked, `elan toolchain list` reporting
`leanprover/lean4:v4.31.0`), and re-run to confirm it is a no-op.

---

## The model contains what the crate *reaches*

**Aeneas/charon finding, caught by `make build` rather than by reading.** Deleting
`smoke.rs` removed `Ext4` from `lean/Generated.lean` entirely, and so broke two
assertions in `lean/Check.lean` § 2 that Workstream 0 had left there.

`--include 'cpoly::_'` says which foreign items charon *may* translate, not which
it does: it still only follows what the local crate reaches. `smoke.rs` was the
only thing that ever touched the extension field, and no module of the scheme does
— the ring, the gadget and the commitment are all over `Z_q`; `Ext4` enters with
the protocol layer, which is out of scope. So the model losing `Ext4` is correct,
and the fix is to assert about the `Fp` items the scheme computes with. § 2 now
checks all four operator impls (`add`, `sub`, `mul`, `neg`) instead.

**The part worth remembering is how it was caught.** Of the two stale assertions,
only one failed:

```lean
example (a : cpoly.field.Ext4) : Std.U64 := a.c0          -- compiled anyway
example : cpoly.field.Ext4.ZERO.c0 = 0#u64 := by …        -- unknown identifier
```

With `autoImplicit` on — the Lean default — an unknown identifier in a *binder
type* is silently auto-bound as an implicit variable. The first example therefore
kept compiling as a statement about a universally quantified nothing. That is
precisely the "true but vacuous" failure `Check.lean` exists to detect, turned on
the audit file itself, and it would have gone on passing indefinitely. `Check.lean`
now opens with `set_option autoImplicit false` (which is also ArkLib's
repository-wide setting, for the same reason).

**Corollary for the audit's design:** an assertion about an extracted name is only
as good as the guarantee that the name still exists. Type ascriptions in *term*
position (`example : Result ring.Rq := ring.Rq.zero`) have that property;
assertions that mention a name only in a binder do not. § 2b is written in the
former style throughout.

---

## The Lean side does build here, it just takes hours

**Supersedes the scoring in § "What this environment could and could not check".**
The from-source build finished: Mathlib and ArkLib compiled, `make build` ran, and
it passed — *and it immediately earned its keep* by failing first, on two stale
assertions (§ "The model contains what the crate reaches").

```
Build completed successfully (3007 jobs).
==> proofs check out: no errors, no `sorry`
```

Cost, for planning: roughly 2700 Mathlib modules on 4 cores while the Rust work
proceeded alongside it. Not minutes, but not the wall it looked like from the 8542
refused cache downloads.

**Definition of done, rescored.**

| | (a) tests | (b) extracted | (c) audit compiles | (d) bench |
|---|---|---|---|---|
| `ring` | ✔ | ✔ | audit ✔, equivalence proofs ✘ | ✔ |
| `linalg` | ✔ | ✔ | audit ✔, equivalence proofs ✘ | ✔ |
| `gadget` | ✔ | ✔ | audit ✔, equivalence proofs ✘ | ✔ |
| `commit` | ✔ | ✔ | audit ✔, equivalence proofs ✘ | ✔ |

Column (c) has to be read in two halves, because they are different claims:

* **The audit compiles.** `lean/Check.lean` is machine-checked, including every new
  claim: the parameters are the ones `params.rs` names, they discharge the spec's
  side conditions (`1 < b`, `q ≤ b^digits`, `b - 1 ≤ q/2`, `q % 8 = 5`, `κ² < q`),
  the derived bounds `GAMMA`/`BETA_SQ` are what the specification's shortness
  lemmas give at these dimensions, and all four modules are present in the model
  with the shapes the proofs will need.
* **The equivalence proofs are still statements.** `hachi/lean-wip/` is not a Lake
  root and is not audited. Nothing about that changed; what changed is that
  iterating on it is now cheap, because Mathlib is built.

**A detail the build also confirmed:** the Makefile's `sorry` scan is correctly
scoped. The build surfaces four `sorry` warnings from `Aeneas.Std.Slice` and
`Aeneas.Std.StringIter` — upstream, in definitions this development never reaches —
and the scan ignores them because it matches only diagnostics carrying this
library's own `lean/` srcDir. The `sorryAx` half of the pattern is what would catch
one reached indirectly.

---

## What is proved, as of the end of this session

**Status entry, superseding the "audit ✔, equivalence proofs ✘" line of the
rescoring above.** The equivalence development is no longer only statements. In the
audited library, `make build` passing means:

| | file | status |
|---|---|---|
| `Fp` operator impls (`add`, `sub`, `mul`, `neg`) total and equal to `ZMod q` arithmetic | `lean/Field.lean` | **proved** |
| `Fp::new` reduces (so `Red` is an invariant of construction) and `toK` is injective on reduced words | `lean/Field.lean` | **proved** |
| `Rq::zero`, `add`, `sub`, `neg`, `scalar_mul` total, length-preserving, coefficientwise correct | `lean/Ring.lean` | **proved** |
| `Rq::mul` (the negacyclic convolution) coefficientwise correct | `lean/Ring.lean` | **proved** |
| `Rq::constant`, `one`, `from_coeffs`, `coeff`, `equals`, `is_zero`, `copy` at the coefficient level | `lean/Ring.lean` | **proved** |
| all thirteen operations lifted to ArkLib's `Rq Φ`, `mul` (i.e. `modByMonic` against `X^N + 1`) included | `lean-wip/RqBridge.lean` | **proved** (unchecked by `make build`) |
| `linalg`, `gadget`, `commit` | `lean-wip/Scheme.lean` | stated |

Nineteen `#print axioms` lines in `Check.lean` § 4 report
`[propext, Classical.choice, Quot.sound]` for every proved spec — the three kernel
axioms the README's trusted computing base names, and nothing else. No `sorryAx`,
and no axiom from an un-whitelisted `cpoly` item.

**Both `lean-wip` files typecheck, and `RqBridge.lean` is now fully proved** — 26
theorems, every one reporting the three kernel axioms. It is not yet *checked*: the file
is not a Lake root, so `make build` never looks at it and a change under it could break it
silently. Promoting it (the procedure in `lean-wip/README.md`) is what would close that
gap, and it is the obvious next step.

`Scheme.lean`'s 23 obligations remain stated only. Typechecking is a weaker claim than
proved and a stronger one than plausible: `lake env lean` elaborates them against the
pinned ArkLib specification with no errors, so each is a well-formed statement about the
specification's own definitions at this crate's parameters. A mistranslation would have
surfaced as a type error rather than waiting for a proof attempt.

### Two things that made the proofs go through

**The development splits at the coefficient level, not at the type level.** The
work in a spec like `add_spec` is the loop invariant and the totality of every
`u64` intermediate; the `Rq Φ` statement on top is bookkeeping through
`ofFinCoeff_coeff`. Separating them (`lean/Ring.lean` for the first,
`lean-wip/RqBridge.lean` for the second) meant the hard half could be proved and
audited against a *much* smaller import surface — `Generated` and `Field`, no ArkLib
at all — instead of waiting on the whole bridge. It is also why the five proved ring
specs are stated in terms of `coeffK` rather than `Rq Φ`.

**One proof pattern covers every coefficientwise operation.** All five are
`loop.spec_decr_nat` with measure `n - i` and an invariant of the same shape
(counter bounded, accumulator length equals counter, entries reduced, coefficients
so far correct). Two lemmas about `out.val ++ [x]` (`coeffK_append_lt`,
`coeffK_append_eq`) are the whole of the `push` reasoning. Once `add` was through,
`sub`, `neg` and `scalar_mul` were mechanical.

Three details cost time and are worth knowing:

* `subst` on the invariant's `s.1 = rhs` conjunct eliminates **`rhs`**, so the rest
  of the body proof has to name the loop-state variable instead — and that conjunct
  is then already discharged for the successor state, which changes the arity of
  the `refine`.
* A triple over `ok (done x)` needs `WP.spec_ok` *and* a reduction of the
  `ControlFlow` match: `show` the postcondition (or `dsimp only`), or the rewrite
  fails with a type-correctness note that does not name the real problem.
* The invariant arrives phrased in projections of the state tuple
  (`↑(o1, i1).1`), so `dsimp only at` the hypotheses before rewriting with them.

### `autoImplicit` again

It bit a second time, in `lean-wip/Scheme.lean`: a missing `open HachiEquiv.Field`
turned `q`, `Red` and `toK` into auto-bound implicit variables, so `dd`'s side
condition became `⊢ q ≤ 4294967296` for an arbitrary `q` — unprovable, which is the
lucky case. Had the statement not needed a side condition it would have compiled as
a theorem about every natural number. **Every file in this development now sets
`autoImplicit false`.** For an equivalence development this is not a style option:
the failure mode it prevents is precisely the one the audit exists to catch.

### One more import to know about

`Nat.Prime 4294967197` is decided by norm_num's primality extension, and that
extension is not reached by ArkLib's imports. Without an explicit
`import Mathlib.Tactic.NormNum.Prime` the `Fact (Nat.Prime q)` instance fails with a
bare `⊢ Nat.Prime 4294967197`, which reads like a hard problem and is actually a
missing import.

---

## The first benchmark run, and what it says about the harness

**Measurement, on an idle machine, and the finding is about the harness rather than
the code.** `make run-bench` completed (`EXIT=0`), 32 cases across the four groups.

Order of magnitude, `now` column, which is what a caller would wait for:

| case | time |
|---|---|
| `ring/mul` (64×64 negacyclic convolution) | 8.51 µs |
| `ring/add`, `sub`, `neg`, `scalar_mul` | 190–245 ns |
| `ring/equals` | 20 ns |
| `gadget/gadget_mul` (4 rows × 32 digits) | 68.9 µs |
| `gadget/gadget_decompose` | 82.2 µs |
| `gadget/gadget_matrix` (materialized `G`) | 123 µs |
| `linalg/dot` (128 entries) | 1.16 ms |
| `linalg/mat_vec_mul` (2 × 128) | 2.29 ms |
| `commit/commit` (2 blocks, end to end) | 6.83 ms |
| `commit/verify_weak` | 8.41 ms |
| `commit/l1_norm`, `l2_norm_sq` | 37 ns, 57 ns |

The shape is as expected: everything above the ring is `ring::mul` in a loop, and
the norms are invisible next to it. `gadget_matrix` costing more than `gadget_mul`
is also as expected and is the reason `gadget_mul` exists — materializing `G` builds
`rows²·digits` ring elements of which all but `rows·digits` are zero.

**The finding: the A/B harness cannot currently resolve small differences.** `now`
and `genesis` are byte-identical source (the frozen copy differs only in comments),
so every gap between the two columns is harness bias. The gaps are large:

| case | now | genesis | apparent "difference" |
|---|---|---|---|
| `ring/_control` | 212 ns | 243 ns | 15% |
| `linalg/_control` | 27.9 µs | 31.7 µs | 14% |
| `commit/_control` | 297 ns | 271 ns | 10% |
| `ring/scalar_mul` | 192 ns | 306 ns | **59%** |
| `ring/neg` | 222 ns | 307 ns | 38% |
| `commit/verify_weak` | 8.41 ms | 11.72 ms | **39%** |

The `_control` cases did exactly the job they exist for — they put a 10–15% floor
under every reading in their group — but `scalar_mul` and `verify_weak` are *worse
than the floor*, and `verify_weak` is a multi-millisecond case, so this is not the
small-case jitter the floor was meant to bound.

Most likely cause is the environment rather than the configuration: this is a
4-core cloud container with no CPU pinning, no isolation from neighbours, and
steal time invisible to the process. `profile.bench` already carries the
`lto = "fat"` / `codegen-units = 1` settings that AeneasCompPoly adopted after
measuring a 28% artefact under thin LTO, so the usual suspect is already ruled out.

**Consequence, and it is a real one for the optimization loop:** on a host like
this, a "vs genesis" reading is trustworthy only for effects well above 50%. Before
this harness is used to accept or reject a candidate, it needs one of — a machine
with CPU pinning and quiet cores, many more samples per case, or a comparison
method that is robust to placement (interleaved repetitions rather than one block
per variant). Until then, treat the table above as sizing information and *not* as
a baseline to compare a future candidate against.

This also supersedes the caveat in § "Benchmark numbers from this session are not
measurement-grade": the numbers are now taken on an idle machine, and the problem
turns out not to have been the competing build.

# The AeneasCompPoly skills, ported

[AeneasCompPoly](https://github.com/tobias-rothmann/AeneasCompPoly) carries 33
skills in `.claude/skills/` — written procedures for the two loops this
repository also runs: optimize an operation until a benchmark says it is faster,
then prove the optimized Rust equivalent to the specification. This repository
already followed that method in structure; what it lacked was the method written
down, and the enforcement the written method assumes. Both are now here, together
with [`INSTRUCTIONS.md`](INSTRUCTIONS.md) as the catalogue.

## What was actually missing, as opposed to differently book-kept

Most of the gap was bookkeeping: the same disciplines, recorded in prose here and
in schemas there. Three things were not.

**The genesis stamps were decorative.** Every frozen item carried
`// @genesis (this file's introducing commit) 2026-08-18 — <path>` — a
placeholder that reads to a human as provenance while satisfying nothing. There
was no `check-genesis`, so nothing compared the frozen text against git, and
`make run-bench` had no gate: an edited baseline would have made every past and
future "vs genesis" figure wrong, silently and retroactively. This was the one
place the repository was *weaker* than its own documentation claimed, not merely
less mechanised. `make bench-stamp` now derives the stamps from history and
`make bench-check` verifies them; all **81** frozen items resolved, 74 to
`d664190` (where the four modules landed) and 7 to `4409640` (the `params.rs`
consts already in final form at Workstream 0). Genesis was byte-identical to
`hachi/src` at the time, so this was a clean first stamping rather than a repair.

**The coverage gate would have been vacuous.** `coverage --strict` requires every
item claiming to mirror an ArkLib definition to be benchmarked or excluded by
name with a checkable reason. The claim is a ``Mirrors `<name>` `` docstring
line, and there was exactly **one** in the whole crate (on `ring::Rq`), even
though every module doc already carried a spec-to-here correspondence table with
`file:line` references. A gate over one item passes trivially — which in a
repository whose TCB table warns about "a spec that quantifies over an
uninterpreted symbol, and so says nothing" is the wrong kind of green. There are
now **40** markers, every ArkLib name confirmed against the pinned spec at
`hachi/.lake/packages/Arklib/`. The 14 `params.rs` consts are deliberately
unmarked: a const is a *value chosen for a generic parameter*, not a translation
of a definition, and marking one would claim `RING_LOG_DEGREE` *is*
`hachiModulus` rather than its argument `α`.

**There was no digest oracle.** A bench case can measure less than it claims, or
measure the wrong thing, and both make a number go down — the direction an
autonomous loop reads as success. The bench layer now runs one body per case,
which the harness either times or runs once and digests, and asserts that
`hachi`, the frozen copy and the candidate slot agree *before* timing anything.

## The 5% accept floor is borrowed, and no host here has yet earned it

The accept rule the skills enforce — only a recentered, within-run
`CANDIDATE=1` delta, over a 5% floor, vetoed above 10% A/B bias — comes with
numbers that were measured on AeneasCompPoly's machine, not ours. Every skill
says so where it uses one; `harness.py`'s `MIN_EFFECT` comment says so at length.
Nothing here has been swept.

That matters more than a missing calibration usually would, because the one run
this repository has completed failed the harness's own self-test: § "The first
benchmark run, and what it says about the harness" recorded controls at
15%/14%/10% and byte-identical source reading 59% and 39% apart, i.e. a run
`USABLE_BIAS_MAX` would have refused outright. So the honest status is not "the
floor is untuned" but "no instrument here has yet resolved anything the floor
could gate", and the skills are written to expect the veto to fire rather than to
be surprised by it.

**And that run and this port were not on the same machine**, which is why the
sentence above says "no host" rather than "this host". The earlier readings came
from a 4-core cloud container; the port was done on a 16-core Ryzen 8845HS. A
first smoke run here (`ring/mul` plus the four controls) put the worst control at
**3.5%**, comfortably inside the veto — encouraging, and *not* evidence, for two
independent reasons: a `lake build` was running during it (load 1.82/16), which
is exactly the contention the machine-serialization rule exists to forbid, and
one filtered run of one row is not a sweep. Nothing from it is recorded as a
result. It does mean the 10–15% figures should not be read as a property of the
harness: they are a property of that container, and the instrument's real floor
here is unmeasured in both directions.

The controls were rebuilt during the port, and the obvious hypothesis for the
10–15% readings **did not survive contact with the old data.** Two of the three
controls were sub-microsecond (`Rq::zero()` at 212 ns in `ring`, 297 ns in
`commit`), which is where timer and scheduling noise dominate, and
AeneasCompPoly sizes its own control near 19 µs *and* makes it allocate on the
explicit ground that a too-quiet control flatters the harness while its number is
what every real row must clear. So "the control was too cheap" was the natural
diagnosis. But the `linalg` control in that same run was **already** a
`PolyVec::zeros(128)` at 27.9 µs — properly sized by exactly this standard — and
it read **14%**, no better than the 212 ns one's 15%. One properly-sized control
reading as badly as two cheap ones is evidence the noise is not about control
size.

The controls were nonetheless made uniform — `_control/<binary>` is now
`PolyVec::zeros(128)` in every bench binary, ~15.6–18.9 µs, one separately
compiled copy per variant crate so it sees code layout *and* timing order, which
is both halves of what the recentering claims to divide out. That is a
correctness argument about what the instrument measures, not a fix for the floor,
and it should not be recorded as one.

What remains is the cheapest experiment available, and it is still unrun: the
candidate slot is null and genesis is byte-identical to `hachi/src`, so a full
`make run-bench` on a quiet machine measures nothing but that machine's own
noise, and **every row of it must read noise**. The worst row that does not is
this repository's floor. Until that exists, `MIN_EFFECT` is a borrowed number and
the residual-noise question is open.

One trap the new control carries, documented in `benches/support/mod.rs` rather
than left to be discovered: `PolyVec::zeros` fills with `Rq::zero`, which is
itself now a benched row. So a candidate that rewrites `Rq::zero` moves the
control. That fails closed rather than silently — `harness.py` computes the bias
veto from the worst pairwise control delta *before* printing any verdict, and
`ring/zero` is then the row that explains why — but it is the reason a control
must never be an operation on the optimization loop's path.

## An Aeneas surprise: a docstring edit moves `Generated.lean`

Adding the 40 `Mirrors` lines changed `hachi/lean/Generated.lean` by **304
line-pairs** — and every single one is a `Source:` span, zero code lines, zero
axioms. Aeneas records each declaration's provenance as a `file, lines a:b-c:d`
comment, so *any* edit that shifts a line number in `hachi/src` rewrites the
model even when the program is identical.

Two consequences worth knowing before they cost someone an afternoon. A
comment-only change to `src/` obliges a re-extraction: skip it and the next
`make extract` reports `regenerated`, which is exactly the signature of toolchain
drift and is the first thing extraction triage chases. And the determinism
contract — `make extract` on unchanged Rust must report `unchanged` — is
therefore a claim about the *working tree*, not about the program: it was
restored here by regenerating (verified: re-running now reports `unchanged`, and
the diff contains no code line).

Relatedly, the ten `Source:` lines that name the `cpoly` checkout are written as
`/cargo/git/checkouts/<url-hash>/<short-rev>/…`, a path charon normalises. So the
cross-crate whitelist costs nothing in determinism — but the `cpoly` **rev is
visible in the artifact**, and bumping it regenerates those ten lines with no code
change at all.

## Deliberately not done

`hachi/lean/Opt.lean` does not exist, and `Opt` is not in `roots`. The Lean-side
optimization skills create both on their first run — with the `Check.lean` §4
`#print axioms` line that goes with them — and that is a checkable step better
left to the procedure that owns it than pre-empted by an empty module. No
optimization pass has run, so `logs/ledger.jsonl` is empty, and no skill implies
otherwise: there are no past champions or campaigns here to reason from.

`.claude/settings.json` denies `git commit`, which is what makes "agents stage,
the user commits" enforced rather than trusted — the same move as the stamps, one
level up.

# The parameters forbid a radix-2 NTT

**Observation, found while porting the optimization skills, and it retires the
obvious first candidate.** [`hachi/benches/ring.rs`](hachi/benches/ring.rs)
describes `Rq::mul` — the schoolbook `O(N²)` negacyclic convolution at `N = 64` —
as "the operation an NTT would replace, so this reading is the baseline any such
optimization has to beat *and* carry an equivalence proof for". ArkLib's own
`CyclotomicRing` tree carries a `TODO add proper NTT multiplication here`. So a
number-theoretic transform is the first thing anyone will reach for.

At these parameters it does not exist. A radix-2 negacyclic NTT of length `N`
needs a primitive `2N`-th root of unity in the coefficient field, i.e.
`2N | q - 1`. Here `N = 64`, so it needs `128 | q - 1`, and:

| | |
|---|---|
| `q = 2^32 - 99` | `4294967197` |
| `q - 1` | `4294967196 = 2² · 1073741799` |
| `v₂(q - 1)` | **2** — the largest 2-power root of unity has order 4, not 128 |
| `v₂(q⁴ - 1)` | **4** — so `cpoly`'s quartic extension does not rescue it either |

Two consequences. The complexity-class win on the hot path is **not** a
transform: what remains at this modulus is a convolution *split* (Karatsuba over
`a = a₀ + X^{N/2}a₁`, three half-length products instead of four, and the
negacyclic relation `X^N ≡ −1` folds the wrap-around for free), or a change of
carrier, or a different modulus. And the modulus is not ours to change: `Q` is
`cpoly`'s Hachi prime, forced by the dependency (§ "Chosen parameters"), so
"pick an NTT-friendly prime" is an upstream question about `cpoly` and the
[NOZ26] parameter set, not a local optimization.

This is recorded here rather than only in the skills because it is a fact about
the parameters, and the next person to read "an NTT would replace this" deserves
to meet it in the same file as the parameter choices. A candidate proposing a
transform has to name its root of unity, and no such root exists below order 4.

---

## `RqBridge.lean` is promoted: proved now also means checked

**Status entry, superseding the "proved (unchecked by `make build`)" row of
§ "What is proved, as of the end of this session".** `RqBridge.lean` has moved
from `lean-wip/` to `lean/`, through the procedure in `lean-wip/README.md`:
it is a root of the `HachiEquiv` library in `hachi/lakefile.lean`, `Check.lean`
imports it, and § 4 prints one `#print axioms` line per headline spec — all
thirteen operations, thirty-two audit lines in total now. A change under it
(to `lean/Ring.lean`, to the ArkLib pin) is a build failure from here on, not
a silent break.

One practical consequence for `lean-wip/`: `Scheme.lean`'s `import RqBridge`
now resolves through the built library, so the `/tmp/wiplib` `LEAN_PATH` detour
its README used to prescribe is gone — `lake build` then
`lake env lean lean-wip/Scheme.lean` is the whole workflow. `Scheme.lean`'s 23
obligations remain stated only, and are the last debt in that directory.
