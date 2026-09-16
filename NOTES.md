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

### Superseded 2026-09-01: the local 4.33 port replaces "no fork"

The title above is now false — the revisit condition fired, one version
higher than predicted. ArkLib main merged `feat/hachi-completeness` and
moved to Lean/Mathlib v4.33.1; upstream aeneas releases stop at v4.31.0,
and upstream `main` is still there (checked 2026-08-31: 64 commits past
`3a8586f`, no 4.33 coming). The bridge is our own port: commit `6125cb9e`
("bump to 4.33") in the sibling `../aeneas` checkout, exactly one commit on
top of upstream `3a8586f` — the same commit the pinned extraction binaries
are built from. The regenerated builtins table was checked semantically
identical to upstream's, so the release binaries and the charon pin stay
valid, and the post-port extract formality on commit `6f30811` confirmed
`Generated.lean` is a fixpoint under the port (`make extract` reported
`unchanged`, 0 axioms, `make build` green).

The comment on `require aeneas` in `hachi/lakefile.lean` is the source of
truth now, not this section. Known residual: the require is a `file://` URL
to the sibling checkout, so the build reproduces only on this machine until
the port is published to a public fork — then move only the URL, keeping
the rev pin (`lake update aeneas`).

**Not published — decision of 2026-09-07.** A move of the require to a
public fork was prepared on 2026-09-04 and reverted; the `file://` require
stays, and the aeneas repository is not to be updated for it. The residual has
teeth the plan did not credit it with: the Lean CI job fails at the clone on
every push since 2026-09-03, because the runner cannot read a `file://` path
on this laptop. So `lean.yml` stays red, and `make build` on this machine is
the Lean gate until the require points somewhere a runner can fetch.

**To revisit (replaces the paragraph above):** a rebase onto a moved
upstream is a project decision, never maintenance — upstream already has
two charon bumps queued, so rebasing means rebuilding the extraction
binaries and re-baselining the extraction under a verify-campaign. The
trigger to even consider it: an extraction bug on a protocol-layer
construct that upstream has fixed (the protocol-layer plan, Decision 2).

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

### Superseded 2026-08-28: the paper's commitment/eval-split dimensions are adopted

The open question above is answered: the repository now uses the *commitment
and evaluation-split* dimensions of the [NOZ26] Fig. 9 benchmark parameter set
(the ℓ = 30 row), adopted per the paper-parameters plan so that this crate's
measurements are about the same scheme the paper measured -- with the verifier
bounds taken not from Fig. 9 directly but from ArkLib's paper-parameter mapping
for the *weak-opening* relation (see below), and with two honesty caveats
recorded at the end of this entry. The field layer (`Q = 2^32 - 99`,
`EXT_DEGREE = 4`, `EXT_W = 2`) was already the paper's; everything else moved:

| const | old | new | Fig. 9 name |
|---|---|---|---|
| `RING_LOG_DEGREE` (`α`) | 6 | **10** | `d = 1024 = 2^α` |
| `GADGET_BASE` | 2 | **16** | `b` |
| `GADGET_DIGITS` | 32 | **8** | forced: `16^8 = 2^32 ≥ q`, `16^7 < q` |
| `GAMMA` | 1 | **16** | ArkLib weak-opening `γ̄ = b` (Soundness.lean) |
| `BETA_SQ` | 8192 | **163 966 054 471 565 312** | ArkLib `quadEvalBetaSq b b τ d m δ` at `τ = 4` |
| `MESSAGE_ROWS` | 4 | **1024** | `2^m`, `m = 10` |
| `BLOCKS` | 2 | **1024** | `2^r`, `r = 10` |
| `INNER_ROWS` | 2 | **1** | `n_A` |
| `OUTER_ROWS` | 2 | **1** | `n_B` |
| `KAPPA` | 65535 | **32** | ArkLib weak-opening `ω̄ = 2ω`, `ω = 16` |
| `ML_VARS_LOW/HIGH` | 1/2 | **10/10** | `r`/`m`; `ℓ - α = 20` variables ✓ |
| `ML_*_LEN` | 2/4/8 | **1024/1024/1048576** | literals for `2^10`, `2^10`, `2^20` |

Decisions taken with the user (2026-08-28; the bound values were then corrected
the same day after the user's review -- see "The verifier bounds are the
weak-opening triple" below):

* **`KAPPA` off the invertibility ceiling.** `κ` used to sit at
  `⌊√q⌋ = 65535`, the most permissive legal value; it now carries the
  weak-opening bound. `kappa_is_the_invertibility_ceiling` became
  `kappa_is_legal_for_invertibility` (legality `κ² < q` -- ArkLib Lemma 8's own
  `hκ : (2ω)² < q` -- plus the `2ω` relation), and the matching ceiling example
  was dropped from `lean/Check.lean` § 1.
* **`INNER_ROWS = OUTER_ROWS = 1`.** `dimensions_are_nondegenerate` now asserts
  only `≥ 1` for the two Ajtai row counts (a single row is the paper's shape,
  not a degenerate one); the multi-row index-computation duty is carried by
  `BLOCKS = MESSAGE_ROWS = 1024`.
* **Full-const tests and benches are opt-in** — see below.

**The verifier bounds are the weak-opening triple, not the honest-case one.**
The first cut of this flip set `(κ, γ, βSq) = (16, 15, 1 887 436 800)` -- the
paper's sampled-challenge bound `ω` and the honest unsigned decomposition's own
norms. The user's review caught the category error: those are the bounds an
honest `c = 1` opening meets, not the ones the extraction protocol's weak
openings must be verified against. ArkLib documents the intended mapping
explicitly (`QuadEval/Soundness.lean`, "Paper parameter mapping", Hachi
Lemma 8): `(βSq, γ, κ) = (quadEvalBetaSq γ b τ d m δ at γ := b, b, 2ω)` --
extracted openings carry challenge *differences* (`≤ 2ω`), the paper's `S_b`
box is relaxed to the symmetric ball `γ = b`, and `βSq` is ArkLib's deliberate
squared-`ℓ₂` replacement for the paper's `β̄ = 2·b^τ`, which at
`(γ = b = 16, τ = 4, d = 1024, m = 10, δ = 8)` evaluates to
`4·(2^10·8)·(1024·(4369·16)²) = 163 966 054 471 565 312 ≈ 1.64·10^17`. A
verifier at the honest-case values would reject extracted openings the ArkLib
`relIn` admits. The honest bounds now sit strictly inside (`15 < 16`;
`1 887 436 800` is ~8.7·10^7 below `βSq`), which also means **no admissible
challenge can push an honest opening past `βSq`** -- the `ℓ₂²` rejection test
became `an_overlong_message_decomposition_is_rejected`, and the slot-rewrite
tests moved to `+2b/-2` so they clear `γ = b` strictly.

**No repo counterpart** (the protocol layer is deliberately absent, `lib.rs`
§ Status): the paper's `n_D`/matrix `D`, the `z` norm bound 30583, and the
sparse-challenge count `c = 16`. `τ = 4` (the `z`-decomposition expansion)
appears in exactly one place -- inside `BETA_SQ`'s derived literal, per the
mapping above -- and nowhere else; no other constants were invented, and the
`z`-machinery itself arrives with the protocol layer.

**The gadget decomposition is not paper-faithful at `b = 16`.** The paper uses
balanced base-16 digits in `[-8, 7]`; the pinned ArkLib
(`zmodDigitDecomposition`) -- and therefore this crate, by hard rule 1 -- uses
unsigned digits in `{0, …, 15}` (§ "The digits are not balanced"). Harmless at
`b = 2`, where the two representations carry essentially the same bound; at
`b = 16` it changes the honest decomposition outputs (and so commitment
values), the honest norm sizes, and the norm side of the paper's argument for
`n_A = n_B = 1`. The fix trigger is recorded: upstream ArkLib PR #782 switches
the honest layer to `balancedZmodDigitDecomposition` (the reason
`QuadEval/Gadgets.lean` was never onboarded, § Workstream 2), and adopting it
here is an ArkLib pin bump plus a gadget-layer re-verification, not a local
edit. Until then, cross-implementation comparisons with the paper are
dimension-for-dimension, not output-for-output.

**Test policy at paper scale (the Phase 4 deviation).** A full-const message is
`BLOCKS × MESSAGE_ROWS = 2^20` ring elements of 1024 coefficients (~8 GiB), and
one `commit` is ~2^23 schoolbook ring products of ~2^20 field ops each — hours.
The full-pipeline tests in `commit_semantics.rs` / `evalsplit_semantics.rs` are
therefore `#[ignore]`d (run on demand: `cargo test --release -- --ignored`, on
a machine sized for them), with the tamper/shortness logic they exercised kept
live in shape-generic property tests over small ad-hoc vectors. This is a
recorded deviation from the repo habit that tests exercise the real consts.

**Bench policy at paper scale.** The scheme-level `commit` cases and the
const-bound `evalsplit` reshape/evaluation cases are excluded by a signed-off
policy exception (`benches/exclusions.toml`, new section, with the arithmetic);
the two shape-generic basis cases run at reduced variable counts (4 and 6) with
the deviation stated in the bench file; `CONTROL_N` moved 128 → 8192 with the
block width it is pinned to. All of it returns the moment a sub-quadratic
`ring::mul` champion lands — which the parameter flip turns from optional into
the single highest-leverage optimization in the repository (`opt-algo-swap`,
the Karatsuba/convolution-split candidate).

**Genesis re-freeze.** Every frozen baseline was measured at the old
parameters, so genesis was re-frozen to the new first translations under the
re-freeze carve-out (see `.claude/skills/rust-bench`): `logs/ledger.jsonl` was
empty and no measurement had been published against the old baselines, so there
was no history to rewrite. **No benchmark reading taken before this flip is
comparable to one taken after it** — including every number in § "The first
benchmark run", which was already labelled sizing information.

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
the honest digit bound `b - 1` sits strictly inside `params.rs`'s weak-opening
`GAMMA = b`, with the side condition checked in `params_semantics.rs` and
`lean/Check.lean` § 1.

**Update 2026-08-28, at `b = 16` this stopped being harmless.** The paper's own
decomposition is *balanced* base-16 (digits in `[-8, 7]`), so with the Fig. 9
dimensions adopted (§ "Chosen parameters") the unsigned form now diverges from
the paper's implementation in commitment outputs, honest norm sizes, and the
norm side of the `n_A = n_B = 1` justification -- see the caveat recorded in
the superseding parameters entry. The fix is upstream: ArkLib PR #782's
`balancedZmodDigitDecomposition` (already the reason `QuadEval/Gadgets.lean`
was not onboarded, § Workstream 2); adopting it is an ArkLib pin bump plus a
gadget-layer re-verification.

**Update 2026-09-01: the pin bump landed, and the resolution is a sibling,
not a flip.** Commit `6f30811` moved the pin to merged main (`294b3f0b0`),
which carries `balancedZmodDigitDecomposition` — and the composed protocol
chain instantiates its message and z decompositions at it
(`HonestChain.lean:350–351`). The adoption shape is settled the other way
from the paragraph above's guess: the balanced layer is **added alongside**
the unsigned one, and `gadget.rs` is never flipped — the 74 proved specs
keep targeting `zmodDigitDecomposition 16 8`, which stays present and green
at the pin because `InnerOuter/Scheme.lean` is decomposition-generic. The
"gadget-layer re-verification" is thereby avoided by construction; the cost
moves to a new balanced sibling surface instead (the protocol-layer plan,
Decision 4, and § "Spec stability at the pin" under Workstream 3 below).

**Update 2026-09-04: the sibling surface exists, and the promotion cost no
rename.** Stage 3 target 1 onboarded it — `gadget::balanced_digit_at`,
`balanced_digit_decompose`, `balanced_gadget_decompose`, the `z`-side
`bounded_z_digit_at`, `commit::{generate_decomps_balanced, commit_balanced}`
and the new `ringswitch::rho_digits`, seven `Mirrors`-marked items, all frozen
into genesis at their first translation.

The target brief's re-base section expected Decision 4's revision ("balanced =
public API, unsigned = primitive") to force a rename pass through `hachi/src`,
on the grounds that PR #847 renamed `commitBalanced` → `commit` and deleted the
unsigned committer. It does not, and the reason is worth recording because it
looked settled the other way: **`hachi/src`'s `commit` never mirrored
`Commitment.lean`'s committer.** It mirrors `InnerOuter.commitmentScheme.commit`
(`commit.rs`), which takes the `Decomposition` as a *parameter*
(`InnerOuter/Scheme.lean`) and is untouched by #847 — as are
`zmodDigitDecomposition`, `generateDecomps` and `commitWithDecomps`. Every
`Mirrors` target the existing crate names still exists at `d51d8bc`, so the
promotion is pure addition: the balanced items take their own names, the
unsigned ones keep theirs and the seventy-four proved specs with them, and
`benches/genesis/` is appended to rather than re-frozen under new names.

What the promotion *does* move is which statement is the headline. That is a
spec-layer choice, and it is made in `lean-wip/Balanced.lean`:
`commit_balanced_spec` is stated against the balanced instantiation — which,
composed with `Hachi.toMatrix`, is `Hachi.commit` itself.

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

**Update 2026-09-03 — the protocol layer's third count, `zDigits` = τ, is
*not* 8.** The `z`-decomposition's digit count was briefly read as a third
copy of 8, by the same `q ≤ b ^ digits` argument, while ArkLib stated the
`z`-gadget under `hqz : q ≤ b ^ zDigits`. ArkLib PR #847 removed that
hypothesis (`BoundedDigitDecomposition`: the folded witness is
deterministically short, so `τ` is sized from its bound, not from `q`) and
fixed **τ = 5** for the `ℓ = 30` profile. So the message and inner counts are
one constant (8) and `τ` is a genuinely different one (5) — see § "`BETA_SQ`
corrected" under Workstream 3. (The `b = 2`/32 arithmetic above is pre-flip:
at today's `b = 16` the two gadget counts are 8.)

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

## What the compiler already does to the digit layer (2026-09-04)

Target 1's birth run was audited under `rust-bench` §4 — twelve read-only
refutation agents, four lenses over three case groups, adjudicators on every
refutation. **No finding survived**: all five new cases measure their item and
nothing else, and the three refutations were overturned on disassembly of the
run's own binary. What that disassembly showed is worth more than the verdict.

**The source-level "hoist the constants" optimization is already done, by
rustc.** `balanced_digit_at` is written as
`digit_at(c + Fp::new(BALANCED_SHIFT), e) - Fp::new(HALF_BASE)`, and the target
brief priced it at five `% P` per digit against `digit_at`'s one, with
`opt-word-arith`'s "hoist the two constant `Fp::new`s" as the headline win. In
the emitted code both constants are folded to immediates and hoisted above the
criterion loop; in `balanced_digit_decompose`, `GADGET_DIGITS` being a constant
lets rustc unroll the loop entirely and CSE the eight `c + shift` computations
into **one** add and **one** reduction. The source-level hoist would delete zero
instructions. The same is true of `digit_decompose`: its `O(digits²)` division
chain — the thing `hachi/benches/gadget.rs`'s own header advertises as the first
thing an optimization would remove — is already collapsed to constant `shr`s off
one value.

Read the general lesson, not the local one: **"the first translation does not
make this optimization" is a claim about the source, and the fitness function
measures the binary.** Several docstrings in this repository make that claim, and
at these constant sizes rustc falsifies most of them. Price a candidate against
`objdump`, not against the Rust.

**But there is still a real `opt-word-arith` target, and it is a different
one.** Two reductions survive inside the timed loop: a full Barrett multiply-
shift for `Fp::add`, and a conditional-subtract fold for `Fp::sub`. LLVM emitted
the cheap form for the `Sub` only because that operand is the literal `8`; it
could not for the `Add`, because `Fp`'s reducedness is not in its type
(`hachi/src/ring.rs` records exactly this). Both operands *are* below `P` —
`BALANCED_SHIFT = 2290649224 < P` — so the sum is below `2P` and one conditional
subtract suffices. That is `opt-word-arith`'s conditional-subtract fold, it sits
at a named address, and it generalizes to every `Fp::add`/`Fp::sub` in the crate.
It is also a `cpoly` boundary question, since `Fp` is a dependency and not ours
to reimplement.

**And the brief's cost model is wrong about what dominates.** The per-digit rows
are taken-branch bound, not reduction bound: `e` reaches the callee through
`black_box`, so the digit loop cannot be unrolled, and at `e = 7` the row is
about eight taken branches. That is why `bounded_z_digit_at` at `Z_DIGITS - 1 =
4` reads *faster* (1.43ns) than `digit_at` at 7 (1.90ns) while doing more work
per digit, and why the balanced chain's extra straight-line uops cost only ~6%.
An optimization aimed at the reductions will not move these rows much; one aimed
at the division chain will.

## A `--since` cut can silently drop half a sweep (2026-09-04)

Also from that audit, and a harness lesson rather than a code one. The birth run
was a full six-binary sweep, 09:39:12 to 09:56:37. It was first reported with
`--since` set to 09:45 — six minutes in — which silently discarded all five
`commit` rows, `_control/commit`, `_control/evalsplit`, and three `evalsplit`
rows, and printed **"A/B bias 0.7%"** when the worst control actually measured
was `_control/commit` at **1.4%**, twice that. No verdict moved, because
`t_genesis = max(MIN_EFFECT, bias)` is `5%` either way — but the number was
wrong, and the run id derived from that cut (`…T0945…`) does not have the
property `harness.py` documents for it, that the timestamp is the run's start.

`make run-bench` cannot produce this: it stamps `started` before `cargo bench`.
It is reachable only by regenerating a report by hand with a later `--since`,
which is exactly what happened. Two consequences worth carrying: **quote the A/B
bias from the run's own report, never from a re-derivation**, and note that
`report` filters *per variant* and keeps a case if any variant is fresh — so a
cut landing mid-case can pair a fresh `now` against a stale `genesis`. It did not
here; the mechanism exists. The corrected run id for target 1's birth is
`20260904T0939+0200-0d88eccc`, 40 rows and 6 controls, A/B bias 1.4%.

> ⟲ **Corrected the same evening:** that id is *also* a re-report artifact, not
> the run's own — `run_id` hashes `head_state()` at report time, and this
> re-report ran at HEAD `4c146b1`, a commit that did not exist while the sweep
> measured (HEAD was `09df61b`). The 0939 run's own id was never captured; its
> provenance is the commit and the window. See § "Two full null-slot sweeps, and
> the run id that cannot name them (2026-09-04)".

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

## The NTT is possible after all -- in three other fields

**Superseding the section above, 2026-09-16.** Everything it says is true and
none of it is retracted: `v₂(q − 1) = 2`, `v₂(q⁴ − 1) = 4`, there is no
power-of-two root of unity above order 4 anywhere near this modulus, and `q` is
still not ours to change. What the section got wrong is the conclusion it drew
from that -- "the complexity-class win on the hot path is **not** a transform"
-- because it only ever considered transforms *in the coefficient field*.

The product does not have to be computed in `Z_q`. Coefficient `k` of the
product of two `Rq` elements is, before any reduction, an **integer**: a sum of
at most `N` products of representatives below `q`, so at most `N·(q−1)² < 2^74`.
An integer convolution can be computed in any ring large enough to determine it,
and the CRT makes "large enough" a choice of primes rather than a property of
`q`. So the transform runs at three auxiliary primes

```text
p1 = 469762049   = 7 · 2^26 + 1
p2 = 998244353   = 7 · 17 · 2^23 + 1
p3 = 1004535809  = 479 · 2^21 + 1
```

each of which *does* have a root of exact order `2N = 2048`, and Garner
reconstruction recovers the integer coefficient exactly, because
`p1·p2·p3 ≈ 2^88.6` dwarfs the bound. Only then is anything reduced mod `q`.
`hachi/src/ntt.rs` is that construction and `hachi/lean/Aux*.lean` is its
equivalence proof; `logs/ntt-execution.md` is the full execution record,
including what was measured and what was tried and rejected.

Three things are worth keeping from the attempt, because each contradicts
something a reader would reasonably assume:

1. **The textbook route is slower than the schoolbook loop it replaces.** A
   *cyclic* transform of length `2N` with zero padding -- the obvious way to get
   an ordinary convolution out of a cyclic transform, and the one the plan
   specified -- measured **0.79×** the schoolbook product. It does 2.2× the
   transform work of the negacyclic form, on buffers twice the size. What clears
   the gate is the negacyclic transform at length `N`, reached by the twist
   `X ↦ ψ·Y`, which costs two extra proof obligations and half the arithmetic.
2. **The signed coefficient is handled by an offset, not by a sign test.** The
   negacyclic coefficient `posSum − negSum` is signed, and the CRT reconstructs
   a residue class. Adding `BOUND = N·q²` before reconstruction makes it a
   natural number in `[0, 2·BOUND]`, and `2·BOUND < P` keeps the reconstruction
   exact. `BOUND` is `N·q²` rather than the tighter `N·(q−1)²` for two proof
   reasons: it is the ceiling `Ring.lean`'s `posSum_le`/`negSum_le` *already*
   prove, so no sharper bound was needed; and `q ∣ N·q²`, so the offset is
   invisible mod `q` and `Rq::mul` needs no correction term at all.
3. **Doing less arithmetic made it slower, twice.** A runtime `t % len` in the
   stage index was 70 % of a stage's cost (a hardware division); removing it was
   free. But the natural butterfly -- writing both outputs in one iteration,
   which does strictly fewer multiplications and half the loads -- measured
   **17 % slower** than two sequential half-block loops, because the split form
   writes its output buffer in one increasing stream. The code therefore
   computes one twiddle product twice on purpose, and `ntt.rs` says so where a
   reader would otherwise "fix" it.

The exclusions whose removal condition was "until a sub-quadratic `ring::mul`
lands" (`benches/exclusions.toml`) now have their condition met on the
arithmetic as well as on the note above. They are **not** removed here: turning
one into a row is the un-ignore ceremony that file assigns its own slot.

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

---

## The scheme layer is proved, and checked

**Status entry, superseding the `lean-wip/Scheme.lean` rows of § "What is proved, as
of the end of this session" and § "`RqBridge.lean` is promoted".** `Scheme.lean` has
moved from `lean-wip/` to `lean/` through the same procedure: it is a root of the
`HachiEquiv` library, `Check.lean` imports it, and § 4 prints one `#print axioms`
line per headline spec. The 23 obligations that were "stated only" are proved, and
`lean-wip/` is now empty.

**Definition of done, rescored.** Column (c) no longer splits into halves — the
audit compiles *and* the equivalence proofs are checked, for every module.

| | (a) tests | (b) extracted | (c) audit + proofs | (d) bench |
|---|---|---|---|---|
| `ring` | ✔ | ✔ | ✔ | ✔ |
| `linalg` | ✔ | ✔ | ✔ | ✔ |
| `gadget` | ✔ | ✔ | ✔ | ✔ |
| `commit` | ✔ | ✔ | ✔ | ✔ |

Fifty-eight `#print axioms` lines in `Check.lean` § 4 report
`[propext, Classical.choice, Quot.sound]`: 6 for `Field.lean`, 13 for `Ring.lean`,
13 for `RqBridge.lean`, 26 for `Scheme.lean`. No `sorryAx`, and no axiom from an
un-whitelisted `cpoly` item.

**What the top of the composition says.** The last line is
`Scheme.honest_verifies`: for an honest commitment and its honest opening, the
extracted `commit::verify_weak` returns `true`. It reaches every other line above
it, so its axiom set summarises the development. Two features of the statements
below it are what make that worth having rather than tautological:

* `verify_weak_spec` is an **equality of decisions**, not an implication. An
  implication in the accepting direction is satisfied by a verifier that rejects
  everything — the failure a correctness test cannot see. Only the equality puts the
  rejection paths inside the claim, which is what makes `honest_verifies` a
  statement about *this* verifier rather than about some verifier.
* `gadget_round_trip` is about the *Rust*: the extracted `gadget_mul` inverts the
  extracted `gadget_decompose`. It is the one claim at this layer a reader can also
  check against the test suite
  (`tests/gadget_semantics.rs::gadget_mul_inverts_gadget_decompose`), and it is
  where the scheme's correctness rests.

**Four statements were weakened to be true, and each is recorded in place.** The
originals are kept verbatim in comments beside the theorems that replaced them,
with the counterexample that killed them — the pattern is worth naming because in
every case the falsity was an artefact of the Aeneas model's fixed-width and
capacity invariants, not of the Rust's intent:

* `flatten_blocks_spec` gained `hsize : blocks * width ≤ Usize.max`. The output has
  `blocks * width` entries and `alloc.vec.Vec` admits lengths only up to
  `Usize.max`; hypotheses bounding `blocks` and `width` separately do not bound
  their product, so the final `push` could `fail`.
* `gadget_decompose_spec` gained `hmax : 32 * rows ≤ Usize.max`, for the same reason
  one level down: the Rust pushes `32 * rows` ring elements, and the input `x` bounds
  only `rows`. This one is the mildest of the four, and worth the distinction: the
  postcondition already asserts `WfVec (rows * 32) z`, which forces `32 * rows` below
  `Usize.max` anyway, so the hypothesis takes away nothing the conclusion did not
  already carry.
* `vec_l2_norm_sq_spec` gained `hsize : k * (N * (q / 2) ^ 2) ≤ U128.max`. `u128` is
  wide enough for one ring element's `ℓ₂²` norm (`N · (q/2)² < 2^68`) but not for a
  vector of up to `Usize.max` of them.
* `verify_weak_spec` gained `hoc : WfVec 2 o.challenge`. The verifier indexes
  `opening.challenge[i]` and takes its `ℓ₁` norm, and the `Opening` type carries no
  shape condition on that field — with an empty `challenge` the left-hand side is
  `fail`, so no postcondition holds of it. The only one of the four that is not an
  arithmetic bound: it is a shape invariant the extracted struct simply does not have.

At the crate's concrete dimensions all four side conditions are discharged at the
call sites, by `decide` or `scalar_tac` on numerals. They are model artefacts rather
than gaps in the Rust: `usize` capacity and `u128` width are where a proof about a
Rust program has to meet the machine.

**What is left.** Not the scheme layer. The protocol layer (per-link provers and
verifiers) is still blocked upstream on unfilled definitional parameters in its
ArkLib specification, and the optimization loop's ledger is still empty — no
measurement-grade bench run has happened on this host (§ "The 5% accept floor is
borrowed"). `Rq::mul` remains the hot path, and § "Deliberately not done" records
why the transform everyone reaches for does not exist at this modulus.

---

## Three mirrored operations were never stated, and the coverage gate cannot see it

**Finding, and a gap in a gate rather than in a proof.** § "The scheme layer is
proved, and checked" says nothing is left stated-but-unproved. That was true of
everything that had been *stated*. Three public functions of `hachi/src` carry a
``Mirrors `<ArkLib name>` `` docstring, are extracted into `Generated.lean`, are
benchmarked — and had no equivalence statement anywhere:

| Rust | mirrors | why it matters |
|---|---|---|
| `commit::verify` | `InnerOuter.commitmentScheme.verify` | the scheme's full verifier; `honest_verifies` reaches only `verify_weak` |
| `gadget::gadget_matrix` | `gadgetMatrix` | `gadget_mul_spec` can hold while the materialized `G` is transposed |
| `gadget::digit_decompose` | `zmodDigitDecomposition.digit`, at every `e` | `digit_at_spec` can hold while the digit *order* is reversed |

**The gate that should have caught it, doesn't.** `make bench-check`'s
`coverage --strict` requires every mirrored item to be benched or excluded by name
with a reason — and that is all it requires. Nothing requires a mirrored item to be
*specified*. So "40 `Mirrors` markers, 58 audited specs" looks like comfortable
surplus and is not a comparison of the two sets at all. The asymmetry is worth
closing in `harness.py`: the same scan that proves an item is benched can prove a
`_spec` mentioning it exists, and until it does, "mirrored" and "specified" have to
be reconciled by hand.

The seven statements (three headline, four loop specs) are staged in
`hachi/lean-wip/SchemeGaps.lean`, typechecked with zero errors, and promote into
`lean/Scheme.lean`.

**`verify_spec` cannot name the bundled scheme, and the reason is an instance.**
ArkLib's verifier is a structure *field* — `InnerOuter.commitmentScheme`'s
`verify` — and `commitmentScheme` carries two `SampleableType` instance arguments
that its `setup` field needs and its `verify` field does not. `SampleableType β`
demands a `ProbComp β` that is uniform with full support, i.e. a uniform sampler
over a matrix of `Rq Φ`, and neither ArkLib nor CompPoly has one at these types
(the elaborator: `failed to synthesize SampleableType (Simple.PublicParams Φ
?rows (?cols * 32))`).

Taking the two as hypotheses would have been the wrong repair, and it is worth
naming why, because it looks harmless: an instance argument nobody can supply makes
the theorem **vacuously** true, and it would then print a clean
`[propext, Classical.choice, Quot.sound]` line in `Check.lean` § 4 while claiming
nothing. That is exactly the failure § 1–§ 3 of that file exist to catch, arriving
by a route none of them watches.

So `verify_spec` states the `verify` field's own body at this crate's parameters,
naming `InnerOuter.derivedMessage` and `InnerOuter.verify_weak` in the field's own
`List.finRange` / `decide` / `&&` shape. **The cost, recorded because it is a real
one:** alone among the headline specs, this statement does not move automatically
if ArkLib restructures `commitmentScheme.verify` — the type error that would catch
a mistranslation elsewhere will not fire here. An ArkLib bump wants this theorem
re-read by hand. It becomes the bundled form, by `rfl`, the moment those instances
exist.

**`hm.1` is load-bearing, not defensive.** `verify_spec` hypothesizes
`m.val.length = 2`, and without it the equality of decisions is *false* rather than
merely unprovable: the specification's message is `Fin 2`-indexed, so a shorter `m`
is represented with zero-padded blocks, and the specification can then accept a
message the extracted verifier rejects on its length test. The other four
hypotheses (`hpp`, `hu`, `hoc`, `ho`) are `verify_weak_spec`'s, inherited
unconditionally: the extracted body calls `verify_weak` on *both* branches of the
length test, because the Rust sets `ok = false` and falls through rather than
returning early.

---

## The three gap statements are proved, and two of their recorded rationales were wrong

**Status entry, extending § "Three mirrored operations were never stated".** The
seven statements staged in `hachi/lean-wip/SchemeGaps.lean` are now proved: zero
errors, zero `sorry` warnings under `lake env lean`, and every theorem's axiom
closure is `[propext, Classical.choice, Quot.sound]`. An eighth theorem was added,
`honest_verifies_full`: perfect correctness restated at `commit::verify` itself —
the derived-message check included — closing the observation that
`honest_verifies` reaches only `verify_weak`. The file awaits promotion
(steps 2–5 of `lean-wip/README.md`).

An adversarial audit (four lenses plus a critic, each backing claims with
compiled scratch files) found no defect in any proof or statement, and two
defects in the *prose* this log had recorded about them:

* **The vacuity rationale for `verify_spec`'s unbundled right-hand side was
  false.** § "Three mirrored operations…" says instance binders nobody can supply
  would make the theorem "vacuously true… while claiming nothing". The critic
  refuted this by compiling the bundled-form statement under the two
  `SampleableType` binders and discharging it with `verify_spec`'s own proof
  term: the `verify` field never mentions the instances, so the binder form is
  the *same* claim, true and clean-axiomed. The real cost of the binder form is
  different and remains decisive: no instance exists, so no caller could ever
  eliminate the theorem — unusable, not vacuous. The unbundled statement stands;
  the reason in `SchemeGaps.lean`'s docstring is corrected.
* **The hypothesis accounting undersold two load-bearing hypotheses.** The same
  section credits only `hm.1` as load-bearing for the truth of the equality of
  decisions. The audit exhibited falsifying witnesses for `hm.2` (a block of the
  wrong inner width flips the extracted `equals` while `toVec (k := 4)` cannot
  see the discrepancy) and `hu` (a lengthened `u` flips `verify_weak`'s outer
  comparison while `toVec (k := 2) u` is unchanged). All three share one
  mechanism — `Fin`-indexed representation functions are blind to carrier-length
  deviations the extracted length tests reject — now recorded in the file's
  section note.

**To revisit:** promotion moves the three headline specs (and
`honest_verifies_full`) into `Check.lean` § 4; the four loop lemmas stay out of
§ 4, which has never audited loop specs.

---

## The gap statements are promoted

**Status entry, closing § "The three gap statements are proved".**
`lean-wip/SchemeGaps.lean` is gone: its eight theorems now live in
`lean/Scheme.lean` beside their siblings — the `digit_decompose` pair after
`digit_at_spec`, the `gadget_matrix` trio after `gadget_entry_spec`, and the
`verify` pair plus `honest_verifies_full` after `honest_verifies` — each with
its section note, the bundled-scheme rationale included. `Check.lean` § 4 gained
four `#print axioms` lines (`digit_decompose_spec`, `gadget_matrix_spec`,
`verify_spec`, `honest_verifies_full`; the four loop lemmas stay out of § 4 per
its headline-only rule), bringing the audited count to sixty-two, and its
summary line is now `honest_verifies_full`: perfect correctness at
`commit::verify` itself. `make build` passes — no errors, no `sorry` — so all
eight are enforced from here on. `lean-wip/` is empty again, and its README and
the root README are updated to match.

---

# Workstream 2: the evaluation split (`evalsplit`, the sixth module)

## What was onboarded, and the two decisions that shaped it

`Hachi/EvalSplit.lean` — `splitEquiv`, `toMatrix`, `toPolynomial`, `evalSplit`,
`toMatrixEval`, `evalSplitEval`, plus their chain (`splitForm` from
`Vectors.lean:178` into `linalg`, and the two CompPoly bases `monomialBasis` /
`lagrangeBasis` at `R = Rq Φ`). Sorry-free and definition-stable at the pin;
checked against upstream PR #782 ("perfect correctness of the nonrecursive
Hachi"), which does not touch this file and only adds lemmas to its
dependencies. Its sibling `QuadEval/Gadgets.lean` was deliberately **not**
onboarded: its definitions are parametric in a `DigitDecomposition`, and #782
switches the honest layer to the new `balancedZmodDigitDecomposition` and pins
`dRows`/`zDigits` — translating it now would freeze the unsigned-digit
instantiation into an append-only baseline just before the spec abandons it.

**The carrier is `Rq`, not the extension field.** The plausible reuse — cpoly's
`multilinear.rs` (`MultilinearPoly`, `monomial_basis`, `dot`) — is over `Ext4`,
and the consumer pins the other choice: the bridge works with
`CMlPolynomial (Rq Φ) (r + m)` and `derivedMsgMatrix : PolyMatrix (Rq Φ) (2^r)
(2^m)` (`QuadEval/Bridge.lean:104`, `QuadEval/Reduction.lean:193`). So the
bases and reshapes are implemented over `Rq` with this crate's own ring/linalg
layer, and the `Ext4` multilinear layer stays what it is — the §3 packing
layer's tool, protocol-side, out of scope.

**The split dimensions are derived, not chosen.** `2^nl` = matrix rows =
`blocks` and `2^nh` = columns = `messageRows` (same citations), so at
`BLOCKS = 2` / `MESSAGE_ROWS = 4` the crate gets `ML_VARS_LOW = 1`,
`ML_VARS_HIGH = 2`, length-8 polynomials. Five new consts, all literals with
relations checked in `tests/params_semantics.rs` and `Check.lean` § 1 —
including `ML_LOW_LEN = BLOCKS` and `ML_HIGH_LEN = MESSAGE_ROWS`, the two that
tie the split to the commitment's shape.

## The sixth module, and what extending the harness actually took

`MODULES` in `harness.py` grew to a 6-tuple, and that edit turned out to be the
*only* harness change: the slot file-count check, the null-slot report and the
stamping all derive from the tuple. The rest was mechanical and enumerable:
`pub mod evalsplit;` in both slot `lib.rs` (append-only in genesis), a
`[[bench]]` **and** `[[test]]` declaration in `hachi/Cargo.toml` — both
`auto*` flags are off, and the test one is the trap: an undeclared
`tests/evalsplit_semantics.rs` silently never runs while `cargo test` stays
green. Caught here because the suite count did not move.

A second silent-gate near-miss, worth its own sentence: the coverage scanner's
`Mirrors` regex accepts only `Mirrors (ArkLib's)? \`name\``, so the four
markers written as ``Mirrors ArkLib's (CompPoly's) `…` `` were *invisible* to
`coverage --strict` — 0 unaccounted, wrong denominator. The tell was the
mirrored count moving by 8 when 12 markers were added. Rewritten to put the
backticked name immediately after "Mirrors"; the parenthetical now follows the
name.

## Status at the end of the session

(a) 80 tests green (was 66), clippy-pedantic clean; (b) extracted — 47 new
definitions, zero axioms, determinism `unchanged`, no existing definition
moved, loop states in the known 2/3-tuple classes; `Check.lean` § 1 gained the
five-const block and § 2b the eleven shape ascriptions; (c) equivalence
statements: 12 theorems in `lean-wip/EvalSplit.lean`, typechecked with zero
errors (`sorry` warnings only) — the recorded proof debt of this onboarding;
(d) bench: 8 new cases (7 in `benches/evalsplit.rs` + `linalg/split_form`) plus
the module's `_control`, 4 by-name exclusions. Genesis and candidate slots hold
the new items verbatim; stamps and the birth run wait on commit 1 per the
op-genesis choreography.

---

# Workstream 3: the protocol layer

## Spec stability at the pin, and the rules it imposes

**Audit record, 2026-08-31 (file-level read of the pinned tree at
`294b3f0b0`, then upstream `main`'s tip; recorded here 2026-09-01 as Stage 2
of the protocol-layer plan opened).** Everything below was read from
`hachi/.lake/packages/Arklib/ArkLib/Commitments/Functional/Hachi/` (45 Lean
files); it fixes what the protocol-layer specs may be stated against. Four
records, each with the rule it imposes.

**Thirteen sorries, and the `Commitment.hachi` rule.** Twelve sorries sit in
`Recursion/` — 6 in `PartialEval.lean`, 4 in `TraceHandoff.lean`, 2 in
`ZBatchBridge.lean` — and one outside it: `Commitment.lean:199`, the
recursive scheme instance's field `hachi.opening := sorry`, whose own
docstring warns the field's *type* will change when it lands. Two of the
Recursion sorries are documented in their docstrings as design gaps rather
than proof debt: `TraceHandoff.lean:238` is "not merely unproven but false"
as stated (:210), and `ZBatchBridge.lean:117` is "expected to be unprovable"
as stated (:42, :105–106) — the eventual fills will churn protocol content,
not just proofs. The saving grace: `Composition.lean` does not import
`Recursion/`; the composed chain ends at `relWEvalClaim` and closes with
`endPiece`, and `Recursion/Basic.lean`'s docstring itself says the adapters
are not composed. **Rules:** the recursive tail is out of scope, and no spec
of ours mentions `Commitment.hachi` — a sorried field whose type will move
takes any statement through it along. Revisit only on a deliberate re-pin
after `Recursion/` is sorry-free.

**The composed chain is balanced; the proved bottom layer is unsigned.**
`HonestChain.lean:350–351` and `Correctness.lean:384` instantiate the
message and z decompositions at `balancedZmodDigitDecomposition`; our 74
proved specs target the unsigned `zmodDigitDecomposition 16 8`, which stays
green because `InnerOuter/Scheme.lean` is decomposition-generic. **Rule:**
add the balanced sibling layer, never flip `gadget.rs` — the full record is
the 2026-09-01 update under § "The digits are not balanced".

**The upstream `sorryAx` line, for the Stage 7 claims ledger.** Every
*composed* completeness theorem (`hachiNonrecursive*_perfectCorrectness`)
inherits `sorryAx` from ArkLib's generic `Reduction.append_completeness`
(`OracleReduction/Composition/Sequential/Append.lean`, 11 sorries, plus
`LiftContext/Reduction.lean`); the soundness-side composition is claimed
clean. **Rule:** our obligations are equivalence-to-*definitions*, so this
taints ArkLib's meta-theorems and none of our specs — but every public claim
must say which side of that line it sits on, and the comparison deliverable
carries the split explicitly.

**Keys and challenges are inputs, not constants.** The Ajtai lift key `D` is
caller-supplied all the way through `Concrete.lean` (`hachiLiftCom`'s
docstring: "a full treatment would sample it in `keygen`"), and the fold
challenge sampler is carried as an undischarged
`[SampleableType (ShortChallenge …)]` hypothesis (`Composition.lean:196`).
**Rule:** the Rust protocol API takes `D` and the challenge streams as
explicit arguments — no invented keygen, no baked-in randomness — which is
also what keeps per-link equivalence provable for public-coin verifiers.

## Re-pin to ArkLib PR #847 (`d51d8bc`), and the unsigned layer becomes a primitive (2026-09-03)

**What moved.** `hachi/lakefile.lean` now requires ArkLib at
`d51d8bc3c22062bf21385bd15b39d390b0fe4584` — the head of PR #847
(`hachi-cleanup`, a *draft*, branched from main at pin+17 and behind main by
11 lint/perf commits at the time). A deliberate re-pin under the protocol-layer plan
Decision 2, taken because Stage 3's first target is not defined at `294b3f0b0`:
the pin's `z`-decomposition was full-width under `hqz : q ≤ b ^ zDigits`, and
#847 replaces it with `BoundedDigitDecomposition` at `τ = 5` (see § "`BETA_SQ`
corrected" below). Toolchain and Mathlib did not move (`lake update Arklib`:
"toolchain not updated", Mathlib cache "No files to download"); only the
`Arklib` rows of `lake-manifest.json` changed. `Generated.lean` is untouched —
it depends on the Rust and the Aeneas pin, not on ArkLib. Expect one more
re-pin, to the merge SHA, when #847 lands (it is still moving: 4 commits in a
day).

**What the pin's second day changed.** Commit `eab7eaa32` ("unbalanced digits
& docs") *demotes* the unsigned decomposition: `zmodDigitDecomposition`'s
docstring now reads "the building block the balanced digits are shifted from,
not itself a Hachi gadget inverse"; `commitBalanced` is renamed `commit` and
the unsigned committer is deleted; and the unsigned norm lemmas
`zmodDigit_natAbs_le`, `gadgetDecompose_zmod_vecLInftyNorm_le`,
`gadgetDecompose_zmod_l2NormSq_le`, `gadgetDecompose_zmod_vecL2NormSq_le`,
plus `gadgetDecompose_apply`, `gadgetDecompose_eq_fun` and
`DigitDecomposition.toBounded`, are gone. `zmodDigitDecomposition` itself,
`gadgetDecompose`, `gadgetDecompose_lawful`, `gadgetDecompose_coeff` and the
generic `gadgetDecompose_{vecLInftyNorm,l2NormSq,vecL2NormSq}_le_of_digit_le`
survive.

**Repair bill: three proof sites, no statement changed.** All 74 specs
typecheck as stated; the edits are proof-internal.

* `Scheme.lean` (`gadget_decompose_spec`'s index bookkeeping):
  `gadgetDecompose_apply Φ dd …` → `gadgetDecomposeFun_apply Φ dd.digit …`,
  stated at `gadgetDecompose` (which is `gadgetDecomposeFun Φ dd.digit` by
  definition, so the term is accepted unchanged).
* `Scheme.lean` (`verify_weak_honest`, both norm conjuncts): the two
  `_zmod_` lemmas → the surviving `…_of_digit_le` forms at a new local
  `dd_digit_natAbs_le : (dd.digit c e).valMinAbs.natAbs ≤ 15` — a verbatim
  copy of the deleted `zmodDigit_natAbs_le`, specialised to `dd`, kept next
  to `def dd`. The unsigned layer now owns its one analytic input.
* `Check.lean` § 1: three comments that named the deleted lemmas.

`make build`: 3496 jobs, no errors, no `sorry`; § 4's `#print axioms` lines
unchanged.

**Decision 4 revised: promote, don't shadow.** With upstream calling the
balanced digits *the* gadget inverse and shipping a balanced-only `commit`,
"add the balanced layer alongside, never flip" would leave the public Rust
`gadget_decompose`/`commit` on a decomposition the spec no longer treats as
Hachi's. The user's call (2026-09-03): adapt. Target 1 becomes a
**promotion** — the balanced digit map and decomposition take the
`gadget_decompose` / `generate_decomps` / `commit` names, matching
`Hachi.commit`, and the proved unsigned `digit_at` becomes the primitive they
are built from, exactly upstream's own structure. The 74 specs keep their
content (the unsigned instantiation still exists upstream as a building
block); the cost over the sibling plan is a rename pass plus re-pointing the
headline `commit_spec` at the balanced committer. Full note:
the protocol-layer plan Decision 4 ⊕⊕.

**Stale until folded.** the Stage 2 scoping document and the six briefs were read at
`294b3f0b0`; the τ = 5 deltas (μ₀ 57344, lift width 57384, m₀ 26,
`Z_BOUND = honestZBound = 131072`, `Z_DIGITS = 5 ≠ GADGET_DIGITS`), the
promotion shape, and the deleted-lemma citations (`rhoDigitsShortCheck_eq_true_of_digitBaseOk`,
`hachiLiftCom_com`, `balancedDigit_valMinAbs_mem`) are owed to them along
with the Stage 2 corrections list.

## The protocol layer's parameters land, and Stage 2 closes (2026-09-03)

**What landed.** Eighteen constants appended to `hachi/src/params.rs` under
a "protocol layer" banner — `OMEGA`, `D_ROWS`, `B_ZERO`, `CHAIN_GAMMA`,
`HALF_BASE`, `BALANCED_SHIFT`, `Z_DIGITS`, `Z_BOUND`, `Z_BALANCED_SHIFT`,
`RLIN_CW/CT/CZ`, `RLIN_COLS`, `RLIN_ROWS`, `D_QUAD_COLS`, `LIFT_COLS`,
`M_ZERO`, `M_ONE` — every one a literal (the `RING_DEGREE` reason), every
one read today only by `tests/params_semantics.rs` (27 tests) and
`lean/Check.lean` § 1 (`section ProtocolParams`, 54 rows). The values are
ArkLib's own `ℓ = 30` profile, `Hachi/Params.lean` at the pinned PR #847
head: **τ = 5**, `zBound = 131072`, `μ₀ = 57344`, lift width 57384,
`M = 25` (so `M_ZERO = m₀ = 26`), `γ = 15`, `bZero = 16`. Three things the
Stage 2 audit table (the Stage 2 scoping document § Parameter mapping) listed were
*not* introduced, each for a reason recorded there: `RHO_DIGIT_COUNT`
(equals `GADGET_DIGITS`; the identity is a Check row via
`HachiParams.clog_eq_delta`), `TAU` (a second name for `Z_DIGITS`) and
`CHALLENGE_WEIGHT` (no ArkLib expression *and* no consumer — the spec sees
a challenge only through `‖c‖₁ ≤ ω`; corpus sparsity is a bench-side
knob). `Generated.lean` regenerated with exactly the eighteen new
`def params.*` lines plus `Source:` shifts — the gate the plan set.

**Named ties, for the first time.** Until now every derived literal's
Check row was an unnamed recomputation — and an unnamed recomputation
agrees with itself at any τ, which is exactly how the τ = 4 error survived
review. `Params.lean` names the quantities, so § 1 now states
`params.Z_DIGITS.val = HachiParams.hachiTau`, `params.Z_BOUND.val =
HachiParams.honestZBound`, `params.RLIN_COLS.val = HachiParams.mu0`,
`params.LIFT_COLS.val = HachiParams.liftKeyWidth`, and
`HachiParams.liftKeyWidth * hachiD ≤ 2 ^ params.M_ZERO.val`; the rest tie
to the defining arithmetic (`rlinCW/CT/CZ/Rows`, `digitOnesValue`,
`balancedDigitCapacity`, `rhoDigitCount`). Technique: `rw
[<Params.lean>_eq]; simp [params.X]`, and `simp only [hachiB, hachiTau] at
h` to bring a profile lemma down to literals. `Check.lean` imports
`Hachi.Params`, which pulls the whole chain — the build is 3841 jobs now.

**The house-discipline exception shrank to one row.** Stage 2's F4 listed
four constants with no ArkLib expression (`Z_BOUND`, `CHALLENGE_WEIGHT`,
`M_ZERO`, `M_ONE`). `Z_BOUND` is `honestZBound`; `M_ZERO`'s coverage and
minimality are `sumcheckWidthAtProfile{,_minimal}`; `CHALLENGE_WEIGHT`
does not exist. **`M_ONE` alone** keeps the exception — ArkLib holds `m₁`
free under `n₀ ≤ 2^m₁` and the profile names no value — recorded at the
constant and in § 1's section header. **Rule (restated):** a literal in
`params.rs` has a `Check.lean` § 1 row equating it to the ArkLib name where
one exists and to the defining expression otherwise; `M_ONE` is the one
row that is coverage + minimality only, and a second such row needs its
own justification here.

**Two literal-collision additions** for the proof watchlist (rewrite
hypotheses, never goals): value **5** is now `Z_DIGITS` and `RLIN_ROWS` —
τ and n₀, unrelated; value **15** is `CHAIN_GAMMA` and the unsigned digit
ceiling `b − 1`. The full list is in `params.rs`'s banner.

**Doc-sync items 4–6 rode this landing**, as the plan scheduled: `lib.rs`
§ Status no longer says the spec has unfilled parameters (it says: absent
as code, present as parameters); `params.rs`'s caveats state the
promotion (unsigned = the spec's building block, balanced = the gadget
inverse target 1 promotes to the public names); `exclusions.toml`'s header
no longer carries a const count.

**Stage 2 is closed.** the Stage 2 scoping document was re-based on the new pin the
same day (marks ⊗⊗): the six briefs' corrections folded in, the τ = 5
constant table, the reversed target-2 verdict (`Z_DIGITS = 5 ≠
GADGET_DIGITS`, so `_z` siblings return), m₀ = 26, the five scale walls,
and Decision 4's revision; brief 1 carries a re-base section (promotion +
the bounded τ = 5 digit map `boundedBalancedZmodDigit`, a *second* digit
function with a conditional reconstruction spec). The briefs' `file:line`
citations remain at `294b3f0b0` and are re-read when each target opens.
Next: Stage 3, `/op-genesis` target 1 ∥ target 2.

**Genesis mechanics, for the record.** `params` is a `MODULES` member, so
`check-genesis` wants each new const frozen in `benches/genesis/src/params.rs`
and stamped. The eighteen were copied verbatim (docstrings included, the
banner omitted — a stamp leads on the item's own doc), and the stamp dance
applies as the Makefile states it: commit the translation and the frozen copy
together, `make bench-stamp`, commit the stamp lines separately, never
`--amend`. The genesis `BETA_SQ` stays at the stamped τ = 4 literal — the
baseline is not re-frozen for a bound no benched case reads.

## `BETA_SQ` corrected: τ = 5, not Fig. 9's τ = 4 (2026-09-03; supersedes an uncommitted τ = 8 reading of 2026-09-01)

The stamped params work derived `BETA_SQ = quadEvalBetaSq γ b τ d m δ` at
`τ = 4`, read off [NOZ26] Fig. 9's z-decomposition digit count. That τ is not
instantiable in ArkLib, for a reason that was misdiagnosed once before being
fixed upstream:

* **The 2026-09-01 diagnosis (τ = 8) — never committed.** At pin `294b3f0b0`
  every Hachi theorem instantiated `τ := zDigits` under
  `hqz : q ≤ b ^ zDigits`, the `z`-gadget covering all of ℤ_q, which at
  `b = 16` forces 8. A working session moved the literal to
  `704250333132185328448176128` (≈ 2^89.2) on that reading. The reading was
  faithful to the pin but the pin was wrong about `z`: the folded witness
  `z = Σᵢ cᵢ sᵢ` is deterministically short (`‖z‖∞ ≤ 2ʳ·ω·⌊b/2⌋ = 131072`),
  so demanding full coverage sizes the gadget from `q` when it should be
  sized from that bound — the z-shortness plan is the audit.
* **The fix (ArkLib PR #847, `hachi-cleanup`, 2026-09-03).**
  `BoundedDigitDecomposition` — a total, executable digit map whose
  reconstruction law holds on short inputs only — replaces `hqz` with
  `hcap : zBound ≤ balancedDigitCapacity b τ` through the whole chain
  (`QuadEval/Reduction.lean`'s `honestComputeResp`/`zDecompBounded`,
  `HonestChain.lean`, `Correctness.lean`, `Concrete.lean`), and
  `Hachi/Params.lean` fixes the `ℓ = 30` profile at **τ = 5**: five balanced
  base-16 digits carry `7·69905 = 489335 ≥ 131072`, four carry `7·4369 =
  30583 < 131072` (`tau_minimal`). 30583 is exactly Fig. 9's `z` bound — the
  paper's τ = 4 rests on a sharper statistical analysis ArkLib does not
  formalize, so τ = 5 is the conservative, perfectly-complete choice
  (the z-shortness plan's Option B).

The literal is now `41976510894886092800`
(`= 4·(1024·8)·(1024·(69905·16)²)`, ≈ 2^65.2, fits u128); the honest bound
`1887436800` sits under it by ~2.2·10¹⁰, so completeness never noticed any of
the three values. `Hachi/Params.lean` names the same expression `betaSq`
(`quadEvalBetaSq params.γ hachiB hachiTau d hachiM hachiDelta`), so on the
re-pin to #847 `Check.lean` § 1 gains a name-binding row for it — at the
current pin the check is the arithmetic only, and says so.

Both `τ = 4` and `τ = 8` were wrong in the same way: βSq is the
knowledge-soundness radius (Lemma 8 extracts openings only up to
`quadEvalBetaSq(τ)`), and a verifier at any other radius either rejects
extracted-grade openings the design must admit (τ = 4) or admits ones the
extractor never produces (τ = 8). Equivalence-wise each simply targeted a βSq
instantiation no composed theorem uses.

Consequences, one reversed and one kept:

* **The ℓ₂² branch is live again.** Under the τ = 8 reading the largest
  representable `ℓ₂²`, `(1024·8)·1024·(q/2)² ≈ 3.9·10²⁵`, sat under
  `βSq ≈ 7.0·10²⁶`, so `verify_weak`'s norm rejection could not fire and
  `commit_semantics::an_overlong_message_decomposition_is_rejected` had lost
  its witness. At τ = 5 (`βSq ≈ 4.2·10¹⁹`) the witness is long again: the
  ignored full-scale test is back verbatim from the τ = 4 commit, its cheap
  half lives as `the_l2_check_can_fire_at_these_dimensions`, and `Check.lean`
  § 1 carries the strict inequality as an example.
* **`√βSq ≈ 2^32.6 > q ≈ 2^32` still** — by 1.5× rather than 2^12.6× — so
  the weak-binding hypothesis at this radius remains not SIS-instantiable at
  Fig. 9's toy row count. This is ArkLib's ball-relaxed `γ̄ = b` at work
  (the z-shortness plan: the box-`γ` restatement would put it 1.3× under
  `q`), not the translation. Owed to the Stage 7 claims ledger.

**Rule:** τ's only appearance in the crate is inside the `BETA_SQ` literal;
it is `HachiParams.hachiTau`, and it changes only when that upstream
definition does — never by re-deriving it from a hypothesis (`hqz`) or a
paper table (Fig. 9). The genesis mirror keeps the stamped τ = 4 value: no
benched case reads `BETA_SQ` (`verify_weak` is excluded), so the baseline is
not invalidated.

## Two full null-slot sweeps, and the run id that cannot name them (2026-09-04)

The calibration § "The 5% accept floor is borrowed" asked for was attempted
twice as the two Stage-3 birth runs, and neither settles the floor. Both are
full `make run-bench CANDIDATE=1` passes with the candidate slot null and
genesis byte-identical to `hachi/src`, so every row measures only this machine
and this harness — every row should read noise, and the worst that does not is
the local floor.

| sweep | provenance | rows / controls | A/B bias | worst byte-identical row |
|---|---|---|---|---|
| morning (target 1's birth) | commit `09df61b` + then-uncommitted stamps; window 09:39:12–09:56:37; **no run id captured**; **machine conditions not recorded** | 40 / 6 | 1.42% | `ring/from_coeffs/1024` −7.54%, `ring/constant/1024` −6.73%, both verdict *faster* |
| evening (target 2's birth) | `source fcd5381`, quiet-gated start 19:26:39 | **incomplete — see below** | — | — |
| 2026-09-07 (certified) | `source 460905d`, run `20260907T1158+0200-d70ac8d1`, gated + lid-inhibited + monitored — § "The certified null-slot sweep" | 47 / 7 | 4.42% | `quadeval/in_sb/1024` −7.31%, `ring/one/1024` +6.17% |

The morning sweep's only in-band evidence of quietness is its own control
spread (bias 1.42%), which is the weakest evidence there is — the controls are
exactly what a contended run corrupts. So its two `ring/*` rows are an
*observation from a run whose conditions were not certified*, not a floor. The
evening sweep was the certified one — gated on four consecutive quiet samples
(no `lean`/`lake`/`cargo`/`rustc` above 5% CPU, load under 1.5), with a monitor
sampling load every 30 s throughout — but it **died at 146/147 variants** when
the session was torn down, killed in the last binary (`ringswitch`) before
`report` ran, so it produced no report and no id. **It must be re-run clean; the
floor question is still open** (re-run 2026-09-07 — § "The certified null-slot
sweep" below — which answers it), and the honest reading here remained that
this host's
harness noise sits somewhere between the ~1.4–2.2% the controls show and the
~6–8% the worst `ring/*` rows show — the gap being the per-case layout and
warming effect the flat single-control design does not model.

**The run id cannot name a measurement.** `harness.py`'s `run_id` is
`<start stamp>-<sha256 of machine | rustc | head_state().sha | case:variant
pairs>`, and `head_state()` is read when `report` runs, not when `cargo bench`
did — and `src_dirty` is not in the hash. Inside one `make run-bench` the start
stamp and the report-time HEAD coincide, so an id printed by the measuring
recipe is sound; a *detached* re-report is not. The morning sweep measured at
HEAD `09df61b`; re-reported at `4c146b1` it minted `…-0d88eccc`, re-reported
again at `fcd5381` it minted `…-071b29ef`, and no id was printed at measurement
time. So: cite only an id printed by the recipe that measured; never re-derive
one after a commit; quote the report's `source <sha>[+uncommitted]` line beside
the id, since the id alone cannot witness a clean tree; and when a run's id was
not captured, its provenance is the commit plus the time window. The fix — pass
the recipe's `started`-time sha into `report` rather than reading HEAD there —
was made on 2026-09-07: `report` takes `--source-sha`/`--source-dirty`, the
recipe reads both beside `started`, the JSON carries them as `source`, and a
report invoked without them reads HEAD and labels its `source` line a
re-report. Checked by re-deriving the certified sweep's report with
`--source-sha 460905d`: it reproduces `20260907T1158+0200-d70ac8d1`; a
different sha mints a different id. That check used the original 47-row case
set, before the later `in_sb_box` measurements changed Criterion's mutable
state; re-report stability assumes the case/variant set is unchanged.

**The shake-out that did run.** `BENCH='quadeval|_control' CANDIDATE=1`, run
`20260904T1914+0200-40dec1a6`, `source fcd5381` (no `+uncommitted`), bias 2.19%,
7 controls — the first execution of target 2's cases. All five `quadeval/*`
digested and read noise (worst +1.6% vs genesis), so **target 2's freeze is
faithful**. Its one anomaly is the sub-microsecond case: `quadeval/in_sb/1024`
(583 ns against a 36.8 ms control) read the null candidate slot **+18.6%
"slower"** on byte-identical code, and the per-binary recentering left it there,
because the binary's control is a 36.8 ms `PolyVec::zeros` with no layout
sensitivity in common with a 583 ns case — the documented cost of the flat
single-control design, biting for the first time. A row that size cannot carry
a candidate verdict.

**A §4 corpus trap on those cases** (from the auditor session; its own record
is separate). `support::corpus` draws coefficients uniformly from `[1, q)`, so a
coefficient lands in the box `[-8, 7]` with probability ≈ 3.7·10⁻⁹: every
benched `Rq` is *outside* the box, `in_sb`/`vec_in_sb` answer a constant
`false`, and their digest contributes nothing (the bench's `check()` is what
discriminates). The teeth: `in_sb` is branchless, the obvious first optimization
is an early exit, and on an all-outside corpus an early-exit candidate books a
~1000× win that exists only for rejected inputs — while the honest workload, the
balanced decomposition's digits, lies entirely *inside* the box and is the slow
path. This is `rust-bench` §2's `Rq::is_zero` trap. Fix, agreed and append-only:
`quadeval/in_sb` and `vec_in_sb` keep their `[1, q)` reject-draw meaning, and
`in_sb_box`/`vec_in_sb_box` are *added* for the honest in-box workload, so no
existing case id changes meaning. Those rows were added on 2026-09-07. The
scalar case is still in the locally unreliable 100 ns–2 µs band, so neither
scalar row carries an acceptance verdict until the harness gains a per-band
floor or case-local control.

**A contention source the rule did not name.** The evening sweep's first attempt
was discarded because opening `hachi/lean/QuadEval.lean` in the IDE spun up
`lake serve` and a `lean --server` that elaborated the file at 30–65% CPU during
the `commit` binary's samples (caught by the monitor at 19:23). Add the editor's
Lean server to the pre-run check: `ps -eo pcpu,comm | grep -E 'lean|lake'` before
*and* during a run, not only a check for `lake build`.

## The certified null-slot sweep, and what the floor turned out to be (2026-09-07)

The run the section above asked for. `make run-bench CANDIDATE=1
JSON=bench-report-20260907-nullslot.json` at `source 460905d` (no
`+uncommitted`), run **`20260907T1158+0200-d70ac8d1`** — printed by the recipe
that measured, which is the only kind of id that names a measurement. Window
11:58:52–12:29:43, 162 variants (47 rows + 7 controls, each at genesis / now /
candidate), exit 0, usable. Candidate slot byte-identical to `hachi/src`, genesis
byte-identical to the frozen items, so every number below is identical code
measured against itself.

**What "certified" meant this time.** A gate of four consecutive 30 s samples
with load₁ < 1.5 and no `lean`/`lake`/`cargo`/`rustc`/`criterion` process above
5% CPU; the run wrapped in `systemd-inhibit --what=handle-lid-switch:sleep:idle
--mode=block`; a monitor sampling every 30 s throughout — 62 samples, no gap,
no `lean`/`lake` process above 5% at any of them, load₁ min 1.01 / median 1.50 /
max 2.46 with the bench binary at 100% of one core; the journal shows no suspend
and criterion's `new/estimates.json` mtimes show no gap over 2 min between
consecutive variants. It was not idle-clean: `gnome-system-monitor` sat at
7–11% of one core for six minutes (12:00–12:06, during the `commit` and
`evalsplit` binaries) and Firefox content processes peaked at 33% + 26% of one
core in one sample and 8–15% in four more (12:17–12:20, during `linalg`). None
of that overlaps a row that reads beyond noise: the `linalg` rows measured under
the Firefox spike all read noise (worst +3.5%), and every outlier below landed
at 12:12, 12:23, 12:25–12:27 or 12:29, when nothing foreign was above 5%. It is
recorded because the rule says "nothing else heavy" and a third of one core out
of sixteen was let through as not heavy.

**Why there was an attempt 1.** The first run of the day (gate passed 11:01:09,
same source) was suspended for 33 minutes — lid closed 11:12:49, `PM: suspend
exit` 11:45:59, s2idle — while the `gadget` binary's own `_control` `now` variant
was collecting samples; its `candidate` and `genesis` variants then ran on a
cold CPU against a control measured half warm. That is the one-condition-set
rule broken in the row that recenters the whole binary, so the run was killed at
82 variants. The monitor showed only a hole; the cause was in `journalctl` and in
a 2000 s gap between two consecutive criterion mtimes. GNOME's idle policy was
not it (`sleep-inactive-ac-type` = nothing); logind's lid handling was, and
logind **ignores high-level `sleep` inhibitors for lid events by default**
(`HandleLidSwitchIgnoreInhibited=yes`) — the low-level `handle-lid-switch` lock
is the one that works, and an active session may take it unprivileged. The
pre-run rule gains that line, and the after-the-fact check gains the mtime-gap
test, since `CLOCK_MONOTONIC` does not advance across a suspend and the numbers
themselves do not scream.

**Results.**

* A/B bias **4.42%**, set by `_control/ringswitch`'s candidate lean; the seven
  controls' own vs-genesis spread is within ±3.2% and the other six leans within
  ±2.3%. The threshold this run applied is `max(MIN_EFFECT, bias)` = **5%**: the
  borrowed floor was binding, by 0.6 points.
* `vs genesis`: 42 noise, **5 false verdicts** on identical code —
  `quadeval/in_sb/1024` −7.31%, `ring/one/1024` +6.17%, `ring/from_coeffs/1024`
  +5.93%, `gadget/gadget_entry/8` −5.03%, `ring/zero/1024` −5.01%.
* The accept column (`cand vs now`, recentered per binary): 45 noise, **2 false
  verdicts** — `quadeval/in_sb/1024` +8.15%, `ring/one/1024` −7.96%.
* The eleven rows new since 09-04 (`balanced_*`, `bounded_z_*`, `quadeval/*`,
  `ringswitch/rho_digits`) read noise on both columns except `in_sb`, which the
  shake-out had already flagged as unable to carry a verdict. **Target 2's
  freeze is certified faithful** on the ten rows that can carry one.

**The floor is a function of the case's absolute time, not of the case.** Two
earlier readings — "the `Vec::new()`+push constructors" (09-04 §4 audit) and
"the sub-microsecond case" (the shake-out) — were both looking at the same band
from different rows. Grouping the 47 rows by their measured time:

| band | rows | worst \|vs genesis\| | worst \|cand vs now, adj\| |
|---|---|---|---|
| < 100 ns (`digit_at`, `base_pow`, the 8-digit decomposes…) | 6 | 3.18% | 2.54% |
| 100 ns – 2 µs | 14 | **7.31%** (five rows ≥ 5%) | **8.15%** (two rows ≥ 5%; `commit/l1_norm` 4.85%, `ring/neg` 3.81%) |
| > 2 µs | 27 | 3.48% | 4.67% |

Every row that crossed 5% on identical code sits between 400 ns and 900 ns
(`in_sb` 645, `gadget_entry` 658, `ring/zero` 675, `ring/one` 713,
`ring/from_coeffs` 879), while `ring/constant` at 761 ns read +0.07% — so the band
is a susceptibility, not a sentence. Below it, per-iteration overhead dominates
and averages out; above it, the work dominates; inside it, a swing of a few tens
of nanoseconds *is* 5–8%, and criterion's "three fastest settled samples" cannot
average away something that is the same on every sample.

⊗⊗ **The mechanism stated here was wrong, corrected 2026-09-07 by the §4 audit
below.** This paragraph read the band as the 09-04 disassembly finding —
byte-identical code at a different *placement* — and for `in_sb` that is not
available as an explanation: fat LTO folds the three variants of that row into
one function at one address, so there is no placement difference to have. What
the samples show instead is a discrete two-level machine state (~430 vs ~515 ns
on that row, in runs of tens of consecutive samples) that the three-fastest
estimator resolves to whichever level a variant happened to touch three times.
The extent table stands; the cause named for it does not, and it is not the same
cause on every row in the band (`gadget_entry` keeps three distinct copies and
*can* differ by placement).

**What follows, and what does not.** (1) On this host, `MIN_EFFECT = 5%` flat is
about right for rows outside the band — their worst identical-code reading sits
at the line on `vs genesis` (5.03%, one row) and under it on the accept column
(4.85%) — and wrong inside it, where a byte-identical candidate is accepted or
rejected at 5% one time in seven. (2) A candidate verdict on a 100 ns–2 µs row is
therefore not a verdict until either the floor is per-band or the row has its
own control; that is a harness change and is not made here. (3) The bias itself
read 1.42% → 2.19% → 4.42% across three runs on the same machine, so the *usable*
limit and the `max(MIN_EFFECT, bias)` rule are doing real work; a run whose bias
crosses 5% will already raise its own threshold. (4) The `in_sb_box` /
`vec_in_sb_box` additions agreed on 09-04 were added after this run, covering
the honest all-inside workload; both scalar rows remain outside any verdict
until the timing-band problem is repaired. (5) None of this writes a ledger row — a null-slot
sweep records no candidate verdict — so Stage 0's ledger exit still closes with
the first `perf-loop`; what closed today is Stage 0's *measurement-grade bench*
item, with an id that can be cited.

## The §4 audit of target 2's rows, and the merge that hides the A/B (2026-09-07)

Target 1's birth run was audited under `rust-bench` §4 on 09-04; target 2's rows
never were, and the two `*_box` cases added today needed the same treatment. Both
debts are paid here. Twelve refute agents, three row groups (the four box rows,
the three tensor/carrier rows, the two `z`-side gadget rows) by four lenses, all
read-only and forbidden from benching, against the two null-slot reports of
today. Three lenses refuted, all three on the same pair of rows, and their
adjudicators were the three agents a session limit killed — so the adjudication
was done by hand, which is why the confirmations below are commands rather than
opinions.

**Nine lenses found nothing.** The three tensor/carrier rows time one call to the
named function plus the drop of its result, corpus and digest outside the timer,
and each lands within 0.45% of 8 × `ring/mul` (1.429 ns per multiply-accumulate)
— the containment relation holds in the direction it should. The two `z`-side
gadget rows likewise, with `gadget_mul` paying ~20% more per digit than
`gadget_mul_z` exactly as its `O(e)` `base_pow` recomputation predicts. Every
`@covers` path names the function its body calls; the frozen copies differ from
`hachi/src` only in `@genesis` stamp lines; both slots fingerprinted clean.

**Finding 1 — fat LTO merges the variants, so many rows have no A/B at all.**
Confirmed directly: `nm` on the quadeval bench binary lists
`quadeval::now::{in_sb, in_sb_box, vec_in_sb, vec_in_sb_box}` and **no**
`genesis::` or `candidate::` counterpart, while `carrier_entry`/`tensor_g`/
`tensor_g1` keep all three; the three variant call sites for `in_sb`
(`0x78514`, `0x7852b`, `0x78548`) all `call 9ab50 <quadeval::now::in_sb>`; and
the only `_control` iter in the binary is the *genesis* one. LLVM's
MergeFunctions folds any case whose inlined body no longer references a
variant-distinct symbol. The same holds in the gadget binary for
`bounded_z_gadget_decompose`, `gadget_decompose`, `balanced_gadget_decompose`,
`base_pow` and the control, but not for `gadget_entry`, `gadget_matrix`,
`gadget_mul` or `gadget_mul_z`.

Three consequences, and the third is the one that matters. (i) On a merged row a
null-slot sweep measures *zero* layout bias, because there is one address; the
paragraph above is corrected accordingly. (ii) `support/mod.rs`'s rationale for
a cross-crate control — that it is "subject to exactly the layout bias the real
cases are" — is void in the built binary whenever the three sources are
identical, which is to say in every null-slot calibration and for every control
in every run. (iii) **The certified floor is therefore a lower bound.** A real
candidate is not byte-identical, so it is not merged, so it pays a placement
term that no null-slot sweep has ever exercised. Nothing here says the 5% floor
is too tight; it says the measurement that would justify it cannot be taken with
a null slot, and a floor for real candidates has to come from a sweep whose
candidate slot holds something semantically equal but differently written.

**Finding 2 — the two single-`Rq` box rows measure a regime no caller sees.**
`in_sb`'s per-coefficient sign test (`v ≤ q/2`) compiles to a real
data-dependent branch — the box decision itself is branchless, the dispatch is
not — and it is a coin flip on both corpora by construction. The single-`Rq`
rows re-feed the same 1024 coefficients about 11 million times and read
0.437 ns/coefficient (`in_sb`) and 0.469 (`in_sb_box`); the vector rows run the
same machine code over a stream they cannot learn and read 2.536 and 2.533. That
is the whole 5.8× "containment inversion", and the two candidate explanations
were excluded arithmetically: no SIMD in either loop, and 2 MiB streaming at
8 B / 2.54 ns is 3.16 GB/s, an order of magnitude under this part's L3. What is
left is branch memorization. **That attribution is inferred, not counter-measured**
— `perf_event_paranoid` is 4 on this host, so `perf stat -e branches,branch-misses`
needs a sysctl this session did not take. The decisive numbers, if anyone wants
them: memorization predicts under 3% branch misses on `in_sb/1024` against over
10% on `vec_in_sb/256`. The *conclusion* does not depend on settling it: under
either explanation the single-`Rq` rows report a per-coefficient cost 5.8× below
what a caller pays, so a candidate that changes the branch structure would read
the wrong sign there.

So: `quadeval/in_sb/1024` and `quadeval/in_sb_box/1024` **cannot carry a
candidate verdict**, and `in_sb_box` — added this morning to fix the corpus —
fixes the corpus and not the shape. The rows that carry the verdict are
`vec_in_sb/256` and `vec_in_sb_box/256`. All four are kept, because deleting one
changes what the others' ids mean. Written into the case docs.

**Finding 3 — recentering can manufacture a verdict when the control's lean is
not the binary's.** In the shake-out, `_control/quadeval` measured a candidate
lean of **+2.24%** while the five stable rows of the same binary leaned
**−0.16%** on average. `report` divides the control's lean out of every row, so
every accept-column value in that binary moved about 2.2 points: `in_sb`'s raw
−3.52%, which is noise under any floor, became an adjusted −5.63% and printed
the verdict *faster* on a null candidate. The recentering is still right in
principle — a signed per-binary lean is real and AeneasCompPoly measured it —
but a control that is itself one 33 ms row, merged to a single address, is a
one-sample estimate of that lean and it can be noisier than what it corrects.
Not fixed here. The cheap mitigation is to read the raw `cand_vs_now` beside the
adjusted one whenever a verdict lands near the floor; the real one is more than
one control per binary, which is a harness change.

**Two documentation defects, fixed.** The `in_sb` case doc claimed the loop is
"branchless to the end" — true of the source, false of the binary, and the whole
of Finding 2 lives in that gap. The `vec_in_sb` REDUCED-width note justified 256
by an arithmetic that does not apply (it named `commit::centered_abs` in a loop,
and 8192 would cost ~21 ms per iteration, below the binary's own control rather
than above it); the scheme's real widths are `paper_rel_out`'s 8192 / 8192 /
40960. The width stays at 256 — it is what has been measured since the freeze,
and moving it is a re-freeze — but the reason recorded for it is now the true
one. Also documented: `box_coeffs` emits a zero coefficient at rate 1/16 against
`support`'s no-zeros rule, which is deliberate (a balanced digit is legitimately
zero) and harmless (nothing in `in_sb` short-circuits).

## Target 3 opened: the full ring-switch link (2026-09-07)

The target-3 brief was re-read against ArkLib `d51d8bc` before translation.
The six computational definitions are unchanged, but the concrete width is now
`RLIN_COLS + RLIN_ROWS·rhoDigitCount = 57344 + 5·8 = 57384`, `M_ZERO = 26`,
and three old convenience lemmas were deleted. The proof statements therefore
unfold `hachiLiftCom` directly and derive the digit-check tautology through
`rhoDigitsShortCheck_eq_true_iff` plus `rhoDigitsShort_of_digitBaseOk`.

The Rust surface is now complete: `QuotientRow`, `LiftedWitness`, `rhoAsRq`,
`rhoDigitAsRq`, `liftMessage`, `hachiLiftCom`, `rhoDigitsShortCheck`, and
`liftShortCheck`. The two checks live in `endpiece.rs`, per the settled API map;
target 6 will extend that module. Eleven ring-switch semantics tests pass, the
full Rust suite and strict clippy pass, extraction adds only transparent
definitions, `make build` is green, and the six exact equivalence statements
typecheck in `lean-wip/RingSwitch.lean` with their intended `sorry` debt.

Freeze policy keeps the walls separate. `lift_commit` is W1 REDUCED: 57,384
schoolbook ring products, removed by a sub-quadratic `ring::mul`. `lift_message`
is W3 REDUCED in the benchmark: copying a 448 MiB `z` creates an approximately
896 MiB peak, removed only by a fused/streaming lift. `lift_short_check` retains
the real 57,344-entry `z` scan and constructs that input outside the timed
region. The quotient-digit verdict is provably always true at `(bDig,bound) =
(16,15)`; its computation remains in the baseline so parameter drift cannot
silently delete a verifier check.

⊗⊗ **Two claims in this paragraph did not survive the row audit of the same
day — see § "The endpiece rows get a binary, and `lift_message` gets its real
shape" below.** `lift_message` is no longer W3 REDUCED: it runs at
`(RLIN_COLS, RLIN_ROWS)` with a measured 904 MiB peak, because the reduction
was not a smaller version of the row's mixture but the inverted one — the
registered `[8]` hid a second, undocumented `rho_rows = 2` inside the case
body. And "the quotient-digit verdict is provably always true" is right, but
its consequence was not drawn here: a provably constant verdict means the
benchmark's digest oracle cannot discriminate *any* candidate on that row,
including one that deletes the loop. The rest of the paragraph stands.

The genesis and candidate copies and all benchmark coverage are staged but
unstamped. The required next actions are the standard interleaving: commit the
target-3 translation/freeze, run `make bench-stamp`, commit the stamp-only
change, then run `make bench-check` and the birth benchmark.


## The endpiece rows get a binary, and `lift_message` gets its real shape (2026-09-07)

Target 3's bench coverage was re-read against what `harness.py` actually does
with each row rather than against what the rows say they measure. Three defects,
in descending order of how quietly they failed.

**1. Two rows sat in a binary that could not give them a verdict.**
`endpiece::rho_digits_short_check` and `endpiece::lift_short_check` were benched
from `benches/ringswitch.rs`, under `_control/ringswitch`. `report` attributes a
row to a bench binary by the **module prefix of its group id** (`case_binary`)
and divides that binary's own control lean out before printing any candidate
verdict, so both rows resolved to a binary named `endpiece` that had no control:
under `CANDIDATE=1` they would have read `unvalidated` and exited 2. Nothing
failed at bench time — the rows ran and printed times — so the failure was
reserved for the optimization loop's accept pass, which is the most expensive
place to find it.

Fixed by giving `endpiece` its own `[[bench]]` target and `benches/endpiece.rs`
with `_control/endpiece`, which is what `src/endpiece.rs` wants anyway (target 6
extends that module). Hardened so it cannot recur: `covered_paths` now requires
that **a bench file be one binary** — at least one `_control/<binary>` case,
every control in the file naming the same `<binary>`, and every other group id
prefixed with it. That is a `make bench-check` failure now, before any
measurement is taken, and it was negative-tested against four shapes: the exact
historical arrangement (caught, and it names the exact fix), a file with no
control (caught), a file carrying two different binaries' controls (caught), and
a file with two controls for the *same* binary (passes, deliberately — see
below).

The rule is about binaries rather than about the number of controls, and that
distinction is load-bearing. The alternative fix — a second `_control/endpiece`
row inside `ringswitch.rs` — works mechanically and was rejected: it puts a
second draw into the run's *worst*-pairwise-control usability veto for a binary
whose rows are not in that file, and it leaves `endpiece` recentered on a
control interleaved with `ringswitch`'s rows rather than its own. But two
controls for the **same** binary is a different proposal, and it is § "The §4
audit of target 2's rows"' own recommended fix for recentering manufacturing a
verdict from one unlucky control. That fix is still not made — `report`'s
`leans` dict is keyed by binary, so a second control for one binary would
silently overwrite the first rather than average with it — and the new check
deliberately permits the shape so that whoever makes it changes `report`
instead of working around a gate.

**2. `lift_message` was measured at the opposite of its real mixture.** It was
registered at `[8]` while its second dimension, the quotient-row count, was a
bare `2` inside the case body — invisible at the registration, absent from the
case id, and so a second undocumented reduction stacked on the declared one. At
the real shape the row is 57,344 `z`-copies against 40 digit extractions, ~99.96%
copy by time; at `(8, 2)` it was 8 copies against 16 extractions, about half and
half. The candidate the case's own removal condition names — a fused/streaming
lift — is a change to the *copy* half, and at `(8, 2)` the copy half was barely
present, so the row could not have shown such a candidate winning.

Now at `(RLIN_COLS, RLIN_ROWS)`, both dimensions read from `params` at file
scope next to the constant each is (or is not) a reduction of. Measured peak RSS
904 MiB, against the ~896 MiB the arithmetic predicts. `lift_commit` keeps its
W1 reduction — its composition genuinely survives it, 99.83% `mat_vec_mul` at
the reduced width against 99.70% at the real one, priced against `ring/mul` at
1.511 ms — but both of *its* dimensions are now stated at file scope too.

**3. `rho_digits_short_check` has no oracle, and no mechanical fix exists.** The
check is a tautology at the pinned parameters: balanced digits are
centered-bounded by `HALF_BASE = 8` unconditionally
(`rhoDigits_valMinAbs_natAbs_le`) against `CHAIN_GAMMA = 15`, so no
`Vec<QuotientRow>` this crate can build makes it `false`. Its digest is one bit
that is always the same bit, which means `case!`'s cross-variant equality — the
thing that normally stops a semantics change being reported as a speedup —
cannot tell the real function from `|_| true`. A candidate that deleted the
digit loop would pass the oracle and read as an enormous win.

The row is kept, because the optimization the void oracle fails to police is a
real and measurable one (fusing digit extraction into the comparison instead of
materializing 40 × 8 KiB `Rq`s), and deleting the row would lose it. What
changed is that the voidness is now stated where a reviewer looks — the module
header, the case doc, and `check()` — and carried by a compile-time
`assert!(HALF_BASE <= CHAIN_GAMMA)` in every variant's own `params`, so a
parameter move that gives the check a false branch breaks the build rather than
quietly restoring an oracle nobody re-reads. Acceptance routes through the
existing human gate: `lean-opt` § "No new value-level preconditions without a
gate" now says out loud that its digest backstop does not exist on an
oracle-void row and names this one, and `perf-loop`'s pre-flight list carries
the same warning. **This is a policy choice.** The alternative — excluding the
row under a new signed-off "oracle-void at the pinned parameters" class, as
Decision 3 did for Fig. 9 — remains available and was not taken.

`lift_short_check` is not in that position: its `z` conjunct rejects, so both
directions are pinnable and `check()` now pins them, transplanted from
`tests/ringswitch_semantics.rs` (the `quadeval.rs` precedent). Its corpus `z` is
zeros, which is load-bearing rather than lazy — an ordinary `[1, q)` draw has
`‖z‖∞ ≈ q/2`, the `&&` short-circuits, and the row would silently measure half
the function it names — so an `assert!(vec_l_infty_norm(z) <= CHAIN_GAMMA)` now
sits above the timed region.

**Riding along.** `autobins = false` (a `src/main.rs` timing probe would
otherwise become a target with `bench = true` and be handed criterion's flags,
and would give charon's `--lib` extraction a second crate root); the
`exclusions.toml` header's "`params` is the one module with no `[[bench]]`
target" (false while `endpiece` had none, and now checked rather than asserted);
`harness.py`'s `MODULES` comment, which claimed the `params` consts are excluded
by name in `exclusions.toml` when that file's own header says the opposite and
is right — they carry no `Mirrors` marker, so `coverage` never asks about them;
`support/mod.rs`'s "four bench binaries" (eight); `black_box` on `rho_as_rq`'s
receiver, the last case in the crate whose input was not opaque; `rho_as_rq` and
`rho_digits` annotated against the certified sweep's 100 ns – 2 µs band (725 ns
and 2.4 µs — one inside it, one 20% clear of it); `rho_digit_as_rq`'s
deepest-index choice argued against `rho_digits`' `u = 0`, which is the opposite
convention and deliberately so; `perf-loop`'s slot-fill list, which named eight
modules and now derives the list from `harness.py`'s `MODULES` (nine since
`endpiece`); and `rust-bench`'s floor advice, which still said `GADGET_BASE` is
`2` — it is 16, and `GADGET_DIGITS` 8 rather than 32, so any floor derived from
the old pair was off by 4x.

**The §4 audit's `nm` check, run on both binaries.** Finding 1 of that audit
made "does this row keep three variant copies, or did fat LTO merge them?" a
standard question for any new row, and it had never been asked of target 3's.
Built `--features candidate` against the null slot, reading the symbol that is
actually timed (`Bencher::iter::<_, &mut <variant>::<case>::{closure#0}>`):

* **three copies, a real A/B** — `ringswitch/rho_digit_as_rq`,
  `ringswitch/lift_message`, `ringswitch/lift_commit`;
* **merged into one function** — `ringswitch/rho_digits`,
  `ringswitch/rho_as_rq`, `endpiece/rho_digits_short_check`,
  `endpiece/lift_short_check`, and both `_control` rows.

Every row in the `endpiece` binary merges, controls included: both cases return
a `bool` through a `&`-borrowed input, so nothing variant-distinct survives
inlining. The consequence is the audit's, unchanged — a merged row has no layout
bias to measure, so a null-slot sweep of it is a lower bound and its (also
merged) control cannot correct for a term it never saw. It does not make those
rows' verdicts wrong during a real candidate pass, where the slot is not
byte-identical and therefore does not merge; it makes a floor borrowed from a
null sweep optimistic for exactly them. Recorded in both file headers with the
command to re-run.

**The numbers below are a shakeout, not a run.** Taken by invoking the bench
binaries directly on a machine that was *not* quiet (load ~2, a browser and a
music player alive); the two controls read 2.6% and 5.2% apart on identical
code, which would have failed a candidate pass. They are here to justify the two
sampling overrides and the band annotations, and nothing in this section is a
verdict:

| case | reading |
|---|---|
| `_control/ringswitch` | ~36 ms |
| `_control/endpiece` | ~37 ms |
| `ringswitch/rho_digits` | ~2.4 µs |
| `ringswitch/rho_as_rq` | ~725 ns |
| `ringswitch/rho_digit_as_rq` | ~3.4 µs |
| `ringswitch/lift_message` | ~260 ms, 904 MiB peak RSS |
| `ringswitch/lift_commit` | ~18 ms |
| `endpiece/rho_digits_short_check` | ~119 µs |
| `endpiece/lift_short_check` | ~31 ms |
| `ring/mul` (for the composition arithmetic) | ~1.511 ms |

Both new binaries carry a `commit.rs`-style `sample_size(50)` /
`measurement_time(10s)` override, and the two comments say different things
because the arithmetic differs. In `endpiece.rs` it buys *averaging*: a flat
sample of the 31 ms row is 7 iterations at this setting against 2 at the
default, and `_robust` takes the three fastest samples, so two-iteration samples
amount to picking the three luckiest executions in the run. In `ringswitch.rs`
it buys only *wall clock*: a 260 ms row fits one iteration per flat sample
either way, so the override halves `lift_message` from ~27s to ~13s per variant
(the averaging argument does apply to `lift_commit` at 18 ms, 11 iterations per
sample against 3).

`make bench-check` green (176 frozen items, slot null across nine modules,
0 unaccounted), `make test` green (111 tests), strict clippy clean on all
benches under `--all-features`, and `make extract` reports `lean/Generated.lean`
unchanged — `autobins = false` does not move the model.


## Target 3's birth run, on a machine that was actually quiet (2026-09-07)

Run `20260907T1848+0200-bf4a4457`, source `9ae732b` clean, full pass (no
`BENCH=` filter, no candidate slot), `nightly-2026-06-01` /
`rustc 1.98.0-nightly (14210df0e)`, AMD Ryzen 7 8845HS, 16 cores. Taken after
the desktop was emptied — 1-minute load `0.11` at launch against the `1.20` the
shakeout in the section above ran under, with Firefox, Spotify, VS Code (whose
`rust-analyzer` was the largest single consumer) and the system monitor all
closed. This is the first full run on this host that met the "benchmarking needs
the machine to itself" rule rather than working around it, and the difference is
visible in one number: the worst identical-code control reads **2.64%**, against
the 10–59% that `NOTES.md § "The first benchmark run…"` records and the 2.6% /
5.2% pair the shakeout printed on rows that were *supposed* to be identical.

`op-genesis` stage 7's bar is that the new op's rows read noise against the
printed threshold. They do — the threshold is the flat 5%, since the measured
A/B bias (2.64%) does not exceed it:

| row | vs genesis | significant | timed copies (`nm`) |
|---|---|---|---|
| `ringswitch/lift_commit/4` | −0.01% | no | two — a real A/B |
| `ringswitch/lift_message/57344` | +0.18% | no | two — a real A/B |
| `ringswitch/rho_digit_as_rq/5` | +1.05% | yes | two — a real A/B |
| `endpiece/lift_short_check/57344` | −0.10% | no | **merged** |
| `endpiece/rho_digits_short_check/5` | +1.60% | yes | **merged** |
| `ringswitch/rho_digits/1024` | +2.18% | yes | **merged** |
| `ringswitch/rho_as_rq/1024` | +3.40% | yes | **merged** |

Controls: `_control/endpiece` −0.61% (the new binary's own control, healthy on
its first real outing), `_control/ringswitch` −0.46%, worst of the eight
`_control/commit` +2.64%; run marked `usable`. Widest row in the whole report is
not a target-3 row at all — `ring/constant/1024` at +4.14%.

**Read the two columns together, because they say different things.** The `nm`
check was re-run on the exact binaries this run executed (the non-candidate
build: `ringswitch-f90ec929b516ae9f`, `endpiece-a8c0e834f88e58f0`), and it
reproduces the table in both bench headers, which was taken under
`--features candidate`. So four of the seven rows time *literally the same
machine code* in both variants: their deltas are not a comparison of anything
and cannot be evidence that the freeze is faithful. What they are instead is a
free measurement of this host's per-row noise floor, and it is size-dependent in
a way the report's single bias line does not show — **+3.40% on a 660 ns row and
+2.18% on a 2.1 µs row, where the 33 ms control that sets the bias number reads
2.64% and the 30 ms merged row reads 0.10%.** The flat 5% covered it here, but a
floor derived for a sub-µs row from an 8192-sized control understates that row's
noise; the certified-floor section's caveats apply to the small end of this
table, not only to the merged/fat-LTO argument it was written about.

The freeze's actual evidence is the other three rows, the ones that kept two
copies: **−0.01%, +0.18%, +1.05%.** Those are byte-identical sources compiled
into distinct functions and separately timed, and they agree to about a percent.

**The report's `(skipping 7 case(s) not measured in this run)` line is benign
and was checked rather than assumed.** A stale case is a `criterion/` directory
with no variant written after the run started, and all seven are historical
sizes from earlier sizing sessions, none of them a case any bench file registers
today: `_control/{commit,gadget,linalg,ring}/128` (the control before it moved to
8192), `ring/mul/64`, `linalg/scalar_vec_mul/8192` (the live case is `/16`), and
`smoke/sum`. Every registered case ran: 55 rows plus 8 controls.

Target 3 is therefore through `op-genesis` stage 7 and loop-eligible: naive
translation is the champion, genesis is its baseline, brief 3 exists re-based.
No ledger row — an onboarding's provenance is the `@genesis` stamp, and the
ledger records candidate verdicts. Its Lean debt (`hachi/lean-wip/RingSwitch.lean`,
6 `sorry`s) is out with Aristotle session `8d26c89e` and is not touched here.


## Target 4 opens: the zero-check's `H₀` side (2026-09-08)

Stage 3 target 4 of the protocol-layer plan. `op-genesis` stages 1–6 are done
and staged; stage 7 (the birth run) is the plan's tail, below.

### The brief's re-base, and what moved

the target-4 brief was written at `294b3f0b0` and is now at
`d51d8bc`. **Every definition the target translates is byte-identical across the
move** — checked by extracting each declaration block from both revs and
comparing, not by reading. The only change in `ZeroCheck/Constraints.lean`'s
whole diff is four *deleted* theorems (`hZeroML_eq_zero_iff`,
`hAlphaML_eq_zero_iff`, and the two `sum_sumcheckPoly*'` aliases the file itself
labelled "retained for the sumcheck bridge"); target 5's bridge must stop citing
the primed names.

What did change is the instantiation, and in a way the old brief could not have
predicted: a **new `Hachi/Params.lean`** pins the profile that brief 4 treated as
free — `hachiTau = 5` (`:90`), `mu0_eq : mu0 = 57344` (`:415`),
`liftKeyWidth_eq : 57384` (`:425`), and `sumcheckWidthAtProfile` at `M = 25` with
`sumcheckWidthAtProfile_minimal` ruling out `M = 24` (`:432`, `:439`), i.e.
`m₀ = 26`. So μ₀ / `LIFT_COLS` / `m₀` move from *derived under an inequality
ArkLib leaves open* (the brief's flag F4) to **pinned and discharged upstream**,
and every cube-sized figure halves: `2^27 → 2^26`, `wTableMleEval`
`3.76·10⁹ → 1.81·10⁹` `Ext4` mults at 4.0 GiB resident, `hZero`
`4.16·10⁹ → 2.08·10⁹`, naive `alphaPublicEvals` `8.3·10¹¹ → 4.1·10¹¹`; dense
`s.M` 3.2 → 2.2 GiB. No conclusion of the brief reverses — `hZero` is still the
largest cube term (`31·2^m₀` beats `(m₀+1)·2^m₀` while `m₀ < 30`) and the
`d = 2^10` split is still a bit-boundary split, since `d` did not move.

The citation re-base was mechanical but **verified rather than trusted**: each
`file:line` was remapped from the two revs' diff hunks and accepted only if the
old and new blobs carry *identical text* at the mapped line. 116 moved, 77 were
already right, 5 were held back. Two classes were deliberately left alone —
`CompPoly/…` and `cpoly/…` citations (that package's rev is `a09455a…` at *both*
ArkLib pins, so its lines did not move) and this repo's own `.rs`/`.md` cites.
Ambiguous bare `:N` forms were resolved by hand against the declaration they
name, after a context-inference pass was caught mis-attributing `wTable`'s body
lines to `RingSwitch/Reduction.lean`: the brief's bare-citation convention is
"the file this section is about", which is semantics, not a regex. The brief now
carries a per-file shift table so any citation it does not hold can be checked.

### Why this pass is the `H₀` side only

**A scope decision, taken by the user.** The α-side (`hAlphaEvals`, `hAlpha`,
and through them `alphaPublicEvals`, `mAlphaTilde`, `zcTargetAlpha`) is reached
through `cRowSum` (`RingSwitch/Reduction.lean:439`), `∑ⱼ (s.M i j).1 * (z j).1`
— a sum of products of the *`CPolynomial` representatives*, and the `*` there is
**not** the ring product. `Rq::mul` reduces modulo `X^1024 + 1`; this one does
not, so two degree-1023 inputs give degree 2046.

That difference is the entire content of the check, which is why the obvious
shortcut is not available: `hAlphaEvals`' third term carries `cEvalAt α Φ.φ` —
the modulus polynomial itself — as an explicit factor, so the identity says "the
row sum equals `yᵢ` plus a multiple of the modulus", i.e. it *certifies the ring
reduction was performed correctly*. Computing `cRowSum` with `Rq::mul` would
apply that reduction in advance, make the `Φ.φ·(…)` term indistinguishable from
zero, and leave a check that is vacuously satisfiable. It would compile, pass a
careless test, and prove the wrong theorem.

So the α-side needs a carrier this crate does not have (a `Vec<Fp>` polynomial
of up to 2047 coefficients with non-wrapping multiplication); cpoly's
`UnivariatePoly` is not a drop-in because its coefficients are `Ext4`, not `Fp`,
which would put an embedding in the equivalence proof that the ArkLib statement
never mentions. Brief 4's Correction 3 already recorded that **no target owns
`cEvalAt`/`cRowSum` today**. Verified while scoping: `cRowSum` is the *only*
place an unreduced product appears — `zcTargetAlpha` evaluates `(s.yvec i).1` and
`mAlphaTilde` evaluates `(s.M i u).1`, both plain `Rq` representatives, and
`cEvalAt α Φ.φ` is just `α^d + 1`. So the α-side splits cleanly and everything
except `hAlphaEvals`/`hAlpha` is carrier-free whenever it is picked up.

### The six items, and three deliberate shapes

`src/zerocheck.rs`: `range_product`, `w_table`, `c_w_table_mle`,
`w_table_mle_eval`, `h_zero`, `h_zero_is_zero` (plus a private `two_pow`, which
carries no `Mirrors` marker and is owed no bench).

* **Arities come from the data, against the crate's habit.** `m₀` is an argument
  and `μ`, `n` are read off the witness. At `M_ZERO = 26` a cube table is 2.0 GiB,
  so a `w_table` hard-wired to `params` could not be tested or benched at all.
  The precedent is inside `evalsplit.rs` (`to_matrix` reads a const,
  `lagrange_basis` reads `w.len()`), and the bonus is that the `_spec` statements
  will be the generic ArkLib ones at arbitrary `m₀`.
* **The cube point is taken as its flat index**, which is faithful rather than a
  shortcut: every consumer feeds `finFunctionFinEquiv.symm i` into a `wTable`
  whose first act is `finFunctionFinEquiv`, and the two cancel by
  `Equiv.apply_symm_apply` — the simp step of `wTable_zRow`'s own proof.
* **The `d`-factor redundancy is kept.** `w_table`'s digit branch rebuilds a
  whole `Rq` — `d = 1024` `balanced_digit_at` calls — to read one coefficient.
  That is `rhoDigits`' own shape (`CPolynomial.ofFinCoeff d`), not a translation
  artefact, and freezing an improved body would zero that gain out of the
  baseline forever (`op-genesis` § "The one rule").

### `Check.lean` § 2 was asserting a falsehood, and the file said so itself

`zerocheck.rs` is the crate's **first `Ext4` consumer**. § 2 carried a long note
explaining that `Ext4` "is no longer in `Generated.lean` at all" because "no
module of the scheme touches the extension field yet", with the condition for its
return spelled out: "`Ext4` enters with the *protocol* layer, which commits to
multilinear polynomials over the extension". That condition has now arrived, so
the note was replaced by live assertions: the four-field structure,
`from_base a = ok ⟨a,0,0,0⟩` (the `φF` every `wTable` branch goes through),
addition as four `Fp` additions, and `cpoly.field.W = params.EXT_W`.

`Ext4.mul`'s 19-multiply body is deliberately *not* transcribed, and the reason
is stated in the file: copying cpoly's proved code into a tripwire adds no claim,
while `--include 'cpoly::_'` is all-or-nothing — an axiomatized `Ext4.mul` would
take `Fp.add` (asserted) with it and would print in § 4 anyway. One shape is
recorded in prose because the cost model turns on it: the `W`-foldback lands on
`c0`, `c1`, `c2` only, `c3` being the plain `t3` sum, so `Y^4 = W` costs three
extra multiplies rather than four. § 2b gains the module, including
`MultilinearEvals = Vec Ext4` by `rfl` — so a statement about `hZero`'s table is
a statement about a vector, with nothing transported across a wrapper.

### The oracle, and the hole mutation testing found

`tests/zerocheck_semantics.rs`, 10 tests, REDUCED (`μ = 1`, `n = 0`,
`m₀ = 10`/`11`; branch tests probe single indices and materialize no table).
References written unlike the crate: the balanced digit as `Nat.digits b` on a
shifted representative, `eq̃(i, a)` as an explicit bit product, and the range
factor as a *descending* product of `(v² − j²)` against the crate's ascending
`(v−j)(v+j)` pairs.

The tests passed on the first run, which is exactly when they are worth least, so
five mutations were injected into `src/zerocheck.rs` to see which the suite could
actually catch. Four were caught — the `range_product` loop stopping one short,
the `w_table` digit split transposed, `row`/`col` swapped, and `h_zero`'s loop
starting at 1. **One was not**: `h_zero_is_zero` scanning `2^m₀ − 1` entries
instead of `2^m₀` passed everything, because the out-of-range coefficients the
test planted sat at indices 7 and 9 and never at the end of the scan. Fixed by
pinning both endpoints (cube index `0` and `2^m₀ − 1`, which at `μ = 1`, `n = 0`,
`m₀ = 10` are exactly `z₀`'s first and last coefficients); both fencepost
mutations are caught now. The general lesson, worth carrying to the next
`_semantics.rs`: a test that plants a defect in the *interior* of a scan cannot
see a fencepost error, and a `bool`-returning verifier check is where that
matters most, because its digest is one bit.

### Extraction and proofs

`make extract` clean and **deterministic** (a second run reports
`lean/Generated.lean unchanged`), **zero axioms**, and the six items arrive with
the counter-loop shapes the proofs want — `(acc1, j1)`-style state tuples,
`Result`-valued throughout, and `h_zero_is_zero`'s accumulation branchless to the
end. The one construct worth noting: `w_table_mle_eval` passes a `&Vec<Ext4>`
where cpoly's `eval` takes `&[Ext4]`, and the deref coercion extracts as the
modelled `alloc.vec.Vec.deref` rather than as an axiom. `make build` green — no
errors, no `sorry`, and § 4 still prints exactly the three Lean kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`) on every spec.

No `_spec` was written for the new items: they are proof debt, and per
`op-genesis` stage 4 unproved obligations do not go under `lean/`. Nothing was
staged under `lean-wip/` either — the specs are target 4's verification work and
belong to a `verify-campaign`, not to this onboarding.

### The bench binary, its floor, and the §4 audit

`benches/zerocheck.rs`, a tenth `[[bench]]` and the tenth `MODULES` entry, with
`_control/zerocheck` — the one-binary-per-file gate added on 09-07 accepts it,
which is the first new binary to be built under that rule rather than repaired
into it.

REDUCED at `m₀ = 14`, and unusually the size is bounded **below**: the cube must
cover the table, `(μ + n·δρ)·d ≤ 2^m₀`, and `d = 1024` is pinned, so at the
smallest witness with a quotient block at all (`μ = 1`, `n = 1`) the table is
`9·1024 = 9216`, `2^13` is too small, and `m₀ = 14` is the *least legal* value —
brief 4's Correction 6(a). A row at a smaller `m₀` would not be a smaller version
of this computation but an illegal one. Both dimensions of every two-dimensional
case sit at file scope, beside the constant each is a reduction of.

`w_table` gets **two** rows rather than one, because its branches differ by a
factor of `d`: `w_table_z_row` is a coefficient read, `w_table_rho_row` builds
`RING_DEGREE` balanced digits. A single row would report whichever branch it
happened to index and call it the entry cost. The digit row is taken at the
deepest digit index for `ringswitch.rs`'s reason: every real consumer walks the
whole block, so the worst entry of a loop run to completion is representative.

`zerocheck/range_product` sits at ~1.2 µs, **inside the 100 ns – 2 µs band** the
certified sweep found false verdicts in, so it carries no candidate verdict on
its own; that is tolerable here rather than a gap, because `h_zero` applies the
same arithmetic `2^m₀` times at ~40 ms and is the vector-shaped reading of it —
the `vec_in_sb`/`in_sb` relationship.

The §4 `nm` audit was run *before* any number is believed, on this binary built
`--features candidate` against the null slot. Note the symbol shape: these case
bodies are large enough that the `Bencher::iter` closure inlines into them, so
the thing to grep is `zerocheck::<variant>::<case>`, not the closure the older
headers name. **Three real copies**: `range_product`, `w_table_rho_row`,
`w_table_mle_eval`. **Merged into one**: `_control/zerocheck`, `w_table_z_row`,
`c_w_table_mle`, `h_zero`, and `h_zero_is_zero` (fully inlined — no symbol at
all). Consequence as in the 09-07 audit: a merged row has no layout bias to
measure, so a floor borrowed from a null sweep is optimistic for exactly those,
while a real candidate is not byte-identical and so does not merge.

### Gate state, and the plan's tail

`coverage --strict` moved by exactly the six new markers — **92 mirrored items,
53 benched, 39 excluded, 0 unaccounted** (from 86/47/39) — and `cargo test`
is green at **121 tests**, strict clippy clean on the crate, the tests and all
benches under `--all-features`. `cargo bench --bench zerocheck -- --test` runs
every case in both variants, so `check()` and `case!`'s digest equality both
pass.

Two gates fail, and both are the documented "resolves at commit 1" pair:
`check-genesis` on six unstamped items, and `check-candidate` because the slot's
`lib.rs` differs from its git-pinned content — which a *new module* necessarily
changes, since the slot needs `pub mod zerocheck;`. Neither can be fixed before
the commit exists.

Required next actions, in this order (`op-genesis` § "The commit choreography"):

1. *(user)* **commit 1** — everything staged, in one commit: `src/zerocheck.rs`,
   `src/lib.rs`, the semantics test, `Cargo.toml`'s `[[test]]` + `[[bench]]`,
   `benches/zerocheck.rs`, `harness.py`'s `MODULES`, both slots' `lib.rs`, the
   **unstamped** genesis copy, the candidate slot copy, `lean/Generated.lean`,
   `lean/Check.lean`, the re-based brief, the brief index, and this section.
2. `make bench-stamp` — derives `// @genesis <sha> <date>` from commit 1; stage.
3. *(user)* **commit 2** — the stamp lines alone. Never `--amend` commit 1: the
   stamp stores its sha, and an amend orphans every annotation.
4. `make bench-check` green.
5. Stage 7, the **birth run**: `make run-bench` on a quiet machine. The new rows
   must read noise against the printed threshold; the three-copy rows above are
   the ones whose agreement is evidence that the freeze is faithful, and the
   merged five cannot be (they time the same machine code twice).


## Target 4's birth run was contended, and the re-run split the anomalies (2026-09-08)

Run **`20260908T0901+0200-b33e9d1d`** (source `abdcd7e` clean, full pass) is
**discarded, not recorded**: an Aristotle result was integrated at `09:02:02`
local, one minute after the run started at `09:01`, and
`aristotle_check.py`'s integration path verifies the returned file with
`lake env lean` before incorporating it. The precedent for discarding is the
repo's own — NOTES.md § "The 5% accept floor is borrowed" discarded a smoke run
for the same reason.

⊗⊗ **The mechanism is not pinned, and the obvious candidate does not fit.**
Re-running that verification by hand takes **4.8 s** on a warm olean cache, so
the check itself cannot account for anomalies in binaries that ran 10–25 minutes
later (`gadget` ~09:08, `zerocheck` ~09:25). What *is* established is that the
run was contended by something transient: two rows that read −12.41% and −8.02%
came back −0.37% and −0.31% on the clean re-run, on byte-identical code. The
best remaining candidate is the **editor's Lean language server**, which the
09:02 write to `RingSwitch.lean` would have woken into a background rebuild
lasting minutes, and which leaves no trace a later `ps` can find. So the
mitigation is wider than "do not run an Aristotle check during a bench window":
a bench window needs the *editor* off the repo too, because a file write is
enough to start a build nobody typed.

The load check before launching (0.18) could not have caught this: the competing
work *started after* the run did. What prevents it is serialization between the
bench window and any Lean build — including an Aristotle **check**, which is a
Lean build in disguise. Worth stating because it is the second time the
"benchmarking needs the machine to itself" rule was broken by a *proof* task
rather than by a build of this crate.

**The controls did not notice.** Worst identical-code control was 1.42% in the
contended run and 1.42% again in the clean one. Their body is
`PolyVec::zeros(8192)`, which is allocation-bound and barely feels a CPU-bound
competitor, so the harness's own self-test certified a contended run. The printed
`A/B bias` line is not the safety net it looks like for compute-bound rows.

A filtered clean re-run (**`20260908T0932+0200-b8905313`**,
`BENCH='zerocheck|gadget|_control'`) splits the eight flagged rows in two:

| row | contended | clean | reading |
|---|---|---|---|
| `gadget/digit_decompose/8` | −12.41% | **−0.37%** | contention, gone |
| `zerocheck/h_zero/14` | −8.02% | **−0.31%** | contention, gone |
| `gadget/gadget_entry/8` | +5.68% | +4.32% | band row, no verdict either way |
| `zerocheck/c_w_table_mle/14` | −4.13% | −1.97% | same sign, shrinks, inside threshold |
| `zerocheck/h_zero_is_zero/14` | −2.30% | −1.92% | ditto |
| `zerocheck/w_table_mle_eval/14` | −2.99% | −3.75% | ditto, and the largest of the three |
| **`zerocheck/w_table_rho_row/1`** | −8.51% | **−5.13%** | **reproduces, still flagged** |
| **`gadget/balanced_digit_decompose/8`** | +74.98% | **+92.25%** | **reproduces, and worse** |

So target 4's cube rows are clean once the machine is quiet, and two rows are
genuinely unexplained. Both are owed work before any verdict on them is
believed.

### The 92% row is an inlining asymmetry, not a regression

`gadget/balanced_digit_decompose` is target 1's row and was untouched today.
Its absolute times say where the change is: **genesis is stable** (29.50 ns
yesterday, 31.55 and 28.60 ns today) while **`now` moved from 29.28 ns yesterday
to ~55 ns in both of today's runs**. The only change to `hachi/src` today was
gaining a *new module* — `gadget.rs` itself was not edited.

The symbol table names the mechanism. In the gadget bench binary,
`hachi_genesis::gadget::balanced_digit_decompose` exists as an out-of-line
function; **`hachi::gadget::balanced_digit_decompose` has no symbol at all**, so
in the `now` crate it was inlined into the criterion closure. The two crates
compile identical source with different inlining decisions, and today's module
addition flipped `hachi`'s copy across that boundary.

**This is therefore a harness artefact and not a regression in the shipped
library**: being inlined into a `Bencher::iter` closure is a context no real
consumer of `hachi::gadget` provides. An earlier note in this session's log
called it a shipped regression; that was wrong, and the correction changes who
owns it — the bench methodology, not `gadget.rs`.

What is *not* established is why the inlined form is 1.9× slower; that needs the
closure disassembled, which is the next step on this item. It is a third
distinct LTO failure mode beside the §4 audit's two: not "merged, so no A/B" and
not "placement bias", but **"inlined asymmetrically, so the row measures the
inliner's decision rather than the code"**. Its consequence is sharper than the
others, because target 1's own headroom is ~1.25× (brief 1) — smaller than this
artefact, so the row cannot referee its own optimization until this is settled.

### `w_table_rho_row` is the one target-4 row still owed an explanation

−8.51% contended, −5.13% clean, so it reproduces at just over the 5% threshold.
The `nm` audit of the binary the run used shows *no* symbol for either variant,
i.e. both sides are fully inlined into their closures, so this is a placement
difference between two inlined copies rather than the asymmetry above. At 2.5 µs
it is well clear of the 100 ns – 2 µs no-verdict band, so the band does not
excuse it. Until it is explained, the row reports a number but carries no
verdict.

### Also corrected: the §4 `nm` table in `benches/zerocheck.rs` is for the wrong binary

It was taken under `--features candidate`, the audit convention, and the merge
pattern there is **not** the one the birth run measured. Candidate build:
`h_zero` merges to one copy, `w_table_rho_row` keeps three. The 2-variant build
the birth run used: `h_zero` keeps two distinct copies, `w_table_rho_row` has no
symbol at all. Both tables are true of their own binary; the header must say
which, and a birth run must be read against the 2-variant one. The same caveat
applies to the tables in `benches/ringswitch.rs` and `benches/endpiece.rs`,
which were taken the same way.

### Owed, at the next quiet window

1. Re-take target 4's birth run (it will cover both target-4 passes at once if
   the α-side lands first, which is cheaper than two runs).
2. Disassemble `balanced_digit_decompose`'s two forms and explain the 1.9×.
3. Explain or exclude `zerocheck/w_table_rho_row`.
4. Annotate the three bench headers' `nm` tables with the build they describe.


## The flat index the specification does not have (2026-09-08)

Aristotle's proof of the ring-switch link came back with two of its six
statements *changed*: `rho_digits_short_check_spec` and `lift_short_check_spec`
had gained a hypothesis `hmax : n * 8 ≤ Usize.max`, with the original statements
left commented out above them and the reason given — the check forms the flat
digit index `i * GADGET_DIGITS + u` as a **checked `usize` product** over an `i`
bounded only by `rho.len()`, so at large `n` the extracted function *fails*
instead of returning a boolean, and a triple asserting success is false as
stated. The analysis is correct. The conclusion drawn from it was not.

**The specification has no flat index in that definition.**
`rhoDigitsShortCheck` (`EndPiece/Reduction.lean:111-113`) is

```lean
decide (∀ i, ∀ u < rhoDigitCount q bDig, ∀ k < Φ.φ.natDegree,
    ((rhoDigits Φ bDig (ρ i) u).coeff k).valMinAbs.natAbs ≤ bound)
```

— three nested quantifiers applying `rhoDigits` to `ρ i` **directly**. No
`rhoDigitAsRq`, no `finProdFinEquiv`, no `j`. Our translation invented the flat
index, handed it to `rho_digit_as_rq`, and that function split it straight back
into `(j / δ, j % δ)`. A round trip absent from the specification, and the sole
source of the fallibility.

So the hypothesis was not a fact about the specification being translated; it was
a fact about a translation defect. Fixed at the source instead of assumed away:
`ringswitch::rho_digits_at(rho, i, u)` (new, `= rho_digits(&rho[i].0, u)`, which
is the spec's own `rhoDigits Φ bDig (ρ i) u`), and
`endpiece::rho_digits_short_check` now addresses digits by the pair. **The
extracted model of that check contains no multiplication at all** — verified on
`Generated.lean`, and its three nested loops are now literally the
specification's three quantifiers. `rho_digit_as_rq` is unchanged and keeps the
flat form, because *its* specification (`rhoDigitAsRq`,
`RingSwitch/Reduction.lean:256`) genuinely takes a flat index.

**Where the artefact is real, it stays.** `lift_message_spec` keeps
`n * 8 ≤ Usize.max`, correctly: there ArkLib itself forms `μ + n · δ` and
indexes it flat (`Fin.append w.z (rhoDigitAsRq …)`), so the product is in the
definition being translated rather than in the translation. Aristotle's note
justified the added hypothesis by pointing at that sibling; the sibling is the
one case where it belongs.

Two consequences worth recording rather than discovering later:

* **`op-genesis`'s "trivial translation of the spec" rule was violated, and the
  freeze preserved the violation.** The frozen genesis body still has the flat
  index, and a number has been published against the row (target 3's birth run),
  so the re-freeze carve-out is closed and this lands as a champion change.
  Consequence: `endpiece/rho_digits_short_check`'s `vs genesis` column now
  contains a **faithfulness repair, not an optimization** — the champion removes
  a multiplication and a function call per digit that the specification never
  asked for. A ledger row citing that column must say so, or the loop will bank
  a translation fix as a speedup. (The direction is at least the honest one:
  genesis is *pessimistic* here, so nothing already recorded was overstated.)
* **The oracle could not have caught it.** `case!`'s digest compares the
  returned `bool`, and the flat-index version returns the same `bool`; the
  semantics tests compared against an independent reference of the same
  *function*, not of the specification's *shape*. What caught it was a proof
  obligation — the remote prover could not prove the statement as given and said
  why. That is the equivalence layer paying for itself: a defect invisible to
  every test and every benchmark in the repository surfaced as a hypothesis
  someone had to justify.

The two new tests (`rho_digits_at_is_the_balanced_digit_of_that_row`,
`rho_digits_at_agrees_with_the_flat_index`) pin the pair form against an
independent balanced-digit reference and against the flat index it replaces;
both were mutation-tested (row index off by one, digit index off by one — each
caught by both tests). 123 tests green, strict clippy clean.


## Target 4's α side, carrier-free (2026-09-08)

The second `op-genesis` pass on target 4, scoped by the user this morning: the
part of the α side that needs no new carrier. Eight items, staged unstamped.

`ringswitch.rs` (its ArkLib home is `RingSwitch/{Rlin,Reduction}.lean`):
`RlinStatement` with its three accessors, a private `ext_pow`, `c_eval_at`,
`c_eval_at_modulus`. `zerocheck.rs`: `alpha_tilde`, `eq_weight`,
`m_alpha_tilde`, `alpha_public_evals`, `zc_target_alpha`.

`hAlphaEvals`/`hAlpha` remain out, for the reason § "The flat index the
specification does not have" neighbours: they are reached through `cRowSum`,
whose product of two `CPolynomial` representatives is **not** reduced modulo
`X^d + 1`, so it needs a 2047-coefficient `Fp` carrier this crate does not have
and `Rq` cannot stand in for. Confirmed while scoping that `cRowSum` is the
*only* such product in the target: `zcTargetAlpha` evaluates `(s.yvec i).1`,
`mAlphaTilde` evaluates `(s.M i u).1`, both plain `Rq` representatives, and
`cEvalAt φF α Φ.φ` is the modulus, handled below. So the split is clean.

### `eval₂` is the power sum, not Horner — which decides the whole shape

`cEvalAt φF a p = p.eval₂ φF a`, and `eval₂` is
`p.val.zipIdx.foldl (fun acc ⟨a, i⟩ => acc + f a * x ^ i) 0`
(`CompPoly/Univariate/Basic.lean:251`) — the naive sum, with `x ^ i` recomputed
per term. CompPoly *does* offer Horner, as `eval₂Horner` on the next line, and
this definition does not use it. So the faithful translation is the power sum
with a recomputed power, and writing Horner instead would have been the classic
freeze-an-optimization mistake — invisible afterwards, because Horner's `d`
multiplies against the sum's `~d²/2` would have made the baseline ~500× faster
than the specification's shape and permanently zeroed the largest optimization
on this operation. `hachi/src` now has three deliberate naiveties of that
family, each with the same justification as `gadget::base_pow`'s: `ext_pow`
recomputes `αⁱ` per term inside `c_eval_at`, `alpha_tilde` is the same power
loop at the specification's own `alphaTilde`, and `c_eval_at_modulus` walks all
`d + 1` coefficients of `X^d + 1` rather than collapsing to `α^d + 1`
(ten squarings at `d = 1024`, a ~50 000× cut, and the single largest win the
α side offers — priced by its own bench row rather than spent in advance).

`c_eval_at_modulus` is a separate entry point rather than `c_eval_at` applied to
the modulus, and not by preference: `Φ.φ = X^d + 1` has `d + 1` coefficients and
an `Rq`'s invariant is exactly `d` of them, so no `Rq` can hold it.

### A freeze constraint nobody had hit: an appended item may not need a new import

Both new blocks first went into genesis and **failed to compile there**:
`hachi/src/ringswitch.rs` had gained `use cpoly::{Ext4, Fp}` and
`hachi/src/zerocheck.rs` a `use crate::gadget`, while the frozen copies carry the
import lines they were frozen with — and `benches/genesis/src/lib.rs` says
"Nothing here is ever edited. Not to fix a lint, not to fix a typo, not to
follow a rename in `hachi`", plus "Append only". An import line is not
appendable.

Editing the frozen imports would have been the easy wrong answer. Instead the
*source* was changed so the appended text needs nothing new: `cpoly::Ext4`,
`crate::gadget::base_pow` and `crate::ringswitch::{c_eval_at, …}` are written
fully qualified inside the new items. The frozen text is then byte-identical to
`hachi/src` with no import edit anywhere, which is what `check-genesis`
verifies. Verified afterwards that the fully-qualified form does not move the
model: `make extract` is deterministic and the diff against the previous state
is purely additive (+408 lines, no deletions).

**The general rule, which `op-genesis` § "A new module, not just a new item"
should carry: a new item appended to an already-frozen module must be written in
terms of what that module already imports, or fully qualify.** It is the second
constraint the append-only baseline puts on the *translation* rather than on the
copy, after "the body must be the specification's shape".

### The oracle: 11 new tests, and what each one is for

`ringswitch_semantics.rs` (+3, now 16): `c_eval_at` against **Horner** — a
different algorithm from the power sum, so a mistake in either side shows as a
mismatch instead of being reproduced; additivity `(p + r)(α) = p(α) + r(α)`,
which no single-input comparison gives; and `c_eval_at_modulus` against
`α^d + 1` by repeated squaring. That last one is the identity the largest
optimization rests on, pinned *before* anyone attempts it.

`zerocheck_semantics.rs` (+8, now 18): `alpha_tilde` against squaring;
`eq_weight` summing to one over the whole `m₁`-cube (a property of the family,
which a consistently wrong product cannot satisfy) and equalling the indicator
at Boolean `τ₁` (which pins the **bit order** — the thing a `finFunctionFinEquiv`
mix-up transposes silently); `m_alpha_tilde`'s three cases each against an
independent computation, including that row `i` does **not** see row `j`'s digit
columns; `alpha_public_evals`'s factorization and its vanishing on the padding;
and `zc_target_alpha` both in general and at `τ₁ = e_k`, where it must equal
`y_k(α)` exactly — a sharper claim than re-summing the same products, and one
that pins the weight family and the evaluation together.

Mutation-tested, four injected defects, all caught: the sign dropped from
`−φ(α)·bᵉ`, `idx / d` swapped with `idx % d`, `eq_weight`'s bit order reversed,
and `m_alpha_tilde`'s row-match condition `(u − μ)/δ = i` deleted. 134 tests
green, strict clippy clean on crate, tests and benches under `--all-features`.

### Extraction, and the bench rows

`make extract` deterministic, **zero axioms**, `RlinStatement` arriving as a
named-fields structure with plain projections, and every new loop carrying the
`(accumulator, counter)` state tuple the proofs want — including `eq_weight`'s
bit test as plain `Usize` `/` and `%`. `Check.lean` § 2b gained the eight items
plus the three shape facts the proofs will lean on. `make build` green: no
errors, no `sorry`, three kernel axioms.

Seven new rows. `ringswitch/c_eval_at` and `ringswitch/c_eval_at_modulus` at the
**real** `d = 1024`, registered separately because their removal conditions
differ (a running product versus the `α^d + 1` collapse).
`zerocheck/alpha_tilde` at `ℓ = d − 1`, the worst entry of a loop every consumer
runs to completion. `zerocheck/m_alpha_tilde_matrix` and `.../m_alpha_tilde_digit`
— two rows for one item, as `w_table` has, because the branches reach different
helpers. `zerocheck/alpha_public_evals`. And `zerocheck/zc_target_alpha` at the
**real** `n = 5` and `m₁ = 3`, the one α-side row that is not REDUCED, because it
touches neither the cube nor `s.M`.

**A second wall, and it is not `m₀`'s.** Everything reading `s.M` is REDUCED
because at the real `(n, μ) = (5, 57 344)` the matrix alone is `286 720` `Rq` =
**2.2 GiB** — brief 4's Correction 2, and as independent of `ring::mul` as the
cube is. The exclusion and case notes name `s.M` rather than `m₀`, deliberately.

Two exclusions: `ringswitch::RlinStatement` (a type declaration; its three
accessors are single-field reads carrying no `Mirrors` marker) and
`zerocheck::eq_weight` (three `Ext4` multiplies at `m₁ = 3`, no loop over data,
inside the no-verdict timing band, and measured at scale through both callers —
the `commit::centered_abs` precedent).

`coverage --strict` moved by exactly the eight new markers: **101 mirrored, 59
benched, 42 excluded, 0 unaccounted** (from 93/53/40). Slot null across ten
modules. `cargo bench --bench zerocheck -- --test` and the same for `ringswitch`
run every case in both variants, so `check()` and `case!`'s digest equality both
pass. `check-genesis` fails on the twelve unstamped items, which is the
documented "resolves at commit 1" state.

### Required next actions

1. *(user)* **commit 1** — everything staged in one commit.
2. `make bench-stamp`, then *(user)* **commit 2** — stamp lines alone, never
   `--amend`.
3. `make bench-check` green.
4. **The birth run, on a quiet machine**, which now covers both target-4 passes
   *and* re-takes the run the concurrent Lean build spoiled — one run instead of
   three. The `rust-bench` §4 `nm` audit must be re-run on the 2-variant build
   this time, and the three bench headers' merge tables annotated with which
   build they describe (§ "Target 4's birth run was contended" item 4).
5. Still owed from this morning and unaffected by this pass: the
   `gadget/balanced_digit_decompose` inlining asymmetry, and
   `zerocheck/w_table_rho_row`'s reproducible −5.13%.


## The two flagged rows, diagnosed — and they are not the same defect (2026-09-08)

Static analysis only (`objdump`/`nm`), no timing, so this was done on a busy
machine. It supersedes the inlining hypothesis in § "The two flagged rows,
diagnosed" above: that guess was wrong, and the truth is worse in one case and
milder in the other.

### `gadget/balanced_digit_decompose` (+74.98%, +92.25%): both variants run *the same function*

In the gadget bench binary there is exactly one `Bencher::iter` instantiation
for this case, named `&mut gadget::now::balanced_digit_decompose::{closure#0}`,
and **both** `gadget::now::balanced_digit_decompose` and
`gadget::genesis::balanced_digit_decompose` call it — 142 instructions each,
identical call sets. That instantiation in turn calls
`hachi_genesis::gadget::balanced_digit_decompose`. So LLVM merged the two
identical library copies, kept the genesis one, merged the two closures on top,
and both timed regions now execute **the same machine code at the same
address**.

A row whose two sides are the same code cannot differ by 92% for any reason
having to do with code. It is a *measurement* difference, and the only thing
that distinguishes the two readings is when each ran: `case!` times `now` first,
then `genesis`. On a 28 ns body that allocates (three `free`s, eight
`Vec::push`/`grow_one` calls in the out-of-line form), 27 ns is ~80 cycles —
one different malloc path or one extra cache miss per iteration covers it.

**The consequence is about the harness, not about `gadget.rs`.** This row is, in
effect, a second `_control` — identical code timed twice — and it read **92%**
in the same run where the official control read **1.42%**. The control's body is
`PolyVec::zeros(8192)`: one large allocation, 33 ms, insensitive to exactly the
effects a 28 ns eight-push body is dominated by. So the printed `A/B bias` is
not an upper bound on measurement error for small allocation-heavy rows, and no
amount of machine quiet fixes it — the clean re-run made it *worse* (+92% vs
+75%).

Not explained, and left open: why `gadget/digit_decompose` has the identical
structure (same merge, same shape, `now` timed first) and reads −0.37%. Two rows
this similar diverging this much is itself information, and the next step needs
timing, not disassembly.

### `zerocheck/w_table_rho_row` (−8.51%, −5.13%): a genuine A/B, and a real placement difference

The opposite finding. Here the two case bodies are 160 instructions each but
call **different** functions — `now` calls `hachi::zerocheck::w_table`, `genesis`
calls `hachi_genesis::zerocheck::w_table`. Nothing merged, so this row really is
two separately compiled copies of identical source, and −5% is the *placement
bias* the §4 audit predicted for exactly that case (NOTES.md § "The §4 audit of
target 2's rows", finding 1: "a real candidate is not byte-identical, so it is
not merged and pays a placement term no null-slot sweep exercises").

So the row is behaving correctly and the **threshold** is what is wrong: a 5%
flat floor cannot separate placement bias from a real 5% win on a genuine A/B
row. −5.13% is a *false verdict* produced by a correct measurement.

### What this means for the birth run, and what it would take to fix

The birth-run criterion — "the new rows read noise against the printed
threshold" — currently rests on a threshold derived from one 33 ms
allocation-bound control per binary. Both diagnoses say that is too weak:

* a merged row's noise can be **92%** at the ns scale while the control says
  1.42%, so "reads noise" carries little information there;
* an unmerged row pays a placement term of ~5%, so a row landing at 5% cannot be
  told from a genuine improvement.

Three fixes, in increasing order of cost, none yet made:

1. **Record both rows as verdict-incapable, with the reason** — cheap, honest,
   and it only stops the loop believing them. Extends the existing list in
   NOTES.md § "Rows that cannot carry a verdict".
2. **Controls that resemble the rows.** The §4 audit already recommended more
   than one control per binary and nobody made it; this adds the shape argument
   — a control should match the row's *scale and allocation profile*, so a ns
   scale eight-push control belongs beside the 8192-element one. Blocked on the
   same `report` change the audit named: its `leans` dict is keyed by binary and
   would overwrite rather than average.
3. **A per-band or per-row threshold** instead of the flat 5% `MIN_EFFECT`,
   which the certified sweep's band finding already pointed at and this
   sharpens: the band is not only about *time* but about allocation profile.

Until at least (1) is done, a birth run can establish that target 4's cases
compile, digest and scale — which is what `op-genesis` stage 7 says a run on a
noisy host establishes — but not that a freeze is faithful to within a few
percent.


## The computable route around `cRowSum` (2026-09-08)

Target 4's α side was blocked on `hAlphaEvals` being `noncomputable` and on
`cRowSum` needing a 2047-coefficient `Fp` carrier this crate does not have (see
§ "Target 4's α side, carrier-free" for why `Rq` cannot stand in: `Rq::mul`
reduces modulo `X^d + 1`, and the `φ·ρ` term that reduction deletes is the
entire content of the ring-switch claim). The user pointed out the way round it,
and it is ArkLib's own.

**`alphaDefect` is computable, and ArkLib proves it equals `hAlphaEvals`.**
`alphaContract` (`ZeroCheck/Constraints.lean:540`) is a plain `def`:

```
∑ u : Fin (μ + n·δ), ∑ ℓ : Fin d,
  mAlphaTilde Φ φF b s α i u * T (wTablePoint Φ m₀ b hμn u ℓ) * alphaTilde α ℓ
```

`alphaDefect` (`:549`) is that minus `cEvalAt φF α (s.yvec i).1`, and
`hAlphaEvals_eq_alphaDefect` (`:771`) proves `hAlphaEvals = alphaDefect` at
`T = wTable`, under `1 < b`, `0 < d` and the coverage bound `hμn` — the last of
which is now ArkLib's own pinned `sumcheckWidthAtProfile`. So:

* **no carrier**: `cRowSum` occurs only in the noncomputable form and is now
  needed by nothing in target 4;
* **no weakening**: the headline `_spec` can still be stated against
  `hAlphaEvals`, the Eq. (22) object the protocol reasons about, and discharged
  by rewriting with ArkLib's theorem. The equivalence is supplied, not assumed;
* **no rule bent**: what is translated is an ArkLib definition, so
  `op-genesis`'s "the frozen body is the spec's trivial translation" still holds.

Every ingredient was already translated — `m_alpha_tilde`, `w_table`,
`alpha_tilde`, `c_eval_at` — and `wTablePoint` (`:525`) is the flat index
`d·u + ℓ` carrying a proof it lands in the cube: the proof erases and the
arithmetic that remains is exactly the argument `w_table` already takes.

**Convention check on the H₀ side, at the user's request.** `Constraints.lean`
has exactly four `noncomputable def`s, and they are two different things:
`hZeroML` (`:255`) and `hAlphaML` (`:261`) are the *Mathlib views* (`MLE` inside
`MvPolynomial.restrictDegree`, "used only in algebraic proofs"), while
`hAlphaEvals` (`:176`) and `hAlpha` (`:213`) are the α table itself. All nine
previously translated items resolve to computable sources — `hZero` (`:204`) is
a plain `def`, as are `wTable`, `rangeProduct`, `cWTableMle` and
`wTableMleEval` — so H₀ was already on the computable side, and no change was
needed there. With `alphaDefect` the two sides are now structurally parallel:
both translate the computable Boolean-evaluation object and neither touches the
`…ML` view. Incidental confirmation that this is the right side: the two bridges
*to* the ML views, `hZeroML_eq_zero_iff` and `hAlphaML_eq_zero_iff`, are among
the four theorems **deleted** at the current pin.

### Five items, and the test that validates all of them at once

`alpha_contract`, `alpha_defect`, `h_alpha_evals`, `h_alpha`,
`h_alpha_is_zero`. `M̃_α(i, u)` is recomputed inside the `ℓ` loop because that is
where the specification's nested sum puts it; hoisting it is the brief's largest
identified win on this operation and a baseline that had already hoisted it
would report that win as zero forever.

The oracle is the **ring-switching identity itself**:
`alpha_defect_vanishes_exactly_on_an_honest_lift` builds a witness for which
`Mᵢ·z = yᵢ + φ·ρᵢ` holds by construction — multiplying *without* reducing,
dividing by `X^d + 1`, handing the quotient to the witness and the remainder to
the statement — and asserts the defect is zero, then that corrupting one
coefficient of `y` makes it nonzero. That one test exercises `alpha_contract`'s
double sum, `m_alpha_tilde`'s three cases *and its sign*, `w_table`'s two-level
layout, `alpha_tilde`'s powers, `c_eval_at` on `yvec`, and the digit
reconstruction `Σ_e bᵉρ_e = ρ`, against the mathematics rather than against a
restatement of the code. Note where the unreduced 2047-coefficient carrier
ended up: in the test, and nowhere in the crate.

It costs 228 s in release, so it and the double-sum test are `#[ignore]`d — and
both were **run green before the freeze**, which is what `op-genesis` requires
of the birth oracle. `h_alpha_pads_above_the_real_rows` is the live half.

### All five rows are excluded, with a precise removal condition

`alpha_contract` is infeasible *even REDUCED*: at the smallest witness with a
digit block (`μ = 1`, `n = 1`) the double sum makes `8 · 1024 = 8192` calls to
the `O(d²)` `c_eval_at_modulus`, ~172 s per criterion iteration. Excluded under
the Fig. 9 policy exception, and the removal condition is exact — hoist `M̃_α`
out of the inner loop, **or** collapse `cEvalAt α Φ.φ` to `α^d + 1` (ten
squarings). Either alone brings the rows within criterion's reach, and both are
`perf-loop` candidates rather than translation choices.

`coverage --strict` moved by exactly the five new markers: **106 mirrored, 59
benched, 47 excluded, 0 unaccounted**. 135 live tests plus the two `#[ignore]`d,
strict clippy clean, extraction deterministic and axiom-free, `Check.lean` § 2b
extended, `make build` green over 3844 jobs — which now re-checks target 3's
promoted `lean/RingSwitch.lean` against the regenerated model as well.

### Required next actions

1. *(user)* commit 1, then `make bench-stamp`, then commit 2 (stamps alone).
2. `make bench-check` green.
3. **Target 4's spec layer**, which is now the whole of its remaining debt: 19
   triples (the six H₀ items, the eight α-side items, these five) on top of
   `lean-wip/Ext.lean`'s 8 ported obligations — one Aristotle batch. `Ext.lean`
   is deliberately *not* submitted alone: those 8 are pure ports and belong with
   the new work.
4. The birth run, at the next quiet window, reading against the threshold
   caveats in § "The two flagged rows, diagnosed".


## Target 6 opened: the end piece (2026-09-08)

The brief (the target-6 brief, written at `294b3f0b0`) was re-read
against ArkLib `d51d8bc` before translation. The three definitions are
byte-identical across the move: `endPieceCheck` (`EndPiece/Reduction.lean:143`),
`endPieceProver` (`:241`), `endPieceWitness` (`:172`), plus `WEvalStatement`
(`Sumcheck/FinalEval.lean:72`). What moved is the sizing, exactly as
the brief index predicted: `LIFT_COLS` 81 960 → 57 384, `m₀` 27 → 26, so
conjunct C's table is `2^26` `Ext4` (2.0 GiB), not `2^27`. The dependency
claim held: the end piece needs target 3's `lift_short_check` and target 4's
`w_table_mle_eval`, both in the tree (target 4 staged, unstamped), and nothing
from target 5 — the `{5 ∥ 6}` edge is real and this target ran on it.

### Four items in `src/endpiece.rs`, one parameter read off the data

`WEvalStatement { t: PolyVec, point: Vec<Ext4>, value: Ext4 }`,
`end_piece_check(d_key, stmt, w)`, `end_piece_prove(w) = w`,
`end_piece_witness(_stmt, message) = message`. `end_piece_check` is the
specification's `A && B && C` in its order with its short-circuit: `A` is
`lift_commit(d_key, w).equals(stmt.t())`, `B` is `lift_short_check(w)`, `C` is
`w_table_mle_eval(w, m0, stmt.point()) == stmt.value()`. `m₀` is
`stmt.point().len()` — `stmt.point : Fin m₀ → F`, so the vector's length *is*
the arity, the same "arities come from the data" reading `zerocheck.rs` argues
for. `K`, `bound`, `bDig`, `b`, `φF` are the chain's fixed values
(`Correctness.lean:254` at `ofPinnedDigitBase 16`): `d_key` an argument,
`CHAIN_GAMMA = 15`, `B_ZERO = GADGET_BASE = 16`, `Ext4::from_base`. Nothing is
hoisted: the digit block of `ρ` is rebuilt inside all three conjuncts, because
that is where the specification's three definitions each compute it, and
sharing it is the brief's highest-ratio `perf-loop` candidate.

Conjunct C's `==` is cpoly's **derived** `PartialEq for Ext4`, and that is the
right call, not a shortcut: cpoly's own development proves `ext_eq_spec` about
exactly that derived body (`cpoly/lean/Field.lean:691-700`, "the derived
`impl PartialEq for Ext4` decides equality in the field"). It is the first `==`
on a field element anywhere in `hachi/src`, so the extraction gained two new
transparent bodies through the `cpoly::_` whitelist,
`cpoly.field.Fp.Insts.CoreCmpPartialEqFp.eq` and
`cpoly.field.Ext4.Insts.CoreCmpPartialEqExt4.eq` (a four-deep `if` of `Fp`
equalities). `Check.lean` § 2b pins both as `def`s, together with the shape of
the record, the three accessors, and `end_piece_prove w = ok w` /
`end_piece_witness stmt w = ok w` by `rfl`.

### Extraction, build, tests

`make extract`: `Generated.lean` +333/−221 lines, of which every `−` is a move —
the ten added definitions are the four items, the record's `new` + three
accessors, and the two `eq` bodies; a name-keyed comparison of every `def`
block against the staged model found **zero changed bodies**. Zero axioms,
deterministic (`unchanged` on the re-run), and the extracted
`end_piece_check` is the specification's own nesting: `if PolyVec.equals … then
if lift_short_check … then CoreCmpPartialEqExt4.eq … else false else false`.
`make build` green, 99 headline specs on exactly the three kernel axioms —
which re-checks `lean/RingSwitch.lean` and everything else against the
reordered model.

`tests/endpiece_semantics.rs` (new `[[test]]` in `Cargo.toml`): nine tests,
references written unlike the crate — `w̃(i)` through a `Nat.digits`-style
balanced digit, the MLE as an explicit `Σ w̃(i)·eq̃(i, a)` with a bit-product
`eq̃`, the commitment as a `u128` unreduced schoolbook product folded by
`X^d = −1`, the norm through a signed `valMinAbs`. Honest `t` and `value` come
from *those* references, so the accept case pins each conjunct and not only
the conjunction. Each reject case isolates one conjunct with the other two
honest; the `z` boundary is pinned at `‖z‖∞ ∈ {14, 15, 16}` through
`end_piece_check` itself; `endPieceCheck_eq_true_iff` is pinned over a
nine-entry corpus hitting all seven non-empty failing subsets of `{A, B, C}`;
and one **live** test runs the whole check with a quotient row at
`(μ, n, m₀) = (1, 1, 14)` — 3.1 s in debug, so no `#[ignore]`. Conjunct B2 is
asserted vacuously and the file says so. 144 live tests total, strict clippy
clean.

One observation from that oracle worth carrying into the spec layer:
`end_piece_check` never compares `d_key.cols()` with `μ + n·8`. `PolyVec::dot`
runs over the shorter length, so a key of the wrong width commits to a
truncated message rather than rejecting. The specification's `Fin`-indexed
types make that state unreachable, so it is not a translation defect; it is a
`WfMat dRows (μ + n * 8) dKey` hypothesis `end_piece_check_spec` must carry,
exactly as `lift_commit_spec` already does.

### Bench: one row, two walls, stated separately

`benches/endpiece.rs` gains `endpiece/end_piece_check`, **REDUCED**, and it is
the one row in the repository where two different scale walls fire inside one
function, so the case doc carries both removal notes apart: **W1** — conjunct
A is `lift_commit` at `LIFT_COLS = 57 384` schoolbook products, `≈ 6.0 × 10^10`
coefficient mult-adds and ≈ 900 MiB of key plus message; the wall is
`ring::mul`'s width and a sub-quadratic `ring::mul` champion removes it.
**W2** — conjunct C is `w_table_mle_eval` at `M_ZERO = 26`: `2^26` points, a
2.0 GiB `Ext4` table twice over; the wall is `m₀`'s cube, which no
multiplication speedup touches and which the split/`eval_mle` rewrites shrink
in *allocation* but not in point count. Reduced shape, each dimension a
file-scope `const` beside the `params` constant it cuts: `RING_DEGREE = 1024`
**real**, `μ = 8` (from `RLIN_COLS`), `n = 1` (from `RLIN_ROWS`), so
`16 · 1024 = 2^14` and `m₀ = 14` is the least legal cube (`const`-asserted both
ways; note the cube is exactly full, where the real one has 12.4% padding). The
input takes the accepting path by construction — `t` and `value` recomputed in
setup, outside the timed region — and the case asserts `‖z‖∞ ≤ CHAIN_GAMMA`,
the coverage inequality, and `end_piece_check(...) == true` before timing, so
a corpus edit that flips any conjunct fails the run instead of silently
shortening the row through `&&`. `z` is drawn from `[1, 15] ∪ {q − c}`, not
zeros: zeros would be half of every `ring::mul` operand and half the table, a
gift to any zero-skipping candidate. The digest is one `bool`, so `check()`
pins what the oracle cannot — honest accepts; `t` bumped rejects; `‖z‖∞ = 16`
with `t`/`value` recomputed honestly rejects; `value + 1` rejects. Sizing
information only: one call at the benched shape took ≈ 82 ms in a plain
release build (no bench, no number to publish).

`end_piece_prove`, `end_piece_witness` and the `WEvalStatement` type are
excluded by name (identities/moves, O(1) by inspection — a run would time the
`black_box` and the move). `coverage --strict`: **110 mirrored, 60 benched,
50 excluded, 0 unaccounted** — moved by exactly the four new markers.
Candidate slot byte-identical; `check-genesis` fails only on the nine unstamped
items (target 4's five, target 6's four), which is the choreography's state
before commit 1.

A harness finding, riding along: `harness.py`'s `BENCH_CASE` regex reads
`bench_case!(c, "<group>", <fn>,` on one line, and rustfmt's `fn_call_width`
wraps the new call into a form the regex rejects — verified: rustfmt's reflow
made `coverage --strict` report all three `endpiece` markers orphaned. HEAD's
file already failed `rustfmt --check` on those lines for the same reason. The
registration function now carries `#[rustfmt::skip]` with a comment; the
real fix is a multi-line-tolerant regex in `harness.py`, not taken here.

### The spec layer is debt, and why it cannot be stubbed yet

`end_piece_check_spec` would be stated against `relWEvalClaim`
(`endPieceCheck_eq_true_iff`) with a `RepWEvalStatement` relation whose
`point`/`value` halves need `lean-wip/Ext.lean`'s `toExt`/`Reduced`, and a
`w_table_mle_eval_spec` that does not exist yet (target 4's 19 triples are
themselves unauthored). A wip file cannot import another wip file
(`lean-wip/README.md`), so the end piece's obligations cannot be typechecked
before `Ext.lean` is promoted. They join target 4's Aristotle batch: the three
headline triples (`end_piece_check_spec` — the `iff` shape `QuadEval` set the
precedent for — and the two identities, which are `rfl`-grade), plus the
`WfMat` hypothesis above.

### Required next actions

1. *(user)* commit 1 — **one commit for targets 4 and 6 together**: both sit
   unstamped in the same tree, both touch `Generated.lean`, `Check.lean` and
   `exclusions.toml`, and the stamp names whichever commit first contains each
   item's text, so folding them costs nothing and halves the stamp dance. Then
   `make bench-stamp`, then commit 2 (stamps alone; never `--amend`).
2. `make bench-check` green.
3. Birth run at a quiet window, then the `rust-bench` § 4 audit of
   `endpiece/end_piece_check` (the `nm` merge check included — a `bool` through
   borrowed inputs, expected merged like every other row in that binary).
4. Promote `lean-wip/Ext.lean`, then author targets 4 + 6's spec layer as one
   Aristotle batch.


## `make spec-check`, and the eleven quadeval items nobody was counting (2026-09-08)

Target 4's and target 6's obligations were authored as
`lean-wip/{ZeroCheck,EndPiece}.lean` (twenty and four statements, zero errors),
on top of `lean-wip/Ext.lean`'s eight ported ones. While building the inventory
for that, three things came out that are worth more than the statements.

**The gate asymmetry.** `bench-check`'s `coverage` gate asks whether every
mirrored item is *benched or excluded* — whether anyone **measures** it. Nothing
asked whether anyone had **stated** what it computes. So proof debt could
accumulate silently while the measurement side stayed green, and it had:
**eleven `quadeval` items have no equivalence statement at all** —
`PublicParamsD`, `QuadEvalStatement`, `QuadEvalResponse`, `carrier_decomp`,
`carrier_commit`, `honest_z`, `honest_compute_v`, `honest_compute_resp`,
`j_mul`, `rel_out`, `paper_rel_out`. `lean/QuadEval.lean` proves eighteen
theorems and not one of them is about those; `rel_out` and `j_mul` appear in it
only inside comments.

`scripts/spec_coverage.py` and `make spec-check` close that: 110 mirrored items,
99 stated, 11 owed. It **reports and never fails** — unspecified is debt to
schedule, not a broken invariant.

Two files are deliberately not counted as specs, and getting this wrong makes
the check vacuous rather than wrong-in-a-visible-way: `Generated.lean` (the
model — every item is in it by construction) and **`Check.lean`, whose § 2b
holds one type ascription per item**. Those pin the model's *shape*, not what it
computes. The first version of the script counted them and cheerfully reported
"0 owed".

**A documentation claim that was false.** `lean-wip/README.md` said QuadEval's
four `iff` statements covered "`InSb`, `vecInSb`, `relOut` and `paperRelOut`".
The theorem named `paper_rel_out_implies_rel_out_spec` is about
`quadeval.vec_in_sb`'s norm implication and mentions neither relation. Corrected
in place, with the mark. The lesson is the one the flat-index defect already
taught in a different register: **a claim that nothing checks is a claim that
drifts**, and the fix is a check rather than a more careful sentence.

**The three ways this project avoids re-proving what is already proved**, now
that all three are in use:

1. **Port, don't re-derive.** `Ext.lean`'s eight stubs carry cpoly's original
   proof scripts *inlined as comments*, because the prover receives only the
   submitted file — a bare `cpoly/lean/Field.lean:513` pointer would have been
   invisible to it and it would have started from scratch.
2. **Compose on upstream theorems.** `hAlphaEvals_eq_alphaDefect` is *used*, not
   re-derived; that is what removed `cRowSum` and its carrier from target 4
   entirely (§ "The computable route around `cRowSum`").
3. **Detect the debt mechanically.** `make spec-check`, above. Memory and prose
   had both already failed at this.

### File layout, corrected

The end-piece statements were first written into `ZeroCheck.lean` to avoid a
second `LEAN_PATH` hop. That was wrong on two counts: `lean/` keeps one file per
`hachi/src` module, and bundling would force targets 4 and 6 to be promoted
together when their obligations are independent. Split into `EndPiece.lean`
importing `ZeroCheck.lean`; the chain is `Ext` → `ZeroCheck` → `EndPiece`, in
that promotion order, with the build recipe in `lean-wip/README.md`.

The three `ringswitch` items the α side introduced (`c_eval_at`,
`c_eval_at_modulus`, `RlinStatement`) stay in `ZeroCheck.lean` for now because
`lean/RingSwitch.lean` is promoted and cannot hold a `sorry`; they belong beside
their siblings there and should be merged in at promotion time.


## The planning documents left the repository, and what that cost (2026-09-08)

Commit `a81b01d` removed `PLAN_PAPER_PARAMS.md`, `PLAN_PROTOCOL_LAYER.md`,
`PLAN_Z_SHORTNESS.md`, `STAGE2_SCOPING.md` and all of `briefs/` from tracking,
and gitignored `briefs/`. They stay on disk as working documents.

The consequence was not obvious and is worth recording: **sixty references in
twenty-five tracked files pointed at them** — `briefs/` alone from fifteen files
— so the repository was citing paths it no longer contained. Worse, four of
those files are the append-only frozen genesis copies
(`benches/genesis/src/{params,ringswitch,zerocheck,endpiece}.rs`), whose contract
forbids editing them "not to fix a lint, not to fix a typo": those references
could never be repaired, only explained.

Resolved by keeping every claim and its attribution while dropping the dangling
*path*: docstrings, `NOTES.md`, `exclusions.toml`, the Lean files and the bench
files now say "the target-4 brief", "the Stage 2 scoping document", "the
protocol-layer plan" and so on. Twenty files edited; the four frozen ones left
untouched and documented as the exception in `README.md`'s layout table, which is
also the one place the literal filenames still belong.

Two traps in doing it, both caught before they landed:

* the blanket substitution mangled `README.md`'s own layout table, which is
  precisely where those filenames *should* appear literally — restored, and
  extended with the convention so the next reader knows why code cites by prose;
* comment-only Rust edits move `Source` spans and normally force a
  re-extraction (the `aeneas-extract` trap). Here `make extract` reported
  `Generated.lean unchanged`, which was **verified rather than believed**: the
  edits came to three insertions and three deletions in `src/zerocheck.rs`, a net
  zero line change, and the model's last `zerocheck` span (`489:0-505:1`) still
  lands exactly on `pub fn h_alpha_is_zero`. Had the count moved, every span
  below the edit would have needed regenerating.

Gates after the change: genesis intact at 210 frozen items, slot byte-identical
across ten modules, coverage 110/60/50/0 unaccounted, **144 tests**, strict
clippy clean. `make spec-check` unchanged at 99 stated / 11 owed.

Also on disk but outside git from here on: the **re-based target-5 brief**
(§ "Re-base from `294b3f0` to `d51d8bc`" inside it). Its findings are summarised
in this file rather than only there, since the document is no longer tracked —
all seven compute-bearing items byte-identical, `CHom` relocated to
`ToCompPoly/Univariate/Basic.lean:354`, `m₀ = 26` halving every cost figure to
`6.87·10^10` `Ext4` mults and a ~46-minute floor, and the external anchor's
larger caveat *removed* because the paper's prototype runs at the same cube size,
leaving the field layer as the whole of the residual ~10× gap.


## Decision: target 5's genesis holds the dense form (2026-09-08)

**Taken by the user**, and it is a deliberate deviation from `op-genesis`'s
central rule — genesis normally holds the *trivial* translation so that every
later gain is measured against the specification's own shape. The rule now
carries this as its one narrow exception, with the test that licenses it.

**What was checked, and one thing that was not.** The first framing of this —
"there is no honest naive-grade translation of this target" — was too strong,
and the user pushed back on it. Three separate claims were collapsed into one:

1. *Can a naive form be written?* **Probably yes.** The ceiling objection is to
   `Std.ExtTreeMap` specifically, not to sparse representation: a monomial
   dictionary as `Vec<(Vec<usize>, Ext4)>` is the same object in the container
   this crate uses for everything (there is no map type anywhere in `hachi/src`).
   **Unprobed** — the `aeneas-extract` probe procedure would settle it, and it
   was not run, so this stays a judgement rather than a finding.
2. *Can it be tested?* **Yes, at toy width.** `b = 3`, `m₀ = 5` gives
   `7^5 = 16 807` monomials, and the reference toy run finishes in six minutes.
3. *Can it be a baseline?* **No** — and this is the only claim that holds. At
   `b = 16` it is `3.9·10^7` monomials at `m₀ = 5` and `1.4·10^12` at `m₀ = 8`,
   so no width both runs and resembles the operation.

**Why (3) is decisive rather than merely inconvenient**, which is the argument
that actually justifies the decision:

* the row would be excluded as infeasible — 9 of the 50 by-name exclusions
  already are — so `vs genesis` for target 5 would yield **no number, ever**;
* `case!`'s digest oracle compares `now` against `genesis` on a fixed input at
  bench time, and genesis could not compute one, so the case could not be
  **built** at all, not merely left unregistered;
* and as a mirrored item it would carry spec and proof debt for a body that
  never executes.

So following the rule's letter buys nothing the rule exists to buy: the
naive-to-dense gain is unmeasurable either way, and freezing naive would add a
dead artifact, dead proof debt, and an unbuildable case.

**What the decision costs, stated so nobody has to rediscover it.** A target-5
`vs genesis` figure measures distance from the **dense** form, never from the
specification's shape. Any ledger row citing that column for a `zerocheck`- or
sumcheck-side candidate must say so; read as distance-from-spec it is simply
wrong, and it will understate a candidate's true headroom.

**The mitigation is required, not optional.** The naive `CMvPolynomial`-shaped
form goes into `hachi/tests/` as the semantic reference at `b = 3`, `m₀ = 5`,
which recovers exactly the independent oracle the dense freeze gives up. Same
move as the α side, where the unreduced 2047-coefficient carrier lives in the
test and nowhere in the crate — and for the same reason: the shape the
specification names has to be executable *somewhere* that the crate is checked
against, even when it cannot be the thing that ships.


## Target 5 opened: the sumcheck's round message, dense (2026-09-08)

First increment of the sumcheck link, taken under the decision recorded above:
`benches/genesis` holds the **dense** form here, and `hachi/src/sumcheck.rs`'s
header says so at the top so that nobody reads its `vs genesis` column as
distance from the specification's shape.

**Five items, the bottom of the chain**: `round_node`, `interpolate`,
`round_value_zero`, `round_values_zero`, `round_poly_zero`, plus two `params`
constants. Eleventh module, so the full new-module choreography — `MODULES`,
both slots' `lib.rs`, a declared `[[bench]]` *and* `[[test]]`.

### The blocker that shaped the design: cpoly has no inversion

Lagrange interpolation needs `1/(xᵢ − xⱼ)`, and **`cpoly` exposes no `inv`, no
`pow` and no `Div`, for `Fp` or `Ext4`** — checked across the whole crate, not
assumed. Reimplementing the field layer is forbidden (`lib.rs` § the cpoly
dependency), so the operation looked unwritable.

What makes it writable is a property of the *nodes* rather than of the field:
the nodes are `0 … 2b`, small integers, so every denominator `∏_{j≠i}(i − j)`
is an integer and **its inverse lives in the base field, never in the
extension**. So the weights are thirty-three `Fp` literals precomputed offline
(`params::ROUND_NODE_INV`), a round message is interpolated by multiplying
`Ext4` values by embedded `Fp` constants, and **no inversion happens at runtime
at either carrier**. Same discipline as `BALANCED_SHIFT` and
`Z_BALANCED_SHIFT`: compute the constant outside, store the literal, check the
relation in a test — `interpolation_weights_invert_their_denominators` pins
`wᵢ · ∏_{j≠i}(i − j) = 1` for all thirty-three, which is what keeps them
auditable rather than magic.

`interpolate` takes the weights as an *argument* rather than reading the table,
so it stays faithful to `interpolateArray`'s arbitrary node set instead of
hard-wiring `0 … 2b`; `round_node_weights()` is the instantiation.

### What was deliberately not done, so it stays measurable

S1 and S2 of the target-5 analysis are prerequisites — nothing runs without
them — and they are what this increment implements. Everything else is left for
`perf-loop` **so that the dense baseline still has headroom to measure**:
`range_product` is called in its literal 31-multiply form (the `v² − j²` form is
16, a 2× cut on the 94%-dominant term), the closed-form `eq̃`, the tensor split
of `Ã` (1024× on the verifier's dominant term), and hoisting the triple
`computeG`. That was the point of freezing dense-but-unoptimized rather than
dense-and-tuned.

### The oracle, and the gap in it that I am not papering over

`tests/sumcheck_semantics.rs`, 7 tests. The load-bearing ones:
`interpolant_reproduces_its_values_at_every_node` (the specification's
`eval_interpolateArray_at_index`, and the property the whole node-value
representation rests on), `interpolant_agrees_off_the_nodes_with_the_polynomial_it_came_from`
(uniqueness — the previous test cannot see away from the nodes), and
`round_poly_has_degree_at_most_two_b`, which would catch an interpolant that
matched at every node while being unsound as a round message.

Three mutations injected, all caught: the fold orientation swapped
(`one_minus·hi + node·lo`), the interpolation basis including its own node, and
the weight dropped.

**The gap.** The decision above promised the naive `CMvPolynomial` shape as the
test-side oracle at the toy width `b = 3`, `m₀ = 5`. That is not what landed,
and the reason is worth recording: the crate's `range_product` is hard-wired to
`GADGET_BASE = 16`, so a `b = 3` comparison cannot run the crate's code at all —
it would compare two test-side implementations. At `b = 16` the naive shape needs
`33^5 ≈ 3.9·10^7` monomials, about 2.8 GB, which is not a test. So the honest
position is: **the identity is checked against an independent dense computation
at the real `b`, and the naive shape is checked against nothing.** Closing it
needs either a `b`-parameterised `range_product` in the crate (a translation
change, since the specification's `rangeProduct` does take `b`) or acceptance
that this link's naive shape is unexercised. It is owed, and it is smaller than
it looked only because the first framing of it was wrong.

### State

`make extract` deterministic, **zero axioms** — including
`params.ROUND_NODE_INV`, which arrives as `Array Std.U64 33#usize` via
`Array.make` and is read with the modelled `Array.index_usize`, not as an opaque
constant. `Check.lean` § 2b extended with the three shape facts. `make build`
green over 3844 jobs. Coverage moved by exactly the five new markers: **115
mirrored, 64 benched, 51 excluded, 0 unaccounted**. **151 tests**, strict clippy
clean. `cargo bench --bench sumcheck -- --test` runs all ten case-variants, so
`check()` and `case!`'s digest equality both pass.

`check-candidate` fails on the slot's git-pinned `lib.rs`, which a new module
necessarily changes — the documented "resolves at commit 1" state, as with
`zerocheck`.

### Owed next on this target

The round machinery above the message: `honest_compute_g`, `round_check`,
`round_out`, `final_check`, `honest_compute_y`, the two statement carriers and
the round loop. `honest_compute_y` should be free once the folded table exists
(S2's shared-subexpression point), and `round_check` needs only the node values
at `0` and `1`, which are nodes — no evaluation machinery.


## The birth run for targets 4, 5 and 6 — and both anomalies dissolved (2026-09-08)

Run **`20260908T1646+0200-10de67cd`**, source `48606df` clean, full pass over
all eleven bench binaries on a genuinely quiet machine (1-min load `0.10`,
Firefox and the editor closed, zero Lean processes — checked, since a Lean build
is what spoiled the 09:01 attempt). Report JSON
`bench-report-20260908-t456-birth.json` (repo root, gitignored).

**The cleanest run this project has had.** 74 rows, **one** flagged, A/B bias
**1.53%**, usable. It is the first measurement for the **42 frozen items** added
since the last good run (176 → 218 frozen), covering targets 4, 5 and 6 at once,
and it doubles as the re-take of the run the concurrent Lean build spoiled.

`op-genesis` stage 7 is satisfied for all three targets: the **19 registered
rows** over those items read noise with a **worst |Δ| of 1.61%**
(`zerocheck/c_w_table_mle`), against a 5% printed threshold. The sumcheck rows
are the sharpest — `interpolate`, `round_value_zero`, `round_values_zero`,
`round_poly_zero` all at ±0.0% — and the `nm` audit confirms each keeps **two
real variant copies**, so that agreement is evidence rather than an artifact of
timing the same function twice.

The single flagged row is `ring/from_coeffs/1024` at **+10.20%**, which is a
known member of the sub-µs `Vec::new()`+push constructor class the § 4 audit
identified; it carries no verdict and needs none.

### Both open anomalies vanished, and the reason matters more than the relief

`gadget/balanced_digit_decompose` — reproducibly **+74.98%** then **+92.25%**
across two runs of the same binary — reads **−0.2%** here.
`zerocheck/w_table_rho_row` — **−8.51%** then **−5.13%** — reads **+1.1%**.

The `nm` audit on the binaries *this* run used explains it, and inverts the
intuition I had recorded:

* in the earlier binary, `balanced_digit_decompose`'s two case wrappers both
  called the **same merged function** — one copy, one address — and the row read
  +92%;
* in this binary it keeps **two distinct copies**, a genuine A/B, and reads
  noise.

So the +92% was never placement bias *between* two copies: with one copy there
is no placement difference to have. It was a property of how that particular
binary reached the single merged function from two wrappers, and it **did not
survive a rebuild** — the crate gained `zerocheck` and `sumcheck` between the
two builds, which moved the merge decisions.

**The rule that follows, and it is the useful part**: a small-row `vs genesis`
verdict is valid only **within one build**. A rebuild can move such a row by tens
of percent without a line of its code changing, so a cross-build comparison of a
sub-millisecond row is not evidence of anything. Before trusting a candidate
verdict on one, confirm it inside the same binary. This supersedes the earlier
reading of these two rows as deterministic placement bias — that reading was
consistent with two runs and wrong about the third.

What survives from the earlier diagnosis: the `_control` rows are merged in every
binary (1 copy each, confirmed again here), so the control still cannot exhibit
the merge-related effects the rows it certifies can, and the printed A/B bias
remains a weaker bound than it looks for small compute-bound rows. The proposals
stand — a control matching each row's scale and allocation profile, and a
per-band threshold — but they are no longer urgent, since no row currently
carries a false verdict.

### Ledger note

No ledger row: this is an onboarding birth run, and an onboarding's provenance
is the `@genesis` stamp. When target 5's rows *do* appear in a ledger row, that
row must state that its `vs genesis` column measures distance from the **dense**
form, per the decision above.

## The dropped `eq̃` factor, and the oracle that could not have caught it (2026-09-08)

Target 5's first increment froze `round_value_zero`, `round_values_zero` and
`round_poly_zero` with `Mirrors computableRoundPoly` lines and a module-header
formula reading

```text
g_i(T) = Σ_y  eq_suffix(y) · P_b( (1 - T)·W[2y] + T·W[2y+1] )
```

**That formula is not `computableRoundPoly (sumcheckPolyZero …)`.** It is missing
two factors of the equality kernel. `sumcheckPolyZero` is
`cEqualityPolynomial m₀ τ₀ * cRangeProduct m₀ b (mle[w̃])`
(`ZeroCheck/Constraints.lean:860`), so the round polynomial at round `i` is

```text
g_i(T) = eq̃(τ₀|<i, a) · eq(τ₀ᵢ, T) · Σ_y eq̃(τ₀|>i, y) · P_b(W(T,y))
```

— a prefix constant over the challenges already drawn, and the free
coordinate's own linear factor. The frozen functions compute the sum alone.

### How the arithmetic gives it away, in one line

`rangeProduct b v = v·∏_{j=1}^{b-1}(v-j)(v+j)` (`:96`) has degree `2b - 1`, and
`w̃` is multilinear, so the sum has degree `2b - 1` in `T`. The specification's
per-round bound is `roundDegZero b = 2b` (`:87`), and `ROUND_NODES = 2b + 1`
exists because of it. The missing degree is exactly the equality kernel's free
factor. A frozen object whose degree is one less than the bound its own node
count is derived from was the tell, and nobody read it.

### Why none of the three gates could see it

* **the `case!` digest** compares `now` against `genesis`, and both hold the
  same formula — this is the shared-semantics-bug-at-birth case `op-genesis`
  warns about, exactly as written;
* **the benchmark** timed a faithful implementation of the wrong formula. The
  birth run's `±0.0%` on all four sumcheck rows was true and told us nothing;
* **the semantics test** — `round_value_is_the_eq_weighted_range_sum` — checked
  the crate against *the same formula the crate implements*, restated. The house
  rule is that a reference is written deliberately unlike the crate and derived
  from the specification; this one was derived from the module header. A
  reference copied from the code under test is not an oracle, however different
  its expression looks.
* and `round_poly_has_degree_at_most_two_b` asserted `≤ 2b`, which `2b - 1`
  satisfies. An inequality where the specification states a tight bound admits
  exactly one defect, and this was it.

Mutation-checked after the fix: dropping the free factor again fails the new
oracle **and** the new exact-degree test; dropping the prefix constant fails the
oracle. Both old tests pass under both mutants.

### Why this is not a re-freeze

The frozen bodies are correct as what they are — the eq-weighted range sum — and
a trivial translation of the dense form legitimately factors this way, since the
kernel is a separate multiplication. Nothing was optimized away and no frozen
byte is wrong. What was wrong was the *labels*: the header formula, and three
`Mirrors` qualifiers that named the whole definition for a factor of it. Those
are comments in `hachi/src`, so the repair is an ordinary edit, and
`benches/genesis` keeps its bytes (its own stale header comments are left alone,
per the append-only rule).

`honest_compute_g` is now the item that mirrors `computableRoundPoly` whole: it
applies `eq_prefix` and `eq_free_factor` around `round_poly_zero`, and its range
component has degree exactly `2b`. The three lower functions keep `Mirrors`
markers — so the coverage gate's work list does not move — with qualifiers that
say precisely which factor they are and which item supplies the rest.

### The rule this leaves

**A semantics test's reference is derived from the specification, never from the
module's own header.** The house pattern already says "written deliberately
unlike the crate", and that was followed to the letter — different order,
different expression — while the *content* came from the code. Restating an
implementation in another order tests the restatement. The check that catches
this class is arithmetic rather than stylistic: when the specification pins a
degree, a node count or a length, assert it **exactly**, because the tight bound
is what a dropped factor violates.

## Target 5's round machinery (2026-09-08)

Fourteen items appended to `hachi/src/sumcheck.rs`, closing the translation of
target 5: `eq_prefix`, `eq_suffix_table`, `eq_free_factor`, `round_value_alpha`,
`round_values_alpha`, `round_node_weights_alpha`, `round_poly_alpha`,
`alpha_public_table`, the three carriers (`NestedZeroCheckStmt`, `RoundMsg`,
`RoundStatement`), `honest_compute_g`, `round_check`, `round_out`,
`honest_compute_y`, `final_check` and `round_loop`; plus
`params::ROUND_NODES_ALPHA` and `params::ROUND_NODE_INV_ALPHA`.

Four things worth keeping:

* **The linear side's interpolation weights are not a prefix of the range
  side's.** The weights of a node set depend on the whole set: for `{0,1,2}`
  they are `2⁻¹, -1, 2⁻¹`, not `ROUND_NODE_INV[0..3]` (which belong to
  `{0,…,32}`). Two separately named and separately tested arrays, because
  reusing the prefix would be a silent wrong answer of exactly the kind above.
* **`round_out` takes its statement by value.** The specification builds a
  statement at the next index; a `clone` of the public data would be a trait
  call with no extracted model, so the fields are moved into the successor and
  the function stays straight-line.
* **No subslice appears anywhere in this crate's extracted model**, which is why
  `eq_prefix` writes its product out instead of calling cpoly's `eq_tilde` on
  `&tau0[..i]`. `final_check`, which needs the kernel over all of `τ₀`, calls
  cpoly's function directly — the reuse rule is satisfied where reuse costs
  nothing.
* **`cube_size` is a deliberate local duplicate** of `zerocheck`'s private
  `two_pow`. Widening a frozen item's visibility is not an append, and the
  duplicate's only cost is that two identical private functions may be merged by
  LTO — which matters to nothing, since neither carries a bench row.

Tests: 15 in `tests/sumcheck_semantics.rs` (was 8), full suite 159 passing / 23
ignored, `cargo clippy --all-targets` clean under pedantic.

Owed on this target, in order: the extraction pass (`make extract`, § 2b
entries), then the freeze/case/slot plumbing for the fourteen items and the
`round_loop` end-to-end test — which needs a `LiftedWitness` builder at toy
width, the one piece of the honest-run oracle not yet written.

## Target 2's statement debt is closed (2026-09-09)

`hachi/lean-wip/QuadEvalProtocol.lean`: eleven statements, zero errors, eleven
`sorry`s, typechecked against the pinned ArkLib (`d51d8bc`) on the first pass.
`make spec-check` goes from **99 stated / 32 owed** to **110 stated / 21 owed**,
and `quadeval` disappears from the owed list. The remaining 21 are target 5's,
which cannot be stated until its extraction pass has run.

Three things this pass established:

* **The subtype that carries a norm is where the hypothesis goes.** ArkLib's
  `relOut` checks no challenge norm, and that is faithful to Eq. (20) *because*
  `ShortChallenge Φ ω = {c : Rq Φ // ‖c‖₁ ≤ ω}` carries it in the type
  (`QuadEval/Reduction.lean:148-151`). The extracted verifier takes a plain
  `PolyVec` and also checks none — so the `ℓ₁` bound has to appear somewhere in
  the statement or the theorem would claim the Rust decides membership for
  challenges the specification's type cannot even express. `toChals` takes the
  proof as an argument and the bound rides on the two relation specs. This is
  the general shape for any erased subtype: the erased side condition becomes a
  rep-function argument, not a dropped obligation.
* **No accessor specs, by precedent.** `RlinStatement` has a `new_spec` and no
  theorems for `m`/`yvec`/`bound`; the projections are consumed through the
  relation. Following that keeps the file at exactly eleven theorems for eleven
  owed items, which is also what makes the gate's arithmetic legible.
* **Three values collide at these parameters and must not be conflated**:
  `ω = 16` (the challenge `ℓ₁` bound), `β = 16` (the paper's digit box, whose
  `[-8, 7]` is `lean/QuadEval.lean`'s `InBoxK`) and `γ = 15` (the `ℓ∞` ball).
  Stage 2 § F3's rule is the mitigation — rewrite hypotheses, never goals — and
  the file's header names all three so a prover reads them before touching it.

This is the only proof work in the tree not gated on `Ext.lean`: it imports the
promoted `lean/QuadEval.lean` and nothing staged, so it can be proved and
promoted while the extension-field layer is still red.

## The chain has four rows no Stage 3 target owned (2026-09-09)

Checking whether Stage 5 could start turned up a gap in the plan's own
accounting. `Composition.lean:244` composes the evaluation chain as

```text
(bridge ▷ quadEval) ▷ rlin ▷ lift ▷ batch ▷ zeroCheck ▷ sumcheckBridge
then (core ▷ rounds) ▷ finalEval
```

— **nine rows.** Stage 3's six targets took the compute-heavy ones (quadEval,
lift, zeroCheck, rounds/finalEval, endPiece). The four **zero-round adapter
rows** were never assigned to a target and none was in the crate:

| Row | ArkLib source | Status |
|---|---|---|
| `bridge` | `QuadEval/Bridge.lean:124,135` | **translated 2026-09-09** (below) |
| `rlin` adapter | `RingSwitch/Rlin.lean`, `Completeness.lean:73` | owed |
| `batch` | `ZeroCheck/Batch.lean:81,267` | owed |
| `nestedSumcheckBridge` | `Sumcheck/Bridge.lean:123` | owed |

They carry no arithmetic — each is a statement map with a pure or guarded
verifier — but they are exactly where one link's output statement becomes the
next link's input, so there is nothing to compose without them. Stage 5's
Rust half is otherwise unblocked: it needs only per-link Rust, all of which
exists.

**Two items in target 4's written scope are also absent from the crate**:
`hypercubeSum` and `relBatched`, both named in the Stage 3 table's target-4
row. Recorded as erasure items in `STAGE2_SCOPING.md`: `hypercubeSum` is
superseded by target 5's dense-form decision (a `CMvPolynomial` hypercube sum
is precisely what the folded table replaces), and `relBatched` belongs with
the `batch` adapter row.

**Neither gate can see a missing translation.** `coverage` and `spec-check`
both work from `Mirrors` lines in `hachi/src`, so they can only report on items
that *exist*: an unstated item is caught, an untranslated one is invisible.
That is a third gate-shaped hole after the two already recorded (`coverage`
asked "is it measured" and nothing asked "is it stated"; now nothing asks "is
it translated"). A scope audit against the brief is the only thing that finds
this class, and it is worth one before Stage 5 closes.

## The bridge row (2026-09-09)

`quadeval::PolyEvalStatement` + `to_quad_eval_statement`, the chain's first
seam (`QuadEval/Bridge.lean:108,124`). It lands in `quadeval.rs` rather than a
module of its own: its ArkLib home is `QuadEval/Bridge.lean`, and a new module
would cost the `MODULES` sync in both `harness.py` and `ledger_check.py`, both
slot mirrors, and a declared `[[bench]]` *and* `[[test]]` — ceremony for two
items. The remaining three adapter rows should sit with their links for the
same reason.

Three things worth keeping:

* **The halves cross, and nothing structural protects it.** The map is
  `avec := mb(xh)`, `bvec := mb(xl)` — inner basis from the *high* half, outer
  from the *low*. At this crate's parameters `ML_VARS_LOW = ML_VARS_HIGH = 10`,
  so a swap typechecks, runs, and computes the transpose of the intended
  bilinear form. The semantics test therefore uses **unequal** toy widths
  (`nl = 2`, `nh = 3`), where the swap is caught by the value *and* the length;
  mutation-checked both ways.
* **The reference had to be written out, not borrowed.** `MlPoly::eval_split`
  is hard-wired to `ML_LOW_LEN`/`ML_HIGH_LEN` and cannot run at a toy width, so
  the test spells out the split form and evaluates `f` by the direct monomial
  sum. That is the better arrangement anyway, for the reason the dropped-`eq̃`
  finding made expensive: a reference taken from the code under test is not a
  reference.
* **There is no `bridge_check` to translate.** The row is a `ReduceClaim` head
  — pure, zero-round, nothing to decide — so the statement map *is* the row.
  The same will be true of the other three adapters, which is why they are
  cheap.

`monomial_basis` was already in `evalsplit.rs` and is the only arithmetic
involved: `2^n · n` ring products, so `1024 · 10 ≈ 10 240` muls per half at the
real width, ~15 s per half at the current schoolbook `ring::mul`. Its bench
case is a REDUCED one when the freeze comes.

Tests: 160 passing, `cargo clippy --all-targets` clean.

## `aristotle-check` cannot validate a wip file that imports a wip file (2026-09-09)

Session `396eb25b` (ZeroCheck's 20 + EndPiece's 4) came back at **24 sorries → 5**
and was refused with `integration_blocked`. The refusal was **not** a proof
failure. Its recorded error is

```
`lake env lean lean-wip/ZeroCheck.lean` failed: …/proofwidgets/.lake/build/lib/lean …
```

— a truncated `LEAN_PATH` dump, because `ZeroCheck.lean` imports `Ext`, and
`lake build` produces no `.olean` for `lean-wip/`. That is the exact case
`lean-wip/README.md` § "Working here" documents, with the detour recipe beside
it; `aristotle_check.py` validates with a plain `lake env lean` and so cannot
build any staged file that imports another staged file.

Re-validated by hand with the detour, against the **now-proved** `Ext.lean`:
**0 errors, 1 sorry** (`w_table_mle_eval_spec`). Integrated manually; the log
carries an `integrated_manual` event saying so, because the helper did not do
it and the provenance should not pretend otherwise.

Two consequences worth keeping:

* **A blocked integration is not evidence of a bad proof.** Both blocks so far
  had different causes — `be85dad4` returned genuinely non-compiling proofs,
  `396eb25b` returned good ones the validator could not build. Read the
  recorded `error` before concluding anything, and note `task_status`:
  `FAILED` and `OUT_OF_BUDGET` mean different things (the second is a partial
  result worth keeping, and 19 of 24 obligations came back from it).
* **Promoting `Ext.lean` makes the problem disappear**, rather than needing the
  helper fixed: once `Ext` is a Lake root under `lean/`, `import Ext` resolves
  from the built library and the plain `lake env lean` the helper runs is
  correct. The fix and the next step are the same action. (Patching the helper
  to use the detour is still worth doing for the general case — nothing
  guarantees the next staged pair won't have the same shape.)

## Two invented powers of two, removed (2026-09-09)

Step 1 of the hypothesis repair. Aristotle's ZeroCheck proofs came back with
five headline specs carrying checked-`usize` fit conditions. Two of the three
Rust causes are now gone; the third (`hmax`, on four specs) is a Lean-side
change because the bound is *derivable* rather than earned.

**`eq_weight` walks a running quotient.** It read bit `j` as
`(i / two_pow(j)) % 2`, materializing `2^j` as a `usize`. `q` now starts at `i`
and is halved each iteration, so `q % 2` at step `j` is the same
`finFunctionFinEquiv` bit with no power formed. That was the sole cause of
`hm1 : 2 ^ m₁ ≤ Usize.max` on `eq_weight_spec`. It is also cpoly's own idiom in
`lagrange_basis`, which this function mirrors — so the fix moves us *onto*
upstream's shape rather than away from it.

**A new private `below_two_pow(i, m)` decides the specification's guard.**
`alpha_public_evals` and `zc_target_alpha` bound `cube = two_pow(tau1.len())`
and compared `i < cube`. They need the *predicate*, never the number, and
`i < 2^m` holds exactly when halving `i` `m` times gives zero. Both locals are
gone and each loop state is one variable shorter.

**`two_pow` stays**, and the reason is worth writing down because it is the
line between an artefact and an earned bound: its remaining callers
(`c_w_table_mle`, `h_zero`, `h_zero_is_zero`, `h_alpha`, `h_alpha_is_zero`)
*build* `2^m`-entry tables. There the caller owes `2 ^ m ≤ Usize.max` anyway —
a table that does not fit in a `usize` does not fit in memory — so removing the
arithmetic would remove nothing real. A bound is an artefact when the function
needs a predicate and computes a number; it is earned when the number is the
output's own size.

### The change is not semantics-preserving, and that is the point

At the pinned `m₁ = 3` old and new agree on every input, which is why the four
existing `eq_weight`/`zc_target_alpha` property tests pass unchanged — and why
the `case!` digest will not fire when the bench next runs. They diverge exactly
where the old code was already wrong: at `m₁ = 64`, `two_pow(64)` doubles `1`
sixty-four times and **wraps to `0`** in release, so `i < cube` was false for
every row and `zc_target_alpha` returned `0` with nothing reported.
`the_cube_guard_survives_a_width_whose_cube_size_does_not_fit` pins that, and
mutation-checked: restoring the old guard fails it in release.

So this is the `rho_digits_at` pattern a second time. The translation invented
arithmetic the specification does not have; the proof layer was the only thing
that noticed; and the repair deletes a hypothesis rather than discharging one.
Worth stating as a rule: **when a statement acquires a `≤ Usize.max`
hypothesis, ask first whether the function needs the number or only the
predicate.** Three of this session's five came from computing a number that was
only ever compared against.

### Owed next on this repair

`below_two_pow` is a new item, so `check-genesis` gains one more unfrozen
entry (35 now). The Lean half cannot be written yet: the Rust change makes
`lean/Generated.lean` stale, and the loop specs move with it —
`eq_weight_loop_spec` gains `q` in its state and the two callers' loop states
each lose a variable. So Step 2 is downstream of `make extract`, which is now
unblocked: no Aristotle session is running.

## The extraction audit, and a faithfulness re-freeze (2026-09-09)

Steps 3 and 4 of the hypothesis repair.

### The audit: the failure source is gone, not moved

`make extract` regenerated `lean/Generated.lean` (deterministic: a second run
is byte-identical; 0 axioms; `cpoly.field.Fp := Std.U64` still transparent, so
the `--include 'cpoly::_'` whitelist held). The check that matters, against the
previous `Generated.lean` from git:

| extracted item | before | after |
|---|---|---|
| `eq_weight_loop.body` | `let i1 ← zerocheck.two_pow j` | — |
| `alpha_public_evals` | `let cube ← zerocheck.two_pow i` | — |
| `zc_target_alpha` | `let cube ← zerocheck.two_pow i` | — |

**Zero checked multiplications** across all eight bodies (the four functions
and their four loops), and `two_pow` is called by none of them. Its five
remaining callers are all `let size ← zerocheck.two_pow …` — table sizes, the
earned-bound case. What is left in the repaired four is the loop counter's
`k + 1#usize`, discharged by the loop guard, and division by the literal `2`.

One methodological note, because it nearly produced a vacuous audit: a checked
multiplication extracts as ``let size1 ← size * 2#usize``, **not** as
`Usize.mul`. Grepping for `Usize.mul` returns zero on any input and proves
nothing. The bodies use `*`, `+`, `/` notation under a monadic bind, and the
bind is the tell — a pure comparison like `if k < m` carries no obligation.

`make build` re-checked the proofs after the regeneration: 0 errors, and all
**99** `#print axioms` lines report exactly
`[propext, Classical.choice, Quot.sound]`. The eighteen
`declaration uses 'sorry'` warnings in the log are all in dependencies
(`Aeneas/Std/Slice.lean`, `ArkLib/Data/Fin/Basic.lean`, …), which the Makefile
§ 220-229 documents as expected: Aeneas and ArkLib ship `sorry`s in definitions
this development never reaches, and `sorryAx` in the axiom audit is the check
that needs no exemption.

### The re-freeze, under the open carve-out

`benches/genesis/src/zerocheck.rs` normally may not be edited at all. This is a
**faithfulness re-freeze** under `op-genesis` § "the one rule": a defect caught
before any measurement has been published against the item is repaired by
replacing the frozen text with the fixed first translation and re-stamping.
The carve-out is still open for every item in this repository —
`logs/ledger.jsonl` has no rows, and the birth runs are provenance rather than
verdicts — so no measurement history is rewritten by this.

Replaced verbatim from `hachi/src`: `eq_weight`, `alpha_public_evals`,
`zc_target_alpha`. Appended: `below_two_pow`. `check-genesis` now reports the
three as *"frozen text do NOT match zerocheck.rs at 1e57c54"*, which is the
gate working: the stamps still name the commit the old text lived in.
`make bench-stamp` re-points them **after** commit 1, per the interleaved
choreography — the stamp stores commit 1's sha, so it cannot be derived before
that commit exists.

Two riders the re-freeze picked up:

* the candidate slot needed **all four** changed modules synced, not just
  `zerocheck` — `params`, `quadeval` and `sumcheck` had drifted since their own
  work landed. `check-candidate` is now null again (11 modules byte-identical).
* copying the fixed text verbatim also carried the *current* doc wording into
  genesis, which incidentally retired that file's dangling references to the
  gitignored planning documents. A re-freeze is the only occasion on which
  genesis's comments may move, and it is worth knowing that they do.

### `below_two_pow`'s marker was invisible for one commit

Its doc comment read ``Mirrors the `i < 2 ^ m₁` guard of `alphaPublicEvals` ``.
The scanner is ``Mirrors\s+(?:ArkLib(?:'s)?\s+)?`(?P<name>[^`]+)` `` — a word
between `Mirrors` and the backticks makes the marker **invisible rather than
wrong**, so coverage silently did not track the item. This is the third
instance of that trap (the `evalsplit` pass recorded the first). Fixed to
``Mirrors `alphaPublicEvals` at its cube guard``, with an `exclusions.toml`
entry: `O(m)` where `m` is a point-count exponent, so a criterion run would
measure the harness.

## Step 5: re-stub only what moved (2026-09-09)

`lean-wip/ZeroCheck.lean`: **0 errors, 9 sorries**, typechecked against the
regenerated `Generated.lean` with the `LEAN_PATH` detour. **47 of 56 theorems
still prove** — the option that preserves proof work rather than re-running it.

Re-stubbed, because their extracted shape moved or they are new:

| statement | why |
|---|---|
| `eq_weight_loop_spec` | state gained `q`, lost `i`; invariant `q.val = i.val / 2 ^ j.val` |
| `eq_weight_spec` | `hm1` retired; keeps `hi`, which `.get` needs |
| `below_two_pow_loop_spec` | new |
| `below_two_pow_spec` | new; `b = true ↔ i.val < 2 ^ m.val`, **no hypothesis at all** |
| `alpha_public_evals_loop_spec` | `cube` argument gone; `hm1` retired, `hmax` kept |
| `alpha_public_evals_spec` | `hm1` retired, `hmax` kept |
| `zc_target_alpha_loop_spec` | `cube` argument gone; `hm1` retired |
| `zc_target_alpha_spec` | `hm1` retired — now **unconditional in the machine model** |

Untouched and still proved: `w_table_spec`, `c_w_table_mle_spec`,
`h_zero_spec`, `h_zero_is_zero_spec` and the whole `h_alpha` family. Their Rust
did not change, so the regeneration did not move them — which is the whole
argument for re-stubbing by *shape* rather than by *file*.

### `hmax` is not minimal, and that is deliberately left standing

The four table-side statements carry `hmax : μ + n * 8 ≤ Usize.max`, and the
audit says it is **not minimal**: `w_table` forms only the product
`rows * digits`, never the sum. The sum is formed by `m_alpha_tilde`
(`zerocheck.rs:334`) and `alpha_contract` (`:441`), whose statements genuinely
need it. So of the twelve `hmax` sites, eight could take the weaker
`n * 8 ≤ Usize.max` and four could not.

Not changed, and the reason is worth recording: `hmax` is consumed *implicitly*
— it appears once as a binder and the proofs reach it through `omega`'s context
scan, e.g. `have hmul : … ≤ Usize.max := by rw [hrholen, hgd]; omega`.
Weakening a hypothesis that eight proofs consume invisibly is exactly the kind
of change that turns into hand-repair of working proofs, which is what
re-stubbing by shape was chosen to avoid. It belongs in a pass of its own, with
each of the eight re-checked.

### The wording change on the bounds that stay

"Model artefact" is retired in favour of **"implied by representability,
invisible to the `Vec` model"**, which is the accurate description and draws
the line this session established. `two_pow`'s `2 ^ n ≤ Usize.max` and
`alpha_contract`'s `hm0` size objects that must exist: a caller who cannot
supply the bound could not hold the table either. What the `Vec` type exposes
is `length ≤ Usize.max` for a vector that *already exists*; it says nothing
about a size computed before the vector is built, so the obligation must be
stated rather than derived. The bounds this session *dropped* were of the other
kind — they sized nothing, and existed only because the code computed a number
where a predicate was wanted.

### The next Aristotle batch

Sixteen obligations across three files, once `982bd0af` resolves: ZeroCheck's
nine (the eight stubs plus `w_table_mle_eval_spec`), EndPiece's four, and
QuadEvalProtocol's eleven if that session returns partial. Promoting `Ext.lean`
first would let the helper validate all three without the manual rescue.

## Two promotions: the Ext4 layer and target 2's protocol layer (2026-09-09)

`lean-wip/Ext.lean` → `lean/Ext.lean` and `lean-wip/QuadEvalProtocol.lean` →
`lean/QuadEvalProtocol.lean`, both at zero `sorry`s. `Check.lean` § 4 goes from
**99 pins to 118**, and all 118 print exactly
`[propext, Classical.choice, Quot.sound]`. `make build`: 0 errors, no `sorry`.

Three things worth keeping.

**`private` puts a statement beyond the audit's reach, and the build says so.**
`fp_is_zero_spec` came back `private` — Aristotle marked all four of its new
helpers that way — and `Check.lean`'s pin failed with
`Unknown constant HachiEquiv.Ext.fp_is_zero_spec`. It is not a helper: it is
the *only* statement in the development about `cpoly::field::Fp::is_zero`
(`lean/Field.lean` covers `Fp`'s operators and its construction boundary, not
this predicate), so it is a headline spec and is now public with the pin kept.
The other three helpers stay private, correctly. The general point: a `private`
`_spec` is invisible to § 4, so the promotion step "add a `#print axioms` line
per headline spec" is also what *detects* a mis-scoped statement — it is a
check, not just bookkeeping.

**The promotion retired a tooling failure, not just a debt.** `ZeroCheck.lean`
now typechecks with a plain `lake env lean` — 0 errors, 9 sorries, no
`LEAN_PATH` detour — because `import Ext` resolves from the built library. That
is precisely the thing that made `aristotle_check.py` refuse session
`396eb25b`'s good proofs, so the next check on ZeroCheck or EndPiece needs no
manual rescue. Promoting the lower layer was the fix and the next step at once.

**I masked a failed `make` again.** The build ran as
`make build > log 2>&1; echo "exit: $?"` in the background; the task wrapper
reported the *compound* command's status (0, from the `echo`), and I read
make's stdout rather than the wrapper's output, so a genuine
`make: *** Error 1` looked green for one round. NOTES already records this
exact failure mode from the bench harness. The rule that actually works:
capture the status into a variable on the line whose output you read
(`rc=$?; echo "make build exit: $rc"`), and for a background command read the
task output file, not only the redirected log.

State after this: `lean/` holds twelve audited modules; `lean-wip/` holds
`ZeroCheck.lean` (9) and `EndPiece.lean` (4) — thirteen obligations, from
thirty-two this morning. `make spec-check` reads 134 mirrored, **111 stated**,
23 owed: the bridge row's two new items and target 5's twenty-one, both
awaiting their own passes.

## The freeze that opened the bench gate (2026-09-09)

`make bench-check` is **green** for the first time since target 5's Rust
landed: 260 frozen items verified against git, the candidate slot null across
11 modules, and coverage at **0 unaccounted for** (134 mirrored, 72 benched, 62
excluded). `make run-bench` is therefore possible again, which is the
prerequisite for the `ring::mul` campaign.

Frozen: 41 items — `params`'s two α-side round constants, the bridge row's
seven `quadeval` items, and target 5's thirty-two. Eight new bench cases and
ten new exclusions.

### Three things the freeze turned up

**`bench-stamp` does not re-point a stale stamp.** After this morning's
re-freeze the three repaired items still carried
`// @genesis 1e57c54 2026-09-08`, and `bench-stamp` had already run — it fills
in *missing* annotations and never asks whether an existing one still holds.
`check-genesis` caught it (*"frozen text do NOT match zerocheck.rs at
1e57c54"*), so the gate is sound; the tool just cannot repair what the gate
reports. The fix is to **delete the stale lines and re-run `bench-stamp`**,
which re-derives them from git — `b95b7ec 2026-09-09` here — rather than
hand-typing a sha, which is the whole point of the mechanism ("a hand-typed
stamp is not a stamp"). Worth teaching `stamp-genesis` to re-point, since a
faithfulness re-freeze will happen again.

**The two-commit choreography collapses when the src text is already
committed.** `op-genesis` prescribes commit 1 (src + genesis) → `bench-stamp` →
commit 2 (stamps). Here the *src* side of all 41 items had landed in earlier
commits, so `stamp-genesis` found each item's text in git immediately and
stamped all 44 in one pass, pre-commit. That is not a loophole: the stamp
asserts "the frozen text equals `hachi/src` at this sha", and `check-genesis`
verifies it against git either way. The dance exists for the case where the
freeze and the source arrive together.

**`BETA_SQ` is frozen at its pre-τ=5 value, and that is correct.** My first
freeze pass matched items by signature *line* and so tried to append `BETA_SQ`,
whose value differs between `hachi/src` (`41_976_510_894_886_092_800`, the
ArkLib #847 correction) and genesis (`163_966_054_471_565_312`). Genesis is
append-only and never follows a change, so the old value standing there is the
baseline doing its job. Match frozen items by *name*, never by signature text —
a re-freeze aside, any difference in the text is the point of the file.

### The exclusion arithmetic, stated honestly

`quadeval::to_quad_eval_statement` is two `monomial_basis` calls =
`2 · 1024 · 10 = 20 480` ring products = **~29 s per iteration** at the
measured `ring/mul/1024 = 1.43 ms`. (**Superseded 2026-09-16 by candidate M**:
the doubling build pays `2 · 1023 = 2 046` products ≈ 2.9 s, so the removal
condition below was re-based in `exclusions.toml` from "a sub-quadratic
`ring::mul`" to "I4 lands a champion". The reasoning recorded here was right
about the cost it was measuring; that cost is gone.) Its removal condition says "until a
sub-quadratic `ring::mul` lands", and the entry now spells out what that is
worth: Karatsuba's 2–4× leaves it at ~8 s, still not a criterion row. What it
needs is the ~30× an NTT would give, which `q = 2^32 − 99` forbids at radix 2.
Same honesty applied to `alpha_public_table`, `final_check` and `round_loop`,
whose wall is `2^m₀` and **not** multiplication — their removal condition is
the tensor split (S6 of the target-5 brief), and conflating the two walls is
what the exclusions header warns against.

### And the MODULES rider fired for real

`ledger_check.py`'s `MODULES` had drifted **three modules behind**
`harness.py`'s — `endpiece`, `zerocheck` and `sumcheck` onboarded while that
set was not touched. Nothing catches it: the two lists are compared only by a
human reading both, and the drift is harmless until a ledger row is written,
at which point it silently rejects or mis-attributes rows for three modules.
Fixed, with the failure recorded in the file's own comment. The first ledger
row is `ring::mul`'s, which is next — so this would have fired then.

## Stage 5's remaining rows, sized (2026-09-09)

Reading the three un-onboarded adapter rows of `Composition.lean:244` before
writing any of them turned two of the three into much less work than the row
count suggested, and the third into a decision.

### Row 7, the sumcheck bridge — done

`sumcheck::nested_to_round_statement` (spec: `nestedToRoundStatement`,
`Sumcheck/Bridge.lean:49`). Zero-round and pure like every adapter, so the
statement map *is* the row.

**Its content is an asymmetry.** The range target opens at the literal `0` —
`H₀` vanishes identically on the cube — while the linear target opens at
`zcTargetAlpha`, which is `n` rows of work the verifier does from the statement
alone. A translation that made the two symmetric (both `0`, or both computed)
would pass any test that checked only shapes, so
`the_bridge_installs_zero_and_the_alpha_target` checks the value, against an
independent reference: `eq̃` by the bit product and `yᵢ(α)` by **Horner**, where
the crate's `c_eval_at` is the specification's power sum with the exponent
recomputed per term. Frozen, excluded by name (it is `zc_target_alpha` plus a
move, measured under its own name in `benches/zerocheck.rs`), 167 tests, strict
clippy clean.

### Row 5, the batching bridge — needs no Rust at all

`batchVerifierPureForm`'s statement map is **`id`**:
`verify := fun stmt _ => stmt` (`ZeroCheck/Batch.lean:267`). The row is a
zero-round `ReduceClaim` at `mapStmt := id`, so nothing is computed and nothing
is reshaped; its whole content is the *relation* `relBatched` and the pull-back
`mem_relLift_of_relBatched`, both proof-side.

That **resolves erasure item 14**: `relBatched` was recorded as owed to the
batch row, and the batch row turns out to have no computable content to hang it
on. It is a spec-layer obligation for Stage 5's proof half, not a translation.

### Row 3, the `R^lin` adapter — its trivial translation cannot be written

`rlinStmt` (`RingSwitch/Rlin.lean:205`) assembles the Eq. (20) block matrix,
five row blocks over three column blocks, with `rlinCols = 8192 + 8192 + 40960
= 57 344` — which is exactly `μ₀`, so the arithmetic confirms the pin. Two
walls, and they are different in kind:

* **`M` itself is 2.2 GiB** (`5 × 57 344` `Rq` at `d = 1024`), matching the
  target-4 brief's note. Large, but holdable; it forces a REDUCED test and an
  excluded bench row, nothing more.
* **the `c4` block is not holdable at all.** It needs
  `(G_{2^m} · J)ᵀ · a`, and `matMul G2m J` is `1024 × 40 960` `Rq` =
  **320 GiB** materialized. There is no width at the pinned parameters where
  the specification's own shape runs.

The reshape that saves it is associativity: `(G J)ᵀ a = Jᵀ (G ᵀ a)`, whose
intermediate is a vector of `8192` `Rq` = **64 MiB**. So the row is
translatable — but only in a form that is *not* the trivial translation of the
definition, which is precisely target 5's situation. It therefore needs
`op-genesis`'s narrow documented exception and its three-part test, and the
decision belongs to the user, not to the translating session. Recording it
rather than quietly taking the reshape is the whole point of that rule: a
freeze that silently contains an optimization zeroes out its own gain forever.

One further flag for whoever takes the row: `rlinStmt` is `noncomputable`
upstream, and ArkLib says why — "only because `rlinStmt` is (it is assembled
through the `stack`/`unstack` reshapes); nothing probabilistic or classical
enters the protocol". So the noncomputability is bookkeeping, not a barrier,
but it means the usual "state against a computable definition" convention needs
the same care the α side needed (`alphaDefect` over `hAlphaEvals`).

## Decision: the `R^lin` adapter's genesis holds the reshaped form (2026-09-09)

Approved by the user. This is the **second** use of `op-genesis`'s narrow
exception to the freeze-the-naive-form rule, after target 5's dense form. Its
three-part test, answered:

**1. The naive form cannot run at any width that still resembles the
operation.** `rlinStmt`'s c4 block is `(G_{2^m}·J)ᵀ·a`, written upstream as a
literal matrix product (`ArkLib.Lattices.matMul G2m J`,
`RingSwitch/Rlin.lean:205`). At the pinned parameters:

```
G  1,024 x  8,192
J  8,192 x 40,960
G·J materialized = 41,943,040 Rq = 320 GiB
```

The **answer** is a vector of `40 960` `Rq` = 320 MiB. The **recipe as
written** costs 1,024× that, one factor for every row of `G` the contraction
against `a` immediately discards. Note this is a *memory* wall, not
`ring::mul`'s time wall — the exclusions header's standing warning against
conflating the two applies, and its removal condition is therefore **not** a
faster multiplication.

**2. So the `case!` digest cannot be computed either.** The digest requires one
Digest-mode execution of the item. A body that allocates 320 GiB does not
execute once, so no bench case can be *built* for it — not merely none
registered.

**3. And it would carry spec and proof debt for a body that never runs.**
`rlin_stmt` is a mirrored item; it would need a `_spec` against `rlinStmt`,
proved about code no test and no bench ever reaches.

The frozen form is therefore the associativity reshape
`(G·J)ᵀa = Jᵀ(Gᵀa)` — an *identity*, not an algorithm change — whose
intermediate is `8 192` `Rq` = 64 MiB.

### Why this exception is cheaper than target 5's, and what that obliges

Target 5's naive form only ran at `b = 3, m₀ = 5`, "a width at which the
operation is no longer itself", so its toy-width oracle tests a *different*
operation and the gap had to be stated rather than closed. **Row 3's naive form
is dimension-parametric**: at `2^m = 4, md = 2, zd = 2` the product `G·J` is
`4 × 16 = 64` `Rq` and the literal `matMul` runs outright. So the mandatory
oracle — "put the naive form in the tests at a toy width instead", which the
exception says is *not optional* — is genuinely available here, testing the
same operation at a smaller size.

That imposes a design constraint on whoever writes the row, and it is the
reason to record this before the code exists: **the arities must travel as
arguments**, as target 4's and 5's do. Hard-wiring `params::MESSAGE_ROWS` and
friends into the reshaped functions would make the toy-width comparison
impossible and would destroy the only oracle this freeze gets — the same
mistake that made `MlPoly::eval_split` untestable at toy width and forced
`tests/quadeval_semantics.rs` to spell the split form out by hand.

### What a reader of a number from this row must know

A `vs genesis` figure for the `R^lin` adapter measures distance from the
**reshaped** form, never from the specification's literal shape. The 1,024×
that associativity already bought is inside the baseline and reads as zero, by
decision. The module header carries this note where the code lands, the same
way `src/sumcheck.rs`'s does.

## The `R^lin` adapter, translated (2026-09-09)

`op-genesis` stages 1–3 for chain row 3. Eleven items:
`gadget::gadget_transpose_mul` and `quadeval::{rlin_cw, rlin_ct, rlin_cz,
rlin_cols, rlin_rows, unflatten, tensor_g_matrix, stack, unstack, rlin_stmt}`.
**173 tests**, strict clippy clean. Stages 4–7 (extraction, freeze, cases,
commits, birth run) are queued; see the ordering note at the end.

### Its Rust home is `quadeval.rs`, and the layering forces that

The ArkLib home is `RingSwitch/Rlin.lean`, and the house convention has been
that the ArkLib home picks the module. Not here: `stack`/`unstack` are maps on
`QuadEvalResponse`, and `lib.rs` declares `ringswitch` *below* `quadeval`. The
adapter consumes QuadEval's output and produces a `ringswitch::RlinStatement`,
so it can only sit on the QuadEval side of that boundary. Layering beats
provenance when they disagree.

### The second wall dissolved on inspection

c5's block is `matMul pp.innerMatrix J`, and the naive product is
`40 960 × 8 192 = 335 544 320` ring multiplications — **5.5 days** at the
measured `ring/mul/1024`. That looked like a second infeasibility needing its
own exception, of a different kind from c4's (time, not memory: the *result* is
only 320 MiB).

It is not. `J`'s columns have exactly one nonzero each, so
`(A·J)[p][k·zd+f] = A[p][k]·base^f` — which is precisely `Jᵀ` applied to row
`p` of `A`. That is the convention `quadeval::j_mul` already froze
("`jMatrix` itself is ~2.5 TB at these parameters and is never materialized"),
and it is faithful rather than optimized for the reason that item gives:
`gadgetMul` is *defined* as `gadgetMatrix *ᵥ v`, so reading the structure
computes the same function. **The same helper therefore serves c3, c4 and c5**,
and the approved exception covers only what it was approved for: c4's
associativity reorder. Worth recording because the 5.5-day figure is alarming
and the resolution is not obvious from it.

### The oracle needed *unequal* digit counts, and mutation found that

The mandatory toy-width test builds `G·J` naively and compares `(G·J)ᵀa`
against the frozen `Jᵀ(Gᵀa)`. First written at `messageDigits = zDigits = 2`,
where a mutant that **swaps the two digit counts** passed: with the counts
equal the two transposed applications commute, so the test could not see the
ordering at all. Re-run at `messageDigits = 2, zDigits = 3` it dies.

That is the **third** instance of one pattern today, and it is worth stating as
a rule: **equal parameters hide ordering bugs, so a toy width must make the
parameters it is testing distinct.** The other two were the sumcheck cube guard
(every case had `n ≤ 2^m₁`, so the guard's upper boundary was never exercised,
and an off-by-one bound survived 24 tests) and the bridge row's crossed point
halves (`ML_VARS_LOW = ML_VARS_HIGH = 10`, so a swap typechecks, runs, and
silently transposes). In all three the fix was to choose unequal toy values;
in none of them would a larger test count have helped.

### Two smaller things

`quadeval::tensor_g` is params-locked to `GADGET_DIGITS`, so the c5 identity
`tensorGMatrix c *ᵥ flatten x = tensorG c x` (upstream's `tensorGMatrix_mulVec`)
can only be checked at that digit count. A live demonstration of why the new
items take their arities as arguments — a frozen item's hard-wired dimension
narrows every future test that has to agree with it.

`rlin_stmt` carries `#[allow(clippy::too_many_arguments, too_many_lines)]` with
the reasons written out: eleven arguments because the six dimensions must
travel for the oracle to exist, and 118 lines because five row blocks over
three column blocks with **no closures** (Aeneas does not support them) means
every block is its own explicit loop with its zero padding written out.

### The ordering that stopped this at stage 3

A bench case for a new item cannot compile before the item is frozen: the
`define_cases!` macro instantiates every case for `now`, `genesis` *and*
`candidate`, so `hc::gadget::gadget_transpose_mul` is an unresolved name in the
`hachi-genesis` crate until the freeze lands. And the freeze must follow the
extraction pass, because a ceiling failure there reshapes the translation —
i.e. changes the text that would have been frozen. So stages 4 and 5 are
genuinely sequential, and the eleven items sit uncovered (`coverage` reports
them) until the extraction runs. That is the expected mid-onboarding state, not
a gap.

## Targets 4 and 6 are proved, and `lean-wip/` is empty (2026-09-09)

Aristotle session `2266ab16`: **13 obligations to zero**, `ZeroCheck.lean` and
`EndPiece.lean` both fully proved. Promoted the same day. `lean/` now holds
**fourteen** audited modules and `Check.lean` § 4 prints **147** headline specs,
all reporting exactly `[propext, Classical.choice, Quot.sound]`. `make build`:
0 errors, no `sorry`. `hachi/lean-wip/` contains nothing but its README for the
first time in the project's history.

### The helper blocked it again, for the third time, for the same reason

`task_status` was `COMPLETE_WITH_ERRORS` and the recorded error was
`lake env lean lean-wip/EndPiece.lean` failing — `EndPiece` imports the
still-staged `ZeroCheck`, and `aristotle_check.py` validates with a plain
`lake env lean`. Third instance today (`be85dad4` was a genuine proof failure;
`396eb25b` and this one were the validator). The pattern is now unmistakable:
**a blocked integration says nothing about the proofs until you read the
recorded `error`.** Rescue is mechanical — build the lower file's `.olean` into
a scratch `LEAN_PATH`, validate, integrate, log `integrated_manual`.

One wrinkle worth writing down: `lake env lean -o out.olean file.lean` refuses
an input outside the Lake root ("must be contained in root directory"), so the
returned files have to be validated **in place**, not from a scratch copy. That
is safe precisely because both were committed and therefore revertible — check
`git status` on the targets before overwriting them, which is also what proves
the local files had not drifted since submission.

### The signature audit found one change, and it was consistent

`w_table_mle_eval_spec` gained `hmax : μ + n * 8 ≤ Usize.max`. Not a new class:
it calls `c_w_table_mle` → `w_table`, whose `rows * digits` product earns the
bound, and the four other table-side statements already carry it. So it joins
the deferred minimality pass (the bound is not minimal — `w_table` forms the
product, never the sum) rather than needing its own decision. Seven new
helper/loop specs otherwise, and no other signature moved.

### What the promotion step caught, again

Nothing this time — but only because the `private` check was run *before* the
build. `Ext.lean`'s promotion failed on exactly that (a `private` `_spec` is an
unknown constant to `Check.lean`), so checking for `private theorem` in the
headline list is now a pre-flight step, not a post-mortem. Both files came back
clean.

## Row 3's tail: extraction, freeze, green gate (2026-09-09)

`op-genesis` stages 4–6 for the `R^lin` adapter. **`make bench-check` green**:
272 frozen items verified against git, candidate slot null across 11 modules,
coverage 146 mirrored / 74 benched / 72 excluded / **0 unaccounted for**.
173 tests, strict clippy clean.

**The extraction was additive, checked properly.** A line diff of
`Generated.lean` showed 102 non-comment *deletions*, including
`ring.Rq.neg_loop.body` — alarming until compared the right way: the set of
definition names went 509 → 587 with **zero disappearances**, all 78 additions
being row 3's items and their loops. Aeneas reorders definitions as new ones
interleave, so a line diff reports moves as delete+add. **The additivity
invariant is about names, not lines**; the same lesson as matching frozen items
by name rather than signature text. Determinism byte-identical, 0 axioms, `Fp`
still transparent, and `make build` re-checked all **147** pins clean against
the regenerated model.

**Two bench rows, nine exclusions.** `gadget/gadget_transpose_mul` and
`quadeval/tensor_g_matrix` do real arithmetic and got rows — the second
deliberately paired with the existing `quadeval/tensor_g`, since upstream's
`tensorGMatrix_mulVec` says the two compute the same thing, so the pair
measures what materializing the c5 block costs over applying it. The nine
excluded split cleanly: five `rlinC*`/`rlin_rows` are O(1) `usize` arithmetic,
three (`unflatten`, `stack`, `unstack`) are pure reshapes whose row would time
the allocator, and `rlin_stmt` is the 2.2 GiB matrix — infeasible even REDUCED,
with its arithmetic already measured through the two rows above.

### The stamp guard, understood properly this time

`stamp-genesis` refuses when `found == head && src_dirty`, where `src_dirty` is
any uncommitted change under `hachi/src` **or** `hachi/benches`. Earlier today
that blocked `nested_to_round_statement`: its text matched at HEAD while row 3
sat uncommitted in the same crate. This time the eleven stamped straight away
despite a dirty `benches`, because HEAD had moved past the commit containing
their text (`found != head`), so the guard does not apply.

So the rule is narrower than "the tree must be clean": **the guard fires only
when the matching commit *is* HEAD.** Stamp immediately after the introducing
commit and it fires; stamp once anything else has landed on top and it does
not. That is why the choreography's step 3 says "commit 1, *then*
`bench-stamp`" — and why two overlapping onboardings trip it, which
`op-genesis`'s written steps do not currently mention.

## The `R^lin` spec layer (2026-09-09)

`hachi/lean-wip/Rlin.lean`: thirteen statements, **0 errors, 13 sorries**,
typechecked against the pinned ArkLib. `make spec-check` goes 111 → **124
stated**, 35 → 22 owed; `gadget` and `quadeval` are clear and only target 5's
sumcheck remains.

**The obligation the file exists for is `rlin_stmt_spec`, and its right-hand
side is the specification's `rlinStmt` — not the reshaped form the crate
computes.** That is the one rule holding: the statement names the ArkLib
definition, and bridging `(matMul G J).transpose *ᵥ a` to `Jᵀ(Gᵀa)` is the
*proof's* job, an associativity argument in `Matrix.transpose_mul` /
`mulVec_mulVec`. Which means the freeze exception is sound exactly when that
theorem is proved, and nothing else can substitute for it — no benchmark, no
digest, and not the toy-width oracle, which checks the identity at `2^m = 4`
rather than at the parameters the crate runs.

### Instantiated or generic: the file had to pick, and the reps decided

Four statements failed to typecheck generically, and the reason is worth
recording because it is a real constraint rather than a slip. `RepParamsD`,
`RepStmt` and `RepResp` live in the promoted `lean/QuadEvalProtocol.lean` and
are **instantiated** at the pinned dimensions (`Φ 1 (2^10) 8 1 (2^10) 8 1`),
per the house rule that a statement instantiates a generic ArkLib one at
`params.rs` values. A statement generic in `blocks`/`messageRows` cannot use
them.

So `stack`, `unstack`, `to_quad_eval_statement` and `rlin_stmt` are stated at
the pinned dimensions, with the Rust's dimension arguments pinned by hypotheses
(`hb : b.val = 2 ^ 10`). The other nine — the five `rlinC*`/`rlin_rows`,
`unflatten`, `tensor_g_matrix`, `gadget_transpose_mul` — are generic, because
they touch no carrier relation. **Both conventions are live in this tree**
(`ZeroCheck.lean` is generic, `QuadEvalProtocol.lean` instantiated), and which
one a file can use is decided by the reps it consumes, not by preference.

Note this does not weaken the toy-width oracle: the *Rust* still takes its
arities as arguments, which is what lets `tests/quadeval_semantics.rs` run the
naive `matMul` at `2^m = 4, md = 2, zd = 3`. The Lean statement being pinned
and the Rust being parametric are independent facts.

### What target 5's file will need first

The remaining 22 are all `sumcheck`, and they are not simply more of the same:
`RoundMsg` is a pair of `UnivariatePoly`, and **this tree has no
representation for a univariate polynomial yet**. Every carrier so far is a
vector or a matrix (`toRq`, `toVec`, `toMat`, `toEvals`, `toPoint`), and
`CPolynomial`'s invariant is *canonicity* — no trailing zeros, `Trim` — which
is a second invariant beyond a length, and the reason `Rq` could get away with
a plain fixed length and this cannot. Per `aeneas-spec-author`, a genuinely new
carrier gets its representation function, its invariant, its coefficient kit
and its `Check.lean` non-degeneracy entries **before** its first spec. So the
sumcheck file opens with a design step, not with a statement.

## Cross-review of the `R^lin` adapter, and what it caught (2026-09-09)

An independent adversarial review of the adapter, its freeze exception, its
oracle and its statements. The mathematics held; the **oracle did not**, and the
finding is the most useful thing to come out of this session.

### What was verified independently, and is correct

The reviewer derived the associativity claim from first principles rather than
from the docstrings — `gadgetEntry` (`Gadget/Core.lean:391`), `matMul`/
`matVecMul` (`Data/Lattices/Vectors.lean:87,93`), and `jMatrix = gadgetMatrix`
at the **same base** (`QuadEval/Gadgets.lean:126`) — and confirmed that
`(G·J)ᵀa` and `Jᵀ(Gᵀa)` both come out as `base^(e+f)·a[i]` at index
`(i·md+e)·zd+f`. Also confirmed correct: c5's `(A·J)[p] = Jᵀ` applied to row `p`
of `A`; `tensor_g_matrix`'s column walk against `finProdFinEquiv` (whose
`.val = e + digits*i'` is `rfl` at `Gadget/Core.lean:418`); the `yvec` order;
the `stack`/`unstack` layout; and the spec's deliberate parenthesisation. All
thirteen statements in `Rlin.lean` name the ArkLib definition they claim, at the
right argument order and instantiation, and `rlin_stmt_spec` is stated against
`rlinStmt` rather than the reshape.

### What it caught: three mutants alive against the whole 173-test suite

`the_assembled_rlin_system_has_the_specified_blocks` asserted **only** c1, c4's
`ẑ` block and four `yvec` entries. c2, c3, c4's carrier block, c5's tensor block
and c5's `ẑ` block were asserted nowhere. I reproduced two of the mutants
before believing them:

| mutant | before | after |
|---|---|---|
| swap `Gᵀb` and `Gᵀc` (c3 ↔ c4 carrier) | 173 pass | **fails** |
| drop the sign on c5's `ẑ` block | 173 pass | **fails** |
| collapse c2 to column `0` | 173 pass | **fails** |
| build c5's tensor at `z_digits` | 173 pass | **fails** |

The test now asserts every block and both paddings by value, plus two
non-vacuity checks (`bvec ≠ c`, so the c3/c4 swap is ruled out non-trivially;
and c5's response block nonzero, so the sign is testable at all).

**The rule this yields, and it is not the "unequal toy values" rule from
earlier today.** A block-structured object needs **every block asserted**,
because each block is the only place its own data appears — no choice of
parameters makes a missing assertion visible. Earlier today three bugs were
hidden by *equal* parameters (the sumcheck guard, the bridge's crossed halves,
the two digit counts); this one was hidden by *absent assertions*, and more
parameters would not have helped. The reviewer's own diagnosis is worth
keeping verbatim: at these parameters `RLIN_CW = RLIN_CT = 8192` and
`messageRows = blocks`, `messageDigits = innerDigits`, so **`z_digits` is the
only dimension that differs from its neighbours anywhere in this row** — every
ordering bug not involving it is structurally invisible to a shape-based test.

### Three statement defects, one of which I had already hit

* `rlin_ct_spec`/`rlin_cz_spec` were **false as stated** — the outer `hfit` is
  satisfied at `blocks = 0` where the inner product overflows and the code
  `fail`s, so the triple cannot hold. I found this independently while
  *proving* them (the goal came out as `ir * idg ≤ Usize.max`); the reviewer
  found it by reading. `rlin_cols_spec` inherited it and is now fixed too.
* `unflatten_spec` was **false at `width = 0`**: the loop never runs, `out` is
  empty, and the postcondition asserts `out.val.length = blocks` with nothing
  determining `blocks`. Now carries `0 < width`.
* The recorded **proof plan was wrong**. `ArkLib.Lattices.matMul` is standalone
  (`fun i k => dot (M i) …`, `Vectors.lean:93`), *not* Mathlib's `Matrix.mul`,
  so `Matrix.transpose_mul` does not apply and no `(matMul M N)ᵀ = matMul Nᵀ Mᵀ`
  exists in ArkLib. The bridge is an index computation — `Matrix.transpose_apply`,
  `matMul_apply`, `dot_eq_sum`, `Finset.sum_comm` — and the docstring now says
  so. Cheap to fix on paper; a prover would have burned a run finding it.

Also fixed: `Rlin.lean`'s header claimed all thirteen statements were generic
when four are instantiated — a contradiction in the paragraph a reviewer reads
first.

### On the `Shared<n>` gap, the review narrowed the risk usefully

Not a present soundness hole: `honest_compute_g` is in no promoted file, so it
is outside the transitive closure of all 147 headline specs. What the pins
actually defend against is a **cpoly rev bump** changing a body under an
unchanged name — and the `Shared<n>` index is assigned by Aeneas per `&T`
occurrence, so it is not a stable identifier and a renumbering would silently
rebind a spec. One detail worth carrying into target 5's specs: the poly×poly
`mul` returns `zero` on an empty operand and **ends in `trim`**, so its result
is canonical. A spec assuming untrimmed convolution would assume something
nothing checks.

## The composed chain has no practical oracle (2026-09-09)

`chain_verify` cannot be exercised, and the reason splits into two independent
halves of which only one is fixable.

**It cannot run at a toy width at all.** Row 2's `paper_rel_out` is hard-wired
to `params::BLOCKS`, `MESSAGE_ROWS` and `INNER_ROWS`, so there is no reduced
shape: an attempt at `blocks = 2` panicked in `PolyVec::get` in all four tests.
A frozen item's arity narrowing every test above it — the fourth instance this
session, after `tensor_g`, `MlPoly::eval_split` and `gadget_mul`.

**At the real width it is too slow, and the dominator is not what it looks
like.** Three `chain_verify` calls were OOM-killed (2.2 GiB each for the
`R^lin` matrix); one ran **24 minutes at 99.9% CPU and 3.9 GB resident without
finishing**. The cost is not the matrix and not `ring::mul`'s mat-vecs (~12 s
each): it is `h_alpha_is_zero` → `alpha_defect` → `alpha_contract`, where the
specification recomputes `M̃_α` *inside* the `ℓ` loop and each `c_eval_at` is a
1024-term power sum with the exponent rebuilt per term.
`zerocheck_semantics.rs` already marks that shape "makes this minutes" for a
single row; the chain multiplies it by the cube.

So Stage 5's exit criterion — "one composed `open`/`verify` pair, proved, with
a bench case" — **cannot be met as written**: no bench case, and no executable
acceptance test. The composition rests on the per-link specs plus a composition
proof, with tests limited to the plumbing and the guard-rejection paths. The
removal condition is the `M̃_α` hoist — strategy S8 of the target-5 brief, a
`perf-loop` accept — and **not** a faster `ring::mul`. One more place where the
two walls must not be conflated.

## `Rlin.lean` readied for Aristotle (2026-09-10)

Pre-flight per `aeneas-spec-author` § 1: `make extract` regenerated
`Generated.lean` with **5 new `chain` defs and a whole-file reorder** relative
to the staged copy — the `chain` module had been added to the crate after that
extraction, and Aeneas orders output by dependency, so the file moved around it.
Deterministic (two runs byte-identical); a block-by-block comparison ignoring
`Source` spans finds 621 → 626 declarations, three new names, **no body
changed**. `lake build` against the fresh file: 0 errors, 147 axiom lines
unchanged. `lake env lean lean-wip/Rlin.lean`: **0 errors, 9 `sorry`s**
(`gadget_transpose_mul`, `rlin_cols`, `unflatten`, `tensor_g_matrix`, `stack`,
`unstack`, `PolyEvalStatement_new`, `to_quad_eval_statement`, `rlin_stmt`); the
four `usize` dimension specs are proved in place. Header corrected (it still said
"none proved here"), `rlin_cols_spec`'s four inner bounds given their fail-point
justification, `lean-wip/README.md` "Current debt" re-pointed at this file.

Lesson: a staged `Generated.lean` is not a fresh one. Adding a module — even one
no spec mentions — reorders the whole extraction, so the "is it fresh" probe is
`make extract` + `git diff`, never the absence of a Rust diff in the modules a
spec touches.

## `Rlin.lean` is proved and promoted (2026-09-10)

Aristotle session `4d70f965`: **9 obligations to zero**, `task_status`
`OUT_OF_BUDGET` — the budget ran out *after* the last `sorry` went, so the
status is misleading on its own and `after_sorries` is the field to read. The
helper integrated it unaided: the file imports only promoted modules, so its
plain `lake env lean` validation was correct for the first time this week.

Audit before promotion: fourteen declarations (thirteen headline specs plus
`RepPolyEval`) compared hypothesis-by-hypothesis against the submitted
baseline — **none changed**, nothing removed. Forty-one declarations added,
all helper or loop lemmas: per-loop specs for the reshapes, the witness maps
and the five row blocks of `rlin_stmt`, two index helpers for
`tensor_g_matrix`, and the two pieces of the associativity bridge,
`matMul_transpose_mulVec` and `matMul_row`, which are exactly what the
corrected proof plan said would be needed once `Matrix.transpose_mul` was
ruled out. No `axiom`, `native_decide` or `admit`; one
`set_option maxHeartbeats 2000000 in` on `rlin_stmt_spec`, which is the
3000-line-file's one heavy elaboration and is local to that theorem.

Promoted per the README's five steps: `lean/Rlin.lean`, `Rlin` root,
`import Rlin`, thirteen `#print axioms` lines. `make build`: 0 errors, **160**
headline specs all on `[propext, Classical.choice, Quot.sound]`, no `sorry`
outside the eighteen known dependency warnings. `make spec-check`: 148
mirrored / 124 stated / **24 owed** — the two `chain` rows and target 5's
twenty-two `sumcheck` items. `lean-wip/` is empty again.

What this closes: the genesis freeze of the *reshaped* c4 block
(NOTES.md § "Decision: the `R^lin` adapter's genesis holds the reshaped
form") rested on `rlin_stmt_spec` being true against the specification's
`rlinStmt`. It now is, machine-checked, so the reshaped genesis is a faithful
baseline rather than a decision awaiting its proof.

## Target 5's statement debt is closed: `Sumcheck.lean` (2026-09-10)

`hachi/lean-wip/Sumcheck.lean`: twenty-four `sumcheck` statements, **0 errors,
32 `sorry`s** (24 items + 8 scaffolding lemmas). `make spec-check` goes 124 →
**146 stated**, owed 24 → **2** (the two `chain` rows, whose Rust is still
moving). Two adversarial reviews (ArkLib side; Rust fail points) converged on
one defect, fixed: `eq_suffix_table_spec` lacked the bound its own doubling
pushes need, `2^(m₀ − i − 1) ≤ Usize.max`, and its `i < m₀` was not a fail
point at all (the statement is true at `i ≥ m₀`, table `[1]`), so it now
carries `i < Usize.max` instead. Everything else -- argument orders,
little-endian bit conventions, the "interpolant equals the node function
everywhere" claims, `honest_compute_g` against `honestComputeG`, the honest
run for `round_loop`, the weights identities for all 36 literals -- verified.

Four things this pass established:

* **The univariate carrier is a port, not a design.** cpoly's own
  `Univariate.lean` has `toRaw : Vec Ext4 → CPolynomial.Raw F` with
  `VecReduced` as the only invariant and proved specs for `zero`,
  `from_coeffs`, `trim`, `eval` and both `Mul` impls; all ten ported proofs
  compiled across the v4.32 → v4.33.1 gap unchanged (Ext.lean's eight did
  not). The one new definition is `toUni := ofArray ∘ toRaw` -- `ofArray` is
  trim -- which lands in `CPolynomial F` and lets `RepRoundMsg` compare
  against the `degreeLE` subtypes' values. Right call because the extracted
  code is **not canonical**: `interpolate` returns exactly `n` coefficients
  with a zero top one, `from_coeffs` never trims, scalar `Mul` never trims.
* **Two forms of the round polynomial, one statement shape.** ArkLib builds
  `computableRoundPoly` symbolically; the crate samples 33 resp. 3 nodes and
  interpolates. The pieces (`round_value_*`, `round_values_*`,
  `round_poly_*`, the three kernel pieces) get lower-half statements in
  explicit field arithmetic (`rangeSumZero`, `linSumAlpha`, `eqProd`, `fold`),
  with `round_poly_*_spec` asserting the interpolant equals the node function
  **everywhere** (degree 31 < 33, 2 < 3); `honest_compute_g_spec` is the
  headline against `honestComputeG`, and its proof is an equality of two
  degree-≤32 polynomials through `computableRoundPoly_eval` and
  `eval_sumcheckPolyZero`. `computableRoundPoly_toPoly` never appears.
* **The round loop is stated three ways.** `round_loop_spec` is the honest
  run (`honestRounds`, built from `roundOut`/`honestComputeG`, `some` when the
  initial targets are the two hypercube sums); `honest_round_messages_spec`
  is the prover's half (`roundProver` at `computeG := honestComputeG`);
  `round_verify_loop_spec` is the verifier's half **for any messages**, via
  `verifyRounds` (the chained `if roundCheck then roundOut else failure`) and
  `RepOptStmt`, so it carries both directions of every round's decision. The
  last two items landed in `sumcheck.rs` while the file was being written;
  `make spec-check` caught them.
* **`LawfulBEq F` is not exported anywhere.** `EndPiece.lean` proves it
  inline as a `have`; every `CPolynomial` operation over `F` needs it. Now an
  instance at the top of `Sumcheck.lean` -- worth moving into `Ext.lean` at
  promotion.

Pre-flight per `aeneas-extract` (run late, after the user asked why the
skill was skipped; recorded so the omission is not repeated): 0 axioms,
`Shared<n>` names unchanged, loop-state histogram gained exactly the two new
loops (a 5-tuple for `honest_round_messages`, the model's largest), no-op
re-extraction `unchanged`, `check-toolchain` green, `make build` green on
the fresh file (160 axiom lines, kernel-only). The two changed `chain` bodies
are the user's live edit to `chain.rs`, not drift.

## Target 5's spec layer: `Sumcheck.lean` readied for Aristotle (2026-09-10)

`hachi/lean-wip/Sumcheck.lean`: **twenty-four `sumcheck` statements** — every
`Mirrors`-marked item, including the two rows added the same day
(`honest_round_messages`, `round_verify_loop`) — on top of the univariate
carrier the tree did not have. `make spec-check`: 150 mirrored / **148
stated / 2 owed**, the two `chain` rows. 0 errors, **32 `sorry`s**.

### The design step: the carrier is a port, and it is not canonical

NOTES § "What target 5's file will need first" predicted the file would open
with a representation for `UnivariatePoly`, and that canonicity was the
difficulty. Both true, but the resolution was cheaper than feared: cpoly's own
equivalence development (`cpoly/lean/Univariate.lean`, the file `Ext.lean` was
ported from) already has it — `toRaw : Vec Ext4 → CPolynomial.Raw F`, the
coefficient array **as it stands**, with `VecReduced` as the only invariant.
Canonicity is what `trim` *establishes*, not what the representation assumes,
and that is forced by the extracted code: `interpolate` returns exactly `n`
coefficients with a zero top coefficient, `from_coeffs` never trims, and the
scalar `Mul<Ext4>` does not trim; only the poly×poly `Mul` trims, once, as
`CPolynomial.Raw.mul` does. The one new definition is
`toUni v := CPolynomial.ofArray (toRaw v)` (`ofArray` **is** trim), which lands
in the specification's `CPolynomial F` and lets `RepRoundMsg` compare against
the `degreeLE` subtypes' values. Ported: ten `cpoly.univariate` specs
(`uni_*`), six proved in place across the v4.32 → v4.33.1 gap
(`zero`, `from_coeffs`, `trim_loop`, `trim`, `eval_loop`, `eval`), the scalar
and convolution `Mul`s carried with their upstream scripts. Two frictions:
hachi's extraction spells the impls without the `cpoly.` prefix, and
`LawfulBEq F` is not exported by `Ext.lean` (EndPiece proved it inline; now an
instance).

### Headline against the definition, lower half in field arithmetic

The `Mirrors` lines split the round polynomial into pieces ArkLib does not
name ("`computableRoundPoly` at the `sumcheckPolyZero` summand, one node,
*without* its `cEqualityPolynomial` factor"). Those get lower-half statements
in plain defs (`rangeSumZero`, `linSumAlpha`, `eqProd`, `fold`); the items
mirroring an ArkLib definition *whole* get the headline against it —
`honest_compute_g_spec` against `honestComputeG`, `interpolate_spec` against
`CLagrange.interpolateArray`, `round_check`/`round_out`/`final_check`/
`nested_to_round_statement` against their names, `honest_compute_y` against
`wTableMleEval` (Correction 5: `honestComputeY` picks up `[SampleableType F]`
by section accident). ArkLib builds the round polynomial *symbolically* while
the crate samples `33` resp. `3` nodes and interpolates, so
`round_poly_{zero,alpha}_spec` say the interpolant equals the node function
**everywhere** (degree `31 < 33`, `2 < 3`), and `honest_compute_g_spec`'s proof
is an equality of two polynomials of degree `≤ 2b` through
`computableRoundPoly_eval` and `eval_sumcheckPolyZero`; the `CPolynomial`
identity `computableRoundPoly_toPoly` never has to appear. The round loop is
stated as the **honest run**: `honestRounds` iterates `roundOut ∘ honestComputeG`,
`verifyRounds` iterates `roundVerifier`'s `if roundCheck then roundOut else
failure`; `round_loop_spec` returns `some` under exactly the two sum clauses of
`nestedRoundRel` that `roundCheck_honestComputeG` consumes.

### Cross-review: two independent adversarial passes

One walked every `sumcheck.*` fail point in `Generated.lean` and every callee
spec's hypotheses; the other checked all nineteen ArkLib/CompPoly names for
argument order and instantiation, both bit-order conventions (the suffix table
against `lagrangeBasis`'s `getLsb`; `fold`'s `(2y, 2y+1)` against
`finFunctionFinEquiv`'s units bit and `hypercubePoint`'s pivot), the
prefix/pivot/suffix kernel decomposition, and the round-loop sufficiency. One
statement was **false**: `eq_suffix_table_spec` had no bound on the table's
`2^(m₀−i−1)` pushes — at `m₀ = 65, i = 0` the 64th doubling pushes onto a
vector of length `Usize.max`. Fixed with the output's own size, the same shape
as `cube_size`'s bound; `honest_compute_g` derives it from `w_tab`'s `Vec`
length and needs nothing new. Everything else verified: no vacuous hypothesis
set, `hw` on `interpolate` subsumes node distinctness (a repeated node makes
it read `0 = 1`), `finalCheck`'s `bound`/`b` — the one place two same-typed
`ℕ`s could permute silently — in the right order.

Proof debt the file leaves for the prover, noted in the docstrings: specs for
`cpoly.multilinear.eval_mle_layer` and `eq_tilde` do not exist yet; the
`toUni g = sg.1.1` equalities go through "equal at more than `deg` points",
not `Polynomial.funext`.

Pre-flight: `make extract` deterministic, `lake build` green against the fresh
extraction (the new `chain`/`sumcheck` items reorder `Generated.lean`, as
recorded yesterday). Imports only promoted files, so the Aristotle helper's
plain validation works on the return.

## The chain's two rows are stated: `Chain.lean` (2026-09-10)

`hachi/lean-wip/Chain.lean`: `chain_verify_spec` and `chain_open_spec`, **0
errors, 5 `sorry`s** (the two rows plus `copy_point`'s pair and the one-line
`μR + nR·8 ≤ Usize.max`). `make spec-check`: **150 stated / 0 owed**, the first
time every mirrored item in the crate has a statement.

Extraction first, this time by the skill: `make extract` reported
`unchanged`; `check-toolchain` green; 0 axioms; loop-state histogram and
`Shared<n>` names identical to the previous generation; declaration set
identical. The chain rows had already been re-extracted with the prover /
verifier split of `chain.rs`.

What the statements are against, since `evaluation` is not a function:
`chainStart` (rows 1–7 as one statement map — `toQuadEvalStatement`,
`rlinStmt`, the `NestedZeroCheckStatement` the lift and zero-check rows adjoin
`(t, α, τ₀, τ_α)` to, `nestedToRoundStatement`) and `chainVerdict` (the
**three** decisions the composed verifier runs: `verifyRounds`, then
`finalCheck && endPieceCheck`, with `γ` as both `rlinStmt`'s and `finalCheck`'s
bound and `hachiLiftCom` at the extracted key as the commitment scheme, exactly
`end_piece_check_spec`'s shape). Eq. (20), the lift's shortness and the two
zero-check blocks appear in neither, faithfully: they are relations, not
checks, per `chain.rs` § "What the verifier checks". `chain_open_spec` is the
conjunction of `honest_compute_v_spec`, `lift_commit_spec`,
`honest_round_messages_spec` along `honestRounds` from `chainStart` at the
honest `v` and `t`, and `wTableMleEval`.

Two mechanics worth keeping. `LiftCom` is not greppable as a `structure`/
`class` under the pinned ArkLib tree from here (it is reached through
`hachiLiftCom`'s result type), so the verdict takes the extracted key matrix
and builds `hachiLiftCom Φ 15 16 (toMat d_key)` inside, as the promoted end-piece
spec does — no bare `LiftCom` in a signature. And `Chain.lean` imports the
staged `Sumcheck.lean`, so it is validated with the `LEAN_PATH` detour
(`lake env lean -o scratch/Sumcheck.olean lean-wip/Sumcheck.lean`, then
`LEAN_PATH="$(lake env printenv LEAN_PATH):scratch"`); promotion order is
`Sumcheck` then `Chain`, and the chain's proofs are local work, not Aristotle's.

## `Chain.lean` is proved, locally (2026-09-10)

All five obligations filled without touching a statement (signature diff
against the committed file: empty; two helpers added, `toPoint_of_val_eq` and
`wfPoint_of_val_eq`). `lake env lean` through the detour: 0 errors, 0 `sorry`,
0 warnings. Axiom closures: `copy_point_spec` and `rlin_dims_fit` kernel-only;
`chain_verify_spec` and `chain_open_spec` carry `sorryAx` **only** through
`Sumcheck.lean`'s still-open `final_check_spec` and
`honest_round_messages_spec`, the two link specs they call that Aristotle's
restart session `c8d6894b` is working on. Once those close, both chain
theorems are kernel-only with no further work here.

The proofs are what the statements promised: `step with <link spec>` chains
through eleven promoted or staged specs, an anonymous-constructor
`NestedZeroCheckStatement` handed to `NestedZeroCheckStmt_new_spec`, one
`rcases` on `verifyRounds`'s `Option` mirrored by `rcases` on the extracted
`after`, and `Bool.eq_iff_iff` to turn `end_piece_check_spec`'s iff into the
`&&`. Four mechanics cost a round-trip each and are worth keeping:

* `subst` on the extracted `match after with …` fails with "invalid motive";
  `rcases after with _ | s2` and a `cases` on the impossible equation does it.
* The final `step … as` of a function whose body ends in `ok (…)` consumes that
  `ok`: the goal is already the bare postcondition (`let`s included), and a
  trailing `simp only [WP.spec_ok]` errors with "no progress".
* `set s0 := chainStart …` and, separately, a constructor field written as
  `(hachiLiftCom Φ 15 16 (toMat … d_key)).com sw` both hit `maxRecDepth` —
  the unifier evaluating `8 =?= rhoDigitCount q 16` (`Nat.clog`) while
  matching the key's column count. Build the statement with `toVec t`, prove
  the constructor spec with the plain `hpv`, then `rw [htV] at hopened`.
* `μR + nR * 8 ≤ Usize.max` is `norm_num [μR, nR, rlinCols, rlinRows]` down
  to `57384 ≤ Usize.max`, closed from `usize_max_ge` (Aristotle's helper in
  `Sumcheck.lean`) by `omega`.

## Birth run for the Stage 5 rows (2026-09-10, evening)

`bench-report-20260910-stage5-birth.json`, run `20260910T2014+0200-092bdc7f`,
40 minutes on a quiet machine (0 `lean` processes, load 0.78 at start), source
`d4093f4`. **Usable**, A/B bias **1.3%** -- the tightest control of any run so
far (previous runs: 1.4–4.4%). 84 rows, none outside the noise band, as a
birth run must be: `now` and `genesis` are the same bytes. The ten rows that
had never been measured -- `gadget/gadget_transpose_mul`,
`quadeval/tensor_g_matrix`, and the eight sumcheck round-machinery rows
(`eq_prefix`, `eq_suffix_table`, `round_check`, `round_out`,
`round_value_alpha`, `round_values_alpha`, `round_poly_alpha`,
`honest_compute_g`) -- now have a baseline number. Sizing information worth
one line each: `honest_compute_g/1024` 17.1 ms and `round_poly_zero/1024`
16.9 ms, so at the REDUCED cube one round message is essentially one range-side
interpolation; `round_check/26` 1.25 µs and `round_out/26` 0.67 µs, the
verifier's per-round cost, four polynomial evaluations; `interpolate/33`
172 µs; `gadget_transpose_mul/1024` 37 ms. This is provenance, not a verdict:
the ledger is still empty and the re-freeze carve-out stays open.

## Sumcheck: Aristotle's second pass adopted, three obligations left (2026-09-11)

Restart session `c8d6894b` (the helper's automatic follow-up on the seven left
by `430518ae`) came back `OUT_OF_BUDGET` at **7 → 3**, and the helper blocked
integration with *"changed locally since Aristotle submission"* — correct this
time: three of the seven had been proved by hand overnight (`final_check_spec`,
`round_poly_zero_spec`, `round_poly_alpha_spec`, commit `d4093f4`). Aristotle
proved those three **and `interpolate_spec`**, the Lagrange construction that
had defeated it once; its open set is a strict subset of the local one, so its
file was adopted wholesale and the local hand proofs (plus six helpers) are
superseded, kept only in git history.

Two facts from the audit:

* **No statement moved on either side.** Every signature in Aristotle's return
  and in the local edit is byte-identical to the submitted baseline. Aristotle
  added thirty helper lemmas — the interpolation ones (`basisProd_*`,
  `interpolate_*_loop_spec`, `interpPartial_*`, `weights_prod_eq_one`,
  `interpolateArray_toPoly_eq`, `cpoly_eq_of_eval_eq`) and, for the round
  message, `cMLE_eval_update` (one-coordinate multilinearity),
  `finFunctionFinEquiv_cons_val`, `raw_eval_mul`, `raw_eval_smul`,
  `toUni_mem_degreeLE` — exactly the bridge lemmas the statement-side plan had
  named.
* **Its `honest_compute_g_spec` did not compile here.** A 137-line partial
  proof with eight elaboration errors in this environment (`omega` on a
  `Fin.snoc` index, a `Fin.snoc` motive mismatch, unsolved goals) sat where
  Aristotle's own count reported a `sorry`; replaced by `sorry`, and the file
  re-validates at **0 errors, 3 `sorry`s**. `Chain.lean` re-typechecked over
  it unchanged. Manual integration is logged (`integrated_manual`) with the new
  sha, since the helper could not. A further restart on the three needs a
  fresh submission (the blocked integration did not trigger the automatic one).

Left: `honest_compute_g_spec` (the degree-32 polynomial identity through
`computableRoundPoly_eval`, `eval_sumcheckPolyZero` and the kernel
factorization — the lemma scaffolding for it now exists), and the two loop
specs that consume it.

## `Check.lean` § 2b covers sumcheck and chain; the docs catch up (2026-09-11)

While Aristotle's third pass runs, the two Stage 4 chores that do not touch
`Sumcheck.lean`.

**§ 2b pins.** Until today the sumcheck block pinned six early items and
nothing of the round machinery, the prover/verifier split, the three statement
carriers or the chain module — the "is it stated" gap's older sibling, "is its
shape pinned". Now every non-loop `sumcheck.*` and `chain.*` item has a
term-position ascription, and the block records the four facts a re-extraction
must not move: accessors extract under an `impl` segment
(`sumcheck.RoundStatement.impl.zc`) while constructors are `.new`; the linear
side's node count and weight array are their own objects (`3`,
`Array Std.U64 3`), not a prefix of the range side's; the two rejecting loops
return `Option` inside `Result`; `cube_size` is `two_pow`'s deliberate local
duplicate. § 1's protocol block gains the node counts as checked relations
against the named bounds — `ROUND_NODES = roundDegZero GADGET_BASE + 1` and
`ROUND_NODES_ALPHA = roundDegAlpha + 1` — so the `2 · 16 + 1` and `2 + 1` in
`params.rs`'s docstrings are no longer prose. `make build`: 0 errors, 160
axiom lines, kernel-only.

**Docs.** `lean/Ext.lean`'s header still said it had yet to move to `lean/`;
the root README listed seven Lean modules and eight Rust ones, said
"ninety-nine specs", and described ring-switch, zero-check, sumcheck and the
end piece as "absent code"; INSTRUCTIONS named `Ext.lean` as the standing debt.
All re-pointed at today's state: fourteen promoted modules and two staged, one
hundred and sixty audited specs, every chain link translated and stated, and
the two things actually absent named precisely — the honest lift prover
(`honestLiftWitnessC`) and an executable oracle for the chain at real width.
The wip README's "Working here" now records the two times the detour was used
instead of claiming it never was.

## The honest lift prover is translated (2026-09-11)

Stage 5's one untranslated item. Three ArkLib definitions
(`RingSwitch/ComputableWitness.lean`, `RingSwitch/Reduction.lean:439`) land in
`hachi/src/ringswitch.rs` as `honest_lift_witness`, `c_quotient` and
`c_row_sum`, with two private helpers: `long_mul`, the product of two canonical
representatives in `Zq[X]` **without** the negacyclic fold, and
`div_by_modulus`, `CPolynomial.divByMonic` at `X^N + 1`. `chain_open` can now
stop taking the lifted witness as an input; that change is a separate step,
because `chain.rs` is frozen and stamped and the swap is a body change to a
frozen item (carve-out open, no number published against it -- but a decision,
not a reflex). Brief: `briefs/target-7-lift-prover.md`.

Four things this pass established:

* **The unreduced product finally has a carrier**, and it is a `Vec<Fp>` of
  exactly `2N − 1 = 2047` words, not a newtype: only `c_quotient` consumes it.
  It is the `Raw` array reading of a `CPolynomial (ZMod q)`; the Lean
  representation `toCPolyK` is `ofArray` of the word map -- trim on the spec
  side -- with the length a separate invariant (`WfWords`). This is the
  object NOTES.md § "Target 4 opens" said the crate lacked; it exists now
  because the lift prover cannot do without it, where the zero-check could.
* **The division is the spec's recursion, densified.** `divModByMonicAux.go`
  peels one leading term per step and trims; on the fixed-width carrier the
  loop walks every slot from `2N − 2` down to `N`, and a zero slot is a step the
  specification skipped -- a no-op subtraction. That equivalence ("skipped steps
  are no-ops") is the one non-mechanical lemma the proof of `div_by_modulus`
  will need, and the brief names it. The loop's state is a **3-tuple**
  `(rem, quot, k)` -- two vectors plus the counter, the first such shape since
  `mul_loop1_loop0`; the extraction audit recorded it.
* **The oracle is the cross-route identity.** The semantics test states
  `defect = ρ · (X^N + 1) + (M·z − y)ᵢ` in `Zq[X]` with the reduced term taken
  from the ring layer's own (separately proved) `mat_vec_mul`/`sub` and the
  products by a `u128` double sum -- two routes to one polynomial meeting in
  the unreduced ring. A `+` for the modulus's sign, a dropped high half, or an
  off-by-one in the leading slot all fail it; the honest case (`y := M·z`)
  additionally has zero remainder, and the quotient's top word is asserted
  zero (degree `≤ N − 2`, inside `hρ`'s `d − 1`).
* **Everything before the freeze is green**: 20 ring-switch tests (4 new),
  full suite, clippy pedantic; extraction regenerated with 27 declarations,
  0 axioms, deterministic, no `Shared` change; `make build` 0 errors, 160
  axiom lines kernel-only; `Check.lean` § 2b pins the five items;
  `lean-wip/LiftProver.lean` states all five (0 errors, 5 `sorry`s);
  `make spec-check` **155/155 stated**; coverage 155 mirrored, 77 benched
  (three new W1-REDUCED rows at `LIFT_PROVER_COLS = 4`), 78 excluded (the two
  private helpers, by name with the reason), 0 unaccounted. Genesis has the
  five appended verbatim, the candidate slot is synced and null. `check-genesis`
  fails only on the five missing stamps, which is the choreography's step 3.

Owed, in order: commit 1 (Rust, tests, bench, exclusions, genesis copy, slot,
`Check.lean`, `Generated.lean`, `LiftProver.lean`, brief stays local), then
`make bench-stamp`, commit 2 (stamps only, never `--amend`), `make bench-check`,
then a filtered shake-out and a birth run for the three rows. Then the decision
on `chain_open` taking `w` as an input.

## Sumcheck and the chain are proved and promoted (2026-09-11)

Aristotle's third pass on `Sumcheck.lean`, session `3fd1e8a2`, returned
`COMPLETE` at **3 → 0** and the helper integrated it unaided -- the file had not
moved since submission. Audit before promotion: every statement byte-identical
to the submitted baseline (the scanner's one flag, `honestRounds`, was a false
alarm from a lemma appended right after the definition; the two texts are
equal); fourteen helper lemmas added -- `hypercubePoint_snoc_update`,
`hypercubePoint_cons_eq`, `lagrangeBasis_get_cube`, `fold_tableFn_eq_mle`,
`eqProd_hypercubePoint_split`, `eval_mle_layer_spec` and its loop,
`roundCheck_honest`, the two initial-table lemmas, and the `honestRounds`
congruences -- which are exactly the bridge lemmas the statement-side plan
named for the degree-32 identity and the loop invariants; six local
`maxHeartbeats` overrides, no axiom, no `admit`. All twenty-five spec theorems
(the twenty-four items plus `cube_size`) print the three kernel axioms.

Promoted together with `Chain.lean`, which imports it and re-typechecked over
the finished file at 0 errors / 0 `sorry` / 0 warnings. Twenty-six new lines in
`Check.lean` § 4; `make build`: 0 errors, **186** headline specs, kernel-only.
`lean-wip/` now holds `LiftProver.lean` alone.

The record of the three sessions, since it is the first file here that took
more than one: `430518ae` (32 → 7, `OUT_OF_BUDGET`), `c8d6894b` (7 → 3,
`OUT_OF_BUDGET`, adopted over hand proofs of three of the seven because its
open set was a strict subset -- and with its broken partial proof of
`honest_compute_g_spec` cut back to `sorry`), `3fd1e8a2` (3 → 0, `COMPLETE`,
submitted with `--allow-small` on the recorded grounds that the remaining three
were the identity and its two consumers). Two lessons: read `after_sorries`, not
`task_status`, on an out-of-budget return; and a restart's partial may not
compile here even when its count is right -- validate before adopting, always.

With this, every mirrored item in the crate except the five lift-prover items
has a proved, audited specification, and the composed chain's two rows are
kernel-clean. Stage 4's exit is one file away; Stage 5's remaining structural
gap is `chain_open` computing the witness it now can.

## The full REDUCED run after the lift prover landed (2026-09-11)

`bench-report-20260911-stage5-reduced.json`, run `20260911T1509+0200-53a20295`,
source `8e2052c` clean, 15:09–15:50 (41 min), machine quiet (load 0.27 at
start, only the editor's idle `lake serve`; no Lean build, no other `cargo`).
**Usable**, A/B bias **1.6%** (`_control/sumcheck` +1.56% the worst; the other
nine controls within ±0.9%). 87 rows: 84 `noise`, 3 printed `slower`. The
three are the band, not a regression, and every one of them is already on the
no-verdict list of § "The endpiece rows get a binary" and the certified sweep:
`quadeval/in_sb_box/1024` +13.6% at ~0.6 µs (band *and* memorized branch),
`ringswitch/rho_digits/1024` +7.4% at ~2 µs (the row noted as 20% clear of
the band's upper edge — it is not clear of it), `ring/one/1024` +5.0% at
~0.7 µs. `now` and `genesis` are the same bytes at this HEAD (`check-genesis`
passed on 282 items), so a printed verdict on those rows is the flat 5% floor
being wrong inside 100 ns – 2 µs, for the third run in a row. The next row down
is `quadeval/in_sb/1024` at +3.9%, also on the list; everything above 2 µs is
within ±3%.

The three lift-prover rows get their first baseline, all `noise` at ±0.03%:
`ringswitch/c_row_sum/4` 4.52 ms, `c_quotient/4` 4.52 ms,
`honest_lift_witness/4` 4.52 ms (one row of `LIFT_PROVER_COLS = 4` columns, so
the three rows are one `cRowSum` each — four unreduced `1024 × 1024` products at
~1.1 ms — plus an `O(N)` division and a copy that the row cannot see). Sizing
only: the ledger is still empty and the re-freeze carve-out stays open for
every item.

What this run *is*: the per-operation REDUCED measurement of every onboarded
item, taken so the Stage 6 loop has a same-host reference for what its rows
read at rest. What it is not: a composed-chain number — `chain::chain_verify`
and `chain_open` stay excluded by name, and the discussion of the day (a
REDUCED chain row needs an accepting transcript, hence a covering cube,
`m₀ = 17` at the smallest widths the crate allows, ~20 s per verifier call in
the naive `alpha_public_table`) is the reason the Stage 5 exit is to be read
as "pair proved, bench case deferred to Stage 6". ⊕ **The user ratified that
amendment on 2026-09-11**; `PLAN_PROTOCOL_LAYER.md` carries it, and Stage 6
inherits the row together with the three walls that block it.

## The lift prover is proved, and Stage 4 closes (2026-09-11)

Aristotle session `1ddd5790` on `lean-wip/LiftProver.lean` returned `COMPLETE`
at **5 → 0** and the helper integrated it unaided -- the file had not moved
since submission, so neither the merge guard nor the local `lake env lean`
validation had anything to complain about. The five were the honest lift
prover's own items: the unreduced row sum against `InnerOuter.cRowSum`, its
division against `InnerOuter.cQuotient`, the headline `honestLiftWitnessC`
through `RepLiftedWitness`, and the two private helpers -- the product in
`Zq[X]` against `CPolynomial`'s `*` and the synthetic division against
`CPolynomial.divByMonic`. `honest_lift_witness_loop_spec` had been proved here
before submission and is unchanged.

Audit before promotion: all **eleven** submitted declarations compared
signature-for-signature against the recorded baseline, none changed (the
comparison is mechanical -- declaration text up to the first top-level `:=`);
**twenty-six** target-local helper lemmas added, which are the ones the
statement-side plan named -- coefficient bookkeeping between
`toCPolyK`/`coeffK`/`toRq`/`toQuotientRow`, three single-slot `IndexMut` facts,
a loop spec for each of the eight extracted loops, and the convolution and
division algebra; no `sorry`, `admit`, `axiom`, `native_decide` or `unsafe`, and
**no `set_option` beyond the two it was submitted with** (`autoImplicit false`,
`maxRecDepth 8192`) -- the first file back from Aristotle that needed no
`maxHeartbeats` override anywhere. Independent re-elaboration over the built
library: 13 s, no errors, no `declaration uses 'sorry'`; a throwaway probe
copy printed the three Lean kernel axioms for all six statements, the loop
spec included.

Promoted by the five steps in `lean-wip/README.md`: `lean/LiftProver.lean`, a
`LiftProver` root in `lakefile.lean` after `Chain`, `import LiftProver` in
`Check.lean`, and five § 4 lines. `make build`: 0 errors, no `sorry`, **191**
headline specs, every one kernel-only. `make spec-check`: 155 mirrored items,
**155 stated, 0 owed**. `cargo test`: green (`chain_semantics` all four
`#[ignore]`d, which is the working tree's own state, not this change).
`lean-wip/` holds only its README again.

Two things from it worth keeping:

* the file carries a **local copy** of `PolyVec::copy`'s loop spec, because the
  promoted file that already proves that shape (`QuadEvalProtocol.lean`) is not
  below it in the import graph. Duplication rather than debt, but the pair
  belongs in `Scheme.lean` before a third file wants it;
* instantiating a general polynomial lemma at `Φ.φ.toPoly` directly makes the
  kernel unfold the concrete degree-`N` modulus and time out. The division
  argument is stated at the abstract `X ^ d + 1` and tied to the modulus by
  rewriting with `phi_toPoly` -- the same move `Ext.lean` needed for
  `ext4Params.d`, and the one to reach for first in any proof that mentions the
  modulus.

**Stage 4's exit criterion is met**, re-checked mechanically rather than
asserted: of the 155 mirrored items, 145 have a `#print axioms` line in § 4 on
a spec that names them, and the other ten are the nine carrier types (`Rq`,
`PolyVec`, `PolyMatrix`, `MlPoly`, `MlEvals`, `Decomp`, `Opening`,
`LiftedWitness`, `QuotientRow`), which are specified by representation
functions rather than by a theorem of their own, plus `QuotientRow::to_rq`,
whose spec is audited under its ArkLib name (`rho_as_rq_spec`). TE's half of
the criterion -- the `Ext4` bridge -- was proved and promoted 2026-09-09. So:
every onboarded operation's headline `_spec` proved and audited, axiom-clean.

One loose end in the plan, not touched here: Stage 5's amended exit paragraph
forward-references a § "Stage 5 — what remains" that does not exist in
`PLAN_PROTOCOL_LAYER.md` or here. The item it points at -- the acceptance test,
an honest transcript that verifies -- is sitting in the working tree as
`the_honest_chain_verifies` (`#[ignore]`d, hours at `m₀ = 26`), so the pointer
wants either that section written or the sentence rewritten to name the test.

## Stage 6 opens: iteration 1 lands two champions (2026-09-14)

The first `perf-loop` iteration this repository has run, on the zero-check
target (`PLAN_STAGE6.md` I1, brief 4). Two candidates, both `opt-algo-swap`,
both accepted on a within-run `CANDIDATE=1` verdict; the ledger has its first
rows and Stage 0's ledger exit closes with them.

**What was actually slow was not what the brief said.** Reading the α-side
bodies before the fan-out: `ringswitch::c_eval_at` computed the specification's
power sum `∑_k φF(p.coeff k) · α^k` with `ext_pow` recomputing `α^k` from scratch
per term -- `N(N−1)/2 ≈ 524 000` extension multiplications per call at `N =
1024`, ~8 ms -- and `c_eval_at_modulus` the same over `N + 1` terms. Every
`m_alpha_tilde` entry is one such call and every `alpha_public_evals` entry five
of them, which is why `zerocheck/zc_target_alpha/5` read 42 ms. It also means
the acceptance test `the_honest_chain_verifies` (previous section) could never
have finished: `alpha_public_table` at `m₀ = 26` is `2^26 × 5` calls, ~10^14
multiplications, weeks rather than the "three hours" estimated on 09-11. That
run's log died with the machine's shutdown the same night, and its verdict was
never recorded; nothing is lost that could have been kept, because there was
nothing to keep.

**Candidate A -- the running power** (`lean/Opt.lean` `c_eval_at.opt`,
`c_eval_at_modulus.opt`; `opt_eq_spec` against `InnerOuter.cEvalAt` through
`cEvalAt_eq_sum_range`, one Opus prover, green on its first typecheck). The
loop threads `pw = α^k` through its state: `2N` multiplications, and the
modulus as a bare running power plus one. Run `20260914T1058+0200-d5a5f55c`,
usable (worst identical-code control 3.9%), six rows all `faster`:
`ringswitch/c_eval_at` 8.35 ms → 20.7 µs, `c_eval_at_modulus` 8.36 ms → 18.1 µs,
`zerocheck/m_alpha_tilde_{matrix,digit}` 8.4 ms → 42 / 25 µs,
`alpha_public_evals` 16.7 ms → 84 µs, `zc_target_alpha` 41.8 ms → 106 µs
(−99.5% to −99.8% after recentering).

**Candidate B -- the row-hoisted table and the layer fold** (`Opt.lean`
`wTableRow`, `blockLoop`/`rowLoop`, `c_w_table_mle.opt`, `h_zero.opt`,
`h_zero_is_zero.opt`, `w_table_mle_eval.opt`; seventeen lemmas, one Opus prover,
green on its first typecheck). Brief 4 item 5 -- the digit branch of `w_table`
rebuilt the whole `rhoDigits` polynomial to read one coefficient, `d = 1024`
times too much work per digit-row entry -- plus item 1, CompPoly's proved
`evalMle` fold in place of the Lagrange dot. The inner loop's second guard
truncates the last block, so the equality with `cWTableMle` holds for every
`m₀`, `μ`, `n` with no hypothesis the specification lacks (and no padding loop:
the `m₀ < 10` case falls out). Rust: a new `w_table_row(w, u) -> Rq` helper
(no `Mirrors` line -- it mirrors this crate's own opt def, not ArkLib -- so the
coverage gate does not pair it with a row), a private `c_w_table_mle_values`
with a running flat index `idx` standing for Lean's `base + l` (a checked
`base + N` would have strengthened `hm0`), and the fold written as hachi's own
loop over `cpoly::multilinear::eval_mle_layer` because `MultilinearEvals::
eval_mle` clones its table and `clone` has no model. Run
`20260914T1134+0200-ae251cad`, usable (6.2%), four rows all `faster`:
`c_w_table_mle/14` 18.9 ms → 40 µs, `h_zero/14` 27.4 ms → 1.05 ms,
`h_zero_is_zero/14` 27.5 ms → 1.03 ms, `w_table_mle_eval/14` 23.5 ms → 520 µs.
What is left in those rows is the range product (`31·2^m₀` multiplications)
and the fold itself.

**Three things the first iteration taught about the instrument.**

* `make run-bench` ran `check-candidate` unconditionally, so a slot holding a
  candidate could never be benched -- the loop's one mode had never been
  exercised. It is now skipped exactly under `CANDIDATE=1` (the report
  fingerprints the slot and prints its sha, which is the attribution that
  matters mid-loop); at rest `make bench-check` still demands a null slot.
* Two of candidate B's runs came back `unusable` (`…1116…` at 30.4% bias,
  `…1126…` at 89.2%) and both were the laptop's power state: the first on
  battery (every control 1.7× slower than the morning run), the second with the
  charger plugged in *during* the first control binary (`commit` 33 → 43 → 62 ms
  across its three variants, every later control within 2%). The harness caught
  both, as designed; the rule for the runbook is **mains power, checked with the
  load average**, before any run. Both runs have a `bench-unusable` ledger row.
* The opt lemmas cannot be imported by the spec files: `Opt.lean` imports
  `ZeroCheck.lean` for the representation layer, so the Aeneas loop proofs
  re-establish the invariants directly and the pure row lemma (`wTableRow`,
  `wTableFlat_eq_row`) moves down into `ZeroCheck.lean`. The lemma in `Opt.lean`
  is still the down payment the contract asks for -- the algebra was settled
  before any Rust existed -- it just is not the object the triple cites.

Extraction after both swaps: deterministic (unchanged on re-run), zero axioms,
the `c_eval_at` loop state `(acc, k) → (acc, pw, k)`, the modulus loop
`(acc, k) → (pw, k)`, `ext_pow` gone, and the table builders as nested loops
with states `(values, u, idx)` / `(values, idx, l)`. `cargo test`: 181 passing
(two new: the row helper against `w_table` on message rows, digit rows and
padding; the truncated cube at `m₀ = 11`). The two new helpers are frozen into
`benches/genesis/src/zerocheck.rs` verbatim and owe their `@genesis` stamps
after the content commit.

**Owed and open.** Brief 4 items 3 and 4 (the `α^ℓ` power table and the hoisted
`M̃_α` table) are cross-call hoists: their win shows only in
`sumcheck::alpha_public_table`, which is excluded by name and has no row. That
row can now be built -- at `m₀ = 14` a REDUCED case is ~1.5 s per sample after
candidate A, where before it was ten minutes -- and it is the row-enabling
step the plan's trap 1 predicts. Until items 3/4 land, `alpha_public_table` at
the pin is still `2^26 × ~6 000` multiplications, about five hours per table,
so the acceptance test stays out of reach; after them it is seconds, and the
test's remaining cost is the sumcheck range factor and `lift_commit`.

**The campaign closed the same day.** One verify-campaign for both champions
(they land in one spec file). Champion review: both swaps conformant, no Rust
change, so no re-extraction; its findings became two tests (the partial block
at `m₀ ∈ {3, 9}`, where `2^m₀ < d` and the inner guard's second conjunct is the
one that fires; the multi-row verdict with a digit row) and doc repairs. Prover
A: the four `c_eval_at` specs restated on the `(acc, pw, k)` / `(pw, k)` states,
headlines verbatim, one typecheck. Prover B: eleven loop specs and two new
helper specs, headlines verbatim, three typechecks; two statement choices worth
keeping -- the inner table specs take an *opaque* `base` with a guarded row
hypothesis (`base + k < 2^m₀ → …`), so `omega` never meets `N * u`, and the
outer specs carry `idx = min (N * u) (2^m₀)`, which is what survives the
truncated final block; and the `w_table_mle_eval` loop invariant is "remaining
work equals the answer" (`mleFold (m₀ − j) (table after j layers) (point from
j) = target`), which is what makes a table of shrinking arity statable at all.
Seven declarations (`lo`, `hi`, `fold`, `tableFn`, `tableFn_apply`, the two
`eval_mle_layer` specs) moved from `Sumcheck.lean` down to `ZeroCheck.lean`
because the import graph runs the other way; Sumcheck already opened the
namespace, so its fifty uses did not move. `make build`: 3872 jobs, no errors,
no `sorry`, **200** § 4 lines (191 headline specs, eight `opt_eq_spec`, the two
new helpers), every one the three kernel axioms. `make spec-check` 155/155/0.
Effort, from the running tally: prover wall time 31 min, ~640 k agent tokens,
zero retries, zero interventions -- K = 1 costs nothing worth relaxing yet.

**The first full run on a committed champion** (`20260914T1238+0200-c27977bb`,
source `2af5297`, usable at 3.9%, `logs/runs/`). Twelve of 87 rows read
`faster` against genesis: the ten rows the two champions touched, at the same
−96% to −99.8% the candidate runs promised; `endpiece/end_piece_check/14` at
**−48%**, which nobody optimized -- it calls `w_table_mle_eval` and inherited
the fold; and `quadeval/vec_in_sb/256` at −5.5%, identical code sitting on the
threshold. Three untouched rows read `slower` by 5–9%: `w_table_z_row` (below
100 ns, the no-verdict band), `rho_digit_as_rq/5` (3.3 µs, its edge) and
`lift_short_check/57344` (+5.4% on 30 ms of identical code) -- the flat floor's
known false positives (§ "The certified null-slot sweep"), recorded here so
nobody reads them as regressions. `make gains` now prints this column beside
the candidate runs' increments.

**The row that items 3 and 4 needed** (`sumcheck/alpha_public_table`, 2026-09-14
afternoon). Excluded by name until today because at any cube its per-entry cost
was `n` quadratic `c_eval_at` calls; with candidate A landed, a REDUCED case
exists. Its size is a lesson worth the sentence: the first attempt at `2^12`
entries with the real `n = 5` measured 0.47 s per champion iteration and never
finished one genesis iteration -- the frozen baseline still has the quadratic
`c_eval_at`, `7.5 ms` a call, and the harness re-measures genesis every run --
so the row is sized from the **genesis** side: `2^7` entries, `n = 2`, one
column, `1.87 s` per genesis iteration, `~100 s` added to every full run (now the
heaviest row; `lift_message` was `~26 s`). Audited by three adversarial lenses
before any number was believed (`rust-bench` § 4): ablating the body to an empty
`Vec` drops the row from 9.7 ms to 0.96 ns; sizes `2^7 → 2^8 → 2^9` scale
1.99× and 2.03×; the operation count (`128 · 4105 + Σ idx = 533 568` Ext4
multiplications) puts the champion at 1.1–2.0× the two anchors' floors and
genesis at 0.9× its own; every input is `black_box`ed and removing the box from
`α` changes nothing, so nothing is folding. Two doc defects fixed (a projected
"150 s" written as if measured; a corpus tag `α` shared with `M[1][0]`) and
two proportions recorded on the case for whoever reads a verdict off it: the
two `c_eval_at` calls are ~98% of the champion's multiplications and
`alpha_tilde` ~1.5%, so item 3 alone would sit under the floor; and with every
entry in row `u = 0` the per-`u` repeat factor is `128` where the pin's is
`1024`, so an item-4 hoist reads ~8× smaller here than at `m₀ = 26`. Recorded
run `20260914T1353+0200-f8559634`: genesis 1.87 s, champion 9.51 ms, −99.5%,
which is candidate A's gain seen from one level up. One more thing the audit
turned up, about two *pre-existing* rows: `zerocheck/m_alpha_tilde_matrix/2`
reads 1.94× `ringswitch/c_eval_at/1024` in the same run although its body is
one `c_eval_at` plus `O(1)` -- the absolute-time artefact class § "The
certified null-slot sweep" already names, and one more reason no claim here
rests on an absolute time.

**Candidate C -- the α-side tables, accepted** (`opt-algo-swap`, brief 4 items 3
and 4; `lean/Opt.lean` § "Candidate C", fourteen lemmas, one Opus prover, green
on its first typecheck). `alpha_public_table` built each of its `2^m₀` entries
from scratch: `alpha_tilde(idx % d)` (up to `d` multiplications), `n` equality
weights, `n` calls of `m_alpha_tilde` -- each a `c_eval_at` over `d`
coefficients -- although every one of those depends only on `ℓ = idx % d`, on
`i`, or on `(i, u = idx / d)`. Now three tables are built once (`α^ℓ` for
`ℓ < d`; the `n` weights; the `n × (μ + n·δ)` matrix `M̃_α`, with `φ(α)` and the
`b^e` powers computed once) and an entry is `pw[ℓ] · Σ_i eqw[i] · mt[i][u]`:
`n` multiplications where the frozen form paid `~n·2d + d/2`. The equality with
`alphaPublicEvals` is unconditional in `m₀`, `n`, `μ`, `m₁`; unstored columns
read as `0`, which `mAlphaTilde` is there. Rust: three new `pub` helpers in
`zerocheck.rs` (`alpha_pow_table`, `eq_weight_table`, `m_alpha_table` -- rows of
rows, as `PolyMatrix` is; no `Mirrors` line, since a table of an ArkLib
function's values is not an ArkLib definition), the `sumcheck::alpha_public_table`
body rewritten with the same signature, three semantics tests, the helpers
frozen verbatim into genesis (stamps owed). Extraction deterministic, zero
axioms; a nested `Vec<Vec<Ext4>>` extracts as two ordinary loops. Single-row
target, so two independent `CANDIDATE=1` runs: `20260914T1401+0200-108de948`
and `20260914T1409+0200-108de948`, both usable (6.3%, 6.8%), both `faster` --
9.51 ms → 87.5 µs and 9.48 ms → 87.6 µs, **−99.1% / −99.0%** recentered. Read
with the row's own caveat: at `2^7` the per-`u` repeat factor is 128 where the
pin's is 1024, so this understates the hoist ~8×. At the pin the α table goes
from about five hours per build to seconds; the acceptance test's remaining
cost is the sumcheck range factor and `lift_commit`.

**Campaign C closed the same afternoon.** Review: bodies conformant, no Rust
change; its one substantive finding was that the rewritten `alpha_public_table`
had no oracle test at all -- `final_check`'s test fed the crate's own table into
both sides of its comparison -- and that the one branch the candidate adds (the
unstored columns `u ≥ μ + n·δ`) never executed below a `2^15` cube, which is
also the only regime the pin is in (`2^26 / 1024 = 65 536 > 57 384`). Now
`alpha_public_table_is_alpha_public_evals_tabulated` probes both. Prover: the
headline `alpha_public_table_spec` byte-identical, six loop specs, three helper
specs, five typechecks, no heartbeat overrides. One trap for the record: at
`n = 0` the extracted `PolyMatrix::cols` reports `0`, not `μ`, so the loop specs
guard `mu.val = μ` by `0 < n` (the row loop derives it from its own guard) and
the headline keeps the frozen statement's silence about `n`. `make build` 3872
jobs green, **205** § 4 lines, all three kernel axioms; `make spec-check`
155/155/0; 187 tests. Three champions, three campaigns, one day; iteration 1's
zero-check target is done and `alpha_public_table` at the pin is seconds, not
hours -- the acceptance test is runnable for the first time.

## Decision: memory walls are a valid reason on their own (2026-09-14)

Found while scoping I2: fusing `lift_message` into `lift_commit` removes a
448 MiB copy, but that copy is < 1% of `lift_commit`'s row and the
`lift_message` row does not change when a caller stops calling it, so the accept
rule -- every target row `faster` -- would reject the plan's own W3 item, and
W1/W2 have the same shape. Three options were weighed: a calibrated peak-memory
metric (a new instrument for two or three changes, poor return, and the paper's
comparison is time anyway -- its README records peak RSS only as a run
condition, 12.7 GiB at ℓ = 30 on this same laptop); leaving the walls to Stage 7;
or a separate acceptance category. **The user chose the category**, with the
time guard kept and the memory figure recorded but not gated: `perf-loop`'s
`accepted-wall` clause (no row `slower`, proof paid as usual, bytes-before →
bytes-after at the pin written into the row, peak RSS if measured, the wall
named). `make gains` will show such rows near zero, which is the truth. Time
stays the primary, strict criterion; memory is recorded because the end-to-end
comparison has to run in 30 GiB. Written into the skill, the ledger validator's
verdict enum, `INSTRUCTIONS.md` and `PLAN_STAGE6.md`; I2 stays queued after I3
under the clause.

## The honest chain verifies at the pin (2026-09-14)

`the_honest_chain_verifies` -- Stage 5's acceptance property, an honest
transcript at `m₀ = 26`, one block, the real digit counts -- ran to completion
for the first time and **passed**: `chain_verify = true` at 2 202 s (36.7 min),
on `c0f8147` with all three iteration-1 champions, on mains, 5.9 GiB resident
at the widest point observed, log in `logs/runs/honest-chain-20260914.log`.
The stage lines: statement 51 s, `R^lin` assembled 68 s (`5 × 40 976`),
`M ζ = y` 375 s, lifted witness 693 s (lift width 41 016), `chain_open`
2 010 s, `chain_verify` 2 202 s. So the honest prover is ~22 min and the
composed verifier ~3 min; the α table that made this test impossible three
days ago (weeks, by the arithmetic in § "Stage 6 opens") is now inside the
noise of those figures. What remains in the 22 minutes is what the plan
already names: the 26 sumcheck rounds' range factor (brief 5, I5) and
`lift_commit`'s 41 016 schoolbook ring products (I4). This is the by-value
completeness check of the composed extracted scheme that the per-link proofs
do not provide; it is `#[ignore]`d for cost and belongs in the runbook after
any change to the protocol layer, run from `logs/runs/`.

**Candidate D, rejected, and what it says about the harness.** The allocation
family's first candidate pre-sized the *outer* vectors (`PolyVec::add`/`sub`'s
`Vec<Rq>`, `lift_message`'s, and `Rq::copy`'s `Vec<Fp>`), a proof-free change
since `with_capacity` is erased by the extraction. Run
`20260914T1534+0200-356088c0`: `lift_message` −10.9% `faster` (57 344 pre-sized
copies), `vec_add`/`vec_sub` −1.7%/−1.2% `noise` -- so `rejected-noise`, nothing
landed. The lesson is where the 4× overhead of `vec_add` over `ring/add`
actually lives: not in growing an 8192-pointer vector, but in `Rq::add`
allocating a fresh 1024-word `Vec` by `Vec::new` + `push` -- ten reallocations,
about twice the data copied -- once per element. The fix is the ring-level
pre-sizing, and there the loop's own rule bites: `ring/add/1024` is 1.1 µs, inside
the 100 ns–2 µs band the certified sweep found false verdicts in, so a candidate
on `Rq::add` cannot be judged on its own row, and the accept rule does not count
its callers' rows. That is the standing harness gap (§ "The certified null-slot
sweep") now blocking a concrete, probably ~3× win on two 40 ms rows; closing it --
a per-band floor from a second, ~1 µs-scale control per binary -- is the next
instrument change worth its cost.

## I2 opens: the lift commitment without its concatenation (2026-09-14)

Candidate E, `opt-inplace-buffers`, the plan's wall W3: `lift_commit` was
`d_key.mat_vec_mul(&lift_message(w))`, and `lift_message` materializes
`z ‖ digits(ρ)` -- 57 384 ring elements, 448 MiB at the pin, 57 344 `Rq::copy`
calls -- for `mat_vec_mul` to read once. Now each output row is accumulated in
place, the `μ` columns of `z` first and the `n·δ` digit columns after, with each
digit polynomial built for the column that reads it (`lift_commit_row`, a new
private helper, frozen; `lean/Opt.lean` § "Candidate E": `lift_commit.opt`,
`opt_eq_spec` unconditional and symbolic in the digit base -- the literal width
`μ + n * 8` makes `whnf` re-run `rhoDigitCount q 16 = 8` and time out, so the
lemma bridges at the triple as the specs do; the column analogue of ArkLib's
`matVecMul_append_rows`). Operation count unchanged; peak inside `lift_commit`
≈ 1.3 GiB → ≈ 896 MiB at the pin (the arithmetic is in the ledger row); one
caveat recorded, the digit polynomials are rebuilt per output row, nothing at
`dRows = 1`. **The first `accepted-wall` row**: run `20260914T1629+0200-f5298aa2`,
`lift_commit/4` +0.5% and `lift_message/57344` +0.9% against the champion, both
`noise`, neither `slower`, bias 2.1% -- the time guard the clause keeps; the
speedup column is honestly nothing, and `make gains` will say so. A merge slip
worth one line: appending a candidate file that carries its own
`end HachiEquiv.Opt` gives "Invalid `end`: There is no current scope to end";
strip it before the build, not after.

Champion review of E: the Rust accepted as written -- operand order exact against
the Lean folds, every checked index covered by the existing `WfMat` and
`hmax` hypotheses, no new precondition -- with a widened oracle test (`dRows = 2`,
`n = 2`, so a row helper that ignored `i` cannot pass) and doc fixes. One
recommendation declined, on the record: hoisting `w.z()` / `w.rho()` out of the
two loop bodies (they are accessor calls, so Aeneas keeps a bind per iteration
where `lift_message`'s field reads hoist) would give the three ringswitch
row-accumulators one shape, but it changes the extracted loop signatures for no
machine-code difference, and the prover was already working against the
current model. Recorded as a shape preference for the next time
`lift_commit_row` is touched, not as debt. One behavioural note worth keeping:
the old `dot` truncated to `min(row, message)` and returned a wrong value on a
key narrower than `μ + n·δ`; the fused body fails there. Inside the spec's
`WfMat` hypothesis the two agree, so the headline statement is unchanged.

**Campaign E closed the same evening.** Three typechecks: the pure column split
re-established in `RingSwitch.lean` as `hachiLiftCom_com_split`, kept symbolic in
`rhoDigitCount q 16` inside the `Fin` index type with `fz`/`fd` abstractions
that turn the loops' `Finset.range` sums into `Fin` sums without rewriting under
a binder -- the shape Opt.lean's own note asked for -- then two row-loop specs
(the digit loop takes the `z` sum as an arbitrary `pre`, which is what makes it a
statement about in-place accumulation), the row spec, the outer loop, and the
headline byte-identical. `make build` 3872 jobs, **208** § 4 lines, three kernel
axioms each; `make spec-check` 155/155/0; 187 tests. **I2 is closed**: W3 is
down, `lift_commit` no longer builds the 448 MiB vector, and the ledger's first
`accepted-wall` row has its campaign row beside it (13 min of prover wall
time). What I2 leaves is the `lift_message` row itself, a copy at the
translation ceiling's floor whose headroom is the ring-level pre-sizing on the
evening list.

## Where the honest prover's minutes go, measured (2026-09-14 evening)

`the_honest_chain_profile` (new, `#[ignore]`d): the acceptance instance at one
block, `chain_open` replayed piece by piece with a timer around each, then the
verifier whole. Run on `85e7917` +uncommitted (candidates A–C committed, E in the
tree), log `logs/runs/honest-chain-profile-20260914.log`, `chain_verify = true`:

| piece | time |
|---|---|
| `rlin_stmt` | 0.5 s |
| `lift_commit` (41 016 ring products) | 62 s |
| `c_w_table_mle` at `2^26` | 0.8 s |
| `alpha_public_table` at `2^26` | 12.5 s |
| `honest_round_messages` (26 rounds, incl. its own two tables) | **1 201 s** |
| `honest_compute_y` | 4 s |
| `chain_verify` | 202 s |

So the prover is **the rounds, by twenty to one** over `lift_commit`; the two
`2^26` tables that were weeks and minutes this morning are 13 s together. That
settles the queue order the plan left to measurement: I5 (brief 5's range
factor, 94% of a round by its own count) before I4 (`ring::mul`), whose share
of the prover is one minute -- I4's weight is in `commit` and in the test's own
setup checks (`M ζ = y` and the honest lift are five minutes each, both
200 000-product matrix-vector products). The verifier's 202 s is worth a
profile of its own before I5 closes: `final_check` builds the α table (12.5 s)
and evaluates it, `end_piece_check` recomputes `lift_commit` (62 s) and the
witness evaluation, and the round checks are cheap -- roughly 120 s of it is
unaccounted by those figures and is probably the verifier-side `alpha_contract`
(`m_alpha_tilde` per table cell, brief 4 item 4 on the *verifier* path).

**The stray probe is gone.** `hachi/src/main.rs` -- a plain-`Instant` ratio
probe of the ringswitch bench cases' cost relations, left behind on 2026-09-07
(`9ae732b`) -- is removed (evening list item 4). `Cargo.toml`'s own comment
beside `autobins = false` says why a probe must not stay in `src/`: with
`autobins` on it would be a bench target and a second crate root for charon.
It was inert under the flag and never part of the extraction or the frozen
modules; its readings were sizing information for the 09-07 bench cases and are
recoverable from git history if ever wanted.

**Candidate D2, the ring-level pre-sizing, accepted under the band reading
rule** (run `20260914T1830+0200-7b74c3a3`, bias 1.7%). The rule, decided the
same evening and written into `perf-loop` step 5: a callee whose own rows sit in
the 100 ns–2 µs band is judged on the caller rows it dominates by arithmetic,
every one of which must read `faster`; its own rows are recorded, not judged.
Here the items are `Rq::{constant, from_coeffs, copy, add, sub, neg,
scalar_mul}` -- not `Rq::zero`, which is the harness control's body and must
stay identical code across the variants, and not `Rq::mul`, whose rows are
mul-bound -- plus `PolyVec::{add, sub}` and `lift_message`'s outer vector. The
evidence rows: `vec_add` −12.7%, `vec_sub` −17.4%, `flatten_blocks` −14.2%,
`lift_message` −10.0%; the recorded ring rows −19% to −28%. Honest reading of
the size: candidate D's post-mortem hoped for ~3× on `vec_add` and got 13%,
because the reallocation growth was a seventh of the row, not its bulk --
`vec_add` still costs 36 ms against 7 ms of arithmetic, and what remains is one
8 KiB allocation and free per element plus the cache traffic of touching a
fresh buffer each time. The lever for that is not allocating per element
(accumulate into a caller-sized buffer), which changes the Lean definition's
shape and is `opt-inplace-buffers`' third move, for a later candidate. The
model gained 18 `with_capacity` binds, each definitionally `Vec.new`; the
campaign is expected to be `simp only [alloc.vec.Vec.with_capacity]` repairs.

**Campaign D2 closed in minutes.** Eighteen `with_capacity` binds entered the
model and one proof noticed: `lift_message_spec`, whose body gained a checked
`z_len + rho_len` before the buffer -- one `step` (its overflow goal discharged
from `hmax` by `step` itself) and a `simp only [alloc.vec.Vec.with_capacity]`.
Every other spec unified through the definitional equality without a change.
`make build` 3872 jobs, 208 § 4 lines; 187 tests; `spec-check` 155/155/0. The
evening list is done except for the commits: the band rule written, D2
accepted and verified, the plan's forward reference rewritten, the stray probe
removed, brief 5's re-base in progress.

## I5 opens with a mixed verdict, and the verdict is the finding (2026-09-14, night)

Candidate F, brief 5's S5: `rangeProduct b v = v · ∏ (v − j)(v + j)` written as
`v · ∏ (v² − j²)`, one squaring then fifteen multiplications by a base-field
literal difference -- 16 extension multiplications instead of 30, no
additions; `range_product.opt_eq_spec` unconditional in `b`, `lean/Opt.lean`
§ "Candidate F", proved in six minutes. Its own row is in the band, so under
the evening's reading rule it was judged on six caller rows (run
`20260914T2014+0200-708424de`, bias 2.3%). The four sumcheck rows read
**−20%** (`honest_compute_g`, `round_poly_zero`, `round_values_zero`,
`round_value_zero`; the count promised 47% -- the rows also carry the fold and
`eq̃` work). The two zero-check table rows read **+450%**: `h_zero` 1.05 → 5.75 ms.
`rejected-mixed`, and the rule's instruction to surface a mixed row paid off:
the champion's `h_zero` pays ~64 ns per range factor against the standalone
row's 470 ns because every input it feeds is `Ext4::from_base` of a coefficient
-- three coordinates zero -- and after inlining the compiler folds the zeros
through the frozen `(v − s)(v + s)` chain; the new body loses that folding and
`h_zero` falls to the general cost, `16 384 × 348 ns`. Real, within-run, not a
layout effect. What it says is algebraic, not compiler-shaped: the table
builders' inputs are base-field values, `φF` is a ring homomorphism, so
`rangeProduct b (φF x) = φF (rangeProduct_base b x)` -- sixteen base-field
multiplications at about a nanosecond each, then one embedding. That is
candidate G (in flight), after which `h_zero` no longer calls the extension
range factor and F re-runs on the sumcheck rows alone. Brief 5's new S7′ --
round 0 of the sumcheck multiplies base-field values through the full quartic
multiply, half of all base-field multiplications in the prover -- is the same
observation one level up. The Lean lemma of F stays in `Opt.lean`; the Rust
swap did not land.

**Candidate G, accepted: the table builders compute the range factor in the
base field.** `φF` is a ring homomorphism, so `rangeProduct b (φF x) =
φF (rangeProduct_base b x)`, and the zero test needs no embedding at all
(`φF` is injective). `lean/Opt.lean` § "Candidate G": `range_product_base.opt`
over `ZMod q` in candidate F's `x² − j²` shape, the bridge
`phiF_range_product_base`, `phiF_eq_zero_iff`, and sibling table loops
`blockLoopBase`/`rowLoopBase` that apply a `ZMod q → F` map to the coefficient
itself (candidate B's loops apply their map *after* `φF`, so they could not
express this) -- sixteen lemmas, one Opus prover. Rust: `range_product_base(c:
Fp) -> Fp` (sixteen base-field multiplications, frozen into genesis, stamp
owed), one line changed in each of `h_zero` and `h_zero_is_zero`, a semantics
test on random coefficients, the whole symmetric range and just outside it.
Run `20260914T2052+0200-04d6ef1a`, bias 2.4%: `h_zero/14` 1.05 ms → 432 µs
(**−59.4%**), `h_zero_is_zero/14` 1.02 ms → 391 µs (**−62.4%**); the prover
had predicted −25% to −40% because the champion already benefited from the
compiler's zero-coordinate folding. Campaign: two inner-loop specs re-proved
with the per-entry step moved to the `Fp` specs, `range_product_base_spec`
new, `phiF_eq_zero_iff` moved from `Opt.lean` down to `ZeroCheck.lean`
(a duplicate would have made the bare name ambiguous), two typechecks.
Candidate F's re-run on the sumcheck rows alone is **blocked by the stamp
mechanics**: `run-bench` opens with `check-genesis`, `range_product_base` is
frozen but cannot be stamped before a commit, and setting the block aside
fails the gate from the other side ("no frozen counterpart"). A back-to-back
pair of champions in one module costs a commit round-trip; recorded in
`perf-loop`.

**Candidate F, accepted on its second run** (`20260914T2321+0200-3ad39fb4`,
bias 4.0%): with the table builders moved off the extension-field range factor
by candidate G, F's evidence rows are the four sumcheck rows it dominates --
`honest_compute_g` −18.7%, `round_poly_zero` −19.0%, `round_value_zero` −19.3%,
`round_values_zero` −19.2% -- and `h_zero`/`h_zero_is_zero`, kept in the run as
controls, read noise as they should now that they call `range_product_base`.
The count promised 47% on the range factor; the rows carry the fold and `eq̃`
work too, so about 19% of a round, which at the pin is about 19% of the
prover's 1 201 s. The pair F+G is I5's first step: the same identity applied
twice, once in each field, judged on the rows each actually moves. What the
mixed verdict cost was one extra bench run and one candidate; what it bought
was G, worth 60% on two rows, and the observation behind brief 5's S7′.

**Brief 6 re-based (2026-09-14, night)** -- the last brief at the old pin. 187
citations re-resolved, three deleted ArkLib declarations replaced by their
successors, the τ-impossibility argument retired (PR #847 deleted the `hqz`
hypothesis and pins τ = 5), two erroneous claims fixed (`Ext4` equality is the
derived `PartialEq`; the cube is 2.0 GiB, not 4.29 GB). Cost model at the pin:
`end_piece_check` ≈ 85–92 s, **96% of it conjunct A** -- the 57 384 `ring::mul`s
of the recomputed `lift_commit` -- which validates against the row to 0.5%
and against the profile's `lift_commit` to 5%. Two things it settles for the
queue: **the recomputation cannot be taken away** -- conjunct A *is*
`K.com w == stmt.t`, the binding content of the closing link (`EndPiece/
Reduction.lean:146`, `FinalEval.lean:163`), so target 6's lever is I4's
`ring::mul` and nothing local; and the verifier's ~120 s unaccounted in the
prover profile is **not** the per-cell `m_alpha_tilde` I guessed (candidate C
hoisted it; the whole `alpha_public_table` is *measured* at 12.5 s) but most
likely **`final_check`'s `MultilinearEvals::eval`** -- still the Lagrange-dot
form over the `2^26` α table, `1.8·10⁹` Ext4 multiplications and a 2 GiB basis,
the same shape candidate B deleted from the witness side. Its removal is the
one-line `eval → evalMle` swap under `eval_mle_eq_eval`; the overnight verifier
profile will say whether the count is right. Also noted, read-only: three
stale statements in `hachi/benches/endpiece.rs` (pre-B/E wording, "not yet
measured" on a measured row) and that file's local "W1/W2" naming collides
with the plan's W1–W4 -- a doc pass for tomorrow.

## The overnight runs (2026-09-14 → 15)

**Run 1, the profile with the verifier split, completed** (log
`logs/runs/overnight-20260914.log`, on `42f6dea` + candidate F in the tree,
`chain_verify = true`):

| piece | time |
|---|---|
| `lift_commit` | 57 s |
| `c_w_table_mle` / `alpha_public_table` at `2^26` | 0.8 s / 12.6 s |
| `honest_round_messages` (26 rounds) | **920 s** (1 201 s before F: −23%) |
| `honest_compute_y` | 3.9 s |
| verifier: `R^lin` + statement thread | 0.35 s |
| verifier: `round_verify_loop` (26 checks) | 66 µs |
| verifier: **`final_check`** | **99 s** |
| verifier: `end_piece_check` | 62 s |
| `chain_verify` whole (control) | 190 s |

Brief 6's count was right: the verifier's unaccounted minutes are
`final_check`, and inside it the only work of that size is `MultilinearEvals::
eval` -- the Lagrange dot over the `2^26` α table, `1.8·10⁹` Ext4
multiplications and a 2 GiB basis (the α table itself is 12.6 s). That is
**candidate H**: the `eval → evalMle` swap candidate B made on the witness
side, one line, `eval_mle_eq_eval`; it needs a REDUCED `sumcheck/final_check`
row first. `end_piece_check`'s 62 s is the recomputed `lift_commit`, the check
itself (brief 6), I4's lever. The prover after F is 920 s of rounds against
57 s of `lift_commit`: I5 remains the queue's head (S7′ next).

**Run 2, the 128-block end-to-end, was killed by the system for memory** before
its first stage line: the machine had ~15 GiB free (a Lean server, a Rust
analyzer and a browser hold the rest), and the 128-block instance -- 1 GiB of
message, 8 GiB of digit decomposition, the inner decompositions, the `R^lin`
statement and the tables -- wanted more. So W4 bites at 128 blocks already on
this machine as it was configured overnight. Options for the Stage 7 fallback:
64 blocks (≈4 GiB of decomposition), or the same run with the editor's Lean
server and the browser closed. A decision for the user, not taken here.

## The honest chain verifies at 64 blocks (2026-09-15, Stage 7 route 1)

The user chose 64 blocks over 128 (64 is enough for the scaling point; 128
buys nothing the arithmetic does not give). Log
`logs/runs/honest-chain-64blocks-20260915.log`, on `858fe3d` with `hachi/src`
at HEAD, AC power, the machine otherwise idle.

**Run 1 failed after 24.7 minutes, and the failure was the test's.**
`pin_instance` built the QuadEval challenge `c` as a single ternary ring
element, while `honest_z` folds message block `i` against `c.get(i)`: at 64
blocks the second block indexed past the end (`linalg.rs:92`, "the len is 1
but the index is 1"). The `HACHI_CHAIN_BLOCKS` parameterisation of 09-14 had
sized everything by `blocks` except that vector; the 1-block acceptance test
could never see it, and the 128-block attempt died of memory before reaching
it. The other instance builder in the same file already drew
`c: r.next_poly_vec(s.blocks)`. Fixed by sizing `c` by `blocks`; nothing in
the crate changed.

**Run 2 passed: `chain_verify = true` in 4 180 s (69.7 min).** The phase
times, against the 1-block acceptance run of 09-14 (2 202 s, pre-F):

| phase | 64 blocks | 1 block | scaling |
|---|---|---|---|
| `commit::commit` | 760 s | 12 s | ×63 -- linear in blocks (`ring::mul` bound) |
| statement (`dense_eval`, the test's own oracle) | 505 s | 36 s | ×14 |
| `honest_compute_v` | 99 s | 3 s | ×33 |
| `honest_compute_resp` + `stack` (`honest_z`) | 850 s | -- | the brief-2 wall, now measured |
| `R^lin` assembled | 1 s, `5 × 41 984` | `5 × 40 976` | 48 columns per block |
| `M ζ = y` check | 300 s | 307 s | flat |
| `honest_lift_witness` | 310 s, width 42 024 | 318 s | flat |
| `chain_open` | 1 154 s | 1 317 s (920 s of rounds after F) | flat -- the cube is `m₀ = 26` either way |
| `chain_verify` | 200 s | 192 s | flat |

Resident memory read at 46 min (the `M ζ = y` phase): 12.2 GiB; the peak was
not sampled and is at least that. Two readings:

* **W4 is now a number, not a projection.** Every block-scaled phase above is
  `ring::mul`-bound schoolbook work (`commit`, `honest_z`, `honest_compute_v`),
  and together they are 1 710 s of the 4 180 -- already more than the whole
  prover. At the pin's 1 024 blocks the same phases extrapolate to ~7.6 h
  (commit 3.4 h, `honest_z` 3.8 h) on top of the 64 GiB decomposition; so the
  end-to-end at the pin is I4's (`ring::mul`) and W2's (lazy `R^lin`) problem
  before it is a memory problem, and the reduced-blocks route remains the way
  to a measured end-to-end on this machine.
* **Against the reference implementation** (`logs/paper-impl/README.md`), this
  instance is the `ℓ = 26` shape (`2^6` blocks of `2^10` rows, `d = 1024`):
  reference wall 94 s, ours 4 180 s (×44). Piecewise: commit 6.5 s vs 760 s
  (×117, NTT vs schoolbook -- the `ring/mul` gap the brief predicted); prove
  84.5 s vs ~2 300 s (`honest_z` + lift + `chain_open`); verify 28 ms vs 200 s
  -- ours recomputes `lift_commit` and evaluates the `2^26` α table
  (candidates H and the I4 lever), and our sumcheck runs at the pin's `m₀ = 26`
  where the reference's shrinks with `ℓ`. Stage 7's span comparison is the
  formal version of this paragraph; this is its first data point.

## Candidate I: round 0 of the sumcheck in the base field (2026-09-15)

Brief 5's S7′, ranked second after the range factor. At round 0 every entry of
`w̃` is `φF` of a witness coefficient, the 33 nodes are embedded integers and the
range factor's constants are embedded integers, so the zero side of the first
round message -- `Σ_y eq[y] · P_b((1 − T)·w[2y] + T·w[2y+1])` -- is base-field
arithmetic performed through the quartic multiply, 19 `Fp` multiplications
where one would do. Only `eq[y]` (a function of the challenge `τ₀`) is a genuine
extension element, and `Fp × Ext4` is four `Fp` multiplications. From round 1
on the challenge is a genuine `Ext4` and nothing changes.

**The candidate** (`lean/Opt.lean` § "Candidate I", eleven lemmas, prover agent,
one iteration): `foldBase`, `rangeSumZeroBase`, `roundValuesZeroBase`,
`evalMleLayerBase`, `linSumAlphaBase`, each proved equal to the extension-field
expression the existing hachi spec concludes (`rangeSumZero`, `fold`,
`linSumAlpha`) on the embedded table at the embedded node. Two operand orders
are fixed by the definitions and kept verbatim in the Rust, because they select
`impl Mul<Ext4> for Fp`: `p * eq[y]` and `lo * one_minus + hi * x0`. The Rust:
`zerocheck::c_w_table_fp` (the row-blocked table as `Vec<Fp>`), the
`round_{value,values,poly}_{zero,alpha}_base` sextet, `eval_mle_layer_base`
(the one mixed fold), `honest_compute_g_base`, and `honest_round_messages` with
round 0 peeled behind `0 < m₀`. `Opt.lean` now imports `Sumcheck`.

**The row had to be built first.** The per-round rows measure a generic round
and cannot see a change confined to round 0, and `honest_round_messages` was
excluded by name ("infeasible even REDUCED"). It is not: at `m₀ = 11` round 0
folds exactly `HALF = 1024` pairs, the same shape as the per-round rows, and
the champion runs in 29.5 ms. What is expensive is the **genesis** variant,
14.8 s per iteration -- and not for the reason first written down. With
`RING_DEGREE = 1024` the 2 048 cube entries have `u = idx / d ∈ {0, 1}`, so
1 024 of them take the frozen quadratic `c_eval_at` and 1 024 the frozen
quadratic `c_eval_at_modulus`, ~7 ms each; the first projection of "~4 s from
576 non-padding entries" had used `d = 64`. The adversarial review of the row
(three lenses, read-only during the run) reconciled the champion's 29.5 ms
against the per-round rows to 0.1%, confirmed setup and digest outside the timed
region, and refuted three of the row's comments -- the `d = 64` arithmetic, a
witness-sizing claim (only rows `u = 0, 1` are read; the quotient row is never
reached), and a stale "the α table is a third of the row" (it is 0.5% since
candidate C). All three are corrected in the file. Its `vs genesis` (−99.8%) is
**not** a sumcheck figure: it is the frozen quadratic evaluation one layer down.

**Accepted on two independent runs** (single-row target):

| run | now | candidate | recentered | bias |
|---|---|---|---|---|
| `20260915T1008+0200-7cd34c7b` | 29.5 ms | 17.5 ms | **−40.7%** | 3.3% |
| `20260915T1029+0200-7cd34c7b` | 29.6 ms | 17.5 ms | **−41.0%** | 5.5% |

Round 0 is half of the fold work at any `m₀` (`2^{m₀−1}` of `2^{m₀} − 1`
pairs), so the reduction does not distort its share, and the reading transfers
to the pin: `honest_round_messages` 920 s → ≈ 550 s projected. Realized round-0
gain ≈ 8× against a ~17× count ratio (726 vs 12 540 `Fp` multiplications per
cube point on the post-F champion): `range_product_base` is a serial dependent
chain of 15 multiply-and-reduce steps, latency-bound where the quartic path was
throughput-bound. The layer-0 table is now 512 MiB instead of 2 GiB at the pin,
a side effect recorded as arithmetic, not a wall claim.

Extraction: deterministic, zero axioms, `Mul<Ext4> for Fp` arrives as a real
body (`cpoly.field.Fp.Insts.CoreOpsArithMulExt4Ext4.mul`, four `Fp.mul`s), one
new `(out, j)` loop shape. The nine new items are frozen into genesis; their
stamps are owed after the content commit. Ledger row 17. Campaign: the headline
`honest_round_messages_spec` verbatim with round 0 peeled in the proof, plus
specs for the nine new items and the mixed multiply.

**A procedural note.** Candidate G's unstamped helper blocked candidate F's
re-run on 09-14 because G had already landed in `hachi/src`. Here the candidate
stayed in the slot with `hachi/src` at HEAD during both runs -- the ordinary
restore step -- and `check-genesis`, whose live set is read from `hachi/src`,
had nothing to complain about. New helpers block the *next* candidate only once
their champion has landed unstamped; the standing rule is unchanged, the
sequencing is what avoids it.

**Campaign closed the same day (2026-09-15, ~11:50).** Headline
`honest_round_messages_spec` carried verbatim (statement byte-diffed), proof
restated with round 0 peeled and the loop state re-indexed to
`(a_tab, current, out, w_tab, i)`; `fold_tableFn_eq_mle` and `round_node_spec`
carried verbatim with rerouted proofs. New: `fp_ext_mul_spec` for the mixed
multiply (with a `Check.lean` § 2 pin of its four-`Fp.mul` body), the `Vec<Fp>`
table carrier `WfEvalsFp`/`tableFnFp`, `c_w_table_fp_spec`, the eight `_base`
specs (five of them loop specs), `eval_mle_layer_base_table_spec`,
`initial_w_table_fp`, `honest_compute_g_base_spec` (its twin at `i = 0`, one
free hypothesis fewer). No statement weakened, nothing moved out of `Opt.lean`.
Effort: two prover agents (the first stopped by accident ten minutes in; its
Ext/ZeroCheck additions compiled as written), 31 minutes end to end for the
second, 2 typecheck iterations, 1 retry. `make build` green, 235 § 4 lines,
`spec-check` 155/155/0, `lean-wip/` empty. Two API facts the prover recorded:
`(0#usize).val` is `0` by `rfl`, so the round-0 specs need no `Fin`-arity
transport; and `fold (φF ∘ tableFnFp t) T y` unfolds to its two-coefficient
form by `rfl`. Ledger rows 17 (candidate) and 18 (campaign).

## A correction to the verifier profile: `final_check` has two `2^m₀` walls, not one (2026-09-15)

§ "The overnight runs" attributed `final_check`'s 99 s to the α table and its
Lagrange dot. Candidate J's prover agent, reading `Generated.lean`, found the
second half: cpoly's `eq_tilde(w, x)` is `lagrange_basis(w).eval(x)`
(`cpoly/src/multilinear.rs:248`), and `eval` builds a second Lagrange basis, so
the `eq̃(τ₀, a)` factor of the range claim costs two `2^m₀` bases and a dot of
its own -- another 2 GiB and `≈ 2·10⁹` multiplications at the pin. Brief 5 had
recorded S3 ("the closed-form `eq̃`") as *paid in Rust* on the strength of the
name; it was not, and the brief is corrected. So S4's verifier half (candidate
J) removes the α half of the 99 s, and the other half is one line away:
hachi's own `eq_prefix` over the whole of `τ₀` is the `m₀`-factor closed form
and `eq_prefix_spec` already concludes the `eqProd` that `eq_tilde_spec`
does. That swap is proposed as candidate K, on the same `sumcheck/final_check`
row, after J's verdict -- kept separate so that each strategy's number is its
own.

## Candidate J: the tensor split of `Ã`, verifier half (2026-09-15, afternoon)

Brief 5's S4, the last of its three levers. `alphaPublicEvals` at the flat
index `idx` is `α^{idx % d} · Σᵢ eq̃(τ₁, i)·M̃_α(i, idx / d)`, and the flat index
is little-endian in the cube coordinates, so with `d = 2^10` the table is a
tensor product of a function of the low ten coordinates and a function of the
high `m₀ − 10`, and its multilinear extension at a point is the product of two
small extensions. `sumcheck::alpha_public_mle_eval` computes exactly that: a
`2^k`-entry table of powers of `α` folded over `a[0..k]`, a `2^{m₀−k}`-entry
table of row-contracted matrix values folded over `a[k..]`, `k = min(m₀, 10)`,
one product. `final_check` calls it in place of building the `2^m₀` table and
taking cpoly's Lagrange dot. Lean: `mle_tensor_split` (the MLE of a
tensor-product table factorizes; cube split by an explicit equivalence, the
little-endian index split from `finFunctionFinEquiv_apply`) and
`alpha_public_mle_eval.opt_eq_spec`, unconditional in `m₀` -- below `d` the
whole cube is the low factor and the high table is one entry. Prover agent, one
iteration, fourteen lemmas clean.

**The row.** `sumcheck/final_check/11`, the smallest cube at which both factors
are non-trivial. `final_check` returns a `bool`, so its digest is a void oracle
(`|_| true` would digest identically); the row therefore carries its oracle in
`check()`, which in every variant's own crate demands acceptance of the honest
statement and rejection of each conjunct moved on its own, and the honest
targets are computed the pre-J way (tabulated `Ã`, cpoly `eval`) so that for
the candidate they are an independent computation of the value the split must
reproduce. The statement is honest so that all three conjuncts run; a random
one would stop at the first `&&`.

**Accepted on two runs**: −31.2% (bias 8.5%, the browser holding two cores)
and −32.1% (bias 3.5%). The absolute row times differed by 1.9× between the
runs (1.68 ms vs 3.14 ms for the champion) because the CPU sat at 2.0 GHz
under the browser's load in the first and 3.3 GHz in the second -- a live
example of why an absolute time is not comparable across runs and the
within-run ratio is. Not the projected −94%, and the reason is the finding
recorded in § "A correction to the verifier profile": the equality factor is
the other half of the row and of the pin's 99 s, and it is candidate K. New
item frozen into genesis with its own row `sumcheck/alpha_public_mle_eval/26`
at the real cube on a REDUCED statement; stamp owed. Ledger row 19.

**Campaign J closed (2026-09-15, ~14:20).** `final_check_spec` carried verbatim
(byte-diffed), its proof now stepping through the new
`alpha_public_mle_eval_spec` instead of the tabulated table, the Lagrange basis
and the dot. Five positional loop specs for the new item, two of them proved by
`rfl` transport because the extracted loops are byte-identical to
`alpha_public_table`'s. The pure tensor-split lemmas moved down from `Opt.lean`
into `Sumcheck.lean`, the house pattern; `Opt.lean`'s `opt_eq_spec` now reuses
them. 26 minutes, two typecheck iterations, no retries, no intervention. Build
green at 240 § 4 lines, `spec-check` 155/155/0. Ledger row 20.

## Candidate K: the equality factor in closed form (2026-09-15, afternoon)

The other half of § "A correction to the verifier profile". One line in
`final_check`: hachi's own `eq_prefix` over the whole of `τ₀` -- `m₀` factors
`τ_k·a_k + (1 − τ_k)(1 − a_k)` -- in place of cpoly's `eq_tilde`, which is
`lagrange_basis(w).eval(x)` and so builds two `2^m₀` bases and a dot for a
value that is a product of `m₀` terms. No new item, no new Lean: the algebra is
the `eqProd` characterization both `eq_prefix_spec` and `eq_tilde_spec` already
concluded, and a test pins the closed form against cpoly's form and the test
file's reference. Approved by the user as its own candidate, after J, so that
each strategy keeps its own number.

**Accepted on two runs against champion J**: −87.9% (bias 4.6%) and −87.8%
(bias 5.8%); the row went from 807 µs to 98 µs. J and K together take
`final_check` from the two `2^m₀` walls it had -- at the pin two 2 GiB tables
and two 2 GiB bases, 99 s -- to two small folds and `m₀` factors, milliseconds
and about 2 MiB. The verifier's 190 s becomes about 90 s projected; what is left
is `end_piece_check` recomputing the lift commitment, which is the multiplier's
(I4). Ledger row 21.

**What the extraction did.** With `eq_tilde` gone, the crate no longer reaches
cpoly's `lagrange_basis`, `dot`, `MultilinearEvals::eval`, `table_len`, nor the
`AddAssign`/`MulAssign` impls on `Ext4` those used, and all of them left the
model -- "the model contains what the crate reaches". Their Aeneas specs
(`eq_tilde_spec`, `cpoly_lagrange_basis_spec`, `cpoly_dot_spec`, the assign
specs) cannot be stated any more and go with them; a spec about code the crate
does not contain is not proof debt, it is a statement about nothing. The
campaign records which declarations left.

**Campaign K closed (2026-09-15, ~15:45).** `final_check_spec` carried verbatim;
its first step now `eq_prefix_spec` at `i = m₀`, where `Fin.castLE le_rfl`
collapses by `rfl`. Nine specs deleted with the code they specified --
`eq_tilde_spec`, the `lagrange_basis` and `dot` loop specs, `table_len`, the two
`Ext4` assign specs -- and two pure helpers that served only the first; hachi's
own `evalsplit::lagrange_basis` and `linalg::dot` specs, and the pure
`lagrangeBasis` lemmas still in use, stay. Ten minutes, no retries. Build green
at 238 § 4 lines, `spec-check` 155/155/0. Ledger row 22. With J and K the
verifier side of I5 is closed; the prover half of S4, the α table carried as
two factors through the rounds under the wall rule, is what remains of brief 5.

## Candidate L: the α table carried as two factors -- wall W1 down (2026-09-15, late afternoon)

The prover half of brief 5's S4, and the last of that brief's three levers. The
public table `Ã` at round 0 is the tensor product `L(idx % 2^10) · H(idx / 2^10)`
that candidate J evaluated; the fold of the least-significant coordinate
commutes with that structure -- it acts on `L` while `L` has more than one
entry, and on `H` once `L` is a scalar -- so the prover carries `(low, high)`
through every round and reads `Ã[j]` as `low[j % L] · high[j / L]`. Eleven new
items (`alpha_split_low`/`_high`, `alpha_split_fold`, the `_split` round pieces
on both the extension and the base-field witness table, `honest_compute_g_split`
and its round-0 sibling); `honest_round_messages` never builds `Ã`;
`round_loop`, the fused reference reduction, is left on the flat table on
purpose so the tests keep an independent oracle. Lean: eleven lemmas, chief
among them `fold_tensorTable_low`/`_scalar` and `linSumAlpha_tensor`, delivered
in `Opt.lean` § L and moved down into `Sumcheck.lean` by the campaign staging
(only `honest_round_messages.opt_eq_spec` stays in `Opt.lean`); the tensor
index is written high-exponent-first so the fold lemmas carry no casts.

**Accepted under the wall rule** on run `20260915T1615+0200-3277d79f`: the
`sumcheck/honest_round_messages/11` row read +0.4% raw, −0.07% recentered,
`noise` at a 1.7% control -- the predicted one extra multiplication per α read
is about 1% of a round and sits inside the control. No row slower. The memory
gain, recorded as arithmetic: `2^26 · 32 B = 2 GiB` → `(2^10 + 2^16) · 32 B =
2.03 MiB`, 1008×, and the per-round fold work on `Ã` shrinks from `≈ 2^{m₀+1}`
steps to `2·(2^10 + 2^{m₀−10})`. Tests: the two factors tensor to
`alpha_public_table` at five cubes; every split piece equals its flat original
through eleven rounds including the crossover from `low` to `high`; the peeled
prover equals the unpeeled loop. Ledger row 23. **Brief 5's list is now
exhausted** except its sub-5% items (S5b, S5c, S11).

**The first campaign under the new process.** From here the campaign proofs go
to Aristotle, run by the user: the restated `honest_round_messages_spec` keeps
its statement verbatim, its body becomes `sorry`, and its previous proof stays
verbatim in a comment beneath it with a note on what moved in the model (the
loop state, the `hav` invariant), so that the remote prover adapts a route
rather than rediscovering one; each new `_split` stub names its flat twin.
The working tree carries those sorries until the session returns, and nothing
is committed in that state.

**Campaign L closed by Aristotle (2026-09-15, evening).** The first campaign
under the new division of labour: a local agent staged the statements -- the
headline `honest_round_messages_spec` verbatim with `sorry` and its previous
proof kept in a comment beneath a re-route note, nineteen new `_split` stubs
each naming its flat twin, and the pure tensor lemmas moved down from
`Opt.lean` -- and Aristotle session `aba005e6` took the twenty obligations to
zero (submitted 17:41, complete by the user's evening check after three
in-progress checks). Integrated by `/aristotle-check` after Lean validation;
here the full build then confirmed it: 3872 jobs green, **263** § 4 lines all
at the three kernel axioms, no `sorry` under `lean/`, `spec-check` 155/155/0,
and none of the 141 pre-existing theorem statements in `Sumcheck.lean` moved.
Four small specs had been proved locally beforehand by `rfl` transport where
the extracted loops were byte-identical to `alpha_public_mle_eval`'s. Ledger
row 24. **I5 is closed**: brief 5's three levers (F, I, J+K+L) have all landed.

## The AeneasCompPoly optimization brief, checked item by item (2026-09-15, night)

An external brief (`AENEASCOMPOLY_OPTIMIZATION_AGENT_BRIEF.md`, written against
`ErVinuelas/AeneasArklib` and `tobias-rothmann/AeneasCompPoly`) proposed adopting
upstream cpoly's recent optimization work. It was checked against the tree
rather than taken on trust, and the check changed the queue. What it got right,
what it got wrong, and what it cost:

**Already paid.** Its §7 (replace `lagrange_basis(w).eval(x)` with the direct
equality kernel) is candidate K. Its §2 running powers are candidate A --
including `c_eval_at_modulus` (`ringswitch.rs:351`), which the brief believed
still recomputed a power per term and which has been a running-power loop since
iteration 1.

**Its headline item is our own sub-5% tail.** The brief's §5 -- the affine fold
`(1-x)·lo + x·hi = lo + x·(hi-lo)` -- is brief 5's **S5b**
(`briefs/target-5-sumcheck.md:1054`, `:1133`), already priced there at
1 104 → 1 071 `Ext4` mults (3.0%), and **5.4%** after S5 landed as F/G. That is
at the harness's 5% floor. Counting multiplications inside
`round_value_alpha_split` alone reads −29%, which is how the brief's estimate
and a first reading here both went wrong; the target's work is 94% range
product, so the weighted figure is brief 5's and brief 5's stands. Two further
corrections in the same item: the brief's per-pair count (5 → 3) omits the two
tensor products candidate L introduced, so the live count is 7 → 5; and brief 5
records what the brief misses, that the saving needs the **loop interchange**
(point-outer, node-inner) to share `hi − lo` across the 33 nodes, which is
separately the fix for the 56–63 s DRAM residual and is worth more than the
multiplication it saves.

**Its §8 proof-migration warning is real, and it implies an ordering the brief
does not draw.** cpoly's generic `UnivariatePoly × UnivariatePoly` schoolbook
*is* in the reachable extracted model
(`Shared1UnivariatePoly.Insts.CoreOpsArithMulShared0UnivariatePolyUnivariatePoly.mul_loop0_loop0`,
`lean/Generated.lean`), reached from `sumcheck.rs`'s `&inner * &free` -- where
`free` is the degree-1 equality factor and has two coefficients. So bumping the
pin to upstream's Karatsuba + `u128` implementation would force re-porting a
proof for a product this crate never needs. The brief's own *alternative* --
spell that degree-1 multiply in hachi -- is therefore a **prerequisite** of any
bump, not a follow-up: it shrinks the bump's proof surface to `Ext4::mul` and
`eval_mle_layer`. Decided with the user: defer the bump until after it.

**Its §2 squaring ladder is sub-noise here** (1 024 → 10 `Ext4` mults on a call
already hoisted out of the `ℓ` loop, and `zerocheck.rs:698` names the per-cell
`m_alpha_tilde` table as the real win) and needs no upstream `square`: `pw * pw`
does it. Cleanup tier. Its RISC-V inline-assembly path: agreed, not adopted --
the same line § "no `unsafe`" already draws.

**Its §3/§4 is the one genuinely new item, and it is worth more than the brief
claims.** That became iteration 8.

## Stage 6 iteration 8: the `Rq`-valued bases built one variable at a time (candidates M and N, 2026-09-15 night → 09-16)

`evalsplit::monomial_basis` and `::lagrange_basis` read their specifications
literally: entry `i` of the `2^n` result was a product of exactly `n` factors,
one per variable, with `Rq::one()` (resp. `1 - wⱼ`) multiplied in wherever bit
`j` of `i` was clear. `2^n · n` schoolbook degree-1024 ring products per call;
`10 240` each at `ML_VARS_LOW = ML_VARS_HIGH = 10`.

No brief proposed the doubling build for them -- checked across all seven files
in `briefs/`. What makes it cheap is that the shape was already in this crate
at `Ext4`: `sumcheck::eq_suffix_table` (`sumcheck.rs:302`) is the same
level-by-level construction with its spec proved, so neither the Rust shape nor
the proof route was a new risk.

* **Candidate M, `monomial_basis`.** Bit `j` of every index below `2^j` is
  clear and bit `j` of `2^j + r` is set, so the table for the prefix `w₀…wⱼ` is
  the table for `w₀…wⱼ₋₁` followed by that same table scaled by `wⱼ`. One
  multiplication per entry ever written, no index arithmetic, no `1`-factors:
  `2^n − 1 = 1 023`. Accepted on run `20260915T2341+0200-2fc68e72`:
  `monomial_basis/4` 91.5 ms → 21.5 ms (**−77.3%**), `/6` 549 ms → 90.2 ms
  (**−84.1%**), both recentered, both `faster`, A/B bias 4.3%.
* **Candidate N, `lagrange_basis`.** Both children of an entry `p` are
  `p·(1−wⱼ)` and `p·wⱼ`, and the first is spelled `p − p·wⱼ`, so a level costs
  one ring multiplication and one ring *subtraction* per entry instead of two
  multiplications: `2^n − 1 = 1 023`, where upstream's own two-multiplication
  form would pay `2 046`. `Rq::sub` is `N` coefficient subtractions against
  `Rq::mul`'s `N²` products, so at `N = 1024` the subtraction is free at this
  ratio. Accepted on run
  `20260916T0010+0200-d0bcebeb`: `lagrange_basis/4` 91.6 ms → 21.5 ms
  (**−76.4%**), `/6` 550 ms → 90.4 ms (**−83.5%**), both recentered, both
  `faster`, A/B bias 4.4%. The level rewrites the low half in place through
  `Vec.index_mut` and appends the high half, so the inner loop's invariant has
  three parts rather than two -- the entries already rewritten, the entries
  still holding the level's input, and the multiples appended above.

Both measured deltas land within 0.2% of what the operation count predicts, and
on N's run `now ≈ genesis` on both rows (91.6/550 against 91.7/550), which is
the check that M -- which touched only `monomial_basis` -- did not leak into N's
attribution. That mattered here because `git commit` was denied for the whole
session, so N could not be benched against a *committed* M: `hachi/src` was
restored from a saved copy of the M champion instead of with
`git restore hachi/src`, which would have destroyed it. Both ledger rows carry
`pins.dirty: true` and say so.

**Why the rows could carry a verdict at all.** `evalsplit/{monomial,lagrange}_basis`
have rows at n = 4 and n = 6 and are **not** excluded, and at ~91 ms and ~549 ms
they sit far outside the certified 100 ns–2 µs unresolved band. Each measured
delta landed within 1% of what the operation count predicts (−76.6% / −83.6%),
which is the check that rules out a hidden allocation regression: the win is
the arithmetic and nothing else.

**What this does to I4's case.** § "The exclusion arithmetic, stated honestly"
prices `quadeval::to_quad_eval_statement` at two `monomial_basis` calls =
`2 · 1024 · 10 = 20 480` ring products ≈ 29 s, and gives its removal condition
as "until a sub-quadratic `ring::mul` lands", conceding that Karatsuba's 2–4×
would only reach ~8 s. Candidate M alone takes it to `2 046` products ≈ **2.9 s**
without touching `ring::mul`, and the two compose. That is one of I4's stated
justifications, answered more cheaply than I4 could answer it. I4 keeps the
other two (the 21 mul-bound rows and the un-ignore ceremony) and keeps its
place in the queue -- but the brief's remaining advice for it is now on the
record: **benchmark the `u128` delayed-reduction schoolbook before assuming
Karatsuba wins**. The bound checks out, `1024·(q−1)² < 2^74`, with ample `u128`
room.

**`two_pow` and `test_bit` in `evalsplit` are now dead, and stay.** Both bases
stopped calling them, and `zerocheck::two_pow` is a separate function with
callers. They keep `#[allow(dead_code)]` rather than being deleted: both are
frozen in the genesis corpus, both carry proved specs that § 4 audits, and --
probed, not assumed -- charon translates every *local* item whether or not the
crate reaches it, so the model and those specs are still exactly about this
code. (The reachability caveat in `aeneas-extract` applies to *foreign* items
under `--include`, and this is the measurement that pins the difference.)
Deleting proved specs is the larger and less reversible move, and it is not
forced.

**Proofs are local, not Aristotle's.** Both `opt_eq_spec`s are hand-written,
stated over a bare `CommSemiring` (M) and `CommRing` (N) against
`CMlPolynomial.monomialBasis` / `CMlPolynomialEval.lagrangeBasis` themselves,
and both campaigns restate their loop specs with the headline statements
byte-identical. One structural note worth keeping: the campaign **cannot** route
through the contract, because `Opt.lean` imports `EvalSplit.lean`. So the
identity is proved twice, independently -- once over an abstract ring in
`Opt.lean`, once over the extracted loops in `EvalSplit.lean` -- and § 4 audits
both. That is the safe direction for this dependency, and the alternative
(moving the pure layer down into `EvalSplit.lean`, as candidate L's lemmas were
moved down into `Sumcheck.lean`) stays available if a third caller ever wants it.

## I4's desk-work prerequisite is cleared: the iterative Karatsuba shape extracts (2026-09-16)

`PLAN_STAGE6.md` § I4 made an `aeneas-extract` ceiling probe the gate on the
whole track, for a real reason: Decision 6's "~20×" assumed recursion to a small
base, Aeneas's supported subset is loops rather than recursion, and nobody had
measured whether an **iterative, bottom-up** convolution split extracts at all.
It does, and the answer is better than the gate needed.

A scratch crate (`probe-i4/`, one construct family per function plus a
`use_all` so charon cannot drop anything) carried: a `&mut Vec<u64>`
out-parameter written through `IndexMut`; offset index arithmetic in place of
subslices; several live scratch buffers at once; a guarded subtraction under a
counter loop; and, separately, a `u128` two-accumulator delayed-reduction
negacyclic convolution. charon and aeneas both exit 0, `Probe.lean` has **zero**
axioms and zero `Shared` prefixes, every loop carries a positional
`@[rust_loop]` name, and **every loop state is a 2-tuple** except the `u128`
one, whose inner state is `(pos, neg, i)` -- the two accumulators, expected.

The shape of `karatsuba_1level` is the finding. It extracts as a straight-line
chain -- `zeros`, `conv_at`, `zeros`, `conv_at`, `add_halves`, `add_halves`,
`zeros`, `conv_at`, `zeros` -- followed by a **single** recombination loop. So
the proof is one spec per helper, proved once each, and a `step` chain at the
top; the plan's worry that a restructure would "not weaken the proof, it would
stop it compiling" is still true of `Ring.lean`'s three `mul_loop*` specs, but
the replacement is cheaper to write than those were.

Two caveats to carry rather than lose:

* The probe used `u64` with `wrapping_mul`/`wrapping_add` as an `Fp` stand-in.
  It answers the loop-and-buffer-shape question, which was the open one; it says
  nothing `Fp`-specific, and with real `Fp` operations the bodies become
  monadic, which changes nothing structurally since the model already is.
* It says nothing about whether the split *pays*. One level is 4/3, two 16/9,
  three 64/27 ≈ 2.4×, against three sequential loop nests of overhead per level.
  That is what the benchmark decides.

**So the candidate slot is unblocked for I4, and the first candidate to bench is
the `u128` dense convolution, not Karatsuba** -- the AeneasCompPoly brief's one
piece of advice about I4 that survived checking, and its bound checks out
(`1024·(q−1)² < 2^74`, ample `u128` room). If the simpler candidate lands most
of the factor, the Karatsuba proof cost is never spent.

## I4 opens and closes in one candidate: the reduction, delayed (candidate Q, 2026-09-16)

`Rq::mul` was the broadest lever in the stage -- ~100% of 21 rows -- and the one
the plan expected to cost the most. It cost the least of the three candidates
this session, and the reason is worth keeping.

Every `Fp` operation reduces: cpoly's `Mul for Fp` is `(a.0 * b.0) % P`. So the
frozen schoolbook paid a `%` on each of the `N²` products *and* on each
accumulation. Walking the output coefficient instead of the input pair lets slot
`k`'s two antidiagonals accumulate in `u128` untouched, and `% q` is paid once
per slot: `N²` reductions become `2N`. The sign rule did not change, only its
indexing -- `j = k − i` for `i ≤ k`, `j = N + k − i` for `i > k`.

**Measured −55.6% twice** (`ring/mul/1024` 1.43 ms → 637 µs; runs
`20260916T0826+0200-a07c93d7` and `…0835…`, biases 1.8% and 2.8%, same slot sha,
agreeing to 0.01%). Single-row target, so two runs were required and both read
`faster`. Ledger row 27.

**This closes I4 without Karatsuba, and that is the finding.** Three-level
Karatsuba's ceiling is `64/27 ≈ 2.37×` *before* recombination overhead, against
a much heavier proof; Q delivers 2.25× with a proof that reuses the existing
`negConv` bridge. The ceiling probe (§ above) was still worth running -- it is
what made it safe to *not* run Karatsuba, by establishing that the fallback
existed. And the ordering advice came from the AeneasCompPoly brief, which is the
one thing in that brief about I4 that survived checking.

**What the proof actually needed**, both paid by hand:

* `accBound` -- `N · (q−1)² < 2^74` against `u128`. Load-bearing, not caution:
  one term already fills a `u64`, so a `u64` accumulator overflows on the *first*
  product. This is the hypothesis the whole candidate rests on.
* the cast bridge -- reducing once per slot equals reducing per product, because
  `Nat.cast` into `ZMod q` is a ring hom and `ZMod.natCast_mod` discards the
  `% q`. The `N + k` antidiagonal needs both vanishing arguments: `coeffK a`
  above `N`, and `coeffK b` because `N + k − t ≥ N` once `t ≤ k`.

`mul_spec` is byte-identical; the three old loop specs became two. Route R2
(`rust-direct`) rather than R3 -- benched first, proved straight against
`negConv` with no Lean `opt` chain, so no `Opt.lean` entry by design. The ledger
row says so, because it is a different shape from M and N in the same session.

Two smaller records. The inner loop state is the 5-tuple
`(self, rhs, pos, neg, i)`: Aeneas threads both shared borrows, they come back
unchanged, and the inner spec has to *say* so or the outer loop cannot use them.
And `Ring.lean` now carries private `getD_append_lt'` / `getD_append_eq'`
duplicating `Scheme.lean`'s, because `Scheme` is downstream of `Ring` via
`RqBridge` -- the same "the dependency runs the wrong way" shape as the
`Opt`/`EvalSplit` note above. Hoisting `Scheme`'s copies into `Ring` is the
tidier fix and is owed, not done.

**Owed, and now unblocked**: `to_quad_eval_statement`'s exclusion condition is
**met**. M took it from ~29 s to ~2.9 s and Q takes it to ~1.3 s, the same order
as the live `evalsplit/lagrange_basis/6` row. The entry is re-based and says so;
turning it into a row is the un-ignore ceremony, with the 27 `#[ignore]`d scale
tests in the same pass.

## Candidate P: the univariate schoolbook moves in, and a new verdict for that shape (2026-09-16)

cpoly's `impl Mul<&UnivariatePoly> for &UnivariatePoly` was reachable from
hachi, from exactly four places -- `&inner * &free` in the `honest_compute_g`
family -- where `free` is `eq_free_factor`'s **two** coefficients. Upstream has
since put Karatsuba and `u128` leaves behind that operator, so a pin bump would
have forced a re-port of a proof for a product this crate never wants.
`sumcheck::poly_mul` is that multiplication written here instead, cpoly's body
verbatim to the extent hachi can be (`UnivariatePoly`'s field is private, so
`from_coeffs` stands where cpoly names the constructor).

The surface, counted, because that is the deliverable: **out** went five defs
and two loops; **in** came `UnivariatePoly::len`, its `Index` impl, and
`alloc.vec.from_elem` -- three identity wrappers.

**Two findings from the desk work, both of which changed the plan.** First, P was
priced as medium proof work and is not: `lean/Sumcheck.lean` already proved the
whole chain against cpoly's copy, so a verbatim mirror retargets
`uni_mul_{inner_loop,outer_loop,}_spec` by **item name alone** -- no statement
moved. Second, the reason a verbatim mirror is even possible: `vec![x; n]`, the
*repeat* form, is modelled with no loop of its own, so cpoly's `Mul` extracts to
exactly two loops and so does ours. The forbidden-list entry in `aeneas-extract`
covers the `vec![a, b]` *list* form only; conflating the two would have cost a
loop index and the whole retarget with it.

**A new ledger verdict, `accepted-surface`** (agreed with the user), because the
enum had no name for this shape. P is not a speed candidate -- the counts are
identical, the body is the same body -- so `accepted` would assert a win that
does not exist, and `rejected-noise` reads as "not landed". It sits beside
`accepted-wall`: same time guard (no row `slower`), and the row must record what
the model gained and lost as arithmetic. Wired into both enforcers, which is the
part that would have rotted: `perf-loop`'s enum and step-5 rule, *and*
`skill-lab`'s `ledger_check.py`, which keeps its own hardcoded list and rejected
the row until it was updated. The trap is written in too -- the verdict is not
for a candidate that merely happens to be noise; the test is whether the model
change *is* the deliverable.

Measured: both `honest_compute_g` rows `noise`, no row slower, as identical
counts require. Recorded rather than glossed: the A/B bias was 6.7% on that run,
so it could not have seen a regression below that. The real guard is the
arithmetic.

**`Check.lean` § 2's alias pin lost its polynomial-multiply ascription, and how
it was lost is the point.** It stopped *typechecking* the moment the item left
the model, so this arrived as a build failure rather than silent rot -- exactly
the outcome the pin was written for, and the first time that section has earned
its keep. What remains is weaker and the note now says so: with one `Shared<n>`
impl left there is nothing for the index to swap with, so the surviving pin
asserts only that `Shared0` is still the scalar multiply. The `Index` impl P
added needs no pin, being an impl on the type rather than by reference.

`poly_mul` is excluded by name on the `honest_compute_y` precedent: 66 `Ext4`
multiply-adds at the only ratio the scheme uses (`np = 33`, `nq = 2`), inside the
certified band, measured one level up. The entry says the part that matters --
it *could* be given a row at an artificial square size, and that is what would
make the row misleading.

**The bump is now cheap, and that was the whole point.** With cpoly's generic
multiplication out of the model, a `583cfaff → d7e26bb` bump has to re-port
`Ext4::mul` and `eval_mle_layer` and nothing else of substance. It stays
deferred to the cleanup tier, but it is no longer gated on P.

## The chain, measured again: 1.74× end to end -- and one phase that is not what I said it was (2026-09-16)

First end-to-end reading since 2026-09-14. Same shape (1 block), same machine,
`85e7917` → `3ed053e`, so a direct before/after across nine accepted candidates
(F/G, I, J, K, L, M, N, Q, P). Logs: `logs/runs/honest-chain-profile-20260914.log`
and `…-20260916.log`.

**2 179.0 s → 1 249.5 s = 1.74×.**

| phase | 09-14 | 09-16 | factor |
|---|---|---|---|
| commit 1 block | 12.5 s | 5.6 s | 2.23× |
| statement built | 38.4 s | 4.7 s | **8.2×** |
| `honest_compute_v` | 1.6 s | 0.7 s | 2.3× |
| `honest_compute_resp` + stack | 14.6 s | 6.6 s | 2.2× |
| `M·ζ = y` | 296.8 s | 144.4 s | 2.06× |
| lifted witness | 300.7 s | 345.3 s | **0.87×** |
| `lift_commit` | 61.9 s | 30.3 s | 2.04× |
| rounds (26) | 1 201.3 s | 599.0 s | 2.01× |
| `chain_verify` | 202.3 s | 46.1 s | 4.39× |

**Candidate Q is confirmed exactly where it was supposed to be.** commit 2.23×,
`M·ζ=y` 2.06×, `lift_commit` 2.04× -- all at the 2.25× the `ring/mul` row
measured. So those phases really are `ring::mul`-dominated, which is what makes
the un-ignore ceremony's arithmetic trustworthy rather than hopeful. The rounds
halved against candidate I's ≈550 s projection, and the verifier's new
sub-breakdown shows where I5 landed: `final_check` 99 s → **8.7 s**,
`round_verify_loop` (26 rounds) → **69.6 µs**, leaving `end_piece_check` (34.6 s)
as three quarters of a 46 s verifier.

**A correction to my own arithmetic, which the run caught.** The ≈1.42×-from-Q
estimate I wrote before this run counted the lifted-witness phase (300 s) among
the `ring::mul`-bound work. It is not: `honest_lift_witness` goes through
`ringswitch::long_mul`, the *unreduced* `2N−1`-wide product, which is a separate
function Q never touched. That phase did not improve, and `long_mul` is now the
largest unoptimised thing in the run -- **345 s, 28% of the total**.

`long_mul` is therefore the next candidate, and the case for it does not rest on
any disputed number, only on reading it: it is the pre-Q schoolbook shape,
`ai * b.coeff(j)` reducing once per product and `out[s] + term` reducing again.
Q's proof transfers with the negacyclic fold *removed* rather than added -- a
linear convolution, one accumulator, no sign split -- and the `u128` ceiling is
the same `1024 · (q−1)² < 2^74`.

**An unresolved caveat, recorded rather than smoothed over.** Three phases that
no candidate touched all came back 10–13% *slower*: lifted witness
(300.7 → 345.3 s), `alpha_public_table` (12.5 → 14.3 s), `honest_compute_y`
(4.1 → 4.5 s). One common direction across three unrelated phases suggests one
cause -- code layout under fat LTO, or machine state -- rather than three
regressions. But it is not explained, and **this profile has no control**, unlike
the criterion harness. A repeat run was started and then abandoned on the user's
instruction in favour of moving on, so the question stands open: **the 1.74×
should not be trusted to better than ~10%, and neither should any single phase
figure this profile has produced since 09-14.** Owed: either a controlled repeat,
or a per-phase control in the profile itself.

## Candidate R: the same trick one function over, and the profile is what found it (2026-09-16)

`ringswitch::long_mul` -- the unreduced `2N−1`-wide product `cRowSum` needs --
was the pre-candidate-Q schoolbook: `ai * b.coeff(j)` reducing once per product
and `out[s] + term` reducing again. Candidate R walks the output slot, sums its
clipped antidiagonal in `u128` unreduced, and pays `% q` once per slot.
**1.75× on all three rows** (`c_row_sum`, `c_quotient`, `honest_lift_witness`,
−42.8/−43.0/−42.8%, bias 3.2%). Ledger row 29.

**What is worth recording is how it was found.** No brief proposed it. The
end-to-end profile did, by contradicting me: I had counted the lifted-witness
phase among the `ring::mul`-bound work when estimating what Q would buy, and it
is not -- `long_mul` is a separate function, Q never touched it, and it sat there
as 345 s of a 1 250 s run, the largest unoptimised phase left. An estimate that
assumed a factor and a measurement that checked it disagreed, and the
measurement was right. That is the argument for keeping the profile in the loop
rather than reasoning from per-row factors.

**And one claim I got wrong inside the candidate itself.** The first version's
comment said the clipped antidiagonal bounds were "the second saving here",
`N²` inner steps against `(2N−1)·N`. They are not a saving over the *baseline*:
the frozen scatter was already `N²` steps. The bounds exist so that walking the
output does not **cost** a factor two, which a guarded pass over the whole square
would. The measured 1.75× is the reduction, plus an accumulator that stays in a
register instead of round-tripping through `out[i + j]`. The comment is corrected
in the landed code, so the landed text differs from the benched `slot_sha` by a
comment only -- recorded in the ledger row, since the sha is supposed to pin what
was measured.

**The proof is where Q pays off twice.** `wordN`, `wordN_lt` and `accBound` are
`Ring.lean`'s, and `Ring.lean` is *upstream* of `LiftProver.lean`, so this time
the dependency runs the right way and the `ℕ`-level layer is genuinely shared
rather than duplicated -- the opposite of the `Opt`/`EvalSplit` and
`Ring`/`Scheme` cases above. R is also strictly easier than Q: a `Zq[X]` product
has no negacyclic fold, so one accumulator and no sign split.
`long_mul_spec` is byte-identical; three loop specs became two.

Four small things the model forced, all worth knowing for the next candidate of
this shape:

* `Rq::coeff` needed a **word-level** spec (`coeff_word`). `coeff_spec` gives the
  `ZMod q` value, which is the wrong currency for a `u128` accumulator.
* the two clipped bounds extract as **monadic** `if`s (`k + 1 - n` is a checked
  subtraction), which `step` cannot take; one spec each (`clip_lo_spec`,
  `clip_hi_spec`) keeps the four-way split out of the loop proof.
* `k - i` is a checked subtraction, so the inner spec needs `hi ≤ k + 1` as a
  hypothesis -- easy to forget, and the model is what reminds you.
* **`omega` does not unfold `N`.** `abbrev N : ℕ := 1024` is an atom to it, so
  every bound argument that depends on `N`'s value needs `have hNv : N = 1024 :=
  rfl` in scope first. This cost several iterations and will cost them again.

## The full sweep, banked before the re-freeze: 87 rows, no regression anywhere (2026-09-16)

First full `make run-bench` since 2026-09-14 (`2af5297`), which predated nine
accepted candidates -- I, J, K, L, M, N, Q, P, R. Run
`20260916T1210+0200-84e11de8`, **A/B bias 1.5%**, the tightest of any run this
session. `logs/runs/full-20260916.json`.

The point of doing it now is that the I4 ceremony **re-freezes genesis**, and
`vs genesis` is the only cumulative record of what Stage 6 bought. Re-freeze
first and this evidence would never have existed.

Cumulative gain over the frozen baseline, the largest first:

| row | genesis | now | |
|---|---|---|---|
| `sumcheck/final_check/11` | 14.9 s | 96.4 µs | −100.0% (≈1.5·10⁵×) |
| `sumcheck/alpha_public_table/7` | 1.86 s | 85.1 µs | −100.0% (≈2.2·10⁴×) |
| `sumcheck/honest_round_messages/11` | 14.9 s | 17.8 ms | −99.9% (≈837×) |
| `ringswitch/c_eval_at{,_modulus}/1024` | 7.25 ms | 18 / 15.7 µs | −99.8% |
| `zerocheck/c_w_table_mle/14` | 19 ms | 39.1 µs | −99.8% |
| `zerocheck/zc_target_alpha/5` | 36.2 ms | 92.3 µs | −99.7% |
| `zerocheck/h_zero{,_is_zero}/14` | 27 ms | 432 / 393 µs | −98.4 / −98.6% |
| `zerocheck/w_table_mle_eval/14` | 23.1 ms | 512 µs | −97.8% |
| `sumcheck/alpha_public_mle_eval/26` | 24 ms | 2.34 ms | −90.3% |
| `evalsplit/{monomial,lagrange}_basis/6` | 550 ms | 49.3 / 40.4 ms | −91.0 / −92.6% |
| `endpiece/end_piece_check/14` | 47.6 ms | 11.2 ms | −76.5% |
| `ring/mul/1024` | 1.43 ms | 636 µs | −55.5% |
| `linalg/{dot,mat_vec_mul,scalar_vec_mul,split_form}` | — | — | −55.5 … −55.6% |
| `ringswitch/lift_commit/4` | 17.2 ms | 7.89 ms | −54.1% |
| `ringswitch/{c_row_sum,c_quotient,honest_lift_witness}/4` | 4.52 ms | ≈2.4 ms | −46 … −47% |
| `sumcheck/honest_compute_g{,_split}`, round kernels | ≈17 ms | ≈14 ms | −18% |
| `gadget/*` | — | — | −9 … −29% |

39 rows read `noise`, which is what an unoptimised row should read.

**No regression anywhere in 87 rows.** Two rows print `slower` and neither is a
measurement of anything:

* `quadeval/in_sb/1024`, 430 → 472 ns, +9.7% -- deep inside the certified
  100 ns–2 µs band, and its sibling `in_sb_box` moved **−8.9%**, the other way by
  the same amount. That opposed pair is the band's signature.
* `zerocheck/w_table_z_row/3`, **5.44 → 5.91 ns**, +8.8%. Five nanoseconds. Two
  orders of magnitude below the band.

**This also all but settles the profile anomaly.** The 09-16 profile showed three
untouched phases 10–13% slower, and I could not tell a build-layout effect from a
real regression. With the A/B bias at 1.5% across all ten binaries and not one
genuine `slower` row, the machine and the build were clean; the profile's spread
is its own missing control (it has none) rather than anything in the code. Not
*proved* -- that needs a controlled profile -- but it is now much the better
explanation, and the earlier caveat should be read with this beside it.

**Two facts about the harness worth keeping.** The sweep took ~1 h 45 m, and it
is dominated by the genesis variants of the rows we optimised hardest: criterion
needed ~750 s for 50 samples of `final_check`'s pre-K baseline and the same again
for `honest_round_messages`. **The better a candidate is, the slower its own
baseline is to measure**, so a full `vs genesis` sweep gets more expensive with
every win. That is a second, independent reason the ceremony's re-freeze belongs
*after* this measurement: it banks the record and makes the next sweep cheap.

## Correction: 144 s of the "chain" profile is a test assertion, not protocol work (2026-09-16)

`hachi/tests/chain_semantics.rs:481-484` is

    assert!(rlin.m().mat_vec_mul(&zeta).equals(rlin.yvec()), …);
    eprintln!("[…] M zeta = y holds", …);

The protocol never forms `M·ζ`. The prover builds the lifted witness and the
verifier checks the R^lin claim through `alpha_contract`; this `mat_vec_mul` over
the dense `5 × 57 344` matrix exists only so the test can assert the relation
directly. So the phase the two profile logs label `M zeta = y` — **296.8 s** on
09-14 and **144.4 s** on 09-16 — is test-harness time.

**What this corrects in the two entries above.** § "The chain, measured again"
reports `2 179.0 s → 1 249.5 s = 1.74×` as the end-to-end figure and lists
`M·ζ = y` among the chain phases without qualification. Both are true of the
*test*, which is what the profile times; neither is protocol time. Protocol-only:

    1 882.2 s → 1 105.1 s = 1.70×

The headline barely moves. The **shares move a lot**, and those were the basis
of a reprioritisation, so they matter more:

| of protocol time | pre-R | after R (lift ≈197 s) |
|---|---|---|
| rounds (26) | 54.2% | **62.6%** |
| lifted witness | 31.2% | 20.6% |
| `chain_verify` | 4.2% | 4.8% |

I had also counted `M·ζ = y` among the `ring::mul`-bound phases when estimating
what candidate Q would buy end-to-end. It *is* mul-bound — `mat_vec_mul` is ring
products, and Q duly took it 296.8 → 144.4 s — but it is mul-bound *test* work,
so it never belonged in a chain projection. That is the second error in the same
estimate: the first was counting the lifted-witness phase as `ring::mul`-bound
when it is `long_mul`-bound (§ "Candidate R"). One estimate, two
misattributions, both caught by measurement rather than by re-reading it.

**Owed** (now on the candidate backlog's § 5): either drop this assertion from
the profile's accounting, or make the test derive it from the lift's output
instead of multiplying the dense matrix. Until then every phase percentage taken
from `the_honest_chain_profile` must say whether it is over protocol or over the
harness total.

## The post-R profile, and the control the profile never had (2026-09-16)

`logs/runs/honest-chain-profile-20260916-postR.log`, 1 block, `6533d1d`, the
same shape as the two earlier profiles. **943.0 s** harness total,
**808.6 s protocol** (the `M·ζ = y` assertion excluded, per the correction above).

**Finding 1: the profile's run-to-run offset is systematic, coherent, and about
10%.** Candidate R touched `long_mul` and nothing else. Every phase it did *not*
touch came back faster by almost exactly the same margin:

| unchanged phase | 09-16 | post-R | |
|---|---|---|---|
| rounds (26) | 599.0 s | 526.2 s | −12.2% |
| `alpha_public_table` | 14.3 s | 12.6 s | −11.9% |
| `final_check` | 8.7 s | 7.7 s | −11.5% |
| `lift_commit` | 30.3 s | 27.0 s | −10.9% |
| `honest_compute_y` | 4.5 s | 4.1 s | −8.9% |
| `chain_verify` | 46.1 s | 42.3 s | −8.2% |

That is the control this profile has never had, arrived at by accident: the same
measurement twice with a known change in exactly one place. **The "three
untouched phases drifted 10–13%" on 09-16 was not three phases — it was the whole
run, systematically ~10% slow.** § 5's owed item in
`PLAN_STAGE6_CANDIDATES.md` is discharged as an explanation (a per-phase control
is still worth having as an instrument). Practical rule: **no phase figure from
this profile means anything to better than ±12%**, and cross-run phase ratios
need the whole-run offset divided out before they are read.

**Finding 2: R's REDUCED row understated its real-shape effect.** The lifted
witness phase went 345.3 → **133.9 s**. Even taking the 09-16 number as ~10%
inflated (so ~307 s true), that is **2.3×** where R's accepted rows measured
**1.75×** at `LIFT_PROVER_COLS = 4`. The reason is structural: at four columns,
`long_mul` is a smaller share of `honest_lift_witness` than it is at the pin's
5 × 40 976, so the fixed work around it (allocation, `div_by_modulus`) dilutes
the win. **A REDUCED row can understate as well as overstate**, and which way
depends on whether the optimised inner function's share grows or shrinks with the
shape. Worth checking per candidate rather than assuming conservatism.

**Finding 3: cumulative protocol speedup 2.33×**, `1 882.2 → 808.6 s` across
F/G, I, J, K, L, M, N, Q, P, R — read as ~2.1–2.6× given the offset above. And
the shares have moved decisively:

| post-R protocol share | s | % |
|---|---|---|
| **rounds (26)** | 526.2 | **65.1%** |
| lifted witness | 133.9 | 16.6 |
| `chain_verify` | 42.3 | 5.2 |
| `lift_commit` | 27.0 | 3.3 |
| setup (commit → R^lin) | 19.1 | 2.4 |
| `alpha_public_table` | 12.6 | 1.6 |

**Consequence: this inverts T1 before T2.** The candidate backlog orders
T7 → T1 → T2 on a pre-R lift phase of 345 s. Measured post-R it is 133.9 s, so
T1's remaining headroom is ~127 s (**15.7%** of protocol, lift + α-table down to
the card's projected 15–20 s), while T2's rounds are 526.2 s and its ~1.5×
is ~175 s (**21.7%**) — on a proof the card itself prices at a day against T1's
five-block-structure argument. T3 is ~350 s (43%) and is reached *through* T2.
T1 keeps one thing T2 has not: T1b removes wall W2 (2.2 GiB) and unblocks I6b
and I7. So the order is a choice between seconds now and unblocking later, not a
correctness question. This is exactly the check the backlog's preflight gate 1
existed to force, and it fired.

## Candidate T2a: the range factor expanded, and the proof split so the table cannot hide (2026-09-16)

T2's card projects ~1.5× on the round work by loop interchange. Before touching
the loops, the *innermost* thing they call turned out to be worth more than the
whole card projected, and it is a smaller change.

`zerocheck::range_product` is the range factor of the zero check,
`P(v) = v · ∏_{j=1}^{15} (v² − j²)` after candidate F's contraction. F computes
it one factor at a time: 15 **full** extension multiplications (19 base
multiplications each, `ext_mul_spec`) and 15 `Fp::new` + `Ext4::from_base`
embeddings. Candidate T2a expands the product into its 16 coefficients **once,
at compile time** — `params::RANGE_Q_COEFFS`, a `const [u64; 16]` — and then
evaluates the degree-15 polynomial by Paterson–Stockmeyer at block width 4:
with `y = v²` and `y², y³, y⁴` precomputed, three Horner multiplications by `y⁴`
and twelve **mixed** `Fp × Ext4` multiplications, four base multiplications each.
So the coefficient work drops from `15 × 19` to `12 × 4` base multiplications.

Measured (`20260916T1530+0200-ad543615`): the five caller rows read
**−43.0 / −42.6 / −43.6 / −44.5 / −44.0 %**, and the item's own row −50.1% at
348 ns, which carries no verdict — it is inside the certified 100 ns–2 µs band,
so the callers are the evidence, per `perf-loop`'s band rule. A/B bias 3.1%.

**The cross-check that mattered.** `h_zero` and `h_zero_is_zero` moved +1.6%,
i.e. noise. That is the intended result, not an accident: those two route through
`range_product_base`, the `Fp` variant, which T2a deliberately does **not** touch
(rule 12 — it is its own candidate). Candidate F's first attempt earned
`rejected-mixed` on exactly these two rows, and the failure mode did not recur.

### Why the proof is in two halves

The risk in a precomputed table is that it is wrong and the algebra absorbs it.
So `rangeQ_eq_prod` is split on purpose:

* **Lemma A** — the fifteen-factor product expands to a degree-15 polynomial
  with **exact integer** coefficients (`a_0 = −1 710 012 252 724 199 424 000 000`,
  25 digits). `ring` closes it; it uses no characteristic and would hold over any
  commutative ring.
* **Lemma B, sixteen times** — each exact integer equals the reduced word the
  table stores. That is a computation in `ZMod q`, by `decide`, lifted into `F`
  through `castB`, which factors both casts through the ring homomorphism `φF`.
  `decide` is why Lemma B is stated about `ZMod q` — a finite type — rather than
  about `F`, where there is nothing to compute with.

`rc` is *defined* as the table read (`params.RANGE_Q_COEFFS.val.getD j 0`), so a
wrong word cannot be papered over: it fails its own `decide`. And the claim is
verified twice from opposite ends —
`params_semantics::range_q_coeffs_are_the_product_form` rebuilds all sixteen
literals in `u128` from `GADGET_BASE` on the Rust side.

`Opt.lean` carries the rearrangement generically in the coefficient sequence
(`range_product.optPS_eq`): the loop shape is what the candidate *is*, and the
particular sixteen words belong to `rc`. `range_product.optPS_eq_spec` composes
the two.

### Three things the Lean cost

* **`Array.index_usize_spec` hands back a `getElem` at a boundedness proof**, and
  `rw`ing the *index* afterwards fails with "motive is not type correct" — the
  proof depends on the term being abstracted. The fix is ordering: bridge to `rc`
  (whose argument is an ordinary `ℕ`) **first**, rewrite the index second. Same
  family as the `rw [hlen]` failure recorded for candidate M.
* **`@[irreducible]` on an extracted `const` is not a wall.** Aeneas also puts
  `@[global_simps]` on it, so `simp only [params.RANGE_Q_COEFFS, Array.make]`
  unfolds the table and `rfl` reads an entry.
* **`norm_num` cancelled the leading `v`** in `rangeQ_sq_eq_rangeProduct`, turning
  a goal into `… ∨ v = 0` (it is a field, so it may). Targeted rewrites plus
  `Finset.prod_congr` — candidate F's shape — instead.

Rule 12 headroom left on the table, deliberately: the twelve `Fp::new` calls each
pay a redundant `% P` on a table word that is already reduced.

## The post-T2a profile: rounds down 35.7%, and the "offset" is not one number (2026-09-16)

Preflight gate 1 re-run on `28a043f`, 1 block, 864.1 s total
(`logs/runs/honest-chain-profile-20260916-postT2a.log`). Since the post-R run
(`6533d1d`, 943.0 s) the only change is candidate T2a, on
`zerocheck::range_product`.

**The machine offset, measured from the phases T2a cannot touch** — and this is
the finding that matters more than the headline:

| untouched phase | post-R | post-T2a | Δ |
|---|---|---|---|
| setup (commit → R^lin) | 19.1 | 21.4 | +12.0% |
| `M ζ = y` (test assertion) | 134.4 | 152.0 | +13.1% |
| lifted witness | 133.9 | 150.1 | +12.1% |
| `lift_commit` | 27.0 | 30.5 | +13.0% |
| `alpha_public_table` | 12.6 | 14.5 | +15.1% |
| `honest_compute_y` | 4.1 | 4.5 | +9.8% |
| `final_check` | 7.7 | 8.9 | +15.6% |
| **`end_piece_check`** | 32.1 | 41.3 | **+28.7%** |
| **`chain_verify`** (contains it) | 42.3 | 54.9 | **+29.8%** |

**The offset drifts within a run.** Seven phases cluster at +10 to +16% (median
+13.1%); `end_piece_check` and the `chain_verify` that contains it sit at +29%.
Those two are the *last* things the run does, at minute 14 of sustained load, so
the natural reading is thermal or page-cache state rather than anything about the
code — but the honest statement is that a single scalar cannot recenter this
profile, and every previous cross-run comparison here (including the "8–12%
coherent offset" recorded after R) assumed it could.

So the recentering below uses the **median of the seven middle-of-run phases**,
+13.1%, which are the ones the rounds sit among. That is a defensible choice, not
a correction.

**Rounds**: `526.2 → 382.5 s` raw = **−27.3%**; recentered **−35.7%** (to 338.2 s).

Less than the −43/−44% the five caller bench rows read, and that is expected
rather than a discrepancy: `honest_round_messages` also contains
`round_poly_alpha`, `eq_suffix_table`, the interpolation and its own two tables,
none of which T2a touches. The bench rows measure the kernel's callers; this
measures the phase those callers live in.

**Protocol total (excluding `M ζ = y`, a test assertion):** `808.6 → 712.1 s`
raw = −11.9%; recentered 629.6 s = −22.1%. Cumulative against the 1 882.2 s
genesis baseline that is **2.64× raw / 2.99× recentered** — read as ~2.6–3.0×,
and note the same caveat the 2.33× figure carried: compounding recentered numbers
across runs is an estimate, not a within-run measurement, and nothing in the
ledger does it.

| post-T2a protocol share (recentered) | s | % |
|---|---|---|
| **rounds (26)** | 338.2 | **53.7%** |
| lifted witness | 132.7 | 21.1 |
| `chain_verify` | 48.5 | 7.7 |
| `end_piece_check` | 36.5 | 5.8 |
| `lift_commit` | 27.0 | 4.3 |
| setup | 18.9 | 3.0 |
| `alpha_public_table` | 12.8 | 2.0 |

### Consequence: the T2-before-T1 decision rested on numbers T2a has now spent

The order was changed to T2 before T1 on the post-R reading of T2 ≈ 175 s /
21.7% against T1 ≈ 127 s / 15.7%. T2a has now *taken* most of T2's headroom.
What is left of the card:

* **T2b** (loop interchange + incremental node fold) removes the fold's two full
  `Ext4` multiplies — 38 of ~257 base multiplies per node per pair, **~14.8% of
  round arithmetic** ≈ 50 s ≈ **8% of protocol** — plus whatever the interchange
  buys on memory traffic (brief 5 priced S5b at 5.4%). Its proof is a loop-nest
  restatement with a 33-wide vector accumulator, times the variants.
* **T1** still has the whole lifted-witness phase: 132.7 s / **21.1%** of
  protocol, down to the card's projected 15–20 s ≈ **18% of protocol** — and it
  keeps the non-time value T2 never had (removes wall W2, unblocks I6b and I7).

So on measured value T1 is now roughly **twice** T2b, and it was already ahead on
everything else. **Left as written pending the user's decision**, exactly as the
pre-R entry was: the grounds for the T2-first decision were the numbers, and the
numbers moved because T2a landed — but reordering the user's own decision is not
mine to make.

Cheap pickup available either way: **candidate T2c** (scratchpad draft).
`round_value_zero`'s fold computes `one_minus * lo + node * hi` as two *full*
`Ext4 × Ext4` multiplies, yet `node = ofBase(t)` and
`one_minus = Ext4::ONE − node = ofBase(1 − t)` — both scalars are in `ofBase`'s
image, so the mixed `Mul<Ext4> for Fp` impl applies: 2 × 4 base multiplies
instead of 2 × 19. That is ~30 of the 38 T2b would remove, **~11.7% of round
arithmetic ≈ 6% of protocol**, with no new constructs, no new specs, and one
rewrite of proof content (`ofBase` is a ring homomorphism). T2b subsumes it but
needs the interchange first; T2c does not.

### Two owed items paid here

* **The `M ζ = y` assertion is now gated.** It lives in `pin_instance`, the setup
  helper *both* chain tests share, so it could not simply be deleted; it is now
  behind a `check_relout` parameter — `true` from `the_honest_chain_verifies`,
  where a semantics check belongs, `false` from the profile. It is a dense `Rq`
  matrix–vector multiply at 5 × 40 976, ~205 000 `Rq::mul` calls, and it costs
  ~150 s, a sixth of a profile run spent on work the protocol never does.
* **The profile has a control.** `profile_control()` times a fixed
  allocate-and-fill in the **frozen** `hachi-genesis` crate — immune to
  candidates by construction, since `check-genesis` pins that copy to git — at
  the start and again at the end. Same choice, and for the same reasons, as
  `benches/support/mod.rs`'s `PolyVec::zeros(CONTROL_N)`: fixed-shape, allocating,
  on no hot path. Sized from measurement, not guess: `_control/*/8192` reads
  33.4 ms, so 50 reps ≈ 1.7 s, ~3.3 s per run for both readings. Two readings
  rather than one precisely because of the +29% tail above — the offset drifts
  within a run, and one reading cannot see that.

## Candidate T2c: the fold's scalars belong in the base field (2026-09-16)

The specification's two-point fold is `fold w T y = (1 − T)·w(lo y) + T·w(hi y)`,
and the crate evaluates it at the 33 nodes `T = 0 … 32`. `round_value_zero`
takes `T` as an arbitrary `Ext4`, so it pays two **full** quartic
multiplications per pair per node — nineteen base multiplications apiece. But
`round_values_zero` knows something `round_value_zero` cannot: its node is
`Fp::new(t)`, and therefore `1 − T` is `Fp::ONE − Fp::new(t)`. *Both* scalars
are in `ofBase`'s image, so each product is the **mixed** `Mul<Ext4> for Fp`
impl — four base multiplications. 30 of ~257 base multiplications per node per
pair, which predicted −11.7% of the round arithmetic.

Measured `20260916T1729+0200` (exit 0, A/B bias 4.0%, every control noise):

| row | `cand vs now` | verdict |
|---|---|---|
| `sumcheck/round_values_zero/1024` | **−13.9%** | faster |
| `sumcheck/round_poly_zero/1024` | −13.5% | faster |
| `sumcheck/honest_compute_g/1024` | −13.1% | faster |
| `sumcheck/honest_compute_g_split/1024` | −13.1% | faster |
| `sumcheck/round_value_zero/1024` | −0.7% | **noise** |

That last row is the candidate's **built-in control**: it is the arbitrary-node
function, left untouched under rule 12, so it must *not* move while its caller
does. Same device as `zerocheck/h_zero` for T2a, and this time it was free.

### Two things this candidate taught the harness and the loop

**A benched item's signature cannot change.** This is new, and it is a design
constraint on candidates rather than a bug. `benches/*.rs` defines each case
body once inside `define_cases!(<mod>, <crate>)`, instantiated against **all
three** variant crates, so one source expression must typecheck against the
current code *and* against the frozen first translation. The natural form of
T2c was `round_value_zero(w, eq, node: Fp)`, and the bench body's
`hc::sumcheck::round_node(7)` returns `Ext4` in `hachi_genesis` — which is
frozen and cannot be brought along. So the optimization moved to the caller
that already has the cheaper type, which is also the caller that *knows* the
node is `Fp::new(t)`. Written into `perf-loop` § "Before the first iteration"
with the three ways out ranked; route 1 (move it to such a caller) is best
because it costs no new item, no genesis freeze, no bench-case work, and
usually leaves the changed function's spec statement alone. Here it did exactly
that, and it handed over the control row as a bonus.

**The first run was thrown away, correctly.** Run 1 (`20260916T1708+0200`) came
back exit 2: `_control/ring` measured **+18.0%** against genesis on *identical
code*, against a 10% limit, so every verdict was `unusable` and nothing was
recorded. The cause is worth keeping: the genesis controls split into two
clusters (`ring`/`ringswitch`/`sumcheck` at ~38.8 ms, the other seven at
~44–48 ms), and the run had started six minutes after a 14-minute full-load
chain profile ended. Run 2 waited for load < 1.0 first and read bias 4.0%. The
threshold was never touched, and the unusable run has its own `bench-unusable`
ledger row — including the one thing it got wrong, `honest_compute_g_split` at
+0.8%, which would have been `rejected-mixed` had it been believed. It was the
bias, and the clean run puts that row at −13.1% with the rest.

### The proof

`round_values_zero_spec`'s **statement does not move.** It is pointwise in the
node — `∀ t : Fin 33, toExt out[t] = rangeSumZero … (t : F)` — so it says
nothing about how the 33 values were produced, and T2c changes only that. What
forced a restatement was Aeneas: a second loop appeared, so the outer loop was
renamed `round_values_zero_loop` → `_loop0` positionally, and the old proof
stopped compiling. The new `round_values_zero_loop0_loop0_spec` is
`round_value_zero_spec`'s loop with `toExt node` read as `ofBase (toK node)`,
and the single line of new content is that `ofBase` is a ring homomorphism:

```lean
have hom : (Ext.ofBase (toK one_minus) : F) = 1 - Ext.ofBase (toK node) := by
  rw [hone, ← phiF_apply, ← phiF_apply, map_sub, map_one]
```

`Opt.lean` carries the same fact as `round_values_zero.optFold_eq_spec`, at the
scalar level, which is the honest granularity: T2c is a representation change
on the scalars, not an algorithm.

No new items, so **no genesis freeze** — genesis stays at 312 frozen items.
`make build` green, 297 audit lines on the three standard axioms only, 0 axioms
in `Generated.lean`, extraction deterministic, 199 tests, `bench-check` green.

One `Ext.ofBase` annotation was needed (`… : F`) because it is polymorphic in
the extension and a standalone `have` has nothing to infer from. And the stale
`Generated.olean` trap fired a **third** time this session: `lake env lean`
reported the new loop names as unknown identifiers until `lake build Generated`
ran. It is worth treating `make extract && lake build Generated` as one step.

## The pre-bump sweep: 92 rows, 35 of them ≥50% faster than genesis (2026-09-16)

Banked deliberately, because the cpoly pin bump re-baselines `vs genesis` and
this is the last full measurement on the old pin `583cfaf`. Run
`20260916T1817+0200-af4f447d`, started on load **0.45** — the quietest machine
of the session — **usable**, A/B bias 4.3%, 1 h 23 m.
`logs/runs/full-20260916-preBump.json`.

92 rows: **62 faster, 28 noise, 2 slower**, and **35 rows are at or beyond −50%**
against the frozen first translation.

### What T2a and T2c did to the cumulative record

| row | 2026-09-16T1210 sweep | this sweep |
|---|---|---|
| `sumcheck/round_values_zero/1024` | −18.5% | **−61.2%** |
| `sumcheck/round_poly_zero/1024` | −18.4% | −60.0% |
| `sumcheck/honest_compute_g/1024` | −18.1% | −59.6% |
| `sumcheck/honest_compute_g_split/1024` | −18.1% | −59.2% |
| `sumcheck/round_value_zero/1024` | −18.7% | −55.5% |
| `zerocheck/range_product/16` | −26.1% | −63.2% |
| `zerocheck/h_zero/14` | −98.4% | −98.4% |

Two of these rows say something the within-run numbers cannot.

**`round_value_zero` improved to −55.5% although T2c deliberately did not touch
it.** No contradiction: T2c's within-run control read −0.7% for exactly that
row, and `range_product` — which T2a rewrote — is its callee. The two
instruments measure different things. `cand_vs_now` isolates the one candidate;
`vs genesis` accumulates every candidate that ever touched the row *or anything
it calls*. Keeping both is what makes the control row meaningful and the
cumulative claim honest at the same time.

**`h_zero` is unchanged to four decimal places across the two sweeps.** That is
rule 12 working, not a null result: `h_zero` routes through
`range_product_base`, the `Fp` variant, which T2a left alone on purpose so that
this pair could serve as a cross-check. Candidate F's `rejected-mixed` came from
exactly these rows, and they have not moved since.

### The two `slower` rows are the band again, and one of them is not new

* `gadget/digit_decompose/8` — **29.3 ns**, an order of magnitude *below* the
  certified 100 ns–2 µs band's floor. The previous sweep read it **−1.4%,
  noise**, at 26.3 ns, and nothing has touched `gadget` since. Noise.
* `zerocheck/w_table_z_row/3` — **6.1 ns**, the timer floor. The previous sweep
  **also** read it `slower` (+8.8% at 5.91 ns), so this is a persistent artifact
  and not a new regression; the earlier sweep's entry already named it.

The rotation is the band's signature. Last sweep the pair was
`quadeval/in_sb` + `w_table_z_row`; this time `gadget/digit_decompose` +
`w_table_z_row`. The 6 ns row is always there, and the second slot moves around
among sub-band rows between runs.

### A process note on reading a long run

I checked this sweep's progress at 21:01 by looking at the last `Benchmarking`
line and concluded it was still going. It had finished at **19:40** — the
`# exit 0` marker was already in the log. Grep for the exit marker, not for the
last line of progress output; criterion's trailing `Analyzing` line looks
identical whether the run is mid-flight or long done.

## A second session was benchmarking on this machine, and it changes a diagnosis (2026-09-16)

Discovered when the commit gate refused a commit with "a benchmark is running"
while nothing was running *here*. It was running in
`/home/pablo/Documents/internship-eth/hachi-ntt/AeneasArklib` — a **separate
clone** of this repository (its own `.git`, not a worktree), at `90120fe`, with
an NTT candidate in progress (`hachi/benches/candidate/src/ntt.rs`,
`NTT_EXECUTION_PLAYBOOK_v2.md`), running
`cargo bench --benches -- ring/|linalg/|evalsplit/|gadget/|_control`.

**The correction.** Candidate T2c's first bench run failed the bias veto with
`_control/ring` at +18.0% on identical code, and I attributed that to "the
machine was still in the thermal tail of a 14-minute chain profile" — in the
`bench-unusable` ledger row and in the T2c entry. A concurrent benchmark in
another clone is a **better explanation**, and the filter that session runs
includes `ring/` and `_control` specifically. I cannot prove which it was after
the fact, and the ledger is append-only so the row stands as written; this is
the qualification. The remedy was the same either way — discard the run, wait,
repeat — which is why the verdict is still right even if the reason was not.

**The process hole.** `perf-loop` § "Before the first iteration" says to check
the machine is quiet with `ps -eo command | grep -c "[b]in/lean"` plus the load
average. I ran exactly that, saw load 1.88–2.28, and attributed it to Firefox
and to decaying tails of my own runs. Neither check looks for `cargo bench`
**machine-wide**, and the skill's own rule — "one criterion session or one
`lake build` at a time, **repo-wide**" — plainly intends to cover this case
while its wording does not. A second clone is outside "repo-wide" as written and
squarely inside what the rule is for.

The pre-bump profile itself is **clean**: it exited 21:14:24 and that bench
started ≈21:15:28, about 64 s later, with no overlap.

**Also worth knowing for anyone working in two clones at once**:
`logs/ledger.jsonl` is append-only *and* checked against HEAD, so two sessions
appending rows independently will fail `make ledger-check` for whichever merges
second. Same hazard for `NOTES.md` and the skill files.

## The cpoly pin bump: 583cfaf → d7e26bb, and what it cost to prove (2026-09-16)

The bump the plan had been deferring since candidate P. Upstream HEAD of
`tobias-rothmann/AeneasCompPoly`, four commits on from our pin ("SPEED-UPs",
"Stamp F1 genesis baseline", "squaring and doubeling", "clean-up skills").

### What it actually contains

More than the plan's one-line note ("upstream has a delayed-reduction `Ext4`
multiply") suggested:

* **`reduce_wide(low, high)`** — a pseudo-Mersenne reducer. *This is card T7.*
  `2^32 ≡ 99`, `2^64 ≡ 9801 (mod q)`, so `low` folds at 32 bits twice and `high`
  enters scaled by `9801`; then **one** conditional subtraction. Upstream's
  contract is `high.val ≤ 7`, not the card's "`hi ≤ 6`".
* **`Ext4::mul` rewritten**: sixteen products accumulated into four unreduced
  two-word `(low, high)` pairs, then four `reduce_wide` calls — instead of
  reducing after each of nineteen base multiplications.
* **`Fp::add`, `Fp::sub`, `Fp::neg` rewritten** to conditional subtracts and a
  zero branch. `Fp::mul` is unchanged (still `(a*b) % P`).
* **`eval_mle_layer`'s fold made affine**: `lo + x0·(hi − lo)` instead of
  `(1 − x0)·lo + x0·hi`. That is **brief 5's S5b**, implemented upstream rather
  than by us, and it dropped the `one_minus` parameter.
* `Ext4::square` and `mul_by_w` exist upstream but **are not in our model**,
  because the whitelist follows only what the crate *reaches* and hachi does not
  call them yet. `Ext4::square` is card T13, still available, now cheaper.

### `cpoly.field.W` left the model

The sharpest consequence, and not one I predicted. The new `Ext4::mul` folds the
`Y^4 = 2` wrap into `add_double_product` rather than multiplying by a `W`
constant, and the only upstream reader of `W` that remains is `mul_by_w`, which
we do not reach. So `W` is simply *absent* from `Generated.lean` — the same
failure mode candidate P hit with `Shared1UnivariatePoly…mul`, and the third
time NOTES § "The model contains what the crate *reaches*" has earned its place.

It took `cpoly_W_val`, `red_W` and `toK_W` with it, and it cost a **pin**:
`Check.lean` § 2's `cpoly.field.W = params.EXT_W`, which asserted that our
extension constant is cpoly's. That claim has moved rather than vanished —
`params.EXT_W = 2#u64` is still asserted, and the `2` on the cpoly side is now
carried by `add_double_product_spec`'s postcondition — but what is genuinely
lost is *the equality of the two constants as constants*. Recorded in § 2 in
those terms rather than quietly deleted.

### The proof work: transcription, and why not import

`ext_mul_spec`'s statement upstream is **byte-identical** to ours, so nothing
downstream in hachi moved; only bodies did. Every spec needed already exists
upstream in the same `Red`/`Reduced`/`toK`/`toExt` vocabulary, because hachi's
`Ext.lean` derives from cpoly's.

It is **not importable**, for a concrete reason: cpoly's Lean package is on
Lean/Mathlib **v4.32.0** on its own aeneas fork (its lakefile says upstream has
no 4.32.0 release), while hachi and ArkLib are on **v4.33.1**, and one Lake
build holds one toolchain. Compounded by the standing decision never to touch
the aeneas fork for hachi. So these are *our* proofs of upstream's code,
audited in § 4 like everything else.

What landed, by file:

| file | change |
|---|---|
| `Field.lean` | `fp_add_spec`, `fp_sub_spec`, `fp_neg_spec` re-proved for the branching bodies; **new**: `red_mul_fits_u64`, `carryK`, `wideK`, `u64_size_toK`, `overflowing_add_toK`, `add_product_spec`, `add_double_product_spec`, `reduce_wide_spec` |
| `Ext.lean` | `cpoly_W_val`/`red_W`/`toK_W` removed; `ext_mul_spec` re-proved on `wideK` |
| `ZeroCheck.lean` | `eval_mle_layer_loop_spec` re-proved for the affine fold, `one_minus` binder dropped |
| `Check.lean` | § 2's `add`/`sub` body pins rewritten, the `W` pin retired with its reasoning, § 4 gained six audit lines |

`Fp::mul` needed nothing, which is the useful negative: `fp_mul_spec` did not
break, so the 19-multiply → accumulator change is entirely above the base field.

### Four API-drift fixes, all mechanical

* `linear_combination` is **not** available — `Field.lean` imports only
  `Generated` and `Mathlib.Data.ZMod.Basic`. Added
  `import Mathlib.Tactic.LinearCombination`.
* `U64.max` does not unfold for `omega`; `Std.U64.max_eq` does (upstream's
  `norm_num [U64.max_eq]` carries over under the `Std.` prefix).
* Upstream's `P`/`K` are hachi's `q`/`ZMod q`, and upstream reaches the modulus
  literal through `Hachi.fieldSize`, which hachi does not have — `q` is already
  the literal, so those steps become `rfl`.
* One `step` side goal that 4.32 needed an explicit bullet for is discharged
  automatically here, so the bullet had to go (`reduce_wide_spec`'s subtraction).

### Two process notes

**A regex is not a transcription.** My first attempt substituted `K → ZMod q`
and `P → q` across 321 extracted lines mechanically. It unbalanced parentheses
inside `change` expressions, cut a declaration in half, and left a dangling
docstring — twelve errors that took longer to read than writing the blocks by
hand did. The second attempt went spec by spec, compiling each before starting
the next, and every one landed first or second try.

**The stale `Generated.olean` trap fired for the fourth and fifth time today**,
now including a *second* flavour: after editing `Field.lean` I ran
`lake env lean lean/Ext.lean`, which type-checks against the stale `Field.olean`
and reported the brand-new `@[step]` lemmas as "could not find a local
assumption or a theorem to apply". `lake env lean` never rebuilds dependencies.
The rule is wider than `make extract && lake build Generated`: **after editing
any module, `lake build <that module>` before `lake env lean` on a downstream
one.**

Gates on the bumped tree: `make build` green (no errors, no `sorry`), **303**
audit lines on the three standard axioms only, **0** axioms in `Generated.lean`,
extraction deterministic, 199 tests pass, genesis intact at 312 frozen items.
`check-candidate` correctly *refuses* until this lands as a commit — the slot's
`Cargo.toml` is git-pinned precisely so a pin change cannot arrive as a loop
edit.

### What the bump measured: a trade, not a pure win

The harness cannot see a cpoly bump at all — `hachi`, `benches/genesis` and
`benches/candidate` pin the same rev *by design*, so `cand_vs_now` and
`vs_genesis` both move together and read nothing. And holding `genesis` on the
old rev to recover a real `vs genesis` number is **impossible**, not merely
unwise: `define_cases!`'s body has `use cpoly::{Ext4, Fp, UnivariatePoly}`
unparameterized by the variant, so two revs are two distinct `Ext4` types and
the bench harness stops compiling. That makes the same-rev pin load-bearing for
the *build*, which is stronger than what `Cargo.toml`'s "no drift" comment
claims.

So the measurement is the profile pair, `-preBump` (567.2 s) against `-postBump`
(477.2 s), and the verdict is `accepted-surface` with no within-run number:

| phase | pre | post raw | Δ raw | recentered | Δ |
|---|---|---|---|---|---|
| **rounds (26)** | 299.3 | **212.8** | −28.9% | 199.1 | **−33.5%** |
| **lifted witness** | 119.4 | **132.0** | **+10.6%** | 123.5 | **+3.4%** |
| `alpha_public_table` | 12.8 | 8.4 | −34.4% | 7.9 | −38.6% |
| `final_check` | 7.7 | 4.7 | −39.0% | 4.4 | −42.9% |
| `honest_compute_y` | 4.0 | 2.5 | −37.5% | 2.3 | −42.5% |
| `end_piece_check` | 33.8 | 29.6 | −12.4% | 27.7 | −18.0% |
| `chain_verify` | 40.5 | 37.4 | −7.7% | 35.0 | −13.6% |
| `lift_commit` | 26.9 | 26.5 | −1.5% | 24.8 | −7.8% |
| **total** | 567.2 | **477.2** | −15.9% | 446.4 | **−21.3%** |

The gains land exactly where `Ext4` multiplication lives, which is the
prediction the op count made: rounds −33.5%, `alpha_public_table` −38.6%,
`final_check` −42.9%, `honest_compute_y` −42.5%.

**But the lifted-witness phase got slower** — the only phase that did, +10.6%
raw and still +3.4% recentered. That phase is `long_mul`/`div_by_modulus`-bound,
i.e. heavy in `Fp::add`/`Fp::sub` rather than in `Ext4::mul`, and those two are
precisely what the bump changed from a `%` by a **compile-time constant** — which
LLVM lowers to branchless multiply-shift — into a **data-dependent branch** that
can mispredict. Stated as a hypothesis, not a finding: it fits the phase
breakdown exactly, and confirming it needs a perf-counter run this repository has
no harness for. Either way the honest summary is that the bump is a **trade**,
and it is a very good one: about −21% of protocol for about +3% on a phase worth
21% of it.

### The control moved, and reading it beat re-running it

`profile_control()` read 500.7/530.3 ms pre-bump and 547.4/554.7 ms post-bump —
a **+7–9% shift in level**, which by the rule written into it demanded
investigation. Its within-run spread actually *improved* (+5.9% → +1.3%), so the
run was internally more stable; only the level moved.

Resolved by reading the control rather than burning another eight-minute run:
`PolyVec::zeros` pushes `Rq::zero()`, and `Rq::zero` pushes `Fp::ZERO`, a
`const`. **The control calls no cpoly function at all**, so the bump cannot have
changed its machine code, and the movement is machine state. That is the check
doing its job and then being answered by argument instead of by more
measurement.

One limitation this exposed, and it belongs in the record: the control is
**allocate-and-fill, i.e. memory-bound**, while every phase it is being used to
recenter is **compute-bound**. Using it to correct compute drift is an
approximation, not a calibration. A second, compute-bound control — a fixed
number of frozen-genesis `Rq::mul`s, say — would make the recentering honest
rather than indicative. Owed.

Cumulative against the 1 882.2 s genesis baseline: **3.94× raw / 4.22×
recentered** — and as always the recentered figure compounds hand corrections
across runs, so it is an estimate, not a measurement. Read it as ~3.9–4.2×.

## Two process failures in one bench attempt, and I destroyed someone else's run (2026-09-16)

Candidate T1a1's first bench run is abandoned, and the second failure is worse
than the first.

**Failure 1: I defeated my own pre-flight check by backgrounding it.** Earlier
today I widened `perf-loop`'s "machine is quiet" check to be **machine-wide**,
precisely because a second clone (`.../hachi-ntt/AeneasArklib`) was benching and
the old check could not see it. Then I put that check *inside* a command I
launched with `run_in_background`, so its output never reached me, and launched
a `CANDIDATE=1` run onto a machine where the NTT clone had been benching for
**~15 minutes**. The run is contaminated and is discarded (`exit 2`,
`logs/runs/candT1a1-run1.log`). A gate whose result you do not read is not a
gate. **Pre-flight checks run in the foreground, always.**

**Failure 2: my kill pattern matched both clones, so I killed the run I was
trying to protect.** Having realised the contamination, I killed my own run --
correct, since the other started first and mine was corrupting it. But I used

```
pkill -f "AeneasArklib/hachi/target/release/deps"
```

and the other clone's path is
`.../hachi-ntt/AeneasArklib/hachi/target/release/deps/...`, which **contains
that same substring**. So it killed the NTT session's benchmark too. That run
had started at 23:10 and was 19 minutes in with no JSON written (its last
output, `ntt-final-core.json`, is from 23:09), so roughly nineteen minutes of
someone else's measurement is simply gone, and the thing I was trying to avoid
is exactly what I caused.

**Kill by PID, never by a path substring**, when two checkouts of the same
project share a directory layout -- which is the normal case for a worktree or a
second clone. `pkill -f` over a repo path is not specific to a repo.

Consequences taken: no further benchmark runs from this session tonight, since I
cannot verify machine exclusivity without inspecting processes, and process
inspection is now (rightly) refused to me. The bench-case work below is
separable and lands on its own; candidate T1a1 stays unaccepted and unmeasured.

## The lift rows now measure the shape the prover actually builds (2026-09-17)

**User decision, 2026-09-17**, taken on the question raised in the previous
entry: the dense four-column lift cases are **replaced** by block-shaped ones,
rather than the accept rule gaining a third exception.

`quadeval::rlin_stmt` never emits a dense `M`. It builds c1 as `[D | 0 | 0]`,
c2 as `[0 | B | 0]`, c3 as `[Gᵀb | 0 | 0]`, and at the pin
(`cw + ct + cz = 8192 + 8192 + 40 960 = 57 344`) rows c1–c3 are **86% literal
`Rq::zero()`** — those are `Rq::zero()` pushes in `src/quadeval.rs:862`+, not a
claim about an input distribution. The bench built its REDUCED statement with
`matrix_of`, dense random, four columns. So the rows priced work the prover
never does.

Retired: `ringswitch/c_row_sum`, `ringswitch/c_quotient`,
`ringswitch/honest_lift_witness` (4 dense columns).
In their place: `…/c_row_sum_blocks`, `…/c_quotient_blocks`,
`…/honest_lift_witness_blocks` at `LIFT_PROVER_COLS = 28` — the pin's own
`cw : ct : cz = 1 : 1 : 5` proportions, so 4 dense entries and 24 zeros, 86%
zeros as at the pin, with the dense part the same size the old rows used.

**The ids changed on purpose.** Silently redefining `/4` would have left every
future reader comparing two different computations under one name. The cost is
stated rather than hidden: those rows' `vs genesis` history **stops here**, and
its last reading is the pre-bump sweep `logs/runs/full-20260916-preBump.json`
(run `20260916T1817+0200-af4f447d`).

**The dense cases were not wrong, and that is why this needed a decision.**
Candidate R was accepted on exactly those rows at −43%, and correctly so: R sped
up `long_mul` itself, which is structure-independent, and a dense matrix is a
perfectly good instrument for that. They are the right instrument for
structure-independent candidates and the wrong one for structure-exploiting
ones. Carrying both would have meant the accept rule ("every measured row of the
target reads `faster`") permanently blocking every structure-exploiting
candidate, since the dense row can never improve. The project chose one
instrument over a rule exception — and notably, the alternative would have been
the **first** "no `slower`" relaxation granted to a candidate whose deliverable
*is* speed; the two existing ones (`accepted-wall`, `accepted-surface`) are both
keyed to deliverables that are not.

This unblocks T1a1, T1a2 and T1a3, all three of which are structure-conditional.

## Integrating the verified NTT: what had to be checked, and what came free (2026-09-17)

Merged `ntt/experiment/verified-ntt-mul` at `45987ea` into the main line on the
user's instruction ("incorporate it in here if you consider it will make a
speedup"). It does, and it merged **conflict-free**.

### The judgement: yes, but the row is not the protocol

Comparable through the shared genesis baseline -- both runs measured genesis
in-run, 1 496 µs against 1 433 µs, 4% apart, so the ratio is sound:

| case | mine vs genesis | NTT vs genesis | NTT over mine |
|---|---|---|---|
| `ring/mul/1024` | −55.0% | **−82.5%** | **~2.6×** |
| `linalg/mat_vec_mul/16` | −54.7% | −75.1% | ~1.8× |
| `linalg/dot/16` | −55.3% | −75.5% | ~1.8× |

**But the protocol effect is far smaller than the row**, and saying so is the
point. The commit changes `ring.rs` and adds `ntt.rs`; it does **not** touch
`ringswitch.rs`. So `long_mul` is unchanged and the lifted-witness phase —
**27.7% of protocol** — gets nothing, and the rounds (44.6%) are `Ext4`-bound
and get nothing either. What is `Rq::mul`-bound is `lift_commit` (5.6%), setup
(4.1%) and the end-piece/verify path (~6–8%): call it **~11% of protocol** at
2.6×. The big prize is a *follow-on* — the same `ntt.rs` machinery applied to
`long_mul`, the unreduced `2N−1`-wide product, which is the 27.7% phase.

Card C ("Ceiling, not a candidate: multi-prime NTT … the proof is months") is
**wrong and should be struck**. It is done, it is proved, and it is not the
five-prime scheme the card priced.

### What it does, and why `Z_q` was never an option

`q − 1 = 2² · 1 073 741 799`, so `v₂(q−1) = 2`: the largest power-of-two root of
unity in `Z_q` has order 4, and `v₂(q⁴−1) = 4` so `cpoly`'s quartic extension
does not rescue it. A radix-2 negacyclic transform of length `N` needs
`2N | q−1`. So there is no NTT in `Z_q` at all, and `q` is not ours to change.

Instead the negacyclic product is computed as the **integer** polynomial product
it already is, in three auxiliary NTT-friendly primes, with the exact integer
coefficients recovered by CRT and reduced mod `q` once at the end. The sign
problem — `v_k = posSum − negSum` is signed, and CRT reconstructs a residue
class — is handled by an offset: `W_k = posSum + N·q² − negSum` lies in
`[0, 2·N·q²]`, a natural number, so nothing branches on a coefficient's sign.
It reuses **candidate Q's own bound lemmas**, `posSum_le` and `negSum_le`.

### The four things I checked before trusting the merge

1. **`mul_spec`'s statement is byte-identical** to the pre-merge one, so nothing
   downstream of `Ring.lean` moves. Their commit message claimed this; verified
   by diffing the statement at `1eb6a57` against the merged file.
2. **Zero direct `cpoly` body unfolds** across all seven new proof files — no
   `rw [cpoly.field.Fp.Insts.CoreOpsArith*.{add,sub,mul,neg}]` anywhere. That is
   what made them survive my cpoly bump: the bump changed those *bodies* and
   re-proved the specs, but left every spec *statement* alone, and the NTT
   proofs go through the statements.
3. **`45987ea` is sorry-free in all seven files**, so the uncommitted
   refinements left in that clone (AuxTransform 74 lines, Ring 22) are polish,
   not gap-fillers. They were **not** taken: uncommitted work in someone else's
   checkout that I cannot verify.
4. **The `d7e26bb` cpoly pin survived** in all three manifests.

### What came free, and one genuine surprise

`make extract` reported **`unchanged`** on the first run. The auto-merged
`Generated.lean` was already byte-identical to the true extraction of the merged
Rust against the new cpoly — because their NTT regeneration and my cpoly-bump
regeneration touched **disjoint regions** of the artifact (`src/ntt.rs` and
`src/ring.rs` sections against the `cpoly::field` section, whose `Source:` lines
carry the rev). A derived artifact merging correctly is luck worth noting rather
than relying on; the re-extraction is what confirmed it, and it would have
regenerated silently had it been wrong.

Gates on the merged tree: `make build` green (no errors, no `sorry`), **306**
audit lines on the three standard axioms only, **0** axioms in `Generated.lean`,
extraction deterministic, 199 tests pass, **genesis intact at 352 frozen items**
(up from 312 — `ntt.rs`'s items arrived stamped). `harness.py`'s `MODULES` is now
**13**, `ntt` added, which every future slot copy must respect.
