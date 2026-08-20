# AeneasArklib

Executable Rust for Lean specifications, with a machine-checked proof that the
Rust computes what the specification says — here for the Hachi lattice-based
multilinear polynomial commitment scheme ([NOZ26]), as formalized in
[Verified-zkEVM/ArkLib](https://github.com/Verified-zkEVM/ArkLib).

```
        Lean world             ┊             Rust world
                               ┊
   ┌──────────────────┐   AI writes it  ┌──────────────────┐
   │   ArkLib specs   │────────────────►│    hachi/src     │
   └──────────────────┘        ┊        └──────────────────┘
             ▲                 ┊                  │
             │  equivalence    ┊                  │  extract via
             │  proofs         ┊                  │  Aeneas
             ▼                 ┊                  │
   ┌──────────────────┐        ┊                  │
   │  Generated.lean  │◄──────────────────────────┘
   └──────────────────┘        ┊
```

The intent is that every operation is proved to succeed and to commute with its
ArkLib counterpart. What *is* trusted is enumerated under
[Trusted computing base](#trusted-computing-base).

This repository follows [AeneasCompPoly](https://github.com/tobias-rothmann/AeneasCompPoly)
in structure and in method, and depends on it for the coefficient field.

> **Status: the bottom layers are implemented, tested and extracted; the ring layer's
> equivalence with the specification is proved, the scheme layer is stated but not proved.**
>
> Four modules are in place — [`ring`](hachi/src/ring.rs) (the negacyclic ring
> `R_q = Z_q[X]/(X^N+1)`), [`linalg`](hachi/src/linalg.rs),
> [`gadget`](hachi/src/gadget.rs) (base-`b` digit decomposition and the gadget
> matrix) and [`commit`](hachi/src/commit.rs) (the inner-outer Ajtai commitment
> and its weak-opening verifier). 66 tests pass, including perfect correctness and
> every rejection path of the verifier; `make extract` produces a model with no
> axioms and no opaque bodies; each module has a criterion bench.
>
> `make build` passes, and it now checks real equivalence proofs. Proved and
> audited: the base field ([`lean/Field.lean`](hachi/lean/Field.lean) — the four
> `Fp` operator impls total and equal to `ZMod q` arithmetic) and the whole
> coefficient level of the ring ([`lean/Ring.lean`](hachi/lean/Ring.lean) — all
> thirteen operations total, length-preserving and coefficientwise correct, `mul`
> being the negacyclic convolution and `equals`/`is_zero` being decision procedures
> proved correct in both directions), and the lift of that ring layer to ArkLib's
> `Rq Φ` ([`lean/RqBridge.lean`](hachi/lean/RqBridge.lean) — each operation's `toRq`
> is the ArkLib operation applied to the `toRq`s of the inputs, `mul` against
> `modByMonic (X^N + 1)` included).
> [`lean/Check.lean`](hachi/lean/Check.lean) additionally checks that the parameters
> discharge the specification's side conditions, and prints the axiom dependencies
> of all thirty-two proved specs: the three Lean kernel axioms, nothing else.
>
> What remains merely *stated* is all of `linalg`/`gadget`/`commit`, in
> [`hachi/lean-wip/Scheme.lean`](hachi/lean-wip/Scheme.lean). That file **typechecks**
> against the pinned specification, which is what makes it statements about ArkLib's own
> definitions rather than paraphrases of them.
> [`NOTES.md`](NOTES.md) § "The Lean side does build here" scores every claim in
> this repository as verified or not, and
> [`lean-wip/README.md`](hachi/lean-wip/README.md) says what has to happen before
> a file moves into the audited library.
>
> The protocol layer (per-link provers and verifiers) is deliberately absent: its
> ArkLib specification still has unfilled definitional parameters, so there is
> nothing stable to be equivalent to.

## Usage

```sh
make setup       # install everything: elan, the Lean dependencies, rust, the extraction binaries
make build       # check the proofs
make extract     # regenerate hachi/lean/Generated.lean from src/
make run-bench   # time every operation against its frozen first translation
make bench-check # verify that frozen baseline against git, and bench coverage
```

`make` on its own lists the targets.

A fresh clone needs `make setup` once. It takes a few minutes, and installs
nothing system-wide: the extraction binaries go in `./toolchain`, the rest into
the per-user directories elan and rustup manage. On a host whose egress policy
allows only GitHub it still works — [`scripts/install-lean.sh`](scripts/install-lean.sh)
falls back to the GitHub release assets for elan and the toolchain — with one
caveat it cannot fix: the Mathlib olean cache has no GitHub mirror, so `lake exe
cache get` fails there and Mathlib and ArkLib compile from source, which is hours
rather than minutes. `make setup` says so and continues.

`make build` fails if any declaration under `lean/` uses `sorry`, or if `sorryAx`
turns up in the axiom dependencies `Check.lean` prints.

`make clean` drops the build output and keeps the downloads. Overriding
`CHARON=` or `AENEAS=` on the command line points `make extract` at binaries kept
elsewhere.

## Layout

```
Makefile              setup, build, test, extraction, benchmarks
NOTES.md              decisions, spec observations, Aeneas surprises
INSTRUCTIONS.md       the skill catalogue: what to invoke, and what it asks
.claude/skills/       the written procedures the pipeline runs, one per directory
logs/
  ledger.jsonl        append-only candidate and campaign rows (currently empty)
scripts/
  install-lean.sh     elan + the pinned toolchain, from GitHub if the usual
                      hosts are blocked (used by `make setup`)
toolchain/            charon and aeneas, put there by `make setup`; not in git

hachi/
  Cargo.toml          the `hachi` crate: a library, one dependency (cpoly)
  src/                the Rust implementation, strictly bottom-up
    params.rs         every parameter of the scheme, as consts
    ring.rs           R_q = Z_q[X]/(X^N + 1), the negacyclic ring
    linalg.rs         vectors and matrices over R_q
    gadget.rs         base-b digit decomposition, the gadget matrix G, and G⁻¹
    commit.rs         the inner-outer Ajtai commitment, its weak verifier, the norms
  tests/              Rust-side semantics tests, one per src/ module
  benches/            criterion benchmarks, one file per src/ module
    support/          the corpus, the digest oracle, and the case macros
    harness.py        stamping, the integrity gates, and the run report
    rustitems.py      the item scanner both gates read spans from
    exclusions.toml   mirrored items that deliberately have no benchmark
    genesis/          the frozen first translation; append-only, never edited
    candidate/        the optimization loop's A/B slot

  lakefile.lean       Lean library, srcDir `lean/`
  lean/
    Generated.lean    the extracted model -- DERIVED by `make extract`, never hand-edit
    Field.lean        the base field `Fp` against `ZMod q` -- proved
    Ring.lean         the ring operations at the coefficient level -- proved
    RqBridge.lean     the lift of the ring layer to ArkLib's `Rq Φ` -- proved
    Check.lean        audit: the specs are not vacuous, and no `sorryAx` hides under one
  lean-wip/           the equivalence development, NOT a Lake root and NOT audited
    Scheme.lean       the linalg / gadget / commit obligations -- stated only
    README.md         what has to happen before a file moves into lean/
```

Each module names the ArkLib file it is a translation of, and each operation the
definition it mirrors, in its docstring. The correspondence is the point of the
repository, so it is written down where the code is rather than only in a proof.

## The field layer comes from cpoly

The base field `F_P` with `P = 2^32 - 99` (the "Hachi" prime) and its quartic
extension `Ext4 = F_P[Y] / (Y^4 - 2)` are **not** reimplemented here. They are
already written and verified in AeneasCompPoly's `cpoly` crate, and this crate
takes them as a cargo dependency pinned by commit.

Charon can follow that dependency across the crate boundary, but only when told
to: `make extract` passes `--include 'cpoly::_'`, without which every `cpoly` item
lands in `Generated.lean` as an `axiom` — an uninterpreted field with an
uninterpreted addition. [`lean/Check.lean`](hachi/lean/Check.lean) § 2 asserts the
transparent form, so the flag cannot be dropped silently. See
[`NOTES.md`](NOTES.md) § "The cpoly dependency" for the three extractions that
settled this, and § "What the cpoly dependency does *not* buy" for the one piece
of reuse that is unavailable and why.

## Concrete, not generic

The ArkLib specification is generic in all four of `(q, α, b, digits)` and pins
none of them. This crate is the opposite by design: no type parameters over the
ring or the field, and every parameter a `const` in
[`hachi/src/params.rs`](hachi/src/params.rs), so each equivalence proof
instantiates a generic ArkLib statement at fixed values. Which values are forced
by a dependency and which are choices is recorded per-constant there, and
summarized in [`NOTES.md`](NOTES.md) § "Chosen parameters".

## The benchmark baseline is checked, not trusted

Speed is the other half of the point, and it is measured against
[`hachi/benches/genesis/`](hachi/benches/genesis) — a real crate holding the
*first* translation of every operation, compiled the same way `hachi` is and
measured in the **same criterion session**, so a "vs genesis" reading is a
comparison made now rather than a remembered number. Nothing is ever compared
across runs.

That only means something if the frozen text cannot move, so it is verified
rather than promised. Every frozen item carries a `// @genesis <sha> <date>`
stamp, and `make bench-check` proves three things before any measurement is
believed:

* **`check-genesis`** — each frozen item, *attributes included*, is byte-for-byte
  what `hachi/src` held at the commit its stamp names. An edited baseline would
  make every past and present "vs genesis" figure wrong, silently and
  retroactively; `make run-bench` therefore refuses to run without this.
* **`check-candidate`** — the A/B slot
  ([`hachi/benches/candidate/`](hachi/benches/candidate)) is a *null* candidate at
  rest: byte-copies of `hachi/src`, no symlink, no extra file, `lib.rs` and
  `Cargo.toml` pinned to git.
* **`coverage --strict`** — every item whose docstring claims to mirror an ArkLib
  definition is either benchmarked or excluded *by name, with a reason*, in
  [`hachi/benches/exclusions.toml`](hachi/benches/exclusions.toml). Silence is not
  an exclusion.

Each case also has exactly one body, which the harness either times or runs once
and digests; the digests of `hachi`, the frozen copy and the candidate slot must
agree *before* anything is timed. So an "optimization" that changes an answer
fails the run instead of being reported as a speedup.

What this machinery does **not** yet have is a local calibration. No
measurement-grade run has happened here — the noise floor the accept rule uses is
inherited from [AeneasCompPoly](https://github.com/tobias-rothmann/AeneasCompPoly)
and is documented as borrowed where it is used. See [`NOTES.md`](NOTES.md)
§ "Benchmark numbers from this session are not measurement-grade", and
[`INSTRUCTIONS.md`](INSTRUCTIONS.md) for the procedures that act on all of this.

## Dependencies and pins

Lake fetches the Lean dependencies itself and records the exact revision of each
in `lake-manifest.json`, which is what makes a clone reproducible:

* **ArkLib** — `Verified-zkEVM/ArkLib`, pinned to a **commit** rather than `main`.
  The specs are the reference this development is proved against, and a spec that
  moves under a proof turns a passing build into a failing one for reasons that
  have nothing to do with the Rust. Bump with `lake update Arklib`.

* **aeneas** — `AeneasVerif/aeneas` @ `nightly-2026.07.26-3a8586f`, **upstream**.
  No fork is needed: this nightly's Lean backend requires Lean/Mathlib v4.31.0,
  which is exactly ArkLib's pin. (AeneasCompPoly does need a fork, because
  CompPoly moved to v4.32.0 — see [`NOTES.md`](NOTES.md) § "Upstream aeneas".)

* **cpoly** — `tobias-rothmann/AeneasCompPoly`, a cargo dependency pinned by
  `rev`. Pinned by commit so the frozen bench baseline cannot drift.

The charon and aeneas *binaries* `make extract` runs are a separate artifact,
pinned by `AENEAS_TAG` and `AENEAS_COMMIT` in the `Makefile` and downloaded from
the release. They have to stay on the same Aeneas commit as the backend, since
`lean/Generated.lean` is only valid against the version that produced it —
`make setup` checks both directions and `make extract` re-checks the binaries.

A Lean bump therefore moves `lake-manifest.json`, `lean-toolchain` and the
Makefile pins together, and an ArkLib bump to v4.32.0 would additionally require
an aeneas release on that Mathlib.

## Trusted computing base

The trusted computing base (TCB): components trusted because they lie outside our
verification boundary.

| Trusted | Why it cannot be checked away | If it is wrong |
|---|---|---|
| **[Lean kernel](https://github.com/leanprover/lean4/tree/v4.31.0/src/kernel)** — ~8k lines of C++, plus `propext`, `Classical.choice`, `Quot.sound` | No machine-checked proof of it exists; its C fast path for `Nat` carries every `decide` in the parameter checks | A false theorem, with no diagnostic |
| **Aeneas extraction** — [charon](https://github.com/AeneasVerif/charon) + [aeneas](https://github.com/AeneasVerif/aeneas), and their hand-written [model of Rust `std`](https://github.com/AeneasVerif/aeneas/blob/main/backends/lean/Aeneas/Std/Vec.lean) | `Generated.lean` is asserted to model `src/`, never proved: the paper proof covers a fragment, the OCaml that ran does not | The proofs are about a different program |
| **The charon whitelist** — `--include 'cpoly::_'` decides which foreign items are translated rather than axiomatized | Nothing checks that the whitelist is *complete*; a missed item becomes an `axiom`, which is visible but only if someone reads for it | A spec that quantifies over an uninterpreted symbol, and so says nothing |
| **Rust to machine code** — rustc, LLVM, linker, libc, OS, CPU | No verified Rust compiler exists; memory safety is inherited from the borrow checker, not proved | The binary betrays a correct proof |
| **The specs** — [ArkLib](https://github.com/Verified-zkEVM/ArkLib)'s Hachi definitions, and the parameter choices they are instantiated at | They *are* the definition of correct; degenerate ones would make every spec true and empty | True theorems about the wrong thing |

## References

* [NOZ26] Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient
  Lattice-Based Multilinear Polynomial Commitments over Extension Fields*.
* [NS24] Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments
  from Lattices*.

## License

Apache-2.0 — see [LICENSE](LICENSE). The same terms as
[ArkLib](https://github.com/Verified-zkEVM/ArkLib),
[AeneasCompPoly](https://github.com/tobias-rothmann/AeneasCompPoly) and
[aeneas](https://github.com/AeneasVerif/aeneas), so combining them adds no
further obligations.
