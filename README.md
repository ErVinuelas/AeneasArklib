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

> **Status: scaffold.** Workstream 0 is complete — the toolchain round-trips
> (`make setup && make extract && make build`), the field layer is wired, and the
> parameters are fixed and checked. No operation of the scheme is implemented
> yet, so there are no equivalence proofs yet either. [`NOTES.md`](NOTES.md)
> records what was decided and what was deferred.

## Usage

```sh
make setup     # install everything: elan, the Lean dependencies, rust, the extraction binaries
make build     # check the proofs
make extract   # regenerate hachi/lean/Generated.lean from src/
make run-bench # time every operation
```

`make` on its own lists the targets.

A fresh clone needs `make setup` once. It takes a few minutes, and installs
nothing system-wide: the extraction binaries go in `./toolchain`, the rest into
the per-user directories elan and rustup manage.

`make build` fails if any declaration under `lean/` uses `sorry`, or if `sorryAx`
turns up in the axiom dependencies `Check.lean` prints.

`make clean` drops the build output and keeps the downloads. Overriding
`CHARON=` or `AENEAS=` on the command line points `make extract` at binaries kept
elsewhere.

## Layout

```
Makefile              setup, build, test, extraction, benchmarks
NOTES.md              decisions, spec observations, Aeneas surprises
toolchain/            charon and aeneas, put there by `make setup`; not in git

hachi/
  Cargo.toml          the `hachi` crate: a library, one dependency (cpoly)
  src/                the Rust implementation
    params.rs         every parameter of the scheme, as consts
    smoke.rs          TEMPORARY: the cross-crate extraction probe
  tests/              Rust-side semantics tests, one per src/ module
  benches/            criterion benchmarks, one file per src/ module
    genesis/          the frozen first translation; append-only, never edited
    candidate/        the optimization loop's A/B slot

  lakefile.lean       Lean library, srcDir `lean/`
  lean/
    Generated.lean    the extracted model -- DERIVED by `make extract`, never hand-edit
    Check.lean        audit: the specs are not vacuous, and no `sorryAx` hides under one
```

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
