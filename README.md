# AeneasArklib

A Rust implementation of the Hachi lattice-based multilinear polynomial
commitment scheme ([NOZ26]), with Lean proofs that the Rust computes exactly what
[ArkLib](https://github.com/Verified-zkEVM/ArkLib)'s specification of Hachi says.

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

Each function in `hachi/src` is a translation of an ArkLib definition.
[Aeneas](https://github.com/AeneasVerif/aeneas) turns the Rust into a Lean model
(`hachi/lean/Generated.lean`), and the proofs show that every modelled function,
under its stated preconditions, terminates without error and returns what the
ArkLib definition returns. The
project follows [AeneasCompPoly](https://github.com/tobias-rothmann/AeneasCompPoly)
in structure and method, and uses its `cpoly` crate for the coefficient field.

## Status

The work is complete.

* **Implemented and proved.** The commitment scheme (commit, open, verify) and
  every step of the evaluation protocol: QuadEval, the ring switch and its lift,
  the zero check, the paired sumcheck, the end piece, and the composed honest
  prover `chain_open` and verifier `chain_verify`. The top-level theorems
  include perfect correctness: an honest commitment and opening are accepted.
* **Audited.** `make build` checks every proof and fails on any `sorry`.
  [`Check.lean`](hachi/lean/Check.lean) prints the axioms behind each of the
  779 proved specs: only Lean's three standard axioms appear. All 155 functions
  that mirror an ArkLib definition have a proved spec (`make spec-check`).
* **Tested.** 262 tests pass. 52 more are `#[ignore]`d, each tagged with why:
  27 `instrument:` (timing probes), 8 `scale:` (correctness at the paper's
  parameters, `make test-scale`, about 25 minutes) and 17 `scale-xl:` (need
  more memory than a 30 GiB machine).
* **Fast.** At the paper's parameters (ℓ = 30, 1024 blocks) the prover went
  from 1170.8 s to **183.2 s** through a series of optimizations, each one
  benchmarked and re-proved before it landed. The verifier takes 4.2 s and
  the peak memory is 5.3 GiB. The end-to-end acceptance test (an honest proof
  that verifies) last passed in 221 s.

Left open by decision rather than unfinished: the full chain has no Criterion
benchmark row of its own (each of its phases has one), and `chain_open` takes
the lifted witness as an input instead of computing it with
`honest_lift_witness`. [`NOTES.md`](NOTES.md) is the full decision record.

### What the proofs cover

They prove **functional equivalence** at the pinned parameters: each Rust
function computes its ArkLib definition. They do not prove cryptographic
security, constant-time execution, or the correctness of the compiler and the
extraction. See [Trusted computing base](#trusted-computing-base).

## Getting started

```sh
make setup         # once: elan, the Lean dependencies, Rust, the extraction binaries
make build         # check the proofs
make test          # the Rust tests
make extract       # regenerate hachi/lean/Generated.lean from hachi/src
make spec-check    # every mirrored function has a proved spec
make bench-check   # the frozen benchmark baseline is intact, and every function is covered
make ledger-check  # logs/ledger.jsonl is valid and append-only
make run-bench     # time every function against its first translation
make run-profile   # the full prover and verifier at the paper's parameters, phase by phase
make test-scale    # the scale tests at the paper's parameters
```

`make` alone lists every target and variable. `make setup` installs nothing
system-wide: the extraction binaries go in `./toolchain`, everything else in
the directories elan and rustup manage. On a network that only reaches GitHub
it still works, but Mathlib then compiles from source, which takes hours.

The crate has one optional feature, `parallel`, which commits independent blocks
on Rayon worker threads. It is for native use only: the default build, the
extraction and all proofs use the serial code, and a test checks that both
produce the same commitment. `make run-profile PARALLEL=1` uses it; set the
thread count with `RAYON_NUM_THREADS`.

CI (`.github/workflows/`) runs the tests, clippy, `bench-check`, `ledger-check`,
an extraction-determinism check and the proof build on pushes to `main` (the
last two only when the Rust or Lean changed).

## Layout

```
hachi/                  the crate and its proofs
  src/                  the Rust, one module per protocol step:
    params.rs             every parameter, as a constant
    ntt.rs, ring.rs       the ring Z_q[X]/(X^N + 1) and the NTT behind its products
    linalg.rs, gadget.rs  vectors and matrices; digit decomposition and the gadget matrix
    commit.rs             the Ajtai commitment and its verifier
    evalsplit.rs          the multilinear evaluation split
    quadeval.rs           QuadEval: the fold, the honest prover, the Eq. (20) checks
    ringswitch.rs         the ring switch, the lift, and the honest lift prover
    zerocheck.rs          the zero check
    sumcheck.rs           the paired sumcheck
    endpiece.rs           the final evaluation claim
    chain.rs              the composed honest prover and verifier
  lean/                 the proofs
    Generated.lean        the extracted model; derived by `make extract`, never edit
    Field, Ext            the base field and its quartic extension
    Ring*, Ntt*, Gold*    ring arithmetic, the NTT, the Goldilocks lanes
    RqBridge, Raw32       the lift to ArkLib's `Rq`, the compact message format
    Scheme*, Balanced     linear algebra, gadgets, the commitment
    EvalSplit             the evaluation split
    QuadEval*, ZPacked    QuadEval
    RingSwitch, Rlin, Lift*   the ring switch and the lift prover
    ZeroCheck, Sumcheck*  the zero check and the sumcheck
    EndPiece, Chain       the end piece and the composed chain
    Opt*                  optimized variants and their equivalence lemmas
    Check.lean            the audit: specs are not vacuous, axioms are standard
  lean-wip/             staging for unproved statements; empty
  tests/                one test file per module
  benches/              Criterion benchmarks, the frozen baseline (genesis/),
                        and the A/B slot the optimization loop uses (candidate/)
benchmarks/             standalone campaigns: Rayon scaling, and a paired run
                        against the paper's reference implementation
logs/                   the optimization ledger, benchmark reports, proof sessions
scripts/                helpers the Makefile calls
.claude/skills/         the written procedures the agents follow
hachi-jazz/             a Jasmin integration experiment, rejected at its gate
NOTES.md                the decision record
INSTRUCTIONS.md         the catalogue of skills
```

## Design choices

**The field comes from `cpoly`.** The base field (`q = 2^32 − 99`) and its
quartic extension are taken from AeneasCompPoly's verified `cpoly` crate, not
rewritten. `make extract` passes `--include 'cpoly::_'` so that charon translates
those items instead of turning them into axioms, and `Check.lean` fails the build
if that flag is ever lost.

**Concrete, not generic.** ArkLib's Hachi is generic in its parameters. This
crate fixes all of them as constants in [`params.rs`](hachi/src/params.rs), so
each proof instantiates a generic ArkLib statement at known values. The file
says which values are forced and which are choices.

**Benchmarks against a frozen baseline.** Every function's first translation is
frozen in `hachi/benches/genesis/` and timed in the same run as the current
code, so "faster than the original" is measured, never remembered.
`make bench-check` verifies that the frozen copies match the commits they came
from, and that every mirrored function is either benchmarked or excluded with
a written reason (`benches/exclusions.toml`). Before timing, the harness checks
that both versions give the same answers.

**Pinned dependencies.** ArkLib is pinned to a commit in
`hachi/lake-manifest.json`. The Lean side of Aeneas is our Lean 4.33 port, one
commit on top of upstream `3a8586f`. It is fetched from a sibling `../aeneas`
checkout, and CI substitutes the public fork
[ErVinuelas/aeneas](https://github.com/ErVinuelas/aeneas). `cpoly` is pinned
by git revision, and the charon and aeneas binaries by `AENEAS_TAG` in the
`Makefile`. The binaries and the Lean backend must come from the same Aeneas
commit; `make setup` and `make extract` check this.

## Trusted computing base

What the proofs rely on without checking:

| Trusted | Why it can't be checked | If it is wrong |
|---|---|---|
| **The Lean kernel**, plus `propext`, `Classical.choice`, `Quot.sound` | Nothing verifies the kernel itself | A false theorem, silently |
| **Aeneas and charon** | `Generated.lean` is assumed to model `src/`; that is not proved | The proofs are about a different program |
| **The `cpoly` include list** | Nothing checks that it covers every item; a missed one becomes an axiom | A spec about an uninterpreted symbol |
| **rustc, LLVM, the OS and the CPU** | No verified Rust compiler exists | The binary differs from the proved model |
| **ArkLib's Hachi definitions and our parameter choices** | They *are* the definition of correct | True theorems about the wrong thing |

## References

* [NOZ26] Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient
  Lattice-Based Multilinear Polynomial Commitments over Extension Fields*.
* [NS24] Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments
  from Lattices*.

## License

Apache-2.0, see [LICENSE](LICENSE): the same terms as ArkLib, AeneasCompPoly
and Aeneas.
