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

> **Optimization review: do not merge until proper controlled benchmarking is
> completed and reviewed.** The current-upstream allocation and fast-path changes
> are proved in Lean; runtime acceptance remains pending. The
> [full report](docs/optimization-current/REPORT.md) records all components,
> validation evidence, and the explicitly approved terminal shortness shortcut.

> **Status: the commitment scheme and every link of the protocol layer are
> implemented, tested, extracted, and proved equivalent to the specification —
> build-enforced, up to perfect correctness of the scheme and the composed
> chain's honest `open`/`verify` pair.**
>
> Thirteen modules are in place — [`params`](hachi/src/params.rs),
> [`ntt`](hachi/src/ntt.rs) (the number-theoretic transform the ring
> multiplication runs on — three auxiliary Barrett primes for the general
> path, one Goldilocks lane for the digit path, and the fused pair of
> decimation-in-frequency stages that halves the passes over the buffer),
> [`ring`](hachi/src/ring.rs) (the negacyclic ring `R_q = Z_q[X]/(X^N+1)`),
> [`linalg`](hachi/src/linalg.rs), [`gadget`](hachi/src/gadget.rs) (base-`b` digit
> decomposition, unsigned and balanced, and the gadget matrix),
> [`commit`](hachi/src/commit.rs) (the inner-outer Ajtai commitment and its
> weak-opening verifier), [`evalsplit`](hachi/src/evalsplit.rs) (the multilinear
> evaluation split), [`ringswitch`](hachi/src/ringswitch.rs) (the quotient digits
> of the ring switch, the lift, and the honest lift prover),
> [`quadeval`](hachi/src/quadeval.rs) (the QuadEval fold, its Eq. (20) checks and
> the `R^lin` adapter), [`zerocheck`](hachi/src/zerocheck.rs) (the `H₀`/`H_α`
> sides and the mixed evaluation), [`sumcheck`](hachi/src/sumcheck.rs) (the
> paired sumcheck's round polynomials, checks and loops),
> [`endpiece`](hachi/src/endpiece.rs) (the final evaluation claim's three
> conjuncts) and [`chain`](hachi/src/chain.rs) (the composed honest `open` and
> `verify` over the proved links). 236 tests pass, including perfect correctness
> and every rejection path of the verifier; 50 more are `#[ignore]`d, each
> reason opening with a tag that says which kind it is: **25 `instrument:`**
> (timing gates, kill-gates and the profile, which must never join a
> correctness sweep), **8 `scale:`** (correctness at the paper's constants,
> run by `make test-scale` — historically green in 25 minutes on 2026-09-20;
> see the current report for this branch's run) and **17
> `scale-xl:`** (past this machine, each carrying the measurement that put it
> there). `scripts/scale_tests.py --check` fails an untagged one. `make extract` produces a model with
> no axioms and no opaque bodies; every mirrored item is benched or excluded by
> name, and the 478 frozen baseline items are verified against git. The
> measured campaign history, including accepted and rejected candidates, is in
> `logs/ledger.jsonl`. Earlier campaigns reduced the pin-scale prover
> from 1170.8 s to **598.4 s** (−48.9%) at an unchanged 5453 MiB peak. Every
> accepted champion is proof-carrying — some as an optimized definition in
> [`lean/Opt.lean`](hachi/lean/Opt.lean) with its `opt_eq_spec`, the rest as a
> re-proof of the item's own spec with the statement unmoved — and no theorem
> statement was weakened to let one land (NOTES.md, the Stage 6 sections).
>
> `make build` passes, and every layer it checks is proved:
>
> * the base field ([`lean/Field.lean`](hachi/lean/Field.lean)) — the four `Fp`
>   operator impls total and equal to `ZMod q` arithmetic;
> * the coefficient level of the ring ([`lean/Ring.lean`](hachi/lean/Ring.lean)) —
>   all thirteen operations total, length-preserving and coefficientwise correct,
>   `mul` being the negacyclic convolution and `equals`/`is_zero` being decision
>   procedures proved correct in both directions;
> * the lift of that ring layer to ArkLib's `Rq Φ`
>   ([`lean/RqBridge.lean`](hachi/lean/RqBridge.lean)) — each operation's `toRq` is
>   the ArkLib operation applied to the `toRq`s of the inputs, `mul` against
>   `modByMonic (X^N + 1)` included;
> * `linalg`, `gadget` and `commit` ([`lean/Scheme.lean`](hachi/lean/Scheme.lean)) —
>   the vector and matrix operations, both directions of the gadget (including
>   `gadget_round_trip`: the extracted `gadget_mul` inverts the extracted
>   `gadget_decompose`, and the materialized `gadget_matrix` *is* `gadgetMatrix`,
>   tensor layout and all), the digit vector `digit_decompose` in specification
>   order, the four centered norms, and the commitment against the
>   specification's own `InnerOuter` definitions. `verify_weak_spec` and
>   `verify_spec` — the full verifier a caller actually invokes — are equalities
>   of *decisions*, so the rejection paths are part of the claim rather than
>   outside it, and the composition ends at `honest_verifies_full`: **perfect
>   correctness of the extracted scheme at its top-level API** — an honest
>   commitment and its honest opening pass `commit::verify`, derived-message
>   check included;
> * the multilinear evaluation layer ([`lean/EvalSplit.lean`](hachi/lean/EvalSplit.lean))
>   — the `evalsplit` module and `linalg::split_form` against ArkLib's
>   `Hachi.evalSplit`/`evalSplitEval`;
> * the balanced digit layer ([`lean/Balanced.lean`](hachi/lean/Balanced.lean)) —
>   the Hachi gadget inverse `G⁻¹` proper (balanced digits in `[-8, 7]`), the
>   bounded `z`-side digit map at `τ = 5`, the quotient digits, and
>   `commit_balanced_spec`: the honest Hachi commitment, `Hachi.commit` itself;
> * the QuadEval fold ([`lean/QuadEval.lean`](hachi/lean/QuadEval.lean)) — the
>   `z`-side gadget at `τ = 5` with its conditional round trip, the carrier entry,
>   `tensorG1`, and the Eq. (20) box and relation decisions, stated as iffs
>   against the `Prop`s ArkLib states them as;
> * the QuadEval protocol layer ([`lean/QuadEvalProtocol.lean`](hachi/lean/QuadEvalProtocol.lean))
>   — the three carriers, the honest prover's `z`/`v`/response, and both output
>   relations — over the `Ext4` extension field
>   ([`lean/Ext.lean`](hachi/lean/Ext.lean)), ported from cpoly's own development;
> * the ring-switch link ([`lean/RingSwitch.lean`](hachi/lean/RingSwitch.lean)) —
>   the quotient-row presentation change, the quotient digits, the lifted message
>   and its Ajtai commitment, and both shortness decisions, unconditionally — and
>   the `R^lin` adapter ([`lean/Rlin.lean`](hachi/lean/Rlin.lean)), whose
>   `rlin_stmt_spec` is what makes the reshaped `Jᵀ(Gᵀa)` form faithful to a
>   product that would be 320 GiB if it were ever materialized;
> * the zero check ([`lean/ZeroCheck.lean`](hachi/lean/ZeroCheck.lean)) and the
>   paired sumcheck ([`lean/Sumcheck.lean`](hachi/lean/Sumcheck.lean)) — the round
>   polynomials in both forms, the verifier's two decisions, the honest prover's
>   messages, and the round loop three ways;
> * the end piece ([`lean/EndPiece.lean`](hachi/lean/EndPiece.lean)), the honest
>   lift prover ([`lean/LiftProver.lean`](hachi/lean/LiftProver.lean)) — including
>   the one carrier this crate does not fold back into `Rq`, a `CPolynomial` of
>   degree up to `2N − 2` — and the composed chain
>   ([`lean/Chain.lean`](hachi/lean/Chain.lean)): the verifier's verdict against
>   `chainVerdict` and the honest prover's four wire messages, both through the
>   statement thread `chainStart`.
>
> [`lean/Check.lean`](hachi/lean/Check.lean) additionally checks that the parameters
> discharge the specification's side conditions, and prints the axiom dependencies
> of every proved spec — 585 `#print axioms` lines, headline specs, the
> `opt_eq_spec`/length lemmas and the helper specs alike: the three Lean kernel
> axioms or subsets thereof, nothing else. `make spec-check` reports 156 mirrored items, 156
> stated, 0 owed.
> [`hachi/lean-wip/`](hachi/lean-wip) — the staging area for statements not yet
> proved — is **empty**; its [README](hachi/lean-wip/README.md) holds the
> procedure for promoting a file, which the next translated operation will need.
> > [`NOTES.md`](NOTES.md) § "The scheme layer is proved, and checked" scores every
> claim in this repository as verified or not.
>
> Every protocol link of `Composition.lean`'s chain is translated, stated **and
> proved**: the bridge, QuadEval, the `R^lin` adapter, the ring-switch lift,
> zero-check, the sumcheck bridge, the paired sumcheck rounds, the final
> evaluation, the end piece and the honest lift prover, plus the composed
> `chain_open`/`chain_verify` pair over them. What is absent is no longer code
> but reach:
>
> * `chain_open` still takes the lifted witness as an **input** rather than
>   computing it with the now-translated `ringswitch::honest_lift_witness`. That
>   is the specification's own shape either way (`honestLiftWitnessC` is a
>   separate definition) and the proofs are stated against it as it is; making
>   the call is a deliberate decision, deferred to the optimization stage;
> * **the composed chain has no bench row.** A row has to *accept*, or the round
>   loop rejects at round 1 and neither the final check nor the end piece is ever
>   timed; accepting needs a covering cube, and the honest side sizes its widths
>   from `params`, so the smallest accepting shape is the pin's `m₀ = 26` — hours
>   per verifier call in the naive `alpha_public_table`. Every operation the
>   chain threads is measured under its own reduced row instead
>   (`chain::chain_verify` and `chain::chain_open` are excluded by name, with
>   that reason and the three walls whose removal brings the row back);
> * an **acceptance test** — an honest transcript that verifies end to end — is
>   in `tests/chain_semantics.rs` as `the_honest_chain_verifies`, at one block
>   and otherwise the pin. It is `#[ignore]`d because it costs hours (two naive
>   `alpha_public_table`s of `2^26` entries, one on each side). It has since
>   been run: it **passed** on 2026-09-14, `chain_verify = true` in 2202 s,
>   log under [`logs/runs/`](logs/runs). The plumbing, the rejection paths and
>   the cross-route identity around it are tested and passing.

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
PLAN_*.md, STAGE2_SCOPING.md, briefs/
                      local planning documents; ignored, never pushed. Code and
                      NOTES.md cite them by prose name ("the target-4 brief",
                      "the Stage 2 scoping document") rather than by path, so
                      that no tracked file points at a file the repository does
                      not contain. The four frozen copies under
                      benches/genesis/src/ are the documented exception: they
                      still carry literal paths, because that directory is
                      append-only and may not be edited even to fix a
                      reference.
.claude/skills/       the written procedures the pipeline runs, one per directory
logs/
  ledger.jsonl        append-only candidate and campaign rows (currently empty)
  aristotle-sessions.jsonl  append-only record of the remote Aristotle proof sessions
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
    evalsplit.rs      the multilinear evaluation split uᵀ M v
    ringswitch.rs     the balanced quotient digits of the ring switch
    quadeval.rs       the QuadEval fold: carrier, tensors, honest z, the Eq. (20) checks
    zerocheck.rs      the zero-check's H₀ and H_α tables and their two decisions
    endpiece.rs       the end piece: check, prover and witness map
    sumcheck.rs       the paired sumcheck: round messages, per-round checks, the loops, final check
    chain.rs          the composed chain: honest `open` and `verify` over the proved links
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
    NttArith.lean     the transform's modular arithmetic at a runtime prime (Barrett) -- proved
    NttMath.lean      the transform as mathematics: DIF/DIT stages over any ring, no code -- proved
    NttCRT.lean       the three auxiliary primes and the exact Garner reconstruction -- proved
    NttStage.lean     the extracted DIF stage against the word-level stage function -- proved
    NttTransform.lean the extracted DIT stage, twist, pointwise and the two transform loops -- proved
    NttProduct.lean   the per-prime pipeline and negconv_mod_p / negconv_mod_q -- proved
    GoldArith.lean    the Goldilocks lane's arithmetic at p = 2^64 - 2^32 + 1 -- proved
    GoldStage.lean    the Goldilocks DIF stage -- proved
    GoldFusedStage.lean  two DIF stages in one pass (the radix-4 memory pattern) -- proved
    GoldTransform.lean   the Goldilocks twiddles, twist, DIT stage and transform loops -- proved
    GoldDot.lean      the Goldilocks digit-path dot: accumulation, offset, headline -- proved
    RingShort.lean    multiplication by a short element, the word level -- proved
    RingFused.lean    the fused dot product in the transform domain -- proved
    RqBridge.lean     the lift of the ring layer to ArkLib's `Rq Φ` -- proved
    Raw32.lean        the compact u32 raw-message carrier -- proved
    Scheme.lean       linalg / gadget / commit, up to perfect correctness -- proved; the honest
                      path also at arbitrary rows/blocks (`...specG`), the pinned specs its instances
    EvalSplit.lean    the evalsplit module against ArkLib's split evaluation -- proved
    Balanced.lean     the balanced digit layer, up to the honest Hachi commitment -- proved
    QuadEval.lean     the QuadEval fold's gadget, carrier and Eq. (20) decisions -- proved
    QuadEvalProtocol.lean  the QuadEval carriers, honest prover and output relations -- proved
    Ext.lean          the `Ext4` extension-field layer, ported from cpoly -- proved
    RingSwitch.lean   the ring-switch lift, commitment and shortness decisions -- proved
    ZeroCheck.lean    the zero-check's `H₀` and `H_α` sides, plus the mixed evaluation -- proved
    EndPiece.lean     the end piece's check, prover and witness map -- proved
    Rlin.lean         the `R^lin` adapter and the polynomial-level bridge -- proved
    Sumcheck.lean     the paired sumcheck: round polynomials, checks, loops, final check -- proved
    SumcheckShift.lean  the Taylor-shift round polynomial (candidate T3) -- proved
    Chain.lean        the composed chain's honest `open` and `verify` -- proved
    LiftProver.lean   the honest lift prover, and the one unfolded `CPolynomial` carrier -- proved
    Opt.lean          umbrella over the optimization loop's `Foo.opt` variants and `opt_eq_spec` lemmas:
    OptFold.lean        the fold lemmas the parts share -- proved
    OptZeroCheck.lean   zerocheck's variants, and the two ringswitch evaluations of the α side -- proved
    OptSumcheck.lean    sumcheck's variants -- proved
    OptRingSwitch.lean  ringswitch::lift_commit's variant -- proved
    OptEvalSplit.lean   evalsplit's two Rq-valued bases -- proved
    OptRingShort.lean   the short multiply's algebra (MulShort) -- proved
    Check.lean        audit: the specs are not vacuous, and no `sorryAx` hides under one
  lean-wip/           staging for statements not yet proved; NOT a Lake root, NOT audited
                      -- currently EMPTY: every statement is proved and audited
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

The first measurement-grade local calibration ran on 2026-09-07. It confirmed
that the flat 5% floor is adequate outside the 100 ns–2 µs band on this host,
but found false 5–8% verdicts on byte-identical code inside that band. Candidate
timings there are therefore not actionable until the harness gains a per-band
floor or a case-local control. See [`NOTES.md`](NOTES.md) § "The certified
null-slot sweep" and [`INSTRUCTIONS.md`](INSTRUCTIONS.md) for the procedures
that act on this result.

## Dependencies and pins

Lake fetches the Lean dependencies itself and records the exact revision of each
in `lake-manifest.json`, which is what makes a clone reproducible:

* **ArkLib** — `Verified-zkEVM/ArkLib`, pinned to a **commit** rather than `main`.
  The specs are the reference this development is proved against, and a spec that
  moves under a proof turns a passing build into a failing one for reasons that
  have nothing to do with the Rust. Bump with `lake update Arklib`.

* **aeneas** — our Lean 4.33 port of `AeneasVerif/aeneas`: commit `6125cb9e`
  ("bump to 4.33"), one commit on top of upstream `3a8586f` — the commit the
  pinned extraction binaries are built from — fetched by a `file://` require
  from the sibling `../aeneas` checkout, so the Lean build reproduces only on
  this machine (the Lean CI job cannot clone it). Upstream
  releases stop at Lean/Mathlib v4.31.0 while ArkLib `main` is on v4.33.1; the
  port's regenerated builtins table is semantically identical to upstream's, so
  the release binaries stay valid. See the comment on `require aeneas` in
  `hachi/lakefile.lean` and [`NOTES.md`](NOTES.md) § "Upstream aeneas, no fork"
  (superseding entry).

* **cpoly** — `tobias-rothmann/AeneasCompPoly`, a cargo dependency pinned by
  `rev`. Pinned by commit so the frozen bench baseline cannot drift.

The charon and aeneas *binaries* `make extract` runs are a separate artifact,
pinned by `AENEAS_TAG` and `AENEAS_COMMIT` in the `Makefile` and downloaded from
the release. They have to stay on the same Aeneas commit as the backend, since
`lean/Generated.lean` is only valid against the version that produced it —
`make setup` checks both directions and `make extract` re-checks the binaries.

A Lean bump therefore moves `lake-manifest.json`, `lean-toolchain` and the
Makefile pins together, and a further Mathlib bump means rebasing the port,
which rebuilds the extraction binaries and re-baselines the extraction — a
project decision with its own verify-campaign, never maintenance
(the protocol-layer plan, Decision 2).

## Trusted computing base

The trusted computing base (TCB): components trusted because they lie outside our
verification boundary.

| Trusted | Why it cannot be checked away | If it is wrong |
|---|---|---|
| **[Lean kernel](https://github.com/leanprover/lean4/tree/v4.33.1/src/kernel)** — ~8k lines of C++, plus `propext`, `Classical.choice`, `Quot.sound` | No machine-checked proof of it exists; its C fast path for `Nat` carries every `decide` in the parameter checks | A false theorem, with no diagnostic |
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
