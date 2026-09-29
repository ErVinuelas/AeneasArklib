# hachi-jazz — the Jasmin integration experiment

The first-Jasmin-optimization milestone (2026-09-29), run to completion. This
crate is the deliverable: a working, tested, benchmarked Rust ↔ Jasmin
integration pattern, and the measured reason it is **not** wired into `hachi`.

## Verdict: REJECT for production, KEEP as the integration pattern

* The plan's primary target, `fill_digit_from_words`, died before the plan ran:
  card **T65b** fused the digit extraction into `gold_dif_stage2_twist_tab`,
  and `hachi/src/ring.rs` says it outright — *"nothing on the hot path calls
  it any more."* On top of that, LLVM already vectorizes its loop (SSE2
  `movdqu`/`psrlq`/`pand`, 4 words per iteration), so even on the old hot path
  there was no headroom of the kind the plan assumed.
* Per the plan's Phase 0 pivot rule, the milestone fell back to the
  integration target: a Jasmin `MULX` kernel for
  `mul_hi_u64(x, y) = ⌊x·y / 2^64⌋`, the quantity `hachi::ntt::aux_reduce`
  forms as its Barrett quotient.
* The kernel is correct (differential tests below) and the pipeline works
  end to end, but the microbenchmark gate rejects it for production: a
  one-instruction kernel cannot pay for its `call`.

## Benchmark record (gate result)

AMD Ryzen 7 8845HS, rustc 1.98.1, `[profile.bench]` pinned as in
`hachi/Cargo.toml` (opt-level 3, fat LTO, codegen-units 1), quiet machine,
criterion 0.7, 4096 operations per iteration:

| case                        | scalar Rust | Jasmin FFI | ratio |
|-----------------------------|-------------|------------|-------|
| `mul_hi` (per op)           | 0.53 ns     | 1.28 ns    | 2.4×  |
| `aux_reduce` shape (per op) | 0.84 ns     | 1.48 ns    | 1.8×  |

LLVM already compiles the `u128` idiom to one inlined `mulq` (and `gold_mul`
to `mulq` plus a branch-free cmov reduction — see the disassembly note below),
so the FFI variant is the *same multiply* behind a non-inlinable call:
~0.75 ns/op of pure boundary cost. No end-to-end run was warranted — nothing
was wired into the hot path, and Phase 0 had already ruled the primary target
out.

This is a sibling-crate microbenchmark, deliberately outside hachi's ledger
harness; it carries no accept/reject row in `logs/ledger.jsonl`.

**Consequence for future Jasmin work here:** the boundary tax sets the bar. A
Jasmin kernel only becomes interesting when it does enough work per call to
amortize ~0.75 ns and to beat what fat-LTO'd LLVM emits *with* inlining — i.e.
a whole 1024-coefficient stage (the Goldilocks AVX2 `gold_dif_stage2` family),
not a scalar primitive. That was Milestone B of the original discussion, and
it now has a working integration substrate plus a measured cost floor.

## What this crate is

```
hachi  (untouched: #![forbid(unsafe_code)], the extracted, proved crate)
  ▲
  │  dev-dependency, tests/bench only — hachi does NOT depend on hachi-jazz
  │
hachi-jazz
  ├── jazz/mul_hi_u64.jazz   Jasmin source (the checked-in truth)
  ├── jazz/mul_hi_u64.s      its compiled output, checked in, reproducible
  ├── build.rs               assembles the .s (cc); never invokes Jasmin
  ├── src/lib.rs             the ONE unsafe extern block + safe wrapper
  ├── tests/differential.rs  kernel vs. scalar reference, elementwise
  └── benches/mul_hi.rs      the gate microbenchmark
```

## Toolchain pin

Jasmin **2026.03.2** from nixpkgs rev
`f45c6f04c2f013f004bf94e284e95d72898d9393`
(store path `/nix/store/9v6p3bfnjvc3dkazahg1asf35hr7a4an-jasmin-compiler-2026.03.2-bin`).

Regenerate the assembly with:

```sh
nix build nixpkgs/f45c6f04c2f013f004bf94e284e95d72898d9393#jasmin-compiler
cd jazz && jasminc -arch x86-64 -o mul_hi_u64.s mul_hi_u64.jazz
```

Building the crate itself needs only cargo and a C toolchain (the `.s` is
checked in). Requires x86-64; the wrapper checks BMI2 at runtime.

## Trust-boundary note

What holds, and on whose authority:

1. **Jasmin source → assembly** — inherited from the Jasmin project (the
   intrinsic's instruction semantics and the verified compiler). Nothing
   re-proved here; nothing EasyCrypt-shaped was installed or written, per the
   plan's gate — the candidate failed the performance gate, so Phase 7's
   proof-bridge question never opened.
2. **FFI contract** (symbol, SysV AMD64 ABI, register-only, no memory access,
   BMI2) — stated once in `src/lib.rs`, enforced by the safe wrapper, checked
   by `tests/differential.rs` (edge cross-products, ~56k boundary pairs, 10⁶
   random pairs, and `aux_reduce` rebuilt on the kernel agreeing with
   `hachi::ntt::aux_reduce` over its three real `(p, m)` pairs — all passing).
3. **The Lean development** — completely unaffected. `hachi` source is
   byte-identical, so `lean/Generated.lean`, every spec, and the axiom audit
   are exactly what they were. No axiom, no `sorry`, no statement moved. The
   scalar Rust model remains the only thing Aeneas reasons about.

## Phase-by-phase disposition of the plan

* **Phase 0 (baseline)** — done; both pivot conditions fired (target off the
  hot path since T65b; LLVM already vectorizes it). Baseline of record: the
  pin profile at `0a9c1f5`, prover 183.2 s. Disassembly checked from
  `cargo rustc --release -- --emit asm`: `gold_mul` is `mulq` + cmov chain,
  `fill_digit_from_words` is an SSE2 shift/mask loop.
* **Phase 1 (smallest primitive)** — `mul_hi_u64`, registers only, no
  pointers, no `Fp`/`Rq` in the kernel.
* **Phase 2 (kernel)** — two instructions, pinned toolchain, output checked in.
* **Phase 3 (boundary)** — this crate; `hachi` untouched.
* **Phase 4 (differential tests)** — 5/5 passing in release.
* **Phase 5 (benchmark gate)** — numbers above; **REJECT**.
* **Phase 6 (invariants)** — trivially preserved (hachi byte-identical);
  hachi's own build and tests unaffected.
* **Phase 7 (proof bridge)** — not entered, by the plan's own rule: it is
  conditional on a performance win.
