import Lake
open Lake DSL

-- This Lake package sits in the *same* directory as the Rust crate it is about:
-- `src/` is the crate, `lean/` is the proof development, and `../toolchain`
-- turns the former into `lean/Generated.lean` (see `make extract`).
-- Keeping them together is what lets Aeneas write its output straight into the
-- library, with no copy of the generated model to keep in sync.

-- The local 4.33 port of the Aeneas Lean backend, pinned by commit -- a git
-- require against the sibling checkout, not (yet) a published fork.
--
-- ArkLib main moved to Mathlib v4.33.1 and upstream aeneas releases stop at
-- v4.31.0. The port that bridges the gap is commit 6125cb9e ("bump to 4.33"),
-- one commit on top of upstream 3a8586f -- which is exactly the commit the
-- extraction binaries (`../toolchain/{charon,aeneas}`, `AENEAS_TAG` in the
-- Makefile) are built from. The port's regenerated builtins table was checked
-- semantically identical to upstream's, so those binaries stay valid and
-- `Generated.lean` remains the output of the same Aeneas that this library
-- models it against. `make setup`'s backend check accepts descendants of
-- `AENEAS_COMMIT`, so it reads this pin as "3a8586f + 1 commit(s)".
--
-- The manifest records the resolved commit, which is what makes the build
-- reproducible -- on this machine: a `file://` URL does not travel. When the
-- port lands on a public fork or upstream, move only the URL, keeping the
-- rev pin, with `lake update aeneas`.
require aeneas from git
  "file:///home/pablo/Documents/internship-eth/aeneas" @ "6125cb9e191aa500cac5b3de4df643002818b03a"
    / "backends" / "lean"

-- The specification side. Pinned to a commit rather than to `main`, because the
-- specs are the reference this development is proved against: a spec that moves
-- under a proof turns a passing build into a failing one for reasons that have
-- nothing to do with the Rust. Bump it deliberately with
-- `lake update Arklib`, and re-check the Mathlib invariant above -- aeneas and
-- `lean-toolchain` have to move with ArkLib's Mathlib pin.
--
-- `Arklib`, not `ArkLib`: that is the package name in the dependency's own
-- lakefile, and Lake matches on it. The *library* inside it is `ArkLib`, which is
-- what the `import ArkLib.…` lines in `lean/` name.
require Arklib from git
  "https://github.com/Verified-zkEVM/ArkLib.git" @ "d51d8bc3c22062bf21385bd15b39d390b0fe4584"

package «HachiEquiv» where

-- `lean/`, not the package root: the package root is the Rust crate, so `src/`
-- is Rust and `lean/` holds the modules of this library -- flat, with no
-- directory level of its own: `lean/Check.lean` is the module `Check`.
--
-- Which is why `roots` has to name every module. There is no module called
-- after the library to reach the rest through, and Lake counts a module as part
-- of a library only when one of the roots is a *prefix* of its name -- under the
-- default `roots := #[`HachiEquiv]` not one of these files would resolve. The
-- default `globs` is one glob per root, so listing them is also what makes
-- `lake build` check all of them, `Check.lean` included: nothing imports that
-- one, it is only ever built as a root of its own.
--
-- Adding a module under `lean/` therefore means adding it here too. Listed in
-- dependency order, which is also the order to read them in.
@[default_target]
lean_lib «HachiEquiv» where
  srcDir := "lean"
  roots := #[`Generated, `Field, `Ext, `NttArith, `GoldArith, `NttMath, `NttCRT, `NttStage, `NttTransform, `GoldStage, `GoldFusedStage, `GoldTransform, `NttProduct, `SumcheckShift, `Ring, `RingShort, `RingFused, `GoldDot, `RqBridge, `Scheme, `Raw32, `EvalSplit, `Balanced,
             `QuadEval, `QuadEvalProtocol, `RingSwitch, `ZeroCheck, `EndPiece, `Rlin, `Sumcheck,
             `Chain, `LiftProver, `OptFold, `OptZeroCheck, `OptSumcheck, `OptRingSwitch, `OptEvalSplit, `OptRingShort, `Opt, `Check]
