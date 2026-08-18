import Lake
open Lake DSL

-- This Lake package sits in the *same* directory as the Rust crate it is about:
-- `src/` is the crate, `lean/` is the proof development, and `../toolchain`
-- turns the former into `lean/Generated.lean` (see `make extract`).
-- Keeping them together is what lets Aeneas write its output straight into the
-- library, with no copy of the generated model to keep in sync.

-- Upstream aeneas, and no fork -- which is worth saying because the sister
-- project AeneasCompPoly does need one.
--
-- The Lean backend of this nightly hard-`require`s Mathlib v4.31.0, and v4.31.0
-- is exactly what ArkLib pins (`lean-toolchain` here matches both). AeneasCompPoly
-- had to fork aeneas only because CompPoly had moved on to v4.32.0, for which
-- upstream aeneas has no release. Nothing in this repository needs that bump, so
-- the dependency below is the plain upstream tag.
--
-- Read the tag as the truth and `lake-manifest.json` as its resolution: the
-- manifest records the resolved commit, which is what makes a clone reproducible.
-- Move it deliberately with `lake update aeneas`.
--
-- Either way the extraction binaries (`../toolchain/{charon,aeneas}`, pinned by
-- `AENEAS_TAG` in the Makefile) must stay on the same Aeneas commit as this
-- library: `Generated.lean` is only valid against the Aeneas version that
-- produced it. `make setup` and `make extract` check that they do.
require aeneas from git
  "https://github.com/AeneasVerif/aeneas.git" @ "nightly-2026.07.26-3a8586f"
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
  "https://github.com/Verified-zkEVM/ArkLib.git" @ "e92dc315f453db88dd7351c88e889caf0e6bf269"

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
  roots := #[`Generated, `Check]
