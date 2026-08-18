//! **Frozen, and currently empty.** The first translation of every `hachi`
//! operation, kept so that the optimization loop always has a starting point it
//! can *re-measure* rather than merely remember.
//!
//! Nothing is frozen here yet. Workstream 0 built the scaffold; the only code in
//! `hachi/src/` besides the parameters is `smoke.rs`, a throwaway extraction
//! probe, and freezing a throwaway into an append-only baseline is precisely the
//! mistake this file's contract exists to prevent. The first entry arrives with
//! the first real module.
//!
//! # Why a whole crate exists for this
//!
//! The fitness function of this project is criterion wall-clock time. A number
//! recorded three weeks ago on a laptop that may since have been rebooted,
//! updated, or thermally throttled is not comparable to a number recorded today,
//! and comparing them anyway is how an autonomous loop convinces itself of a
//! speedup it never achieved. So `make run-bench` does not compare against a
//! remembered number: it measures this crate and `hachi` **back to back in the
//! same criterion session**, on the same machine, at the same temperature, with
//! the same compiler. The genesis time is re-derived every run.
//!
//! # Why a separate crate rather than a module inside `benches/`
//!
//! Symmetry of compilation. If the baseline lived in the bench binary's own
//! crate it would be inlinable at will, while `hachi` — a real external crate —
//! would be inlinable only through LTO. The baseline would look artificially fast
//! and every genuine improvement would be understated or inverted. As a sibling
//! crate, `hachi_genesis` and `hachi` reach the bench binary through the
//! identical path: same profile, same LTO decision, same codegen units.
//!
//! # The contract
//!
//! 1. **Nothing here is ever edited.** Not to fix a lint, not to fix a typo, not
//!    to follow a rename in `hachi`. Editing genesis silently rewrites history
//!    for every past measurement.
//! 2. **Append only.** When an ArkLib definition is translated to Rust *for the
//!    first time*, that first translation is copied here verbatim, in the same
//!    commit that adds it to `hachi/src/`.
//! 3. **Every item carries `// @genesis <sha> <date> — <path>`**, naming the
//!    earliest commit whose `hachi/src/<file>` contains that item's body
//!    verbatim.
//! 4. **Genesis composes with genesis.** A function frozen today calls the
//!    *frozen* arithmetic below it, not today's. So "vs genesis" is the cumulative
//!    improvement over the first translation of the whole call chain.
//!
//! # The open question this crate has with the field layer
//!
//! Point 4 and the "no dependencies, ever" rule in `Cargo.toml` pull against the
//! way `hachi` currently reaches its coefficient field. `hachi` depends on the
//! `cpoly` crate for `Fp`/`Ext4`, so a frozen copy of a `hachi` module that uses
//! the field cannot compile here without that same dependency — and taking it
//! would mean the baseline drifts whenever `cpoly` does, which is exactly what
//! point 1 forbids. Vendoring the field into `hachi/src/` resolves it; depending
//! on `cpoly` as a crate does not. See NOTES.md § "The cpoly dependency".

#![no_std]
#![forbid(unsafe_code)]
// Frozen code answers to the standards of the day it was frozen, not today's.
// A lint that fires here can never be fixed (see contract point 1), so it must
// never be able to fail a build either.
#![allow(warnings, clippy::all, clippy::pedantic)]

extern crate alloc;
