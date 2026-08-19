//! The optimization loop's **candidate slot**.
//!
//! At rest this crate is a byte-copy of `hachi/src/` — a null candidate, so a
//! default `make run-bench` measures exactly what it measured before the slot
//! existed. Inside the optimization loop's worktree it is overwritten with the
//! candidate under test, which is what lets a candidate and the current champion
//! be measured *in the same criterion session* rather than across two runs.
//!
//! It holds the four bottom-layer modules, byte-identical to `hachi/src/`.
//!
//! The `cpoly` dependency is taken here for the same reason it is taken in
//! `benches/genesis/` (see that crate's `src/lib.rs`): the frozen and copied
//! modules use `Fp`, and `hachi`'s pin is what keeps the slot comparable.
//!
//! Unlike `benches/genesis/`, nothing here is append-only or historically
//! meaningful — it is scratch space, and every run overwrites it. The one rule
//! it does share is in `Cargo.toml`: no dependencies, ever, so that the slot
//! reaches the bench binary through the identical compilation path as `hachi`
//! and `hachi_genesis`.

#![no_std]
#![forbid(unsafe_code)]
#![allow(warnings, clippy::all, clippy::pedantic)]

extern crate alloc;

pub mod params;

pub mod ring;

pub mod linalg;

pub mod gadget;

pub mod commit;
