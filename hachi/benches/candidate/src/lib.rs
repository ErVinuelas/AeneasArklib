//! The optimization loop's **candidate slot**, currently empty.
//!
//! At rest this crate is a byte-copy of `hachi/src/` — a null candidate, so a
//! default `make run-bench` measures exactly what it measured before the slot
//! existed. Inside the optimization loop's worktree it is overwritten with the
//! candidate under test, which is what lets a candidate and the current champion
//! be measured *in the same criterion session* rather than across two runs.
//!
//! It is empty now because `hachi/src/` holds no operation worth optimizing yet:
//! the parameters are `const`s and `smoke.rs` is a throwaway extraction probe.
//! The slot fills when the first real module lands.
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
