//! The Hachi lattice-based multilinear polynomial commitment scheme ([NOZ26]),
//! written to be translated to Lean by charon/Aeneas and proved equivalent to
//! the reference development in
//! [ArkLib](https://github.com/Verified-zkEVM/ArkLib).
//!
//! # Status
//!
//! Workstream 0: the scaffold. What is here is [`params`] -- every parameter of
//! the scheme as a `const` -- and [`smoke`], a temporary probe that exists only
//! to answer whether charon can follow the `cpoly` dependency across the crate
//! boundary. No part of the scheme itself is implemented yet. [`smoke`] goes
//! away when the first real module lands.
//!
//! # Layout
//!
//! One module per layer, and the Lean side mirrors it: a Rust path
//! `hachi::<module>::<item>` becomes the extracted Lean name
//! `hachi.<module>.<item>` (see `lean/Generated.lean`).
//!
//! * [`params`] -- the parameters, and where each one comes from.
//!
//! The coefficient field is *not* in this crate. `Fp` (the Hachi prime
//! `2^32 - 99`) and its quartic extension `Ext4` come from the `cpoly` crate of
//! [AeneasCompPoly](https://github.com/tobias-rothmann/AeneasCompPoly), which
//! already carries their Lean equivalence proofs against CompPoly. Reusing them
//! rather than reimplementing is a hard rule of this project; see NOTES.md
//! § "The cpoly dependency" for how that reuse is wired and what it cost.
//!
//! # Concrete, not generic
//!
//! There are no type parameters over the ring or the field anywhere in this
//! crate, and no parameter is threaded through a signature: everything is a
//! `const` in [`params`]. The ArkLib specification is generic in all four of
//! `(q, α, b, digits)`, so each equivalence proof instantiates a generic
//! statement at the constants above.
//!
//! # Style notes (for clean Aeneas output)
//!
//! Habits here that are for the extraction's benefit rather than the reader's,
//! and are load-bearing:
//!
//! * **Explicit index-based `while` loops, and no iterator adaptors.** `.map`,
//!   `.zip`, `.fold` and `.collect` have no model in the Aeneas Lean backend --
//!   using them puts unknown definitions in the extracted file. `for i in 0..n`
//!   *is* modelled, but it turns every loop's state from a `usize` counter into a
//!   `Range<usize>` iterator, and that state is what each loop invariant on the
//!   Lean side is written about, so the counter loops stay.
//! * **Bit tests written with `/` and `%`** rather than `>>` and `&`, so the
//!   extracted model stays in plain `Usize` arithmetic that `scalar_tac` and
//!   `omega` can see through.
//! * **No `Vec::is_empty`, `Vec::truncate` or `#[derive(Default)]` on a
//!   `Vec`-holding struct**: none of the three has a model, and each would put an
//!   `axiom` in `lean/Generated.lean`.
//!
//! # References
//!
//! * [NOZ26] Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient
//!   Lattice-Based Multilinear Polynomial Commitments over Extension Fields*.
//! * [NS24] Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial
//!   Commitments from Lattices*.

#![no_std]
#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![warn(missing_debug_implementations)]

extern crate alloc;

pub mod params;

pub mod smoke;
