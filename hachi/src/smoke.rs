//! **Temporary.** The extraction probe for Workstream 0.
//!
//! This module implements no part of the scheme. It exists to answer one
//! question before any real code is written: *can charon follow the `cpoly`
//! dependency across the crate boundary, and does Aeneas give us a transparent
//! Lean model of what it finds there?*
//!
//! That question has a cheap wrong answer. Charon marks items from other crates
//! opaque unless told otherwise, and an opaque `Fp::add` would leave the Lean
//! side with an uninterpreted constant where the field addition should be --
//! provably nothing. If that is what happens, `field.rs` gets vendored into this
//! crate verbatim instead and this probe is what recorded why (NOTES.md
//! § "The cpoly dependency").
//!
//! [`sum`] is written to touch exactly the four things every real module will
//! need from the boundary: a foreign newtype ([`Fp`]), a foreign associated
//! constant (`Fp::ZERO`), a foreign operator impl (`impl Add for Fp`), and a
//! `Vec` walked by an index-counter loop. [`ext_sum_of_products`] then repeats
//! the exercise for [`Ext4`], which is the case a one-field newtype does not
//! cover: a foreign struct with *four* private fields, whose `mul` is a
//! sixteen-term unrolled convolution rather than a one-liner.
//!
//! Delete this module, and its bench and test, when the first real module lands.

use alloc::vec::Vec;
use cpoly::{Ext4, Fp};

/// Sum a vector of base-field elements.
///
/// Nothing in the scheme calls this; see the module header for what it is for.
pub fn sum(v: &Vec<Fp>) -> Fp {
    let mut acc = Fp::ZERO;
    let mut i = 0;
    while i < v.len() {
        acc = acc + v[i];
        i += 1;
    }
    acc
}

/// Sum the pairwise products of two vectors of extension-field elements.
///
/// Nothing in the scheme calls this either; see the module header. It exists
/// because [`Ext4`] is a multi-field foreign struct and [`Fp`] is not, and only
/// the former shows whether charon reconstructs a foreign *structure* rather
/// than an alias.
pub fn ext_sum_of_products(a: &Vec<Ext4>, b: &Vec<Ext4>) -> Ext4 {
    let mut acc = Ext4::ZERO;
    let mut i = 0;
    while i < a.len() && i < b.len() {
        acc = acc + a[i] * b[i];
        i += 1;
    }
    acc
}
