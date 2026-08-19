//! Vectors and matrices over `R_q`.
//!
//! Reference specification: `ArkLib/Data/Lattices/Vectors.lean`.
//!
//! # Only what the two consumers use
//!
//! `Vectors.lean` is larger than this module. It also carries `matMul`,
//! `splitForm` and the transpose/composition lemmas around them, which exist for
//! the evaluation argument -- moving a gadget factor between the witness and the
//! basis side of `uᵀ M v` (Hachi [NOZ26] eq. 12 → 15). That is the protocol
//! layer, which is out of scope here, and every one of those operations would be
//! dead code with an equivalence proof attached. What is below is exactly the
//! surface `Gadget/Core.lean` and `InnerOuter/Scheme.lean` reach for:
//!
//! | spec | here |
//! |---|---|
//! | `dot` (`Vectors.lean:77`) | [`PolyVec::dot`] |
//! | `matVecMul` (`:81`) | [`PolyMatrix::mat_vec_mul`] |
//! | `scalarVecMul` (`:91`) | [`PolyVec::scalar_mul`] |
//! | `PolyVec.flattenBlocks` (`:49`) | [`flatten_blocks`] |
//! | `Pi` add / sub | [`PolyVec::add`] / [`PolyVec::sub`] |
//!
//! # Containers, and why the spec's are function types
//!
//! ArkLib represents a length-`k` vector as `Fin k → P` and a matrix as
//! Mathlib's `Matrix`, and computes `dot` through `List.sum ∘ List.ofFn` rather
//! than `Matrix.mulVec`. Both choices are about computability: `Rq`'s `CommRing`
//! instance routes through a noncomputable transport, so anything defined over it
//! would not `#eval` (`Vectors.lean:20-23`). Here the containers are `Vec`s, and
//! the index arithmetic that a `Fin`-indexed function makes implicit is written
//! out -- which is where the flattening convention below becomes something to get
//! right rather than something to read off.
//!
//! # The flattening convention
//!
//! Both the gadget layout and `flattenBlocks` go through ArkLib's
//! `finProdFinEquiv`, and its value on a pair is
//! `finProdFinEquiv (i, e) = e + width · i` (`Gadget/Core.lean:166`). So the
//! flat index runs *fastest in the second component*: block `i` occupies the
//! contiguous slice `[width·i, width·i + width)`. Every index computation here
//! and in [`crate::gadget`] follows that, and it is why flattening is plain
//! concatenation.

use alloc::vec::Vec;

use crate::ring::Rq;

/// A vector over `R_q` (spec: `PolyVec (Rq Φ) k`, `Vectors.lean:39`).
pub struct PolyVec(Vec<Rq>);

/// A matrix over `R_q`, as its rows (spec: `PolyMatrix (Rq Φ) rows cols`,
/// `Vectors.lean:42`).
///
/// Every row is expected to have the same length; that is the matrix's column
/// count, and like the ring's degree invariant it is a property of construction
/// rather than a checked precondition (see [`crate::ring`]).
pub struct PolyMatrix(Vec<PolyVec>);

impl PolyVec {
    /// Wrap a vector of ring elements.
    pub fn new(entries: Vec<Rq>) -> PolyVec {
        PolyVec(entries)
    }

    /// The all-zero vector of the given length.
    pub fn zeros(k: usize) -> PolyVec {
        let mut out: Vec<Rq> = Vec::new();
        let mut i: usize = 0;
        while i < k {
            out.push(Rq::zero());
            i += 1;
        }
        PolyVec(out)
    }

    /// The number of entries.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// The `i`-th entry.
    pub fn get(&self, i: usize) -> &Rq {
        &self.0[i]
    }

    /// An independent copy (hand-rolled; see [`Rq::copy`]).
    pub fn copy(&self) -> PolyVec {
        let n: usize = self.0.len();
        let mut out: Vec<Rq> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            out.push(self.0[i].copy());
            i += 1;
        }
        PolyVec(out)
    }

    /// Entrywise equality.
    ///
    /// This is what `Simple.verify` decides (`Ajtai/Simple/Scheme.lean:46`,
    /// `decide (commit Φ A s = c)`): equality of two commitment vectors.
    pub fn equals(&self, rhs: &PolyVec) -> bool {
        let n: usize = self.0.len();
        if n != rhs.0.len() {
            false
        } else {
            let mut i: usize = 0;
            let mut same: bool = true;
            while i < n {
                if !self.0[i].equals(&rhs.0[i]) {
                    same = false;
                }
                i += 1;
            }
            same
        }
    }

    /// Entrywise addition (spec: the `Pi` instance, used through
    /// `matVecMul_add` and the norm-difference lemmas).
    pub fn add(&self, rhs: &PolyVec) -> PolyVec {
        let n: usize = self.0.len();
        let mut out: Vec<Rq> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            out.push(self.0[i].add(&rhs.0[i]));
            i += 1;
        }
        PolyVec(out)
    }

    /// Entrywise subtraction (spec: the `Pi` instance; this is the vector whose
    /// norm `sub_l2NormSq_le` bounds).
    pub fn sub(&self, rhs: &PolyVec) -> PolyVec {
        let n: usize = self.0.len();
        let mut out: Vec<Rq> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            out.push(self.0[i].sub(&rhs.0[i]));
            i += 1;
        }
        PolyVec(out)
    }

    /// Left scalar multiplication by a ring element (spec: `scalarVecMul`,
    /// `Vectors.lean:91`).
    ///
    /// This is the `cᵢ •ᵥ sᵢ` of the weak verifier's shortness check.
    pub fn scalar_mul(&self, c: &Rq) -> PolyVec {
        let n: usize = self.0.len();
        let mut out: Vec<Rq> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            out.push(c.mul(&self.0[i]));
            i += 1;
        }
        PolyVec(out)
    }

    /// The dot product `Σᵢ uᵢ · vᵢ` (spec: `dot`, `Vectors.lean:77`).
    ///
    /// The spec sums a `List` (so, right-nested: `x₀ + (x₁ + (… + 0))`) while
    /// this accumulates left. `R_q` is commutative and associative, so the two
    /// agree -- but the equivalence proof has to say so rather than match
    /// syntactically.
    ///
    /// Over the shorter of the two lengths, which makes the operation total; the
    /// spec's version is only defined at equal lengths, so the equivalence
    /// statement carries that as a hypothesis.
    pub fn dot(&self, rhs: &PolyVec) -> Rq {
        let n: usize = if self.0.len() <= rhs.0.len() {
            self.0.len()
        } else {
            rhs.0.len()
        };
        let mut acc: Rq = Rq::zero();
        let mut i: usize = 0;
        while i < n {
            let term: Rq = self.0[i].mul(&rhs.0[i]);
            acc = acc.add(&term);
            i += 1;
        }
        acc
    }
}

impl PolyMatrix {
    /// Wrap a list of rows.
    pub fn new(rows: Vec<PolyVec>) -> PolyMatrix {
        PolyMatrix(rows)
    }

    /// The number of rows.
    pub fn rows(&self) -> usize {
        self.0.len()
    }

    /// The number of columns: the length of row `0`, and `0` for a matrix with
    /// no rows.
    pub fn cols(&self) -> usize {
        if self.0.len() == 0 {
            0
        } else {
            self.0[0].len()
        }
    }

    /// The `i`-th row.
    pub fn row(&self, i: usize) -> &PolyVec {
        &self.0[i]
    }

    /// The matrix-vector product `A *ᵥ v` (spec: `matVecMul`,
    /// `Vectors.lean:81`), each entry the dot product of a row with `v`.
    ///
    /// This is the Ajtai commitment itself: `Simple.commit Φ A s = A *ᵥ s`
    /// (`Ajtai/Simple/Scheme.lean:38`).
    pub fn mat_vec_mul(&self, v: &PolyVec) -> PolyVec {
        let n: usize = self.0.len();
        let mut out: Vec<Rq> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            out.push(self.0[i].dot(v));
            i += 1;
        }
        PolyVec(out)
    }
}

/// Flatten equal-width blocks into one vector, in block order (spec:
/// `PolyVec.flattenBlocks`, `Vectors.lean:49`).
///
/// Entry `width·i + w` of the result is entry `w` of block `i`, which is what
/// `flattenBlocks xs (finProdFinEquiv (i, w)) = xs i w` says once
/// `finProdFinEquiv`'s value is unfolded (see the module header). So this is
/// concatenation, and the width never has to be passed in -- it is each block's
/// own length, and the blocks are expected to agree on it.
pub fn flatten_blocks(blocks: &Vec<PolyVec>) -> PolyVec {
    let nblocks: usize = blocks.len();
    let mut out: Vec<Rq> = Vec::new();
    let mut i: usize = 0;
    while i < nblocks {
        let width: usize = blocks[i].len();
        let mut w: usize = 0;
        while w < width {
            out.push(blocks[i].get(w).copy());
            w += 1;
        }
        i += 1;
    }
    PolyVec(out)
}
