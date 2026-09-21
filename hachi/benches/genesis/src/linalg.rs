//! Vectors and matrices over `R_q`.
//!
//! Reference specification: `ArkLib/Data/Lattices/Vectors.lean`.
//!
//! # Only what the consumers use
//!
//! `Vectors.lean` is larger than this module. It also carries `matMul` and the
//! transpose/composition lemmas, which exist for moving a gadget factor between
//! the witness and the basis side of `uᵀ M v` (Hachi [NOZ26] eq. 12 → 15).
//! Those are still out of scope: every one would be dead code with an
//! equivalence proof attached. `splitForm` itself *was* in that list until the
//! evaluation split ([`crate::evalsplit`]) arrived as a consumer; it is below
//! now. What is here is exactly the surface `Gadget/Core.lean`,
//! `InnerOuter/Scheme.lean` and `Hachi/EvalSplit.lean` reach for:
//!
//! | spec | here |
//! |---|---|
//! | `dot` (`Vectors.lean:77`) | [`PolyVec::dot`] |
//! | `matVecMul` (`:81`) | [`PolyMatrix::mat_vec_mul`] |
//! | `scalarVecMul` (`:91`) | [`PolyVec::scalar_mul`] |
//! | `splitForm` (`:178`) | [`PolyMatrix::split_form`] |
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

// @genesis d664190 2026-08-19 — linalg::PolyVec
/// A vector over `R_q` (spec: `PolyVec (Rq Φ) k`, `Vectors.lean:39`).
///
/// Mirrors ArkLib's `PolyVec (Rq Φ) k`; the spec carries the length `k` in the
/// type and this carries it in the `Vec`, which is the container difference the
/// module header describes.
pub struct PolyVec(Vec<Rq>);

// @genesis d664190 2026-08-19 — linalg::PolyMatrix
/// A matrix over `R_q`, as its rows (spec: `PolyMatrix (Rq Φ) rows cols`,
/// `Vectors.lean:42`).
///
/// Mirrors ArkLib's `PolyMatrix (Rq Φ) rows cols`, which is Mathlib's `Matrix`
/// over `Fin rows` and `Fin cols`; here it is the list of rows.
///
/// Every row is expected to have the same length; that is the matrix's column
/// count, and like the ring's degree invariant it is a property of construction
/// rather than a checked precondition (see [`crate::ring`]).
pub struct PolyMatrix(Vec<PolyVec>);

impl PolyVec {
    // @genesis d664190 2026-08-19 — linalg::PolyVec::new
    /// Wrap a vector of ring elements.
    pub fn new(entries: Vec<Rq>) -> PolyVec {
        PolyVec(entries)
    }

    // @genesis d664190 2026-08-19 — linalg::PolyVec::zeros
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

    // @genesis d664190 2026-08-19 — linalg::PolyVec::len
    /// The number of entries.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    // @genesis d664190 2026-08-19 — linalg::PolyVec::get
    /// The `i`-th entry.
    pub fn get(&self, i: usize) -> &Rq {
        &self.0[i]
    }

    // @genesis d664190 2026-08-19 — linalg::PolyVec::copy
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

    // @genesis d664190 2026-08-19 — linalg::PolyVec::equals
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

    // @genesis d664190 2026-08-19 — linalg::PolyVec::add
    /// Entrywise addition (spec: the `Pi` instance, used through
    /// `matVecMul_add` and the norm-difference lemmas).
    ///
    /// Mirrors ArkLib's `Pi` addition on `PolyVec (Rq Φ) k` -- the canonical
    /// instance set `Vectors.lean` adopts rather than defining its own.
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

    // @genesis d664190 2026-08-19 — linalg::PolyVec::sub
    /// Entrywise subtraction (spec: the `Pi` instance; this is the vector whose
    /// norm `sub_l2NormSq_le` bounds).
    ///
    /// Mirrors ArkLib's `Pi` subtraction on `PolyVec (Rq Φ) k`.
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

    // @genesis d664190 2026-08-19 — linalg::PolyVec::scalar_mul
    /// Left scalar multiplication by a ring element (spec: `scalarVecMul`,
    /// `Vectors.lean:91`).
    ///
    /// Mirrors ArkLib's `scalarVecMul`.
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

    // @genesis d664190 2026-08-19 — linalg::PolyVec::dot
    /// The dot product `Σᵢ uᵢ · vᵢ` (spec: `dot`, `Vectors.lean:77`).
    ///
    /// Mirrors ArkLib's `dot`.
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
    // @genesis d664190 2026-08-19 — linalg::PolyMatrix::new
    /// Wrap a list of rows.
    pub fn new(rows: Vec<PolyVec>) -> PolyMatrix {
        PolyMatrix(rows)
    }

    // @genesis d664190 2026-08-19 — linalg::PolyMatrix::rows
    /// The number of rows.
    pub fn rows(&self) -> usize {
        self.0.len()
    }

    // @genesis d664190 2026-08-19 — linalg::PolyMatrix::cols
    /// The number of columns: the length of row `0`, and `0` for a matrix with
    /// no rows.
    pub fn cols(&self) -> usize {
        if self.0.len() == 0 {
            0
        } else {
            self.0[0].len()
        }
    }

    // @genesis d664190 2026-08-19 — linalg::PolyMatrix::row
    /// The `i`-th row.
    pub fn row(&self, i: usize) -> &PolyVec {
        &self.0[i]
    }

    // @genesis d664190 2026-08-19 — linalg::PolyMatrix::mat_vec_mul
    /// The matrix-vector product `A *ᵥ v` (spec: `matVecMul`,
    /// `Vectors.lean:81`), each entry the dot product of a row with `v`.
    ///
    /// Mirrors ArkLib's `matVecMul`.
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

    // @genesis afa0140 2026-08-26 — linalg::PolyMatrix::split_form
    /// The split bilinear form `⟨u, M *ᵥ v⟩ = uᵀ M v` (spec: `splitForm`,
    /// `Vectors.lean:178`).
    ///
    /// Mirrors ArkLib's `splitForm`.
    ///
    /// This is the shape of the Hachi evaluation equation: the multilinear
    /// evaluation split states `eval p (xl ++ xh)` as `splitForm` of the
    /// reshaped coefficient matrix against the two monomial bases
    /// (`Hachi/EvalSplit.lean:173`, consumed by [`crate::evalsplit`]).
    pub fn split_form(&self, u: &PolyVec, v: &PolyVec) -> Rq {
        let mv: PolyVec = self.mat_vec_mul(v);
        u.dot(&mv)
    }
}

// @genesis d664190 2026-08-19 — linalg::flatten_blocks
/// Flatten equal-width blocks into one vector, in block order (spec:
/// `PolyVec.flattenBlocks`, `Vectors.lean:49`).
///
/// Mirrors ArkLib's `PolyVec.flattenBlocks`.
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

// ---------------------------------------------------------------------------
// A prepared matrix
// ---------------------------------------------------------------------------

// @genesis 47976f7 2026-09-17 — linalg::PreparedMatrix
/// A matrix with every entry forward-transformed and kept, one
/// [`crate::ring::PreparedVec`] per row.
///
/// **Whether this is worth building is the caller's decision, not
/// `mat_vec_mul`'s.** The store is `rows · cols · 24 KiB`, so it pays only when
/// one matrix is applied to many vectors. See [`PolyMatrix::prepare`].
pub struct PreparedMatrix {
    rows: Vec<crate::ring::PreparedVec>,
    cols: usize,
}

impl PolyMatrix {
    // @genesis 47976f7 2026-09-17 — linalg::PolyMatrix::prepare
    /// Forward-transform every entry, once.
    ///
    /// **Not wired into [`PolyMatrix::mat_vec_mul`], deliberately.** The store
    /// is `rows · cols · 3 · RING_DEGREE · 8` bytes = `rows · cols · 24 KiB`:
    ///
    /// * the inner Ajtai matrix `A` is `1 × 8192` → **192 MiB**, built once and
    ///   applied to all `BLOCKS` message blocks, which is what makes it pay;
    /// * `ringswitch`'s `R^lin` matrix `M` is `5 × 40976` → **4.8 GiB**, which
    ///   does not pay and must not be prepared.
    ///
    /// A matrix applied *once* should never be prepared: preparation performs
    /// exactly the transforms the unprepared dot would, and then holds them.
    pub fn prepare(&self) -> PreparedMatrix {
        let n: usize = self.0.len();
        let c: usize = self.cols();
        let mut rows: Vec<crate::ring::PreparedVec> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            rows.push(crate::ring::prepare_vec(&self.0[i].0, c));
            i += 1;
        }
        PreparedMatrix { rows, cols: c }
    }
}

impl PreparedMatrix {
    // @genesis 47976f7 2026-09-17 — linalg::PreparedMatrix::rows
    /// The number of prepared rows.
    pub fn rows(&self) -> usize {
        self.rows.len()
    }

    // @genesis 47976f7 2026-09-17 — linalg::PreparedMatrix::apply
    /// `A *ᵥ v`, with `A`'s transforms already in hand (spec: `matVecMul`,
    /// `Vectors.lean:81` -- the same product [`PolyMatrix::mat_vec_mul`]
    /// computes).
    pub fn apply(&self, v: &PolyVec) -> PolyVec {
        let n: usize = self.rows.len();
        let w: usize = if self.cols <= v.0.len() { self.cols } else { v.0.len() };
        let mut out: Vec<Rq> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            out.push(crate::ring::dot_prepared(&self.rows[i], &v.0, w));
            i += 1;
        }
        PolyVec(out)
    }
}

impl PolyMatrix {
    // @genesis 09a57ac 2026-09-17 — linalg::PolyMatrix::prepare_digits
    /// Forward-transform every entry under **two** primes, for the bounded dot.
    ///
    /// Pairs with [`PreparedMatrix::apply_digits`], and carries that method's
    /// precondition: the vectors it will be applied to must have every
    /// coefficient below `GADGET_BASE`. Two thirds of `prepare`'s store -- 128
    /// MiB for the inner Ajtai matrix rather than 192 MiB.
    pub fn prepare_digits(&self) -> PreparedMatrix {
        let n: usize = self.0.len();
        let c: usize = self.cols();
        let mut rows: Vec<crate::ring::PreparedVec> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            rows.push(crate::ring::prepare_vec_two(&self.0[i].0, c));
            i += 1;
        }
        PreparedMatrix { rows, cols: c }
    }
}

impl PreparedMatrix {
    // @genesis 09a57ac 2026-09-17 — linalg::PreparedMatrix::apply_digits
    /// `A *ᵥ v` for a `v` of gadget digits (spec: `matVecMul`,
    /// `Vectors.lean:81` -- the same product [`PolyMatrix::mat_vec_mul`]
    /// computes).
    ///
    /// **Only correct when every coefficient of every entry of `v` is below
    /// `GADGET_BASE`**, and only for a `self` built by
    /// [`PolyMatrix::prepare_digits`]. See
    /// [`crate::ring::dot_prepared_digits`] for why the precondition cannot be
    /// a type.
    pub fn apply_digits(&self, v: &PolyVec) -> PolyVec {
        let n: usize = self.rows.len();
        let w: usize = if self.cols <= v.0.len() { self.cols } else { v.0.len() };
        let mut out: Vec<Rq> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            out.push(crate::ring::dot_prepared_digits(&self.rows[i], &v.0, w));
            i += 1;
        }
        PolyVec(out)
    }
}

// ---------------------------------------------------------------------------
// FROZEN 2026-09-18 -- candidate T29, the compact raw-message carrier
// The FIRST translation, copied verbatim from hachi/src. Do not edit.
// ---------------------------------------------------------------------------
// ---------------------------------------------------------------------------
// The compact raw carrier, per block
// ---------------------------------------------------------------------------

// @genesis af3f7d5 2026-09-18 — linalg::RawVec32
/// One message block held in [`crate::ring::RawRq32`]s: half the bytes of a
/// [`PolyVec`].
///
/// The raw message is `Vec<RawVec32>`, and a consumer expands one block --
/// `MESSAGE_ROWS` elements, 8 MiB at the pin -- for the length of one loop
/// iteration. See `RawRq32` for why the representation exists and why nothing
/// computes in it.
pub struct RawVec32(Vec<crate::ring::RawRq32>);

impl RawVec32 {
    // @genesis af3f7d5 2026-09-18 — linalg::RawVec32::compact
    /// Compact a vector of reduced ring elements.
    pub fn compact(v: &PolyVec) -> RawVec32 {
        let n: usize = v.0.len();
        let mut out: Vec<crate::ring::RawRq32> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            out.push(crate::ring::RawRq32::compact(&v.0[i]));
            i += 1;
        }
        RawVec32(out)
    }

    // @genesis af3f7d5 2026-09-18 — linalg::RawVec32::expand
    /// The vector back.
    pub fn expand(&self) -> PolyVec {
        let n: usize = self.0.len();
        let mut out: Vec<Rq> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            out.push(self.0[i].expand());
            i += 1;
        }
        PolyVec(out)
    }
}


// @genesis b54235e 2026-09-19 — linalg::PreparedMatrixG
/// A matrix prepared in the single Goldilocks lane (candidate T27).
pub struct PreparedMatrixG {
    rows: Vec<crate::ring::PreparedVecG>,
    cols: usize,
}

impl PolyMatrix {
    // @genesis b54235e 2026-09-19 — linalg::PolyMatrix::prepare_digits_gold
    /// Prepare every row in the Goldilocks lane, for the digit path.
    pub fn prepare_digits_gold(&self) -> PreparedMatrixG {
        let n: usize = self.0.len();
        let c: usize = self.cols();
        let mut rows: Vec<crate::ring::PreparedVecG> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            rows.push(crate::ring::prepare_vec_gold(&self.0[i].0, c));
            i += 1;
        }
        PreparedMatrixG { rows, cols: c }
    }
}

impl PreparedMatrixG {
    // @genesis 47976f7 2026-09-17 — linalg::PreparedMatrixG::rows
    /// The number of prepared rows.
    pub fn rows(&self) -> usize {
        self.rows.len()
    }

    // @genesis b54235e 2026-09-19 — linalg::PreparedMatrixG::apply_digits_gold
    /// `M · v` with every row prepared, in one Goldilocks lane.
    pub fn apply_digits_gold(&self, v: &PolyVec) -> PolyVec {
        let n: usize = self.rows.len();
        let w: usize = if self.cols <= v.0.len() { self.cols } else { v.0.len() };
        let mut out: Vec<Rq> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            out.push(crate::ring::dot_prepared_digits_gold(&self.rows[i], &v.0, w));
            i += 1;
        }
        PolyVec(out)
    }
}


// @genesis b97d6dd 2026-09-21 — linalg::PreparedMatrixGA
// Card G2 (2026-09-21): the general path in two lanes instead of three.
/// A matrix prepared for the **general** path in two lanes, one Goldilocks
/// and one 31-bit Barrett (candidate G2): one
/// [`crate::ring::PreparedVecGA`] per row.
pub struct PreparedMatrixGA {
    rows: Vec<crate::ring::PreparedVecGA>,
    cols: usize,
}

impl PolyMatrix {
    // @genesis b97d6dd 2026-09-21 — linalg::PolyMatrix::prepare_ga
    /// Prepare every row in the general path's two lanes.
    ///
    /// Pairs with [`PreparedMatrixGA::apply_ga`]. The three-lane
    /// [`PolyMatrix::prepare`] stays where it is, dead but proved.
    pub fn prepare_ga(&self) -> PreparedMatrixGA {
        let n: usize = self.0.len();
        let c: usize = self.cols();
        let mut rows: Vec<crate::ring::PreparedVecGA> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            rows.push(crate::ring::prepare_vec_ga(&self.0[i].0, c));
            i += 1;
        }
        PreparedMatrixGA { rows, cols: c }
    }
}

impl PreparedMatrixGA {
    // @genesis b97d6dd 2026-09-21 — linalg::PreparedMatrixGA::apply_ga
    /// `M · v` with `M` prepared in two lanes: the value
    /// [`PreparedMatrix::apply`] computes, two transforms per term instead of
    /// three.
    pub fn apply_ga(&self, v: &PolyVec) -> PolyVec {
        let n: usize = self.rows.len();
        let w: usize = if self.cols <= v.0.len() { self.cols } else { v.0.len() };
        let mut out: Vec<Rq> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            out.push(crate::ring::dot_prepared_ga(&self.rows[i], &v.0, w));
            i += 1;
        }
        PolyVec(out)
    }
}

// ---------------------------------------------------------------------------
// Card T35: the limb-split general path (PROTOTYPE, 2026-09-21)
// ---------------------------------------------------------------------------

// @genesis f3a4046 2026-09-21 — linalg::PreparedMatrixL2
/// A matrix prepared as two 16-bit limbs per row (card T35, variant 2A).
pub struct PreparedMatrixL2 {
    rows: Vec<crate::ring::PreparedVecL2>,
    cols: usize,
}

impl PolyMatrix {
    // @genesis f3a4046 2026-09-21 — linalg::PolyMatrix::prepare_limbs2
    /// Prepare every row as two 16-bit limbs.
    pub fn prepare_limbs2(&self) -> PreparedMatrixL2 {
        let n: usize = self.0.len();
        let c: usize = self.cols();
        let mut rows: Vec<crate::ring::PreparedVecL2> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            rows.push(crate::ring::prepare_vec_limbs2(&self.0[i].0, c));
            i += 1;
        }
        PreparedMatrixL2 { rows, cols: c }
    }

}

impl PreparedMatrixL2 {
    // @genesis f3a4046 2026-09-21 — linalg::PreparedMatrixL2::apply_limbs2
    /// `M · v` with `M` prepared as two limbs.
    pub fn apply_limbs2(&self, v: &PolyVec) -> PolyVec {
        let n: usize = self.rows.len();
        let w: usize = if self.cols <= v.0.len() { self.cols } else { v.0.len() };
        let mut out: Vec<Rq> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            out.push(crate::ring::dot_prepared_limbs2(&self.rows[i], &v.0, w));
            i += 1;
        }
        PolyVec(out)
    }
}
