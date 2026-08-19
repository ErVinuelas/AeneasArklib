//! `src/linalg.rs` computes the vector and matrix operations over `R_q`.
//!
//! Two things are worth checking beyond linearity, and they are the two that a
//! reader cannot verify by inspection:
//!
//! * the matrix-vector product is the one a hand computation gives, on a `2 × 2`
//!   example small enough to write out;
//! * the flattening convention matches `finProdFinEquiv`, which is what the
//!   gadget layout and `flattenBlocks` both go through. Getting that transposed
//!   would leave every operation individually plausible and the composition
//!   wrong.

mod support;

use hachi::linalg::{flatten_blocks, PolyMatrix, PolyVec};
use hachi::ring::Rq;
use support::{rq_from_u64s, show, show_vec, Lcg};

/// `[[a, b], [c, d]] *ᵥ [x, y] = [ax + by, cx + dy]`, with every entry a
/// *constant* ring element so the arithmetic is `Z_q` and can be checked by
/// hand.
#[test]
fn mat_vec_mul_matches_a_hand_computation() {
    let a = PolyMatrix::new(vec![
        PolyVec::new(vec![rq_from_u64s(&[2]), rq_from_u64s(&[3])]),
        PolyVec::new(vec![rq_from_u64s(&[5]), rq_from_u64s(&[7])]),
    ]);
    let v = PolyVec::new(vec![rq_from_u64s(&[11]), rq_from_u64s(&[13])]);

    let out = a.mat_vec_mul(&v);
    assert_eq!(out.len(), 2);
    assert_eq!(out.get(0).coeff(0).to_u64(), 2 * 11 + 3 * 13);
    assert_eq!(out.get(1).coeff(0).to_u64(), 5 * 11 + 7 * 13);
}

/// The same, one degree up: with `X` in the matrix the product has to place
/// coefficients as well as add them.
#[test]
fn mat_vec_mul_multiplies_in_the_ring_not_just_the_field() {
    // [[X]] *ᵥ [1 + X] = [X + X²]
    let a = PolyMatrix::new(vec![PolyVec::new(vec![rq_from_u64s(&[0, 1])])]);
    let v = PolyVec::new(vec![rq_from_u64s(&[1, 1])]);
    let out = a.mat_vec_mul(&v);
    assert!(
        out.get(0).equals(&rq_from_u64s(&[0, 1, 1])),
        "expected X + X², got {}",
        show(out.get(0))
    );
}

#[test]
fn dot_is_symmetric_and_bilinear() {
    let mut rng = Lcg::new(0x0102_0304_0506_0708);
    for _ in 0..4 {
        let u = rng.next_poly_vec(3);
        let v = rng.next_poly_vec(3);
        let w = rng.next_poly_vec(3);
        assert!(u.dot(&v).equals(&v.dot(&u)), "dot is not symmetric");
        assert!(
            u.dot(&v.add(&w)).equals(&u.dot(&v).add(&u.dot(&w))),
            "dot is not additive on the right"
        );
        let c = rng.next_rq();
        assert!(
            u.dot(&v.scalar_mul(&c)).equals(&c.mul(&u.dot(&v))),
            "dot does not pull out a scalar"
        );
    }
}

/// `dot` on the zero vector is zero, and on a length-zero vector too -- the
/// empty-sum case the spec gets from `List.sum []`.
#[test]
fn dot_of_empty_and_zero_vectors_is_zero() {
    let empty = PolyVec::new(vec![]);
    assert!(empty.dot(&empty).is_zero());
    let z = PolyVec::zeros(4);
    let mut rng = Lcg::new(0x1111_2222_3333_4444);
    assert!(z.dot(&rng.next_poly_vec(4)).is_zero());
}

/// `A *ᵥ (v + w) = A *ᵥ v + A *ᵥ w`: the property the correctness proof uses to
/// move a commitment across a sum.
#[test]
fn mat_vec_mul_is_additive() {
    let mut rng = Lcg::new(0x9999_8888_7777_6666);
    let a = rng.next_poly_matrix(2, 3);
    let v = rng.next_poly_vec(3);
    let w = rng.next_poly_vec(3);
    let lhs = a.mat_vec_mul(&v.add(&w));
    let rhs = a.mat_vec_mul(&v).add(&a.mat_vec_mul(&w));
    assert!(lhs.equals(&rhs), "matrix-vector product is not additive");
}

/// `A *ᵥ (c •ᵥ v) = c •ᵥ (A *ᵥ v)` (the spec's `matVecMul_scalarVecMul`).
#[test]
fn mat_vec_mul_commutes_with_scaling() {
    let mut rng = Lcg::new(0x4444_3333_2222_1111);
    let a = rng.next_poly_matrix(2, 3);
    let v = rng.next_poly_vec(3);
    let c = rng.next_rq();
    let lhs = a.mat_vec_mul(&v.scalar_mul(&c));
    let rhs = a.mat_vec_mul(&v).scalar_mul(&c);
    assert!(lhs.equals(&rhs), "scaling does not commute with the product");
}

/// **The flattening convention.** `finProdFinEquiv (i, w) = w + width·i`, so entry
/// `width·i + w` of the flattening is entry `w` of block `i`. Checked with
/// distinguishable blocks, which is what makes a transposition visible.
#[test]
fn flatten_blocks_is_block_major() {
    let blocks = vec![
        PolyVec::new(vec![rq_from_u64s(&[10]), rq_from_u64s(&[11])]),
        PolyVec::new(vec![rq_from_u64s(&[20]), rq_from_u64s(&[21])]),
        PolyVec::new(vec![rq_from_u64s(&[30]), rq_from_u64s(&[31])]),
    ];
    let flat = flatten_blocks(&blocks);
    assert_eq!(flat.len(), 6);
    let got: Vec<u64> = (0..flat.len()).map(|j| flat.get(j).coeff(0).to_u64()).collect();
    assert_eq!(
        got,
        vec![10, 11, 20, 21, 30, 31],
        "flattening is not block-major: {}",
        show_vec(&flat)
    );

    // Stated the way the spec states it, for every index: flat[width·i + w] = blocks[i][w].
    let width = 2;
    for i in 0..blocks.len() {
        for w in 0..width {
            assert!(
                flat.get(width * i + w).equals(blocks[i].get(w)),
                "flat[{}] is not block {i} entry {w}",
                width * i + w
            );
        }
    }
}

/// Flattening nothing gives nothing, and flattening empty blocks gives nothing --
/// the degenerate cases an index computation with an off-by-one tends to get
/// wrong.
#[test]
fn flatten_blocks_handles_degenerate_shapes() {
    assert_eq!(flatten_blocks(&vec![]).len(), 0);
    assert_eq!(
        flatten_blocks(&vec![PolyVec::new(vec![]), PolyVec::new(vec![])]).len(),
        0
    );
}

/// Vector equality is entrywise, and a difference in the last entry is not
/// missed.
#[test]
fn vector_equality_examines_every_entry() {
    let u = PolyVec::new(vec![Rq::zero(), Rq::zero()]);
    let v = PolyVec::new(vec![Rq::zero(), Rq::one()]);
    assert!(!u.equals(&v));
    assert!(u.equals(&PolyVec::zeros(2)));
    // Different lengths are unequal rather than a panic or a prefix comparison.
    assert!(!u.equals(&PolyVec::zeros(3)));
}

/// `cols()` reads the width off row 0, and is `0` for a matrix with no rows --
/// the case where there is no row 0 to read.
#[test]
fn matrix_shape_accessors() {
    let mut rng = Lcg::new(0xFFFF_0000_FFFF_0000);
    let a = rng.next_poly_matrix(3, 5);
    assert_eq!(a.rows(), 3);
    assert_eq!(a.cols(), 5);
    assert_eq!(a.row(0).len(), 5);

    let empty = PolyMatrix::new(vec![]);
    assert_eq!(empty.rows(), 0);
    assert_eq!(empty.cols(), 0);
}
