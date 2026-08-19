//! `src/ring.rs` computes in `R_q = Z_q[X] / (X^N + 1)`.
//!
//! What these tests are for: the equivalence proofs establish that the *extracted
//! model* agrees with ArkLib's `Rq`, which is a statement about the Lean side of
//! the translation. They say nothing about whether the Rust was the code anyone
//! meant to write. These do -- they are the cheap check that the operations really
//! are a commutative ring with the negacyclic wraparound, run in seconds instead
//! of at the end of a Lean build.
//!
//! The ring axioms are checked on a fixed seeded corpus rather than proved here;
//! the proofs are the Lean side's job. A failure is reproducible from the test
//! name, since the seeds are literals.

mod support;

use cpoly::Fp;
use hachi::params::RING_DEGREE;
use hachi::ring::Rq;
use support::{coeffs_of, rq_from_u64s, show, Lcg};

/// `X^k`, as a ring element.
fn x_pow(k: usize) -> Rq {
    let mut coeffs = vec![Fp::ZERO; RING_DEGREE];
    coeffs[k] = Fp::ONE;
    Rq::from_coeffs(&coeffs)
}

#[test]
fn zero_and_one_have_the_expected_coefficients() {
    let z = Rq::zero();
    assert_eq!(z.len(), RING_DEGREE);
    assert!(z.is_zero());
    assert_eq!(coeffs_of(&z), vec![0u64; RING_DEGREE]);

    let o = Rq::one();
    assert_eq!(o.coeff(0).to_u64(), 1);
    for k in 1..RING_DEGREE {
        assert_eq!(o.coeff(k).to_u64(), 0, "one has a nonzero coefficient at {k}");
    }
}

/// The spec's `constRq_val`: no reduction happens, so the constant sits alone in
/// the zeroth slot.
#[test]
fn constants_occupy_only_the_zeroth_slot() {
    let c = Fp::new(1234);
    let k = Rq::constant(c);
    assert_eq!(k.coeff(0).to_u64(), 1234);
    for i in 1..RING_DEGREE {
        assert_eq!(k.coeff(i).to_u64(), 0);
    }
}

/// `coeff ∘ from_coeffs` is the identity below the degree, and zero above it --
/// the spec's `ofFinCoeff_coeff`, `if k < N then c k else 0`.
#[test]
fn coeff_of_from_coeffs_round_trips() {
    let mut rng = Lcg::new(0x0000_1111_2222_3333);
    let mut coeffs = Vec::new();
    for _ in 0..RING_DEGREE {
        coeffs.push(rng.next_fp());
    }
    let a = Rq::from_coeffs(&coeffs);
    for k in 0..RING_DEGREE {
        assert_eq!(a.coeff(k).to_u64(), coeffs[k].to_u64(), "coefficient {k}");
    }
    // And past the degree the read is zero rather than a panic.
    assert_eq!(a.coeff(RING_DEGREE).to_u64(), 0);
    assert_eq!(a.coeff(RING_DEGREE + 17).to_u64(), 0);
}

/// Short input: the missing high coefficients are zero, not garbage, and the
/// result still has the full width.
#[test]
fn from_coeffs_zero_pads_a_short_input() {
    let a = rq_from_u64s(&[7, 8]);
    assert_eq!(a.len(), RING_DEGREE);
    assert_eq!(a.coeff(0).to_u64(), 7);
    assert_eq!(a.coeff(1).to_u64(), 8);
    assert_eq!(a.coeff(2).to_u64(), 0);
}

/// Over-long input: the tail is dropped rather than widening the ring.
#[test]
fn from_coeffs_truncates_an_overlong_input() {
    let mut v = Vec::new();
    for i in 0..(RING_DEGREE + 10) {
        v.push(Fp::new(i as u64 + 1));
    }
    let a = Rq::from_coeffs(&v);
    assert_eq!(a.len(), RING_DEGREE);
    assert_eq!(a.coeff(RING_DEGREE - 1).to_u64(), RING_DEGREE as u64);
}

#[test]
fn addition_is_commutative_and_associative() {
    let mut rng = Lcg::new(0x1234_5678_9ABC_DEF0);
    for _ in 0..8 {
        let (a, b, c) = (rng.next_rq(), rng.next_rq(), rng.next_rq());
        assert!(a.add(&b).equals(&b.add(&a)), "add not commutative");
        assert!(
            a.add(&b).add(&c).equals(&a.add(&b.add(&c))),
            "add not associative"
        );
        assert!(a.add(&Rq::zero()).equals(&a), "zero is not neutral");
        assert!(a.add(&a.neg()).is_zero(), "negation does not cancel");
        assert!(a.sub(&b).equals(&a.add(&b.neg())), "sub is not add-of-neg");
    }
}

#[test]
fn multiplication_is_commutative_associative_and_distributive() {
    let mut rng = Lcg::new(0x0FED_CBA9_8765_4321);
    for _ in 0..4 {
        let (a, b, c) = (rng.next_rq(), rng.next_rq(), rng.next_rq());
        assert!(a.mul(&b).equals(&b.mul(&a)), "mul not commutative");
        assert!(
            a.mul(&b).mul(&c).equals(&a.mul(&b.mul(&c))),
            "mul not associative"
        );
        assert!(
            a.mul(&b.add(&c)).equals(&a.mul(&b).add(&a.mul(&c))),
            "mul does not distribute"
        );
        assert!(a.mul(&Rq::one()).equals(&a), "one is not neutral");
        assert!(a.mul(&Rq::zero()).is_zero(), "zero does not annihilate");
    }
}

/// The defining relation of the ring: `X^(N-1) · X = X^N = -1`.
///
/// This is the one test that would still pass for an ordinary (cyclic)
/// convolution if the sign were dropped -- with the wrong sign the product would
/// be `+1` -- so it is stated as the exact element, not just as "wraps around".
#[test]
fn the_negacyclic_relation_holds() {
    let top = x_pow(RING_DEGREE - 1);
    let x = x_pow(1);
    let product = top.mul(&x);
    let minus_one = Rq::one().neg();
    assert!(
        product.equals(&minus_one),
        "X^(N-1)·X should be -1, got {}",
        show(&product)
    );
    // ... and it is *not* +1, i.e. this ring is not the cyclic one.
    assert!(!product.equals(&Rq::one()));
}

/// Wraparound at a general index: `X^i · X^j` is `X^(i+j)` below the degree and
/// `-X^(i+j-N)` above it.
#[test]
fn monomial_products_wrap_with_a_sign() {
    for i in [0usize, 1, 7, RING_DEGREE - 1] {
        for j in [0usize, 1, 13, RING_DEGREE - 1] {
            let product = x_pow(i).mul(&x_pow(j));
            let s = i + j;
            let expected = if s < RING_DEGREE {
                x_pow(s)
            } else {
                x_pow(s - RING_DEGREE).neg()
            };
            assert!(
                product.equals(&expected),
                "X^{i} · X^{j} wrong: got {}",
                show(&product)
            );
        }
    }
}

/// Scalar multiplication is multiplication by the constant, which is the spec's
/// `constRq_mul_coeff` -- and it is what the gadget product relies on.
#[test]
fn scalar_mul_agrees_with_multiplication_by_a_constant() {
    let mut rng = Lcg::new(0xAAAA_BBBB_CCCC_DDDD);
    for _ in 0..8 {
        let a = rng.next_rq();
        let c = rng.next_fp();
        assert!(
            a.scalar_mul(c).equals(&Rq::constant(c).mul(&a)),
            "scalar_mul disagrees with constant multiplication"
        );
    }
}

/// A copy is equal to its original and independent of it. (Independence is not
/// observable through the API -- there is no mutator -- but the equality is the
/// half a proof will need.)
#[test]
fn copy_preserves_the_element() {
    let mut rng = Lcg::new(0x5555_6666_7777_8888);
    let a = rng.next_rq();
    assert!(a.copy().equals(&a));
}

/// Equality is coefficientwise, and it is not fooled by a difference in a single
/// high coefficient -- the failure mode of a loop that stops early.
#[test]
fn equality_examines_every_coefficient() {
    let mut coeffs = vec![Fp::ZERO; RING_DEGREE];
    let a = Rq::from_coeffs(&coeffs);
    coeffs[RING_DEGREE - 1] = Fp::ONE;
    let b = Rq::from_coeffs(&coeffs);
    assert!(!a.equals(&b), "equality ignored the top coefficient");
    assert!(a.equals(&Rq::zero()));
}

/// Field arithmetic is modular, so a coefficient sum that passes the modulus wraps
/// rather than growing. Checked at the boundary, where an unreduced
/// implementation would differ.
#[test]
fn coefficient_arithmetic_reduces_modulo_q() {
    let q = hachi::params::Q;
    let a = rq_from_u64s(&[q - 1]);
    let b = rq_from_u64s(&[2]);
    assert_eq!(a.add(&b).coeff(0).to_u64(), 1);
    assert_eq!(Rq::zero().sub(&b).coeff(0).to_u64(), q - 2);
    assert_eq!(b.neg().coeff(0).to_u64(), q - 2);
}
