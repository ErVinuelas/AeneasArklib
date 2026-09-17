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

// --- the transform behind `mul` ------------------------------------------------
//
// `Rq::mul` delegates to `hachi::ntt`, and everything that makes that delegation
// sound is a property of the constants in that module plus the exactness of the
// CRT. The tests below check those properties *from their definitions* rather
// than trusting the literals -- a wrong root or a wrong Barrett magic would
// otherwise show up only as a wrong product on some inputs and not others.
//
// The differential tests against a schoolbook oracle are the other half, and
// they are the reason the oracle is written out here: git history is the real
// reference, but a test that cannot run cannot fail.

use hachi::ntt;
use hachi::params::Q;

/// The three `(p, barrett m, ψ, ψ⁻¹, N⁻¹, BOUND mod p)` tuples, in the order
/// [`ntt::garner`] assumes.
fn aux_params() -> [(u64, u64, u64, u64, u64, u64); 3] {
    [
        (ntt::AUX_P1, ntt::AUX_M1, ntt::AUX_PSI1, ntt::AUX_PSIINV1, ntt::AUX_NINV1, ntt::AUX_BOFF1),
        (ntt::AUX_P2, ntt::AUX_M2, ntt::AUX_PSI2, ntt::AUX_PSIINV2, ntt::AUX_NINV2, ntt::AUX_BOFF2),
        (ntt::AUX_P3, ntt::AUX_M3, ntt::AUX_PSI3, ntt::AUX_PSIINV3, ntt::AUX_NINV3, ntt::AUX_BOFF3),
    ]
}

fn is_prime(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    let mut d = 2u64;
    while d * d <= n {
        if n % d == 0 {
            return false;
        }
        d += 1;
    }
    true
}

/// The transform length is the ring degree, because the transform is negacyclic.
#[test]
fn ntt_length_is_the_ring_degree() {
    assert_eq!(ntt::NTT_LEN, RING_DEGREE);
    assert_eq!(1usize << ntt::NTT_LOG, ntt::NTT_LEN);
}

/// Each auxiliary modulus is prime, below `2^30`, and admits a length-`2N`
/// transform. Below `2^30` is what keeps a product of two residues inside a
/// `u64`; `2N | p − 1` is what makes ψ exist at all.
#[test]
fn auxiliary_moduli_are_ntt_friendly_primes() {
    // Ordered, which is what `garner` skips two reductions on. The operands
    // are constants, so this is checked at compile time.
    const _: () = assert!(ntt::AUX_P1 < ntt::AUX_P2 && ntt::AUX_P2 < ntt::AUX_P3);
    for (p, _, _, _, _, _) in aux_params() {
        assert!(is_prime(p), "{p} is not prime");
        assert!(p < (1u64 << 30), "{p} is not below 2^30");
        assert_eq!((p - 1) % (2 * ntt::NTT_LEN as u64), 0, "2N does not divide {p} - 1");
    }
}

/// Each Barrett magic is `⌊2^64 / p⌋`, and [`ntt::aux_reduce`] really is `% p`
/// over the whole `u64` range its proof claims -- boundaries included.
#[test]
fn barrett_reduction_is_modular_reduction() {
    for (p, m, _, _, _, _) in aux_params() {
        let magic = u64::try_from((1u128 << 64) / u128::from(p)).unwrap();
        assert_eq!(m, magic, "barrett magic for {p}");
        let mut probes = vec![0u64, 1, p - 1, p, p + 1, 2 * p - 1, 2 * p, p * p - 1, p * p,
                              u64::MAX, u64::MAX - 1, u64::MAX / p * p];
        let mut rng = Lcg::new(0x4E54_5400_0000_0001 ^ p);
        for _ in 0..4000 {
            probes.push(rng.next_u64());
        }
        for x in probes {
            assert_eq!(ntt::aux_reduce(x, p, m), x % p, "aux_reduce({x}, {p})");
        }
    }
}

/// `aux_add`, `aux_sub`, `aux_mul` are the three field operations.
#[test]
fn auxiliary_arithmetic_is_field_arithmetic() {
    for (p, m, _, _, _, _) in aux_params() {
        let mut rng = Lcg::new(0x4155_5800_0000_0001 ^ p);
        for _ in 0..4000 {
            let a = rng.next_u64() % p;
            let b = rng.next_u64() % p;
            assert_eq!(ntt::aux_add(a, b, p), (a + b) % p);
            assert_eq!(ntt::aux_sub(a, b, p), (a + p - b) % p);
            let expected = u64::try_from(u128::from(a) * u128::from(b) % u128::from(p)).unwrap();
            assert_eq!(ntt::aux_mul(a, b, p, m), expected);
        }
    }
}

/// ψ has *exact* order `2N`: `ψ^N = −1`. For a prime modulus that is equivalent
/// to exact order `2N`, and it is what makes `X ↦ ψY` an isomorphism
/// `Z_p[X]/(X^N + 1) → Z_p[Y]/(Y^N − 1)`. Also that ψ⁻¹ and `N⁻¹` are the
/// inverses they claim to be.
#[test]
fn roots_have_exact_order_and_correct_inverses() {
    for (p, _, psi, psiinv, ninv, _) in aux_params() {
        let pm = u128::from(p);
        let mut acc = 1u128;
        for _ in 0..ntt::NTT_LEN {
            acc = acc * u128::from(psi) % pm;
        }
        assert_eq!(acc, u128::from(p - 1), "psi^N != -1 mod {p}");
        assert_eq!(u128::from(psi) * u128::from(psiinv) % pm, 1, "psiinv mod {p}");
        assert_eq!(u128::from(ntt::NTT_LEN as u64) * u128::from(ninv) % pm, 1, "ninv mod {p}");
    }
}

/// `psi_table` is the powers of ψ, which is the whole correctness rule for it.
#[test]
fn psi_table_is_the_powers_of_psi() {
    for (p, m, psi, _, _, _) in aux_params() {
        let t = ntt::psi_table(psi, p, m);
        assert_eq!(t.len(), ntt::NTT_LEN);
        let mut e = 1u128;
        for (i, &entry) in t.iter().enumerate() {
            assert_eq!(u128::from(entry), e, "psi_table[{i}] mod {p}");
            e = e * u128::from(psi) % u128::from(p);
        }
    }
}

/// The inverse transform undoes the forward one up to the factor `N`, which is
/// what `N⁻¹` in `untwist` cancels. Checked on the shapes a transform is most
/// likely to be wrong on: zero, the two extreme basis vectors, a constant
/// vector at the modulus boundary, an alternating pattern, and random data.
#[test]
fn transform_round_trips_up_to_the_length_factor() {
    for (p, m, psi, psiinv, ninv, _) in aux_params() {
        let pt = ntt::psi_table(psi, p, m);
        let it = ntt::psi_table(psiinv, p, m);
        let mut cases: Vec<Vec<u64>> = Vec::new();
        cases.push(vec![0u64; ntt::NTT_LEN]);
        let mut e0 = vec![0u64; ntt::NTT_LEN];
        e0[0] = 1;
        cases.push(e0);
        let mut etop = vec![0u64; ntt::NTT_LEN];
        etop[ntt::NTT_LEN - 1] = 1;
        cases.push(etop);
        cases.push(vec![p - 1; ntt::NTT_LEN]);
        cases.push((0..ntt::NTT_LEN).map(|i| if i % 2 == 0 { 0 } else { p - 1 }).collect());
        let mut rng = Lcg::new(0x524F_4F54_0000_0001 ^ p);
        for _ in 0..3 {
            cases.push((0..ntt::NTT_LEN).map(|_| rng.next_u64() % p).collect());
        }
        for c in &cases {
            let (fwd, scratch) = ntt::ntt_forward(c.clone(), ntt::zeros(ntt::NTT_LEN), &pt, p, m);
            assert!(fwd.iter().all(|&x| x < p), "forward output not canonical mod {p}");
            let (back, _) = ntt::ntt_inverse(fwd, scratch, &it, p, m);
            for i in 0..ntt::NTT_LEN {
                assert_eq!(
                    u128::from(back[i]) * u128::from(ninv) % u128::from(p),
                    u128::from(c[i]),
                    "round trip mod {p} at {i}"
                );
            }
        }
    }
}

/// The CRT reconstruction is exact on `[0, P)` -- at the boundaries of each
/// modulus and of each pairwise product, at the offset the pipeline actually
/// uses, and on random points.
#[test]
fn garner_reconstruction_is_exact() {
    let (p1, p2, p3) = (u128::from(ntt::AUX_P1), u128::from(ntt::AUX_P2), u128::from(ntt::AUX_P3));
    let big_p = p1 * p2 * p3;
    assert_eq!(u128::from(ntt::GARNER_P12), p1 * p2);
    assert_eq!(p1 * u128::from(ntt::GARNER_INV1) % p2, 1);
    assert_eq!((p1 * p2) % p3 * u128::from(ntt::GARNER_INV12) % p3, 1);

    let bound = u128::from(RING_DEGREE as u64) * u128::from(Q) * u128::from(Q);
    let mut xs: Vec<u128> = vec![
        0, 1, 2, p1 - 1, p1, p1 + 1, p2 - 1, p2, p2 + 1, p3 - 1, p3, p3 + 1,
        p1 * p2 - 1, p1 * p2, p1 * p2 + 1, p1 * p3, p2 * p3, big_p - 1, bound, 2 * bound,
    ];
    let mut rng = Lcg::new(0x4741_524E_4552_0001);
    for _ in 0..20_000 {
        let hi = u128::from(rng.next_u64());
        let lo = u128::from(rng.next_u64());
        xs.push(((hi << 64) | lo) % big_p);
    }
    for x in xs {
        assert_eq!(
            ntt::garner(
                u64::try_from(x % p1).unwrap(),
                u64::try_from(x % p2).unwrap(),
                u64::try_from(x % p3).unwrap(),
            ),
            x,
            "garner is not exact at {x}"
        );
    }
}

/// The offset is what makes the reconstructed value a natural number, and it has
/// to satisfy exactly two things: `2·BOUND < P`, so the reconstruction stays
/// exact; and `q | BOUND`, so `Rq::mul` needs no correction term.
#[test]
fn the_crt_offset_fits_and_vanishes_mod_q() {
    let bound = u128::from(RING_DEGREE as u64) * u128::from(Q) * u128::from(Q);
    let big_p = u128::from(ntt::AUX_P1) * u128::from(ntt::AUX_P2) * u128::from(ntt::AUX_P3);
    assert!(2 * bound < big_p, "2*BOUND does not fit under P");
    assert_eq!(bound % u128::from(Q), 0, "BOUND is not a multiple of q");
    for (p, _, _, _, _, boff) in aux_params() {
        assert_eq!(u128::from(boff), bound % u128::from(p), "BOUND mod {p}");
    }
}

/// The schoolbook convolution `Rq::mul` used to be, kept as a test oracle. This
/// is the reference every differential case below is judged against, and it is
/// deliberately the *old production body*, transliterated onto words.
fn schoolbook_oracle(a: &Rq, b: &Rq) -> Vec<u64> {
    let n = RING_DEGREE;
    let q = u128::from(Q);
    let mut out = Vec::with_capacity(n);
    for k in 0..n {
        let mut pos: u128 = 0;
        let mut neg: u128 = 0;
        for i in 0..n {
            let ai = u128::from(a.coeff(i).to_u64());
            if i <= k {
                pos += ai * u128::from(b.coeff(k - i).to_u64());
            } else {
                neg += ai * u128::from(b.coeff(k + n - i).to_u64());
            }
        }
        let p = u64::try_from(pos % q).unwrap();
        let m = u64::try_from(neg % q).unwrap();
        out.push(if p >= m { p - m } else { p + Q - m });
    }
    out
}

/// The transform's coefficients equal the schoolbook product's, on the shapes
/// that break implementations and on a deterministic random corpus.
///
/// `ntt::negconv_mod_q` is called directly rather than through [`Rq::mul`], so
/// that this test says the same thing before and after the production switch:
/// while `Rq::mul` is still the schoolbook loop, going through it would compare
/// the oracle with itself.
///
/// `all q−1` is the case that matters most: it is where the integer convolution
/// coefficients reach their maximum, so it is the case a too-small CRT modulus
/// or a too-small offset gets wrong.
#[test]
fn ntt_product_agrees_with_the_schoolbook_oracle() {
    let n = RING_DEGREE;
    let zero = Rq::zero();
    let one = Rq::one();
    let allmax = Rq::from_coeffs(&vec![Fp::new(Q - 1); n]);
    let alt = Rq::from_coeffs(
        &(0..n).map(|i| if i % 2 == 0 { Fp::new(Q - 1) } else { Fp::ZERO }).collect::<Vec<Fp>>(),
    );
    let mut rng = Lcg::new(0x4E54_5444_4946_4600);
    let arb = rng.next_rq();

    let mut cases: Vec<(Rq, Rq)> = vec![
        (zero.copy(), zero.copy()),
        (zero.copy(), arb.copy()),
        (one.copy(), arb.copy()),
        (arb.copy(), one.copy()),
        (x_pow(n - 1), x_pow(1)),
        (x_pow(n - 1), x_pow(n - 1)),
        (x_pow(n / 2), x_pow(n / 2)),
        (allmax.copy(), allmax.copy()),
        (alt.copy(), alt.copy()),
        (allmax.copy(), arb.copy()),
    ];
    for _ in 0..12 {
        cases.push((rng.next_rq(), rng.next_rq()));
    }

    for (i, (a, b)) in cases.iter().enumerate() {
        let want = schoolbook_oracle(a, b);
        let got = ntt::negconv_mod_q(&coeffs_of(a), &coeffs_of(b));
        assert_eq!(got.len(), n);
        for k in 0..n {
            assert_eq!(
                got[k], want[k],
                "case {i}: coefficient {k} disagrees with the schoolbook oracle"
            );
        }
        // And the same through the public operation, which is the schoolbook
        // loop today and the transform after the switch. Either way it has to
        // agree with the oracle.
        let via_mul = a.mul(b);
        assert_eq!(via_mul.len(), n);
        for k in 0..n {
            assert_eq!(via_mul.coeff(k).to_u64(), want[k], "case {i}: Rq::mul at {k}");
        }
    }
}

/// Every word the transform produces is a canonical representative below `q`.
/// `Fp::new` is the identity on the representation, so a word at or above `q`
/// would make the product an unreduced `Fp` -- which is the `Red` half of `Wf`,
/// and every downstream proof depends on it.
#[test]
fn ntt_product_coefficients_are_reduced() {
    let mut rng = Lcg::new(0x5245_4400_0000_0001);
    let allmax = Rq::from_coeffs(&vec![Fp::new(Q - 1); RING_DEGREE]);
    for a in [rng.next_rq(), allmax.copy()] {
        for b in [rng.next_rq(), allmax.copy()] {
            for w in ntt::negconv_mod_q(&coeffs_of(&a), &coeffs_of(&b)) {
                assert!(w < Q, "a transform coefficient is not reduced: {w}");
            }
        }
    }
}

/// `classify_short` + `mul_short_desc` agree with `Rq::mul` on every short
/// element, and decline exactly the ones over budget.
///
/// The oracle for Stage 6 candidate T17 Change 1. The protocol's challenges are
/// `ShortChallenge Φ 16`, so a valid `c` has centred `ℓ₁` norm at most
/// `params::OMEGA`; such an element needs signed negacyclic shifts, not a
/// three-prime NTT. The only thing worth asserting is that the fast path is
/// *the same product*, so every case below is compared against `Rq::mul`.
///
/// The cases are chosen to hit what the implementation can get wrong:
/// magnitudes beyond `±1` (a `-5` is protocol-valid if the budget still fits,
/// so `±1` must not be assumed); the **wrap**, where `X^N = −1` flips the sign
/// of whatever crosses the degree boundary; a coefficient at exactly `N − 1`,
/// which wraps for every nonzero shift; the budget boundary at 16 and 17; and
/// dense ternary, which must decline.
#[test]
fn short_multiplication_agrees_with_the_generic_one() {
    let mut rng = Lcg::new(0x5170_0000_0000_0011);
    let q = hachi::params::Q;
    let omega = hachi::params::OMEGA;

    // a dense-ish arbitrary right operand: the short side is `c`, not this
    let mut sc = Vec::new();
    for _ in 0..RING_DEGREE {
        sc.push(rng.next_u64() % q);
    }
    let s = rq_from_u64s(&sc);

    // (description, coefficient list) — each is `c`, built as raw words
    let mut cases: Vec<(&str, Vec<u64>)> = Vec::new();

    // weight 1, no wrap
    let mut c = vec![0u64; RING_DEGREE];
    c[0] = 1;
    cases.push(("weight 1 at index 0", c));

    // weight 1 at the last index: every shift wraps
    let mut c = vec![0u64; RING_DEGREE];
    c[RING_DEGREE - 1] = 1;
    cases.push(("weight 1 at index N-1", c));

    // a single negative unit (centred -1 is the word q-1)
    let mut c = vec![0u64; RING_DEGREE];
    c[3] = q - 1;
    cases.push(("weight 1, negative", c));

    // magnitude beyond +/-1: +5 and -5, total 10
    let mut c = vec![0u64; RING_DEGREE];
    c[7] = 5;
    c[RING_DEGREE - 2] = q - 5;
    cases.push(("magnitudes 5 and -5", c));

    // exactly at the budget: 16 units spread over 16 indices, mixed signs
    let mut c = vec![0u64; RING_DEGREE];
    let mut k = 0usize;
    while k < omega as usize {
        let at = (k * 61) % RING_DEGREE;
        c[at] = if k % 2 == 0 { 1 } else { q - 1 };
        k += 1;
    }
    cases.push(("weight 16, mixed signs", c));

    // exactly at the budget as a single coefficient
    let mut c = vec![0u64; RING_DEGREE];
    c[11] = omega;
    cases.push(("weight 16 in one coefficient", c));

    for (name, cc) in &cases {
        let cpoly_c = rq_from_u64s(cc);
        let desc = hachi::ring::classify_short(&cpoly_c)
            .unwrap_or_else(|| panic!("{name}: should classify as short"));
        let fast = hachi::ring::mul_short_desc(&desc, &s);
        let slow = cpoly_c.mul(&s);
        assert!(
            fast.equals(&slow),
            "{name}: short multiply disagrees with Rq::mul\n  short: {}\n  generic: {}",
            show(&fast),
            show(&slow)
        );
    }

    // over budget by one unit: must decline, and the caller then falls back
    let mut c = vec![0u64; RING_DEGREE];
    let mut k = 0usize;
    while k < omega as usize + 1 {
        c[k * 7] = 1;
        k += 1;
    }
    assert!(
        hachi::ring::classify_short(&rq_from_u64s(&c)).is_none(),
        "weight 17 is over the omega budget and must decline"
    );

    // dense ternary, the shape the acceptance test draws: must decline
    let mut c = vec![0u64; RING_DEGREE];
    for e in c.iter_mut() {
        let t = rng.next_u64() % 3;
        *e = if t == 2 { q - 1 } else { t };
    }
    assert!(
        hachi::ring::classify_short(&rq_from_u64s(&c)).is_none(),
        "dense ternary has l1 norm in the hundreds and must decline"
    );
}

/// `mul_short_add_into` accumulates exactly what `mul_short_desc` returns.
///
/// The oracle for Stage 6 candidate T17 Change 2. The in-place form exists only
/// to avoid allocating, so the property to pin is that it changes nothing about
/// the value: for every description and every accumulator,
/// `add_into(desc, s, acc)` leaves `acc` holding `acc + desc·s`.
///
/// A *non-zero* starting accumulator is the case worth testing, and the one a
/// zero-initialised test would miss: the function adds into whatever is already
/// there, so an implementation that overwrote instead of accumulating would pass
/// against a zero accumulator and be wrong on the second message block. The
/// repeated-application case below is that second block.
#[test]
fn short_multiplication_in_place_accumulates() {
    let mut rng = Lcg::new(0x5170_0000_0000_0012);
    let q = hachi::params::Q;

    // an arbitrary right operand and an arbitrary *non-zero* accumulator
    let mut sc = Vec::new();
    let mut ac = Vec::new();
    for _ in 0..RING_DEGREE {
        sc.push(rng.next_u64() % q);
        ac.push(rng.next_u64() % q);
    }
    let s = rq_from_u64s(&sc);
    let acc0 = rq_from_u64s(&ac);

    // the same descriptions the returning form is tested on
    let mut cases: Vec<(&str, Vec<u64>)> = Vec::new();
    let mut c = vec![0u64; RING_DEGREE];
    c[0] = 1;
    cases.push(("weight 1 at index 0", c));
    let mut c = vec![0u64; RING_DEGREE];
    c[RING_DEGREE - 1] = 1;
    cases.push(("weight 1 at index N-1", c));
    let mut c = vec![0u64; RING_DEGREE];
    c[3] = q - 1;
    cases.push(("weight 1, negative", c));
    let mut c = vec![0u64; RING_DEGREE];
    c[7] = 5;
    c[RING_DEGREE - 2] = q - 5;
    cases.push(("magnitudes 5 and -5", c));
    let mut c = vec![0u64; RING_DEGREE];
    c[11] = 16;
    cases.push(("the whole budget in one coefficient", c));

    for (name, coeffs) in &cases {
        let cc = rq_from_u64s(coeffs);
        let desc = hachi::ring::classify_short(&cc)
            .unwrap_or_else(|| panic!("{name}: should classify as short"));

        // against the returning form, plus the accumulator
        let expected = acc0.add(&hachi::ring::mul_short_desc(&desc, &s));
        let mut got = acc0.copy();
        hachi::ring::mul_short_add_into(&desc, &s, &mut got);
        assert!(
            got.equals(&expected),
            "{name}: in-place accumulation disagrees with add(mul_short_desc(..))"
        );

        // and it really accumulates: applying it twice adds twice
        let expected2 = expected.add(&hachi::ring::mul_short_desc(&desc, &s));
        hachi::ring::mul_short_add_into(&desc, &s, &mut got);
        assert!(
            got.equals(&expected2),
            "{name}: applying it twice did not add twice -- it overwrites"
        );
    }
}
// Change 3's oracle, to append to hachi/tests/ring_semantics.rs.

/// `dot_fused` agrees with summing per-term `Rq::mul`, at every width that
/// matters.
///
/// The oracle for Stage 6 candidate T18/Change 3. The fused dot keeps its
/// accumulator in the transform domain, so it reconstructs ONE integer for a
/// whole chunk rather than one per product, and that integer carries the CRT
/// offset `L · BOUND` rather than a single `BOUND`.
///
/// **`n = 8` is the load-bearing case, and it is deliberately small.** With
/// random dense operands, coefficient 0's negative antidiagonal has `N − 1`
/// terms against the positive one's 1, so the accumulated value under a
/// *single* offset is
///
/// ```text
///   L·E[posSum] + BOUND − L·E[negSum]
/// ```
///
/// which turns negative from `L = 5` onwards (computed: `L = 4` leaves
/// `+3.7e19`, `L = 5` leaves `−4.7e21`). Garner does not reconstruct negatives,
/// so an implementation that forgot to scale the offset by the chunk length is
/// wrong here and *right* at `n ≤ 4` -- which is exactly why a test that only
/// tried one or two terms would pass while the commitment silently computed
/// garbage. It is a small test only because the arithmetic was worked out
/// first; nothing about `n = 8` looks special.
///
/// `n = DOT_CHUNK + 1` is the other case with teeth: it is the only width here
/// that runs the chunk loop twice, so it is what checks that the ring-level
/// accumulator carries correctly across a reduction and that the final short
/// chunk gets its own (smaller) offset.
#[test]
fn fused_dot_agrees_with_summed_products() {
    let mut rng = Lcg::new(0x5170_0000_0000_0013);
    let q = hachi::params::Q;
    let chunk = hachi::ring::DOT_CHUNK;

    // dense random operands are the adversarial shape here, not a lazy choice:
    // they are what makes the negative antidiagonal dominate
    let build = |rng: &mut Lcg, n: usize| -> Vec<hachi::ring::Rq> {
        let mut v = Vec::with_capacity(n);
        for _ in 0..n {
            let mut cs = Vec::with_capacity(RING_DEGREE);
            for _ in 0..RING_DEGREE {
                cs.push(rng.next_u64() % q);
            }
            v.push(rq_from_u64s(&cs));
        }
        v
    };

    for &n in &[1usize, 2, 4, 5, 8, 33, chunk, chunk + 1] {
        let a = build(&mut rng, n);
        let b = build(&mut rng, n);

        // the oracle: the champion's per-term product, summed at ring level
        let mut expected = hachi::ring::Rq::zero();
        let mut j = 0usize;
        while j < n {
            expected = expected.add(&a[j].mul(&b[j]));
            j += 1;
        }

        let got = hachi::ring::dot_fused(&a, &b, n);
        assert!(
            got.equals(&expected),
            "fused dot disagrees at n = {n} (chunks = {})",
            (n + chunk - 1) / chunk
        );
    }
}

/// The fused dot is what `PolyVec::dot` now computes.
///
/// Separate from the test above because it pins the *caller*: `dot` also has to
/// keep truncating to the shorter operand, which the fused path must not
/// disturb.
#[test]
fn poly_vec_dot_matches_the_fused_dot() {
    let mut rng = Lcg::new(0x5170_0000_0000_0014);
    let q = hachi::params::Q;
    for &(la, lb) in &[(4usize, 4usize), (4, 7), (9, 3)] {
        let mk = |rng: &mut Lcg, n: usize| {
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                let mut cs = Vec::with_capacity(RING_DEGREE);
                for _ in 0..RING_DEGREE {
                    cs.push(rng.next_u64() % q);
                }
                v.push(rq_from_u64s(&cs));
            }
            hachi::linalg::PolyVec::new(v)
        };
        let u = mk(&mut rng, la);
        let v = mk(&mut rng, lb);
        let n = la.min(lb);
        let mut expected = hachi::ring::Rq::zero();
        let mut j = 0usize;
        while j < n {
            expected = expected.add(&u.get(j).mul(v.get(j)));
            j += 1;
        }
        assert!(
            u.dot(&v).equals(&expected),
            "PolyVec::dot at lengths {la}/{lb} disagrees with the truncated sum"
        );
    }
}

/// `dot_prepared` computes exactly what `dot_fused` does.
///
/// The oracle for Stage 6 candidate T19/Change 4. Preparation only caches the
/// left operand's forward transforms, so the value must be bit-identical to the
/// unprepared fused dot -- and, transitively, to the summed per-term products.
///
/// The widths are the same set the fused dot is tested at, for the same reason:
/// `n = 8` is where a mis-scaled CRT offset would first show, and
/// `n = DOT_CHUNK + 1` is the only one that runs the chunk loop twice, which is
/// what checks that a *prepared* operand is indexed by absolute position `j`
/// rather than by position-within-chunk. That indexing is the one thing
/// preparation can get wrong and the unprepared path cannot.
#[test]
fn prepared_dot_agrees_with_the_fused_dot() {
    let mut rng = Lcg::new(0x5170_0000_0000_0015);
    let q = hachi::params::Q;
    let chunk = hachi::ring::DOT_CHUNK;

    let build = |rng: &mut Lcg, n: usize| -> Vec<hachi::ring::Rq> {
        let mut v = Vec::with_capacity(n);
        for _ in 0..n {
            let mut cs = Vec::with_capacity(RING_DEGREE);
            for _ in 0..RING_DEGREE {
                cs.push(rng.next_u64() % q);
            }
            v.push(rq_from_u64s(&cs));
        }
        v
    };

    for &n in &[1usize, 2, 5, 8, 33, chunk, chunk + 1] {
        let a = build(&mut rng, n);
        let b = build(&mut rng, n);
        let prep = hachi::ring::prepare_vec(&a, n);
        assert_eq!(prep.len(), n, "prepared length at n = {n}");
        let got = hachi::ring::dot_prepared(&prep, &b, n);
        let expected = hachi::ring::dot_fused(&a, &b, n);
        assert!(
            got.equals(&expected),
            "prepared dot disagrees with the fused dot at n = {n} (chunks = {})",
            (n + chunk - 1) / chunk
        );
    }
}

/// `dot_prepared_digits` is `dot_fused`, on the inputs it is allowed.
///
/// The two-prime reconstruction is exact only because one operand's
/// coefficients are below `GADGET_BASE`; nothing in the types says so, so this
/// is the only check that the bound chosen for `DOT_CHUNK_D` is the right one.
/// Widths straddle the chunk boundary in both directions, because a
/// reconstruction that overflows `p1 · p2` fails *per chunk* and a single-chunk
/// test would never see it.
#[test]
fn bounded_prepared_dot_agrees_with_the_fused_dot() {
    let mut rng = Lcg::new(0x5170_0000_0000_0016);
    let q = hachi::params::Q;
    let base = hachi::params::GADGET_BASE;
    let chunk = hachi::ring::DOT_CHUNK_D;

    let dense = |rng: &mut Lcg, n: usize| -> Vec<hachi::ring::Rq> {
        let mut v = Vec::with_capacity(n);
        for _ in 0..n {
            let mut cs = Vec::with_capacity(RING_DEGREE);
            for _ in 0..RING_DEGREE {
                cs.push(rng.next_u64() % q);
            }
            v.push(rq_from_u64s(&cs));
        }
        v
    };
    // every coefficient a digit: the precondition, and the worst case for the
    // bound is the largest digit, so `base - 1` is forced in explicitly.
    let digits = |rng: &mut Lcg, n: usize| -> Vec<hachi::ring::Rq> {
        let mut v = Vec::with_capacity(n);
        for j in 0..n {
            let mut cs = Vec::with_capacity(RING_DEGREE);
            for k in 0..RING_DEGREE {
                if (j + k) % 7 == 0 {
                    cs.push(base - 1);
                } else {
                    cs.push(rng.next_u64() % base);
                }
            }
            v.push(rq_from_u64s(&cs));
        }
        v
    };

    for &n in &[1usize, 2, 5, chunk - 1, chunk, chunk + 1, 8192] {
        let a = dense(&mut rng, n);
        let b = digits(&mut rng, n);
        let prep = hachi::ring::prepare_vec_two(&a, n);
        let got = hachi::ring::dot_prepared_digits(&prep, &b, n);
        let expected = hachi::ring::dot_fused(&a, &b, n);
        assert!(
            got.equals(&expected),
            "bounded prepared dot disagrees at n = {n} (chunks = {})",
            n.div_ceil(chunk)
        );
    }
}

/// The all-maximal-digit case at the full 8192 width: the single input that
/// comes closest to `p1 · p2`, and the one a margin error shows up on first.
#[test]
fn the_bounded_dot_survives_its_worst_case() {
    let mut rng = Lcg::new(0x5170_0000_0000_0017);
    let q = hachi::params::Q;
    let base = hachi::params::GADGET_BASE;
    let n = 8192;

    let mut a = Vec::with_capacity(n);
    let mut b = Vec::with_capacity(n);
    for _ in 0..n {
        let mut cs = Vec::with_capacity(RING_DEGREE);
        for _ in 0..RING_DEGREE {
            cs.push(q - 1 - (rng.next_u64() % 3));
        }
        a.push(rq_from_u64s(&cs));
        b.push(rq_from_u64s(&vec![base - 1; RING_DEGREE]));
    }

    let prep = hachi::ring::prepare_vec_two(&a, n);
    let got = hachi::ring::dot_prepared_digits(&prep, &b, n);
    let expected = hachi::ring::dot_fused(&a, &b, n);
    assert!(got.equals(&expected), "bounded dot wrong at the worst case");
}
