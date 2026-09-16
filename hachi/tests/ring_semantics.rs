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
    for (p, _, _, _, _, _) in aux_params() {
        assert!(is_prime(p), "{p} is not prime");
        assert!(p < (1u64 << 30), "{p} is not below 2^30");
        assert_eq!((p - 1) % (2 * ntt::NTT_LEN as u64), 0, "2N does not divide {p} - 1");
    }
    // Ordered, which is what `garner` skips two reductions on.
    assert!(ntt::AUX_P1 < ntt::AUX_P2 && ntt::AUX_P2 < ntt::AUX_P3);
}

/// Each Barrett magic is `⌊2^64 / p⌋`, and [`ntt::aux_reduce`] really is `% p`
/// over the whole `u64` range its proof claims -- boundaries included.
#[test]
fn barrett_reduction_is_modular_reduction() {
    for (p, m, _, _, _, _) in aux_params() {
        assert_eq!(m, ((1u128 << 64) / u128::from(p)) as u64, "barrett magic for {p}");
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
            assert_eq!(ntt::aux_mul(a, b, p, m), (u128::from(a) * u128::from(b) % u128::from(p)) as u64);
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
            ntt::garner((x % p1) as u64, (x % p2) as u64, (x % p3) as u64),
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
        let p = (pos % q) as u64;
        let m = (neg % q) as u64;
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

    let mut cases: Vec<(Rq, Rq)> = Vec::new();
    cases.push((zero.copy(), zero.copy()));
    cases.push((zero.copy(), arb.copy()));
    cases.push((one.copy(), arb.copy()));
    cases.push((arb.copy(), one.copy()));
    cases.push((x_pow(n - 1), x_pow(1)));
    cases.push((x_pow(n - 1), x_pow(n - 1)));
    cases.push((x_pow(n / 2), x_pow(n / 2)));
    cases.push((allmax.copy(), allmax.copy()));
    cases.push((alt.copy(), alt.copy()));
    cases.push((allmax.copy(), arb.copy()));
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
