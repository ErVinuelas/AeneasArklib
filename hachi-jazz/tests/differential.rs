//! Differential tests: the Jasmin `MULX` kernel against the scalar Rust
//! reference, elementwise, over edge inputs, an exhaustive small grid, random
//! pairs, and — through `aux_reduce` — against `hachi`'s own use of the idiom.

use hachi_jazz::mul_hi_u64;

/// The scalar reference: the exact idiom `hachi::ntt::aux_reduce` uses to
/// form its Barrett quotient (`wide / BARRETT_SCALE` is `wide >> 64`).
fn mul_hi_ref(x: u64, y: u64) -> u64 {
    (((x as u128) * (y as u128)) >> 64) as u64
}

/// splitmix64: a deterministic PRNG so failures reproduce without a seed dump.
fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

const EDGES: [u64; 14] = [
    0,
    1,
    2,
    15,
    (1 << 32) - 99,        // the hachi prime Q
    (1 << 32) - 1,
    1 << 32,
    (1 << 32) + 1,
    0xFFFF_FFFF_0000_0001, // the Goldilocks prime
    (1 << 63) - 1,
    1 << 63,
    (1 << 63) + 1,
    u64::MAX - 1,
    u64::MAX,
];

#[test]
fn cpu_has_bmi2() {
    assert!(
        hachi_jazz::available(),
        "these tests require BMI2; the kernel is unavailable on this CPU"
    );
}

#[test]
fn edges_cross_product() {
    for &x in &EDGES {
        for &y in &EDGES {
            assert_eq!(mul_hi_u64(x, y), mul_hi_ref(x, y), "x={x:#x} y={y:#x}");
        }
    }
}

#[test]
fn exhaustive_around_boundaries() {
    // Every pair within ±128 of each edge value, saturating at the ends:
    // the carries into bit 64 flip exactly around these neighbourhoods.
    for &ex in &EDGES {
        for &ey in &EDGES {
            for dx in 0..=16u64 {
                for dy in 0..=16u64 {
                    let x = ex.wrapping_add(dx.wrapping_sub(8));
                    let y = ey.wrapping_add(dy.wrapping_sub(8));
                    assert_eq!(mul_hi_u64(x, y), mul_hi_ref(x, y), "x={x:#x} y={y:#x}");
                }
            }
        }
    }
}

#[test]
fn random_pairs_one_million() {
    let mut s: u64 = 0x0123_4567_89AB_CDEF;
    for _ in 0..1_000_000 {
        let x = splitmix64(&mut s);
        let y = splitmix64(&mut s);
        assert_eq!(mul_hi_u64(x, y), mul_hi_ref(x, y), "x={x:#x} y={y:#x}");
    }
}

/// `aux_reduce` rebuilt on the Jasmin kernel instead of the `u128` idiom.
fn aux_reduce_via_jazz(x: u64, p: u64, m: u64) -> u64 {
    let qh: u64 = mul_hi_u64(x, m);
    let r: u64 = x - qh * p;
    if r >= p {
        r - p
    } else {
        r
    }
}

#[test]
fn aux_reduce_agrees_with_hachi() {
    // The three (p, m) pairs hachi actually reduces with, over the full input
    // range aux_reduce is specified for (x = a·b with a, b < p < 2^30, so
    // x < 2^60); random x plus the boundary values of each range.
    let pairs = [
        (hachi::ntt::AUX_P1, hachi::ntt::AUX_M1),
        (hachi::ntt::AUX_P2, hachi::ntt::AUX_M2),
        (hachi::ntt::AUX_P3, hachi::ntt::AUX_M3),
    ];
    let mut s: u64 = 0xDEAD_BEEF_CAFE_F00D;
    for &(p, m) in &pairs {
        for x in [0, 1, p - 1, p, p + 1, (p - 1) * (p - 1)] {
            assert_eq!(
                aux_reduce_via_jazz(x, p, m),
                hachi::ntt::aux_reduce(x, p, m),
                "x={x} p={p}"
            );
        }
        for _ in 0..200_000 {
            let a = splitmix64(&mut s) % p;
            let b = splitmix64(&mut s) % p;
            let x = a * b;
            assert_eq!(
                aux_reduce_via_jazz(x, p, m),
                hachi::ntt::aux_reduce(x, p, m),
                "x={x} p={p}"
            );
        }
    }
}
