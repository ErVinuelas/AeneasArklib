//! Change 7's decisive quantity, measured rather than counted.
//!
//! The one-prime route replaces two 30-bit modular multiplies by one 62-bit
//! one, so it wins only if a 62-bit modmul costs less than two 30-bit ones.
//! Counting multiplies is not enough, because the two sides of a fused dot use
//! different reducers:
//!
//! * a transform multiplies by a **fixed** twiddle, so it can precompute that
//!   twiddle's magic -- Shoup's form, two 64x64 multiplies, the same count as
//!   the 30-bit Barrett the production NTT uses;
//! * the pointwise multiply-accumulate multiplies two **runtime** values, so it
//!   needs a general reducer -- Montgomery, three 64x64 multiplies.
//!
//! Per term per prime the production pipeline is 1024 twist + 5120 forward
//! (both fixed-twiddle) + 1024 pointwise = 7168 modmuls. So the comparison that
//! decides Change 7 is
//!
//! ```text
//! 2 * (6144 * barrett30 + 1024 * barrett30)
//! versus
//! 1 * (6144 * shoup62   + 1024 * montgomery62)
//! ```
//!
//! Throughput and latency are both taken: a butterfly network's inner loop has
//! independent multiplies, but the twist and the accumulate chain do not.

const P30: u64 = 998_244_353;
const M30: u64 = ((1u128 << 64) / (P30 as u128)) as u64;

/// A 62-bit prime with `p - 1` divisible by `2^32`, so a `2·NTT_LEN`-th root of
/// unity exists with room to spare. The whole 8192-term bounded dot fits it in
/// ONE chunk: `2 · 8192 · N · 16 · q = 1.15e18 < p`.
const P62: u64 = 4_611_685_941_117_976_577;

#[inline(always)]
fn mul_barrett30(a: u64, b: u64) -> u64 {
    let x: u64 = a * b;
    let qh: u64 = (((x as u128) * (M30 as u128)) >> 64) as u64;
    let r: u64 = x - qh * P30;
    if r >= P30 { r - P30 } else { r }
}

/// Shoup: `w` fixed, `wm = floor(w * 2^64 / p)` precomputed.
#[inline(always)]
fn mul_shoup(x: u64, w: u64, wm: u64) -> u64 {
    let qh: u64 = (((x as u128) * (wm as u128)) >> 64) as u64;
    let r: u64 = x.wrapping_mul(w).wrapping_sub(qh.wrapping_mul(P62));
    if r >= P62 { r.wrapping_sub(P62) } else { r }
}

#[inline(always)]
fn shoup_magic(w: u64) -> u64 {
    (((w as u128) << 64) / (P62 as u128)) as u64
}

/// `-p^{-1} mod 2^64`, by Newton iteration on the 2-adic inverse.
const fn neg_inv(p: u64) -> u64 {
    let mut inv: u64 = 1;
    let mut i = 0;
    while i < 6 {
        inv = inv.wrapping_mul(2u64.wrapping_sub(p.wrapping_mul(inv)));
        i += 1;
    }
    inv.wrapping_neg()
}
const NP62: u64 = neg_inv(P62);

/// Montgomery: the general reducer, for a product of two runtime values.
/// Returns `a * b * 2^-64 mod p`, which is what a Montgomery-domain pipeline
/// wants throughout.
#[inline(always)]
fn mul_mont(a: u64, b: u64) -> u64 {
    let t: u128 = (a as u128) * (b as u128);
    let m: u64 = (t as u64).wrapping_mul(NP62);
    let u: u128 = (t + (m as u128) * (P62 as u128)) >> 64;
    let r: u64 = u as u64;
    if r >= P62 { r - P62 } else { r }
}

fn xs(n: usize) -> Vec<u64> {
    let mut v = Vec::with_capacity(n);
    let mut s: u64 = 0x243F_6A88_85A3_08D3;
    for _ in 0..n {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        v.push(s);
    }
    v
}

#[inline(always)]
fn add_mod(a: u64, b: u64, p: u64) -> u64 {
    let s = a + b;
    if s >= p { s - p } else { s }
}

/// One twiddle per position, as a transform has: the multiplier is a table
/// entry, the multiplicand is data, and the accumulator carries the loop
/// dependency through a modular add. This is the shape being measured, and it
/// matters: with the accumulator out of the chain the compiler deletes the loop
/// entirely, which is how the first version of this program reported a 62-bit
/// Shoup multiply as free.
const TW: usize = 64;

fn main() {
    let n: usize = 1 << 24;
    let src = xs(n);

    // correctness first: a wrong kernel measures nothing.
    for &x in src.iter().take(20000) {
        let (u, v) = (x % P30, (x >> 7) % P30);
        assert_eq!(mul_barrett30(u, v),
            (((u as u128) * (v as u128)) % (P30 as u128)) as u64, "barrett30");
        let (u, v) = (x % P62, (x >> 7) % P62);
        assert_eq!(mul_shoup(u, v, shoup_magic(v)),
            (((u as u128) * (v as u128)) % (P62 as u128)) as u64, "shoup62");
        let want_mont = {
            let m = (((u as u128) * (v as u128)) % (P62 as u128)) as u64;
            let r64 = ((1u128 << 64) % (P62 as u128)) as u64;
            let mut e = P62 - 2; let mut base = r64 as u128; let mut acc: u128 = 1;
            while e > 0 {
                if e & 1 == 1 { acc = acc * base % (P62 as u128); }
                base = base * base % (P62 as u128); e >>= 1;
            }
            ((m as u128) * acc % (P62 as u128)) as u64
        };
        assert_eq!(mul_mont(u, v), want_mont, "montgomery62");
    }

    // twiddle tables, with Shoup's precomputed magics
    let tw30: Vec<u64> = (0..TW).map(|j| src[j * 37 + 1] % P30).collect();
    let tw62: Vec<u64> = (0..TW).map(|j| src[j * 37 + 1] % P62).collect();
    let tw62m: Vec<u64> = tw62.iter().map(|&w| shoup_magic(w)).collect();

    // data, reduced once so the loops measure the multiply and not a remainder
    let d30: Vec<u64> = src.iter().map(|&x| x % P30).collect();
    let d62: Vec<u64> = src.iter().map(|&x| x % P62).collect();

    let t = std::time::Instant::now();
    let mut a: u64 = 1;
    for (j, &x) in d30.iter().enumerate() {
        a = add_mod(a, mul_barrett30(x, tw30[j % TW]), P30);
    }
    let e30 = t.elapsed().as_secs_f64();
    std::hint::black_box(a);

    let t = std::time::Instant::now();
    let mut a: u64 = 1;
    for (j, &x) in d62.iter().enumerate() {
        a = add_mod(a, mul_shoup(x, tw62[j % TW], tw62m[j % TW]), P62);
    }
    let esh = t.elapsed().as_secs_f64();
    std::hint::black_box(a);

    let t = std::time::Instant::now();
    let mut a: u64 = 1;
    for (j, &x) in d62.iter().enumerate() {
        a = add_mod(a, mul_mont(x, tw62[j % TW]), P62);
    }
    let emo = t.elapsed().as_secs_f64();
    std::hint::black_box(a);

    // and the pointwise MAC: both operands are data, so no magic can be stored
    let t = std::time::Instant::now();
    let mut a: u64 = 1;
    for w in d30.chunks_exact(2) {
        a = add_mod(a, mul_barrett30(w[0], w[1]), P30);
    }
    let g30 = t.elapsed().as_secs_f64() * 2.0;
    std::hint::black_box(a);

    let t = std::time::Instant::now();
    let mut a: u64 = 1;
    for w in d62.chunks_exact(2) {
        a = add_mod(a, mul_mont(w[0], w[1]), P62);
    }
    let g62 = t.elapsed().as_secs_f64() * 2.0;
    std::hint::black_box(a);

    println!("{} multiply-accumulates each:", n);
    println!("  fixed twiddle   barrett30 {:.4}s   shoup62 {:.4}s ({:.2}x)   mont62 {:.4}s ({:.2}x)",
        e30, esh, esh / e30, emo, emo / e30);
    println!("  both from data  barrett30 {:.4}s   mont62  {:.4}s ({:.2}x)",
        g30, g62, g62 / g30);
    println!();
    // per term per prime: 6144 fixed-twiddle multiplies, 1024 pointwise
    let two_prime = 2.0 * (6144.0 * e30 + 1024.0 * g30);
    let one_shoup = 6144.0 * esh + 1024.0 * g62;
    let one_mont  = 6144.0 * emo + 1024.0 * g62;
    println!("per-term cost model (6144 fixed-twiddle + 1024 pointwise per prime):");
    println!("  two 30-bit primes            {:.3}", two_prime);
    println!("  one 62-bit prime, Shoup      {:.3}   {:+.1}%",
        one_shoup, 100.0 * (one_shoup / two_prime - 1.0));
    println!("  one 62-bit prime, Montgomery {:.3}   {:+.1}%",
        one_mont, 100.0 * (one_mont / two_prime - 1.0));
    println!();
    println!("p62 = {P62}");
}
