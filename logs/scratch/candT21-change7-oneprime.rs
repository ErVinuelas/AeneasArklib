//! Change 7, measured at the shape that decides it: one 62-bit prime against
//! the landed two-prime bounded dot, on the real 8192-term Ajtai product.
//!
//! SCRATCH. Nothing here is extracted, frozen, or proved; it exists to answer
//! one question -- whether a single wide prime beats two narrow ones at the
//! caller level -- before any of that is paid for.
//!
//! Why one prime can work at all: the bounded dot's exact convolution
//! coefficient is at most `L · N · (q−1) · 15`, and with the offset that is
//! `1.117e18` at `L = 8192` against `p = 4.61e18` -- a 4.1x margin, so the whole
//! product is ONE chunk with no CRT and no chunk loop at all.
//!
//! Montgomery throughout, and the domain changes are free: the twist table is
//! stored as `psi^t · R²`, so `montmul(x, T[t]) = x · psi^t · R` both twists and
//! enters the domain; the untwist table is stored plain, so the same trick
//! leaves it. The op count per term is therefore exactly one prime's worth of
//! the production pipeline -- 1024 twist + 5120 forward + 1024 pointwise -- and
//! the whole question is what a 62-bit `montmul` costs against a 30-bit Barrett
//! `aux_mul`.

const N: usize = 1024;
const P: u64 = 4_611_685_941_117_976_577;
const NP: u64 = 4_611_685_941_117_976_575; // -P^-1 mod 2^64
const R2: u64 = 1_600_614_052_114_192; // R^2 mod P
const PSI: u64 = 3_117_988_034_827_192_157;
const PSIINV: u64 = 4_187_833_922_032_149_955;
const NINV: u64 = 4_607_182_341_566_103_553;
const Q: u64 = 4_294_967_197;
const BOUND_D: u64 = 70_368_742_555_648; // N * 16 * Q, a multiple of Q

#[inline(always)]
fn mont(a: u64, b: u64) -> u64 {
    let t: u128 = (a as u128) * (b as u128);
    let m: u64 = (t as u64).wrapping_mul(NP);
    let u: u128 = (t + (m as u128) * (P as u128)) >> 64;
    let r: u64 = u as u64;
    if r >= P { r - P } else { r }
}

#[inline(always)]
fn addm(a: u64, b: u64) -> u64 { let s = a + b; if s >= P { s - P } else { s } }
#[inline(always)]
fn subm(a: u64, b: u64) -> u64 { if a >= b { a - b } else { a + P - b } }

fn powm(mut b: u64, mut e: u64) -> u64 {
    let mut acc: u128 = 1; let mut base = b as u128;
    let _ = &mut b;
    while e > 0 {
        if e & 1 == 1 { acc = acc * base % (P as u128); }
        base = base * base % (P as u128); e >>= 1;
    }
    acc as u64
}

/// `[c^0, c^1, …, c^(N-1)]`, each multiplied by `scale` (plain arithmetic).
fn table(c: u64, scale: u64) -> Vec<u64> {
    let mut out = Vec::with_capacity(N);
    let mut cur: u128 = 1;
    for _ in 0..N {
        out.push(((cur * (scale as u128)) % (P as u128)) as u64);
        cur = cur * (c as u128) % (P as u128);
    }
    out
}

fn dif(src: &[u64], dst: &mut [u64], len: usize, tw: &[u64]) {
    let half = len / 2;
    let step = 2 * (N / len);
    let mut start = 0;
    while start < N {
        for j in 0..half {
            dst[start + j] = addm(src[start + j], src[start + j + half]);
        }
        let mut e = 0;
        for i in 0..half {
            let d = subm(src[start + i], src[start + i + half]);
            dst[start + half + i] = mont(d, tw[e]);
            e += step;
        }
        start += len;
    }
}

fn dit(src: &[u64], dst: &mut [u64], len: usize, tw: &[u64]) {
    let half = len / 2;
    let step = 2 * (N / len);
    let mut start = 0;
    while start < N {
        let mut e = 0;
        for j in 0..half {
            let v = mont(src[start + j + half], tw[e]);
            dst[start + j] = addm(src[start + j], v);
            e += step;
        }
        let mut e2 = 0;
        for i in 0..half {
            let v = mont(src[start + i + half], tw[e2]);
            dst[start + half + i] = subm(src[start + i], v);
            e2 += step;
        }
        start += len;
    }
}

fn forward(cur: &mut Vec<u64>, tmp: &mut Vec<u64>, tw: &[u64]) {
    let mut len = N;
    while len > 1 {
        dif(cur, tmp, len, tw);
        std::mem::swap(cur, tmp);
        len /= 2;
    }
}

fn inverse(cur: &mut Vec<u64>, tmp: &mut Vec<u64>, tw: &[u64]) {
    let mut len = 2;
    while len <= N {
        dit(cur, tmp, len, tw);
        std::mem::swap(cur, tmp);
        len *= 2;
    }
}

struct Tables { fwd: Vec<u64>, inv: Vec<u64>, twist: Vec<u64>, untwist: Vec<u64> }

fn tables() -> Tables {
    // The transform tables are powers of PSI, not of omega = psi^2: `dif`/`dit`
    // index them with `step = 2 * (n / len)`, so the squaring is in the stride.
    // Building them at omega instead double-counts it, which is a wrong answer
    // and not a wrong speed -- the oracle below is what caught it.
    let r_mod = ((1u128 << 64) % (P as u128)) as u64;
    Tables {
        fwd: table(PSI, r_mod),
        inv: table(PSIINV, r_mod),
        // psi^t * R^2: both twists and enters the Montgomery domain
        twist: table(PSI, mont(R2, r_mod)),
        // psiinv^t * ninv, plain: leaves the domain
        untwist: table(PSIINV, NINV),
    }
}

/// Every entry of `a`, forward-transformed under the one prime.
fn prepare(a: &[Vec<u64>], t: &Tables) -> Vec<u64> {
    let mut out = Vec::with_capacity(a.len() * N);
    let mut cur = vec![0u64; N];
    let mut tmp = vec![0u64; N];
    for e in a {
        for k in 0..N { cur[k] = mont(e[k], t.twist[k]); }
        forward(&mut cur, &mut tmp, &t.fwd);
        out.extend_from_slice(&cur);
    }
    out
}

/// `Σⱼ a[j]·b[j] mod q`, `a` prepared, one prime, one chunk, no CRT.
fn dot(pfwd: &[u64], b: &[Vec<u64>], t: &Tables) -> Vec<u64> {
    let n = b.len();
    let mut acc = vec![0u64; N];
    let mut cur = vec![0u64; N];
    let mut tmp = vec![0u64; N];
    for (j, e) in b.iter().enumerate() {
        for k in 0..N { cur[k] = mont(e[k], t.twist[k]); }
        forward(&mut cur, &mut tmp, &t.fwd);
        let base = j * N;
        for k in 0..N { acc[k] = addm(acc[k], mont(pfwd[base + k], cur[k])); }
    }
    inverse(&mut acc, &mut tmp, &t.inv);
    // untwist, leave the domain, add the offset once per coefficient
    let off = ((BOUND_D as u128) * (n as u128) % (P as u128)) as u64;
    let mut out = Vec::with_capacity(N);
    for k in 0..N {
        let v = mont(acc[k], t.untwist[k]);
        out.push(addm(v, off) % Q);
    }
    out
}


// ---------------------------------------------------------------------------
// The same pipeline at TWO 30-bit primes
// ---------------------------------------------------------------------------
//
// The point of this arm: the one-prime figure above is not a prime-count
// measurement on its own, because this scratch reuses its buffers and the
// landed `dot_prepared_digits` allocates a fresh `Vec` per entry per prime
// (`slice_out` and `mac_into` return new ones, `twist` allocates, `psi_table`
// is rebuilt per chunk). Running the SAME loop structure at two 30-bit primes
// separates the two effects: this arm against the landed one is the allocation
// gap, and the one-prime arm against this one is what dropping a prime is
// actually worth.

const Q1: u64 = 469_762_049;
const Q2: u64 = 998_244_353;
const M1: u64 = ((1u128 << 64) / (Q1 as u128)) as u64;
const M2: u64 = ((1u128 << 64) / (Q2 as u128)) as u64;
const PSI1: u64 = 165_447_688;
const PSI2: u64 = 584_193_783;
const DOFF1: u64 = 266_663_644;
const DOFF2: u64 = 501_623_972;
const GINV1: u64 = 554_580_198;

#[inline(always)]
fn bmul(a: u64, b: u64, p: u64, m: u64) -> u64 {
    let x = a * b;
    let qh = (((x as u128) * (m as u128)) >> 64) as u64;
    let r = x - qh * p;
    if r >= p { r - p } else { r }
}
#[inline(always)]
fn badd(a: u64, b: u64, p: u64) -> u64 { let s = a + b; if s >= p { s - p } else { s } }
#[inline(always)]
fn bsub(a: u64, b: u64, p: u64) -> u64 { if a >= b { a - b } else { a + p - b } }

fn ptable(c: u64, p: u64, m: u64) -> Vec<u64> {
    let mut out = Vec::with_capacity(N);
    let mut cur = 1u64;
    for _ in 0..N { out.push(cur); cur = bmul(cur, c, p, m); }
    out
}

fn bdif(src: &[u64], dst: &mut [u64], len: usize, tw: &[u64], p: u64, m: u64) {
    let half = len / 2; let step = 2 * (N / len); let mut start = 0;
    while start < N {
        for j in 0..half { dst[start + j] = badd(src[start + j], src[start + j + half], p); }
        let mut e = 0;
        for i in 0..half {
            let d = bsub(src[start + i], src[start + i + half], p);
            dst[start + half + i] = bmul(d, tw[e], p, m);
            e += step;
        }
        start += len;
    }
}
fn bdit(src: &[u64], dst: &mut [u64], len: usize, tw: &[u64], p: u64, m: u64) {
    let half = len / 2; let step = 2 * (N / len); let mut start = 0;
    while start < N {
        let mut e = 0;
        for j in 0..half {
            let v = bmul(src[start + j + half], tw[e], p, m);
            dst[start + j] = badd(src[start + j], v, p); e += step;
        }
        let mut e2 = 0;
        for i in 0..half {
            let v = bmul(src[start + i + half], tw[e2], p, m);
            dst[start + half + i] = bsub(src[start + i], v, p); e2 += step;
        }
        start += len;
    }
}

struct P30Tables { fwd: Vec<u64>, inv: Vec<u64>, ninv: u64, p: u64, m: u64 }

fn p30_tables(p: u64, m: u64, psi: u64) -> P30Tables {
    let fwd = ptable(psi, p, m);
    let psiinv = {
        let mut acc: u128 = 1; let mut base = psi as u128; let mut e = p - 2;
        while e > 0 { if e & 1 == 1 { acc = acc * base % (p as u128); } base = base * base % (p as u128); e >>= 1; }
        acc as u64
    };
    let ninv = {
        let mut acc: u128 = 1; let mut base = N as u128; let mut e = p - 2;
        while e > 0 { if e & 1 == 1 { acc = acc * base % (p as u128); } base = base * base % (p as u128); e >>= 1; }
        acc as u64
    };
    P30Tables { fwd, inv: ptable(psiinv, p, m), ninv, p, m }
}

fn prepare30(a: &[Vec<u64>], t: &P30Tables) -> Vec<u64> {
    let mut out = Vec::with_capacity(a.len() * N);
    let mut cur = vec![0u64; N];
    let mut tmp = vec![0u64; N];
    for e in a {
        for k in 0..N { cur[k] = bmul(e[k] % t.p, t.fwd[k], t.p, t.m); }
        let mut len = N;
        while len > 1 { bdif(&cur, &mut tmp, len, &t.fwd, t.p, t.m); std::mem::swap(&mut cur, &mut tmp); len /= 2; }
        out.extend_from_slice(&cur);
    }
    out
}

/// One prime's residue vector of ONE CHUNK of the bounded dot, buffers reused.
///
/// Chunked at 2048 exactly as the landed code is, and for the same reason: at
/// two primes the reconstruction only fits `L <= 3332`, so a single chunk of
/// 8192 overflows `p1 * p2` and returns a different integer. The first version
/// of this arm did that, and the oracle caught it -- which is the bound
/// `offConvSumD_lt_P12` states, observed rather than assumed.
fn dot30(pfwd: &[u64], b: &[Vec<u64>], start: usize, end: usize,
         t: &P30Tables, doff: u64) -> Vec<u64> {
    let n = end - start;
    let b = &b[start..end];
    let mut acc = vec![0u64; N];
    let mut cur = vec![0u64; N];
    let mut tmp = vec![0u64; N];
    for (j, e) in b.iter().enumerate() {
        for k in 0..N { cur[k] = bmul(e[k] % t.p, t.fwd[k], t.p, t.m); }
        let mut len = N;
        while len > 1 { bdif(&cur, &mut tmp, len, &t.fwd, t.p, t.m); std::mem::swap(&mut cur, &mut tmp); len /= 2; }
        let base = (start + j) * N;   // ABSOLUTE, as the prepared table is whole
        for k in 0..N { acc[k] = badd(acc[k], bmul(pfwd[base + k], cur[k], t.p, t.m), t.p); }
    }
    let mut len = 2;
    while len <= N { bdit(&acc, &mut tmp, len, &t.inv, t.p, t.m); std::mem::swap(&mut acc, &mut tmp); len *= 2; }
    let off = bmul(doff, (n % t.p as usize) as u64, t.p, t.m);
    let mut out = Vec::with_capacity(N);
    for k in 0..N {
        let v = bmul(bmul(acc[k], t.inv[k], t.p, t.m), t.ninv, t.p, t.m);
        out.push(badd(v, off, t.p));
    }
    out
}

#[inline(always)]
fn garner2(r1: u64, r2: u64) -> u64 {
    let d1 = bsub(r2, r1, Q2);
    let t1 = bmul(d1, GINV1, Q2, M2);
    r1 + Q1 * t1
}

// ---------------------------------------------------------------------------
// The same 30-bit prime, with the modulus as a CONSTANT
// ---------------------------------------------------------------------------
//
// `bmul` above takes `p` and `m` as runtime arguments, because the production
// `ntt::aux_mul` does: one function serves all three primes, which `ring.rs`
// records as a deliberate choice. `mont` in the one-prime arm cannot do that --
// there is only one prime, so `P` and `NP` are `const`. That difference is
// invisible in an op count and very visible to the optimizer, so this arm
// measures it: prime 1's dot, once with a runtime modulus and once with a
// constant one, everything else identical.

#[inline(always)]
fn cmul(a: u64, b: u64) -> u64 {
    let x = a * b;
    let qh = (((x as u128) * (M1 as u128)) >> 64) as u64;
    let r = x - qh * Q1;
    if r >= Q1 { r - Q1 } else { r }
}
#[inline(always)]
fn cadd(a: u64, b: u64) -> u64 { let s = a + b; if s >= Q1 { s - Q1 } else { s } }
#[inline(always)]
fn csub(a: u64, b: u64) -> u64 { if a >= b { a - b } else { a + Q1 - b } }

fn cdif(src: &[u64], dst: &mut [u64], len: usize, tw: &[u64]) {
    let half = len / 2; let step = 2 * (N / len); let mut start = 0;
    while start < N {
        for j in 0..half { dst[start + j] = cadd(src[start + j], src[start + j + half]); }
        let mut e = 0;
        for i in 0..half {
            let d = csub(src[start + i], src[start + i + half]);
            dst[start + half + i] = cmul(d, tw[e]);
            e += step;
        }
        start += len;
    }
}

/// Prime 1's chunk, with the modulus a constant. Value-identical to
/// `dot30(.., &t1, DOFF1)` -- only the code generation differs.
fn dot30_const(pfwd: &[u64], b: &[Vec<u64>], start: usize, end: usize, t: &P30Tables) -> Vec<u64> {
    let bs = &b[start..end];
    let mut acc = vec![0u64; N];
    let mut cur = vec![0u64; N];
    let mut tmp = vec![0u64; N];
    for (j, e) in bs.iter().enumerate() {
        for k in 0..N { cur[k] = cmul(e[k] % Q1, t.fwd[k]); }
        let mut len = N;
        while len > 1 { cdif(&cur, &mut tmp, len, &t.fwd); std::mem::swap(&mut cur, &mut tmp); len /= 2; }
        let base = (start + j) * N;
        for k in 0..N { acc[k] = cadd(acc[k], cmul(pfwd[base + k], cur[k])); }
    }
    acc
}

fn main() {
    use hachi::params::RING_DEGREE;
    let t = tables();
    let mut s: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut rnd = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };

    for &n in &[1usize, 2, 5, 8192] {
        // a: arbitrary mod q; b: unsigned gadget digits
        let aw: Vec<Vec<u64>> = (0..n).map(|_| (0..N).map(|_| rnd() % Q).collect()).collect();
        let bw: Vec<Vec<u64>> = (0..n).map(|_| (0..N).map(|_| rnd() % 16).collect()).collect();
        let arq: Vec<hachi::ring::Rq> = aw.iter().map(|v| rq(v)).collect();
        let brq: Vec<hachi::ring::Rq> = bw.iter().map(|v| rq(v)).collect();

        // the oracle: the landed fused dot
        let want = hachi::ring::dot_fused(&arq, &brq, n);
        let wantw: Vec<u64> = (0..RING_DEGREE).map(|k| want.coeff(k).to_u64()).collect();

        let p1 = prepare(&aw, &t);
        let got = dot(&p1, &bw, &t);
        assert_eq!(got, wantw, "one-prime dot disagrees at n = {n}");

        if n < 8192 { continue; }

        // and the timing, against the landed two-prime prepared dot
        let t0 = std::time::Instant::now();
        let prep2 = hachi::ring::prepare_vec_two(&arq, n);
        let tp2 = t0.elapsed().as_secs_f64();
        let t0 = std::time::Instant::now();
        let r2 = hachi::ring::dot_prepared_digits(&prep2, &brq, n);
        let td2 = t0.elapsed().as_secs_f64();
        std::hint::black_box(r2.coeff(0).to_u64());

        let t0 = std::time::Instant::now();
        let prep1 = prepare(&aw, &t);
        let tp1 = t0.elapsed().as_secs_f64();
        let t0 = std::time::Instant::now();
        let r1 = dot(&prep1, &bw, &t);
        let td1 = t0.elapsed().as_secs_f64();
        std::hint::black_box(r1[0]);

        println!("n = {n}, one term = one 1024-coefficient ring element");
        println!("  prepare   two 30-bit primes {:.3}s   one 62-bit prime {:.3}s   {:+.1}%",
            tp2, tp1, 100.0 * (tp1 / tp2 - 1.0));
        println!("  dot       two 30-bit primes {:.3}s   one 62-bit prime {:.3}s   {:+.1}%",
            td2, td1, 100.0 * (td1 / td2 - 1.0));
        println!("  table     two 30-bit primes {} MiB   one 62-bit prime {} MiB",
            n * 2 * N * 8 / (1 << 20), n * N * 8 / (1 << 20));

        // the same loop structure at two 30-bit primes, to separate the
        // allocation gap from the prime-count win
        let t1 = p30_tables(Q1, M1, PSI1);
        let t2 = p30_tables(Q2, M2, PSI2);
        let s0 = std::time::Instant::now();
        let f1 = prepare30(&aw, &t1);
        let f2 = prepare30(&aw, &t2);
        let sp = s0.elapsed().as_secs_f64();
        let s0 = std::time::Instant::now();
        let mut sd = vec![0u64; N];
        let mut st = 0usize;
        while st < n {
            let en = (st + 2048).min(n);
            let d1 = dot30(&f1, &bw, st, en, &t1, DOFF1);
            let d2 = dot30(&f2, &bw, st, en, &t2, DOFF2);
            for k in 0..N {
                sd[k] = (sd[k] + garner2(d1[k], d2[k]) % Q) % Q;
            }
            st = en;
        }
        let sdt = s0.elapsed().as_secs_f64();
        assert_eq!(sd, wantw, "scratch two-prime dot disagrees");
        println!();
        println!("  SAME loop structure, two 30-bit primes:");
        println!("    prepare {:.3}s   dot {:.3}s", sp, sdt);
        println!("  allocation gap (landed 2-prime -> scratch 2-prime): prepare {:+.1}%  dot {:+.1}%",
            100.0 * (sp / tp2 - 1.0), 100.0 * (sdt / td2 - 1.0));
        println!("  prime count    (scratch 2-prime -> scratch 1-prime): prepare {:+.1}%  dot {:+.1}%",
            100.0 * (tp1 / sp - 1.0), 100.0 * (td1 / sdt - 1.0));

        // one prime's worth of the dot, runtime modulus versus constant modulus
        let s0 = std::time::Instant::now();
        let mut hot = 0u64;
        let mut st = 0usize;
        while st < n {
            let en = (st + 2048).min(n);
            hot ^= dot30(&f1, &bw, st, en, &t1, DOFF1)[0];
            st = en;
        }
        let run_p = s0.elapsed().as_secs_f64();
        let s0 = std::time::Instant::now();
        let mut hot2 = 0u64;
        let mut st = 0usize;
        while st < n {
            let en = (st + 2048).min(n);
            hot2 ^= dot30_const(&f1, &bw, st, en, &t1)[0];
            st = en;
        }
        let con_p = s0.elapsed().as_secs_f64();
        std::hint::black_box((hot, hot2));
        println!();
        println!("  ONE 30-bit prime's dot: runtime modulus {:.3}s   const modulus {:.3}s   {:+.1}%",
            run_p, con_p, 100.0 * (con_p / run_p - 1.0));
        println!("  (so of the -{:.0}% above, the constant-modulus part is available at ANY prime count)",
            100.0 * (1.0 - td1 / sdt));
    }
}

fn rq(w: &[u64]) -> hachi::ring::Rq {
    let cs: Vec<cpoly::Fp> = w.iter().map(|&x| cpoly::Fp::new(x)).collect();
    hachi::ring::Rq::from_coeffs(&cs)
}
