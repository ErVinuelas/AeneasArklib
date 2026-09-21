//! The auxiliary-prime negacyclic number-theoretic transform behind
//! [`crate::ring::Rq::mul`].
//!
//! # Why an auxiliary prime at all
//!
//! A radix-2 negacyclic transform of length `N` over `Z_q` needs a primitive
//! `2N`-th root of unity in `Z_q`, i.e. `2N | q - 1`. Hachi's modulus does not
//! have one: `q - 1 = 2^32 - 100 = 2² · 1073741799`, so `v₂(q - 1) = 2` and the
//! largest power-of-two root of unity in `Z_q` has order **4** -- and
//! `v₂(q⁴ - 1) = 4`, so `cpoly`'s quartic extension does not rescue it either
//! (NOTES.md § "The parameters forbid a radix-2 NTT"). `q` is not ours to
//! change: it is `cpoly`'s Hachi prime, fixed by the dependency.
//!
//! So the transform does not happen in `Z_q`. The negacyclic product is
//! computed as an *integer* polynomial product -- which is what it is, before
//! any reduction -- in three auxiliary NTT-friendly prime fields, and the exact
//! integer coefficients are recovered by CRT. Only then is anything reduced mod
//! `q`. The construction needs nothing of `q` beyond a bound.
//!
//! # The bound, the offset, and why the offset is `N · q²`
//!
//! Both inputs have `N = 1024` coefficients, each a canonical representative
//! below `q`. Coefficient `k` of their negacyclic product is, as an *integer*,
//!
//! ```text
//! v_k = posSum − negSum,   0 ≤ posSum, negSum ≤ N · q²
//! ```
//!
//! where `posSum`/`negSum` are the two antidiagonal sums `Ring.lean` already
//! defines and already bounds by `N · q²` (`posSum_le`, `negSum_le`). So `v_k`
//! is *signed*, and CRT reconstructs a residue class, not a signed integer.
//!
//! The fix is an offset. This module reconstructs
//!
//! ```text
//! W_k = posSum + BOUND − negSum,   BOUND = N · q² = 18 889 465 060 665 381 692 416
//! ```
//!
//! which is a **natural number** in `[0, 2·BOUND]` -- no sign, no branch on the
//! coefficient's sign, nothing data-dependent. And
//!
//! ```text
//! 2 · BOUND = 37 778 930 121 330 763 384 832  ≈ 2^74.9
//! P = p1·p2·p3 = 471 064 322 751 194 440 790 966 273  ≈ 2^88.6
//! ```
//!
//! so `2·BOUND < P` with a factor of about `1.25 · 10^4` to spare and the
//! reconstruction is *exact*.
//!
//! `BOUND` is `N · q²` rather than the tighter `N · (q−1)²` for two reasons,
//! both about the proof: it is the ceiling the existing `posSum_le`/`negSum_le`
//! lemmas already establish, so no sharper bound has to be proved; and it is
//! **divisible by `q`**, so `W_k ≡ v_k (mod q)` and the caller needs no
//! correction term at all -- coefficient `k` of the product is just
//! `Fp::new(W_k mod q)`.
//!
//! # The primes, the roots, and what is checked about them
//!
//! ```text
//! p1 = 469762049   = 7 · 2^26 + 1        ψ1 = 165447688
//! p2 = 998244353   = 7 · 17 · 2^23 + 1   ψ2 = 584193783
//! p3 = 1004535809  = 479 · 2^21 + 1      ψ3 = 714163887
//! ```
//!
//! Each `pi` is prime, each is `< 2^30` (so a product of two residues is
//! `< 2^60` and fits a `u64`), and `2N = 2048 | pi − 1`, which is what makes a
//! negacyclic transform of length `N` exist. Each `ψi` has **exact order 2048**:
//! `ψi^1024 = pi − 1 = −1`, which for a prime modulus is equivalent to exact
//! order `2048`, and is the form the Lean side checks by `decide`. The
//! order-`N` root the transform itself runs on is `ωi = ψi²`, so it needs no
//! constant of its own -- `ωi^e = ψi^(2e)`, which is why every twiddle index
//! below steps by `2 · (N / len)`.
//!
//! They are ordered `p1 < p2 < p3`, which is what lets [`garner`] skip two
//! reductions it would otherwise need.
//!
//! `tests/ring_semantics.rs` re-derives every constant here from its defining
//! property rather than trusting the literal.
//!
//! # The pipeline
//!
//! Multiplication mod `X^N + 1` is turned into multiplication mod `X^N − 1` by
//! a twist. Substituting `X ↦ ψ·Y` is a ring isomorphism
//! `Z_p[X]/(X^N + 1) → Z_p[Y]/(Y^N − 1)`, because `(ψY)^N = ψ^N Y^N = −Y^N`;
//! on coefficients it is `a_t ↦ a_t · ψ^t`. So, per prime:
//!
//! ```text
//! twist      a_t ↦ (a_t mod p) · ψ^t                       (both operands)
//! forward    log N decimation-in-frequency stages, root ω = ψ²
//! pointwise  Â_i · B̂_i
//! inverse    log N decimation-in-time stages, root ω⁻¹
//! untwist    c_t ↦ c_t · ψ^(−t) · N⁻¹,  then  + (BOUND mod p)
//! ```
//!
//! and then [`garner`] reconstructs `W_k` from the three residues.
//!
//! A cyclic transform of length `2N` with zero padding is the other standard
//! route and was measured first: it needs no twist and no signed-coefficient
//! argument, but it is **2.2× more transform work** and its buffers are twice
//! the size. On this machine it came out *slower* than the schoolbook
//! convolution it was meant to replace; the negacyclic form at length `N` is
//! what clears the gate. See `logs/ntt-execution.md`, gate "performance".
//!
//! # Shape, and why it is this shape
//!
//! **Ping-pong, not in-place.** Each stage reads one whole buffer and writes
//! another, and the two are swapped between stages. That is a proof-driven
//! choice: a stage is then a *function* of its input buffer, with the loop
//! invariant "every output index written so far holds what the stage function
//! says", which is the shape every other operation in this crate is already
//! proved in. A genuinely in-place butterfly loop would need an invariant that
//! splits one array into a rewritten part and an untouched part *inside* a group
//! structure, and the same array would appear on both sides of it.
//!
//! **Two sequential inner loops per block, not one fused butterfly.** The
//! natural butterfly writes `dst[start+j]` and `dst[start+half+j]` in the same
//! iteration, which does strictly less work: one twiddle multiplication instead
//! of two in [`dit_stage`], and half the loads. It was implemented and
//! measured, and it is **17 % slower** (338 µs against 288 µs for a product,
//! single-implementation binaries, three runs each): the split form writes
//! `dst` in one strictly increasing stream, and the store-side locality of that
//! is worth more than the arithmetic it wastes. So the loops are split, and
//! [`dit_stage`] pays for the twiddle multiplication twice on purpose.
//!
//! **Tables are built, not pinned.** `psi_table` costs `N` multiplications per
//! direction per prime -- about 6 % of a product -- and in exchange the
//! correctness rule is one line (`out[i] = ψ^i`) with no hand-written table to
//! audit.
//!
//! # Security scope
//!
//! This module is proved *functionally* correct. Nothing here claims
//! constant-time execution: [`aux_add`], [`aux_sub`] and [`aux_reduce`] each end
//! in a conditional subtraction, which a compiler may or may not turn into a
//! branchless select. Every loop bound and every index is a public constant, and
//! the offset above is what keeps the reconstruction free of any branch on a
//! coefficient's value -- but that is an argument about this source, not a
//! conclusion of the Lean proof.

use alloc::vec::Vec;

use crate::params;

// @genesis 5dd855a 2026-09-16 — ntt::NTT_LEN
/// The transform length, `N = 2^α`: the same `1024` as
/// [`params::RING_DEGREE`], because the transform is negacyclic and so runs at
/// the ring degree itself rather than at twice it.
///
/// A literal for the same reason [`params::RING_DEGREE`] is one: Aeneas models a
/// shift as fallible, and a derived form would extract as a `Result` every use
/// would have to discharge. `params_semantics` keeps the two in step.
pub const NTT_LEN: usize = 1024;

// @genesis 5dd855a 2026-09-16 — ntt::NTT_LOG
/// The number of transform stages, `log2(NTT_LEN)`. The loops count on `len`
/// rather than reading this; it is here because the Lean stage induction is
/// stated over it.
pub const NTT_LOG: usize = 10;

// @genesis 5dd855a 2026-09-16 — ntt::BARRETT_SCALE
/// `2^64`, the Barrett scale.
///
/// A literal rather than `1u128 << 64`, because Aeneas models a shift as
/// fallible. As a literal, the division in [`aux_reduce`] is a `u128` division
/// by a constant power of two, which is taking the high word.
const BARRETT_SCALE: u128 = 18_446_744_073_709_551_616;

// @genesis 5dd855a 2026-09-16 — ntt::AUX_P1
/// The first auxiliary prime, `7 · 2^26 + 1`.
pub const AUX_P1: u64 = 469_762_049;
// @genesis 5dd855a 2026-09-16 — ntt::AUX_M1
/// Barrett magic for [`AUX_P1`]: `⌊2^64 / p1⌋`.
pub const AUX_M1: u64 = 39_268_272_336;
// @genesis 5dd855a 2026-09-16 — ntt::AUX_PSI1
/// A root of exact order `2 · NTT_LEN` mod [`AUX_P1`] (`3^((p1−1)/2048)`).
pub const AUX_PSI1: u64 = 165_447_688;
// @genesis 5dd855a 2026-09-16 — ntt::AUX_PSIINV1
/// The inverse of [`AUX_PSI1`] mod [`AUX_P1`].
pub const AUX_PSIINV1: u64 = 63_413_564;
// @genesis 5dd855a 2026-09-16 — ntt::AUX_NINV1
/// The inverse of [`NTT_LEN`] mod [`AUX_P1`].
pub const AUX_NINV1: u64 = 469_303_297;
// @genesis 5dd855a 2026-09-16 — ntt::AUX_BOFF1
/// `BOUND mod p1`, the offset that makes the reconstructed value a natural
/// number. See the module header.
pub const AUX_BOFF1: u64 = 261_237_050;

// @genesis 5dd855a 2026-09-16 — ntt::AUX_P2
/// The second auxiliary prime, `7 · 17 · 2^23 + 1`.
pub const AUX_P2: u64 = 998_244_353;
// @genesis 5dd855a 2026-09-16 — ntt::AUX_M2
/// Barrett magic for [`AUX_P2`]: `⌊2^64 / p2⌋`.
pub const AUX_M2: u64 = 18_479_187_002;
// @genesis 5dd855a 2026-09-16 — ntt::AUX_PSI2
/// A root of exact order `2 · NTT_LEN` mod [`AUX_P2`] (`3^((p2−1)/2048)`).
pub const AUX_PSI2: u64 = 584_193_783;
// @genesis 5dd855a 2026-09-16 — ntt::AUX_PSIINV2
/// The inverse of [`AUX_PSI2`] mod [`AUX_P2`].
pub const AUX_PSIINV2: u64 = 335_559_352;
// @genesis 5dd855a 2026-09-16 — ntt::AUX_NINV2
/// The inverse of [`NTT_LEN`] mod [`AUX_P2`].
pub const AUX_NINV2: u64 = 997_269_505;
// @genesis 5dd855a 2026-09-16 — ntt::AUX_BOFF2
/// `BOUND mod p2`.
pub const AUX_BOFF2: u64 = 370_509_789;

// @genesis 5dd855a 2026-09-16 — ntt::AUX_P3
/// The third auxiliary prime, `479 · 2^21 + 1`.
pub const AUX_P3: u64 = 1_004_535_809;
// @genesis 5dd855a 2026-09-16 — ntt::AUX_M3
/// Barrett magic for [`AUX_P3`]: `⌊2^64 / p3⌋`.
pub const AUX_M3: u64 = 18_363_450_967;
// @genesis 5dd855a 2026-09-16 — ntt::AUX_PSI3
/// A root of exact order `2 · NTT_LEN` mod [`AUX_P3`] (`3^((p3−1)/2048)`).
pub const AUX_PSI3: u64 = 714_163_887;
// @genesis 5dd855a 2026-09-16 — ntt::AUX_PSIINV3
/// The inverse of [`AUX_PSI3`] mod [`AUX_P3`].
pub const AUX_PSIINV3: u64 = 278_605_116;
// @genesis 5dd855a 2026-09-16 — ntt::AUX_NINV3
/// The inverse of [`NTT_LEN`] mod [`AUX_P3`].
pub const AUX_NINV3: u64 = 1_003_554_817;
// @genesis 5dd855a 2026-09-16 — ntt::AUX_BOFF3
/// `BOUND mod p3`.
pub const AUX_BOFF3: u64 = 695_009_305;

// @genesis 5dd855a 2026-09-16 — ntt::GARNER_P12
/// `p1 · p2`, the second Garner radix. `< 2^59`, so it is a `u64`.
pub const GARNER_P12: u64 = 468_937_312_667_959_297;
// @genesis 5dd855a 2026-09-16 — ntt::GARNER_INV1
/// `p1⁻¹ mod p2`.
pub const GARNER_INV1: u64 = 554_580_198;
// @genesis 5dd855a 2026-09-16 — ntt::GARNER_INV12
/// `(p1 · p2)⁻¹ mod p3`.
pub const GARNER_INV12: u64 = 395_249_030;

// @genesis 5dd855a 2026-09-16 — ntt::aux_reduce
/// Barrett reduction: `x mod p`, for any `x < 2^64` and `p < 2^32` with
/// `m = ⌊2^64 / p⌋`.
///
/// Why not `x % p`: `p` is a *runtime* value here -- one function serves all
/// three primes -- so `%` would be a hardware 64-bit division, tens of cycles,
/// on the hot path of every butterfly. Barrett is a multiply-high, a multiply, a
/// subtraction and one conditional subtraction.
///
/// **Why one conditional subtraction is enough.** Write `2^64 = m·p + s` with
/// `0 ≤ s < p`, and let `qh = ⌊x·m / 2^64⌋`. Then
///
/// ```text
/// x·m / 2^64 = x/p − x·s/(p·2^64)   and   x·s/(p·2^64) < x/2^64 < 1,
/// ```
///
/// so `x/p − 1 < x·m/2^64 ≤ x/p`, giving `qh ∈ {⌊x/p⌋ − 1, ⌊x/p⌋}` and
/// `r = x − qh·p ∈ [0, 2p)`. In particular `qh·p ≤ x`, so the subtraction does
/// not underflow; `qh ≤ x/p` and `p < 2^32` keep `qh·p < 2^64`; and
/// `x·m < 2^64 · 2^36` fits the `u128`.
#[allow(clippy::cast_possible_truncation)]
pub fn aux_reduce(x: u64, p: u64, m: u64) -> u64 {
    let wide: u128 = (x as u128) * (m as u128);
    let qh: u64 = (wide / BARRETT_SCALE) as u64;
    let r: u64 = x - qh * p;
    if r >= p {
        r - p
    } else {
        r
    }
}

// @genesis 5dd855a 2026-09-16 — ntt::aux_add
/// `a + b mod p`, for `a, b < p < 2^30`.
pub fn aux_add(a: u64, b: u64, p: u64) -> u64 {
    let s: u64 = a + b;
    if s >= p {
        s - p
    } else {
        s
    }
}

// @genesis 5dd855a 2026-09-16 — ntt::aux_sub
/// `a − b mod p`, for `a, b < p < 2^30`.
pub fn aux_sub(a: u64, b: u64, p: u64) -> u64 {
    if a >= b {
        a - b
    } else {
        a + p - b
    }
}

// @genesis 5dd855a 2026-09-16 — ntt::aux_mul
/// `a · b mod p`, for `a, b < p < 2^30`: the product is `< 2^60`, so it fits a
/// `u64` and [`aux_reduce`] applies to it.
pub fn aux_mul(a: u64, b: u64, p: u64, m: u64) -> u64 {
    aux_reduce(a * b, p, m)
}

// @genesis 5dd855a 2026-09-16 — ntt::zeros
/// A zero buffer of length `n`, as a push loop: the scratch half of the
/// ping-pong pair.
///
/// Its contents are irrelevant -- every entry is overwritten by the first stage
/// that writes into it -- so nothing downstream depends on the value `0`; it is
/// the shortest way to get a `Vec` of the right length that Aeneas models.
pub fn zeros(n: usize) -> Vec<u64> {
    let mut out: Vec<u64> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        out.push(0);
        i += 1;
    }
    out
}

// @genesis 5dd855a 2026-09-16 — ntt::psi_table
/// The powers `ψ^0, ψ^1, …, ψ^(NTT_LEN − 1)` mod `p`.
///
/// One table serves two purposes: the twist reads `ψ^t` at every `t`, and the
/// transform stages read `ω^e = ψ^(2e)`, i.e. the even entries. The largest
/// index any stage asks for is `(half − 1) · 2 · (N/len) = N − 2·(N/len) < N`,
/// so `NTT_LEN` entries are exactly enough.
pub fn psi_table(psi: u64, p: u64, m: u64) -> Vec<u64> {
    let n: usize = NTT_LEN;
    let mut out: Vec<u64> = Vec::with_capacity(n);
    let mut cur: u64 = 1;
    let mut i: usize = 0;
    while i < n {
        out.push(cur);
        cur = aux_mul(cur, psi, p, m);
        i += 1;
    }
    out
}

// @genesis 5dd855a 2026-09-16 — ntt::twist
/// The twist: `out[t] = (v[t] mod p) · ψ^t mod p`.
///
/// `v`'s entries are canonical representatives below `q < 2^32`, which is why
/// the [`aux_reduce`] is needed at all and why it is in range.
pub fn twist(v: &Vec<u64>, pt: &Vec<u64>, p: u64, m: u64) -> Vec<u64> {
    let n: usize = NTT_LEN;
    let mut out: Vec<u64> = Vec::with_capacity(n);
    let mut t: usize = 0;
    while t < n {
        out.push(aux_mul(aux_reduce(v[t], p, m), pt[t], p, m));
        t += 1;
    }
    out
}

// @genesis 5dd855a 2026-09-16 — ntt::dif_stage
/// One decimation-in-frequency stage at block length `len`, written into `dst`.
///
/// With `half = len / 2` and `step = 2 · (N / len)`, for every block start
/// `start ∈ {0, len, 2·len, …}` and every `j < half`:
///
/// ```text
/// dst[start + j]        = src[start + j] + src[start + j + half]
/// dst[start + half + j] = (src[start + j] − src[start + j + half]) · tw[j·step]
/// ```
///
/// which is the butterfly `(u, v) ↦ (u + v, (u − v)·ω^j)` with `ω^j = ψ^(2j)`
/// read out of the `ψ` table. Algebraically the stage is the pair of ring maps
/// `Z_p[X]/(X^len − 1) → Z_p[X]/(X^half − 1)` given by reducing mod
/// `X^half ∓ 1` and, in the minus case, substituting `X ↦ ω^(N/len) · X`.
///
/// `dst` is written in one strictly increasing stream -- that is why the two
/// halves are two loops and not one; see the module header.
pub fn dif_stage(src: &Vec<u64>, mut dst: Vec<u64>, len: usize, tw: &Vec<u64>, p: u64, m: u64) -> Vec<u64> {
    let n: usize = NTT_LEN;
    let half: usize = len / 2;
    let step: usize = 2 * (n / len);
    let mut start: usize = 0;
    while start < n {
        let mut j: usize = 0;
        while j < half {
            dst[start + j] = aux_add(src[start + j], src[start + j + half], p);
            j += 1;
        }
        let mut i: usize = 0;
        let mut e: usize = 0;
        while i < half {
            let d: u64 = aux_sub(src[start + i], src[start + i + half], p);
            dst[start + half + i] = aux_mul(d, tw[e], p, m);
            i += 1;
            e += step;
        }
        start += len;
    }
    dst
}

// @genesis 5dd855a 2026-09-16 — ntt::dit_stage
/// One decimation-in-time stage at block length `len`: the inverse of
/// [`dif_stage`] at the same `len`, given the inverse root's table.
///
/// ```text
/// dst[start + j]        = src[start + j] + src[start + j + half] · tw[j·step]
/// dst[start + half + j] = src[start + j] − src[start + j + half] · tw[j·step]
/// ```
///
/// Composing the two at the same `len` doubles: with `A = u + v` and
/// `B = (u − v)·ω^e`, this stage returns `A + B·ω^(−e) = 2u` and
/// `A − B·ω^(−e) = 2v`. That identity, applied once per stage from the innermost
/// out, is the whole inverse-transform argument -- no orthogonality sum is
/// needed, and the accumulated factor `2^(log N) = N` is what `N⁻¹` in
/// [`untwist`] cancels.
///
/// The twiddle product is computed twice, once in each loop, and that is
/// deliberate: see the module header on why `dst` is written sequentially.
pub fn dit_stage(src: &Vec<u64>, mut dst: Vec<u64>, len: usize, tw: &Vec<u64>, p: u64, m: u64) -> Vec<u64> {
    let n: usize = NTT_LEN;
    let half: usize = len / 2;
    let step: usize = 2 * (n / len);
    let mut start: usize = 0;
    while start < n {
        let mut j: usize = 0;
        let mut e: usize = 0;
        while j < half {
            let v: u64 = aux_mul(src[start + j + half], tw[e], p, m);
            dst[start + j] = aux_add(src[start + j], v, p);
            j += 1;
            e += step;
        }
        let mut i: usize = 0;
        let mut e2: usize = 0;
        while i < half {
            let v: u64 = aux_mul(src[start + i + half], tw[e2], p, m);
            dst[start + half + i] = aux_sub(src[start + i], v, p);
            i += 1;
            e2 += step;
        }
        start += len;
    }
    dst
}

// @genesis 5dd855a 2026-09-16 — ntt::ntt_forward
/// The forward transform: [`dif_stage`] at `len = N, N/2, …, 2`, ping-ponging
/// between the two buffers.
///
/// Both buffers are handed back, the first holding the result: the caller owns
/// the scratch and reuses it for the next transform, so a whole product
/// allocates a handful of buffers rather than one per stage.
///
/// Input in natural order, output in bit-reversed order -- which costs nothing,
/// because the only thing done to it is a pointwise product with another output
/// of the same transform.
pub fn ntt_forward(cur0: Vec<u64>, tmp0: Vec<u64>, tw: &Vec<u64>, p: u64, m: u64) -> (Vec<u64>, Vec<u64>) {
    let mut cur: Vec<u64> = cur0;
    let mut tmp: Vec<u64> = tmp0;
    let mut len: usize = NTT_LEN;
    while len > 1 {
        let filled: Vec<u64> = dif_stage(&cur, tmp, len, tw, p, m);
        tmp = cur;
        cur = filled;
        len = len / 2;
    }
    (cur, tmp)
}

// @genesis 5dd855a 2026-09-16 — ntt::ntt_inverse
/// The inverse transform up to the factor `N`: [`dit_stage`] at
/// `len = 2, 4, …, N`. The `N⁻¹` is applied by [`untwist`], where it is one
/// multiplication on a pass that happens anyway.
///
/// Input in bit-reversed order, output in natural order.
pub fn ntt_inverse(cur0: Vec<u64>, tmp0: Vec<u64>, tw: &Vec<u64>, p: u64, m: u64) -> (Vec<u64>, Vec<u64>) {
    let mut cur: Vec<u64> = cur0;
    let mut tmp: Vec<u64> = tmp0;
    let mut len: usize = 2;
    while len <= NTT_LEN {
        let filled: Vec<u64> = dit_stage(&cur, tmp, len, tw, p, m);
        tmp = cur;
        cur = filled;
        len = len * 2;
    }
    (cur, tmp)
}

// @genesis 5dd855a 2026-09-16 — ntt::pointwise
/// Coefficientwise product mod `p`, in place in `a`.
pub fn pointwise(mut a: Vec<u64>, b: &Vec<u64>, p: u64, m: u64) -> Vec<u64> {
    let n: usize = NTT_LEN;
    let mut i: usize = 0;
    while i < n {
        a[i] = aux_mul(a[i], b[i], p, m);
        i += 1;
    }
    a
}

// @genesis 5dd855a 2026-09-16 — ntt::untwist
/// The untwist, the `N⁻¹` normalisation and the offset, in one pass:
///
/// ```text
/// out[t] = src[t] · ψ^(−t) · N⁻¹ + (BOUND mod p)   (mod p)
/// ```
///
/// After it, `out[t]` is `W_t mod p` for the `W_t` of the module header -- a
/// residue of a *natural* number, which is what makes [`garner`] exact.
pub fn untwist(src: &Vec<u64>, it: &Vec<u64>, ninv: u64, boff: u64, p: u64, m: u64) -> Vec<u64> {
    let n: usize = NTT_LEN;
    let mut out: Vec<u64> = Vec::with_capacity(n);
    let mut t: usize = 0;
    while t < n {
        let u: u64 = aux_mul(src[t], it[t], p, m);
        let s: u64 = aux_mul(u, ninv, p, m);
        out.push(aux_add(s, boff, p));
        t += 1;
    }
    out
}

// @genesis 5dd855a 2026-09-16 — ntt::negconv_mod_p
/// `W_k mod p` for every `k < NTT_LEN`: the whole pipeline at one prime.
#[allow(clippy::too_many_arguments)]
pub fn negconv_mod_p(
    a: &Vec<u64>,
    b: &Vec<u64>,
    p: u64,
    m: u64,
    psi: u64,
    psiinv: u64,
    ninv: u64,
    boff: u64,
) -> Vec<u64> {
    let pt: Vec<u64> = psi_table(psi, p, m);
    let it: Vec<u64> = psi_table(psiinv, p, m);
    let scratch: Vec<u64> = zeros(NTT_LEN);
    let ta: Vec<u64> = twist(a, &pt, p, m);
    let fwa: (Vec<u64>, Vec<u64>) = ntt_forward(ta, scratch, &pt, p, m);
    let tb: Vec<u64> = twist(b, &pt, p, m);
    let fwb: (Vec<u64>, Vec<u64>) = ntt_forward(tb, fwa.1, &pt, p, m);
    let prod: Vec<u64> = pointwise(fwa.0, &fwb.0, p, m);
    let inv: (Vec<u64>, Vec<u64>) = ntt_inverse(prod, fwb.1, &it, p, m);
    untwist(&inv.0, &it, ninv, boff, p, m)
}

// @genesis 5dd855a 2026-09-16 — ntt::garner
/// Garner reconstruction from the three residues: the unique `x < P` with
/// `x ≡ r1 (p1)`, `x ≡ r2 (p2)`, `x ≡ r3 (p3)`.
///
/// ```text
/// t1 = (r2 − r1) · p1⁻¹                 mod p2
/// t2 = (r3 − r1 − p1·t1) · (p1·p2)⁻¹    mod p3
/// x  = r1 + p1·t1 + (p1·p2)·t2
/// ```
///
/// **Every intermediate, and why each fits.** `p1 < p2 < p3`, so `r1 < p1 < p2`
/// needs no reduction to enter the mod-`p2` step and `r1 < p1 < p3` none to
/// enter the mod-`p3` one. `t1 < p2 < p3`, so `p1·t1 < 2^59` is both a valid
/// `u64` product and a valid [`aux_mul`] operand pair mod `p3`. The result is
/// `< P < 2^89`, so the `u128` has 39 bits spare, and `(p1·p2)·t2 < P` is the
/// widest term.
///
/// Staged rather than the one-shot `Σ rᵢ·(P/pᵢ)·((P/pᵢ)⁻¹ mod pᵢ)`: that form
/// needs a `u128 × u128` product and a `u128` reduction mod `P`, neither of
/// which has a cheap no-overflow argument, while Garner never multiplies
/// anything wider than `u64 × u64`.
pub fn garner(r1: u64, r2: u64, r3: u64) -> u128 {
    let d1: u64 = aux_sub(r2, r1, AUX_P2);
    let t1: u64 = aux_mul(d1, GARNER_INV1, AUX_P2, AUX_M2);
    let partial: u64 = aux_add(r1, aux_mul(AUX_P1, t1, AUX_P3, AUX_M3), AUX_P3);
    let d2: u64 = aux_sub(r3, partial, AUX_P3);
    let t2: u64 = aux_mul(d2, GARNER_INV12, AUX_P3, AUX_M3);
    (r1 as u128) + (AUX_P1 as u128) * (t1 as u128) + (GARNER_P12 as u128) * (t2 as u128)
}

// @genesis 5dd855a 2026-09-16 — ntt::negconv_mod_q
/// Coefficient `k` of the negacyclic product, reduced mod `q`, for every
/// `k < RING_DEGREE`.
///
/// This is the whole pipeline, and the only entry point
/// [`crate::ring::Rq::mul`] uses. What comes back is `W_k mod q`, and because
/// `BOUND = N·q²` is divisible by `q` that **is** the product's coefficient --
/// the offset that makes the CRT exact is invisible mod `q`, so the caller has
/// no correction to apply.
#[allow(clippy::cast_possible_truncation)]
pub fn negconv_mod_q(a: &Vec<u64>, b: &Vec<u64>) -> Vec<u64> {
    let r1: Vec<u64> = negconv_mod_p(a, b, AUX_P1, AUX_M1, AUX_PSI1, AUX_PSIINV1, AUX_NINV1, AUX_BOFF1);
    let r2: Vec<u64> = negconv_mod_p(a, b, AUX_P2, AUX_M2, AUX_PSI2, AUX_PSIINV2, AUX_NINV2, AUX_BOFF2);
    let r3: Vec<u64> = negconv_mod_p(a, b, AUX_P3, AUX_M3, AUX_PSI3, AUX_PSIINV3, AUX_NINV3, AUX_BOFF3);
    let qw: u128 = params::Q as u128;
    let n: usize = NTT_LEN;
    let mut out: Vec<u64> = Vec::with_capacity(n);
    let mut t: usize = 0;
    while t < n {
        out.push((garner(r1[t], r2[t], r3[t]) % qw) as u64);
        t += 1;
    }
    out
}

// @genesis 09a57ac 2026-09-17 — ntt::AUX_DOFF1
/// `BOUND_D mod p1`, where `BOUND_D = NTT_LEN · GADGET_BASE · Q`.
///
/// The offset for the **bounded** fused dot, where one operand's coefficients
/// are gadget digits rather than arbitrary residues. The generic offset
/// `BOUND = N·q²` is `2^73`, so `2 · L · BOUND` cannot fit `p1·p2` for any
/// `L ≥ 1`; `BOUND_D = N·16·q` is `2^46`, and it is what makes a two-prime
/// reconstruction possible at all. Like `BOUND` it is a multiple of `q`, so it
/// is still invisible in the answer.
pub const AUX_DOFF1: u64 = 266_663_644;
// @genesis 09a57ac 2026-09-17 — ntt::AUX_DOFF2
/// `BOUND_D mod p2`. See [`AUX_DOFF1`].
pub const AUX_DOFF2: u64 = 501_623_972;

// @genesis 09a57ac 2026-09-17 — ntt::garner2
/// Garner reconstruction from **two** residues: the unique `x < p1·p2` with
/// `x ≡ r1 (p1)` and `x ≡ r2 (p2)`.
///
/// ```text
/// t1 = (r2 − r1) · p1⁻¹   mod p2
/// x  = r1 + p1 · t1
/// ```
///
/// Exactly the first stage of [`garner`], and the result is a `u64` rather than
/// a `u128`: `r1 < p1` and `t1 < p2` give `x < p1 + p1·(p2−1) = p1·p2 < 2^59`,
/// so neither the product nor the sum can overflow.
///
/// Only sound where the reconstructed integer is known to be below `p1·p2`;
/// that is the bounded fused dot's precondition, not a property of the residues.
pub fn garner2(r1: u64, r2: u64) -> u64 {
    let d1: u64 = aux_sub(r2, r1, AUX_P2);
    let t1: u64 = aux_mul(d1, GARNER_INV1, AUX_P2, AUX_M2);
    r1 + AUX_P1 * t1
}


// ---------------------------------------------------------------------------
// The Goldilocks lane
// ---------------------------------------------------------------------------

// @genesis b54235e 2026-09-19 — ntt::GOLD_P
/// The Goldilocks prime `2^64 − 2^32 + 1` (candidate T27).
///
/// An **auxiliary** prime, exactly as [`AUX_P1`]–[`AUX_P3`] are: the protocol
/// modulus `params::Q = 2^32 − 99` is untouched and is not NTT-friendly, which
/// is why auxiliary primes exist at all. What this one buys is the *lane
/// count*. A digit-path dot has one operand whose coefficients are below
/// `GADGET_BASE`, so a whole `C`-term product is bounded by
/// `2·C·N·(Q−1)·15`; at `C = 8192` that is `1.081·10^18` against this prime's
/// `1.845·10^19`, a 17× margin. **One lane, and no chunking at all**, where
/// two 30-bit primes need two lanes and four chunks of
/// [`crate::ring::DOT_CHUNK_D`] — and with one lane there is no CRT step
/// either, so [`garner2`] does not run.
///
/// Measured: 158.61 ns per coefficient against the two-prime path's 479.64,
/// **−66.9%**, on `apply_digits` at the pin.
pub const GOLD_P: u64 = 18_446_744_069_414_584_321;

// @genesis b54235e 2026-09-19 — ntt::GOLD_PSI
/// A root of exact order `2 · NTT_LEN` mod [`GOLD_P`] (`7^((p−1)/2048)`).
pub const GOLD_PSI: u64 = 455_906_449_640_507_599;
// @genesis b54235e 2026-09-19 — ntt::GOLD_PSIINV
/// The inverse of [`GOLD_PSI`] mod [`GOLD_P`].
pub const GOLD_PSIINV: u64 = 8_548_973_421_900_915_981;
// @genesis b54235e 2026-09-19 — ntt::GOLD_NINV
/// The inverse of [`NTT_LEN`] mod [`GOLD_P`].
pub const GOLD_NINV: u64 = 18_428_729_670_909_296_641;

// @genesis b54235e 2026-09-19 — ntt::gold_add
/// `a + b mod p`, for `a, b < GOLD_P`.
///
/// The sum can reach `2^65`, so it is formed in a `u128`. The obvious
/// alternatives were measured and are worse: `overflowing_add` is not in the
/// extraction ceiling, and `checked_add` with a `match` on the `Option` is
/// **three times slower** (7.995 ns per butterfly against 2.787) because the
/// match defeats the carry path.
pub fn gold_add(a: u64, b: u64) -> u64 {
    let s: u128 = (a as u128) + (b as u128);
    let p: u128 = GOLD_P as u128;
    if s >= p {
        (s - p) as u64
    } else {
        s as u64
    }
}

// @genesis b54235e 2026-09-19 — ntt::gold_sub
/// `a − b mod p`, for `a, b < GOLD_P`.
pub fn gold_sub(a: u64, b: u64) -> u64 {
    if a >= b {
        a - b
    } else {
        let d: u128 = (a as u128) + (GOLD_P as u128) - (b as u128);
        d as u64
    }
}

// @genesis b54235e 2026-09-19 — ntt::gold_reduce
/// `x mod GOLD_P` for a full 128-bit product.
///
/// `2^64 ≡ 2^32 − 1 (mod p)` is exact, so the fold is two shifts, a mask, one
/// multiply by `2^32 − 1` and two modular adds — no Barrett, no magic
/// constant, and no error term to bound. Writing `hi = a·2^32 + b`, the value
/// is `lo − a + b·(2^32 − 1)`; `b < 2^32` makes `b·(2^32 − 1) < 2^64` and in
/// fact below `p`, so the product needs no reduction of its own.
pub fn gold_reduce(x: u128) -> u64 {
    let lo: u64 = x as u64;
    let hi: u64 = (x >> 64) as u64;
    let hi_hi: u64 = hi >> 32;
    let hi_lo: u64 = hi & 4_294_967_295;
    let m: u64 = hi_lo.wrapping_mul(4_294_967_295);
    gold_add(gold_sub(lo, hi_hi), m)
}

// @genesis b54235e 2026-09-19 — ntt::gold_mul
/// `a · b mod GOLD_P`.
pub fn gold_mul(a: u64, b: u64) -> u64 {
    gold_reduce((a as u128) * (b as u128))
}

// @genesis b54235e 2026-09-19 — ntt::gold_psi_table
/// Powers of `psi` mod [`GOLD_P`], `NTT_LEN` of them.
pub fn gold_psi_table(psi: u64) -> Vec<u64> {
    let n: usize = NTT_LEN;
    let mut out: Vec<u64> = Vec::with_capacity(n);
    let mut cur: u64 = 1;
    let mut i: usize = 0;
    while i < n {
        out.push(cur);
        cur = gold_mul(cur, psi);
        i += 1;
    }
    out
}

// @genesis b54235e 2026-09-19 — ntt::gold_twist
/// The twist: `out[t] = (v[t] mod p) · ψ^t mod p`, in the Goldilocks lane.
///
/// `v[t] < Q < GOLD_P`, so the entry needs no reduction before the multiply.
pub fn gold_twist(v: &Vec<u64>, pt: &Vec<u64>) -> Vec<u64> {
    let n: usize = NTT_LEN;
    let mut out: Vec<u64> = Vec::with_capacity(n);
    let mut t: usize = 0;
    while t < n {
        out.push(gold_mul(v[t], pt[t]));
        t += 1;
    }
    out
}

// @genesis b54235e 2026-09-19 — ntt::gold_dif_stage
/// One decimation-in-frequency stage in the Goldilocks lane.
pub fn gold_dif_stage(src: &Vec<u64>, mut dst: Vec<u64>, len: usize, tw: &Vec<u64>) -> Vec<u64> {
    let n: usize = NTT_LEN;
    let half: usize = len / 2;
    let step: usize = 2 * (n / len);
    let mut start: usize = 0;
    while start < n {
        let mut j: usize = 0;
        while j < half {
            dst[start + j] = gold_add(src[start + j], src[start + j + half]);
            j += 1;
        }
        let mut i: usize = 0;
        let mut e: usize = 0;
        while i < half {
            let d: u64 = gold_sub(src[start + i], src[start + i + half]);
            dst[start + half + i] = gold_mul(d, tw[e]);
            i += 1;
            e += step;
        }
        start += len;
    }
    dst
}

// @genesis b54235e 2026-09-19 — ntt::gold_dit_stage
/// One decimation-in-time stage in the Goldilocks lane.
pub fn gold_dit_stage(src: &Vec<u64>, mut dst: Vec<u64>, len: usize, tw: &Vec<u64>) -> Vec<u64> {
    let n: usize = NTT_LEN;
    let half: usize = len / 2;
    let step: usize = 2 * (n / len);
    let mut start: usize = 0;
    while start < n {
        let mut j: usize = 0;
        let mut e: usize = 0;
        while j < half {
            let v: u64 = gold_mul(src[start + j + half], tw[e]);
            dst[start + j] = gold_add(src[start + j], v);
            j += 1;
            e += step;
        }
        let mut i: usize = 0;
        let mut e2: usize = 0;
        while i < half {
            let v: u64 = gold_mul(src[start + i + half], tw[e2]);
            dst[start + half + i] = gold_sub(src[start + i], v);
            i += 1;
            e2 += step;
        }
        start += len;
    }
    dst
}

// @genesis f65ce91 2026-09-20 — ntt::gold_dif_stage2
/// **Two** decimation-in-frequency stages in one pass -- the radix-4 shape, in
/// the Goldilocks lane.
///
/// Computes exactly what [`gold_dif_stage`] at `len` followed by
/// [`gold_dif_stage`] at `len / 2` computes: the same values, at the same
/// positions, from the same twiddles. That is the whole design. A textbook
/// radix-4 butterfly permutes its four outputs, so it agrees with the radix-2
/// transform only up to base-4 digit reversal, and proving it would mean a
/// radix-4 theory of its own -- a `dif4Run`, its multiplicativity, its
/// inverse. Fusing the *pair* instead leaves [`AuxNTT.difRun`] alone: one pass
/// here is `difRun om (k+2) step = difRun om k (step*4)` by `difRun_succ`
/// twice, so `gold_forward_spec`'s statement does not move and everything
/// above it -- `AuxProduct.prod_difRun`, `inv_value`, `gold_dot_spec` -- is
/// untouched.
///
/// The gain is the memory pattern, which is the radix-4 one either way: four
/// reads and four writes per group at stride `len/4`, and **five** passes over
/// the array instead of ten. Gated at -34.7% on the transform.
///
/// The intermediate names are the pair's: `b0..b3` is what the first stage
/// would have written, `dst` is what the second one makes of it. Writing the
/// four outputs in *that* order, rather than the natural radix-4 order, is
/// exactly what buys the elementwise agreement.
pub fn gold_dif_stage2(src: &Vec<u64>, mut dst: Vec<u64>, len: usize, tw: &Vec<u64>) -> Vec<u64> {
    let n: usize = NTT_LEN;
    let half: usize = len / 2;
    let quarter: usize = len / 4;
    let step1: usize = 2 * (n / len);
    let step2: usize = 2 * step1;
    let mut start: usize = 0;
    while start < n {
        let mut j: usize = 0;
        while j < quarter {
            let a0: u64 = src[start + j];
            let a1: u64 = src[start + j + quarter];
            let a2: u64 = src[start + j + half];
            let a3: u64 = src[start + j + half + quarter];
            let b0: u64 = gold_add(a0, a2);
            let b1: u64 = gold_add(a1, a3);
            let d0: u64 = gold_sub(a0, a2);
            let b2: u64 = gold_mul(d0, tw[j * step1]);
            let d1: u64 = gold_sub(a1, a3);
            let b3: u64 = gold_mul(d1, tw[(j + quarter) * step1]);
            dst[start + j] = gold_add(b0, b1);
            let e0: u64 = gold_sub(b0, b1);
            dst[start + j + quarter] = gold_mul(e0, tw[j * step2]);
            dst[start + half + j] = gold_add(b2, b3);
            let e1: u64 = gold_sub(b2, b3);
            dst[start + half + quarter + j] = gold_mul(e1, tw[j * step2]);
            j += 1;
        }
        start += len;
    }
    dst
}

// @genesis b54235e 2026-09-19 — ntt::gold_forward
/// The forward transform in the Goldilocks lane.
pub fn gold_forward(cur0: Vec<u64>, tmp0: Vec<u64>, tw: &Vec<u64>) -> (Vec<u64>, Vec<u64>) {
    let mut cur: Vec<u64> = cur0;
    let mut tmp: Vec<u64> = tmp0;
    let mut len: usize = NTT_LEN;
    while len > 1 {
        let filled: Vec<u64> = gold_dif_stage(&cur, tmp, len, tw);
        tmp = cur;
        cur = filled;
        len = len / 2;
    }
    (cur, tmp)
}

// @genesis b54235e 2026-09-19 — ntt::gold_inverse
/// The inverse transform in the Goldilocks lane, up to the factor `N`.
pub fn gold_inverse(cur0: Vec<u64>, tmp0: Vec<u64>, tw: &Vec<u64>) -> (Vec<u64>, Vec<u64>) {
    let mut cur: Vec<u64> = cur0;
    let mut tmp: Vec<u64> = tmp0;
    let mut len: usize = 2;
    while len <= NTT_LEN {
        let filled: Vec<u64> = gold_dit_stage(&cur, tmp, len, tw);
        tmp = cur;
        cur = filled;
        len = len * 2;
    }
    (cur, tmp)
}

// @genesis 64721ad 2026-09-19 — ntt::GOLD_DOFF
/// `BOUND_D = N · q · GADGET_BASE`, the per-term offset of the digit path,
/// which is already below [`GOLD_P`] so it needs no reduction.
pub const GOLD_DOFF: u64 = 70_368_742_555_648;

// @genesis 64721ad 2026-09-19 — ntt::gold_untwist_off
/// The untwist, with the digit path's offset — the Goldilocks counterpart of
/// [`untwist`] at [`AUX_DOFF1`].
///
/// The offset rather than a centred lift, deliberately. A centred lift is the
/// obvious thing for one lane (the signed coefficient fits the prime whole,
/// `1.081·10^18` against `1.845·10^19`) and it is what the first cut did, but
/// the *offset* is what `AuxFused`'s `offConvSumD` machinery is already stated
/// and proved against — `BOUND_D` is a multiple of `q`, so it vanishes in the
/// reduction, and the whole bound argument carries over with only the radix
/// changed. One modular add per coefficient buys roughly two hundred lines of
/// proof that are already written.
pub fn gold_untwist_off(src: &Vec<u64>, it: &Vec<u64>, off: u64) -> Vec<u64> {
    let n: usize = NTT_LEN;
    let mut out: Vec<u64> = Vec::with_capacity(n);
    let mut t: usize = 0;
    while t < n {
        let u: u64 = gold_mul(src[t], it[t]);
        let s: u64 = gold_mul(u, GOLD_NINV);
        out.push(gold_add(s, off));
        t += 1;
    }
    out
}


// Card T37 (2026-09-21): the transform's boundary passes, fused.
// @genesis PENDING 2026-09-21 — ntt::gold_dif_stage2_mac
/// [`gold_dif_stage2`] with the prepared multiply-accumulate folded into the
/// writes (card T37, B).
///
/// The last pass of the transform is the only one whose output nobody reads
/// again as a transform input, so it is the only one that can absorb the MAC.
/// Where [`gold_dif_stage2`] writes `dst[i] = v`, this writes
/// `acc[i] += pfwd[base + i] · v`, and the 8 KiB buffer the MAC would have
/// read back never exists.
///
/// What this does **not** remove is the stream of `pfwd[base ..]`, a slice of
/// a table far larger than any cache. That read is the loop's one genuinely
/// expensive memory access and it is unchanged here; what the fusion saves is
/// the warm buffer beside it. The multiplications are the same ones in the
/// same order.
///
/// The body is [`gold_dif_stage2`] verbatim down to `b3`, with each of the
/// four `dst[...] = v` writes replaced by the accumulate. Keeping the
/// destination indices in named `let`s rather than repeating the arithmetic
/// is what keeps `acc[o] = ...acc[o]...` a single indexed read-modify-write,
/// the shape the extraction models as an ordinary update.
pub fn gold_dif_stage2_mac(
    src: &Vec<u64>,
    mut acc: Vec<u64>,
    len: usize,
    tw: &Vec<u64>,
    pfwd: &Vec<u64>,
    base: usize,
) -> Vec<u64> {
    let n: usize = NTT_LEN;
    let half: usize = len / 2;
    let quarter: usize = len / 4;
    let step1: usize = 2 * (n / len);
    let step2: usize = 2 * step1;
    let mut start: usize = 0;
    while start < n {
        let mut j: usize = 0;
        while j < quarter {
            let a0: u64 = src[start + j];
            let a1: u64 = src[start + j + quarter];
            let a2: u64 = src[start + j + half];
            let a3: u64 = src[start + j + half + quarter];
            let b0: u64 = gold_add(a0, a2);
            let b1: u64 = gold_add(a1, a3);
            let d0: u64 = gold_sub(a0, a2);
            let b2: u64 = gold_mul(d0, tw[j * step1]);
            let d1: u64 = gold_sub(a1, a3);
            let b3: u64 = gold_mul(d1, tw[(j + quarter) * step1]);
            let o0: usize = start + j;
            let v0: u64 = gold_add(b0, b1);
            acc[o0] = gold_add(acc[o0], gold_mul(pfwd[base + o0], v0));
            let o1: usize = start + j + quarter;
            let e0: u64 = gold_sub(b0, b1);
            let v1: u64 = gold_mul(e0, tw[j * step2]);
            acc[o1] = gold_add(acc[o1], gold_mul(pfwd[base + o1], v1));
            let o2: usize = start + half + j;
            let v2: u64 = gold_add(b2, b3);
            acc[o2] = gold_add(acc[o2], gold_mul(pfwd[base + o2], v2));
            let o3: usize = start + half + quarter + j;
            let e1: u64 = gold_sub(b2, b3);
            let v3: u64 = gold_mul(e1, tw[j * step2]);
            acc[o3] = gold_add(acc[o3], gold_mul(pfwd[base + o3], v3));
            j += 1;
        }
        start += len;
    }
    acc
}
