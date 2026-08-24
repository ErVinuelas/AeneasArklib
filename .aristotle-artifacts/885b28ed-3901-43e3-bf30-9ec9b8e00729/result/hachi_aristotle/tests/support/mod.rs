//! Shared test scaffolding: a deterministic generator and a few printers.
//!
//! No RNG crate, by project rule and because the tests would be worse with one:
//! a failure has to be reproducible from the test name alone, so every generator
//! below is seeded explicitly and produces the same corpus on every machine.
//!
//! The types under test carry no `Debug` impl on purpose (see `src/lib.rs`: a
//! `Debug` impl is extracted, and `core::fmt` plumbing in the model is four items
//! per type that no proof mentions). So the printers here exist to keep assertion
//! messages informative anyway; they use the same public API a caller has.

#![allow(dead_code)]

use cpoly::Fp;
use hachi::linalg::{PolyMatrix, PolyVec};
use hachi::params::{Q, RING_DEGREE};
use hachi::ring::Rq;

/// A linear congruential generator: `x ← 6364136223846793005·x + 1442695040888963407`
/// (Knuth's MMIX constants), high bits taken.
///
/// Deterministic, four lines, no dependency. The low bits of an LCG are famously
/// poor, so [`Lcg::next_u64`] returns the xor-folded high half rather than the
/// raw state -- which matters here only because a corpus of coefficients whose
/// low bits are correlated would make a digit-decomposition test look better than
/// it is.
pub struct Lcg(u64);

impl Lcg {
    /// A generator with the given seed.
    pub fn new(seed: u64) -> Lcg {
        Lcg(seed)
    }

    /// The next 64 bits.
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 ^ (self.0 >> 32)
    }

    /// The next field element, uniform enough over `[0, Q)` for a test corpus.
    pub fn next_fp(&mut self) -> Fp {
        Fp::new(self.next_u64() % Q)
    }

    /// A ring element with random coefficients.
    pub fn next_rq(&mut self) -> Rq {
        let mut coeffs = Vec::new();
        for _ in 0..RING_DEGREE {
            coeffs.push(self.next_fp());
        }
        Rq::from_coeffs(&coeffs)
    }

    /// A vector of `k` random ring elements.
    pub fn next_poly_vec(&mut self, k: usize) -> PolyVec {
        let mut entries = Vec::new();
        for _ in 0..k {
            entries.push(self.next_rq());
        }
        PolyVec::new(entries)
    }

    /// A `rows × cols` matrix of random ring elements.
    pub fn next_poly_matrix(&mut self, rows: usize, cols: usize) -> PolyMatrix {
        let mut out = Vec::new();
        for _ in 0..rows {
            out.push(self.next_poly_vec(cols));
        }
        PolyMatrix::new(out)
    }
}

/// A ring element from its low-order coefficients, the rest zero.
pub fn rq_from_u64s(coeffs: &[u64]) -> Rq {
    let mut v = Vec::new();
    for c in coeffs {
        v.push(Fp::new(*c));
    }
    Rq::from_coeffs(&v)
}

/// The coefficients of a ring element, as words.
pub fn coeffs_of(a: &Rq) -> Vec<u64> {
    let mut out = Vec::new();
    for k in 0..a.len() {
        out.push(a.coeff(k).to_u64());
    }
    out
}

/// A ring element as a short string: the leading coefficients, and how many
/// non-zero ones there are in total.
pub fn show(a: &Rq) -> String {
    let c = coeffs_of(a);
    let nonzero = c.iter().filter(|x| **x != 0).count();
    let head: Vec<String> = c.iter().take(6).map(u64::to_string).collect();
    format!("[{}, …] ({nonzero} nonzero)", head.join(", "))
}

/// A vector of ring elements as a short string.
pub fn show_vec(v: &PolyVec) -> String {
    let mut parts = Vec::new();
    for i in 0..v.len() {
        parts.push(show(v.get(i)));
    }
    format!("[{}]", parts.join("; "))
}
