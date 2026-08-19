//! Shared bench scaffolding: the seeded corpus, and the discipline notes that
//! apply to every case.
//!
//! # Three variants, one session
//!
//! Every case is measured in up to three variants -- `now` (`hachi`), `genesis`
//! (`hachi_genesis`, the frozen first translation) and, under
//! `--features candidate`, `cand` (`hachi_candidate`). They are measured *back to
//! back in one criterion session*, on the same machine, at the same temperature,
//! with the same compiler, because that is the only way a "vs genesis" reading is
//! a comparison rather than a recollection. Nothing is ever compared across runs.
//!
//! # What the corpus guarantees
//!
//! * **Identical inputs across variants.** The three crates have distinct types
//!   (`hachi::ring::Rq` is not `hachi_genesis::ring::Rq`), so each variant builds
//!   its own values -- but from the same `Vec<Fp>` corpus produced by the same
//!   seed, so they are the same values. A difference in a reading is then a
//!   difference in code.
//! * **Reproducibility.** Seeds are literals; no clock, no RNG crate.
//! * **No zeros.** Coefficients are drawn from `[1, Q)`. Zeros are the input on
//!   which a short-circuiting implementation looks fastest, and a corpus whose
//!   zero count depends on the seed makes two runs incomparable for a reason that
//!   has nothing to do with the code.
//!
//! # The `_control` case
//!
//! Each group carries a `_control` case timing an operation whose code is
//! *byte-identical* in all three crates. Any spread it reports is the harness's
//! own bias -- LTO decisions, code placement, measurement order -- and it is the
//! noise floor against which every other spread in the group has to be read. A
//! 3% "improvement" in a case whose control also moved 3% is not an improvement.

#![allow(dead_code)]

use cpoly::Fp;

/// `SplitMix64`, as in the scaffold's bench: four lines, no dependency.
pub struct SplitMix64(u64);

impl SplitMix64 {
    /// A generator with the given seed.
    pub fn new(seed: u64) -> SplitMix64 {
        SplitMix64(seed)
    }

    /// The next 64 bits.
    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// `n` field elements drawn from `[1, Q)`; see the module header for why zero is
/// excluded.
pub fn corpus(seed: u64, n: usize) -> Vec<Fp> {
    let q = hachi::params::Q;
    let mut rng = SplitMix64::new(seed);
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(Fp::new(1 + rng.next() % (q - 1)));
    }
    v
}

/// `blocks` corpora of `n` elements each, from one seed.
pub fn corpora(seed: u64, blocks: usize, n: usize) -> Vec<Vec<Fp>> {
    let mut out = Vec::with_capacity(blocks);
    for b in 0..blocks {
        out.push(corpus(seed.wrapping_add(b as u64 * 0x1000), n));
    }
    out
}
