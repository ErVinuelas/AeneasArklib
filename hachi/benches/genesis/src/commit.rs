//! The inner-outer (Greyhound [NS24] / Hachi [NOZ26]) Ajtai commitment, and its
//! weak-opening verifier.
//!
//! Reference specification:
//! `ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean`; perfect
//! correctness of what is below is `InnerOuter/Correctness.lean`, and the
//! weak-binding reduction to Module-SIS is `InnerOuter/Security.lean`.
//!
//! # The construction
//!
//! Each message block `mᵢ` is gadget-decomposed to `sᵢ = G⁻¹(mᵢ)` and
//! inner-committed under `A`; each inner commitment is itself gadget-decomposed
//! to `t̂ᵢ = G⁻¹(A sᵢ)`; the `t̂ᵢ` are flattened and outer-committed under `B`.
//! The commitment is that single outer product, of `OUTER_ROWS` ring elements,
//! whatever the message size -- which is the point of the composition.
//!
//! # Weak openings
//!
//! The opening this scheme carries is Hachi's *weak* opening `(sᵢ, t̂ᵢ, cᵢ)`
//! ([NOZ26] §4.1): per block a decomposed message, an inner decomposition, and a
//! *challenge*. The challenge is not the committer's to choose -- it originates
//! as the verifier's challenge in the evaluation protocol and is only ever
//! recovered during knowledge extraction -- so the specification splits the types:
//! [`Decomp`] is what the honest committer produces, and [`Opening`] extends it
//! with the challenge. The honest committer pairs its decomposition with
//! `cᵢ = 1`, under which the weak checks collapse to the ordinary honest ones
//! (`1` is a unit, `‖1‖₁ = 1`, and scaling by it changes no norm).
//!
//! A weak opening does not store the message: block `i` is *derived* from `sᵢ`
//! as `mᵢ = G · sᵢ` ([NOZ26] Eq. (13)), which is [`derived_message`].
//!
//! # What is not here
//!
//! * **Parameter generation.** `PublicParams` is taken as input, as the
//!   specification's `setup` does at the level of a distribution
//!   (`$ᵗ (Simple.PublicParams …)`). Deriving the two matrices from a seed is a
//!   design decision this repository has not made and the specification does not
//!   constrain; tests construct them explicitly.
//! * **The `CommitmentScheme` bundle** (`Scheme.lean:217`). It is `setup` (a
//!   distribution), `commit` (an `OracleComp`) and a `verify` that adds the
//!   `derivedMessage = m` check to [`verify_weak`]. The monadic wrapper has no
//!   computational content to translate; its two computational halves are
//!   [`commit_with_decomps`] and [`verify_weak`], and the message check is
//!   [`derived_message`] plus an equality.
//! * **Extractors and the soundness machinery.** Never extracted, by design.
//!
//! # The norms live here
//!
//! `Rq.l1Norm`, `Rq.l2NormSq`, `Rq.lInftyNorm` and their vector lifts are
//! `Data/Lattices/CyclotomicRing/NormBounds/Basic.lean` on the specification
//! side, a layer below the commitment. Here they sit beside their only consumer,
//! [`verify_weak`]: nothing else in this crate measures anything. They would move
//! to a module of their own the moment the security layer (which is not in scope)
//! needed them.

use alloc::vec::Vec;
use cpoly::Fp;

use crate::gadget;
use crate::linalg::{self, PolyMatrix, PolyVec};
use crate::params;
use crate::ring::Rq;

// ---------------------------------------------------------------------------
// Centered norms
// ---------------------------------------------------------------------------

/// The absolute value of a field element's *centered* representative (spec:
/// `(c.valMinAbs).natAbs`, via `zmodCenteredView`,
/// `CyclotomicRing/Norms.lean:48`).
///
/// `ZMod.valMinAbs` sends a residue to its unique representative in
/// `(-q/2, q/2]`; taking the absolute value of that is the same as folding the
/// upper half of `[0, q)` back down, which is what this does. `q` is odd, so
/// `q/2 = (q-1)/2` and the fold has no fixed point to get wrong.
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
pub fn centered_abs(c: Fp) -> u64 {
    let q: u64 = params::Q;
    let half: u64 = q / 2;
    let v: u64 = c.to_u64();
    if v <= half {
        v
    } else {
        q - v
    }
}

/// The centered `ℓ₁` norm of a ring element (spec: `Rq.l1Norm`,
/// `NormBounds/Basic.lean:82`): `Σₖ |cₖ|` over the `deg φ` coefficients.
///
/// Cannot overflow: at most `RING_DEGREE = 64` terms, each below `q/2 < 2^31`.
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
pub fn l1_norm(a: &Rq) -> u64 {
    let n: usize = params::RING_DEGREE;
    let mut acc: u64 = 0;
    let mut k: usize = 0;
    while k < n {
        acc = acc + centered_abs(a.coeff(k));
        k += 1;
    }
    acc
}

/// The centered `ℓ∞` norm of a ring element (spec: `Rq.lInftyNorm`,
/// `NormBounds/Basic.lean:87`): `maxₖ |cₖ|`.
///
/// The spec's `Finset.sup` over an empty range is `0`, which is what an empty
/// loop leaves in the accumulator here.
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
pub fn l_infty_norm(a: &Rq) -> u64 {
    let n: usize = params::RING_DEGREE;
    let mut best: u64 = 0;
    let mut k: usize = 0;
    while k < n {
        let x: u64 = centered_abs(a.coeff(k));
        if x > best {
            best = x;
        }
        k += 1;
    }
    best
}

/// The centered squared-`ℓ₂` norm of a ring element (spec: `Rq.l2NormSq`,
/// `NormBounds/Basic.lean:78`): `Σₖ |cₖ|²`.
///
/// `u128`, and that is forced rather than cautious: a single centered
/// coefficient can reach `q/2 ≈ 2^31`, so one square approaches `2^62` and 64 of
/// them overflow `u64`. The specification sums in `ℕ`, which has no such ceiling;
/// `u128` is what makes this function *total* at every input rather than only at
/// the short ones an honest committer produces -- and totality is what the
/// equivalence proof has to establish (the extracted model is fallible: an
/// overflow there is `Result.fail`, and a spec that only holds for short inputs
/// would leave the verifier's own rejection path unproved).
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
pub fn l2_norm_sq(a: &Rq) -> u128 {
    let n: usize = params::RING_DEGREE;
    let mut acc: u128 = 0;
    let mut k: usize = 0;
    while k < n {
        let x: u128 = centered_abs(a.coeff(k)) as u128;
        acc = acc + x * x;
        k += 1;
    }
    acc
}

/// The centered squared-`ℓ₂` norm of a vector (spec: `vecL2NormSq`,
/// `NormBounds/Basic.lean:91`): the sum of the entrywise norms.
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
pub fn vec_l2_norm_sq(v: &PolyVec) -> u128 {
    let n: usize = v.len();
    let mut acc: u128 = 0;
    let mut i: usize = 0;
    while i < n {
        acc = acc + l2_norm_sq(v.get(i));
        i += 1;
    }
    acc
}

/// The centered `ℓ∞` norm of a vector (spec: `vecLInftyNorm`,
/// `NormBounds/Basic.lean:95`): the largest entrywise norm.
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
pub fn vec_l_infty_norm(v: &PolyVec) -> u64 {
    let n: usize = v.len();
    let mut best: u64 = 0;
    let mut i: usize = 0;
    while i < n {
        let x: u64 = l_infty_norm(v.get(i));
        if x > best {
            best = x;
        }
        i += 1;
    }
    best
}

// ---------------------------------------------------------------------------
// The scheme's data
// ---------------------------------------------------------------------------

/// The two Ajtai matrices (spec: `PublicParams`, `Scheme.lean:94`).
///
/// `inner_matrix` is `A`, of shape `INNER_ROWS × (MESSAGE_ROWS · GADGET_DIGITS)`;
/// `outer_matrix` is `B`, of shape
/// `OUTER_ROWS × (BLOCKS · (INNER_ROWS · GADGET_DIGITS))`.
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
pub struct PublicParams {
    inner_matrix: PolyMatrix,
    outer_matrix: PolyMatrix,
}

impl PublicParams {
    /// Bundle the inner and outer matrices.
    // @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
    pub fn new(inner_matrix: PolyMatrix, outer_matrix: PolyMatrix) -> PublicParams {
        PublicParams {
            inner_matrix,
            outer_matrix,
        }
    }

    /// The inner Ajtai matrix `A`.
    // @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
    pub fn inner_matrix(&self) -> &PolyMatrix {
        &self.inner_matrix
    }

    /// The outer Ajtai matrix `B`.
    // @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
    pub fn outer_matrix(&self) -> &PolyMatrix {
        &self.outer_matrix
    }
}

/// The committer-produced decomposition data `(sᵢ, t̂ᵢ)ᵢ` (spec: `Decomp`,
/// `Scheme.lean:104`), without the challenge.
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
pub struct Decomp {
    message: Vec<PolyVec>,
    inner_decomp: Vec<PolyVec>,
}

impl Decomp {
    /// Bundle per-block decomposed messages and inner decompositions.
    // @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
    pub fn new(message: Vec<PolyVec>, inner_decomp: Vec<PolyVec>) -> Decomp {
        Decomp {
            message,
            inner_decomp,
        }
    }

    /// The number of blocks.
    // @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
    pub fn blocks(&self) -> usize {
        self.message.len()
    }

    /// The decomposed message `sᵢ` of block `i`.
    // @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
    pub fn message(&self, i: usize) -> &PolyVec {
        &self.message[i]
    }

    /// The inner decomposition `t̂ᵢ` of block `i`.
    // @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
    pub fn inner_decomp(&self, i: usize) -> &PolyVec {
        &self.inner_decomp[i]
    }

    /// The inner decompositions as blocks, for flattening.
    // @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
    pub fn inner_decomps(&self) -> &Vec<PolyVec> {
        &self.inner_decomp
    }
}

/// A Hachi/Greyhound weak opening `(sᵢ, t̂ᵢ, cᵢ)ᵢ` (spec: `Opening`,
/// `Scheme.lean:115`).
///
/// The specification's `Opening` *extends* `Decomp`; composition is the same
/// data, reached as `opening.decomp()`.
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
pub struct Opening {
    decomp: Decomp,
    challenge: PolyVec,
}

impl Opening {
    /// Pair decomposition data with per-block challenges.
    // @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
    pub fn new(decomp: Decomp, challenge: PolyVec) -> Opening {
        Opening { decomp, challenge }
    }

    /// The honest opening: the decomposition with the trivial challenge
    /// `cᵢ = 1`, which is what `commitmentScheme.commit` produces
    /// (`Scheme.lean:229`).
    // @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
    pub fn honest(decomp: Decomp) -> Opening {
        let blocks: usize = decomp.blocks();
        let mut ones: Vec<Rq> = Vec::new();
        let mut i: usize = 0;
        while i < blocks {
            ones.push(Rq::one());
            i += 1;
        }
        Opening {
            decomp,
            challenge: PolyVec::new(ones),
        }
    }

    /// The underlying decomposition data.
    // @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
    pub fn decomp(&self) -> &Decomp {
        &self.decomp
    }

    /// The challenge `cᵢ` of block `i`.
    // @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
    pub fn challenge(&self, i: usize) -> &Rq {
        self.challenge.get(i)
    }
}

// ---------------------------------------------------------------------------
// Commit
// ---------------------------------------------------------------------------

/// The message block derived from the decomposition data: `mᵢ = G · sᵢ` (spec:
/// `derivedMessage`, `Scheme.lean:148`, i.e. [NOZ26] Eq. (13)).
///
/// The specification applies the materialized message gadget matrix through
/// `Simple.commit`; [`gadget::gadget_mul`] is the same map by `gadgetMul_apply`,
/// and is the form that does `O(rows · digits)` work instead of
/// `O(rows² · digits)`.
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
pub fn derived_message(decomp: &Decomp) -> Vec<PolyVec> {
    let blocks: usize = decomp.blocks();
    let rows: usize = params::MESSAGE_ROWS;
    let mut out: Vec<PolyVec> = Vec::new();
    let mut i: usize = 0;
    while i < blocks {
        out.push(gadget::gadget_mul(rows, decomp.message(i)));
        i += 1;
    }
    out
}

/// Honest decomposition generation (spec: `generateDecomps`,
/// `Scheme.lean:157`): `sᵢ = G⁻¹(mᵢ)` and `t̂ᵢ = G⁻¹(A sᵢ)`.
///
/// Both steps are the same base-`b` gadget inverse, which is the specification's
/// `Decomposition.ofDigits` (`Scheme.lean:131`) instantiating its two
/// decomposition slots with `gadgetDecompose` at `zmodDigitDecomposition`. The
/// two slots exist because the specification allows different digit counts for
/// them; here they coincide (see [`params::GADGET_DIGITS`]), so one function
/// serves both and `ofDigits` has no computational content left to translate.
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
pub fn generate_decomps(pp: &PublicParams, m: &Vec<PolyVec>) -> Decomp {
    let blocks: usize = m.len();
    let mut ss: Vec<PolyVec> = Vec::new();
    let mut ts: Vec<PolyVec> = Vec::new();
    let mut i: usize = 0;
    while i < blocks {
        let s: PolyVec = gadget::gadget_decompose(&m[i]);
        let inner: PolyVec = pp.inner_matrix().mat_vec_mul(&s);
        ts.push(gadget::gadget_decompose(&inner));
        ss.push(s);
        i += 1;
    }
    Decomp::new(ss, ts)
}

/// The outer commitment computed from the decomposition data (spec:
/// `commitWithDecomps`, `Scheme.lean:166`): `u = B · flatten(t̂)`.
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
pub fn commit_with_decomps(pp: &PublicParams, decomp: &Decomp) -> PolyVec {
    let flat: PolyVec = linalg::flatten_blocks(decomp.inner_decomps());
    pp.outer_matrix().mat_vec_mul(&flat)
}

/// Commit to a message: generate the honest decomposition and return it with the
/// outer commitment (spec: `commitmentScheme.commit`, `Scheme.lean:227`, minus
/// the `OracleComp` wrapper and with the challenge left to
/// [`Opening::honest`]).
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
pub fn commit(pp: &PublicParams, m: &Vec<PolyVec>) -> (PolyVec, Decomp) {
    let decomp: Decomp = generate_decomps(pp, m);
    let u: PolyVec = commit_with_decomps(pp, &decomp);
    (u, decomp)
}

// ---------------------------------------------------------------------------
// Verify
// ---------------------------------------------------------------------------

/// Verify a weak opening against the outer commitment `u` (spec:
/// `verify_weak`, `Scheme.lean:194`).
///
/// Per block `i`:
///
/// * `0 < ‖cᵢ‖₁` -- the challenge is nonzero. The specification checks this
///   rather than invertibility because the two coincide here: `isUnit_of_l1Norm_le`
///   ([LS18], `NormBounds/LyubashevskySeiler.lean:344`) turns
///   `0 < ‖cᵢ‖₁ ≤ κ` into `IsUnit cᵢ` given `q % 8 = 5` and `κ² < q`, both of
///   which hold at these parameters (see [`params::KAPPA`]).
/// * `‖cᵢ‖₁ ≤ κ` -- the challenge is `ℓ₁`-short.
/// * `‖cᵢ · sᵢ‖₂² ≤ βSq` -- the scaled message is `ℓ₂²`-short.
/// * `A sᵢ = G t̂ᵢ` -- the inner gadget relation.
///
/// Then globally: `‖t̂‖∞ ≤ γ` on the flattened inner decomposition, and
/// `B · flatten(t̂) = u`.
///
/// Every check is evaluated; there is no short-circuit. That mirrors the
/// specification, which is a `&&` of `List.all` over eagerly-`decide`d
/// propositions, and it keeps the control flow (and so the extracted model) a
/// straight line.
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
pub fn verify_weak(pp: &PublicParams, u: &PolyVec, opening: &Opening) -> bool {
    let decomp: &Decomp = opening.decomp();
    let blocks: usize = decomp.blocks();
    let mut ok: bool = true;

    let mut i: usize = 0;
    while i < blocks {
        let c: &Rq = opening.challenge(i);
        let c_l1: u64 = l1_norm(c);
        if c_l1 == 0 {
            ok = false;
        }
        if c_l1 > params::KAPPA {
            ok = false;
        }
        let scaled: PolyVec = decomp.message(i).scalar_mul(c);
        if vec_l2_norm_sq(&scaled) > params::BETA_SQ {
            ok = false;
        }
        let inner: PolyVec = pp.inner_matrix().mat_vec_mul(decomp.message(i));
        let recomposed: PolyVec = gadget::gadget_mul(params::INNER_ROWS, decomp.inner_decomp(i));
        if !recomposed.equals(&inner) {
            ok = false;
        }
        i += 1;
    }

    let flat: PolyVec = linalg::flatten_blocks(decomp.inner_decomps());
    if vec_l_infty_norm(&flat) > params::GAMMA {
        ok = false;
    }
    let outer: PolyVec = pp.outer_matrix().mat_vec_mul(&flat);
    if !outer.equals(u) {
        ok = false;
    }

    ok
}

/// Verify an opening against a claimed message (spec:
/// `commitmentScheme.verify`, `Scheme.lean:231`): the message must be the one
/// derived from the opening, and the weak checks must pass.
// @genesis (this file's introducing commit) 2026-08-18 -- hachi/src/commit.rs
pub fn verify(pp: &PublicParams, m: &Vec<PolyVec>, u: &PolyVec, opening: &Opening) -> bool {
    let derived: Vec<PolyVec> = derived_message(opening.decomp());
    let blocks: usize = m.len();
    let mut ok: bool = true;
    if derived.len() != blocks {
        ok = false;
    } else {
        let mut i: usize = 0;
        while i < blocks {
            if !derived[i].equals(&m[i]) {
                ok = false;
            }
            i += 1;
        }
    }
    if !verify_weak(pp, u, opening) {
        ok = false;
    }
    ok
}
