//! The QuadEval fold: Hachi's [NOZ26] Figure 3 reduction, from the committed
//! evaluation claim to the output witness `(ŵ, t̂, ẑ)` and the Eq. (20) checks.
//!
//! Reference specification:
//! `ArkLib/Commitments/Functional/Hachi/QuadEval/Gadgets.lean` (the carrier and
//! tensor algebra) and `QuadEval/Reduction.lean` (the statement, response,
//! honest prover computations, and the output relation).
//!
//! The prover folds the `2^r` message blocks against the verifier's challenge
//! into a single opening `z = Σᵢ cᵢ sᵢ`, commits to the *carrier*
//! `wᵢ = aᵀ G sᵢ` in decomposed form `ŵ = G⁻¹(w)`, and answers with
//! `(ŵ, t̂, ẑ)` where `ẑ = J⁻¹(z)`. `relOut` is what the verifier checks of
//! that triple.
//!
//! # Two gadget widths, and they are not interchangeable
//!
//! The carrier side decomposes arbitrary residues, so it uses the full-width
//! balanced gadget at [`params::GADGET_DIGITS`]` = 8`
//! ([`crate::gadget::balanced_gadget_decompose`]). The `z` side does not: an
//! honest `z` is deterministically short, so ArkLib sizes its digit count from
//! that bound instead of from `q`, giving [`params::Z_DIGITS`]` = 5` over a
//! `BoundedDigitDecomposition` ([`crate::gadget::bounded_z_gadget_decompose`]).
//! `16^5 < q`, so a five-digit decomposition of *every* residue does not exist
//! and the `z` round trip `z = J ẑ` holds only for `‖z‖∞ ≤ `[`params::Z_BOUND`]
//! -- see ArkLib PR #847, and NOTES.md § "One digit count, not two".
//!
//! # No matrix here is ever materialized
//!
//! `gadgetMatrix Φ base (2^m) δ` is `2^m × 2^m·δ` ring elements, ~64 GiB, and
//! `jMatrix Φ base n zDigits` is ~2.5 TB at these parameters. Both are always
//! reached through the collapsed per-block digit sum
//! ([`crate::gadget::gadget_mul`] and [`crate::gadget::gadget_mul_z`]), which
//! the specification's own `gadgetMul_apply` (`Gadget/Core.lean:429`) proves
//! equals the matrix product. That is a feasibility requirement, not an
//! optimization: the direct form cannot be run at any speed.
//!
//! # `relOut` is a `Prop`; [`rel_out`] is a decision procedure
//!
//! `relOut` and `paperRelOut` are `Set`s of conjunctions
//! (`QuadEval/Reduction.lean:258, 335`), where the already-translated
//! `InnerOuter.verify_weak` is a `Bool`. So the equivalence statement for
//! [`rel_out`] is an **iff**, not an equality of `Bool`s. Every conjunct is
//! decidable -- `Rq` equality is canonical and the norms are `ℕ` -- so this is
//! a shape difference rather than a risk, but it is a shape the spec author has
//! to be told about.
//!
//! # Two range checks, and the difference between them is the point
//!
//! [`rel_out`]'s c6 is an `ℓ∞` **ball**, `‖·‖∞ ≤ `[`params::CHAIN_GAMMA`]` = 15`.
//! [`paper_rel_out`] replaces it with the paper's exact **box**
//! `S_b = [-8, 7]` ([`in_sb`]). The box is asymmetric and tight on the honest
//! balanced digits; the ball has slack 7 and admits `+8`, which the box does
//! not. A corpus that stays inside the ball therefore cannot tell the two
//! apart -- see `tests/quadeval_semantics.rs`.

use alloc::vec::Vec;

use crate::commit::{centered_abs, PublicParams};
use crate::gadget;
use crate::linalg::{self, PolyMatrix, PolyVec};
use crate::params;
use crate::ring::Rq;

// ---------------------------------------------------------------------------
// Carriers
// ---------------------------------------------------------------------------

// @genesis b984c53 2026-09-04 — quadeval::PublicParamsD
/// The inner-outer parameters extended with Hachi's short-commitment matrix `D`
/// (spec: `PublicParamsD`, `QuadEval/Gadgets.lean:67`).
///
/// Mirrors ArkLib's `Hachi.PublicParamsD`.
///
/// The specification's structure `extends InnerOuter.PublicParams`; composition
/// is the same data, reached as `pp.inner()`, exactly as [`crate::commit::Opening`]
/// renders its own `extends Decomp`.
pub struct PublicParamsD {
    inner: PublicParams,
    d_matrix: PolyMatrix,
}

impl PublicParamsD {
    // @genesis b984c53 2026-09-04 — quadeval::PublicParamsD::new
    /// Extend inner-outer parameters with the short-commitment matrix `D`, of
    /// shape `D_ROWS × D_QUAD_COLS`.
    pub fn new(inner: PublicParams, d_matrix: PolyMatrix) -> PublicParamsD {
        PublicParamsD { inner, d_matrix }
    }

    // @genesis b984c53 2026-09-04 — quadeval::PublicParamsD::inner
    /// The underlying inner-outer parameters `(A, B)`.
    pub fn inner(&self) -> &PublicParams {
        &self.inner
    }

    // @genesis b984c53 2026-09-04 — quadeval::PublicParamsD::d_matrix
    /// The short-commitment matrix `D` ([NOZ26] Eq. (16)).
    pub fn d_matrix(&self) -> &PolyMatrix {
        &self.d_matrix
    }
}

// @genesis b984c53 2026-09-04 — quadeval::QuadEvalStatement
/// The reduction's input statement (spec: `QuadEvalStatement`,
/// `QuadEval/Reduction.lean:84`).
///
/// Mirrors ArkLib's `QuadEvalStatement`.
pub struct QuadEvalStatement {
    u: PolyVec,
    avec: PolyVec,
    bvec: PolyVec,
    y: Rq,
}

impl QuadEvalStatement {
    // @genesis b984c53 2026-09-04 — quadeval::QuadEvalStatement::new
    /// Bundle the outer commitment, the two evaluation bases and the claim.
    pub fn new(u: PolyVec, avec: PolyVec, bvec: PolyVec, y: Rq) -> QuadEvalStatement {
        QuadEvalStatement { u, avec, bvec, y }
    }

    // @genesis b984c53 2026-09-04 — quadeval::QuadEvalStatement::u
    /// The outer commitment `u`.
    pub fn u(&self) -> &PolyVec {
        &self.u
    }

    // @genesis b984c53 2026-09-04 — quadeval::QuadEvalStatement::avec
    /// The inner evaluation basis `aᵀ` ([NOZ26] Eq. (12)).
    pub fn avec(&self) -> &PolyVec {
        &self.avec
    }

    // @genesis b984c53 2026-09-04 — quadeval::QuadEvalStatement::bvec
    /// The outer evaluation basis `bᵀ` ([NOZ26] Eq. (12)).
    pub fn bvec(&self) -> &PolyVec {
        &self.bvec
    }

    // @genesis b984c53 2026-09-04 — quadeval::QuadEvalStatement::y
    /// The claimed evaluation `y = f(x)`.
    pub fn y(&self) -> &Rq {
        &self.y
    }
}

// @genesis b984c53 2026-09-04 — quadeval::QuadEvalResponse
/// The reduction's output witness `(ŵ, t̂, ẑ)` (spec: `QuadEvalResponse`,
/// `QuadEval/Reduction.lean:98`).
///
/// Mirrors ArkLib's `QuadEvalResponse`.
///
/// `inner_dec` stays blocked rather than flattened because c2 and c5 flatten it
/// themselves (`QuadEval/Reduction.lean:272, 279`).
// The three field names are the specification's own -- `carrierDec`, `innerDec`,
// `zDec` (`QuadEval/Reduction.lean:98`) -- and matching them is what makes the
// struct readable next to the Lean it mirrors. `struct_field_names` wants the
// shared `_dec` suffix dropped, which would rename all three away from the spec.
#[allow(clippy::struct_field_names)]
pub struct QuadEvalResponse {
    carrier_dec: PolyVec,
    inner_dec: Vec<PolyVec>,
    z_dec: PolyVec,
}

impl QuadEvalResponse {
    // @genesis b984c53 2026-09-04 — quadeval::QuadEvalResponse::new
    /// Bundle the decomposed carrier, the per-block inner decompositions, and
    /// the decomposed folded opening.
    pub fn new(carrier_dec: PolyVec, inner_dec: Vec<PolyVec>, z_dec: PolyVec) -> QuadEvalResponse {
        QuadEvalResponse {
            carrier_dec,
            inner_dec,
            z_dec,
        }
    }

    // @genesis b984c53 2026-09-04 — quadeval::QuadEvalResponse::carrier_dec
    /// `ŵ = G⁻¹(w)`, the decomposed carrier.
    pub fn carrier_dec(&self) -> &PolyVec {
        &self.carrier_dec
    }

    // @genesis b984c53 2026-09-04 — quadeval::QuadEvalResponse::inner_dec
    /// `t̂`, the per-block inner decompositions.
    pub fn inner_dec(&self) -> &Vec<PolyVec> {
        &self.inner_dec
    }

    // @genesis b984c53 2026-09-04 — quadeval::QuadEvalResponse::z_dec
    /// `ẑ = J⁻¹(z)`, the decomposed folded opening.
    pub fn z_dec(&self) -> &PolyVec {
        &self.z_dec
    }
}

// @genesis b984c53 2026-09-04 — quadeval::carrier_entry
/// One carrier entry `wᵢ = aᵀ (G sᵢ)` (spec: `carrierEntry`,
/// `QuadEval/Gadgets.lean:82`, i.e. `splitForm (gadgetMatrix …) a s`).
///
/// Mirrors ArkLib's `carrierEntry`.
///
/// `splitForm M u v` is `u ⬝ᵥ (M *ᵥ v)` (`Vectors.lean:197`), and the `M` here
/// is the gadget matrix, so this is [`crate::gadget::gadget_mul`] followed by a
/// dot product rather than [`crate::linalg::PolyMatrix::split_form`] against a
/// materialized `G` -- see the module header on why `G` is never built.
pub fn carrier_entry(a: &PolyVec, s: &PolyVec) -> Rq {
    let rows: usize = a.len();
    let recomposed: PolyVec = gadget::gadget_mul(rows, s);
    a.dot(&recomposed)
}

// @genesis b984c53 2026-09-04 — quadeval::carrier
/// The carrier `w = (w₁, …, w_{2ʳ})` (spec: `carrier`,
/// `QuadEval/Gadgets.lean:87`).
///
/// Mirrors ArkLib's `carrier`.
pub fn carrier(a: &PolyVec, s: &Vec<PolyVec>) -> PolyVec {
    let blocks: usize = s.len();
    let mut out: Vec<Rq> = Vec::new();
    let mut i: usize = 0;
    while i < blocks {
        out.push(carrier_entry(a, &s[i]));
        i += 1;
    }
    PolyVec::new(out)
}

// @genesis b984c53 2026-09-04 — quadeval::carrier_decomp
/// The carrier decomposition `ŵ = G⁻¹(w)` (spec: `carrierDecomp`,
/// `QuadEval/Gadgets.lean:95`, at the balanced `ddCarrier` the composed chain
/// supplies, `HonestChain.lean:308`).
///
/// Mirrors ArkLib's `carrierDecomp` at `balancedZmodDigitDecomposition`.
///
/// Full width: carrier coefficients are arbitrary residues, so this is the
/// `GADGET_DIGITS = 8` gadget and not the `z` side's bounded one.
pub fn carrier_decomp(a: &PolyVec, s: &Vec<PolyVec>) -> PolyVec {
    let w: PolyVec = carrier(a, s);
    gadget::balanced_gadget_decompose(&w)
}

// @genesis b984c53 2026-09-04 — quadeval::carrier_commit
/// The short carrier commitment `v = D ŵ` (spec: `carrierCommit`,
/// `QuadEval/Gadgets.lean:110`; `Simple.commit Φ D x` is `D *ᵥ x`,
/// `Simple/Scheme.lean:38`).
///
/// Mirrors ArkLib's `carrierCommit` at `balancedZmodDigitDecomposition`.
pub fn carrier_commit(d_matrix: &PolyMatrix, a: &PolyVec, s: &Vec<PolyVec>) -> PolyVec {
    let what: PolyVec = carrier_decomp(a, s);
    d_matrix.mat_vec_mul(&what)
}

// ---------------------------------------------------------------------------
// The block-weighted gadget sums
// ---------------------------------------------------------------------------

// @genesis b984c53 2026-09-04 — quadeval::tensor_g
/// `tensorG_k c x = Σᵢ cᵢ •ᵥ (G_k xᵢ)` (spec: `tensorG`,
/// `QuadEval/Gadgets.lean:187`), the Eq. (20) row-5 left-hand side.
///
/// Mirrors ArkLib's `tensorG`.
///
/// A `Finset.sum` of *vectors*, i.e. `Pi` addition, accumulated here from
/// [`crate::linalg::PolyVec::zeros`] so that the empty-block case is the
/// specification's empty sum. `•ᵥ` is `scalarVecMul`, a full ring product per
/// entry (`Vectors.lean:97`), not a coefficient scaling.
pub fn tensor_g(rows: usize, c: &PolyVec, x: &Vec<PolyVec>) -> PolyVec {
    let blocks: usize = x.len();
    let mut acc: PolyVec = PolyVec::zeros(rows);
    let mut i: usize = 0;
    while i < blocks {
        let recomposed: PolyVec = gadget::gadget_mul(rows, &x[i]);
        let scaled: PolyVec = recomposed.scalar_mul(c.get(i));
        acc = acc.add(&scaled);
        i += 1;
    }
    acc
}

// @genesis b984c53 2026-09-04 — quadeval::tensor_g1
/// `tensorG1 c x = ⟨c, G_{2ʳ} x⟩` (spec: `tensorG1`,
/// `QuadEval/Gadgets.lean:224`), the Eq. (20) row-4 left-hand side.
///
/// Mirrors ArkLib's `tensorG1`.
///
/// The challenge-weighted sum of the recomposed carrier: `cᵀ ⊗ G₁` is
/// `cᵀ · (I ⊗ G₁)`, which is why one `gadget_mul` and one dot product suffice.
pub fn tensor_g1(c: &PolyVec, x: &PolyVec) -> Rq {
    let blocks: usize = c.len();
    let recomposed: PolyVec = gadget::gadget_mul(blocks, x);
    c.dot(&recomposed)
}

// ---------------------------------------------------------------------------
// The honest prover's computations
// ---------------------------------------------------------------------------

// @genesis b984c53 2026-09-04 — quadeval::honest_z
/// The folded opening `z = Σᵢ cᵢ sᵢ` (spec: `honestZ`,
/// `QuadEval/Reduction.lean:515`).
///
/// Mirrors ArkLib's `honestZ`.
///
/// **The dominant cost of the whole target.** `•ᵥ` multiplies by a *ring
/// element*, so this is `blocks · (MESSAGE_ROWS · GADGET_DIGITS)` full ring
/// products -- `2^23` at [NOZ26] Fig. 9, the same order as
/// `commit::commit`. It is also the function that makes the witness
/// `message` `2^23` ring elements (~64 GiB), which is a *memory* wall
/// independent of multiplication speed; see `benches/exclusions.toml`.
pub fn honest_z(message: &Vec<PolyVec>, c: &PolyVec) -> PolyVec {
    let blocks: usize = message.len();
    let width: usize = params::MESSAGE_ROWS * params::GADGET_DIGITS;
    let mut acc: PolyVec = PolyVec::zeros(width);
    let mut i: usize = 0;
    while i < blocks {
        let scaled: PolyVec = message[i].scalar_mul(c.get(i));
        acc = acc.add(&scaled);
        i += 1;
    }
    acc
}

// @genesis b984c53 2026-09-04 — quadeval::honest_compute_v
/// The prover's round-0 message `v = D ŵ` (spec: `honestComputeV`,
/// `QuadEval/Reduction.lean:502`).
///
/// Mirrors ArkLib's `honestComputeV`.
pub fn honest_compute_v(
    pp: &PublicParamsD,
    stmt: &QuadEvalStatement,
    message: &Vec<PolyVec>,
) -> PolyVec {
    carrier_commit(pp.d_matrix(), stmt.avec(), message)
}

// @genesis b984c53 2026-09-04 — quadeval::honest_compute_resp
/// The honest output witness `(ŵ, t̂, ẑ)` (spec: `honestComputeResp`,
/// `QuadEval/Reduction.lean:531`).
///
/// Mirrors ArkLib's `honestComputeResp` at
/// `boundedBalancedZmodDigitDecomposition`.
///
/// The `z` step uses the **bounded** decomposition at [`params::Z_DIGITS`]` = 5`
/// (ArkLib PR #847), not the full-width one the carrier step uses. `inner_dec`
/// is a pass-through of the witness's own inner decompositions.
pub fn honest_compute_resp(
    stmt: &QuadEvalStatement,
    message: &Vec<PolyVec>,
    inner_decomp: &Vec<PolyVec>,
    c: &PolyVec,
) -> QuadEvalResponse {
    let carrier_dec: PolyVec = carrier_decomp(stmt.avec(), message);
    let z: PolyVec = honest_z(message, c);
    let z_dec: PolyVec = gadget::bounded_z_gadget_decompose(&z);
    let mut inner: Vec<PolyVec> = Vec::new();
    let mut i: usize = 0;
    while i < inner_decomp.len() {
        inner.push(inner_decomp[i].copy());
        i += 1;
    }
    QuadEvalResponse::new(carrier_dec, inner, z_dec)
}

// ---------------------------------------------------------------------------
// The output relation
// ---------------------------------------------------------------------------

// @genesis b984c53 2026-09-04 — quadeval::in_sb
/// Membership of one ring element in the paper's balanced digit box
/// `S_b = [⌈-b/2⌉, ⌈b/2⌉ - 1] = [-8, 7]` (spec: `InSb`,
/// `QuadEval/Reduction.lean:297`).
///
/// Mirrors ArkLib's `InSb` at `β = GADGET_BASE`.
///
/// Every bound in the specification is on `ZMod.valMinAbs`, the *centered*
/// representative, and the box is **asymmetric**: `-8` is admissible and `+8`
/// is not. So this branches on the sign of the centered value rather than
/// testing a magnitude -- [`crate::commit::centered_abs`] alone cannot express
/// it, which is why the two endpoints are checked separately.
pub fn in_sb(a: &Rq) -> bool {
    let n: usize = params::RING_DEGREE;
    let q: u64 = params::Q;
    let half: u64 = q / 2;
    let mut ok: bool = true;
    let mut k: usize = 0;
    while k < n {
        let v: u64 = a.coeff(k).to_u64();
        if v <= half {
            // Centered value is `+v`; the box admits up to `SB_HI = 7`.
            if v > params::SB_HI {
                ok = false;
            }
        } else {
            // Centered value is `-(q - v)`; the box admits down to `-HALF_BASE`.
            if centered_abs(a.coeff(k)) > params::HALF_BASE {
                ok = false;
            }
        }
        k += 1;
    }
    ok
}

// @genesis b984c53 2026-09-04 — quadeval::vec_in_sb
/// Every entry of a vector lies in the box (spec: `vecInSb`,
/// `QuadEval/Reduction.lean:303`).
///
/// Mirrors ArkLib's `vecInSb` at `β = GADGET_BASE`.
///
/// Branchless to the end, like [`crate::ring::Rq::equals`], because that is the
/// shape the decision-procedure proof mirrors.
pub fn vec_in_sb(v: &PolyVec) -> bool {
    let n: usize = v.len();
    let mut ok: bool = true;
    let mut i: usize = 0;
    while i < n {
        if !in_sb(v.get(i)) {
            ok = false;
        }
        i += 1;
    }
    ok
}

// @genesis b984c53 2026-09-04 — quadeval::j_mul
/// The folded opening recovered from its decomposition, `z = J ẑ` (spec: the
/// `let z := jMatrix Φ base n zDigits *ᵥ resp.zDec` of `relOut`,
/// `QuadEval/Reduction.lean:267`).
///
/// Mirrors ArkLib's `jMatrix` applied to `ẑ`.
///
/// Collapsed through [`crate::gadget::gadget_mul_z`]; `jMatrix` itself is ~2.5
/// TB at these parameters and is never materialized.
pub fn j_mul(z_dec: &PolyVec) -> PolyVec {
    let n: usize = params::MESSAGE_ROWS * params::GADGET_DIGITS;
    gadget::gadget_mul_z(n, z_dec)
}

// @genesis b984c53 2026-09-04 — quadeval::rel_out
/// The verifier's Eq. (20) checks with the `ℓ∞` **ball** range condition
/// (spec: `relOut`, `QuadEval/Reduction.lean:258`).
///
/// Mirrors ArkLib's `relOut` at the values [`params`] fixes.
///
/// A decision procedure for what the specification states as a `Set` of
/// `Prop`s, so its equivalence statement is an iff (module header). The six
/// conjuncts, in the specification's order: `D ŵ = v`; `B flatten(t̂) = u`;
/// `bᵀ G ŵ = y`; `(cᵀ ⊗ G₁) ŵ = aᵀ G z`; `(cᵀ ⊗ G_{n_A}) t̂ = A z`; and three
/// `‖·‖∞ ≤ γ` at [`params::CHAIN_GAMMA`] -- **not** [`params::GAMMA`], which is
/// the weak-opening `γ̄ = b` on a different relation.
///
/// Branchless: every conjunct is evaluated. That costs the `2^23`-order work
/// of the two mat-vecs whatever the answer, and it is the shape the proof
/// mirrors.
pub fn rel_out(
    pp: &PublicParamsD,
    stmt: &QuadEvalStatement,
    v: &PolyVec,
    c: &PolyVec,
    resp: &QuadEvalResponse,
) -> bool {
    let gamma: u64 = params::CHAIN_GAMMA;
    let z: PolyVec = j_mul(resp.z_dec());
    let flat: PolyVec = linalg::flatten_blocks(resp.inner_dec());

    let c1: bool = pp.d_matrix().mat_vec_mul(resp.carrier_dec()).equals(v);
    let c2: bool = pp
        .inner()
        .outer_matrix()
        .mat_vec_mul(&flat)
        .equals(stmt.u());
    let c3: bool = stmt
        .bvec()
        .dot(&gadget::gadget_mul(params::BLOCKS, resp.carrier_dec()))
        .equals(stmt.y());
    let c4: bool = tensor_g1(c, resp.carrier_dec()).equals(
        &stmt
            .avec()
            .dot(&gadget::gadget_mul(params::MESSAGE_ROWS, &z)),
    );
    let c5: bool = tensor_g(params::INNER_ROWS, c, resp.inner_dec())
        .equals(&pp.inner().inner_matrix().mat_vec_mul(&z));
    let c6: bool = crate::commit::vec_l_infty_norm(resp.carrier_dec()) <= gamma
        && crate::commit::vec_l_infty_norm(&flat) <= gamma
        && crate::commit::vec_l_infty_norm(resp.z_dec()) <= gamma;

    c1 && c2 && c3 && c4 && c5 && c6
}

// @genesis b984c53 2026-09-04 — quadeval::paper_rel_out
/// The same checks with the paper's exact **box** range condition (spec:
/// `paperRelOut`, `QuadEval/Reduction.lean:335`).
///
/// Mirrors ArkLib's `paperRelOut` at the values [`params`] fixes.
///
/// Differs from [`rel_out`] only in c6: three [`vec_in_sb`] in place of the
/// three `ℓ∞` balls. `paperRelOut ⊆ relOut` holds under `b/2 ≤ γ`
/// (`paperRelOut_subset_relOut`, `:367`), which is `8 ≤ 15` here -- so this is
/// the strictly stronger check, and the honest balanced digits satisfy it
/// exactly.
pub fn paper_rel_out(
    pp: &PublicParamsD,
    stmt: &QuadEvalStatement,
    v: &PolyVec,
    c: &PolyVec,
    resp: &QuadEvalResponse,
) -> bool {
    let z: PolyVec = j_mul(resp.z_dec());
    let flat: PolyVec = linalg::flatten_blocks(resp.inner_dec());

    let c1: bool = pp.d_matrix().mat_vec_mul(resp.carrier_dec()).equals(v);
    let c2: bool = pp
        .inner()
        .outer_matrix()
        .mat_vec_mul(&flat)
        .equals(stmt.u());
    let c3: bool = stmt
        .bvec()
        .dot(&gadget::gadget_mul(params::BLOCKS, resp.carrier_dec()))
        .equals(stmt.y());
    let c4: bool = tensor_g1(c, resp.carrier_dec()).equals(
        &stmt
            .avec()
            .dot(&gadget::gadget_mul(params::MESSAGE_ROWS, &z)),
    );
    let c5: bool = tensor_g(params::INNER_ROWS, c, resp.inner_dec())
        .equals(&pp.inner().inner_matrix().mat_vec_mul(&z));
    let c6: bool = vec_in_sb(resp.carrier_dec()) && vec_in_sb(&flat) && vec_in_sb(resp.z_dec());

    c1 && c2 && c3 && c4 && c5 && c6
}

// @genesis 62cf3c8 2026-09-09 — quadeval::PolyEvalStatement
/// The composed chain's **input statement**, at the polynomial level (spec:
/// `PolyEvalStatement`, `QuadEval/Bridge.lean:108`).
///
/// Mirrors ArkLib's `PolyEvalStatement`.
///
/// Lives in this module because its ArkLib home is `QuadEval/Bridge.lean` and
/// its only computation is [`to_quad_eval_statement`]; the four adapter rows of
/// `Composition.lean` each sit with the link they adapt rather than in a module
/// of their own.
///
/// The evaluation point travels **pre-split** as the two halves `xl` (the first
/// `r` variables, indexing matrix rows) and `xh` (the last `m` variables,
/// indexing columns), which is the specification's own choice: it "avoids
/// `take`/`drop` casts", and `xl ++ xh` recovers the paper's point. Their
/// lengths are `ML_VARS_LOW` and `ML_VARS_HIGH`, which travel as `_spec`
/// hypotheses since Aeneas cannot see a privacy boundary.
pub struct PolyEvalStatement {
    u: PolyVec,
    xl: PolyVec,
    xh: PolyVec,
    y: Rq,
}

impl PolyEvalStatement {
    // @genesis 62cf3c8 2026-09-09 — quadeval::PolyEvalStatement::new
    /// Bundle the outer commitment, the two point halves and the claim.
    pub fn new(u: PolyVec, xl: PolyVec, xh: PolyVec, y: Rq) -> PolyEvalStatement {
        PolyEvalStatement { u, xl, xh, y }
    }

    // @genesis b984c53 2026-09-04 — quadeval::PolyEvalStatement::u
    /// The outer commitment `u`.
    pub fn u(&self) -> &PolyVec {
        &self.u
    }

    // @genesis 62cf3c8 2026-09-09 — quadeval::PolyEvalStatement::xl
    /// The low/outer point half `x₁ … x_r`.
    pub fn xl(&self) -> &PolyVec {
        &self.xl
    }

    // @genesis 62cf3c8 2026-09-09 — quadeval::PolyEvalStatement::xh
    /// The high/inner point half `x_{r+1} … x_l`.
    pub fn xh(&self) -> &PolyVec {
        &self.xh
    }

    // @genesis b984c53 2026-09-04 — quadeval::PolyEvalStatement::y
    /// The claimed evaluation `y = f(xl ++ xh)`.
    pub fn y(&self) -> &Rq {
        &self.y
    }
}

// @genesis 62cf3c8 2026-09-09 — quadeval::to_quad_eval_statement
/// The bridge: reinterpret the polynomial-level statement as a
/// `QuadEvalStatement` by taking the Eq. (12) bases to be the monomial tensor
/// bases of the two point halves (spec: `toQuadEvalStatement`,
/// `QuadEval/Bridge.lean:124`).
///
/// Mirrors ArkLib's `toQuadEvalStatement`.
///
/// **The halves cross, and that is the whole content of this function**:
/// `avec := mb(xh)` (inner, the *high* half, indexing columns) and
/// `bvec := mb(xl)` (outer, the *low* half, indexing rows). At this crate's
/// parameters `ML_VARS_LOW = ML_VARS_HIGH = 10`, so both bases have `1024`
/// entries and a swap would still typecheck and still run -- it would simply
/// compute the transpose of the intended form. Nothing but a value test can
/// catch that, which is what
/// `quadeval_semantics.rs`'s `the_bridge_bases_reproduce_the_polynomial_evaluation`
/// is for, and why it uses *unequal* toy widths.
///
/// The row is zero-round and its verifier is a `ReduceClaim` head -- pure, with
/// no challenge and nothing to decide (`bridgeVerifier`, `:135`). So there is
/// no `bridge_check` to translate: the statement map *is* the row.
pub fn to_quad_eval_statement(s: &PolyEvalStatement) -> QuadEvalStatement {
    let avec: PolyVec = crate::evalsplit::monomial_basis(s.xh());
    let bvec: PolyVec = crate::evalsplit::monomial_basis(s.xl());
    QuadEvalStatement::new(s.u().copy(), avec, bvec, s.y().copy())
}

// @genesis 8d0cd29 2026-09-09 — quadeval::rlin_cw
/// The carrier-block width `cW = 2^r · messageDigits` — the `ŵ` columns
/// (spec: `rlinCW`, `RingSwitch/Rlin.lean:84`).
///
/// Mirrors `rlinCW`.
///
/// `blocks` is `2^r` already expanded, so no power is formed here; the
/// specification writes the exponent because it is generic in `r`.
pub fn rlin_cw(blocks: usize, message_digits: usize) -> usize {
    blocks * message_digits
}

// @genesis 8d0cd29 2026-09-09 — quadeval::rlin_ct
/// The inner-block width `cT = 2^r · (innerRows · innerDigits)` — the
/// `flatten t̂` columns (spec: `rlinCT`, `:86`).
///
/// Mirrors `rlinCT`.
pub fn rlin_ct(blocks: usize, inner_rows: usize, inner_digits: usize) -> usize {
    blocks * (inner_rows * inner_digits)
}

// @genesis 8d0cd29 2026-09-09 — quadeval::rlin_cz
/// The response-block width `cZ = 2^m · messageDigits · zDigits` — the `ẑ`
/// columns (spec: `rlinCZ`, `:88`).
///
/// Mirrors `rlinCZ`.
pub fn rlin_cz(message_rows: usize, message_digits: usize, z_digits: usize) -> usize {
    message_rows * message_digits * z_digits
}

// @genesis 8d0cd29 2026-09-09 — quadeval::rlin_cols
/// The column count `μ` of the Eq. (20) block system (spec: `rlinCols`, `:75`).
///
/// Mirrors `rlinCols`.
///
/// The parenthesisation is the specification's, which says of itself
/// "Associativity fixed once, here" — so it is mirrored rather than
/// normalised, because `a + (b + c)` and `(a + b) + c` are the same number and
/// *not* the same extracted term, and the proof rewrites one of them.
pub fn rlin_cols(
    blocks: usize,
    message_rows: usize,
    message_digits: usize,
    inner_rows: usize,
    inner_digits: usize,
    z_digits: usize,
) -> usize {
    rlin_cw(blocks, message_digits)
        + (rlin_ct(blocks, inner_rows, inner_digits)
            + rlin_cz(message_rows, message_digits, z_digits))
}

// @genesis 8d0cd29 2026-09-09 — quadeval::rlin_rows
/// The row count `n` of the Eq. (20) block system (spec: `rlinRows`, `:80`).
///
/// Mirrors `rlinRows`.
///
/// `c1 ++ (c2 ++ (c3 ++ (c4 ++ c5)))`: `dRows` commitment rows, `outerRows`
/// outer rows, one row each for c3 and c4, and `innerRows` for c5. Same
/// associativity note as [`rlin_cols`].
pub fn rlin_rows(inner_rows: usize, outer_rows: usize, d_rows: usize) -> usize {
    d_rows + (outer_rows + (1 + (1 + inner_rows)))
}

// @genesis 8d0cd29 2026-09-09 — quadeval::unflatten
/// Un-flatten a row-major block vector into blocks — the inverse of
/// `linalg::flatten_blocks` (spec: `unflatten`, `RingSwitch/Rlin.lean:113`).
///
/// Mirrors `unflatten`.
///
/// Entry `w` of block `i` is entry `width·i + w` of the input, which is
/// `flatten_blocks`' own convention read backwards; the round trip both ways is
/// upstream's `flattenBlocks_unflatten` / `unflatten_flattenBlocks`.
pub fn unflatten(v: &PolyVec, width: usize) -> Vec<PolyVec> {
    let total: usize = v.len();
    let mut out: Vec<PolyVec> = Vec::new();
    let mut base: usize = 0;
    while base < total {
        let mut block: Vec<Rq> = Vec::new();
        let mut w: usize = 0;
        while w < width {
            block.push(v.get(base + w).copy());
            w += 1;
        }
        out.push(PolyVec::new(block));
        base += width;
    }
    out
}

// @genesis 8d0cd29 2026-09-09 — quadeval::tensor_g_matrix
/// The c5 block matrix `(cᵀ ⊗ G_k)` (spec: `tensorGMatrix`,
/// `RingSwitch/Rlin.lean:132`).
///
/// Mirrors `tensorGMatrix`.
///
/// Entry `(p, flat)` is `cᵢ · G_k(p, e)` for `(i, e) = finProdFinEquiv.symm
/// flat`, and `G_k(p, e)` is nonzero only when `e / digits = p` — which, with
/// the column walked as `(i, e, f)` below, is the plain `e == p` test. So the
/// matrix is materialized (it is a `PolyMatrix`, and `relRlin` applies it) but
/// its entries come from the gadget's structure, never from a materialized
/// `G`: the [`crate::gadget::gadget_transpose_mul`] convention.
///
/// `k × blocks·(k·digits)` = `1 × 8192` at the pinned parameters, which is why
/// this one is holdable where c4's product is not.
pub fn tensor_g_matrix(k: usize, digits: usize, c: &PolyVec) -> PolyMatrix {
    let blocks: usize = c.len();
    let mut rows: Vec<PolyVec> = Vec::new();
    let mut p: usize = 0;
    while p < k {
        let mut row: Vec<Rq> = Vec::new();
        let mut i: usize = 0;
        while i < blocks {
            let mut e: usize = 0;
            while e < k {
                let mut f: usize = 0;
                while f < digits {
                    let entry: Rq = if e == p {
                        c.get(i).scalar_mul(gadget::base_pow(f))
                    } else {
                        Rq::zero()
                    };
                    row.push(entry);
                    f += 1;
                }
                e += 1;
            }
            i += 1;
        }
        rows.push(PolyVec::new(row));
        p += 1;
    }
    PolyMatrix::new(rows)
}

// @genesis 8d0cd29 2026-09-09 — quadeval::stack
/// Witness stacking `ζ = ŵ ++ (flatten t̂ ++ ẑ)` (spec: `stack`,
/// `RingSwitch/Rlin.lean:158`).
///
/// Mirrors `stack`.
///
/// The adapter's witness map. Its length is [`rlin_cols`] by construction, and
/// the block order is what [`unstack`] and every column block of
/// [`rlin_stmt`] agree on.
pub fn stack(resp: &QuadEvalResponse) -> PolyVec {
    let flat: PolyVec = linalg::flatten_blocks(resp.inner_dec());
    let mut out: Vec<Rq> = Vec::new();
    let mut i: usize = 0;
    while i < resp.carrier_dec().len() {
        out.push(resp.carrier_dec().get(i).copy());
        i += 1;
    }
    let mut j: usize = 0;
    while j < flat.len() {
        out.push(flat.get(j).copy());
        j += 1;
    }
    let mut k: usize = 0;
    while k < resp.z_dec().len() {
        out.push(resp.z_dec().get(k).copy());
        k += 1;
    }
    PolyVec::new(out)
}

// @genesis 8d0cd29 2026-09-09 — quadeval::unstack
/// Witness unstacking: split `ζ` back into `(ŵ, t̂, ẑ)` (spec: `unstack`,
/// `RingSwitch/Rlin.lean:166`).
///
/// Mirrors `unstack`.
///
/// Inverse to [`stack`]. The three widths are arguments because the split is
/// the `rlinCols` layout and nothing in `ζ` records where the boundaries are —
/// the specification recovers them from the type indices, which erase.
pub fn unstack(zeta: &PolyVec, cw: usize, ct: usize, inner_width: usize) -> QuadEvalResponse {
    let mut carrier: Vec<Rq> = Vec::new();
    let mut i: usize = 0;
    while i < cw {
        carrier.push(zeta.get(i).copy());
        i += 1;
    }
    let mut middle: Vec<Rq> = Vec::new();
    let mut j: usize = 0;
    while j < ct {
        middle.push(zeta.get(cw + j).copy());
        j += 1;
    }
    let mut z: Vec<Rq> = Vec::new();
    let mut k: usize = cw + ct;
    while k < zeta.len() {
        z.push(zeta.get(k).copy());
        k += 1;
    }
    QuadEvalResponse::new(
        PolyVec::new(carrier),
        unflatten(&PolyVec::new(middle), inner_width),
        PolyVec::new(z),
    )
}

// @genesis 8d0cd29 2026-09-09 — quadeval::rlin_stmt
/// **The `R^lin` statement assembly**: build the Eq. (20) block matrix and
/// right-hand side from QuadEval's output `(stmt, v, c)` (spec: `rlinStmt`,
/// `RingSwitch/Rlin.lean:205`).
///
/// Mirrors `rlinStmt`.
///
/// # This body is a documented exception to the freeze-the-naive-form rule
///
/// The specification writes c4's `ẑ` block as
/// `(matMul G_{2^m} J).transpose *ᵥ a` — a literal matrix product. At the
/// pinned parameters `G·J` is `1024 × 40960` `Rq` = **320 GiB**, while the
/// answer it contracts down to is a `40960`-entry vector = 320 MiB: a 1024×
/// overhead, one factor for every row of `G` the contraction discards. There
/// is no width at these parameters where the specification's own shape runs,
/// so the naive form cannot be benched, cannot have a `case!` digest computed
/// on it, and would carry spec debt for a body that never executes — all three
/// parts of `op-genesis`' test. **Genesis therefore holds the associativity
/// reshape `(G·J)ᵀa = Jᵀ(Gᵀa)`**, whose intermediate is `8192` `Rq` = 64 MiB,
/// approved and recorded 2026-09-09 (NOTES.md § "Decision: the `R^lin`
/// adapter's genesis holds the reshaped form"). A `vs genesis` figure for this
/// item measures distance from the *reshaped* form.
///
/// Two things that are **not** part of that exception, so they are not
/// optimizations here. Every gadget-matrix application goes through
/// [`crate::gadget::gadget_transpose_mul`], which reads the matrix's structure
/// instead of materializing it — the convention [`j_mul`] already froze, and
/// faithful because `gadgetMul` is *defined* as `gadgetMatrix *ᵥ v`. And c5's
/// `matMul A J` is the same convention rather than a second reshape: `J`'s
/// columns have one nonzero each, so `(A·J)[p]` is exactly `Jᵀ` applied to row
/// `p` of `A`, which is why the same helper serves both blocks.
///
/// # Scale
///
/// `M` is `rlinRows × rlinCols` = `5 × 57 344` `Rq` = **2.2 GiB** at the
/// pinned parameters, independent of `ring::mul`. Its bench row is excluded and
/// its semantics test is REDUCED for that reason alone.
// Eleven arguments and a body over a hundred lines, both forced, both recorded
// rather than worked around. The six dimensions travel as arguments because the
// freeze exception's toy-width oracle depends on it -- bundling them into a
// carrier would put a struct between the specification's own parameters and the
// body, and the oracle needs to call this at `messageDigits != zDigits`. The
// body is long because it assembles five row blocks over three column blocks
// with **no closures**: Aeneas does not support them, so every block is its own
// explicit loop and the zero padding is written out.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
pub fn rlin_stmt(
    pp: &PublicParamsD,
    stmt: &QuadEvalStatement,
    v: &PolyVec,
    c: &PolyVec,
    gamma: u64,
    blocks: usize,
    message_rows: usize,
    message_digits: usize,
    inner_rows: usize,
    inner_digits: usize,
    z_digits: usize,
) -> crate::ringswitch::RlinStatement {
    let cw: usize = rlin_cw(blocks, message_digits);
    let ct: usize = rlin_ct(blocks, inner_rows, inner_digits);
    let cz: usize = rlin_cz(message_rows, message_digits, z_digits);
    let inner_cols: usize = message_rows * message_digits;

    // c4's `ẑ` block, by the approved reshape: `Jᵀ(Gᵀ a)`, never `(G·J)ᵀ a`.
    let g_a: PolyVec = gadget::gadget_transpose_mul(message_rows, message_digits, stmt.avec());
    let jt_g_a: PolyVec = gadget::gadget_transpose_mul(inner_cols, z_digits, &g_a);

    let g_b: PolyVec = gadget::gadget_transpose_mul(blocks, message_digits, stmt.bvec());
    let g_c: PolyVec = gadget::gadget_transpose_mul(blocks, message_digits, c);
    let tensor: PolyMatrix = tensor_g_matrix(inner_rows, inner_digits, c);

    let mut out: Vec<PolyVec> = Vec::new();

    // c1: [ D | 0 | 0 ]
    let mut i: usize = 0;
    while i < pp.d_matrix().rows() {
        let mut row: Vec<Rq> = Vec::new();
        let mut k: usize = 0;
        while k < cw {
            row.push(pp.d_matrix().row(i).get(k).copy());
            k += 1;
        }
        let mut z: usize = 0;
        while z < ct + cz {
            row.push(Rq::zero());
            z += 1;
        }
        out.push(PolyVec::new(row));
        i += 1;
    }

    // c2: [ 0 | B | 0 ]
    let mut i2: usize = 0;
    while i2 < pp.inner().outer_matrix().rows() {
        let mut row: Vec<Rq> = Vec::new();
        let mut z: usize = 0;
        while z < cw {
            row.push(Rq::zero());
            z += 1;
        }
        let mut k: usize = 0;
        while k < ct {
            row.push(pp.inner().outer_matrix().row(i2).get(k).copy());
            k += 1;
        }
        let mut z2: usize = 0;
        while z2 < cz {
            row.push(Rq::zero());
            z2 += 1;
        }
        out.push(PolyVec::new(row));
        i2 += 1;
    }

    // c3: [ (G_{2^r})ᵀ b | 0 | 0 ]
    let mut row3: Vec<Rq> = Vec::new();
    let mut k3: usize = 0;
    while k3 < cw {
        row3.push(g_b.get(k3).copy());
        k3 += 1;
    }
    let mut z3: usize = 0;
    while z3 < ct + cz {
        row3.push(Rq::zero());
        z3 += 1;
    }
    out.push(PolyVec::new(row3));

    // c4: [ (G_{2^r})ᵀ c | 0 | −Jᵀ((G_{2^m})ᵀ a) ]
    let mut row4: Vec<Rq> = Vec::new();
    let mut k4: usize = 0;
    while k4 < cw {
        row4.push(g_c.get(k4).copy());
        k4 += 1;
    }
    let mut z4: usize = 0;
    while z4 < ct {
        row4.push(Rq::zero());
        z4 += 1;
    }
    let mut k4z: usize = 0;
    while k4z < cz {
        row4.push(jt_g_a.get(k4z).neg());
        k4z += 1;
    }
    out.push(PolyVec::new(row4));

    // c5: [ 0 | (cᵀ ⊗ G_{n_A}) | −(A J) ]
    let mut p: usize = 0;
    while p < inner_rows {
        let mut row: Vec<Rq> = Vec::new();
        let mut z: usize = 0;
        while z < cw {
            row.push(Rq::zero());
            z += 1;
        }
        let mut k: usize = 0;
        while k < ct {
            row.push(tensor.row(p).get(k).copy());
            k += 1;
        }
        let aj: PolyVec =
            gadget::gadget_transpose_mul(inner_cols, z_digits, pp.inner().inner_matrix().row(p));
        let mut kz: usize = 0;
        while kz < cz {
            row.push(aj.get(kz).neg());
            kz += 1;
        }
        out.push(PolyVec::new(row));
        p += 1;
    }

    // yvec = (v, u, y, 0, 0)
    let mut y: Vec<Rq> = Vec::new();
    let mut a: usize = 0;
    while a < v.len() {
        y.push(v.get(a).copy());
        a += 1;
    }
    let mut b: usize = 0;
    while b < stmt.u().len() {
        y.push(stmt.u().get(b).copy());
        b += 1;
    }
    y.push(stmt.y().copy());
    y.push(Rq::zero());
    let mut e: usize = 0;
    while e < inner_rows {
        y.push(Rq::zero());
        e += 1;
    }

    crate::ringswitch::RlinStatement::new(PolyMatrix::new(out), PolyVec::new(y), gamma)
}

// @genesis c591e87 2026-09-17 — quadeval::rlin_row
/// Row `i` of `R^lin`'s matrix `M`, built **alone** (Stage 6 candidate T1b,
/// first increment).
///
/// `rlin_stmt` below materialises all `rlinRows × rlinCols` entries at once,
/// which at the pin is `5 × 57 344` ring elements — **2.2 GiB**, memory wall W2
/// (`PLAN_STAGE6.md` § I6). Every consumer, though, walks one row at a time:
/// `ringswitch::c_row_sum` takes the row index `i` as a parameter, and the
/// verifier's `α`-side walks rows too. So the dense matrix is a materialisation
/// nothing actually needs.
///
/// This is the piece both paths need in order to stop needing it: the same
/// blocks `rlin_stmt` builds, emitted one row at a time.
///
/// # Why a row and not an entry
///
/// An entry-at-`(i, j)` form looks tempting and is a trap. c5's `z`-block is
/// `−(A·J)`, whose row is `gadget_transpose_mul(inner_cols, z_digits, …)` — a
/// vector derived from one row of `A` in `O(cz)` work. `rlin_stmt` computes it
/// once per row inside the row loop; an entry-shaped interface would recompute
/// it per access, `O(cz²) ≈ 1.7·10^9` operations per row. Row-shaped keeps that
/// derivation where it belongs, computed once and consumed `cz` times.
///
/// # What this does and does not claim
///
/// It does **not** remove W2. The wall falls only when no live path
/// materialises `M`, and today both the lift and the verifier call
/// `rlin_stmt` (the profile's `rlin_stmt (verifier assembles it too)` line).
/// This is additive: nothing calls it yet, and
/// `quadeval_semantics::rlin_row_agrees_with_rlin_stmt` is what says it is the
/// same matrix, row by row.
#[allow(clippy::too_many_arguments)]
pub fn rlin_row(
    pp: &PublicParamsD,
    stmt: &QuadEvalStatement,
    v: &PolyVec,
    c: &PolyVec,
    blocks: usize,
    message_rows: usize,
    message_digits: usize,
    inner_rows: usize,
    inner_digits: usize,
    z_digits: usize,
    i: usize,
) -> PolyVec {
    let cw: usize = rlin_cw(blocks, message_digits);
    let ct: usize = rlin_ct(blocks, inner_rows, inner_digits);
    let cz: usize = rlin_cz(message_rows, message_digits, z_digits);
    let inner_cols: usize = message_rows * message_digits;
    let d_rows: usize = pp.d_matrix().rows();
    let b_rows: usize = pp.inner().outer_matrix().rows();

    let mut row: Vec<Rq> = Vec::with_capacity(cw + ct + cz);
    if i < d_rows {
        // c1: [ D | 0 | 0 ]
        let mut k: usize = 0;
        while k < cw {
            row.push(pp.d_matrix().row(i).get(k).copy());
            k += 1;
        }
        let mut z: usize = 0;
        while z < ct + cz {
            row.push(Rq::zero());
            z += 1;
        }
    } else if i < d_rows + b_rows {
        // c2: [ 0 | B | 0 ]
        let p: usize = i - d_rows;
        let mut z: usize = 0;
        while z < cw {
            row.push(Rq::zero());
            z += 1;
        }
        let mut k: usize = 0;
        while k < ct {
            row.push(pp.inner().outer_matrix().row(p).get(k).copy());
            k += 1;
        }
        let mut z2: usize = 0;
        while z2 < cz {
            row.push(Rq::zero());
            z2 += 1;
        }
    } else if i == d_rows + b_rows {
        // c3: [ (G_{2^r})ᵀ b | 0 | 0 ]
        let g_b: PolyVec = gadget::gadget_transpose_mul(blocks, message_digits, stmt.bvec());
        let mut k: usize = 0;
        while k < cw {
            row.push(g_b.get(k).copy());
            k += 1;
        }
        let mut z: usize = 0;
        while z < ct + cz {
            row.push(Rq::zero());
            z += 1;
        }
    } else if i == d_rows + b_rows + 1 {
        // c4: [ (G_{2^r})ᵀ c | 0 | −Jᵀ((G_{2^m})ᵀ a) ]
        let g_c: PolyVec = gadget::gadget_transpose_mul(blocks, message_digits, c);
        let g_a: PolyVec =
            gadget::gadget_transpose_mul(message_rows, message_digits, stmt.avec());
        let jt_g_a: PolyVec = gadget::gadget_transpose_mul(inner_cols, z_digits, &g_a);
        let mut k: usize = 0;
        while k < cw {
            row.push(g_c.get(k).copy());
            k += 1;
        }
        let mut z: usize = 0;
        while z < ct {
            row.push(Rq::zero());
            z += 1;
        }
        let mut kz: usize = 0;
        while kz < cz {
            row.push(jt_g_a.get(kz).neg());
            kz += 1;
        }
    } else {
        // c5: [ 0 | (cᵀ ⊗ G_{n_A}) | −(A J) ]
        let p: usize = i - (d_rows + b_rows + 2);
        let tensor: PolyMatrix = tensor_g_matrix(inner_rows, inner_digits, c);
        let aj: PolyVec =
            gadget::gadget_transpose_mul(inner_cols, z_digits, pp.inner().inner_matrix().row(p));
        let mut z: usize = 0;
        while z < cw {
            row.push(Rq::zero());
            z += 1;
        }
        let mut k: usize = 0;
        while k < ct {
            row.push(tensor.row(p).get(k).copy());
            k += 1;
        }
        let mut kz: usize = 0;
        while kz < cz {
            row.push(aj.get(kz).neg());
            kz += 1;
        }
    }
    PolyVec::new(row)
}

// @genesis 964ae4b 2026-09-17 — quadeval::honest_z_from_raw
/// `z = Σᵢ cᵢ •ᵥ sᵢ` from the **raw** message, decomposing one block at a time
/// (spec: the same `honestZ` [`honest_z`] mirrors, composed with
/// `gadgetDecompose`).
///
/// [`honest_z`] takes the decomposed message, which is `BLOCKS · MESSAGE_ROWS ·
/// GADGET_DIGITS` ring elements = **68.7 GiB** at the paper's parameters. This
/// variant takes the raw message and rebuilds `sᵢ` per block, so the resident
/// decomposed state is one block: 8192 ring elements, **64 MiB**. Paired with
/// [`crate::commit::commit_streamed`], the prover never holds the full
/// decomposition at all, and the price is that `gadget_decompose` runs a second
/// time over the raw input.
///
/// The unsigned gadget, matching what `commit::generate_decomps` produces. The
/// balanced path has its own decomposition and would need its own variant.
pub fn honest_z_from_raw(raw: &Vec<PolyVec>, c: &PolyVec) -> PolyVec {
    let blocks: usize = raw.len();
    let width: usize = params::MESSAGE_ROWS * params::GADGET_DIGITS;
    let mut acc: Vec<Rq> = Vec::with_capacity(width);
    let mut z: usize = 0;
    while z < width {
        acc.push(Rq::zero());
        z += 1;
    }
    let mut i: usize = 0;
    while i < blocks {
        // one block's decomposition, alive for one iteration
        let s: PolyVec = gadget::gadget_decompose(&raw[i]);
        let ci: &Rq = c.get(i);
        match crate::ring::classify_short(ci) {
            Some(desc) => {
                let mut j: usize = 0;
                while j < width {
                    crate::ring::mul_short_add_into(&desc, s.get(j), &mut acc[j]);
                    j += 1;
                }
            }
            None => {
                let scaled: PolyVec = s.scalar_mul(ci);
                let mut j: usize = 0;
                while j < width {
                    acc[j] = acc[j].add(scaled.get(j));
                    j += 1;
                }
            }
        }
        i += 1;
    }
    PolyVec::new(acc)
}

// @genesis 964ae4b 2026-09-17 — quadeval::carrier_from_raw
/// The carrier `w` from the **raw** message (spec: the same `carrier`
/// [`carrier`] mirrors, composed with `gadgetDecompose`).
///
/// This one needs no decomposition at all, and that is the point:
/// [`carrier_entry`] recomposes its argument with `gadget_mul` before dotting
/// with `a`, and `gadget_mul ∘ gadget_decompose` is the identity
/// (`Scheme.gadget_round_trip`). So `carrier a (G⁻¹ m) = a · m`, and the
/// decomposition the streamed prover would have rebuilt cancels instead.
///
/// It is therefore not merely a memory win over `carrier(a, s)`: it removes the
/// `BLOCKS` gadget recompositions as well.
pub fn carrier_from_raw(a: &PolyVec, raw: &Vec<PolyVec>) -> PolyVec {
    let blocks: usize = raw.len();
    let mut out: Vec<Rq> = Vec::new();
    let mut i: usize = 0;
    while i < blocks {
        out.push(a.dot(&raw[i]));
        i += 1;
    }
    PolyVec::new(out)
}

// @genesis 964ae4b 2026-09-17 — quadeval::carrier_commit_from_raw
/// `v = D · G⁻¹(w)` from the raw message: [`carrier_commit`] without the
/// decomposed message.
pub fn carrier_commit_from_raw(
    d_matrix: &PolyMatrix,
    a: &PolyVec,
    raw: &Vec<PolyVec>,
) -> PolyVec {
    let w: PolyVec = carrier_from_raw(a, raw);
    let what: PolyVec = gadget::balanced_gadget_decompose(&w);
    d_matrix.mat_vec_mul(&what)
}

// @genesis fa135b2 2026-09-17 — quadeval::carrier_decomp_from_raw
/// `ŵ = G⁻¹(w)` from the raw message: [`carrier_decomp`] without the decomposed
/// message.
pub fn carrier_decomp_from_raw(a: &PolyVec, raw: &Vec<PolyVec>) -> PolyVec {
    let w: PolyVec = carrier_from_raw(a, raw);
    gadget::balanced_gadget_decompose(&w)
}

// @genesis fa135b2 2026-09-17 — quadeval::honest_compute_v_from_raw
/// The prover's round-0 message `v = D ŵ` from the **raw** message (spec: the
/// same `honestComputeV` [`honest_compute_v`] mirrors, composed with
/// `gadgetDecompose`).
///
/// What [`chain_open`](crate::chain::chain_open) calls, so that the honest
/// prover never holds the decomposed message. The decomposition cancels here
/// rather than streaming: see [`carrier_from_raw`].
pub fn honest_compute_v_from_raw(
    pp: &PublicParamsD,
    stmt: &QuadEvalStatement,
    raw: &Vec<PolyVec>,
) -> PolyVec {
    carrier_commit_from_raw(pp.d_matrix(), stmt.avec(), raw)
}

// @genesis fa135b2 2026-09-17 — quadeval::honest_compute_resp_from_raw
/// The honest output witness from the **raw** message (spec: the same
/// `honestComputeResp` [`honest_compute_resp`] mirrors, composed with
/// `gadgetDecompose`).
///
/// The second half of the streamed prover: `honest_z_from_raw` rebuilds one
/// block's `sᵢ` at a time, and `carrier_decomp_from_raw` needs no decomposition
/// at all. With [`honest_compute_v_from_raw`] and
/// [`crate::commit::commit_streamed`], nothing on the honest path holds the
/// 68.7 GiB `Decomp.message`.
pub fn honest_compute_resp_from_raw(
    stmt: &QuadEvalStatement,
    raw: &Vec<PolyVec>,
    inner_decomp: &Vec<PolyVec>,
    c: &PolyVec,
) -> QuadEvalResponse {
    let carrier_dec: PolyVec = carrier_decomp_from_raw(stmt.avec(), raw);
    let z: PolyVec = honest_z_from_raw(raw, c);
    let z_dec: PolyVec = gadget::bounded_z_gadget_decompose(&z);
    let mut inner: Vec<PolyVec> = Vec::new();
    let mut i: usize = 0;
    while i < inner_decomp.len() {
        inner.push(inner_decomp[i].copy());
        i += 1;
    }
    QuadEvalResponse::new(carrier_dec, inner, z_dec)
}

// @genesis af3f7d5 2026-09-18 — quadeval::honest_z_from_raw_32
// ---------------------------------------------------------------------------
// FROZEN 2026-09-18 -- candidate T29, the compact raw-message carrier
// The FIRST translation, copied verbatim from hachi/src. Do not edit.
// ---------------------------------------------------------------------------
/// [`honest_z_from_raw`] over the compact raw carrier.
pub fn honest_z_from_raw_32(raw: &Vec<linalg::RawVec32>, c: &PolyVec) -> PolyVec {
    let blocks: usize = raw.len();
    let width: usize = params::MESSAGE_ROWS * params::GADGET_DIGITS;
    let mut acc: Vec<Rq> = Vec::with_capacity(width);
    let mut z: usize = 0;
    while z < width {
        acc.push(Rq::zero());
        z += 1;
    }
    let mut i: usize = 0;
    while i < blocks {
        let block: PolyVec = raw[i].expand();
        let s: PolyVec = gadget::gadget_decompose(&block);
        let ci: &Rq = c.get(i);
        match crate::ring::classify_short(ci) {
            Some(desc) => {
                let mut j: usize = 0;
                while j < width {
                    crate::ring::mul_short_add_into(&desc, s.get(j), &mut acc[j]);
                    j += 1;
                }
            }
            None => {
                let scaled: PolyVec = s.scalar_mul(ci);
                let mut j: usize = 0;
                while j < width {
                    acc[j] = acc[j].add(scaled.get(j));
                    j += 1;
                }
            }
        }
        i += 1;
    }
    PolyVec::new(acc)
}

// @genesis af3f7d5 2026-09-18 — quadeval::carrier_from_raw_32
/// [`carrier_from_raw`] over the compact raw carrier.
pub fn carrier_from_raw_32(a: &PolyVec, raw: &Vec<linalg::RawVec32>) -> PolyVec {
    let blocks: usize = raw.len();
    let mut rows: Vec<PolyVec> = Vec::new();
    rows.push(a.copy());
    let am: PolyMatrix = PolyMatrix::new(rows);
    let prep: crate::linalg::PreparedMatrix = am.prepare();
    let mut out: Vec<Rq> = Vec::new();
    let mut i: usize = 0;
    while i < blocks {
        let block: PolyVec = raw[i].expand();
        let r: PolyVec = prep.apply(&block);
        out.push(r.get(0).copy());
        i += 1;
    }
    PolyVec::new(out)
}

// @genesis af3f7d5 2026-09-18 — quadeval::carrier_decomp_from_raw_32
/// [`carrier_decomp_from_raw`] over the compact raw carrier.
pub fn carrier_decomp_from_raw_32(a: &PolyVec, raw: &Vec<linalg::RawVec32>) -> PolyVec {
    let w: PolyVec = carrier_from_raw_32(a, raw);
    gadget::balanced_gadget_decompose(&w)
}

// @genesis af3f7d5 2026-09-18 — quadeval::carrier_commit_from_raw_32
/// [`carrier_commit_from_raw`] over the compact raw carrier.
pub fn carrier_commit_from_raw_32(
    d_matrix: &PolyMatrix,
    a: &PolyVec,
    raw: &Vec<linalg::RawVec32>,
) -> PolyVec {
    let what: PolyVec = carrier_decomp_from_raw_32(a, raw);
    d_matrix.mat_vec_mul(&what)
}

// @genesis af3f7d5 2026-09-18 — quadeval::honest_compute_v_from_raw_32
/// [`honest_compute_v_from_raw`] over the compact raw carrier.
pub fn honest_compute_v_from_raw_32(
    pp: &PublicParamsD,
    stmt: &QuadEvalStatement,
    raw: &Vec<linalg::RawVec32>,
) -> PolyVec {
    carrier_commit_from_raw_32(pp.d_matrix(), stmt.avec(), raw)
}

// @genesis af3f7d5 2026-09-18 — quadeval::honest_compute_resp_from_raw_32
/// [`honest_compute_resp_from_raw`] over the compact raw carrier.
pub fn honest_compute_resp_from_raw_32(
    stmt: &QuadEvalStatement,
    raw: &Vec<linalg::RawVec32>,
    inner_decomp: &Vec<PolyVec>,
    c: &PolyVec,
) -> QuadEvalResponse {
    let carrier_dec: PolyVec = carrier_decomp_from_raw_32(stmt.avec(), raw);
    let z: PolyVec = honest_z_from_raw_32(raw, c);
    let z_dec: PolyVec = gadget::bounded_z_gadget_decompose(&z);
    let mut inner: Vec<PolyVec> = Vec::new();
    let mut i: usize = 0;
    while i < inner_decomp.len() {
        inner.push(inner_decomp[i].copy());
        i += 1;
    }
    QuadEvalResponse::new(carrier_dec, inner, z_dec)
}
