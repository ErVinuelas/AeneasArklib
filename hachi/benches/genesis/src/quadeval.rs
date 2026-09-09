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
