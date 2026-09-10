//! The composed Hachi evaluation chain: `open` and `verify` over the proved
//! links.
//!
//! Reference specification:
//! `ArkLib/Commitments/Functional/Hachi/Composition.lean`.
//!
//! # What this module is, and what it deliberately is not
//!
//! `Composition.lean:244` composes the chain as
//!
//! ```text
//! (bridge ▷ quadEval) ▷ rlin ▷ lift ▷ batch ▷ zeroCheck ▷ sumcheckBridge
//! then (core ▷ rounds) ▷ finalEval,  and evaluation = iteration ▷ endPiece
//! ```
//!
//! — **nine rows plus the closing end piece.** Upstream those are
//! `EscapeGCWSSPackage`s: soundness certificates carrying provers, verifiers,
//! extractors and escape events, parameterised by a `ProbComp` and a
//! `QueryImpl`. None of that is translated here and none of it should be: the
//! probabilistic scaffolding is the part `Aeneas` has no model for, and the
//! plan scoped this module to "a composed commit → open → verify over the
//! proved links, with `D` and the challenge stream as **explicit inputs**".
//!
//! So what follows is the *computational residue* of the chain: the statement
//! maps threaded in order, and the conjunction of the guards that actually
//! decide. The challenge stream arrives as arguments because there is no
//! sampler here — a verifier that drew its own challenges would be a different
//! object from the one ArkLib proves sound.
//!
//! # Which rows decide, and which only reshape
//!
//! Four of the nine rows are pure or zero-round and contribute no check at
//! all, which is why this function is shorter than the row count suggests:
//!
//! | row | contributes |
//! |---|---|
//! | 1 bridge | `to_quad_eval_statement`, a statement map |
//! | 2 quadEval | **`paper_rel_out`** — Eq. (20), the Figure 3 verifier |
//! | 3 `R^lin` adapter | `rlin_stmt`, a statement map |
//! | 4 lift | **`lift_short_check`** — the shortness index |
//! | 5 batch | nothing: its map is `id` (`ZeroCheck/Batch.lean:267`) |
//! | 6 zeroCheck | **`h_zero_is_zero`**, **`h_alpha_is_zero`** |
//! | 7 sumcheck bridge | `nested_to_round_statement`, a statement map |
//! | 8 rounds | **`round_loop`**, which runs `round_check` per round |
//! | 9 finalEval | **`final_check`** |
//! | closing | **`end_piece_check`** |
//!
//! # Scale
//!
//! Every wall of every link is inherited here at once: `μ₀ = 57 344` for the
//! `R^lin` matrix (2.2 GiB), `2^m₀ = 6.7·10⁷` for the cube, and `M_ZERO = 26`
//! rounds of the sumcheck. So the composed rows are excluded from the bench by
//! name and the end-to-end test runs at the smallest shapes that keep every
//! row's *shape*, per the scale policy. That is the honest position: this
//! module is where the chain is shown to compose, not where it is measured.

use alloc::vec::Vec;

use cpoly::Ext4;

use crate::linalg::{PolyMatrix, PolyVec};
use crate::quadeval::{PolyEvalStatement, PublicParamsD, QuadEvalResponse};
use crate::ringswitch::LiftedWitness;
use crate::sumcheck::{NestedZeroCheckStmt, RoundStatement};

/// The composed verifier: every guard of the chain, in the specification's row
/// order, threaded through the statement maps between them (spec: the
/// computational residue of `evaluation`, `Composition.lean:283`).
///
/// Mirrors `evaluation` at its guards.
///
/// **Branchless in the rows.** Each guard is evaluated and the results are
/// combined at the end, rather than short-circuiting row by row. That costs
/// every row's work whatever the answer, and it is deliberate: it is the shape
/// the composed-verifier proof mirrors, exactly as `quadeval::rel_out` and
/// `ring::equals` are branchless for the same reason. The one exception is the
/// round loop, which *must* stop early — `roundVerifier` fails the round it
/// rejects in and there is no later round to run (`Sumcheck/Rounds.lean:113`).
///
/// The `Option` from [`crate::sumcheck::round_loop`] is the specification's
/// `failure`; a `None` there is a rejected round and fails the whole chain.
#[allow(clippy::too_many_arguments)]
pub fn chain_verify(
    pp: &PublicParamsD,
    d_key: &PolyMatrix,
    poly_stmt: &PolyEvalStatement,
    v: &PolyVec,
    c: &PolyVec,
    resp: &QuadEvalResponse,
    w: &LiftedWitness,
    alpha: Ext4,
    tau0: &Vec<Ext4>,
    tau1: &Vec<Ext4>,
    challenges: &Vec<Ext4>,
    y_prime: Ext4,
    gamma: u64,
    blocks: usize,
    message_rows: usize,
    message_digits: usize,
    inner_rows: usize,
    inner_digits: usize,
    z_digits: usize,
) -> bool {
    let m0: usize = tau0.len();
    let m1: usize = tau1.len();

    // row 1, the bridge: a statement map.
    let stmt = crate::quadeval::to_quad_eval_statement(poly_stmt);

    // row 2, QuadEval: the Figure 3 verifier, Eq. (20) with the paper's box.
    let c_quadeval: bool = crate::quadeval::paper_rel_out(pp, &stmt, v, c, resp);

    // row 3, the R^lin adapter: a statement map.
    let rlin = crate::quadeval::rlin_stmt(
        pp,
        &stmt,
        v,
        c,
        gamma,
        blocks,
        message_rows,
        message_digits,
        inner_rows,
        inner_digits,
        z_digits,
    );

    // row 4, the lift: the shortness index that makes a colliding pair a
    // Module-SIS break.
    let c_lift: bool = crate::endpiece::lift_short_check(w);

    // row 5, the batching bridge: nothing to check, its map is the identity.

    // row 6, the zero check: both constraint blocks vanish on the cube.
    let c_zero: bool = crate::zerocheck::h_zero_is_zero(w, m0);
    let c_alpha: bool = crate::zerocheck::h_alpha_is_zero(&rlin, alpha, w, m1);

    // the commitment to `w~` that the lift produced, needed twice below.
    let t: PolyVec = crate::ringswitch::lift_commit(d_key, w);

    // row 7, the sumcheck bridge: install the empty prefix and the two initial
    // targets.
    let zc = NestedZeroCheckStmt::new(rlin, t.copy(), alpha, copy_point(tau0), copy_point(tau1));
    let opened: RoundStatement = crate::sumcheck::nested_to_round_statement(zc);

    // row 8, the paired sumcheck rounds. `None` is the round that rejected.
    let after = crate::sumcheck::round_loop(opened, w, challenges);
    match after {
        None => false,
        Some(final_stmt) => {
            // row 9, the final evaluation claim.
            let c_final: bool = crate::sumcheck::final_check(&final_stmt, y_prime, gamma);

            // the closing end piece, on the claim the final row emits.
            let weval = crate::endpiece::WEvalStatement::new(t, copy_point(challenges), y_prime);
            let c_end: bool = crate::endpiece::end_piece_check(d_key, &weval, w);

            c_quadeval && c_lift && c_zero && c_alpha && c_final && c_end
        }
    }
}

/// Copy an evaluation point.
///
/// A `Vec<Ext4>` is `Copy` element-wise but the vector is not, and the chain
/// needs the same point in two carriers. Written as a loop because `clone` is a
/// trait call with no extracted model.
fn copy_point(p: &Vec<Ext4>) -> Vec<Ext4> {
    let mut out: Vec<Ext4> = Vec::new();
    let mut i: usize = 0;
    while i < p.len() {
        out.push(p[i]);
        i += 1;
    }
    out
}

/// The honest prover's side of the chain: the round-0 carrier commitment, the
/// Eq. (20) response, and the claimed evaluation (spec: the honest
/// `computeV`/`computeResp`/`computeY` parameters `evaluation` is instantiated
/// at, `Composition.lean:283` through `Sumcheck/Completeness.lean:74` and
/// `FinalEval.lean:246`).
///
/// Mirrors `evaluation` at its honest instantiation.
///
/// Three values rather than a transcript type: the wire format upstream is a
/// `ProtocolSpec` append-chain whose messages are indexed by `Fin`, and there
/// is no carrier for that here — the composed statement types erase to the
/// arguments [`chain_verify`] already takes. So the honest side produces
/// exactly the three things the verifier cannot compute for itself, and the
/// challenge stream stays an input on both sides.
pub fn chain_open(
    pp: &PublicParamsD,
    poly_stmt: &PolyEvalStatement,
    message: &Vec<PolyVec>,
    inner_decomp: &Vec<PolyVec>,
    c: &PolyVec,
    w: &LiftedWitness,
    challenges: &Vec<Ext4>,
) -> (PolyVec, QuadEvalResponse, Ext4) {
    let stmt = crate::quadeval::to_quad_eval_statement(poly_stmt);
    let v: PolyVec = crate::quadeval::honest_compute_v(pp, &stmt, message);
    let resp: QuadEvalResponse =
        crate::quadeval::honest_compute_resp(&stmt, message, inner_decomp, c);
    let y_prime: Ext4 = crate::sumcheck::honest_compute_y(w, challenges.len(), challenges);
    (v, resp, y_prime)
}
