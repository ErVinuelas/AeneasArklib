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
//! So what follows is the *computational residue* of the chain's two parties:
//! [`chain_verify`] is the composed **verifier** -- the statement maps threaded
//! in order and the boolean checks the specification's verifiers actually run
//! -- and [`chain_open`] is the composed **honest prover**, producing the
//! messages the verifier reads off the wire. The challenge stream arrives as
//! arguments on both sides because there is no sampler here: a verifier that
//! drew its own challenges would be a different object from the one ArkLib
//! proves sound.
//!
//! # What the verifier checks, and what it does not
//!
//! The composed verifier has **exactly three boolean checks** --
//! `roundCheck` once per round, `finalCheck`, and `endPieceCheck` -- and rows
//! 1–7 are pure statement maps (`STAGE2_SCOPING.md` § "API mapping", read off
//! `Correctness.lean`'s wire format and confirmed row by row below):
//!
//! | row | verifier |
//! |---|---|
//! | 1 bridge | `to_quad_eval_statement`, a statement map (`QuadEval/Bridge.lean:182`) |
//! | 2 quadEval | pass-through: re-emits the statement, the message `v` and the challenge `c` (`QuadEval/Reduction.lean:434`) |
//! | 3 `R^lin` adapter | `rlin_stmt`, a statement map (`RingSwitch/Rlin.lean:529`) |
//! | 4 lift | a statement map: adjoins the message `t` and the challenge `α` |
//! | 5 batch | nothing: its map is `id` (`ZeroCheck/Batch.lean:271`) |
//! | 6 zeroCheck | a statement map: adjoins the challenges `τ₀`, `τ_α` (`nestedZcMapStmt`, `ZeroCheck/Reduction.lean:379`) |
//! | 7 sumcheck bridge | `nested_to_round_statement`, a statement map (`Sumcheck/Bridge.lean:165`) |
//! | 8 rounds | **`round_verify_loop`**: `roundCheck` on each received message (`Sumcheck/Rounds.lean:120`) |
//! | 9 finalEval | **`final_check`** on the received `y′` (`Sumcheck/FinalEval.lean:114`) |
//! | closing | **`end_piece_check`** on the received witness (`EndPiece/Reduction.lean:154`) |
//!
//! **What is absent from that table is the point of it.** Eq. (20)
//! (`paper_rel_out`), the lift's shortness (`lift_short_check` on its own), and
//! the two zero-check blocks (`h_zero_is_zero`, `h_alpha_is_zero`) are
//! *relations* -- `relOut`, `relLift`, `relNestedZeroCheck` -- the sets the
//! soundness theorems quantify over. No verifier in the composition evaluates
//! them: the `(ŵ, t̂, ẑ)` triple is never sent (§4.3 proves knowledge of it),
//! and `H₀ ≡ 0`, `H_α ≡ 0` are what the sumcheck exists to establish. That is
//! the paper's headline -- the verifier performs no `R_q` multiplication
//! (§1.2) -- and it is why the verifier here never touches the witness before
//! the end piece, whose one message *is* the witness (`endPieceProver`,
//! `EndPiece/Reduction.lean:241`). A first draft of this module ran all four
//! relations as guards and recomputed the prover's round messages inside the
//! verifier; NOTES.md § "The composed verifier was not a verifier" records
//! what that cost and how it was found.
//!
//! # Inputs, classified
//!
//! Three kinds, and the classification is the wire format
//! (`Correctness.lean:189-201`):
//!
//! * **public**: `pp`, the lift key `d_key`, the evaluation claim `poly_stmt`,
//!   the bound `gamma`, and the six dimensions;
//! * **messages**, prover to verifier, in wire order: `v` (row 2), `t` (row
//!   4), `msgs` (row 8, one pair per round), `y_prime` (row 9), `w` (the end
//!   piece's single message);
//! * **challenges**, verifier to prover, in wire order: `c` (row 2), `alpha`
//!   (row 4), `tau0` and `tau1` (row 6), `challenges` (row 8).
//!
//! The specification's `FullTranscript` types every length; here the lengths
//! (`msgs.len() == challenges.len() == m₀`, `tau0.len() == m₀`,
//! `tau1.len() == m₁`) travel as `_spec` hypotheses.
//!
//! # Scale
//!
//! The verifier inherits two walls, not every wall: the `R^lin` matrix
//! (`rlin_stmt`, 2.2 GiB at `μ₀ = 57 344`) and the `2^m₀` table
//! `alpha_public_table` that `final_check` builds (`6.7·10⁷` extension
//! elements at `M_ZERO = 26`). Neither is a `ring::mul` wall, and neither is
//! the cube-sized *witness* work the first draft carried -- that now sits
//! where the specification puts it, in [`chain_open`]. The composed rows are
//! excluded from the bench by name and the end-to-end test runs at the
//! smallest shapes that keep every row's shape, per the scale policy: this
//! module is where the chain is shown to compose, not where it is measured.

use alloc::vec::Vec;

use cpoly::Ext4;

use crate::linalg::{PolyMatrix, PolyVec};
use crate::quadeval::{PolyEvalStatement, PublicParamsD};
use crate::ringswitch::LiftedWitness;
use crate::sumcheck::{NestedZeroCheckStmt, RoundMsg, RoundStatement};

/// The composed verifier: the statement maps of rows 1–7 threaded in the
/// specification's order, then the three boolean checks it runs on what the
/// prover sent (spec: the verifier of `evaluation`, `Composition.lean:283`).
///
/// Mirrors `evaluation` at its verifier.
///
/// **Short-circuits where the specification does, and only there.** The round
/// loop stops at the first rejected round, which is `roundVerifier`'s
/// `failure` (`Sumcheck/Rounds.lean:123`); `finalEvalVerifier` and
/// `endPieceVerifier` fail the same way (`FinalEval.lean:118`,
/// `EndPiece/Reduction.lean:156`), so a `false` from either ends the chain.
/// The two final checks are still evaluated as the conjunction their
/// verifiers' `GuardedForm`s name, which is what the composed-verifier proof
/// mirrors.
///
/// Rows 4–6 have no carrier of their own here: `LiftStatement` is
/// `(rlin, t, α)` and `nestedZcMapStmt` adjoins `(τ₀, τ_α)` to it, so the two
/// maps compose into one [`NestedZeroCheckStmt::new`].
#[allow(clippy::too_many_arguments)]
pub fn chain_verify(
    pp: &PublicParamsD,
    d_key: &PolyMatrix,
    poly_stmt: &PolyEvalStatement,
    v: &PolyVec,
    c: &PolyVec,
    t: &PolyVec,
    alpha: Ext4,
    tau0: &Vec<Ext4>,
    tau1: &Vec<Ext4>,
    msgs: &Vec<RoundMsg>,
    challenges: &Vec<Ext4>,
    y_prime: Ext4,
    w: &LiftedWitness,
    gamma: u64,
    blocks: usize,
    message_rows: usize,
    message_digits: usize,
    inner_rows: usize,
    inner_digits: usize,
    z_digits: usize,
) -> bool {
    // row 1, the bridge: a statement map.
    let stmt = crate::quadeval::to_quad_eval_statement(poly_stmt);

    // row 2, QuadEval: a pass-through. `v` and `c` are read off the wire and
    // re-emitted; Eq. (20) lives in `relOut` and is not evaluated here.

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

    // rows 4 to 6: the lift adjoins `t` and `α`, batch is the identity, the
    // zero check adjoins `τ₀` and `τ_α`. Three maps, one carrier.
    let zc = NestedZeroCheckStmt::new(rlin, t.copy(), alpha, copy_point(tau0), copy_point(tau1));

    // row 7, the sumcheck bridge: install the empty prefix and the two initial
    // targets.
    let opened: RoundStatement = crate::sumcheck::nested_to_round_statement(zc);

    // row 8, the paired sumcheck rounds: `roundCheck` on each received
    // message. `None` is the round that rejected.
    let after = crate::sumcheck::round_verify_loop(opened, msgs, challenges);
    match after {
        None => false,
        Some(final_stmt) => {
            // row 9, the final evaluation claim, on the received `y′`.
            let c_final: bool = crate::sumcheck::final_check(&final_stmt, y_prime, gamma);

            // the closing end piece: the claim the final row emits, checked
            // against the witness the prover sent in the clear.
            let weval = crate::endpiece::WEvalStatement::new(t.copy(), copy_point(challenges), y_prime);
            let c_end: bool = crate::endpiece::end_piece_check(d_key, &weval, w);

            c_final && c_end
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

/// The honest prover's side of the chain: every message the verifier reads
/// off the wire, in wire order (spec: the honest `computeV`, `hachiLiftCom`,
/// `honestComputeG` and `computeY` parameters `evaluation` is instantiated at,
/// `Composition.lean:283` through `Sumcheck/Completeness.lean:74` and
/// `FinalEval.lean:246`).
///
/// Mirrors `evaluation` at its honest prover.
///
/// Four values rather than a transcript type: the wire format upstream is a
/// `ProtocolSpec` append-chain whose messages are indexed by `Fin`, and there
/// is no carrier for that here -- the composed statement types erase to the
/// arguments [`chain_verify`] already takes. So the honest side produces
/// exactly the things the verifier cannot compute for itself -- `v`, `t`, the
/// `m₀` round-message pairs and `y′` -- and the challenge stream stays an input
/// on both sides. The fifth message, the witness itself, is the end piece's
/// (`end_piece_prove`, the identity) and is already in the caller's hands.
///
/// The prover threads the same statement maps the verifier does (rows 1, 3,
/// 4–7), because `roundProver` carries the statement and `honestComputeG`
/// reads `τ₀`, the challenges drawn so far and, through `alpha_public_table`,
/// the `R^lin` statement. That is the specification's shape, not a
/// convenience: an honest prover that skipped the maps would have nothing to
/// compute its messages against.
///
/// **The lifted witness is an input, not an output** -- by decision now, not
/// by omission. The honest lift prover builds `w = (z, ρ)` from the QuadEval
/// response by synthetic division (`honestLiftWitnessC`,
/// `RingSwitch/ComputableWitness.lean:85`); that item **is** translated here
/// as of 2026-09-11 (`ringswitch::honest_lift_witness`, proved in
/// `lean/LiftProver.lean`), so the scope gap this paragraph used to record is
/// closed (NOTES.md § "The composed verifier was not a verifier", and its
/// successor § "The lift prover is proved, and Stage 4 closes"). What remains
/// is whether `chain_open` should *call* it rather than take `w`: it is the
/// specification's own shape either way -- `honestLiftWitnessC` is a separate
/// definition, not a step inside the prover -- and every spec here is stated
/// against the current signature, so the change is deliberate and deferred to
/// the optimization stage, where it matters only for one-function prover
/// timing. Until then the caller supplies `w`, and the QuadEval response
/// `(ŵ, t̂, ẑ)` -- which is never sent -- is not produced here either:
/// `honest_compute_resp` remains its own mirrored item.
#[allow(clippy::too_many_arguments)]
pub fn chain_open(
    pp: &PublicParamsD,
    d_key: &PolyMatrix,
    poly_stmt: &PolyEvalStatement,
    carrier_dec: &PolyVec,
    c: &PolyVec,
    w: &LiftedWitness,
    alpha: Ext4,
    tau0: &Vec<Ext4>,
    tau1: &Vec<Ext4>,
    challenges: &Vec<Ext4>,
    gamma: u64,
    blocks: usize,
    message_rows: usize,
    message_digits: usize,
    inner_rows: usize,
    inner_digits: usize,
    z_digits: usize,
) -> (PolyVec, PolyVec, Vec<RoundMsg>, Ext4) {
    let m0: usize = tau0.len();

    // row 1, then row 2's message: the carrier commitment.
    let stmt = crate::quadeval::to_quad_eval_statement(poly_stmt);
    // The carrier decomposition arrives computed (candidate T28). `v = D · ŵ`
    // and the response's carrier slot are the SAME `ŵ`, and at the pin it costs
    // 98.7 s, so the composed prover takes it rather than paying for it a
    // second time. The message itself is no longer read here at all -- the
    // decomposition is built from the RAW blocks by
    // `quadeval::carrier_decomp_from_raw_32`, which needs no gadget arithmetic
    // (the round trip inside `carrier_entry` cancels against it), so the honest
    // prover still never builds the 68.7 GiB `Decomp.message`.
    let v: PolyVec = crate::quadeval::honest_compute_v_from_decomp(pp.d_matrix(), carrier_dec);

    // row 3, the statement the rounds are computed against.
    let rlin = crate::quadeval::rlin_stmt(
        pp,
        &stmt,
        &v,
        c,
        gamma,
        blocks,
        message_rows,
        message_digits,
        inner_rows,
        inner_digits,
        z_digits,
    );

    // row 4's message: the commitment to `w̃`.
    let t: PolyVec = crate::ringswitch::lift_commit(d_key, w);

    // rows 4 to 7, as the verifier threads them.
    let zc = NestedZeroCheckStmt::new(rlin, t.copy(), alpha, copy_point(tau0), copy_point(tau1));
    let opened: RoundStatement = crate::sumcheck::nested_to_round_statement(zc);

    // row 8's messages, and row 9's.
    let msgs: Vec<RoundMsg> = crate::sumcheck::honest_round_messages(opened, w, challenges);
    let y_prime: Ext4 = crate::sumcheck::honest_compute_y(w, m0, challenges);

    (v, t, msgs, y_prime)
}
