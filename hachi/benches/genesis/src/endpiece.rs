//! The terminal checks of Hachi's nonrecursive opening.
//!
//! Reference specification:
//! `ArkLib/Commitments/Functional/Hachi/EndPiece/Reduction.lean`.
//!
//! Target 3 introduces the two shortness checks because they complete the
//! ring-switch link. Target 6 will extend this module with the terminal
//! commitment and multilinear-evaluation conjunction.

use alloc::vec::Vec;

use cpoly::Ext4;

use crate::commit::{centered_abs, vec_l_infty_norm};
use crate::linalg::{PolyMatrix, PolyVec};
use crate::params;
use crate::ringswitch::{lift_commit, rho_digit_as_rq, LiftedWitness, QuotientRow};
use crate::zerocheck::w_table_mle_eval;

// @genesis 240f277 2026-09-07 — endpiece::rho_digits_short_check
/// Check every coefficient of every balanced quotient digit against the
/// chain's bound (spec: `rhoDigitsShortCheck`,
/// `EndPiece/Reduction.lean:111`).
///
/// Mirrors `rhoDigitsShortCheck`.
///
/// At the fixed parameters the result is always `true`, since balanced base-16
/// digits have centered magnitude at most 8 and `CHAIN_GAMMA = 15`. The loop is
/// retained as the direct translation so a future parameter change cannot
/// silently remove the verifier check.
pub fn rho_digits_short_check(rho: &Vec<QuotientRow>) -> bool {
    let rows: usize = rho.len();
    let mut i: usize = 0;
    let mut short: bool = true;
    while i < rows {
        let mut u: usize = 0;
        while u < params::GADGET_DIGITS {
            let j: usize = i * params::GADGET_DIGITS + u;
            let digit = rho_digit_as_rq(rho, j);
            let mut k: usize = 0;
            while k < params::RING_DEGREE {
                if centered_abs(digit.coeff(k)) > params::CHAIN_GAMMA {
                    short = false;
                }
                k += 1;
            }
            u += 1;
        }
        i += 1;
    }
    short
}

// @genesis 240f277 2026-09-07 — endpiece::lift_short_check
/// Check the `ℓ∞` bound on `z` and the quotient-digit bound (spec:
/// `liftShortCheck`, `EndPiece/Reduction.lean:130`).
///
/// Mirrors `liftShortCheck`.
pub fn lift_short_check(w: &LiftedWitness) -> bool {
    vec_l_infty_norm(w.z()) <= params::CHAIN_GAMMA && rho_digits_short_check(w.rho())
}

// @genesis bad614d 2026-09-08 — endpiece::WEvalStatement
/// The evaluation-claim statement, output of the sumcheck and input of the end
/// piece (spec: `WEvalStatement`, `Sumcheck/FinalEval.lean:72`).
///
/// Mirrors `WEvalStatement`.
///
/// Three fields and nothing else: the `w̃`-commitment `t` from the lift stage,
/// the sumcheck challenge point `a ∈ F^{m₀}`, and the claimed evaluation
/// `y′ = mle[w̃](a)`. Everything else the sumcheck knew (the `R^lin` data, `α`,
/// the seeds, the targets) has been dropped by the time this statement exists.
///
/// `TCom` is instantiated at the concrete chain's `Simple.Commitment Φ dRows`,
/// i.e. a [`PolyVec`] of `D_ROWS` ring elements (`hachiLiftCom`,
/// `RingSwitch/Reduction.lean:277-281`); the point is a `Vec<Ext4>` whose
/// length is `m₀` -- `Fin m₀ → F` is a function type in the specification for
/// computability's sake, and the dynamic-length `Vec` is the house shape for it
/// (the same choice `zerocheck::w_table_mle_eval` makes for its argument `a`).
pub struct WEvalStatement {
    t: PolyVec,
    point: Vec<Ext4>,
    value: Ext4,
}

impl WEvalStatement {
    // @genesis bad614d 2026-09-08 — endpiece::WEvalStatement::new
    /// Bundle the commitment, the sumcheck point and the claimed value.
    pub fn new(t: PolyVec, point: Vec<Ext4>, value: Ext4) -> WEvalStatement {
        WEvalStatement { t, point, value }
    }

    // @genesis bad614d 2026-09-08 — endpiece::WEvalStatement::t
    /// The `w̃`-commitment from the lift stage.
    pub fn t(&self) -> &PolyVec {
        &self.t
    }

    // @genesis bad614d 2026-09-08 — endpiece::WEvalStatement::point
    /// The sumcheck challenge point `a = (a₁, …, a_{m₀})`; its length is `m₀`.
    pub fn point(&self) -> &Vec<Ext4> {
        &self.point
    }

    // @genesis bad614d 2026-09-08 — endpiece::WEvalStatement::value
    /// The claimed evaluation `y′ = mle[w̃](a)`.
    pub fn value(&self) -> Ext4 {
        self.value
    }
}

// @genesis bad614d 2026-09-08 — endpiece::end_piece_check
/// The end piece: decide `relWEvalClaim` on the witness the prover sent (spec:
/// `endPieceCheck`, `EndPiece/Reduction.lean:143`).
///
/// Mirrors `endPieceCheck`.
///
/// Three conjuncts, in the specification's order and with its short-circuit:
/// `&&` is Lean's `Bool.and`, which does not evaluate its right operand when the
/// left one is `false`, and Rust's `&&` does the same, so the extracted model
/// is the same `if`-nesting as the specification's.
///
/// * **A** -- `K.com w == stmt.t`: the lift commitment recomputes to the claimed
///   `t`. `K.com` is `hachiLiftCom`'s `Simple.commit Φ D (liftMessage Φ bDig w)`
///   (`RingSwitch/Reduction.lean:281`), i.e. [`crate::ringswitch::lift_commit`];
///   `==` is the `[BEq K.TCom]` instance at `TCom = PolyVec (Rq Φ) dRows`, i.e.
///   [`PolyVec::equals`]. This is the whole cost of the function at the real
///   constants -- `LIFT_COLS = 57 384` schoolbook ring products -- and the wall
///   is `ring::mul`'s width, not anything in this module.
/// * **B** -- `liftShortCheck Φ bound bDig w`: [`lift_short_check`] at the
///   chain's `(bound, bDig) = (CHAIN_GAMMA, B_ZERO) = (15, 16)`.
/// * **C** -- `wTableMleEval Φ m₀ φF b w stmt.point == stmt.value`:
///   [`crate::zerocheck::w_table_mle_eval`] at `m₀ = stmt.point.len()` (module
///   header § "Where the parameters come from"), compared in `F` by cpoly's
///   derived `PartialEq for Ext4`, which is the equality `ext_eq_spec` in
///   cpoly's own development is about. This is the `m₀`-cube wall: `2^m₀`
///   table entries at the pinned `M_ZERO = 26`, which no multiplication speedup
///   touches.
///
/// The two walls fire in one function, and they are removed by different
/// champions; the bench file keeps them stated separately.
///
/// Nothing is hoisted: the digit block of `w.rho()` is rebuilt inside conjunct A
/// (`lift_message`), inside conjunct B (`rho_digits_short_check`) and inside
/// conjunct C (`w_table`), three times over, because that is where the
/// specification's three definitions each compute it. Sharing one pre-sized
/// digit block across the conjuncts is the brief's highest-ratio optimization
/// (briefs/target-6-end-piece.md § "Strategy candidates"), and a baseline that
/// had already done it would report that win as zero forever.
pub fn end_piece_check(d_key: &PolyMatrix, stmt: &WEvalStatement, w: &LiftedWitness) -> bool {
    let com: PolyVec = lift_commit(d_key, w);
    let m0: usize = stmt.point().len();
    com.equals(stmt.t())
        && lift_short_check(w)
        && w_table_mle_eval(w, m0, stmt.point()) == stmt.value()
}

// @genesis bad614d 2026-09-08 — endpiece::end_piece_prove
/// The honest end-piece prover's one message: the witness itself, in the clear
/// (spec: `endPieceProver`'s `sendMessage ⟨0, _⟩ = fun w => pure (w, w)`,
/// `EndPiece/Reduction.lean:241-249`).
///
/// Mirrors `endPieceProver`.
///
/// The identity, by value: `pSpecEndPiece` is a single `P_to_V` round whose
/// message type is the witness (`:86`), the prover's state before and after that
/// round is the witness (`:244-246`), and its output is trivial (`:252`). There
/// is no arithmetic content -- the honest run is characterized as a single
/// `pure` by `endPieceProver_run_support` (`:274`) -- so this function is a move,
/// and its benchmark row is excluded by name as O(1) by inspection.
pub fn end_piece_prove(w: LiftedWitness) -> LiftedWitness {
    w
}

// @genesis bad614d 2026-09-08 — endpiece::end_piece_witness
/// The witness read off an end-piece transcript: the prover's single message
/// (spec: `endPieceWitness`, `EndPiece/Reduction.lean:172`).
///
/// Mirrors `endPieceWitness`.
///
/// `endPieceWitness _stmt tr = tr 0`, and a `FullTranscript` of the one-round
/// `pSpecEndPiece` is that one message, so the transcript *is* the argument
/// `message`. The statement is taken and ignored exactly as the specification
/// takes and ignores `_stmt`: the extractor `endPieceExtractor` (`:179`) is this
/// function on the tree's unique path, so keeping the statement in the
/// signature keeps the two arities in step. Also an identity, and also excluded
/// from the bench by name.
pub fn end_piece_witness(_stmt: &WEvalStatement, message: LiftedWitness) -> LiftedWitness {
    message
}
