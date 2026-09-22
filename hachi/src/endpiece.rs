//! The terminal checks of Hachi's nonrecursive opening.
//!
//! Reference specification:
//! `ArkLib/Commitments/Functional/Hachi/EndPiece/Reduction.lean`.
//!
//! Target 3 introduced the two shortness checks because they complete the
//! ring-switch link. Target 6 extends the module with the terminal statement
//! and the end piece itself: the single decision procedure of the closing link
//! (`endPieceCheck`), and the two identities around it (`endPieceProver`'s one
//! message and `endPieceWitness`).
//!
//! # One decision procedure, two consumers
//!
//! `endPieceCheck` is the guard of the soundness-side `endPieceVerifier`
//! (`EndPiece/Reduction.lean:150`) *and* the verdict the nonrecursive scheme's
//! `terminalVerifier` returns (`Correctness.lean:117`,
//! `terminalVerifier_verify_eq_endPieceCheck`, `:126`, by `rfl`). One Rust
//! function therefore serves both shapes, and it decides `relWEvalClaim`
//! exactly (`endPieceCheck_eq_true_iff`, `EndPiece/Reduction.lean:225`).
//!
//! # Where the parameters come from
//!
//! The specification's `K`, `bound`, `bDig`, `b`, `φF` and `m₀` are all fixed by
//! the composed chain (`Correctness.lean`, `nonrecursiveTerminalReduction`
//! instantiated at `HonestRangeParams.ofPinnedDigitBase 16`): `K` is
//! `hachiLiftCom` at a caller-supplied key, so `d_key` is an argument;
//! `bound = CHAIN_GAMMA = 15` and `bDig = b = B_ZERO = GADGET_BASE = 16` are the
//! `params` constants [`lift_short_check`] and [`crate::ringswitch::rho_digits`]
//! already carry; `φF` is `Ext4::from_base`, the fixed base embedding
//! `w_table` already applies; and `m₀` is the arity of the statement's point,
//! read off the data as `zerocheck` reads every arity (`zerocheck.rs`
//! § "Arities come from the data, not from `params`") -- `stmt.point` has type
//! `Fin m₀ → F`, so its length *is* `m₀`.

use alloc::vec::Vec;

use cpoly::Ext4;

use crate::commit::{centered_abs, vec_l_infty_norm};
use crate::linalg::{PolyMatrix, PolyVec};
use crate::params;
use crate::ringswitch::{lift_commit, rho_digits_at, LiftedWitness, QuotientRow};
use crate::zerocheck::w_table_mle_eval;

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
///
/// The three nested loops are the specification's three quantifiers, in its
/// order: `∀ i` over the rows, `∀ u < δ` over the digits, `∀ k < d` over the
/// coefficients (`EndPiece/Reduction.lean:111-113`). The digit is addressed by
/// the pair `(i, u)` through [`crate::ringswitch::rho_digits_at`] because that
/// is what `rhoDigitsShortCheck` applies `rhoDigits` to. An earlier version
/// built the flat index `i * GADGET_DIGITS + u` and went through
/// `rho_digit_as_rq`, which split it back apart; that round trip is not in the
/// specification, and because `i * 8` is a checked `usize` product over an
/// `i` bounded only by `rho.len()`, it made the extracted model *fallible* --
/// forcing an `n * 8 ≤ Usize.max` hypothesis into
/// `rho_digits_short_check_spec` and, through the caller,
/// `lift_short_check_spec`. Forming no product removes the hypothesis instead
/// of assuming it away. The frozen genesis copy still has the old shape, so
/// this operation's `vs genesis` column now contains a **faithfulness repair
/// and not an optimization**; see NOTES.md § "The flat index the specification
/// does not have".
pub fn rho_digits_short_check(rho: &Vec<QuotientRow>) -> bool {
    let rows: usize = rho.len();
    let mut i: usize = 0;
    let mut short: bool = true;
    while i < rows {
        let mut u: usize = 0;
        while u < params::GADGET_DIGITS {
            let digit = rho_digits_at(rho, i, u);
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

/// Check the `ℓ∞` bound on `z` and the quotient-digit bound (spec:
/// `liftShortCheck`, `EndPiece/Reduction.lean:130`).
///
/// Mirrors `liftShortCheck`.
pub fn lift_short_check(w: &LiftedWitness) -> bool {
    vec_l_infty_norm(w.z()) <= params::CHAIN_GAMMA && rho_digits_short_check(w.rho())
}

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
    /// Bundle the commitment, the sumcheck point and the claimed value.
    pub fn new(t: PolyVec, point: Vec<Ext4>, value: Ext4) -> WEvalStatement {
        WEvalStatement { t, point, value }
    }

    /// The `w̃`-commitment from the lift stage.
    pub fn t(&self) -> &PolyVec {
        &self.t
    }

    /// The sumcheck challenge point `a = (a₁, …, a_{m₀})`; its length is `m₀`.
    pub fn point(&self) -> &Vec<Ext4> {
        &self.point
    }

    /// The claimed evaluation `y′ = mle[w̃](a)`.
    pub fn value(&self) -> Ext4 {
        self.value
    }
}

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
/// (the target-6 brief § "Strategy candidates"), and a baseline that
/// had already done it would report that win as zero forever.
pub fn end_piece_check(d_key: &PolyMatrix, stmt: &WEvalStatement, w: &LiftedWitness) -> bool {
    // Card T40b: the shortness test FIRST. `&&` short-circuits and every
    // conjunct is total, so the value is the one the old order computed --
    // `Bool.and` is commutative and that is the whole proof obligation. What
    // changes is what a *dishonest* prover costs the verifier: a witness that
    // fails the bound used to be rejected only after a full `lift_commit`,
    // which is 17.9 s at the pin. Now it is rejected before that runs.
    //
    // It is also the conjunct T40a's fast path is guarded on, so on the
    // honest path the test is one the verifier was going to run anyway.
    let m0: usize = stmt.point().len();
    lift_short_check(w)
        && lift_commit(d_key, w).equals(stmt.t())
        && w_table_mle_eval(w, m0, stmt.point()) == stmt.value()
}

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
