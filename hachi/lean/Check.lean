import Generated
import Field
import Ext
import Ring
import RqBridge
import Scheme
import EvalSplit
import Balanced
import QuadEval
import QuadEvalProtocol
import RingSwitch
import ZeroCheck
import EndPiece
import Rlin
import Sumcheck
import Chain
import LiftProver
import Opt
import ArkLib.Data.Lattices.CyclotomicRing.Core.Modulus
import ArkLib.Commitments.Functional.Hachi.Params

/-!
Audit file: not part of the development, only a machine-checked review of what
this repository currently claims.

Nothing imports this file and nothing here is used by a proof; it is a root of
the library in its own right (see `lakefile.lean`), which is what gets it checked
by `lake build`. Its eventual job is the one `Check.lean` does in AeneasCompPoly:
catch the failure mode that a `_spec` theorem is *true but vacuous*, and print
the axiom dependencies of the headline specs so that a reader can confirm no
`sorryAx` hides under one.

What it audits, in four sections:

1. the extracted parameters are the ones `src/params.rs` names, and they satisfy
   every side condition the generic ArkLib statements carry as a hypothesis --
   including the two that the *derived* bounds rest on (`b - 1 ≤ q/2` for the digit
   bound, `q % 8 = 5` and `κ² < q` for challenge invertibility) -- and the
   protocol-layer block is tied *by name* to ArkLib's own `ℓ = 30` profile
   (`Hachi/Params.lean`: `hachiTau`, `honestZBound`, `mu0`, `liftKeyWidth`, …);
2. the `cpoly` field layer arrives *transparently*, not as axioms -- the question
   Workstream 0 existed to settle;
   2b. all four modules of the scheme are present in the model, with the shapes the
   equivalence proofs need: the container newtypes are `Vec` aliases, and every
   operation is `Result`-valued (so each spec owes a totality proof, not just an
   equality);
3. the ArkLib specification side is reachable from this package at all, and the
   ring degree the Rust fixes is the degree ArkLib's modulus actually has;
4. the axiom dependencies of every proved spec, which is what makes a `sorryAx`
   a build failure rather than a silent debt.

§ 4 covers every module of this library: the base-field specs
(`lean/Field.lean`), the coefficient-level ring specs (`lean/Ring.lean`), their
lifts to ArkLib's `Rq Φ` (`lean/RqBridge.lean`), the `linalg`, `gadget` and
`commit` layers (`lean/Scheme.lean`) up to perfect correctness of the extracted
scheme, the multilinear evaluation layer (`lean/EvalSplit.lean`), the balanced
committer, the QuadEval fold and its protocol layer, the `Ext4` extension field,
the ring-switch link, the zero check, the end piece, the `R^lin` adapter, the
paired sumcheck, the composed chain and -- since 2026-09-11 -- the honest lift
prover (`lean/LiftProver.lean`). Every one is proved, so `lean-wip/` is empty
again; the procedure for promoting a file into here, when the next translated
operation lands there, is in `lean-wip/README.md`.
-/

-- Off, and load-bearing for an audit file specifically. With `autoImplicit` on (the
-- Lean default; ArkLib turns it off repository-wide for the same reason), an
-- unknown identifier appearing in a *binder type* is silently auto-bound as an
-- implicit variable rather than reported. An assertion about an extracted name that
-- has since left `Generated.lean` then keeps compiling, about a universally
-- quantified nothing -- which is exactly the "true but vacuous" failure this file
-- exists to catch, applied to the file itself. Found the hard way: the `Ext4`
-- examples below outlived the item they were about, and only the one that used the
-- name in a *term* position failed the build.
set_option autoImplicit false

open Aeneas Aeneas.Std
open ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus

-- Aeneas wraps the whole extracted model in a namespace named after the crate,
-- so every generated name is `hachi.…` -- including the `cpoly` items the
-- `--include` whitelist pulled in, which land at `hachi.cpoly.field.…` rather
-- than at a top-level `cpoly`. Opening it lets this file spell them the way
-- `Generated.lean` reads.
open hachi

namespace HachiEquiv.Check

/-! ## 1. The parameters are what `params.rs` says, and they are legal -/

-- The extracted constants. `simp` rather than `rfl`: Aeneas marks each global
-- `irreducible`, so the equation lemma is the way in.
example : params.Q = 4294967197#u64 := by simp [params.Q]
example : params.EXT_DEGREE = 4#usize := by simp [params.EXT_DEGREE]
example : params.EXT_W = 2#u64 := by simp [params.EXT_W]
example : params.RING_LOG_DEGREE = 10#usize := by simp [params.RING_LOG_DEGREE]
example : params.RING_DEGREE = 1024#usize := by simp [params.RING_DEGREE]
example : params.GADGET_BASE = 16#u64 := by simp [params.GADGET_BASE]
example : params.GADGET_DIGITS = 8#usize := by simp [params.GADGET_DIGITS]
example : params.MESSAGE_ROWS = 1024#usize := by simp [params.MESSAGE_ROWS]
example : params.INNER_ROWS = 1#usize := by simp [params.INNER_ROWS]
example : params.OUTER_ROWS = 1#usize := by simp [params.OUTER_ROWS]
example : params.BLOCKS = 1024#usize := by simp [params.BLOCKS]
example : params.GAMMA = 16#u64 := by simp [params.GAMMA]
example : params.BETA_SQ = 41976510894886092800#u128 := by simp [params.BETA_SQ]
example : params.KAPPA = 32#u64 := by simp [params.KAPPA]

-- `RING_DEGREE` is a literal in Rust (a shift would extract as a `Result`; see
-- the docstring in `params.rs`), so the relation to `RING_LOG_DEGREE` is not
-- true by construction on this side and has to be checked.
example : params.RING_DEGREE.val = 2 ^ params.RING_LOG_DEGREE.val := by
  simp [params.RING_DEGREE, params.RING_LOG_DEGREE]

-- `zmodDigitDecomposition` (Gadget/Core.lean) needs `1 < b` and `q ≤ b ^ digits`.
-- Without these two the gadget layer has no instance at all, so they are checked
-- before any of it is written.
example : 1 < params.GADGET_BASE.val := by simp [params.GADGET_BASE]
example : params.Q.val ≤ params.GADGET_BASE.val ^ params.GADGET_DIGITS.val := by
  simp [params.Q, params.GADGET_BASE, params.GADGET_DIGITS]

-- ... and `digits` is minimal: one fewer would not cover the modulus, which is
-- what pins it to 8 rather than merely permitting it.
example : params.GADGET_BASE.val ^ (params.GADGET_DIGITS.val - 1) < params.Q.val := by
  simp [params.Q, params.GADGET_BASE, params.GADGET_DIGITS]

-- The unsigned digit bound `zmodDigit_natAbs_le` (ours, in `Scheme.lean`: ArkLib
-- dropped it when the balanced digits became the gadget inverse, PR #847) -- the
-- single analytic input to every honest-case shortness bound of the proved
-- unsigned layer -- additionally needs `b - 1 ≤ q/2`, which is what stops a small
-- non-negative digit from wrapping to a negative centered representative.
example : params.GADGET_BASE.val - 1 ≤ params.Q.val / 2 := by
  simp [params.Q, params.GADGET_BASE]

-- `GAMMA` and `BETA_SQ` are the *weak-opening* bounds of ArkLib's
-- paper-parameter mapping (`QuadEval/Soundness.lean`, Hachi Lemma 8):
-- `γ̄ = b` (the paper's `S_b` box relaxed to the symmetric `ℓ∞` ball) and
-- `βSq = quadEvalBetaSq γ b τ d m δ` at `γ := b` --
-- `4 · (2^m·δ) · (d · ((Σ_{u<τ} b^u) · γ)²)` with `τ = 5`, the folded-witness
-- digit count of ArkLib's `ℓ = 30` profile (ArkLib PR #847,
-- `Hachi/Params.lean`: `hachiTau`, and its `betaSq` is this same expression).
-- Neither [NOZ26] Fig. 9's `τ = 4` (four balanced base-16 digits carry
-- `30583 < 131072 = 2ʳ·ω·⌊b/2⌋`, the honest `‖z‖∞` bound ArkLib proves) nor
-- the message digit count `δ = 8` (the `z`-gadget no longer has to cover all
-- of `ℤ_q`: `BoundedDigitDecomposition` replaced `hqz : q ≤ b ^ zDigits`, and
-- `16⁵ < q`). `τ`'s only appearance in this crate is inside this derived
-- literal; the example below checks the arithmetic, and binding it to
-- `HachiParams.betaSq` by name waits on the pin moving to #847. Both are
-- literals in `params.rs` (Aeneas models `const` arithmetic as fallible, so
-- the derived forms would extract as `Result`s), so the derivation is checked
-- rather than structural.
example : params.GAMMA.val = params.GADGET_BASE.val := by
  simp [params.GAMMA, params.GADGET_BASE]

example : params.BETA_SQ.val
    = 4 * ((params.MESSAGE_ROWS.val * params.GADGET_DIGITS.val)
        * (params.RING_DEGREE.val
            * ((1 + params.GADGET_BASE.val + params.GADGET_BASE.val ^ 2
                + params.GADGET_BASE.val ^ 3 + params.GADGET_BASE.val ^ 4)
                * params.GAMMA.val) ^ 2)) := by
  simp [params.BETA_SQ, params.MESSAGE_ROWS, params.GADGET_DIGITS, params.RING_DEGREE,
    params.GADGET_BASE, params.GAMMA]

-- ... and the *honest* bounds sit strictly inside them: the honest
-- decomposition's digit bound is `b - 1 = 15 < 16 = γ`
-- (`gadgetDecompose_vecLInftyNorm_le_of_digit_le` at `zmodDigit_natAbs_le`), and
-- its `ℓ₂²` bound `(messageRows · digits) · (deg φ) · (b-1)² = 1887436800` is
-- ~2.2·10¹⁰ below `βSq` (`gadgetDecompose_vecL2NormSq_le_of_digit_le`, same
-- digit bound). The slack is the design: it
-- is what admits the protocol's *extracted* openings -- and at `τ = 5` it is
-- not total: the largest representable `ℓ₂²`, `(1024·8) · 1024 · (q/2)²
-- ≈ 3.9·10²⁵`, exceeds `βSq ≈ 4.2·10¹⁹`, so the verifier's `ℓ₂²` branch is
-- live (`commit_semantics.rs`'s overlong-message witness; the full-coverage
-- `τ = 8` reading had it vacuous). What survives of that reading is thinner:
-- `√βSq ≈ 2^32.6` still exceeds `q ≈ 2^32`, so weak binding at this radius is
-- not SIS-instantiable at Fig. 9's toy row count -- recorded in `NOTES.md`,
-- owed to the Stage 7 claims ledger.
example : ¬ ((1024 * 8) * 1024 * (params.Q.val / 2) ^ 2 ≤ params.BETA_SQ.val) := by
  simp [params.Q, params.BETA_SQ]
example : params.GADGET_BASE.val - 1 < params.GAMMA.val := by
  simp [params.GADGET_BASE, params.GAMMA]

example : params.MESSAGE_ROWS.val * params.GADGET_DIGITS.val * params.RING_DEGREE.val
    * (params.GADGET_BASE.val - 1) ^ 2 ≤ params.BETA_SQ.val := by
  simp [params.BETA_SQ, params.MESSAGE_ROWS, params.GADGET_DIGITS, params.RING_DEGREE,
    params.GADGET_BASE]

-- `KAPPA` is capped by `isUnit_of_l1Norm_le` (`NormBounds/LyubashevskySeiler.lean`),
-- which turns the verifier's `0 < ‖c‖₁ ≤ κ` into the invertibility a weak opening
-- actually requires -- given `q % 8 = 5` and `κ² < q`. `params.rs` no longer sits
-- on that ceiling (`⌊√q⌋ = 65535`): the value is the weak-opening bound
-- `ω̄ = 2ω = 32` at [NOZ26] Fig. 9's `ω = 16` (extracted openings carry challenge
-- *differences*), so `κ² < q` here is exactly ArkLib Lemma 8's own hypothesis
-- `hκ : (2ω)² < q`.
example : params.Q.val % 8 = 5 := by simp [params.Q]
example : params.KAPPA.val ^ 2 < params.Q.val := by simp [params.KAPPA, params.Q]

-- The honest challenge is `c = 1`, and `Rq.l1Norm_one` gives `‖1‖₁ = 1`; the
-- verifier's upper bound has to admit it or nothing this crate produces verifies.
example : 1 ≤ params.KAPPA.val := by simp [params.KAPPA]

-- `Y^4 - W` is irreducible over `F_q` for non-square `W` exactly when `q ≡ 1 mod
-- 4`, which is what makes the quartic extension a field.
example : params.Q.val % 4 = 1 := by simp [params.Q]

-- The evaluation-split shapes. The two variable counts are the `r`/`m` of the
-- Hachi bridge (`QuadEval/Bridge.lean`), and the three lengths are literals in
-- `params.rs` (a `1 << n` const would extract as a `Result`; see `RING_DEGREE`),
-- so both the power-of-two relations and the consumer's shape constraints --
-- the reshaped matrix is `blocks × messageRows` (`derivedMsgMatrix`,
-- `QuadEval/Reduction.lean`) -- are checked rather than structural.
example : params.ML_VARS_LOW = 10#usize := by simp [params.ML_VARS_LOW]
example : params.ML_VARS_HIGH = 10#usize := by simp [params.ML_VARS_HIGH]
example : params.ML_LOW_LEN = 1024#usize := by simp [params.ML_LOW_LEN]
example : params.ML_HIGH_LEN = 1024#usize := by simp [params.ML_HIGH_LEN]
example : params.ML_POLY_LEN = 1048576#usize := by simp [params.ML_POLY_LEN]

example : params.ML_LOW_LEN.val = 2 ^ params.ML_VARS_LOW.val := by
  simp [params.ML_LOW_LEN, params.ML_VARS_LOW]
example : params.ML_HIGH_LEN.val = 2 ^ params.ML_VARS_HIGH.val := by
  simp [params.ML_HIGH_LEN, params.ML_VARS_HIGH]
example : params.ML_POLY_LEN.val = params.ML_LOW_LEN.val * params.ML_HIGH_LEN.val := by
  simp [params.ML_POLY_LEN, params.ML_LOW_LEN, params.ML_HIGH_LEN]
example : params.ML_LOW_LEN.val = params.BLOCKS.val := by
  simp [params.ML_LOW_LEN, params.BLOCKS]
example : params.ML_HIGH_LEN.val = params.MESSAGE_ROWS.val := by
  simp [params.ML_HIGH_LEN, params.MESSAGE_ROWS]

/-! ### The protocol layer's parameters, against `Hachi/Params.lean`

The second block of `params.rs` (`OMEGA` … `M_ONE`) is the `ℓ = 30` profile ArkLib
itself states in `Hachi/Params.lean` (PR #847, the pinned rev). That file *names*
most of the values -- `hachiTau`, `hachiOmega`, `hachiN`, `honestZBound`, `params`
(`γ`, `bZero`), `mu0`, `liftKeyWidth` -- and proves the profile's side conditions
(`params_hcap`, `params_hzb`, `sumcheckWidthAtProfile{,_minimal}`), so the rows
below tie each literal to the *named* ArkLib value where one exists, and to the
defining arithmetic (`rlinCW/CT/CZ/Rows`, `digitOnesValue`, `balancedDigitCapacity`,
`rhoDigitCount`) otherwise. The house rule's one exception is `M_ONE`: ArkLib keeps
`m₁` free under `n₀ ≤ 2^m₁` and the profile names no value, so its rows are the
coverage inequality and its minimality, nothing more. -/

section ProtocolParams
open ArkLib.Lattices.Ajtai ArkLib.Lattices.Ajtai.InnerOuter

-- The extracted constants, as literals.
example : params.OMEGA = 16#u64 := by simp [params.OMEGA]
example : params.D_ROWS = 1#usize := by simp [params.D_ROWS]
example : params.B_ZERO = 16#u64 := by simp [params.B_ZERO]
example : params.CHAIN_GAMMA = 15#u64 := by simp [params.CHAIN_GAMMA]
example : params.HALF_BASE = 8#u64 := by simp [params.HALF_BASE]
example : params.BALANCED_SHIFT = 2290649224#u64 := by simp [params.BALANCED_SHIFT]
example : params.SB_HI = 7#u64 := by simp [params.SB_HI]
example : params.Z_DIGITS = 5#usize := by simp [params.Z_DIGITS]
example : params.Z_BOUND = 131072#u64 := by simp [params.Z_BOUND]
example : params.Z_BALANCED_SHIFT = 559240#u64 := by simp [params.Z_BALANCED_SHIFT]
example : params.RLIN_CW = 8192#usize := by simp [params.RLIN_CW]
example : params.RLIN_CT = 8192#usize := by simp [params.RLIN_CT]
example : params.RLIN_CZ = 40960#usize := by simp [params.RLIN_CZ]
example : params.RLIN_COLS = 57344#usize := by simp [params.RLIN_COLS]
example : params.RLIN_ROWS = 5#usize := by simp [params.RLIN_ROWS]
example : params.D_QUAD_COLS = 8192#usize := by simp [params.D_QUAD_COLS]
example : params.LIFT_COLS = 57384#usize := by simp [params.LIFT_COLS]
example : params.M_ZERO = 26#usize := by simp [params.M_ZERO]
example : params.M_ONE = 3#usize := by simp [params.M_ONE]
example : params.ROUND_NODES = 33#usize := by simp [params.ROUND_NODES]
example : params.ROUND_NODES_ALPHA = 3#usize := by simp [params.ROUND_NODES_ALPHA]

-- The round messages' node counts are the per-round degree bounds plus one:
-- `roundDegZero b = 2b` for the range summand (`Constraints.lean:87`) and
-- `roundDegAlpha = 2` for the linear one (`:90`). `2 * 16 + 1` in
-- `ROUND_NODES`'s docstring is now a checked relation against the named bound,
-- as is the `3` that is deliberately *not* a prefix of the range side.
example : params.ROUND_NODES.val = roundDegZero params.GADGET_BASE.val + 1 := by
  simp [params.ROUND_NODES, params.GADGET_BASE, roundDegZero]
example : params.ROUND_NODES_ALPHA.val = roundDegAlpha + 1 := by
  simp [params.ROUND_NODES_ALPHA, roundDegAlpha]

-- `ω`, and `κ = 2ω`: the weak-opening bound is the double of the sampled one, and
-- the `2 * 16` in `KAPPA`'s docstring is now a checked relation.
example : params.OMEGA.val = HachiParams.hachiOmega := by
  simp [params.OMEGA, HachiParams.hachiOmega]
example : params.KAPPA.val = 2 * params.OMEGA.val := by simp [params.KAPPA, params.OMEGA]

-- `n_D`, and the chain's range parameters at `HonestRangeParams.ofPinnedDigitBase b`:
-- `bZero = b`, `γ = bZero − 1` -- one below the weak-opening `GAMMA = b`, and the
-- two must never be confused (F1 of the Stage 2 scoping document).
example : params.D_ROWS.val = HachiParams.hachiN := by simp [params.D_ROWS, HachiParams.hachiN]
example : params.B_ZERO.val = HachiParams.params.bZero := by
  simp [params.B_ZERO, HachiParams.params_bZero, HachiParams.hachiB]
example : params.CHAIN_GAMMA.val = HachiParams.params.γ := by
  simp [params.CHAIN_GAMMA, HachiParams.params_gamma, HachiParams.hachiB]
example : params.CHAIN_GAMMA.val = params.B_ZERO.val - 1 := by
  simp [params.CHAIN_GAMMA, params.B_ZERO]
example : params.CHAIN_GAMMA.val + 1 = params.GAMMA.val := by
  simp [params.CHAIN_GAMMA, params.GAMMA]

-- The balanced digit constants. `HALF_BASE = ⌊b/2⌋`; `BALANCED_SHIFT` is
-- `balancedShift 16 8` read in `ℕ`: `⌊b/2⌋ · digitOnesValue b δ`, and strictly below
-- `q`, so its `ZMod q` image is the literal itself (no reduction step to audit).
example : params.HALF_BASE.val = params.GADGET_BASE.val / 2 := by
  simp [params.HALF_BASE, params.GADGET_BASE]
example : params.BALANCED_SHIFT.val
    = params.GADGET_BASE.val / 2 * digitOnesValue params.GADGET_BASE.val params.GADGET_DIGITS.val := by
  simp [params.BALANCED_SHIFT, params.GADGET_BASE, params.GADGET_DIGITS, digitOnesValue,
    Finset.sum_range_succ]
example : params.BALANCED_SHIFT.val < params.Q.val := by simp [params.BALANCED_SHIFT, params.Q]

-- The paper's balanced digit box `S_b = [⌈-b/2⌉, ⌈b/2⌉-1]` (`InSb`,
-- `QuadEval/Reduction.lean`), at `β := b`. Its endpoints are `β/2` and
-- `(β+1)/2 - 1` in `ℕ` division and truncated `ℕ` subtraction. The lower one
-- *is* `HALF_BASE` (tied just above) -- the same quantity `⌊b/2⌋`, not a
-- value-8 collision -- so only the upper one needs a name of its own.
example : params.SB_HI.val = (params.GADGET_BASE.val + 1) / 2 - 1 := by
  simp [params.SB_HI, params.GADGET_BASE]
-- The box is ASYMMETRIC: its width is `b`, but `-⌊b/2⌋` is admissible and
-- `+⌊b/2⌋` is not. A check written on a magnitude cannot express that.
example : params.HALF_BASE.val ≠ params.SB_HI.val := by
  simp [params.HALF_BASE, params.SB_HI]

-- `τ`, by name, and what sizes it: `Z_BOUND` is `honestZBound = 2ʳ·ω·⌊b/2⌋` (so `hzb`
-- holds with equality), it fits the balanced capacity of `τ` digits (`hcap`) and not
-- of `τ − 1` (`tau_minimal`; that capacity is exactly [NOZ26] Fig. 9's `30583`), and
-- `b^τ < q` -- so this is a *bounded* decomposition, never a full-width one.
example : params.Z_DIGITS.val = HachiParams.hachiTau := by
  simp [params.Z_DIGITS, HachiParams.hachiTau]
example : params.Z_BOUND.val = HachiParams.honestZBound := by
  rw [HachiParams.honestZBound_eq]; simp [params.Z_BOUND]
example : params.Z_BOUND.val
    = 2 ^ params.ML_VARS_LOW.val * params.OMEGA.val * params.HALF_BASE.val := by
  simp [params.Z_BOUND, params.ML_VARS_LOW, params.OMEGA, params.HALF_BASE]
example : params.Z_BOUND.val ≤ balancedDigitCapacity params.GADGET_BASE.val params.Z_DIGITS.val := by
  have h := HachiParams.balancedDigitCapacity_eq
  simp only [HachiParams.hachiB, HachiParams.hachiTau] at h
  simp [params.Z_BOUND, params.GADGET_BASE, params.Z_DIGITS, h]
example : ¬ (params.Z_BOUND.val
    ≤ balancedDigitCapacity params.GADGET_BASE.val (params.Z_DIGITS.val - 1)) := by
  have h := HachiParams.balancedDigitCapacity_four_eq
  simp only [HachiParams.hachiB] at h
  simp [params.Z_BOUND, params.GADGET_BASE, params.Z_DIGITS, h]
example : params.GADGET_BASE.val ^ params.Z_DIGITS.val < params.Q.val := by
  simp [params.GADGET_BASE, params.Z_DIGITS, params.Q]
example : params.Z_BALANCED_SHIFT.val
    = params.GADGET_BASE.val / 2 * digitOnesValue params.GADGET_BASE.val params.Z_DIGITS.val := by
  have h := HachiParams.digitOnesValue_eq
  simp only [HachiParams.hachiB, HachiParams.hachiTau] at h
  simp [params.Z_BALANCED_SHIFT, params.GADGET_BASE, params.Z_DIGITS, h]

-- The Eq. (20) block system: the three column blocks and their sum `μ₀` (by name:
-- `mu0`), the row count `n₀`, and the QuadEval `D` width.
example : params.RLIN_CW.val = rlinCW params.GADGET_DIGITS.val params.ML_VARS_LOW.val := by
  simp [params.RLIN_CW, params.GADGET_DIGITS, params.ML_VARS_LOW, rlinCW]
example : params.RLIN_CT.val
    = rlinCT params.INNER_ROWS.val params.GADGET_DIGITS.val params.ML_VARS_LOW.val := by
  simp [params.RLIN_CT, params.INNER_ROWS, params.GADGET_DIGITS, params.ML_VARS_LOW, rlinCT]
example : params.RLIN_CZ.val
    = rlinCZ params.GADGET_DIGITS.val params.Z_DIGITS.val params.ML_VARS_HIGH.val := by
  simp [params.RLIN_CZ, params.GADGET_DIGITS, params.Z_DIGITS, params.ML_VARS_HIGH, rlinCZ]
example : params.RLIN_COLS.val = HachiParams.mu0 := by
  rw [HachiParams.mu0_eq]; simp [params.RLIN_COLS]
example : params.RLIN_COLS.val = params.RLIN_CW.val + (params.RLIN_CT.val + params.RLIN_CZ.val) := by
  simp [params.RLIN_COLS, params.RLIN_CW, params.RLIN_CT, params.RLIN_CZ]
example : params.RLIN_ROWS.val
    = rlinRows params.INNER_ROWS.val params.OUTER_ROWS.val params.D_ROWS.val := by
  simp [params.RLIN_ROWS, params.INNER_ROWS, params.OUTER_ROWS, params.D_ROWS, rlinRows]
example : params.D_QUAD_COLS.val = params.BLOCKS.val * params.GADGET_DIGITS.val := by
  simp [params.D_QUAD_COLS, params.BLOCKS, params.GADGET_DIGITS]

-- The lift key width, by name (`liftKeyWidth`), and its derivation: the quotient
-- digit count `rhoDigitCount q bZero = ⌈log₁₆ q⌉` *is* `GADGET_DIGITS` (via the
-- profile's `clog_eq_delta`), which is why `params.rs` carries no second name for 8.
example : params.LIFT_COLS.val = HachiParams.liftKeyWidth := by
  rw [HachiParams.liftKeyWidth_eq]; simp [params.LIFT_COLS]
example : rhoDigitCount params.Q.val params.B_ZERO.val = params.GADGET_DIGITS.val := by
  have h := HachiParams.clog_eq_delta
  simp only [HachiParams.hachiB, HachiParams.hachiQ, HachiParams.hachiDelta] at h
  simp [rhoDigitCount, params.Q, params.B_ZERO, params.GADGET_DIGITS, h]
example : params.LIFT_COLS.val
    = params.RLIN_COLS.val + params.RLIN_ROWS.val * params.GADGET_DIGITS.val := by
  simp [params.LIFT_COLS, params.RLIN_COLS, params.RLIN_ROWS, params.GADGET_DIGITS]

-- The two cube widths. `M_ZERO = M + 1` at the profile's `M = 25`: the coverage
-- hypothesis `hμn : liftKeyWidth · d ≤ 2^(M+1)` holds (`sumcheckWidthAtProfile`) and
-- fails one lower (`sumcheckWidthAtProfile_minimal`). `M_ONE` has no ArkLib name:
-- coverage `n₀ ≤ 2^m₁` and minimality are all that can be checked.
example : params.M_ZERO.val = 25 + 1 := by simp [params.M_ZERO]
example : HachiParams.liftKeyWidth * HachiParams.hachiD ≤ 2 ^ params.M_ZERO.val := by
  rw [HachiParams.liftKeyWidth_eq]; simp [params.M_ZERO, HachiParams.hachiD]
example : params.LIFT_COLS.val * params.RING_DEGREE.val ≤ 2 ^ params.M_ZERO.val := by
  simp [params.LIFT_COLS, params.RING_DEGREE, params.M_ZERO]
example : ¬ (params.LIFT_COLS.val * params.RING_DEGREE.val ≤ 2 ^ (params.M_ZERO.val - 1)) := by
  simp [params.LIFT_COLS, params.RING_DEGREE, params.M_ZERO]
example : params.RLIN_ROWS.val ≤ 2 ^ params.M_ONE.val := by simp [params.RLIN_ROWS, params.M_ONE]
example : ¬ (params.RLIN_ROWS.val ≤ 2 ^ (params.M_ONE.val - 1)) := by
  simp [params.RLIN_ROWS, params.M_ONE]

end ProtocolParams

/-! ## 2. The `cpoly` field layer is transparent, not axiomatized

This is the finding of Workstream 0 and the reason the field is a cargo
dependency rather than a vendored copy of `field.rs`. Charon's default whitelist
is the local crate, so a plain `charon cargo --preset=aeneas` puts

    axiom cpoly.field.Fp : Type
    axiom cpoly.field.Fp.ZERO : Result cpoly.field.Fp
    axiom cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add : ...

in `Generated.lean` -- an uninterpreted field with an uninterpreted addition,
about which nothing can be proved, and three `axiom`s that would show up under
every `#print axioms` in § 4 forever. `make extract` passes `--include 'cpoly::_'`
instead, and the examples below are what would break if that flag were ever
dropped: an `axiom` has no body and no projections, so not one of them would
typecheck against one. -/

-- The newtype is free on this side: Aeneas extracts a single-field tuple struct
-- as a `@[reducible]` abbreviation, so `Fp` *is* `U64` as far as proofs care.
example : cpoly.field.Fp = Std.U64 := rfl

-- ### The `Shared<n>` mangling, pinned
--
-- Target 5's round message multiplies univariate polynomials (`&p * &q` and
-- `&p * scalar` in `sumcheck::honest_compute_g`), and cpoly implements those
-- **by reference**. Aeneas mangles a by-reference operator impl's `Self` into a
-- synthetic `Shared<n><T>`, so those two impls arrived as
--
--     Shared0UnivariatePoly.Insts.CoreOpsArithMulExt4UnivariatePoly.mul
--     Shared1UnivariatePoly.Insts.CoreOpsArithMulShared0UnivariatePolyUnivariatePoly.mul
--
-- **Candidate P (2026-09-16) removed the second.** `&p * &q` is now
-- `sumcheck::poly_mul`, this crate's own item, so cpoly's polynomial multiply
-- is no longer reachable and its pin below is deleted rather than kept pointing
-- at a name the model does not define. This is the § "The model contains what
-- the crate *reaches*" hazard arriving as a *build failure* instead of silent
-- rot, which is the outcome the pin was written for -- the ascription stopped
-- typechecking the moment the item left the model.
--
-- What remains needs saying, because the hazard is not gone, only smaller. With
-- one `Shared<n>` impl left there is nothing for the index to swap *with*, so
-- the pin below no longer distinguishes two impls; it asserts that `Shared0` is
-- still the scalar multiply and not something a later extraction attached that
-- index to. Candidate P also added `UnivariatePoly`'s `Index` impl to the model,
-- and that one needs no pin: it is an impl on the type, not by reference, so it
-- carries no `Shared<n>` mangling at all
-- (`cpoly.univariate.UnivariatePoly.Insts.CoreOpsIndexIndexUsizeExt4.index`).
--
-- and every statement about a `RoundMsg` is about those names. A *name* is not
-- a body: the mangling is an Aeneas artefact and the index is positional, so a
-- future extraction could plausibly attach `Shared0`/`Shared1` to different
-- impls and a spec bound to the old name would silently be about the new one.
-- These ascriptions are what makes that a build failure. They were absent from
-- 2026-09-08, when target 5 first pulled the impls in, until 2026-09-09 --
-- the `aeneas-spec-author` skill predicted exactly this ("if a by-reference
-- operator impl is ever added to `hachi`, the `Shared<n><T>` mangling returns
-- ... and `Check.lean` has no alias-pin section, so the pins need one added").
--
-- Scalar multiply: a polynomial and a field element in, a polynomial out.
example : cpoly.univariate.UnivariatePoly → cpoly.field.Ext4 →
    Result cpoly.univariate.UnivariatePoly :=
  Shared0UnivariatePoly.Insts.CoreOpsArithMulExt4UnivariatePoly.mul

-- (The polynomial-multiply pin that stood here until 2026-09-16 is gone with the
-- impl it pinned; see the note above. A body pin -- that the surviving impl
-- delegates to its own loop -- is owed and would be strictly stronger than an
-- ascription; it needs `Result`'s `ok`/`do` notation, which this file does not
-- open.)

-- The modulus travelled across the crate boundary as a value, not a symbol.
example : cpoly.field.P = 4294967197#u64 := by simp [cpoly.field.P]

-- ... and it is the same modulus this crate's own parameter names. If these two
-- ever disagree, every proof bridging the two layers is about two fields.
example : cpoly.field.P = params.Q := by simp [cpoly.field.P, params.Q]

-- The addition has a body, and it is the Rust one. **Updated by the 2026-09-16
-- cpoly bump**: it was `(self + rhs) % P`, and it is now a *conditional
-- subtraction*, which is the whole point of the bump -- `a + b < 2q < 2^33` for
-- reduced operands, so one compare-and-subtract replaces a `u64` division. This
-- is the example that an axiom could not satisfy, and the fact that it had to be
-- rewritten is the pin doing its job.
example (a b : cpoly.field.Fp) :
    cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add a b
      = (do let s ← a + b
            if s ≥ cpoly.field.P then (do let d ← s - cpoly.field.P; Result.ok d)
            else Result.ok s) := by
  simp [cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add]

-- The other three operator impls, for the same reason: each has a body, and it is
-- the Rust one. `sub` now *branches* instead of adding the modulus
-- unconditionally -- it subtracts directly when it can and borrows `P` only when
-- it must -- and `neg` branches on zero where it used to rely on an outer `% P`
-- to send `0` to `0` rather than to `P`. Both visible here, which is what
-- "transparent" means in practice.
example (a b : cpoly.field.Fp) :
    cpoly.field.Fp.Insts.CoreOpsArithSubFpFp.sub a b
      = (if a ≥ b then (do let d ← a - b; Result.ok d)
         else (do let s ← a + cpoly.field.P; let d ← s - b; Result.ok d)) := by
  simp [cpoly.field.Fp.Insts.CoreOpsArithSubFpFp.sub]

example (a b : cpoly.field.Fp) :
    cpoly.field.Fp.Insts.CoreOpsArithMulFpFp.mul a b
      = (do let p ← a * b; let r ← p % cpoly.field.P; Result.ok r) := by
  simp [cpoly.field.Fp.Insts.CoreOpsArithMulFpFp.mul]

-- `Ext4` -- the quartic extension, the case a one-field newtype does not cover.
--
-- This block was absent for most of the crate's life, and the reason it is back is
-- the condition its own removal note named: "`Ext4` enters with the *protocol*
-- layer, which commits to multilinear polynomials over the extension". That layer
-- has arrived. `src/zerocheck.rs` is the first module whose carrier is the
-- extension field, so charon now follows `cpoly::field::Ext4` and
-- `cpoly::multilinear` into the model -- the `--include 'cpoly::_'` whitelist
-- decides which foreign items *may* be translated, and what is actually
-- translated is what the local crate reaches. See NOTES.md § "The model contains
-- what the crate reaches" and § "Target 4 opens".

example (a b c d : cpoly.field.Fp) : cpoly.field.Ext4 :=
  { c0 := a, c1 := b, c2 := c, c3 := d }

-- The base-field embedding `φF` every `wTable` branch goes through: the constant
-- coefficient, and three zeros.
example (a : cpoly.field.Fp) :
    cpoly.field.Ext4.from_base a
      = Result.ok { c0 := a, c1 := cpoly.field.Fp.ZERO, c2 := cpoly.field.Fp.ZERO,
                    c3 := cpoly.field.Fp.ZERO } := by
  simp [cpoly.field.Ext4.from_base]

-- Addition is coefficientwise, through the `Fp` addition asserted above -- so a
-- single `Ext4` add is four modular reductions, which is the arithmetic the cost
-- model in the target-4 brief is written against.
example (a b : cpoly.field.Ext4) :
    cpoly.field.Ext4.Insts.CoreOpsArithAddExt4Ext4.add a b
      = (do let f ← cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add a.c0 b.c0
            let f1 ← cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add a.c1 b.c1
            let f2 ← cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add a.c2 b.c2
            let f3 ← cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add a.c3 b.c3
            Result.ok { c0 := f, c1 := f1, c2 := f2, c3 := f3 }) := by
  simp [cpoly.field.Ext4.Insts.CoreOpsArithAddExt4Ext4.add]

-- `impl Mul<Ext4> for Fp` -- the **mixed** product, and the second impl in the
-- model whose mangled name ends `MulExt4Ext4.mul`. Two things separate it from
-- `Ext4`'s own: the namespace (`cpoly.field.Fp.Insts` against
-- `cpoly.field.Ext4.Insts`), and the body -- four `Fp` multiplies, one per
-- coefficient, against the quartic multiply's nineteen. That count is what
-- candidate I's round 0 is costed against, and `Ext.fp_ext_mul_spec` is stated
-- about the name asserted here.
example (a : cpoly.field.Fp) (b : cpoly.field.Ext4) :
    cpoly.field.Fp.Insts.CoreOpsArithMulExt4Ext4.mul a b
      = (do let f ← cpoly.field.Fp.Insts.CoreOpsArithMulFpFp.mul a b.c0
            let f1 ← cpoly.field.Fp.Insts.CoreOpsArithMulFpFp.mul a b.c1
            let f2 ← cpoly.field.Fp.Insts.CoreOpsArithMulFpFp.mul a b.c2
            let f3 ← cpoly.field.Fp.Insts.CoreOpsArithMulFpFp.mul a b.c3
            Result.ok { c0 := f, c1 := f1, c2 := f2, c3 := f3 }) := by
  simp [cpoly.field.Fp.Insts.CoreOpsArithMulExt4Ext4.mul]

-- `W`, the extension modulus's constant in `Y^4 - W`, **used to be pinned here**
-- against this crate's own `params.EXT_W`. The 2026-09-16 cpoly bump removed it
-- from the model: the new `Ext4::mul` folds the `Y^4 = 2` wrap into
-- `add_double_product` instead of multiplying by a `W` constant, and the only
-- upstream reader of `W` that remains is `mul_by_w`, which this crate does not
-- reach -- so the whitelist never translates it (NOTES § "The model contains
-- what the crate *reaches*").
--
-- The claim has not been dropped, it has moved. `params.EXT_W = 2#u64` is still
-- asserted in § 1 above, and the `2` on the cpoly side is now carried by
-- `add_double_product_spec`'s postcondition (`wideK acc + 2 * toK a * toK b`),
-- which is audited in § 4. What is genuinely lost is the *equality of the two
-- constants as constants*; what replaces it is that the only arithmetic `W` ever
-- justified is the doubling, and that doubling is proved.

-- The multiplication's *body* is deliberately not transcribed here, unlike the
-- four `Fp` operators: it is 19 `Fp` multiplies and 13 adds, and copying it into
-- this tripwire would duplicate cpoly's own proved code without adding a claim.
-- What guards it is § 4's axiom audit, which is global: `--include 'cpoly::_'`
-- is all-or-nothing, so an `Ext4.mul` that arrived as an `axiom` would take
-- `Fp.add` (asserted above) with it, and would in any case print in § 4. The one
-- shape worth recording in prose, because the cost model turns on it: the
-- `W`-foldback lands on `c0`, `c1` and `c2` only -- `c3` is the plain `t3` sum --
-- so the `Y^4 = W` reduction costs three extra multiplies, not four.

-- Deliberately *not* asserted here: that `add 1 2` evaluates to `ok 3`. It is
-- true, but `simp` and `decide` do not get there on their own -- the checked
-- `U64` arithmetic needs Aeneas's `progress`/`scalar_tac` machinery, which
-- arrives with the first real spec. The structural equality above is the claim
-- that matters for § 2 anyway: it is the one an `axiom` cannot satisfy.

/-! ## 2b. The modules arrived, with the shapes the proofs will need

Structural, not mathematical: each check below is a type ascription or an `rfl`,
and what it rules out is a module that silently failed to extract, or extracted
behind a wrapper that the equivalence file would then have to unfold. Two facts
are worth having on record:

* the three container newtypes (`Rq`, `PolyVec`, `PolyMatrix`) are `@[reducible]`
  aliases for `Vec`, so a statement about a `Rq` *is* a statement about a
  `Vec cpoly.field.Fp` and nothing has to be transported across a wrapper;
* every operation is `Result`-valued, i.e. fallible in the model, so each spec has
  a totality obligation to discharge and not merely an equality to prove. -/

example : ring.Rq = alloc.vec.Vec cpoly.field.Fp := rfl
example : linalg.PolyVec = alloc.vec.Vec ring.Rq := rfl
example : linalg.PolyMatrix = alloc.vec.Vec linalg.PolyVec := rfl

-- The ring layer.
example : Result ring.Rq := ring.Rq.zero
example (a b : ring.Rq) : Result ring.Rq := ring.Rq.add a b
example (a b : ring.Rq) : Result ring.Rq := ring.Rq.mul a b
example (a : ring.Rq) (k : Std.Usize) : Result cpoly.field.Fp := ring.Rq.coeff a k

-- The linear algebra layer.
example (u v : linalg.PolyVec) : Result ring.Rq := linalg.PolyVec.dot u v
example (a : linalg.PolyMatrix) (v : linalg.PolyVec) : Result linalg.PolyVec :=
  linalg.PolyMatrix.mat_vec_mul a v
example (xs : alloc.vec.Vec linalg.PolyVec) : Result linalg.PolyVec := linalg.flatten_blocks xs

-- The gadget layer.
example (c : cpoly.field.Fp) (e : Std.Usize) : Result cpoly.field.Fp := gadget.digit_at c e
example (rows : Std.Usize) (v : linalg.PolyVec) : Result linalg.PolyVec :=
  gadget.gadget_mul rows v
example (x : linalg.PolyVec) : Result linalg.PolyVec := gadget.gadget_decompose x

-- The balanced digit layer: the Hachi gadget inverse `G⁻¹` proper
-- (`balancedZmodDigitDecomposition`), and the bounded `z`-side map at its own
-- width. All three digit maps are `Fp`-valued at one index, so their `_spec`s
-- are one family; what differs is where the `⌊b/2⌋` shift goes.
example (c : cpoly.field.Fp) (e : Std.Usize) : Result cpoly.field.Fp :=
  gadget.balanced_digit_at c e
example (c : cpoly.field.Fp) : Result (alloc.vec.Vec cpoly.field.Fp) :=
  gadget.balanced_digit_decompose c
example (x : linalg.PolyVec) : Result linalg.PolyVec := gadget.balanced_gadget_decompose x
example (c : cpoly.field.Fp) (e : Std.Usize) : Result cpoly.field.Fp :=
  gadget.bounded_z_digit_at c e

-- The `z`-side gadget siblings at `Z_DIGITS = 5`. A separate pair from the
-- full-width ones, not the same functions at another width: the digit maps
-- differ, and the bounded decomposition's round trip is conditional.
example (x : linalg.PolyVec) : Result linalg.PolyVec := gadget.bounded_z_gadget_decompose x
example (rows : Std.Usize) (v : linalg.PolyVec) : Result linalg.PolyVec :=
  gadget.gadget_mul_z rows v

-- The ring-switching layer. A quotient digit is an `Rq`, i.e. a `Vec Fp` of the
-- ring degree -- the `Rq.ofFinCoeff` shape `rhoDigits` builds, carried through
-- `Rq::from_coeffs`.
example (rho : ring.Rq) (u : Std.Usize) : Result ring.Rq := ringswitch.rho_digits rho u

-- The full ring-switch link. `QuotientRow` erases to the same coefficient
-- vector as `Rq`, while its Rust newtype prevents quotient-ring operations from
-- being exposed on a raw quotient polynomial. The two terminal checks live in
-- `endpiece`, matching ArkLib's source split.
example : ringswitch.QuotientRow = ring.Rq := rfl
example (rho : ringswitch.QuotientRow) : Result ring.Rq :=
  ringswitch.QuotientRow.to_rq rho
example (rho : alloc.vec.Vec ringswitch.QuotientRow) (j : Std.Usize) : Result ring.Rq :=
  ringswitch.rho_digit_as_rq rho j
example (z : linalg.PolyVec) (rho : alloc.vec.Vec ringswitch.QuotientRow) :
    Result ringswitch.LiftedWitness := ringswitch.LiftedWitness.new z rho
example (w : ringswitch.LiftedWitness) : Result linalg.PolyVec := ringswitch.lift_message w
example (dKey : linalg.PolyMatrix) (w : ringswitch.LiftedWitness) : Result linalg.PolyVec :=
  ringswitch.lift_commit dKey w
example (rho : alloc.vec.Vec ringswitch.QuotientRow) : Result Bool :=
  endpiece.rho_digits_short_check rho
example (w : ringswitch.LiftedWitness) : Result Bool := endpiece.lift_short_check w

-- The end piece (target 6): the terminal statement and the single decision
-- procedure of the closing link. Three shape facts the equivalence proofs will
-- lean on:
--
-- * `WEvalStatement` is a three-field record whose `point` is a plain
--   `Vec Ext4` -- the specification's `Fin m0 -> F` -- so `m0` is the vector's
--   length and nothing about the arity is carried separately;
-- * `end_piece_check` extracts as the specification's own `&&`-nesting: an `if`
--   on `PolyVec.equals`, then an `if` on `lift_short_check`, then the derived
--   `PartialEq for Ext4` (`CoreCmpPartialEqExt4.eq`, whitelisted through
--   `cpoly::_` like every other field item, so it is a `def` and not an axiom);
-- * the prover message and the transcript read-off are both `ok` of their
--   argument -- identities, as `endPieceProver`/`endPieceWitness` are.
example (t : linalg.PolyVec) (point : alloc.vec.Vec cpoly.field.Ext4) (value : cpoly.field.Ext4) :
    Result endpiece.WEvalStatement := endpiece.WEvalStatement.new t point value
example (stmt : endpiece.WEvalStatement) : Result linalg.PolyVec :=
  endpiece.WEvalStatement.impl.t stmt
example (stmt : endpiece.WEvalStatement) : Result (alloc.vec.Vec cpoly.field.Ext4) :=
  endpiece.WEvalStatement.impl.point stmt
example (stmt : endpiece.WEvalStatement) : Result cpoly.field.Ext4 :=
  endpiece.WEvalStatement.impl.value stmt
example (a b : cpoly.field.Ext4) : Result Bool :=
  cpoly.field.Ext4.Insts.CoreCmpPartialEqExt4.eq a b
example (dKey : linalg.PolyMatrix) (stmt : endpiece.WEvalStatement)
    (w : ringswitch.LiftedWitness) : Result Bool := endpiece.end_piece_check dKey stmt w
example (w : ringswitch.LiftedWitness) : Result ringswitch.LiftedWitness :=
  endpiece.end_piece_prove w
example (stmt : endpiece.WEvalStatement) (w : ringswitch.LiftedWitness) :
    Result ringswitch.LiftedWitness := endpiece.end_piece_witness stmt w
example (w : ringswitch.LiftedWitness) : endpiece.end_piece_prove w = Result.ok w := rfl
example (stmt : endpiece.WEvalStatement) (w : ringswitch.LiftedWitness) :
    endpiece.end_piece_witness stmt w = Result.ok w := rfl

-- The zero-check layer, and the crate's first extension-field carrier. Two shape
-- facts the equivalence proofs will lean on:
--
-- * `MultilinearEvals` is a plain alias for `Vec Ext4`, so a statement about
--   `hZero`'s table *is* a statement about a vector and nothing is transported
--   across a wrapper -- the same property `Rq`/`PolyVec`/`PolyMatrix` have above;
-- * `w_table` takes the cube point as its flat `Usize` index, which is what makes
--   the `finFunctionFinEquiv`/`.symm` cancellation of `wTable_zRow` a definitional
--   step rather than a rewrite.
example : cpoly.multilinear.MultilinearEvals = alloc.vec.Vec cpoly.field.Ext4 := rfl
example (values : alloc.vec.Vec cpoly.field.Ext4) :
    cpoly.multilinear.MultilinearEvals.from_values values = Result.ok values := by
  simp [cpoly.multilinear.MultilinearEvals.from_values]
example (v : cpoly.field.Ext4) : Result cpoly.field.Ext4 := zerocheck.range_product v
example (w : ringswitch.LiftedWitness) (idx : Std.Usize) : Result cpoly.field.Ext4 :=
  zerocheck.w_table w idx
example (w : ringswitch.LiftedWitness) (m0 : Std.Usize) :
    Result cpoly.multilinear.MultilinearEvals := zerocheck.c_w_table_mle w m0
example (w : ringswitch.LiftedWitness) (m0 : Std.Usize)
    (a : alloc.vec.Vec cpoly.field.Ext4) : Result cpoly.field.Ext4 :=
  zerocheck.w_table_mle_eval w m0 a
example (w : ringswitch.LiftedWitness) (m0 : Std.Usize) :
    Result cpoly.multilinear.MultilinearEvals := zerocheck.h_zero w m0
example (w : ringswitch.LiftedWitness) (m0 : Std.Usize) : Result Bool :=
  zerocheck.h_zero_is_zero w m0

-- The α side, and the crate's first *mixed* evaluation: `Fp` coefficients at an
-- `Ext4` point. Three shape facts the proofs lean on:
--
-- * `RlinStatement` is a named-fields structure, so the extracted model reads
--   `s.m`/`s.yvec`/`s.bound` as projections rather than through a `Vec` of
--   heterogeneous parts -- the reason `arklib-analyze` § 6 prescribes that shape
--   for a small fixed carrier;
-- * `c_eval_at` takes the polynomial by reference and the point by value, so the
--   spec quantifies over an `Rq` and an `Ext4` and not over two borrows;
-- * `c_eval_at_modulus` takes *no* polynomial: `Φ.φ = X^d + 1` has `d + 1`
--   coefficients and no `Rq` can hold it, which is why it is a separate entry
--   point and not a call with the modulus passed in.
example (m : linalg.PolyMatrix) (yvec : linalg.PolyVec) (bound : Std.U64) :
    Result ringswitch.RlinStatement := ringswitch.RlinStatement.new m yvec bound
example (s : ringswitch.RlinStatement) : Result linalg.PolyMatrix :=
  ringswitch.RlinStatement.impl.m s
example (alpha : cpoly.field.Ext4) (p : ring.Rq) : Result cpoly.field.Ext4 :=
  ringswitch.c_eval_at alpha p
example (alpha : cpoly.field.Ext4) : Result cpoly.field.Ext4 :=
  ringswitch.c_eval_at_modulus alpha
example (c : cpoly.field.Fp) : Result cpoly.field.Fp := zerocheck.range_product_base c

-- The honest lift prover (`RingSwitch/ComputableWitness.lean`), the chain's last
-- item to be translated (2026-09-11). Two shape facts: the unreduced row sum is a `Vec Fp` of
-- `2N - 1` words -- a `CPolynomial (ZMod q)` in the `Raw` array reading, the
-- first carrier in this crate for a product that is *not* folded back into
-- `Rq` -- and the division by the modulus returns the `N`-word quotient that
-- `QuotientRow::new` wraps. The two helpers are private and still extracted.
example (a b : ring.Rq) : Result (alloc.vec.Vec cpoly.field.Fp) := ringswitch.long_mul a b
example (s : ringswitch.RlinStatement) (z : linalg.PolyVec) (i : Std.Usize) :
    Result (alloc.vec.Vec cpoly.field.Fp) := ringswitch.c_row_sum s z i
example (p : alloc.vec.Vec cpoly.field.Fp) : Result (alloc.vec.Vec cpoly.field.Fp) :=
  ringswitch.div_by_modulus p
example (s : ringswitch.RlinStatement) (z : linalg.PolyVec) (i : Std.Usize) :
    Result ringswitch.QuotientRow := ringswitch.c_quotient s z i
example (s : ringswitch.RlinStatement) (z : linalg.PolyVec) : Result ringswitch.LiftedWitness :=
  ringswitch.honest_lift_witness s z
example (alpha : cpoly.field.Ext4) (l : Std.Usize) : Result cpoly.field.Ext4 :=
  zerocheck.alpha_tilde alpha l
example (tau1 : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize) :
    Result cpoly.field.Ext4 := zerocheck.eq_weight tau1 i
example (s : ringswitch.RlinStatement) (alpha : cpoly.field.Ext4)
    (i u : Std.Usize) : Result cpoly.field.Ext4 :=
  zerocheck.m_alpha_tilde s alpha i u
example (s : ringswitch.RlinStatement) (alpha : cpoly.field.Ext4)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) (idx : Std.Usize) :
    Result cpoly.field.Ext4 := zerocheck.alpha_public_evals s alpha tau1 idx
example (s : ringswitch.RlinStatement) (alpha : cpoly.field.Ext4)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) : Result cpoly.field.Ext4 :=
  zerocheck.zc_target_alpha s alpha tau1

-- The `H_alpha` side, reached through ArkLib's *computable* `alphaDefect`
-- rather than the `noncomputable` `hAlphaEvals` it is proved equal to
-- (`ZeroCheck/Constraints.lean:771`). Two shape facts follow from that choice
-- and are worth pinning:
--
-- * `alpha_contract` takes the witness, not a table function: the
--   specification's `T : (Fin m0 -> Fin 2) -> F` is instantiated at `wTable`,
--   which is the only instantiation the chain uses and the one the equivalence
--   theorem is stated at -- a function argument has no translation here;
-- * `h_alpha` is a `MultilinearEvals` like `h_zero`, so both constraint blocks
--   are the same carrier and `Check.lean`'s alias fact above covers both.
example (s : ringswitch.RlinStatement) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (i : Std.Usize) : Result cpoly.field.Ext4 :=
  zerocheck.alpha_contract s alpha w i
example (s : ringswitch.RlinStatement) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (i : Std.Usize) : Result cpoly.field.Ext4 :=
  zerocheck.alpha_defect s alpha w i
example (s : ringswitch.RlinStatement) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (idx : Std.Usize) : Result cpoly.field.Ext4 :=
  zerocheck.h_alpha_evals s alpha w idx
example (s : ringswitch.RlinStatement) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (m1 : Std.Usize) :
    Result cpoly.multilinear.MultilinearEvals := zerocheck.h_alpha s alpha w m1
example (s : ringswitch.RlinStatement) (alpha : cpoly.field.Ext4)
    (w : ringswitch.LiftedWitness) (m1 : Std.Usize) : Result Bool :=
  zerocheck.h_alpha_is_zero s alpha w m1

-- The sumcheck layer. Three shape facts, and the first is the one a reader of
-- this module most needs:
--
-- * the interpolation weights arrive as an `Array Std.U64 33`, not as an
--   axiomatized opaque constant -- `params.ROUND_NODE_INV` is `Array.make` of
--   thirty-three literals and is indexed with the modelled
--   `Array.index_usize`. They are literals because `cpoly` exposes no inversion
--   at either carrier, and they are *checkable* because
--   `tests/sumcheck_semantics.rs` pins each against its own denominator;
-- * a round message is a `cpoly.univariate.UnivariatePoly`, i.e. a `Vec Ext4`,
--   so the `2b + 1` node values and the interpolant live in the same carrier;
-- * `round_value_zero` takes the folded table and the `eq̃` suffix as separate
--   vectors, which is what makes the fold's `2y`/`2y+1` pairing visible in the
--   model rather than hidden inside a closure.
example : cpoly.univariate.UnivariatePoly = alloc.vec.Vec cpoly.field.Ext4 := rfl
example : Array Std.U64 33#usize := params.ROUND_NODE_INV
example (i : Std.Usize) : Result cpoly.field.Ext4 := sumcheck.round_node i
example (values : alloc.vec.Vec cpoly.field.Ext4)
    (weights : alloc.vec.Vec cpoly.field.Fp) :
    Result cpoly.univariate.UnivariatePoly := sumcheck.interpolate values weights
example (w eq : alloc.vec.Vec cpoly.field.Ext4) (node : cpoly.field.Ext4) :
    Result cpoly.field.Ext4 := sumcheck.round_value_zero w eq node
example (w eq : alloc.vec.Vec cpoly.field.Ext4) :
    Result (alloc.vec.Vec cpoly.field.Ext4) := sumcheck.round_values_zero w eq
example (w eq : alloc.vec.Vec cpoly.field.Ext4) :
    Result cpoly.univariate.UnivariatePoly := sumcheck.round_poly_zero w eq

-- The rest of the sumcheck layer, as it stands after target 5's round machinery
-- and the prover/verifier split. Four facts a re-extraction must not move:
--
-- * the three statement carriers are plain `structure`s whose accessors extract
--   under an `impl` segment -- `sumcheck.RoundStatement.impl.zc`, not a Lean
--   projection -- while the constructors are `sumcheck.<T>.new`. A spec that
--   names the wrong spelling fails here, not in a proof;
-- * the linear side has its *own* node count and weight array, `3` and
--   `Array Std.U64 3`: the weights of a node *set* depend on the whole set, so
--   `ROUND_NODE_INV_ALPHA` is not a prefix of `ROUND_NODE_INV`
--   (NOTES.md § "Target 5's round machinery");
-- * the two loops that can reject return `Option` inside `Result`: `none` is the
--   specification's `failure`, and the round-message list is a `Vec RoundMsg`;
-- * `cube_size` is `zerocheck::two_pow`'s local duplicate (a frozen item's
--   visibility cannot be widened), so it is a separate item with its own bound.
example : params.ROUND_NODES = 33#usize := by simp [params.ROUND_NODES]
example : params.ROUND_NODES_ALPHA = 3#usize := by simp [params.ROUND_NODES_ALPHA]
example : Array Std.U64 3#usize := params.ROUND_NODE_INV_ALPHA
example (rlin : ringswitch.RlinStatement) (t : linalg.PolyVec) (alpha : cpoly.field.Ext4)
    (tau0 tau1 : alloc.vec.Vec cpoly.field.Ext4) : Result sumcheck.NestedZeroCheckStmt :=
  sumcheck.NestedZeroCheckStmt.new rlin t alpha tau0 tau1
example (zc : sumcheck.NestedZeroCheckStmt) : Result (alloc.vec.Vec cpoly.field.Ext4) :=
  sumcheck.NestedZeroCheckStmt.impl.tau0 zc
example (g_zero g_alpha : cpoly.univariate.UnivariatePoly) : Result sumcheck.RoundMsg :=
  sumcheck.RoundMsg.new g_zero g_alpha
example (g : sumcheck.RoundMsg) : Result cpoly.univariate.UnivariatePoly :=
  sumcheck.RoundMsg.impl.g_zero g
example (zc : sumcheck.NestedZeroCheckStmt) (challenges : alloc.vec.Vec cpoly.field.Ext4)
    (target_zero target_alpha : cpoly.field.Ext4) : Result sumcheck.RoundStatement :=
  sumcheck.RoundStatement.new zc challenges target_zero target_alpha
example (stmt : sumcheck.RoundStatement) : Result sumcheck.NestedZeroCheckStmt :=
  sumcheck.RoundStatement.impl.zc stmt
example (vars : Std.Usize) : Result Std.Usize := sumcheck.cube_size vars
example : Result (alloc.vec.Vec cpoly.field.Fp) := sumcheck.round_node_weights
example : Result (alloc.vec.Vec cpoly.field.Fp) := sumcheck.round_node_weights_alpha
example (tau0 challenges : alloc.vec.Vec cpoly.field.Ext4) : Result cpoly.field.Ext4 :=
  sumcheck.eq_prefix tau0 challenges
example (tau0 : alloc.vec.Vec cpoly.field.Ext4) (i : Std.Usize) :
    Result (alloc.vec.Vec cpoly.field.Ext4) := sumcheck.eq_suffix_table tau0 i
example (t : cpoly.field.Ext4) : Result cpoly.univariate.UnivariatePoly :=
  sumcheck.eq_free_factor t
example (w a_tab : alloc.vec.Vec cpoly.field.Ext4) (node : cpoly.field.Ext4) :
    Result cpoly.field.Ext4 := sumcheck.round_value_alpha w a_tab node
example (w a_tab : alloc.vec.Vec cpoly.field.Ext4) :
    Result (alloc.vec.Vec cpoly.field.Ext4) := sumcheck.round_values_alpha w a_tab
example (w a_tab : alloc.vec.Vec cpoly.field.Ext4) :
    Result cpoly.univariate.UnivariatePoly := sumcheck.round_poly_alpha w a_tab
example (s : ringswitch.RlinStatement) (alpha : cpoly.field.Ext4)
    (tau1 : alloc.vec.Vec cpoly.field.Ext4) (m0 : Std.Usize) :
    Result (alloc.vec.Vec cpoly.field.Ext4) := sumcheck.alpha_public_table s alpha tau1 m0
example (stmt : sumcheck.RoundStatement) (w_tab a_tab : alloc.vec.Vec cpoly.field.Ext4)
    (i : Std.Usize) : Result sumcheck.RoundMsg := sumcheck.honest_compute_g stmt w_tab a_tab i
example (stmt : sumcheck.RoundStatement) (g : sumcheck.RoundMsg) : Result Bool :=
  sumcheck.round_check stmt g
example (stmt : sumcheck.RoundStatement) (g : sumcheck.RoundMsg) (a : cpoly.field.Ext4) :
    Result sumcheck.RoundStatement := sumcheck.round_out stmt g a
example (stmt : sumcheck.RoundStatement) (y_prime : cpoly.field.Ext4) (bound : Std.U64) :
    Result Bool := sumcheck.final_check stmt y_prime bound
example (w : ringswitch.LiftedWitness) (m0 : Std.Usize)
    (challenges : alloc.vec.Vec cpoly.field.Ext4) : Result cpoly.field.Ext4 :=
  sumcheck.honest_compute_y w m0 challenges
example (zc : sumcheck.NestedZeroCheckStmt) : Result sumcheck.RoundStatement :=
  sumcheck.nested_to_round_statement zc
example (stmt : sumcheck.RoundStatement) (w : ringswitch.LiftedWitness)
    (challenges : alloc.vec.Vec cpoly.field.Ext4) : Result (Option sumcheck.RoundStatement) :=
  sumcheck.round_loop stmt w challenges
example (stmt : sumcheck.RoundStatement) (w : ringswitch.LiftedWitness)
    (challenges : alloc.vec.Vec cpoly.field.Ext4) : Result (alloc.vec.Vec sumcheck.RoundMsg) :=
  sumcheck.honest_round_messages stmt w challenges
example (stmt : sumcheck.RoundStatement) (msgs : alloc.vec.Vec sumcheck.RoundMsg)
    (challenges : alloc.vec.Vec cpoly.field.Ext4) : Result (Option sumcheck.RoundStatement) :=
  sumcheck.round_verify_loop stmt msgs challenges

-- The composed chain (`src/chain.rs`), Stage 5's two rows. The verifier returns
-- a bare `Bool` -- the three decisions it runs, conjoined -- and the honest prover
-- returns the four wire messages as a tuple (`v`, `t`, the round messages, `y′`);
-- there is no transcript carrier, by design (`chain.rs` § "What this module
-- is"). `copy_point` is the `Vec<Ext4>` copy loop that stands in for the
-- unmodelled `clone`.
example (p : alloc.vec.Vec cpoly.field.Ext4) : Result (alloc.vec.Vec cpoly.field.Ext4) :=
  chain.copy_point p
example (pp : quadeval.PublicParamsD) (d_key : linalg.PolyMatrix)
    (poly_stmt : quadeval.PolyEvalStatement) (v c t : linalg.PolyVec)
    (alpha : cpoly.field.Ext4) (tau0 tau1 : alloc.vec.Vec cpoly.field.Ext4)
    (msgs : alloc.vec.Vec sumcheck.RoundMsg) (challenges : alloc.vec.Vec cpoly.field.Ext4)
    (y_prime : cpoly.field.Ext4) (w : ringswitch.LiftedWitness) (gamma : Std.U64)
    (b mr md ir idg zd : Std.Usize) : Result Bool :=
  chain.chain_verify pp d_key poly_stmt v c t alpha tau0 tau1 msgs challenges y_prime w
    gamma b mr md ir idg zd
example (pp : quadeval.PublicParamsD) (d_key : linalg.PolyMatrix)
    (poly_stmt : quadeval.PolyEvalStatement) (carrier_dec : linalg.PolyVec)
    (c : linalg.PolyVec) (w : ringswitch.LiftedWitness) (alpha : cpoly.field.Ext4)
    (tau0 tau1 challenges : alloc.vec.Vec cpoly.field.Ext4) (gamma : Std.U64)
    (b mr md ir idg zd : Std.Usize) :
    Result (linalg.PolyVec × linalg.PolyVec × alloc.vec.Vec sumcheck.RoundMsg × cpoly.field.Ext4) :=
  chain.chain_open pp d_key poly_stmt carrier_dec c w alpha tau0 tau1 challenges gamma
    b mr md ir idg zd

-- The commitment layer. `verify_weak` returning a `Bool` inside `Result` is the
-- shape the specification's own `verify_weak` has (a `Bool`, not a `Prop`), which
-- is what makes the equivalence statement an equality of decisions.
example (pp : commit.PublicParams) (m : alloc.vec.Vec linalg.PolyVec) :
    Result (linalg.PolyVec × commit.Decomp) := commit.commit pp m
example (pp : commit.PublicParams) (u : linalg.PolyVec) (o : commit.Opening) : Result Bool :=
  commit.verify_weak pp u o

-- The balanced committer -- the honest Hachi commitment (`Hachi.commit`). Same
-- type as `commit.commit`, which is the point: `generateDecomps` takes the
-- decomposition as a parameter, so one verifier serves both.
example (pp : commit.PublicParams) (m : alloc.vec.Vec linalg.PolyVec) :
    Result (linalg.PolyVec × commit.Decomp) := commit.commit_balanced pp m
example (pp : commit.PublicParams) (m : alloc.vec.Vec linalg.PolyVec) :
    Result commit.Decomp := commit.generate_decomps_balanced pp m

-- The `ℓ₂²` norm is `u128`-valued, and that is load-bearing rather than
-- defensive: one centered coefficient can reach `q/2`, so a `u64` accumulator
-- would overflow -- i.e. *fail* in this model -- on inputs the verifier is
-- supposed to reject rather than crash on.
example (a : ring.Rq) : Result Std.U128 := commit.l2_norm_sq a
example : params.BETA_SQ.val = 41976510894886092800 := by simp [params.BETA_SQ]

-- The evaluation-split layer. The two polynomial newtypes are `@[reducible]`
-- `Vec` aliases like the three containers above -- two spec types
-- (`CMlPolynomial` / `CMlPolynomialEval`) over one carrier, so two names for
-- `Vec ring.Rq` here.
example : evalsplit.MlPoly = alloc.vec.Vec ring.Rq := rfl
example : evalsplit.MlEvals = alloc.vec.Vec ring.Rq := rfl

example (x y : Std.Usize) : Result Std.Usize := evalsplit.split_equiv x y
example (k : Std.Usize) : Result (Std.Usize × Std.Usize) := evalsplit.split_equiv_inv k
example (w : linalg.PolyVec) : Result linalg.PolyVec := evalsplit.monomial_basis w
example (w : linalg.PolyVec) : Result linalg.PolyVec := evalsplit.lagrange_basis w
example (p : evalsplit.MlPoly) : Result linalg.PolyMatrix := evalsplit.MlPoly.to_matrix p
example (m : linalg.PolyMatrix) : Result evalsplit.MlPoly := evalsplit.to_polynomial m
example (m : linalg.PolyMatrix) (u v : linalg.PolyVec) : Result ring.Rq :=
  linalg.PolyMatrix.split_form m u v
example (p : evalsplit.MlPoly) (xl xh : linalg.PolyVec) : Result ring.Rq :=
  evalsplit.MlPoly.eval_split p xl xh
example (v : evalsplit.MlEvals) : Result linalg.PolyMatrix :=
  evalsplit.MlEvals.to_matrix_eval v
example (v : evalsplit.MlEvals) (xl xh : linalg.PolyVec) : Result ring.Rq :=
  evalsplit.MlEvals.eval_split_eval v xl xh

-- The QuadEval fold. `in_sb`/`vec_in_sb`/`rel_out`/`paper_rel_out` return
-- `Bool` inside `Result`, and that is the shape that matters: ArkLib states
-- `relOut`, `paperRelOut`, `InSb` and `vecInSb` as `Prop`s (`Set`s of
-- conjunctions), so each equivalence statement here is an **iff** rather than
-- an equality of decisions -- unlike `commit.verify_weak`, whose spec is
-- already `Bool`.
example (a : ring.Rq) : Result Bool := quadeval.in_sb a
example (v : linalg.PolyVec) : Result Bool := quadeval.vec_in_sb v

example (a s : linalg.PolyVec) : Result ring.Rq := quadeval.carrier_entry a s
example (a : linalg.PolyVec) (s : alloc.vec.Vec linalg.PolyVec) : Result linalg.PolyVec :=
  quadeval.carrier a s
example (a : linalg.PolyVec) (s : alloc.vec.Vec linalg.PolyVec) : Result linalg.PolyVec :=
  quadeval.carrier_decomp a s
example (rows : Std.Usize) (c : linalg.PolyVec) (x : alloc.vec.Vec linalg.PolyVec) :
    Result linalg.PolyVec := quadeval.tensor_g rows c x
example (c x : linalg.PolyVec) : Result ring.Rq := quadeval.tensor_g1 c x
example (m : alloc.vec.Vec linalg.PolyVec) (c : linalg.PolyVec) : Result linalg.PolyVec :=
  quadeval.honest_z m c
example (z : linalg.PolyVec) : Result linalg.PolyVec := quadeval.j_mul z

-- The three carriers are `@[reducible]` records, like `commit.Decomp`, so a
-- statement about one is a statement about its fields.
example (pp : quadeval.PublicParamsD) : commit.PublicParams := pp.inner
example (stmt : quadeval.QuadEvalStatement) : linalg.PolyVec := stmt.avec
example (resp : quadeval.QuadEvalResponse) : linalg.PolyVec := resp.z_dec

/-! ## 3. The specification side is reachable, and agrees on the ring degree

The point of this section is not the mathematics -- `powTwoCyclotomic_natDegree`
is ArkLib's theorem and is proved there -- but that this package can *see* it.
The ArkLib dependency is the riskiest edge of the build (a Lean/Mathlib pin
shared with aeneas, resolved from a different repository), so the scaffold states
one fact that fails to compile if that edge is broken.

Kept generic in the coefficient ring `R`. Instantiating at `ZMod q` would need
`Fact (Nat.Prime q)` plus `BEq`/`LawfulBEq` instances that ArkLib's own
statements take as explicit parameters, and supplying them is the gadget layer's
job, not the scaffold's. -/

-- The ring this crate fixes -- degree `RING_DEGREE = 64` -- is the degree ArkLib's
-- power-of-two cyclotomic modulus has at `α = RING_LOG_DEGREE = 6`. This is the
-- one line that ties `params.rs` to the specification rather than to itself.
example {R : Type} [Field R] [BEq R] [LawfulBEq R] :
    (powTwoCyclotomic (R := R) params.RING_LOG_DEGREE.val).φ.natDegree
      = params.RING_DEGREE.val := by
  rw [powTwoCyclotomic_natDegree]
  simp [params.RING_LOG_DEGREE, params.RING_DEGREE]

-- The conductor is `2^(α+1)`, i.e. the modulus really is the `2048`th cyclotomic
-- polynomial at our `α` -- recorded because the Hachi norm bounds are stated
-- about `X^{2^α} + 1` specifically and would not hold of another modulus.
example {R : Type} [Field R] [BEq R] [LawfulBEq R] :
    (powTwoCyclotomic (R := R) params.RING_LOG_DEGREE.val).conductor = 2048 := by
  simp [powTwoCyclotomic, params.RING_LOG_DEGREE]

/-! ## 4. Axiom audit

One `#print axioms` line per headline spec. This is how a reader confirms that no
`sorryAx` hides under a `_spec` -- and, given § 2, that no stray `axiom` from an
un-whitelisted dependency crept in either.

`make build` greps the build log for `sorryAx`, so a `sorry` reached from any line
printed here is a build failure rather than a silent debt. The expected output is
the three Lean kernel axioms and nothing else: `propext`, `Classical.choice`,
`Quot.sound`, which are the ones the README's trusted computing base names.

What is here is now everything: the base field (`lean/Field.lean`), the whole
coefficient level of the ring (`lean/Ring.lean`) -- all thirteen operations -- those
thirteen lifted to ArkLib's `Rq Φ` (`lean/RqBridge.lean`), `linalg`, `gadget` and
`commit` (`lean/Scheme.lean`), ending at `honest_verifies_full`: an honest commitment
and its honest opening pass `commit::verify` itself, the crate's top-level API,
derived-message check included -- and the multilinear evaluation layer
(`lean/EvalSplit.lean`), the `evalsplit` module and `linalg::split_form` against
ArkLib's `Hachi.evalSplit`/`evalSplitEval` -- and, since 2026-09-04, the balanced
digit layer (`lean/Balanced.lean`), ending at `commit_balanced_spec`: the honest
**Hachi** commitment, `Hachi.commit` itself, which is what makes this crate a
translation of the paper's committer rather than of the unsigned building block
underneath it -- and, since the same day, the QuadEval fold (`lean/QuadEval.lean`):
the `z`-side gadget siblings at `τ = 5` with their conditional round trip, the
carrier entry and `tensorG1`, and the Eq. (20) box and relation decisions, four of
them stated as iffs because ArkLib states those as `Prop`s -- and, since
2026-09-08, the full ring-switch link (`lean/RingSwitch.lean`): the quotient-row
presentation change, the quotient digits, the lifted message and its Ajtai
commitment, and the two shortness decisions, both unconditional.

Stated-but-unproved today: nothing. `Ext.lean` -- the `Ext4` port from cpoly's
own development, which this sentence used to name -- was promoted 2026-09-09,
and the honest lift prover, the last file to pass through `lean-wip/`, on
2026-09-11. The next translated operation puts debt back there. -/

-- The balanced digit layer (`lean/Balanced.lean`): the Hachi gadget inverse
-- `G⁻¹` at `ddBal`, the bounded `z`-side digit map at `τ = 5`, the quotient
-- digits, and the balanced committer. Proved by Aristotle session `58843236`
-- and promoted 2026-09-04; these nine lines are what keep it proved.
#print axioms HachiEquiv.Balanced.balanced_digit_at_spec
#print axioms HachiEquiv.Balanced.balanced_digit_decompose_spec
#print axioms HachiEquiv.Balanced.balanced_gadget_decompose_spec
#print axioms HachiEquiv.Balanced.balanced_digit_at_natAbs_le
#print axioms HachiEquiv.Balanced.bounded_z_digit_at_spec
#print axioms HachiEquiv.Balanced.bounded_z_digit_at_natAbs_le
#print axioms HachiEquiv.Balanced.rho_digits_spec
#print axioms HachiEquiv.Balanced.generate_decomps_balanced_spec
#print axioms HachiEquiv.Balanced.commit_balanced_spec

-- The QuadEval fold (`lean/QuadEval.lean`): the `z`-side gadget siblings at
-- `τ = 5` and their conditional round trip, the carrier entry, `tensorG1`, and
-- the Eq. (20) box and relation decisions. Proved by Aristotle session
-- `14b9bf77` and promoted 2026-09-04; these eight lines are what keep it proved.
#print axioms HachiEquiv.QuadEval.bounded_z_gadget_decompose_spec
#print axioms HachiEquiv.QuadEval.gadget_mul_z_spec
#print axioms HachiEquiv.QuadEval.gadget_mul_z_inverts_spec
#print axioms HachiEquiv.QuadEval.carrier_entry_spec
#print axioms HachiEquiv.QuadEval.tensor_g1_spec
#print axioms HachiEquiv.QuadEval.in_sb_spec
#print axioms HachiEquiv.QuadEval.vec_in_sb_spec
#print axioms HachiEquiv.QuadEval.paper_rel_out_implies_rel_out_spec

-- The full ring-switch link (`lean/RingSwitch.lean`): `QuotientRow::to_rq` as
-- `rhoAsRq`, the quotient digits at the flat and the `(row, digit)` index,
-- `lift_message` as `Fin.append` and `lift_commit` as the concrete Ajtai map, and
-- the two shortness decisions against `RhoDigitsShort`/`liftShort` -- stated as
-- iffs, and *unconditional*: a first Aristotle pass (`8d26c89e`) returned them
-- under `n * 8 ≤ Usize.max`, the Rust dropped the flat index the specification
-- never had, and the second pass (`90c5c852`) proved them as stated. Promoted
-- 2026-09-08; these eight lines are what keep it proved.
#print axioms HachiEquiv.RingSwitch.rho_as_rq_spec
#print axioms HachiEquiv.RingSwitch.rho_digit_as_rq_raw_spec
#print axioms HachiEquiv.RingSwitch.rho_digit_as_rq_spec
#print axioms HachiEquiv.RingSwitch.lift_message_spec
#print axioms HachiEquiv.RingSwitch.lift_commit_spec
#print axioms HachiEquiv.RingSwitch.rho_digits_at_raw_spec
#print axioms HachiEquiv.RingSwitch.rho_digits_short_check_spec
#print axioms HachiEquiv.RingSwitch.lift_short_check_spec

#print axioms HachiEquiv.Field.fp_add_spec
#print axioms HachiEquiv.Field.fp_sub_spec
#print axioms HachiEquiv.Field.fp_mul_spec
#print axioms HachiEquiv.Field.fp_neg_spec
#print axioms HachiEquiv.Field.fp_new_spec
#print axioms HachiEquiv.Field.toK_inj_of_Red
-- The two-word accumulator layer, new with the 2026-09-16 cpoly bump. These are
-- what let `Ext4::mul` defer its reductions: sixteen unreduced products into
-- four `(low, high)` pairs, then one `reduce_wide` per output coefficient.
-- `u64_size_toK` is the single arithmetic fact underneath (`2^64 = 9801 mod q`,
-- because `q = 2^32 - 99`), and `add_double_product_spec` is where the extension
-- constant `W = 2` now lives, the `cpoly.field.W` constant having left the model
-- entirely (see § 2).
--
-- Transcribed from AeneasCompPoly's own `cpoly/lean/Field.lean` at `d7e26bb`
-- rather than imported: that package is on Lean/Mathlib v4.32.0 and this one is
-- on v4.33.1, and one Lake build holds one toolchain. So these are *our* proofs
-- of upstream's code, audited here like everything else.
#print axioms HachiEquiv.Field.red_mul_fits_u64
#print axioms HachiEquiv.Field.u64_size_toK
#print axioms HachiEquiv.Field.overflowing_add_toK
#print axioms HachiEquiv.Field.add_product_spec
#print axioms HachiEquiv.Field.add_double_product_spec
#print axioms HachiEquiv.Field.reduce_wide_spec

-- The ring layer, at the coefficient level (`lean/Ring.lean`): each operation
-- total, length-preserving, and coefficientwise equal to `ZMod q` arithmetic.
-- `mul` is the negacyclic convolution, so its coefficientwise statement is `negConv`:
-- the `k`-th antidiagonal of the raw product minus its `(N + k)`-th, which is
-- `(a * b) mod (X^N + 1)` written out.
#print axioms HachiEquiv.Ring.zero_spec
#print axioms HachiEquiv.Ring.add_spec
#print axioms HachiEquiv.Ring.sub_spec
#print axioms HachiEquiv.Ring.neg_spec
#print axioms HachiEquiv.Ring.scalar_mul_spec
#print axioms HachiEquiv.Ring.mul_spec
-- `Rq::mul` is an auxiliary-prime negacyclic transform with CRT reconstruction
-- (`src/ntt.rs`), and the headline above is the schoolbook convolution's
-- statement verbatim -- which is the whole point of the `Aux*` layer. What the
-- audit has to cover is therefore the *chain*, not one loop: the `ℕ`
-- antidiagonals and their cast bridge (unchanged, and still what
-- `negConv_eq_sums` closes), the three extraction loops, and the two lemmas
-- that identify the copied words' antidiagonals with the operands'. `accBound`
-- is no longer `mul`'s -- its accumulation happens in `ZMod p` one layer down --
-- but `LiftProver.long_mul` still uses it, so it stays audited here.
#print axioms HachiEquiv.Ring.accBound
#print axioms HachiEquiv.Ring.wordN_lt
#print axioms HachiEquiv.Ring.posSum_le
#print axioms HachiEquiv.Ring.negSum_le
#print axioms HachiEquiv.Ring.posSum_cast
#print axioms HachiEquiv.Ring.negSum_cast
#print axioms HachiEquiv.Ring.negConv_eq_sums
#print axioms HachiEquiv.Ring.mul_loop0_spec
#print axioms HachiEquiv.Ring.mul_loop1_spec
#print axioms HachiEquiv.Ring.mul_loop2_spec
#print axioms HachiEquiv.Ring.posW_eq_posSum
#print axioms HachiEquiv.Ring.negW_eq_negSum

-- Construction and observation: how an element is built, read and compared.
-- `equals` and `is_zero` are `↔`, so the rejection direction is audited too.
#print axioms HachiEquiv.Ring.constant_spec
#print axioms HachiEquiv.Ring.one_spec
#print axioms HachiEquiv.Ring.from_coeffs_spec
#print axioms HachiEquiv.Ring.coeff_spec
#print axioms HachiEquiv.Ring.equals_spec
#print axioms HachiEquiv.Ring.is_zero_spec
#print axioms HachiEquiv.Ring.copy_spec

-- The `Rq Φ` bridge (`lean/RqBridge.lean`): the same thirteen operations, with the
-- coefficient facts lifted to ArkLib's ring -- each says `toRq` of the result is the
-- ArkLib operation applied to the `toRq`s of the inputs. `mul_spec`'s lift is the
-- two-block negacyclic fold (`mul_two_block`), i.e. reduction modulo `X^N + 1`.
#print axioms HachiEquiv.RqBridge.zero_spec
#print axioms HachiEquiv.RqBridge.add_spec
#print axioms HachiEquiv.RqBridge.sub_spec
#print axioms HachiEquiv.RqBridge.neg_spec
#print axioms HachiEquiv.RqBridge.scalar_mul_spec
#print axioms HachiEquiv.RqBridge.mul_spec

#print axioms HachiEquiv.RqBridge.constant_spec
#print axioms HachiEquiv.RqBridge.one_spec
#print axioms HachiEquiv.RqBridge.from_coeffs_spec
#print axioms HachiEquiv.RqBridge.coeff_spec
#print axioms HachiEquiv.RqBridge.equals_spec
#print axioms HachiEquiv.RqBridge.is_zero_spec
#print axioms HachiEquiv.RqBridge.copy_spec

-- The linear algebra (`lean/Scheme.lean`): the `PolyVec`/`PolyMatrix` operations,
-- each stated against the ArkLib function of the same job rather than a
-- restatement of it. `flatten_blocks_spec` carries a capacity hypothesis, and
-- `poly_vec_equals_spec` is an `↔`, so its rejection direction is audited too.
#print axioms HachiEquiv.Scheme.dot_spec
#print axioms HachiEquiv.Scheme.vec_add_spec
#print axioms HachiEquiv.Scheme.vec_sub_spec
#print axioms HachiEquiv.Scheme.scalar_vec_mul_spec
#print axioms HachiEquiv.Scheme.mat_vec_mul_spec
#print axioms HachiEquiv.Scheme.flatten_blocks_spec
#print axioms HachiEquiv.Scheme.poly_vec_equals_spec

-- The gadget (`lean/Scheme.lean`): digit extraction (per position and as the
-- full 32-digit vector), the base powers, the gadget matrix (entrywise and
-- materialized), and the two directions of the decomposition. `base_pow_spec` is
-- the one that says the exponentiation happens in `ZMod q` and not in `u64`;
-- `digit_decompose_spec` is the one that pins the digit *order* (slot `e` is
-- digit `e`, least-significant first), and `gadget_matrix_spec` the tensor
-- layout of the materialized `G`, which `gadget_mul_spec` alone cannot see.
#print axioms HachiEquiv.Scheme.digit_at_spec
#print axioms HachiEquiv.Scheme.digit_decompose_spec
#print axioms HachiEquiv.Scheme.base_pow_spec
#print axioms HachiEquiv.Scheme.gadget_entry_spec
#print axioms HachiEquiv.Scheme.gadget_matrix_spec
#print axioms HachiEquiv.Scheme.gadget_mul_spec
#print axioms HachiEquiv.Scheme.gadget_decompose_spec

-- The gadget is lawful, as a statement about the *Rust*: the extracted
-- `gadget_mul` inverts the extracted `gadget_decompose`. This is the claim the
-- scheme's correctness rests on, so its axiom line is worth reading separately
-- from the two specs it is a corollary of.
#print axioms HachiEquiv.Scheme.gadget_round_trip

-- The centered norms (`lean/Scheme.lean`): `valMinAbs`, not the canonical
-- representative -- and each spec is a totality claim as much as an equality,
-- since the accumulators are fixed-width. `l2_norm_sq_spec` is total outright
-- (`u128` is wide enough for one ring element); the vector version carries the
-- capacity hypothesis that makes it so.
#print axioms HachiEquiv.Scheme.centered_abs_spec
#print axioms HachiEquiv.Scheme.l1_norm_spec
#print axioms HachiEquiv.Scheme.l_infty_norm_spec
#print axioms HachiEquiv.Scheme.l2_norm_sq_spec
#print axioms HachiEquiv.Scheme.vec_l2_norm_sq_spec
#print axioms HachiEquiv.Scheme.vec_l_infty_norm_spec

-- The inner-outer commitment (`lean/Scheme.lean`), against the specification's own
-- `InnerOuter` definitions through the structure bridges (`toParams`,
-- `toDecompSpec`, `toOpening`). `verify_weak_spec` is an equality of *decisions*:
-- an implication in the accepting direction would be satisfied by a verifier that
-- rejects everything, so only the equality puts the rejection paths in the claim.
#print axioms HachiEquiv.Scheme.generate_decomps_spec
#print axioms HachiEquiv.Scheme.derived_message_spec
#print axioms HachiEquiv.Scheme.commit_with_decomps_spec
#print axioms HachiEquiv.Scheme.verify_weak_spec
#print axioms HachiEquiv.Scheme.verify_spec
#print axioms HachiEquiv.Scheme.commit_spec
#print axioms HachiEquiv.Scheme.honest_spec

-- Perfect correctness of the extracted scheme, twice over: `honest_verifies`
-- through the weak verifier, and `honest_verifies_full` through `commit::verify`
-- itself -- the crate's top-level API, derived-message check included. The
-- latter is the top of the composition -- it reaches every line above -- so it
-- is the single line whose axiom set summarises the whole development.
#print axioms HachiEquiv.Scheme.honest_verifies
#print axioms HachiEquiv.Scheme.honest_verifies_full

-- The multilinear evaluation layer (`lean/EvalSplit.lean`): the `evalsplit`
-- module and `linalg::split_form`, against ArkLib's split-evaluation definitions
-- at the crate's `nl = 1, nh = 2`. The index helpers are stated against
-- `Nat.testBit` and `Hachi.splitEquiv` (both directions), the bases against
-- `CMlPolynomial.monomialBasis` / `CMlPolynomialEval.lagrangeBasis`, the
-- reshapes against `Hachi.toMatrix`/`toPolynomial`/`toMatrixEval`, and the two
-- headline evaluations against `Hachi.evalSplit`/`evalSplitEval` -- which carry
-- the `CMlPolynomial.eval` reading through ArkLib's own `evalSplit_eq_eval`.
-- `two_pow_spec` (and everything stated through it) carries the one
-- model-artefact hypothesis `2 ^ n ≤ Usize.max`; the rest are exact.
#print axioms HachiEquiv.EvalSplit.two_pow_spec
#print axioms HachiEquiv.EvalSplit.test_bit_spec
#print axioms HachiEquiv.EvalSplit.split_equiv_spec
#print axioms HachiEquiv.EvalSplit.split_equiv_inv_spec
#print axioms HachiEquiv.EvalSplit.monomial_basis_spec
#print axioms HachiEquiv.EvalSplit.lagrange_basis_spec
#print axioms HachiEquiv.EvalSplit.split_form_spec
#print axioms HachiEquiv.EvalSplit.to_matrix_spec
#print axioms HachiEquiv.EvalSplit.to_polynomial_spec
#print axioms HachiEquiv.EvalSplit.to_matrix_eval_spec
#print axioms HachiEquiv.EvalSplit.eval_split_spec
#print axioms HachiEquiv.EvalSplit.eval_split_eval_spec

-- The `Ext4` extension-field layer (`lean/Ext.lean`), ported from cpoly's own
-- equivalence development and re-proved here against *this* crate's extraction:
-- the arithmetic impls of `cpoly::field::Ext4` against `CompPoly.Extension.Ext`
-- at `Hachi.ext4Params`. Not importable from upstream -- cpoly's statements are
-- about its own `Generated.lean`, under a v4.32.0 toolchain this build cannot
-- adopt -- so the layer is a port, and NOTES.md § "The dropped `eq~` factor"'s
-- neighbour § records why the ported scripts needed one bridging lemma:
-- `ext4Params.d` and `ext4Params.toExtensionParams.d` are definitionally equal
-- and syntactically distinct, which every tactic notices and the kernel does
-- not. Exact: no model-artefact hypothesis anywhere in this file.
--
-- `ext_add_assign_spec` and `ext_mul_assign_spec` stood here until the `eq̃`
-- kernel stopped going through `cpoly::multilinear::eq_tilde`: `+=` and `*=` on
-- `Ext4` were reached only from inside `lagrange_basis` and `dot`, so the two
-- impls left `Generated.lean` with them and a `#print axioms` line naming a
-- declaration that no longer exists would not compile. `Ext.lean` § "Scope: the
-- operations hachi's model contains" is where that ledger is kept.
#print axioms HachiEquiv.Ext.fp_is_zero_spec
#print axioms HachiEquiv.Ext.ext_add_spec
#print axioms HachiEquiv.Ext.ext_sub_spec
#print axioms HachiEquiv.Ext.ext_mul_spec
#print axioms HachiEquiv.Ext.ext_from_base_spec
#print axioms HachiEquiv.Ext.ext_is_zero_spec

-- The QuadEval protocol layer (`lean/QuadEvalProtocol.lean`): target 2's three
-- carriers, the two gadget-level helpers, `jMatrix` applied to `z^`, the honest
-- prover's three functions and the two output relations. This is the statement
-- debt `make spec-check` found on 2026-09-08 -- the fold's arithmetic was proved
-- and promoted a week earlier, while eleven of the module's items carried
-- `Mirrors` lines and no `_spec` at all, because `coverage` asked "is it
-- measured" and nothing asked "is it stated".
--
-- Two conventions to know before reading them. `toChals` takes the challenge
-- subtype's `l1Norm <= omega` bound as an *argument*: `relOut` checks no
-- challenge norm precisely because `ShortChallenge` carries it in the type
-- (`QuadEval/Reduction.lean:148-151`), and the extracted verifier takes a plain
-- `PolyVec`, so a faithful statement has to say the challenges are short
-- somewhere. And both relation specs are iffs, not implications -- a verifier
-- that rejected everything would satisfy one direction, and `paperRelOut` is
-- the strictly stronger check (`paperRelOut_subset_relOut` under `beta/2 <= gamma`,
-- here `8 <= 15`), so neither statement implies the other.
#print axioms HachiEquiv.QuadEvalProtocol.PublicParamsD_new_spec
#print axioms HachiEquiv.QuadEvalProtocol.QuadEvalStatement_new_spec
#print axioms HachiEquiv.QuadEvalProtocol.QuadEvalResponse_new_spec
#print axioms HachiEquiv.QuadEvalProtocol.carrier_decomp_spec
#print axioms HachiEquiv.QuadEvalProtocol.carrier_commit_spec
#print axioms HachiEquiv.QuadEvalProtocol.j_mul_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_z_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_compute_v_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_compute_resp_spec
#print axioms HachiEquiv.QuadEvalProtocol.rel_out_spec
#print axioms HachiEquiv.QuadEvalProtocol.paper_rel_out_spec

-- Stage 3 target 4, the zero-check link (`lean/ZeroCheck.lean`): `wTable` and
-- its multilinear extension, the range factor, the computable `H₀` and `H_α`
-- layers, `alphaPublicEvals`, `zcTargetAlpha`, and the three `ringswitch` items
-- the α side introduced. Three conventions in it are load-bearing. Every
-- statement is against a **computable** ArkLib definition -- the α side goes
-- through `alphaDefect`, with the bridge to the noncomputable `hAlphaEvals`
-- stated as its own obligation (`h_alpha_evals_eq_hAlphaEvals_spec`) rather
-- than assumed. Arities are arguments, so each is the generic ArkLib statement
-- at arbitrary width rather than an instantiation at `M_ZERO`. And
-- `eq_weight_spec`, `zc_target_alpha_spec` and `below_two_pow_spec` are
-- unconditional in the machine model after the `two_pow` repair (NOTES.md
-- § "Two invented powers of two, removed"); the four table-side statements
-- carry `μ + n·8 ≤ Usize.max`, which `w_table`'s `rows · digits` product earns
-- and which is not minimal -- recorded as owed, not forgotten.
#print axioms HachiEquiv.ZeroCheck.c_eval_at_spec
#print axioms HachiEquiv.ZeroCheck.c_eval_at_modulus_spec
#print axioms HachiEquiv.ZeroCheck.RlinStatement_new_spec
#print axioms HachiEquiv.ZeroCheck.range_product_spec
#print axioms HachiEquiv.ZeroCheck.w_table_spec
#print axioms HachiEquiv.ZeroCheck.w_table_flat_spec
#print axioms HachiEquiv.ZeroCheck.c_w_table_mle_spec
#print axioms HachiEquiv.ZeroCheck.w_table_mle_eval_spec
#print axioms HachiEquiv.ZeroCheck.h_zero_spec
#print axioms HachiEquiv.ZeroCheck.h_zero_is_zero_spec
#print axioms HachiEquiv.ZeroCheck.alpha_tilde_spec
#print axioms HachiEquiv.ZeroCheck.eq_weight_spec
#print axioms HachiEquiv.ZeroCheck.below_two_pow_spec
#print axioms HachiEquiv.ZeroCheck.poly_matrix_cols_spec
#print axioms HachiEquiv.ZeroCheck.m_alpha_tilde_spec
#print axioms HachiEquiv.ZeroCheck.alpha_public_evals_spec
#print axioms HachiEquiv.ZeroCheck.zc_target_alpha_spec
#print axioms HachiEquiv.ZeroCheck.alpha_contract_spec
#print axioms HachiEquiv.ZeroCheck.alpha_defect_spec
#print axioms HachiEquiv.ZeroCheck.h_alpha_evals_spec
#print axioms HachiEquiv.ZeroCheck.h_alpha_evals_eq_hAlphaEvals_spec
#print axioms HachiEquiv.ZeroCheck.h_alpha_evals_flat_spec
#print axioms HachiEquiv.ZeroCheck.h_alpha_spec
#print axioms HachiEquiv.ZeroCheck.h_alpha_is_zero_spec

-- Stage 3 target 6, the end piece (`lean/EndPiece.lean`): `endPieceCheck`'s
-- three conjuncts in the specification's order and with its short-circuit, the
-- honest prover's single message, and the witness read off the transcript.
-- `end_piece_check_spec` takes `BEq`/`LawfulBEq` on the commitment carrier as
-- instance *hypotheses*, which is ArkLib's own convention for `endPieceCheck`
-- (`Composition.lean:287`): `K.TCom` is a function type, so there is no
-- instance to find, and the binders sit on the `.TCom` projection because
-- instance search will not unfold it.
#print axioms HachiEquiv.EndPiece.WEvalStatement_new_spec
#print axioms HachiEquiv.EndPiece.end_piece_check_spec
#print axioms HachiEquiv.EndPiece.end_piece_prove_spec
#print axioms HachiEquiv.EndPiece.end_piece_witness_spec

-- Stage 5's `R^lin` adapter (`lean/Rlin.lean`, chain row 3) plus the
-- polynomial-level bridge (row 1): the transposed gadget application every
-- block goes through, the five `usize` dimension abbrevs, the two reshapes, the
-- two witness maps, the bridge's carrier and map, and the assembly
-- `rlin_stmt_spec`. That last one is stated against the specification's own
-- `rlinStmt`, whose c4 block is `(matMul G J).transpose *ᵥ a`, while the crate
-- computes `Jᵀ(Gᵀa)` -- the 320 GiB product never exists -- so its proof is
-- what makes the genesis freeze of the reshaped form faithful. Four of the
-- thirteen are stated at the pinned dimensions because the carrier relations
-- they consume (`RepParamsD`/`RepStmt`/`RepResp`) are; the other nine are
-- generic. Aristotle session `4d70f965`, nine obligations to zero, no headline
-- signature changed.
#print axioms HachiEquiv.Rlin.gadget_transpose_mul_spec
#print axioms HachiEquiv.Rlin.rlin_cw_spec
#print axioms HachiEquiv.Rlin.rlin_ct_spec
#print axioms HachiEquiv.Rlin.rlin_cz_spec
#print axioms HachiEquiv.Rlin.rlin_cols_spec
#print axioms HachiEquiv.Rlin.rlin_rows_spec
#print axioms HachiEquiv.Rlin.unflatten_spec
#print axioms HachiEquiv.Rlin.tensor_g_matrix_spec
#print axioms HachiEquiv.Rlin.stack_spec
#print axioms HachiEquiv.Rlin.unstack_spec
#print axioms HachiEquiv.Rlin.PolyEvalStatement_new_spec
#print axioms HachiEquiv.Rlin.to_quad_eval_statement_spec
#print axioms HachiEquiv.Rlin.rlin_stmt_spec

-- Target 5's paired sumcheck (`lean/Sumcheck.lean`, chain rows 6 and 8): the
-- three statement carriers, the node and interpolation layer, the range and
-- linear round polynomials in their lower-half and headline forms, the
-- verifier's two decisions and its state map, the honest prover's message and
-- final value, the bridge into the rounds, and the round loop three ways --
-- the fused honest run (`round_loop`), the prover's half
-- (`honest_round_messages`) and the verifier's half for arbitrary messages
-- (`round_verify_loop`). The univariate carrier underneath (`toRaw`/`toUni`,
-- ported from cpoly's own equivalence development) is not itself a mirrored
-- item and has no line here; its specs are reached through these. Three
-- Aristotle sessions, `430518ae`, `c8d6894b`, `3fd1e8a2`, thirty-two
-- obligations to zero with no headline signature changed.
#print axioms HachiEquiv.Sumcheck.NestedZeroCheckStmt_new_spec
#print axioms HachiEquiv.Sumcheck.RoundMsg_new_spec
#print axioms HachiEquiv.Sumcheck.RoundStatement_new_spec
#print axioms HachiEquiv.Sumcheck.interpolate_spec
#print axioms HachiEquiv.Sumcheck.round_node_spec
#print axioms HachiEquiv.Sumcheck.round_value_zero_spec
#print axioms HachiEquiv.Sumcheck.round_values_zero_spec
#print axioms HachiEquiv.Sumcheck.round_poly_zero_spec
#print axioms HachiEquiv.Sumcheck.eq_prefix_spec
#print axioms HachiEquiv.Sumcheck.eq_suffix_table_spec
#print axioms HachiEquiv.Sumcheck.eq_free_factor_spec
#print axioms HachiEquiv.Sumcheck.round_value_alpha_spec
#print axioms HachiEquiv.Sumcheck.round_values_alpha_spec
#print axioms HachiEquiv.Sumcheck.round_poly_alpha_spec
#print axioms HachiEquiv.Sumcheck.alpha_public_table_spec
#print axioms HachiEquiv.Sumcheck.honest_compute_g_spec
#print axioms HachiEquiv.Sumcheck.round_check_spec
#print axioms HachiEquiv.Sumcheck.round_out_spec
#print axioms HachiEquiv.Sumcheck.final_check_spec
#print axioms HachiEquiv.Sumcheck.honest_compute_y_spec
#print axioms HachiEquiv.Sumcheck.nested_to_round_statement_spec
#print axioms HachiEquiv.Sumcheck.round_loop_spec
#print axioms HachiEquiv.Sumcheck.honest_round_messages_spec
#print axioms HachiEquiv.Sumcheck.round_verify_loop_spec

-- Stage 5's composed chain (`lean/Chain.lean`): the verifier's verdict against
-- `chainVerdict` -- `verifyRounds`, then `finalCheck && endPieceCheck` -- and
-- the honest prover's four wire messages, both through the statement thread
-- `chainStart` (rows 1 to 7 as one map). Proved locally as compositions of the
-- link specs; kernel-clean once `Sumcheck.lean` closed.
#print axioms HachiEquiv.Chain.chain_verify_spec
#print axioms HachiEquiv.Chain.chain_open_spec
-- Candidate T29: the raw message as `u32` WORDS. Every coefficient of a
-- well-formed `Rq` is a canonical residue below `q = 2^32 - 99`, so a `u32`
-- holds it exactly -- and the raw message is the one input the prover keeps
-- resident for the whole protocol. Measured at the pin: the peak fell from
-- 8448 MiB to 4360 MiB at the same stage boundary, and `dense_eval`, which now
-- expands one block at a time, cost 366.3 s against 369.5 s.
--
-- The narrowing in `RawRq32::compact` is FALLIBLE in the extracted model --
-- `lift (UScalar.cast .U32 …)` -- and its side condition is exactly
-- `Field.Red`, which every `Wf` operand already carries. That is what makes
-- the carrier admissible: it costs no new precondition, so no statement below
-- was weakened to accept it.
--
-- Two claims, and the split between them is the design:
--
--  * `rawrq32_round_trip` / `rawvec32_round_trip` -- losslessness, as an
--    equality of extracted VALUES, not of denotations. It needed two
--    representation-level facts the arithmetic had never asked for:
--    `from_coeffs_id` (on an input of the ring's own length the function is the
--    identity, because its loop pushes the entries verbatim) and `fp_new_id`
--    (`Fp::new` is the identity on a word already reduced).
--
--  * each `_32` consumer is proved EQUAL to the item it replaces, on the
--    message its words denote, and its specification is then the original's --
--    inherited, not re-derived. Composed with the `_64` spec it yields the same
--    conclusion in the same vocabulary, and it is the honest shape, because
--    "the compact carrier changes nothing" is what the change asserts. The two
--    tools are `eq_ok_of_spec` (a deterministic postcondition IS an equation,
--    since `theta` sends `fail` and `div` to `False`) and `loop_congr` (`loop`
--    is an ordinary function of its body). The `_32` and `_64` loop bodies
--    differ by one inserted `expand` and the inner loops are byte-identical,
--    so the pointwise body equality is the entire content.
#print axioms HachiEquiv.Raw32.eq_ok_of_spec
#print axioms HachiEquiv.Raw32.loop_congr
#print axioms HachiEquiv.Raw32.fp_new_id
#print axioms HachiEquiv.Raw32.from_coeffs_id
#print axioms HachiEquiv.Raw32.compact_loop_spec
#print axioms HachiEquiv.Raw32.expand_loop_rep
#print axioms HachiEquiv.Raw32.rawrq32_round_trip
#print axioms HachiEquiv.Raw32.rawvec32_compact_loop_spec
#print axioms HachiEquiv.Raw32.rawvec32_round_trip
#print axioms HachiEquiv.Raw32.rawvec32_expand_eq
#print axioms HachiEquiv.Raw32.commit_streamed_32_loop_eq
#print axioms HachiEquiv.Raw32.commit_streamed_32_eq
#print axioms HachiEquiv.Raw32.commit_streamed_32_spec
#print axioms HachiEquiv.Raw32.carrier_from_raw_32_loop_eq
#print axioms HachiEquiv.Raw32.carrier_from_raw_32_eq
#print axioms HachiEquiv.Raw32.honest_z_from_raw_32_loop1_eq
#print axioms HachiEquiv.Raw32.honest_z_from_raw_32_eq
#print axioms HachiEquiv.QuadEvalProtocol.carrier_from_raw_32_spec
#print axioms HachiEquiv.QuadEvalProtocol.carrier_decomp_from_raw_32_spec
#print axioms HachiEquiv.QuadEvalProtocol.carrier_commit_from_raw_32_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_z_from_raw_32_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_compute_v_from_raw_32_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_compute_resp_from_raw_32_spec
-- Candidate T28: the carrier decomposition computed ONCE. `ŵ = G⁻¹(a · raw)`
-- is what `v = D ŵ` needs and it is also the response's carrier slot, and both
-- were computing it -- 98.7 s each at the pin, measured on the profile, and a
-- third time inside `chain_open`, which recomputed `v`. Now the caller computes
-- it once and hands it to both; `chain_open` takes it and reads the message not
-- at all.
--
-- What moves in the statements is a PREMISE, never a conclusion: from "`raw`
-- decomposes to `wo.message`" to "`carrier_dec` IS the carrier decomposition of
-- `wo.message`". `carrier_decomp_from_raw_32_spec` turns the first into the
-- second, so composing the two recovers the old hypotheses exactly and nothing
-- is weakened. `honest_compute_resp_from_raw_32_spec` in fact loses a
-- hypothesis, `RepStmt stmt ss`: the only thing the response used the statement
-- for was the carrier it no longer computes.
--
-- One casualty, recorded rather than hidden: T29's
-- `honest_compute_resp_from_raw_32_eq` is GONE. It said that item was its `_64`
-- original on a re-carriered message, and that stopped being true the moment
-- the item took the decomposition instead of computing it -- the statement no
-- longer typechecks. Its specification is now proved directly, from
-- `honest_z_from_raw_32_eq` (still exactly T29's shape) plus the supplied
-- decomposition. The lesson is that an equality-to-the-old-item proof is only
-- as durable as the signature it is stated at, which is the price of inheriting
-- a specification instead of re-deriving it.
#print axioms HachiEquiv.QuadEvalProtocol.honest_compute_v_from_decomp_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_compute_v_from_decomp_honest

-- The honest lift prover (`lean/LiftProver.lean`), the chain's last item to be
-- translated and Stage 4's last proof debt, paid 2026-09-11: the unreduced row sum against
-- `InnerOuter.cRowSum`, its division by the modulus against
-- `InnerOuter.cQuotient`, the headline `honestLiftWitnessC` through
-- `RepLiftedWitness`, and the two private helpers underneath -- the product in
-- `Zq[X]` against `CPolynomial`'s `*` and the synthetic division against
-- `CPolynomial.divByMonic`. The loop of `honest_lift_witness` is not a mirrored
-- item and has no line here; it is reached through the headline. Aristotle
-- session `1ddd5790`, five obligations to zero with no headline signature
-- changed, promoted 2026-09-11.
#print axioms HachiEquiv.LiftProver.long_mul_spec
-- Candidate R (Stage 6, route R2): `long_mul` with the reduction delayed, the
-- same trick as candidate Q one function over. The headline above is
-- byte-identical; what is new is the `ℕ`-level accumulator, so the audit covers
-- its ceiling and the cast bridge. `accBound` and `wordN_lt` are Q's, reused --
-- `Ring.lean` is upstream of this file, so this time the dependency runs the
-- right way and the layer really is shared rather than duplicated.
#print axioms HachiEquiv.LiftProver.longSum_le
#print axioms HachiEquiv.LiftProver.longSum_cast
#print axioms HachiEquiv.LiftProver.long_mul_loop0_loop0_spec
#print axioms HachiEquiv.LiftProver.long_mul_loop0_spec
#print axioms HachiEquiv.LiftProver.div_by_modulus_spec
#print axioms HachiEquiv.LiftProver.c_row_sum_spec
#print axioms HachiEquiv.LiftProver.c_quotient_spec
#print axioms HachiEquiv.LiftProver.honest_lift_witness_spec

-- The optimized variants (`lean/Opt.lean`): each `opt_eq_spec` equates a
-- translatable `Foo.opt` with the ArkLib definition its Rust item mirrors.
-- Stage 6, iteration 1, candidate A -- the running-power evaluation.
#print axioms HachiEquiv.Opt.c_eval_at.opt_eq_spec
#print axioms HachiEquiv.Opt.c_eval_at.opt_eq_spec_toRq
#print axioms HachiEquiv.Opt.c_eval_at_modulus.opt_eq_spec
#print axioms HachiEquiv.Opt.c_eval_at_modulus.opt_eq_pow_add_one
-- Candidate B -- the row-hoisted witness table and the layer-fold evaluation.
#print axioms HachiEquiv.Opt.c_w_table_mle.opt_eq_spec
#print axioms HachiEquiv.Opt.h_zero.opt_eq_spec
#print axioms HachiEquiv.Opt.h_zero_is_zero.opt_eq_spec
#print axioms HachiEquiv.Opt.w_table_mle_eval.opt_eq_spec
-- The new helpers the row hoist introduced (no ArkLib mirror; specified against
-- `ZeroCheck.wTableRow` and `wTableFlat`).
#print axioms HachiEquiv.ZeroCheck.w_table_row_spec
#print axioms HachiEquiv.ZeroCheck.c_w_table_mle_values_spec
-- Candidate C -- the α-side tables hoisted out of `alpha_public_table`.
#print axioms HachiEquiv.Opt.alpha_public_table.opt_eq_spec
#print axioms HachiEquiv.Opt.alpha_public_table.opt_length
-- The three α-side tables candidate C introduced (no ArkLib mirror; specified
-- against `alphaTilde`, the `eqWeightVal` weights and `mAlphaTilde`).
#print axioms HachiEquiv.ZeroCheck.alpha_pow_table_spec
#print axioms HachiEquiv.ZeroCheck.eq_weight_table_spec
#print axioms HachiEquiv.ZeroCheck.m_alpha_table_spec
-- Candidate E -- the lift commitment without the materialized concatenation (W3).
#print axioms HachiEquiv.Opt.lift_commit.opt_eq_spec
#print axioms HachiEquiv.Opt.lift_commit.opt_eq_spec_hachi
-- The fused row of the lift commitment (no ArkLib mirror; one row of `hachiLiftCom`).
#print axioms HachiEquiv.RingSwitch.lift_commit_row_spec
-- Candidate F -- the range factor as `v · ∏ (v² − j²)` (brief 5's S5).
#print axioms HachiEquiv.Opt.range_product.opt_eq_spec
#print axioms HachiEquiv.Opt.range_product.opt_eq_spec_16
-- Candidate T2a -- the same range factor by Paterson--Stockmeyer at block 4,
-- over the pinned coefficient table.  The two halves are audited separately on
-- purpose: `optPS_eq` is the rearrangement (any coefficient sequence, no
-- characteristic), `rangeQ_eq_prod` is the table (sixteen `decide`s in `ZMod q`
-- plus one `ring`), and `rangeQ_sq_eq_rangeProduct` composes them against the
-- specification.  `rc` is *defined* by `params::RANGE_Q_COEFFS`, so a wrong
-- table word fails its own `decide` rather than being absorbed by the algebra.
#print axioms HachiEquiv.ZeroCheck.rangeQ_eq_prod
#print axioms HachiEquiv.ZeroCheck.rangeQ_sq_eq_rangeProduct
#print axioms HachiEquiv.ZeroCheck.range_product_loop_spec
#print axioms HachiEquiv.Opt.range_product.optPS_eq
#print axioms HachiEquiv.Opt.range_product.optPS_eq_spec
-- Candidate T2c -- the round fold's two scalars kept in the base field, so each
-- product is the mixed `Fp x Ext4` multiply (four base multiplications) instead
-- of the full quartic (nineteen).  A representation change on the scalars, not
-- an algorithmic one: `round_values_zero_spec`'s statement is unmoved and only
-- its proof was restated around the new inner loop, whose spec is audited here.
#print axioms HachiEquiv.Opt.round_values_zero.optFold_eq_spec
#print axioms HachiEquiv.Sumcheck.round_values_zero_loop0_loop0_spec
#print axioms HachiEquiv.Sumcheck.round_values_zero_spec
-- Candidate G -- the table builders' range factor computed in the base field.
#print axioms HachiEquiv.Opt.phiF_range_product_base
#print axioms HachiEquiv.Opt.h_zero.opt2_eq_spec
#print axioms HachiEquiv.Opt.h_zero_is_zero.opt2_eq_spec
-- The base-field range factor the table builders now call (no ArkLib mirror;
-- specified through `phiF` against `rangeProduct` at the embedded argument).
#print axioms HachiEquiv.ZeroCheck.range_product_base_spec
-- Candidate I -- round 0 of the sumcheck in the base field (brief 5's S7').
#print axioms HachiEquiv.Opt.phiF_foldBase
#print axioms HachiEquiv.Opt.rangeSumZeroBase.loop_eq
#print axioms HachiEquiv.Opt.rangeSumZeroBase_eq_loop
#print axioms HachiEquiv.Opt.rangeSumZeroBase_eq
#print axioms HachiEquiv.Opt.roundValuesZeroBase_length
#print axioms HachiEquiv.Opt.roundValuesZeroBase_getD
#print axioms HachiEquiv.Opt.phiF_natCast_node
#print axioms HachiEquiv.Opt.roundValuesZeroBase_eq
#print axioms HachiEquiv.Opt.evalMleLayerBase_eq
#print axioms HachiEquiv.Opt.linSumAlphaBase_eq
#print axioms HachiEquiv.Opt.roundValuesZeroBase_eq_all
-- Candidate J -- the tensor split of Ã: the MLE of a tensor-product table is the
-- product of the two small MLEs (brief 5's S4, verifier half). The pure algebra
-- lives in `lean/Sumcheck.lean`, which `Opt.lean` imports, so the tensor-split
-- lemma and the split-against-the-specification lemma print under `Sumcheck`.
#print axioms HachiEquiv.Sumcheck.mle_tensor_split
#print axioms HachiEquiv.Sumcheck.alphaSplit_eval_eq
#print axioms HachiEquiv.Opt.alpha_public_mle_eval.opt_eq_spec
#print axioms HachiEquiv.Opt.alpha_public_mle_eval.opt_eq_spec'
-- Candidate L -- the α table carried as two factors: the fold commutes with the
-- tensor structure, and the split read is the flat read (brief 5's S4, prover half).
-- The pure algebra was moved down into `lean/Sumcheck.lean` by the campaign (the
-- spec layer there consumes it and `Opt.lean` imports that file), so the tensor
-- table, the two fold-commutation lemmas, the round-0 identification, the split
-- read and the whole-run iteration print under `Sumcheck`; only the candidate's
-- own contract stays under `Opt`.
#print axioms HachiEquiv.Sumcheck.tensorTable_apply
#print axioms HachiEquiv.Sumcheck.tensorTable_eq_of_split
#print axioms HachiEquiv.Sumcheck.fold_tensorTable_low
#print axioms HachiEquiv.Sumcheck.fold_tensorTable_scalar
#print axioms HachiEquiv.Sumcheck.alphaPublicEvals_eq_tensorTable
#print axioms HachiEquiv.Sumcheck.linSumAlpha_tensor
#print axioms HachiEquiv.Sumcheck.fold_tensorTable_read
#print axioms HachiEquiv.Sumcheck.fold_tensorTable_read_scalar
#print axioms HachiEquiv.Sumcheck.foldIter_tensorTable
#print axioms HachiEquiv.Opt.honest_round_messages.opt_eq_spec
-- Candidate J (campaign) -- the extracted tensor-split evaluation, proved against
-- the same `cMultilinearExtension m₀ (alphaPublicEvals …)` the table path was
-- proved against; `final_check_spec` above is the headline that consumes it and
-- its statement did not move.
#print axioms HachiEquiv.Sumcheck.alpha_public_mle_eval_spec
-- Candidate P (Stage 6, route R2 `accepted-surface`): `sumcheck::poly_mul`, the
-- univariate schoolbook moved out of cpoly and into this crate so that a `cpoly`
-- pin bump cannot break a proof about code this repository does not own. The
-- three specs are the ported ones retargeted by item name -- the body is cpoly's
-- body, so the loops and their invariants did not move.
#print axioms HachiEquiv.Sumcheck.poly_mul_inner_loop_spec
#print axioms HachiEquiv.Sumcheck.poly_mul_outer_loop_spec
#print axioms HachiEquiv.Sumcheck.poly_mul_spec
-- Candidate I (campaign) -- the extracted round-0 path, proved against the same
-- ArkLib definitions the extension-field path is proved against.  The mixed
-- multiply and the base-field committed table first (`Ext`, `ZeroCheck`), then
-- the six round-message items, the one mixed layer fold and the round-0 message
-- (`Sumcheck`); `honest_round_messages_spec` above is the headline that consumes
-- them and its statement did not move.
#print axioms HachiEquiv.Ext.fp_ext_mul_spec
#print axioms HachiEquiv.ZeroCheck.c_w_table_fp_spec
#print axioms HachiEquiv.Sumcheck.round_value_zero_base_spec
#print axioms HachiEquiv.Sumcheck.round_values_zero_base_spec
#print axioms HachiEquiv.Sumcheck.round_poly_zero_base_spec
#print axioms HachiEquiv.Sumcheck.round_value_alpha_base_spec
#print axioms HachiEquiv.Sumcheck.round_values_alpha_base_spec
#print axioms HachiEquiv.Sumcheck.round_poly_alpha_base_spec
#print axioms HachiEquiv.Sumcheck.eval_mle_layer_base_spec
#print axioms HachiEquiv.Sumcheck.honest_compute_g_base_spec
-- Candidate L (campaign, Aristotle) -- the extracted prover items that carry the
-- α table as its two tensor factors, proved against the same ArkLib definitions
-- the flat-table path was proved against: the two table builders, the per-round
-- fold of the pair, the six round-polynomial items off the split read, and the
-- two round messages.  `honest_round_messages_spec` above is the headline that
-- consumes them and its statement did not move.  These print `sorryAx` until the
-- remote prover returns, which is why the tree carrying them is not committed.
#print axioms HachiEquiv.Sumcheck.tensorRead_eq_tensorTable
#print axioms HachiEquiv.Sumcheck.tensorRead_eq_reidx
#print axioms HachiEquiv.Sumcheck.linSumAlphaSplit_eq_sum_range
#print axioms HachiEquiv.Sumcheck.linSumAlphaSplitFp_eq_sum_range
#print axioms HachiEquiv.Sumcheck.alpha_split_low_spec
#print axioms HachiEquiv.Sumcheck.alpha_split_high_spec
#print axioms HachiEquiv.Sumcheck.alpha_split_fold_spec
#print axioms HachiEquiv.Sumcheck.round_value_alpha_split_spec
#print axioms HachiEquiv.Sumcheck.round_values_alpha_split_spec
#print axioms HachiEquiv.Sumcheck.round_poly_alpha_split_spec
#print axioms HachiEquiv.Sumcheck.round_value_alpha_base_split_spec
#print axioms HachiEquiv.Sumcheck.round_values_alpha_base_split_spec
#print axioms HachiEquiv.Sumcheck.round_poly_alpha_base_split_spec
#print axioms HachiEquiv.Sumcheck.honest_compute_g_split_spec
#print axioms HachiEquiv.Sumcheck.honest_compute_g_base_split_spec

-- Candidate M (Stage 6, `evalsplit::monomial_basis`) -- the doubling build. Two
-- independent proofs of one identity, and the dependency between the files
-- makes that the safe direction: the candidate-time contract is stated over a
-- bare `CommSemiring` against `CMlPolynomial.monomialBasis` itself, while the
-- campaign proves the extracted loops in `EvalSplit` (which `Opt` imports, so
-- it cannot route through the contract). `monomial_basis_spec` is audited above
-- and its statement did not move.
#print axioms HachiEquiv.Opt.monomial_basis.opt_eq_spec
#print axioms HachiEquiv.Opt.monomial_basis.opt_getD
#print axioms HachiEquiv.Opt.monomial_basis.opt_length
#print axioms HachiEquiv.EvalSplit.monomial_basis_inner_loop_spec
#print axioms HachiEquiv.EvalSplit.monomial_basis_outer_loop_spec
-- Candidate N (Stage 6, `evalsplit::lagrange_basis`) -- the same build over a
-- `CommRing`, with the clear-bit child taken as `p - p*x` so a level costs one
-- ring multiplication and one subtraction per entry. `lagrange_basis_spec` is
-- audited above and its statement did not move either.
#print axioms HachiEquiv.Opt.lagrange_basis.opt_eq_spec
#print axioms HachiEquiv.Opt.lagrange_basis.optLoop_getD
#print axioms HachiEquiv.Opt.lagrange_basis.optLoop_length
#print axioms HachiEquiv.EvalSplit.lagrange_basis_inner_loop_spec
#print axioms HachiEquiv.EvalSplit.lagrange_basis_outer_loop_spec
-- Candidate T17 Changes 1 and 2 (Stage 6, `quadeval::honest_z` via
-- `ring::mul_short_desc` / `ring::mul_short_add_into`) -- multiplication by a
-- short element as signed negacyclic shifts, then the same product accumulated
-- in place. Both headlines are stated against `Ring.negConv`, the same
-- right-hand side `Ring.mul_spec` proves, so `honest_z`'s specification did not
-- move under either change: `honest_z_spec` below carries the statement it had
-- before the fast path existed. The `ell_1` budget is deliberately NOT a
-- hypothesis anywhere, which is what makes the classification unable to affect
-- soundness -- only speed.
--
-- `Opt.lean` (the algebra) and `AuxShort.lean` (the word level) share one copy
-- of `negConvF`/`single`/`contrib`, which is why those audit lines name
-- `AuxShort` rather than `Opt`. Change 2 reuses that algebra verbatim and adds
-- only `Fp`-buffer twins of the loop specs (`coeffK` where Change 1 used
-- `AuxCode.wordAt`).
#print axioms HachiEquiv.Opt.MulShort.opt_eq_spec
#print axioms HachiEquiv.Opt.MulShort.opt_eq_negConvF
#print axioms HachiEquiv.Opt.MulShort.passLoop_eq
#print axioms HachiEquiv.AuxShort.negConvF_single
#print axioms HachiEquiv.AuxShort.negConvF_add_left
#print axioms HachiEquiv.AuxShort.negConvF_coeffK
#print axioms HachiEquiv.AuxShort.inner_spec
#print axioms HachiEquiv.AuxShort.pass_spec
#print axioms HachiEquiv.AuxShort.terms_spec
#print axioms HachiEquiv.AuxShort.termsSum_eq_negConvF
#print axioms HachiEquiv.AuxShort.mul_short_desc_spec
#print axioms HachiEquiv.AuxShort.classify_short_loop_spec
#print axioms HachiEquiv.AuxShort.classify_short_spec
#print axioms HachiEquiv.AuxShort.write_invariant_fp
#print axioms HachiEquiv.AuxShort.inner_add_spec
#print axioms HachiEquiv.AuxShort.pass_add_spec
#print axioms HachiEquiv.AuxShort.terms_add_spec
#print axioms HachiEquiv.AuxShort.mul_short_add_into_spec
#print axioms HachiEquiv.RqBridge.mul_short_desc_spec
#print axioms HachiEquiv.RqBridge.mul_short_add_into_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_z_loop0_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_z_loop1_loop0_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_z_loop1_loop1_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_z_loop1_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_z_spec
-- Candidate T18 Change 3 (Stage 6, `linalg::PolyVec::dot`) -- the fused dot
-- product: the accumulator stays in the transform domain, so the two psi tables
-- are built once per chunk and there is ONE inverse transform and ONE Garner
-- pass per chunk instead of one per term.
--
-- `Scheme.dot_spec`'s statement is UNCHANGED, so its seven call sites are
-- untouched -- the third Stage 6 champion to move an implementation without
-- moving its specification. `AuxProduct` needed no generalizing: `inv_value`
-- already takes an arbitrary buffer and `garner_spec` an arbitrary `x < P`.
--
-- The one new mathematical fact is that the transforms commute with a finite
-- sum (`AuxNTT.difRun_sum` / `ditRun_sum`), which is not free because they are
-- butterfly networks rather than explicit sums.
--
-- The correctness-critical detail is the offset: `untwist` adds `BOUND` once
-- per coefficient, so a fused dot over `L` terms needs `L · BOUND` or the
-- reconstructed integer goes negative and Garner returns a different value.
-- `offConvSum_lt_P` is the bound that pins `DOT_CHUNK = 8192`.
#print axioms HachiEquiv.AuxNTT.difRun_add
#print axioms HachiEquiv.AuxNTT.ditRun_add
#print axioms HachiEquiv.AuxNTT.difRun_sum
#print axioms HachiEquiv.AuxNTT.ditRun_sum
#print axioms HachiEquiv.AuxFused.untwist_value_sum
#print axioms HachiEquiv.AuxFused.accum_spec
#print axioms HachiEquiv.AuxFused.words_a_spec
#print axioms HachiEquiv.AuxFused.words_b_spec
#print axioms HachiEquiv.AuxFused.terms_chunk_spec
#print axioms HachiEquiv.AuxFused.dot_chunk_mod_p_spec
#print axioms HachiEquiv.AuxFused.garner_out_spec
#print axioms HachiEquiv.AuxFused.offConvSum_lt_P
#print axioms HachiEquiv.AuxFused.offConvSum_cast_q
#print axioms HachiEquiv.AuxFused.dot_chunk_word_spec
#print axioms HachiEquiv.AuxFused.chunk_loop_spec
#print axioms HachiEquiv.AuxFused.dot_fused_spec
#print axioms HachiEquiv.RqBridge.dot_fused_spec
#print axioms HachiEquiv.Scheme.dot_spec
-- Candidate T19 Change 4 (Stage 6, `commit::generate_decomps`) -- the CACHED
-- transformed matrix: `PolyMatrix::prepare` twists and forward-transforms every
-- entry of a matrix once, and `PreparedMatrix::apply` then only multiplies
-- pointwise, inverts and reconstructs. The left operand's transform is paid per
-- MATRIX instead of per matrix-vector product, so at 1024 message blocks the
-- Ajtai `A · s` pays it once rather than 1024 times.
--
-- `Scheme.apply_spec`'s conclusion is `mat_vec_mul_spec`'s word for word, which
-- is the whole content of the change: `PrepRow` and `WfPrep` are the only new
-- vocabulary, and `generate_decomps_spec`'s statement is unchanged, so the
-- layers above it are untouched.
--
-- `prepare_one_spec` had to be strengthened with the canonicity of its table
-- (`∀ u ∈ z.val, u.val < p`) before `PrepAt` could be discharged: the values
-- alone do not say the words are reduced, and `dot_prep_chunk_mod_p` reads them
-- back as residues.
--
-- The change is NOT wired into `mat_vec_mul` itself. The store is
-- `rows · cols · 3 · N · 8` bytes -- 192 MiB for `A` (1 × 8192) but 4.8 GiB for
-- `rlin_stmt`'s `M` (5 × 40976) -- so the choice is per caller, and
-- `hachi/src/linalg.rs` records it at `PolyMatrix::prepare`.
#print axioms HachiEquiv.AuxFused.slice_out_spec
#print axioms HachiEquiv.AuxFused.mac_into_spec
#print axioms HachiEquiv.AuxFused.prep_append_spec
#print axioms HachiEquiv.AuxFused.prepare_one_spec
#print axioms HachiEquiv.AuxFused.prep_terms_chunk_spec
#print axioms HachiEquiv.AuxFused.dot_prep_chunk_mod_p_spec
#print axioms HachiEquiv.AuxFused.dot_prep_chunk_word_spec
#print axioms HachiEquiv.AuxFused.prep_chunk_loop_spec
#print axioms HachiEquiv.AuxFused.dot_prepared_spec
#print axioms HachiEquiv.AuxFused.prepare_vec_spec
#print axioms HachiEquiv.RqBridge.dot_prepared_spec
#print axioms HachiEquiv.Scheme.dot_prep_spec
#print axioms HachiEquiv.Scheme.cols_spec
#print axioms HachiEquiv.Scheme.prepare_spec
#print axioms HachiEquiv.Scheme.apply_spec
-- Candidate T20 Change 6 (Stage 6, `commit::generate_decomps`) -- the TWO-PRIME
-- bounded dot. One operand of the Ajtai product is `G⁻¹(m)`, whose coefficients
-- are unsigned gadget digits below `GADGET_BASE = 16`, so the exact convolution
-- coefficient is at most `N · q · 16 = 2^46` rather than `N · q² = 2^73` and
-- thousands of terms fit `p1 · p2`. The third prime's transform is then pure
-- waste: 14336 modular multiplies per term instead of 21504.
--
-- The transforms are reused UNCHANGED: `dot_prep_chunk_mod_p_spec` is already
-- generic in `(p, m, psi, psiinv, ninv, boff)` and states its offset as
-- `boff · L`, with no mention of `BOUND` or `P`, so instantiating it at the
-- digit offsets costs nothing at all.
--
-- What is new is the bound and the reconstruction: `offConvSumD_lt_P12` is the
-- fit that pins `DOT_CHUNK_D = 2048` (the ceiling is 3332), and `garner2_spec`
-- is `garner_spec`'s first stage -- with `x < p1·p2` there is no third digit to
-- compute, which is the step that has no three-prime analogue.
--
-- The precondition is on VALUES, not on types: a caller that hands
-- `dot_prepared_digits` an arbitrary operand gets a wrong answer with no
-- complaint from the compiler. `gadget_decompose_digit_words` is what discharges
-- it, and it is derived from `gadget_decompose_spec` rather than proved by a
-- second induction -- the represented block IS `dd.digit` of the input
-- coefficient, and `dd_digit_val_lt` bounds that. `AuxCode.spec_and` puts the
-- value spec and the bound together without either statement moving, which is
-- why `gadget_decompose_spec` is untouched and its other call sites are too.
--
-- The BALANCED path is deliberately excluded: centred digits give a two-sided
-- word bound (`< 8` or `> q − 9`), for which this argument does not hold.
#print axioms HachiEquiv.AuxCode.spec_and
#print axioms HachiEquiv.AuxCRT.garner2_spec
#print axioms HachiEquiv.Scheme.dd_digit_val_lt
#print axioms HachiEquiv.Scheme.digit_at_lt_base
#print axioms HachiEquiv.Scheme.gadget_decompose_digit_words
#print axioms HachiEquiv.AuxFused.posSumD_le
#print axioms HachiEquiv.AuxFused.negSumD_le
#print axioms HachiEquiv.AuxFused.offConvSumD_lt_P12
#print axioms HachiEquiv.AuxFused.offConvSumD_cast_q
#print axioms HachiEquiv.AuxFused.doff1_val
#print axioms HachiEquiv.AuxFused.doff2_val
#print axioms HachiEquiv.AuxFused.dot_prep_chunk_word_digits_spec
#print axioms HachiEquiv.AuxFused.prep2_garner_out_spec
#print axioms HachiEquiv.AuxFused.prep2_chunk_loop_spec
#print axioms HachiEquiv.AuxFused.dot_prepared_digits_spec
#print axioms HachiEquiv.AuxFused.prepare_vec_two_spec
#print axioms HachiEquiv.RqBridge.dot_prepared_digits_spec
#print axioms HachiEquiv.Scheme.dot_prep_digits_spec
#print axioms HachiEquiv.Scheme.prepare_digits_spec
#print axioms HachiEquiv.Scheme.apply_digits_spec
-- Candidate T22 Change 8 (Stage 6) -- STREAMED decomposition, a WALL removal.
-- `Decomp.message` is `BLOCKS · MESSAGE_ROWS · GADGET_DIGITS` ring elements =
-- 68.7 GiB at the paper's parameters, and the largest single object the prover
-- builds. The three items below take the RAW message and rebuild one block's
-- `sᵢ` at a time, so the resident decomposed state is 64 MiB.
--
-- All three statements are output equalities against the specification the
-- materializing versions already satisfy: nothing here reasons about memory,
-- which is the only way to state a liveness change as a theorem. The measured
-- peak RSS is in the ledger row.
--
-- `commit_streamed_spec` is `commit_spec` on the parts it returns -- the two
-- halves of `generate_decomps_loop_spec` were always independent, and this is
-- that spec with the `ss` half deleted.
--
-- `honest_z_from_raw_spec` is `honest_z_spec`'s conclusion word for word, with
-- `hm` tying the RAW blocks to the opening through `gadgetDecompose`. The
-- device that keeps its loop invariant in the same shape as every other one in
-- that file is the abstract family `sv` with `hsv`: a hypothesis that is itself
-- a specification, saying "decomposing block `j` gives a vector whose entries
-- are `sv j`", discharged from `gadget_decompose_spec`.
--
-- `carrier_from_raw_spec` is the interesting one: the streamed carrier does no
-- gadget arithmetic AT ALL. `carrierEntry` is `splitForm G`, which recomposes
-- its argument with `gadgetMul`, and `gadgetMul ∘ gadgetDecompose` is the
-- identity -- so the recomposition cancels against the decomposition, and the
-- streamed form is both smaller and strictly less work.
#print axioms HachiEquiv.Scheme.commit_streamed_loop_spec
#print axioms HachiEquiv.Scheme.commit_streamed_spec
#print axioms HachiEquiv.QuadEvalProtocol.carrier_from_raw_loop_spec
#print axioms HachiEquiv.QuadEvalProtocol.carrier_from_raw_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_z_from_raw_loop0_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_z_from_raw_loop1_loop0_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_z_from_raw_loop1_loop1_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_z_from_raw_loop1_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_z_from_raw_spec
-- Change 8's ADOPTION: the honest prover now runs from the raw message.
-- `chain_open` takes the raw blocks and decomposes internally, so nothing on
-- the honest path builds `Decomp.message`. Each hypothesis
-- `toBlocks message = wo.message` became "the decomposition of `raw` is
-- `wo.message`", and no conclusion moved -- including `chain_open_spec`'s,
-- which is the whole point: the composed honest prover is the same prover.
--
-- Evidence that the wall was real and is gone: the toy chain test
-- `chain_open_produces_the_messages_the_verifier_reads` was killed by the OOM
-- killer before this change (it materializes 68.7 GiB at `BLOCKS = 1024`) and
-- passes in 180 s after it. It had also never reached `lift_commit`, whose
-- fixture width was wrong by `GADGET_DIGITS` -- a bug the memory wall had been
-- hiding.
#print axioms HachiEquiv.QuadEvalProtocol.carrier_decomp_from_raw_spec
#print axioms HachiEquiv.QuadEvalProtocol.carrier_commit_from_raw_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_compute_v_from_raw_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_compute_resp_from_raw_loop_spec
#print axioms HachiEquiv.QuadEvalProtocol.honest_compute_resp_from_raw_spec
#print axioms HachiEquiv.Chain.chain_open_spec
-- Candidate T25, found by the Phase D reprofile rather than by the work order:
-- `carrier_from_raw` prepares `a` ONCE. It dotted the same `a` against every
-- block, so `dot_fused` re-transformed all 1024 of its entries on each of 1024
-- blocks, 1023/1024 of that work redundant. Measured -33.4% and -35.4% on
-- `quadeval/carrier_from_raw/8` in two independent runs.
--
-- No new item and no new specification: `a` becomes a one-row `PolyMatrix`, and
-- `PreparedMatrix::apply` at one row IS the dot against that row, so
-- `apply_spec` plus `matVecMul_apply` does it. `carrier_from_raw_spec`'s
-- statement is unchanged -- the sixth Stage 6 champion to move an
-- implementation without moving its specification.
#print axioms HachiEquiv.QuadEvalProtocol.dot_eq_carrierEntry_of_decomp

end HachiEquiv.Check
