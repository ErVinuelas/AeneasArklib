import Generated
import Field
import Ring
import RqBridge
import Scheme
import EvalSplit
import Balanced
import QuadEval
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

§ 4 now covers the whole development: the base-field specs (`lean/Field.lean`), the
coefficient-level ring specs (`lean/Ring.lean`), their lifts to ArkLib's `Rq Φ`
(`lean/RqBridge.lean`), the `linalg`, `gadget` and `commit` layers
(`lean/Scheme.lean`) up to perfect correctness of the extracted scheme, and the
multilinear evaluation layer (`lean/EvalSplit.lean`). Every one is proved, so
`lean-wip/` is empty; the procedure for promoting a file into here, should a later
one land there first, is in `lean-wip/README.md`.
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

-- `ω`, and `κ = 2ω`: the weak-opening bound is the double of the sampled one, and
-- the `2 * 16` in `KAPPA`'s docstring is now a checked relation.
example : params.OMEGA.val = HachiParams.hachiOmega := by
  simp [params.OMEGA, HachiParams.hachiOmega]
example : params.KAPPA.val = 2 * params.OMEGA.val := by simp [params.KAPPA, params.OMEGA]

-- `n_D`, and the chain's range parameters at `HonestRangeParams.ofPinnedDigitBase b`:
-- `bZero = b`, `γ = bZero − 1` -- one below the weak-opening `GAMMA = b`, and the
-- two must never be confused (F1 of `STAGE2_SCOPING.md`).
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

-- The modulus travelled across the crate boundary as a value, not a symbol.
example : cpoly.field.P = 4294967197#u64 := by simp [cpoly.field.P]

-- ... and it is the same modulus this crate's own parameter names. If these two
-- ever disagree, every proof bridging the two layers is about two fields.
example : cpoly.field.P = params.Q := by simp [cpoly.field.P, params.Q]

-- The addition has a body, and it is the Rust one: `(self + rhs) % P`, in
-- Aeneas's fallible form. This is the example that an axiom could not satisfy.
example (a b : cpoly.field.Fp) :
    cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add a b
      = (do let s ← a + b; let r ← s % cpoly.field.P; Result.ok r) := by
  simp [cpoly.field.Fp.Insts.CoreOpsArithAddFpFp.add]

-- The other three operator impls, for the same reason: each has a body, and it is
-- the Rust one. `sub` adds the modulus before subtracting (so the `u64` cannot go
-- negative) and `neg`'s outer `% P` is what sends `0` to `0` rather than to `P` --
-- both visible here, which is what "transparent" means in practice.
example (a b : cpoly.field.Fp) :
    cpoly.field.Fp.Insts.CoreOpsArithSubFpFp.sub a b
      = (do let s ← a + cpoly.field.P; let d ← s - b; let r ← d % cpoly.field.P;
            Result.ok r) := by
  simp [cpoly.field.Fp.Insts.CoreOpsArithSubFpFp.sub]

example (a b : cpoly.field.Fp) :
    cpoly.field.Fp.Insts.CoreOpsArithMulFpFp.mul a b
      = (do let p ← a * b; let r ← p % cpoly.field.P; Result.ok r) := by
  simp [cpoly.field.Fp.Insts.CoreOpsArithMulFpFp.mul]

-- `Ext4` -- the quartic extension, the case a one-field newtype does not cover --
-- is deliberately *not* asserted here any more, and the reason is a finding rather
-- than a retreat.
--
-- Workstream 0 checked it, because `smoke.rs` (the extraction probe) used it. The
-- probe is gone and no module of the scheme touches the extension field yet: the
-- ring, the gadget and the commitment are all over `Z_q`, and `Ext4` enters with
-- the *protocol* layer, which commits to multilinear polynomials over the
-- extension and is out of scope until its ArkLib specification is frozen.
--
-- So `Ext4` is no longer in `Generated.lean` at all -- charon's `--include
-- 'cpoly::_'` whitelist decides which foreign items *may* be translated, not which
-- are: it still only follows what the local crate reaches. Asserting anything
-- about it here would be asserting about a name that does not exist, and this
-- section's claim -- that the field layer arrives transparently rather than as
-- axioms -- is made by the `Fp` items above, which are the ones the scheme
-- actually computes with. See NOTES.md § "The model contains what the crate
-- reaches".

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
them stated as iffs because ArkLib states those as `Prop`s.

Nothing is left stated-but-unproved: `lean-wip/` is empty again, and the next file
staged there joins this list when it is proved and promoted. -/

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

#print axioms HachiEquiv.Field.fp_add_spec
#print axioms HachiEquiv.Field.fp_sub_spec
#print axioms HachiEquiv.Field.fp_mul_spec
#print axioms HachiEquiv.Field.fp_neg_spec
#print axioms HachiEquiv.Field.fp_new_spec
#print axioms HachiEquiv.Field.toK_inj_of_Red

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

end HachiEquiv.Check
