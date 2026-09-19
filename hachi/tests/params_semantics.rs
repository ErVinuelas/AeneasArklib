//! The parameters satisfy every side condition the ArkLib specification carries
//! as a hypothesis.
//!
//! `src/params.rs` fixes concrete values for `(q, α, b, digits)`, which the spec
//! leaves generic. Each generic statement comes with hypotheses -- `Fact
//! (Nat.Prime q)`, `1 < b`, `q ≤ b ^ digits` -- and an equivalence proof can only
//! instantiate it if the constants actually discharge them. Those hypotheses are
//! checked on the Lean side too, once the proofs exist; checking them here as
//! well means a bad parameter edit fails in seconds rather than at the end of a
//! Lean build.
//!
//! The dimensions and norm bounds added for the commitment layer are checked the
//! same way, and for two further reasons: `GAMMA` and `BETA_SQ` are *derived*
//! quantities written as literals (Aeneas models `const` arithmetic as fallible,
//! so a derived form would extract as a `Result`), and `KAPPA` has a legality
//! ceiling (`κ² < q`) that only holds at this modulus.

// Every assertion here is *about* a constant -- that is the file's purpose, so
// clippy's "this assertion has a constant value" is the expected state and not a
// finding. The cast is to `u32` for `pow`, on values below 64.
#![allow(clippy::assertions_on_constants, clippy::cast_possible_truncation)]

use hachi::params::{
    BALANCED_SHIFT, BETA_SQ, BLOCKS, B_ZERO, CHAIN_GAMMA, D_QUAD_COLS, D_ROWS, EXT_DEGREE, EXT_W,
    GADGET_BASE, GADGET_DIGITS, GAMMA, HALF_BASE, INNER_ROWS, KAPPA, LIFT_COLS, MESSAGE_ROWS,
    ML_HIGH_LEN, ML_LOW_LEN, ML_POLY_LEN, ML_VARS_HIGH, ML_VARS_LOW, M_ONE, M_ZERO, OMEGA,
    OUTER_ROWS, Q, RANGE_Q_COEFFS, RING_DEGREE, RING_LOG_DEGREE, RLIN_COLS, RLIN_CT, RLIN_CW,
    RLIN_CZ, RLIN_ROWS, Z_BALANCED_SHIFT, Z_BOUND, Z_DIGITS,
};

/// `RANGE_Q_COEFFS` is `∏_{j=1}^{b−1}(x − j²)`, rebuilt here from
/// [`GADGET_BASE`] rather than trusted as a table.
///
/// This is the test the constant's doc names, and it is the only thing standing
/// between a change to `b` and sixteen silently wrong literals. It multiplies the
/// factors out in `u128` with a reduction per step -- deliberately not the
/// crate's own arithmetic and not the Paterson–Stockmeyer schedule the crate
/// evaluates them with, so a shared mistake cannot cancel.
///
/// The exact integers are astronomically larger than `q` (`a_0` is 25 digits),
/// which is why the reduction happens inside the loop and why the coefficients
/// cannot be read off by inspection.
#[test]
fn range_q_coeffs_are_the_product_form() {
    let q: u128 = u128::from(Q);
    // the polynomial `1`, then multiply in `(x − j²)` for each j
    let mut coeffs: Vec<u128> = vec![1];
    for j in 1..GADGET_BASE {
        let sq = u128::from(j) * u128::from(j) % q;
        let mut next: Vec<u128> = vec![0; coeffs.len() + 1];
        for (i, c) in coeffs.iter().enumerate() {
            next[i + 1] = (next[i + 1] + c) % q; // x · c
            next[i] = (next[i] + (q - sq % q) * c) % q; // −j² · c
        }
        coeffs = next;
    }
    assert_eq!(
        coeffs.len(),
        RANGE_Q_COEFFS.len(),
        "b = {GADGET_BASE} gives a degree-{} polynomial, so {} coefficients",
        coeffs.len() - 1,
        coeffs.len()
    );
    for (k, c) in coeffs.iter().enumerate() {
        assert_eq!(
            u128::from(RANGE_Q_COEFFS[k]),
            *c,
            "coefficient a{k} of the range polynomial"
        );
    }
    // the two the doc calls out by hand
    assert_eq!(RANGE_Q_COEFFS[15], 1, "the product is monic");
    let sum_sq: u64 = (1..GADGET_BASE).map(|j| j * j).sum();
    assert_eq!(RANGE_Q_COEFFS[14], Q - sum_sq, "a_14 = −Σ j²");
}

/// `Σ_{u<digits} b^u`: ArkLib's `digitOnesValue b digits` (`Gadget/Core.lean`),
/// the all-ones base-`b` value, so that a constant balanced digit `a`
/// represents `a · ones`.
fn ones(b: u128, digits: u32) -> u128 {
    (0..digits).map(|u| b.pow(u)).sum()
}

/// `(b - 1 - ⌊b/2⌋) · Σ_{u<digits} b^u`: ArkLib's `balancedDigitCapacity b digits`,
/// the largest integer `digits` balanced base-`b` digits represent.
fn balanced_capacity(b: u128, digits: u32) -> u128 {
    (b - 1 - b / 2) * ones(b, digits)
}

/// `a * b mod m` without overflow, for `m < 2^32`.
///
/// Every value below is reduced mod `Q < 2^32`, so each product is `< 2^64`.
fn mul_mod(a: u64, b: u64, m: u64) -> u64 {
    (a % m) * (b % m) % m
}

fn pow_mod(mut base: u64, mut exp: u64, m: u64) -> u64 {
    let mut acc = 1u64;
    base %= m;
    while exp > 0 {
        if exp % 2 == 1 {
            acc = mul_mod(acc, base, m);
        }
        base = mul_mod(base, base, m);
        exp /= 2;
    }
    acc
}

/// `Fact (Nat.Prime q)` is an instance argument of essentially every definition in
/// `CyclotomicRing/PowTwo.lean`, so a composite `Q` would not merely weaken the
/// scheme -- no spec would instantiate at all.
///
/// Trial division is fine here: `Q < 2^32`, so this stops by 65536.
#[test]
fn q_is_prime() {
    assert!(Q > 1);
    assert_eq!(Q % 2, 1);
    let mut d = 3u64;
    while d * d <= Q {
        assert!(Q % d != 0, "Q is divisible by {d}");
        d += 2;
    }
}

/// `Q < 2^32` is the no-overflow argument every `u64` intermediate rests on:
/// a product of two reduced representatives is then `< 2^64`.
#[test]
fn q_fits_in_32_bits() {
    assert!(Q < 1u64 << 32);
    // And the bound is tight enough to be worth stating: this is the *largest*
    // prime below 2^32 that keeps the `- 99` shape, so there is no slack to
    // spend on a wider modulus without moving to `u128` intermediates.
    assert_eq!(Q, (1u64 << 32) - 99);
}

/// `Y^4 - W` is irreducible over `F_q` for non-square `W` exactly when
/// `q ≡ 1 mod 4`, which is what makes `Ext4` a field rather than a ring with
/// zero divisors.
#[test]
fn q_is_one_mod_four() {
    assert_eq!(Q % 4, 1);
}

/// ... and `W` really is a non-square mod `Q`, by Euler's criterion:
/// `W^((q-1)/2) = -1`.
#[test]
fn ext_w_is_a_non_square() {
    assert_eq!(pow_mod(EXT_W, (Q - 1) / 2, Q), Q - 1);
}

/// The extension is the quartic one `cpoly` proves things about.
#[test]
fn ext_degree_is_four() {
    assert_eq!(EXT_DEGREE, 4);
}

/// `RING_DEGREE` is derived from `RING_LOG_DEGREE`; they cannot drift apart.
#[test]
fn ring_degree_is_a_power_of_two() {
    assert_eq!(RING_DEGREE, 1 << RING_LOG_DEGREE);
    assert!(RING_DEGREE.is_power_of_two());
}

/// `zmodDigitDecomposition` requires `1 < b`.
#[test]
fn gadget_base_exceeds_one() {
    assert!(GADGET_BASE > 1);
}

/// `zmodDigitDecomposition` requires `q ≤ b ^ digits`, so that every residue fits
/// in `digits` base-`b` digits and the reconstruction law holds.
#[test]
fn gadget_digits_cover_the_modulus() {
    let capacity = (GADGET_BASE as u128).pow(GADGET_DIGITS as u32);
    assert!(
        u128::from(Q) <= capacity,
        "Q = {Q} exceeds b^digits = {capacity}"
    );
}

/// ... and `digits` is the *smallest* count that does, so the gadget is not
/// carrying a digit that is provably always zero. This is what pins
/// `GADGET_DIGITS` to 8 rather than merely permitting it.
#[test]
fn gadget_digits_are_minimal() {
    let one_fewer = (GADGET_BASE as u128).pow(GADGET_DIGITS as u32 - 1);
    assert!(
        u128::from(Q) > one_fewer,
        "digits could be reduced: Q = {Q} already fits in b^{} = {one_fewer}",
        GADGET_DIGITS - 1
    );
}

/// The parameter file and `cpoly`'s field agree on the modulus. If they ever
/// disagree, every proof that bridges the two layers is about two different
/// fields.
#[test]
fn q_agrees_with_the_field_layer() {
    assert_eq!(Q, cpoly::field::P);
}

/// `GAMMA` is the weak-opening `ℓ∞` bound `γ̄ = b` of ArkLib's paper-parameter
/// mapping (`QuadEval/Soundness.lean`: the paper's `S_b` box relaxed to the
/// symmetric ball `‖·‖∞ ≤ b`). It is a literal in `params.rs`, so nothing but
/// this keeps it in step with the base -- and the honest decomposition's own
/// bound `b - 1` (`gadgetDecompose_zmod_vecLInftyNorm_le`) must sit strictly
/// inside it, or honest openings would need the slack they do not have.
#[test]
fn gamma_is_the_weak_opening_bound() {
    assert_eq!(GAMMA, GADGET_BASE);
    assert!(GADGET_BASE - 1 < GAMMA);
}

/// The digit bound above holds only under `b - 1 ≤ q/2` (`zmodDigit_natAbs_le`),
/// which is what stops a small *non-negative* digit from wrapping to a negative
/// centered representative.
#[test]
fn digit_bound_side_condition_holds() {
    assert!(GADGET_BASE - 1 <= Q / 2);
}

/// `BETA_SQ` is ArkLib's `quadEvalBetaSq γ b τ d m δ` at `γ := b` (Hachi
/// Lemma 8's `4·B_z`, `QuadEval/Soundness.lean`):
/// `4 · (2^m·δ) · (d · ((Σ_{u<τ} b^u) · γ)²)` at `τ = Z_DIGITS = 5` -- the same
/// `zDigits` the correctness chain uses, which is what `Hachi/Params.lean`'s
/// `betaSq` pins (see the `BETA_SQ` docstring). `Z_DIGITS` is the only `τ` in
/// this crate. Also a literal, for the same reason as `GAMMA`.
#[test]
fn beta_sq_is_the_weak_opening_bound() {
    let geom = ones(u128::from(GADGET_BASE), Z_DIGITS as u32);
    let z_l2_sq =
        (MESSAGE_ROWS * GADGET_DIGITS) as u128 * (RING_DEGREE as u128 * (geom * u128::from(GAMMA)).pow(2));
    assert_eq!(BETA_SQ, 4 * z_l2_sq);
}

/// ... and the honest decomposition's own `ℓ₂²` bound
/// (`gadgetDecompose_zmod_vecL2NormSq_le` at these dimensions, with the honest
/// digit bound `b - 1`) sits far inside it -- the slack is what admits the
/// protocol's *extracted* openings, and it is why no admissible challenge can
/// push an honest opening past `BETA_SQ`.
#[test]
fn beta_sq_admits_the_honest_decomposition() {
    let honest = (MESSAGE_ROWS * GADGET_DIGITS) as u128
        * RING_DEGREE as u128
        * u128::from(GADGET_BASE - 1).pow(2);
    assert_eq!(honest, 1_887_436_800);
    assert!(honest <= BETA_SQ);
}

/// `KAPPA` is capped by the Lyubashevsky-Seiler invertibility lemma
/// (`isUnit_of_l1Norm_le`), which needs `κ² < q`: that is what turns the
/// verifier's `0 < ‖c‖₁ ≤ κ` into the invertibility a weak opening actually
/// requires. `params.rs` no longer sits on that ceiling (`⌊√q⌋ = 65535`): the
/// value is the weak-opening bound `ω̄ = 2ω = 32` at [NOZ26] Fig. 9's `ω = 16`
/// (extracted openings carry challenge *differences*), so the checkable facts
/// are legality -- ArkLib Lemma 8's own `hκ : (2ω)² < q` -- and the relation
/// to `ω`.
#[test]
fn kappa_is_legal_for_invertibility() {
    // ArkLib Lemma 8's `hκ : (2ω)² < q`, at the paper's ω = 16.
    assert_eq!(KAPPA, 2 * 16);
    assert!(u128::from(KAPPA).pow(2) < u128::from(Q));
}

/// The other half of that lemma's hypothesis: `q % 8 = 5`. Unlike `κ`, this is
/// not a choice -- it is a property of the Hachi prime, and without it the
/// invertibility argument (and so the meaning of the `κ` check) is gone.
#[test]
fn q_is_five_mod_eight() {
    assert_eq!(Q % 8, 5);
}

/// The honest challenge is `c = 1`, whose `ℓ₁` norm is `1`; the verifier's
/// `0 < ‖c‖₁ ≤ κ` must admit it, or nothing this crate produces would verify.
#[test]
fn the_honest_challenge_is_admissible() {
    assert!(KAPPA >= 1);
}

/// The matrix dimensions are the ones the specification's `PublicParams` shapes
/// are built from. `BLOCKS` and `MESSAGE_ROWS` must be at least 2 so that the
/// per-block and per-row structure -- more than one row, more than one block --
/// is exercised at all; at [NOZ26] Fig. 9 they are 1024 and carry that duty
/// alone. The Ajtai row counts are the paper's `n_A = n_B = 1`, so for them
/// only nonzero-ness is checkable: a single Ajtai row is a legal (and the
/// paper's) shape, not a degenerate one.
#[test]
fn dimensions_are_nondegenerate() {
    assert!(MESSAGE_ROWS >= 2);
    assert!(INNER_ROWS >= 1);
    assert!(OUTER_ROWS >= 1);
    assert!(BLOCKS >= 2);
}

/// The evaluation-split shape constants are the powers of two their variable
/// counts claim, and match the consumer's shape: the reshaped matrix is
/// `blocks × messageRows` (`derivedMsgMatrix`, `QuadEval/Reduction.lean:193`),
/// so `2^nl = BLOCKS` and `2^nh = MESSAGE_ROWS`.
#[test]
fn evalsplit_shape_constants_are_consistent() {
    assert_eq!(1usize << ML_VARS_LOW, ML_LOW_LEN);
    assert_eq!(1usize << ML_VARS_HIGH, ML_HIGH_LEN);
    assert_eq!(ML_LOW_LEN * ML_HIGH_LEN, ML_POLY_LEN);
    assert_eq!(ML_LOW_LEN, BLOCKS);
    assert_eq!(ML_HIGH_LEN, MESSAGE_ROWS);
}

// ---------------------------------------------------------------------------
// The protocol layer's parameters (`Hachi/Params.lean`, ArkLib PR #847)
// ---------------------------------------------------------------------------

/// `KAPPA` is `2ω`: the weak-opening bound is the double of the sampled bound
/// `OMEGA` (extracted openings carry challenge differences), and `ω = 16` is
/// the profile's `hachiOmega`. The `2 * 16` that used to be a magic number.
#[test]
fn kappa_is_twice_omega() {
    assert_eq!(OMEGA, 16);
    assert_eq!(KAPPA, 2 * OMEGA);
}

/// The chain's range parameters are `HonestRangeParams.ofPinnedDigitBase b`:
/// `bZero = b` (forced by the soundness chain) and `γ = bZero − 1` (forced by
/// completeness), so `CHAIN_GAMMA = 15` is one below the weak-opening
/// `GAMMA = 16`; `HALF_BASE` is the `⌊b/2⌋` every balanced digit is re-centred
/// by. `D_ROWS` is Fig. 9's `n_D = 1`, a paper pin like `INNER_ROWS`.
#[test]
fn chain_range_parameters_are_the_pinned_digit_base() {
    assert_eq!(B_ZERO, GADGET_BASE);
    assert_eq!(CHAIN_GAMMA, B_ZERO - 1);
    assert_eq!(CHAIN_GAMMA + 1, GAMMA);
    assert_eq!(HALF_BASE, GADGET_BASE / 2);
    assert_eq!(D_ROWS, 1);
    // `bZero − 1 ≤ γ`, the nested zero-check's reverse range orientation
    // (`params_hZeroγ`), holds with equality at the pinned point.
    assert!(B_ZERO - 1 <= CHAIN_GAMMA);
}

/// `BALANCED_SHIFT` is `balancedShift 16 8 = ⌊b/2⌋ · Σ_{e<8} 16^e`, the
/// message-digit balanced shift, strictly below `q` so its field image is the
/// literal itself.
#[test]
fn balanced_shift_is_half_base_times_the_ones_value() {
    let shift = u128::from(HALF_BASE) * ones(u128::from(GADGET_BASE), GADGET_DIGITS as u32);
    assert_eq!(u128::from(BALANCED_SHIFT), shift);
    assert_eq!(BALANCED_SHIFT, 0x8888_8888);
    assert!(BALANCED_SHIFT < Q);
}

/// `Z_DIGITS = 5` is sized from the honest folded-witness bound, not from `q`:
/// `Z_BOUND = 2ʳ · ω · ⌊b/2⌋` (`honestZBound`, with `r = ML_VARS_LOW`) fits the
/// balanced capacity of five digits (`hcap`) and not of four -- whose capacity
/// is exactly Fig. 9's `30583` (`tau_minimal`) -- and `16^5 < q`, so this is a
/// *bounded* decomposition (`BoundedDigitDecomposition`), not a full-width
/// one. `Z_BALANCED_SHIFT` is its shift `⌊b/2⌋ · Σ_{e<5} 16^e`.
#[test]
fn z_digits_are_minimal_for_the_honest_bound() {
    let b = u128::from(GADGET_BASE);
    let tau = Z_DIGITS as u32;
    let honest = (1u128 << ML_VARS_LOW) * u128::from(OMEGA) * u128::from(HALF_BASE);
    assert_eq!(u128::from(Z_BOUND), honest); // `hzb`, with equality
    assert!(u128::from(Z_BOUND) <= balanced_capacity(b, tau)); // `hcap`
    assert_eq!(balanced_capacity(b, tau), 489_335);
    assert_eq!(balanced_capacity(b, tau - 1), 30_583);
    assert!(balanced_capacity(b, tau - 1) < u128::from(Z_BOUND));
    assert!(b.pow(tau) < u128::from(Q));
    assert_eq!(u128::from(Z_BALANCED_SHIFT), u128::from(HALF_BASE) * ones(b, tau));
    assert_ne!(Z_DIGITS, GADGET_DIGITS);
}

/// The Eq. (20) block widths are `rlinCW/CT/CZ/Cols/Rows` at the profile
/// (`RingSwitch/Rlin.lean`), with the spec's own parenthesization, and the
/// `D` matrix of the QuadEval link is `blocks · messageDigits` wide.
#[test]
fn rlin_block_widths_are_consistent() {
    assert_eq!(RLIN_CW, (1 << ML_VARS_LOW) * GADGET_DIGITS);
    assert_eq!(RLIN_CT, (1 << ML_VARS_LOW) * (INNER_ROWS * GADGET_DIGITS));
    assert_eq!(RLIN_CZ, (1 << ML_VARS_HIGH) * GADGET_DIGITS * Z_DIGITS);
    assert_eq!(RLIN_COLS, RLIN_CW + (RLIN_CT + RLIN_CZ));
    assert_eq!(RLIN_ROWS, D_ROWS + (OUTER_ROWS + (1 + (1 + INNER_ROWS))));
    assert_eq!(D_QUAD_COLS, BLOCKS * GADGET_DIGITS);
    assert_eq!(RLIN_COLS, 57_344);
}

/// The lift key is `μ₀ + n₀ · rhoDigitCount q bZero` wide, and the quotient
/// digit count `⌈log₁₆ q⌉` is `GADGET_DIGITS` (the same `16^7 < q ≤ 16^8` that
/// pins the gadget), so no separate constant carries it.
#[test]
fn lift_cols_is_rlin_cols_plus_the_quotient_digits() {
    let rho_digit_count = GADGET_DIGITS; // `Nat.clog 16 q = 8`
    assert!(u128::from(B_ZERO).pow(rho_digit_count as u32 - 1) < u128::from(Q));
    assert!(u128::from(Q) <= u128::from(B_ZERO).pow(rho_digit_count as u32));
    assert_eq!(LIFT_COLS, RLIN_COLS + RLIN_ROWS * rho_digit_count);
    assert_eq!(LIFT_COLS, 57_384);
}

/// The sumcheck cube covers the digit-committed table, minimally:
/// `LIFT_COLS · d ≤ 2^m₀` (`hμn` at `M = m₀ − 1 = 25`, `sumcheckWidthAtProfile`)
/// and not at one variable fewer (`sumcheckWidthAtProfile_minimal`).
#[test]
fn sumcheck_cube_covers_the_table_minimally() {
    let table = LIFT_COLS * RING_DEGREE;
    assert!(table <= 1 << M_ZERO);
    assert!(table > 1 << (M_ZERO - 1));
    assert_eq!(M_ZERO, 25 + 1);
}

/// The nested zero-check's second cube covers the `n₀` quotient rows,
/// minimally: `n₀ ≤ 2^m₁` (`hn`) and not at one variable fewer. ArkLib leaves
/// `m₁` free under that inequality and names no value, so this is the one
/// constant checked by its defining inequality alone.
#[test]
fn zero_check_cube_covers_the_quotient_rows_minimally() {
    assert!(RLIN_ROWS <= 1 << M_ONE);
    assert!(RLIN_ROWS > 1 << (M_ONE - 1));
}

/// [`SHIFT_T`] is `p_{2j+1} · C(2j+1, m)`, rebuilt from [`RANGE_Q_COEFFS`] and
/// Pascal's triangle.
///
/// The same contract [`range_q_coeffs_are_the_product_form`] holds over
/// [`RANGE_Q_COEFFS`]: the table is a literal because the extraction has no
/// `const fn`, and a literal a test checks is worth more than a computation the
/// model cannot see. Everything here is pinned to `GADGET_BASE`, so the test
/// derives the shape from it rather than from `SHIFT_ROWS`/`SHIFT_DEG` — if
/// `b` moved and the three constants moved with it, the entries would still
/// have to be rebuilt, and this is what would say so.
#[test]
fn shift_t_is_the_binomial_table() {
    let q: u128 = u128::from(hachi::params::Q);
    let b: usize = hachi::params::GADGET_BASE as usize;
    assert_eq!(hachi::params::SHIFT_ROWS, b, "one row per nonzero p_k, and P_b is odd");
    assert_eq!(hachi::params::SHIFT_DEG, 2 * b, "2b coefficients of degree 0 … 2b−1");
    assert_eq!(
        hachi::params::SHIFT_T_LEN,
        hachi::params::SHIFT_ROWS * hachi::params::SHIFT_DEG,
        "SHIFT_T_LEN is a literal because a product is a Result in the model"
    );
    assert_eq!(hachi::params::SHIFT_T.len(), hachi::params::SHIFT_T_LEN);

    // Pascal's triangle up to row 2b−1, exactly, in u128 — C(31,15) is 3.0e8
    let top: usize = 2 * b - 1;
    let mut pascal: Vec<Vec<u128>> = vec![vec![0; top + 1]; top + 1];
    for k in 0..=top {
        pascal[k][0] = 1;
        for m in 1..=k {
            pascal[k][m] = pascal[k - 1][m - 1] + if m <= k - 1 { pascal[k - 1][m] } else { 0 };
        }
    }
    assert_eq!(pascal[31][15], 300_540_195, "the largest binomial in the table");

    for j in 0..hachi::params::SHIFT_ROWS {
        let k = 2 * j + 1;
        let p = u128::from(hachi::params::RANGE_Q_COEFFS[j]);
        for m in 0..hachi::params::SHIFT_DEG {
            let want = if m <= k { p * (pascal[k][m] % q) % q } else { 0 };
            assert_eq!(
                u128::from(hachi::params::SHIFT_T[j * hachi::params::SHIFT_DEG + m]),
                want,
                "SHIFT_T[j = {j} (k = {k})][m = {m}]"
            );
        }
    }
}

/// The Taylor-shift identity the table exists for, checked numerically:
/// `P_b(lo + Δ·T) = Σ_m Δ^m T^m · Σ_{k ≥ m} p_k C(k,m) lo^{k−m}`.
///
/// `range_product_base` is `P_b`, so this compares the shifted coefficients
/// against a direct evaluation at several nodes. A table entry can be wrong in
/// a way Pascal's triangle reproduces — a transposed index, say — and the test
/// above would not see it; this one would.
#[test]
fn the_shift_table_reproduces_the_range_polynomial() {
    use hachi::params::{SHIFT_DEG, SHIFT_ROWS, SHIFT_T, Q};
    let mul = |a: u64, b: u64| ((u128::from(a) * u128::from(b)) % u128::from(Q)) as u64;
    let add = |a: u64, b: u64| (a + b) % Q;
    let sub = |a: u64, b: u64| (a + Q - b) % Q;
    for (lo, hi) in [(0u64, 1u64), (7, 3), (123_456, 789), (Q - 1, 2), (5, 5)] {
        let d = sub(hi, lo);
        // powers of lo
        let mut lop = vec![1u64; SHIFT_DEG];
        for k in 1..SHIFT_DEG {
            lop[k] = mul(lop[k - 1], lo);
        }
        // the shifted coefficients
        let mut c = vec![0u64; SHIFT_DEG];
        let mut dpow = 1u64;
        for m in 0..SHIFT_DEG {
            let mut s = 0u64;
            let mut j = m / 2;
            while j < SHIFT_ROWS {
                let k = 2 * j + 1;
                s = add(s, mul(SHIFT_T[j * SHIFT_DEG + m], lop[k - m]));
                j += 1;
            }
            c[m] = mul(dpow, s);
            dpow = mul(dpow, d);
        }
        // against the direct evaluation at every node the round uses
        for t in 0..hachi::params::ROUND_NODES as u64 {
            let folded = add(lo, mul(d, t));
            let direct = hachi::zerocheck::range_product_base(cpoly::field::Fp::new(folded));
            let mut shifted = 0u64;
            let mut tp = 1u64;
            for m in 0..SHIFT_DEG {
                shifted = add(shifted, mul(c[m], tp));
                tp = mul(tp, t);
            }
            assert_eq!(
                direct.to_u64(),
                shifted,
                "the shift disagrees at lo = {lo}, hi = {hi}, T = {t}"
            );
        }
    }
}
