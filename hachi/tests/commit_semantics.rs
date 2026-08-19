//! `src/commit.rs`: the inner-outer commitment, its weak verifier, and the
//! centered norms the verifier checks.
//!
//! The two properties worth testing are the two the specification proves and
//! reduces to, respectively:
//!
//! * **perfect correctness** -- an honest commit-then-verify always accepts
//!   (`InnerOuter/Correctness.lean`);
//! * **the checks actually check something** -- each rejection path fires when the
//!   thing it guards against happens. A verifier that accepts everything satisfies
//!   correctness too, so correctness alone is not evidence.
//!
//! Public parameters are constructed explicitly from a seeded generator: the
//! specification's `setup` samples them, and deriving them from a seed is a design
//! decision this crate has not made (see the module header of `src/commit.rs`).

mod support;

use cpoly::Fp;
use hachi::commit::{
    centered_abs, commit, commit_with_decomps, derived_message, generate_decomps, l1_norm,
    l2_norm_sq, l_infty_norm, verify, verify_weak, Decomp, Opening, PublicParams,
};
use hachi::linalg::{flatten_blocks, PolyVec};
use hachi::params::{
    BETA_SQ, BLOCKS, GADGET_DIGITS, GAMMA, INNER_ROWS, KAPPA, MESSAGE_ROWS, OUTER_ROWS, Q,
    RING_DEGREE,
};
use hachi::ring::Rq;
use support::{rq_from_u64s, show_vec, Lcg};

/// Public parameters of the shapes the specification's `PublicParams` fixes:
/// `A : INNER_ROWS × (MESSAGE_ROWS · digits)` and
/// `B : OUTER_ROWS × (BLOCKS · (INNER_ROWS · digits))`.
fn params_from_seed(seed: u64) -> PublicParams {
    let mut rng = Lcg::new(seed);
    let a = rng.next_poly_matrix(INNER_ROWS, MESSAGE_ROWS * GADGET_DIGITS);
    let b = rng.next_poly_matrix(OUTER_ROWS, BLOCKS * (INNER_ROWS * GADGET_DIGITS));
    PublicParams::new(a, b)
}

/// A message: `BLOCKS` blocks of `MESSAGE_ROWS` ring elements.
fn message_from_seed(seed: u64) -> Vec<PolyVec> {
    let mut rng = Lcg::new(seed);
    let mut m = Vec::new();
    for _ in 0..BLOCKS {
        m.push(rng.next_poly_vec(MESSAGE_ROWS));
    }
    m
}

// ---------------------------------------------------------------------------
// Norms
// ---------------------------------------------------------------------------

/// The centered representative folds the upper half of `[0, q)` down: `q - 1` is
/// `-1`, so its absolute value is `1`. An implementation that forgot to center
/// would report `q - 1` here, and would then accept openings that are not short.
#[test]
fn centered_abs_folds_the_upper_half() {
    assert_eq!(centered_abs(Fp::ZERO), 0);
    assert_eq!(centered_abs(Fp::ONE), 1);
    assert_eq!(centered_abs(Fp::new(Q - 1)), 1);
    assert_eq!(centered_abs(Fp::new(Q - 5)), 5);
    // The boundary: q is odd, so q/2 = (q-1)/2 is the largest value that stays
    // positive, and the next one folds to the same magnitude.
    assert_eq!(centered_abs(Fp::new(Q / 2)), Q / 2);
    assert_eq!(centered_abs(Fp::new(Q / 2 + 1)), Q / 2);
}

#[test]
fn norms_of_simple_elements() {
    let a = rq_from_u64s(&[1, 2, 3]);
    assert_eq!(l1_norm(&a), 6);
    assert_eq!(l_infty_norm(&a), 3);
    assert_eq!(l2_norm_sq(&a), 1 + 4 + 9);

    assert_eq!(l1_norm(&Rq::zero()), 0);
    assert_eq!(l_infty_norm(&Rq::zero()), 0);
    assert_eq!(l2_norm_sq(&Rq::zero()), 0);

    // ‖1‖₁ = 1, which is what makes the honest challenge pass `0 < ‖c‖₁ ≤ κ`
    // (the spec's `Rq.l1Norm_one`).
    assert_eq!(l1_norm(&Rq::one()), 1);
}

/// Negation does not change any centered norm; the norms are of `±` magnitudes.
#[test]
fn norms_are_invariant_under_negation() {
    let mut rng = Lcg::new(0x1357_9BDF_0246_8ACE);
    for _ in 0..8 {
        let a = rng.next_rq();
        assert_eq!(l1_norm(&a), l1_norm(&a.neg()));
        assert_eq!(l_infty_norm(&a), l_infty_norm(&a.neg()));
        assert_eq!(l2_norm_sq(&a), l2_norm_sq(&a.neg()));
    }
}

/// The `ℓ₂²` norm is computed in `u128` because it has to be: a full-width
/// element's squared norm exceeds `u64`. This is the case that would overflow --
/// every coefficient at the maximum centered magnitude.
#[test]
fn l2_norm_sq_does_not_overflow_at_the_maximum() {
    let mut coeffs = Vec::new();
    for _ in 0..RING_DEGREE {
        coeffs.push(Fp::new(Q / 2));
    }
    let worst = Rq::from_coeffs(&coeffs);
    let expected = RING_DEGREE as u128 * u128::from(Q / 2).pow(2);
    assert_eq!(l2_norm_sq(&worst), expected);
    assert!(
        expected > u128::from(u64::MAX),
        "the overflow case is not actually beyond u64: {expected}"
    );
}

// ---------------------------------------------------------------------------
// Correctness
// ---------------------------------------------------------------------------

/// **Perfect correctness.** An honest commitment and its honest weak opening
/// verify -- the computational content of `InnerOuter/Correctness.lean`'s
/// `perfectlyCorrect`.
#[test]
fn honest_commitments_verify() {
    for seed in [1u64, 2, 3] {
        let pp = params_from_seed(0xA000 + seed);
        let m = message_from_seed(0xB000 + seed);
        let (u, decomp) = commit(&pp, &m);
        assert_eq!(u.len(), OUTER_ROWS);
        let opening = Opening::honest(decomp);
        assert!(
            verify_weak(&pp, &u, &opening),
            "weak verification of an honest opening failed (seed {seed})"
        );
        assert!(
            verify(&pp, &m, &u, &opening),
            "full verification of an honest opening failed (seed {seed})"
        );
    }
}

/// The message really is recoverable from the opening: `mᵢ = G · sᵢ`, the spec's
/// `derivedMessage` ([NOZ26] Eq. (13)). This is what lets a weak opening not
/// store the message.
#[test]
fn the_message_is_derived_from_the_decomposition() {
    let pp = params_from_seed(0xC001);
    let m = message_from_seed(0xC002);
    let decomp = generate_decomps(&pp, &m);
    let derived = derived_message(&decomp);
    assert_eq!(derived.len(), m.len());
    for i in 0..m.len() {
        assert!(
            derived[i].equals(&m[i]),
            "block {i} was not recovered:\n  want {}\n  got  {}",
            show_vec(&m[i]),
            show_vec(&derived[i])
        );
    }
}

/// The honest decomposition is short, which is *why* verification accepts it:
/// `‖t̂‖∞ ≤ γ` on the flattening, and `‖sᵢ‖₂² ≤ βSq` per block.
#[test]
fn the_honest_decomposition_meets_the_verifier_bounds() {
    let pp = params_from_seed(0xC003);
    let m = message_from_seed(0xC004);
    let decomp = generate_decomps(&pp, &m);

    let flat = flatten_blocks(decomp.inner_decomps());
    assert_eq!(flat.len(), BLOCKS * (INNER_ROWS * GADGET_DIGITS));
    assert!(hachi::commit::vec_l_infty_norm(&flat) <= GAMMA);

    for i in 0..decomp.blocks() {
        assert!(hachi::commit::vec_l2_norm_sq(decomp.message(i)) <= BETA_SQ);
    }
}

/// The commitment is the outer product of the flattened inner decomposition, and
/// `commit` is `commit_with_decomps` of what `generate_decomps` produced --
/// i.e. the two entry points agree.
#[test]
fn commit_agrees_with_commit_with_decomps() {
    let pp = params_from_seed(0xC005);
    let m = message_from_seed(0xC006);
    let (u, decomp) = commit(&pp, &m);
    assert!(u.equals(&commit_with_decomps(&pp, &decomp)));
}

// ---------------------------------------------------------------------------
// Rejection
// ---------------------------------------------------------------------------

/// A tampered coefficient in the inner decomposition breaks the inner gadget
/// relation `A sᵢ = G t̂ᵢ`, and the verifier says so.
#[test]
fn a_tampered_inner_decomposition_is_rejected() {
    let pp = params_from_seed(0xD001);
    let m = message_from_seed(0xD002);
    let (u, decomp) = commit(&pp, &m);

    // Rebuild the decomposition with one coefficient of t̂₀ slot 0 flipped.
    let mut messages = Vec::new();
    let mut inners = Vec::new();
    for i in 0..decomp.blocks() {
        messages.push(decomp.message(i).copy());
        let t = decomp.inner_decomp(i);
        let mut entries = Vec::new();
        for j in 0..t.len() {
            if i == 0 && j == 0 {
                entries.push(t.get(j).add(&Rq::one()));
            } else {
                entries.push(t.get(j).copy());
            }
        }
        inners.push(PolyVec::new(entries));
    }
    let tampered = Opening::honest(Decomp::new(messages, inners));
    assert!(
        !verify_weak(&pp, &u, &tampered),
        "a tampered inner decomposition verified"
    );
}

/// A tampered decomposed message breaks both the gadget relation and the derived
/// message, so both the weak verifier and the full one reject.
#[test]
fn a_tampered_message_decomposition_is_rejected() {
    let pp = params_from_seed(0xD003);
    let m = message_from_seed(0xD004);
    let (u, decomp) = commit(&pp, &m);

    let mut messages = Vec::new();
    let mut inners = Vec::new();
    for i in 0..decomp.blocks() {
        let s = decomp.message(i);
        let mut entries = Vec::new();
        for j in 0..s.len() {
            if i == 0 && j == 0 {
                entries.push(s.get(j).add(&Rq::one()));
            } else {
                entries.push(s.get(j).copy());
            }
        }
        messages.push(PolyVec::new(entries));
        inners.push(decomp.inner_decomp(i).copy());
    }
    let tampered = Opening::honest(Decomp::new(messages, inners));
    assert!(!verify_weak(&pp, &u, &tampered), "a tampered sᵢ verified");
    assert!(!verify(&pp, &m, &u, &tampered), "a tampered sᵢ verified fully");
}

/// A commitment to a different message does not verify against this opening --
/// the property binding is about, here in its trivial (honest) direction.
#[test]
fn an_opening_does_not_verify_against_the_wrong_commitment() {
    let pp = params_from_seed(0xD005);
    let m = message_from_seed(0xD006);
    let other = message_from_seed(0xD007);
    let (u, decomp) = commit(&pp, &m);
    let (u_other, _) = commit(&pp, &other);
    assert!(!u.equals(&u_other), "two messages collided; pick another seed");

    let opening = Opening::honest(decomp);
    assert!(
        !verify_weak(&pp, &u_other, &opening),
        "an opening verified against another message's commitment"
    );
}

/// The full verifier ties the opening to a *claimed* message, so a correct
/// opening against the wrong claim is rejected even though the weak checks pass.
#[test]
fn the_full_verifier_checks_the_claimed_message() {
    let pp = params_from_seed(0xD008);
    let m = message_from_seed(0xD009);
    let other = message_from_seed(0xD00A);
    let (u, decomp) = commit(&pp, &m);
    let opening = Opening::honest(decomp);
    assert!(verify_weak(&pp, &u, &opening));
    assert!(
        !verify(&pp, &other, &u, &opening),
        "the claimed message was not checked"
    );
}

/// The `ℓ∞` bound is a real check: an inner decomposition that satisfies the
/// gadget relation but is *not* short must still be rejected.
///
/// Constructed rather than tampered: scale a valid `t̂` by the ring constant `1`
/// after adding `b·(one) - ...`; the simplest witness is to replace `t̂ᵢ` by a
/// vector whose gadget product is the same but whose coefficients are large,
/// which is what the digit slots `(e, e+1)` allow -- `b·(slot e) = slot (e+1)`.
/// Here `b = 2`: moving one unit from slot `e+1` into two units of slot `e`
/// preserves `Σ bᵉ·t̂ₑ` while pushing `‖t̂‖∞` to 2.
#[test]
fn a_long_inner_decomposition_is_rejected_even_when_the_relation_holds() {
    let pp = params_from_seed(0xD00B);
    let m = message_from_seed(0xD00C);
    let (_, decomp) = commit(&pp, &m);

    // Rebuild t̂ with the digit-slot rewrite above applied to block 0's first
    // gadget block: slot 0 += 2·1, slot 1 -= 1. The gadget sum is unchanged
    // (2^0·2 - 2^1·1 = 0) but slot 0 now has a coefficient of magnitude ≥ 2.
    let two = rq_from_u64s(&[2]);
    let one = Rq::one();
    let mut messages = Vec::new();
    let mut inners = Vec::new();
    for i in 0..decomp.blocks() {
        messages.push(decomp.message(i).copy());
        let t = decomp.inner_decomp(i);
        let mut entries = Vec::new();
        for j in 0..t.len() {
            if i == 0 && j == 0 {
                entries.push(t.get(j).add(&two));
            } else if i == 0 && j == 1 {
                entries.push(t.get(j).sub(&one));
            } else {
                entries.push(t.get(j).copy());
            }
        }
        inners.push(PolyVec::new(entries));
    }
    let long = Decomp::new(messages, inners);

    // The gadget relation still holds -- this is the point of the construction --
    // so the rejection has to come from the norm check.
    let flat = flatten_blocks(long.inner_decomps());
    assert!(
        hachi::commit::vec_l_infty_norm(&flat) > GAMMA,
        "the constructed decomposition is not actually long"
    );

    // Re-commit to it, so the outer check passes and the ℓ∞ check is the only
    // thing that can reject.
    let u_long = commit_with_decomps(&pp, &long);
    let opening = Opening::honest(long);
    assert!(
        !verify_weak(&pp, &u_long, &opening),
        "a long inner decomposition verified"
    );
}

/// The challenge checks are real too: `c = 0` fails `0 < ‖c‖₁`, and a challenge
/// with `‖c‖₁ > κ` fails the upper bound. Both are checked with an otherwise
/// honest opening, so the challenge is the only thing that can reject.
#[test]
fn inadmissible_challenges_are_rejected() {
    let pp = params_from_seed(0xD00D);
    let m = message_from_seed(0xD00E);
    let (u, decomp) = commit(&pp, &m);

    let zero_challenge = PolyVec::zeros(decomp.blocks());
    let mut messages = Vec::new();
    let mut inners = Vec::new();
    for i in 0..decomp.blocks() {
        messages.push(decomp.message(i).copy());
        inners.push(decomp.inner_decomp(i).copy());
    }
    let opening = Opening::new(Decomp::new(messages, inners), zero_challenge);
    assert!(
        !verify_weak(&pp, &u, &opening),
        "a zero challenge verified (0 < ‖c‖₁ not checked)"
    );

    // A challenge whose ℓ₁ norm exceeds κ: `KAPPA + 1` spread over one
    // coefficient is enough, and the centered norm of that coefficient is
    // exactly its value since KAPPA + 1 < q/2.
    let big = rq_from_u64s(&[KAPPA + 1]);
    assert_eq!(l1_norm(&big), KAPPA + 1);
    let mut challenges = Vec::new();
    for _ in 0..decomp.blocks() {
        challenges.push(big.copy());
    }
    let mut messages = Vec::new();
    let mut inners = Vec::new();
    for i in 0..decomp.blocks() {
        messages.push(decomp.message(i).copy());
        inners.push(decomp.inner_decomp(i).copy());
    }
    let opening = Opening::new(Decomp::new(messages, inners), PolyVec::new(challenges));
    assert!(
        !verify_weak(&pp, &u, &opening),
        "an over-long challenge verified (‖c‖₁ ≤ κ not checked)"
    );
}

/// And the `ℓ₂²` check on the scaled message: a challenge that is admissible on
/// its own (`0 < ‖c‖₁ ≤ κ`) but blows up `‖c·sᵢ‖₂²` must be rejected.
#[test]
fn a_challenge_that_lengthens_the_message_is_rejected() {
    let pp = params_from_seed(0xD00F);
    let m = message_from_seed(0xD010);
    let (u, decomp) = commit(&pp, &m);

    // c = 1000: ‖c‖₁ = 1000 ≤ κ, but scaling every coefficient of sᵢ by 1000
    // takes ‖c·sᵢ‖₂² well past βSq (the honest value sits *on* βSq).
    let c = rq_from_u64s(&[1000]);
    assert!(l1_norm(&c) <= KAPPA);
    let mut challenges = Vec::new();
    let mut messages = Vec::new();
    let mut inners = Vec::new();
    for i in 0..decomp.blocks() {
        challenges.push(c.copy());
        messages.push(decomp.message(i).copy());
        inners.push(decomp.inner_decomp(i).copy());
    }
    let opening = Opening::new(Decomp::new(messages, inners), PolyVec::new(challenges));
    assert!(
        !verify_weak(&pp, &u, &opening),
        "a challenge that lengthens the message verified"
    );
}
