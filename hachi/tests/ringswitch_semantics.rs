//! `src/ringswitch.rs`: the balanced digit decomposition of a quotient row.
//!
//! The headline test is [`rho_digits_reconstruct_the_row`], the specification's
//! `rhoDigits_reconstruct` (`RingSwitch/RhoDigits.lean:169`) at these
//! parameters: `Σ_u bᵘ · rho_digits(ρ, u) = ρ` for a row within the ring
//! dimension. The others pin the two facts the lift depends on -- that each
//! digit is `⌊b/2⌋`-short as a centered residue, which is what makes
//! `liftShort` pass at `CHAIN_GAMMA = 15`, and that every digit is a full
//! `RING_DEGREE`-wide block, which is what makes the widened `w̃` table a
//! uniform grid.
//!
//! # Scale
//!
//! Real consts throughout. A quotient digit is one coefficient loop of
//! `RING_DEGREE = 1024` balanced digits and one `Rq`; nothing here reaches a
//! ring product.
//!
//! The references are written in the specification's shape and not the crate's:
//! `Nat.digits b n` as a list read with `getD e 0`, `ZMod.valMinAbs` as a signed
//! integer, and `bᵘ` as a bit shift rather than `base_pow`'s repeated modular
//! multiplication.

// The centered view of a residue is a *signed* integer (`ZMod.valMinAbs`), and
// the references below compute it as one. Every value cast is below `q < 2^32`.
#![allow(clippy::cast_possible_wrap)]
#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::cast_sign_loss)]

mod support;

use cpoly::Fp;
use hachi::commit::l_infty_norm;
use hachi::params::{
    BALANCED_SHIFT, CHAIN_GAMMA, GADGET_BASE, GADGET_DIGITS, HALF_BASE, Q, RING_DEGREE,
};
use hachi::ring::Rq;
use hachi::ringswitch::rho_digits;
use support::{rq_from_u64s, show, Lcg};

/// `Nat.digits b n`, the whole little-endian list.
fn nat_digits(mut n: u64, b: u64) -> Vec<u64> {
    let mut out = Vec::new();
    while n > 0 {
        out.push(n % b);
        n /= b;
    }
    out
}

/// `ZMod.valMinAbs`, as the signed integer it is.
fn val_min_abs(c: Fp) -> i64 {
    let v = c.to_u64();
    if v <= Q / 2 {
        v as i64
    } else {
        v as i64 - Q as i64
    }
}

/// `balancedDigit 16 (rhoDigitCount q 16) c u`, as its centered integer value.
fn balanced_digit_ref(c: Fp, u: usize) -> i64 {
    let shifted = ((u128::from(c.to_u64()) + u128::from(BALANCED_SHIFT)) % u128::from(Q)) as u64;
    let ds = nat_digits(shifted, GADGET_BASE);
    let d = if u < ds.len() { ds[u] as i64 } else { 0 };
    d - HALF_BASE as i64
}

/// Reduce a centered integer into `[0, q)`.
fn into_field(x: i128) -> u64 {
    let q = i128::from(Q);
    (((x % q) + q) % q) as u64
}

/// Digit `u` of a row is `balancedDigit … (ρ.coeff k) u` at every coefficient
/// `k` below the ring dimension -- checked against an independent computation
/// of the balanced digit, not against `balanced_digit_at`.
#[test]
fn rho_digits_are_the_balanced_digits_of_each_coefficient() {
    let mut rng = Lcg::new(0x8047_0000_0000_0001);
    for _ in 0..4 {
        let rho = rng.next_rq();
        for u in 0..GADGET_DIGITS {
            let d = rho_digits(&rho, u);
            for k in 0..RING_DEGREE {
                assert_eq!(
                    val_min_abs(d.coeff(k)),
                    balanced_digit_ref(rho.coeff(k), u),
                    "digit {u}, coefficient {k}"
                );
            }
        }
    }
}

/// The reconstruction law `Σ_u bᵘ · rho_digits(ρ, u) = ρ`, summed over the
/// centered digit values in `ℤ`. The digit count is `rhoDigitCount q bZero`,
/// which is `GADGET_DIGITS` here -- a decomposition one digit short would fail
/// at `q - 1`, which is in the corpus.
#[test]
fn rho_digits_reconstruct_the_row() {
    let mut rng = Lcg::new(0x8047_0000_0000_0002);
    let mut corpus = vec![
        Rq::zero(),
        Rq::one(),
        rq_from_u64s(&[Q - 1, 0, Q / 2, 1]),
    ];
    for _ in 0..4 {
        corpus.push(rng.next_rq());
    }
    for rho in corpus {
        let digits: Vec<Rq> = (0..GADGET_DIGITS).map(|u| rho_digits(&rho, u)).collect();
        for k in 0..RING_DEGREE {
            let mut acc: i128 = 0;
            for (u, d) in digits.iter().enumerate() {
                acc += (1i128 << (4 * u)) * i128::from(val_min_abs(d.coeff(k)));
            }
            assert_eq!(
                into_field(acc),
                rho.coeff(k).to_u64(),
                "coefficient {k} of {} was not reconstructed",
                show(&rho)
            );
        }
    }
}

/// Every quotient digit is `⌊b/2⌋ = 8`-short as a centered residue,
/// unconditionally in `ρ` (`rhoDigits_valMinAbs_natAbs_le`). That is what makes
/// the `liftShort` range check pass at `CHAIN_GAMMA = 15` -- and it has room to
/// spare, which is why the check is a tautology at these parameters.
#[test]
fn rho_digits_are_short() {
    let mut rng = Lcg::new(0x8047_0000_0000_0003);
    for _ in 0..4 {
        let rho = rng.next_rq();
        for u in 0..GADGET_DIGITS {
            let n = l_infty_norm(&rho_digits(&rho, u));
            assert!(n <= HALF_BASE, "digit {u} has ‖·‖∞ = {n}, over ⌊b/2⌋");
            assert!(n <= CHAIN_GAMMA, "digit {u} misses the chain's γ");
        }
    }
}

/// A quotient digit is a full `d`-wide block, whatever the row's own degree --
/// the truncate-and-pad shape `rhoDigits_natDegree_le` records, and what makes
/// the widened table a uniform grid.
#[test]
fn rho_digits_have_the_full_ring_width() {
    let sparse = rq_from_u64s(&[7, 0, 0, 3]);
    for u in 0..GADGET_DIGITS {
        let d = rho_digits(&sparse, u);
        assert_eq!(d.len(), RING_DEGREE, "digit {u} is not d-wide");
    }
}

/// Digits past the count are not zero, they are `-⌊b/2⌋`: the unsigned digit
/// runs out and `0 - 8` is what is left. Worth pinning, because "the digits
/// above the count vanish" is true of the unsigned map and false of this one.
#[test]
fn quotient_digits_past_the_count_are_minus_half_base() {
    let rho = Rq::one();
    let d = rho_digits(&rho, GADGET_DIGITS + 3);
    for k in 0..RING_DEGREE {
        assert_eq!(
            val_min_abs(d.coeff(k)),
            -(HALF_BASE as i64),
            "coefficient {k} past the digit count"
        );
    }
}
