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

use cpoly::{Ext4, Fp};
use hachi::commit::l_infty_norm;
use hachi::endpiece::{lift_short_check, rho_digits_short_check};
use hachi::linalg::PolyVec;
use hachi::params::{
    BALANCED_SHIFT, CHAIN_GAMMA, GADGET_BASE, GADGET_DIGITS, HALF_BASE, Q, RING_DEGREE,
};
use hachi::ring::Rq;
use hachi::ringswitch::{
    c_eval_at, c_eval_at_modulus, lift_commit, lift_message, rho_digit_as_rq, rho_digits,
    rho_digits_at, LiftedWitness, QuotientRow,
};
use support::{coeffs_of, rq_from_u64s, show, Lcg};

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

/// Carry an `Rq` coefficient array as the specification's quotient-polynomial
/// representation. The production type keeps the two algebraic roles distinct.
fn quotient_row(a: &Rq) -> QuotientRow {
    let mut coeffs = Vec::new();
    for k in 0..RING_DEGREE {
        coeffs.push(a.coeff(k));
    }
    QuotientRow::new(&coeffs)
}

/// `rhoAsRq` is a presentation change, not a cyclotomic reduction: every
/// coefficient below `d` is preserved.
#[test]
fn rho_as_rq_preserves_the_quotient_row_coefficients() {
    let mut rng = Lcg::new(0x8047_0000_0000_0010);
    for _ in 0..4 {
        let a = rng.next_rq();
        let row = quotient_row(&a);
        assert_eq!(coeffs_of(&row.to_rq()), coeffs_of(&a));
    }
}

/// `finProdFinEquiv.symm` splits the flat index as `(j / digits, j %
/// digits)`. This checks both sides of a row boundary against separate calls to
/// `rho_digits`.
#[test]
fn rho_digit_as_rq_uses_row_major_digit_indices() {
    let mut rng = Lcg::new(0x8047_0000_0000_0011);
    let a = rng.next_rq();
    let b = rng.next_rq();
    let rho = vec![quotient_row(&a), quotient_row(&b)];
    for j in 0..2 * GADGET_DIGITS {
        let source = if j < GADGET_DIGITS { &a } else { &b };
        let expected = rho_digits(source, j % GADGET_DIGITS);
        assert!(rho_digit_as_rq(&rho, j).equals(&expected), "flat index {j}");
    }
}

/// `rho_digits_at` is the specification's own `rhoDigits Φ bDig (ρ i) u`: the
/// digit of row `i` at index `u`, addressed by the pair rather than through a
/// flat index. Two things are pinned here, and the second is why the pair form
/// exists at all.
///
/// The reference is written the specification's way (the balanced digit of the
/// row's own coefficients), not by calling `rho_digits`.
#[test]
fn rho_digits_at_is_the_balanced_digit_of_that_row() {
    let mut rng = Lcg::new(0x8047_0000_0000_0021);
    let rows = [rng.next_rq(), rng.next_rq(), rng.next_rq()];
    let rho: Vec<QuotientRow> = rows.iter().map(quotient_row).collect();
    for (i, source) in rows.iter().enumerate() {
        for u in [0usize, 1, GADGET_DIGITS - 1] {
            let digit = rho_digits_at(&rho, i, u);
            for k in [0usize, 7, RING_DEGREE - 1] {
                assert_eq!(
                    val_min_abs(digit.coeff(k)),
                    balanced_digit_ref(source.coeff(k), u),
                    "row {i}, digit {u}, coefficient {k}"
                );
            }
        }
    }
}

/// And `rho_digits_at(rho, i, u)` is the same digit the flat index selects,
/// `j = i · δ + u`. This is the equality that licensed dropping the flat index
/// from `endpiece::rho_digits_short_check`: the check's result is unchanged,
/// while the `i · δ` product -- which is a *checked* `usize` multiplication in
/// the extracted model, over an `i` bounded only by `rho.len()` -- is no longer
/// formed, so the check's `_spec` needs no `n · 8 ≤ Usize.max` hypothesis.
/// `rho_digit_as_rq` keeps the flat form because its own specification
/// (`rhoDigitAsRq`) takes one.
#[test]
fn rho_digits_at_agrees_with_the_flat_index() {
    let mut rng = Lcg::new(0x8047_0000_0000_0022);
    let rho = vec![
        quotient_row(&rng.next_rq()),
        quotient_row(&rng.next_rq()),
        quotient_row(&rng.next_rq()),
    ];
    for i in 0..rho.len() {
        for u in 0..GADGET_DIGITS {
            let flat = rho_digit_as_rq(&rho, i * GADGET_DIGITS + u);
            assert!(
                rho_digits_at(&rho, i, u).equals(&flat),
                "pair ({i}, {u}) must select the digit of flat index {}",
                i * GADGET_DIGITS + u
            );
        }
    }
}

/// An extension-field point built from four base coefficients.
fn ext4(rng: &mut Lcg) -> Ext4 {
    Ext4::new(rng.next_fp(), rng.next_fp(), rng.next_fp(), rng.next_fp())
}

/// `p(α)` by **Horner's method**, descending -- a different algorithm from the
/// `∑ₖ cₖ·αᵏ` power-sum `cEvalAt` is defined as, so a mistake in either shows up
/// as a mismatch rather than being reproduced.
fn horner_ref(alpha: Ext4, p: &Rq) -> Ext4 {
    let mut acc = Ext4::ZERO;
    let mut k = RING_DEGREE;
    while k > 0 {
        k -= 1;
        acc = acc * alpha + Ext4::from_base(p.coeff(k));
    }
    acc
}

/// `αⁿ` by repeated squaring -- again a different algorithm from the repeated
/// multiplication the crate uses.
fn pow_by_squaring(alpha: Ext4, mut n: usize) -> Ext4 {
    let mut acc = Ext4::ONE;
    let mut base = alpha;
    while n > 0 {
        if n % 2 == 1 {
            acc = acc * base;
        }
        base = base * base;
        n /= 2;
    }
    acc
}

/// `cEvalAt φF α p = p.eval₂ φF α`: the `Zq[X]` polynomial evaluated at a point
/// of the extension field, against Horner.
#[test]
fn c_eval_at_evaluates_the_polynomial_at_alpha() {
    let mut rng = Lcg::new(0x8047_0000_0000_0031);
    for _ in 0..2 {
        let p = rng.next_rq();
        let alpha = ext4(&mut rng);
        assert_eq!(c_eval_at(alpha, &p), horner_ref(alpha, &p));
    }
}

/// A property no single-input comparison gives: evaluation is additive in the
/// polynomial, `(p + r)(α) = p(α) + r(α)`. `Rq::add` is coefficientwise, so this
/// is a statement about `cEvalAt` and not about the ring.
#[test]
fn c_eval_at_is_additive_in_the_polynomial() {
    let mut rng = Lcg::new(0x8047_0000_0000_0032);
    let p = rng.next_rq();
    let r = rng.next_rq();
    let alpha = ext4(&mut rng);
    assert_eq!(
        c_eval_at(alpha, &p.add(&r)),
        c_eval_at(alpha, &p) + c_eval_at(alpha, &r)
    );
}

/// `cEvalAt φF α Φ.φ` at `Φ.φ = X^d + 1` is `α^d + 1` -- the identity the naive
/// `d + 1`-term sum computes the long way round, checked against ten squarings.
/// This is the equality that makes the α-side's largest optimization sound, so
/// it is pinned before that optimization is attempted.
#[test]
fn c_eval_at_modulus_is_alpha_to_the_d_plus_one() {
    let mut rng = Lcg::new(0x8047_0000_0000_0033);
    for _ in 0..2 {
        let alpha = ext4(&mut rng);
        let expected = pow_by_squaring(alpha, RING_DEGREE) + Ext4::ONE;
        assert_eq!(c_eval_at_modulus(alpha), expected);
    }
}

/// `liftMessage` is exactly `Fin.append w.z (rhoDigitAsRq …)`. The reduced
/// shape keeps this default test below the W3 allocation wall; the function is
/// otherwise shape-generic and uses the real ring degree and digit count.
#[test]
fn lift_message_appends_all_quotient_digits_after_z() {
    let mut rng = Lcg::new(0x8047_0000_0000_0012);
    let z = rng.next_poly_vec(3);
    let a = rng.next_rq();
    let b = rng.next_rq();
    let witness = LiftedWitness::new(z.copy(), vec![quotient_row(&a), quotient_row(&b)]);
    let lifted = lift_message(&witness);
    assert_eq!(lifted.len(), 3 + 2 * GADGET_DIGITS);
    for i in 0..3 {
        assert!(lifted.get(i).equals(z.get(i)), "z entry {i}");
    }
    for j in 0..2 * GADGET_DIGITS {
        assert!(
            lifted.get(3 + j).equals(&rho_digit_as_rq(witness.rho(), j)),
            "quotient digit {j}"
        );
    }
}

/// `hachiLiftCom.com` is the ordinary Ajtai matrix-vector product over the
/// lifted message. This is REDUCED for W1: the real key has 57,384 columns and
/// schoolbook multiplication; a sub-quadratic `ring::mul` removes that wall.
#[test]
fn lift_commit_is_the_matrix_product_of_lift_message() {
    let mut rng = Lcg::new(0x8047_0000_0000_0013);
    let z = rng.next_poly_vec(2);
    let rho_source = rng.next_rq();
    let witness = LiftedWitness::new(z, vec![quotient_row(&rho_source)]);
    let width = 2 + GADGET_DIGITS;
    let d_key = rng.next_poly_matrix(1, width);
    let message = lift_message(&witness);
    let expected = d_key.mat_vec_mul(&message);
    assert!(lift_commit(&d_key, &witness).equals(&expected));
}

/// At `(bDig, bound) = (16, 15)` every balanced quotient digit is at most 8,
/// so this check is provably true for arbitrary quotient rows. The computation
/// is retained and tested even though its false branch is unreachable here.
#[test]
fn rho_digits_short_check_is_true_at_the_pinned_parameters() {
    let mut rng = Lcg::new(0x8047_0000_0000_0014);
    let rho = vec![quotient_row(&rng.next_rq()), quotient_row(&rng.next_rq())];
    assert!(rho_digits_short_check(&rho));
}

/// `liftShortCheck` can still reject through its `z` conjunct. Pin both
/// directions independently of the quotient-digit tautology.
#[test]
fn lift_short_check_accepts_and_rejects_on_the_z_norm() {
    let rho = vec![quotient_row(&Rq::zero())];
    let good = LiftedWitness::new(PolyVec::new(vec![rq_from_u64s(&[CHAIN_GAMMA])]), rho);
    assert!(lift_short_check(&good));

    let bad = LiftedWitness::new(
        PolyVec::new(vec![rq_from_u64s(&[CHAIN_GAMMA + 1])]),
        vec![quotient_row(&Rq::zero())],
    );
    assert!(!lift_short_check(&bad));
}
