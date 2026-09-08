//! `src/zerocheck.rs`: the committed table `w̃` and the range block `H₀`.
//!
//! # Sizes: REDUCED, and `m₀` has a floor
//!
//! Every row here is REDUCED, as `STAGE2_SCOPING.md` § "Scale policies" fixes
//! for target 4, and the wall is not a multiplication cost: at the pinned
//! profile `m₀ = M_ZERO = 26`, so a cube-shaped object is `2^26` `Ext4` values
//! -- **2.0 GiB** -- and `w_table_mle_eval` holds two of them at once. No
//! `ring::mul` champion touches that; the removal condition for these rows is a
//! `2^m₀`-free algorithm (the `d = 2^10` evaluation split), not a faster
//! product. The two walls must not be conflated in a note or a commit message.
//!
//! `m₀` is bounded *below* as well, which is unusual for a REDUCED row and is
//! why the reduced size is 14 rather than something smaller: the cube has to
//! cover the table, `(μ + n·δρ)·d ≤ 2^m₀`, and `d = RING_DEGREE = 1024` is
//! pinned. At the smallest witness that still has a quotient block at all
//! (`μ = 1`, `n = 1`) that is `9·1024 = 9216`, so `2^13 = 8192` is too small and
//! `m₀ = 14` is the least legal value. A row at a smaller `m₀` would not be a
//! smaller version of this computation; it would be an illegal one.
//!
//! Both dimensions of every two-dimensional case are named at file scope below,
//! beside the constant each is or is not a reduction of -- the arrangement
//! `benches/ringswitch.rs` § "Sizes" argues for, and whose absence inverted
//! `ringswitch/lift_message`.
//!
//! # Which rows can carry a verdict
//!
//! `zerocheck/range_product` reads ~1.2 µs, inside the 100 ns – 2 µs band the
//! certified sweep found false verdicts in (NOTES.md § "The certified null-slot
//! sweep"), so **it carries no candidate verdict on its own**. That is
//! acceptable here rather than a gap, because the operation's real consumer is
//! `h_zero`, which applies it `2^m₀` times and is 40 ms -- the vector-shaped
//! reading of the same arithmetic, in the same sense that `vec_in_sb` is the
//! readable row and `in_sb` is not.
//!
//! # Which rows are a real A/B (the §4 audit's `nm` check)
//!
//! Run on this binary built `--features candidate` against the null slot, and
//! note the symbol this file's cases actually expose: the per-variant case
//! functions themselves (`zerocheck::<variant>::<case>`), not the
//! `Bencher::iter` closure the older headers grep for -- the case bodies here
//! are large enough that the closure inlines into them rather than the reverse.
//!
//! | case | timed copies |
//! |---|---|
//! | `range_product` | three -- `now`, `candidate`, `genesis` |
//! | `w_table_rho_row` | three |
//! | `w_table_mle_eval` | three |
//! | `_control/zerocheck` | **merged** (one) |
//! | `w_table_z_row` | **merged** |
//! | `c_w_table_mle` | **merged** |
//! | `h_zero` | **merged** |
//! | `h_zero_is_zero` | **merged**, and fully inlined -- no symbol at all |
//!
//! A merged row has no layout bias to measure, so a null-slot sweep of it
//! reports a lower bound and its `_control` -- merged too, as every control is
//! -- cannot correct for a term it never saw (NOTES.md § "The §4 audit of
//! target 2's rows", finding 1). It does not make a merged row's candidate
//! verdict wrong: a real candidate is not byte-identical, so it does not merge.
//! Re-run after any edit here:
//!
//! ```text
//! nm -C target/release/deps/zerocheck-* | grep 'zerocheck::\(now\|genesis\|candidate\)::'
//! ```
//!
//! See `benches/support/mod.rs` for the corpus discipline, the digest oracle and
//! what the `_control` case is.

mod support;

use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};

// ---------------------------------------------------------------------------
// Sizes
// ---------------------------------------------------------------------------

/// The cube width every table-shaped row runs at: **REDUCED** from
/// `params::M_ZERO = 26`, and the least legal value at the witness below (see
/// the module header's floor argument).
const M_ZERO_REDUCED: usize = 14;

/// The message-block width of the benched witness: **REDUCED** from
/// `params::RLIN_COLS = 57 344`. One `Rq`, the smallest witness with a message
/// block at all.
const Z_COLS: usize = 1;

/// The quotient-row count of the benched witness: **REDUCED** from
/// `params::RLIN_ROWS = 5`. One row, i.e. `GADGET_DIGITS = 8` digit rows in the
/// table -- enough that `w_table`'s digit branch is exercised at every digit
/// index, which is what the second `w_table` row below measures.
const RHO_ROWS: usize = 1;

/// One body per case, instantiated once per variant crate.
macro_rules! define_cases {
    ($modname:ident, $hachi:path) => {
        mod $modname {
            // `support::run`'s digest argument is `Fn(&R) -> u64`, so a digest of
            // a `Copy` scalar has to take it by reference.
            #![allow(clippy::trivially_copy_pass_by_ref)]

            use std::hint::black_box;

            use cpoly::{Ext4, Fp, MultilinearEvals};

            use $hachi as hc;

            use crate::support::{self, Mode};
            use crate::{RHO_ROWS, Z_COLS};

            type Rq = hc::ring::Rq;
            type PolyVec = hc::linalg::PolyVec;
            type QuotientRow = hc::ringswitch::QuotientRow;
            type LiftedWitness = hc::ringswitch::LiftedWitness;

            // -- corpus -----------------------------------------------------

            /// The benched witness: `Z_COLS` message polynomials and `RHO_ROWS`
            /// quotient rows, both from the shared corpus, so every variant
            /// builds bit-identical inputs.
            fn witness(seed: u64) -> LiftedWitness {
                let degree = hc::params::RING_DEGREE;
                let mut z = Vec::with_capacity(Z_COLS);
                let mut i = 0usize;
                while i < Z_COLS {
                    z.push(Rq::from_coeffs(&support::corpus(
                        seed.wrapping_add(i as u64),
                        degree,
                    )));
                    i += 1;
                }
                let mut rho = Vec::with_capacity(RHO_ROWS);
                let mut r = 0usize;
                while r < RHO_ROWS {
                    rho.push(QuotientRow::new(&support::corpus(
                        seed.wrapping_add(0x1000 + r as u64),
                        degree,
                    )));
                    r += 1;
                }
                LiftedWitness::new(PolyVec::new(z), rho)
            }

            /// An `m₀`-coordinate evaluation point, the verifier's challenge.
            fn point(seed: u64, m0: usize) -> Vec<Ext4> {
                let c = support::corpus(seed, 4 * m0);
                let mut out = Vec::with_capacity(m0);
                let mut j = 0usize;
                while j < m0 {
                    out.push(Ext4::new(c[4 * j], c[4 * j + 1], c[4 * j + 2], c[4 * j + 3]));
                    j += 1;
                }
                out
            }

            // -- digests (outside every timed region) -----------------------

            fn d_bool(b: &bool) -> u64 {
                u64::from(*b)
            }

            fn d_ext4(v: &Ext4) -> u64 {
                let mut acc = support::mix(0, v.c0.to_u64());
                acc = support::mix(acc, v.c1.to_u64());
                acc = support::mix(acc, v.c2.to_u64());
                support::mix(acc, v.c3.to_u64())
            }

            fn d_evals(t: &MultilinearEvals) -> u64 {
                let vs = t.values();
                let mut acc = support::mix_len(0, vs.len());
                let mut i = 0usize;
                while i < vs.len() {
                    acc = support::mix(acc, d_ext4(&vs[i]));
                    i += 1;
                }
                acc
            }

            fn d_rq(a: &Rq) -> u64 {
                let n = a.len();
                let mut acc = support::mix_len(0, n);
                let mut k = 0usize;
                while k < n {
                    acc = support::mix(acc, a.coeff(k).to_u64());
                    k += 1;
                }
                acc
            }

            fn d_polyvec(v: &PolyVec) -> u64 {
                let k = v.len();
                let mut acc = support::mix_len(0, k);
                let mut i = 0usize;
                while i < k {
                    acc = support::mix(acc, d_rq(v.get(i)));
                    i += 1;
                }
                acc
            }

            // -- the semantics this binary pins itself ----------------------

            /// Facts the digest oracle cannot supply, pinned in every variant
            /// before any timing is taken (the `benches/quadeval.rs`
            /// precedent). `case!`'s cross-variant equality proves that `now`
            /// and `genesis` *agree*; these prove they are computing the thing
            /// the specification names, in both directions where a direction
            /// exists.
            pub fn check() {
                // `rangeProduct_eq_zero_iff` (`Constraints.lean:102`) at the two
                // values the whole link turns on: `b − 1 = CHAIN_GAMMA = 15` is
                // a root, and `b = 16` is not. Without the second assertion a
                // candidate that widened the range would read as correct.
                let b = hc::params::GADGET_BASE;
                let inside = Ext4::from_base(Fp::new(b - 1));
                let outside = Ext4::from_base(Fp::new(b));
                assert!(
                    hc::zerocheck::range_product(inside).is_zero(),
                    "range_product must vanish at b - 1 = CHAIN_GAMMA"
                );
                assert!(
                    !hc::zerocheck::range_product(outside).is_zero(),
                    "range_product must NOT vanish at b: the range check would be vacuous"
                );

                // `wTable_zRow` (`:378`): the message block is read
                // coefficientwise. Pins the outer index split.
                let w = witness(0x5A17_1000);
                let ell = 3usize;
                assert_eq!(
                    hc::zerocheck::w_table(&w, ell),
                    Ext4::from_base(w.z().get(0).coeff(ell)),
                    "w_table must read z coefficientwise on the message block"
                );

                // The `else 0` branch: above the committed rows the cube is
                // padding, and padding is zero.
                let above = hc::params::RING_DEGREE * (Z_COLS + RHO_ROWS * hc::params::GADGET_DIGITS);
                assert!(
                    hc::zerocheck::w_table(&w, above).is_zero(),
                    "w_table must be zero above the committed rows"
                );

                // `hZero_eq_zero_iff` (`:219`), both directions, at a table
                // small enough to scan here: all-legal digits accept, and a
                // single coefficient at `+b` rejects.
                let mut coeffs = Vec::with_capacity(hc::params::RING_DEGREE);
                let mut k = 0usize;
                while k < hc::params::RING_DEGREE {
                    coeffs.push(Fp::new((k as u64) % b));
                    k += 1;
                }
                let good = LiftedWitness::new(
                    PolyVec::new(vec![Rq::from_coeffs(&coeffs)]),
                    Vec::new(),
                );
                assert!(
                    hc::zerocheck::h_zero_is_zero(&good, 10),
                    "H0 must vanish on a witness whose every coefficient is a legal digit"
                );
                coeffs[hc::params::RING_DEGREE - 1] = Fp::new(b);
                let bad =
                    LiftedWitness::new(PolyVec::new(vec![Rq::from_coeffs(&coeffs)]), Vec::new());
                assert!(
                    !hc::zerocheck::h_zero_is_zero(&bad, 10),
                    "H0 must not vanish when a coefficient is out of range -- including the last"
                );
            }

            // -- cases ------------------------------------------------------

            /// `rangeProduct` at one point: `b − 1 = 15` quadratic factors,
            /// 31 `Ext4` multiplies. Registered at `GADGET_BASE`, the base whose
            /// range it vanishes on -- **real**, not reduced; it is the only
            /// dimension the operation has.
            pub fn range_product(m: Mode<'_, '_>, base: u64) -> u64 {
                assert_eq!(base, hc::params::GADGET_BASE, "range_product size is the digit base");
                let c = support::corpus(0x5A17_2001, 4);
                let v = Ext4::new(c[0], c[1], c[2], c[3]);
                support::run(m, || hc::zerocheck::range_product(black_box(v)), d_ext4)
            }

            /// One `w_table` entry on the **message** block -- the cheap branch:
            /// two `Usize` divisions and one coefficient read.
            pub fn w_table_z_row(m: Mode<'_, '_>, ell: usize) -> u64 {
                let w = witness(0x5A17_2002);
                support::run(
                    m,
                    || hc::zerocheck::w_table(black_box(&w), black_box(ell)),
                    d_ext4,
                )
            }

            /// One `w_table` entry on the **quotient-digit** block -- the branch
            /// that rebuilds a whole `Rq` of `d` balanced digits to read one
            /// coefficient out of it, which is the specification's own shape and
            /// the target's largest single redundancy.
            ///
            /// Taken at the deepest digit index of the block (`u =
            /// GADGET_DIGITS - 1`) and the last coefficient, for the reason
            /// `benches/ringswitch.rs` § "Why the digit index is..." gives: every
            /// real consumer walks the whole block, so the worst entry of a loop
            /// run to completion is the representative one, not a corner.
            pub fn w_table_rho_row(m: Mode<'_, '_>, rows: usize) -> u64 {
                assert_eq!(rows, RHO_ROWS, "w_table_rho_row size is the quotient-row count");
                let w = witness(0x5A17_2003);
                let degree = hc::params::RING_DEGREE;
                let last_digit = Z_COLS + rows * hc::params::GADGET_DIGITS - 1;
                let idx = degree * last_digit + (degree - 1);
                support::run(
                    m,
                    || hc::zerocheck::w_table(black_box(&w), black_box(idx)),
                    d_ext4,
                )
            }

            /// `cWTableMle`: the whole `2^m₀` table.
            pub fn c_w_table_mle(m: Mode<'_, '_>, m0: usize) -> u64 {
                let w = witness(0x5A17_2004);
                support::run(
                    m,
                    || hc::zerocheck::c_w_table_mle(black_box(&w), black_box(m0)),
                    d_evals,
                )
            }

            /// `wTableMleEval`: the table, plus the Lagrange basis at the
            /// challenge point and the dot product against it. Two `2^m₀`
            /// tables resident at once, which is the memory wall of the target.
            pub fn w_table_mle_eval(m: Mode<'_, '_>, m0: usize) -> u64 {
                let w = witness(0x5A17_2005);
                let a = point(0x5A17_2006, m0);
                support::run(
                    m,
                    || hc::zerocheck::w_table_mle_eval(black_box(&w), black_box(m0), black_box(&a)),
                    d_ext4,
                )
            }

            /// `hZero`: the range factor applied to every one of the `2^m₀`
            /// table entries. The dominant term of the target as specified.
            pub fn h_zero(m: Mode<'_, '_>, m0: usize) -> u64 {
                let w = witness(0x5A17_2007);
                support::run(
                    m,
                    || hc::zerocheck::h_zero(black_box(&w), black_box(m0)),
                    d_evals,
                )
            }

            /// `hZero = 0`, the verifier's actual decision, in the pointwise
            /// form of `hZero_eq_zero_iff`. Digests to a `bool`, so this row's
            /// cross-variant oracle is one bit -- which is why [`check()`] pins
            /// both directions of it above.
            pub fn h_zero_is_zero(m: Mode<'_, '_>, m0: usize) -> u64 {
                let w = witness(0x5A17_2008);
                support::run(
                    m,
                    || hc::zerocheck::h_zero_is_zero(black_box(&w), black_box(m0)),
                    d_bool,
                )
            }

            // -- the A/B fairness control -----------------------------------

            /// The harness's A/B fairness control. Every variant runs its own
            /// compiled copy of the *same source*, so any difference the report
            /// shows for it is measurement bias and not code. Deliberately the
            /// same body as every other binary's control, so the eight controls
            /// are comparable with each other.
            pub fn control(m: Mode<'_, '_>, n: usize) -> u64 {
                support::run(m, || PolyVec::zeros(black_box(n)), d_polyvec)
            }
        }
    };
}

define_cases!(now, hachi);
define_cases!(genesis, hachi_genesis);
#[cfg(feature = "candidate")]
define_cases!(candidate, hachi_candidate);

fn zerocheck_benches(c: &mut Criterion) {
    now::check();
    genesis::check();
    #[cfg(feature = "candidate")]
    candidate::check();

    // The run's sanity check: identical source in every variant, so anything it
    // reads is the harness disagreeing with itself.
    bench_case!(c, "_control/zerocheck", control, [support::CONTROL_N]);

    // @covers zerocheck::range_product
    bench_case!(c, "zerocheck/range_product", range_product, [hachi::params::GADGET_BASE]);
    // Two rows for one item, because `w_table`'s two branches differ by a factor
    // of `d`: the message branch is a coefficient read, the digit branch builds
    // `RING_DEGREE` balanced digits. A single row would report whichever branch
    // it happened to index and call it the entry cost.
    // @covers zerocheck::w_table
    bench_case!(c, "zerocheck/w_table_z_row", w_table_z_row, [3]);
    // @covers zerocheck::w_table
    bench_case!(c, "zerocheck/w_table_rho_row", w_table_rho_row, [RHO_ROWS]);
    // @covers zerocheck::c_w_table_mle
    bench_case!(c, "zerocheck/c_w_table_mle", c_w_table_mle, [M_ZERO_REDUCED]);
    // @covers zerocheck::w_table_mle_eval
    bench_case!(c, "zerocheck/w_table_mle_eval", w_table_mle_eval, [M_ZERO_REDUCED]);
    // @covers zerocheck::h_zero
    bench_case!(c, "zerocheck/h_zero", h_zero, [M_ZERO_REDUCED]);
    // @covers zerocheck::h_zero_is_zero
    bench_case!(c, "zerocheck/h_zero_is_zero", h_zero_is_zero, [M_ZERO_REDUCED]);
}

criterion_group! {
    // A per-binary override of `support::criterion_config`, for the arithmetic
    // reason `benches/endpiece.rs` gives: criterion samples linearly by default,
    // so 100 samples cost `100·101/2 = 5050` executions. At the ~40 ms `h_zero`
    // row that is over three minutes per variant, which `SamplingMode::Auto`
    // refuses -- it flips to *flat* sampling, `sample_size` samples of
    // `ceil(window / sample_size / met)` iterations each. At 50 samples over a
    // 10 s window a 40 ms row is 5 iterations per sample against 2 at the
    // default, and `_robust` takes the three fastest samples, so two-iteration
    // samples would amount to picking the three luckiest executions in the run.
    // The override buys averaging, not just wall clock.
    name = zerocheck_group;
    config = support::criterion_config()
        .sample_size(50)
        .measurement_time(Duration::from_secs(10));
    targets = zerocheck_benches
}
criterion_main!(zerocheck_group);
