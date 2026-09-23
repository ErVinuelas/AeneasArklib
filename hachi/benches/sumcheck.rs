//! `src/sumcheck.rs`: the round message in folded-table value form.
//!
//! # Read a `vs genesis` figure here differently from every other binary
//!
//! `benches/genesis` holds the **dense** form for this module, by decision
//! (NOTES.md § "Decision: target 5's genesis holds the dense form"). Everywhere
//! else in this harness, `vs genesis` is distance from the specification's
//! trivial shape; **here it is distance from the dense form**, because the
//! trivial shape does not run at any width that resembles the operation. A
//! ledger row citing a number from this file has to say so.
//!
//! What is still measurable against this baseline, and deliberately left for
//! `perf-loop`: `range_product` in its literal 31-multiply form against the
//! `v² - j²` form's 16 (a 2× cut on the 94%-dominant term), the closed-form
//! `eq̃`, the tensor split of `Ã`, and hoisting the triple `computeG`.
//!
//! # Sizes
//!
//! REDUCED on the cube, real on the node count. The round-0 remaining cube is
//! `2^{m₀-1} = 2^25` points at the pinned `M_ZERO = 26`; these rows run at
//! `2^10`, which keeps the *shape* — a fold pairing `2y`/`2y+1`, then `2b+1`
//! nodes, then interpolation — while fitting a criterion iteration. The node
//! count is **not** reduced: it is `ROUND_NODES = 2b + 1 = 33`, and reducing it
//! would change which polynomial the interpolant is.
//!
//! One row runs the *whole* honest prover: `sumcheck/honest_round_messages` at
//! `m₀ = 11`, so that its round 0 has exactly the `2^10` shape of the per-round
//! rows and its table has `2^11` real witness coefficients. It is the row a
//! change confined to one round is measured on.
//!
//! The verifier's `final_check` runs at the same `m₀ = 11`, where the tensor
//! split of `Ã` first has both of its factors; its bool result makes `check()`
//! the oracle (see the case). `sumcheck/alpha_public_mle_eval` runs at the
//! **real** `m₀ = 26` on a REDUCED statement: the split is what makes the
//! pin's cube affordable, and the row is there to say what it costs.

mod support;

use std::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};

// ---------------------------------------------------------------------------
// Sizes
// ---------------------------------------------------------------------------

/// The remaining-cube size the round rows run at: **REDUCED** from `2^25`.
/// `1024` folded pairs, so the `w̃` table is `2048` `Ext4` and the `eq̃`-suffix
/// table `1024`.
const HALF: usize = 1024;

/// The suffix-kernel width the `eq_suffix_table` row runs at: **REDUCED** from
/// the round-0 real `m₀ - 1 = 25`. Chosen as `HALF.trailing_zeros()` so the
/// table it builds is exactly the `eq̃` table the round rows consume.
const SUFFIX_VARS: usize = 10;

/// The cube the `round_poly_zero_base` row runs at: **REDUCED** from the
/// round-0 real `2^25` pairs to `2^20`, on a table of balanced digits. Large
/// because card T46a's win is a per-pair cost against a fixed cost of 256
/// types: at [`HALF`] the fixed cost would be a quarter of the pairs and the
/// row would understate the pin several-fold. The per-pair path at this size
/// is ~0.7 s per iteration, genesis ~1.4 s.
const R0_HALF: usize = 1 << 20;

/// The cube the `alpha_public_table` row runs at: **REDUCED** from the pinned
/// `M_ZERO = 26` to `7`, i.e. `128` entries, all in table row `0` (the matrix
/// branch of `m_alpha_tilde`). The size is set by the **genesis** variant, not
/// by the champion: the frozen `alpha_public_evals` reaches the frozen
/// quadratic `c_eval_at` (`~7 ms` per call, `AP_ROWS` calls per entry), and the
/// harness re-measures genesis in every run, so `128 · 2 · 7 ms ≈ 1.9 s` per
/// genesis iteration is the budget. The abandoned `2^12` trial, at the real
/// `RLIN_ROWS = 5` and two columns, measured 0.47 s per champion iteration and
/// its genesis variant -- projected at ~90 s per iteration, never completed --
/// had to be killed. What the row exists to measure is the per-entry
/// recomputation the brief's items 3 and 4 hoist (`α^ℓ` by `alpha_tilde`,
/// `M̃_α(i, u)` by `m_alpha_tilde`), and both happen on every entry here. Two
/// proportions to read a verdict with: the two `c_eval_at` calls per entry are
/// ~98% of the champion's multiplications and `alpha_tilde` ~1.5%, so item 4 is
/// what this row can see and item 3 alone would sit under the 5% floor; and
/// because every entry has `u = idx / d = 0`, the per-`u` repeat factor here is
/// the cube size `128` where the pin's is `d = 1024`, so an item-4 hoist reads
/// **8× smaller** here than at `m₀ = 26` -- conservative, and a ledger row
/// citing this figure should say so. The digit branch and the zero padding are
/// not reached at one row; the digit branch's per-entry cost is
/// `zerocheck/m_alpha_tilde_digit`'s row.
const AP_M0: usize = 7;

/// The `R^lin` row count the `alpha_public_table` row's statement carries:
/// **REDUCED** from `RLIN_ROWS = 5` to `2`, for the genesis budget above (the
/// per-entry cost is linear in it); `benches/zerocheck.rs`'s
/// `alpha_public_evals` row makes the same reduction.
const AP_ROWS: usize = 2;

/// The `R^lin` column count the statement carries: **REDUCED** from
/// `μ₀ = 57 344` to `1` (the real `M` is `5 × 57 344` `Rq`, 2.2 GiB). One
/// column is all a one-row cube reads.
const AP_COLS: usize = 1;

/// The cube the `honest_round_messages` row runs at: **REDUCED** from the
/// pinned `M_ZERO = 26` to `11`, so that round 0 folds `2^10 = HALF` pairs --
/// the same shape as the per-round rows above -- and the item runs its `11`
/// rounds over a `2048`-entry `w̃` table. The row exists to measure the
/// *whole* honest prover, which is the item a round-0 rewrite changes: the
/// per-round rows cannot see a change that only touches the first round. Its
/// genesis budget is set by the frozen `alpha_public_table` inside it, not by
/// the cube: every table entry has `u = idx / d` with `d = RING_DEGREE = 1024`,
/// so the `2048` entries split into `u = 0` (the matrix branch, one frozen
/// quadratic `c_eval_at` over `d` terms) and `u = 1` (the first digit branch,
/// one frozen quadratic `c_eval_at_modulus` over `d + 1` terms), about `7 ms`
/// each -- **measured 14.8 s per genesis iteration** (run
/// `20260915T1008+0200-7cd34c7b`), about 13 minutes for the row's three
/// variants. `m₀ = 10` would halve that (all `u = 0`) but lose the `HALF`
/// shape; `m₀ = 12` would double it. An earlier version of this comment
/// projected `4 s` from `d = 64`, which is not this crate's ring degree.
const HRM_M0: usize = 11;

/// The witness the `honest_round_messages` row commits: **REDUCED** from
/// `μ₀ = 57 344` message polynomials to `24`, plus [`HRM_RHO_ROWS`] quotient
/// row. With `d = RING_DEGREE = 1024` the `2^11` cube covers only table rows
/// `u = 0, 1` -- the first two message polynomials -- so every entry is a real
/// witness coefficient and none is zero padding, but `z[2..]` and the quotient
/// row are never read at this cube (the adversarial review of 2026-09-15
/// measured the table build at ~0.03 ms of the row either way). The witness is
/// kept at a shape that would also feed the digit branch at a wider cube; it is
/// not what the row measures.
const HRM_Z_COLS: usize = 24;

/// The quotient-row count of that witness: `1`. Not reached at `m₀ = 11` (the
/// digit rows start at `u = μ = 24`); see [`HRM_Z_COLS`].
const HRM_RHO_ROWS: usize = 1;

/// The cube the `final_check` row runs at: **REDUCED** from `M_ZERO = 26` to
/// `11`, the smallest cube at which the tensor split of `Ã` has two
/// non-trivial factors (`d = RING_DEGREE = 2^10` low coordinates, one high).
/// Below `d` the whole cube is the low factor and the high table is one entry,
/// which is a different shape from the pin's. The genesis budget is the same
/// `2 048` frozen quadratic evaluations as [`HRM_M0`]'s, ~15 s per iteration.
const FC_M0: usize = 11;

/// One body per case, instantiated once per variant crate.
macro_rules! define_cases {
    ($modname:ident, $hachi:path) => {
        mod $modname {
            #![allow(clippy::trivially_copy_pass_by_ref)]

            use std::hint::black_box;

            use cpoly::{Ext4, Fp, UnivariatePoly};

            use $hachi as hc;

            use crate::support::{self, Mode};

            type PolyVec = hc::linalg::PolyVec;
            type Rq = hc::ring::Rq;
            type RlinStatement = hc::ringswitch::RlinStatement;
            type RoundStatement = hc::sumcheck::RoundStatement;
            type RoundMsg = hc::sumcheck::RoundMsg;
            type QuotientRow = hc::ringswitch::QuotientRow;
            type LiftedWitness = hc::ringswitch::LiftedWitness;

            // -- corpus -----------------------------------------------------

            fn ext_table(seed: u64, n: usize) -> Vec<Ext4> {
                let c = support::corpus(seed, 4 * n);
                let mut out = Vec::with_capacity(n);
                let mut i = 0usize;
                while i < n {
                    out.push(Ext4::new(c[4 * i], c[4 * i + 1], c[4 * i + 2], c[4 * i + 3]));
                    i += 1;
                }
                out
            }

            /// A round statement whose *carried* halves are minimal on purpose.
            /// `honest_compute_g` reads `τ₀` and the challenges; `round_check`
            /// reads the two targets; neither touches `M` or `yvec`, so the
            /// `R^lin` statement is `1 × 1` rather than the `2.2 GiB` real one
            /// (`benches/zerocheck.rs` § the statement builder). Sizing a
            /// carried field up would measure the corpus, not the item.
            fn nested_stmt(seed: u64, m0: usize) -> hc::sumcheck::NestedZeroCheckStmt {
                let degree = hc::params::RING_DEGREE;
                let one = |k: u64| Rq::from_coeffs(&support::corpus(seed.wrapping_add(k), degree));
                let rlin = RlinStatement::new(
                    hc::linalg::PolyMatrix::new(vec![PolyVec::new(vec![one(1)])]),
                    PolyVec::new(vec![one(2)]),
                    hc::params::CHAIN_GAMMA,
                );
                hc::sumcheck::NestedZeroCheckStmt::new(
                    rlin,
                    PolyVec::new(vec![one(3)]),
                    ext_table(seed.wrapping_add(4), 1)[0],
                    ext_table(seed.wrapping_add(5), m0),
                    ext_table(seed.wrapping_add(6), hc::params::M_ONE),
                )
            }

            fn round_stmt(seed: u64, m0: usize, drawn: usize) -> RoundStatement {
                let zc = nested_stmt(seed, m0);
                let t = ext_table(seed.wrapping_add(7), 2);
                RoundStatement::new(zc, ext_table(seed.wrapping_add(8), drawn), t[0], t[1])
            }

            /// A round-`m₀` statement whose two targets are the **honest** final
            /// claims for the drawn `y′`, moved by `(dz, da)`: at `(0, 0)` the
            /// statement is one `final_check` accepts, and any other offset is
            /// one it must reject. The linear target is computed the way the
            /// crate did before candidate J -- the tabulated `Ã` and cpoly's
            /// Lagrange `eval` -- so for the `candidate` variant this is an
            /// independent computation of the value its tensor-split
            /// evaluation must reproduce. Built in every variant's own crate,
            /// outside every timed region (the genesis variant pays its frozen
            /// quadratic `c_eval_at` here once, ~15 s at `m₀ = 11`).
            fn final_stmt(seed: u64, m0: usize, dz: Ext4, da: Ext4) -> (RoundStatement, Ext4) {
                let zc = nested_stmt(seed, m0);
                let challenges = ext_table(seed.wrapping_add(8), m0);
                let y_prime = ext_table(seed.wrapping_add(9), 1)[0];
                let eq_all = cpoly::multilinear::eq_tilde(zc.tau0(), &challenges);
                let table = hc::sumcheck::alpha_public_table(zc.rlin(), zc.alpha(), zc.tau1(), m0);
                let a_mle = cpoly::MultilinearEvals::from_values(table).eval(&challenges);
                let t0 = eq_all * hc::zerocheck::range_product(y_prime) + dz;
                let ta = y_prime * a_mle + da;
                (RoundStatement::new(zc, challenges, t0, ta), y_prime)
            }

            /// A round message, built from coefficients rather than from
            /// `honest_compute_g`, so a `round_check`/`round_out` row measures
            /// the check and not the prover.
            fn round_msg(seed: u64) -> RoundMsg {
                RoundMsg::new(
                    UnivariatePoly::from_coeffs(ext_table(seed, hc::params::ROUND_NODES)),
                    UnivariatePoly::from_coeffs(ext_table(
                        seed.wrapping_add(1),
                        hc::params::ROUND_NODES_ALPHA,
                    )),
                )
            }

            /// The committed witness of the `honest_round_messages` row:
            /// [`crate::HRM_Z_COLS`] message polynomials and
            /// [`crate::HRM_RHO_ROWS`] quotient rows from the shared corpus,
            /// one tag per polynomial (`benches/zerocheck.rs`'s `witness`
            /// builds the same shape at its own sizes).
            fn witness(seed: u64, z_cols: usize, rho_rows: usize) -> LiftedWitness {
                let degree = hc::params::RING_DEGREE;
                let mut z = Vec::with_capacity(z_cols);
                let mut i = 0usize;
                while i < z_cols {
                    z.push(Rq::from_coeffs(&support::corpus(
                        seed.wrapping_add(i as u64),
                        degree,
                    )));
                    i += 1;
                }
                let mut rho = Vec::with_capacity(rho_rows);
                let mut r = 0usize;
                while r < rho_rows {
                    rho.push(QuotientRow::new(&support::corpus(
                        seed.wrapping_add(0x1000 + r as u64),
                        degree,
                    )));
                    r += 1;
                }
                LiftedWitness::new(PolyVec::new(z), rho)
            }

            // -- digests (outside every timed region) -----------------------

            fn d_ext4(v: &Ext4) -> u64 {
                let mut acc = support::mix(0, v.c0.to_u64());
                acc = support::mix(acc, v.c1.to_u64());
                acc = support::mix(acc, v.c2.to_u64());
                support::mix(acc, v.c3.to_u64())
            }

            fn d_vec(v: &Vec<Ext4>) -> u64 {
                let mut acc = support::mix_len(0, v.len());
                let mut i = 0usize;
                while i < v.len() {
                    acc = support::mix(acc, d_ext4(&v[i]));
                    i += 1;
                }
                acc
            }

            fn d_poly(p: &UnivariatePoly) -> u64 {
                let c = p.coeffs();
                let mut acc = support::mix_len(0, c.len());
                let mut i = 0usize;
                while i < c.len() {
                    acc = support::mix(acc, d_ext4(&c[i]));
                    i += 1;
                }
                acc
            }

            fn d_round_stmt(st: &RoundStatement) -> u64 {
                let mut acc = support::mix(0, d_vec(st.challenges()));
                acc = support::mix(acc, d_ext4(&st.target_zero()));
                support::mix(acc, d_ext4(&st.target_alpha()))
            }

            fn d_bool(b: &bool) -> u64 {
                support::mix(0, u64::from(*b))
            }

            fn d_polyvec(v: &PolyVec) -> u64 {
                let k = v.len();
                let mut acc = support::mix_len(0, k);
                let mut i = 0usize;
                while i < k {
                    let r = v.get(i);
                    let n = r.len();
                    let mut inner = support::mix_len(0, n);
                    let mut j = 0usize;
                    while j < n {
                        inner = support::mix(inner, r.coeff(j).to_u64());
                        j += 1;
                    }
                    acc = support::mix(acc, inner);
                    i += 1;
                }
                acc
            }

            // -- the semantics this binary pins itself ----------------------

            /// Facts the digest oracle cannot supply. The load-bearing one is
            /// the interpolation property: a round message is *represented* by
            /// its node values, so if the interpolant did not reproduce them
            /// the whole representation would be unsound while every timing
            /// stayed plausible.
            pub fn check() {
                let values = ext_table(0x5A17_7000, hc::params::ROUND_NODES);
                let weights = hc::sumcheck::round_node_weights();
                let p = hc::sumcheck::interpolate(&values, &weights);
                let mut i = 0usize;
                while i < values.len() {
                    assert_eq!(
                        p.eval(hc::sumcheck::round_node(i)),
                        values[i],
                        "the interpolant must reproduce node {i}"
                    );
                    i += 1;
                }
                // And the nodes are the specification's: 0 and 1 first, because
                // those are the two `roundCheck` evaluates.
                assert_eq!(hc::sumcheck::round_node(0), Ext4::ZERO);
                assert_eq!(hc::sumcheck::round_node(1), Ext4::from_base(Fp::new(1)));
                assert_eq!(hc::params::ROUND_NODES as u64, 2 * hc::params::GADGET_BASE + 1);
                // `final_check` returns a `bool`, so its digest cannot tell a
                // correct body from `|_| true`; this is the oracle instead, in
                // every variant's own crate: the honest statement is accepted
                // and each conjunct moved on its own is rejected.
                let bound = hc::params::CHAIN_GAMMA;
                let (honest, y) = final_stmt(0x5A17_7001, crate::FC_M0, Ext4::ZERO, Ext4::ZERO);
                assert!(hc::sumcheck::final_check(&honest, y, bound), "the honest final claim must pass");
                let (moved_z, y1) = final_stmt(0x5A17_7001, crate::FC_M0, Ext4::ONE, Ext4::ZERO);
                assert!(!hc::sumcheck::final_check(&moved_z, y1, bound), "a moved range target must fail");
                let (moved_a, y2) = final_stmt(0x5A17_7001, crate::FC_M0, Ext4::ZERO, Ext4::ONE);
                assert!(!hc::sumcheck::final_check(&moved_a, y2, bound), "a moved linear target must fail");
                assert!(!hc::sumcheck::final_check(&honest, y, bound + 1), "a bound above rlin.bound must fail");
            }

            // -- cases ------------------------------------------------------

            /// Lagrange interpolation at the **real** node count: `33` basis
            /// products of `32` factors each.
            pub fn interpolate(m: Mode<'_, '_>, nodes: usize) -> u64 {
                assert_eq!(nodes, hc::params::ROUND_NODES, "interpolate runs at the real node count");
                let values = ext_table(0x5A17_7001, nodes);
                let weights = hc::sumcheck::round_node_weights();
                support::run(
                    m,
                    || hc::sumcheck::interpolate(black_box(&values), black_box(&weights)),
                    d_poly,
                )
            }

            /// One node of the range summand: the fold plus `HALF`
            /// `range_product`s. The inner loop the whole target is dominated
            /// by.
            pub fn round_value_zero(m: Mode<'_, '_>, half: usize) -> u64 {
                let w = ext_table(0x5A17_7002, 2 * half);
                let eq = ext_table(0x5A17_7003, half);
                let node = hc::sumcheck::round_node(7);
                support::run(
                    m,
                    || {
                        hc::sumcheck::round_value_zero(
                            black_box(&w),
                            black_box(&eq),
                            black_box(node),
                        )
                    },
                    d_ext4,
                )
            }

            /// All `2b + 1` nodes of it: the per-round prover cost, REDUCED on
            /// the cube only.
            pub fn round_values_zero(m: Mode<'_, '_>, half: usize) -> u64 {
                let w = ext_table(0x5A17_7004, 2 * half);
                let eq = ext_table(0x5A17_7005, half);
                support::run(
                    m,
                    || hc::sumcheck::round_values_zero(black_box(&w), black_box(&eq)),
                    d_vec,
                )
            }

            /// The whole round message: node values then interpolation, which
            /// is what a round of the prover actually sends.
            pub fn round_poly_zero(m: Mode<'_, '_>, half: usize) -> u64 {
                let w = ext_table(0x5A17_7006, 2 * half);
                let eq = ext_table(0x5A17_7007, half);
                support::run(
                    m,
                    || hc::sumcheck::round_poly_zero(black_box(&w), black_box(&eq)),
                    d_poly,
                )
            }

            /// A round-0 table of balanced digits: every entry in the box
            /// `S_b = [-8, 7]` the honest lifted witness lives in
            /// (`quadeval.rs`: `S_b` "is tight on the honest balanced
            /// digits"). The random-`Fp` corpus of every other row is never in
            /// the box, so it cannot see card T46a.
            fn digit_table(seed: u64, n: usize) -> Vec<Fp> {
                let c = support::corpus(seed, n);
                let eight = Fp::new(8);
                let mut out = Vec::with_capacity(n);
                let mut i = 0usize;
                while i < n {
                    out.push(Fp::new(c[i].to_u64() % 16) - eight);
                    i += 1;
                }
                out
            }

            /// The round-0 zero-side message on an honest-shaped table:
            /// `round_poly_zero_base` over `half` pairs of balanced digits.
            pub fn round_poly_zero_base(m: Mode<'_, '_>, half: usize) -> u64 {
                let w = digit_table(0x5A17_7046, 2 * half);
                let eq = ext_table(0x5A17_7047, half);
                support::run(
                    m,
                    || hc::sumcheck::round_poly_zero_base(black_box(&w), black_box(&eq)),
                    d_poly,
                )
            }

            /// One node of the **linear** summand: two folds and one product
            /// per remaining cube point, against the range side's fold plus
            /// `range_product`. The pair is what makes the `2b + 1` versus `3`
            /// node counts legible.
            pub fn round_value_alpha(m: Mode<'_, '_>, half: usize) -> u64 {
                let w = ext_table(0x5A17_7010, 2 * half);
                let a = ext_table(0x5A17_7011, 2 * half);
                let node = hc::sumcheck::round_node(2);
                support::run(
                    m,
                    || {
                        hc::sumcheck::round_value_alpha(
                            black_box(&w),
                            black_box(&a),
                            black_box(node),
                        )
                    },
                    d_ext4,
                )
            }

            /// All three of its nodes -- `roundDegAlpha + 1`, not reduced.
            pub fn round_values_alpha(m: Mode<'_, '_>, half: usize) -> u64 {
                let w = ext_table(0x5A17_7012, 2 * half);
                let a = ext_table(0x5A17_7013, 2 * half);
                support::run(
                    m,
                    || hc::sumcheck::round_values_alpha(black_box(&w), black_box(&a)),
                    d_vec,
                )
            }

            /// And interpolated: the linear half of a round message.
            pub fn round_poly_alpha(m: Mode<'_, '_>, half: usize) -> u64 {
                let w = ext_table(0x5A17_7014, 2 * half);
                let a = ext_table(0x5A17_7015, 2 * half);
                support::run(
                    m,
                    || hc::sumcheck::round_poly_alpha(black_box(&w), black_box(&a)),
                    d_poly,
                )
            }

            /// The equality kernel over the drawn challenges, at the **real**
            /// `m₀`: `M_ZERO` products, one per round already played. Cheap and
            /// unreduced, which makes it the one row here that needs no caveat.
            pub fn eq_prefix(m: Mode<'_, '_>, m0: usize) -> u64 {
                let tau0 = ext_table(0x5A17_7016, m0);
                let cs = ext_table(0x5A17_7017, m0);
                support::run(
                    m,
                    || hc::sumcheck::eq_prefix(black_box(&tau0), black_box(&cs)),
                    d_ext4,
                )
            }

            /// The suffix kernel table, REDUCED: `2^{vars}` entries built by
            /// doubling, at `vars = 10` against the round-0 real `2^25`.
            pub fn eq_suffix_table(m: Mode<'_, '_>, vars: usize) -> u64 {
                let tau0 = ext_table(0x5A17_7018, vars + 1);
                support::run(
                    m,
                    || hc::sumcheck::eq_suffix_table(black_box(&tau0), black_box(0)),
                    d_vec,
                )
            }

            /// **The honest round message**, both summands with their equality
            /// factors applied: what a prover actually computes per round.
            /// REDUCED on the cube like the rows above; `τ₀` is sized so the
            /// suffix table matches the folded tables.
            pub fn honest_compute_g(m: Mode<'_, '_>, half: usize) -> u64 {
                let vars = half.trailing_zeros() as usize + 1;
                let st = round_stmt(0x5A17_7019, vars, 0);
                let w = ext_table(0x5A17_701A, 2 * half);
                let a = ext_table(0x5A17_701B, 2 * half);
                support::run(
                    m,
                    || {
                        hc::sumcheck::honest_compute_g(
                            black_box(&st),
                            black_box(&w),
                            black_box(&a),
                            black_box(0),
                        )
                    },
                    d_poly_pair,
                )
            }

            /// [`honest_compute_g`]'s row with `Ã` read through its two factors
            /// (candidate L): same cube, same round, `low` of `HALF` entries
            /// and `high` of two, the shape round 0 of an `m₀ = 11` run has.
            /// The α side is ~1.4% of the round, so this row cannot resolve
            /// the split's one extra multiplication per read; it exists to put
            /// a number beside `sumcheck/honest_compute_g` and to keep the
            /// item the prover now calls under measurement. New item: its
            /// genesis is its first translation.
            pub fn honest_compute_g_split(m: Mode<'_, '_>, half: usize) -> u64 {
                let vars = half.trailing_zeros() as usize + 1;
                let st = round_stmt(0x5A17_7025, vars, 0);
                let w = ext_table(0x5A17_7125, 2 * half);
                let low = ext_table(0x5A17_7225, half);
                let high = ext_table(0x5A17_7325, 2);
                support::run(
                    m,
                    || {
                        hc::sumcheck::honest_compute_g_split(
                            black_box(&st),
                            black_box(&w),
                            black_box(&low),
                            black_box(&high),
                            black_box(0),
                        )
                    },
                    d_poly_pair,
                )
            }

            fn d_poly_pair(g: &RoundMsg) -> u64 {
                support::mix(d_poly(g.g_zero()), d_poly(g.g_alpha()))
            }

            fn d_msgs(v: &Vec<RoundMsg>) -> u64 {
                let mut acc = support::mix_len(0, v.len());
                let mut i = 0usize;
                while i < v.len() {
                    acc = support::mix(acc, d_poly_pair(&v[i]));
                    i += 1;
                }
                acc
            }

            /// The verifier's round check: four polynomial evaluations against
            /// the two targets. Real constants -- there is nothing to reduce.
            pub fn round_check(m: Mode<'_, '_>, m0: usize) -> u64 {
                let st = round_stmt(0x5A17_701C, m0, 3);
                let g = round_msg(0x5A17_701D);
                support::run(
                    m,
                    || hc::sumcheck::round_check(black_box(&st), black_box(&g)),
                    d_bool,
                )
            }

            /// The round's output map. It takes the statement **by value** (so
            /// the extracted model stays straight-line), so each iteration
            /// needs a fresh one: `run_batched` builds it in setup, outside the
            /// timed region. Timing it any other way would measure
            /// `round_stmt`, which is corpus.
            pub fn round_out(m: Mode<'_, '_>, m0: usize) -> u64 {
                let g = round_msg(0x5A17_701E);
                let a = ext_table(0x5A17_701F, 1)[0];
                support::run_batched(
                    m,
                    || round_stmt(0x5A17_7020, m0, 3),
                    |st| hc::sumcheck::round_out(st, black_box(&g), black_box(a)),
                    d_round_stmt,
                )
            }

            /// An `R^lin` statement with `rows` real rows and `cols` columns of
            /// drawn ring elements, for the one row here that reads `M`. Each
            /// entry gets its own corpus tag, so no two matrix entries are
            /// equal and the `c_eval_at` inside `m_alpha_tilde` sees a fresh
            /// polynomial per call.
            fn rlin_statement(seed: u64, rows: usize, cols: usize) -> RlinStatement {
                let degree = hc::params::RING_DEGREE;
                let mut m = Vec::with_capacity(rows);
                let mut i = 0usize;
                while i < rows {
                    let mut row = Vec::with_capacity(cols);
                    let mut j = 0usize;
                    while j < cols {
                        row.push(Rq::from_coeffs(&support::corpus(
                            seed.wrapping_add((i * cols + j) as u64),
                            degree,
                        )));
                        j += 1;
                    }
                    m.push(PolyVec::new(row));
                    i += 1;
                }
                let mut y = Vec::with_capacity(rows);
                let mut k = 0usize;
                while k < rows {
                    y.push(Rq::from_coeffs(&support::corpus(
                        seed.wrapping_add(1000 + k as u64),
                        degree,
                    )));
                    k += 1;
                }
                RlinStatement::new(
                    hc::linalg::PolyMatrix::new(m),
                    PolyVec::new(y),
                    hc::params::CHAIN_GAMMA,
                )
            }

            /// The public table `Ã` over a REDUCED cube ([`crate::AP_M0`]),
            /// with [`crate::AP_ROWS`] statement rows and [`crate::AP_COLS`]
            /// matrix columns. Every entry is one `alpha_public_evals`: `n`
            /// rows of `eq_weight · m_alpha_tilde` and one `alpha_tilde(idx % d)`,
            /// all recomputed per entry -- which is exactly the cost the
            /// `sumcheck/alpha_public_table` row is here to expose, and the
            /// reason it was excluded until `c_eval_at` became linear
            /// (`NOTES.md` § "Stage 6 opens"). The statement, `α` and `τ₁` are
            /// built once, outside the timed region; the body allocates and
            /// returns the `2^m₀` table, which is the operation's real cost.
            ///
            /// Read its `vs genesis` as an ordinary trivial-baseline distance,
            /// not through this file's header caveat: the round-message rows'
            /// genesis is the *dense form by decision*, but a hypercube table
            /// is dense in the specification itself, and genesis's
            /// `alpha_public_table` is the literal first translation (stamp
            /// `2152e10`). The `~160×` between the two variants is the frozen
            /// quadratic `c_eval_at` one layer down, nothing about this row.
            /// Corpus tags: the statement's entries take `seed + k`, so `α` and
            /// `τ₁` sit in a different hundreds block to keep every tag distinct.
            pub fn alpha_public_table(m: Mode<'_, '_>, m0: usize) -> u64 {
                let s = rlin_statement(0x5A17_7021, crate::AP_ROWS, crate::AP_COLS);
                let alpha = ext_table(0x5A17_7121, 1)[0];
                let tau1 = ext_table(0x5A17_7221, hc::params::M_ONE);
                support::run(
                    m,
                    || {
                        hc::sumcheck::alpha_public_table(
                            black_box(&s),
                            black_box(alpha),
                            black_box(&tau1),
                            black_box(m0),
                        )
                    },
                    d_vec,
                )
            }

            /// **The whole honest prover**: `c_w_table_mle` and
            /// `alpha_public_table` over a REDUCED cube ([`crate::HRM_M0`]),
            /// then `m₀` rounds of `honest_compute_g`, `round_out` and the two
            /// `eval_mle_layer` folds. This is the item a change to *one* round
            /// lands in, and the per-round rows above cannot see such a change
            /// -- `honest_compute_g` is measured at a generic round, and round
            /// 0 is the only round whose `w̃` table is base-field. Round 0 folds
            /// `2^{m₀-1} = HALF` pairs, so its cost is `sumcheck/honest_compute_g`'s
            /// row, and the eleven rounds together are about twice it (rounds
            /// `1..` are `2^{m₀-1} − 1` of the `2^{m₀} − 1` fold pairs: 50%
            /// here and 50% at the pin, so the reduction does not distort the
            /// round-0 share). The hoisted `alpha_public_table` inside is
            /// ~0.5% of the row at one statement row and column, and the
            /// per-round interpolation ~7%, which the pin would not show --
            /// slightly conservative for a fold-level change. Reconciled
            /// against the per-round rows to 0.1% on 2026-09-15 (run
            /// `20260915T1008+0200-7cd34c7b`: 29.5 ms). Its `vs genesis` is
            /// **not** a sumcheck figure: 99.8% of it is the frozen quadratic
            /// `c_eval_at`/`c_eval_at_modulus` one layer down, which has its own
            /// rows; the round loop itself is within noise of genesis.
            ///
            /// The statement is consumed (`round_out` takes it by value), so
            /// `run_batched` builds a fresh one per iteration in setup, outside
            /// the timed region; the witness and the challenges are shared
            /// borrows built once. The statement carries one `R^lin` row and
            /// one column, which is what keeps the **genesis** variant at about
            /// `15 s` per iteration (the `HRM_M0` doc has the arithmetic).
            /// Corpus tags: the statement's entries take `seed + k`, the
            /// witness a separate hundreds block, the challenges a third.
            pub fn honest_round_messages(m: Mode<'_, '_>, m0: usize) -> u64 {
                let w = witness(0x5A17_7022, crate::HRM_Z_COLS, crate::HRM_RHO_ROWS);
                let challenges = ext_table(0x5A17_7222, m0);
                support::run_batched(
                    m,
                    || round_stmt(0x5A17_7122, m0, 0),
                    |st| {
                        hc::sumcheck::honest_round_messages(
                            st,
                            black_box(&w),
                            black_box(&challenges),
                        )
                    },
                    d_msgs,
                )
            }

            /// **The final check** at a REDUCED cube ([`crate::FC_M0`]): the
            /// whole-`τ₀` `eq̃`, the range factor, `Ã`'s multilinear extension
            /// at the sumcheck point, and the three comparisons. This is the
            /// row for a change to how `Ã(a)` is evaluated -- the tensor split
            /// (brief 5's S4, candidate J) against the tabulated form -- and
            /// `m₀ = 11` is the smallest cube where the split has two
            /// non-trivial factors (`d = 2^10` low coordinates and one high).
            /// The statement is honest (`final_stmt` at offset `(0, 0)`), so
            /// the body runs all three conjuncts to the end; `&&` would stop at
            /// the first false one on a random statement and time nothing.
            ///
            /// **The digest is a `bool`, and the void-oracle caveat applies**
            /// (`lean-opt` § "No new value-level preconditions without a
            /// gate"): `|_| true` digests identically to the real body. The
            /// oracle is `check()` above, which runs in every variant's own
            /// crate and demands acceptance of the honest statement and
            /// rejection of each moved conjunct; the `tests/` suite compares
            /// the new evaluation against the tabulated one directly. Genesis
            /// here builds the frozen `Ã` table with the frozen quadratic
            /// `c_eval_at`, ~15 s per iteration at this cube (the same 2 048
            /// entries as `sumcheck/honest_round_messages`); read its
            /// `vs genesis` accordingly -- it is not a final-check figure.
            pub fn final_check(m: Mode<'_, '_>, m0: usize) -> u64 {
                let (st, y) = final_stmt(0x5A17_7023, m0, Ext4::ZERO, Ext4::ZERO);
                let bound = hc::params::CHAIN_GAMMA;
                support::run(
                    m,
                    || hc::sumcheck::final_check(black_box(&st), black_box(y), black_box(bound)),
                    d_bool,
                )
            }

            /// `Ã`'s multilinear extension at a point by the tensor split, at
            /// the **real** `m₀ = 26` and a REDUCED statement ([`crate::AP_ROWS`]
            /// rows, [`crate::AP_COLS`] columns): a `2^10`-entry low table, a
            /// `2^16`-entry high table, two folds and one product. The row
            /// exists to put a number on the verifier's dominant step at the
            /// pin's cube -- the tabulated form it replaces is `2^26` entries
            /// and cannot run here at all. New item: its genesis is its own
            /// first translation, so `vs genesis` reads 0 by construction and
            /// the absolute time is the information.
            pub fn alpha_public_mle_eval(m: Mode<'_, '_>, m0: usize) -> u64 {
                let s = rlin_statement(0x5A17_7024, crate::AP_ROWS, crate::AP_COLS);
                let alpha = ext_table(0x5A17_7124, 1)[0];
                let tau1 = ext_table(0x5A17_7224, hc::params::M_ONE);
                let a = ext_table(0x5A17_7324, m0);
                support::run(
                    m,
                    || {
                        hc::sumcheck::alpha_public_mle_eval(
                            black_box(&s),
                            black_box(alpha),
                            black_box(&tau1),
                            black_box(&a),
                        )
                    },
                    d_ext4,
                )
            }

            // -- the A/B fairness control -----------------------------------

            /// The harness's A/B fairness control, the same body as every other
            /// binary's so that the controls stay comparable with each other.
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

fn sumcheck_benches(c: &mut Criterion) {
    now::check();
    genesis::check();
    #[cfg(feature = "candidate")]
    candidate::check();

    bench_case!(c, "_control/sumcheck", control, [support::CONTROL_N]);

    // @covers sumcheck::interpolate
    bench_case!(c, "sumcheck/interpolate", interpolate, [hachi::params::ROUND_NODES]);
    // @covers sumcheck::round_value_zero
    bench_case!(c, "sumcheck/round_value_zero", round_value_zero, [HALF]);
    // @covers sumcheck::round_values_zero
    bench_case!(c, "sumcheck/round_values_zero", round_values_zero, [HALF]);
    // @covers sumcheck::round_poly_zero
    bench_case!(c, "sumcheck/round_poly_zero", round_poly_zero, [HALF]);
    // @covers sumcheck::round_poly_zero_base
    bench_case!(c, "sumcheck/round_poly_zero_base", round_poly_zero_base, [R0_HALF]);

    // @covers sumcheck::round_value_alpha
    bench_case!(c, "sumcheck/round_value_alpha", round_value_alpha, [HALF]);
    // @covers sumcheck::round_values_alpha
    bench_case!(c, "sumcheck/round_values_alpha", round_values_alpha, [HALF]);
    // @covers sumcheck::round_poly_alpha
    bench_case!(c, "sumcheck/round_poly_alpha", round_poly_alpha, [HALF]);
    // @covers sumcheck::eq_prefix
    bench_case!(c, "sumcheck/eq_prefix", eq_prefix, [hachi::params::M_ZERO]);
    // @covers sumcheck::eq_suffix_table
    bench_case!(c, "sumcheck/eq_suffix_table", eq_suffix_table, [SUFFIX_VARS]);
    // @covers sumcheck::honest_compute_g
    bench_case!(c, "sumcheck/honest_compute_g", honest_compute_g, [HALF]);
    // @covers sumcheck::honest_compute_g_split
    bench_case!(c, "sumcheck/honest_compute_g_split", honest_compute_g_split, [HALF]);
    // @covers sumcheck::round_check
    bench_case!(c, "sumcheck/round_check", round_check, [hachi::params::M_ZERO]);
    // @covers sumcheck::round_out
    bench_case!(c, "sumcheck/round_out", round_out, [hachi::params::M_ZERO]);
    // @covers sumcheck::alpha_public_table
    bench_case!(c, "sumcheck/alpha_public_table", alpha_public_table, [AP_M0]);
    // @covers sumcheck::honest_round_messages
    bench_case!(c, "sumcheck/honest_round_messages", honest_round_messages, [HRM_M0]);
    // @covers sumcheck::final_check
    bench_case!(c, "sumcheck/final_check", final_check, [FC_M0]);
    // @covers sumcheck::alpha_public_mle_eval
    bench_case!(c, "sumcheck/alpha_public_mle_eval", alpha_public_mle_eval, [hachi::params::M_ZERO]);
}

criterion_group! {
    // The same override as `benches/commit.rs` and the other heavy binaries,
    // for the averaging reason: at `HALF = 1024` the `round_values_zero` and
    // `round_poly_zero` rows are tens of milliseconds, where criterion's
    // default linear sampling would refuse the window and flip to flat samples
    // of two iterations -- and `_robust` takes the three fastest of those,
    // which is picking the three luckiest executions in the run.
    name = sumcheck_group;
    config = support::criterion_config()
        .sample_size(50)
        .measurement_time(Duration::from_secs(10));
    targets = sumcheck_benches
}
criterion_main!(sumcheck_group);
