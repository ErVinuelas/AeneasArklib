//! Wall-clock time for the multilinear evaluation split -- at *reduced* point
//! sizes, by signed-off policy exception.
//!
//! At the [NOZ26] Fig. 9 parameters the scheme's own sizes are out of a
//! criterion run's reach: the point halves are `ML_VARS_LOW = ML_VARS_HIGH =
//! 10` coordinates, so one basis is `2^10` schoolbook `ring::mul`s of `2^20`
//! field operations each (seconds per iteration), and the reshape/evaluation
//! cases build `ML_POLY_LEN = 2^20` ring elements (~8 GiB) before multiplying
//! `2^20` more. Policy, per PLAN_PAPER_PARAMS.md Decision 3 (signed off
//! 2026-08-28):
//!
//! * the two *shape-generic* basis cases stay, at reduced variable counts
//!   (4 and 6) that are NOT the scheme's -- the rows measure the per-entry
//!   cost shape (`n · 2^n` ring muls at the real `RING_DEGREE = 1024`), not
//!   the scheme-scale total, and say so here rather than pretending;
//! * the const-bound reshape/evaluation cases are excluded by name in
//!   `exclusions.toml`; their bodies are retained below, unregistered, for
//!   the day a sub-quadratic `ring::mul` champion lands.
//!
//! Everything with ring multiplications in it is `ring::mul` in a loop, as
//! everywhere above the ring; the two reshapes are the exceptions
//! (`Rq::copy` in a loop, no arithmetic).
//!
//! See `benches/support/mod.rs` for the corpus discipline, the digest oracle and
//! what the `_control` case is.

mod support;

use criterion::{criterion_group, criterion_main, Criterion};

/// One body per case, instantiated once per variant crate. Writing the variants
/// separately is how a benchmark quietly starts comparing two different
/// computations; a macro makes that impossible.
macro_rules! define_cases {
    ($modname:ident, $hachi:path) => {
        mod $modname {
            // `support::run`'s digest argument is `Fn(&R) -> u64`; see
            // `benches/linalg.rs` for why the digests take references.
            #![allow(clippy::trivially_copy_pass_by_ref)]
            // The reshape/evaluation case bodies are kept but not registered:
            // at the [NOZ26] Fig. 9 parameters they are excluded by policy (see
            // the module doc and `exclusions.toml`), and they return verbatim
            // when a sub-quadratic `ring::mul` lands.
            #![allow(dead_code)]

            use std::hint::black_box;

            use $hachi as hc;

            use crate::support::{self, Mode};

            type Rq = hc::ring::Rq;
            type PolyVec = hc::linalg::PolyVec;
            type PolyMatrix = hc::linalg::PolyMatrix;
            type MlPoly = hc::evalsplit::MlPoly;
            type MlEvals = hc::evalsplit::MlEvals;

            // -- corpus -----------------------------------------------------

            /// A `k`-entry vector of full-degree ring elements, one stream per
            /// entry (see `benches/linalg.rs::vec_of`).
            fn vec_of(seed: u64, k: usize) -> PolyVec {
                let degree = hc::params::RING_DEGREE;
                let mut entries = Vec::with_capacity(k);
                for i in 0..k {
                    entries.push(Rq::from_coeffs(&support::corpus(
                        seed.wrapping_add(i as u64 * 0x100),
                        degree,
                    )));
                }
                PolyVec::new(entries)
            }

            /// The `ML_POLY_LEN` ring elements of a committed polynomial.
            fn coeffs_of(seed: u64) -> Vec<Rq> {
                let len = hc::params::ML_POLY_LEN;
                let degree = hc::params::RING_DEGREE;
                let mut out = Vec::with_capacity(len);
                for i in 0..len {
                    out.push(Rq::from_coeffs(&support::corpus(
                        seed.wrapping_add(i as u64 * 0x100),
                        degree,
                    )));
                }
                out
            }

            /// The split matrix shape, `ML_LOW_LEN × ML_HIGH_LEN`.
            fn split_matrix(seed: u64) -> PolyMatrix {
                let rows = hc::params::ML_LOW_LEN;
                let cols = hc::params::ML_HIGH_LEN;
                let mut out = Vec::with_capacity(rows);
                for i in 0..rows {
                    out.push(vec_of(seed.wrapping_add(i as u64 * 0x10_000), cols));
                }
                PolyMatrix::new(out)
            }

            // -- digests (outside every timed region) -----------------------

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

            /// Shape first, then every row: a reshape that transposed, dropped
            /// or reordered rows must not collide with a correct result.
            fn d_polymatrix(m: &PolyMatrix) -> u64 {
                let rows = m.rows();
                let mut acc = support::mix_len(0, rows);
                let mut i = 0usize;
                while i < rows {
                    acc = support::mix(acc, d_polyvec(m.row(i)));
                    i += 1;
                }
                acc
            }

            fn d_mlpoly(p: &MlPoly) -> u64 {
                let k = p.len();
                let mut acc = support::mix_len(0, k);
                let mut i = 0usize;
                while i < k {
                    acc = support::mix(acc, d_rq(p.get(i)));
                    i += 1;
                }
                acc
            }

            // -- the bases ---------------------------------------------------

            /// `n · 2^n` ring multiplications, the naive per-entry product.
            pub fn monomial_basis(m: Mode<'_, '_>, n: usize) -> u64 {
                let w = vec_of(0x51_0000_0001, n);
                support::run(
                    m,
                    || hc::evalsplit::monomial_basis(black_box(&w)),
                    d_polyvec,
                )
            }

            /// The same shape with a subtraction on the zero branches.
            pub fn lagrange_basis(m: Mode<'_, '_>, n: usize) -> u64 {
                let w = vec_of(0x51_0000_0002, n);
                support::run(
                    m,
                    || hc::evalsplit::lagrange_basis(black_box(&w)),
                    d_polyvec,
                )
            }

            // -- the reshapes ------------------------------------------------

            /// Pure data movement: `ML_POLY_LEN` ring copies, no arithmetic.
            pub fn to_matrix(m: Mode<'_, '_>, _len: usize) -> u64 {
                let p = MlPoly::new(coeffs_of(0x52_0000_0001));
                support::run(m, || black_box(&p).to_matrix(), d_polymatrix)
            }

            /// The inverse reshape, same cost shape.
            pub fn to_polynomial(m: Mode<'_, '_>, _len: usize) -> u64 {
                let mat = split_matrix(0x52_0000_0002);
                support::run(
                    m,
                    || hc::evalsplit::to_polynomial(black_box(&mat)),
                    d_mlpoly,
                )
            }

            /// The value-vector reshape (distinct item, same layout).
            pub fn to_matrix_eval(m: Mode<'_, '_>, _len: usize) -> u64 {
                let v = MlEvals::new(coeffs_of(0x52_0000_0003));
                support::run(m, || black_box(&v).to_matrix_eval(), d_polymatrix)
            }

            // -- the evaluations ---------------------------------------------

            /// End to end: reshape + both monomial bases + the bilinear form.
            /// About 20 `ring::mul`s at the crate's split.
            pub fn eval_split(m: Mode<'_, '_>, _len: usize) -> u64 {
                let p = MlPoly::new(coeffs_of(0x53_0000_0001));
                let xl = vec_of(0x53_0000_0002, hc::params::ML_VARS_LOW);
                let xh = vec_of(0x53_0000_0003, hc::params::ML_VARS_HIGH);
                support::run(
                    m,
                    || black_box(&p).eval_split(black_box(&xl), black_box(&xh)),
                    d_rq,
                )
            }

            /// End to end on the Lagrange representation.
            pub fn eval_split_eval(m: Mode<'_, '_>, _len: usize) -> u64 {
                let v = MlEvals::new(coeffs_of(0x53_0000_0004));
                let xl = vec_of(0x53_0000_0005, hc::params::ML_VARS_LOW);
                let xh = vec_of(0x53_0000_0006, hc::params::ML_VARS_HIGH);
                support::run(
                    m,
                    || black_box(&v).eval_split_eval(black_box(&xl), black_box(&xh)),
                    d_rq,
                )
            }

            // -- the A/B fairness control -----------------------------------

            /// The harness's A/B fairness control; see
            /// `support/mod.rs` § "The A/B fairness control".
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

fn evalsplit_benches(c: &mut Criterion) {
    // The run's sanity check; see `benches/linalg.rs`.
    bench_case!(c, "_control/evalsplit", control, [support::CONTROL_N]);

    // REDUCED sizes, not the scheme's (`ML_VARS_LOW = ML_VARS_HIGH = 10` puts
    // one basis at `2^10` schoolbook d=1024 ring muls -- seconds per
    // iteration). 4 and 6 keep two points on the `n · 2^n` curve so the
    // exponential shape stays visible; the module doc records the policy
    // exception and its sign-off.
    let n_small = 4;
    let n_large = 6;

    // @covers evalsplit::monomial_basis
    bench_case!(c, "evalsplit/monomial_basis", monomial_basis, [n_small, n_large]);
    // @covers evalsplit::lagrange_basis
    bench_case!(c, "evalsplit/lagrange_basis", lagrange_basis, [n_small, n_large]);

    // The reshape/evaluation cases (`to_matrix`, `to_polynomial`,
    // `to_matrix_eval`, `eval_split`, `eval_split_eval`) are excluded at the
    // Fig. 9 parameters: their shapes are the `params` constants
    // (`ML_POLY_LEN = 2^20` ring elements, ~8 GiB per corpus, and `2^20` ring
    // muls per evaluation), so no input can make them criterion-sized. See
    // `exclusions.toml` and NOTES.md ("Adopting the paper's parameters").
}

criterion_group! {
    name = benches;
    config = support::criterion_config();
    targets = evalsplit_benches
}
criterion_main!(benches);
