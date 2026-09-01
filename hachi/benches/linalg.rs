//! Wall-clock time for the vector and matrix operations.
//!
//! Sizes: the coefficientwise cases (`vec_add`, `vec_sub`, `equals`) run at
//! the scheme's own width, `MESSAGE_ROWS · GADGET_DIGITS = 8192` -- the width
//! of the inner Ajtai matrix -- and `flatten_blocks` at `BLOCKS` blocks of
//! `INNER_ROWS · GADGET_DIGITS = 8`, the shape `commit` actually flattens.
//! The ring-product cases (`dot`, `scalar_vec_mul`, `mat_vec_mul`,
//! `split_form`) run at REDUCED shapes, not the scheme's: at the [NOZ26]
//! Fig. 9 parameters one schoolbook `ring::mul` is ~2-4 ms (`RING_DEGREE =
//! 1024`), so the scheme shapes pay 8192 ring muls per iteration for the
//! first three (measured: 12.3 s/iteration for `scalar_vec_mul` at width
//! 8192, 2026-08-31) and `2^20` ring muls (~an hour) for `split_form` -- the
//! same arithmetic behind `exclusions.toml`'s Fig. 9 policy exception. The
//! reduced sizes are recorded at the registrations below; they return to the
//! scheme's the moment a sub-quadratic `ring::mul` champion lands.
//!
//! Every case here is dominated by `ring::mul`, which is the point: if this
//! module ever shows up as a cost of its own, the loop below it got faster. The
//! two exceptions are `flatten_blocks` and `equals`, which touch no ring
//! arithmetic at all -- `flatten_blocks` is `Rq::copy` in a loop and `equals` is
//! a coefficient compare.
//!
//! `vec_add` and `vec_sub` are separate rows for an identical loop shape. That is
//! deliberate: they are separate items with separate equivalence obligations
//! against the spec's `Pi` instances, and a shared shape is exactly the situation
//! in which an optimization applied to one and not the other goes unnoticed.
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
            // `support::run`'s digest argument is `Fn(&R) -> u64`, so a digest of
            // a `Copy` scalar has to take it by reference. That is the bound's
            // shape, not a choice this file makes.
            #![allow(clippy::trivially_copy_pass_by_ref)]

            use std::hint::black_box;

            use $hachi as hc;

            use crate::support::{self, Mode};

            type Rq = hc::ring::Rq;
            type PolyVec = hc::linalg::PolyVec;
            type PolyMatrix = hc::linalg::PolyMatrix;

            // -- corpus -----------------------------------------------------

            /// A `k`-entry vector of full-degree ring elements.
            ///
            /// Each entry gets its own stream (`seed + 0x100·i`), so no two
            /// entries are the same element and `dot` is not accidentally summing
            /// `k` copies of one product.
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

            /// Length first, then every entry in order. `flatten_blocks` is the
            /// case that needs both: a flatten that dropped a block, or emitted
            /// the blocks in the wrong order, must not be able to collide with a
            /// correct result.
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

            fn d_bool(x: &bool) -> u64 {
                support::mix(0, u64::from(*x))
            }

            // -- vector arithmetic ------------------------------------------

            /// `Σᵢ uᵢ · vᵢ`: `k` ring products and `k` ring additions, so this is
            /// `ring/mul` times `k` plus change, and the row every `linalg`
            /// reading should be read against.
            pub fn dot(m: Mode<'_, '_>, k: usize) -> u64 {
                let u = vec_of(0x0A0A_0A0A_0000_0001, k);
                let v = vec_of(0x0B0B_0B0B_0000_0002, k);
                support::run(m, || black_box(&u).dot(black_box(&v)), d_rq)
            }

            pub fn vec_add(m: Mode<'_, '_>, k: usize) -> u64 {
                let u = vec_of(0x0A0A_0A0A_0000_0001, k);
                let v = vec_of(0x0B0B_0B0B_0000_0002, k);
                support::run(m, || black_box(&u).add(black_box(&v)), d_polyvec)
            }

            pub fn vec_sub(m: Mode<'_, '_>, k: usize) -> u64 {
                let u = vec_of(0x0A0A_0A0A_0000_0001, k);
                let v = vec_of(0x0B0B_0B0B_0000_0002, k);
                support::run(m, || black_box(&u).sub(black_box(&v)), d_polyvec)
            }

            /// Left multiplication by a ring element: `k` full `ring::mul`s, not
            /// `k` coefficient scalings. `Rq::scalar_mul` is the coefficient one
            /// and lives in `benches/ring.rs`.
            pub fn scalar_vec_mul(m: Mode<'_, '_>, k: usize) -> u64 {
                let u = vec_of(0x0A0A_0A0A_0000_0001, k);
                let degree = hc::params::RING_DEGREE;
                let scalar = Rq::from_coeffs(&support::corpus(0x0C0C_0C0C_0000_0003, degree));
                support::run(
                    m,
                    || black_box(&u).scalar_mul(black_box(&scalar)),
                    d_polyvec,
                )
            }

            /// Equal operands on purpose; see `ring/equals` for why.
            pub fn equals(m: Mode<'_, '_>, k: usize) -> u64 {
                let u = vec_of(0x0A0A_0A0A_0000_0001, k);
                support::run(m, || black_box(&u).equals(black_box(&u)), d_bool)
            }

            // -- matrix ------------------------------------------------------

            /// `A *ᵥ v`, the Ajtai commitment itself. `cols` is the parameter; the
            /// row count is `INNER_ROWS`, taken from the variant's own `params`
            /// because it is `A`'s shape and not a knob.
            pub fn mat_vec_mul(m: Mode<'_, '_>, cols: usize) -> u64 {
                let u = vec_of(0x0A0A_0A0A_0000_0001, cols);
                let rows = hc::params::INNER_ROWS;
                let mut entries = Vec::with_capacity(rows);
                for i in 0..rows {
                    entries.push(vec_of(0x0D0D_0000_0000_0000 + i as u64, cols));
                }
                let a = PolyMatrix::new(entries);
                support::run(m, || black_box(&a).mat_vec_mul(black_box(&u)), d_polyvec)
            }

            /// `uᵀ M v` on a square `cols × cols` matrix (the parameter is the
            /// column count). One `mat_vec_mul` plus one `dot`, so
            /// `cols² + cols` ring products -- quadratic in the parameter,
            /// which is why this case gets two points. The scheme's own shape
            /// (`ML_LOW_LEN = 1024` rows) is `2^20` ring products per
            /// iteration at the Fig. 9 parameters; see the module doc.
            pub fn split_form(m: Mode<'_, '_>, cols: usize) -> u64 {
                let rows = cols;
                let mut entries = Vec::with_capacity(rows);
                for i in 0..rows {
                    entries.push(vec_of(0x0F0F_0000_0000_0000 + i as u64, cols));
                }
                let a = PolyMatrix::new(entries);
                let u = vec_of(0x0A0A_0A0A_0000_0001, rows);
                let v = vec_of(0x0B0B_0B0B_0000_0002, cols);
                support::run(
                    m,
                    || black_box(&a).split_form(black_box(&u), black_box(&v)),
                    d_rq,
                )
            }

            /// `width` is one block's width, `BLOCKS` blocks of it -- the shape
            /// `commit_with_decomps` flattens.
            pub fn flatten_blocks(m: Mode<'_, '_>, width: usize) -> u64 {
                let nblocks = hc::params::BLOCKS;
                let mut blocks = Vec::with_capacity(nblocks);
                for i in 0..nblocks {
                    blocks.push(vec_of(0x0E0E_0000 + i as u64, width));
                }
                support::run(
                    m,
                    || hc::linalg::flatten_blocks(black_box(&blocks)),
                    d_polyvec,
                )
            }

            // -- the A/B fairness control -----------------------------------

            /// The harness's A/B fairness control. Every variant of this case runs
            /// its own compiled copy of the *same source*, so any difference the
            /// report shows for it is measurement bias -- timing order, machine
            /// drift and code layout -- and not code. See
            /// `support/mod.rs` § "The A/B fairness control" for why the body is a
            /// variant-crate operation rather than a bench-crate symbol, and for
            /// what that costs.
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

fn linalg_benches(c: &mut Criterion) {
    // The run's sanity check: identical source in every variant, so anything it
    // reads is the harness disagreeing with itself. Runs first, while the machine
    // is in the same state the first real cases will see.
    bench_case!(c, "_control/linalg", control, [support::CONTROL_N]);

    // `A`'s width, and so every coefficientwise case's vector length.
    let width = hachi::params::MESSAGE_ROWS * hachi::params::GADGET_DIGITS;
    // One inner decomposition block, which is what gets flattened.
    let block = hachi::params::INNER_ROWS * hachi::params::GADGET_DIGITS;
    // REDUCED width for the three `ring::mul`-dominated cases, per the module
    // doc: 16 full-degree ring products per iteration (~tens of ms) instead of
    // `width = 8192` (~tens of seconds). The row stays >99% `ring::mul`, which
    // is the cost it exists to track.
    let mul_width = 16;

    // @covers linalg::PolyVec::dot
    bench_case!(c, "linalg/dot", dot, [mul_width]);
    // @covers linalg::PolyVec::add
    bench_case!(c, "linalg/vec_add", vec_add, [width]);
    // @covers linalg::PolyVec::sub
    bench_case!(c, "linalg/vec_sub", vec_sub, [width]);
    // @covers linalg::PolyVec::scalar_mul
    bench_case!(c, "linalg/scalar_vec_mul", scalar_vec_mul, [mul_width]);
    // @covers linalg::PolyVec::equals
    bench_case!(c, "linalg/equals", equals, [width]);

    // @covers linalg::PolyMatrix::mat_vec_mul
    bench_case!(c, "linalg/mat_vec_mul", mat_vec_mul, [mul_width]);

    // The evaluation split's bilinear form, at REDUCED square shapes (module
    // doc); two points because the case is quadratic in its parameter.
    // @covers linalg::PolyMatrix::split_form
    bench_case!(c, "linalg/split_form", split_form, [4, 8]);

    // @covers linalg::flatten_blocks
    bench_case!(c, "linalg/flatten_blocks", flatten_blocks, [block]);
}

criterion_group! {
    name = benches;
    config = support::criterion_config();
    targets = linalg_benches
}
criterion_main!(benches);
