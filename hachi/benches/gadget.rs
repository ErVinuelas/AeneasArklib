//! Wall-clock time for the gadget algebra.
//!
//! `gadget_decompose` is the interesting one, and the case most likely to be
//! optimized first: as written it re-derives each digit from the coefficient with
//! a fresh division chain (`digit_at` divides `e` times), which is
//! `O(digits²)` per coefficient where a running quotient would be `O(digits)`.
//! That is a deliberate choice for the equivalence proof's sake -- each output
//! digit is literally the spec's `digit c e` -- and the reading here is what makes
//! the trade visible instead of assumed.
//!
//! `base_pow` inside `gadget_mul` is the same trade: recomputing `bᵉ` per slot
//! rather than carrying it, so every term is syntactically the spec's `base ^ e`.
//!
//! # Two families of size, and what each parameter means
//!
//! * `GADGET_DIGITS = 8` for the per-coefficient layer (`digit_at`, `base_pow`,
//!   `digit_decompose`, `gadget_entry`). For the two that take a digit index, the
//!   row measures the **deepest** one, `digits - 1`: both are `O(e)` division or
//!   multiplication chains, so index 0 would measure a loop that never runs.
//! * `MESSAGE_ROWS = 1024` for `gadget_decompose` and `gadget_mul` -- the
//!   message block shape the scheme actually decomposes (both are
//!   coefficientwise, no full ring product, so they stay ~tens of ms at the
//!   [NOZ26] Fig. 9 parameters); `verify_weak` also calls `gadget_mul` at
//!   `INNER_ROWS`, which is smaller and covered by the same row.
//! * a REDUCED row count for `gadget_matrix`, not the scheme's: the dense `G`
//!   is `rows × (rows · digits)` ring elements, and at `MESSAGE_ROWS = 1024`
//!   that is `2^23` elements of `RING_DEGREE = 1024` coefficients each,
//!   ~64 GiB -- unbuildable, the same arithmetic class as `exclusions.toml`'s
//!   Fig. 9 policy exception. The reduced size is recorded at the
//!   registration; unlike the `ring::mul`-bound cases it returns with a
//!   sparse or streamed `G`, not with the multiplication champion -- the cost
//!   here is materialization, not arithmetic.
//!
//! `gadget_entry` measures the on-diagonal branch (`j / digits == i`), the one
//! that does work: `Rq::constant(base_pow(j % digits))`. The off-diagonal branch
//! is `Rq::zero()` and is measured as `ring/zero`; `gadget_matrix`, which is
//! `rows · rows · digits` entries of which all but `rows · digits` take the zero
//! branch, is the row that shows the mix.
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

            use cpoly::Fp;

            use $hachi as hc;

            use crate::support::{self, Mode};

            type Rq = hc::ring::Rq;
            type PolyVec = hc::linalg::PolyVec;
            type PolyMatrix = hc::linalg::PolyMatrix;

            // -- corpus -----------------------------------------------------

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

            /// The single coefficient the per-coefficient rows decompose.
            ///
            /// One draw from its own stream, so the digit chains all see the same
            /// element and the four rows are comparable to each other.
            fn one_coeff() -> Fp {
                support::corpus(0x1B1B_0000_0000_0002, 1)[0]
            }

            // -- digests (outside every timed region) -----------------------

            fn d_fp(x: &Fp) -> u64 {
                support::mix(0, x.to_u64())
            }

            /// Length first: `digit_decompose` returning the right digits and the
            /// wrong number of them must not collide with a correct result.
            fn d_fps(v: &Vec<Fp>) -> u64 {
                let mut acc = support::mix_len(0, v.len());
                let mut i = 0usize;
                while i < v.len() {
                    acc = support::mix(acc, v[i].to_u64());
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

            /// Both dimensions, then the rows. `gadget_matrix`'s shape is
            /// `rows × (rows · digits)`, and a wrong shape is the most likely way
            /// for it to be wrong.
            fn d_polymatrix(a: &PolyMatrix) -> u64 {
                let rows = a.rows();
                let mut acc = support::mix_len(support::mix_len(0, rows), a.cols());
                let mut i = 0usize;
                while i < rows {
                    acc = support::mix(acc, d_polyvec(a.row(i)));
                    i += 1;
                }
                acc
            }

            // -- the gadget round trip --------------------------------------

            /// `G · G⁻¹(x) = x`, asserted before anything is timed.
            ///
            /// The whole point of the gadget is that this holds while `G⁻¹(x)` has
            /// tiny norm; a timing of a decomposition that does not invert would
            /// be meaningless. Called for every variant, which is what makes it a
            /// real check that the frozen and slot copies were copied and not
            /// paraphrased.
            pub fn check() {
                let degree = hc::params::RING_DEGREE;
                let x = PolyVec::new(vec![Rq::from_coeffs(&support::corpus(0x1234, degree))]);
                assert!(
                    hc::gadget::gadget_mul(1, &hc::gadget::gadget_decompose(&x)).equals(&x),
                    "the gadget round trip fails; a timing of it would be meaningless"
                );
            }

            // -- the per-coefficient layer ----------------------------------

            /// `digits` is the parameter, `digits - 1` the index measured: this is
            /// an `O(e)` division chain, so the deepest digit is the row worth
            /// having.
            pub fn digit_at(m: Mode<'_, '_>, digits: usize) -> u64 {
                let c = one_coeff();
                support::run(
                    m,
                    || hc::gadget::digit_at(black_box(c), black_box(digits - 1)),
                    d_fp,
                )
            }

            /// All `digits` digits, i.e. `digit_at` at every index -- `O(digits²)`
            /// divisions in total, which is the cost `gadget_decompose` pays per
            /// coefficient and the one an optimization would remove.
            pub fn digit_decompose(m: Mode<'_, '_>, _digits: usize) -> u64 {
                let c = one_coeff();
                support::run(
                    m,
                    || hc::gadget::digit_decompose(black_box(c)),
                    d_fps,
                )
            }

            /// See [`digit_at`]: `O(e)` modular multiplications, measured at the
            /// deepest exponent.
            pub fn base_pow(m: Mode<'_, '_>, digits: usize) -> u64 {
                support::run(
                    m,
                    || hc::gadget::base_pow(black_box(digits - 1)),
                    d_fp,
                )
            }

            /// The on-diagonal entry at the deepest exponent: `base_pow(digits-1)`
            /// followed by an `Rq::constant` that fills `RING_DEGREE` slots.
            pub fn gadget_entry(m: Mode<'_, '_>, digits: usize) -> u64 {
                support::run(
                    m,
                    || hc::gadget::gadget_entry(black_box(0), black_box(digits - 1)),
                    d_rq,
                )
            }

            // -- the balanced per-coefficient layer --------------------------

            /// The balanced digit at the deepest index: the unsigned chain plus
            /// the two constant `Fp::new`s, the field shift add and the
            /// recentring subtract -- five modular reductions where
            /// [`digit_at`] pays one.
            pub fn balanced_digit_at(m: Mode<'_, '_>, digits: usize) -> u64 {
                let c = one_coeff();
                support::run(
                    m,
                    || hc::gadget::balanced_digit_at(black_box(c), black_box(digits - 1)),
                    d_fp,
                )
            }

            /// All `digits` balanced digits: the row that shows what hoisting
            /// the one `c + shift` out of the loop would buy, since the first
            /// translation re-derives it per digit.
            pub fn balanced_digit_decompose(m: Mode<'_, '_>, _digits: usize) -> u64 {
                let c = one_coeff();
                support::run(
                    m,
                    || hc::gadget::balanced_digit_decompose(black_box(c)),
                    d_fps,
                )
            }

            /// The `z`-side digit map at its own deepest index, `Z_DIGITS - 1`.
            /// A different shape from [`balanced_digit_at`], not just a
            /// different width: it centres first and shifts in the integers, so
            /// the reading includes the `valMinAbs` fold and excludes one of the
            /// two constant field reductions.
            pub fn bounded_z_digit_at(m: Mode<'_, '_>, z_digits: usize) -> u64 {
                let c = one_coeff();
                support::run(
                    m,
                    || hc::gadget::bounded_z_digit_at(black_box(c), black_box(z_digits - 1)),
                    d_fp,
                )
            }

            // -- the row layer ------------------------------------------------

            pub fn gadget_matrix(m: Mode<'_, '_>, rows: usize) -> u64 {
                support::run(
                    m,
                    || hc::gadget::gadget_matrix(black_box(rows)),
                    d_polymatrix,
                )
            }

            pub fn gadget_decompose(m: Mode<'_, '_>, rows: usize) -> u64 {
                let x = vec_of(0x1A1A_0000_0000_0001, rows);
                support::run(
                    m,
                    || hc::gadget::gadget_decompose(black_box(&x)),
                    d_polyvec,
                )
            }

            /// The Hachi gadget inverse proper, at the same `x` the unsigned
            /// `gadget_decompose` row uses -- so the two rows differ by exactly
            /// the balanced layer's cost and nothing else.
            pub fn balanced_gadget_decompose(m: Mode<'_, '_>, rows: usize) -> u64 {
                let x = vec_of(0x1A1A_0000_0000_0001, rows);
                support::run(
                    m,
                    || hc::gadget::balanced_gadget_decompose(black_box(&x)),
                    d_polyvec,
                )
            }

            /// `G · v` on the honest decomposition of the same `x` the
            /// `gadget_decompose` row uses, so the two rows are two halves of one
            /// round trip rather than two unrelated readings.
            pub fn gadget_mul(m: Mode<'_, '_>, rows: usize) -> u64 {
                let x = vec_of(0x1A1A_0000_0000_0001, rows);
                let decomposed = hc::gadget::gadget_decompose(&x);
                support::run(
                    m,
                    || hc::gadget::gadget_mul(black_box(rows), black_box(&decomposed)),
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

fn gadget_benches(c: &mut Criterion) {
    now::check();
    genesis::check();
    #[cfg(feature = "candidate")]
    candidate::check();

    // The run's sanity check: identical source in every variant, so anything it
    // reads is the harness disagreeing with itself. Runs first, while the machine
    // is in the same state the first real cases will see.
    bench_case!(c, "_control/gadget", control, [support::CONTROL_N]);

    let digits = hachi::params::GADGET_DIGITS;
    let z_digits = hachi::params::Z_DIGITS;
    let rows = hachi::params::MESSAGE_ROWS;
    // REDUCED row count for the dense-`G` case only (module doc): 16 rows is
    // `16 × 128` ring elements (~17 MiB) instead of the scheme's ~64 GiB.
    let matrix_rows = 16;

    // @covers gadget::digit_at
    bench_case!(c, "gadget/digit_at", digit_at, [digits]);
    // @covers gadget::digit_decompose
    bench_case!(c, "gadget/digit_decompose", digit_decompose, [digits]);
    // @covers gadget::base_pow
    bench_case!(c, "gadget/base_pow", base_pow, [digits]);
    // @covers gadget::gadget_entry
    bench_case!(c, "gadget/gadget_entry", gadget_entry, [digits]);

    // @covers gadget::balanced_digit_at
    bench_case!(c, "gadget/balanced_digit_at", balanced_digit_at, [digits]);
    // @covers gadget::balanced_digit_decompose
    bench_case!(c, "gadget/balanced_digit_decompose", balanced_digit_decompose, [digits]);
    // @covers gadget::bounded_z_digit_at
    bench_case!(c, "gadget/bounded_z_digit_at", bounded_z_digit_at, [z_digits]);

    // @covers gadget::gadget_matrix
    bench_case!(c, "gadget/gadget_matrix", gadget_matrix, [matrix_rows]);
    // @covers gadget::gadget_decompose
    bench_case!(c, "gadget/gadget_decompose", gadget_decompose, [rows]);
    // @covers gadget::balanced_gadget_decompose
    bench_case!(c, "gadget/balanced_gadget_decompose", balanced_gadget_decompose, [rows]);
    // @covers gadget::gadget_mul
    bench_case!(c, "gadget/gadget_mul", gadget_mul, [rows]);
}

criterion_group! {
    name = benches;
    config = support::criterion_config();
    targets = gadget_benches
}
criterion_main!(benches);
