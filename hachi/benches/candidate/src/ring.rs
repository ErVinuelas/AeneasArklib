//! The negacyclic ring `R_q = Z_q[X] / (X^N + 1)`, with `N = RING_DEGREE`.
//!
//! Reference specification: `ArkLib/Data/Lattices/CyclotomicRing/Rq.lean`,
//! instantiated at the Hachi modulus (`InnerOuter/Arithmetic.lean`'s
//! `hachiModulus q α = primePowTwoModulus q α`, i.e. `φ = X^{2^α} + 1`).
//!
//! # Representation, and how it lines up with the spec
//!
//! ArkLib's `Rq Φ` is a *subtype*: `{ p : CPolynomial R // Φ.reduce p = p }`,
//! the computable polynomials already fixed by reduction mod `φ`. It is a
//! subtype rather than a raw polynomial for a reason that matters to the
//! commitment's soundness -- two raw polynomials can be unequal yet congruent
//! mod `φ`, which would make the binding reduction unsound (`Rq.lean:14-17`).
//!
//! Here that subtype is a coefficient vector of *exactly* [`params::RING_DEGREE`]
//! elements, little-endian in `X`: `Rq::from_coeffs(vec![a, b])` is `a + b·X`.
//! The two presentations agree because `deg φ = N`, so "fixed by reduction" and
//! "has fewer than `N` coefficients" are the same condition -- ArkLib proves
//! exactly this in `reduce_eq_self_of_degree_lt` and
//! `natDegree_lt_of_reduced`. Fixing the length at `N` (rather than trimming
//! trailing zeros, as `CPolynomial` does) is what makes every operation below a
//! straight loop with no reduction step: the spec's `add_val` / `sub_val` /
//! `neg_val` prove that reduction is a no-op on those, and `mul` folds the
//! wraparound in as it goes.
//!
//! # The length invariant
//!
//! The `N`-coefficient shape is an invariant of construction, not a checked
//! precondition: every constructor here produces exactly `N` coefficients and
//! every operation preserves that. The operations index up to `N`, so a
//! hand-built shorter vector would panic -- which is why the Lean side carries
//! it as a hypothesis (`Wf a : a.length = N`) on each `_spec`, the way `cpoly`'s
//! `Field.lean` carries `Red` for the reducedness of an `Fp` word. Aeneas cannot
//! see a Rust privacy boundary, so the invariant has to be said out loud there
//! even though nothing outside this module can break it.
//!
//! # Where the product went
//!
//! [`Rq::mul`] is no longer the schoolbook `O(N²)` convolution. It delegates to
//! [`crate::ntt`], an auxiliary-prime negacyclic number-theoretic transform
//! with CRT reconstruction, and what comes back is the *same integer
//! convolution* the schoolbook loop computed -- reduced mod `q` once per
//! coefficient, exactly as before. `ntt`'s module header says why the transform
//! cannot happen in `Z_q` and what makes the reconstruction exact.
//!
//! The specification did not move with the implementation: `Ring.mul_spec` and
//! `RqBridge.mul_spec` are the statements they were.

use alloc::vec::Vec;
use cpoly::Fp;

use crate::params;

/// An element of `R_q = Z_q[X] / (X^N + 1)`, as its `N` coefficients,
/// little-endian in `X`.
///
/// Mirrors ArkLib's `CyclotomicModulus.Rq Φ` at `Φ = hachiModulus q α`; see the
/// module header for why a fixed-length vector is the right presentation of that
/// subtype.
pub struct Rq(Vec<Fp>);

impl Rq {
    /// The zero element (spec: the `Zero (Rq Φ)` instance, `Rq.lean:107`).
    ///
    /// Mirrors ArkLib's `Zero (Rq Φ)` instance.
    pub fn zero() -> Rq {
        let n: usize = params::RING_DEGREE;
        let mut out: Vec<Fp> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            out.push(Fp::ZERO);
            i += 1;
        }
        Rq(out)
    }

    /// The multiplicative identity (spec: the `One (Rq Φ)` instance,
    /// `Rq.lean:108`).
    ///
    /// Mirrors ArkLib's `One (Rq Φ)` instance.
    pub fn one() -> Rq {
        Rq::constant(Fp::ONE)
    }

    /// The constant polynomial `C c` (spec: `Rq.constRq`, `Rq.lean:353`).
    ///
    /// Mirrors ArkLib's `Rq.constRq`.
    ///
    /// The spec's `constRq_val` records that no reduction happens here, since
    /// `deg (C c) = 0 < deg φ`; correspondingly this is just `c` in the
    /// zeroth slot.
    ///
    /// Pre-sized to `n` (Stage 6 candidate D2): `Vec::with_capacity` is erased by
    /// the extraction (`alloc.vec.Vec.with_capacity T _ = Vec.new T`), so the model
    /// and its spec are those of the push loop; the capacity spares the ten
    /// reallocations a 1024-word push loop otherwise pays.
    pub fn constant(c: Fp) -> Rq {
        let n: usize = params::RING_DEGREE;
        let mut out: Vec<Fp> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            if i == 0 {
                out.push(c);
            } else {
                out.push(Fp::ZERO);
            }
            i += 1;
        }
        Rq(out)
    }

    /// The element with the given coefficients (spec: `Rq.ofFinCoeff`,
    /// `Rq.lean:269`, at `N = deg φ`).
    ///
    /// Mirrors ArkLib's `Rq.ofFinCoeff` at `N = deg φ`.
    ///
    /// Coefficients beyond `coeffs.len()` are zero and coefficients from
    /// `RING_DEGREE` on are dropped, which is what makes this total: the spec's
    /// `ofFinCoeff_coeff` reads `if k < N then c k else 0`, and its side
    /// condition `N ≤ deg φ` holds with equality here.
    ///
    /// Pre-sized to `n` (Stage 6 candidate D2): `Vec::with_capacity` is erased by
    /// the extraction (`alloc.vec.Vec.with_capacity T _ = Vec.new T`), so the model
    /// and its spec are those of the push loop; the capacity spares the ten
    /// reallocations a 1024-word push loop otherwise pays.
    pub fn from_coeffs(coeffs: &Vec<Fp>) -> Rq {
        let n: usize = params::RING_DEGREE;
        let m: usize = coeffs.len();
        let mut out: Vec<Fp> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            if i < m {
                out.push(coeffs[i]);
            } else {
                out.push(Fp::ZERO);
            }
            i += 1;
        }
        Rq(out)
    }

    /// The `k`-th coefficient (spec: `Rq.coeffHom`, `Rq.lean:260`).
    ///
    /// Mirrors ArkLib's `Rq.coeffHom`.
    ///
    /// Zero at and beyond `RING_DEGREE`, which is the spec's
    /// `coeff_eq_zero_of_natDegree_le` rather than a convention chosen here.
    pub fn coeff(&self, k: usize) -> Fp {
        if k < self.0.len() {
            self.0[k]
        } else {
            Fp::ZERO
        }
    }

    /// The number of coefficients: `RING_DEGREE`, for anything this module built.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Coefficientwise equality.
    ///
    /// This, not `==`, is the equality the scheme uses: it is what
    /// `Simple.verify`'s `decide (commit Φ A s = c)` corresponds to. Written out
    /// rather than derived so that there is exactly *one* notion of equality on
    /// this type for a proof to be about -- a `#[derive(PartialEq)]` alongside it
    /// would extract as a second one. (It would extract: Aeneas models the
    /// derives. See NOTES.md § "Derives extract, and are still not worth it".)
    ///
    /// The comparison goes through [`Fp::to_u64`] rather than `Fp`'s own `==`
    /// for the same reason, one layer down. Both representatives are reduced, so
    /// comparing the words is comparing the field elements.
    pub fn equals(&self, rhs: &Rq) -> bool {
        let n: usize = self.0.len();
        if n != rhs.0.len() {
            false
        } else {
            let mut i: usize = 0;
            let mut same: bool = true;
            while i < n {
                if self.0[i].to_u64() != rhs.0[i].to_u64() {
                    same = false;
                }
                i += 1;
            }
            same
        }
    }

    /// Is this the zero element?
    pub fn is_zero(&self) -> bool {
        let n: usize = self.0.len();
        let mut i: usize = 0;
        let mut zero: bool = true;
        while i < n {
            if self.0[i].to_u64() != 0 {
                zero = false;
            }
            i += 1;
        }
        zero
    }

    /// An independent copy.
    ///
    /// Hand-rolled rather than `#[derive(Clone)]`, which would go through
    /// `Vec::clone`: the Aeneas `Vec` model covers `push`, `len`, `index` and
    /// `index_mut` (all four appear in `lean/Generated.lean`), and a `clone` that
    /// is not among them would arrive as an opaque function -- a copy about which
    /// nothing is known, in the middle of a proof that needs to know the copy is
    /// a copy. A `push` loop is transparent and costs the same.
    ///
    /// Pre-sized to `n` (Stage 6 candidate D2): `Vec::with_capacity` is erased by
    /// the extraction (`alloc.vec.Vec.with_capacity T _ = Vec.new T`), so the model
    /// and its spec are those of the push loop; the capacity spares the ten
    /// reallocations a 1024-word push loop otherwise pays.
    pub fn copy(&self) -> Rq {
        let n: usize = self.0.len();
        let mut out: Vec<Fp> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            out.push(self.0[i]);
            i += 1;
        }
        Rq(out)
    }

    /// Coefficientwise addition (spec: the `Add (Rq Φ)` instance,
    /// `Rq.lean:109`; that it is coefficientwise -- that the reduction in
    /// `Rq.mk` does nothing -- is the spec's `add_val`, `Rq.lean:246`).
    ///
    /// Mirrors ArkLib's `Add (Rq Φ)` instance.
    ///
    /// Pre-sized to `n` (Stage 6 candidate D2): `Vec::with_capacity` is erased by
    /// the extraction (`alloc.vec.Vec.with_capacity T _ = Vec.new T`), so the model
    /// and its spec are those of the push loop; the capacity spares the ten
    /// reallocations a 1024-word push loop otherwise pays.
    pub fn add(&self, rhs: &Rq) -> Rq {
        let n: usize = self.0.len();
        let mut out: Vec<Fp> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            out.push(self.0[i] + rhs.0[i]);
            i += 1;
        }
        Rq(out)
    }

    /// Coefficientwise subtraction (spec: `Rq.lean:112`, coefficientwise by
    /// `sub_val`, `Rq.lean:231`).
    ///
    /// Mirrors ArkLib's `Sub (Rq Φ)` instance.
    ///
    /// Pre-sized to `n` (Stage 6 candidate D2): `Vec::with_capacity` is erased by
    /// the extraction (`alloc.vec.Vec.with_capacity T _ = Vec.new T`), so the model
    /// and its spec are those of the push loop; the capacity spares the ten
    /// reallocations a 1024-word push loop otherwise pays.
    pub fn sub(&self, rhs: &Rq) -> Rq {
        let n: usize = self.0.len();
        let mut out: Vec<Fp> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            out.push(self.0[i] - rhs.0[i]);
            i += 1;
        }
        Rq(out)
    }

    /// Coefficientwise negation (spec: `Rq.lean:111`, coefficientwise by
    /// `neg_val`, `Rq.lean:239`).
    ///
    /// Mirrors ArkLib's `Neg (Rq Φ)` instance.
    ///
    /// Pre-sized to `n` (Stage 6 candidate D2): `Vec::with_capacity` is erased by
    /// the extraction (`alloc.vec.Vec.with_capacity T _ = Vec.new T`), so the model
    /// and its spec are those of the push loop; the capacity spares the ten
    /// reallocations a 1024-word push loop otherwise pays.
    pub fn neg(&self) -> Rq {
        let n: usize = self.0.len();
        let mut out: Vec<Fp> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            out.push(-self.0[i]);
            i += 1;
        }
        Rq(out)
    }

    /// Multiplication by a field scalar.
    ///
    /// Mirrors ArkLib's `Rq.constRq Φ c * x`, multiplication by a ring
    /// constant.
    ///
    /// Spec: multiplication by a constant, `Rq.constRq Φ c * x`, whose
    /// coefficientwise action is `constRq_mul_coeff` (`Rq.lean:369`). Kept as an
    /// operation of its own because the gadget matrix is built entirely from
    /// constants (`gadgetEntry` is `constRq (base ^ e)`), so this is the shape
    /// the gadget product wants -- not a special case anyone has to recognise.
    ///
    /// Pre-sized to `n` (Stage 6 candidate D2): `Vec::with_capacity` is erased by
    /// the extraction (`alloc.vec.Vec.with_capacity T _ = Vec.new T`), so the model
    /// and its spec are those of the push loop; the capacity spares the ten
    /// reallocations a 1024-word push loop otherwise pays.
    pub fn scalar_mul(&self, c: Fp) -> Rq {
        let n: usize = self.0.len();
        let mut out: Vec<Fp> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            out.push(c * self.0[i]);
            i += 1;
        }
        Rq(out)
    }

    /// The negacyclic product (spec: the `Mul (Rq Φ)` instance, `Rq.lean:110`,
    /// which is `reduce (a.val * b.val)`).
    ///
    /// Mirrors ArkLib's `Mul (Rq Φ)` instance.
    ///
    /// The mathematics is unchanged from the schoolbook convolution this
    /// replaced: term `aᵢbⱼ` belongs to slot `i + j` with a `+` and to slot
    /// `i + j − N` with a `−`, because `X^N ≡ −1`. What changed is how the `N²`
    /// products are computed. [`crate::ntt`] computes the same integer
    /// coefficients in `O(N log N)` through three auxiliary prime fields and a
    /// CRT reconstruction, and its module header carries the whole argument:
    /// why `Z_q` has no usable root of unity, why `BOUND = N·q²` is the right
    /// offset, and why the reconstruction is exact rather than merely modular.
    ///
    /// Three loops, and each is a plain pass:
    ///
    /// * read both operands' canonical words (the `Red` invariant is what makes
    ///   `to_u64` the value and not merely a representative);
    /// * call [`crate::ntt::negconv_mod_q`], which returns coefficient `k` of
    ///   the product already reduced mod `q`;
    /// * wrap each word back up as an `Fp`.
    ///
    /// There is no correction term and no second reduction pass: `ntt`'s CRT
    /// offset is a multiple of `q`, so `negconv_mod_q` hands back the
    /// coefficient itself. Every word it returns is below `q`, which is what
    /// makes `Fp::new` the identity on the representation -- and that is
    /// `mul_spec`'s obligation, not an assumption.
    ///
    /// Pre-sized (Stage 6 candidate D2): `Vec::with_capacity` is erased by the
    /// extraction (`alloc.vec.Vec.with_capacity T _ = Vec.new T`), so the model
    /// and its spec are those of the push loop; the capacity spares the ten
    /// reallocations a 1024-word push loop otherwise pays.
    pub fn mul(&self, rhs: &Rq) -> Rq {
        let n: usize = params::RING_DEGREE;
        let mut aw: Vec<u64> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            aw.push(self.0[i].to_u64());
            i += 1;
        }
        let mut bw: Vec<u64> = Vec::with_capacity(n);
        let mut j: usize = 0;
        while j < n {
            bw.push(rhs.0[j].to_u64());
            j += 1;
        }
        let cw: Vec<u64> = crate::ntt::negconv_mod_q(&aw, &bw);
        let mut out: Vec<Fp> = Vec::with_capacity(n);
        let mut k: usize = 0;
        while k < n {
            out.push(Fp::new(cw[k]));
            k += 1;
        }
        Rq(out)
    }
}

// ---------------------------------------------------------------------------
// Multiplication by a short element
// ---------------------------------------------------------------------------

/// A short left operand, described by its nonzero centred coefficients.
///
/// Three parallel vectors rather than a `Vec` of tuples: Aeneas models
/// `Vec::push` / `len` / `index`, and a struct of `Vec`s keeps every field a
/// `@[reducible]` `Vec` alias in the extracted model, which is the shape
/// `Generated.lean`'s existing specs are written about. `idx[t]` is the
/// coefficient position, `mag[t]` its centred magnitude and `neg[t]` its sign
/// (`true` = the centred value is `-mag[t]`).
pub struct ShortMul {
    idx: Vec<usize>,
    mag: Vec<u64>,
    neg: Vec<bool>,
}

impl ShortMul {
    /// How many nonzero coefficients the described element has.
    pub fn terms(&self) -> usize {
        self.idx.len()
    }
}

/// Describe `a` as a short element, or decline.
///
/// Returns `Some(desc)` exactly when `a`'s **centred** `ℓ₁` norm is at most
/// [`params::OMEGA`] -- which is precisely the `ShortChallenge Φ ω` predicate
/// the protocol's challenges satisfy -- and `None` otherwise. Declining is not
/// a failure: [`honest_z`](crate::quadeval::honest_z) falls back to the generic
/// product, so correctness never depends on the classification succeeding.
///
/// The centred representative of a word `c` is `c` when `c ≤ q/2` and
/// `-(q - c)` otherwise; the budget is checked incrementally so a dense input
/// is rejected after ~`OMEGA` nonzero coefficients rather than after `N`.
pub fn classify_short(a: &Rq) -> Option<ShortMul> {
    let n: usize = params::RING_DEGREE;
    let q: u64 = params::Q;
    let half: u64 = q / 2;
    let budget: u64 = params::OMEGA;
    let mut idx: Vec<usize> = Vec::new();
    let mut mag: Vec<u64> = Vec::new();
    let mut neg: Vec<bool> = Vec::new();
    let mut total: u64 = 0;
    let mut k: usize = 0;
    while k < n {
        let c: u64 = a.coeff(k).to_u64();
        if c != 0 {
            let m: u64 = if c <= half { c } else { q - c };
            let s: bool = c > half;
            total = total + m;
            if total > budget {
                return None;
            }
            idx.push(k);
            mag.push(m);
            neg.push(s);
        }
        k += 1;
    }
    Some(ShortMul { idx, mag, neg })
}

/// `desc · s` in `Rq = Z_q[X]/(X^N + 1)`, by signed negacyclic shifts.
///
/// **Nothing multiplies.** Each described term `(k, m, sign)` contributes `m`
/// passes that add (or subtract) the `k`-shifted `s`, and `Σ m ≤ OMEGA = 16`,
/// so the whole product costs at most 16 passes over `N` -- `16 · 1024` modular
/// additions against the three-prime NTT's forward/pointwise/inverse pipeline
/// plus its Garner recombination.
///
/// The negacyclic rule is the only subtle line: `X^N = -1`, so a term whose
/// shifted position `pos = k + i` reaches `N` or beyond lands at `pos - N`
/// **with its sign flipped**.
pub fn mul_short_desc(desc: &ShortMul, s: &Rq) -> Rq {
    let n: usize = params::RING_DEGREE;
    let q: u64 = params::Q;
    let terms: usize = desc.idx.len();
    let mut out: Vec<u64> = Vec::with_capacity(n);
    let mut z: usize = 0;
    while z < n {
        out.push(0);
        z += 1;
    }
    let mut t: usize = 0;
    while t < terms {
        let k: usize = desc.idx[t];
        let m: u64 = desc.mag[t];
        let negt: bool = desc.neg[t];
        let mut pass: u64 = 0;
        while pass < m {
            let mut i: usize = 0;
            while i < n {
                let sv: u64 = s.coeff(i).to_u64();
                if sv != 0 {
                    let pos: usize = k + i;
                    // X^N = -1: crossing the boundary flips the sign
                    let w: usize = if pos >= n { pos - n } else { pos };
                    let wrapped: bool = pos >= n;
                    let sub: bool = negt != wrapped;
                    let cur: u64 = out[w];
                    if sub {
                        out[w] = if cur >= sv { cur - sv } else { cur + q - sv };
                    } else {
                        let sum: u64 = cur + sv;
                        out[w] = if sum >= q { sum - q } else { sum };
                    }
                }
                i += 1;
            }
            pass += 1;
        }
        t += 1;
    }
    let mut res: Vec<Fp> = Vec::with_capacity(n);
    let mut j: usize = 0;
    while j < n {
        res.push(Fp::new(out[j]));
        j += 1;
    }
    Rq(res)
}

/// `acc += desc · s`, in place (spec: the same product
/// [`mul_short_desc`] computes, added to `acc`).
///
/// The allocation-free form of [`mul_short_desc`], for callers that already
/// hold the accumulator. `mul_short_desc` must allocate twice per call -- the
/// `u64` scratch it zero-fills and the `Fp` vector it converts into -- and its
/// caller then allocates a third time to add the result in. At the paper's
/// parameters `honest_z` calls it `MESSAGE_ROWS · GADGET_DIGITS = 8192` times
/// per message block, so those are `16 384` allocations and ~`16.7M` pushes per
/// block that buy nothing: the shift loop can add straight into the
/// accumulator, since adding a shifted copy is what it already does.
///
/// Writes through `&mut Rq`'s own storage rather than a `set_coeff` method,
/// which this module may do and no other may.
pub fn mul_short_add_into(desc: &ShortMul, s: &Rq, acc: &mut Rq) {
    // **The per-term reduction was redundant** (Stage 6 candidate T33).
    //
    // The inner step used to finish with `Fp::new(nv)` on an `nv` the branchy
    // add/sub had already put in `[0, q)`: a `% Q` for nothing, on the hottest
    // loop in the prover. What replaces it is an unreduced `u64` buffer, with
    // a subtraction contributing `q - sv` instead of `-sv` so the accumulator
    // only ever grows and its value mod `q` is the answer -- the offset trick
    // `RingFused.offConvSumD` already uses twice in this tree.
    //
    // A slot grows by at most `q` per pass, so [`params::SHORT_CHUNK`] passes
    // between reductions keep it below `(SHORT_CHUNK + 1)·q`, unconditionally
    // and for any description. At the pin `Σ mag ≤ OMEGA = 16 < 32`, so the
    // inner reduction never fires and the whole call is one deferred pass.
    let n: usize = params::RING_DEGREE;
    let chunk: u64 = params::SHORT_CHUNK;
    let mut buf: Vec<u64> = Vec::with_capacity(n);
    let mut z: usize = 0;
    while z < n {
        buf.push(acc.0[z].to_u64());
        z += 1;
    }
    let terms: usize = desc.idx.len();
    let mut left: u64 = chunk;
    let mut t: usize = 0;
    while t < terms {
        let k: usize = desc.idx[t];
        let m: u64 = desc.mag[t];
        let negt: bool = desc.neg[t];
        let mut pass: u64 = 0;
        while pass < m {
            buf = short_pass_off(s, k, negt, buf);
            if left > 1 {
                left = left - 1;
            } else {
                buf = short_reduce_buf(buf);
                left = chunk;
            }
            pass += 1;
        }
        t += 1;
    }
    let mut w: usize = 0;
    while w < n {
        acc.0[w] = Fp::new(buf[w]);
        w += 1;
    }
}

/// One signed negacyclic pass of [`mul_short_add_into`], scattered into an
/// **unreduced** buffer (Stage 6 candidate T33).
///
/// `acc[(k + i) mod N] += s[i]`, with the sign flipped when the shift crosses
/// the boundary (`X^N = -1`) and a negative contribution added as `q - s[i]`
/// so the buffer never has to borrow. A separate item, and a single loop,
/// because a borrowed read nested inside an accumulator-writing loop is what
/// aeneas aborts on (`aeneas-extract`'s 2026-09-17 row).
fn short_pass_off(s: &Rq, k: usize, negt: bool, acc: Vec<u64>) -> Vec<u64> {
    let n: usize = params::RING_DEGREE;
    let q: u64 = params::Q;
    let mut out: Vec<u64> = acc;
    // `X^N = -1`: the term at `i` lands at `k + i`, and crossing `N` flips its
    // sign. The old shape tested `pos >= n` per element, which put two
    // conditionals and a computed index in the inner loop. The wrap point is
    // known before the loop -- it is `i = n - k` -- so the pass splits into
    // two runs, each with a constant sign and a stride-1 destination:
    //
    //   i <  n-k  ->  out[k + i]     gets  +s[i]  (negated if `negt`)
    //   i >= n-k  ->  out[k + i - n] gets  -s[i]  (negated if `negt`)
    //
    // Both are branch-free over `i`, which is what lets them vectorize; the
    // remaining `if negt` is loop-invariant and unswitches. Measured on the
    // general path's fused NTT (2026-09-20), a stride-1 branch-free run is
    // worth more here than any arithmetic saving.
    //
    // Two shapes are still forced by the extraction, both measured 2026-09-19
    // (`aeneas-extract`'s ceiling table): a negative contribution is added as
    // `q - sv` so the buffer never borrows, and the accumulate reads `out[w]`
    // into a `let` before adding, because `out[w] = out[w] + add` in one
    // expression is an unmodelled binary operation when the element type is a
    // scalar.
    let lim: usize = n - k;
    let mut i: usize = 0;
    while i < lim {
        let sv: u64 = s.0[i].to_u64();
        let add: u64 = if negt { q - sv } else { sv };
        let w: usize = k + i;
        let cur: u64 = out[w];
        let nv: u64 = cur + add;
        out[w] = nv;
        i += 1;
    }
    let mut j: usize = lim;
    while j < n {
        let sv: u64 = s.0[j].to_u64();
        let add: u64 = if negt { sv } else { q - sv };
        let w: usize = j - lim;
        let cur: u64 = out[w];
        let nv: u64 = cur + add;
        out[w] = nv;
        j += 1;
    }
    out
}

/// Every slot of a [`short_pass_off`] buffer, reduced mod `q`.
fn short_reduce_buf(acc: Vec<u64>) -> Vec<u64> {
    let n: usize = params::RING_DEGREE;
    let q: u64 = params::Q;
    let mut out: Vec<u64> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        out.push(acc[i] % q);
        i += 1;
    }
    out
}

// ---------------------------------------------------------------------------
// Fused dot products
// ---------------------------------------------------------------------------

/// How many terms a fused dot accumulates before reducing.
///
/// The transform-domain accumulator holds
/// `Σⱼ posSumⱼ + L·BOUND − Σⱼ negSumⱼ` with `BOUND = N·q²`, which is in
/// `[0, 2·L·BOUND)`. Garner reconstructs only below `P = p₁p₂p₃`, so
/// `2·L·BOUND < P` bounds `L` at **12 468** (checked: 12 469 overflows).
/// `8192` is a power of two comfortably inside that, and is exactly the
/// commitment's own width, so the pin's dots are a single chunk.
///
/// This constant is the whole reason a fused dot is not a drop-in replacement:
/// `rlin_stmt`'s rows are 40 976 wide, three times the bound, and without
/// chunking the reconstruction would be silently wrong there.
pub const DOT_CHUNK: usize = 8192;

/// One chunk of a fused dot product, modulo one auxiliary prime.
///
/// The saving over `negconv_mod_p` per term: the two ψ tables are built once
/// for the whole chunk instead of per product, and there is one inverse
/// transform for the chunk instead of one per product. Per term this leaves
/// twist + forward on each operand and one pointwise multiply -- 13 312 modular
/// multiplies against `negconv_mod_p`'s 21 528.
#[allow(clippy::too_many_arguments)]
pub fn dot_chunk_mod_p(
    a: &Vec<Rq>,
    b: &Vec<Rq>,
    start: usize,
    end: usize,
    p: u64,
    m: u64,
    psi: u64,
    psiinv: u64,
    ninv: u64,
    boff: u64,
) -> Vec<u64> {
    let n: usize = crate::ntt::NTT_LEN;
    let pt: Vec<u64> = crate::ntt::psi_table(psi, p, m);
    let it: Vec<u64> = crate::ntt::psi_table(psiinv, p, m);
    let mut acc: Vec<u64> = crate::ntt::zeros(n);
    let mut scratch: Vec<u64> = crate::ntt::zeros(n);
    let mut j: usize = start;
    while j < end {
        let mut aw: Vec<u64> = Vec::with_capacity(n);
        let mut t: usize = 0;
        while t < n {
            aw.push(a[j].0[t].to_u64());
            t += 1;
        }
        let mut bw: Vec<u64> = Vec::with_capacity(n);
        let mut u: usize = 0;
        while u < n {
            bw.push(b[j].0[u].to_u64());
            u += 1;
        }
        let ta: Vec<u64> = crate::ntt::twist(&aw, &pt, p, m);
        let fwa: (Vec<u64>, Vec<u64>) = crate::ntt::ntt_forward(ta, scratch, &pt, p, m);
        let tb: Vec<u64> = crate::ntt::twist(&bw, &pt, p, m);
        let fwb: (Vec<u64>, Vec<u64>) = crate::ntt::ntt_forward(tb, fwa.1, &pt, p, m);
        let prod: Vec<u64> = crate::ntt::pointwise(fwa.0, &fwb.0, p, m);
        let mut k: usize = 0;
        while k < n {
            acc[k] = crate::ntt::aux_add(acc[k], prod[k], p);
            k += 1;
        }
        scratch = fwb.1;
        j += 1;
    }
    // ONE offset per accumulated term, not one per chunk: see DOT_CHUNK.
    let len: u64 = (end - start) as u64;
    let scaled: u64 = crate::ntt::aux_mul(boff, len, p, m);
    let inv: (Vec<u64>, Vec<u64>) = crate::ntt::ntt_inverse(acc, scratch, &it, p, m);
    crate::ntt::untwist(&inv.0, &it, ninv, scaled, p, m)
}

/// `Σⱼ a[j] · b[j]` in `Rq`, fused: one inverse transform and one Garner pass
/// per chunk of [`DOT_CHUNK`] terms instead of one per term.
pub fn dot_fused(a: &Vec<Rq>, b: &Vec<Rq>, n: usize) -> Rq {
    let deg: usize = params::RING_DEGREE;
    let qw: u128 = params::Q as u128;
    let mut acc: Rq = Rq::zero();
    let mut start: usize = 0;
    while start < n {
        // `start + take` rather than `min(start + DOT_CHUNK, n)`: the latter can
        // overflow `usize` for an absurd `n`, which would force every caller of
        // `PolyVec::dot` to carry a headroom precondition -- and three of them
        // are generic in the width, so it would cascade. Taking the remainder
        // first bounds the sum by `n` and needs nothing from the caller.
        let remaining: usize = n - start;
        let take: usize = if remaining < DOT_CHUNK { remaining } else { DOT_CHUNK };
        let end: usize = start + take;
        let r1: Vec<u64> = dot_chunk_mod_p(a, b, start, end, crate::ntt::AUX_P1,
            crate::ntt::AUX_M1, crate::ntt::AUX_PSI1, crate::ntt::AUX_PSIINV1,
            crate::ntt::AUX_NINV1, crate::ntt::AUX_BOFF1);
        let r2: Vec<u64> = dot_chunk_mod_p(a, b, start, end, crate::ntt::AUX_P2,
            crate::ntt::AUX_M2, crate::ntt::AUX_PSI2, crate::ntt::AUX_PSIINV2,
            crate::ntt::AUX_NINV2, crate::ntt::AUX_BOFF2);
        let r3: Vec<u64> = dot_chunk_mod_p(a, b, start, end, crate::ntt::AUX_P3,
            crate::ntt::AUX_M3, crate::ntt::AUX_PSI3, crate::ntt::AUX_PSIINV3,
            crate::ntt::AUX_NINV3, crate::ntt::AUX_BOFF3);
        let mut out: Vec<Fp> = Vec::with_capacity(deg);
        let mut t: usize = 0;
        while t < deg {
            out.push(Fp::new((crate::ntt::garner(r1[t], r2[t], r3[t]) % qw) as u64));
            t += 1;
        }
        acc = acc.add(&Rq(out));
        start = end;
    }
    acc
}

// ---------------------------------------------------------------------------
// The compact raw carrier
// ---------------------------------------------------------------------------

/// A ring element held as `u32` words: half the bytes of [`Rq`].
///
/// Every coefficient of a well-formed `Rq` is a canonical residue below
/// `q = 2^32 - 99`, so it fits a `u32` exactly. This carrier exists for the
/// **raw message only** -- `BLOCKS * MESSAGE_ROWS * RING_DEGREE * 8 B` = 8 GiB
/// at the paper's parameters, about half the measured peak -- and
/// `Rq(Vec<Fp>)` is not replaced anywhere else. Nothing computes in this
/// representation: [`RawRq32::expand`] is the only way out of it, and every
/// consumer expands one block at a time.
///
/// The narrowing in [`RawRq32::compact`] is *fallible in the extracted model*
/// (`lift (UScalar.cast .U32 ...)`, measured in `probe-t29/`), and its side
/// condition is exactly `Field.Red` -- which every `Wf` operand already
/// carries, so it costs no new precondition. The widening in `expand` is pure.
pub struct RawRq32(Vec<u32>);

impl RawRq32 {
    /// Compact a reduced ring element. Total: `Rq::coeff` reads `0` past the end.
    pub fn compact(a: &Rq) -> RawRq32 {
        let n: usize = params::RING_DEGREE;
        let mut words: Vec<u32> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            words.push(a.coeff(i).to_u64() as u32);
            i += 1;
        }
        RawRq32(words)
    }

    /// The ring element back. Total: `Rq::from_coeffs` pads and truncates.
    pub fn expand(&self) -> Rq {
        let n: usize = self.0.len();
        let mut cs: Vec<Fp> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n {
            cs.push(Fp::new(self.0[i] as u64));
            i += 1;
        }
        Rq::from_coeffs(&cs)
    }
}

// ---------------------------------------------------------------------------
// A prepared left operand
// ---------------------------------------------------------------------------

/// One operand of a dot product, forward-transformed under all three auxiliary
/// primes and kept.
///
/// Three separate stores rather than one interleaved buffer: the primes are
/// individual constants, not an indexable table, so a loop over them would need
/// a lookup Aeneas has no model for. Each store is `len * NTT_LEN` words.
pub struct PreparedVec {
    len: usize,
    fwd1: Vec<u64>,
    fwd2: Vec<u64>,
    fwd3: Vec<u64>,
}

impl PreparedVec {
    /// How many entries were prepared.
    pub fn len(&self) -> usize {
        self.len
    }
}

/// Forward-transform every entry of `a` under one prime, concatenated.
#[allow(clippy::too_many_arguments)]
pub fn prepare_one(a: &Vec<Rq>, n: usize, p: u64, m: u64, psi: u64) -> Vec<u64> {
    let deg: usize = crate::ntt::NTT_LEN;
    let pt: Vec<u64> = crate::ntt::psi_table(psi, p, m);
    let mut out: Vec<u64> = Vec::with_capacity(n * deg);
    let mut j: usize = 0;
    while j < n {
        let mut w: Vec<u64> = Vec::with_capacity(deg);
        let mut t: usize = 0;
        while t < deg {
            w.push(a[j].0[t].to_u64());
            t += 1;
        }
        let scratch: Vec<u64> = crate::ntt::zeros(deg);
        let tw: Vec<u64> = crate::ntt::twist(&w, &pt, p, m);
        let f: (Vec<u64>, Vec<u64>) = crate::ntt::ntt_forward(tw, scratch, &pt, p, m);
        let mut k: usize = 0;
        while k < deg {
            out.push(f.0[k]);
            k += 1;
        }
        j += 1;
    }
    out
}

/// Forward-transform every entry of `a`, once, and keep the result.
///
/// **Only worth doing for an operand reused across many dot products.** The
/// store is `n * 3 * NTT_LEN * 8` bytes = `n * 24 KiB`: at the inner Ajtai
/// matrix's `n = MESSAGE_ROWS * GADGET_DIGITS = 8192` that is 192 MiB, computed
/// once and applied to all `BLOCKS` message blocks. Applied to a vector used
/// *once* it is strictly worse than [`dot_fused`], because it does the same
/// transforms and then holds them.
///
/// For scale: `rlin_stmt`'s `M` is `5 x 40976`, which would be **4.8 GiB**.
/// Nothing mechanical stops a caller preparing that; this comment is the guard.
pub fn prepare_vec(a: &Vec<Rq>, n: usize) -> PreparedVec {
    let fwd1: Vec<u64> = prepare_one(a, n, crate::ntt::AUX_P1, crate::ntt::AUX_M1,
        crate::ntt::AUX_PSI1);
    let fwd2: Vec<u64> = prepare_one(a, n, crate::ntt::AUX_P2, crate::ntt::AUX_M2,
        crate::ntt::AUX_PSI2);
    let fwd3: Vec<u64> = prepare_one(a, n, crate::ntt::AUX_P3, crate::ntt::AUX_M3,
        crate::ntt::AUX_PSI3);
    PreparedVec { len: n, fwd1, fwd2, fwd3 }
}

/// `pfwd`'s `n` words starting at `base`, copied out.
///
/// A function of its own rather than a loop inside
/// [`dot_prep_chunk_mod_p`]: reading a borrowed buffer inside a loop that also
/// writes an accumulator makes the pinned Aeneas abort in
/// `filter_loop_useless_inputs_outputs` (measured 2026-09-17,
/// `nightly-2026.07.26-3a8586f`), and there is no fork here to patch.
pub fn slice_out(pfwd: &Vec<u64>, base: usize, n: usize) -> Vec<u64> {
    let mut out: Vec<u64> = Vec::with_capacity(n);
    let mut c: usize = 0;
    while c < n {
        out.push(pfwd[base + c]);
        c += 1;
    }
    out
}

/// `acc += af ∘ bf` pointwise, modulo `p`.
///
/// The multiply-accumulate the prepared dot spends all its time in, factored
/// out for the same extraction reason as [`slice_out`].
pub fn mac_into(acc: Vec<u64>, af: &Vec<u64>, bf: &Vec<u64>, n: usize, p: u64, m: u64)
    -> Vec<u64> {
    let mut out: Vec<u64> = acc;
    let mut k: usize = 0;
    while k < n {
        let prod: u64 = crate::ntt::aux_mul(af[k], bf[k], p, m);
        out[k] = crate::ntt::aux_add(out[k], prod, p);
        k += 1;
    }
    out
}

/// One chunk of a dot product against a prepared left operand, modulo one
/// auxiliary prime.
///
/// [`dot_chunk_mod_p`] without the left operand's twist and forward transform:
/// those are read out of `pfwd` instead. That is the whole of Change 4 --
/// `7168` modular multiplies per term per prime against the fused dot's
/// `13 312` and the unfused `21 528`.
#[allow(clippy::too_many_arguments)]
pub fn dot_prep_chunk_mod_p(
    pfwd: &Vec<u64>,
    b: &Vec<Rq>,
    start: usize,
    end: usize,
    p: u64,
    m: u64,
    psi: u64,
    psiinv: u64,
    ninv: u64,
    boff: u64,
) -> Vec<u64> {
    let n: usize = crate::ntt::NTT_LEN;
    let pt: Vec<u64> = crate::ntt::psi_table(psi, p, m);
    let it: Vec<u64> = crate::ntt::psi_table(psiinv, p, m);
    let mut acc: Vec<u64> = crate::ntt::zeros(n);
    let mut scratch: Vec<u64> = crate::ntt::zeros(n);
    let mut j: usize = start;
    while j < end {
        let mut bw: Vec<u64> = Vec::with_capacity(n);
        let mut u: usize = 0;
        while u < n {
            bw.push(b[j].0[u].to_u64());
            u += 1;
        }
        let tb: Vec<u64> = crate::ntt::twist(&bw, &pt, p, m);
        let fwb: (Vec<u64>, Vec<u64>) = crate::ntt::ntt_forward(tb, scratch, &pt, p, m);
        // `j * n` is an ABSOLUTE offset: `pfwd` holds every prepared entry, not
        // just this chunk's. Using a position-within-chunk offset here is the one
        // mistake preparation can make that the unprepared path cannot, and the
        // semantics oracle is checked to catch it at the first multi-chunk width.
        let af: Vec<u64> = slice_out(pfwd, j * n, n);
        acc = mac_into(acc, &af, &fwb.0, n, p, m);
        scratch = fwb.1;
        j += 1;
    }
    let len: u64 = (end - start) as u64;
    let scaled: u64 = crate::ntt::aux_mul(boff, len, p, m);
    let inv: (Vec<u64>, Vec<u64>) = crate::ntt::ntt_inverse(acc, scratch, &it, p, m);
    crate::ntt::untwist(&inv.0, &it, ninv, scaled, p, m)
}

/// One chunk of the fused dot in the **Goldilocks** lane, on the general path.
///
/// [`dot_prep_chunk_mod_p`]'s body with the Goldilocks operations in place of
/// the Barrett ones and [`crate::ntt::GOLD_BOFF`] as the offset. The lane
/// carries one of the two residues [`crate::ntt::garner_ga`] reconstructs
/// from; it does not have to hold the whole sum, only the sum mod `GOLD_P`.
pub fn dot_prep_chunk_gold(
    pfwd: &Vec<u64>,
    b: &Vec<Rq>,
    start: usize,
    end: usize,
    boff: u64,
) -> Vec<u64> {
    let n: usize = crate::ntt::NTT_LEN;
    let pt: Vec<u64> = crate::ntt::gold_psi_table(crate::ntt::GOLD_PSI);
    let it: Vec<u64> = crate::ntt::gold_psi_table(crate::ntt::GOLD_PSIINV);
    let mut acc: Vec<u64> = crate::ntt::zeros(n);
    let mut scratch: Vec<u64> = crate::ntt::zeros(n);
    let mut j: usize = start;
    while j < end {
        let mut bw: Vec<u64> = Vec::with_capacity(n);
        let mut u: usize = 0;
        while u < n {
            bw.push(b[j].0[u].to_u64());
            u += 1;
        }
        let tb: Vec<u64> = crate::ntt::gold_twist(&bw, &pt);
        let fwb: (Vec<u64>, Vec<u64>) = crate::ntt::gold_forward(tb, scratch, &pt);
        let af: Vec<u64> = slice_out(pfwd, j * n, n);
        acc = mac_into_gold(acc, &af, &fwb.0, n);
        scratch = fwb.1;
        j += 1;
    }
    let len: u64 = (end - start) as u64;
    let scaled: u64 = crate::ntt::gold_mul(boff, len);
    let inv: (Vec<u64>, Vec<u64>) = crate::ntt::gold_inverse(acc, scratch, &it);
    crate::ntt::gold_untwist_off(&inv.0, &it, scaled)
}

/// A left operand prepared for the general path in **two** lanes: one
/// Goldilocks and one 31-bit Barrett (candidate G2).
///
/// The three-lane [`PreparedVec`] stays where it is, dead but proved, for the
/// same reason `dot_prepared_digits` did after T27: re-proving a superseded
/// path buys nothing.
pub struct PreparedVecGA {
    len: usize,
    fwd_g: Vec<u64>,
    fwd_a: Vec<u64>,
}

impl PreparedVecGA {
    /// How many entries were prepared.
    pub fn len(&self) -> usize {
        self.len
    }
}

/// Prepare a left operand in the general path's two lanes.
pub fn prepare_vec_ga(a: &Vec<Rq>, n: usize) -> PreparedVecGA {
    let fwd_g: Vec<u64> = prepare_one_gold(a, n);
    let fwd_a: Vec<u64> = prepare_one(a, n, crate::ntt::AUX_P1, crate::ntt::AUX_M1,
        crate::ntt::AUX_PSI1);
    PreparedVecGA { len: n, fwd_g, fwd_a }
}

/// `Σⱼ a[j] · b[j]` with `a` prepared, in **two** lanes instead of three
/// (candidate G2).
///
/// The same value [`dot_prepared`] computes. What changes is the lane count
/// and the arithmetic in one of them: the general path's chunk bound is
/// `N·cols·(q−1)² ≈ 2^87`, three 31-bit primes give `2^93`, and
/// `GOLD_P · AUX_P1` gives `2^92.8` — the same margin from two lanes. The
/// Goldilocks lane is the one the digit path already uses, so it arrives with
/// its fused radix-4 transform; the second lane is `AUX_P1` unchanged.
///
/// This is the card the board priced at 2500–3500 lines and a Montgomery
/// representation change. That estimate assumed two *64-bit* lanes, which the
/// bound does not require.
pub fn dot_prepared_ga(prep: &PreparedVecGA, b: &Vec<Rq>, n: usize) -> Rq {
    let deg: usize = params::RING_DEGREE;
    let qw: u128 = params::Q as u128;
    let mut acc: Rq = Rq::zero();
    let mut start: usize = 0;
    while start < n {
        let remaining: usize = n - start;
        let take: usize = if remaining < DOT_CHUNK { remaining } else { DOT_CHUNK };
        let end: usize = start + take;
        let rg: Vec<u64> = dot_prep_chunk_gold(&prep.fwd_g, b, start, end,
            crate::ntt::GOLD_BOFF);
        let ra: Vec<u64> = dot_prep_chunk_mod_p(&prep.fwd_a, b, start, end,
            crate::ntt::AUX_P1, crate::ntt::AUX_M1, crate::ntt::AUX_PSI1,
            crate::ntt::AUX_PSIINV1, crate::ntt::AUX_NINV1, crate::ntt::AUX_BOFF1);
        let mut out: Vec<Fp> = Vec::with_capacity(deg);
        let mut t: usize = 0;
        while t < deg {
            out.push(Fp::new((crate::ntt::garner_ga(rg[t], ra[t]) % qw) as u64));
            t += 1;
        }
        acc = acc.add(&Rq(out));
        start = end;
    }
    acc
}

/// The chunk width of the **bounded** fused dot, where one operand's
/// coefficients are gadget digits.
///
/// The ceiling is `2 · L · BOUND_D < p1 · p2` with `BOUND_D = N · GADGET_BASE ·
/// Q`, i.e. `L ≤ 3332`; a signed convolution coefficient over `L` terms is at
/// most `L · N · (Q−1) · 15` in absolute value, so at `L = 3332` the shifted
/// value is `454 283 009 702 445 056` against a radix of
/// `468 937 312 667 959 297`. This is the largest power of two below that
/// ceiling, which leaves a 1.6x margin: the ceiling moves with `Q` and
/// `GADGET_BASE`, and a chunk boundary is the wrong place to be exactly tight.
///
/// Four chunks at the inner matrix's width of 8192. The extra chunk boundaries
/// cost one inverse transform and one untwist each -- about 57 000 modular
/// multiplies over the whole product against the 117 million the terms cost, so
/// 0.05%.
pub const DOT_CHUNK_D: usize = 2048;

/// Forward-transform every entry of `a` under **two** primes.
///
/// For the bounded dot only. `fwd3` is left empty, which is what makes the store
/// 128 MiB rather than 192 MiB for the inner matrix; nothing reads it, and
/// [`dot_prepared_digits`] is the only consumer.
pub fn prepare_vec_two(a: &Vec<Rq>, n: usize) -> PreparedVec {
    let fwd1: Vec<u64> = prepare_one(a, n, crate::ntt::AUX_P1, crate::ntt::AUX_M1,
        crate::ntt::AUX_PSI1);
    let fwd2: Vec<u64> = prepare_one(a, n, crate::ntt::AUX_P2, crate::ntt::AUX_M2,
        crate::ntt::AUX_PSI2);
    let fwd3: Vec<u64> = Vec::new();
    PreparedVec { len: n, fwd1, fwd2, fwd3 }
}

/// `Σⱼ a[j] · b[j]` with `a` prepared and **`b`'s coefficients bounded by
/// `GADGET_BASE`** -- the same value [`dot_prepared`] computes, under two primes
/// instead of three.
///
/// **This is only correct for a `b` whose every coefficient is below
/// [`crate::params::GADGET_BASE`]**, which is what the unsigned gadget
/// decomposition produces. It is a separate function rather than a branch
/// because the precondition is on values, not on types: a caller that hands it
/// an arbitrary `b` gets a wrong answer with no complaint from the compiler.
/// [`crate::linalg::PreparedMatrix::apply_digits`] is the only caller, and
/// `commit::generate_decomps` applies it to `G⁻¹(m)`.
///
/// The saving is one third of the per-term work: 7168 modular multiplies per
/// term per prime (a twist, a forward transform, a pointwise multiply-add), so
/// 14336 rather than 21504.
///
/// The *balanced* decomposition does not qualify: its digits are centred, so a
/// negative digit is the `Fp` word `q − |d|`, and the bound is two-sided.
pub fn dot_prepared_digits(prep: &PreparedVec, b: &Vec<Rq>, n: usize) -> Rq {
    let deg: usize = params::RING_DEGREE;
    let qw: u64 = params::Q;
    let mut acc: Rq = Rq::zero();
    let mut start: usize = 0;
    while start < n {
        let remaining: usize = n - start;
        let take: usize = if remaining < DOT_CHUNK_D { remaining } else { DOT_CHUNK_D };
        let end: usize = start + take;
        let r1: Vec<u64> = dot_prep_chunk_mod_p(&prep.fwd1, b, start, end,
            crate::ntt::AUX_P1, crate::ntt::AUX_M1, crate::ntt::AUX_PSI1,
            crate::ntt::AUX_PSIINV1, crate::ntt::AUX_NINV1, crate::ntt::AUX_DOFF1);
        let r2: Vec<u64> = dot_prep_chunk_mod_p(&prep.fwd2, b, start, end,
            crate::ntt::AUX_P2, crate::ntt::AUX_M2, crate::ntt::AUX_PSI2,
            crate::ntt::AUX_PSIINV2, crate::ntt::AUX_NINV2, crate::ntt::AUX_DOFF2);
        let mut out: Vec<Fp> = Vec::with_capacity(deg);
        let mut t: usize = 0;
        while t < deg {
            out.push(Fp::new(crate::ntt::garner2(r1[t], r2[t]) % qw));
            t += 1;
        }
        acc = acc.add(&Rq(out));
        start = end;
    }
    acc
}

/// A left operand prepared in the **single Goldilocks lane** (candidate T27).
///
/// One forward table where [`PreparedVec`] holds two or three, so the prepared
/// matrix halves as well: 64 MiB rather than 128 at the inner width.
pub struct PreparedVecG {
    len: usize,
    fwd: Vec<u64>,
}

impl PreparedVecG {
    /// How many entries were prepared.
    pub fn len(&self) -> usize {
        self.len
    }
}

/// Forward-transform every entry of `a` in the Goldilocks lane.
pub fn prepare_one_gold(a: &Vec<Rq>, n: usize) -> Vec<u64> {
    let deg: usize = params::RING_DEGREE;
    let pt: Vec<u64> = crate::ntt::gold_psi_table(crate::ntt::GOLD_PSI);
    let mut out: Vec<u64> = Vec::with_capacity(n * deg);
    let mut j: usize = 0;
    while j < n {
        let mut w: Vec<u64> = Vec::with_capacity(deg);
        let mut u: usize = 0;
        while u < deg {
            w.push(a[j].0[u].to_u64());
            u += 1;
        }
        let tw: Vec<u64> = crate::ntt::gold_twist(&w, &pt);
        let scratch: Vec<u64> = crate::ntt::zeros(deg);
        let f: (Vec<u64>, Vec<u64>) = crate::ntt::gold_forward(tw, scratch, &pt);
        let mut k: usize = 0;
        while k < deg {
            out.push(f.0[k]);
            k += 1;
        }
        j += 1;
    }
    out
}

/// Prepare a left operand in the single Goldilocks lane.
pub fn prepare_vec_gold(a: &Vec<Rq>, n: usize) -> PreparedVecG {
    let fwd: Vec<u64> = prepare_one_gold(a, n);
    PreparedVecG { len: n, fwd }
}

/// `Σⱼ a[j] · b[j]` with `a` prepared and `b`'s coefficients bounded by
/// [`params::GADGET_BASE`], in **one** Goldilocks lane (candidate T27).
///
/// The same value [`dot_prepared_digits`] computes, and the same precondition:
/// this is only correct for a `b` the unsigned gadget decomposition produced.
///
/// What one lane changes is everything around the arithmetic. The two-prime
/// path chunks at [`DOT_CHUNK_D`] because `2·L·BOUND_D` must stay below
/// `p1·p2`; here the bound is `1.081·10^18` against `1.845·10^19` for the
/// whole 8192-term width, so there is **one chunk**, **one inverse transform**,
/// **one untwist**, and **no CRT reconstruction at all** — [`crate::ntt::
/// garner2`] does not run, and the centred lift replaces the offset. Measured
/// 158.61 ns per coefficient against 479.64, −66.9%.
pub fn dot_prepared_digits_gold(prep: &PreparedVecG, b: &Vec<Rq>, n: usize) -> Rq {
    let deg: usize = params::RING_DEGREE;
    let qw: u64 = params::Q;
    let pt: Vec<u64> = crate::ntt::gold_psi_table(crate::ntt::GOLD_PSI);
    let it: Vec<u64> = crate::ntt::gold_psi_table(crate::ntt::GOLD_PSIINV);
    let mut acc: Vec<u64> = crate::ntt::zeros(deg);
    let mut scratch: Vec<u64> = crate::ntt::zeros(deg);
    // Card T34, part 1C: a third buffer, recycled from the previous
    // iteration's transform output, so the loop allocates nothing per
    // polynomial. `gold_forward` already threads its scratch pair; this
    // extends the same discipline to the twist input.
    let mut buf: Vec<u64> = crate::ntt::zeros(deg);
    let mut j: usize = 0;
    while j < n {
        buf = load_twisted_into(buf, &b[j], &pt);
        let fwb: (Vec<u64>, Vec<u64>) = crate::ntt::gold_forward(buf, scratch, &pt);
        // `j * deg` is an ABSOLUTE offset into the prepared table, exactly as
        // `dot_prep_chunk_mod_p` does it. Card T34 part 1B: the offset is the
        // helper's argument now, so the 8 KiB `slice_out` copy is gone. The
        // tuple's part is still bound out before the call rather than indexed
        // in place -- indexing `fwb.0[k]` inside this loop is what made aeneas
        // report "Not an open binder or an ignored pattern".
        acc = mac_into_gold_off(acc, &prep.fwd, j * deg, &fwb.0, deg);
        buf = fwb.0;
        scratch = fwb.1;
        j += 1;
    }
    // the offset is one per term, exactly as `dot_prep_chunk_mod_p` scales
    // `boff` by the chunk length
    let scaled: u64 = crate::ntt::gold_mul(crate::ntt::GOLD_DOFF, n as u64);
    let inv: (Vec<u64>, Vec<u64>) = crate::ntt::gold_inverse(acc, scratch, &it);
    let words: Vec<u64> = crate::ntt::gold_untwist_off(&inv.0, &it, scaled);
    let mut out: Vec<Fp> = Vec::with_capacity(deg);
    let mut t: usize = 0;
    while t < deg {
        out.push(Fp::new(words[t] % qw));
        t += 1;
    }
    Rq(out)
}

/// Load a ring element's canonical words into `out`, already ψ-twisted
/// (card T34, part 1A+1C).
///
/// Two passes become one and the buffer is the caller's. The old shape --
/// `w = Vec::with_capacity(n)` filled by `to_u64`, then
/// [`crate::ntt::gold_twist`] returning a second fresh `Vec` -- allocated
/// 2 x 8 KiB per right-hand polynomial and walked the words twice. Here the
/// twist happens where the word is read, into a buffer the prepared dot
/// recycles from the previous iteration's transform output.
///
/// `out` is overwritten, not appended to, so it arrives at length
/// [`crate::ntt::NTT_LEN`] and leaves at it; the loop writes every index.
pub fn load_twisted_into(out: Vec<u64>, a: &Rq, pt: &Vec<u64>) -> Vec<u64> {
    let n: usize = crate::ntt::NTT_LEN;
    let mut w: Vec<u64> = out;
    let mut t: usize = 0;
    while t < n {
        w[t] = crate::ntt::gold_mul(a.0[t].to_u64(), pt[t]);
        t += 1;
    }
    w
}

/// `acc[k] += pfwd[base + k] · bf[k]` in the Goldilocks lane, reading the
/// prepared table in place (card T34, part 1B).
///
/// [`mac_into_gold`] takes its left factor as a vector, so the prepared dot
/// had to copy 8 KiB out of the prepared table with [`slice_out`] on every
/// right-hand polynomial. The offset moves into the index instead. This is a
/// *separate helper* and not an offset index written into the caller's loop,
/// because a borrowed read beside a mutated accumulator in one loop body is
/// what tripped `filter_loop_useless_inputs_outputs` before; behind a helper
/// boundary it extracts to the ordinary 2-tuple loop, probed 2026-09-21
/// (`aeneas-extract` ceiling table).
///
/// [`slice_out`] stays: the mod-p lane and the general path still use it.
pub fn mac_into_gold_off(acc: Vec<u64>, pfwd: &Vec<u64>, base: usize, bf: &Vec<u64>, n: usize)
    -> Vec<u64> {
    let mut out: Vec<u64> = acc;
    let mut k: usize = 0;
    while k < n {
        let prod: u64 = crate::ntt::gold_mul(pfwd[base + k], bf[k]);
        out[k] = crate::ntt::gold_add(out[k], prod);
        k += 1;
    }
    out
}

/// `acc[k] += af[k] · bf[k]` in the Goldilocks lane, the counterpart of
/// [`mac_into`].
pub fn mac_into_gold(acc: Vec<u64>, af: &Vec<u64>, bf: &Vec<u64>, n: usize) -> Vec<u64> {
    let mut out: Vec<u64> = acc;
    let mut k: usize = 0;
    while k < n {
        let prod: u64 = crate::ntt::gold_mul(af[k], bf[k]);
        out[k] = crate::ntt::gold_add(out[k], prod);
        k += 1;
    }
    out
}

/// `Σⱼ a[j] · b[j]` with `a` prepared: the same value [`dot_fused`] computes.
pub fn dot_prepared(prep: &PreparedVec, b: &Vec<Rq>, n: usize) -> Rq {
    let deg: usize = params::RING_DEGREE;
    let qw: u128 = params::Q as u128;
    let mut acc: Rq = Rq::zero();
    let mut start: usize = 0;
    while start < n {
        let remaining: usize = n - start;
        let take: usize = if remaining < DOT_CHUNK { remaining } else { DOT_CHUNK };
        let end: usize = start + take;
        let r1: Vec<u64> = dot_prep_chunk_mod_p(&prep.fwd1, b, start, end,
            crate::ntt::AUX_P1, crate::ntt::AUX_M1, crate::ntt::AUX_PSI1,
            crate::ntt::AUX_PSIINV1, crate::ntt::AUX_NINV1, crate::ntt::AUX_BOFF1);
        let r2: Vec<u64> = dot_prep_chunk_mod_p(&prep.fwd2, b, start, end,
            crate::ntt::AUX_P2, crate::ntt::AUX_M2, crate::ntt::AUX_PSI2,
            crate::ntt::AUX_PSIINV2, crate::ntt::AUX_NINV2, crate::ntt::AUX_BOFF2);
        let r3: Vec<u64> = dot_prep_chunk_mod_p(&prep.fwd3, b, start, end,
            crate::ntt::AUX_P3, crate::ntt::AUX_M3, crate::ntt::AUX_PSI3,
            crate::ntt::AUX_PSIINV3, crate::ntt::AUX_NINV3, crate::ntt::AUX_BOFF3);
        let mut out: Vec<Fp> = Vec::with_capacity(deg);
        let mut t: usize = 0;
        while t < deg {
            out.push(Fp::new((crate::ntt::garner(r1[t], r2[t], r3[t]) % qw) as u64));
            t += 1;
        }
        acc = acc.add(&Rq(out));
        start = end;
    }
    acc
}

// ---------------------------------------------------------------------------
// Card T35: the general path by limb decomposition (PROTOTYPE, 2026-09-21)
// ---------------------------------------------------------------------------

/// One limb of a left operand: coefficient `c` becomes `(c / div) % base`.
///
/// Division rather than a shift because a shift with a *runtime* amount is not
/// on the extraction's measured list, and `/` and `%` by a runtime `u64` are
/// (the gadget decomposition is the same shape). The divisors here are powers
/// of two, so the compiler emits the shift regardless.
pub fn limb_at(a: &Vec<Rq>, n: usize, div: u64, base: u64) -> Vec<Rq> {
    let deg: usize = params::RING_DEGREE;
    let mut out: Vec<Rq> = Vec::with_capacity(n);
    let mut j: usize = 0;
    while j < n {
        let mut c: Vec<Fp> = Vec::with_capacity(deg);
        let mut u: usize = 0;
        while u < deg {
            c.push(Fp::new((a[j].0[u].to_u64() / div) % base));
            u += 1;
        }
        out.push(Rq(c));
        j += 1;
    }
    out
}

/// `N · q · 2^16`, the per-term offset of the two-limb split. A multiple of
/// `q`, so `% q` at the end is unaffected by it -- the same trick
/// [`crate::ntt::GOLD_DOFF`] plays on the digit path.
pub const GOLD_LOFF2: u64 = 288_230_369_507_934_208;
/// Terms per chunk at two limbs: `2·C·N·B·q < GOLD_P` with `B = 2^16` gives
/// `C ≤ 32`.
pub const LIMB2_CHUNK: usize = 32;
/// A left operand split into two 16-bit limbs, each prepared in the
/// Goldilocks lane (card T35, variant 2A).
pub struct PreparedVecL2 {
    len: usize,
    f0: Vec<u64>,
    f1: Vec<u64>,
}

impl PreparedVecL2 {
    /// How many entries were prepared.
    pub fn len(&self) -> usize {
        self.len
    }
}

/// Prepare a left operand as two 16-bit limbs.
pub fn prepare_vec_limbs2(a: &Vec<Rq>, n: usize) -> PreparedVecL2 {
    let l0: Vec<Rq> = limb_at(a, n, 1, 65536);
    let l1: Vec<Rq> = limb_at(a, n, 65536, 65536);
    PreparedVecL2 { len: n, f0: prepare_one_gold(&l0, n), f1: prepare_one_gold(&l1, n) }
}

/// One chunk of the two-limb fused dot: the right operand is transformed
/// **once** and multiply-accumulated into both limb accumulators.
///
/// This is the whole card in one function. The three-prime path transforms
/// `b[j]` in each of its lanes; here there is one lane and one transform, and
/// the limbs cost a MAC each -- `N` multiplications against a transform's
/// `N log N`.
pub fn dot_prep_chunk_limbs2(
    f0: &Vec<u64>,
    f1: &Vec<u64>,
    b: &Vec<Rq>,
    start: usize,
    end: usize,
    boff: u64,
) -> (Vec<u64>, Vec<u64>) {
    let n: usize = crate::ntt::NTT_LEN;
    let pt: Vec<u64> = crate::ntt::gold_psi_table(crate::ntt::GOLD_PSI);
    let it: Vec<u64> = crate::ntt::gold_psi_table(crate::ntt::GOLD_PSIINV);
    let mut acc0: Vec<u64> = crate::ntt::zeros(n);
    let mut acc1: Vec<u64> = crate::ntt::zeros(n);
    let mut scratch: Vec<u64> = crate::ntt::zeros(n);
    let mut buf: Vec<u64> = crate::ntt::zeros(n);
    let mut j: usize = start;
    while j < end {
        buf = load_twisted_into(buf, &b[j], &pt);
        let fwb: (Vec<u64>, Vec<u64>) = crate::ntt::gold_forward(buf, scratch, &pt);
        acc0 = mac_into_gold_off(acc0, f0, j * n, &fwb.0, n);
        acc1 = mac_into_gold_off(acc1, f1, j * n, &fwb.0, n);
        buf = fwb.0;
        scratch = fwb.1;
        j += 1;
    }
    let len: u64 = (end - start) as u64;
    let scaled: u64 = crate::ntt::gold_mul(boff, len);
    let inv0: (Vec<u64>, Vec<u64>) = crate::ntt::gold_inverse(acc0, scratch, &it);
    let w0: Vec<u64> = crate::ntt::gold_untwist_off(&inv0.0, &it, scaled);
    let inv1: (Vec<u64>, Vec<u64>) = crate::ntt::gold_inverse(acc1, inv0.1, &it);
    let w1: Vec<u64> = crate::ntt::gold_untwist_off(&inv1.0, &it, scaled);
    (w0, w1)
}

/// `Σⱼ a[j] · b[j]` with `a` prepared as two 16-bit limbs (card T35, 2A).
///
/// The value [`dot_prepared`] computes, by a different route: one Goldilocks
/// lane instead of three 31-bit ones, no Garner reconstruction, and the right
/// operand transformed once rather than three times.
pub fn dot_prepared_limbs2(prep: &PreparedVecL2, b: &Vec<Rq>, n: usize) -> Rq {
    let deg: usize = params::RING_DEGREE;
    let qw: u128 = params::Q as u128;
    let mut acc: Rq = Rq::zero();
    let mut start: usize = 0;
    while start < n {
        let remaining: usize = n - start;
        let take: usize = if remaining < LIMB2_CHUNK { remaining } else { LIMB2_CHUNK };
        let end: usize = start + take;
        let ws: (Vec<u64>, Vec<u64>) =
            dot_prep_chunk_limbs2(&prep.f0, &prep.f1, b, start, end, GOLD_LOFF2);
        let mut out: Vec<Fp> = Vec::with_capacity(deg);
        let mut t: usize = 0;
        while t < deg {
            let v: u128 = (ws.0[t] as u128) + 65536 * (ws.1[t] as u128);
            out.push(Fp::new((v % qw) as u64));
            t += 1;
        }
        acc = acc.add(&Rq(out));
        start = end;
    }
    acc
}
