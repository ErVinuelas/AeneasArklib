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
    let n: usize = params::RING_DEGREE;
    let q: u64 = params::Q;
    let terms: usize = desc.idx.len();
    let mut t: usize = 0;
    while t < terms {
        let k: usize = desc.idx[t];
        let m: u64 = desc.mag[t];
        let negt: bool = desc.neg[t];
        let mut pass: u64 = 0;
        while pass < m {
            let mut i: usize = 0;
            while i < n {
                let sv: u64 = s.0[i].to_u64();
                if sv != 0 {
                    let pos: usize = k + i;
                    // X^N = -1: crossing the boundary flips the sign
                    let w: usize = if pos >= n { pos - n } else { pos };
                    let wrapped: bool = pos >= n;
                    let sub: bool = negt != wrapped;
                    let cur: u64 = acc.0[w].to_u64();
                    let nv: u64 = if sub {
                        if cur >= sv { cur - sv } else { cur + q - sv }
                    } else {
                        let sum: u64 = cur + sv;
                        if sum >= q { sum - q } else { sum }
                    };
                    acc.0[w] = Fp::new(nv);
                }
                i += 1;
            }
            pass += 1;
        }
        t += 1;
    }
}
