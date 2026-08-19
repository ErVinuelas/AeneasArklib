/-
The **upper layers** of the equivalence: linear algebra, the gadget, and the
inner-outer commitment. Statements only, on the bridge from `Ring.lean`.

Unchecked, and outside the audited library; see `lean-wip/README.md`.

## Why the statements are the deliverable

Each theorem below fixes what the corresponding Rust function has to mean, in the
specification's own vocabulary, before any proof exists. That is worth having on
its own: it is where a mistranslation shows up. Two of them earn their place
already, because writing them down is what settled a design question in the Rust:

* `gadget_mul_spec` states agreement with `gadgetMul`, which is
  `gadgetMatrix *ᵥ v` — a *matrix* product. The Rust computes the per-block digit
  sum instead. Those are equal by the specification's own `gadgetMul_apply`, which
  is therefore not an optimization note but a load-bearing step of this proof.
* `verify_weak_spec` is an *equality of decisions*, not an implication. A verifier
  that rejected everything would satisfy `verify_weak = true → (the spec's checks
  hold)`; only the equality says the two accept the same openings, and only that
  form makes the rejection paths part of the claim.

## The composition order

`linalg` over `Ring`, `gadget` over both, `commit` over all three — the same
layering as `src/`. Each layer's specs are stated so that the layer above can
`step` through them without unfolding anything: that is why the `Wf` predicates
below are conjunctions of a shape condition and an entrywise one, and why the
gadget statements are about `Φ.φ.natDegree` where the Rust says `RING_DEGREE`
(they are equal by `Ring.phi_natDegree`, and using the spec's spelling keeps the
rewrite out of the upper layers).
-/
import RqBridge
import ArkLib.Commitments.Functional.Hachi.InnerOuter.Scheme
import ArkLib.Commitments.Functional.Hachi.Gadget.Norms

-- On, for the reason `lean/Check.lean` gives at length: with `autoImplicit` an
-- unknown identifier in a binder becomes an implicitly bound variable, so a missing
-- `open` turns a statement about `q` into a statement about *any* natural number --
-- which is how a spec silently becomes vacuous.
set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.Scheme

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge

/-! ## Vectors and matrices -/

/-- A vector of the extracted model is well-formed when it has the expected length
and every entry is. -/
def WfVec (k : ℕ) (v : linalg.PolyVec) : Prop :=
  v.val.length = k ∧ ∀ x ∈ v.val, Wf x

/-- The `PolyVec` an extracted vector represents. `Fin`-indexed, as the
specification's containers are; out-of-range indices cannot occur, so the
function is total by construction. -/
def toVec {k : ℕ} (v : linalg.PolyVec) : PolyVec (Rq Φ) k :=
  fun i => toRq (v.val.getD i.val (alloc.vec.Vec.new cpoly.field.Fp))

/-- A matrix is well-formed when it has the expected number of rows and each row is
a well-formed vector of the expected width. -/
def WfMat (rows cols : ℕ) (a : linalg.PolyMatrix) : Prop :=
  a.val.length = rows ∧ ∀ r ∈ a.val, WfVec cols r

/-- The `PolyMatrix` an extracted matrix represents. -/
def toMat {rows cols : ℕ} (a : linalg.PolyMatrix) : PolyMatrix (Rq Φ) rows cols :=
  fun i j => (toVec (k := cols) (a.val.getD i.val (alloc.vec.Vec.new ring.Rq))) j

/-- `PolyVec::dot` — ArkLib's `dot`.

The two are not syntactically the same sum: the specification is
`(List.ofFn fun i => u i * v i).sum`, which is right-nested and ends in `0`, while
the Rust accumulates from the left. They agree because `Rq Φ` is a commutative
monoid under `+`, and `dot_eq_sum` is the bridge to the `Finset.sum` form the rest
of the specification uses. Equal lengths are a hypothesis: the Rust takes the
shorter of the two, which makes it total, and the specification's version is only
defined when they match. -/
theorem dot_spec {k : ℕ} (u v : linalg.PolyVec) (hu : WfVec k u) (hv : WfVec k v) :
    linalg.PolyVec.dot u v
      ⦃ z => Wf z ∧ toRq z = ArkLib.Lattices.dot (toVec (k := k) u) (toVec (k := k) v) ⦄ := by
  sorry

/-- `PolyVec::add` — the `Pi` instance. -/
theorem vec_add_spec {k : ℕ} (u v : linalg.PolyVec) (hu : WfVec k u) (hv : WfVec k v) :
    linalg.PolyVec.add u v
      ⦃ z => WfVec k z ∧ toVec (k := k) z = toVec (k := k) u + toVec (k := k) v ⦄ := by
  sorry

/-- `PolyVec::sub` — the `Pi` instance; the vector whose norm `sub_l2NormSq_le`
bounds. -/
theorem vec_sub_spec {k : ℕ} (u v : linalg.PolyVec) (hu : WfVec k u) (hv : WfVec k v) :
    linalg.PolyVec.sub u v
      ⦃ z => WfVec k z ∧ toVec (k := k) z = toVec (k := k) u - toVec (k := k) v ⦄ := by
  sorry

/-- `PolyVec::scalar_mul` — ArkLib's `scalarVecMul`, the `cᵢ •ᵥ sᵢ` of the weak
verifier. -/
theorem scalar_vec_mul_spec {k : ℕ} (c : ring.Rq) (v : linalg.PolyVec)
    (hc : Wf c) (hv : WfVec k v) :
    linalg.PolyVec.scalar_mul v c
      ⦃ z => WfVec k z ∧ toVec (k := k) z = ArkLib.Lattices.scalarVecMul (toRq c)
        (toVec (k := k) v) ⦄ := by
  sorry

/-- `PolyMatrix::mat_vec_mul` — ArkLib's `matVecMul`, and so the Ajtai commitment
itself: `Simple.commit Φ A s = A *ᵥ s`. -/
theorem mat_vec_mul_spec {rows cols : ℕ} (a : linalg.PolyMatrix) (v : linalg.PolyVec)
    (ha : WfMat rows cols a) (hv : WfVec cols v) :
    linalg.PolyMatrix.mat_vec_mul a v
      ⦃ z => WfVec rows z ∧ toVec (k := rows) z
        = ArkLib.Lattices.matVecMul (toMat (rows := rows) (cols := cols) a)
            (toVec (k := cols) v) ⦄ := by
  sorry

/-- `flatten_blocks` — ArkLib's `PolyVec.flattenBlocks`.

The content of this one is the index convention: `finProdFinEquiv (i, w)` is
`w + width · i`, so the flattening is block-major, and the Rust's concatenation is
that. Getting it transposed would leave every other statement here true and the
composition wrong, which is why it is stated against `flattenBlocks` directly
rather than against a hand-written index formula. -/
theorem flatten_blocks_spec {blocks width : ℕ} (xs : alloc.vec.Vec linalg.PolyVec)
    (hxs : xs.val.length = blocks ∧ ∀ x ∈ xs.val, WfVec width x) :
    linalg.flatten_blocks xs
      ⦃ z => WfVec (blocks * width) z ∧ toVec (k := blocks * width) z
        = PolyVec.flattenBlocks (fun i : Fin blocks =>
            toVec (k := width) (xs.val.getD i.val (alloc.vec.Vec.new ring.Rq))) ⦄ := by
  sorry

/-! ## The gadget

The specification's digit decomposition is
`zmodDigitDecomposition b digits hb hq`, whose `digit c e` is
`((Nat.digits b c.val).getD e 0 : ZMod q)` — the ordinary base-`b` digits of the
canonical representative, *not* a balanced decomposition. `digit_at_spec` is
where that becomes a proof obligation, and it is the one genuinely arithmetic
statement in this file: the Rust divides `e` times and takes a remainder, and the
specification indexes into `Nat.digits`. The missing lemma is
`(Nat.digits b n).getD e 0 = n / b ^ e % b`, by induction on `e` with
`Nat.digits_def`. -/

/-- The instantiated digit decomposition at this crate's parameters. Its two side
conditions are `1 < b` and `q ≤ b ^ digits`, which `lean/Check.lean` § 1 checks of
the extracted constants. -/
def dd : DigitDecomposition (R := ZMod q) (2 : ZMod q) 32 :=
  zmodDigitDecomposition 2 32 (by norm_num) (by norm_num)

/-- `gadget::digit_at` — the specification's `digit c e`, at every `e`: past the
length of `Nat.digits b c.val` the specification's `getD` returns its default and
the Rust's quotient has run out, so both are `0`. -/
theorem digit_at_spec (c : cpoly.field.Fp) (e : Std.Usize) (hc : Red c) (he : e.val < 32) :
    gadget.digit_at c e ⦃ d => Red d ∧ toK d = dd.digit (toK c) ⟨e.val, he⟩ ⦄ := by
  sorry

/-- `gadget::base_pow` — `bᵉ` in `ZMod q`, not in `u64`: the specification's
exponent lives in the coefficient ring, and `b ^ e` passes the modulus at
`e = 32`. -/
theorem base_pow_spec (e : Std.Usize) :
    gadget.base_pow e ⦃ p => Red p ∧ toK p = (2 : ZMod q) ^ e.val ⦄ := by
  sorry

/-- `gadget::gadget_entry` — ArkLib's `gadgetEntry`. -/
theorem gadget_entry_spec (i j : Std.Usize) :
    gadget.gadget_entry i j
      ⦃ z => Wf z ∧ ∀ (rows : ℕ) (hi : i.val < rows) (hj : j.val < rows * 32),
          toRq z = gadgetEntry Φ (2 : ZMod q) (rows := rows) (digits := 32)
            ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⦄ := by
  sorry

/-- `gadget::gadget_mul` — ArkLib's `gadgetMul`, i.e. `gadgetMatrix *ᵥ v`.

The Rust computes the per-block digit sum directly. The bridge is the
specification's `gadgetMul_apply`: row `i` of the matrix product *is*
`Σ_{e} constRq (bᵉ) * v (finProdFinEquiv (i, e))`. -/
theorem gadget_mul_spec {rows : ℕ} (r : Std.Usize) (v : linalg.PolyVec)
    (hr : r.val = rows) (hv : WfVec (rows * 32) v) :
    gadget.gadget_mul r v
      ⦃ z => WfVec rows z ∧ toVec (k := rows) z
        = gadgetMul Φ (2 : ZMod q) (toVec (k := rows * 32) v) ⦄ := by
  sorry

/-- `gadget::gadget_decompose` — ArkLib's `gadgetDecompose` at `dd`. -/
theorem gadget_decompose_spec {rows : ℕ} (x : linalg.PolyVec) (hx : WfVec rows x) :
    gadget.gadget_decompose x
      ⦃ z => WfVec (rows * 32) z ∧ toVec (k := rows * 32) z
        = gadgetDecompose Φ dd (toVec (k := rows) x) ⦄ := by
  sorry

/-- **The gadget is lawful**, as a statement about the *Rust*: the extracted
`gadget_mul` inverts the extracted `gadget_decompose`. A corollary of the two
specs above and the specification's `gadgetDecompose_lawful`, and the property the
scheme's correctness rests on. Worth stating separately because it is the one
claim about this layer a reader can check against the test suite
(`tests/gadget_semantics.rs::gadget_mul_inverts_gadget_decompose`). -/
theorem gadget_round_trip {rows : ℕ} (r : Std.Usize) (x : linalg.PolyVec)
    (hr : r.val = rows) (hx : WfVec rows x) :
    (do let d ← gadget.gadget_decompose x; gadget.gadget_mul r d)
      ⦃ z => WfVec rows z ∧ toVec (k := rows) z = toVec (k := rows) x ⦄ := by
  sorry

/-! ## The centered norms

The specification measures every coefficient through `ZMod.valMinAbs`, which sends
a residue to its representative in `(-q/2, q/2]`; `commit::centered_abs` folds the
upper half of `[0, q)` down instead. The two agree because `q` is odd, and that is
`centered_abs_spec`.

The `ℓ₂²` statements are about `Std.U128` for a reason that is part of the claim:
the specification sums in `ℕ`, which cannot overflow, and a `u64` accumulator
would *fail* in this model on inputs the verifier is supposed to reject. -/

/-- `commit::centered_abs` — `(c.valMinAbs).natAbs`. -/
theorem centered_abs_spec (c : cpoly.field.Fp) (hc : Red c) :
    commit.centered_abs c ⦃ n => n.val = (toK c).valMinAbs.natAbs ⦄ := by
  sorry

/-- `commit::l1_norm` — ArkLib's `Rq.l1Norm`. -/
theorem l1_norm_spec (a : ring.Rq) (ha : Wf a) :
    commit.l1_norm a ⦃ n => n.val = Rq.l1Norm Φ (toRq a) ⦄ := by
  sorry

/-- `commit::l_infty_norm` — ArkLib's `Rq.lInftyNorm`. The Rust's running maximum
over an empty range is `0`, which is what the specification's `Finset.sup` gives
there too. -/
theorem l_infty_norm_spec (a : ring.Rq) (ha : Wf a) :
    commit.l_infty_norm a ⦃ n => n.val = Rq.lInftyNorm Φ (toRq a) ⦄ := by
  sorry

/-- `commit::l2_norm_sq` — ArkLib's `Rq.l2NormSq`, and total: `u128` is wide
enough for `N · (q/2)²`. -/
theorem l2_norm_sq_spec (a : ring.Rq) (ha : Wf a) :
    commit.l2_norm_sq a ⦃ n => n.val = Rq.l2NormSq Φ (toRq a) ⦄ := by
  sorry

/-- `commit::vec_l2_norm_sq` — ArkLib's `vecL2NormSq`. -/
theorem vec_l2_norm_sq_spec {k : ℕ} (v : linalg.PolyVec) (hv : WfVec k v) :
    commit.vec_l2_norm_sq v ⦃ n => n.val = vecL2NormSq Φ (toVec (k := k) v) ⦄ := by
  sorry

/-- `commit::vec_l_infty_norm` — ArkLib's `vecLInftyNorm`, the `‖t̂‖∞ ≤ γ` of the
weak verifier. -/
theorem vec_l_infty_norm_spec {k : ℕ} (v : linalg.PolyVec) (hv : WfVec k v) :
    commit.vec_l_infty_norm v ⦃ n => n.val = vecLInftyNorm Φ (toVec (k := k) v) ⦄ := by
  sorry

/-! ## The commitment

The specification's scheme is generic in six dimensions; these statements fix them
at `params.rs`'s values. `WfParams` and `WfDecomp` are the shape conditions that
make the two sides comparable at all -- the extracted structures carry `Vec`s
whose lengths nothing in the type system pins. -/

/-- Shape invariant of the public parameters: the two Ajtai matrices are of the
shapes `PublicParams` fixes. -/
def WfParams (pp : commit.PublicParams) : Prop :=
  WfMat 2 (4 * 32) pp.inner_matrix ∧ WfMat 2 (2 * (2 * 32)) pp.outer_matrix

/-- Shape invariant of the decomposition data. -/
def WfDecomp (d : commit.Decomp) : Prop :=
  (d.message.val.length = 2 ∧ ∀ s ∈ d.message.val, WfVec (4 * 32) s) ∧
  (d.inner_decomp.val.length = 2 ∧ ∀ t ∈ d.inner_decomp.val, WfVec (2 * 32) t)

/-- The specification's public parameters that an extracted `PublicParams`
represents. -/
def toParams (pp : commit.PublicParams) : InnerOuter.PublicParams Φ 2 4 32 2 2 32 where
  innerMatrix := toMat (rows := 2) (cols := 4 * 32) pp.inner_matrix
  outerMatrix := toMat (rows := 2) (cols := 2 * (2 * 32)) pp.outer_matrix

/-- The specification's decomposition data that an extracted `Decomp` represents. -/
def toDecompSpec (d : commit.Decomp) : InnerOuter.Decomp Φ 2 4 32 2 32 where
  message := fun i => toVec (k := 4 * 32) (d.message.val.getD i.val
    (alloc.vec.Vec.new ring.Rq))
  innerDecomp := fun i => toVec (k := 2 * 32) (d.inner_decomp.val.getD i.val
    (alloc.vec.Vec.new ring.Rq))

/-- The specification's weak opening that an extracted `Opening` represents. -/
def toOpening (o : commit.Opening) : InnerOuter.Opening Φ 2 4 32 2 32 where
  toDecomp := toDecompSpec o.decomp
  challenge := toVec (k := 2) o.challenge

/-- `commit::generate_decomps` — ArkLib's `generateDecomps` at
`Decomposition.ofDigits dd dd`: per block `sᵢ = G⁻¹(mᵢ)` and `t̂ᵢ = G⁻¹(A sᵢ)`.

Both halves matter. The shape half (`WfDecomp`) is what the layer above needs to
apply anything; the agreement half is what makes it the specification's
decomposition and not merely a decomposition of the right shape. -/
theorem generate_decomps_spec (pp : commit.PublicParams) (m : alloc.vec.Vec linalg.PolyVec)
    (hpp : WfParams pp) (hm : m.val.length = 2 ∧ ∀ x ∈ m.val, WfVec 4 x) :
    commit.generate_decomps pp m
      ⦃ d => WfDecomp d ∧ toDecompSpec d
        = InnerOuter.generateDecomps Φ (InnerOuter.Decomposition.ofDigits Φ dd dd)
            (toParams pp)
            (fun i : Fin 2 => toVec (k := 4) (m.val.getD i.val
              (alloc.vec.Vec.new ring.Rq))) ⦄ := by
  sorry

/-- `commit::derived_message` — ArkLib's `derivedMessage`, `mᵢ = G · sᵢ`
([NOZ26] Eq. (13)): the message a weak opening does not store but determines. -/
theorem derived_message_spec (d : commit.Decomp) (hd : WfDecomp d) :
    commit.derived_message d
      ⦃ out => (out.val.length = 2 ∧ ∀ x ∈ out.val, WfVec 4 x) ∧
        (fun i : Fin 2 => toVec (k := 4) (out.val.getD i.val (alloc.vec.Vec.new ring.Rq)))
          = InnerOuter.derivedMessage Φ (2 : ZMod q) (toDecompSpec d) ⦄ := by
  sorry

/-- `commit::commit_with_decomps` — ArkLib's `commitWithDecomps`,
`u = B · flatten(t̂)`. -/
theorem commit_with_decomps_spec (pp : commit.PublicParams) (d : commit.Decomp)
    (hpp : WfParams pp) (hd : WfDecomp d) :
    commit.commit_with_decomps pp d
      ⦃ u => WfVec 2 u ∧ toVec (k := 2) u
        = InnerOuter.commitWithDecomps Φ (toParams pp) (toDecompSpec d) ⦄ := by
  sorry

/-- `commit::verify_weak` — ArkLib's `verify_weak`, as an equality of *decisions*.

An equality of `Bool`s, not an implication: an implication in the accepting
direction is satisfied by a verifier that rejects everything, and that is exactly
the failure a correctness test cannot see. The specification's `verify_weak` is
itself `Bool`-valued (a `&&` of `List.all` over eagerly-`decide`d propositions),
which is why no `decide` appears on either side.

The three bounds are `params.rs`'s: `βSq = 8192`, `γ = 1`, `κ = 65535`. They are
the numbers `lean/Check.lean` § 1 ties to the extracted constants, so this
statement and the Rust cannot disagree about them without that audit failing. -/
theorem verify_weak_spec (pp : commit.PublicParams) (u : linalg.PolyVec)
    (o : commit.Opening) (hpp : WfParams pp) (hu : WfVec 2 u) (ho : WfDecomp o.decomp) :
    commit.verify_weak pp u o
      ⦃ r => r = InnerOuter.verify_weak Φ (2 : ZMod q) 8192 1 65535
        (toParams pp) (toVec (k := 2) u) (toOpening o) ⦄ := by
  sorry

/-- **Perfect correctness of the extracted scheme**: an honest commitment and its
honest opening verify. The computational content of ArkLib's
`InnerOuter.Correctness.perfectlyCorrect`, and the statement the test
`tests/commit_semantics.rs::honest_commitments_verify` checks by example.

Stated as a single `do` block rather than as three composed specs because that is
what the honest committer actually runs, and because the challenge the honest
committer supplies (`cᵢ = 1`) is part of the claim: it is admissible only because
`‖1‖₁ = 1` sits inside `0 < ‖c‖₁ ≤ κ`, which is a fact about `params.rs`'s `κ`
and not about the scheme. -/
theorem honest_verifies (pp : commit.PublicParams) (m : alloc.vec.Vec linalg.PolyVec)
    (hpp : WfParams pp) (hm : m.val.length = 2 ∧ ∀ x ∈ m.val, WfVec 4 x) :
    (do
      let (u, d) ← commit.commit pp m
      let o ← commit.Opening.honest d
      commit.verify_weak pp u o) ⦃ r => r = true ⦄ := by
  sorry

end HachiEquiv.Scheme
