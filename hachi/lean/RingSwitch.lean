/-
The full ring-switch link: the quotient-row presentation change, the quotient
digits, the lifted message and its Ajtai commitment, and the two shortness
decisions.

Proved, on `Balanced.lean`'s `rho_digits_spec` and the scheme bridge, and part
of the audited library -- `lean/Check.lean` § 4 prints the axiom dependencies of
every headline spec below, so a `sorry` here is a `make build` failure. Proved
by two Aristotle sessions -- `8d26c89e` (2026-09-07, six obligations, two of
them returned under an added hypothesis) and `90c5c852` (2026-09-08, the five
re-stubbed after the Rust fix, to zero) -- and promoted out of `lean-wip/` on
the strength of the second: no errors, no `declaration uses 'sorry'`, and all
eight headline specs on exactly the three Lean kernel axioms.

All six headline obligations are **proved**, the two decision procedures at the
original unconditional statements. A first proof pass returned them with an added
`n * 8 ≤ Usize.max`, correctly diagnosing that the translation's flat digit index
made the extracted check fallible; the Rust was then changed to drop that index
(which the specification never had), so the hypothesis is gone rather than
assumed. `rho_digits_at_raw_spec`, `short_digit_loop_spec`,
`short_row_loop_spec` and the two check specs are the five obligations that
follow from that change, and they are now discharged. See the docstring on
`rho_digits_short_check_spec` and NOTES.md § "The flat index the specification
does not have". The file is rebased on ArkLib `d51d8bc`: `Z_DIGITS = 5` makes
`RLIN_COLS = 57344`, while the quotient digit count remains `clog 16 q = 8`.
The deleted convenience lemmas `hachiLiftCom_TCom`, `hachiLiftCom_com`, and
`rhoDigitsShortCheck_eq_true_of_digitBaseOk` are deliberately not referenced.

`ShortChallenge` erasure does not enter any definition below: this link receives
no challenge. The missing `ℓ₁ ≤ ω` precondition remains a composition-level
obligation when the verifier first consumes the fold challenge.
-/

import QuadEval
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Reduction
import ArkLib.Commitments.Functional.Hachi.EndPiece.Reduction

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi

namespace HachiEquiv.RingSwitch

open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme

theorem rhoDigitCount_eq : InnerOuter.rhoDigitCount q 16 = 8 := by
  have h := InnerOuter.HachiParams.clog_eq_delta
  simp only [InnerOuter.HachiParams.hachiB, InnerOuter.HachiParams.hachiQ,
    InnerOuter.HachiParams.hachiDelta] at h
  simpa [InnerOuter.rhoDigitCount, q] using h

/-- The raw quotient polynomial represented by a `QuotientRow`. -/
def toQuotientRow (v : ringswitch.QuotientRow) : CPolynomial (ZMod q) :=
  CPolynomial.ofFinCoeff N (coeffK v)

/-- A vector of raw quotient rows is well-formed at length `n`. -/
def WfRho (n : ℕ) (rho : alloc.vec.Vec ringswitch.QuotientRow) : Prop :=
  rho.val.length = n ∧ ∀ x ∈ rho.val, Wf x

/-- The specification-side quotient-row family represented by a Rust vector. -/
def toRho {n : ℕ} (rho : alloc.vec.Vec ringswitch.QuotientRow) :
    Fin n → CPolynomial (ZMod q) :=
  fun i => toQuotientRow (rho.val.getD i.val (alloc.vec.Vec.new cpoly.field.Fp))

/-- Relation between the extracted pair and ArkLib's proof-carrying witness. -/
def RepLiftedWitness {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) : Prop :=
  WfVec μ w.z ∧ WfRho n w.rho ∧
    toVec (k := μ) w.z = sw.z ∧ toRho (n := n) w.rho = sw.ρ

/-! ## The presentation change

`toQuotientRow` and `toRq` read the *same* coefficient vector, one into
`CPolynomial (ZMod q)` and one into `Rq Φ`; `rhoAsRq` is the map between them, so
the square commutes by `ofFinCoeff` extensionality alone. -/

/-- The coefficients of the represented quotient row: the represented words below
`N`, zero above. -/
theorem toQuotientRow_coeff (v : ringswitch.QuotientRow) (k : ℕ) :
    (toQuotientRow v).coeff k = if k < N then coeffK v k else 0 := by
  rw [toQuotientRow, CPolynomial.coeff_ofFinCoeff]

/-- Reading a coefficient vector into `Rq Φ` directly is reading it into a
`CPolynomial` and then applying `rhoAsRq`. -/
theorem toRq_eq_rhoAsRq (v : ringswitch.QuotientRow) :
    toRq v = InnerOuter.rhoAsRq Φ (toQuotientRow v) := by
  simp only [InnerOuter.rhoAsRq, phi_natDegree, toRq]
  refine ofFinCoeff_congr ?_
  intro t ht
  rw [toQuotientRow_coeff, if_pos ht]

/-- `QuotientRow::to_rq` is ArkLib's `rhoAsRq`: a presentation change, not a
cyclotomic reduction. -/
theorem rho_as_rq_spec (rho : ringswitch.QuotientRow) (hrho : Wf rho) :
    ringswitch.QuotientRow.to_rq rho
      ⦃ out => Wf out ∧ toRq out = InnerOuter.rhoAsRq Φ (toQuotientRow rho) ⦄ := by
  rw [ringswitch.QuotientRow.to_rq]
  apply spec_mono (RqBridge.copy_spec rho hrho)
  rintro out ⟨hW, hout⟩
  exact ⟨hW, by rw [hout, toRq_eq_rhoAsRq]⟩

/-! ## The quotient digits, indexed by a flat `ℕ`

`rhoDigitAsRq` is indexed by `Fin (n · rhoDigitCount q 16)`, which is the wrong
shape for a loop invariant: the loop counter is a `Usize` and its bound moves. So
the digit is named once as a function of a plain `ℕ` (`digitRq`), every loop below
is stated with that, and `rhoDigitAsRq_eq_digitRq` is the single place where the
flat index is put back into its `Fin`. -/

/-- Digit `t % 8` of quotient row `t / 8`, as an element of `Rq Φ`; the
`ℕ`-indexed form of `rhoDigitAsRq`. -/
def digitRq (rho : alloc.vec.Vec ringswitch.QuotientRow) (t : ℕ) : Rq Φ :=
  InnerOuter.rhoAsRq Φ (InnerOuter.rhoDigits Φ 16
    (toQuotientRow (rho.val.getD (t / 8) (alloc.vec.Vec.new cpoly.field.Fp))) (t % 8))

/-- The coefficients of a quotient digit: the balanced digit of the corresponding
coefficient of the row, below `N`, and zero above. -/
theorem digitRq_coeff (rho : alloc.vec.Vec ringswitch.QuotientRow) (t k : ℕ) :
    (digitRq rho t).1.coeff k
      = if k < N then InnerOuter.balancedDigit 16 (InnerOuter.rhoDigitCount q 16)
          (coeffK (rho.val.getD (t / 8) (alloc.vec.Vec.new cpoly.field.Fp)) k) (t % 8)
        else 0 := by
  rw [digitRq, InnerOuter.rhoAsRq, Rq.ofFinCoeff_coeff Φ _ (by rw [phi_natDegree]; exact N_le_degree)]
  by_cases hk : k < N
  · rw [if_pos (by rw [phi_natDegree]; exact hk), if_pos hk, InnerOuter.rhoDigits_coeff,
      if_pos (by rw [phi_natDegree]; exact hk), toQuotientRow_coeff, if_pos hk]
  · rw [if_neg (by rw [phi_natDegree]; exact hk), if_neg hk]

/-- The `Fin`-indexed digit of the specification is the `ℕ`-indexed one: the flat
index splits as row `t / 8` and digit `t % 8`, which is exactly `finProdFinEquiv`. -/
theorem rhoDigitAsRq_eq_digitRq {n : ℕ} (rho : alloc.vec.Vec ringswitch.QuotientRow)
    (t : ℕ) (ht : t < n * InnerOuter.rhoDigitCount q 16) :
    InnerOuter.rhoDigitAsRq Φ 16 (toRho (n := n) rho) ⟨t, ht⟩ = digitRq rho t := by
  have h1 : (((finProdFinEquiv.symm ⟨t, ht⟩ :
      Fin n × Fin (InnerOuter.rhoDigitCount q 16))).1 : ℕ) = t / 8 := rfl
  have h2 : (((finProdFinEquiv.symm ⟨t, ht⟩ :
      Fin n × Fin (InnerOuter.rhoDigitCount q 16))).2 : ℕ) = t % 8 := rfl
  simp only [InnerOuter.rhoDigitAsRq, digitRq, toRho, h1, h2]

/-- `rho_digit_as_rq` computes `digitRq`; the `Fin`-indexed restatement is
`rho_digit_as_rq_spec`. -/
theorem rho_digit_as_rq_raw_spec {n : ℕ} (rho : alloc.vec.Vec ringswitch.QuotientRow)
    (j : Std.Usize) (hrho : WfRho n rho) (hj : j.val < n * 8) :
    ringswitch.rho_digit_as_rq rho j
      ⦃ out => Wf out ∧ toRq out = digitRq rho j.val ⦄ := by
  have hgd : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  have hrowlt : j.val / 8 < rho.val.length := by rw [hrho.1]; omega
  rw [ringswitch.rho_digit_as_rq]
  step as ⟨row, hrow⟩
  step as ⟨u, hu⟩
  rw [hgd] at hrow hu
  have hrowlt' : row.val < rho.val.length := by rw [hrow]; exact hrowlt
  step as ⟨qr, hqr⟩
  have hWqr : Wf qr := by rw [hqr]; exact hrho.2 _ (List.getElem_mem hrowlt')
  have hqr' : qr = rho.val.getD (j.val / 8) (alloc.vec.Vec.new cpoly.field.Fp) := by
    rw [List.getD_eq_getElem _ _ hrowlt, hqr]
    simp only [hrow]
  apply spec_mono (HachiEquiv.Balanced.rho_digits_spec qr u hWqr)
  rintro z ⟨hWz, hz⟩
  refine ⟨hWz, ?_⟩
  rw [toRq]
  apply Subtype.ext
  rw [CompPoly.CPolynomial.eq_iff_coeff]
  intro k
  rw [Rq.ofFinCoeff_coeff Φ _ N_le_degree, digitRq_coeff]
  by_cases hk : k < N
  · rw [if_pos hk, if_pos hk, hz ⟨k, hk⟩, hu, hqr']
  · rw [if_neg hk, if_neg hk]

/-- The flat index is split as quotient row `j / 8` and digit `j % 8`. -/
theorem rho_digit_as_rq_spec {n : ℕ} (rho : alloc.vec.Vec ringswitch.QuotientRow)
    (j : Std.Usize) (hrho : WfRho n rho) (hj : j.val < n * 8) :
    ringswitch.rho_digit_as_rq rho j
      ⦃ out => Wf out ∧ toRq out =
        InnerOuter.rhoDigitAsRq Φ 16 (toRho (n := n) rho)
          ⟨j.val, by rw [rhoDigitCount_eq]; exact hj⟩ ⦄ := by
  apply spec_mono (rho_digit_as_rq_raw_spec rho j hrho hj)
  rintro out ⟨hW, hout⟩
  exact ⟨hW, by rw [hout, rhoDigitAsRq_eq_digitRq]⟩

/-! ## The lifted message

`Fin.append` is stated in Mathlib through `castAdd`/`natAdd`; the two lemmas here
re-state it for an index given by its value, which is the form a loop invariant
produces.

Two appends, so two loop invariants of the same shape: the entries already written
are the ones they should be, and the length is the counter. The second loop takes
the prefix the first one wrote as an opaque `pre`, which is what makes the
concatenation `Fin.append` at the end. -/

/-- `Fin.append` below the cut, read at an index given by its value. -/
theorem fin_append_of_lt {α : Type*} {a b : ℕ} (u : Fin a → α) (v : Fin b → α)
    (i : Fin (a + b)) (h : i.val < a) : Fin.append u v i = u ⟨i.val, h⟩ :=
  Fin.append_left u v ⟨i.val, h⟩

/-- `Fin.append` above the cut, read at an index given by its value. -/
theorem fin_append_of_ge {α : Type*} {a b : ℕ} (u : Fin a → α) (v : Fin b → α)
    (i : Fin (a + b)) (hge : a ≤ i.val) (h : i.val - a < b) :
    Fin.append u v i = v ⟨i.val - a, h⟩ := by
  have hi : i = Fin.natAdd a ⟨i.val - a, h⟩ := Fin.ext (by simp; omega)
  conv_lhs => rw [hi]
  rw [Fin.append_right]

/-- The first loop of `lift_message`: the `μ` entries of `z`, copied. -/
theorem lift_message_loop0_spec {μ : ℕ} (z : linalg.PolyVec) (zlen : Std.Usize)
    (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hz : WfVec μ z) (hzlen : zlen.val = μ) (hi : i.val ≤ μ)
    (hlen : out.val.length = i.val) (hwf : ∀ y ∈ out.val, Wf y)
    (hval : ∀ t < i.val, toRq (out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
      = toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))) :
    ringswitch.lift_message_loop0 z zlen out i
      ⦃ o => o.val.length = μ ∧ (∀ y ∈ o.val, Wf y) ∧
        ∀ t < μ, toRq (o.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [ringswitch.lift_message_loop0]
  apply loop.spec_decr_nat (fun s => zlen.val - s.2.val)
    (fun s => s.2.val ≤ μ ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ t < s.2.val, toRq (s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [ringswitch.lift_message_loop0.body]
    by_cases hlt : i1 < zlen
    · rw [if_pos hlt]
      have hilt : i1.val < z.val.length := by rw [hz.1, ← hzlen]; scalar_tac
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hz.2 _ (List.getElem_mem hilt)
      step with RqBridge.copy_spec r hWr as ⟨r1, hWr1, hr1⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_⟩
      · rw [hi2, ho2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr1
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = o1.val.length := by omega
          rw [hteq, ho2, getD_append_eq, hr1, hr, hlen1, List.getD_eq_getElem _ _ hilt]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = μ := by rw [← hzlen] at hi1 ⊢; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, by rw [← heq]; exact hval1⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- The second loop of `lift_message`: the `n · 8` quotient digits, appended after
an arbitrary prefix `pre`. -/
theorem lift_message_loop1_spec {n : ℕ} (rho : alloc.vec.Vec ringswitch.QuotientRow)
    (rlen : Std.Usize) (out : alloc.vec.Vec ring.Rq) (j : Std.Usize)
    (base : ℕ) (pre : ℕ → Rq Φ)
    (hrho : WfRho n rho) (hrlen : rlen.val = n * 8) (hj : j.val ≤ n * 8)
    (hmax : base + n * 8 ≤ Usize.max)
    (hlen : out.val.length = base + j.val) (hwf : ∀ y ∈ out.val, Wf y)
    (hpre : ∀ t < base, toRq (out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = pre t)
    (hdig : ∀ t < j.val, toRq (out.val.getD (base + t) (alloc.vec.Vec.new cpoly.field.Fp))
      = digitRq rho t) :
    ringswitch.lift_message_loop1 rho rlen out j
      ⦃ o => o.val.length = base + n * 8 ∧ (∀ y ∈ o.val, Wf y) ∧
        (∀ t < base, toRq (o.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = pre t) ∧
        (∀ t < n * 8, toRq (o.val.getD (base + t) (alloc.vec.Vec.new cpoly.field.Fp))
          = digitRq rho t) ⦄ := by
  rw [ringswitch.lift_message_loop1]
  apply loop.spec_decr_nat (fun s => rlen.val - s.2.val)
    (fun s => s.2.val ≤ n * 8 ∧ s.1.val.length = base + s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      (∀ t < base, toRq (s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)) = pre t) ∧
      (∀ t < s.2.val, toRq (s.1.val.getD (base + t) (alloc.vec.Vec.new cpoly.field.Fp))
        = digitRq rho t))
  · rintro ⟨o1, j1⟩ ⟨hj1, hlen1, hwf1, hpre1, hdig1⟩
    dsimp only at hj1 hlen1 hwf1 hpre1 hdig1
    simp only [ringswitch.lift_message_loop1.body]
    by_cases hlt : j1 < rlen
    · rw [if_pos hlt]
      have hjlt : j1.val < n * 8 := by rw [← hrlen]; scalar_tac
      step with rho_digit_as_rq_raw_spec rho j1 hrho hjlt as ⟨r, hWr, hr⟩
      have hbound : o1.val.length < Usize.max := by omega
      step as ⟨o2, ho2⟩
      step as ⟨j2, hj2⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hj2, ho2, List.length_append, hlen1]; simp; omega
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr
      · intro t ht
        rw [ho2, getD_append_lt _ _ _ (by omega), hpre1 t ht]
      · intro t ht
        rw [hj2] at ht
        rcases Nat.lt_or_ge t j1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hdig1 t htlt]
        · have hteq : base + t = o1.val.length := by omega
          have htj : t = j1.val := by omega
          rw [hteq, ho2, getD_append_eq, hr, htj]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : j1.val = n * 8 := by rw [← hrlen] at hj1 ⊢; scalar_tac
      exact ⟨by rw [hlen1, heq], hwf1, hpre1, by rw [← heq]; exact hdig1⟩
  · exact ⟨hj, hlen, hwf, hpre, hdig⟩

/-- `lift_message` is `Fin.append z (rhoDigitAsRq …)`. -/
theorem lift_message_spec {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (hw : RepLiftedWitness w sw)
    (hmax : μ + n * 8 ≤ Usize.max) :
    ringswitch.lift_message w
      ⦃ out => WfVec (μ + n * 8) out ∧ toVec (k := μ + n * 8) out =
        InnerOuter.liftMessage Φ 16 sw ⦄ := by
  obtain ⟨hWz, hWrho, hzeq, hrhoeq⟩ := hw
  have hgd : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  have hrholen : (alloc.vec.Vec.len w.rho).val = n := by simpa using hWrho.1
  have hzlen : (alloc.vec.Vec.len w.z).val = μ := by simpa using hWz.1
  rw [ringswitch.lift_message]
  simp only [linalg.PolyVec.len, bind_tc_ok]
  step as ⟨rl, hrl⟩
  rw [hgd, hrholen] at hrl
  · step with lift_message_loop0_spec (μ := μ) w.z (alloc.vec.Vec.len w.z)
      (alloc.vec.Vec.new ring.Rq) 0#usize hWz hzlen (by simp) (by simp)
      (by intro y hy; simp at hy) (by intro t ht; simp at ht) as ⟨o1, hlen1, hwf1, hval1⟩
    step with lift_message_loop1_spec (n := n) w.rho rl o1 0#usize μ
      (fun t => toRq (w.z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)))
      hWrho hrl (by simp) hmax (by simpa using hlen1) hwf1 hval1
      (by intro t ht; simp at ht) as ⟨o2, hlen2, hwf2, hpre2, hdig2⟩
    simp only [linalg.PolyVec.new, WP.spec_ok]
    refine ⟨⟨hlen2, hwf2⟩, ?_⟩
    funext m
    rw [InnerOuter.liftMessage]
    by_cases hm : m.val < μ
    · have happ := fin_append_of_lt sw.z (InnerOuter.rhoDigitAsRq Φ 16 sw.ρ) m hm
      rw [happ, ← hzeq]
      simp only [toVec]
      exact hpre2 m.val hm
    · have hge : μ ≤ m.val := by omega
      have hmlt : m.val - μ < n * 8 := by have := m.isLt; omega
      have happ := fin_append_of_ge sw.z (InnerOuter.rhoDigitAsRq Φ 16 sw.ρ) m hge hmlt
      have hdg := rhoDigitAsRq_eq_digitRq (n := n) w.rho (m.val - μ) hmlt
      have hidx := hdig2 (m.val - μ) hmlt
      rw [show μ + (m.val - μ) = m.val by omega] at hidx
      rw [happ, ← hrhoeq, hdg]
      simp only [toVec]
      exact hidx

/-- `lift_commit` is the concrete Ajtai commitment map at `(bound,bDig) =
(15,16)`. -/
theorem lift_commit_spec {dRows μ n : ℕ} (dKey : linalg.PolyMatrix)
    (w : ringswitch.LiftedWitness) (sw : InnerOuter.LiftedWitness Φ μ n)
    (hD : WfMat dRows (μ + n * 8) dKey) (hw : RepLiftedWitness w sw)
    (hmax : μ + n * 8 ≤ Usize.max) :
    ringswitch.lift_commit dKey w
      ⦃ out => WfVec dRows out ∧ toVec (k := dRows) out =
        (InnerOuter.hachiLiftCom Φ 15 16
          (toMat (rows := dRows) (cols := μ + n * 8) dKey)).com sw ⦄ := by
  rw [ringswitch.lift_commit]
  step with lift_message_spec w sw hw hmax as ⟨msg, hWmsg, hmsg⟩
  apply spec_mono (mat_vec_mul_spec (rows := dRows) (cols := μ + n * 8) dKey msg hD hWmsg)
  rintro out ⟨hWout, hout⟩
  refine ⟨hWout, ?_⟩
  rw [hout, hmsg]
  rfl

/-! ## The shortness decision

`RhoDigitsShort` quantifies over `Fin n × Fin (rhoDigitCount q 16)` and over *all*
coefficient indices; the Rust runs three nested `usize` loops and stops at `N`.
`ShortDigit` is the per-digit form both sides are reduced to, and
`rhoDigitsShort_iff` is the single place the two indexings meet: above `N` a digit
coefficient is zero, so the specification's unbounded `k` costs nothing. -/

/-- Every coefficient below `N` of the flat digit `t` is `15`-bounded. -/
def ShortDigit (rho : alloc.vec.Vec ringswitch.QuotientRow) (t : ℕ) : Prop :=
  ∀ k < N, ((digitRq rho t).1.coeff k).valMinAbs.natAbs ≤ 15

/-- The flat digit `r · 8 + e` reads coefficientwise as the specification's digit
`e` of row `r`. -/
theorem digitRq_coeff_eq_rhoDigits {n : ℕ} (rho : alloc.vec.Vec ringswitch.QuotientRow)
    {r e : ℕ} (hr : r < n) (he : e < 8) {k : ℕ} (hk : k < N) :
    (digitRq rho (r * 8 + e)).1.coeff k
      = (InnerOuter.rhoDigits Φ 16 (toRho (n := n) rho ⟨r, hr⟩) e).coeff k := by
  have hdiv : (r * 8 + e) / 8 = r := by omega
  have hmod : (r * 8 + e) % 8 = e := by omega
  rw [digitRq_coeff, if_pos hk, hdiv, hmod, InnerOuter.rhoDigits_coeff,
    if_pos (by rw [phi_natDegree]; exact hk)]
  show _ = InnerOuter.balancedDigit 16 (InnerOuter.rhoDigitCount q 16)
    ((toQuotientRow (rho.val.getD r (alloc.vec.Vec.new cpoly.field.Fp))).coeff k) e
  rw [toQuotientRow_coeff, if_pos hk]

/-- The specification's quotient-digit bound, in the flat form the loops produce. -/
theorem rhoDigitsShort_iff {n : ℕ} (rho : alloc.vec.Vec ringswitch.QuotientRow) :
    InnerOuter.RhoDigitsShort Φ 15 16 (toRho (n := n) rho)
      ↔ ∀ r < n, ∀ e < 8, ShortDigit rho (r * 8 + e) := by
  constructor
  · intro h r hr e he k hk
    rw [digitRq_coeff_eq_rhoDigits rho hr he hk]
    exact h ⟨r, hr⟩ ⟨e, by rw [rhoDigitCount_eq]; exact he⟩ k
  · intro h i u k
    by_cases hk : k < N
    · have hu : (u : ℕ) < 8 := by rw [← rhoDigitCount_eq]; exact u.isLt
      have := h i.val i.isLt (u : ℕ) hu k hk
      rwa [digitRq_coeff_eq_rhoDigits rho i.isLt hu hk] at this
    · rw [InnerOuter.rhoDigits_coeff, if_neg (by rw [phi_natDegree]; exact hk)]
      simp

/-- The innermost loop of `rho_digits_short_check`: no coefficient of the digit
visited so far exceeds `γ = 15`. -/
theorem short_coeff_loop_spec (digit : ring.Rq) (b0 short : Bool) (k : Std.Usize)
    (hd : Wf digit) (hk : k.val ≤ N)
    (hshort : short = true ↔ (b0 = true ∧ ∀ t < k.val,
      ((toRq digit).1.coeff t).valMinAbs.natAbs ≤ 15)) :
    endpiece.rho_digits_short_check_loop0_loop0_loop0 short digit k
      ⦃ b => (b = true ↔ (b0 = true ∧ ∀ t < N,
        ((toRq digit).1.coeff t).valMinAbs.natAbs ≤ 15)) ⦄ := by
  have hcg : (params.CHAIN_GAMMA).val = 15 := by simp [params.CHAIN_GAMMA]
  have hdeg : (params.RING_DEGREE).val = N := by simp
  rw [endpiece.rho_digits_short_check_loop0_loop0_loop0]
  apply loop.spec_decr_nat (fun s => N - s.2.val)
    (fun s => s.2.val ≤ N ∧ (s.1 = true ↔ (b0 = true ∧ ∀ t < s.2.val,
      ((toRq digit).1.coeff t).valMinAbs.natAbs ≤ 15)))
  · rintro ⟨b1, k1⟩ ⟨hk1, hb1⟩
    dsimp only at hk1 hb1
    simp only [endpiece.rho_digits_short_check_loop0_loop0_loop0.body]
    by_cases hlt : k1 < params.RING_DEGREE
    · rw [if_pos hlt]
      have hkN : k1.val < N := by rw [← hdeg]; scalar_tac
      step with RqBridge.coeff_spec digit k1 hd as ⟨f, hRf, hf⟩
      step with centered_abs_spec f hRf as ⟨cn, hcn⟩
      have hcn' : cn.val = ((toRq digit).1.coeff k1.val).valMinAbs.natAbs := by rw [hcn, hf]
      have hite : (if cn > params.CHAIN_GAMMA then ok false else ok b1)
          ⦃ c => (c = true ↔ (b1 = true ∧
            ((toRq digit).1.coeff k1.val).valMinAbs.natAbs ≤ 15)) ⦄ := by
        by_cases hgt : cn > params.CHAIN_GAMMA
        · rw [if_pos hgt, WP.spec_ok]
          have h15 : 15 < cn.val := by scalar_tac
          simp only [Bool.false_eq_true, false_iff, not_and]
          intro _ hb
          omega
        · rw [if_neg hgt, WP.spec_ok]
          have h15 : cn.val ≤ 15 := by scalar_tac
          exact ⟨fun h => ⟨h, by omega⟩, fun h => h.1⟩
      step with hite as ⟨b2, hb2⟩
      step as ⟨k2, hk2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [hk2, hb2]
        constructor
        · rintro ⟨hb1t, hbound⟩
          refine ⟨(hb1.mp hb1t).1, fun t ht => ?_⟩
          rcases Nat.lt_or_ge t k1.val with htlt | htge
          · exact (hb1.mp hb1t).2 t htlt
          · have : t = k1.val := by omega
            rw [this]; exact hbound
        · rintro ⟨hb0, hall⟩
          exact ⟨hb1.mpr ⟨hb0, fun t ht => hall t (by omega)⟩, hall k1.val (by omega)⟩
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = N := by rw [← hdeg] at hk1 ⊢; scalar_tac
      rw [← heq]; exact hb1
  · exact ⟨hk, hshort⟩

set_option maxRecDepth 8192 in
/-- `rho_digits_at` computes `digitRq` at the flat index the *pair* denotes.

The flat index survives on the specification side, where it is `ℕ` arithmetic and
cannot overflow; what the Rust no longer forms is the `usize` product. With
`u < 8` the two projections of `digitRq` collapse: `(i * 8 + u) / 8 = i` and
`(i * 8 + u) % 8 = u`. -/
theorem rho_digits_at_raw_spec {n : ℕ} (rho : alloc.vec.Vec ringswitch.QuotientRow)
    (i u : Std.Usize) (hrho : WfRho n rho) (hi : i.val < n) (hu : u.val < 8) :
    ringswitch.rho_digits_at rho i u
      ⦃ out => Wf out ∧ toRq out = digitRq rho (i.val * 8 + u.val) ⦄ := by
  have hrowlt : i.val < rho.val.length := by rw [hrho.1]; exact hi
  have hdiv : (i.val * 8 + u.val) / 8 = i.val := by omega
  have hmod : (i.val * 8 + u.val) % 8 = u.val := by omega
  rw [ringswitch.rho_digits_at]
  step as ⟨qr, hqr⟩
  have hWqr : Wf qr := by rw [hqr]; exact hrho.2 _ (List.getElem_mem hrowlt)
  have hqr' : qr = rho.val.getD i.val (alloc.vec.Vec.new cpoly.field.Fp) := by
    rw [List.getD_eq_getElem _ _ hrowlt, hqr]
  apply spec_mono (HachiEquiv.Balanced.rho_digits_spec qr u hWqr)
  rintro z ⟨hWz, hz⟩
  refine ⟨hWz, ?_⟩
  rw [toRq]
  apply Subtype.ext
  rw [CompPoly.CPolynomial.eq_iff_coeff]
  intro k
  rw [Rq.ofFinCoeff_coeff Φ _ N_le_degree, digitRq_coeff, hdiv, hmod]
  by_cases hk : k < N
  · rw [if_pos hk, if_pos hk, hz ⟨k, hk⟩, hqr']
  · rw [if_neg hk, if_neg hk]

set_option maxRecDepth 8192 in
/-- The middle loop of `rho_digits_short_check`: the eight digits of row `i`. -/
theorem short_digit_loop_spec {n : ℕ} (rho : alloc.vec.Vec ringswitch.QuotientRow)
    (i : Std.Usize) (b0 short : Bool) (u : Std.Usize)
    (hrho : WfRho n rho) (hi : i.val < n) (hu : u.val ≤ 8)
    (hshort : short = true ↔ (b0 = true ∧ ∀ e < u.val, ShortDigit rho (i.val * 8 + e))) :
    endpiece.rho_digits_short_check_loop0_loop0 rho i short u
      ⦃ b => (b = true ↔ (b0 = true ∧ ∀ e < 8, ShortDigit rho (i.val * 8 + e))) ⦄ := by
  have hgd : (params.GADGET_DIGITS).val = 8 := by simp [params.GADGET_DIGITS]
  rw [endpiece.rho_digits_short_check_loop0_loop0]
  apply loop.spec_decr_nat (fun s => 8 - s.2.val)
    (fun s => s.2.val ≤ 8 ∧ (s.1 = true ↔ (b0 = true ∧ ∀ e < s.2.val,
      ShortDigit rho (i.val * 8 + e))))
  · rintro ⟨b1, u1⟩ ⟨hu1, hb1⟩
    dsimp only at hu1 hb1
    simp only [endpiece.rho_digits_short_check_loop0_loop0.body]
    by_cases hlt : u1 < params.GADGET_DIGITS
    · rw [if_pos hlt]
      have hult : u1.val < 8 := by rw [← hgd]; scalar_tac
      step with rho_digits_at_raw_spec rho i u1 hrho hi hult as ⟨digit, hWd, hd⟩
      have hSD : (∀ t < N, ((toRq digit).1.coeff t).valMinAbs.natAbs ≤ 15)
          ↔ ShortDigit rho (i.val * 8 + u1.val) := by
        rw [ShortDigit, hd]
      step with short_coeff_loop_spec digit b1 b1 0#usize hWd (by simp)
        (by simp) as ⟨b2, hb2⟩
      step as ⟨u2, hu2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [hu2, hb2]
        constructor
        · rintro ⟨hb1t, hbound⟩
          refine ⟨(hb1.mp hb1t).1, fun e he => ?_⟩
          rcases Nat.lt_or_ge e u1.val with helt | hege
          · exact (hb1.mp hb1t).2 e helt
          · have heq : e = u1.val := by omega
            rw [heq]; exact hSD.mp hbound
        · rintro ⟨hb0, hall⟩
          exact ⟨hb1.mpr ⟨hb0, fun e he => hall e (by omega)⟩,
            hSD.mpr (hall u1.val (by omega))⟩
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : u1.val = 8 := by rw [← hgd] at hu1 ⊢; scalar_tac
      rw [heq] at hb1; exact hb1
  · exact ⟨hu, hshort⟩

/-- The outer loop of `rho_digits_short_check`: the rows. -/
theorem short_row_loop_spec {n : ℕ} (rho : alloc.vec.Vec ringswitch.QuotientRow)
    (rows i : Std.Usize) (short : Bool)
    (hrho : WfRho n rho) (hrows : rows.val = n) (hi : i.val ≤ n)
    (hshort : short = true ↔ ∀ r < i.val, ∀ e < 8, ShortDigit rho (r * 8 + e)) :
    endpiece.rho_digits_short_check_loop0 rho rows i short
      ⦃ b => (b = true ↔ ∀ r < n, ∀ e < 8, ShortDigit rho (r * 8 + e)) ⦄ := by
  rw [endpiece.rho_digits_short_check_loop0]
  apply loop.spec_decr_nat (fun s => n - s.1.val)
    (fun s => s.1.val ≤ n ∧ (s.2 = true ↔ ∀ r < s.1.val, ∀ e < 8,
      ShortDigit rho (r * 8 + e)))
  · rintro ⟨i1, b1⟩ ⟨hi1, hb1⟩
    dsimp only at hi1 hb1
    simp only [endpiece.rho_digits_short_check_loop0.body]
    by_cases hlt : i1 < rows
    · rw [if_pos hlt]
      have hilt : i1.val < n := by rw [← hrows]; scalar_tac
      step with short_digit_loop_spec rho i1 b1 b1 0#usize hrho hilt (by simp)
        (by simp) as ⟨b2, hb2⟩
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, ?_⟩
      · rw [hi2, hb2]
        constructor
        · rintro ⟨hb1t, hrow⟩ r hr
          rcases Nat.lt_or_ge r i1.val with hrlt | hrge
          · exact hb1.mp hb1t r hrlt
          · have heq : r = i1.val := by omega
            rw [heq]; exact hrow
        · intro hall
          exact ⟨hb1.mpr (fun r hr => hall r (by omega)), hall i1.val (by omega)⟩
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = n := by rw [← hrows] at hi1 ⊢; scalar_tac
      rw [heq] at hb1; exact hb1
  · exact ⟨hi, hshort⟩

/-- The Rust boolean decides the quotient-digit half of `liftShort`.

**Unconditional, and it took a Rust change to make it so.** An earlier proof of
this statement could not be completed as written and was returned with an added
`n * 8 ≤ Usize.max`: the check built the flat index `i * GADGET_DIGITS + u` as a
checked `usize` product over an `i` bounded only by `rho.len()`, so the extracted
function could *fail* rather than return a boolean, and a triple asserting
success is false without the bound. The diagnosis was right and the remedy was
in the wrong place -- `rhoDigitsShortCheck` has no flat index at all
(`EndPiece/Reduction.lean:111`: three quantifiers applying `rhoDigits` to `ρ i`
directly), so the product was a translation artefact. `rho_digits_short_check`
now addresses digits by the pair `(i, u)` through `ringswitch.rho_digits_at`,
its extracted model contains no multiplication, and the hypothesis has nothing
left to be about. See NOTES.md § "The flat index the specification does not
have". -/
theorem rho_digits_short_check_spec {n : ℕ}
    (rho : alloc.vec.Vec ringswitch.QuotientRow) (hrho : WfRho n rho) :
    endpiece.rho_digits_short_check rho
      ⦃ b => (b = true ↔ InnerOuter.RhoDigitsShort Φ 15 16 (toRho (n := n) rho)) ⦄ := by
  have hrows : (alloc.vec.Vec.len rho).val = n := by simpa using hrho.1
  rw [endpiece.rho_digits_short_check]
  apply spec_mono (short_row_loop_spec rho (alloc.vec.Vec.len rho) 0#usize true hrho hrows
    (by simp) (by simp))
  intro b hb
  rw [hb, rhoDigitsShort_iff]

/-- The Rust boolean decides `liftShort` at the concrete chain parameters.

Unconditional for the same reason as `rho_digits_short_check_spec`, which it
calls. Note the contrast with `lift_message_spec` two sections up, which keeps
its `μ + n * 8 ≤ Usize.max`: there the product is in the *specification*
(`liftMessage` is `Fin.append` over `Fin (μ + n · δ)`), so it is a real
obligation and not an artefact to translate away. -/
theorem lift_short_check_spec {μ n : ℕ} (w : ringswitch.LiftedWitness)
    (sw : InnerOuter.LiftedWitness Φ μ n) (hw : RepLiftedWitness w sw) :
    endpiece.lift_short_check w
      ⦃ b => (b = true ↔ InnerOuter.liftShort Φ 15 16 sw) ⦄ := by
  obtain ⟨hWz, hWrho, hzeq, hrhoeq⟩ := hw
  have hcg : (params.CHAIN_GAMMA).val = 15 := by simp [params.CHAIN_GAMMA]
  rw [endpiece.lift_short_check]
  simp only [ringswitch.LiftedWitness.impl.z, ringswitch.LiftedWitness.impl.rho, bind_tc_ok]
  step with vec_l_infty_norm_spec (k := μ) w.z hWz as ⟨nrm, hnrm⟩
  rw [hzeq] at hnrm
  by_cases hle : nrm ≤ params.CHAIN_GAMMA
  · rw [if_pos hle]
    have h15 : nrm.val ≤ 15 := by scalar_tac
    have hnorm : vecLInftyNorm Φ sw.z ≤ 15 := by omega
    apply spec_mono (rho_digits_short_check_spec (n := n) w.rho hWrho)
    intro b hb
    rw [hb, hrhoeq]
    simp only [InnerOuter.liftShort]
    exact ⟨fun h => ⟨hnorm, h⟩, fun h => h.2⟩
  · rw [if_neg hle, WP.spec_ok]
    have h15 : 15 < nrm.val := by scalar_tac
    simp only [Bool.false_eq_true, false_iff, InnerOuter.liftShort]
    rintro ⟨h1, -⟩
    omega

end HachiEquiv.RingSwitch
