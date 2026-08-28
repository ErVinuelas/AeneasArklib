/-
# Equivalence statements for `hachi/src/evalsplit.rs` (and `linalg::split_form`)

**All statements are proved.** Staged in `lean-wip/` as statements-only during
the EvalSplit onboarding, proved by Aristotle (session `cc7674ce`, see
`logs/aristotle-sessions.jsonl`), and promoted here: each statement is
well-formed at this crate's parameters, about the specification's own
definitions, and now carries its proof. `lean/Check.lean` § 4 audits the axiom
dependencies of the twelve headline specs.

The vocabulary is `lean/Scheme.lean`'s (`Wf`/`WfVec`/`WfMat`, `toRq`/`toVec`/
`toMat`), extended with the two `Vector`-valued representation maps the
multilinear layer needs (`toVector`, and the polynomial readings `toMlPoly` /
`toMlEvals`). The split dimensions are the crate's `ML_VARS_LOW = 1`,
`ML_VARS_HIGH = 2` (`params.rs`; `2^nl = BLOCKS`, `2^nh = MESSAGE_ROWS`, the
shape `derivedMsgMatrix` fixes).

Two model-artefact hypotheses appear, in the `flatten_blocks_spec` tradition:
`two_pow` multiplies its way to `2^n`, so any statement through it carries
`2 ^ n ≤ Usize.max`; everything else is exact.
-/
import Scheme
import ArkLib.Commitments.Functional.Hachi.EvalSplit

set_option autoImplicit false

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus ArkLib.Lattices.Ajtai
open hachi
open HachiEquiv.Field HachiEquiv.Ring HachiEquiv.RqBridge HachiEquiv.Scheme

namespace HachiEquiv.EvalSplit

/-! ## The split dimensions, and the `Vector`-valued representation maps -/

/-- The low variable count `nl` (`params.ML_VARS_LOW`): rows are `2^nl = 1024`. -/
abbrev nl : ℕ := 10

/-- The high variable count `nh` (`params.ML_VARS_HIGH`): columns are `2^nh = 1024`. -/
abbrev nh : ℕ := 10

/-- A well-formed length-`n` vector, read as the spec's `Vector (Rq Φ) n` (the
carrier `CMlPolynomial` and the basis functions take, where `toVec` produces the
`Fin`-function `PolyVec`). -/
def toVector {n : ℕ} (v : linalg.PolyVec) : Vector (Rq Φ) n :=
  Vector.ofFn (toVec (k := n) v)

/-- An extracted `MlPoly`, read as the spec's monomial-coefficient polynomial. -/
def toMlPoly (p : evalsplit.MlPoly) : CMlPolynomial (Rq Φ) (nl + nh) :=
  toVector (n := 2 ^ (nl + nh)) p

/-- An extracted `MlEvals`, read as the spec's hypercube-value polynomial. -/
def toMlEvals (p : evalsplit.MlEvals) : CMlPolynomialEval (Rq Φ) (nl + nh) :=
  toVector (n := 2 ^ (nl + nh)) p

attribute [local step] HachiEquiv.RqBridge.mul_spec HachiEquiv.RqBridge.sub_spec
  HachiEquiv.RqBridge.one_spec HachiEquiv.RqBridge.copy_spec

/-! ## Index helpers -/

/-- The loop of `two_pow`: the accumulator is `2 ^ t` after `t` doublings. -/
theorem two_pow_loop_spec (n size t : Std.Usize) (hn : 2 ^ n.val ≤ Usize.max)
    (ht : t.val ≤ n.val) (hsize : size.val = 2 ^ t.val) :
    evalsplit.two_pow_loop n size t ⦃ s => s.val = 2 ^ n.val ⦄ := by
  rw [evalsplit.two_pow_loop]
  apply loop.spec_decr_nat (fun s => n.val - s.2.val)
    (fun s => s.2.val ≤ n.val ∧ s.1.val = 2 ^ s.2.val)
  · rintro ⟨s1, t1⟩ ⟨ht1, hs1⟩
    dsimp only at ht1 hs1
    simp only [evalsplit.two_pow_loop.body]
    by_cases hlt : t1 < n
    · rw [if_pos hlt]
      have hfit : s1.val * 2 ≤ Usize.max := by
        have hmono : 2 ^ (t1.val + 1) ≤ 2 ^ n.val :=
          Nat.pow_le_pow_right (by norm_num) (by scalar_tac)
        rw [hs1, ← pow_succ] at *
        omega
      step as ⟨s2, hs2⟩
      step as ⟨t2, ht2⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hs2, hs1, ht2, pow_succ]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : t1.val = n.val := by scalar_tac
      rw [hs1, heq]
  · exact ⟨ht, hsize⟩

/-- `two_pow` is `2 ^ n`, total up to the `usize` ceiling (the checked
multiplication is the model artefact the hypothesis discharges). -/
theorem two_pow_spec (n : Std.Usize) (hn : 2 ^ n.val ≤ Usize.max) :
    evalsplit.two_pow n ⦃ s => s.val = 2 ^ n.val ⦄ :=
  two_pow_loop_spec n 1#usize 0#usize hn (by simp) (by simp)

/-- The loop of `test_bit`: after `t` halvings the remaining word is `i / 2ᵗ`. -/
theorem test_bit_loop_spec (j rest t : Std.Usize) (i0 : ℕ)
    (ht : t.val ≤ j.val) (hrest : rest.val = i0 / 2 ^ t.val) :
    evalsplit.test_bit_loop j rest t ⦃ z => z.val = i0 / 2 ^ j.val ⦄ := by
  rw [evalsplit.test_bit_loop]
  apply loop.spec_decr_nat (fun s => j.val - s.2.val)
    (fun s => s.2.val ≤ j.val ∧ s.1.val = i0 / 2 ^ s.2.val)
  · rintro ⟨r1, t1⟩ ⟨ht1, hr1⟩
    dsimp only at ht1 hr1
    simp only [evalsplit.test_bit_loop.body]
    by_cases hlt : t1 < j
    · rw [if_pos hlt]
      step as ⟨r2, hr2⟩
      step as ⟨t2, ht2⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hr2, hr1, ht2, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : t1.val = j.val := by scalar_tac
      rw [hr1, heq]
  · exact ⟨ht, hrest⟩

/-- `test_bit` is `Nat.testBit`, i.e. the spec's `(BitVec.ofFin i).getLsb j`.
Total unconditionally: the loop only divides. -/
theorem test_bit_spec (i j : Std.Usize) :
    evalsplit.test_bit i j ⦃ b => b = Nat.testBit i.val j.val ⦄ := by
  rw [evalsplit.test_bit]
  step with test_bit_loop_spec j i 0#usize i.val (by simp) (by simp) as ⟨r, hr⟩
  step as ⟨m, hm⟩
  have hmval : m.val = i.val / 2 ^ j.val % 2 := by rw [hm, hr]
  rw [Nat.testBit_eq_decide_div_mod_eq, ← hmval, decide_eq_decide]
  constructor
  · intro h; rw [h]; rfl
  · intro h; scalar_tac

/-- `split_equiv` is the value of ArkLib's `splitEquiv nl nh` (`splitEquiv_val`:
`(x, y) ↦ y + 2^nl · x`). The `Fin` bounds arrive as hypotheses; totality of the
checked `+`/`*` follows from them. -/
theorem split_equiv_spec (x y : Std.Usize) (hx : x.val < 2 ^ nh) (hy : y.val < 2 ^ nl) :
    evalsplit.split_equiv x y
      ⦃ k => k.val = (Hachi.splitEquiv nl nh (⟨x.val, hx⟩, ⟨y.val, hy⟩)).val ⦄ := by
  have hx4 : x.val < 1024 := by have h := hx; norm_num at h; omega
  have hy2 : y.val < 1024 := by have h := hy; norm_num at h; omega
  have hlow : (params.ML_LOW_LEN).val = 1024 := by simp [params.ML_LOW_LEN]
  rw [evalsplit.split_equiv]
  have hfit : (params.ML_LOW_LEN).val * x.val ≤ Usize.max := by
    rw [hlow]; scalar_tac
  step as ⟨i1, hi1⟩
  have hi1v : i1.val = 1024 * x.val := by rw [hi1, hlow]
  step as ⟨k, hk⟩
  rw [hk, hi1v, Hachi.splitEquiv_val]
  norm_num

/-- `splitEquiv.symm` at the crate's split (`2 ^ nl = 1024`), componentwise. -/
theorem splitEquiv_symm_val (k : Fin (2 ^ (nl + nh))) :
    ((Hachi.splitEquiv nl nh).symm k).1.val = k.val / 1024
      ∧ ((Hachi.splitEquiv nl nh).symm k).2.val = k.val % 1024 := by
  have happ : Hachi.splitEquiv nl nh ((Hachi.splitEquiv nl nh).symm k) = k :=
    Equiv.apply_symm_apply _ _
  have hval : ((Hachi.splitEquiv nl nh).symm k).2.val
      + 1024 * ((Hachi.splitEquiv nl nh).symm k).1.val = k.val := by
    conv_rhs => rw [← happ]
    rw [Hachi.splitEquiv_val]
    norm_num
  have h2 : ((Hachi.splitEquiv nl nh).symm k).2.val < 1024 := by
    have h := ((Hachi.splitEquiv nl nh).symm k).2.isLt
    norm_num at h; exact h
  omega

/-- `split_equiv_inv` is `splitEquiv.symm`, componentwise. -/
theorem split_equiv_inv_spec (k : Std.Usize) (hk : k.val < 2 ^ (nl + nh)) :
    evalsplit.split_equiv_inv k
      ⦃ p => p.1.val = ((Hachi.splitEquiv nl nh).symm ⟨k.val, hk⟩).1.val
           ∧ p.2.val = ((Hachi.splitEquiv nl nh).symm ⟨k.val, hk⟩).2.val ⦄ := by
  have hlow : (params.ML_LOW_LEN).val = 1024 := by simp [params.ML_LOW_LEN]
  obtain ⟨hs1, hs2⟩ := splitEquiv_symm_val ⟨k.val, hk⟩
  rw [evalsplit.split_equiv_inv]
  step as ⟨x, hx⟩
  step as ⟨y, hy⟩
  refine ⟨?_, ?_⟩
  · rw [hx, hlow, hs1]
  · rw [hy, hlow, hs2]

/-! ## The bases -/

/-- `monomial_basis` computes `CMlPolynomial.monomialBasis` of the represented
point, entrywise: length `2^n`, entries reduced, and the `Fin`-function reading
equal to the spec's basis vector. Stated at every point length `n` with the
`usize` ceiling as the one model-artefact hypothesis. -/
theorem monomial_basis_inner_loop_spec {n : ℕ} (w : linalg.PolyVec) (nn i : Std.Usize)
    (one acc : ring.Rq) (j : Std.Usize)
    (hw : WfVec n w) (hn : nn.val = n) (hone : Wf one) (honev : toRq one = 1)
    (hj : j.val ≤ nn.val) (hacc : Wf acc)
    (hval : toRq acc = ∏ t ∈ Finset.range j.val,
      (if Nat.testBit i.val t then toRq (w.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        else 1)) :
    evalsplit.monomial_basis_loop0_loop0 one w nn i acc j
      ⦃ z => Wf z ∧ toRq z = ∏ t ∈ Finset.range n,
        (if Nat.testBit i.val t then toRq (w.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          else 1) ⦄ := by
  rw [evalsplit.monomial_basis_loop0_loop0]
  apply loop.spec_decr_nat (fun s => nn.val - s.2.val)
    (fun s => s.2.val ≤ nn.val ∧ Wf s.1 ∧
      toRq s.1 = ∏ t ∈ Finset.range s.2.val,
        (if Nat.testBit i.val t then toRq (w.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          else 1))
  · rintro ⟨a1, j1⟩ ⟨hj1, hWa1, hval1⟩
    dsimp only at hj1 hWa1 hval1
    simp only [evalsplit.monomial_basis_loop0_loop0.body]
    by_cases hlt : j1 < nn
    · rw [if_pos hlt]
      have hjn : j1.val < n := by rw [← hn]; scalar_tac
      have hjw : j1.val < w.val.length := by rw [hw.1]; exact hjn
      step with test_bit_spec i j1 as ⟨b, hb⟩
      by_cases hbb : b = true
      · rw [if_pos hbb]
        have htb : Nat.testBit i.val j1.val = true := by rw [← hb]; exact hbb
        simp only [linalg.PolyVec.get]
        step as ⟨r, hr⟩
        have hWr : Wf r := by rw [hr]; exact hw.2 _ (List.getElem_mem hjw)
        step as ⟨f, hWf, hf⟩
        step as ⟨a2, hWa2, ha2⟩
        step as ⟨j2, hj2⟩
        refine ⟨by scalar_tac, hWa2, ?_, by scalar_tac⟩
        rw [ha2, hval1, hf, hr, hj2, Finset.prod_range_succ, if_pos htb,
          List.getD_eq_getElem _ _ hjw]
      · rw [if_neg hbb]
        have htb : Nat.testBit i.val j1.val = false := by
          rw [← hb]; exact Bool.eq_false_iff.mpr hbb
        step as ⟨a2, hWa2, ha2⟩
        step as ⟨j2, hj2⟩
        refine ⟨by scalar_tac, hWa2, ?_, by scalar_tac⟩
        rw [ha2, hval1, honev, hj2, Finset.prod_range_succ, if_neg (by simp [htb])]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : j1.val = n := by rw [← hn]; scalar_tac
      exact ⟨hWa1, by rw [hval1, heq]⟩
  · exact ⟨hj, hacc, hval⟩

/-- The outer loop of `monomial_basis`: entry `t` already written is the monomial
basis value at index `t`. -/
theorem monomial_basis_outer_loop_spec {n : ℕ} (w : linalg.PolyVec) (nn size : Std.Usize)
    (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hw : WfVec n w) (hn : nn.val = n) (hsize : size.val = 2 ^ n)
    (hi : i.val ≤ size.val) (hlen : out.val.length = i.val)
    (hwf : ∀ y ∈ out.val, Wf y)
    (hval : ∀ t, t < i.val →
      toRq (out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        = ∏ s ∈ Finset.range n,
          (if Nat.testBit t s then toRq (w.val.getD s (alloc.vec.Vec.new cpoly.field.Fp))
            else 1)) :
    evalsplit.monomial_basis_loop0 w nn size out i
      ⦃ z => z.val.length = 2 ^ n ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ t, t < 2 ^ n →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = ∏ s ∈ Finset.range n,
              (if Nat.testBit t s then toRq (w.val.getD s (alloc.vec.Vec.new cpoly.field.Fp))
                else 1) ⦄ := by
  rw [evalsplit.monomial_basis_loop0]
  apply loop.spec_decr_nat (fun s => size.val - s.2.val)
    (fun s => s.2.val ≤ size.val ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ t, t < s.2.val →
        toRq (s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          = ∏ u ∈ Finset.range n,
            (if Nat.testBit t u then toRq (w.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
              else 1))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [evalsplit.monomial_basis_loop0.body]
    by_cases hlt : i1 < size
    · rw [if_pos hlt]
      step as ⟨one, hWone, hone⟩
      step with monomial_basis_inner_loop_spec w nn i1 one one 0#usize hw hn hWone hone
        (by simp) hWone (by simp [hone]) as ⟨a1, hWa1, ha1⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      and_intros
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWa1
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = o1.val.length := by omega
          rw [hteq, ho2, getD_append_eq, ha1, hlen1]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = size.val := by scalar_tac
      exact ⟨by rw [hlen1, heq, hsize], hwf1, by
        intro t ht; exact hval1 t (by rw [heq, hsize]; exact ht)⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- The spec's monomial basis, entrywise, in the vocabulary of the extracted
vector: a product of `Nat.testBit`-selected coordinates. -/
theorem monomialBasis_get_toVector {n : ℕ} (w : linalg.PolyVec) (t : Fin (2 ^ n)) :
    (CMlPolynomial.monomialBasis (toVector (n := n) w)).get t
      = ∏ s ∈ Finset.range n,
        (if Nat.testBit t.val s then toRq (w.val.getD s (alloc.vec.Vec.new cpoly.field.Fp))
          else 1) := by
  rw [Hachi.monomialBasis_get, ← Fin.prod_univ_eq_prod_range
    (fun s => if Nat.testBit t.val s then
      toRq (w.val.getD s (alloc.vec.Vec.new cpoly.field.Fp)) else 1) n]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, toVector,
    Vector.get_ofFn, toVec]

theorem monomial_basis_spec {n : ℕ} (w : linalg.PolyVec)
    (hw : WfVec n w) (hn : 2 ^ n ≤ Usize.max) :
    evalsplit.monomial_basis w
      ⦃ z => WfVec (2 ^ n) z ∧
        toVec (k := 2 ^ n) z
          = (CMlPolynomial.monomialBasis (toVector (n := n) w)).get ⦄ := by
  rw [evalsplit.monomial_basis]
  simp only [linalg.PolyVec.len]
  have hnn : (alloc.vec.Vec.len w).val = n := by simpa using hw.1
  step with two_pow_spec (alloc.vec.Vec.len w) (by rw [hnn]; exact hn) as ⟨size, hsize⟩
  step with monomial_basis_outer_loop_spec w (alloc.vec.Vec.len w) size
    (alloc.vec.Vec.new ring.Rq) 0#usize hw hnn (by rw [hsize, hnn]) (by simp)
    (by simp) (by intro y hy; simp at hy) (by intro t ht; simp at ht)
    as ⟨z, hzlen, hzwf, hzval⟩
  simp only [linalg.PolyVec.new, WP.spec_ok]
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext t
  rw [monomialBasis_get_toVector]
  exact hzval t.val t.isLt

/-- The inner loop of `lagrange_basis`: the accumulator collects the running
product of `w j` (bit set) and `1 - w j` (bit clear) over the processed range. -/
theorem lagrange_basis_inner_loop_spec {n : ℕ} (w : linalg.PolyVec) (nn i : Std.Usize)
    (one acc : ring.Rq) (j : Std.Usize)
    (hw : WfVec n w) (hn : nn.val = n) (hone : Wf one) (honev : toRq one = 1)
    (hj : j.val ≤ nn.val) (hacc : Wf acc)
    (hval : toRq acc = ∏ t ∈ Finset.range j.val,
      (if Nat.testBit i.val t then toRq (w.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        else 1 - toRq (w.val.getD t (alloc.vec.Vec.new cpoly.field.Fp)))) :
    evalsplit.lagrange_basis_loop0_loop0 one w nn i acc j
      ⦃ z => Wf z ∧ toRq z = ∏ t ∈ Finset.range n,
        (if Nat.testBit i.val t then toRq (w.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          else 1 - toRq (w.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))) ⦄ := by
  rw [evalsplit.lagrange_basis_loop0_loop0]
  apply loop.spec_decr_nat (fun s => nn.val - s.2.val)
    (fun s => s.2.val ≤ nn.val ∧ Wf s.1 ∧
      toRq s.1 = ∏ t ∈ Finset.range s.2.val,
        (if Nat.testBit i.val t then toRq (w.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          else 1 - toRq (w.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))))
  · rintro ⟨a1, j1⟩ ⟨hj1, hWa1, hval1⟩
    dsimp only at hj1 hWa1 hval1
    simp only [evalsplit.lagrange_basis_loop0_loop0.body]
    by_cases hlt : j1 < nn
    · rw [if_pos hlt]
      have hjn : j1.val < n := by rw [← hn]; scalar_tac
      have hjw : j1.val < w.val.length := by rw [hw.1]; exact hjn
      step with test_bit_spec i j1 as ⟨b, hb⟩
      by_cases hbb : b = true
      · rw [if_pos hbb]
        have htb : Nat.testBit i.val j1.val = true := by rw [← hb]; exact hbb
        simp only [linalg.PolyVec.get]
        step as ⟨r, hr⟩
        have hWr : Wf r := by rw [hr]; exact hw.2 _ (List.getElem_mem hjw)
        step as ⟨f, hWf, hf⟩
        step as ⟨a2, hWa2, ha2⟩
        step as ⟨j2, hj2⟩
        refine ⟨by scalar_tac, hWa2, ?_, by scalar_tac⟩
        rw [ha2, hval1, hf, hr, hj2, Finset.prod_range_succ, if_pos htb,
          List.getD_eq_getElem _ _ hjw]
      · rw [if_neg hbb]
        have htb : Nat.testBit i.val j1.val = false := by
          rw [← hb]; exact Bool.eq_false_iff.mpr hbb
        simp only [linalg.PolyVec.get]
        step as ⟨r, hr⟩
        have hWr : Wf r := by rw [hr]; exact hw.2 _ (List.getElem_mem hjw)
        step as ⟨f, hWf, hf⟩
        step as ⟨a2, hWa2, ha2⟩
        step as ⟨j2, hj2⟩
        refine ⟨by scalar_tac, hWa2, ?_, by scalar_tac⟩
        rw [ha2, hval1, hf, honev, hr, hj2, Finset.prod_range_succ,
          if_neg (by simp [htb]), List.getD_eq_getElem _ _ hjw]
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : j1.val = n := by rw [← hn]; scalar_tac
      exact ⟨hWa1, by rw [hval1, heq]⟩
  · exact ⟨hj, hacc, hval⟩

/-- The outer loop of `lagrange_basis`: entry `t` already written is the Lagrange
basis value at index `t`. -/
theorem lagrange_basis_outer_loop_spec {n : ℕ} (w : linalg.PolyVec) (nn size : Std.Usize)
    (out : alloc.vec.Vec ring.Rq) (i : Std.Usize)
    (hw : WfVec n w) (hn : nn.val = n) (hsize : size.val = 2 ^ n)
    (hi : i.val ≤ size.val) (hlen : out.val.length = i.val)
    (hwf : ∀ y ∈ out.val, Wf y)
    (hval : ∀ t, t < i.val →
      toRq (out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        = ∏ s ∈ Finset.range n,
          (if Nat.testBit t s then toRq (w.val.getD s (alloc.vec.Vec.new cpoly.field.Fp))
            else 1 - toRq (w.val.getD s (alloc.vec.Vec.new cpoly.field.Fp)))) :
    evalsplit.lagrange_basis_loop0 w nn size out i
      ⦃ z => z.val.length = 2 ^ n ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ t, t < 2 ^ n →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = ∏ s ∈ Finset.range n,
              (if Nat.testBit t s then toRq (w.val.getD s (alloc.vec.Vec.new cpoly.field.Fp))
                else 1 - toRq (w.val.getD s (alloc.vec.Vec.new cpoly.field.Fp))) ⦄ := by
  rw [evalsplit.lagrange_basis_loop0]
  apply loop.spec_decr_nat (fun s => size.val - s.2.val)
    (fun s => s.2.val ≤ size.val ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ t, t < s.2.val →
        toRq (s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          = ∏ u ∈ Finset.range n,
            (if Nat.testBit t u then toRq (w.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))
              else 1 - toRq (w.val.getD u (alloc.vec.Vec.new cpoly.field.Fp))))
  · rintro ⟨o1, i1⟩ ⟨hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [evalsplit.lagrange_basis_loop0.body]
    by_cases hlt : i1 < size
    · rw [if_pos hlt]
      step as ⟨one, hWone, hone⟩
      step with lagrange_basis_inner_loop_spec w nn i1 one one 0#usize hw hn hWone hone
        (by simp) hWone (by simp [hone]) as ⟨a1, hWa1, ha1⟩
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      and_intros
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro y hy
        rw [ho2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWa1
      · intro t ht
        rw [hi2] at ht
        rcases Nat.lt_or_ge t i1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = o1.val.length := by omega
          rw [hteq, ho2, getD_append_eq, ha1, hlen1]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = size.val := by scalar_tac
      exact ⟨by rw [hlen1, heq, hsize], hwf1, by
        intro t ht; exact hval1 t (by rw [heq, hsize]; exact ht)⟩
  · exact ⟨hi, hlen, hwf, hval⟩

/-- The spec's Lagrange basis, entrywise, in the vocabulary of the extracted
vector. -/
theorem lagrangeBasis_get_toVector {n : ℕ} (w : linalg.PolyVec) (t : Fin (2 ^ n)) :
    (CMlPolynomialEval.lagrangeBasis (toVector (n := n) w)).get t
      = ∏ s ∈ Finset.range n,
        (if Nat.testBit t.val s then toRq (w.val.getD s (alloc.vec.Vec.new cpoly.field.Fp))
          else 1 - toRq (w.val.getD s (alloc.vec.Vec.new cpoly.field.Fp))) := by
  rw [Hachi.lagrangeBasis_get, ← Fin.prod_univ_eq_prod_range
    (fun s => if Nat.testBit t.val s then
      toRq (w.val.getD s (alloc.vec.Vec.new cpoly.field.Fp))
      else 1 - toRq (w.val.getD s (alloc.vec.Vec.new cpoly.field.Fp))) n]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  simp only [BitVec.getLsb_eq_getElem, Fin.getElem_fin, BitVec.getElem_ofFin, toVector,
    Vector.get_ofFn, toVec]

/-- `lagrange_basis` computes `CMlPolynomialEval.lagrangeBasis` of the
represented point, entrywise (the multilinear equality kernel `eq̃(·, w)`). -/
theorem lagrange_basis_spec {n : ℕ} (w : linalg.PolyVec)
    (hw : WfVec n w) (hn : 2 ^ n ≤ Usize.max) :
    evalsplit.lagrange_basis w
      ⦃ z => WfVec (2 ^ n) z ∧
        toVec (k := 2 ^ n) z
          = (CMlPolynomialEval.lagrangeBasis (toVector (n := n) w)).get ⦄ := by
  rw [evalsplit.lagrange_basis]
  simp only [linalg.PolyVec.len]
  have hnn : (alloc.vec.Vec.len w).val = n := by simpa using hw.1
  step with two_pow_spec (alloc.vec.Vec.len w) (by rw [hnn]; exact hn) as ⟨size, hsize⟩
  step with lagrange_basis_outer_loop_spec w (alloc.vec.Vec.len w) size
    (alloc.vec.Vec.new ring.Rq) 0#usize hw hnn (by rw [hsize, hnn]) (by simp)
    (by simp) (by intro y hy; simp at hy) (by intro t ht; simp at ht)
    as ⟨z, hzlen, hzwf, hzval⟩
  simp only [linalg.PolyVec.new, WP.spec_ok]
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext t
  rw [lagrangeBasis_get_toVector]
  exact hzval t.val t.isLt

/-! ## The split bilinear form (`linalg::split_form`) -/

/-- `split_form` is ArkLib's `splitForm`: `⟨u, M *ᵥ v⟩`. Generic in the shape,
like `mat_vec_mul_spec`, and total under the same well-formedness. -/
theorem split_form_spec {a b : ℕ} (m : linalg.PolyMatrix) (u v : linalg.PolyVec)
    (hm : WfMat a b m) (hu : WfVec a u) (hv : WfVec b v) :
    linalg.PolyMatrix.split_form m u v
      ⦃ z => Wf z ∧
        toRq z = ArkLib.Lattices.splitForm (toMat (rows := a) (cols := b) m)
          (toVec (k := a) u) (toVec (k := b) v) ⦄ := by
  rw [linalg.PolyMatrix.split_form]
  step with mat_vec_mul_spec (rows := a) (cols := b) m v hm hv as ⟨mv, hWmv, hmv⟩
  apply spec_mono (dot_spec (k := a) u mv hu hWmv)
  rintro z ⟨hz, hzval⟩
  exact ⟨hz, by rw [hzval, hmv, ArkLib.Lattices.splitForm]⟩

/-! ## The reshapes -/

/-- `to_matrix` is ArkLib's `Hachi.toMatrix` at the crate's split: a
`2^nl × 2^nh` matrix whose `(i, j)` entry is coefficient `splitEquiv (j, i)`.
The length hypothesis is the `MlPoly` shape invariant (`ML_POLY_LEN = 1048576`),
which Aeneas cannot see across the privacy boundary. -/
theorem to_matrix_inner_loop_spec (p : evalsplit.MlPoly) (cols i : Std.Usize)
    (row : alloc.vec.Vec ring.Rq) (j : Std.Usize)
    (hp : WfVec (2 ^ (nl + nh)) p) (hcols : cols.val = 2 ^ nh) (hi : i.val < 2 ^ nl)
    (hj : j.val ≤ cols.val) (hlen : row.val.length = j.val)
    (hwf : ∀ y ∈ row.val, Wf y)
    (hval : ∀ t, t < j.val →
      toRq (row.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (p.val.getD (i.val + 1024 * t) (alloc.vec.Vec.new cpoly.field.Fp))) :
    evalsplit.MlPoly.to_matrix_loop0_loop0 p cols i row j
      ⦃ z => z.1 = p ∧ z.2.val.length = 2 ^ nh ∧ (∀ y ∈ z.2.val, Wf y) ∧
        ∀ t, t < 2 ^ nh →
          toRq (z.2.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = toRq (p.val.getD (i.val + 1024 * t) (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  have hplen : p.val.length = 1048576 := by have h := hp.1; norm_num at h; exact h
  have hi2 : i.val < 1024 := by norm_num at hi; omega
  have hcols4 : cols.val = 1024 := by rw [hcols]; norm_num
  rw [evalsplit.MlPoly.to_matrix_loop0_loop0]
  apply loop.spec_decr_nat (fun s => cols.val - s.2.2.val)
    (fun s => s.1 = p ∧ s.2.2.val ≤ cols.val ∧ s.2.1.val.length = s.2.2.val ∧
      (∀ y ∈ s.2.1.val, Wf y) ∧
      ∀ t, t < s.2.2.val →
        toRq (s.2.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq (p.val.getD (i.val + 1024 * t) (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨s1, r1, j1⟩ ⟨rfl, hj1, hlen1, hwf1, hval1⟩
    dsimp only at hj1 hlen1 hwf1 hval1
    simp only [evalsplit.MlPoly.to_matrix_loop0_loop0.body]
    by_cases hlt : j1 < cols
    · rw [if_pos hlt]
      have hjlt : j1.val < 2 ^ nh := by rw [← hcols]; scalar_tac
      have hjlt4 : j1.val < 1024 := by norm_num at hjlt; omega
      step with split_equiv_spec j1 i hjlt hi as ⟨k, hk⟩
      have hkv : k.val = i.val + 1024 * j1.val := by
        rw [hk, Hachi.splitEquiv_val]; norm_num
      have hkidx : k.val < s1.val.length := by rw [hplen, hkv]; omega
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hp.2 _ (List.getElem_mem hkidx)
      step as ⟨r2, hWr2, hr2⟩
      step as ⟨row2, hrow2⟩
      step as ⟨j2, hj2⟩
      and_intros
      · scalar_tac
      · rw [hrow2, hj2, List.length_append, hlen1]; simp
      · intro y hy
        rw [hrow2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr2
      · intro t ht
        rw [hj2] at ht
        rcases Nat.lt_or_ge t j1.val with htlt | htge
        · rw [hrow2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = r1.val.length := by omega
          rw [hteq, hrow2, getD_append_eq, hr2, hr, hlen1, ← hkv,
            List.getD_eq_getElem _ _ hkidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : j1.val = cols.val := by scalar_tac
      exact ⟨rfl, by rw [hlen1, heq, hcols], hwf1, by
        intro t ht; exact hval1 t (by rw [heq, hcols]; exact ht)⟩
  · exact ⟨rfl, hj, hlen, hwf, hval⟩


/-- The outer loop of `MlPoly::to_matrix`: row `s` already written is the row of the
reshaped matrix. -/
theorem to_matrix_outer_loop_spec (p : evalsplit.MlPoly) (rows cols : Std.Usize)
    (out : alloc.vec.Vec linalg.PolyVec) (i : Std.Usize)
    (hp : WfVec (2 ^ (nl + nh)) p) (hrows : rows.val = 2 ^ nl) (hcols : cols.val = 2 ^ nh)
    (hi : i.val ≤ rows.val) (hlen : out.val.length = i.val)
    (hwf : ∀ r ∈ out.val, WfVec (2 ^ nh) r)
    (hval : ∀ s, s < i.val → ∀ t, t < 2 ^ nh →
      toRq ((out.val.getD s (alloc.vec.Vec.new ring.Rq)).val.getD t
          (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (p.val.getD (s + 1024 * t) (alloc.vec.Vec.new cpoly.field.Fp))) :
    evalsplit.MlPoly.to_matrix_loop0 p rows cols out i
      ⦃ z => z.val.length = 2 ^ nl ∧ (∀ r ∈ z.val, WfVec (2 ^ nh) r) ∧
        ∀ s, s < 2 ^ nl → ∀ t, t < 2 ^ nh →
          toRq ((z.val.getD s (alloc.vec.Vec.new ring.Rq)).val.getD t
              (alloc.vec.Vec.new cpoly.field.Fp))
            = toRq (p.val.getD (s + 1024 * t) (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [evalsplit.MlPoly.to_matrix_loop0]
  apply loop.spec_decr_nat (fun s => rows.val - s.2.2.val)
    (fun s => s.1 = p ∧ s.2.2.val ≤ rows.val ∧ s.2.1.val.length = s.2.2.val ∧
      (∀ r ∈ s.2.1.val, WfVec (2 ^ nh) r) ∧
      ∀ u, u < s.2.2.val → ∀ t, t < 2 ^ nh →
        toRq ((s.2.1.val.getD u (alloc.vec.Vec.new ring.Rq)).val.getD t
            (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq (p.val.getD (u + 1024 * t) (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨s1, o1, i1⟩ ⟨rfl, hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [evalsplit.MlPoly.to_matrix_loop0.body]
    by_cases hlt : i1 < rows
    · rw [if_pos hlt]
      have hilt : i1.val < 2 ^ nl := by rw [← hrows]; scalar_tac
      step with to_matrix_inner_loop_spec s1 cols i1 (alloc.vec.Vec.new ring.Rq) 0#usize
        hp hcols hilt (by simp) (by simp) (by intro y hy; simp at hy)
        (by intro t ht; simp at ht) as ⟨z1, z2, hz1, hz2, hz3, hz4⟩
      simp only [linalg.PolyVec.new]
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      and_intros
      · exact hz1
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro r hr
        rw [ho2] at hr
        rcases List.mem_append.mp hr with h | h
        · exact hwf1 r h
        · rw [List.mem_singleton.mp h]; exact ⟨hz2, hz3⟩
      · intro u hu t ht
        rw [hi2] at hu
        rcases Nat.lt_or_ge u i1.val with hult | huge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 u hult t ht
        · have hueq : u = o1.val.length := by omega
          rw [hueq, ho2, getD_append_eq, hlen1]
          exact hz4 t ht
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = rows.val := by scalar_tac
      exact ⟨by rw [hlen1, heq, hrows], hwf1, by
        intro u hu t ht; exact hval1 u (by rw [heq, hrows]; exact hu) t ht⟩
  · exact ⟨rfl, hi, hlen, hwf, hval⟩

/-- The represented coefficient at a split index. -/
theorem toMlPoly_get (p : evalsplit.MlPoly) (k : Fin (2 ^ (nl + nh))) :
    (toMlPoly p).get k = toRq (p.val.getD k.val (alloc.vec.Vec.new cpoly.field.Fp)) := by
  simp only [toMlPoly, toVector, Vector.get_ofFn, toVec]

theorem to_matrix_spec (p : evalsplit.MlPoly) (hp : WfVec (2 ^ (nl + nh)) p) :
    evalsplit.MlPoly.to_matrix p
      ⦃ m => WfMat (2 ^ nl) (2 ^ nh) m ∧
        toMat (rows := 2 ^ nl) (cols := 2 ^ nh) m = Hachi.toMatrix (toMlPoly p) ⦄ := by
  have hlow : (params.ML_LOW_LEN).val = 2 ^ nl := by norm_num [params.ML_LOW_LEN]
  have hhigh : (params.ML_HIGH_LEN).val = 2 ^ nh := by norm_num [params.ML_HIGH_LEN]
  rw [evalsplit.MlPoly.to_matrix]
  step with to_matrix_outer_loop_spec p params.ML_LOW_LEN params.ML_HIGH_LEN
    (alloc.vec.Vec.new linalg.PolyVec) 0#usize hp hlow hhigh (by simp [hlow])
    (by simp) (by intro r hr; simp at hr) (by intro s hs; simp at hs)
    as ⟨z, hzlen, hzwf, hzval⟩
  simp only [linalg.PolyMatrix.new, WP.spec_ok]
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i j
  rw [toMat_apply]
  simp only [toVec, Hachi.toMatrix, toMlPoly_get, Hachi.splitEquiv_val]
  rw [hzval i.val i.isLt j.val j.isLt]
  norm_num

/-- `to_polynomial` is ArkLib's `Hachi.toPolynomial`, the inverse reshape. -/
theorem to_polynomial_loop_spec (m : linalg.PolyMatrix) (len : Std.Usize)
    (out : alloc.vec.Vec ring.Rq) (k : Std.Usize)
    (hm : WfMat (2 ^ nl) (2 ^ nh) m) (hlenv : len.val = 2 ^ (nl + nh))
    (hk : k.val ≤ len.val) (hlen : out.val.length = k.val)
    (hwf : ∀ y ∈ out.val, Wf y)
    (hval : ∀ t, t < k.val →
      toRq (out.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq ((m.val.getD (t % 1024) (alloc.vec.Vec.new ring.Rq)).val.getD (t / 1024)
            (alloc.vec.Vec.new cpoly.field.Fp))) :
    evalsplit.to_polynomial_loop m len out k
      ⦃ z => z.val.length = 2 ^ (nl + nh) ∧ (∀ y ∈ z.val, Wf y) ∧
        ∀ t, t < 2 ^ (nl + nh) →
          toRq (z.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = toRq ((m.val.getD (t % 1024) (alloc.vec.Vec.new ring.Rq)).val.getD (t / 1024)
                (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  have hmlen : m.val.length = 1024 := by have h := hm.1; norm_num at h; exact h
  have hlen8 : len.val = 1048576 := by rw [hlenv]; norm_num
  rw [evalsplit.to_polynomial_loop]
  apply loop.spec_decr_nat (fun s => len.val - s.2.val)
    (fun s => s.2.val ≤ len.val ∧ s.1.val.length = s.2.val ∧ (∀ y ∈ s.1.val, Wf y) ∧
      ∀ t, t < s.2.val →
        toRq (s.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq ((m.val.getD (t % 1024) (alloc.vec.Vec.new ring.Rq)).val.getD (t / 1024)
              (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨o1, k1⟩ ⟨hk1, hlen1, hwf1, hval1⟩
    dsimp only at hk1 hlen1 hwf1 hval1
    simp only [evalsplit.to_polynomial_loop.body]
    by_cases hlt : k1 < len
    · rw [if_pos hlt]
      have hk18 : k1.val < 1048576 := by scalar_tac
      have hkbound : k1.val < 2 ^ (nl + nh) := by rw [← hlenv]; scalar_tac
      obtain ⟨e1, e2⟩ := splitEquiv_symm_val ⟨k1.val, hkbound⟩
      step with split_equiv_inv_spec k1 hkbound as ⟨x, y, hx, hy⟩
      have hxv : x.val = k1.val / 1024 := by rw [hx, e1]
      have hyv : y.val = k1.val % 1024 := by rw [hy, e2]
      have hyidx : y.val < m.val.length := by rw [hmlen, hyv]; omega
      simp only [linalg.PolyMatrix.row]
      step as ⟨pv, hpv⟩
      have hWpv : WfVec (2 ^ nh) pv := by
        rw [hpv]; exact hm.2 _ (List.getElem_mem hyidx)
      have hpvlen : pv.val.length = 1024 := by have h := hWpv.1; norm_num at h; exact h
      have hxidx : x.val < pv.val.length := by rw [hpvlen, hxv]; omega
      simp only [linalg.PolyVec.get]
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hWpv.2 _ (List.getElem_mem hxidx)
      step as ⟨r2, hWr2, hr2⟩
      step as ⟨o2, ho2⟩
      step as ⟨k2, hk2⟩
      and_intros
      · scalar_tac
      · rw [ho2, hk2, List.length_append, hlen1]; simp
      · intro z hz
        rw [ho2] at hz
        rcases List.mem_append.mp hz with h | h
        · exact hwf1 z h
        · rw [List.mem_singleton.mp h]; exact hWr2
      · intro t ht
        rw [hk2] at ht
        rcases Nat.lt_or_ge t k1.val with htlt | htge
        · rw [ho2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = o1.val.length := by omega
          rw [hteq, ho2, getD_append_eq, hr2, hr, hlen1, ← hxv, ← hyv,
            List.getD_eq_getElem _ _ hyidx, ← hpv,
            List.getD_eq_getElem _ _ hxidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : k1.val = len.val := by scalar_tac
      exact ⟨by rw [hlen1, heq, hlenv], hwf1, by
        intro t ht; exact hval1 t (by rw [heq, hlenv]; exact ht)⟩
  · exact ⟨hk, hlen, hwf, hval⟩

theorem to_polynomial_spec (m : linalg.PolyMatrix) (hm : WfMat (2 ^ nl) (2 ^ nh) m) :
    evalsplit.to_polynomial m
      ⦃ p => WfVec (2 ^ (nl + nh)) p ∧
        toMlPoly p = Hachi.toPolynomial (toMat (rows := 2 ^ nl) (cols := 2 ^ nh) m) ⦄ := by
  have hpoly : (params.ML_POLY_LEN).val = 2 ^ (nl + nh) := by
    norm_num [params.ML_POLY_LEN]
  rw [evalsplit.to_polynomial]
  step with to_polynomial_loop_spec m params.ML_POLY_LEN (alloc.vec.Vec.new ring.Rq) 0#usize
    hm hpoly (by simp) (by simp) (by intro y hy; simp at hy) (by intro t ht; simp at ht)
    as ⟨z, hzlen, hzwf, hzval⟩
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  have hfun : toVec (k := 2 ^ (nl + nh)) z
      = fun t => toMat (rows := 2 ^ nl) (cols := 2 ^ nh) m
          ((Hachi.splitEquiv nl nh).symm t).2 ((Hachi.splitEquiv nl nh).symm t).1 := by
    funext t
    obtain ⟨e1, e2⟩ := splitEquiv_symm_val t
    simp only [toVec, toMat_apply, e1, e2]
    exact hzval t.val t.isLt
  simp only [toMlPoly, toVector, hfun, Hachi.toPolynomial]

/-- `to_matrix_eval` is ArkLib's `Hachi.toMatrixEval` — the same reshape on the
hypercube-value reading (a distinct spec definition on a distinct spec type). -/
theorem to_matrix_eval_inner_loop_spec (p : evalsplit.MlEvals) (cols i : Std.Usize)
    (row : alloc.vec.Vec ring.Rq) (j : Std.Usize)
    (hp : WfVec (2 ^ (nl + nh)) p) (hcols : cols.val = 2 ^ nh) (hi : i.val < 2 ^ nl)
    (hj : j.val ≤ cols.val) (hlen : row.val.length = j.val)
    (hwf : ∀ y ∈ row.val, Wf y)
    (hval : ∀ t, t < j.val →
      toRq (row.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (p.val.getD (i.val + 1024 * t) (alloc.vec.Vec.new cpoly.field.Fp))) :
    evalsplit.MlEvals.to_matrix_eval_loop0_loop0 p cols i row j
      ⦃ z => z.1 = p ∧ z.2.val.length = 2 ^ nh ∧ (∀ y ∈ z.2.val, Wf y) ∧
        ∀ t, t < 2 ^ nh →
          toRq (z.2.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
            = toRq (p.val.getD (i.val + 1024 * t) (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  have hplen : p.val.length = 1048576 := by have h := hp.1; norm_num at h; exact h
  have hi2 : i.val < 1024 := by norm_num at hi; omega
  have hcols4 : cols.val = 1024 := by rw [hcols]; norm_num
  rw [evalsplit.MlEvals.to_matrix_eval_loop0_loop0]
  apply loop.spec_decr_nat (fun s => cols.val - s.2.2.val)
    (fun s => s.1 = p ∧ s.2.2.val ≤ cols.val ∧ s.2.1.val.length = s.2.2.val ∧
      (∀ y ∈ s.2.1.val, Wf y) ∧
      ∀ t, t < s.2.2.val →
        toRq (s.2.1.val.getD t (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq (p.val.getD (i.val + 1024 * t) (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨s1, r1, j1⟩ ⟨rfl, hj1, hlen1, hwf1, hval1⟩
    dsimp only at hj1 hlen1 hwf1 hval1
    simp only [evalsplit.MlEvals.to_matrix_eval_loop0_loop0.body]
    by_cases hlt : j1 < cols
    · rw [if_pos hlt]
      have hjlt : j1.val < 2 ^ nh := by rw [← hcols]; scalar_tac
      have hjlt4 : j1.val < 1024 := by norm_num at hjlt; omega
      step with split_equiv_spec j1 i hjlt hi as ⟨k, hk⟩
      have hkv : k.val = i.val + 1024 * j1.val := by
        rw [hk, Hachi.splitEquiv_val]; norm_num
      have hkidx : k.val < s1.val.length := by rw [hplen, hkv]; omega
      step as ⟨r, hr⟩
      have hWr : Wf r := by rw [hr]; exact hp.2 _ (List.getElem_mem hkidx)
      step as ⟨r2, hWr2, hr2⟩
      step as ⟨row2, hrow2⟩
      step as ⟨j2, hj2⟩
      and_intros
      · scalar_tac
      · rw [hrow2, hj2, List.length_append, hlen1]; simp
      · intro y hy
        rw [hrow2] at hy
        rcases List.mem_append.mp hy with h | h
        · exact hwf1 y h
        · rw [List.mem_singleton.mp h]; exact hWr2
      · intro t ht
        rw [hj2] at ht
        rcases Nat.lt_or_ge t j1.val with htlt | htge
        · rw [hrow2, getD_append_lt _ _ _ (by omega), hval1 t htlt]
        · have hteq : t = r1.val.length := by omega
          rw [hteq, hrow2, getD_append_eq, hr2, hr, hlen1, ← hkv,
            List.getD_eq_getElem _ _ hkidx]
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : j1.val = cols.val := by scalar_tac
      exact ⟨rfl, by rw [hlen1, heq, hcols], hwf1, by
        intro t ht; exact hval1 t (by rw [heq, hcols]; exact ht)⟩
  · exact ⟨rfl, hj, hlen, hwf, hval⟩

/-- The outer loop of `MlEvals::to_matrix_eval`. -/
theorem to_matrix_eval_outer_loop_spec (p : evalsplit.MlEvals) (rows cols : Std.Usize)
    (out : alloc.vec.Vec linalg.PolyVec) (i : Std.Usize)
    (hp : WfVec (2 ^ (nl + nh)) p) (hrows : rows.val = 2 ^ nl) (hcols : cols.val = 2 ^ nh)
    (hi : i.val ≤ rows.val) (hlen : out.val.length = i.val)
    (hwf : ∀ r ∈ out.val, WfVec (2 ^ nh) r)
    (hval : ∀ s, s < i.val → ∀ t, t < 2 ^ nh →
      toRq ((out.val.getD s (alloc.vec.Vec.new ring.Rq)).val.getD t
          (alloc.vec.Vec.new cpoly.field.Fp))
        = toRq (p.val.getD (s + 1024 * t) (alloc.vec.Vec.new cpoly.field.Fp))) :
    evalsplit.MlEvals.to_matrix_eval_loop0 p rows cols out i
      ⦃ z => z.val.length = 2 ^ nl ∧ (∀ r ∈ z.val, WfVec (2 ^ nh) r) ∧
        ∀ s, s < 2 ^ nl → ∀ t, t < 2 ^ nh →
          toRq ((z.val.getD s (alloc.vec.Vec.new ring.Rq)).val.getD t
              (alloc.vec.Vec.new cpoly.field.Fp))
            = toRq (p.val.getD (s + 1024 * t) (alloc.vec.Vec.new cpoly.field.Fp)) ⦄ := by
  rw [evalsplit.MlEvals.to_matrix_eval_loop0]
  apply loop.spec_decr_nat (fun s => rows.val - s.2.2.val)
    (fun s => s.1 = p ∧ s.2.2.val ≤ rows.val ∧ s.2.1.val.length = s.2.2.val ∧
      (∀ r ∈ s.2.1.val, WfVec (2 ^ nh) r) ∧
      ∀ u, u < s.2.2.val → ∀ t, t < 2 ^ nh →
        toRq ((s.2.1.val.getD u (alloc.vec.Vec.new ring.Rq)).val.getD t
            (alloc.vec.Vec.new cpoly.field.Fp))
          = toRq (p.val.getD (u + 1024 * t) (alloc.vec.Vec.new cpoly.field.Fp)))
  · rintro ⟨s1, o1, i1⟩ ⟨rfl, hi1, hlen1, hwf1, hval1⟩
    dsimp only at hi1 hlen1 hwf1 hval1
    simp only [evalsplit.MlEvals.to_matrix_eval_loop0.body]
    by_cases hlt : i1 < rows
    · rw [if_pos hlt]
      have hilt : i1.val < 2 ^ nl := by rw [← hrows]; scalar_tac
      step with to_matrix_eval_inner_loop_spec s1 cols i1 (alloc.vec.Vec.new ring.Rq) 0#usize
        hp hcols hilt (by simp) (by simp) (by intro y hy; simp at hy)
        (by intro t ht; simp at ht) as ⟨z1, z2, hz1, hz2, hz3, hz4⟩
      simp only [linalg.PolyVec.new]
      step as ⟨o2, ho2⟩
      step as ⟨i2, hi2⟩
      and_intros
      · exact hz1
      · scalar_tac
      · rw [ho2, hi2, List.length_append, hlen1]; simp
      · intro r hr
        rw [ho2] at hr
        rcases List.mem_append.mp hr with h | h
        · exact hwf1 r h
        · rw [List.mem_singleton.mp h]; exact ⟨hz2, hz3⟩
      · intro u hu t ht
        rw [hi2] at hu
        rcases Nat.lt_or_ge u i1.val with hult | huge
        · rw [ho2, getD_append_lt _ _ _ (by omega)]
          exact hval1 u hult t ht
        · have hueq : u = o1.val.length := by omega
          rw [hueq, ho2, getD_append_eq, hlen1]
          exact hz4 t ht
      · scalar_tac
    · rw [if_neg hlt, WP.spec_ok]
      dsimp only
      have heq : i1.val = rows.val := by scalar_tac
      exact ⟨by rw [hlen1, heq, hrows], hwf1, by
        intro u hu t ht; exact hval1 u (by rw [heq, hrows]; exact hu) t ht⟩
  · exact ⟨rfl, hi, hlen, hwf, hval⟩

/-- The represented hypercube value at a split index. -/
theorem toMlEvals_get (p : evalsplit.MlEvals) (k : Fin (2 ^ (nl + nh))) :
    (toMlEvals p).get k = toRq (p.val.getD k.val (alloc.vec.Vec.new cpoly.field.Fp)) := by
  simp only [toMlEvals, toVector, Vector.get_ofFn, toVec]

theorem to_matrix_eval_spec (p : evalsplit.MlEvals) (hp : WfVec (2 ^ (nl + nh)) p) :
    evalsplit.MlEvals.to_matrix_eval p
      ⦃ m => WfMat (2 ^ nl) (2 ^ nh) m ∧
        toMat (rows := 2 ^ nl) (cols := 2 ^ nh) m = Hachi.toMatrixEval (toMlEvals p) ⦄ := by
  have hlow : (params.ML_LOW_LEN).val = 2 ^ nl := by norm_num [params.ML_LOW_LEN]
  have hhigh : (params.ML_HIGH_LEN).val = 2 ^ nh := by norm_num [params.ML_HIGH_LEN]
  rw [evalsplit.MlEvals.to_matrix_eval]
  step with to_matrix_eval_outer_loop_spec p params.ML_LOW_LEN params.ML_HIGH_LEN
    (alloc.vec.Vec.new linalg.PolyVec) 0#usize hp hlow hhigh (by simp [hlow])
    (by simp) (by intro r hr; simp at hr) (by intro s hs; simp at hs)
    as ⟨z, hzlen, hzwf, hzval⟩
  simp only [linalg.PolyMatrix.new, WP.spec_ok]
  refine ⟨⟨hzlen, hzwf⟩, ?_⟩
  funext i j
  rw [toMat_apply]
  simp only [toVec, Hachi.toMatrixEval, toMlEvals_get, Hachi.splitEquiv_val]
  rw [hzval i.val i.isLt j.val j.isLt]
  norm_num

/-! ## The headline evaluations -/

/-- **Headline.** `eval_split` is ArkLib's `Hachi.evalSplit` at this crate's
split: the bilinear form of the reshaped coefficient matrix against the monomial
bases of the two point halves. Through ArkLib's `evalSplit_eq_eval` this is
`CMlPolynomial.eval (toMlPoly p) (toVector xl ++ toVector xh)` — the statement
targets the definition and inherits the evaluation reading from the
specification's own theorem. -/
theorem eval_split_spec (p : evalsplit.MlPoly) (xl xh : linalg.PolyVec)
    (hp : WfVec (2 ^ (nl + nh)) p) (hxl : WfVec nl xl) (hxh : WfVec nh xh) :
    evalsplit.MlPoly.eval_split p xl xh
      ⦃ z => Wf z ∧
        toRq z = Hachi.evalSplit (toMlPoly p) (toVector (n := nl) xl)
          (toVector (n := nh) xh) ⦄ := by
  rw [evalsplit.MlPoly.eval_split]
  step with to_matrix_spec p hp as ⟨m, hmwf, hm⟩
  step with monomial_basis_spec (n := nl) xl hxl
    (by rw [show (2 : ℕ) ^ nl = 1024 by decide]; scalar_tac) as ⟨bl, hblwf, hbl⟩
  step with monomial_basis_spec (n := nh) xh hxh
    (by rw [show (2 : ℕ) ^ nh = 1024 by decide]; scalar_tac) as ⟨bh, hbhwf, hbh⟩
  apply spec_mono (split_form_spec (a := 2 ^ nl) (b := 2 ^ nh) m bl bh hmwf hblwf hbhwf)
  rintro z ⟨hz, hzval⟩
  exact ⟨hz, by rw [hzval, hm, hbl, hbh, Hachi.evalSplit]⟩

/-- **Headline.** `eval_split_eval` is ArkLib's `Hachi.evalSplitEval` (the
Lagrange / hypercube representation), with `evalSplitEval_eq_eval` supplying the
evaluation reading. -/
theorem eval_split_eval_spec (p : evalsplit.MlEvals) (xl xh : linalg.PolyVec)
    (hp : WfVec (2 ^ (nl + nh)) p) (hxl : WfVec nl xl) (hxh : WfVec nh xh) :
    evalsplit.MlEvals.eval_split_eval p xl xh
      ⦃ z => Wf z ∧
        toRq z = Hachi.evalSplitEval (toMlEvals p) (toVector (n := nl) xl)
          (toVector (n := nh) xh) ⦄ := by
  rw [evalsplit.MlEvals.eval_split_eval]
  step with to_matrix_eval_spec p hp as ⟨m, hmwf, hm⟩
  step with lagrange_basis_spec (n := nl) xl hxl
    (by rw [show (2 : ℕ) ^ nl = 1024 by decide]; scalar_tac) as ⟨bl, hblwf, hbl⟩
  step with lagrange_basis_spec (n := nh) xh hxh
    (by rw [show (2 : ℕ) ^ nh = 1024 by decide]; scalar_tac) as ⟨bh, hbhwf, hbh⟩
  apply spec_mono (split_form_spec (a := 2 ^ nl) (b := 2 ^ nh) m bl bh hmwf hblwf hbhwf)
  rintro z ⟨hz, hzval⟩
  exact ⟨hz, by rw [hzval, hm, hbl, hbh, Hachi.evalSplitEval]⟩

end HachiEquiv.EvalSplit
