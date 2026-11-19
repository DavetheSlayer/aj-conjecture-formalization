import Mathlib
import AJConjecture.QAlgEvalAtFieldZeros
import AJConjecture.QAlgGaugeOpApply
import AJConjecture.QAlgGaugeOpSpecialize
import AJConjecture.QAlgSpecializeDvdOfOreMul
import AJConjecture.QAlgGaugeToUnreduced
import AJConjecture.QAlgKillFiniteDefect
import AJConjecture.QAlgTwoSidedAnnihilator
import AJHandoff.TorusQuantum.PairQFormulaBasic
import AJHandoff.TorusQuantum.PairQTailAnnihilator

/-!
# The quantum side of Theorem T for the formula of `T(r, s)`

For `f = pairQFormula (pairQOddColor r s)`:

* `pairQ_exists_annihilator`: `f` has a nonzero annihilator valid at every integer colour, up to a
  nonzero left coefficient (as `exists_annihilator_torusWhiteheadFormula`: the tail annihilator,
  reflected through the evenness of `F` (`exists_annihilator_outside_finite_of_even`), with the
  finitely many remaining colours killed by a coefficient
  (`exists_C_mul_annihilator_of_outside_finite`) and gauged to `[n] F` by
  `exists_gauge_quantumInt_mul`);
* `pairQ_extraFactor_dvd_specialize`: `E` divides the specialization `Q(-1, M, L)` of every
  primitive operator in the localized annihilator of `f` (as
  `extraFactor_dvd_specialize_of_annihilates_torusWhiteheadFormula`: the gauge of `Q` is a tail
  annihilator of `F` (`pairQ_exists_tail_annihilator_gaugeOp`), hence a pseudo-multiple of `P_(rs)`,
  whose symbol contains `E` (`extraFactor_dvd_specialize_famTransferOp`)).

`pairQ_exists_tail_annihilator_gaugeOp` holds for every input `u`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The gauge of an operator in the localized annihilator of `pairQFormula u` annihilates the even
reduced formula at all large colours. -/
theorem pairQ_exists_tail_annihilator_gaugeOp (u : ℕ → RatFunc ℚ) {Q : RecOp}
    (hann : ∃ c : Coeff, c ≠ 0 ∧
      ∀ n : ℤ, opApplyField (Polynomial.C c * Q) (pairQFormula u) n = 0) :
    ∃ n₁ : ℤ, ∀ n : ℤ, n₁ ≤ n → opApplyField (gaugeOp Q) (pairQReducedFormulaEven u) n = 0 := by
  obtain ⟨c, hc, hann⟩ := hann
  obtain ⟨n₀, hn₀⟩ := exists_forall_ge_evalAtField_ne_zero hc
  refine ⟨n₀, fun n hn ↦ ?_⟩
  have hfun : pairQFormula u = fun m ↦ quantumInt m * pairQReducedFormulaEven u m :=
    funext (pairQFormula_eq_quantumInt_mul u)
  have h := hann n
  rw [opApplyField_C_mul_left, hfun] at h
  rw [opApplyField_gaugeOp, (mul_eq_zero.mp h).resolve_left (hn₀ n hn), mul_zero]

theorem pairQ_exists_annihilator (r s : ℕ) (h : IsTorusPair r s) :
    ∃ Q : RecOp, Q ≠ 0 ∧ ∃ c : Coeff, c ≠ 0 ∧
      ∀ n : ℤ, opApplyField (Polynomial.C c * Q) (pairQFormula (pairQOddColor r s)) n = 0 := by
  obtain ⟨G, hG, hGann⟩ := pairQ_exists_tail_annihilator r s h
  obtain ⟨Q₀, hQ₀, N, hN⟩ :=
    exists_annihilator_outside_finite_of_even (pairQReducedFormulaEven_neg _) hG hGann
  obtain ⟨c, hc, hc0⟩ := exists_C_mul_annihilator_of_outside_finite hN
  obtain ⟨Q, hQ, hQann⟩ := exists_gauge_quantumInt_mul (Polynomial.C c * Q₀)
  have hne : Polynomial.C c * Q₀ ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hQ₀
  have hfun : pairQFormula (pairQOddColor r s) =
      fun m ↦ quantumInt m * pairQReducedFormulaEven (pairQOddColor r s) m :=
    funext (pairQFormula_eq_quantumInt_mul _)
  refine ⟨Q, hQ hne, 1, one_ne_zero, fun n ↦ ?_⟩
  rw [Polynomial.C_1, one_mul, hfun]
  exact hQann (pairQReducedFormulaEven (pairQOddColor r s)) n (hc0 n)

theorem pairQ_extraFactor_dvd_specialize (r s : ℕ) (h : IsTorusPair r s) {Q : RecOp}
    (hQ : Q.IsPrimitive)
    (hann : ∃ c : Coeff, c ≠ 0 ∧
      ∀ n : ℤ, opApplyField (Polynomial.C c * Q) (pairQFormula (pairQOddColor r s)) n = 0) :
    toComparison extraFactor ∣ toComparison (specialize Q) := by
  obtain ⟨n₁, hn₁⟩ := pairQ_exists_tail_annihilator_gaugeOp _ hann
  obtain ⟨β, hβ, T, hT⟩ := pairQ_exists_C_mul_eq_oreMul_famTransferOp r s h hn₁
  have hX : (X ^ 2 - 1 : ℤ[X]) ≠ 0 := by
    intro h0
    have h1 := congrArg (Polynomial.eval 0) h0
    norm_num at h1
  have hm : 1 ≤ r * s := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := h.1; omega) (by have := h.1; have := h.2.1; omega))
  have hspec : specialize (gaugeOp Q) ≠ 0 := by
    rw [specialize_gaugeOp]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hX) (specialize_ne_zero_of_isPrimitive hQ)
  have h1 : toComparison (specialize (famTransferOp (r * s))) ∣
      toComparison (specialize (gaugeOp Q)) :=
    toComparison_specialize_dvd_of_oreMul hβ hT hspec (specialize_famTransferOp_ne_zero _ hm)
  have h2 := (extraFactor_dvd_specialize_famTransferOp _ hm).trans h1
  rw [specialize_gaugeOp, map_mul] at h2
  exact (isUnit_toComparison_coeff_of_ne_zero hX).dvd_mul_left.mp h2

end AJConjecture
