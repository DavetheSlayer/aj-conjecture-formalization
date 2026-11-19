import Mathlib
import AJConjecture.QAlgHomogenizeOpApply
import AJFamily.Quantum.FamSymbolFacts
import AJFamily.Quantum.FamTransferRhsRational

/-!
# A tail annihilator of the even reduced formula

The even reduced formula has a nonzero annihilator on the colours `n ≥ 1`, obtained from
`famTransferOp (2a)`, which maps it to a rational function of `M`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The even torus reduced formula is annihilated at all colours `n ≥ 1` by a nonzero
recurrence operator. -/
theorem exists_tail_annihilator_torusReducedFormulaEven (a : ℕ) (ha : 1 ≤ a) :
    ∃ G : RecOp, G ≠ 0 ∧ ∀ n : ℤ, 1 ≤ n → opApplyField G (torusReducedFormulaEven a) n = 0 := by
  obtain ⟨β, δ, hδ, h⟩ := exists_coeff_mul_opApplyField_famTransferOp a ha
  have hP : famTransferOp (2 * a) ≠ 0 := fun h0 ↦ by
    have hdeg := natDegree_famTransferOp (2 * a) (by omega)
    rw [h0, natDegree_zero] at hdeg
    omega
  by_cases hβ : β = 0
  · refine ⟨C δ * famTransferOp (2 * a), mul_ne_zero (C_ne_zero.mpr hδ) hP, fun n hn ↦ ?_⟩
    rw [opApplyField_C_mul_left, h n hn, hβ, map_zero]
  · refine ⟨homogenizeOp β δ (famTransferOp (2 * a)), fun h0 ↦ ?_, fun n hn ↦
      opApplyField_homogenizeOp_eq_zero (h n hn) (h (n + 1) (by omega))⟩
    have hdeg := natDegree_homogenizeOp hβ hδ hP
    rw [h0, natDegree_zero] at hdeg
    omega

end AJConjecture
