import Mathlib
import AJConjecture.QAlgEvalAtFieldZeros
import AJConjecture.QAlgGaugeOpApply
import AJFamily.Quantum.TorusFormulaEven

/-!
# Gauging annihilators of the torus formula

Gauging turns an annihilator of `torusWhiteheadFormula a` into a tail annihilator of the even
reduced formula.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The gauge of an operator in the localised annihilator of `torusWhiteheadFormula a`
annihilates the even reduced formula at all large colours. -/
theorem exists_tail_annihilator_gaugeOp_torus (a : ℕ) {Q : RecOp}
    (hann : ∃ c : Coeff, c ≠ 0 ∧
      ∀ n : ℤ, opApplyField (Polynomial.C c * Q) (torusWhiteheadFormula a) n = 0) :
    ∃ n₁ : ℤ, ∀ n : ℤ, n₁ ≤ n → opApplyField (gaugeOp Q) (torusReducedFormulaEven a) n = 0 := by
  obtain ⟨c, hc, hann⟩ := hann
  obtain ⟨n₀, hn₀⟩ := exists_forall_ge_evalAtField_ne_zero hc
  refine ⟨n₀, fun n hn ↦ ?_⟩
  have hfun : torusWhiteheadFormula a = fun m ↦ quantumInt m * torusReducedFormulaEven a m :=
    funext (torusWhiteheadFormula_eq_quantumInt_mul a)
  have h := hann n
  rw [opApplyField_C_mul_left, hfun] at h
  rw [opApplyField_gaugeOp, (mul_eq_zero.mp h).resolve_left (hn₀ n hn), mul_zero]

end AJConjecture
