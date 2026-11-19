import Mathlib
import AJConjecture.WhiteheadFormula

/-!
# Linearity of the action of recurrence operators

The action `opApplyField` of recurrence operators on sequences with values in `ℚ(t)` is
additive in the operator, a constant coefficient acts by its value at the colour, and the
action is a finite sum over the degrees of the operator.
-/

open Polynomial

namespace AJConjecture

/-- The action is additive in the operator. -/
theorem opApplyField_add_left (P Q : RecOp) (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField (P + Q) f n = opApplyField P f n + opApplyField Q f n := by
  simp only [opApplyField]
  refine sum_add_index P Q _ (fun i ↦ ?_) (fun i a b ↦ ?_)
  · rw [map_zero, zero_mul]
  · rw [map_add, add_mul]

/-- The action is compatible with subtraction of operators. -/
theorem opApplyField_sub_left (P Q : RecOp) (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField (P - Q) f n = opApplyField P f n - opApplyField Q f n := by
  rw [eq_sub_iff_add_eq, ← opApplyField_add_left, sub_add_cancel]

/-- A coefficient on the left acts by its value at the colour. -/
theorem opApplyField_C_mul_left (c : Coeff) (P : RecOp) (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField (C c * P) f n = evalAtField n c * opApplyField P f n := by
  simp only [opApplyField]
  rw [← smul_eq_C_mul, sum_smul_index P c _ (fun i ↦ by rw [map_zero, zero_mul]), Polynomial.sum,
    Polynomial.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, mul_assoc]

/-- The action of a monomial `c L ^ i`. -/
theorem opApplyField_monomial (i : ℕ) (c : Coeff) (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField (monomial i c) f n = evalAtField n c * f (n + i) := by
  simp only [opApplyField]
  exact sum_monomial_index c _ (by simp only [map_zero, zero_mul])

/-- The action as a sum over the degrees up to the degree of the operator. -/
theorem opApplyField_eq_sum_range (P : RecOp) (f : ℤ → RatFunc ℚ) (n : ℤ) :
    opApplyField P f n =
      ∑ i ∈ Finset.range (P.natDegree + 1), evalAtField n (P.coeff i) * f (n + i) := by
  simp only [opApplyField]
  exact sum_over_range P fun i ↦ by rw [map_zero, zero_mul]

end AJConjecture
