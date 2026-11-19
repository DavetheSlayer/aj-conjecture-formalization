import Mathlib
import AJConjecture.ClaspAlgBasic
import AJFamily.Quantum.TorusFormula

/-!
# The reduced formula at `N = 2`

`torusReducedFormula_two`: for `T(2, a)`, `F_2 = q (1 + q² + (1 - q) u_1) / (1 + q)`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The colour `u_0` of `T(2, a)` is `1`. -/
theorem torusOddColor_zero_eq_one (a : ℕ) : torusOddColor a 0 = 1 := by
  simp only [torusOddColor, quantumInt, Nat.cast_zero, neg_zero, Finset.Icc_self,
    Finset.sum_singleton, mul_zero, zero_add, zpow_zero, one_mul, mul_one]
  exact div_self claspAlg_ratFuncX_sq_sub_ne_zero

/-- The reduced formula of `T(2, a)` at `N = 2`. -/
theorem torusReducedFormula_two (a : ℕ) :
    torusReducedFormula a 2 =
      qParam * (1 + qParam ^ 2 + (1 - qParam) * torusOddColor a 1) / (1 + qParam) := by
  have hq := qParam_ne_zero
  have h1 : 1 - qParam ≠ 0 := by simpa using one_sub_qParam_zpow_ne_zero (n := 1) one_ne_zero
  have h2 : 1 - qParam ^ 2 ≠ 0 := by
    simpa using one_sub_qParam_zpow_ne_zero (n := 2) two_ne_zero
  have h3 : 1 - qParam ^ 3 ≠ 0 := by
    simpa using one_sub_qParam_zpow_ne_zero (n := 3) three_ne_zero
  have hp : 1 + qParam ≠ 0 := by
    intro h
    apply h2
    linear_combination (1 - qParam) * h
  simp only [torusReducedFormula, torusCyclotomicCoeff, cyclotomicKernel, qPochhammer,
    Finset.sum_range_succ, Finset.prod_range_succ, Finset.sum_range_zero,
    Finset.prod_range_zero, torusOddColor_zero_eq_one]
  norm_num [Finset.Icc_self]
  field_simp
  ring

end AJConjecture
