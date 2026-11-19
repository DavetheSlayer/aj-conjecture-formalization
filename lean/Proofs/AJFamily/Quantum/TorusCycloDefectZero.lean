import Mathlib
import AJConjecture.QAlgQParamBasic
import AJFamily.Quantum.TorusCycloDefect

/-!
# The cyclotomic defect at `j = 0`

At `j = 0`, `S_d(V)` is multiplication by `1 + q^(-d)` and `D_0 = 1`, so the defect is `2(1 - q)`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- At `j = 0` the twisted Chebyshev operator `S_d(V)` is multiplication by `1 + q^(-d)`. -/
private theorem cycloCheb_apply_zero_eq_torus (d : ℕ) (y : ℕ → RatFunc ℚ) :
    cycloCheb d y 0 = (1 + (qParam ^ d)⁻¹) * y 0 := by
  have hq := qParam_ne_zero
  induction d using Nat.twoStepInduction with
  | zero =>
    simp only [cycloCheb, pow_zero, inv_one]
    ring
  | one =>
    simp only [cycloCheb, cycloStep, pow_zero, pow_one, mul_one, sub_self, zero_div, zero_mul,
      sub_zero]
    ring
  | more d ih0 ih1 =>
    simp only [cycloCheb, cycloStep, pow_zero, mul_one, sub_self, zero_div, zero_mul, sub_zero]
    rw [show cycloCheb (d + 1) y 0 = (1 + (qParam ^ (d + 1))⁻¹) * y 0 from ih1, ih0]
    have hd : qParam ^ d ≠ 0 := pow_ne_zero d hq
    field_simp
    ring

/-- The cyclotomic coefficient `D_0` is `1`. -/
private theorem torusCyclotomicCoeff_zero_eq_one (a : ℕ) : torusCyclotomicCoeff a 0 = 1 := by
  have hD : (RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ) ≠ 0 := by
    intro h
    have h2 : (2 : ℤ) = -2 := ratFuncX_zpow_injective (sub_eq_zero.mp h)
    omega
  have h1 : 1 - qParam ≠ 0 := by
    have h := one_sub_qParam_zpow_ne_zero (n := 1) one_ne_zero
    rwa [zpow_one] at h
  have hu : torusOddColor a 0 = 1 := by
    simp only [torusOddColor, quantumInt, Nat.cast_zero, neg_zero, Finset.Icc_self,
      Finset.sum_singleton, mul_zero, zero_add, zpow_zero, one_mul, mul_one]
    exact div_self hD
  simp only [torusCyclotomicCoeff, qPochhammer, hu, zero_add, Finset.sum_range_one,
    Finset.prod_range_one, Finset.prod_range_zero, pow_zero, mul_one, one_mul, Nat.zero_div,
    Nat.sub_zero]
  exact mul_one_div_cancel h1

/-- The defect at `j = 0` is `2(1 - q)`. -/
theorem torusCycloDefect_zero (a : ℕ) (ha : 1 ≤ a) : torusCycloDefect a 0 = 2 * (1 - qParam) := by
  have hq := qParam_ne_zero
  rw [torusCycloDefect, cycloCheb_apply_zero_eq_torus, cycloCheb_apply_zero_eq_torus,
    cycloCheb_apply_zero_eq_torus, torusCyclotomicCoeff_zero_eq_one]
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have h1 : 2 * (b + 1) - 1 = 2 * b + 1 := by omega
  rw [h1]
  field_simp
  ring

end AJConjecture
