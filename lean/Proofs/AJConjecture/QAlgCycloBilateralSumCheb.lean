import Mathlib
import AJConjecture.QAlgCycloKernelStep
import AJConjecture.QAlgCycloStep

/-!
# The bilateral transform turns `S_d(Z)` into `S_d(V)`

With `Z = Q + 1/(qQ)`, `Q = q^n`: `S_d(Z) = Q^d + q^(-d) Q^(-d)`, and the bilateral transform of
`n ↦ S_d(Z) g(n)` is `S_d(V)` applied to the bilateral transform of `g`.
-/

namespace AJConjecture

/-- The bilateral transform intertwines multiplication by `Z = Q + 1/(qQ)` with the operator
`V`. -/
private theorem cycloBilateralSum_mul_step (g : ℤ → RatFunc ℚ) (j : ℕ) :
    cycloBilateralSum (fun n ↦ (qParam ^ n + (qParam * qParam ^ n)⁻¹) * g n) j =
      cycloStep (cycloBilateralSum g) j := by
  have hsub : ∑ n ∈ Finset.Icc (-((j : ℤ) + 1)) (j : ℤ), cycloBilateralKernel (j - 1) n * g n =
      cycloBilateralSum g (j - 1) := by
    symm
    refine Finset.sum_subset ?_ ?_
    · intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      omega
    · intro n _ hn
      rw [Finset.mem_Icc] at hn
      rw [cycloBilateralKernel, ite_eq_right hn, zero_mul]
  rw [cycloStep, ← hsub, cycloBilateralSum, cycloBilateralSum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [← mul_assoc, mul_comm (cycloBilateralKernel j n), cycloBilateralKernel_mul_step]
  ring

/-- The three-term recurrence `s_(d+2) = Z s_(d+1) - q⁻¹ s_d` of
`s_d = Q^d + q^(-d) Q^(-d)`. -/
private theorem cycloChebSymbol_add_two (d : ℕ) (n : ℤ) :
    qParam ^ (n * ((d + 2 : ℕ) : ℤ)) +
        qParam ^ (-((d + 2 : ℕ) : ℤ)) * qParam ^ (-(n * ((d + 2 : ℕ) : ℤ))) =
      (qParam ^ n + (qParam * qParam ^ n)⁻¹) *
          (qParam ^ (n * ((d + 1 : ℕ) : ℤ)) +
            qParam ^ (-((d + 1 : ℕ) : ℤ)) * qParam ^ (-(n * ((d + 1 : ℕ) : ℤ)))) -
        qParam⁻¹ * (qParam ^ (n * (d : ℤ)) + qParam ^ (-(d : ℤ)) * qParam ^ (-(n * (d : ℤ)))) := by
  have hq := qParam_ne_zero
  have hQ : qParam ^ n ≠ 0 := zpow_ne_zero n hq
  simp only [zpow_neg, zpow_mul, zpow_natCast]
  field_simp
  ring

/-- The bilateral transform intertwines multiplication by `Q^d + q^(-d) Q^(-d)` with the twisted
Chebyshev operator `S_d(V)`. -/
theorem cycloBilateralSum_cheb (d : ℕ) (g : ℤ → RatFunc ℚ) (j : ℕ) :
    cycloBilateralSum
        (fun n ↦ (qParam ^ (n * d) + qParam ^ (-(d : ℤ)) * qParam ^ (-(n * d))) * g n) j =
      cycloCheb d (cycloBilateralSum g) j := by
  induction d using Nat.twoStepInduction generalizing g j with
  | zero =>
    simp only [cycloCheb, cycloBilateralSum, Nat.cast_zero, mul_zero, neg_zero, zpow_zero,
      mul_one]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    ring
  | one =>
    rw [cycloCheb, ← cycloBilateralSum_mul_step]
    simp only [cycloBilateralSum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [Nat.cast_one, mul_one, zpow_neg, zpow_neg, zpow_one, mul_inv]
  | more d ih0 ih1 =>
    have hsplit : cycloBilateralSum (fun n ↦ (qParam ^ (n * ((d + 2 : ℕ) : ℤ)) +
        qParam ^ (-((d + 2 : ℕ) : ℤ)) * qParam ^ (-(n * ((d + 2 : ℕ) : ℤ)))) * g n) j =
        cycloBilateralSum (fun n ↦ (qParam ^ n + (qParam * qParam ^ n)⁻¹) *
          ((qParam ^ (n * ((d + 1 : ℕ) : ℤ)) +
            qParam ^ (-((d + 1 : ℕ) : ℤ)) * qParam ^ (-(n * ((d + 1 : ℕ) : ℤ)))) * g n)) j -
        qParam⁻¹ * cycloBilateralSum (fun n ↦ (qParam ^ (n * (d : ℤ)) +
          qParam ^ (-(d : ℤ)) * qParam ^ (-(n * (d : ℤ)))) * g n) j := by
      simp only [cycloBilateralSum]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      rw [cycloChebSymbol_add_two]
      ring
    rw [hsplit, cycloBilateralSum_mul_step, ih0 g j, funext fun i ↦ ih1 g i]
    rfl

end AJConjecture
