import Mathlib
import AJConjecture.QAlgCycloBilateralKernel
import AJConjecture.QAlgQParamBasic

/-!
# Multiplication by `Z` on the bilateral kernel is the operator `V`

`(Q + 1/(qQ)) K_(j,n) = (1/(qJ) + J) K_(j,n) - ((1 - J)/J) K_(j-1,n)` for every `j ≥ 0` and
every integer `n`, with `J = q^j`, `Q = q^n`; at `j = 0` the last term is multiplied by `0`.
-/

namespace AJConjecture

/-- The rational identity behind the step relation inside the support of `K_(i,·)`:
`I = q^i`, `Q = q^n`, `A = q^(i-n)`, `B = q^(i+n+1)`, and `s`, `E`, `Pi`, `Pa`, `Pb` stand for
the common factors. -/
private theorem kernel_step_interior_algebra (q I Q A B s E Pi Pa Pb : RatFunc ℚ)
    (hq : q ≠ 0) (hQ : Q ≠ 0) (hA : A ≠ 0) (hI : I = A * Q) (hB : B = A * Q * Q * q)
    (hPa : Pa ≠ 0) (hPb : Pb ≠ 0) (hA1 : 1 - q * A ≠ 0) (hB1 : 1 - q * B ≠ 0) :
    (Q + (q * Q)⁻¹) * (I * q * (1 - q) * (Pi * (1 - q * I)) * s * E /
        (Pa * (1 - q * A) * (Pb * (1 - q * B)))) =
      ((q * (I * q))⁻¹ + I * q) * (I * q * (1 - q) * (Pi * (1 - q * I)) * s * E /
        (Pa * (1 - q * A) * (Pb * (1 - q * B)))) -
        (1 - I * q) / (I * q) * (I * (1 - q) * Pi * s * E / (Pa * Pb)) := by
  subst hI
  field_simp
  subst hB
  ring

/-- At the two ends `n = j` and `n = -j-1` of the support, `Q + 1/(qQ) = 1/(qJ) + J`. -/
private theorem kernel_step_end_coeff (j : ℕ) (n : ℤ) (hn : n = j ∨ n = -((j : ℤ) + 1)) :
    qParam ^ n + (qParam * qParam ^ n)⁻¹ = (qParam * qParam ^ j)⁻¹ + qParam ^ j := by
  have hq := qParam_ne_zero
  rcases hn with rfl | rfl
  · rw [zpow_natCast]
    ring
  · have hz : qParam ^ (-((j : ℤ) + 1)) = (qParam * qParam ^ j)⁻¹ := by
      rw [zpow_neg, zpow_add_one₀ hq, zpow_natCast, mul_comm]
    have hj : qParam ^ j ≠ 0 := pow_ne_zero j hq
    rw [hz]
    field_simp

/-- Multiplication by `Z = Q + 1/(qQ)` on the bilateral kernel is the first-order operator `V`
in `j`. -/
theorem cycloBilateralKernel_mul_step (j : ℕ) (n : ℤ) :
    (qParam ^ n + (qParam * qParam ^ n)⁻¹) * cycloBilateralKernel j n =
      ((qParam * qParam ^ j)⁻¹ + qParam ^ j) * cycloBilateralKernel j n -
        (1 - qParam ^ j) / qParam ^ j * cycloBilateralKernel (j - 1) n := by
  have hq := qParam_ne_zero
  by_cases hs : -((j : ℤ) + 1) ≤ n ∧ n ≤ j
  · by_cases hin : -(j : ℤ) ≤ n ∧ n ≤ (j : ℤ) - 1
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have h0 : -((i : ℤ) + 1) ≤ n ∧ n ≤ (i : ℤ) := by omega
      unfold cycloBilateralKernel
      rw [Nat.add_sub_cancel, ite_eq_left hs, ite_eq_left h0]
      obtain ⟨a, ha⟩ : ∃ a : ℕ, (i : ℤ) - n = a := ⟨((i : ℤ) - n).toNat, by omega⟩
      obtain ⟨b, hb⟩ : ∃ b : ℕ, (i : ℤ) + n + 1 = b := ⟨((i : ℤ) + n + 1).toNat, by omega⟩
      have ea : (((i + 1 : ℕ) : ℤ) - n).toNat = a + 1 := by omega
      have eb : (((i + 1 : ℕ) : ℤ) + n + 1).toNat = b + 1 := by omega
      have hqi : qParam ^ i = qParam ^ a * qParam ^ n := by
        rw [← zpow_natCast qParam a, ← zpow_natCast qParam i, ← zpow_add₀ hq]
        congr 1
        omega
      have hqb : qParam ^ b = qParam ^ a * qParam ^ n * qParam ^ n * qParam := by
        rw [← zpow_natCast qParam a, ← zpow_natCast qParam b, ← zpow_add₀ hq, ← zpow_add₀ hq,
          ← zpow_add_one₀ hq]
        congr 1
        omega
      have hPi : qPochhammer qParam (i + 1) = qPochhammer qParam i * (1 - qParam * qParam ^ i) :=
        Finset.prod_range_succ _ _
      have hPa : qPochhammer qParam (a + 1) = qPochhammer qParam a * (1 - qParam * qParam ^ a) :=
        Finset.prod_range_succ _ _
      have hPb : qPochhammer qParam (b + 1) = qPochhammer qParam b * (1 - qParam * qParam ^ b) :=
        Finset.prod_range_succ _ _
      have hA1 : 1 - qParam * qParam ^ a ≠ 0 := by
        have := one_sub_qParam_zpow_ne_zero (n := (a : ℤ) + 1) (by omega)
        rwa [zpow_add_one₀ hq, zpow_natCast, mul_comm] at this
      have hB1 : 1 - qParam * qParam ^ b ≠ 0 := by
        have := one_sub_qParam_zpow_ne_zero (n := (b : ℤ) + 1) (by omega)
        rwa [zpow_add_one₀ hq, zpow_natCast, mul_comm] at this
      rw [ea, eb, ha, hb, Int.toNat_natCast, Int.toNat_natCast, hPi, hPa, hPb, pow_succ qParam i]
      exact kernel_step_interior_algebra qParam (qParam ^ i) (qParam ^ n) (qParam ^ a)
        (qParam ^ b) _ _ (qPochhammer qParam i) (qPochhammer qParam a) (qPochhammer qParam b)
        hq (zpow_ne_zero n hq) (pow_ne_zero a hq) hqi hqb (qPochhammer_qParam_ne_zero a)
        (qPochhammer_qParam_ne_zero b) hA1 hB1
    · have hlast : (1 - qParam ^ j) / qParam ^ j * cycloBilateralKernel (j - 1) n = 0 := by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · rw [pow_zero, sub_self, zero_div, zero_mul]
        · have h0 : ¬(-(((j - 1 : ℕ) : ℤ) + 1) ≤ n ∧ n ≤ ((j - 1 : ℕ) : ℤ)) := by omega
          rw [cycloBilateralKernel, ite_eq_right h0, mul_zero]
      rw [hlast, sub_zero, kernel_step_end_coeff j n (by omega)]
  · have h0 : ¬(-(((j - 1 : ℕ) : ℤ) + 1) ≤ n ∧ n ≤ ((j - 1 : ℕ) : ℤ)) := by omega
    rw [cycloBilateralKernel, cycloBilateralKernel, ite_eq_right hs, ite_eq_right h0, mul_zero,
      mul_zero, mul_zero, sub_zero]

end AJConjecture
