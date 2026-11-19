import Mathlib
import AJConjecture.QAlgCycloBilateralKernel
import AJConjecture.QAlgQParamBasic

/-!
# The shift relation of the bilateral kernel in `n`

`(1 - q² J Q) K_(j,n+1) = -q (Q - J) K_(j,n)` with `J = q^j`, `Q = q^n`, for every integer `n`:
inside the support it is the ratio of consecutive kernel values, and at the two ends of the
support the factors `Q - J` and `1 - q² J Q` vanish.
-/

namespace AJConjecture

/-- The rational identity behind the shift relation inside the support: `A = q^(j-n-1)`,
`B = q^(j+n+1)`, and `c`, `s`, `E`, `Pa`, `Pb` stand for the common factors. -/
private theorem kernel_shift_interior_algebra (q J Q A B c s E Pa Pb : RatFunc ℚ)
    (hJ : J = A * Q * q) (hB : B = J * Q * q) (hPa : Pa ≠ 0) (hPb : Pb ≠ 0)
    (hA1 : 1 - q * A ≠ 0) (hB1 : 1 - q * B ≠ 0) :
    (1 - q ^ 2 * J * Q) * (c * (s * -1) * (E * (Q * q)) / (Pa * (Pb * (1 - q * B)))) =
      -q * (Q - J) * (c * s * E / (Pa * (1 - q * A) * Pb)) := by
  subst hB hJ
  rw [mul_div_assoc', mul_div_assoc', div_eq_div_iff (mul_ne_zero hPa (mul_ne_zero hPb hB1))
    (mul_ne_zero (mul_ne_zero hPa hA1) hPb)]
  ring

/-- The shift relation of the bilateral kernel in `n`, at every integer. -/
theorem cycloBilateralKernel_succ (j : ℕ) (n : ℤ) :
    (1 - qParam ^ 2 * qParam ^ j * qParam ^ n) * cycloBilateralKernel j (n + 1) =
      -qParam * (qParam ^ n - qParam ^ j) * cycloBilateralKernel j n := by
  unfold cycloBilateralKernel
  by_cases h1 : -((j : ℤ) + 1) ≤ n + 1 ∧ n + 1 ≤ j
  · by_cases h0 : -((j : ℤ) + 1) ≤ n ∧ n ≤ j
    · rw [ite_eq_left h1, ite_eq_left h0]
      obtain ⟨a, ha⟩ : ∃ a : ℕ, (j : ℤ) - (n + 1) = a := ⟨((j : ℤ) - (n + 1)).toNat, by omega⟩
      obtain ⟨b, hb⟩ : ∃ b : ℕ, (j : ℤ) + n + 1 = b := ⟨((j : ℤ) + n + 1).toNat, by omega⟩
      have ea : ((j : ℤ) - n).toNat = a + 1 := by omega
      have eb : ((j : ℤ) + (n + 1) + 1).toNat = b + 1 := by omega
      have hqa : qParam ^ j = qParam ^ a * qParam ^ n * qParam := by
        rw [← zpow_natCast qParam a, ← zpow_natCast qParam j, ← zpow_add₀ qParam_ne_zero,
          ← zpow_add_one₀ qParam_ne_zero]
        congr 1
        omega
      have hqb : qParam ^ b = qParam ^ j * qParam ^ n * qParam := by
        rw [← zpow_natCast qParam b, ← zpow_natCast qParam j, ← zpow_add₀ qParam_ne_zero,
          ← zpow_add_one₀ qParam_ne_zero]
        congr 1
        omega
      have hE : (n + 1) * (n + 1 + 1) / 2 = n * (n + 1) / 2 + (n + 1) := by
        have : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
        rw [this, Int.add_mul_ediv_left _ _ (by norm_num)]
      have hs : (-1 : RatFunc ℚ) ^ (n + 1) = (-1) ^ n * -1 := by
        rw [zpow_add_one₀ (by norm_num)]
      have hPa : qPochhammer qParam (a + 1) = qPochhammer qParam a * (1 - qParam * qParam ^ a) :=
        Finset.prod_range_succ _ _
      have hPb : qPochhammer qParam (b + 1) = qPochhammer qParam b * (1 - qParam * qParam ^ b) :=
        Finset.prod_range_succ _ _
      have hA1 : 1 - qParam * qParam ^ a ≠ 0 := by
        have := one_sub_qParam_zpow_ne_zero (n := (a : ℤ) + 1) (by omega)
        rwa [zpow_add_one₀ qParam_ne_zero, zpow_natCast, mul_comm] at this
      have hB1 : 1 - qParam * qParam ^ b ≠ 0 := by
        have := one_sub_qParam_zpow_ne_zero (n := (b : ℤ) + 1) (by omega)
        rwa [zpow_add_one₀ qParam_ne_zero, zpow_natCast, mul_comm] at this
      rw [ha, ea, eb, hb, Int.toNat_natCast, Int.toNat_natCast, hE, hs, hPa, hPb,
        zpow_add₀ qParam_ne_zero, zpow_add_one₀ qParam_ne_zero]
      exact kernel_shift_interior_algebra qParam (qParam ^ j) (qParam ^ n) (qParam ^ a)
        (qParam ^ b) _ _ _ _ _ hqa hqb (qPochhammer_qParam_ne_zero a)
        (qPochhammer_qParam_ne_zero b) hA1 hB1
    · have hn : n = -((j : ℤ) + 2) := by omega
      have hz : qParam ^ 2 * qParam ^ j * qParam ^ n = 1 := by
        rw [← zpow_natCast qParam 2, ← zpow_natCast qParam j, ← zpow_add₀ qParam_ne_zero,
          ← zpow_add₀ qParam_ne_zero, hn]
        have : ((2 : ℕ) : ℤ) + (j : ℤ) + -((j : ℤ) + 2) = 0 := by push_cast; ring
        rw [this, zpow_zero]
      rw [ite_eq_right h0, hz, sub_self, zero_mul, mul_zero]
  · by_cases h0 : -((j : ℤ) + 1) ≤ n ∧ n ≤ j
    · have hn : n = j := by omega
      rw [ite_eq_right h1, hn, zpow_natCast, sub_self, mul_zero, mul_zero, zero_mul]
    · rw [ite_eq_right h1, ite_eq_right h0, mul_zero, mul_zero]

end AJConjecture
