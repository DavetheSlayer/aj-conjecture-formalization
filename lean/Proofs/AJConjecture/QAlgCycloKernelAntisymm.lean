import Mathlib
import AJConjecture.QAlgCycloBilateralKernel

/-!
# Antisymmetry of the bilateral kernel

`K_(j,-n-1) = -K_(j,n)`: the reflection `n ↦ -n-1` exchanges the two Pochhammer symbols of the
denominator, fixes `n(n+1)/2` and changes the sign `(-1)^n`.
-/

namespace AJConjecture

/-- The sign `(-1)^n` changes under the reflection `n ↦ -n - 1`. -/
private theorem neg_one_zpow_neg_sub_one (n : ℤ) :
    (-1 : RatFunc ℚ) ^ (-n - 1) = -(-1) ^ n := by
  rcases Int.even_or_odd n with h | h
  · have h' : Odd (-n - 1) := by
      obtain ⟨r, hr⟩ := h
      exact ⟨-r - 1, by omega⟩
    rw [h.neg_one_zpow, h'.neg_one_zpow]
  · have h' : Even (-n - 1) := by
      obtain ⟨r, hr⟩ := h
      exact ⟨-r - 1, by omega⟩
    rw [h.neg_one_zpow, h'.neg_one_zpow, neg_neg]

/-- The bilateral kernel is antisymmetric under `n ↦ -n - 1`. -/
theorem cycloBilateralKernel_neg_sub_one (j : ℕ) (n : ℤ) :
    cycloBilateralKernel j (-n - 1) = -cycloBilateralKernel j n := by
  unfold cycloBilateralKernel
  by_cases h : -((j : ℤ) + 1) ≤ n ∧ n ≤ j
  · have h' : -((j : ℤ) + 1) ≤ -n - 1 ∧ -n - 1 ≤ j := by omega
    rw [ite_eq_left h, ite_eq_left h', neg_one_zpow_neg_sub_one]
    have e1 : (j : ℤ) - (-n - 1) = (j : ℤ) + n + 1 := by ring
    have e2 : (j : ℤ) + (-n - 1) + 1 = (j : ℤ) - n := by ring
    have e3 : (-n - 1) * (-n - 1 + 1) = n * (n + 1) := by ring
    rw [e1, e2, e3]
    ring
  · have h' : ¬(-((j : ℤ) + 1) ≤ -n - 1 ∧ -n - 1 ≤ j) := by omega
    rw [ite_eq_right h, ite_eq_right h', neg_zero]

end AJConjecture
