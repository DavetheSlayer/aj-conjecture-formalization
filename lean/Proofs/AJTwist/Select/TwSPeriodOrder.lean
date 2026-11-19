import Mathlib
import AJTwist.Select.TwSInput

/-!
# Orders of the Gaussian period inputs

`twsPeriodInput ℓ c n = q^(ℓ n(n+1)) (q^(c n) - q^(-c(n+1)))` is zero (for `c = 0`) or has order at
least `4 (ℓ n(n+1) - |c| (n+1))` at `t = 0` and degree at most `4 (ℓ n(n+1) + |c| (n+1))`
(Section 6.3 of `selection.tex`, revision 5: the valuation of `w_n^{(ℓ,c)}` is
`ℓ n² + (ℓ - c) n - c` for `c > 0`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Lower bound for the order at `t = 0` of the period input. -/
theorem tws_tOrder_periodInput_ge (ℓ c : ℤ) (n : ℕ) :
    twsPeriodInput ℓ c n = 0 ∨
      4 * (ℓ * n * ((n : ℤ) + 1) - |c| * ((n : ℤ) + 1)) ≤ pairQTOrder (twsPeriodInput ℓ c n) := by
  by_cases hc : c = 0
  · exact Or.inl (by rw [twsPeriodInput, hc, zero_mul, zero_mul, neg_zero, sub_self, mul_zero])
  refine Or.inr ?_
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have hne : 4 * (c * (n : ℤ)) ≠ 4 * -(c * ((n : ℤ) + 1)) := by
    intro h
    have h0 : c * (2 * (n : ℤ) + 1) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact hc h1
    · omega
  have hd := pairQTOrder_X_zpow_sub_zpow hne
  rw [← qParam_zpow_eq_ratFuncX_zpow, ← qParam_zpow_eq_ratFuncX_zpow] at hd
  have h := pairQTOrder_mul_eq (pairQTOrder_qParam_zpow_eq (ℓ * n * ((n : ℤ) + 1))) hd
  rw [twsPeriodInput, h.2]
  have h1 := neg_abs_le c
  have h2 := le_abs_self c
  have h3 := abs_nonneg c
  have h4 : -|c| * (n : ℤ) ≤ c * n := mul_le_mul_of_nonneg_right h1 hn
  have h5 : c * ((n : ℤ) + 1) ≤ |c| * ((n : ℤ) + 1) := mul_le_mul_of_nonneg_right h2 (by omega)
  have h6 : 4 * -(|c| * ((n : ℤ) + 1)) ≤ min (4 * (c * (n : ℤ))) (4 * -(c * ((n : ℤ) + 1))) :=
    le_min (by linarith) (by linarith)
  linarith

/-- Upper bound for the degree of the period input. -/
theorem tws_intDegree_periodInput_le (ℓ c : ℤ) (n : ℕ) :
    twsPeriodInput ℓ c n = 0 ∨
      (twsPeriodInput ℓ c n).intDegree ≤ 4 * (ℓ * n * ((n : ℤ) + 1) + |c| * ((n : ℤ) + 1)) := by
  by_cases h0 : twsPeriodInput ℓ c n = 0
  · exact Or.inl h0
  refine Or.inr ?_
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have hd : qParam ^ (c * (n : ℤ)) + -qParam ^ (-(c * ((n : ℤ) + 1))) ≠ 0 := by
    rw [← sub_eq_add_neg]
    exact right_ne_zero_of_mul h0
  have hle := RatFunc.intDegree_add_le hd
  rw [RatFunc.intDegree_neg, intDegree_qParam_zpow, intDegree_qParam_zpow] at hle
  rw [twsPeriodInput, sub_eq_add_neg, RatFunc.intDegree_mul (zpow_ne_zero _ qParam_ne_zero) hd,
    intDegree_qParam_zpow]
  have h1 := neg_abs_le c
  have h2 := le_abs_self c
  have h3 := abs_nonneg c
  have h4 : c * (n : ℤ) ≤ |c| * n := mul_le_mul_of_nonneg_right h2 hn
  have h5 : -|c| * ((n : ℤ) + 1) ≤ c * ((n : ℤ) + 1) := mul_le_mul_of_nonneg_right h1 (by omega)
  have h6 : max (4 * (c * (n : ℤ))) (4 * -(c * ((n : ℤ) + 1))) ≤ 4 * (|c| * ((n : ℤ) + 1)) :=
    max_le (by linarith) (by linarith)
  linarith

end AJConjecture
