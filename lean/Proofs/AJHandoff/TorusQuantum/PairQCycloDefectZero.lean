import Mathlib
import AJConjecture.QAlgQParamBasic
import AJHandoff.TorusQuantum.PairQFormula

/-!
# The first defect

For every input with `u_0 = 1` and every `m ≥ 1`, `e_0 = 2(1 - q)`: `D_0 = u_0 = 1`, the operator
`V` acts at `j = 0` as multiplication by `1 + q⁻¹`, so `(S_l(V) D)_0 = 1 + q^(-l)` for `l ≥ 1`
and `2` for `l = 0`, and `(1 + q^(1-m)) + (1 - q)(1 + q^(-m)) - q(1 + q^(-m-1)) = 2(1 - q)`.
As `torusCycloDefect_zero`, for an arbitrary input.
-/

noncomputable section

namespace AJConjecture

/-- At `j = 0` the twisted Chebyshev operator `S_d(V)` is multiplication by `1 + q^(-d)`. -/
private theorem cycloCheb_apply_zero_eq_pairQ (d : ℕ) (y : ℕ → RatFunc ℚ) :
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

/-- The cyclotomic coefficient `D_0` of an input with `u_0 = 1` is `1`. -/
private theorem pairQCycloCoeff_zero_eq_one (u : ℕ → RatFunc ℚ) (hu : u 0 = 1) :
    pairQCycloCoeff u 0 = 1 := by
  have h1 : 1 - qParam ≠ 0 := by
    have h := one_sub_qParam_zpow_ne_zero (n := 1) one_ne_zero
    rwa [zpow_one] at h
  simp only [pairQCycloCoeff, qPochhammer, hu, zero_add, Finset.sum_range_one,
    Finset.prod_range_one, Finset.prod_range_zero, pow_zero, mul_one, one_mul, Nat.zero_div,
    Nat.sub_zero]
  exact mul_one_div_cancel h1

/-- The defect at `j = 0` is `2(1 - q)`. -/
theorem pairQCycloDefect_zero (m : ℕ) (hm : 1 ≤ m) (u : ℕ → RatFunc ℚ) (hu : u 0 = 1) :
    pairQCycloDefect m u 0 = 2 * (1 - qParam) := by
  have hq := qParam_ne_zero
  rw [pairQCycloDefect, cycloCheb_apply_zero_eq_pairQ, cycloCheb_apply_zero_eq_pairQ,
    cycloCheb_apply_zero_eq_pairQ, pairQCycloCoeff_zero_eq_one u hu]
  obtain ⟨b, rfl⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  field_simp
  ring

end AJConjecture
