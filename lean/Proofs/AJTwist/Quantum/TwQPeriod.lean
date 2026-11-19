import Mathlib
import AJTwist.Quantum.TwQInput

/-!
# The Gaussian periods (Unit Q4)

Source: revision 5, Section 6.3 (`selection.tex`, "The finite Gaussian forcing module"):
"Let `w_n^{(ℓ,c)} = q^(ℓ n(n+1)) (Q^c - \hat Q^c)` be the half-interval input, and let
`G_c^{(ℓ)}` be the output of (universalbailey) on that input. … They satisfy
`G_0^{(ℓ)} = 0`, `G_(-c)^{(ℓ)} = -q^c G_c^{(ℓ)}`. The reflection identity follows from
`\hat Q = q⁻¹/Q`."

`twPeriod ℓ c` is `G_c^{(ℓ)}` as a sequence on `ℤ` (the even extension of the reduced formula of
`twPeriodInput ℓ c`, like `twReducedEven`).
-/

noncomputable section

namespace AJConjecture

/-- The Gaussian period `G_c^{(ℓ)}` as a sequence on `ℤ`. -/
def twPeriod (ℓ c : ℤ) (n : ℤ) : RatFunc ℚ :=
  pairQReducedFormulaEven (twPeriodInput ℓ c) n

theorem twPeriodInput_zero (ℓ : ℤ) (n : ℕ) : twPeriodInput ℓ 0 n = 0 := by
  rw [twPeriodInput, zero_mul, zero_mul, neg_zero, sub_self, mul_zero]

theorem twPeriodInput_neg (ℓ c : ℤ) (n : ℕ) :
    twPeriodInput ℓ (-c) n = -(qParam ^ c) * twPeriodInput ℓ c n := by
  have hq := qParam_ne_zero
  have h1 : qParam ^ (-(-c * ((n : ℤ) + 1))) = qParam ^ c * qParam ^ (c * n) := by
    rw [← zpow_add₀ hq]
    congr 1
    ring
  have h2 : qParam ^ (-c * n) = qParam ^ c * qParam ^ (-(c * ((n : ℤ) + 1))) := by
    rw [← zpow_add₀ hq]
    congr 1
    ring
  rw [twPeriodInput, twPeriodInput, h1, h2]
  ring

/-- `G_0^{(ℓ)} = 0`. -/
theorem twPeriod_zero (ℓ : ℤ) (n : ℤ) : twPeriod ℓ 0 n = 0 := by
  rw [twPeriod, pairQReducedFormulaEven, pairQReducedFormula]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [pairQCycloCoeff, Finset.sum_eq_zero fun k _ ↦ ?_, mul_zero, mul_zero]
  rw [twPeriodInput_zero, mul_zero, zero_div]

/-- `G_(-c)^{(ℓ)} = -q^c G_c^{(ℓ)}`. -/
theorem twPeriod_neg (ℓ c : ℤ) (n : ℤ) : twPeriod ℓ (-c) n = -(qParam ^ c) * twPeriod ℓ c n := by
  rw [twPeriod, twPeriod, pairQReducedFormulaEven, pairQReducedFormulaEven, pairQReducedFormula,
    pairQReducedFormula, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [pairQCycloCoeff, pairQCycloCoeff, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [twPeriodInput_neg]
  ring

end AJConjecture
