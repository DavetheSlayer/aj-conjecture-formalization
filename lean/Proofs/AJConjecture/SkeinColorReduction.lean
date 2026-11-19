import Mathlib
import AJConjecture.SkeinScalars

/-!
# The kink scalar is nonzero

The kink scalar `θ_k = (-1)^k t^(k(k+2))` is a unit of `ℚ(t)`.
-/

open LaurentPolynomial

namespace AJConjecture

/-- The kink scalar `θ_k = (-1)^k t^(k(k+2))` is not zero. -/
theorem kinkScalar_ne_zero (k : ℕ) : kinkScalar k ≠ 0 := by
  unfold kinkScalar
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (zpow_ne_zero _ RatFunc.X_ne_zero)

end AJConjecture
