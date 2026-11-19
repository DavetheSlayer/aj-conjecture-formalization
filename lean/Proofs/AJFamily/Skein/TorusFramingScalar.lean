import Mathlib
import AJConjecture.ClaspAlgScalars

/-!
# The framing scalar of the torus satellite

`halfTwistEigen_inv_pow_mul_torus`: on the channel `n` of colour `c`, the inverse half-twist
eigenvalue to the power `2(2k+1)` times `X^(4(2k+1) n(n+1))` is `X^(2(2k+1) c(c+2))`, independent
of `n`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

theorem halfTwistEigen_inv_pow_mul_torus (k c n : ℕ) :
    ((claspAlgHalfTwistEigen c n)⁻¹) ^ (2 * (2 * k + 1)) *
        (RatFunc.X : RatFunc ℚ) ^ (4 * (2 * (k : ℤ) + 1) * (n : ℤ) * ((n : ℤ) + 1)) =
      (RatFunc.X : RatFunc ℚ) ^ (2 * (2 * (k : ℤ) + 1) * (c : ℤ) * ((c : ℤ) + 2)) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h1 : ((-1 : RatFunc ℚ) ^ (c + n)) ^ (2 * (2 * k + 1)) = 1 := by
    rw [← pow_mul, show (c + n) * (2 * (2 * k + 1)) = 2 * ((c + n) * (2 * k + 1)) from by ring,
      pow_mul, neg_one_sq, one_pow]
  rw [claspAlgHalfTwistEigen, inv_pow, mul_pow, h1, one_mul, ← zpow_natCast, ← zpow_mul,
    ← zpow_neg, ← zpow_add₀ hX]
  congr 1
  push_cast
  ring

end AJConjecture
