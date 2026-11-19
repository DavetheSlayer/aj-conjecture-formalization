import Mathlib

/-!
# Rescaling the variable by `a` with `(1 - a)² = 0`

If `(1 - a)² = 0` then `a^k = 1 - k (1 - a)`, hence for a polynomial `p`
`p(aX) = p - (1 - a) X p'`: the `q`-dilation `J ↦ qJ` is the first-order differential operator
`1 - (1 - q) J ∂_J` when `(1 - q)² = 0`.
-/

open Polynomial

namespace AJConjecture

/-- If `(1 - a)² = 0` then `a^k = 1 - k (1 - a)`. -/
theorem pow_eq_of_one_sub_sq_eq_zero {A : Type*} [CommRing A] {a : A} (ha : (1 - a) ^ 2 = 0)
    (k : ℕ) : a ^ k = 1 - k * (1 - a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (k : A) * ha

/-- If `(1 - a)² = 0` then `p(aX) = p - (1 - a) X p'`. -/
theorem comp_C_mul_X_of_sq_eq_zero {A : Type*} [CommRing A] {a : A} (ha : (1 - a) ^ 2 = 0)
    (p : A[X]) : p.comp (C a * X) = p - C (1 - a) * (X * derivative p) := by
  ext k
  rw [comp_C_mul_X_coeff, coeff_sub, coeff_C_mul, pow_eq_of_one_sub_sq_eq_zero ha]
  rcases k with _ | k
  · simp
  · rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

end AJConjecture
