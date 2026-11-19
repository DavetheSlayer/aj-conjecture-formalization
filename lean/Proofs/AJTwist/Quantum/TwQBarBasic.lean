import Mathlib
import AJTwist.Quantum.TwQBar

/-!
# The bar involution on `q`, on quantum integers and on Laurent polynomials

* `twQBar_qParam_zpow`: `\bar{q^k} = q^(-k)`.
* `twQBar_quantumInt`: the quantum integers are bar-invariant ("Quantum dimensions are invariant
  under that inversion", revision 5, Section 3).
* `twQBar_laurentToField`: on Laurent polynomials the bar involution is
  `LaurentPolynomial.invert`, the form in which the mirror image of a knot acts on its coloured
  Jones function (Section 8.2: `Φ_{S^*}(N; t) = Φ_S(N; t⁻¹)`).
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

theorem twQBar_qParam_zpow (k : ℤ) : twQBar (qParam ^ k) = qParam ^ (-k) := by
  have hq : ∀ j : ℤ, qParam ^ j = (RatFunc.X : RatFunc ℚ) ^ (4 * j) := fun j ↦ by
    rw [qParam, ← zpow_natCast, ← zpow_mul]
    rfl
  rw [hq, hq, twQBar_X_zpow, mul_neg]

/-- The quantum integers are invariant under `t ↦ t⁻¹`. -/
theorem twQBar_quantumInt (m : ℤ) : twQBar (quantumInt m) = quantumInt m := by
  rw [quantumInt, map_div₀, map_sub, map_sub, twQBar_X_zpow, twQBar_X_zpow, twQBar_X_zpow,
    twQBar_X_zpow, neg_neg, neg_neg, ← neg_sub, ← neg_sub (RatFunc.X ^ (2 : ℤ)), neg_div_neg_eq]

/-- On Laurent polynomials the bar involution is `T ↦ T⁻¹`. -/
theorem twQBar_laurentToField (p : ℤ[T;T⁻¹]) :
    twQBar (laurentToField p) = laurentToField (LaurentPolynomial.invert p) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | C_mul_T n a =>
    have hC : ∀ b : ℤ, laurentToField (LaurentPolynomial.C b) = (b : RatFunc ℚ) := fun b ↦ by
      rw [laurentToField, LaurentPolynomial.eval₂_C]
      rfl
    rw [map_mul, map_mul, map_mul, map_mul, LaurentPolynomial.invert_C,
      LaurentPolynomial.invert_T, laurentToField_T, laurentToField_T, hC, map_intCast,
      twQBar_X_zpow]

end AJConjecture
