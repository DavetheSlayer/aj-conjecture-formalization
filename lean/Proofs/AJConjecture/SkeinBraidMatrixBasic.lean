import Mathlib
import AJConjecture.FieldActionBridge
import AJConjecture.SkeinMat

/-!
# First facts on the field-valued generators

Unfolding lemmas: the crossing matrices are `t • 1 + t⁻¹ • e_i` and `t⁻¹ • 1 + t • e_i`, the
generator `e_i` vanishes when it does not fit, and `ρ_m` is multiplicative on words.
-/

namespace AJConjecture

open LaurentPolynomial in

/-- A positive crossing is `t • 1 + t⁻¹ • e_i`. -/
theorem crossingF_pos (m i : ℕ) :
    crossingF m (i, true) =
      (RatFunc.X : RatFunc ℚ) • (1 : SkMat m m) + (RatFunc.X : RatFunc ℚ)⁻¹ • tlGenF m i := by
  ext a b
  simp only [crossingF, crossingMatrix, ↓reduceIte, tlGenF, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_add, map_mul,
    laurentToField_T, zpow_one, zpow_neg, apply_ite laurentToField, map_one,
    map_zero]

/-- A negative crossing is `t⁻¹ • 1 + t • e_i`. -/
theorem crossingF_neg (m i : ℕ) :
    crossingF m (i, false) =
      (RatFunc.X : RatFunc ℚ)⁻¹ • (1 : SkMat m m) + (RatFunc.X : RatFunc ℚ) • tlGenF m i := by
  ext a b
  simp only [crossingF, crossingMatrix, Bool.false_eq_true, ↓reduceIte, tlGenF, Matrix.map_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_add, map_mul,
    laurentToField_T, zpow_one, zpow_neg, apply_ite laurentToField, map_one,
    map_zero]

/-- The generator `e_i` is zero when the factors `i`, `i + 1` do not both exist. -/
theorem tlGenF_eq_zero (m i : ℕ) (h : m ≤ i + 1) : tlGenF m i = 0 := by
  ext a b
  simp only [tlGenF, Matrix.map_apply, tlGen, Matrix.of_apply, Matrix.zero_apply]
  rw [dite_eq_right (by omega), map_zero]

/-- `ρ_m` of the empty word is the identity. -/
theorem braidMatrix_nil (m : ℕ) : braidMatrix m [] = 1 := by
  rw [braidMatrix, List.map_nil, List.prod_nil]

/-- `ρ_m` is multiplicative on words. -/
theorem braidMatrix_append (m : ℕ) (u v : BraidWord) :
    braidMatrix m (u ++ v) = braidMatrix m u * braidMatrix m v := by
  rw [braidMatrix, List.map_append, List.prod_append]
  rfl

end AJConjecture
