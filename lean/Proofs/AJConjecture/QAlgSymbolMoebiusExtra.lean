import Mathlib
import AJConjecture.QAlgSymbolPoly
import AJConjecture.WitnessPolynomials

/-!
# The stationary substitution of `ζ + 2x` is the extra factor

`(ζ + 2x)(x + L)² = (x + 1)² (L² - (x² - 4x + 1) L + x²)` at `J = (x L + 1)/(x + L)`; with
`x = M²` the last factor is `E`.
-/

open Polynomial

namespace AJConjecture

/-- The constant coefficient in `J` of `ζ + 2x`. -/
private theorem coeff_symbolZeta_add_zero :
    (symbolZeta + C (2 * X)).coeff 0 = X ^ 2 + 3 * X + 1 := by
  simp only [symbolZeta, coeff_add, coeff_sub, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num
  ring

/-- The coefficient of `J` of `ζ + 2x`. -/
private theorem coeff_symbolZeta_add_one :
    (symbolZeta + C (2 * X)).coeff 1 = -(X ^ 2 + 1) := by
  simp only [symbolZeta, coeff_add, coeff_sub, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

/-- The coefficient of `J²` of `ζ + 2x`. -/
private theorem coeff_symbolZeta_add_two :
    (symbolZeta + C (2 * X)).coeff 2 = X := by
  simp only [symbolZeta, coeff_add, coeff_sub, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

/-- The stationary substitution sends `ζ + 2x` to `(M² + 1)² E`, after `x = M²`. -/
theorem map_moebiusSubst_symbolZeta_add :
    (moebiusSubst 2 (symbolZeta + C (2 * X))).map (Polynomial.compRingHom (X ^ 2)) =
      C ((X ^ 2 + 1) ^ 2) * extraFactor := by
  rw [moebiusSubst]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_symbolZeta_add_zero,
    coeff_symbolZeta_add_one, coeff_symbolZeta_add_two, extraFactor, zero_add]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X,
    coe_compRingHom_apply, Polynomial.map_one, add_comp, mul_comp, pow_comp, X_comp, neg_comp,
    one_comp, ofNat_comp, Nat.cast_ofNat]
  simp only [C_add, C_mul, C_pow, C_neg, C_1, C_ofNat, C_sub]
  ring

end AJConjecture
