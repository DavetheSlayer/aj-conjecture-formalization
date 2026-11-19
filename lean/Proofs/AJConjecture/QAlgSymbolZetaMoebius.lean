import Mathlib
import AJConjecture.QAlgSymbolCompact
import AJConjecture.QAlgSymbolPoly

/-!
# The stationary substitution of `ζ`

`ζ = x J² - (x² + 1) J + (x² + x + 1)` has degree `2` in `J`, and
`x (x L + 1)² - (x² + 1)(x L + 1)(x + L) + (x² + x + 1)(x + L)²
  = (x² + 1) L² - (x⁴ - 2x³ - 2x² - 2x + 1) L + x² (x² + 1)`.
-/

open Polynomial

namespace AJConjecture

/-- `ζ` has degree at most `2` in `J`. -/
theorem natDegree_symbolZeta_le : symbolZeta.natDegree ≤ 2 := by
  unfold symbolZeta
  compute_degree

/-- The stationary substitution of `ζ`. -/
theorem moebiusSubst_symbolZeta : moebiusSubst 2 symbolZeta = symbolZetaMoebius := by
  have h0 : symbolZeta.coeff 0 = X ^ 2 + X + 1 := by
    simp only [symbolZeta, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    norm_num
  have h1 : symbolZeta.coeff 1 = -(X ^ 2 + 1) := by
    simp only [symbolZeta, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    norm_num
  have h2 : symbolZeta.coeff 2 = X := by
    simp only [symbolZeta, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    norm_num
  simp only [moebiusSubst, Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2,
    symbolZetaMoebius, C_add, C_mul, C_pow, C_neg, C_sub, C_1, C_ofNat]
  ring

end AJConjecture
