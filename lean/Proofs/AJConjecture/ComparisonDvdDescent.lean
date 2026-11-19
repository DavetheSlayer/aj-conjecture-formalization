import Mathlib
import AJConjecture.QAlgTwistFactorPrime
import AJConjecture.RecurrenceIdeal
import AJConjecture.WitnessPolynomials

/-!
# Divisibility by the extra factor descends from the comparison ring

If `E` divides `A` in `ℚ(M)[L, L⁻¹]`, then it already divides `A` in `ℤ[M][L]`: `E` is monic in
`L` and its constant coefficient `M⁴` is nonzero.
-/

open Polynomial

namespace AJConjecture

/-- The coefficient map `ℤ[M] → ℚ(M)` is injective. -/
theorem intPolyToRatFunc_injective : Function.Injective
    ((algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))) :=
  (IsFractionRing.injective ℚ[X] (RatFunc ℚ)).comp
    (Polynomial.map_injective _ Int.cast_injective)

/-- The extra factor is monic in `L`. -/
theorem extraFactor_monic : extraFactor.Monic := by
  have hlin : (C (X ^ 4 - 4 * X ^ 2 + 1 : ℤ[X]) * X).degree < ((2 : ℕ) : WithBot ℕ) :=
    (degree_C_mul_X_le _).trans_lt (by norm_num)
  refine (monic_X_pow_sub hlin).add_of_left ?_
  rw [degree_sub_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
  exact degree_C_le.trans_lt (by norm_num)

/-- The constant coefficient of the extra factor is `M ^ 4`. -/
theorem extraFactor_coeff_zero : extraFactor.coeff 0 = X ^ 4 := by
  simp only [extraFactor, coeff_add, coeff_sub, coeff_C_zero, coeff_X_pow, mul_coeff_zero,
    coeff_X_zero]
  simp

/-- Divisibility by the extra factor in the comparison ring implies divisibility in
`ℤ[M][L]`. -/
theorem extraFactor_dvd_of_toComparison_dvd {A : ℤ[X][X]}
    (h : toComparison extraFactor ∣ toComparison A) : extraFactor ∣ A := by
  rw [← Polynomial.map_dvd_map _ intPolyToRatFunc_injective extraFactor_monic]
  refine dvd_of_toLaurent_dvd ?_ h
  rw [coeff_map, extraFactor_coeff_zero]
  exact (map_ne_zero_iff _ intPolyToRatFunc_injective).mpr (pow_ne_zero 4 X_ne_zero)

end AJConjecture
