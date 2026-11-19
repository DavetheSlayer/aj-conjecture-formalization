import Mathlib
import AJConjecture.ComparisonDvdDescent
import AJConjecture.QAlgTwistFactorPrime
import AJConjecture.ExtraFactorIrreducible
import AJConjecture.RecurrenceIdeal

/-!
# The extra factor is prime in the comparison ring

The image of `E = L² - (M⁴ - 4M² + 1) L + M⁴` in `ℚ(M)[L, L⁻¹]` is a prime element.
-/

open Polynomial

namespace AJConjecture

/-- The extra factor is irreducible as a polynomial in `L` over `ℚ[M]`. -/
private theorem irreducible_extraFactor_map_rat :
    Irreducible (extraFactor.map (Polynomial.mapRingHom (Int.castRingHom ℚ))) := by
  refine (extraFactor_monic.map _).irreducible_of_irreducible_map
    (Polynomial.mapRingHom (algebraMap ℚ ℂ)) _ ?_
  rw [Polynomial.map_map]
  convert irreducible_extraFactor_map using 2
  ext <;> simp

/-- The extra factor is irreducible as a polynomial in `L` over `ℚ(M)`. -/
private theorem irreducible_extraFactor_map_ratFunc :
    Irreducible (extraFactor.map
      ((algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)))) := by
  rw [← Polynomial.map_map]
  exact ((extraFactor_monic.map _).irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc ℚ)).mp irreducible_extraFactor_map_rat

/-- The extra factor `E` is prime in the comparison ring `ℚ(M)[L, L⁻¹]`. -/
theorem prime_toComparison_extraFactor : Prime (toComparison extraFactor) := by
  refine prime_toLaurent_of_prime irreducible_extraFactor_map_ratFunc.prime ?_
  rw [coe_mapRingHom, coeff_map, extraFactor_coeff_zero]
  exact (map_ne_zero_iff _ intPolyToRatFunc_injective).mpr (pow_ne_zero 4 X_ne_zero)

end AJConjecture
