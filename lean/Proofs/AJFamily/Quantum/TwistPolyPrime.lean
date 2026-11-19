import Mathlib
import AJConjecture.ComparisonDvdDescent
import AJConjecture.QAlgTwistFactorPrime
import AJConjecture.RecurrenceIdeal
import AJFamily.Quantum.TwistPolyIrreducible

/-!
# Primality of the twist polynomial

For `m ≥ 2`, `B_m` is prime in `ℚ(M)[L, L⁻¹]`: irreducibility descends from `ℂ(M)` to `ℚ(M)`, and
the constant coefficient `M^(4m)` is nonzero.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The field embedding `ℚ(M) → ℂ(M)` induced by `ℚ → ℂ`. -/
private def ratFuncRatToComplex : RatFunc ℚ →+* RatFunc ℂ :=
  RatFunc.liftRingHom ((algebraMap ℂ[X] (RatFunc ℂ)).comp
    (Polynomial.mapRingHom (Rat.castHom ℂ))) <| by
    have hinj : Function.Injective ((algebraMap ℂ[X] (RatFunc ℂ)).comp
        (Polynomial.mapRingHom (Rat.castHom ℂ))) :=
      (IsFractionRing.injective ℂ[X] (RatFunc ℂ)).comp
        (Polynomial.map_injective _ (Rat.castHom ℂ).injective)
    intro x hx
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    exact (map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hx)

/-- The embedding `ℚ(M) → ℂ(M)` is compatible with the coefficient maps from `ℤ[M]`. -/
private theorem ratFuncRatToComplex_comp :
    ratFuncRatToComplex.comp
      ((algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))) =
      (algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ)) := by
  refine RingHom.ext fun p ↦ ?_
  simp only [ratFuncRatToComplex, RingHom.coe_comp, Function.comp_apply, coe_mapRingHom,
    RatFunc.liftRingHom_algebraMap, Polynomial.map_map]
  congr 1

/-- `B_m` is irreducible as a polynomial in `L` over `ℚ(M)`. -/
private theorem irreducible_twistPoly_ratFunc_rat (m : ℕ) (hm : 2 ≤ m) :
    Irreducible ((twistPoly m).map
      ((algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)))) := by
  have hirr := irreducible_twistPoly_ratFunc m hm
  rw [← ratFuncRatToComplex_comp, ← Polynomial.map_map] at hirr
  refine Polynomial.IsPrimitive.irreducible_of_irreducible_map_of_injective
    ratFuncRatToComplex.injective ?_ hirr
  rw [Polynomial.isPrimitive_iff_ne_zero]
  exact hirr.ne_zero ∘ fun h ↦ by rw [h, Polynomial.map_zero]

/-- The twist polynomial `B_m` is prime in the comparison ring `ℚ(M)[L, L⁻¹]`. -/
theorem prime_toComparison_twistPoly (m : ℕ) (hm : 2 ≤ m) : Prime (toComparison (twistPoly m)) := by
  refine prime_toLaurent_of_prime (irreducible_twistPoly_ratFunc_rat m hm).prime ?_
  rw [coe_mapRingHom, coeff_map, coeff_zero_twistPoly]
  exact (map_ne_zero_iff _ intPolyToRatFunc_injective).mpr
    (pow_ne_zero _ X_ne_zero)

end AJConjecture
