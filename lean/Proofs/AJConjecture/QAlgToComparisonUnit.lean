import Mathlib
import AJConjecture.RecurrenceIdeal

/-!
# Nonzero polynomials in `M` are units of the comparison ring

The image in `ℚ(M)[L, L⁻¹]` of a nonzero constant `p(M) ∈ ℤ[M]` is a unit.
-/

open Polynomial

namespace AJConjecture

/-- A nonzero polynomial in `M` is a unit of the comparison ring. -/
theorem isUnit_toComparison_coeff_of_ne_zero {p : ℤ[X]} (hp : p ≠ 0) :
    IsUnit (toComparison (C p)) := by
  have hne : algebraMap ℚ[X] (RatFunc ℚ) (p.map (Int.castRingHom ℚ)) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective ℚ),
      Polynomial.map_eq_zero_iff Int.cast_injective]
    exact hp
  have hC : toComparison (C p) =
      (Polynomial.toLaurent).comp Polynomial.C
        (algebraMap ℚ[X] (RatFunc ℚ) (p.map (Int.castRingHom ℚ))) := by
    simp [toComparison]
  rw [hC]
  exact (IsUnit.mk0 _ hne).map _

end AJConjecture
