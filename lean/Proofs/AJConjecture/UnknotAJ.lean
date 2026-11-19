import Mathlib
import AJConjecture.QAlgTwistFactorPrime
import AJConjecture.AJStatement
import AJConjecture.APolynomialUnique
import AJConjecture.RecurrencePolynomialUnique
import AJConjecture.UnknotAPolynomial
import AJConjecture.UnknotRecurrence

/-!
# The AJ statement holds for the unknot

A sanity check of the formalisation: for the unknot the hypotheses of the localized square-free
AJ statement are satisfiable (`isRecurrencePolynomial_unknot`, `isAPolynomialOf_unknot`) and the
statement is true: the radical of `((M² - 1) (L - 1))` in `ℚ(M)[L, L⁻¹]` is `(L - 1)`.
-/

open Polynomial

namespace AJConjecture

/-- The image of `L - 1` is prime in the comparison ring `ℚ(M)[L, L⁻¹]`. -/
private theorem prime_toComparison_X_sub_one_unknot :
    Prime (toComparison (X - 1 : ℤ[X][X])) := by
  have hmap : toComparison (X - 1 : ℤ[X][X]) =
      toLaurent (X - C (1 : RatFunc ℚ)) := by
    simp [toComparison]
  rw [hmap]
  refine prime_toLaurent_of_prime (prime_X_sub_C 1) ?_
  simp

/-- The image of the coefficient `M² - 1` is a unit of the comparison ring `ℚ(M)[L, L⁻¹]`. -/
private theorem isUnit_toComparison_C_X_sq_sub_one_unknot :
    IsUnit (toComparison (C (X ^ 2 - 1 : ℤ[X]))) := by
  have hinj : Function.Injective
      ((algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))) :=
    (IsFractionRing.injective ℚ[X] (RatFunc ℚ)).comp
      (Polynomial.map_injective _ Int.cast_injective)
  have hne : (X ^ 2 - 1 : ℤ[X]) ≠ 0 := (monic_X_pow_sub_C (1 : ℤ) two_ne_zero).ne_zero
  have hmap : toComparison (C (X ^ 2 - 1 : ℤ[X])) = LaurentPolynomial.C
      ((algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))
        (X ^ 2 - 1)) := by
    simp [toComparison]
  rw [hmap]
  exact (IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).mpr hne)).map LaurentPolynomial.C

/-- The localized square-free AJ statement holds for the unknot. -/
theorem ajSquareFree_unknot : AJSquareFree unknot := by
  intro α hα A hA
  have hα' : Associated (toComparison (specialize α)) (toComparison (X - 1 : ℤ[X][X])) := by
    have h := ((isRecurrencePolynomial_associated hα isRecurrencePolynomial_unknot).map
      specialize).map toComparison
    rw [specialize_unknotRecurrence, map_mul] at h
    exact h.trans (associated_unit_mul_left _ _ isUnit_toComparison_C_X_sq_sub_one_unknot)
  have hA' : Associated (toComparison A) (toComparison (X - 1 : ℤ[X][X])) :=
    isAPolynomialOf_toComparison_associated hA isAPolynomialOf_unknot
  rw [Ideal.span_singleton_eq_span_singleton.mpr hα',
    Ideal.span_singleton_eq_span_singleton.mpr hA']
  exact ((Ideal.span_singleton_prime prime_toComparison_X_sub_one_unknot.ne_zero).mpr
    prime_toComparison_X_sub_one_unknot).radical

end AJConjecture
