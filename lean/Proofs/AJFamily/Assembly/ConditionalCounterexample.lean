import Mathlib
import AJConjecture.AJStatement
import AJConjecture.ComparisonDvdDescent
import AJConjecture.ExtraFactorPrime
import AJConjecture.FieldActionBridge
import AJConjecture.QAlgSpecializeNeZero
import AJConjecture.RadicalObstruction
import AJConjecture.RecurrencePolynomialExists

/-!
# A braid knot whose coloured Jones function is a given formula is a counterexample

The assembly step of the family proof, for a braid knot `K` and a formula `f : ℤ → ℚ(t)`.
Suppose the coloured Jones function of `K` is `f`, `f` has a nonzero localized annihilator, the
extra factor `E` divides the specialisation of every primitive localized annihilator of `f`, the
eigenvalue set of `K` lies in the zero set of a polynomial `P` that does not vanish at some zero
of `E`, and `K` has an A-polynomial. Then the conjecture fails for `K`, `E` divides the nonzero
specialisation of every primitive localized annihilator of the coloured Jones function, and `E` is
coprime in the comparison ring to every A-polynomial `A` of `K`: if `E ∣ A`, every zero of `E`
lies in the Zariski closure of the eigenvalue set, hence in the zero set of `P`.
-/

open Polynomial LaurentPolynomial

namespace AJConjecture

/-- The Laurent polynomial ring over a field is a principal ideal ring: it is the localisation
of the principal ideal domain `F[X]` at the powers of `X`. -/
private theorem isPrincipalIdealRing_laurentPolynomial_field (F : Type) [Field F] :
    IsPrincipalIdealRing F[T;T⁻¹] := by
  refine ⟨fun J ↦ ?_⟩
  rw [← IsLocalization.map_under (Submonoid.powers (X : F[X])) F[T;T⁻¹] J]
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal (J.under F[X])
  refine ⟨algebraMap F[X] F[T;T⁻¹] g, ?_⟩
  rw [hg, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]

/-- A localized annihilator of the coloured Jones function is one of any formula equal to it. -/
private theorem annihilates_field_of_inLocalizedAnnihilator {K : BraidKnot} {f : ℤ → RatFunc ℚ}
    (hfun : (fun m ↦ laurentToField (coloredJones K m)) = f) {Q : RecOp}
    (hQ : InLocalizedAnnihilator (coloredJones K) Q) :
    ∃ c : Coeff, c ≠ 0 ∧ ∀ n : ℤ, opApplyField (Polynomial.C c * Q) f n = 0 := by
  obtain ⟨c, hc, hann⟩ := hQ
  refine ⟨c, hc, fun n ↦ ?_⟩
  have h := congrArg laurentToField (hann n)
  rwa [map_zero, laurentToField_opApply, hfun] at h

/-- A braid knot whose coloured Jones function is a formula with the properties of the quantum
and classical sides is a counterexample, with `E` in every primitive annihilator and coprime to
every A-polynomial. -/
theorem conditional_counterexample (K : BraidKnot) (f : ℤ → RatFunc ℚ)
    (hseq : ∀ n : ℤ, laurentToField (coloredJones K n) = f n)
    (hann : ∃ Q : RecOp, Q ≠ 0 ∧ ∃ c : Coeff, c ≠ 0 ∧
      ∀ n : ℤ, opApplyField (Polynomial.C c * Q) f n = 0)
    (hE : ∀ Q : RecOp, Q.IsPrimitive →
      (∃ c : Coeff, c ≠ 0 ∧ ∀ n : ℤ, opApplyField (Polynomial.C c * Q) f n = 0) →
        toComparison extraFactor ∣ toComparison (specialize Q))
    (P : ℤ[X][X])
    (hbound : ∀ p ∈ eigenvalueSet K,
      evalPoint (P.map (Polynomial.mapRingHom (Int.castRingHom ℂ))) p = 0)
    (hpt : ∃ p : ℂ × ℂ,
      evalPoint (extraFactor.map (Polynomial.mapRingHom (Int.castRingHom ℂ))) p = 0 ∧
        evalPoint (P.map (Polynomial.mapRingHom (Int.castRingHom ℂ))) p ≠ 0)
    (hA : ∃ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A) :
    ¬ AJSquareFree K ∧
    (∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
      specialize Q ≠ 0 ∧ toComparison extraFactor ∣ toComparison (specialize Q)) ∧
    ∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A →
      IsCoprime (toComparison extraFactor) (toComparison A) := by
  have hfun : (fun m ↦ laurentToField (coloredJones K m)) = f := funext hseq
  have hex : ∃ Q : RecOp, Q ≠ 0 ∧ InLocalizedAnnihilator (coloredJones K) Q := by
    obtain ⟨Q, hQ, c, hc, hann⟩ := hann
    refine ⟨Q, hQ, c, hc, fun n ↦ laurentToField_injective ?_⟩
    rw [map_zero, laurentToField_opApply, hfun]
    exact hann n
  obtain ⟨α, hα⟩ := exists_isRecurrencePolynomial hex
  have hEα : toComparison extraFactor ∣ toComparison (specialize α) :=
    hE α hα.2.2.2 (annihilates_field_of_inLocalizedAnnihilator hfun hα.2.1)
  have hEA : ∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A →
      ¬ toComparison extraFactor ∣ toComparison A := by
    intro A hA hdvd
    have h1 : extraFactor ∣ A := extraFactor_dvd_of_toComparison_dvd hdvd
    have h2 : extraFactor.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) ∣
        A.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) := Polynomial.map_dvd _ h1
    have h3 := (hA.2 _ irreducible_extraFactor_map).mp h2
    obtain ⟨p, hp0, hpne⟩ := hpt
    exact hpne (h3 p hp0 _ hbound)
  refine ⟨fun hAJ ↦ ?_, fun Q _ hprim hQ ↦ ⟨specialize_ne_zero_of_isPrimitive hprim,
    hE Q hprim (annihilates_field_of_inLocalizedAnnihilator hfun hQ)⟩, fun A hA ↦ ?_⟩
  · obtain ⟨A, hA⟩ := hA
    exact radical_span_singleton_ne_of_prime_dvd prime_toComparison_extraFactor hEα
      (hEA A hA) (hAJ α hα A hA)
  · have := isPrincipalIdealRing_laurentPolynomial_field (RatFunc ℚ)
    exact (prime_toComparison_extraFactor.coprime_iff_not_dvd).mpr (hEA A hA)

end AJConjecture
