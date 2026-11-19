import Mathlib
import AJConjecture.QAlgSpecializeNeZero
import AJPaper.Finger.PpFAlgebra

/-!
# Existence of the extra support (Unit PpF, node `PpF_Exists`)

Source: Section 9 of the paper (`fingerprints.tex`): `Δ_K` is defined for `f_K ≠ 0`, in
`R = ℚ(M)[L, L⁻¹]`, a principal ideal domain; Definition 9.1 is made "on the domain where the
primitive minimum exists and `f ≠ 0`".

* `exists_isExtraSupport`: for `f ≠ 0` in `R` and any `A` there is `Δ` with
  `IsExtraSupport f A Δ`. Route: `R` is a principal ideal domain (the localization of
  `ℚ(M)[L]` at the powers of `L`; the library proves this privately, e.g. in
  `AJTwist.Classical.TwCCoprime`: restate it), hence a unique factorization domain; with a
  normalization (`UniqueFactorizationMonoid.normalizationMonoid`), `S` is the product of the
  distinct normalized prime factors of `f`, `g` the product of those dividing `A`, and `Δ` the
  product of the others. Distinct normalized primes are coprime in a principal ideal domain, so
  a product of some of them divides whatever all of them divide
  (`Finset.prod_dvd_of_coprime`).
* `exists_isExtraSupportOf`: `Δ_K` exists as soon as a recurrence polynomial and an
  A-polynomial exist (`specialize_ne_zero_of_isPrimitive`; `toComparison` is injective).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The Laurent polynomial ring over a field is a principal ideal ring: it is the localisation
of the principal ideal domain `F[X]` at the powers of `X`. -/
private theorem isPrincipalIdealRing_laurentPolynomial_ppfExists (F : Type) [Field F] :
    IsPrincipalIdealRing (LaurentPolynomial F) := by
  refine ⟨fun J ↦ ?_⟩
  rw [← IsLocalization.map_under (Submonoid.powers (X : F[X])) (LaurentPolynomial F) J]
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal (J.under F[X])
  refine ⟨algebraMap F[X] (LaurentPolynomial F) g, ?_⟩
  rw [hg, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]

/-- `toComparison` is injective. -/
private theorem toComparison_injective_ppfExists : Function.Injective toComparison :=
  Polynomial.toLaurent_injective.comp
    (Polynomial.map_injective _ ((RatFunc.algebraMap_injective ℚ).comp
      (Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)))

/-- For `f ≠ 0` the extra support exists in `ℚ(M)[L, L⁻¹]`. -/
theorem exists_isExtraSupport {f : ComparisonRing} (hf : f ≠ 0) (A : ComparisonRing) :
    ∃ Δ : ComparisonRing, IsExtraSupport f A Δ := by
  have : IsPrincipalIdealRing ComparisonRing :=
    isPrincipalIdealRing_laurentPolynomial_ppfExists (RatFunc ℚ)
  let : StrongNormalizationMonoid ComparisonRing :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let : GCDMonoid ComparisonRing := UniqueFactorizationMonoid.toGCDMonoid ComparisonRing
  obtain ⟨Δ, hΔ⟩ := gcd_dvd_left (UniqueFactorizationMonoid.radical f) A
  exact ⟨Δ, UniqueFactorizationMonoid.radical f, gcd (UniqueFactorizationMonoid.radical f) A,
    ⟨UniqueFactorizationMonoid.squarefree_radical, fun g hg ↦
      UniqueFactorizationMonoid.dvd_radical_iff_of_irreducible hg.irreducible hf⟩,
    ⟨gcd_dvd_left _ _, gcd_dvd_right _ _, fun d hdS hdA ↦ dvd_gcd hdS hdA⟩, hΔ⟩

/-- The extra support `Δ_K` exists when a recurrence polynomial and an A-polynomial exist. -/
theorem exists_isExtraSupportOf {K : BraidKnot}
    (hα : ∃ α : RecOp, IsRecurrencePolynomial (coloredJones K) α)
    (hA : ∃ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A) :
    ∃ Δ : ComparisonRing, IsExtraSupportOf K Δ := by
  obtain ⟨α, hα⟩ := hα
  obtain ⟨A, hA⟩ := hA
  have hne : toComparison (specialize α) ≠ 0 := fun h0 ↦
    specialize_ne_zero_of_isPrimitive hα.2.2.2
      (toComparison_injective_ppfExists (h0.trans (map_zero toComparison).symm))
  obtain ⟨Δ, hΔ⟩ := exists_isExtraSupport hne (toComparison A)
  exact ⟨Δ, α, A, hα, hA, hΔ⟩

end AJConjecture
