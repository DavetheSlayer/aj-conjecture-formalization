import Mathlib
import AJConjecture.RecurrencePolynomialUnique
import AJConjecture.APolynomialUnique
import AJPaper.Finger.PpFAlgebra

/-!
# Uniqueness of the extra support (Unit PpF, node `PpF_Unique`)

Source: Section 9 of the paper: `Δ_K` is defined "up to association" in `R = ℚ(M)[L, L⁻¹]`.

* `isExtraSupport_unique`: `Δ` is unique up to association: two square-free elements of the
  unique factorization domain `R` with the same prime divisors are associated (restate the
  private `associated_of_squarefree_of_irreducible_dvd_iff` of
  `AJConjecture.APolynomialUnique`), two greatest common divisors are associated, and `g ≠ 0`
  cancels.
* `isExtraSupportOf_unique`: `Δ_K` is unique up to association: two recurrence polynomials are
  associated (`isRecurrencePolynomial_associated`), two A-polynomials are associated in `R`
  (`isAPolynomialOf_toComparison_associated`), and the predicate respects association
  (`isExtraSupport_congr`).

With `exists_isExtraSupportOf` this shows that `IsExtraSupportOf K` determines exactly one
association class of `R`, the `Δ_K` of eq. (45). The uniqueness is not used in the proof of
Corollary 9.2.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The Laurent polynomial ring over a field is a principal ideal ring: it is the localisation
of the principal ideal domain `F[X]` at the powers of `X`. -/
private theorem isPrincipalIdealRing_laurentPolynomial_ppfUnique (F : Type) [Field F] :
    IsPrincipalIdealRing (LaurentPolynomial F) := by
  refine ⟨fun J ↦ ?_⟩
  rw [← IsLocalization.map_under (Submonoid.powers (X : F[X])) (LaurentPolynomial F) J]
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal (J.under F[X])
  refine ⟨algebraMap F[X] (LaurentPolynomial F) g, ?_⟩
  rw [hg, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]

/-- In a unique factorization monoid, a squarefree element all of whose prime divisors divide
`b` divides `b`. -/
private theorem squarefree_dvd_of_forall_prime_dvd_ppfUnique {α : Type*} [CommMonoidWithZero α]
    [Nontrivial α] [UniqueFactorizationMonoid α] (b a : α) :
    Squarefree a → (∀ g : α, Prime g → g ∣ a → g ∣ b) → a ∣ b := by
  induction a using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun hsq _ ↦ absurd hsq not_squarefree_zero
  | h₂ x hx => exact fun _ _ ↦ hx.dvd
  | h₃ a p _ hp ih =>
    intro hsq hdiv
    have hpa : ¬ p ∣ a := fun hpa ↦ hp.not_isUnit (hsq p (mul_dvd_mul_left p hpa))
    obtain ⟨c, rfl⟩ := ih hsq.of_mul_right fun g hg hga ↦ hdiv g hg (hga.mul_left p)
    have hpc : p ∣ c := (hp.dvd_or_dvd (hdiv p hp (dvd_mul_right p a))).resolve_left hpa
    rw [mul_comm p a]
    exact mul_dvd_mul_left a hpc

/-- Two square-free parts of the same element of a unique factorization monoid are
associated. -/
private theorem isSquarefreePart_associated_ppfUnique {α : Type*} [CommMonoidWithZero α]
    [Nontrivial α] [UniqueFactorizationMonoid α] {f S S' : α} (h : IsSquarefreePart f S)
    (h' : IsSquarefreePart f S') : Associated S S' :=
  associated_of_dvd_dvd
    (squarefree_dvd_of_forall_prime_dvd_ppfUnique S' S h.1 fun g hg hgS ↦
      (h'.2 g hg).2 ((h.2 g hg).1 hgS))
    (squarefree_dvd_of_forall_prime_dvd_ppfUnique S S' h'.1 fun g hg hgS ↦
      (h.2 g hg).2 ((h'.2 g hg).1 hgS))

/-- The extra support is unique up to association in `ℚ(M)[L, L⁻¹]`. -/
theorem isExtraSupport_unique {f A Δ Δ' : ComparisonRing} (h : IsExtraSupport f A Δ)
    (h' : IsExtraSupport f A Δ') : Associated Δ Δ' := by
  have : IsPrincipalIdealRing ComparisonRing :=
    isPrincipalIdealRing_laurentPolynomial_ppfUnique (RatFunc ℚ)
  obtain ⟨S, g, hS, ⟨hgS, hgA, hgcd⟩, hSg⟩ := h
  obtain ⟨S', g', hS', ⟨hgS', hgA', hgcd'⟩, hSg'⟩ := h'
  have hSS : Associated S S' := isSquarefreePart_associated_ppfUnique hS hS'
  have hgg : Associated g g' :=
    associated_of_dvd_dvd (hgcd' g (hgS.trans hSS.dvd) hgA) (hgcd g' (hgS'.trans hSS.symm.dvd) hgA')
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hS.1.ne_zero (by rw [hSg, zero_mul])
  rw [hSg, hSg'] at hSS
  exact hSS.of_mul_left hgg hg0

/-- The extra support `Δ_K` of a knot is unique up to association. -/
theorem isExtraSupportOf_unique {K : BraidKnot} {Δ Δ' : ComparisonRing}
    (h : IsExtraSupportOf K Δ) (h' : IsExtraSupportOf K Δ') : Associated Δ Δ' := by
  obtain ⟨α, A, hα, hA, h⟩ := h
  obtain ⟨α', A', hα', hA', h'⟩ := h'
  have hf : Associated (toComparison (specialize α)) (toComparison (specialize α')) :=
    ((isRecurrencePolynomial_associated hα hα').map specialize).map toComparison
  exact isExtraSupport_unique
    (isExtraSupport_congr hf (isAPolynomialOf_toComparison_associated hA hA') (Associated.refl Δ) h)
    h'

end AJConjecture
