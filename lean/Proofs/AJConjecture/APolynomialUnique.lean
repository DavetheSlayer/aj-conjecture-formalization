import Mathlib
import AJConjecture.APolynomial
import AJConjecture.RecurrenceIdeal

/-!
# Uniqueness of the A-polynomial in the comparison ring

Two A-polynomials of the same set (in the sense of `IsAPolynomialOf`) are square-free over `ℂ`
with the same irreducible factors, hence differ by a nonzero rational constant; their images in
`ℚ(M)[L, L⁻¹]` are associated.
-/

open Polynomial

namespace AJConjecture

/-- In a unique factorization monoid, a squarefree element all of whose irreducible divisors
divide `b` divides `b`. -/
private theorem squarefree_dvd_of_forall_irreducible_dvd {α : Type*} [CommMonoidWithZero α]
    [Nontrivial α] [UniqueFactorizationMonoid α] (b a : α) :
    Squarefree a → (∀ g : α, Irreducible g → g ∣ a → g ∣ b) → a ∣ b := by
  induction a using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun hsq _ ↦ absurd hsq not_squarefree_zero
  | h₂ x hx => exact fun _ _ ↦ hx.dvd
  | h₃ a p _ hp ih =>
    intro hsq hdiv
    have hpa : ¬ p ∣ a := fun hpa ↦ hp.not_isUnit (hsq p (mul_dvd_mul_left p hpa))
    obtain ⟨c, rfl⟩ := ih hsq.of_mul_right fun g hg hga ↦ hdiv g hg (hga.mul_left p)
    have hpc : p ∣ c := (hp.dvd_or_dvd (hdiv p hp.irreducible (dvd_mul_right p a))).resolve_left hpa
    rw [mul_comm p a]
    exact mul_dvd_mul_left a hpc

/-- Two squarefree elements of a unique factorization monoid with the same irreducible divisors
are associated. -/
private theorem associated_of_squarefree_of_irreducible_dvd_iff {α : Type*}
    [CommMonoidWithZero α] [Nontrivial α] [UniqueFactorizationMonoid α] {a b : α}
    (ha : Squarefree a) (hb : Squarefree b) (h : ∀ g : α, Irreducible g → (g ∣ a ↔ g ∣ b)) :
    Associated a b :=
  associated_of_dvd_dvd
    (squarefree_dvd_of_forall_irreducible_dvd b a ha fun g hg ↦ (h g hg).1)
    (squarefree_dvd_of_forall_irreducible_dvd a b hb fun g hg ↦ (h g hg).2)

/-- The image in the comparison ring of a nonzero integer constant is a unit. -/
private theorem isUnit_toComparison_C_C_intCast {n : ℤ} (hn : n ≠ 0) :
    IsUnit (toComparison (C (C n))) := by
  have hC : toComparison (C (C n)) = LaurentPolynomial.C ((n : ℚ) : RatFunc ℚ) := by
    simp [toComparison]
  rw [hC]
  refine IsUnit.map LaurentPolynomial.C (IsUnit.mk0 _ ?_)
  exact_mod_cast hn

/-- Two integer two-variable polynomials whose complexifications are associated are proportional
by nonzero integer constants. -/
private theorem exists_intCast_mul_eq_of_associated_map {A A' : ℤ[X][X]}
    (hA : A.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) ≠ 0)
    (h : Associated (A.map (Polynomial.mapRingHom (Int.castRingHom ℂ)))
      (A'.map (Polynomial.mapRingHom (Int.castRingHom ℂ)))) :
    ∃ d m : ℤ, d ≠ 0 ∧ m ≠ 0 ∧ C (C d) * A' = C (C m) * A := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.1 u.isUnit
  obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.1 hr
  rw [← hru] at hu
  have hcoeff : ∀ i k : ℕ, (((A'.coeff i).coeff k : ℤ) : ℂ) = ((A.coeff i).coeff k : ℤ) * c := by
    intro i k
    have hik := congrArg (fun P : ℂ[X][X] ↦ (P.coeff i).coeff k) hu
    simpa using hik.symm
  obtain ⟨i, k, hd⟩ : ∃ i k : ℕ, (A.coeff i).coeff k ≠ 0 := by
    by_contra hne
    push Not at hne
    refine hA ?_
    have hA0 : A = 0 := by
      ext i k
      simpa using hne i k
    simp [hA0]
  refine ⟨(A.coeff i).coeff k, (A'.coeff i).coeff k, hd, ?_, ?_⟩
  · intro hm
    have hik := hcoeff i k
    rw [hm] at hik
    simp only [Int.cast_zero, zero_eq_mul, Int.cast_eq_zero] at hik
    exact hik.elim hd hc.ne_zero
  · ext j l
    have hjl := hcoeff j l
    have hik := hcoeff i k
    have hcast : ((((A.coeff i).coeff k * (A'.coeff j).coeff l : ℤ)) : ℂ) =
        (((A'.coeff i).coeff k * (A.coeff j).coeff l : ℤ) : ℂ) := by
      push_cast
      rw [hjl, hik]
      ring
    simpa using Int.cast_injective hcast

/-- Two A-polynomials of the same set have associated images in the comparison ring. -/
theorem isAPolynomialOf_toComparison_associated {S : Set (ℂ × ℂ)} {A A' : ℤ[X][X]}
    (h : IsAPolynomialOf S A) (h' : IsAPolynomialOf S A') :
    Associated (toComparison A) (toComparison A') := by
  have hassoc := associated_of_squarefree_of_irreducible_dvd_iff h.1 h'.1
    fun g hg ↦ (h.2 g hg).trans (h'.2 g hg).symm
  obtain ⟨d, m, hd, hm, hdm⟩ := exists_intCast_mul_eq_of_associated_map h.1.ne_zero hassoc
  have hmap := congrArg toComparison hdm
  rw [map_mul, map_mul] at hmap
  obtain ⟨ud, hud⟩ := isUnit_toComparison_C_C_intCast hd
  obtain ⟨um, hum⟩ := isUnit_toComparison_C_C_intCast hm
  rw [← hud, ← hum] at hmap
  refine ⟨um * ud⁻¹, ?_⟩
  rw [Units.val_mul, ← mul_assoc, mul_comm (toComparison A), ← hmap, mul_comm _ (toComparison A'),
    mul_assoc, Units.mul_inv, mul_one]

end AJConjecture
