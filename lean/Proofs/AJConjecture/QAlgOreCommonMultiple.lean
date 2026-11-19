import Mathlib
import AJConjecture.QAlgOrePseudoDivision

/-!
# Common left multiples in the Ore product

The left Ore condition: over a commutative domain with an injective endomorphism, two nonzero
skew polynomials have a nonzero common left multiple.
-/

open Polynomial

namespace AJConjecture

/-- The Ore product with `0` on the left is `0`. -/
private theorem oreMul_zero_left_commonMultiple {A : Type*} [Semiring A] (σ : A →+* A)
    (Q : A[X]) : oreMul σ 0 Q = 0 := by
  unfold oreMul
  exact Polynomial.sum_zero_index _

/-- The left Ore condition, in the form used for the induction on the degree of `Q`: divide
`P` by `Q` with remainder `R`, and combine with a common left multiple of `Q` and `R`. -/
private theorem exists_oreMul_eq_oreMul_of_ne_zero {A : Type*} [CommRing A] [IsDomain A]
    {σ : A →+* A} (hσ : Function.Injective σ) (Q : A[X]) :
    Q ≠ 0 → ∀ P : A[X], P ≠ 0 →
      ∃ S T : A[X], S ≠ 0 ∧ T ≠ 0 ∧ oreMul σ S P = oreMul σ T Q := by
  induction Q using Polynomial.degree_lt_wf.induction with
  | _ Q ih =>
    intro hQ P hP
    obtain ⟨β, hβ, S₁, R, hSR, hR⟩ := exists_C_mul_eq_oreMul_add hσ P hQ
    have hCβ : (C β : A[X]) ≠ 0 := Polynomial.C_ne_zero.mpr hβ
    by_cases hR0 : R = 0
    · refine ⟨C β, S₁, hCβ, ?_, ?_⟩
      · rintro rfl
        rw [hR0, add_zero, oreMul_zero_left_commonMultiple] at hSR
        exact mul_ne_zero hCβ hP hSR
      · rw [oreMul_C_left, hSR, hR0, add_zero]
    · obtain ⟨S₂, T₂, hS₂, hT₂, h₂⟩ := ih R hR hR0 Q hQ
      have key : oreMul σ (oreMul σ T₂ (C β)) P = oreMul σ (oreMul σ T₂ S₁ + S₂) Q := by
        rw [oreMul_assoc, oreMul_C_left, hSR, oreMul_add_right, ← oreMul_assoc, oreMul_add_left,
          h₂]
      have hS : oreMul σ T₂ (C β) ≠ 0 := oreMul_ne_zero hσ hT₂ hCβ
      refine ⟨_, _, hS, fun hT ↦ ?_, key⟩
      rw [hT, oreMul_zero_left_commonMultiple] at key
      exact oreMul_ne_zero hσ hS hP key

/-- The left Ore condition: nonzero `P`, `Q` have a common left multiple `S ⋆ P = T ⋆ Q` with
`S`, `T` nonzero. -/
theorem exists_oreMul_eq_oreMul {A : Type*} [CommRing A] [IsDomain A] {σ : A →+* A}
    (hσ : Function.Injective σ) {P Q : A[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ S T : A[X], S ≠ 0 ∧ T ≠ 0 ∧ oreMul σ S P = oreMul σ T Q :=
  exists_oreMul_eq_oreMul_of_ne_zero hσ Q hQ P hP

end AJConjecture
