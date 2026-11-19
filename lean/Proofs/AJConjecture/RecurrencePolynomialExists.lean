import Mathlib
import AJConjecture.RecurrenceIdeal

/-!
# Existence of the recurrence polynomial

A sequence whose localised annihilator contains a nonzero operator has a recurrence polynomial:
an operator of minimal `L`-degree in the localised annihilator, divided by its content.
-/

open Polynomial LaurentPolynomial

namespace AJConjecture

/-- If the localised annihilator of `f` contains a nonzero operator, then `f` has a recurrence
polynomial. -/
theorem exists_isRecurrencePolynomial {f : ℤ → ℤ[T;T⁻¹]}
    (h : ∃ Q : RecOp, Q ≠ 0 ∧ InLocalizedAnnihilator f Q) :
    ∃ α : RecOp, IsRecurrencePolynomial f α := by
  classical
  have h' : ∃ n : ℕ, ∃ Q : RecOp, Q ≠ 0 ∧ InLocalizedAnnihilator f Q ∧ Q.natDegree = n := by
    obtain ⟨Q, hQ0, hQ⟩ := h
    exact ⟨_, Q, hQ0, hQ, rfl⟩
  obtain ⟨Q₀, hQ₀, hQ₀f, hdeg⟩ := Nat.find_spec h'
  have hmin : ∀ Q : RecOp, Q ≠ 0 → InLocalizedAnnihilator f Q →
      Q₀.natDegree ≤ Q.natDegree := by
    intro Q hQ0 hQ
    rw [hdeg]
    exact Nat.find_min' h' ⟨Q, hQ0, hQ, rfl⟩
  refine ⟨Q₀.primPart, Q₀.primPart_ne_zero, ?_, ?_, Q₀.isPrimitive_primPart⟩
  · obtain ⟨c, hc, hann⟩ := hQ₀f
    refine ⟨c * Q₀.content, mul_ne_zero hc (mt Polynomial.content_eq_zero_iff.mp hQ₀), ?_⟩
    rwa [Polynomial.C_mul, mul_assoc, ← Polynomial.eq_C_content_mul_primPart]
  · intro Q hQ0 hQ
    rw [Polynomial.natDegree_primPart]
    exact hmin Q hQ0 hQ

end AJConjecture
