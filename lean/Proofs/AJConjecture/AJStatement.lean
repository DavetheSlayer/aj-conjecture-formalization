import Mathlib
import AJConjecture.RecurrenceIdeal
import AJConjecture.APolynomial

/-!
# The localized square-free `SL₂` AJ conjecture

Contract `AJ-SF-SL2-S3-v1`: for every knot `K` in `S³`, with `α_K` the recurrence polynomial of
its unreduced coloured Jones function, `f_K = α_K(-1, M, L)` and `A_K` its A-polynomial
(including `L - 1`), the radical of `(f_K)` in `ℚ(M)[L, L⁻¹]` is `(A_K)`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The localized square-free `SL₂` AJ statement for one knot: for the recurrence polynomial
`α` of its coloured Jones function and its A-polynomial `A`, the radical of the ideal of
`α(-1, M, L)` in `ℚ(M)[L, L⁻¹]` is the ideal of `A`. -/
def AJSquareFree (K : BraidKnot) : Prop :=
  ∀ α : RecOp, IsRecurrencePolynomial (coloredJones K) α →
    ∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A →
      Ideal.radical (Ideal.span {toComparison (specialize α)}) = Ideal.span {toComparison A}

/-- The localized square-free `SL₂` AJ conjecture for all knots in `S³`. -/
def AJSquareFreeConjecture : Prop :=
  ∀ K : BraidKnot, AJSquareFree K

end AJConjecture
