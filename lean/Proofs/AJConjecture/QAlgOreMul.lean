import Mathlib

/-!
# The Ore product on polynomials

For a semiring `A` with an endomorphism `σ`, the skew polynomial ring `A[L; σ]` is realised on
the type `A[X]`: coefficients are written on the left and `L * a = σ a * L`. Only the product is
new; degrees, coefficients and leading coefficients are those of `Polynomial`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The Ore product on `A[X]` twisted by the endomorphism `σ`, coefficients on the left:
`(a X ^ i) ⋆ (b X ^ k) = (a * σ^[i] b) X ^ (i + k)`. -/
def oreMul {A : Type*} [Semiring A] (σ : A →+* A) (P Q : A[X]) : A[X] :=
  P.sum fun i a ↦ Q.sum fun k b ↦ monomial (i + k) (a * σ^[i] b)

end AJConjecture
