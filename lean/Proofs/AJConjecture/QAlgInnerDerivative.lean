import Mathlib

/-!
# The derivative with respect to the inner variable

`innerDerivative p` is `∂p/∂M` for `p ∈ A[M][L]` (inner variable `M`, outer variable `L`): the
derivative of every coefficient. For `A = ℤ` it is `coeffDerivative`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The partial derivative with respect to the inner variable of `A[M][L]`. -/
def innerDerivative {A : Type*} [CommSemiring A] (p : A[X][X]) : A[X][X] :=
  p.sum fun k c ↦ monomial k (derivative c)

end AJConjecture
