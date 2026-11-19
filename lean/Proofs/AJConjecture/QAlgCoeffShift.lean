import Mathlib
import AJConjecture.RecurrenceIdeal

/-!
# The shift on the coefficient ring

`L * D(t, M) = D(t, t² M) * L` in the algebra of recurrence operators: the endomorphism
`M ↦ t² M` of `ℤ[t][M]` twists the product of `RecOp` through `AJConjecture.oreMul`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The endomorphism `D(t, M) ↦ D(t, t² M)` of the coefficient ring `ℤ[t][M]`. -/
def coeffShift : Coeff →+* Coeff :=
  Polynomial.compRingHom (C (X ^ 2) * X)

end AJConjecture
