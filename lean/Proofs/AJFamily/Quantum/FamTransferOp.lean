import Mathlib
import AJConjecture.RecurrenceIdeal
import AJFamily.Quantum.FamTransferCoeff

/-!
# The family transfer operator

`famTransferOp m`, the recurrence operator of order `2m + 3` whose coefficients are the Cramer
coefficients at `q = t⁴`, `x = t^(4(2m+3)) M²`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The order-`(2m+3)` operator `∑_k A_(d-k)(t⁴, t^(4d) M²) L^k`. -/
def famTransferOp (m : ℕ) : RecOp :=
  ∑ k : Fin (2 * m + 4),
    C ((famCoeff m (X ^ 4 : ℤ[X]) (Fin.rev k)).comp (C (X ^ (4 * (2 * m + 3))) * X ^ 2)) *
      X ^ (k : ℕ)

end AJConjecture
