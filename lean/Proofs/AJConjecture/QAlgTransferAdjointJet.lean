import Mathlib

/-!
# Division by `X` after multiplication by `X`

`divX (X * p) = p` for a polynomial `p` over a semiring.
-/

open Polynomial

namespace AJConjecture

/-- Division by `X` undoes multiplication by `X` on the left. -/
theorem divX_X_mul_jet {A : Type*} [Semiring A] (p : A[X]) : divX (X * p) = p := by
  ext k
  rw [coeff_divX, coeff_X_mul]

end AJConjecture
