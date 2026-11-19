import Mathlib
import AJConjecture.QAlgSymbolPoly
import AJFamily.Quantum.FamTransferPoly

/-!
# The family adjoint at `q = 1`

`famAdjoint_one_eq_mul`: at `q = 1` the family adjoint is multiplication by `ζ = symbolZeta`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- Division by `X` undoes multiplication by `X` on the left. -/
private theorem divX_X_mul_famAtOne {A : Type*} [Semiring A] (p : A[X]) :
    divX (X * p) = p := by
  ext k
  rw [coeff_divX, coeff_X_mul]

/-- At `q = 1` the family adjoint operator is multiplication by `ζ`. -/
theorem famAdjoint_one_eq_mul (m : ℕ) (n : ℤ[X][X]) : famAdjoint m (1 : ℤ) n = symbolZeta * n := by
  have hinner : C (C ((1 : ℤ) ^ (2 * m + 2)) * X) * n -
      (1 - C (C (1 : ℤ)) * X) * (C X - C (C (1 : ℤ)) * X) *
        (C (C ((1 : ℤ) ^ (2 * m + 2))) - C X * X) * n.comp (C (C (1 : ℤ)) * X) =
      X * ((C (X ^ 2 + X + 1) - C (X ^ 2 + X + 1) * X + C X * X ^ 2) * n) := by
    simp only [one_pow, C_1, one_mul, comp_X, C_add, C_pow]
    ring
  rw [famAdjoint, hinner, divX_X_mul_famAtOne, symbolZeta]
  simp only [one_pow, C_1, one_mul, C_add, C_pow]
  ring

end AJConjecture
