import Mathlib
import AJConjecture.WhiteheadFormula

/-!
# The order-seven recurrence of the cyclotomic coefficients: the operators

With `J = q^j` and `D_(-1) = 0`, the first-order operator
`(V y)_j = (1/(qJ) + J) y_j - ((1 - J)/J) y_(j-1)` realises multiplication by `Z = Q + 1/(qQ)`
on the kernel of the Bailey-type transform. The twisted Chebyshev operators are `S_0 = 2`,
`S_1 = V`, `S_(d+2) = V S_(d+1) - q⁻¹ S_d`, and the defect of the cyclotomic coefficients is
`e_j = [S_5(V) + (1 - qJ) S_6(V) - qJ S_7(V)] D_j`. The coefficient of `y_(j-1)` in `V`
vanishes at `j = 0`, so no boundary convention is needed.
-/

noncomputable section

namespace AJConjecture

/-- The first-order operator `V` on sequences in `j`:
`(V y)_j = (1/(q q^j) + q^j) y_j - ((1 - q^j)/q^j) y_(j-1)`. -/
def cycloStep (y : ℕ → RatFunc ℚ) (j : ℕ) : RatFunc ℚ :=
  ((qParam * qParam ^ j)⁻¹ + qParam ^ j) * y j - (1 - qParam ^ j) / qParam ^ j * y (j - 1)

/-- The twisted Chebyshev operators `S_d(V)`: `S_0 = 2`, `S_1 = V`,
`S_(d+2) = V S_(d+1) - q⁻¹ S_d`. -/
def cycloCheb : ℕ → (ℕ → RatFunc ℚ) → ℕ → RatFunc ℚ
  | 0, y => fun j ↦ 2 * y j
  | 1, y => cycloStep y
  | d + 2, y => fun j ↦ cycloStep (cycloCheb (d + 1) y) j - qParam⁻¹ * cycloCheb d y j

end AJConjecture
