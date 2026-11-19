import Mathlib

/-!
# The extra factor

`extraFactor` is `E = L² - (M⁴ - 4M² + 1) L + M⁴ ∈ ℤ[M][L]` (inner variable `M`, outer variable
`L`), the eigenvalue curve of the Whitehead link exterior with one cusp parabolic.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The extra factor `E = L² - (M⁴ - 4M² + 1) L + M⁴`. -/
def extraFactor : ℤ[X][X] :=
  X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X + C (X ^ 4)

end AJConjecture
