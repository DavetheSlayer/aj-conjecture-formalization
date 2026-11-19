import Mathlib

/-!
# The stationary substitution of the cofactor in compact form

Under the stationary substitution `J = (x L + 1)/(x + L)`, cleared by `(x + L)²`, the symbol
`ζ = x J² - (x² + 1) J + (x² + x + 1)` becomes
`Z = (x² + 1) L² - (x⁴ - 2x³ - 2x² - 2x + 1) L + x² (x² + 1)`. Since the substitution is
multiplicative on polynomials of bounded degree, the cofactor `J ǎ₆(ζ) - x ǎ₅(ζ)` becomes
`(x L + 1) A₆(Z, x W) - x (x + L)³ A₅(Z, x W)` with `W = (x + L)²` and the binary forms
`A₆(a, b) = a⁶ - a⁵b - 5a⁴b² + 4a³b³ + 6a²b⁴ - 3ab⁵ - b⁶`,
`A₅(a, b) = a⁵ - a⁴b - 4a³b² + 3a²b³ + 3ab⁴ - b⁵` (homogenised `ǎ₆`, `ǎ₅`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The stationary substitution of `ζ`, cleared by `(x + L)²`:
`(x² + 1) L² - (x⁴ - 2x³ - 2x² - 2x + 1) L + x² (x² + 1)` in `ℤ[x][L]`. -/
def symbolZetaMoebius : ℤ[X][X] :=
  C (X ^ 2 + 1) * X ^ 2 - C (X ^ 4 - 2 * X ^ 3 - 2 * X ^ 2 - 2 * X + 1) * X
    + C (X ^ 2 * (X ^ 2 + 1))

end AJConjecture
