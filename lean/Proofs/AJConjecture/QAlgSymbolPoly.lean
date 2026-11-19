import Mathlib

/-!
# Polynomials for the symbol at `q = 1`

At `q = 1` the adjoint operator of the transfer is multiplication by
`ζ = x J² - (x² + 1) J + (x² + x + 1) ∈ ℤ[x][J]`, and the target polynomial factors as
`-(ζ + 2x) (J ǎ₆(ζ) - x ǎ₅(ζ))` with the homogenised Chebyshev-type polynomials
`ǎ₆(ζ) = ζ⁶ - xζ⁵ - 5x²ζ⁴ + 4x³ζ³ + 6x⁴ζ² - 3x⁵ζ - x⁶` and
`ǎ₅(ζ) = ζ⁵ - xζ⁴ - 4x²ζ³ + 3x³ζ² + 3x⁴ζ - x⁵`. The stationary substitution
`J = (x L + 1)/(x + L)`, cleared by `(x + L)^d` on polynomials of degree at most `d` in `J`, sends
the two factors to `(x + 1)² E` and to `(x - 1)(L - 1) B`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The symbol `ζ = x J² - (x² + 1) J + (x² + x + 1)` of the adjoint operator at `q = 1`. -/
def symbolZeta : ℤ[X][X] :=
  C X * X ^ 2 - C (X ^ 2 + 1) * X + C (X ^ 2 + X + 1)

/-- The stationary substitution `J = (x L + 1)/(x + L)` on polynomials of degree at most `d` in
`J`, cleared by `(x + L)^d`: `∑_{k ≤ d} p_k(x) (x L + 1)^k (x + L)^(d - k)`. -/
def moebiusSubst (d : ℕ) (p : ℤ[X][X]) : ℤ[X][X] :=
  ∑ k ∈ Finset.range (d + 1), C (p.coeff k) * (C X * X + 1) ^ k * (C X + X) ^ (d - k)

end AJConjecture
