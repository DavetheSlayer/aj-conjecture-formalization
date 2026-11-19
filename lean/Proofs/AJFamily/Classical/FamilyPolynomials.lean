import Mathlib

/-!
# The family polynomials

The polynomials in `ℤ[M][L]` behind the bound for `Wh(T(2, 2k+1))`: with `x = M²`,
`P = (x - 1)(1 - L)`, `Q = x + L` and `k = x Q²`, the homogenised trace `τ` of the commutator
`c` and the scalar `A`, the homogenised Chebyshev sequence `homCheb`, the twist factor
`B_m = A Ŝ_m - k² Ŝ_{m-1}` and the bound `(L - 1) B_m`, used with `m = 2(2k+1)`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Integer bivariate polynomials sent to `ℂ[M][L]`. -/
abbrev mapC (P : ℤ[X][X]) : ℂ[X][X] := P.map (Polynomial.mapRingHom (Int.castRingHom ℂ))
/-- `x = M²` in `ℤ[M][L]` (inner variable `M`, outer variable `L`). -/
def famX : ℤ[X][X] := C (X ^ 2)
/-- `P = (M² - 1)(1 - L)`. -/
def famP : ℤ[X][X] := (famX - 1) * (1 - X)
/-- `Q = M² + L`. -/
def famQ : ℤ[X][X] := famX + X
/-- `k = M² Q²`, the homogenising factor. -/
def famK : ℤ[X][X] := famX * famQ ^ 2
/-- `τ = k · tr(c)`: the homogenised trace of the commutator `c = a a₁⁻¹ a⁻¹ a₁`. -/
def famTau : ℤ[X][X] :=
  famX ^ 2 * famP * famQ + famX * famP ^ 2 - 2 * famX * famP * famQ + 2 * famX * famQ ^ 2 +
    famP * famQ
/-- `A = k · α`, `α` the scalar with `a₁ c - c a = α (a₁ - a)`. -/
def famA : ℤ[X][X] :=
  famX ^ 2 * famP * famQ - famX ^ 2 * famQ ^ 2 + famX * famP ^ 2 - 3 * famX * famP * famQ +
    3 * famX * famQ ^ 2 + famP * famQ - famQ ^ 2

/-- The homogenised Chebyshev sequence `Ŝ₀ = 0, Ŝ₁ = 1, Ŝₙ₊₂ = τ Ŝₙ₊₁ - κ² Ŝₙ`; with `κ = 1`
it is the scalar sequence `Sₙ(t) = U_{n-1}(t/2)` of the powers of a matrix of trace `t`. -/
def homCheb {R : Type*} [CommRing R] (τ κ : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | (n + 2) => τ * homCheb τ κ (n + 1) - κ ^ 2 * homCheb τ κ n

/-- The twist factor of `a₁ c^m = c^m a`: `B_m = A Ŝ_m - k² Ŝ_{m-1}`. -/
def famB (m : ℕ) : ℤ[X][X] :=
  famA * homCheb famTau famK m - famK ^ 2 * homCheb famTau famK (m - 1)

/-- The classical bound `(L - 1) B_m`. -/
def famBound (m : ℕ) : ℤ[X][X] := (X - 1) * famB m

/-- The exponent `m = 2(2k+1)` for the companion `T(2, 2k+1)`. -/
def famDegree (k : ℕ) : ℕ := 2 * (2 * k + 1)

end AJConjecture
