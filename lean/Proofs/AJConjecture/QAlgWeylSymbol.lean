import Mathlib
import AJConjecture.APolynomial
import AJConjecture.RecurrenceIdeal

/-!
# The first jet at `t = -1` and the Weyl subprincipal symbol

With `t = -1 + ε`, `ε² = 0`, a recurrence operator is `P₀ + ε P₁` with `P₀ = specialize P` and
`P₁ = specializeJet P` in `ℤ[M][L]`, and the twist is `L M = (1 - 2ε) M L`. The first jet of an
Ore product is `(S ⋆ R)₁ = S₁ R₀ + S₀ R₁ - 2 (L ∂_L S₀)(M ∂_M R₀)`, so the symmetrised symbol
`P₁ + (L ∂_L)(M ∂_M) P₀` is the Weyl subprincipal symbol: on a product it differs from the
Leibniz rule by the antisymmetric bracket `(L ∂_L S₀)(M ∂_M R₀) - (M ∂_M S₀)(L ∂_L R₀)`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The value at a complex point `(m, l)` of a polynomial of `ℤ[M][L]`. -/
def evalIntPoint (p : ℤ[X][X]) (m l : ℂ) : ℂ :=
  evalPoint (p.map (Polynomial.mapRingHom (Int.castRingHom ℂ))) (m, l)

/-- The partial derivative `∂/∂M` on `ℤ[M][L]` (the derivative `∂/∂L` is
`Polynomial.derivative`). -/
def coeffDerivative (p : ℤ[X][X]) : ℤ[X][X] :=
  p.sum fun k c ↦ monomial k (derivative c)

/-- The first jet at `t = -1` of a recurrence operator: every coefficient `a(t) ∈ ℤ[t]` is
replaced by `a'(-1)`. -/
def specializeJet (P : RecOp) : ℤ[X][X] :=
  P.sum fun k c ↦ monomial k (c.sum fun e a ↦ monomial e ((derivative a).eval (-1)))

/-- The operator `(L ∂_L)(M ∂_M)` on `ℤ[M][L]`: the coefficient of `M^e L^k` is multiplied by
`k e`. -/
def eulerEuler (p : ℤ[X][X]) : ℤ[X][X] :=
  p.sum fun k c ↦ monomial k (c.sum fun e a ↦ monomial e (((k * e : ℕ) : ℤ) * a))

/-- The Weyl subprincipal symbol `P₁ + (L ∂_L)(M ∂_M) P₀` of a recurrence operator at
`t = -1`. -/
def weylSymbol (P : RecOp) : ℤ[X][X] :=
  specializeJet P + eulerEuler (specialize P)

end AJConjecture
