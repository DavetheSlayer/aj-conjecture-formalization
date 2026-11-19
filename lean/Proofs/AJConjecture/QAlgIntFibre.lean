import Mathlib

/-!
# The fibre of a polynomial of `ℤ[M][L]` over a complex value of `M`

`intFibre p m` is the polynomial `p(m, L) ∈ ℂ[L]`. Evaluation at a complex point is evaluation
of the fibre, and the fibre commutes with products and with the derivative in `L`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The fibre `p(m, L) ∈ ℂ[L]` of `p ∈ ℤ[M][L]` over the complex value `m` of `M`. -/
def intFibre (p : ℤ[X][X]) (m : ℂ) : ℂ[X] :=
  p.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ) m)

end AJConjecture
