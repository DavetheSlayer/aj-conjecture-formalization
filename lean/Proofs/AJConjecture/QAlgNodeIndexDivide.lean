import Mathlib
import AJConjecture.QAlgInnerDerivativeBasic

/-!
# The bracket of the first-jet equation is homogeneous in the contents

For `A, B, r, s ∈ k[M]` and `S, R ∈ k[M][L]`, the bracket
`2 s (L ∂_L S)(r M ∂_M R - M r' R)` of the first-jet equation, formed for `B S`, `A R` and the
leading coefficients `B s`, `A r`, is `A² B²` times the bracket for `S`, `R`, `s`, `r`: the two
terms containing `A'` cancel. (`A = μ^a`, `B = μ^b` are the contents; no property of them is
used.)

Proof. `innerDerivative_mul`, `innerDerivative_C`, `Polynomial.derivative_C_mul`,
`Polynomial.derivative_mul`, then `C_mul`, `C_add`, `C_pow` and `ring`.
-/

open Polynomial

namespace AJConjecture

/-- The bracket `2 s (L ∂_L S)(r M ∂_M R - M r' R)` scales by `A² B²` under
`(S, R, s, r) ↦ (B S, A R, B s, A r)`. -/
theorem content_mul_jetBracket {k : Type*} [CommRing k] (A B r s : k[X]) (Ss Rs : k[X][X]) :
    C (2 * (B * s)) * (X * derivative (C B * Ss)) *
        (C (A * r) * (C X * innerDerivative (C A * Rs)) -
          C (X * derivative (A * r)) * (C A * Rs)) =
      C (A ^ 2 * B ^ 2) *
        (C (2 * s) * (X * derivative Ss) *
          (C r * (C X * innerDerivative Rs) - C (X * derivative r) * Rs)) := by
  rw [innerDerivative_mul, innerDerivative_C, derivative_C_mul, derivative_mul]
  simp only [C_mul, C_add, C_pow]
  ring

end AJConjecture
