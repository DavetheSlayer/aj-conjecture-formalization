import Mathlib
import AJConjecture.QAlgSymbolNodeDerivatives
import AJConjecture.QAlgWeylSymbol

/-!
# The value at a point of `(L ∂_L)(M ∂_M) p`

`(L ∂_L)(M ∂_M) p = L M ∂_L ∂_M p`, so
`evalIntPoint (eulerEuler p) m l = l m · evalIntPoint (derivative (coeffDerivative p)) m l`.

Proof. Coefficientwise `eulerEuler p = X * derivative (C X * coeffDerivative p)` (the
coefficient of `M^e L^k` is multiplied by `k e` on both sides; `Polynomial.sum_def`,
`Polynomial.coeff_monomial`, `Polynomial.coeff_derivative`, `Polynomial.coeff_X_mul`), then
`Polynomial.derivative_C_mul` and the multiplicativity of the evaluation
(`evalIntPoint p m l = (p.map (mapRingHom (Int.castRingHom ℂ))).eval₂ (evalRingHom m) l`).
-/

open Polynomial

namespace AJConjecture

/-- Evaluation at a complex point `(m, l)`, as a ring homomorphism. -/
private noncomputable def evalIntHomIndexEuler (m l : ℂ) : ℤ[X][X] →+* ℂ :=
  (Polynomial.eval₂RingHom (Polynomial.evalRingHom m) l).comp
    (Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom ℂ)))

/-- `evalIntPoint` is the evaluation homomorphism. -/
private theorem evalIntPoint_eq_evalIntHomIndexEuler (p : ℤ[X][X]) (m l : ℂ) :
    evalIntPoint p m l = evalIntHomIndexEuler m l p :=
  rfl

/-- The value of `M`. -/
private theorem evalIntHomIndexEuler_C_X (m l : ℂ) : evalIntHomIndexEuler m l (C X) = m := by
  simp [evalIntHomIndexEuler]

/-- The value of `L`. -/
private theorem evalIntHomIndexEuler_X (m l : ℂ) : evalIntHomIndexEuler m l X = l := by
  simp [evalIntHomIndexEuler]

/-- The value of `(L ∂_L)(M ∂_M) p` at `(m, l)` is `l m (∂_L ∂_M p)(m, l)`. -/
theorem evalIntPoint_eulerEuler (p : ℤ[X][X]) (m l : ℂ) :
    evalIntPoint (eulerEuler p) m l =
      l * m * evalIntPoint (derivative (coeffDerivative p)) m l := by
  rw [eulerEuler_eq, evalIntPoint_eq_evalIntHomIndexEuler,
    evalIntPoint_eq_evalIntHomIndexEuler, map_mul, map_mul, evalIntHomIndexEuler_C_X,
    evalIntHomIndexEuler_X]
  ring

end AJConjecture
