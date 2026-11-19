import Mathlib
import AJConjecture.QAlgCoeffShift
import AJConjecture.QAlgOreMul

/-!
# Homogenisation of an inhomogeneous recurrence

If `δ · (P f) = β` for coefficients `β`, `δ`, the first-order operator
`β σ(δ) L - σ(β) δ` kills the right-hand side, so its Ore product with `P` annihilates `f`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The homogenisation `(β σ(δ) L - σ(β) δ) ⋆ P` of `P` along the right-hand side `β / δ`. -/
def homogenizeOp (β δ : Coeff) (P : RecOp) : RecOp :=
  oreMul coeffShift (C (β * coeffShift δ) * X - C (coeffShift β * δ)) P

end AJConjecture
