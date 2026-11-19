import Mathlib
import AJConjecture.RecurrenceIdeal

/-!
# Evaluation at `t = -1 + ε` in the dual numbers

The value and the first jet at `t = -1` of a recurrence operator are computed together by
evaluating `t` at `-1 + ε` in the dual numbers `ℂ[ε]/(ε²)`: `a(-1 + ε) = a(-1) + a'(-1) ε`.

* `dualJetHom : ℤ[t] → ℂ[ε]`, `t ↦ -1 + ε`.
* `dualQ = (-1 + ε)⁴ = 1 - 4ε`, the value of `q = t⁴`.
* `evalDualPoint P m l`: the value of `P ∈ ℤ[t][M][L]` at `t = -1 + ε`, `M = m`, `L = l`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The evaluation `ℤ[t] → ℂ[ε]/(ε²)` at `t = -1 + ε`. -/
def dualJetHom : ℤ[X] →+* DualNumber ℂ :=
  Polynomial.eval₂RingHom (Int.castRingHom (DualNumber ℂ)) (-1 + DualNumber.eps)

/-- The dual number `1 - 4ε`, the value of `q = t⁴` at `t = -1 + ε`. -/
def dualQ : DualNumber ℂ :=
  1 - 4 * DualNumber.eps

/-- The value of a recurrence operator at `t = -1 + ε`, `M = m`, `L = l`. -/
def evalDualPoint (P : RecOp) (m l : ℂ) : DualNumber ℂ :=
  (P.map (Polynomial.mapRingHom dualJetHom)).evalEval
    (TrivSqZeroExt.inl m) (TrivSqZeroExt.inl l)

end AJConjecture
