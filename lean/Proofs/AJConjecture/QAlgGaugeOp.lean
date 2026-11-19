import Mathlib
import AJConjecture.RecurrenceIdeal

/-!
# The gauge from the unreduced to the reduced formula

`[n + k] (t² - t⁻²) = t^(-2(n+k)) (t^(4k) M² - 1)` at `M = t^(2n)`. Multiplying the coefficient
of `L^k` of an operator `Q` of degree `r` by `t^(2(r-k)) (t^(4k) M² - 1)` therefore turns the
action of `Q` on `n ↦ [n] g(n)` into the action of the gauged operator on `g`, up to the factor
`t^(2r+2n) (t² - t⁻²)`. All exponents of `t` are even or cancel at `t = -1`, so the gauge
multiplies the specialisation by `M² - 1`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The gauge of a recurrence operator: the coefficient of `L^k` is multiplied by
`t^(2(deg Q - k)) (t^(4k) M² - 1)`. -/
def gaugeOp (Q : RecOp) : RecOp :=
  Q.sum fun k c ↦
    monomial k (c * (C (X ^ (2 * (Q.natDegree - k))) * (C (X ^ (4 * k)) * X ^ 2 - 1)))

end AJConjecture
