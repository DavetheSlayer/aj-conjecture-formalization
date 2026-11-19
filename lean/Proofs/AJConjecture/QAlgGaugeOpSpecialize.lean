import Mathlib
import AJConjecture.QAlgGaugeOp

/-!
# The specialisation of the gauged operator

At `t = -1` the gauge factor `t^(2(r-k)) (t^(4k) M² - 1)` is `M² - 1` for every `k`:
`specialize (gaugeOp Q) = (M² - 1) · specialize Q`.
-/

open Polynomial

namespace AJConjecture

/-- The gauge multiplies the specialisation at `t = -1` by `M² - 1`. -/
theorem specialize_gaugeOp (Q : RecOp) :
    specialize (gaugeOp Q) = C (X ^ 2 - 1) * specialize Q := by
  have hG : ∀ k : ℕ, (C (X ^ (2 * (Q.natDegree - k))) * (C (X ^ (4 * k)) * X ^ 2 - 1) :
      Coeff).map (Polynomial.evalRingHom (-1 : ℤ)) = X ^ 2 - 1 := by
    intro k
    have h4 : 4 * k = 2 * (2 * k) := by ring
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_one, coe_evalRingHom, eval_pow, eval_X, h4, pow_mul,
      neg_one_sq, one_pow, C_1, one_mul]
  conv_rhs => rw [Q.as_sum_support]
  rw [gaugeOp, Polynomial.sum_def, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [specialize, coe_mapRingHom, Polynomial.map_monomial, Polynomial.map_mul, hG,
    Polynomial.C_mul_monomial]
  rw [mul_comm]

end AJConjecture
