import Mathlib
import AJFamily.Quantum.FamTransferMap
import AJFamily.Quantum.FamTransferOp

/-!
# The family transfer operator at `t = -1`

`specialize_famTransferOp_eq_sum`: at `t = -1` the coefficients of `famTransferOp m` are the
Cramer coefficients at `q = 1`, `x = M²`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The specialisation at `t = -1` of the family transfer operator, in terms of the family
Cramer coefficients at `q = 1`. -/
theorem specialize_famTransferOp_eq_sum (m : ℕ) :
    specialize (famTransferOp m) =
      ∑ k : Fin (2 * m + 4), C ((famCoeff m (1 : ℤ) (Fin.rev k)).comp (X ^ 2)) * X ^ (k : ℕ) := by
  have hq : (Polynomial.evalRingHom (-1 : ℤ)) (X ^ 4) = 1 := by
    rw [coe_evalRingHom, eval_pow, eval_X]
    norm_num
  have hx : (C (X ^ (4 * (2 * m + 3))) * X ^ 2 : ℤ[X][X]).map
      (Polynomial.evalRingHom (-1 : ℤ)) = X ^ 2 := by
    rw [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, coe_evalRingHom, eval_pow, eval_X,
      pow_mul]
    norm_num
  rw [famTransferOp, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [specialize, coe_mapRingHom, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C,
    coe_mapRingHom, Polynomial.map_comp, map_famCoeff, hq, hx]

end AJConjecture
