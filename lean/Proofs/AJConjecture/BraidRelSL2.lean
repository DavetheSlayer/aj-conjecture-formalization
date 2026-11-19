import Mathlib

/-!
# Two elements of `SL₂(ℂ)` satisfying the braid relation

If `c d c = d c d` in `SL₂(ℂ)`, then `c` and `d` commute, or the central element `(c d c)²`
of the trefoil group is `-1`. With `u = c d c` one has `u c = d u` and `u d = c u`, so `u²`
commutes with `c`; by Cayley–Hamilton `u² = (tr u) u - 1`, hence `(tr u) (u c - c u) = 0`.
-/

namespace AJConjecture

/-- Cayley–Hamilton for a `2 × 2` matrix of determinant one. -/
theorem braidRel_sq_eq_trace_smul_sub_one (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U.det = 1) :
    U * U = U.trace • U - 1 := by
  rw [Matrix.det_fin_two] at hU
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first
      | ring1
      | linear_combination (-1 : ℂ) * hU

end AJConjecture
