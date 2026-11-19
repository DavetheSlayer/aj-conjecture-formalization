import Mathlib
import AJFamily.Quantum.FamSummationByParts

/-!
# The twisted Chebyshev operators against the family kernel

`sum_famKernel_mul_cycloCheb`: `cycloCheb k` moves across the family kernel as `famCheb m q k`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The adjoint of the twisted Chebyshev operator `S_k(V)` against the family kernel is
`famCheb m q k`. -/
theorem sum_famKernel_mul_cycloCheb (m : ℕ) {N : ℕ} (hN : 2 * m + 4 ≤ N) (k : ℕ)
    (n : (RatFunc ℚ)[X][X]) (y : ℕ → RatFunc ℚ) :
    (qParam ^ (2 * m + 3) * qParam ^ (N : ℤ)) ^ k *
        ∑ j ∈ Finset.range N,
          famKernel m j N * n.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * cycloCheb k y j =
      ∑ j ∈ Finset.range N, famKernel m j N *
        (famCheb m qParam k n).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * y j := by
  induction k using Nat.twoStepInduction generalizing n with
  | zero =>
    rw [pow_zero, one_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [cycloCheb, famCheb, two_mul, evalEval_add]
    ring
  | one =>
    rw [pow_one]
    exact sum_famKernel_mul_cycloStep m hN n y
  | more k ih0 ih1 =>
    have hqi : qParam * qParam⁻¹ = 1 := mul_inv_cancel₀ qParam_ne_zero
    have h1 := ih1 (famAdjoint m qParam n)
    have h0 := ih0 n
    have hs := sum_famKernel_mul_cycloStep m hN n (cycloCheb (k + 1) y)
    have hL : ∑ j ∈ Finset.range N, famKernel m j N *
        n.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * cycloCheb (k + 2) y j =
        (∑ j ∈ Finset.range N, famKernel m j N *
          n.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * cycloStep (cycloCheb (k + 1) y) j) -
        qParam⁻¹ * ∑ j ∈ Finset.range N, famKernel m j N *
          n.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * cycloCheb k y j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [cycloCheb]
      ring
    have hR : ∑ j ∈ Finset.range N, famKernel m j N *
        (famCheb m qParam (k + 2) n).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * y j =
        (∑ j ∈ Finset.range N, famKernel m j N * (famCheb m qParam (k + 1)
          (famAdjoint m qParam n)).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * y j) -
        qParam ^ (4 * m + 5) * (qParam ^ (N : ℤ)) ^ 2 *
          ∑ j ∈ Finset.range N, famKernel m j N *
          (famCheb m qParam k n).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * y j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [famCheb, evalEval_sub, evalEval_mul, evalEval_C, eval_mul, eval_C, eval_pow,
        eval_X]
      ring
    rw [hL, hR]
    linear_combination (qParam ^ (2 * m + 3) * qParam ^ (N : ℤ)) ^ (k + 1) * hs + h1 -
      qParam ^ (4 * m + 5) * (qParam ^ (N : ℤ)) ^ 2 * h0 -
      (qParam ^ (2 * m + 3) * qParam ^ (N : ℤ)) ^ k * (∑ j ∈ Finset.range N, famKernel m j N *
        n.evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * cycloCheb k y j) * qParam ^ (4 * m + 5) *
          (qParam ^ (N : ℤ)) ^ 2 * hqi

end AJConjecture
