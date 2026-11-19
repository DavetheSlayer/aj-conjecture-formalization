import Mathlib
import AJFamily.Quantum.FamSummationCheb
import AJHandoff.TorusQuantum.PairQFormula

/-!
# Summation by parts against the target polynomial

For every input `u`, `m ≥ 1` and `N ≥ 2m + 4`:
`∑_{j<N} G_j(N) 𝒯(q^N, q^j) D_j = (q^d q^N)^(m+1) ∑_{j<N} G_j(N) e_j`, `d = 2m + 3` (source Q9:
`H` is the adjoint image of the defect operator). As `sum_famKernel_mul_famTarget_torus`: apply
`sum_famKernel_mul_cycloCheb` with `(k, p) = (m-1, 1), (m, 1 - qJ), (m+1, qJ)` and combine with the
weights `(q^d x)^2, q^d x, 1` (definition of `famTarget`); the input enters only through
`D = pairQCycloCoeff u`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

theorem pairQ_sum_famKernel_mul_famTarget (m : ℕ) (hm : 1 ≤ m) (u : ℕ → RatFunc ℚ) {N : ℕ}
    (hN : 2 * m + 4 ≤ N) :
    ∑ j ∈ Finset.range N, famKernel m j N *
        (famTarget m qParam).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * pairQCycloCoeff u j =
      (qParam ^ (2 * m + 3) * qParam ^ (N : ℤ)) ^ (m + 1) *
        ∑ j ∈ Finset.range N, famKernel m j N * pairQCycloDefect m u j := by
  have h1 := sum_famKernel_mul_cycloCheb m hN (m - 1) 1 (pairQCycloCoeff u)
  have h2 := sum_famKernel_mul_cycloCheb m hN m (1 - C (C qParam) * X) (pairQCycloCoeff u)
  have h3 := sum_famKernel_mul_cycloCheb m hN (m + 1) (C (C qParam) * X) (pairQCycloCoeff u)
  set Q := qParam ^ (2 * m + 3) * qParam ^ (N : ℤ) with hQ
  have hL : ∑ j ∈ Finset.range N, famKernel m j N *
      (famTarget m qParam).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) * pairQCycloCoeff u j =
      Q ^ 2 * (∑ j ∈ Finset.range N, famKernel m j N *
        (famCheb m qParam (m - 1) 1).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
          pairQCycloCoeff u j) +
      Q * (∑ j ∈ Finset.range N, famKernel m j N *
        (famCheb m qParam m (1 - C (C qParam) * X)).evalEval (qParam ^ (N : ℤ))
          (qParam ^ j) * pairQCycloCoeff u j) -
      ∑ j ∈ Finset.range N, famKernel m j N *
        (famCheb m qParam (m + 1) (C (C qParam) * X)).evalEval (qParam ^ (N : ℤ))
          (qParam ^ j) * pairQCycloCoeff u j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [famTarget, evalEval_sub, evalEval_add, evalEval_mul, evalEval_mul, evalEval_C,
      evalEval_C, eval_pow, eval_mul, eval_C, eval_X]
    ring
  have hR : ∑ j ∈ Finset.range N, famKernel m j N * pairQCycloDefect m u j =
      (∑ j ∈ Finset.range N, famKernel m j N *
        (1 : (RatFunc ℚ)[X][X]).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
          cycloCheb (m - 1) (pairQCycloCoeff u) j) +
      (∑ j ∈ Finset.range N, famKernel m j N *
        (1 - C (C qParam) * X : (RatFunc ℚ)[X][X]).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
          cycloCheb m (pairQCycloCoeff u) j) -
      ∑ j ∈ Finset.range N, famKernel m j N *
        (C (C qParam) * X : (RatFunc ℚ)[X][X]).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
          cycloCheb (m + 1) (pairQCycloCoeff u) j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [pairQCycloDefect, evalEval_sub, evalEval_one, evalEval_mul, evalEval_C, evalEval_X,
      eval_C]
    ring
  rw [hL, hR]
  have e2 : Q ^ m = Q * Q ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have e3 : Q ^ (m + 1) = Q ^ 2 * Q ^ (m - 1) := by
    rw [← pow_add]; congr 1; omega
  rw [e2] at h2
  rw [e3] at h3 ⊢
  linear_combination -Q ^ 2 * h1 - Q * h2 + h3

end AJConjecture
