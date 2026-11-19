import Mathlib
import AJFamily.Quantum.FamSummationCheb
import AJFamily.Quantum.TorusCycloDefect

/-!
# Kernel sum of the target polynomial

The kernel sum of `famTarget (2a)` against `D_j` is `(q^(4a+3) q^N)^(2a+1)` times the kernel sum of
the cyclotomic defect.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

theorem sum_famKernel_mul_famTarget_torus (a : ℕ) (ha : 1 ≤ a) {N : ℕ} (hN : 4 * a + 4 ≤ N) :
    ∑ j ∈ Finset.range N, famKernel (2 * a) j N *
        (famTarget (2 * a) qParam).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
          torusCyclotomicCoeff a j =
      (qParam ^ (4 * a + 3) * qParam ^ (N : ℤ)) ^ (2 * a + 1) *
        ∑ j ∈ Finset.range N, famKernel (2 * a) j N * torusCycloDefect a j := by
  have hN' : 2 * (2 * a) + 4 ≤ N := by omega
  have he : 2 * (2 * a) + 3 = 4 * a + 3 := by ring
  have h1 := sum_famKernel_mul_cycloCheb (2 * a) hN' (2 * a - 1) 1 (torusCyclotomicCoeff a)
  have h2 := sum_famKernel_mul_cycloCheb (2 * a) hN' (2 * a) (1 - C (C qParam) * X)
    (torusCyclotomicCoeff a)
  have h3 := sum_famKernel_mul_cycloCheb (2 * a) hN' (2 * a + 1) (C (C qParam) * X)
    (torusCyclotomicCoeff a)
  rw [he] at h1 h2 h3
  set Q := qParam ^ (4 * a + 3) * qParam ^ (N : ℤ) with hQ
  have hL : ∑ j ∈ Finset.range N, famKernel (2 * a) j N *
      (famTarget (2 * a) qParam).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
        torusCyclotomicCoeff a j =
      Q ^ 2 * (∑ j ∈ Finset.range N, famKernel (2 * a) j N *
        (famCheb (2 * a) qParam (2 * a - 1) 1).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
          torusCyclotomicCoeff a j) +
      Q * (∑ j ∈ Finset.range N, famKernel (2 * a) j N *
        (famCheb (2 * a) qParam (2 * a) (1 - C (C qParam) * X)).evalEval (qParam ^ (N : ℤ))
          (qParam ^ j) * torusCyclotomicCoeff a j) -
      ∑ j ∈ Finset.range N, famKernel (2 * a) j N *
        (famCheb (2 * a) qParam (2 * a + 1) (C (C qParam) * X)).evalEval (qParam ^ (N : ℤ))
          (qParam ^ j) * torusCyclotomicCoeff a j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [famTarget, evalEval_sub, evalEval_add, evalEval_mul, evalEval_mul, evalEval_C,
      evalEval_C, eval_pow, eval_mul, eval_C, eval_X, he]
    ring
  have hR : ∑ j ∈ Finset.range N, famKernel (2 * a) j N * torusCycloDefect a j =
      (∑ j ∈ Finset.range N, famKernel (2 * a) j N *
        (1 : (RatFunc ℚ)[X][X]).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
          cycloCheb (2 * a - 1) (torusCyclotomicCoeff a) j) +
      (∑ j ∈ Finset.range N, famKernel (2 * a) j N *
        (1 - C (C qParam) * X : (RatFunc ℚ)[X][X]).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
          cycloCheb (2 * a) (torusCyclotomicCoeff a) j) -
      ∑ j ∈ Finset.range N, famKernel (2 * a) j N *
        (C (C qParam) * X : (RatFunc ℚ)[X][X]).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
          cycloCheb (2 * a + 1) (torusCyclotomicCoeff a) j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [torusCycloDefect, evalEval_sub, evalEval_one, evalEval_mul, evalEval_C, evalEval_X,
      eval_C]
    ring
  rw [hL, hR]
  have e2 : Q ^ (2 * a) = Q * Q ^ (2 * a - 1) := by
    rw [← pow_succ']; congr 1; omega
  have e3 : Q ^ (2 * a + 1) = Q ^ 2 * Q ^ (2 * a - 1) := by
    rw [← pow_add]; congr 1; omega
  rw [e2] at h2
  rw [e3] at h3 ⊢
  linear_combination -Q ^ 2 * h1 - Q * h2 + h3

end AJConjecture
