import Mathlib
import AJFamily.Quantum.FamTransferCramer
import AJFamily.Quantum.TorusCycloDefectVanishes
import AJFamily.Quantum.TorusReducedFormulaShift
import AJFamily.Quantum.TorusTargetSum

/-!
# The inhomogeneous recurrence of the reduced formula

For `N ≥ 4a + 4`, the family operator applied to the reduced formula gives a finite sum over
`j < a + 3` of kernel values times the cyclotomic defect.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

theorem sum_famCoeff_mul_torusReducedFormula (a : ℕ) (ha : 1 ≤ a) {N : ℕ} (hN : 4 * a + 4 ≤ N) :
    ∑ i : Fin (2 * (2 * a) + 4),
        (famCoeff (2 * a) qParam i).eval (qParam ^ (N : ℤ)) * torusReducedFormula a (N - i) =
      (famDet (2 * a) qParam).eval (qParam ^ (N : ℤ)) *
        (qParam ^ (4 * a + 3) * qParam ^ (N : ℤ)) ^ (2 * a + 1) *
          ∑ j ∈ Finset.range (a + 3), famKernel (2 * a) j N * torusCycloDefect a j := by
  have hcr : ∀ j : ℕ, ∑ i : Fin (2 * (2 * a) + 4),
      (famCoeff (2 * a) qParam i).eval (qParam ^ (N : ℤ)) *
        (famBasisPoly (2 * a) qParam i).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) =
      (famDet (2 * a) qParam).eval (qParam ^ (N : ℤ)) *
        (famTarget (2 * a) qParam).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) := by
    intro j
    have h := congrArg (evalEval (qParam ^ (N : ℤ)) (qParam ^ j))
      (sum_famCoeff_mul_famBasisPoly (2 * a) (by omega) qParam)
    simpa only [evalEval_finsetSum, evalEval_mul, evalEval_C] using h
  have hF : ∀ i : Fin (2 * (2 * a) + 4), (famCoeff (2 * a) qParam i).eval (qParam ^ (N : ℤ)) *
      torusReducedFormula a (N - i) =
        ∑ j ∈ Finset.range N, famKernel (2 * a) j N * torusCyclotomicCoeff a j *
          ((famCoeff (2 * a) qParam i).eval (qParam ^ (N : ℤ)) *
            (famBasisPoly (2 * a) qParam i).evalEval (qParam ^ (N : ℤ)) (qParam ^ j)) := by
    intro i
    have hi : (i : ℕ) ≤ 4 * a + 3 := by have := i.isLt; omega
    rw [torusReducedFormula_sub_eq_sum_famKernel a hN hi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have htr : ∑ j ∈ Finset.range (a + 3), famKernel (2 * a) j N * torusCycloDefect a j =
      ∑ j ∈ Finset.range N, famKernel (2 * a) j N * torusCycloDefect a j := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun j _ hj ↦ ?_
    rw [Finset.mem_range, not_lt] at hj
    rw [torusCycloDefect_eq_zero a ha hj, mul_zero]
  simp only [hF]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hcr]
  rw [htr, mul_assoc, ← sum_famKernel_mul_famTarget_torus a ha hN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

end AJConjecture
