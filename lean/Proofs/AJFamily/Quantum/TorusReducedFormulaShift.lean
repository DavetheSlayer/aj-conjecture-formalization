import Mathlib
import AJFamily.Quantum.FamKernelShift
import AJFamily.Quantum.FamTransferKernel
import AJFamily.Quantum.TorusFormula

/-!
# The shifted reduced formula

For `N ≥ 4a + 4` and `i ≤ 4a + 3`, `F_(N-i)` is written as a sum over `j < N` against the family
kernel at the colour `N`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The cyclotomic kernel `C_j(M)` vanishes for `1 ≤ M ≤ j`: the factor `s = M` is zero. -/
private theorem torusShift_cyclotomicKernel_natCast_eq_zero_of_le {j M : ℕ} (hM : 1 ≤ M)
    (hj : M ≤ j) : cyclotomicKernel j (M : ℤ) = 0 := by
  unfold cyclotomicKernel
  refine Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨hM, hj⟩) ?_
  rw [sub_self, zpow_zero, sub_self, mul_zero]

/-- The reduced torus-knot formula at the colour `N - i` as a sum over `j < N` against the
family kernel at the colour `N`. -/
theorem torusReducedFormula_sub_eq_sum_famKernel (a : ℕ) {N : ℕ} (hN : 4 * a + 4 ≤ N) {i : ℕ}
    (hi : i ≤ 4 * a + 3) :
    torusReducedFormula a (N - i) =
      ∑ j ∈ Finset.range N, famKernel (2 * a) j N *
        (famBasisPoly (2 * a) qParam i).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
          torusCyclotomicCoeff a j := by
  have hcast : ((N - i : ℕ) : ℤ) = (N : ℤ) - i := by omega
  have hterm : ∀ j : ℕ, famKernel (2 * a) j N *
      (famBasisPoly (2 * a) qParam i).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) =
        cyclotomicKernel j ((N - i : ℕ) : ℤ) := by
    intro j
    have hΔ := famBasisPoly_zero_evalEval_ne_zero (2 * a) (N := (N : ℤ))
      (by push_cast; omega) j
    rw [famKernel, div_mul_eq_mul_div, div_eq_iff hΔ, hcast,
      cyclotomicKernel_sub_mul_famBasisPoly (2 * a) j N (by omega)]
  simp only [hterm]
  rw [torusReducedFormula]
  refine Finset.sum_subset (Finset.range_subset_range.mpr (Nat.sub_le N i)) fun j _ hj ↦ ?_
  rw [Finset.mem_range, not_lt] at hj
  rw [torusShift_cyclotomicKernel_natCast_eq_zero_of_le (by omega) hj, zero_mul]

end AJConjecture
