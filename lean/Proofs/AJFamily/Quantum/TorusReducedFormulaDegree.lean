import Mathlib
import AJFamily.Quantum.TorusCyclotomicCoeffDegree

/-!
# Degree of the torus reduced formula

For `a ≥ 2` and `N ≥ 1`, `F_N` is nonzero of `t`-degree `4N(N-1)`; the term `j = N - 1` dominates.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- `1 - q^k`, `k > 0`, is nonzero of degree `4k` in `t`. -/
private theorem intDegree_one_sub_qParam_zpow_of_pos_torusReduced {k : ℤ} (hk : 0 < k) :
    1 - qParam ^ k ≠ 0 ∧ (1 - qParam ^ k).intDegree = 4 * k := by
  rw [sub_eq_neg_add]
  refine intDegree_add_eq_of_lt
    ⟨neg_ne_zero.mpr (zpow_ne_zero k qParam_ne_zero), ?_⟩ (Or.inr ?_)
  · rw [RatFunc.intDegree_neg, intDegree_qParam_zpow]
  · rw [RatFunc.intDegree_one]
    omega

/-- `1 - q^k`, `k < 0`, is nonzero of degree `0` in `t`. -/
private theorem intDegree_one_sub_qParam_zpow_of_neg_torusReduced {k : ℤ} (hk : k < 0) :
    1 - qParam ^ k ≠ 0 ∧ (1 - qParam ^ k).intDegree = 0 := by
  rw [sub_eq_add_neg]
  refine intDegree_add_eq_of_lt ⟨one_ne_zero, RatFunc.intDegree_one⟩ (Or.inr ?_)
  rw [RatFunc.intDegree_neg, intDegree_qParam_zpow]
  omega

/-- The cyclotomic kernel `C_j(N)`, `j < N`, is nonzero of degree `4jN + 2j(j+1)` in `t`. -/
private theorem intDegree_cyclotomicKernel_of_lt_torusReduced {N : ℕ} (j : ℕ) (hj : j < N) :
    cyclotomicKernel j N ≠ 0 ∧ (cyclotomicKernel j N).intDegree =
      4 * (j : ℤ) * N + 2 * (j : ℤ) * ((j : ℤ) + 1) := by
  induction j with
  | zero =>
    rw [cyclotomicKernel, Finset.Icc_eq_empty (by omega), Finset.prod_empty]
    exact ⟨one_ne_zero, by rw [RatFunc.intDegree_one]; simp⟩
  | succ j ih =>
    have h1 := intDegree_one_sub_qParam_zpow_of_pos_torusReduced
      (k := ((j + 1 : ℕ) : ℤ) + N) (by omega)
    have h2 := intDegree_one_sub_qParam_zpow_of_neg_torusReduced
      (k := ((j + 1 : ℕ) : ℤ) - N) (by omega)
    have h3 := intDegree_mul_eq (ih (by omega))
      (intDegree_mul_eq h1 h2)
    rw [cyclotomicKernel, Finset.prod_Icc_succ_top (by omega)]
    refine ⟨h3.1, h3.2.trans ?_⟩
    push_cast
    ring

/-- The reduced formula `F_N` of `T(2, a)`, `a ≥ 2`, `N ≥ 1`, is nonzero of degree `4N(N-1)`
in `t`. -/
theorem intDegree_torusReducedFormula (a : ℕ) (ha : 2 ≤ a) {N : ℕ} (hN : 1 ≤ N) :
    torusReducedFormula a N ≠ 0 ∧
      (torusReducedFormula a N).intDegree = 4 * (N : ℤ) * ((N : ℤ) - 1) := by
  have hterm : ∀ j : ℕ, j < N → cyclotomicKernel j N * torusCyclotomicCoeff a j ≠ 0 ∧
      (cyclotomicKernel j N * torusCyclotomicCoeff a j).intDegree = 4 * (j : ℤ) * N :=
    fun j hj ↦ by
      have h := intDegree_mul_eq (intDegree_cyclotomicKernel_of_lt_torusReduced j hj)
        (intDegree_torusCyclotomicCoeff a ha j)
      refine ⟨h.1, h.2.trans ?_⟩
      ring
  rw [torusReducedFormula]
  refine intDegree_sum_eq_of_lt (a := N - 1) (Finset.mem_range.mpr (by omega))
    ⟨(hterm (N - 1) (by omega)).1, ?_⟩ fun j hj hjN ↦ Or.inr ?_
  · rw [(hterm (N - 1) (by omega)).2, Nat.cast_sub hN]
    push_cast
    ring
  · have hj' : j < N := Finset.mem_range.mp hj
    rw [(hterm j hj').2]
    have h1 : (j : ℤ) + 2 ≤ N := by omega
    have h2 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
    nlinarith

end AJConjecture
