import Mathlib
import AJHandoff.TorusQuantum.PairQCycloCoeffDegree

/-!
# The degree in `t` of the reduced formula

Under the hypotheses of `pairQ_intDegree_cycloCoeff`, for `N ≥ 1`: `F_N ≠ 0` and
`deg_t F_N = 4N(N-1)`. For `j < N`, `deg_t C_j(N) = 4jN + 2j(j+1)`, so the term `j` of `F_N` has
degree `4jN`, strictly increasing in `j`; the term `j = N - 1` dominates. As
`intDegree_torusReducedFormula`.
-/

noncomputable section

namespace AJConjecture

/-- `1 - q^k`, `k > 0`, is nonzero of degree `4k` in `t`. -/
private theorem intDegree_one_sub_qParam_zpow_of_pos_pairQReduced {k : ℤ} (hk : 0 < k) :
    1 - qParam ^ k ≠ 0 ∧ (1 - qParam ^ k).intDegree = 4 * k := by
  rw [sub_eq_neg_add]
  refine intDegree_add_eq_of_lt
    ⟨neg_ne_zero.mpr (zpow_ne_zero k qParam_ne_zero), ?_⟩ (Or.inr ?_)
  · rw [RatFunc.intDegree_neg, intDegree_qParam_zpow]
  · rw [RatFunc.intDegree_one]
    omega

/-- `1 - q^k`, `k < 0`, is nonzero of degree `0` in `t`. -/
private theorem intDegree_one_sub_qParam_zpow_of_neg_pairQReduced {k : ℤ} (hk : k < 0) :
    1 - qParam ^ k ≠ 0 ∧ (1 - qParam ^ k).intDegree = 0 := by
  rw [sub_eq_add_neg]
  refine intDegree_add_eq_of_lt ⟨one_ne_zero, RatFunc.intDegree_one⟩ (Or.inr ?_)
  rw [RatFunc.intDegree_neg, intDegree_qParam_zpow]
  omega

/-- The cyclotomic kernel `C_j(N)`, `j < N`, is nonzero of degree `4jN + 2j(j+1)` in `t`. -/
private theorem intDegree_cyclotomicKernel_of_lt_pairQReduced {N : ℕ} (j : ℕ) (hj : j < N) :
    cyclotomicKernel j N ≠ 0 ∧ (cyclotomicKernel j N).intDegree =
      4 * (j : ℤ) * N + 2 * (j : ℤ) * ((j : ℤ) + 1) := by
  induction j with
  | zero =>
    rw [cyclotomicKernel, Finset.Icc_eq_empty (by omega), Finset.prod_empty]
    exact ⟨one_ne_zero, by rw [RatFunc.intDegree_one]; simp⟩
  | succ j ih =>
    have h1 := intDegree_one_sub_qParam_zpow_of_pos_pairQReduced
      (k := ((j + 1 : ℕ) : ℤ) + N) (by omega)
    have h2 := intDegree_one_sub_qParam_zpow_of_neg_pairQReduced
      (k := ((j + 1 : ℕ) : ℤ) - N) (by omega)
    have h3 := intDegree_mul_eq (ih (by omega))
      (intDegree_mul_eq h1 h2)
    rw [cyclotomicKernel, Finset.prod_Icc_succ_top (by omega)]
    refine ⟨h3.1, h3.2.trans ?_⟩
    push_cast
    ring

theorem pairQ_intDegree_reducedFormula (u : ℕ → RatFunc ℚ) (h0 : u 0 = 1)
    (hdeg : ∀ n : ℕ, 1 ≤ n → u n = 0 ∨ (u n).intDegree ≤ 0) {N : ℕ} (hN : 1 ≤ N) :
    pairQReducedFormula u N ≠ 0 ∧
      (pairQReducedFormula u N).intDegree = 4 * (N : ℤ) * ((N : ℤ) - 1) := by
  have hterm : ∀ j : ℕ, j < N → cyclotomicKernel j N * pairQCycloCoeff u j ≠ 0 ∧
      (cyclotomicKernel j N * pairQCycloCoeff u j).intDegree = 4 * (j : ℤ) * N :=
    fun j hj ↦ by
      have h := intDegree_mul_eq (intDegree_cyclotomicKernel_of_lt_pairQReduced j hj)
        (pairQ_intDegree_cycloCoeff u h0 hdeg j)
      refine ⟨h.1, h.2.trans ?_⟩
      ring
  rw [pairQReducedFormula]
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
