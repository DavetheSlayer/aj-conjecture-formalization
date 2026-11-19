import Mathlib
import AJHandoff.TorusQuantum.PairQTOrderCycloCoeff

/-!
# The `t`-valuation of the reduced formula of `T(r, s)` (source Q13)

For `r, s ≥ 2` and `N ≥ 1`: `F_N ≠ 0` and `ord_t F_N = -4(N-1)(rsN-1)`, the clause "the selected
`F` has `t`-valuation `−4(N−1)(rsN−1)`" of T-TRANSFER. For `j < N`,
`ord_t C_j(N) = 2j(j+1) - 4jN` (the factors `1 - q^(a-N)`, `a ≤ j < N`, have order `4(a - N)`,
the factors `1 - q^(a+N)` order `0`), so the term `j` of `F_N` has order
`4j - 4(rs - 1) j(j+1) - 4jN`, strictly decreasing in `j`; the term `j = N - 1` is the unique term
of least order (`pairQTOrder_sum_eq_of_lt`). Not used downstream: nonrationality goes through the
degree at `t = ∞` (`PairQNotRational`), which is independent of `(r, s)`.
-/

noncomputable section

namespace AJConjecture

/-- The cyclotomic kernel `C_j(N)`, `j < N`, is nonzero of order `2j(j+1) - 4jN`. -/
private theorem pairQTOrder_cyclotomicKernel_of_lt {N : ℕ} (j : ℕ) (hj : j < N) :
    cyclotomicKernel j N ≠ 0 ∧ pairQTOrder (cyclotomicKernel j N) =
      2 * (j : ℤ) * ((j : ℤ) + 1) - 4 * (j : ℤ) * N := by
  induction j with
  | zero =>
    rw [cyclotomicKernel, Finset.Icc_eq_empty (by omega), Finset.prod_empty]
    exact ⟨one_ne_zero, by simpa using pairQTOrder_X_zpow 0⟩
  | succ j ih =>
    have h1 := pairQTOrder_one_sub_qParam_zpow_of_pos (k := ((j + 1 : ℕ) : ℤ) + N) (by omega)
    have h2 := pairQTOrder_one_sub_qParam_zpow_of_neg (k := ((j + 1 : ℕ) : ℤ) - N) (by omega)
    have h3 := pairQTOrder_mul_eq (ih (by omega)) (pairQTOrder_mul_eq h1 h2)
    rw [cyclotomicKernel, Finset.prod_Icc_succ_top (by omega)]
    refine ⟨h3.1, h3.2.trans ?_⟩
    push_cast
    ring

theorem pairQ_tOrder_reducedFormula (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) {N : ℕ}
    (hN : 1 ≤ N) :
    pairQReducedFormula (pairQOddColor r s) N ≠ 0 ∧
      pairQTOrder (pairQReducedFormula (pairQOddColor r s) N) =
        -4 * ((N : ℤ) - 1) * ((r : ℤ) * s * N - 1) := by
  have hterm : ∀ j : ℕ, j < N → cyclotomicKernel j N * pairQCycloCoeff (pairQOddColor r s) j ≠ 0 ∧
      pairQTOrder (cyclotomicKernel j N * pairQCycloCoeff (pairQOddColor r s) j) =
        4 * (j : ℤ) - 4 * (j : ℤ) * N - 4 * ((r : ℤ) * s - 1) * j * ((j : ℤ) + 1) :=
    fun j hj ↦ by
      have h := pairQTOrder_mul_eq (pairQTOrder_cyclotomicKernel_of_lt j hj)
        (pairQ_tOrder_cycloCoeff r s hr hs j)
      refine ⟨h.1, h.2.trans ?_⟩
      ring
  have hr0 : (2 : ℤ) ≤ r := by exact_mod_cast hr
  have hs0 : (2 : ℤ) ≤ s := by exact_mod_cast hs
  have hrs : (4 : ℤ) ≤ r * s := by nlinarith
  rw [pairQReducedFormula]
  refine pairQTOrder_sum_eq_of_lt (a := N - 1) (Finset.mem_range.mpr (by omega))
    ⟨(hterm (N - 1) (by omega)).1, ?_⟩ fun j hj hjN ↦ Or.inr ?_
  · rw [(hterm (N - 1) (by omega)).2, Nat.cast_sub hN]
    push_cast
    ring
  · have hj' : j < N := Finset.mem_range.mp hj
    rw [(hterm j hj').2]
    have h1 : (j : ℤ) + 2 ≤ N := by omega
    have h2 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
    have h3 : (j : ℤ) * ((j : ℤ) + 1) < ((N : ℤ) - 1) * N := by nlinarith
    have h4 : (j : ℤ) * N ≤ ((N : ℤ) - 1) * N := by nlinarith
    have h5 : ((r : ℤ) * s - 1) * ((j : ℤ) * ((j : ℤ) + 1)) <
        ((r : ℤ) * s - 1) * (((N : ℤ) - 1) * N) :=
      mul_lt_mul_of_pos_left h3 (by omega)
    nlinarith

end AJConjecture
