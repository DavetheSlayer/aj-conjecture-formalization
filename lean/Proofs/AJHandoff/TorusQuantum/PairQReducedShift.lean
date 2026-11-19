import Mathlib
import AJFamily.Quantum.FamKernelShift
import AJFamily.Quantum.FamTransferKernel
import AJHandoff.TorusQuantum.PairQFormula

/-!
# The shifted colours as sums against the transfer kernel

For every input `u`, `m`, `N ≥ 2m + 4` and `i ≤ 2m + 3`:
`F_(N-i) = ∑_{j<N} G_j(N) π_i(q^N, q^j) D_j` with `G_j(N) = famKernel m j N` (source: the basis
`R_i` of Q9, `C_j(N - i) = C_j(N) R_i(q^j)`). As `torusReducedFormula_sub_eq_sum_famKernel`, whose
proof uses only `cyclotomicKernel_sub_mul_famBasisPoly`, `famBasisPoly_zero_evalEval_ne_zero` and
the vanishing of `C_j(N - i)` for `N - i ≤ j < N`; it does not use the form of `u`.
-/

noncomputable section

namespace AJConjecture

/-- The cyclotomic kernel `C_j(M)` vanishes for `1 ≤ M ≤ j`: the factor `s = M` is zero. -/
private theorem pairQShift_cyclotomicKernel_natCast_eq_zero_of_le {j M : ℕ} (hM : 1 ≤ M)
    (hj : M ≤ j) : cyclotomicKernel j (M : ℤ) = 0 := by
  unfold cyclotomicKernel
  refine Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨hM, hj⟩) ?_
  rw [sub_self, zpow_zero, sub_self, mul_zero]

theorem pairQReducedFormula_sub_eq_sum_famKernel (m : ℕ) (u : ℕ → RatFunc ℚ) {N : ℕ}
    (hN : 2 * m + 4 ≤ N) {i : ℕ} (hi : i ≤ 2 * m + 3) :
    pairQReducedFormula u (N - i) =
      ∑ j ∈ Finset.range N, famKernel m j N *
        (famBasisPoly m qParam i).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) *
          pairQCycloCoeff u j := by
  have hcast : ((N - i : ℕ) : ℤ) = (N : ℤ) - i := by omega
  have hterm : ∀ j : ℕ, famKernel m j N *
      (famBasisPoly m qParam i).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) =
        cyclotomicKernel j ((N - i : ℕ) : ℤ) := by
    intro j
    have hΔ := famBasisPoly_zero_evalEval_ne_zero m (N := (N : ℤ)) (by omega) j
    rw [famKernel, div_mul_eq_mul_div, div_eq_iff hΔ, hcast,
      cyclotomicKernel_sub_mul_famBasisPoly m j N (by omega)]
  simp only [hterm]
  rw [pairQReducedFormula]
  refine Finset.sum_subset (Finset.range_subset_range.mpr (Nat.sub_le N i)) fun j _ hj ↦ ?_
  rw [Finset.mem_range, not_lt] at hj
  rw [pairQShift_cyclotomicKernel_natCast_eq_zero_of_le (by omega) hj, zero_mul]

end AJConjecture
