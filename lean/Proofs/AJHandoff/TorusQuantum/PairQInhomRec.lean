import Mathlib
import AJFamily.Quantum.FamTransferCramer
import AJHandoff.PairDefs
import AJHandoff.TorusQuantum.PairQCycloDefectVanish
import AJHandoff.TorusQuantum.PairQReducedShift
import AJHandoff.TorusQuantum.PairQTargetSum

/-!
# The inhomogeneous recurrence of order `d = 2rs + 3` for `T(r, s)`

For `N ≥ 2rs + 4`, with `u = pairQOddColor r s` and `m = rs`:
`∑_{i ≤ d} A_i(q^N) F_(N-i) = 𝒟(q^N) (q^d q^N)^(m+1) ∑_{j < r+s+1} G_j(N) e_j`.
Route (as `sum_famCoeff_mul_torusReducedFormula`): `pairQReducedFormula_sub_eq_sum_famKernel`,
the Cramer identity `sum_famCoeff_mul_famBasisPoly` evaluated at `(q^N, q^j)`,
`pairQ_sum_famKernel_mul_famTarget`, and `e_j = 0` for `r + s + 1 ≤ j < N`
(`pairQCycloDefect_eq_zero`; note `r + s + 1 < 2rs + 4 ≤ N`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

theorem pairQ_sum_famCoeff_mul_reducedFormula (r s : ℕ) (h : IsTorusPair r s) {N : ℕ}
    (hN : 2 * (r * s) + 4 ≤ N) :
    ∑ i : Fin (2 * (r * s) + 4),
        (famCoeff (r * s) qParam i).eval (qParam ^ (N : ℤ)) *
          pairQReducedFormula (pairQOddColor r s) (N - i) =
      (famDet (r * s) qParam).eval (qParam ^ (N : ℤ)) *
        (qParam ^ (2 * (r * s) + 3) * qParam ^ (N : ℤ)) ^ (r * s + 1) *
          ∑ j ∈ Finset.range (r + s + 1),
            famKernel (r * s) j N * pairQCycloDefect (r * s) (pairQOddColor r s) j := by
  obtain ⟨hr, hrs, -⟩ := h
  have hm : 1 ≤ r * s := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hsm : r + s + 1 ≤ N := by nlinarith
  have hcr : ∀ j : ℕ, ∑ i : Fin (2 * (r * s) + 4),
      (famCoeff (r * s) qParam i).eval (qParam ^ (N : ℤ)) *
        (famBasisPoly (r * s) qParam i).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) =
      (famDet (r * s) qParam).eval (qParam ^ (N : ℤ)) *
        (famTarget (r * s) qParam).evalEval (qParam ^ (N : ℤ)) (qParam ^ j) := by
    intro j
    have h := congrArg (evalEval (qParam ^ (N : ℤ)) (qParam ^ j))
      (sum_famCoeff_mul_famBasisPoly (r * s) hm qParam)
    simpa only [evalEval_finsetSum, evalEval_mul, evalEval_C] using h
  have hF : ∀ i : Fin (2 * (r * s) + 4), (famCoeff (r * s) qParam i).eval (qParam ^ (N : ℤ)) *
      pairQReducedFormula (pairQOddColor r s) (N - i) =
        ∑ j ∈ Finset.range N, famKernel (r * s) j N * pairQCycloCoeff (pairQOddColor r s) j *
          ((famCoeff (r * s) qParam i).eval (qParam ^ (N : ℤ)) *
            (famBasisPoly (r * s) qParam i).evalEval (qParam ^ (N : ℤ)) (qParam ^ j)) := by
    intro i
    have hi : (i : ℕ) ≤ 2 * (r * s) + 3 := by have := i.isLt; omega
    rw [pairQReducedFormula_sub_eq_sum_famKernel (r * s) _ hN hi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have htr : ∑ j ∈ Finset.range (r + s + 1),
      famKernel (r * s) j N * pairQCycloDefect (r * s) (pairQOddColor r s) j =
      ∑ j ∈ Finset.range N,
        famKernel (r * s) j N * pairQCycloDefect (r * s) (pairQOddColor r s) j := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr hsm) fun j _ hj ↦ ?_
    rw [Finset.mem_range, not_lt] at hj
    rw [pairQCycloDefect_eq_zero r s (by omega) (by omega) hj, mul_zero]
  simp only [hF]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hcr]
  rw [htr, mul_assoc, ← pairQ_sum_famKernel_mul_famTarget (r * s) hm _ hN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

end AJConjecture
