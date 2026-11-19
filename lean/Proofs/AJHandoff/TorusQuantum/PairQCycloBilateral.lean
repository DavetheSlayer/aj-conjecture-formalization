import Mathlib
import AJConjecture.QAlgCycloKernelAntisymm
import AJHandoff.TorusQuantum.PairQFormula

/-!
# The cyclotomic coefficients as a bilateral transform

For every input `u`, `2 D_j = 𝔅_j(ũ)`, where `ũ = pairQOddExt u` is the odd extension
`ũ(-n-1) = -ũ(n)` and `𝔅_j = cycloBilateralSum` sums against the kernel `K_{j,n}` on
`-j-1 ≤ n ≤ j`. The reflection `n ↦ -n-1` changes the sign of both `K_{j,n}`
(`cycloBilateralKernel_neg_sub_one`) and `ũ`, so the bilateral sum is twice the sum over
`0 ≤ n ≤ j`, which is `D_j`. This is `two_mul_torusCyclotomicCoeff` for an arbitrary input; its
proof does not use the form of the input.
-/

noncomputable section

namespace AJConjecture

/-- Oddness of the odd extension under `n ↦ -n - 1`. -/
private theorem pairQOddExt_neg_sub_one_bilateral (u : ℕ → RatFunc ℚ) (n : ℤ) :
    pairQOddExt u (-n - 1) = -pairQOddExt u n := by
  unfold pairQOddExt
  rcases le_or_gt 0 n with hn | hn
  · rw [ite_eq_left hn, ite_eq_right (by omega : ¬(0 : ℤ) ≤ -n - 1),
      show (-(-n - 1) - 1) = n by ring]
  · rw [ite_eq_right (by omega : ¬(0 : ℤ) ≤ n), ite_eq_left (by omega : (0 : ℤ) ≤ -n - 1), neg_neg]

/-- The half of the bilateral sum over `0 ≤ n ≤ j` is the cyclotomic coefficient of `u`. -/
private theorem sum_Icc_zero_cycloBilateralKernel_mul_pairQOddExt (u : ℕ → RatFunc ℚ)
    (j : ℕ) :
    ∑ n ∈ Finset.Icc (0 : ℤ) (j : ℤ), cycloBilateralKernel j n * pairQOddExt u n =
      pairQCycloCoeff u j := by
  rw [pairQCycloCoeff, Finset.mul_sum]
  refine Finset.sum_nbij' (fun n ↦ n.toNat) (fun m ↦ (m : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    omega
  · intro m hm
    rw [Finset.mem_range] at hm
    rw [Finset.mem_Icc]
    omega
  · intro n hn
    rw [Finset.mem_Icc] at hn
    omega
  · intro m _
    exact Int.toNat_natCast m
  · intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn.1
    have hm : m ≤ j := by omega
    have hE : (m : ℤ) * ((m : ℤ) + 1) / 2 = ((m * (m + 1) / 2 : ℕ) : ℤ) := by norm_cast
    rw [cycloBilateralKernel, ite_eq_left (by omega), pairQOddExt,
      ite_eq_left (by omega), Int.toNat_natCast, show ((j : ℤ) - (m : ℤ)).toNat = j - m by omega,
      show ((j : ℤ) + (m : ℤ) + 1).toNat = j + m + 1 by omega, hE, zpow_natCast, zpow_natCast]
    ring

/-- Twice the cyclotomic coefficient of `u` is the bilateral transform of its odd extension. -/
theorem pairQ_two_mul_cycloCoeff (u : ℕ → RatFunc ℚ) (j : ℕ) :
    2 * pairQCycloCoeff u j = cycloBilateralSum (pairQOddExt u) j := by
  have hU : Finset.Icc (-((j : ℤ) + 1)) (j : ℤ) =
      Finset.Icc (-((j : ℤ) + 1)) (-1) ∪ Finset.Icc (0 : ℤ) (j : ℤ) := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hD : Disjoint (Finset.Icc (-((j : ℤ) + 1)) (-1)) (Finset.Icc (0 : ℤ) (j : ℤ)) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    rw [Finset.mem_Icc] at h1 h2
    omega
  have hneg : ∑ n ∈ Finset.Icc (-((j : ℤ) + 1)) (-1),
      cycloBilateralKernel j n * pairQOddExt u n =
        ∑ n ∈ Finset.Icc (0 : ℤ) (j : ℤ), cycloBilateralKernel j n * pairQOddExt u n := by
    refine Finset.sum_nbij' (fun n ↦ -n - 1) (fun n ↦ -n - 1) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      omega
    · intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      omega
    · intro n _
      ring
    · intro n _
      ring
    · intro n _
      rw [cycloBilateralKernel_neg_sub_one, pairQOddExt_neg_sub_one_bilateral, neg_mul_neg]
  rw [cycloBilateralSum, hU, Finset.sum_union hD, hneg,
    sum_Icc_zero_cycloBilateralKernel_mul_pairQOddExt, two_mul]

end AJConjecture
