import Mathlib
import AJConjecture.QAlgCycloKernelAntisymm
import AJFamily.Quantum.TorusOddColorInt

/-!
# Bilateral form of the cyclotomic coefficients

Twice the cyclotomic coefficient `D_j` of `T(2, a)` is the bilateral transform of the extended odd
colours.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- Weyl oddness of the extended odd colours of `T(2, a)`: `u_(-n-1) = -u_n`. -/
private theorem torusOddColorInt_neg_sub_one_bilateral (a : ℕ) (n : ℤ) :
    torusOddColorInt a (-n - 1) = -torusOddColorInt a n := by
  unfold torusOddColorInt
  rcases le_or_gt 0 n with hn | hn
  · rw [ite_eq_left hn, ite_eq_right (by omega : ¬(0 : ℤ) ≤ -n - 1),
      show (-(-n - 1) - 1) = n by ring]
  · rw [ite_eq_right (by omega : ¬(0 : ℤ) ≤ n), ite_eq_left (by omega : (0 : ℤ) ≤ -n - 1),
      neg_neg]

/-- The half of the bilateral sum over `0 ≤ n ≤ j` is the cyclotomic coefficient of
`T(2, a)`. -/
private theorem sum_Icc_zero_cycloBilateralKernel_mul_torusOddColorInt (a j : ℕ) :
    ∑ n ∈ Finset.Icc (0 : ℤ) (j : ℤ), cycloBilateralKernel j n * torusOddColorInt a n =
      torusCyclotomicCoeff a j := by
  rw [torusCyclotomicCoeff, Finset.mul_sum]
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
    rw [cycloBilateralKernel, ite_eq_left (by omega), torusOddColorInt,
      ite_eq_left (by omega), Int.toNat_natCast, show ((j : ℤ) - (m : ℤ)).toNat = j - m by omega,
      show ((j : ℤ) + (m : ℤ) + 1).toNat = j + m + 1 by omega, hE, zpow_natCast, zpow_natCast]
    ring

/-- Twice the cyclotomic coefficient of `T(2, a)` is the bilateral transform of its extended
odd colours. -/
theorem two_mul_torusCyclotomicCoeff (a : ℕ) (j : ℕ) :
    2 * torusCyclotomicCoeff a j = cycloBilateralSum (torusOddColorInt a) j := by
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
      cycloBilateralKernel j n * torusOddColorInt a n =
        ∑ n ∈ Finset.Icc (0 : ℤ) (j : ℤ), cycloBilateralKernel j n * torusOddColorInt a n := by
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
      rw [cycloBilateralKernel_neg_sub_one, torusOddColorInt_neg_sub_one_bilateral, neg_mul_neg]
  rw [cycloBilateralSum, hU, Finset.sum_union hD, hneg,
    sum_Icc_zero_cycloBilateralKernel_mul_torusOddColorInt, two_mul]

end AJConjecture
