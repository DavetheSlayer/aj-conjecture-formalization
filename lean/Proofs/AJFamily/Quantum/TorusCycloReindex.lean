import Mathlib
import AJConjecture.QAlgCycloKernelShift
import AJFamily.Quantum.TorusOddColorRec

/-!
# Re-indexing the bilateral transform

The bilateral transform of a first-order operator applied to `φ`, against the odd colours of
`T(2, a)`, is `-q` times a transform against the forcing term `h_a`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- Shifting the summation index of a sum over an integer interval when the summand vanishes
at the lower end and just above the upper end. -/
private theorem sum_Icc_int_shift_of_ends_eq_zero_torus (F : ℤ → RatFunc ℚ) (a b : ℤ)
    (ha : F a = 0) (hb : F (b + 1) = 0) :
    ∑ n ∈ Finset.Icc a b, F (n + 1) = ∑ n ∈ Finset.Icc a b, F n := by
  have h1 : ∑ n ∈ Finset.Icc a b, F (n + 1) = ∑ m ∈ Finset.Icc (a + 1) (b + 1), F m := by
    refine Finset.sum_nbij' (fun n ↦ n + 1) (fun m ↦ m - 1) ?_ ?_ ?_ ?_ ?_
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
      rfl
  have h2 : ∑ m ∈ Finset.Icc (a + 1) b, F m = ∑ m ∈ Finset.Icc (a + 1) (b + 1), F m := by
    refine Finset.sum_subset ?_ ?_
    · intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      omega
    · intro n hn hn'
      rw [Finset.mem_Icc] at hn hn'
      obtain rfl : n = b + 1 := by omega
      exact hb
  have h3 : ∑ m ∈ Finset.Icc (a + 1) b, F m = ∑ m ∈ Finset.Icc a b, F m := by
    refine Finset.sum_subset ?_ ?_
    · intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      omega
    · intro n hn hn'
      rw [Finset.mem_Icc] at hn hn'
      obtain rfl : n = a := by omega
      exact ha
  rw [h1, ← h2, h3]

/-- The term of the forcing sum of `T(2, a)` splits into a shifted term and a homogeneous
term. -/
private theorem cycloBilateralKernel_mul_torusForcing_split (a : ℕ) (φ : ℤ → RatFunc ℚ)
    (j : ℕ) (n : ℤ) :
    -qParam * (cycloBilateralKernel j n *
        ((qParam ^ n - qParam ^ j) * φ (n + 1) * torusForcing a n)) =
      (1 - qParam * qParam ^ j * qParam ^ (n + 1)) * cycloBilateralKernel j (n + 1) *
          φ (n + 1) * torusOddColorInt a (n + 1) +
        cycloBilateralKernel j n *
          (qParam ^ (1 - 4 * (a : ℤ)) * (qParam ^ n - qParam ^ j) *
            qParam ^ (-(4 * (a : ℤ) * n)) * φ (n + 1) * torusOddColorInt a n) := by
  have hq := qParam_ne_zero
  have hK := cycloBilateralKernel_succ j n
  have hF : torusForcing a n =
      torusOddColorInt a (n + 1) -
        qParam ^ (-(4 * (a : ℤ) * (n + 1))) * torusOddColorInt a n := by
    rw [torusOddColorInt_succ a n]
    ring
  have hpow : qParam ^ (-(4 * (a : ℤ) * (n + 1))) =
      qParam ^ (-(4 * (a : ℤ))) * qParam ^ (-(4 * (a : ℤ) * n)) := by
    rw [← zpow_add₀ hq]
    congr 1
    ring
  have h1 : qParam ^ (1 - 4 * (a : ℤ)) = qParam * qParam ^ (-(4 * (a : ℤ))) := by
    rw [← zpow_one_add₀ hq]
    ring_nf
  rw [hF, hpow, h1, zpow_add_one₀ hq]
  linear_combination (-(φ (n + 1) * torusOddColorInt a (n + 1))) * hK

theorem cycloBilateralSum_reindex_torus (a : ℕ) (φ : ℤ → RatFunc ℚ) (j : ℕ) :
    cycloBilateralSum
        (fun n ↦ ((1 - qParam * qParam ^ j * qParam ^ n) * φ n +
          qParam ^ (1 - 4 * (a : ℤ)) * (qParam ^ n - qParam ^ j) * qParam ^ (-(4 * (a : ℤ) * n)) *
            φ (n + 1)) * torusOddColorInt a n) j =
      -qParam * cycloBilateralSum
        (fun n ↦ (qParam ^ n - qParam ^ j) * φ (n + 1) * torusForcing a n) j := by
  have hq := qParam_ne_zero
  have ha : (1 - qParam * qParam ^ j * qParam ^ (-((j : ℤ) + 1))) *
      cycloBilateralKernel j (-((j : ℤ) + 1)) * φ (-((j : ℤ) + 1)) *
        torusOddColorInt a (-((j : ℤ) + 1)) = 0 := by
    have h0 : 1 - qParam * qParam ^ j * qParam ^ (-((j : ℤ) + 1)) = 0 := by
      rw [zpow_neg, zpow_add_one₀ hq, zpow_natCast, mul_comm qParam]
      exact sub_eq_zero.mpr (mul_inv_cancel₀ (mul_ne_zero (pow_ne_zero j hq) hq)).symm
    rw [h0, zero_mul, zero_mul, zero_mul]
  have hb : (1 - qParam * qParam ^ j * qParam ^ ((j : ℤ) + 1)) *
      cycloBilateralKernel j ((j : ℤ) + 1) * φ ((j : ℤ) + 1) *
        torusOddColorInt a ((j : ℤ) + 1) = 0 := by
    rw [cycloBilateralKernel, ite_eq_right (by omega), mul_zero, zero_mul, zero_mul]
  have hshift := sum_Icc_int_shift_of_ends_eq_zero_torus
    (fun n ↦ (1 - qParam * qParam ^ j * qParam ^ n) * cycloBilateralKernel j n * φ n *
      torusOddColorInt a n) (-((j : ℤ) + 1)) j ha hb
  simp only [cycloBilateralSum]
  rw [Finset.mul_sum, Finset.sum_congr rfl fun n _ ↦
    cycloBilateralKernel_mul_torusForcing_split a φ j n, Finset.sum_add_distrib, hshift,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  ring

end AJConjecture
