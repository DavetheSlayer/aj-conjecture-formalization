import Mathlib
import AJConjecture.QAlgOpApplyFieldOreMul
import AJConjecture.QAlgOreCommonMultiple
import AJConjecture.QAlgReflectAnnihilator

/-!
# From one tail to both tails

An even sequence annihilated on its positive tail by a nonzero operator is annihilated outside
a finite set of colours by a nonzero operator: a common left multiple of the operator and of
its reflection.
-/

open Polynomial

namespace AJConjecture

/-- An even sequence with an annihilator of its positive tail has an annihilator of all colours
of large absolute value. -/
theorem exists_annihilator_outside_finite_of_even {f : ℤ → RatFunc ℚ}
    (hf : ∀ n : ℤ, f (-n) = f n) {G : RecOp} (hG : G ≠ 0) {n₀ : ℤ}
    (h : ∀ n : ℤ, n₀ ≤ n → opApplyField G f n = 0) :
    ∃ Q : RecOp, Q ≠ 0 ∧ ∃ N : ℤ, ∀ n : ℤ, N ≤ |n| → opApplyField Q f n = 0 := by
  obtain ⟨G', hG', h'⟩ := exists_annihilator_neg_tail_of_even hf hG h
  obtain ⟨S, T, hS, hT, hST⟩ := exists_oreMul_eq_oreMul coeffShift_injective hG hG'
  refine ⟨oreMul coeffShift S G, oreMul_ne_zero coeffShift_injective hS hG,
    |n₀| + G.natDegree + T.natDegree, fun n hn ↦ ?_⟩
  rcases le_or_gt 0 n with hpos | hneg
  · rw [opApplyField_oreMul, opApplyField_eq_sum_range]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [h (n + i) (by rw [abs_of_nonneg hpos] at hn; have := le_abs_self n₀; omega), mul_zero]
  · rw [hST, opApplyField_oreMul, opApplyField_eq_sum_range]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    rw [h' (n + i) (by rw [abs_of_neg hneg] at hn; have := le_abs_self n₀; omega), mul_zero]

end AJConjecture
