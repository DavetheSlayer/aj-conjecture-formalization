import Mathlib
import AJConjecture.SkeinPtrTailBasic
import AJConjecture.SkeinThickCup
import AJConjecture.SkeinTraceCyclic

/-!
# Placements and thick cups intertwine the weights

The weight `μ^{⊗ n}` is a tensor power, so a placement `1 ⊗ A ⊗ 1` intertwines the weights when `A`
does (entrywise with `AJConjecture.skPlace_append_apply`; both sides vanish when the placement
does not fit). The thick cap and the thick cup intertwine the weights because each of their
entries pairs a `false` with a `true` (`μ(F) μ(T) = 1`); alternatively by induction with
`AJConjecture.capThick_succ` and `AJConjecture.skWeight_mul_capAt`. With these, every rectangular
matrix of the two-bundle calculus can be moved cyclically under the quantum trace
(`AJConjecture.qtr_mul_comm_of_weight`).
-/

namespace AJConjecture

/-- A placement of a matrix that intertwines the weights intertwines the weights. -/
theorem skWeight_mul_skPlace (n n' i : ℕ) {k l : ℕ} (A : SkMat k l)
    (hA : skWeight k * A = A * skWeight l) :
    skWeight n * skPlace n n' i A = skPlace n n' i A * skWeight n' := by
  by_cases h : i + k ≤ n ∧ n + l = n' + k
  · obtain ⟨r, rfl⟩ : ∃ r, n = i + k + r := ⟨n - (i + k), by omega⟩
    obtain rfl : n' = i + l + r := by omega
    ext a b
    obtain ⟨a₁₂, a₃, rfl⟩ := exists_append_eq a
    obtain ⟨a₁, a₂, rfl⟩ := exists_append_eq a₁₂
    obtain ⟨b₁₂, b₃, rfl⟩ := exists_append_eq b
    obtain ⟨b₁, b₂, rfl⟩ := exists_append_eq b₁₂
    have hA' := congrFun (congrFun hA a₂) b₂
    rw [skWeight, skWeight, Matrix.diagonal_mul, Matrix.mul_diagonal] at hA'
    rw [skWeight, skWeight, Matrix.diagonal_mul, Matrix.mul_diagonal, skPlace_append_apply]
    simp only [prod_skWeightEntry_append]
    by_cases hc : a₁ = b₁ ∧ a₃ = b₃
    · obtain ⟨rfl, rfl⟩ := hc
      rw [ite_eq_left ⟨rfl, rfl⟩]
      linear_combination ((∏ x, skWeightEntry (a₁ x)) * ∏ x, skWeightEntry (a₃ x)) * hA'
    · rw [ite_eq_right hc, mul_zero, zero_mul]
  · have h0 : skPlace n n' i A = 0 := by
      ext a b
      simp [skPlace, h]
    rw [h0, Matrix.mul_zero, Matrix.zero_mul]

/-- The thick cap intertwines the weights. -/
theorem skWeight_mul_capThick (k : ℕ) :
    skWeight (2 * k) * capThick k = capThick k * skWeight 0 := by
  induction k with
  | zero =>
    change skWeight 0 * capThick 0 = capThick 0 * skWeight 0
    rw [capThick_zero, Matrix.mul_one, Matrix.one_mul]
  | succ k ih =>
    rw [capThick_succ, ← Matrix.mul_assoc,
      skWeight_mul_skPlace (2 * (k + 1)) 2 1 (capThick k) ih, Matrix.mul_assoc,
      skWeight_mul_skCap, Matrix.mul_assoc]

end AJConjecture
