import Mathlib
import AJConjecture.SkeinBandClasp
import AJConjecture.SkeinPlaceBasic

/-!
# The rotation is linear

`bandRot c` is a product with fixed matrices on both sides of a placement, and the placement is
linear (`AJConjecture.skPlace_add`, `AJConjecture.skPlace_smul`).
-/

namespace AJConjecture

/-- The rotation is additive. -/
theorem bandRot_add (c : ℕ) (A B : SkMat (2 * c) (2 * c)) :
    bandRot c (A + B) = bandRot c A + bandRot c B := by
  simp only [bandRot, skPlace_add, Matrix.mul_add, Matrix.add_mul]

/-- The rotation commutes with scalars. -/
theorem bandRot_smul (c : ℕ) (x : RatFunc ℚ) (A : SkMat (2 * c) (2 * c)) :
    bandRot c (x • A) = x • bandRot c A := by
  simp only [bandRot, skPlace_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- The rotation commutes with finite sums. -/
theorem bandRot_sum (c : ℕ) {ι : Type*} (s : Finset ι) (A : ι → SkMat (2 * c) (2 * c)) :
    bandRot c (∑ i ∈ s, A i) = ∑ i ∈ s, bandRot c (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : bandRot c (0 : SkMat (2 * c) (2 * c)) = 0 := by
      have h := bandRot_smul c 0 (0 : SkMat (2 * c) (2 * c))
      rwa [zero_smul, zero_smul] at h
    rw [Finset.sum_empty, Finset.sum_empty, h0]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bandRot_add, ih]

end AJConjecture
