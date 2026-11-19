import Mathlib
import AJConjecture.SkeinJonesWenzl
import AJConjecture.SkeinTraceCyclic
import AJConjecture.SkeinTranspose

/-!
# The Jones–Wenzl projector is symmetric and commutes with the weight

Both properties hold for `1` and for the generators `e_j` (`AJConjecture.skWeight_mul_tlGenF`,
`AJConjecture.tlGenF_transpose`) and are preserved by Wenzl's recursion, whose new term
`f e f` is a palindrome. Induction on the size of the projector.
-/

namespace AJConjecture

/-- The Jones–Wenzl projector commutes with the weight of the quantum trace. -/
theorem skWeight_mul_jwAt (n i k : ℕ) : skWeight n * jwAt n i k = jwAt n i k * skWeight n := by
  induction k using Nat.twoStepInduction with
  | zero => rw [jwAt, Matrix.mul_one, Matrix.one_mul]
  | one => rw [jwAt, Matrix.mul_one, Matrix.one_mul]
  | more k _ ih =>
    rw [jwAt, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, ih]
    congr 2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ih, Matrix.mul_assoc (jwAt n i (k + 1)),
      skWeight_mul_tlGenF, Matrix.mul_assoc, Matrix.mul_assoc, ih]
    simp only [Matrix.mul_assoc]

/-- The matrix of the Jones–Wenzl projector is symmetric. -/
theorem jwAt_transpose (n i k : ℕ) : (jwAt n i k).transpose = jwAt n i k := by
  induction k using Nat.twoStepInduction with
  | zero => rw [jwAt, Matrix.transpose_one]
  | one => rw [jwAt, Matrix.transpose_one]
  | more k _ ih =>
    rw [jwAt, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul,
      Matrix.transpose_mul, ih, tlGenF_transpose, Matrix.mul_assoc]

end AJConjecture
