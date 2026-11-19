import Mathlib
import AJConjecture.SkeinThickCrossCap
import AJConjecture.SkeinThickGenReverse

/-!
# Naturality of a thick crossing with respect to cups

The mirror images of `AJConjecture.capAt_mul_braidMatrix_thickCross_fst` and
`AJConjecture.capAt_mul_braidMatrix_thickCross_snd`: transpose the statement for a cap on the
second (respectively first) bundle of the crossing of the bundles in the other order, with
`AJConjecture.braidMatrix_thickCross_transpose` and `cup = -t² capᵀ`.
-/

namespace AJConjecture

/-- A cup on the first bundle slides through a thick crossing. -/
theorem braidMatrix_thickCross_mul_cupAt_fst (n a b off j : ℕ) (s : Bool)
    (hn : off + a + b ≤ n) (hj : j ≤ a) :
    braidMatrix n (thickCross a b off s) * cupAt n (off + b + j) =
      cupAt n (off + j) * braidMatrix (n + 2) (thickCross (a + 2) b off s) := by
  rw [cupAt_eq_smul_transpose_capAt, cupAt_eq_smul_transpose_capAt, Matrix.mul_smul,
    Matrix.smul_mul, ← braidMatrix_thickCross_transpose n b a off s,
    ← braidMatrix_thickCross_transpose (n + 2) b (a + 2) off s, ← Matrix.transpose_mul,
    ← Matrix.transpose_mul, capAt_mul_braidMatrix_thickCross_snd n b a off j s (by omega) hj]

/-- A cup on the second bundle slides through a thick crossing. -/
theorem braidMatrix_thickCross_mul_cupAt_snd (n a b off j : ℕ) (s : Bool)
    (hn : off + a + b ≤ n) (hj : j ≤ b) :
    braidMatrix n (thickCross a b off s) * cupAt n (off + j) =
      cupAt n (off + a + j) * braidMatrix (n + 2) (thickCross a (b + 2) off s) := by
  rw [cupAt_eq_smul_transpose_capAt, cupAt_eq_smul_transpose_capAt, Matrix.mul_smul,
    Matrix.smul_mul, ← braidMatrix_thickCross_transpose n b a off s,
    ← braidMatrix_thickCross_transpose (n + 2) (b + 2) a off s, ← Matrix.transpose_mul,
    ← Matrix.transpose_mul, capAt_mul_braidMatrix_thickCross_fst n b a off j s (by omega) hj]

end AJConjecture
