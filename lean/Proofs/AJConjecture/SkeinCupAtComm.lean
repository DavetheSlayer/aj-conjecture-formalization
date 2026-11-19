import Mathlib
import AJConjecture.SkeinCapAtComm
import AJConjecture.SkeinTranspose

/-!
# A cup commutes with generators and braids on other strands

The mirror images of the statements of `AJConjecture.capAt_mul_tlGenF_of_lt` and its companions:
transpose them, using that the generators are symmetric, that the transpose of a braid matrix
is the matrix of the reversed word, and `cup = -t² capᵀ`.
-/

namespace AJConjecture

/-- Mirror image of an intertwining relation for a cap: if `capAt n i * B = B' * capAt n i` then
`Bᵀ * cupAt n i = cupAt n i * B'ᵀ`. -/
private theorem transpose_mul_cupAt_of_capAt_mul_cupAtComm (n i : ℕ) (B : SkMat n n)
    (B' : SkMat (n + 2) (n + 2)) (h : capAt n i * B = B' * capAt n i) :
    B.transpose * cupAt n i = cupAt n i * B'.transpose := by
  rw [cupAt_eq_smul_transpose_capAt, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.transpose_mul,
    ← Matrix.transpose_mul, h]

/-- A generator on the left of a cup commutes with it. -/
theorem tlGenF_mul_cupAt_of_lt (n i j : ℕ) (h : j + 1 < i) :
    tlGenF n j * cupAt n i = cupAt n i * tlGenF (n + 2) j := by
  have key := transpose_mul_cupAt_of_capAt_mul_cupAtComm n i _ _ (capAt_mul_tlGenF_of_lt n i j h)
  rwa [tlGenF_transpose, tlGenF_transpose] at key

/-- A generator on the right of a cup commutes with it; its index is shifted by `2`. -/
theorem tlGenF_mul_cupAt_of_le (n i j : ℕ) (h : i ≤ j) :
    tlGenF n j * cupAt n i = cupAt n i * tlGenF (n + 2) (j + 2) := by
  have key := transpose_mul_cupAt_of_capAt_mul_cupAtComm n i _ _ (capAt_mul_tlGenF_of_le n i j h)
  rwa [tlGenF_transpose, tlGenF_transpose] at key

end AJConjecture
