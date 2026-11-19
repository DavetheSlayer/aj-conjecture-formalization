import Mathlib
import AJConjecture.SkeinCupAtComm
import AJConjecture.SkeinJonesWenzl

/-!
# The Jones–Wenzl projector commutes with cups and caps outside its block

A projector whose block is on the left of a cap (same position on both sides) or on its right
(position shifted by `2`) commutes with it, and the same for cups. Induction on the size of the
projector with Wenzl's recursion and the far commutation of the generators
(`AJConjecture.capAt_mul_tlGenF_of_lt`, `AJConjecture.capAt_mul_tlGenF_of_le`,
`AJConjecture.tlGenF_mul_cupAt_of_lt`, `AJConjecture.tlGenF_mul_cupAt_of_le`). No hypothesis on the
ambient size is needed.
-/

namespace AJConjecture

/-- A matrix that intertwines the generators of two blocks intertwines their projectors. -/
theorem jwAt_mul_eq_mul_jwAt (n n' i i' : ℕ) (X : SkMat n n') :
    ∀ k : ℕ, (∀ l : ℕ, l + 2 ≤ k → tlGenF n (i + l) * X = X * tlGenF n' (i' + l)) →
      jwAt n i k * X = X * jwAt n' i' k
  | 0, _ => by rw [jwAt, jwAt, Matrix.one_mul, Matrix.mul_one]
  | 1, _ => by rw [jwAt, jwAt, Matrix.one_mul, Matrix.mul_one]
  | k + 2, h => by
    have ih := jwAt_mul_eq_mul_jwAt n n' i i' X (k + 1) fun l hl ↦ h l (by omega)
    have ih' : ∀ Y : SkMat n' n', jwAt n i (k + 1) * (X * Y) = X * (jwAt n' i' (k + 1) * Y) :=
      fun Y ↦ by rw [← Matrix.mul_assoc, ih, Matrix.mul_assoc]
    have he' : ∀ Y : SkMat n' n', tlGenF n (i + k) * (X * Y) = X * (tlGenF n' (i' + k) * Y) :=
      fun Y ↦ by rw [← Matrix.mul_assoc, h k le_rfl, Matrix.mul_assoc]
    rw [jwAt, jwAt]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
      ih, ih', he']

/-- A projector on the left of a cap commutes with it. -/
theorem jwAt_mul_capAt_of_le (n i k j : ℕ) (h : i + k ≤ j) :
    jwAt (n + 2) i k * capAt n j = capAt n j * jwAt n i k :=
  jwAt_mul_eq_mul_jwAt (n + 2) n i i (capAt n j) k fun l hl ↦
    (capAt_mul_tlGenF_of_lt n j (i + l) (by omega)).symm

/-- A projector on the right of a cap commutes with it; its position is shifted by `2`. -/
theorem jwAt_mul_capAt_of_ge (n i k j : ℕ) (h : j ≤ i) :
    jwAt (n + 2) (i + 2) k * capAt n j = capAt n j * jwAt n i k :=
  jwAt_mul_eq_mul_jwAt (n + 2) n (i + 2) i (capAt n j) k fun l _ ↦ by
    rw [capAt_mul_tlGenF_of_le n j (i + l) (by omega), Nat.add_right_comm i l 2]

/-- A projector on the left of a cup commutes with it. -/
theorem cupAt_mul_jwAt_of_le (n i k j : ℕ) (h : i + k ≤ j) :
    cupAt n j * jwAt (n + 2) i k = jwAt n i k * cupAt n j :=
  (jwAt_mul_eq_mul_jwAt n (n + 2) i i (cupAt n j) k fun l hl ↦
    tlGenF_mul_cupAt_of_lt n j (i + l) (by omega)).symm

/-- A projector on the right of a cup commutes with it; its position is shifted by `2`. -/
theorem cupAt_mul_jwAt_of_ge (n i k j : ℕ) (h : j ≤ i) :
    cupAt n j * jwAt (n + 2) (i + 2) k = jwAt n i k * cupAt n j :=
  (jwAt_mul_eq_mul_jwAt n (n + 2) i (i + 2) (cupAt n j) k fun l _ ↦ by
    rw [tlGenF_mul_cupAt_of_le n j (i + l) (by omega), Nat.add_right_comm i l 2]).symm

end AJConjecture
