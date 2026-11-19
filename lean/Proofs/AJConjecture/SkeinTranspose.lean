import Mathlib
import AJConjecture.SkeinPlaceMul
import AJConjecture.SkeinBraidMatrixBasic
import AJConjecture.SkeinPlaceBasic

/-!
# Transposition: the mirror symmetry of the calculus

The matrix of `e_i` is symmetric (`cupCapEntry a₀ a₁ b₀ b₁ = cupCapEntry b₀ b₁ a₀ a₁`), hence so
are the crossing matrices, and the transpose of the matrix of a braid word is the matrix of the
reversed word. The cup is `-t²` times the transpose of the cap (`cup(a, b) = -t² cap(a, b)`), and
transposition commutes with the placement. Every statement about caps therefore has a mirror
statement about cups, read from the top of the diagram to the bottom.
-/

namespace AJConjecture

/-- Transposition commutes with the placement (also when the placement does not fit). -/
theorem skPlace_transpose (n n' i : ℕ) {k l : ℕ} (A : SkMat k l) :
    (skPlace n n' i A).transpose = skPlace n' n i A.transpose := by
  by_cases hfit : i + k ≤ n ∧ n + l = n' + k
  · obtain ⟨r, rfl⟩ : ∃ r, n = i + k + r := ⟨n - (i + k), by omega⟩
    obtain rfl : n' = i + l + r := by omega
    ext a b
    obtain ⟨a₁, a₂, a₃, rfl⟩ := exists_append i l r a
    obtain ⟨b₁, b₂, b₃, rfl⟩ := exists_append i k r b
    rw [Matrix.transpose_apply, skPlace_append_apply, skPlace_append_apply,
      Matrix.transpose_apply]
    exact if_congr ⟨fun h ↦ ⟨h.1.symm, h.2.symm⟩, fun h ↦ ⟨h.1.symm, h.2.symm⟩⟩ rfl rfl
  · have hfit' : ¬(i + l ≤ n' ∧ n' + k = n + l) := by omega
    ext a b
    simp only [Matrix.transpose_apply, skPlace, Matrix.of_apply]
    rw [dite_eq_right hfit, dite_eq_right hfit']

/-- The entries of the generator on two factors are symmetric. -/
private theorem cupCapEntry_symm_transpose (a₀ a₁ b₀ b₁ : Bool) :
    cupCapEntry a₀ a₁ b₀ b₁ = cupCapEntry b₀ b₁ a₀ a₁ := by
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> rfl

/-- The matrix of `e_i` is symmetric. -/
theorem tlGenF_transpose (m i : ℕ) : (tlGenF m i).transpose = tlGenF m i := by
  ext a b
  simp only [Matrix.transpose_apply, tlGenF, Matrix.map_apply, tlGen, Matrix.of_apply]
  congr 1
  by_cases hm : i + 1 < m
  · rw [dite_eq_left hm, dite_eq_left hm]
    exact if_congr ⟨fun h x h₀ h₁ ↦ (h x h₀ h₁).symm, fun h x h₀ h₁ ↦ (h x h₀ h₁).symm⟩
      (cupCapEntry_symm_transpose _ _ _ _) rfl
  · rw [dite_eq_right hm, dite_eq_right hm]

/-- The crossing matrices are symmetric. -/
theorem crossingF_transpose (m : ℕ) (g : ℕ × Bool) :
    (crossingF m g).transpose = crossingF m g := by
  obtain ⟨i, s⟩ := g
  cases s
  · rw [crossingF_neg, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
      Matrix.transpose_one, tlGenF_transpose]
  · rw [crossingF_pos, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
      Matrix.transpose_one, tlGenF_transpose]

/-- The transpose of the matrix of a braid word is the matrix of the reversed word. -/
theorem braidMatrix_transpose (m : ℕ) (w : BraidWord) :
    (braidMatrix m w).transpose = braidMatrix m w.reverse := by
  induction w with
  | nil => rw [List.reverse_nil, braidMatrix_nil, Matrix.transpose_one]
  | cons g w ih =>
    have hg : braidMatrix m [g] = crossingF m g := by
      rw [braidMatrix, List.map_singleton, List.prod_singleton]
    have hcons : braidMatrix m (g :: w) = crossingF m g * braidMatrix m w := by
      rw [braidMatrix, List.map_cons, List.prod_cons]
      rfl
    rw [hcons, Matrix.transpose_mul, ih, crossingF_transpose, List.reverse_cons,
      braidMatrix_append, hg]

/-- The two-strand cup is `-t²` times the transpose of the two-strand cap. -/
private theorem skCup_eq_smul_transpose_skCap_transpose :
    skCup = (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ)) • skCap.transpose := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hentry : ∀ x y : Bool,
      cupEntry x y = -(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) * capEntry x y := by
    intro x y
    cases x <;> cases y <;> simp [cupEntry, capEntry, hX]
  ext a b
  rw [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
  exact hentry (b 0) (b 1)

/-- The cup is `-t²` times the transpose of the cap. -/
theorem cupAt_eq_smul_transpose_capAt (n i : ℕ) :
    cupAt n i = (-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ)) • (capAt n i).transpose := by
  rw [cupAt, capAt, skPlace_transpose, ← skPlace_smul, ← skCup_eq_smul_transpose_skCap_transpose]

end AJConjecture
