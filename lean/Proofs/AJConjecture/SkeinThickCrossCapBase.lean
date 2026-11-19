import Mathlib
import AJConjecture.SkeinThickCrossTlBase
import AJConjecture.SkeinCapAtComm
import AJConjecture.SkeinCapSlideThin
import AJConjecture.SkeinProfileBasic
import AJConjecture.SkeinThickGenInv

/-!
# A cap slides through the crossing of a bundle with a single strand

The cap on the strands `j`, `j + 1` of a bundle that crosses a single strand: the letters of
`σ_{off+a+1} ⋯ σ_{off}` on the right of the cap commute with it (indices shifted by `2`,
`AJConjecture.capAt_mul_braidMatrix_of_le`), the two letters that cross the strands of the cap
are removed by `AJConjecture.crossingF_mul_crossingF_mul_capAt_succ` (respectively
`AJConjecture.crossingF_mul_crossingF_mul_capAt`), and the letters on the left commute with the
cap (`AJConjecture.capAt_mul_braidMatrix_of_lt`).
-/

namespace AJConjecture

/-- The matrix of a word that starts with the letter `g`. -/
private theorem braidMatrix_cons_thickCrossCapBase (m : ℕ) (g : ℕ × Bool) (w : BraidWord) :
    braidMatrix m (g :: w) = crossingF m g * braidMatrix m w := by
  simp only [braidMatrix, List.map_cons, List.prod_cons]

/-- A cap on a bundle slides through its crossing with the strand on its right. -/
theorem capAt_mul_braidMatrix_thickGen_right_one (n a off j : ℕ) (hn : off + a + 1 ≤ n)
    (hj : j ≤ a) :
    capAt n (off + j) * braidMatrix n (thickGen a 1 off true) =
      braidMatrix (n + 2) (thickGen (a + 2) 1 off true) * capAt n (off + 1 + j) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hj
  have h1 : thickGen (j + r) 1 off true =
      thickGen r 1 (off + j) true ++ thickGen j 1 off true := thickGen_add_left j r 1 off
  have h2 : thickGen (j + r + 2) 1 off true =
      thickGen r 1 (off + j + 2) true ++
        ((off + j + 1, true) :: (off + j, true) :: thickGen j 1 off true) := by
    rw [show j + r + 2 = j + (2 + r) from by omega, thickGen_add_left, thickGen_add_left,
      List.append_assoc]
    rfl
  have h4 : thickGen r 1 (off + j + 2) true =
      (thickGen r 1 (off + j) true).map fun g ↦ (g.1 + 2, g.2) :=
    thickCross_add_off r 1 (off + j) 2 true
  have e1 : capAt n (off + j) * braidMatrix n (thickGen r 1 (off + j) true) =
      braidMatrix (n + 2) (thickGen r 1 (off + j + 2) true) * capAt n (off + j) := by
    rw [h4]
    exact capAt_mul_braidMatrix_of_le n (off + j) _ fun g hg ↦
      (mem_thickGen_true hg).1
  have e2 : braidMatrix (n + 2) (thickGen j 1 off true) * capAt n (off + j + 1) =
      capAt n (off + j + 1) * braidMatrix n (thickGen j 1 off true) :=
    (capAt_mul_braidMatrix_of_lt n (off + j + 1) _ fun g hg ↦ by
      have := (mem_thickGen_true hg).2
      omega).symm
  have e3 := crossingF_mul_crossingF_mul_capAt_succ n (off + j) true (by omega)
  rw [h1, h2, braidMatrix_append, braidMatrix_append, braidMatrix_cons_thickCrossCapBase,
    braidMatrix_cons_thickCrossCapBase, show off + 1 + j = off + j + 1 from by omega,
    ← Matrix.mul_assoc, e1]
  simp only [Matrix.mul_assoc]
  rw [e2, ← e3]
  simp only [Matrix.mul_assoc]

/-- A cap on a bundle slides through its crossing with the strand on its left. -/
theorem capAt_mul_braidMatrix_thickGen_left_one (n b off j : ℕ) (hn : off + 1 + b ≤ n)
    (hj : j ≤ b) :
    capAt n (off + 1 + j) * braidMatrix n (thickGen 1 b off true) =
      braidMatrix (n + 2) (thickGen 1 (b + 2) off true) * capAt n (off + j) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hj
  have h4 : thickGen 1 r (off + j + 2) true =
      (thickGen 1 r (off + j) true).map fun g ↦ (g.1 + 2, g.2) :=
    thickCross_add_off 1 r (off + j) 2 true
  have h3 : thickGen 1 2 (off + j) true = [(off + j, true), (off + j + 1, true)] := rfl
  have e1 : capAt n (off + j) * braidMatrix n (thickGen 1 r (off + j) true) =
      braidMatrix (n + 2) (thickGen 1 r (off + j + 2) true) * capAt n (off + j) := by
    rw [h4]
    exact capAt_mul_braidMatrix_of_le n (off + j) _ fun g hg ↦
      (mem_thickGen_true hg).1
  have e2 : capAt n (off + j + 1) * braidMatrix n (thickGen 1 j off true) =
      braidMatrix (n + 2) (thickGen 1 j off true) * capAt n (off + j + 1) :=
    capAt_mul_braidMatrix_of_lt n (off + j + 1) _ fun g hg ↦ by
      have := (mem_thickGen_true hg).2
      omega
  have e3 := crossingF_mul_crossingF_mul_capAt n (off + j) true (by omega)
  rw [braidMatrix_thickGen_add_right, show j + r + 2 = j + (2 + r) from by omega,
    braidMatrix_thickGen_add_right, braidMatrix_thickGen_add_right, h3,
    braidMatrix_cons_thickCrossCapBase, braidMatrix_cons_thickCrossCapBase, braidMatrix_nil,
    Matrix.mul_one, show off + 1 + j = off + j + 1 from by omega, ← Matrix.mul_assoc, e2, ← e3]
  simp only [Matrix.mul_assoc]
  rw [e1]

end AJConjecture
