import Mathlib
import AJConjecture.SkeinCapLegTransfer
import AJConjecture.SkeinThickCrossTlBase
import AJConjecture.SkeinCrossingRelations
import AJConjecture.SkeinThickCableBasic

/-!
# Inverse and splitting of thick crossings

The word `thickGen a b off false` is the reversed inverse of `thickGen a b off true`, so their
matrices are inverse to each other (induction on the word with `σ_i σ_i⁻¹ = 1`). Splitting the
second bundle of a thick crossing is an identity of matrices, not of words: it uses far
commutation.
-/

namespace AJConjecture

/-- A letter followed by its inverse is the identity. -/
private theorem crossingF_mul_not_thickGenInv (n : ℕ) (g : ℕ × Bool) :
    crossingF n g * crossingF n (g.1, !g.2) = 1 := by
  obtain ⟨i, s⟩ := g
  cases s
  · exact crossingF_inv_mul n i
  · exact crossingF_mul_inv n i

/-- A word followed by its reversed inverse word is the identity. -/
private theorem braidMatrix_mul_reverse_map_not_thickGenInv (n : ℕ) (w : BraidWord) :
    braidMatrix n w * braidMatrix n (w.reverse.map fun g ↦ (g.1, !g.2)) = 1 := by
  induction w with
  | nil => rw [List.reverse_nil, List.map_nil, braidMatrix_nil, Matrix.mul_one]
  | cons g w ih =>
    rw [List.reverse_cons, List.map_append, braidMatrix_append, braidMatrix_cons,
      Matrix.mul_assoc, ← Matrix.mul_assoc (braidMatrix n w), ih, Matrix.one_mul,
      List.map_singleton, braidMatrix_cons, braidMatrix_nil, Matrix.mul_one]
    exact crossingF_mul_not_thickGenInv n g

/-- The negative thick word is the reversed inverse of the positive thick word. -/
private theorem thickGen_false_eq_reverse_map_thickGenInv (a b off : ℕ) :
    thickGen a b off false = (thickGen a b off true).reverse.map fun g ↦ (g.1, !g.2) := by
  simp only [thickGen, Bool.false_eq_true, ite_false, ite_true, List.reverse_flatMap,
    List.map_flatMap, List.reverse_reverse, Function.comp_def, ← List.map_reverse, List.map_map,
    Bool.not_true]

/-- A thick crossing followed by the inverse word is the identity. -/
theorem braidMatrix_thickGen_mul_inv (n a b off : ℕ) :
    braidMatrix n (thickGen a b off true) * braidMatrix n (thickGen a b off false) = 1 := by
  rw [thickGen_false_eq_reverse_map_thickGenInv]
  exact braidMatrix_mul_reverse_map_not_thickGenInv n _

/-- The inverse word followed by the thick crossing is the identity. -/
theorem braidMatrix_thickGen_inv_mul (n a b off : ℕ) :
    braidMatrix n (thickGen a b off false) * braidMatrix n (thickGen a b off true) = 1 := by
  exact mul_eq_one_comm.mp (braidMatrix_thickGen_mul_inv n a b off)

/-- A letter commutes with a word all of whose letters are far to its right. -/
theorem crossingF_commute_braidMatrix (n : ℕ) (g : ℕ × Bool) (v : BraidWord)
    (h : ∀ g' ∈ v, g.1 + 1 < g'.1) : Commute (crossingF n g) (braidMatrix n v) := by
  induction v with
  | nil =>
    rw [braidMatrix_nil]
    exact Commute.one_right _
  | cons g' v ih =>
    rw [braidMatrix_cons]
    exact (crossingF_commute n g.1 g'.1 g.2 g'.2 (h g' List.mem_cons_self)).mul_right
      (ih fun g₁ hg₁ ↦ h g₁ (List.mem_cons_of_mem _ hg₁))

/-- Two words commute when every letter of the second is far to the right of every letter of
the first. -/
theorem braidMatrix_commute_of_far (n : ℕ) (u v : BraidWord)
    (h : ∀ g ∈ u, ∀ g' ∈ v, g.1 + 1 < g'.1) :
    Commute (braidMatrix n u) (braidMatrix n v) := by
  induction u with
  | nil =>
    rw [braidMatrix_nil]
    exact Commute.one_left _
  | cons g u ih =>
    rw [braidMatrix_cons]
    exact (crossingF_commute_braidMatrix n g v (h g List.mem_cons_self)).mul_left
      (ih fun g₁ hg₁ ↦ h g₁ (List.mem_cons_of_mem _ hg₁))

/-- Splitting the second bundle: the first bundle crosses its first `b₁` strands, then the
others. -/
theorem braidMatrix_thickGen_add_right (n a b₁ b₂ off : ℕ) :
    braidMatrix n (thickGen a (b₁ + b₂) off true) =
      braidMatrix n (thickGen a b₁ off true) * braidMatrix n (thickGen a b₂ (off + b₁) true) := by
  induction a with
  | zero =>
    have h0 : ∀ b off' : ℕ, thickGen 0 b off' true = [] := fun _ _ ↦ rfl
    rw [h0, h0, h0, braidMatrix_nil, Matrix.mul_one]
  | succ a ih =>
    have hcomm : Commute (braidMatrix n (thickGen 1 b₂ (off + a + b₁) true))
        (braidMatrix n (thickGen a b₁ off true)) :=
      (braidMatrix_commute_of_far n _ _ fun g hg g' hg' ↦ by
        have h1 := mem_thickGen_true hg
        have h2 := mem_thickGen_true hg'
        omega).symm
    rw [thickGen_add_left a 1 (b₁ + b₂) off, thickGen_add_left a 1 b₁ off,
      thickGen_add_left a 1 b₂ (off + b₁), braidMatrix_append, braidMatrix_append,
      braidMatrix_append, ih, thickGen_one_add, braidMatrix_append,
      add_right_comm off b₁ a]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (braidMatrix n (thickGen 1 b₂ (off + a + b₁) true)), hcomm.eq,
      Matrix.mul_assoc]

end AJConjecture
