import Mathlib
import AJConjecture.SkeinCapLegTransfer
import AJConjecture.SkeinThickCrossTl

/-!
# Braids inside a bundle slide through a thick crossing

A braid word on the strands of one of the two bundles slides through the crossing of the
bundles: letter by letter, with `σ_i^{±1} = t^{±1} + t^{∓1} e_i` and the naturality of the thick
crossing with respect to the generators (`AJConjecture.tlGenF_mul_braidMatrix_thickCross_fst`,
`AJConjecture.tlGenF_mul_braidMatrix_thickCross_snd`).
-/

namespace AJConjecture

/-- A crossing slides through a matrix through which the generator slides. -/
private theorem crossingF_mul_of_tlGenF_mul_thickCrossBraid (n i j : ℕ) (s : Bool) (X : SkMat n n)
    (h : tlGenF n i * X = X * tlGenF n j) : crossingF n (i, s) * X = X * crossingF n (j, s) := by
  cases s
  · rw [crossingF_neg, crossingF_neg, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, h, Matrix.one_mul, Matrix.mul_one]
  · rw [crossingF_pos, crossingF_pos, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, h, Matrix.one_mul, Matrix.mul_one]

/-- A braid word inside the first bundle slides through a thick crossing. -/
theorem braidMatrix_mul_thickCross_fst (n a b off : ℕ) (s : Bool) (w : BraidWord)
    (hn : off + a + b ≤ n) (hw : ∀ g ∈ w, g.1 + 1 < a) :
    braidMatrix n (w.map fun g ↦ (g.1 + off, g.2)) * braidMatrix n (thickCross a b off s) =
      braidMatrix n (thickCross a b off s) *
        braidMatrix n (w.map fun g ↦ (g.1 + (off + b), g.2)) := by
  induction w with
  | nil => rw [List.map_nil, List.map_nil, braidMatrix_nil, Matrix.one_mul, Matrix.mul_one]
  | cons g w ih =>
    have hg : crossingF n (g.1 + off, g.2) * braidMatrix n (thickCross a b off s) =
        braidMatrix n (thickCross a b off s) * crossingF n (g.1 + (off + b), g.2) := by
      apply crossingF_mul_of_tlGenF_mul_thickCrossBraid
      rw [show g.1 + off = off + g.1 from by omega,
        show g.1 + (off + b) = off + b + g.1 from by omega]
      exact tlGenF_mul_braidMatrix_thickCross_fst n a b off g.1 s hn (hw g List.mem_cons_self)
    rw [List.map_cons, List.map_cons, braidMatrix_cons,
      braidMatrix_cons, Matrix.mul_assoc,
      ih fun g' hg' ↦ hw g' (List.mem_cons_of_mem _ hg'), ← Matrix.mul_assoc, hg,
      Matrix.mul_assoc]

/-- A braid word inside the second bundle slides through a thick crossing. -/
theorem braidMatrix_mul_thickCross_snd (n a b off : ℕ) (s : Bool) (w : BraidWord)
    (hn : off + a + b ≤ n) (hw : ∀ g ∈ w, g.1 + 1 < b) :
    braidMatrix n (w.map fun g ↦ (g.1 + (off + a), g.2)) * braidMatrix n (thickCross a b off s) =
      braidMatrix n (thickCross a b off s) * braidMatrix n (w.map fun g ↦ (g.1 + off, g.2)) := by
  induction w with
  | nil => rw [List.map_nil, List.map_nil, braidMatrix_nil, Matrix.one_mul, Matrix.mul_one]
  | cons g w ih =>
    have hg : crossingF n (g.1 + (off + a), g.2) * braidMatrix n (thickCross a b off s) =
        braidMatrix n (thickCross a b off s) * crossingF n (g.1 + off, g.2) := by
      apply crossingF_mul_of_tlGenF_mul_thickCrossBraid
      rw [show g.1 + (off + a) = off + a + g.1 from by omega,
        show g.1 + off = off + g.1 from by omega]
      exact tlGenF_mul_braidMatrix_thickCross_snd n a b off g.1 s hn (hw g List.mem_cons_self)
    rw [List.map_cons, List.map_cons, braidMatrix_cons,
      braidMatrix_cons, Matrix.mul_assoc,
      ih fun g' hg' ↦ hw g' (List.mem_cons_of_mem _ hg'), ← Matrix.mul_assoc, hg,
      Matrix.mul_assoc]

end AJConjecture
