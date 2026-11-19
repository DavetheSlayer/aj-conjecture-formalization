import Mathlib
import AJConjecture.SkeinThickGenInv
import AJConjecture.SkeinTranspose

/-!
# The mirror image of a thick crossing

The reversed word of the crossing of `a` strands with `b` strands is, as a matrix, the crossing
of `b` strands with `a` strands (the two words differ by far commutations). Induction on `b`:
`(thickGen (1 + b) a off).reverse = (thickGen 1 a off).reverse ++ (thickGen b a (off + 1)).reverse`
by `AJConjecture.thickGen_add_left`, the reversed word of `thickGen 1 a off true` is the word
`thickGen a 1 off true`, and `AJConjecture.braidMatrix_thickGen_add_right` reassembles
`thickGen a (1 + b) off true`. Consequently the transpose of the matrix of a thick crossing is
the matrix of the thick crossing of the bundles in the other order, for both signs.
-/

namespace AJConjecture

/-- The reversed word of a strand crossing a bundle is the word of the bundle crossing the
strand. -/
private theorem thickGen_one_reverse_thickGenReverse (a off : ℕ) :
    (thickGen 1 a off true).reverse = thickGen a 1 off true := by
  simp only [thickGen, ite_true, List.range_one, List.reverse_singleton, List.flatMap_singleton,
    List.map_singleton, add_zero, ← List.map_eq_flatMap, List.map_reverse]

/-- The reversed word of a positive thick crossing is the thick crossing of the bundles in the
other order. -/
theorem braidMatrix_thickGen_reverse (n a b off : ℕ) :
    braidMatrix n (thickGen a b off true).reverse = braidMatrix n (thickGen b a off true) := by
  induction a generalizing off with
  | zero =>
    have h0 : thickGen b 0 off true = [] := List.flatMap_eq_nil_iff.mpr fun _ _ ↦ rfl
    rw [h0]
    rfl
  | succ a ih =>
    rw [add_comm a 1, thickGen_add_left 1 a b off, List.reverse_append, braidMatrix_append, ih,
      thickGen_one_reverse_thickGenReverse, braidMatrix_thickGen_add_right]

/-- The transpose of a thick crossing is the thick crossing of the bundles in the other order. -/
theorem braidMatrix_thickCross_transpose (n a b off : ℕ) (s : Bool) :
    (braidMatrix n (thickCross a b off s)).transpose = braidMatrix n (thickCross b a off s) := by
  cases s
  · have hP : (braidMatrix n (thickGen b a off true)).transpose =
        braidMatrix n (thickGen a b off true) := by
      rw [braidMatrix_transpose, braidMatrix_thickGen_reverse]
    have h1 : (braidMatrix n (thickGen b a off false)).transpose *
        braidMatrix n (thickGen a b off true) = 1 := by
      rw [← hP, ← Matrix.transpose_mul, braidMatrix_thickGen_mul_inv, Matrix.transpose_one]
    change (braidMatrix n (thickGen b a off false)).transpose =
      braidMatrix n (thickGen a b off false)
    calc (braidMatrix n (thickGen b a off false)).transpose
        = (braidMatrix n (thickGen b a off false)).transpose *
            (braidMatrix n (thickGen a b off true) * braidMatrix n (thickGen a b off false)) := by
          rw [braidMatrix_thickGen_mul_inv, Matrix.mul_one]
      _ = braidMatrix n (thickGen a b off false) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  · change (braidMatrix n (thickGen a b off true)).transpose =
      braidMatrix n (thickGen b a off true)
    rw [braidMatrix_transpose, braidMatrix_thickGen_reverse]

end AJConjecture
