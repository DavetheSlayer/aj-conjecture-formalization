import Mathlib
import AJConjecture.SkeinLongKnotTl

/-!
# The long knot commutes with the Jones–Wenzl projectors

The projector is built from `1` and the generators by Wenzl's recursion, and the long knot
commutes with the generators (`AJConjecture.longKnotOp_commute_tlGenF`). Induction on the size
of the projector.
-/

namespace AJConjecture

/-- The long knot commutes with the Jones–Wenzl projector on any block of its bundle. -/
theorem longKnotOp_commute_jwAt (K : BraidKnot) (k i j : ℕ) :
    Commute (longKnotOp K k) (jwAt k i j) := by
  induction j using Nat.twoStepInduction with
  | zero => rw [jwAt]; exact Commute.one_right _
  | one => rw [jwAt]; exact Commute.one_right _
  | more j _ ih =>
    rw [jwAt]
    exact ih.add_right (((ih.mul_right (longKnotOp_commute_tlGenF K k (i + j))).mul_right
      ih).smul_right _)

end AJConjecture
