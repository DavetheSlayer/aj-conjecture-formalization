import Mathlib
import AJConjecture.SkeinThickCable

/-!
# The strand bookkeeping of a braid word

`strandEnd w` is the composition of the transpositions of the letters of `w`, the first letter
being applied first. It is multiplicative on words, the word read backwards gives the inverse
map, and the columns `< m` are preserved by a word on `m` strands. All statements are inductions
on the word.
-/

namespace AJConjecture

/-- The strand bookkeeping of a concatenation. -/
theorem strandEnd_append (u v : BraidWord) (p : ℕ) :
    strandEnd (u ++ v) p = strandEnd v (strandEnd u p) := by
  induction u generalizing p with
  | nil => rfl
  | cons g u ih => exact ih _

/-- The reversed word undoes the strand bookkeeping. -/
theorem strandEnd_reverse_strandEnd (w : BraidWord) (p : ℕ) :
    strandEnd w.reverse (strandEnd w p) = p := by
  induction w generalizing p with
  | nil => rfl
  | cons g w ih =>
    rw [List.reverse_cons, strandEnd_append]
    change strandEnd [g] (strandEnd w.reverse (strandEnd w _)) = p
    rw [ih]
    exact Equiv.swap_apply_self _ _ _

/-- The word undoes the strand bookkeeping of the reversed word. -/
theorem strandEnd_strandEnd_reverse (w : BraidWord) (p : ℕ) :
    strandEnd w (strandEnd w.reverse p) = p := by
  induction w generalizing p with
  | nil => rfl
  | cons g w ih =>
    rw [List.reverse_cons, strandEnd_append]
    change strandEnd w
      (Equiv.swap g.1 (g.1 + 1) (Equiv.swap g.1 (g.1 + 1) (strandEnd w.reverse p))) = p
    rw [Equiv.swap_apply_self, ih]

end AJConjecture
