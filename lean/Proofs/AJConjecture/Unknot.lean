import Mathlib
import AJConjecture.BraidKnot

/-!
# The unknot

The unknot as the closure of the empty braid on one strand. It is used as a sanity check of
the formal AJ statement: the statement holds for it.
-/

namespace AJConjecture

/-- The unknot: the closure of the empty braid word on one strand. -/
def unknot : BraidKnot where
  strands := 1
  word := []
  strands_pos := Nat.one_pos
  isOnStrands := fun _ hg ↦ absurd hg List.not_mem_nil
  connected := fun _ _ ↦ ⟨0, Subsingleton.elim _ _⟩

end AJConjecture
