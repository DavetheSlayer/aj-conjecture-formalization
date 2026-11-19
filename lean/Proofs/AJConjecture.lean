import Mathlib
import AJConjecture.AJStatement
import AJFamily.FamilyMain

/-!
# Resolution of the localized square-free `SL₂` AJ conjecture

The conjecture is false. A counterexample is `whiteheadTorusKnot 1`, the closure of a 7-strand
braid with 24 crossings presenting the untwisted negative-clasp Whitehead double of the
right-handed trefoil: the case `k = 1` of `whiteheadTorusKnot_counterexample`.
-/

namespace AJConjecture

/-- The localized square-free `SL₂` AJ conjecture (contract `AJ-SF-SL2-S3-v1`) is false. -/
theorem not_ajSquareFreeConjecture : ¬ AJSquareFreeConjecture := fun h ↦
  (whiteheadTorusKnot_counterexample 1 le_rfl).1 (h _)

end AJConjecture
