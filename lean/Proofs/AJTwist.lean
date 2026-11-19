import Mathlib
import AJTwist.TwDefs
import AJTwist.Main.TwMTheorem
import AJTwist.Exist.TwHKnot
import AJTwist.Knot.TwKCayley
import AJTwist.Knot.TwKFamilyWord

/-!
# The four families of twisted Whitehead doubles

Formalization of Theorem 1.1 of *Whitehead doubles and the failure of the square-free AJ
conjecture* (revision 5, handoff of 18 November 2026): all integer twists, both clasp signs and
both companion chiralities. The main theorem is `AJConjecture.theoremFourFamilies`
(`AJTwist/Main/TwMTheorem.lean`); its predicate `TwFamilyClauses` is `PairTClauses` with the
obstruction factor and the classical bound as parameters. The numbers of strands and the braid
words of the four families are the data definitions `twFamilyStrands` and `twFamilyWord`
(`AJTwist/Knot/TwKFamilyWord.lean`).
-/
