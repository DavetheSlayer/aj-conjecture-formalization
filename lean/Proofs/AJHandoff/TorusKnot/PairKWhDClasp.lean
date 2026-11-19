import Mathlib
import AJHandoff.TorusKnot.PairKWhDDefs

/-!
# The clasp of `whDouble` is negative

`orientStates_clasp_negative`: when the band arrives at the clasp with its left edge oriented
upward and its right edge downward and the closing strand upward (the orientation of the long knot
`whDouble D`, whose input is the left edge of the band), the clasp and the last cap have exactly
one orientation and the two clasp crossings contribute `-2`: both are negative crossings. They are
self-crossings of one component, so the sign does not depend on the orientation
(`orientStates_clasp_negative_rev`). Finite checks.
-/

namespace AJConjecture

/-- **The clasp is negative**: with the band edges oriented up and down and the closing strand
up, the clasp and the last cap have one orientation, in which the two clasp crossings contribute
`-2`. -/
theorem orientStates_clasp_negative :
    orientStates (claspWord ++ [(.cap, 1)]) [([true, false, true], 0)] = [([true], -2)] := by
  decide

/-- The same with all orientations reversed: the clasp crossings are self-crossings of one
component, their sign does not depend on the orientation. -/
theorem orientStates_clasp_negative_rev :
    orientStates (claspWord ++ [(.cap, 1)]) [([false, true, false], 0)] = [([false], -2)] := by
  decide

end AJConjecture
