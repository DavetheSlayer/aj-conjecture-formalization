import Mathlib
import AJHandoff.TorusKnot.PairKWhDFrame
import AJHandoff.TorusKnot.PairKWhDOrientReach

/-!
# The Whitehead double is an operation on long knots

`morseReach_whDouble`: if the long-knot diagram `D` reaches `D'` by the moves of the checker
(planar isotopies, the second and third Reidemeister moves, and the framed first Reidemeister
move, see `formalization/WHITEHEAD_BRIDGE.md` of the audit repository), then `whDouble D` reaches `whDouble D'`. Every move preserves
the oriented writhe (`morseWrithe_eq_of_morseReach`), so both doubles carry the same number of
compensating full twists, and the doubled moves are moves (`morseReach_whDouble_of_writhe`, from
the generic `morseReach_morseDouble`). Hence `whDouble` is well defined on the classes of
long-knot diagrams up to the moves.
-/

namespace AJConjecture

/-- **`whDouble` respects the moves**: reachable long-knot diagrams have reachable untwisted
negative-clasp Whitehead doubles. -/
theorem morseReach_whDouble {D D' : MorseWord} (hD : morseFits 1 D = true)
    (h : MorseReach 1 D D') : MorseReach 1 (whDouble D) (whDouble D') :=
  morseReach_whDouble_of_writhe hD h (morseWrithe_eq_of_morseReach hD h)

end AJConjecture
