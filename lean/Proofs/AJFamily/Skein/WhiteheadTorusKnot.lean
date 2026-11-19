import Mathlib
import AJFamily.Skein.TorusWordConnected
import AJFamily.Skein.TorusWordStrands

/-!
# The family knots

`whiteheadTorusKnot k` (`k ≥ 1`): the closure of `whiteheadTorusWord k` on `4k + 3` strands.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The negative-clasp untwisted Whitehead double of `T(2, 2k+1)` as a closed braid on `4k + 3`
strands (`k ≥ 1`). -/
def whiteheadTorusKnot (k : ℕ) (hk : 1 ≤ k) : BraidKnot where
  strands := 4 * k + 3
  word := whiteheadTorusWord k
  strands_pos := by omega
  isOnStrands := isOnStrands_whiteheadTorusWord k
  connected := connected_whiteheadTorusWord k hk

end AJConjecture
