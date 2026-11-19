import Mathlib
import AJTwist.Knot.TwKHalfLine
import AJTwist.Knot.TwKPosHalfLine

/-!
# The half line `ℓ ≤ 0` for the positive clasp

`twSrcOp_halfLine_pos`: the operator form of the band-and-clasp identity for the positive clasp
and the twists `ℓ = -n ≤ 0`, which `TwKBandClasp` extends to every `ℓ` by the Cayley–Hamilton
theorem. It is the case `σ = false` of `twkSrcOp_halfLine` (`TwKPosHalfLine`), which is proved for
both clasp signs from the nodes `TwKPos*`: the positive clasp differs from the negative one by
one fixed macro at the tip of the Hopf disc (`morseReach_twkTipFlip`) and one at the clasp
(`morseReach_twkKRaw_false`), both proved; everything else is common to the two signs.
-/

noncomputable section

namespace AJConjecture

/-- Operator form of the half line for the positive clasp. -/
theorem twSrcOp_halfLine_pos {r s : ℕ} (h : IsTorusPair r s) (c n : ℕ) :
    twSrcOp r s false c (halfTwistZ c (-(2 * (n : ℤ)))) =
      ptrTail c (2 * c) (longKnotOp (torusPairKnot r s h) (2 * c) *
        (halfTwistZ c (-(2 * (n : ℤ)) - 2 * (((r - 1) * s : ℕ) : ℤ)) * claspSOp c false)) :=
  twkSrcOp_halfLine h false c n

end AJConjecture
