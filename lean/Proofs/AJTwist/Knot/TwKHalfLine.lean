import Mathlib
import AJTwist.Knot.TwKPosHalfLine

/-!
# The half line `ℓ ≤ 0`, negative clasp

`twSrcOp_halfLine`: for the negative clasp, the source operator with `n` negative full twists
inserted at the bottom end of the band is the operator of the band-and-clasp word with `2n` more
negative half twists. It is the case `σ = true` of `twkSrcOp_halfLine` (`TwKPosHalfLine`), which
is proved for both clasp signs by one route (closed-form fence word, stages N and S, evacuation of
the beads of the doubled companion, order-independence of the bead operators).
-/

noncomputable section

namespace AJConjecture

/-- The half line `ℓ = -n ≤ 0` for the negative clasp. -/
theorem twSrcOp_halfLine {r s : ℕ} (h : IsTorusPair r s) (c n : ℕ) :
    twSrcOp r s true c (halfTwistZ c (-(2 * (n : ℤ)))) =
      ptrTail c (2 * c) (longKnotOp (torusPairKnot r s h) (2 * c) *
        (halfTwistZ c (-(2 * (n : ℤ)) - 2 * (((r - 1) * s : ℕ) : ℤ)) * claspSOp c true)) :=
  twkSrcOp_halfLine h true c n

end AJConjecture
