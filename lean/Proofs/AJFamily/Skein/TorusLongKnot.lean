import Mathlib
import AJConjecture.SkeinMorseCheckSound
import AJFamily.Skein.TorusPhaseOne
import AJFamily.Skein.TorusPhaseTwo
import AJFamily.Skein.TorusTargetOp
import AJFamily.Skein.WhiteheadTorusKnot

/-!
# The long-knot operator of the family knots

`longKnotOp_whiteheadTorusKnot`: at every colour `c`, the long-knot operator of
`whiteheadTorusKnot k` is the partial trace `ptrTail c (2c)` of `longKnotOp (torusKnot k) (2c)`
followed by `2(2k+1)` negative half twists and the clasp. Phases I and II of the isotopy take the
long closure of the braid word to `torusTargetWord k`; soundness of the checker and
`morseOp_torusTargetWord` give the operator identity.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

theorem longKnotOp_whiteheadTorusKnot (k : ℕ) (hk : 1 ≤ k) (c : ℕ) :
    longKnotOp (whiteheadTorusKnot k hk) c =
      ptrTail c (2 * c)
        (longKnotOp (torusKnot k) (2 * c) * (halfTwist c false ^ (2 * (2 * k + 1)) * claspOp c)) := by
  obtain ⟨mvs, h⟩ := morseReach_trans (morseReach_source_strip k hk) (morseReach_strip_target k hk)
  rw [← morseOp_morseLongClosure_eq_longKnotOp, ← morseOp_torusTargetWord k c]
  exact morseOp_eq_of_morseApplyAll c 1 c c (Nat.mul_one c).symm _ _ mvs h

end AJConjecture
