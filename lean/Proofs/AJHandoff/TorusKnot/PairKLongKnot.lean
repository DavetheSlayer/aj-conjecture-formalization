import Mathlib
import AJConjecture.SkeinMorseCheckSound
import AJHandoff.TorusKnot.PairKIsotopy
import AJHandoff.TorusKnot.PairKKnot
import AJHandoff.TorusKnot.PairKTargetOp

/-!
# The long-knot operator of `Wh⁻₀(T(r, s))`

`longKnotOp_pairWhiteheadKnot`: at every colour `c`, the long-knot operator of
`pairWhiteheadKnot r s h` is the partial trace `ptrTail c (2c)` of
`longKnotOp (torusPairKnot r s h) (2c)` followed by `2(r - 1)s` negative half twists and the
clasp. This is the hypothesis `hK` of `pairQ_knot_package` (package P1), with the framing
exponent `w = (r - 1)s`; the writhe hypothesis `hw` is `writhe_pairWhiteheadWord`.
-/

namespace AJConjecture

/-- T-KNOT: the long-knot identity for `Wh⁻₀(T(r, s))`. -/
theorem longKnotOp_pairWhiteheadKnot {r s : ℕ} (h : IsTorusPair r s) (c : ℕ) :
    longKnotOp (pairWhiteheadKnot r s h) c =
      ptrTail c (2 * c) (longKnotOp (torusPairKnot r s h) (2 * c) *
        (halfTwist c false ^ (2 * ((r - 1) * s)) * claspOp c)) := by
  obtain ⟨mvs, hm⟩ := morseReach_pair_source_target h
  rw [← morseOp_morseLongClosure_eq_longKnotOp, ← morseOp_pairTargetWord h c]
  exact morseOp_eq_of_morseApplyAll c 1 c c (Nat.mul_one c).symm _ _ mvs hm

/-- The writhe of `Wh⁻₀(T(r, s))` as a closed braid is `2(r - 1)s - 2`. -/
theorem writhe_pairWhiteheadKnot {r s : ℕ} (h : IsTorusPair r s) :
    writhe (pairWhiteheadKnot r s h).word = 2 * (((r - 1) * s : ℕ) : ℤ) - 2 :=
  writhe_pairWhiteheadWord h

end AJConjecture
