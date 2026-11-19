import Mathlib
import AJFamily.Skein.TorusPhaseOneClimb
import AJFamily.Skein.TorusPhaseOneK1
import AJFamily.Skein.TorusPhaseOneStair
import AJFamily.Skein.TorusPhaseOneTop

/-!
# The isotopy, phase I: from the family word to the strip word

`morseReach_source_strip`: the long closure of `whiteheadTorusWord k` reaches `stripWord k` by
checker moves. For `k = 1` this is the concrete certificate of `TorusPhaseOneK1`. For `k ≥ 2` it is
a chain of `4k + 1` level steps through the closed-form words of `TorusPhaseOneWords`:
`phaseOneSource k` → `phaseOneTop1 k` → `phaseOneTop2 k` → `phaseOneStair k (4k-1)` → ⋯ →
`phaseOneStair k (2k+2)` → `phaseOneX k` → `phaseOneClimb k (2k)` → ⋯ →
`phaseOneClimb k 1 = stripWord k`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- Phase I: the long closure of the family word reaches the strip word. -/
theorem morseReach_source_strip (k : ℕ) (hk : 1 ≤ k) :
    MorseReach 1 (morseLongClosure (4 * k + 3) (whiteheadTorusWord k)) (stripWord k) := by
  rcases Nat.lt_or_ge k 2 with h | h
  · obtain rfl : k = 1 := by omega
    exact phaseOne_k1
  · rw [phaseOneSource_eq k hk, ← phaseOneClimb_one k hk]
    refine morseReach_trans (phaseOne_stepS0_flip k hk) ?_
    refine morseReach_trans (phaseOne_stepS0_retract k hk) ?_
    refine morseReach_trans (phaseOne_stepS1 k hk) ?_
    refine morseReach_trans (phaseOne_stepS2_flip k h) ?_
    refine morseReach_trans (phaseOne_stepS2_retract k h) ?_
    refine morseReach_trans (phaseOne_stairChain k h (2 * k + 2) le_rfl (by omega)) ?_
    refine morseReach_trans (phaseOne_stairToX k h) ?_
    refine morseReach_trans (phaseOne_stepT_flip k hk) ?_
    refine morseReach_trans (phaseOne_stepT_retract k hk) ?_
    exact phaseOne_climbChain k hk 1 le_rfl (by omega)

end AJConjecture
