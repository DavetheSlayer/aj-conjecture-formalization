import Mathlib
import AJFamily.Skein.TorusPhaseTwoBundle
import AJFamily.Skein.TorusPhaseTwoCurls
import AJFamily.Skein.TorusPhaseTwoFinish
import AJFamily.Skein.TorusPhaseTwoGadget
import AJFamily.Skein.TorusPhaseTwoNormal
import AJFamily.Skein.TorusPhaseTwoSwing

/-!
# The isotopy, phase II: from the strip word to the target word

`morseReach_strip_target`: the strip word reaches the band-and-clasp target word `torusTargetWord k`
in six stages, through the words of `TorusPhaseTwoWords`. Stage N puts the blocks in normal form,
after which the strip is a band: the doubled 2-braid `D^(2k+1)` with curls on its edges, negative
full twists and the clasp. Stage S swings the return strand from the far left to the far right,
stage C cancels the edge curls, stages T and G carry the twists and then the clasp around the band
to its end, and stage E removes the half-twist conjugation left on the clasp.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- Phase II: the strip word reaches the band-and-clasp target word. -/
theorem morseReach_strip_target (k : ℕ) (hk : 1 ≤ k) :
    MorseReach 1 (stripWord k) (torusTargetWord k) :=
  morseReach_trans (phaseTwo_stageN k hk) <| morseReach_trans (phaseTwo_stageS k hk) <|
    morseReach_trans (phaseTwo_stageC k hk) <| morseReach_trans (phaseTwo_stageT k hk) <|
      morseReach_trans (phaseTwo_stageG k hk) (phaseTwo_stageE k hk)

end AJConjecture
