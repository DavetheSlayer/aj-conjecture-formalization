import Mathlib
import AJFamily.Skein.MorsePhaseTools
import AJFamily.Skein.TorusStripWord

/-!
# The intermediate words of phase I

Closed forms, in `k` and the level `L`, of the words met in phase I. Phase I processes the levels
`4k+1, 4k, …, 1`; each level step flips the closing arc of the level and retracts the dead ends. The
words after the steps are `phaseOneTop1 k`, `phaseOneTop2 k`, `phaseOneStair k L`
(`2k+2 ≤ L ≤ 4k-1`), `phaseOneX k` and `phaseOneClimb k L` (`1 ≤ L ≤ 2k`); the stage words are the
words between the links of a step.
-/

namespace AJConjecture

/-! ### Fixed pieces -/

/-- `stripA` shifted one strand to the left. -/
def stripAOne : MorseWord := [(.cup, 2), (.cross true, 1), (.cross true, 0), (.cross false, 1), (.cap, 0)]

/-- `stripM` shifted one strand to the left. -/
def stripMOne : MorseWord :=
  [(.cup, 2), (.cross true, 1), (.cross true, 0), (.cup, 1), (.cross false, 1), (.cross false, 2),
    (.cross false, 3), (.cup, 6), (.cross true, 5), (.cross false, 4), (.cross false, 5),
    (.cross true, 1), (.cross true, 0)]

/-- `stripB` shifted one strand to the left. -/
def stripBOne : MorseWord :=
  [(.cup, 1), (.cross false, 1), (.cross false, 2), (.cross false, 3), (.cap, 4), (.cross true, 1),
    (.cross true, 0)]

theorem morseShiftWord_one_stripAOne : morseShiftWord 1 stripAOne = stripA := by decide
theorem morseShiftWord_one_stripMOne : morseShiftWord 1 stripMOne = stripM := by decide
theorem morseShiftWord_one_stripBOne : morseShiftWord 1 stripBOne = stripB := by decide

/-- The T-part of the staircase phase (shifted by `L - 2`). -/
def phaseOneTp : MorseWord :=
  [(.cross true, 1), (.cross false, 2), (.cross false, 3), (.cap, 4), (.cross true, 1),
    (.cross true, 0), (.cross false, 1), (.cap, 2)]

/-- The first half of the T-part (in the word after the level `2k + 1`). -/
def phaseOneTpHead : MorseWord := [(.cross true, 1), (.cross false, 2), (.cross false, 3), (.cap, 4)]

/-- The tail of the small-climb phase (shifted by `L - 1`). -/
def phaseOneTq : MorseWord :=
  [(.cap, 3), (.cross true, 2), (.cross true, 1), (.cross false, 2), (.cap, 1), (.cross true, 2)]

/-- What the macro `TG` leaves of the T-part (shifted by `l - 1`). -/
def phaseOneR4 : MorseWord :=
  [(.cross true, 1), (.cross false, 2), (.cross false, 3), (.cross false, 4), (.cap, 5),
    (.cross true, 2), (.cross true, 1), (.cross true, 0), (.cross false, 1), (.cross false, 2),
    (.cap, 3)]

/-- What the macro `S2a` leaves of the middle groups (shifted by `4k - 2`). -/
def phaseOneR2s : MorseWord :=
  [(.cross false, 2), (.cup, 5), (.cross true, 4), (.cross true, 3), (.cross true, 2),
    (.cross true, 1), (.cross false, 2), (.cross false, 3), (.cross false, 4), (.cup, 7),
    (.cross true, 6), (.cross false, 5), (.cross false, 6), (.cross true, 2), (.cross true, 1),
    (.cross true, 0), (.cross false, 1), (.cross false, 2), (.cap, 3)]

/-- What the macro `STb` leaves of the T-part head (shifted by `2k`). -/
def phaseOneRT : MorseWord :=
  [(.cross true, 0), (.cross false, 1), (.cross false, 2), (.cross false, 3), (.cap, 4)]

/-- The retracted blocks of the staircase phase: `M` and `r` copies of `B`, shifted by `s`. -/
def phaseOneStairBlocks (s r : ℕ) : MorseWord :=
  morseShiftWord s (stripM ++ (List.replicate r stripB).flatten)

/-- The retracted blocks of the small-climb phase: `a` copies of `A`, `M`, `b` copies of `B`. -/
def phaseOneClimbBlocks (s a b : ℕ) : MorseWord :=
  morseShiftWord s ((List.replicate a stripA).flatten ++ stripM ++ (List.replicate b stripB).flatten)

/-! ### The words after each level step -/

/-- The source word, cut into its pieces: the closing cups, the small climbs, the big climb, the
first staircase step and Hopf letter, the staircase, the last crossing, the final climb, the second
Hopf letter, the closing caps. -/
def phaseOneSource (k : ℕ) : MorseWord :=
  morseCupRun 1 (4 * k + 2) ++ morseClimbRun (2 * k - 1) ++ morseBand (2 * k - 1) (4 * k) ++
    morseBand (4 * k - 1) (4 * k + 1) ++ [(.cross false, 4 * k + 1)] ++
    morseStairRun (2 * k) (4 * k - 2) ++ morseBand 0 (2 * k + 1) ++ morseBand (2 * k) (4 * k + 1) ++
    [(.cross false, 4 * k + 1)] ++ morseCapRun (4 * k + 2)

/-- After the level `4k + 1`. -/
def phaseOneTop1 (k : ℕ) : MorseWord :=
  morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) (4 * k) ++ morseBand (2 * k - 1) (4 * k) ++
    [(.cup, 4 * k + 1), (.cross true, 4 * k), (.cross true, 4 * k - 1), (.cross false, 4 * k)] ++
    [(.cup, 4 * k + 3), (.cross true, 4 * k + 2), (.cross false, 4 * k + 1),
      (.cross false, 4 * k + 2)] ++
    morseStairRun (2 * k) (4 * k - 2) ++ morseBand 0 (2 * k + 1) ++ morseBand (2 * k) (4 * k + 1) ++
    [(.cross true, 4 * k + 2)] ++ morseCapRun (4 * k + 2)

/-- After the level `4k`. -/
def phaseOneTop2 (k : ℕ) : MorseWord :=
  morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) (4 * k) ++ morseBand (2 * k - 1) (4 * k) ++
    [(.cup, 4 * k + 2), (.cross true, 4 * k + 1), (.cross true, 4 * k), (.cross true, 4 * k - 1),
      (.cross false, 4 * k), (.cross false, 4 * k + 1)] ++
    [(.cup, 4 * k + 4), (.cross true, 4 * k + 3), (.cross false, 4 * k + 2),
      (.cross false, 4 * k + 3)] ++
    morseBand (4 * k - 2) (4 * k) ++ [(.cap, 4 * k)] ++
    morseStairRun (2 * k) (4 * k - 3) ++ morseBand 0 (2 * k + 1) ++ morseBand (2 * k) (4 * k) ++
    [(.cross true, 4 * k + 1)] ++ morseCapRun (4 * k + 1)

/-- After the level `L`, staircase phase (`2k + 2 ≤ L ≤ 4k - 1`). -/
def phaseOneStair (k L : ℕ) : MorseWord :=
  morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) L ++ morseBand (2 * k - 1) L ++
    phaseOneStairBlocks (L - 1) (4 * k - 1 - L) ++ morseShiftWord (L - 2) phaseOneTp ++
    morseStairRun (2 * k) (L - 3) ++ morseBand 0 (2 * k + 1) ++ morseBand (2 * k) L ++
    [(.cross true, L + 1)] ++ morseCapRun (L + 1)

/-- After the level `2k + 1`. -/
def phaseOneX (k : ℕ) : MorseWord :=
  morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) (2 * k + 1) ++ morseBand (2 * k - 1) (2 * k + 1) ++
    phaseOneStairBlocks (2 * k) (2 * k - 2) ++ morseShiftWord (2 * k - 1) phaseOneTpHead ++
    morseBand 0 (2 * k + 1) ++ [(.cap, 2 * k + 1)] ++ morseBand (2 * k) (2 * k + 1) ++
    [(.cross true, 2 * k + 2)] ++ morseCapRun (2 * k + 2)

/-- After the level `L`, small-climb phase (`1 ≤ L ≤ 2k`). -/
def phaseOneClimb (k L : ℕ) : MorseWord :=
  morseHeadRun L ++ phaseOneClimbBlocks (L - 1) (2 * k - L) (2 * k - 1) ++ morseBand 0 L ++
    [(.cross false, L), (.cross false, L + 1)] ++ morseShiftWord (L - 1) phaseOneTq ++
    morseCapRun (L + 1)

/-! ### Stage words -/

/-- The tail before the end of a flip: the walk `X(l+1) ⋯ X(l+4)`, the staircase, the last
crossing, the final climb `b(2k, l+1)`, the Hopf letter, the caps. -/
def phaseOneTailWalk (k l : ℕ) : MorseWord :=
  morseWalk true (l + 1) 4 ++ morseStairRun (2 * k) (l - 2) ++ morseBand 0 (2 * k + 1) ++
    morseBand (2 * k) (l + 1) ++ [(.cross true, l + 2)] ++ morseCapRun (l + 2)

/-- The tail after a flip: the closing arc of the level `l` runs along the final climb. -/
def phaseOneTailFlipped (k l : ℕ) : MorseWord :=
  morseStairRun (2 * k) (l - 2) ++ morseBand 0 (2 * k + 1) ++
    [(.cross true, l + 1), (.cross true, l)] ++ morseBand (2 * k) l ++
    [(.cap, l + 1), (.cross true, l + 1)] ++ morseCapRun (l + 1)

/-- The tail after the cap of the level `l` has been retracted (staircase phase, `l ≥ 2k + 2`). -/
def phaseOneTailRetracted (k l : ℕ) : MorseWord :=
  morseBand (l - 2) l ++ [(.cap, l)] ++ morseStairRun (2 * k) (l - 3) ++ morseBand 0 (2 * k + 1) ++
    morseBand (2 * k) l ++ [(.cross true, l + 1)] ++ morseCapRun (l + 1)

/-- The tail after the cap of the level `2k + 1` has been retracted. -/
def phaseOneTailX (k : ℕ) : MorseWord :=
  morseBand 0 (2 * k + 1) ++ [(.cap, 2 * k + 1)] ++ morseBand (2 * k) (2 * k + 1) ++
    [(.cross true, 2 * k + 2)] ++ morseCapRun (2 * k + 2)

/-- The top step after its flip (the level `4k + 1`). -/
def phaseOneS0Mid (k : ℕ) : MorseWord :=
  morseCupRun 1 (4 * k + 1) ++ [(.cup, 4 * k + 3)] ++ morseClimbRun (2 * k - 1) ++
    morseBand (2 * k - 1) (4 * k) ++
    [(.cross true, 4 * k), (.cross true, 4 * k - 1), (.cross false, 4 * k), (.cross true, 4 * k + 2),
      (.cross false, 4 * k + 1), (.cross false, 4 * k + 2)] ++
    morseStairRun (2 * k) (4 * k - 2) ++ morseBand 0 (2 * k + 1) ++ morseBand (2 * k) (4 * k + 1) ++
    [(.cross true, 4 * k + 2)] ++ morseCapRun (4 * k + 2)

/-- The level `4k - 1`: the part of the word in front of the tail during the step. -/
def phaseOneS2Pre (k : ℕ) : MorseWord :=
  morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) (4 * k - 1) ++ [(.cup, 4 * k + 1), (.cross true, 4 * k)] ++
    morseBand (2 * k - 1) (4 * k) ++ morseShiftWord (4 * k - 2) phaseOneR2s

/-- The level `4k - 1` after the walk has passed the middle groups. -/
def phaseOneS2Mid (k : ℕ) : MorseWord :=
  phaseOneS2Pre k ++ phaseOneTailWalk k (4 * k - 1)

/-- Staircase step of the level `l`: the part in front of the tail (after the T-part macro). -/
def phaseOneStairPre (k l : ℕ) : MorseWord :=
  morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) l ++ [(.cup, l + 2), (.cross true, l + 1)] ++
    morseBand (2 * k - 1) (l + 1) ++ [(.cross false, l + 1)] ++
    phaseOneStairBlocks (l + 1) (4 * k - 2 - l) ++ [(.cross true, l + 1)] ++
    morseShiftWord (l - 1) phaseOneR4

/-- Staircase step of the level `l`, after the walk has passed the blocks. -/
def phaseOneStairMid1 (k l : ℕ) : MorseWord :=
  morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) l ++ [(.cup, l + 2), (.cross true, l + 1)] ++
    morseBand (2 * k - 1) (l + 1) ++ [(.cross false, l + 1)] ++
    phaseOneStairBlocks (l + 1) (4 * k - 2 - l) ++ morseWalk true (l + 1) 8 ++
    morseShiftWord (l - 1) phaseOneTp ++ morseStairRun (2 * k) (l - 2) ++ morseBand 0 (2 * k + 1) ++
    morseBand (2 * k) (l + 1) ++ [(.cross true, l + 2)] ++ morseCapRun (l + 2)

/-- Staircase step of the level `l`, after the flip. -/
def phaseOneStairMid2 (k l : ℕ) : MorseWord := phaseOneStairPre k l ++ phaseOneTailFlipped k l

/-- Staircase step of the level `l`, after the retraction of the cap. -/
def phaseOneStairMid3 (k l : ℕ) : MorseWord := phaseOneStairPre k l ++ phaseOneTailRetracted k l

/-- The step of the level `2k` after its flip. -/
def phaseOneTMid (k : ℕ) : MorseWord :=
  morseHeadRun (2 * k - 1) ++
    [(.cup, 2 * k), (.cup, 2 * k + 2), (.cross true, 2 * k + 1), (.cross true, 2 * k),
      (.cross true, 2 * k - 1), (.cross false, 2 * k), (.cross false, 2 * k + 1)] ++
    phaseOneStairBlocks (2 * k + 1) (2 * k - 2) ++ [(.cross true, 2 * k + 1)] ++
    morseShiftWord (2 * k) phaseOneRT ++ [(.cross true, 2 * k + 1)] ++ morseBand 0 (2 * k + 1) ++
    morseWalk true (2 * k + 2) 5 ++ [(.cap, 2 * k + 1), (.cross true, 2 * k), (.cross true, 2 * k + 2)] ++
    morseCapRun (2 * k + 2)

/-- Small-climb step of the level `l` after its flip. -/
def phaseOneClimbMid (k l : ℕ) : MorseWord :=
  morseHeadRun l ++ [(.cup, l + 2), (.cross true, l + 1), (.cross true, l), (.cross false, l + 1)] ++
    phaseOneClimbBlocks (l + 1) (2 * k - l - 1) (2 * k - 1) ++ [(.cross true, l + 1)] ++
    morseBand 0 (l + 1) ++ morseWalk true (l + 2) 7 ++ [(.cross false, l + 1), (.cross false, l + 2)] ++
    morseShiftWord l phaseOneTq ++ morseCapRun (l + 2)

end AJConjecture
