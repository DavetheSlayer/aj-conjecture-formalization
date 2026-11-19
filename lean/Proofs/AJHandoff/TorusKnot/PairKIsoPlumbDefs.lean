import Mathlib
import AJHandoff.TorusKnot.PairKIsoSwing

/-!
# Stage P: the words of the clasp formation

The Hopf band is plumbed onto the annulus along the disc `T`, whose band runs up the right of the
word from round `0` to the last caps; the Hopf hook `isoBHopf` sits right after round `0`. As in the
library's stage C (steps 1–3, `AJFamily.Skein.TorusPhaseTwoCurls`):

1. `pairWP1`: the curl-and-cap `u0 −1 n0 n0` of the second Hopf letter (the *X tip*) moves down
   along the disc `T` to the hook, past everything on its left (exchanges);
2. `pairWP2`: the curl of the top-right climb goes around its cap (macro `CAPM`) and down into the
   hook (exchanges);
3. `pairWP3`: the curl of round `0` moves back through the last `r - 2` doubled crossings of its
   walk (a one-strand bead passes a doubled crossing, `morseReach_pass`), and the hook material
   commutes left past them (`morseReach_comm`): the window is now the library's `WIN` window
   shifted by `4q`;
4. `pairWP`: macro `WIN` (two `kink`s) at the shift `4q`: the X-tip curl cancels the curl of round
   `0`, the clasp absorbs the fold curl; what remains is the conjugated clasp `C_S` on the band of
   the disc `T`.

All four words were validated outside Lean (writhe, rotation numbers `-2c` for 1–3 and `-2c + 4`
for `pairWP`, Jones; `SCR/ISO/tools/lean_words.py`).
-/

namespace AJConjecture

/-- The X tip: a negative curl followed by a cap. -/
def isoXTip : MorseWord := [isoU 0, isoX false 1, isoN 0, isoN 0]

/-- The left side of the library macro `WIN`. -/
def isoWinL : MorseWord :=
  [isoU 2, isoU 3] ++ phaseTwoD ++ [isoU 1, isoX true 2, isoN 1] ++
    [isoU 6, isoX true 5, isoX false 4] ++ [isoU 5, isoX false 4, isoN 5] ++ [isoX false 5] ++
    [isoU 5, isoX false 6, isoN 5, isoN 5]

/-- The right side of the library macro `WIN`. -/
def isoWinR : MorseWord := [isoU 2, isoU 3] ++ phaseTwoD ++ phaseTwoClaspS

/-- The part of the band below round `0`. -/
def pairPlumbPre (r s : ℕ) : MorseWord :=
  [isoU 1] ++ phaseTwoA1 ++ (List.range (r - 2 - 1)).flatMap (fun i ↦ isoBLC (i + 1)) ++
    isoBLC (r - 2) ++ phaseTwoBlk (isoBDec (r - 2)) (pairRunDown r s - 1) ++
    phaseTwoBlk (isoBInc (r - 2)) (pairRunUp r s + 1)

/-- The right descents. -/
def pairPlumbRd (r : ℕ) : MorseWord :=
  (List.range (r - 2 - 1)).reverse.flatMap (fun i ↦ isoBRd (i + 1))

/-- The end of the word after the clasp formation. -/
def pairPlumbTail : MorseWord := [isoN 2, isoU 1, isoX true 2, isoN 1, isoN 1]

/-- Step 1: the X tip moved down to the hook. -/
def pairWP1 (r s : ℕ) : MorseWord :=
  pairPlumbPre r s ++ isoBR0 (r - 2) r ++ isoBHopf (r - 2) r ++
    morseShiftWord (2 * (r - 2) + 2 * r + 1) isoXTip ++ phaseTwoBlk (isoBRound (r - 2) r) (s - 2) ++
    isoBLast (r - 2) r ++ isoBTrc (r - 2) ++ pairPlumbRd r ++ pairPlumbTail

/-- Step 2: the fold curl moved into the hook. -/
def pairWP2 (r s : ℕ) : MorseWord :=
  pairPlumbPre r s ++ morseDouble ([isoU (2 * r - 3)] ++ morseWalkL true (r - 2) (r - 1)) ++
    morseShiftWord (2 * (r - 2)) (isoCurlL true 1) ++
    morseShiftWord (4 * r - 5) [isoU 3, isoX true 2, isoX false 1] ++
    morseShiftWord (4 * r - 4) [isoU 1, isoX false 0, isoN 1] ++
    morseShiftWord (4 * r - 5) [isoX false 2] ++ morseShiftWord (4 * r - 3) isoXTip ++
    phaseTwoBlk (isoBRound (r - 2) r) (s - 2) ++ isoBLast (r - 2) r ++
    morseShiftWord (4 * (r - 2) - 2) [isoX false 0, isoX false 0, isoN 1] ++ pairPlumbRd r ++
    pairPlumbTail

/-- Step 3: the window of macro `WIN`, shifted by `4q`. -/
def pairWP3 (r s : ℕ) : MorseWord :=
  pairPlumbPre r s ++ morseShiftWord (4 * (r - 2)) isoWinL ++
    morseDouble (morseWalkL true (r - 2) (r - 2)) ++ phaseTwoBlk (isoBRound (r - 2) r) (s - 2) ++
    isoBLast (r - 2) r ++ morseShiftWord (4 * (r - 2) - 2) [isoX false 0, isoX false 0, isoN 1] ++
    pairPlumbRd r ++ pairPlumbTail

/-- The word after stage P: the conjugated clasp `C_S` on the band of the disc `T`. -/
def pairWP (r s : ℕ) : MorseWord :=
  pairPlumbPre r s ++ morseShiftWord (4 * (r - 2)) isoWinR ++
    morseDouble (morseWalkL true (r - 2) (r - 2)) ++ phaseTwoBlk (isoBRound (r - 2) r) (s - 2) ++
    isoBLast (r - 2) r ++ morseShiftWord (4 * (r - 2) - 2) [isoX false 0, isoX false 0, isoN 1] ++
    pairPlumbRd r ++ pairPlumbTail

end AJConjecture
