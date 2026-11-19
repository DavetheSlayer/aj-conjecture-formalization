import Mathlib
import AJHandoff.TorusKnot.PairKIsoStripDefs

/-!
# Stage N: the strip blocks in normal form

Each strip block becomes a piece of the blackboard double `morseDouble` of a one-strand word (the
core of the annulus, `pairCore r s`) together with *beads*: negative full twists `−i −i` of a
band, positive or negative left curls `u_i x_{i+1} n_i` on one edge, and the Hopf hook. The pieces
are written in *band coordinates* (`isoB…`): the band of the core at the position `p` occupies the
strands `2p, 2p + 1`; in the strip word, where a return strand runs up the far left, they appear
shifted by one (`pairWN`).

| strip block | normal form (band coordinates) | beads |
|---|---|---|
| `isoStLC i` | `morseDouble [u_{i-1}]` | positive left curl |
| `isoStDec q` | — | positive left curl |
| `isoStInc q` | — | negative full twist, negative left curl (`phaseTwoA1`, macro `A`) |
| `isoStR0 q r` | `morseDouble (u_{q+r-1} · walkL q (r-1))` | positive left curl |
| `isoStHopf q r` | the Hopf hook, unchanged | |
| `isoStRound q r` | `morseDouble (walkL q (r-1))` | positive left curl |
| `isoStLast q r` | `morseDouble (walkL q (r-1) · n_{q-1})` | negative full twist and curl |
| `isoStTrc q` | the inner cap `n_{4q-1}` | negative full twist and curl |
| `isoStRd i` | `morseDouble [n_{i-1}]` | negative full twist and curl |
| `isoStFinal` | `u2 −3 n2 n2 n1` | negative left curl |

Here `walkL q (r - 1) = morseWalkL true q (r - 1)` is one round of the conveyor (the top strand
moves to the left under the other `r - 1`). Every normal form was checked outside Lean
(`SCR/ISO/tools/nf*.py`, `c2checks.py`): equal Kauffman-bracket operators at thickness one (and
two where feasible) and the same arcs with the same rotation numbers.
-/

namespace AJConjecture

/-- Normal form of `isoStLC i` (band coordinates): a doubled cup and a positive left curl. -/
def isoBLC (i : ℕ) : MorseWord :=
  morseShiftWord (2 * (i - 1)) (morseDouble [isoU 0] ++ isoCurlL true 1)

/-- Normal form of `isoStDec q`: a positive left curl. -/
def isoBDec (q : ℕ) : MorseWord := morseShiftWord (2 * (q - 1)) (isoCurlL true 1)

/-- Normal form of `isoStInc q`: negative full twist and negative left curl. -/
def isoBInc (q : ℕ) : MorseWord := morseShiftWord (2 * q) phaseTwoA1

/-- Normal form of `isoStR0 q r`: the doubled cup of the disc pair `T - r`, `T`, its left half
walking under `r - 1` bands, and a positive left curl. -/
def isoBR0 (q r : ℕ) : MorseWord :=
  morseDouble ([isoU (q + r - 1)] ++ morseWalkL true q (r - 1)) ++
    morseShiftWord (2 * q) (isoCurlL true 1)

/-- The Hopf hook (unchanged block `isoStHopf`, band coordinates). -/
def isoBHopf (q r : ℕ) : MorseWord :=
  morseShiftWord (2 * q + 2 * r - 1) [isoU 3, isoX true 2, isoX false 1, isoX false 2]

/-- Normal form of `isoStRound q r`: one doubled round of the conveyor and a positive left curl. -/
def isoBRound (q r : ℕ) : MorseWord :=
  morseDouble (morseWalkL true q (r - 1)) ++ morseShiftWord (2 * q) (isoCurlL true 1)

/-- Normal form of `isoStLast q r`: negative full twist and curl, the last doubled round, a doubled
cap. -/
def isoBLast (q r : ℕ) : MorseWord :=
  morseShiftWord (2 * (q - 1)) phaseTwoA1 ++
    morseDouble (morseWalkL true q (r - 1) ++ [isoN (q - 1)])

/-- Normal form of `isoStTrc q`: negative full twist and curl, and an inner cap. -/
def isoBTrc (q : ℕ) : MorseWord := morseShiftWord (4 * q - 2) phaseTwoA1 ++ [isoN (4 * q - 1)]

/-- Normal form of `isoStRd i`: negative full twist and curl, a doubled cap. -/
def isoBRd (i : ℕ) : MorseWord :=
  morseShiftWord (2 * (i - 1)) phaseTwoA1 ++ morseDouble [isoN (i - 1)]

/-- Normal form of `isoStFinal`: a negative left curl and two caps. -/
def isoFinalNF : MorseWord := [isoU 2, isoX false 3, isoN 2, isoN 2, isoN 1]

/-- The band region of the normal form (band coordinates). -/
def pairBandMid (r s : ℕ) : MorseWord :=
  (List.range (r - 2 - 1)).flatMap (fun i ↦ isoBLC (i + 1)) ++ isoBLC (r - 2) ++
    phaseTwoBlk (isoBDec (r - 2)) (pairRunDown r s - 1) ++
    phaseTwoBlk (isoBInc (r - 2)) (pairRunUp r s + 1) ++ isoBR0 (r - 2) r ++ isoBHopf (r - 2) r ++
    phaseTwoBlk (isoBRound (r - 2) r) (s - 2) ++ isoBLast (r - 2) r ++ isoBTrc (r - 2) ++
    (List.range (r - 2 - 1)).reverse.flatMap (fun i ↦ isoBRd (i + 1))

/-- The word after stage N: the strip with every block in normal form. -/
def pairWN (r s : ℕ) : MorseWord :=
  [isoU 1, isoX true 0] ++ morseShiftWord 1 (pairBandMid r s) ++ [isoX true 0, isoN 1] ++ isoFinalNF

end AJConjecture
