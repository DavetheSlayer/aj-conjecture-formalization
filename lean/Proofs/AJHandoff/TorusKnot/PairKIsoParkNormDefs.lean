import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkDefs

/-!
# Stage C by ports: the words of the normalisation `pairWPb → pairParkW1`

`pairWPb` (the band after stage P with the inner cap moved next to the last cap) is the doubled
core with beads: the bottom block `t n`, a positive curl after each left cup (`isoBLC`), the
`E - 1` curls of the decreasing run and the `z + 1` blocks `t n` of the increasing run (on the
bands `q - 1`, `q`), the conjugated clasp after the first doubled crossing of round `0`, a curl
after every middle round, the block `t n` of the last round on the band `q - 1`, the twist `h`
on the output band `2q + 1` before the cap of the right arc, the blocks `t n` of the right
descents at the top of the left legs, and the top curl. The normalisation moves every bead to
a port, in three steps:

1. `pairParkV1`: the clasp, turned around the doubled cup of the right arc, and the twist `h`,
   carried around the cap of the right arc and down the right strand, sit at the port `r - 1`;
2. `pairParkV2`: the beads of every left leg slid down the leg and around its cup to the port of
   the arc (`p … t n` read upwards is `[ln, t] ++ lp^k` in the band frame of the port; one `kink`
   cancels `ln` against an `lp`), the increasing run joins the port `0`;
3. `pairParkW1`: the round curls ride the conveyor backwards to their ports
   (`morseReach_park_roundCurls`).

`pairParkWX` is the port word with an arbitrary middle in place of the doubled conveyor.
-/

namespace AJConjecture

/-- The band after stage P with the inner cap of the top-right climb moved next to the last cap:
the doubled core with beads. -/
def pairWPb (r s : ℕ) : MorseWord :=
  pairPlumbPre r s ++ morseShiftWord (4 * (r - 2)) isoWinR ++
    morseDouble (morseWalkL true (r - 2) (r - 2)) ++ phaseTwoBlk (isoBRound (r - 2) r) (s - 2) ++
    isoBLast (r - 2) r ++ morseShiftWord (4 * (r - 2) - 2) [isoX false 0, isoX false 0] ++
    morseDouble [isoN (2 * r - 5)] ++ pairPlumbRd r ++ [isoU 1, isoX true 2, isoN 1, isoN 1]

/-- The port word with an arbitrary middle `mid` in place of the doubled conveyor. -/
def pairParkWX (r : ℕ) (bot : List IsoBead) (S : ℕ → List IsoBead) (mid : MorseWord)
    (top : List IsoBead) : MorseWord :=
  [isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
    (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
    mid ++ morseDouble (pairCaps r) ++ isoBeadsWord top ++ [isoN 1]

/-- The port stacks without the round curls. -/
def pairParkS2 (r s a : ℕ) : List IsoBead :=
  if a = 0 then
      [.t] ++ List.replicate (pairRunDown r s - 1) .lp ++
        (List.replicate (pairRunUp r s + 1) [IsoBead.t, .n]).flatten
    else if a < r - 2 then [.t]
    else if a = r - 2 then []
    else [.t, .cs]

/-- One doubled round of the conveyor. -/
def pairDRound (r : ℕ) : MorseWord := morseDouble (morseWalkL true (r - 2) (r - 1))

/-- Step 1: the clasp and the twist `h` at the port `r - 1`. -/
def pairParkV1 (r s : ℕ) : MorseWord :=
  pairPlumbPre r s ++ morseDouble [isoU (2 * r - 3)] ++
    morseShiftWord (2 * (2 * r - 3)) (isoBeadsWord [.t, .cs]) ++ pairDRound r ++
    phaseTwoBlk (isoBRound (r - 2) r) (s - 2) ++ isoBLast (r - 2) r ++
    morseDouble [isoN (2 * r - 5)] ++ pairPlumbRd r ++ isoBeadsWord [.p] ++ [isoN 1]

/-- Step 2: every bead at a port except the round curls. -/
def pairParkV2 (r s : ℕ) : MorseWord :=
  pairParkWX r [.t, .n] (pairParkS2 r s)
    (pairDRound r ++
      phaseTwoBlk (pairDRound r ++ morseShiftWord (2 * (r - 2)) (isoBeadsWord [.p])) (s - 2) ++
      pairDRound r) [.p]

end AJConjecture
