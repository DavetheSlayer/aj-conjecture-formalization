import Mathlib
import AJHandoff.TorusKnot.PairKIsoFenceDefs

/-!
# The strip word of `Wh⁻₀(T(r, s))` (r ≥ 3)

`pairStrip r s` is the fence word of `pairBlocks r s` in closed form (`isoFenceWord_pairBlocks`),
for `r ≥ 3`; put `q = r - 2`, `E = pairRunDown r s`, `z = pairRunUp r s`. Reading the blocks of
`pairBlocks` in order, each becomes one *strip block*: the cups of the discs it opens, its band,
the caps of the discs it closes, at positions that never exceed `4r + 3`:

| block of `pairBlocks` | strip block |
|---|---|
| left climb `b(0, T-1)` | `u1 +0` |
| left climbs `b(i, T-1-i)`, `1 ≤ i < q` | `isoStLC i` (two discs open, joined by a band) |
| first block of the decreasing run | `isoStLC q` |
| the other `E - 1` blocks of the decreasing run | `isoStDec q` |
| increasing run (`z` blocks) and big climb | `isoStInc q` (`z + 1` times) |
| round `0` | `isoStR0 q r` |
| first Hopf letter | `isoStHopf q r` |
| rounds `1, …, s - 2` | `isoStRound q r` |
| last round | `isoStLast q r` |
| top-right climb | `isoStTrc q` |
| right descents `j < q - 1` | `isoStRd i`, `i = q - 1, …, 1` |
| right descent to the disc `0` | `+0 n1` |
| second Hopf letter | `isoStFinal` |

Checked outside Lean (`SCR/ISO/tools/lean_words.py`): equal to the generic fence word for
`(r, s) ∈ {(3,4), (3,5), (4,5), (3,7), (4,7), (5,6), (5,7)}`, with the writhe `2(r-1)s - 2`, the
rotation number `-2(r-1)s` and the Jones polynomial of the long closure of `pairWhiteheadWord`.
-/

namespace AJConjecture

/-- A left-climb block `b(i, T-1-i)`, `1 ≤ i`, and the first block of the decreasing run (`i = q`):
two discs open at `2i - 1`, `2i + 1`, joined by a band. -/
def isoStLC (i : ℕ) : MorseWord :=
  [isoU (2 * i - 1), isoU (2 * i + 1)] ++ isoBand (2 * i - 1) (2 * i + 1) true

/-- A block of the decreasing run (after the first). -/
def isoStDec (q : ℕ) : MorseWord :=
  [isoU (2 * q - 1)] ++ isoBand (2 * q - 1) (2 * q + 1) true ++ [isoN (2 * q + 1)]

/-- A block of the increasing run, and the big climb. -/
def isoStInc (q : ℕ) : MorseWord :=
  [isoU (2 * q + 3)] ++ isoBand (2 * q + 1) (2 * q + 3) true ++ [isoN (2 * q + 1)]

/-- Round `0`: the discs `T - r` and `T` open, joined by a band passing `r - 1` discs. -/
def isoStR0 (q r : ℕ) : MorseWord :=
  [isoU (2 * q + 1), isoU (2 * q + 1 + 2 * r)] ++ isoBand (2 * q + 1) (2 * q + 1 + 2 * r) true

/-- The first Hopf letter: the Hopf disc opens next to the disc `T`. -/
def isoStHopf (q r : ℕ) : MorseWord :=
  [isoU (2 * q + 3 + 2 * r)] ++ isoBand (2 * q + 1 + 2 * r) (2 * q + 3 + 2 * r) false

/-- A round `1 ≤ t ≤ s - 2`: the top disc of the conveyor drops below the other `r - 1`. -/
def isoStRound (q r : ℕ) : MorseWord :=
  [isoU (2 * q + 1)] ++ isoBand (2 * q + 1) (2 * q + 1 + 2 * r) true ++ [isoN (2 * q + 1 + 2 * r)]

/-- The last round: two discs close. -/
def isoStLast (q r : ℕ) : MorseWord :=
  isoBand (2 * q - 1) (2 * q - 1 + 2 * r) true ++ [isoN (2 * q - 1 + 2 * r), isoN (2 * q - 1)]

/-- The top-right climb. -/
def isoStTrc (q : ℕ) : MorseWord := isoBand (4 * q - 1) (4 * q + 1) true ++ [isoN (4 * q - 1)]

/-- A right descent to the disc `i ≥ 1`: two discs close. -/
def isoStRd (i : ℕ) : MorseWord :=
  isoBand (2 * i - 1) (2 * i + 1) true ++ [isoN (2 * i + 1), isoN (2 * i - 1)]

/-- The right descent to the disc `0`. -/
def isoStRd0 : MorseWord := [isoX true 0, isoN 1]

/-- The second Hopf letter with the last two caps. -/
def isoStFinal : MorseWord := isoBand 1 3 false ++ [isoN 3, isoN 1]

/-- The strip word of `Wh⁻₀(T(r, s))`, `r ≥ 3`. -/
def pairStrip (r s : ℕ) : MorseWord :=
  [isoU 1, isoX true 0] ++ (List.range (r - 2 - 1)).flatMap (fun i ↦ isoStLC (i + 1)) ++
    isoStLC (r - 2) ++ phaseTwoBlk (isoStDec (r - 2)) (pairRunDown r s - 1) ++
    phaseTwoBlk (isoStInc (r - 2)) (pairRunUp r s + 1) ++ isoStR0 (r - 2) r ++
    isoStHopf (r - 2) r ++ phaseTwoBlk (isoStRound (r - 2) r) (s - 2) ++ isoStLast (r - 2) r ++
    isoStTrc (r - 2) ++ (List.range (r - 2 - 1)).reverse.flatMap (fun i ↦ isoStRd (i + 1)) ++
    isoStRd0 ++ isoStFinal

end AJConjecture
