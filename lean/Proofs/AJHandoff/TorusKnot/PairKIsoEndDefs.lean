import Mathlib
import AJHandoff.TorusKnot.PairKIsoPlumbDefs
import AJHandoff.TorusKnot.PairKIsoBeadDefs

/-!
# Stages C, G, E: the junction words

After stage P the band is `morseDouble (pairCore r s)` carrying beads: `C` negative full twists
(`C = (r-1)s`), `C - 1` positive and `C - 1` negative curls on its edges, and the conjugated clasp
`C_S = isoClaspS` on the right strand (after `pairCoreHead`), which the core traverses downwards.
The junction words of the end game:

* `pairWC`: all curls cancelled, all twists at the bottom end of the band, the clasp in place;
* `pairWG1`: the clasp moved forward along the knot to the top end. The trace of the core from the
  clasp to the top end makes an **odd** number of turns (1, 3, 5, 7 for the pairs checked, e.g.
  3 for `(3,4)`; `SCR/ISO2/tools/parity.py`), so the clasp arrives rotated by `π`:
  `isoClaspU = isoRot 2 isoClaspS = +0 · claspWord · −0`;
* `pairWG2`: the twists moved to the top end, in front of the clasp;
* `pairWE1 … pairWE5`: stage E, exactly as stage E of the library
  (`AJFamily.Skein.TorusPhaseTwoFinish` for `r = 2`, whose stage G also ends with
  `+0 · claspWord · −0`): macro `E1` of the library turns
  the window into two opposite curls `c₁ = u1 −2 n1` (between the last two half twists) and
  `c₂ = u2 +3 n2` (inside the clasp); `c₂` goes to the return strand (`ToR1`), down to the first
  cup, around it (`CUPL`), along the whole knot, past the `2C - 1` half twists (`PastPair`,
  `PastOdd`) and cancels `c₁` at the clasp (`Cancel`, one `kink`);
* `pairWE`: the target word with the core `pairCore r s` in place of the doubled long closure of
  the torus braid.

Validated (`SCR/ISO2/tools/endgame.py`): for `(3,4), (3,5), (4,5), (5,6), (3,7)` every word has
the Kauffman bracket (thickness one) and writhe `2C - 2` of `pairWC`; rotation numbers `2` up to
`pairWE5`, `0` for `pairWE`; Lean `#eval` agrees with Python.
-/

namespace AJConjecture

/-- The clasp read on an upward band: `+0 · claspWord · −0` (`= isoRot 2 isoClaspS`). -/
def isoClaspU : MorseWord := [isoX true 0] ++ claspWord ++ [isoX false 0]

/-- All curls cancelled, the twists at the bottom end, the clasp on the band of the disc `T`. -/
def pairWC (r s : ℕ) : MorseWord :=
  [isoU 1] ++ List.replicate (2 * ((r - 1) * s)) (isoX false 0) ++ morseDouble (pairCoreHead r) ++
    morseShiftWord (2 * (2 * r - 2)) isoClaspS ++ morseDouble (pairCoreTail r s) ++ [isoN 1]

/-- The clasp at the top end (rotated by `π`: an odd number of turns). -/
def pairWG1 (r s : ℕ) : MorseWord :=
  [isoU 1] ++ List.replicate (2 * ((r - 1) * s)) (isoX false 0) ++ morseDouble (pairCore r s) ++
    isoClaspU ++ [isoN 1]

/-- The twists in front of the clasp at the top end. -/
def pairWG2 (r s : ℕ) : MorseWord :=
  [isoU 1] ++ morseDouble (pairCore r s) ++ List.replicate (2 * ((r - 1) * s)) (isoX false 0) ++
    isoClaspU ++ [isoN 1]

/-- The left side of macro `E1` (window: the last two half twists, the clasp `isoClaspU`, the last
cap); it is `phaseTwoMacroE1_lhs` of the library. -/
def isoE1L : MorseWord := [isoX false 0, isoX false 0] ++ isoClaspU ++ [isoN 1]

/-- The right side of macro `E1`: `c₁ = u1 −2 n1` between the two half twists, `c₂ = u2 +3 n2` on
the left leg of the cup of the clasp; it is `phaseTwoMacroE1_rhs` of the library. -/
def isoE1R : MorseWord :=
  [isoX false 0] ++ isoCurlL false 1 ++ [isoX false 0, isoU 2] ++ isoCurlL true 2 ++
    [isoX true 1, isoX true 1, isoN 0, isoN 1]

/-- After macro `E1`. -/
def pairWE1 (r s : ℕ) : MorseWord :=
  [isoU 1] ++ morseDouble (pairCore r s) ++ List.replicate (2 * ((r - 1) * s) - 2) (isoX false 0) ++
    isoE1R

/-- The curl `c₂` on the return strand above the half twists (macro `ToR1`). -/
def pairWE2 (r s : ℕ) : MorseWord :=
  [isoU 1] ++ morseDouble (pairCore r s) ++ List.replicate (2 * ((r - 1) * s) - 1) (isoX false 0) ++
    isoCurlL true 2 ++ isoCurlL false 1 ++ [isoX false 0] ++ claspWord ++ [isoN 1]

/-- The curl `c₂` down the return strand and around the first cup onto the right edge. -/
def pairWE3 (r s : ℕ) : MorseWord :=
  [isoU 1] ++ isoCurlR true 1 ++ morseDouble (pairCore r s) ++
    List.replicate (2 * ((r - 1) * s) - 1) (isoX false 0) ++ isoCurlL false 1 ++ [isoX false 0] ++
    claspWord ++ [isoN 1]

/-- The curl `c₂` at the top end of the band. -/
def pairWE4 (r s : ℕ) : MorseWord :=
  [isoU 1] ++ morseDouble (pairCore r s) ++ isoCurlR true 1 ++
    List.replicate (2 * ((r - 1) * s) - 1) (isoX false 0) ++ isoCurlL false 1 ++ [isoX false 0] ++
    claspWord ++ [isoN 1]

/-- The curl `c₂` past the half twists, next to `c₁`. -/
def pairWE5 (r s : ℕ) : MorseWord :=
  [isoU 1] ++ morseDouble (pairCore r s) ++ List.replicate (2 * ((r - 1) * s) - 1) (isoX false 0) ++
    isoCurlR true 0 ++ isoCurlL false 1 ++ [isoX false 0] ++ claspWord ++ [isoN 1]

/-- The target word with the core in place of the doubled torus closure. -/
def pairWE (r s : ℕ) : MorseWord :=
  [isoU 1] ++ morseDouble (pairCore r s) ++ List.replicate (2 * ((r - 1) * s)) (isoX false 0) ++
    claspWord ++ [isoN 1]

end AJConjecture
