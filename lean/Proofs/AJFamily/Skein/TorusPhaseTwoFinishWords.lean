import Mathlib
import AJFamily.Skein.TorusPhaseTwoWords

/-!
# Stage E of phase II: the junction words

Closed forms of the words met by the travelling curl in stage E (see `TorusPhaseTwoFinish`).
-/

namespace AJConjecture

/-- `u1 u2 u3 · D^m`. -/
def phaseTwoEPre (m : ℕ) : MorseWord := [(.cup, 1), (.cup, 2), (.cup, 3)] ++ phaseTwoBlk phaseTwoD m

/-- The tail during the transport: closing caps, `4k + 1` negative half twists, `c₁`, the last
twist letter, the clasp, the last cap. -/
def phaseTwoETail (k : ℕ) : MorseWord :=
  [(.cap, 3), (.cap, 2)] ++ List.replicate (2 * (2 * k + 1) - 1) (.cross false, 0) ++
    [(.cup, 1), (.cross false, 2), (.cap, 1), (.cross false, 0)] ++ claspWord ++ [(.cap, 1)]

/-- After macro `E1`. -/
def phaseTwoE1 (k : ℕ) : MorseWord :=
  phaseTwoEPre (2 * k + 1) ++ [(.cap, 3), (.cap, 2)] ++
    List.replicate (2 * (2 * k + 1) - 1) (.cross false, 0) ++
    [(.cup, 1), (.cross false, 2), (.cap, 1), (.cross false, 0), (.cup, 2), (.cup, 2),
      (.cross true, 3), (.cap, 2), (.cross true, 1), (.cross true, 1), (.cap, 0), (.cap, 1)]

/-- The curl on the return strand, after `D^m`. -/
def phaseTwoER (k m : ℕ) : MorseWord :=
  phaseTwoEPre m ++ [(.cup, 6), (.cross true, 7), (.cap, 6)] ++
    phaseTwoBlk phaseTwoD (2 * k + 1 - m) ++ phaseTwoETail k

/-- The travelling curl on the strand `1` (`true`) or `3` (`false`). -/
def phaseTwoECurl (one : Bool) : MorseWord :=
  if one then [(.cup, 2), (.cross true, 1), (.cap, 2)] else [(.cup, 4), (.cross true, 3), (.cap, 4)]

/-- The curl on a pass of the band, after `D^m` (`s = true`: pass 1, starting on the strand `1`;
`s = false`: pass 2, starting on the strand `3`). -/
def phaseTwoEP (k m : ℕ) (s : Bool) : MorseWord :=
  phaseTwoEPre m ++ phaseTwoECurl (s == decide (m % 2 = 0)) ++
    phaseTwoBlk phaseTwoD (2 * k + 1 - m) ++ phaseTwoETail k

/-- The curl on the closing arc, after `D^m`. -/
def phaseTwoEA (k m : ℕ) : MorseWord :=
  phaseTwoEPre m ++ [(.cup, 4), (.cross true, 5), (.cap, 4)] ++
    phaseTwoBlk phaseTwoD (2 * k + 1 - m) ++ phaseTwoETail k

end AJConjecture
