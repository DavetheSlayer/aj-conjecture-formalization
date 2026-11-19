import Mathlib
import AJConjecture.SkeinMorseWord

/-!
# The strip word

`stripWord k = P A^(2k-1) M B^(2k-1) Q`, a narrow periodic Morse word with `2k - 1` stabilisation
blocks `A` and `2k - 1` staircase blocks `B`. It is the end point of phase I and the starting point
of phase II of the isotopy.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The head of the strip word. -/
def stripP : MorseWord := [(.cup, 1), (.cross true, 0)]

/-- The stabilisation block (one per small climb level). -/
def stripA : MorseWord :=
  [(.cup, 3), (.cross true, 2), (.cross true, 1), (.cross false, 2), (.cap, 1)]

/-- The middle block (big climb, top level, Hopf band). -/
def stripM : MorseWord :=
  [(.cup, 3), (.cross true, 2), (.cross true, 1), (.cup, 2), (.cross false, 2), (.cross false, 3),
    (.cross false, 4), (.cup, 7), (.cross true, 6), (.cross false, 5), (.cross false, 6),
    (.cross true, 2), (.cross true, 1)]

/-- The staircase block. -/
def stripB : MorseWord :=
  [(.cup, 2), (.cross false, 2), (.cross false, 3), (.cross false, 4), (.cap, 5),
    (.cross true, 2), (.cross true, 1)]

/-- The tail of the strip word (last crossing, final climb, closing caps). -/
def stripQ : MorseWord :=
  [(.cross true, 0), (.cross false, 1), (.cross false, 2), (.cap, 3), (.cross true, 2),
    (.cross true, 1), (.cross false, 2), (.cap, 1), (.cross true, 2), (.cap, 2), (.cap, 1)]

/-- The strip word `P A^(2k-1) M B^(2k-1) Q`. -/
def stripWord (k : ℕ) : MorseWord :=
  stripP ++ (List.replicate (2 * k - 1) stripA).flatten ++ stripM ++
    (List.replicate (2 * k - 1) stripB).flatten ++ stripQ

end AJConjecture
