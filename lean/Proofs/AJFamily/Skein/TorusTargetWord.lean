import Mathlib
import AJConjecture.SkeinMorseBraid
import AJConjecture.SkeinUFormClasp
import AJFamily.Skein.TorusKnot

/-!
# The target word

`torusTargetWord k`: the band-and-clasp diagram of `Wh⁻₀(T(2, 2k+1))` as a Morse word, the end
point of the isotopy.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The band-and-clasp diagram of `Wh⁻₀(T(2, 2k+1))` cut open on one edge of the band: closing
cups, the blackboard double of `σ_0^(2k+1)`, the caps of the second copy, `2(2k+1)` negative
crossings of the two edges, the clasp, the last cap. -/
def torusTargetWord (k : ℕ) : MorseWord :=
  [(.cup, 1), (.cup, 2), (.cup, 3)] ++ morseOfBraid (cable 2 (torusWord k)) ++
    [(.cap, 3), (.cap, 2)] ++ List.replicate (2 * (2 * k + 1)) (.cross false, 0) ++ claspWord ++
      [(.cap, 1)]

end AJConjecture
