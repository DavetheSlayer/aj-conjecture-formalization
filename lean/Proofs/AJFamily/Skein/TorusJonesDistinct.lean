import Mathlib
import AJFamily.Skein.TorusJonesInjective
import AJFamily.Skein.TorusSequenceIdentity

/-!
# The colour-2 Jones polynomials of the family are distinct

`coloredJones_two_whiteheadTorusKnot_injective`: the colour-2 coloured Jones polynomials of
`whiteheadTorusKnot i` and `whiteheadTorusKnot j` agree only if `i = j`. It combines the sequence
identity with `torusWhiteheadFormula_two_injective`, and is used in
`whiteheadTorusKnot_pairwise_not_markovEquiv`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

theorem coloredJones_two_whiteheadTorusKnot_injective (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (h : laurentToField (coloredJones (whiteheadTorusKnot i hi) 2) =
      laurentToField (coloredJones (whiteheadTorusKnot j hj) 2)) : i = j := by
  rw [laurentToField_coloredJones_whiteheadTorusKnot i hi 2,
    laurentToField_coloredJones_whiteheadTorusKnot j hj 2] at h
  have := torusWhiteheadFormula_two_injective (2 * i + 1) (2 * j + 1) (by omega) (by omega) h
  omega

end AJConjecture
