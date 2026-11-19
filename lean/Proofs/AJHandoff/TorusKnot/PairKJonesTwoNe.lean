import Mathlib
import AJHandoff.TorusKnot.PairKDistinct
import AJHandoff.TorusQuantum.PairQTorusInputProof

/-!
# Distinct colour-2 coloured Jones polynomials

`coloredJones_two_pairWhiteheadKnot_ne`: for different admissible pairs the colour-2 coloured
Jones polynomials of the closed braids `pairWhiteheadKnot r s h` differ. This is the step inside
`pairWhiteheadKnot_not_markovEquiv` (`PairKDistinct`), stated on its own and with the companion
input discharged by `pairQ_torusInput`. Together with the isotopy invariance of the coloured Jones
polynomial (not formalized), it gives distinct knot types without Markov's theorem.
-/

namespace AJConjecture

/-- Different admissible pairs give different colour-2 coloured Jones polynomials. -/
theorem coloredJones_two_pairWhiteheadKnot_ne {r s r' s' : ℕ} (h : IsTorusPair r s)
    (h' : IsTorusPair r' s') (hne : (r, s) ≠ (r', s')) :
    coloredJones (pairWhiteheadKnot r s h) 2 ≠ coloredJones (pairWhiteheadKnot r' s' h') 2 := by
  intro heq
  have h2 := congrArg laurentToField heq
  rw [coloredJones_two_pairWhiteheadKnot h (pairQ_torusInput r s h),
    coloredJones_two_pairWhiteheadKnot h' (pairQ_torusInput r' s' h')] at h2
  obtain ⟨rfl, rfl⟩ := pairQFormula_two_injective h h' h2
  exact hne rfl

end AJConjecture
