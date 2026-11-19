import Mathlib
import AJFamily.Classical.JonesMarkov
import AJHandoff.TorusKnot.PairKJonesTwo
import AJHandoff.TorusKnot.PairKLongKnot
import AJHandoff.TorusQuantum.PairQTorusInput

/-!
# T-DIST (a): the knots are pairwise not Markov equivalent

The colour-2 coloured Jones polynomial is invariant under Markov moves
(`coloredJones_two_eq_of_markovEquiv`). By T-JONES (package P1, `pairQ_coloredJones_of_
longKnotOp_torusPair`, applied to the long-knot identity and the writhe of T-KNOT) the colour-2
value of `Wh⁻₀(T(r, s))` is `pairQFormula (pairQOddColor r s) 2`, which determines `(r, s)`
(`pairQFormula_two_injective`). So different admissible pairs give closed braids that are not
Markov equivalent; by Markov's theorem (not formalized, the same reading as in Theorem F) they
are different oriented knot types. The colour-2 value needs the companion only at colours `1`
and `3`; it enters through the odd-colour input `PairQTorusInput r s h` of P1 (its crux for
`r ≥ 3`), taken here as a hypothesis.
-/

namespace AJConjecture

/-- The colour-2 coloured Jones polynomial of `Wh⁻₀(T(r, s))`, given the companion input. -/
theorem coloredJones_two_pairWhiteheadKnot {r s : ℕ} (h : IsTorusPair r s)
    (hT : PairQTorusInput r s h) :
    laurentToField (coloredJones (pairWhiteheadKnot r s h) 2) =
      pairQFormula (pairQOddColor r s) 2 :=
  pairQ_coloredJones_of_longKnotOp_torusPair hT _ (longKnotOp_pairWhiteheadKnot h)
    (writhe_pairWhiteheadKnot h) 2

/-- T-DIST (a): different admissible pairs give closed braids that are not Markov
equivalent. -/
theorem pairWhiteheadKnot_not_markovEquiv {r s r' s' : ℕ} (h : IsTorusPair r s)
    (h' : IsTorusPair r' s') (hT : PairQTorusInput r s h) (hT' : PairQTorusInput r' s' h')
    (hne : (r, s) ≠ (r', s')) :
    ¬ MarkovEquiv (pairWhiteheadKnot r s h) (pairWhiteheadKnot r' s' h') := by
  intro hM
  have h2 := congrArg laurentToField (coloredJones_two_eq_of_markovEquiv hM)
  rw [coloredJones_two_pairWhiteheadKnot h hT, coloredJones_two_pairWhiteheadKnot h' hT'] at h2
  obtain ⟨rfl, rfl⟩ := pairQFormula_two_injective h h' h2
  exact hne rfl

/-- The new range `r = 3` alone is infinite: the pairs `(3, 3j + 1)`, `j ≥ 1`, are admissible
and pairwise different. -/
theorem isTorusPair_three (j : ℕ) (hj : 1 ≤ j) : IsTorusPair 3 (3 * j + 1) := by
  refine ⟨by norm_num, by omega, ?_⟩
  rw [Nat.coprime_mul_left_add_right]
  exact Nat.coprime_one_right 3

end AJConjecture
