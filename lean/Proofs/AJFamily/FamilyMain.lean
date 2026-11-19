import Mathlib
import AJFamily.Assembly.ConditionalCounterexample
import AJFamily.Classical.APolynomialWitness
import AJFamily.Classical.FamilyPeripheral
import AJFamily.Classical.JonesMarkov
import AJFamily.Quantum.TorusAnnihilatorExists
import AJFamily.Quantum.TorusExtraFactorDvd
import AJFamily.Skein.TorusJonesDistinct

/-!
# Infinitely many counterexamples with the same extra factor

There are infinitely many braid knots, pairwise not Markov equivalent, for which the localized
square-free `SL₂` AJ conjecture fails; for each of them the extra factor
`E = L² - (M⁴ - 4M² + 1) L + M⁴` divides the nonzero specialisation at `t = -1` of every nonzero
primitive element of the localized annihilator of the coloured Jones function, and is coprime
to every A-polynomial. The knots are the untwisted negative-clasp Whitehead doubles
`Wh(T(2, 2k+1))`, `k ≥ 1`, of the right-handed torus knots.
-/

open Polynomial

namespace AJConjecture

/-- Each knot of the family, the braid closure `whiteheadTorusKnot k` (`k ≥ 1`, the braided
Seifert-surface presentation of the untwisted negative-clasp Whitehead double of `T(2, 2k+1)`), is
a counterexample: the localized square-free `SL₂` AJ conjecture fails, the extra factor `E` divides
the nonzero specialisation of every nonzero primitive annihilator, and `E` is coprime to every
A-polynomial. -/
theorem whiteheadTorusKnot_counterexample (k : ℕ) (hk : 1 ≤ k) :
    ¬ AJSquareFree (whiteheadTorusKnot k hk) ∧
      (∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive →
        InLocalizedAnnihilator (coloredJones (whiteheadTorusKnot k hk)) Q →
          specialize Q ≠ 0 ∧ toComparison extraFactor ∣ toComparison (specialize Q)) ∧
      ∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet (whiteheadTorusKnot k hk)) A →
        IsCoprime (toComparison extraFactor) (toComparison A) := by
  have hsat : SatellitePeripheral (whiteheadTorusKnot k hk) k :=
    satellitePeripheral_whiteheadTorusKnot k hk
  have ha : 3 ≤ 2 * k + 1 := by omega
  have hm : 0 < famDegree k := by unfold famDegree; omega
  obtain ⟨A, hA, -⟩ := exists_aPolynomial_not_extraFactor_dvd hsat
  exact conditional_counterexample (whiteheadTorusKnot k hk) (torusWhiteheadFormula (2 * k + 1))
    (laurentToField_coloredJones_whiteheadTorusKnot k hk)
    (exists_annihilator_torusWhiteheadFormula (2 * k + 1) ha)
    (fun Q hQ hann ↦
      extraFactor_dvd_specialize_of_annihilates_torusWhiteheadFormula (2 * k + 1) ha hQ hann)
    (famBound (famDegree k))
    (fun p hp ↦ evalPoint_famBound_of_mem_eigenvalueSet hsat hp)
    (exists_extraFactor_zero_not_famBound_zero hm)
    ⟨A, hA⟩

/-- The family knots are pairwise not Markov equivalent: their coloured Jones polynomials at
colour 2, which are invariant under Markov moves, differ. -/
theorem whiteheadTorusKnot_pairwise_not_markovEquiv :
    Pairwise fun i j : ℕ ↦ ¬ MarkovEquiv (whiteheadTorusKnot (i + 1) (Nat.le_add_left 1 i))
      (whiteheadTorusKnot (j + 1) (Nat.le_add_left 1 j)) := by
  refine pairwise_not_markovEquiv_of_injective
    (fun n ↦ whiteheadTorusKnot (n + 1) (Nat.le_add_left 1 n)) fun i j h ↦ ?_
  have := coloredJones_two_whiteheadTorusKnot_injective (i + 1) (j + 1) _ _
    (congrArg laurentToField h)
  omega

/-- Infinitely many counterexamples to the localized square-free `SL₂` AJ conjecture, with the
extra factor `E` in every primitive annihilator and coprime to every A-polynomial. -/
theorem infinitely_many_counterexamples :
    ∃ K : ℕ → BraidKnot, (Pairwise fun i j ↦ ¬ MarkovEquiv (K i) (K j)) ∧ ∀ n,
        ¬ AJSquareFree (K n) ∧
        (∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones (K n)) Q →
          specialize Q ≠ 0 ∧ toComparison extraFactor ∣ toComparison (specialize Q)) ∧
        ∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet (K n)) A →
          IsCoprime (toComparison extraFactor) (toComparison A) :=
  ⟨fun n ↦ whiteheadTorusKnot (n + 1) (Nat.le_add_left 1 n),
    whiteheadTorusKnot_pairwise_not_markovEquiv,
    fun n ↦ whiteheadTorusKnot_counterexample (n + 1) (Nat.le_add_left 1 n)⟩

end AJConjecture
