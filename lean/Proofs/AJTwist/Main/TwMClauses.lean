import Mathlib
import AJConjecture.AJStatement
import AJConjecture.ExtraFactorPrime
import AJConjecture.RadicalObstruction
import AJConjecture.RecurrencePolynomialExists
import AJHandoff.TorusKnot.PairKTheoremT
import AJHandoff.TorusKnot.PairKMirrorRobust
import AJTwist.Classical.TwCClauses

/-!
# The clauses of the four-family theorem for one knot (Unit M3)

Source: revision 5, Theorem 1.1 (`introduction.tex`, Theorem "Both clasp signs and all integer
twists"): for the marked satellite `S`, "the actual signed rationally saturated annihilator is
nonzero; `0 ≠ f_S = α_S(-1, M, L)`, `G ∣ f_S`, `gcd_R(G, A_S) = 1` …, and `G` is irreducible in
`R`. In each case the localized square-free AJ assertion fails."

* `TwFamilyClauses K G P`: the clauses of `PairTClauses` (`AJHandoff.TorusKnot.PairKTheoremT`)
  for a knot `K`, with the obstruction factor `G` and the classical bound `P` as parameters:
  1. the localized annihilator of the coloured Jones function is nonzero;
  2. a recurrence polynomial `α` (primitive, of minimal order) exists;
  3. `G` divides the nonzero specialization of every nonzero primitive element of the localized
     annihilator (in particular of `α`);
  4. an A-polynomial exists;
  5. every A-polynomial divides `P` and is coprime to `G` in `ℚ(M)[L, L⁻¹]`;
  6. the localized square-free `SL₂` AJ statement fails for `K`.
  `PairTClauses K m` is `TwFamilyClauses K extraFactor (famBound m)` by definition.
* `prime_toComparison_extraFactorMirror`: `E^∨` is prime in `ℚ(M)[L, L⁻¹]` (the image of the
  prime `E` under the automorphism `L ↦ L⁻¹`, times the unit `L²`).
* `twFamilyClauses_of`: the clauses follow from a prime `G`, a nonzero localized annihilator,
  the survival of `G` (clause 3) and the classical clauses `TwClassClauses K G P` (4 and 5):
  clause 2 is `exists_isRecurrencePolynomial`, and clause 6 is
  `radical_span_singleton_ne_of_prime_dvd` (a prime dividing `f_K` and not `A_K`).

This file has no `sorry`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The clauses of the four-family theorem for one knot `K`, with obstruction factor `G` and
classical bound `P`. -/
def TwFamilyClauses (K : BraidKnot) (G P : ℤ[X][X]) : Prop :=
  (∃ Q : RecOp, Q ≠ 0 ∧ InLocalizedAnnihilator (coloredJones K) Q) ∧
    (∃ α : RecOp, IsRecurrencePolynomial (coloredJones K) α) ∧
    (∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
      specialize Q ≠ 0 ∧ toComparison G ∣ toComparison (specialize Q)) ∧
    (∃ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A) ∧
    (∀ A : ℤ[X][X], IsAPolynomialOf (eigenvalueSet K) A →
      toComparison A ∣ toComparison P ∧ IsCoprime (toComparison G) (toComparison A)) ∧
    ¬ AJSquareFree K

/-- The clauses of Theorem T are the clauses of the four-family theorem with `G = E` and the
bound `(L - 1) B_m`. -/
theorem pairTClauses_iff_twFamilyClauses (K : BraidKnot) (m : ℕ) :
    PairTClauses K m ↔ TwFamilyClauses K extraFactor (famBound m) :=
  Iff.rfl

/-- `E^∨ = M⁴ L² - (M⁴ - 4M² + 1) L + 1` is prime in the comparison ring `ℚ(M)[L, L⁻¹]`. -/
theorem prime_toComparison_extraFactorMirror : Prime (toComparison extraFactorMirror) := by
  rw [toComparison_extraFactorMirror]
  have hp : Prime (LaurentPolynomial.invert (toComparison extraFactor)) :=
    (MulEquiv.prime_iff LaurentPolynomial.invert).mpr prime_toComparison_extraFactor
  exact (associated_unit_mul_left _ _ (LaurentPolynomial.isUnit_T 2)).symm.prime hp

/-- **Assembly for one knot**: a prime factor `G` surviving in every primitive element of a
nonzero localized annihilator, together with the classical clauses for `G` and a bound `P`,
gives all clauses; in particular the localized square-free AJ statement fails. -/
theorem twFamilyClauses_of {K : BraidKnot} {G P : ℤ[X][X]} (hG : Prime (toComparison G))
    (hex : ∃ Q : RecOp, Q ≠ 0 ∧ InLocalizedAnnihilator (coloredJones K) Q)
    (hsurv : ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
      specialize Q ≠ 0 ∧ toComparison G ∣ toComparison (specialize Q))
    (hclass : TwClassClauses K G P) : TwFamilyClauses K G P := by
  obtain ⟨α, hα⟩ := exists_isRecurrencePolynomial hex
  refine ⟨hex, ⟨α, hα⟩, hsurv, hclass.1, hclass.2, fun hAJ ↦ ?_⟩
  obtain ⟨A, hA⟩ := hclass.1
  have hGα : toComparison G ∣ toComparison (specialize α) :=
    (hsurv α hα.1 hα.2.2.2 hα.2.1).2
  have hnd : ¬ toComparison G ∣ toComparison A := fun hd ↦
    hG.not_isUnit ((hclass.2 A hA).2.isUnit_of_dvd' dvd_rfl hd)
  exact radical_span_singleton_ne_of_prime_dvd hG hGα hnd (hAJ α hα A hA)

end AJConjecture
