import Mathlib
import AJHandoff.LocalTheory.LocFamilyMinimalOrder
import AJHandoff.TorusKnot.PairKReverse
import AJFamily.Quantum.TwistPolyPrime
import AJTwist.Main.TwMTheorem
import AJPaper.Finger.PpFAlgebra

/-!
# The trefoil test: `Δ_S ≐ E` (Unit PpF, node `PpF_Trefoil`)

Source: Section 9 of the paper, proof of Corollary 9.2: "For the untwisted right-handed trefoil
example, Theorem A.1 gives `𝖫(f_S) ≐ (L - 1) B_6 E` and `A_S ≐ (L - 1) B_6`, so `Δ_S ≐ E`. This
single test bounds the common divisor from above."

The test knot is `S = Z(T(2, 3)) = twFamilyKnot 2 3 h true true 0`, which is the library's
`whiteheadTorusKnot 1` (`whiteheadTorusKnot_one_eq_twFamilyKnot`: `pairWhiteheadWord_two`,
`pairStrands_two`, `twFamilyWord_untwisted`, `eq_twFamilyKnot_of_word`).

* `ppf_trefoil_specialize`: every recurrence polynomial has `f_S ≐ (L - 1)² E B_6`
  (`minimalRecurrence_whiteheadTorusKnot 1`).
* `ppf_trefoil_aPolynomial`: every A-polynomial has `A_S ≐ (L - 1) B_6`
  (`aPolynomial_pair_associated_famBound`, `famB_eq_twistPoly`, `twFamilyKnot_untwisted`).
* `ppf_isExtraSupport_trefoil_model`: `Δ = E` for `f = (L - 1)² E B_6`, `A = (L - 1) B_6`
  (`isExtraSupport_of_three_primes` with the primes `L - 1`, `E`, `B_6` of `R`:
  `prime_toComparison_X_sub_one`, `prime_toComparison_extraFactor`,
  `prime_toComparison_twistPoly`; pairwise non-associated by
  `isCoprime_extraFactor_twBound 0 6` and `B_6(M, 1) ≠ 0`, `eval_one_twistPoly`).
* `ppf_isExtraSupportOf_trefoil`: `E` is an extra support `Δ_S` of the test knot.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The untwisted negative-clasp double of the right-handed trefoil is the knot `W_1` of
Theorem A.1. -/
theorem whiteheadTorusKnot_one_eq_twFamilyKnot (h : IsTorusPair 2 3) :
    whiteheadTorusKnot 1 le_rfl = twFamilyKnot 2 3 h true true 0 :=
  eq_twFamilyKnot_of_word h true true 0
    ((twFamilyWord_untwisted h).1.trans (pairStrands_two 1)).symm
    ((twFamilyWord_untwisted h).2.trans (pairWhiteheadWord_two 1 le_rfl)).symm

/-- Theorem A.1 for the test knot: `f_S ≐ (L - 1)² E B_6`. -/
theorem ppf_trefoil_specialize (h : IsTorusPair 2 3) {α : RecOp}
    (hα : IsRecurrencePolynomial (coloredJones (twFamilyKnot 2 3 h true true 0)) α) :
    Associated (toComparison (specialize α))
      (toComparison ((X - 1) ^ 2 * extraFactor * twistPoly 6)) := by
  rw [← whiteheadTorusKnot_one_eq_twFamilyKnot h] at hα
  exact (isRecurrencePolynomial_whiteheadTorusKnot_one.2 α hα).2

/-- The classical equality for the test knot: `A_S ≐ (L - 1) B_6`. -/
theorem ppf_trefoil_aPolynomial (h : IsTorusPair 2 3) {A : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet (twFamilyKnot 2 3 h true true 0)) A) :
    Associated (toComparison A) (toComparison ((X - 1) * twistPoly 6)) := by
  rw [(twFamilyKnot_untwisted h).1] at hA
  have hassoc := aPolynomial_pair_associated_famBound h hA
  rwa [famBound, famB_eq_twistPoly (2 * 3) (by norm_num)] at hassoc

/-- In the comparison ring `L - 1` does not divide `B_6`: `B_6(M, 1) ≠ 0`. -/
private theorem not_toComparison_X_sub_one_dvd_twistPoly_six_ppfTrefoil :
    ¬ toComparison (X - 1) ∣ toComparison (twistPoly 6) := by
  intro hdvd
  have hev := eval_one_eq_zero_of_toComparison_X_sub_one_dvd hdvd
  rw [eval_one_twistPoly (by norm_num)] at hev
  have h0 := congrArg (Polynomial.eval 1) hev
  norm_num at h0

/-- In the comparison ring `E` is coprime to `L - 1` and to `B_6`. -/
private theorem isCoprime_extraFactor_trefoil_ppfTrefoil :
    IsCoprime (toComparison extraFactor) (toComparison (X - 1)) ∧
      IsCoprime (toComparison extraFactor) (toComparison (twistPoly 6)) := by
  have hco := isCoprime_extraFactor_twBound 0 6
  rw [twBound, twP_zero, mul_one, show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, twP_natCast,
    map_mul] at hco
  exact ⟨hco.of_mul_right_left, hco.of_mul_right_right⟩

/-- The model computation of the trefoil test in `ℚ(M)[L, L⁻¹]`. -/
theorem ppf_isExtraSupport_trefoil_model :
    IsExtraSupport (toComparison ((X - 1) ^ 2 * extraFactor * twistPoly 6))
      (toComparison ((X - 1) * twistPoly 6)) (toComparison extraFactor) := by
  obtain ⟨hEl, hEB⟩ := isCoprime_extraFactor_trefoil_ppfTrefoil
  have hl := prime_toComparison_X_sub_one
  have hE := prime_toComparison_extraFactor
  refine isExtraSupport_of_three_primes hl hE (prime_toComparison_twistPoly 6 (by norm_num))
    (fun hd ↦ hl.not_isUnit (hEl.isUnit_of_dvd' hd dvd_rfl))
    not_toComparison_X_sub_one_dvd_twistPoly_six_ppfTrefoil
    (fun hd ↦ hE.not_isUnit (hEB.isUnit_of_dvd' dvd_rfl hd)) ?_ ?_
  · rw [map_mul, map_mul, map_pow]
  · rw [map_mul]

/-- **The trefoil test**: `Δ_S ≐ E` for `S = Z(T(2, 3))`. -/
theorem ppf_isExtraSupportOf_trefoil (h : IsTorusPair 2 3) :
    IsExtraSupportOf (twFamilyKnot 2 3 h true true 0) (toComparison extraFactor) := by
  have hc := twFamilyClauses_negClasp h true 0
  obtain ⟨α, hα⟩ := hc.2.1
  obtain ⟨A, hA⟩ := hc.2.2.2.1
  exact ⟨α, A, hα, hA, isExtraSupport_congr (ppf_trefoil_specialize h hα).symm
    (ppf_trefoil_aPolynomial h hA).symm (Associated.refl _) ppf_isExtraSupport_trefoil_model⟩

end AJConjecture
