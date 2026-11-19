import Mathlib
import AJConjecture.FieldActionBridge
import AJConjecture.RecurrencePolynomialExists
import AJConjecture.QAlgSpecializeNeZero
import AJConjecture.ColoredJones
import AJHandoff.TorusQuantum.PairQAnnihilator

/-!
# T-MIN: the recurrence ideal of a knot whose coloured Jones function is the formula

`pairQ_tmin_of_formula`: if the coloured Jones function of a braid knot `K` is a formula `f` that
has a nonzero annihilator and `E` in the specialization of every primitive annihilator, then, in
the baseline predicates: the localized annihilator of `coloredJones K` is nonzero, a recurrence
polynomial (`IsRecurrencePolynomial`, the primitive minimum) exists, and every nonzero primitive
`Q` in the localized annihilator has `specialize Q ≠ 0` and `E ∣ specialize Q` in
`ℚ(M)[L, L⁻¹]` — in particular every primitive minimum. The transfer from `ℤ[t,t⁻¹]`-valued
sequences to `ℚ(t)` is `laurentToField_opApply` and `laurentToField_injective` (as in
`conditional_counterexample`); existence of a minimum is `exists_isRecurrencePolynomial`;
nonvanishing is `specialize_ne_zero_of_isPrimitive`.

`pairQ_tmin`: the instance `f = pairQFormula (pairQOddColor r s)`, with the hypotheses supplied by
`pairQ_exists_annihilator` and `pairQ_extraFactor_dvd_specialize`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A localized annihilator of the coloured Jones function is one of any formula equal to it. -/
private theorem annihilates_field_of_inLocalizedAnnihilator_pairQ {K : BraidKnot}
    {f : ℤ → RatFunc ℚ} (hfun : (fun m ↦ laurentToField (coloredJones K m)) = f) {Q : RecOp}
    (hQ : InLocalizedAnnihilator (coloredJones K) Q) :
    ∃ c : Coeff, c ≠ 0 ∧ ∀ n : ℤ, opApplyField (Polynomial.C c * Q) f n = 0 := by
  obtain ⟨c, hc, hann⟩ := hQ
  refine ⟨c, hc, fun n ↦ ?_⟩
  have h := congrArg laurentToField (hann n)
  rwa [map_zero, laurentToField_opApply, hfun] at h

theorem pairQ_tmin_of_formula (K : BraidKnot) (f : ℤ → RatFunc ℚ)
    (hseq : ∀ n : ℤ, laurentToField (coloredJones K n) = f n)
    (hann : ∃ Q : RecOp, Q ≠ 0 ∧ ∃ c : Coeff, c ≠ 0 ∧
      ∀ n : ℤ, opApplyField (Polynomial.C c * Q) f n = 0)
    (hE : ∀ Q : RecOp, Q.IsPrimitive →
      (∃ c : Coeff, c ≠ 0 ∧ ∀ n : ℤ, opApplyField (Polynomial.C c * Q) f n = 0) →
        toComparison extraFactor ∣ toComparison (specialize Q)) :
    (∃ Q : RecOp, Q ≠ 0 ∧ InLocalizedAnnihilator (coloredJones K) Q) ∧
      (∃ α : RecOp, IsRecurrencePolynomial (coloredJones K) α) ∧
      ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
        specialize Q ≠ 0 ∧ toComparison extraFactor ∣ toComparison (specialize Q) := by
  have hfun : (fun m ↦ laurentToField (coloredJones K m)) = f := funext hseq
  have hex : ∃ Q : RecOp, Q ≠ 0 ∧ InLocalizedAnnihilator (coloredJones K) Q := by
    obtain ⟨Q, hQ, c, hc, hann⟩ := hann
    refine ⟨Q, hQ, c, hc, fun n ↦ laurentToField_injective ?_⟩
    rw [map_zero, laurentToField_opApply, hfun]
    exact hann n
  exact ⟨hex, exists_isRecurrencePolynomial hex, fun Q _ hprim hQ ↦
    ⟨specialize_ne_zero_of_isPrimitive hprim,
      hE Q hprim (annihilates_field_of_inLocalizedAnnihilator_pairQ hfun hQ)⟩⟩

theorem pairQ_tmin (r s : ℕ) (h : IsTorusPair r s) (K : BraidKnot)
    (hseq : ∀ n : ℤ, laurentToField (coloredJones K n) = pairQFormula (pairQOddColor r s) n) :
    (∃ Q : RecOp, Q ≠ 0 ∧ InLocalizedAnnihilator (coloredJones K) Q) ∧
      (∃ α : RecOp, IsRecurrencePolynomial (coloredJones K) α) ∧
      ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
        specialize Q ≠ 0 ∧ toComparison extraFactor ∣ toComparison (specialize Q) :=
  pairQ_tmin_of_formula K _ hseq (pairQ_exists_annihilator r s h)
    fun _ hQ hann ↦ pairQ_extraFactor_dvd_specialize r s h hQ hann

end AJConjecture
