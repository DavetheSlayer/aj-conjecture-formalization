import Mathlib
import AJConjecture.FieldActionBridge
import AJConjecture.RecurrencePolynomialExists
import AJConjecture.ColoredJones
import AJTwist.Exist.TwHExists
import AJTwist.Exist.TwHBar

/-!
# The recurrence ideal of a knot whose coloured Jones function is a twisted satellite formula

Source: revision 5, Theorem 1.1 ("the specialized primitive minimal recurrence of the marked
satellite is nonzero …") and Section 8.1, first paragraph: "This gives a nonzero all-integer row
and hence a nonzero saturated ideal."

In the baseline predicates of the library: if the coloured Jones function of a braid knot `K`
is the formula `twFormula η r s ℓ` of a twisted Whitehead double (negative clasp), or the bar of
such a formula (positive clasp: `Φ_{S^*}(N; t) = Φ_S(N; t⁻¹)`), then the localized annihilator of
`coloredJones K` contains a nonzero operator and `coloredJones K` has a recurrence polynomial
(the primitive operator of minimal order, `IsRecurrencePolynomial`). No hypothesis on `η`, `r`,
`s`, `ℓ`; no `q`-holonomicity input.

* `twH_knot_of_formula`: the transfer from an annihilated formula in `ℚ(t)` to the knot
  (`laurentToField_opApply`, `laurentToField_injective`, `exists_isRecurrencePolynomial`; the
  first two parts of `pairQ_tmin_of_formula`).
* `twH_knot`: the formula itself (`twH_exists_annihilator`).
* `twH_knot_bar`: the bar of the formula (`twH_exists_annihilator_bar`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A knot whose coloured Jones function is a sequence of `ℚ(t)` with a nonzero annihilator has
a nonzero localized annihilator and a recurrence polynomial. -/
theorem twH_knot_of_formula (K : BraidKnot) (f : ℤ → RatFunc ℚ)
    (hseq : ∀ n : ℤ, laurentToField (coloredJones K n) = f n)
    (hann : ∃ Q : RecOp, Q ≠ 0 ∧ ∃ c : Coeff, c ≠ 0 ∧
      ∀ n : ℤ, opApplyField (Polynomial.C c * Q) f n = 0) :
    (∃ Q : RecOp, Q ≠ 0 ∧ InLocalizedAnnihilator (coloredJones K) Q) ∧
      ∃ α : RecOp, IsRecurrencePolynomial (coloredJones K) α := by
  have hfun : (fun m ↦ laurentToField (coloredJones K m)) = f := funext hseq
  have hex : ∃ Q : RecOp, Q ≠ 0 ∧ InLocalizedAnnihilator (coloredJones K) Q := by
    obtain ⟨Q, hQ, c, hc, hann⟩ := hann
    refine ⟨Q, hQ, c, hc, fun n ↦ laurentToField_injective ?_⟩
    rw [map_zero, laurentToField_opApply, hfun]
    exact hann n
  exact ⟨hex, exists_isRecurrencePolynomial hex⟩

/-- **Existence of the recurrence polynomial (negative clasp).** A braid knot whose coloured
Jones function is the twisted satellite formula has a nonzero localized annihilator and a
recurrence polynomial. -/
theorem twH_knot (η : Bool) (r s : ℕ) (ℓ : ℤ) (K : BraidKnot)
    (hseq : ∀ n : ℤ, laurentToField (coloredJones K n) = twFormula η r s ℓ n) :
    (∃ Q : RecOp, Q ≠ 0 ∧ InLocalizedAnnihilator (coloredJones K) Q) ∧
      ∃ α : RecOp, IsRecurrencePolynomial (coloredJones K) α :=
  twH_knot_of_formula K _ hseq (twH_exists_annihilator η r s ℓ)

/-- **Existence of the recurrence polynomial (positive clasp).** The same for a braid knot
whose coloured Jones function is the bar of a twisted satellite formula. -/
theorem twH_knot_bar (η : Bool) (r s : ℕ) (ℓ : ℤ) (K : BraidKnot)
    (hseq : ∀ n : ℤ, laurentToField (coloredJones K n) = twQBar (twFormula η r s ℓ n)) :
    (∃ Q : RecOp, Q ≠ 0 ∧ InLocalizedAnnihilator (coloredJones K) Q) ∧
      ∃ α : RecOp, IsRecurrencePolynomial (coloredJones K) α :=
  twH_knot_of_formula K _ hseq (twH_exists_annihilator_bar (twH_exists_annihilator η r s ℓ))

end AJConjecture
