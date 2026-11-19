import Mathlib
import AJTwist.Quantum.TwQPeriodSpan
import AJTwist.Quantum.TwQSymbolEnds
import AJTwist.Select.TwSSurvival
import AJTwist.Factor.TwFMain
import AJTwist.Exist.TwHKnot

/-!
# The quantum clauses for the negative clasp (Unit M1, second half)

Source: revision 5, Sections 6.7 and 8.1 (`selection.tex`, `conclusion.tex`): "this proves
`E ∣ f_S ≠ 0` for each negative-clasp satellite".

`twm_quantum_negClasp`: let `K` be a braid knot whose coloured Jones function is the formula
`twFormula η r s ℓ` of the quantum package (index `a = twIndex η r s ℓ`). Then

1. the localized annihilator of `coloredJones K` contains a nonzero operator, and a recurrence
   polynomial exists (`twH_knot`, package Exist);
2. every nonzero primitive element of the localized annihilator has nonzero specialization
   divisible by `E` in `ℚ(M)[L, L⁻¹]` (`tws_survival`, package Select).

The hypotheses of `tws_survival` are supplied with `P = twTransferOp a`:
`specialize_twTransferOp_ne_zero`, `extraFactor_dvd_specialize_twTransferOp`,
`natDegree_twTransferOp`, `twWindow_zero` and `twQ_transfer_mem_periodSpan` (package Quantum),
`twf_irreducible` and `twf_no_linear` (package Factor). The duplicated definitions of the two
packages (`twsInput`/`twInput`, `twsPeriod`/`twPeriod`) agree by `rfl`, so the statements unify
without rewriting.

This file has no `sorry` of its own.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- **Survival of `E` for the negative clasp** (Sections 6 and 8.1): for a knot whose coloured
Jones function is `twFormula η r s ℓ`, every nonzero primitive element of the localized
annihilator has nonzero specialization divisible by `E`. -/
theorem twm_survival_negClasp {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ) (K : BraidKnot)
    (hseq : ∀ n : ℤ, laurentToField (coloredJones K n) = twFormula η r s ℓ n) :
    ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
      specialize Q ≠ 0 ∧ toComparison extraFactor ∣ toComparison (specialize Q) := by
  have hr : 2 ≤ r := h.1
  have hs : 2 ≤ s := hr.trans h.2.1.le
  refine tws_survival η r s hr hs ℓ (P := twTransferOp (twIndex η r s ℓ))
    (specialize_twTransferOp_ne_zero _) (extraFactor_dvd_specialize_twTransferOp _)
    (fun ha _ hβ _ _ hfac ↦ twf_irreducible _ ha hβ hfac)
    (fun ha ↦ ⟨?_, fun {β} hβ {S R} hfac ↦ ?_⟩) (twQ_transfer_mem_periodSpan η r s ℓ) K hseq
  · rw [natDegree_twTransferOp, ha, twWindow_zero]
  · rw [ha] at hfac
    exact twf_no_linear hβ hfac

/-- **The quantum clauses for the negative clasp**: nonzero localized annihilator, existence of
the recurrence polynomial, and survival of `E`, for every knot whose coloured Jones function is
`twFormula η r s ℓ`. -/
theorem twm_quantum_negClasp {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ) (K : BraidKnot)
    (hseq : ∀ n : ℤ, laurentToField (coloredJones K n) = twFormula η r s ℓ n) :
    (∃ Q : RecOp, Q ≠ 0 ∧ InLocalizedAnnihilator (coloredJones K) Q) ∧
      (∃ α : RecOp, IsRecurrencePolynomial (coloredJones K) α) ∧
      ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
        specialize Q ≠ 0 ∧ toComparison extraFactor ∣ toComparison (specialize Q) :=
  ⟨(twH_knot η r s ℓ K hseq).1, (twH_knot η r s ℓ K hseq).2,
    twm_survival_negClasp h η ℓ K hseq⟩

end AJConjecture
