import Mathlib
import AJTwist.Select.TwSSignedReturn

/-!
# The signed return for the whole symbol of the selected divisor (Unit PpS, node `PpS_Tail`)

Source: Section 8.1 of the paper (`conclusion.tex`, "Return to the signed sequence"): for a
primitive row `H` of the saturated ideal, the conjugate by the quantum dimension is a left
multiple `U R_a` of the selected right divisor and `\bar H = \bar U \bar R_a`. Section 8.4 uses
the whole of `\bar R_a`, not only its factor `E`.

The library's `tws_extraFactor_dvd_specialize_of_tail` (`AJTwist.Select.TwSSignedReturn`) proves
`toComparison (specialize R) ∣ toComparison (specialize (gaugeOp Q))` inside its proof and then
keeps only the factor `E`. Here the same argument is stated for the whole specialization of `R`.

* `pps_specialize_dvd_of_tail`: if every tail annihilator of the reduced sequence of `u` is a
  left pseudo-multiple of `R` and `specialize R ≠ 0`, then `R(-1, M, L)` divides `Q(-1, M, L)`
  in `ℚ(M)[L, L⁻¹]` for every primitive `Q` in the localized annihilator of the signed unreduced
  sequence `pairQFormula u`.
* `pps_dvd_specialize_of_formula`: transport to a knot whose coloured Jones function is the
  formula of `u` (the analogue of `tws_survival_of_formula` for an arbitrary factor `F`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- **Signed return, whole symbol.** If every tail annihilator of the reduced sequence of `u` is
a left pseudo-multiple of `R`, and the specialization of `R` is nonzero, then it divides the
specialization of every primitive operator in the localized annihilator of the signed unreduced
sequence `pairQFormula u`, in `ℚ(M)[L, L⁻¹]`. -/
theorem pps_specialize_dvd_of_tail (u : ℕ → RatFunc ℚ) {R : RecOp} (hR : specialize R ≠ 0)
    (htail : ∀ {Q' : RecOp} {n₁ : ℤ},
      (∀ n : ℤ, n₁ ≤ n → opApplyField Q' (pairQReducedFormulaEven u) n = 0) →
      ∃ β : Coeff, β ≠ 0 ∧ ∃ T : RecOp, C β * Q' = oreMul coeffShift T R)
    {Q : RecOp} (hQ : Q.IsPrimitive)
    (hann : ∃ c : Coeff, c ≠ 0 ∧
      ∀ n : ℤ, opApplyField (Polynomial.C c * Q) (pairQFormula u) n = 0) :
    toComparison (specialize R) ∣ toComparison (specialize Q) := by
  obtain ⟨n₁, hn₁⟩ := pairQ_exists_tail_annihilator_gaugeOp u hann
  obtain ⟨β, hβ, T, hT⟩ := htail hn₁
  have hX : (X ^ 2 - 1 : ℤ[X]) ≠ 0 := by
    intro h0
    have h1 := congrArg (Polynomial.eval 0) h0
    norm_num at h1
  have hspec : specialize (gaugeOp Q) ≠ 0 := by
    rw [specialize_gaugeOp]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hX) (specialize_ne_zero_of_isPrimitive hQ)
  have h1 : toComparison (specialize R) ∣ toComparison (specialize (gaugeOp Q)) :=
    toComparison_specialize_dvd_of_oreMul hβ hT hspec hR
  rw [specialize_gaugeOp, map_mul] at h1
  exact (isUnit_toComparison_coeff_of_ne_zero hX).dvd_mul_left.mp h1

/-- Transport to a knot: if `F` divides the specialization of every primitive operator in the
localized annihilator of the formula of `u`, and the coloured Jones function of `K` is that
formula, then `F` divides the specialization of every nonzero primitive element of the localized
annihilator of the coloured Jones function of `K`, in `ℚ(M)[L, L⁻¹]`. -/
theorem pps_dvd_specialize_of_formula (K : BraidKnot) (u : ℕ → RatFunc ℚ)
    (hseq : ∀ n : ℤ, laurentToField (coloredJones K n) = pairQFormula u n) {F : ComparisonRing}
    (hF : ∀ Q : RecOp, Q.IsPrimitive →
      (∃ c : Coeff, c ≠ 0 ∧ ∀ n : ℤ, opApplyField (Polynomial.C c * Q) (pairQFormula u) n = 0) →
        F ∣ toComparison (specialize Q)) :
    ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator (coloredJones K) Q →
      F ∣ toComparison (specialize Q) := by
  intro Q _ hprim hQ
  refine hF Q hprim ?_
  obtain ⟨c, hc, hann⟩ := hQ
  refine ⟨c, hc, fun n ↦ ?_⟩
  have h := congrArg laurentToField (hann n)
  have hfun : (fun m ↦ laurentToField (coloredJones K m)) = pairQFormula u := funext hseq
  rwa [map_zero, laurentToField_opApply, hfun] at h

end AJConjecture
