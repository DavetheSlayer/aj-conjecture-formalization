import Mathlib
import AJTwist.Factor.TwFRiccatiGauge
import AJPaper.Divisor.PpLCofactor

/-!
# A right factor of order one of the adjoint of `P_0` is unique (Unit PpL, node `PpL_Unique`)

Source: Section 5.6 of the paper (`operators.tex`): "Thus the monic linear right divisor is
unique if it exists." Mirror of `AJTwist/Factor/TwFZeroUnique.lean` for the adjoint `pplAdjOp`.

`ppl_adjoint_rightFactor_unique`: two right pseudo-factors `R`, `R'` of degree one of the
adjoint are proportional: `r₀ r₁' = r₁ r₀'`. Proof: otherwise the gauge transformation
(`exists_cofactor_pseudoFactor_of_two_solutions`, generic) gives a right pseudo-factor of degree
one of the cofactor, against `ppl_adjoint_no_linear_cofactor`.

This file is proved from the node `PpL_Cofactor`; it has no `sorry` of its own.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Two right pseudo-factors of degree one of the adjoint of `P_0` are proportional. -/
theorem ppl_adjoint_rightFactor_unique {β β' : Coeff} (hβ : β ≠ 0) (hβ' : β' ≠ 0)
    {S S' R R' : RecOp} (h : C β * pplAdjOp = oreMul coeffShift S R)
    (h' : C β' * pplAdjOp = oreMul coeffShift S' R') (hR : R.natDegree = 1)
    (hR' : R'.natDegree = 1) : R.coeff 0 * R'.coeff 1 = R.coeff 1 * R'.coeff 0 := by
  by_contra hne
  have hcoeff : ∀ {Q : RecOp}, Q.natDegree = 1 → Q.coeff 1 ≠ 0 := by
    intro Q hQ
    have hQ0 : Q ≠ 0 := fun h0 ↦ by
      rw [h0, natDegree_zero] at hQ
      exact zero_ne_one hQ
    have hlead : Q.coeff Q.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hQ0
    rwa [hQ] at hlead
  have hP : pplAdjOp.natDegree ≤ 3 := natDegree_pplAdjOp.le
  have hric := oreRiccati_eq_zero_of_pseudoFactor coeffShift_injective hβ' h' hR' hP
  have h2 : C β * pplAdjOp = oreMul coeffShift S (C (R.coeff 1) * X + C (R.coeff 0)) := by
    rw [← eq_X_add_C_of_natDegree_le_one hR.le]
    exact h
  obtain ⟨β₂, hβ₂, S₂, R₂, hR₂, hS₂⟩ := exists_cofactor_pseudoFactor_of_two_solutions
    coeffShift_injective hβ hP h2 (hcoeff hR) (hcoeff hR') hric (sub_ne_zero.mpr hne)
  exact ppl_adjoint_no_linear_cofactor hβ hβ₂ h hR hS₂ hR₂

end AJConjecture
