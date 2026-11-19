import Mathlib
import AJTwist.Factor.TwFRiccatiGauge
import AJTwist.Factor.TwFZeroCofactor

/-!
# A right factor of order one of `P_0` is unique (TwF, unit F4)

Source: revision 5, Section 5.6 (`operators.tex`): "Two distinct such divisors would have a monic
degree-two least common left multiple right-dividing `P` … Thus the monic linear right divisor is
unique if it exists. The same argument works over the even-meridian field, because `E_back` is
already irreducible over `ℂ(M)`."

`twf_zero_rightFactor_unique`: two right pseudo-factors `R`, `R'` of degree one of
`P_0 = twTransferOp 0` are proportional: `r₀ r₁' = r₁ r₀'`.

Route: suppose `θ = r₀ r₁' - r₁ r₀' ≠ 0`. `R = C r₁ * X + C r₀` (`natDegree = 1`), `r₁, r₁' ≠ 0`,
`P_0` has degree `3` (`natDegree_twTransferOp`, `twWindow_zero`), and `(r₀', r₁')` solves the
Riccati equation of `P_0` (`oreRiccati_eq_zero_of_pseudoFactor`, `coeffShift_injective`); so by
`exists_cofactor_pseudoFactor_of_two_solutions` the cofactor `S` has a right pseudo-factor of
degree one, contradicting `twf_zero_no_linear_cofactor`.

This is the paper's uniqueness over `ℚ(t, M)`. The paper states it also over `ℂ(t, M)` and
`ℂ(t, x)` in order to apply the automorphism `t ↦ i t`; the Lean route needs uniqueness over
`ℚ(t, M)` only, see `AJTwist/Factor/TwFZeroEven.lean`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Two right pseudo-factors of degree one of `P_0` are proportional. -/
theorem twf_zero_rightFactor_unique {β β' : Coeff} (hβ : β ≠ 0) (hβ' : β' ≠ 0)
    {S S' R R' : RecOp} (h : C β * twTransferOp 0 = oreMul coeffShift S R)
    (h' : C β' * twTransferOp 0 = oreMul coeffShift S' R') (hR : R.natDegree = 1)
    (hR' : R'.natDegree = 1) : R.coeff 0 * R'.coeff 1 = R.coeff 1 * R'.coeff 0 := by
  by_contra hne
  have hcoeff : ∀ {Q : RecOp}, Q.natDegree = 1 → Q.coeff 1 ≠ 0 := by
    intro Q hQ
    have hQ0 : Q ≠ 0 := fun h0 ↦ by
      rw [h0, natDegree_zero] at hQ
      exact zero_ne_one hQ
    have hlead : Q.coeff Q.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hQ0
    rwa [hQ] at hlead
  have hP : (twTransferOp 0).natDegree ≤ 3 := by rw [natDegree_twTransferOp, twWindow_zero]
  have hric := oreRiccati_eq_zero_of_pseudoFactor coeffShift_injective hβ' h' hR' hP
  have h2 : C β * twTransferOp 0 =
      oreMul coeffShift S (C (R.coeff 1) * X + C (R.coeff 0)) := by
    rw [← eq_X_add_C_of_natDegree_le_one hR.le]
    exact h
  obtain ⟨β₂, hβ₂, S₂, R₂, hR₂, hS₂⟩ := exists_cofactor_pseudoFactor_of_two_solutions
    coeffShift_injective hβ hP h2 (hcoeff hR) (hcoeff hR') hric (sub_ne_zero.mpr hne)
  exact twf_zero_no_linear_cofactor hβ hβ₂ h hR hS₂ hR₂

end AJConjecture
