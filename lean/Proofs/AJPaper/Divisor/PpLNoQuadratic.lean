import Mathlib
import AJConjecture.QAlgOreMulZero
import AJTwist.Factor.TwFZeroJet
import AJPaper.Divisor.PpLEven
import AJPaper.Divisor.PpLInfinity

/-!
# `P_0` has no right factor of order two (Unit PpL, node `PpL_NoQuadratic`)

Source: Section 8.4 of the paper (`conclusion.tex`), the case `a = 0`: "This is a statement
about `f_S`, even if the selected divisor specializes to the quadratic alone." The paper leaves
open whether the divisor selected at `a = 0` is a quadratic right factor of `P_0`. It is not:

* `ppl_adjoint_no_linear`: the adjoint `pplAdjOp` of the explicit operator of `a = 0` has no
  right pseudo-factor of degree one (the descent `ppl_adjoint_exists_even_solution` and the
  nonexistence `ppl_adjoint_no_solution`).
* `ppl_no_quadratic`: in every pseudo-factorisation `β · twTransferOp 0 = S ⋆ R` the right
  factor does not have degree two.

Proof of `ppl_no_quadratic`: `R` is also a right pseudo-factor of the explicit operator
(`exists_pseudoFactor_twZeroExplicitOp`), with a cofactor `S'` of degree at most one; by
`ppl_oreRiccati_adjoint_of_linear_left` the pair `(s₁ σ(γ), σ(s₀) γ)` solves the Riccati
equation of the adjoint; `s₀ ≠ 0` because the trailing coefficient of the explicit operator is
not zero; so the adjoint has a right pseudo-factor of degree one
(`exists_pseudoFactor_of_oreRiccati_eq_zero`).

Independent computer-algebra tests that neither a left factor of order one nor a right factor of
order two exists (complete `q`-Petkovšek searches for the adjoint and for the exterior square,
with positive controls): scratch `py/d02_search.py`, `py/d02b_search_M.py`.

This file is proved from the nodes `PpL_Even`, `PpL_Normal`, `PpL_Integral`, `PpL_Reduce`,
`PpL_AtZero`; it has no `sorry` of its own.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The adjoint of the explicit operator of `a = 0` has no right pseudo-factor of degree one. -/
theorem ppl_adjoint_no_linear {β : Coeff} (hβ : β ≠ 0) {S R : RecOp}
    (h : C β * pplAdjOp = oreMul coeffShift S R) : R.natDegree ≠ 1 := by
  intro hR
  obtain ⟨e₀, e₁, h₁, h₀₁, hric, hjet⟩ := ppl_adjoint_exists_even_solution hβ h hR
  exact ppl_adjoint_no_solution h₁ h₀₁ hric hjet

/-- The trailing coefficient of the explicit operator of `a = 0` is not zero. -/
private theorem coeff_zero_twZeroExplicitOp_ne_zero_pplNoQuadratic :
    twZeroExplicitOp.coeff 0 ≠ 0 := by
  intro h0
  have h3 : pplAdjOp.coeff 3 = coeffShift^[3] (twZeroExplicitOp.coeff (3 - 3)) :=
    coeff_pplOreAdjoint coeffShift 3 twZeroExplicitOp le_rfl
  rw [Nat.sub_self, h0, iterate_map_zero] at h3
  have hlead : pplAdjOp.coeff pplAdjOp.natDegree ≠ 0 := by
    refine leadingCoeff_ne_zero.mpr fun h ↦ ?_
    have := natDegree_pplAdjOp
    rw [h, natDegree_zero] at this
    omega
  rw [natDegree_pplAdjOp] at hlead
  exact hlead h3

/-- The explicit operator of `a = 0` has order at most three. -/
private theorem natDegree_twZeroExplicitOp_le_pplNoQuadratic :
    twZeroExplicitOp.natDegree ≤ 3 := by
  unfold twZeroExplicitOp
  refine natDegree_sum_le_of_forall_le _ _ fun k _ ↦ ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- **`P_0` has no right pseudo-factor of degree two**, i.e. no left factor of order one over
`ℚ(t, M)`. -/
theorem ppl_no_quadratic {β : Coeff} (hβ : β ≠ 0) {S R : RecOp}
    (h : C β * twTransferOp 0 = oreMul coeffShift S R) : R.natDegree ≠ 2 := by
  intro hR
  obtain ⟨S', hS'⟩ := exists_pseudoFactor_twZeroExplicitOp h
  have hγ : β * (twDet 3 (X ^ 4 : ℤ[X])).comp (C (X ^ 12) * X ^ 2) ≠ 0 :=
    mul_ne_zero hβ twZero_scalars_ne_zero.1
  have hE0 : twZeroExplicitOp ≠ 0 := fun h0 ↦
    coeff_zero_twZeroExplicitOp_ne_zero_pplNoQuadratic (by rw [h0, coeff_zero])
  have hne : oreMul coeffShift S' R ≠ 0 := hS' ▸ mul_ne_zero (C_ne_zero.mpr hγ) hE0
  have hS'0 : S' ≠ 0 := by
    rintro rfl
    exact hne (oreMul_zero_left _ _)
  have hR0 : R ≠ 0 := by
    rintro rfl
    exact hne (oreMul_zero_right _ _)
  have hS'deg : S'.natDegree ≤ 1 := by
    have hd := congrArg natDegree hS'
    rw [natDegree_C_mul hγ, natDegree_oreMul coeffShift_injective hS'0 hR0, hR] at hd
    have := natDegree_twZeroExplicitOp_le_pplNoQuadratic
    omega
  have hric : oreRiccati coeffShift 3 pplAdjOp
      (S'.coeff 1 * coeffShift (β * (twDet 3 (X ^ 4 : ℤ[X])).comp (C (X ^ 12) * X ^ 2)))
      (coeffShift (S'.coeff 0) * (β * (twDet 3 (X ^ 4 : ℤ[X])).comp (C (X ^ 12) * X ^ 2))) = 0 :=
    ppl_oreRiccati_adjoint_of_linear_left coeffShift hS'deg hR.le hS'
  have hs₀ : S'.coeff 0 ≠ 0 := by
    intro h0
    have hc : β * (twDet 3 (X ^ 4 : ℤ[X])).comp (C (X ^ 12) * X ^ 2) *
        twZeroExplicitOp.coeff 0 = S'.coeff 0 * R.coeff 0 := by
      have := congrArg (fun p : RecOp ↦ p.coeff 0) hS'
      rw [ppl_oreMul_linear_quadratic coeffShift hS'deg hR.le] at this
      simpa [coeff_monomial] using this
    rw [h0, zero_mul] at hc
    exact coeff_zero_twZeroExplicitOp_ne_zero_pplNoQuadratic
      ((mul_eq_zero.mp hc).resolve_left hγ)
  have hr₁ : coeffShift (S'.coeff 0) *
      (β * (twDet 3 (X ^ 4 : ℤ[X])).comp (C (X ^ 12) * X ^ 2)) ≠ 0 :=
    mul_ne_zero ((map_ne_zero_iff coeffShift coeffShift_injective).mpr hs₀) hγ
  obtain ⟨β', hβ', S'', hS''⟩ := exists_pseudoFactor_of_oreRiccati_eq_zero coeffShift_injective
    natDegree_pplAdjOp.le hr₁ hric
  exact ppl_adjoint_no_linear hβ' hS'' (natDegree_linear hr₁)

end AJConjecture
