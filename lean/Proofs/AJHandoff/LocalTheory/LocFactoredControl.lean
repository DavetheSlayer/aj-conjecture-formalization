import Mathlib
import AJHandoff.LocalTheory.LocToyOperator

/-!
# I-CTRL: the factored same-symbol row admits an integral allocation

With `σ(z) = Q z`, `Q = exp(h)`,
`(u - z) ⋆ (u - (2 - z)) = u² - [2 + (1 - Q) z] u + z(2 - z)`.
Its residual symbol is that of the toy operator, `(u - z)(u + z - 2)`, but its actual first jet is
`P₁ = z u` (from `1 - Q = -h + O(h²)`). Formula (4) at the node `(1, 1)` gives `-1` for the
allocation with `G = u - z` on the right and `0` for `H = u + z - 2` on the right: both are
integers, and the known factorization (right factor `u - (2 - z)`, index `0`) is permitted. The
residual symbol alone does not determine the obstruction: the first jet does.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The factored row `u² - [2 + (1 - Q) z] u + z(2 - z)`. -/
def locFactoredOp : LocOp :=
  X ^ 2 - C (2 + C (1 - (toyDilation.Q : PowerSeries ℂ)) * X) * X + C ((X : LocPoly) * (2 - X))

/-- The shift of `z - 2`. -/
private theorem shiftHom_X_sub_two_factored :
    toyDilation.shiftHom (X - 2) = C (toyDilation.Q : PowerSeries ℂ) * X - 2 := by
  change (X - 2 : LocPoly).comp _ = _
  simp

/-- It is the Ore product `(u - z) ⋆ (u - (2 - z))`. -/
theorem locFactoredOp_eq_oreMul :
    locFactoredOp = oreMul toyDilation.shiftHom (X - C X) (X - C (2 - X)) := by
  have hl : (X - C X : LocOp) = monomial 1 1 + monomial 0 (-X) := by
    rw [monomial_zero_left, ← C_mul_X_pow_eq_monomial, map_one, one_mul, pow_one, map_neg,
      sub_eq_add_neg]
  have hr : (X - C (2 - X) : LocOp) = monomial 1 1 + monomial 0 (X - 2) := by
    rw [monomial_zero_left, ← C_mul_X_pow_eq_monomial, map_one, one_mul, pow_one, map_sub,
      map_sub]
    ring
  rw [hl, hr, oreMul_add_left, oreMul_add_right, oreMul_add_right, oreMul_monomial_monomial,
    oreMul_monomial_monomial, oreMul_monomial_monomial, oreMul_monomial_monomial]
  simp only [Function.iterate_one, Function.iterate_zero, id, map_one, shiftHom_X_sub_two_factored]
  simp only [locFactoredOp, ← C_mul_X_pow_eq_monomial]
  simp only [map_sub, map_add, map_mul, map_neg, map_one, map_ofNat]
  ring

/-- Same residual symbol as the toy operator, first jet `z u`. -/
theorem opJet_locFactoredOp :
    opJet0 locFactoredOp = opJet0 locToyOp ∧ opJet1 locFactoredOp = C X * X := by
  have hQ0 : PowerSeries.constantCoeff (toyDilation.Q : PowerSeries ℂ) = 1 :=
    toyDilation.constantCoeff_Q
  have hQ1 : PowerSeries.coeff 1 (toyDilation.Q : PowerSeries ℂ) = 1 :=
    LocDilation.exp_c 1 one_ne_zero
  have hsplit : locFactoredOp =
      locToyOp + C (C ((toyDilation.Q : PowerSeries ℂ) - 1) * X) * X := by
    simp only [locFactoredOp, locToyOp, map_add, map_sub, map_one, map_mul]
    ring
  refine ⟨?_, ?_⟩
  · rw [hsplit, opJet0, opJet0, Polynomial.map_add]
    simp [locJet0, hQ0]
  · rw [hsplit, opJet1_add, opJet1_locToyOp, zero_add]
    have hm : (C (C ((toyDilation.Q : PowerSeries ℂ) - 1) * X) * X : LocOp) =
        monomial 1 (C ((toyDilation.Q : PowerSeries ℂ) - 1) * X) := by
      rw [← C_mul_X_pow_eq_monomial, pow_one]
    have hj : locJet1 (C ((toyDilation.Q : PowerSeries ℂ) - 1) * X) = X := by
      ext n
      rw [coeff_locJet1, coeff_C_mul_X, coeff_X]
      rcases eq_or_ne n 1 with rfl | hn
      · simp [hQ1]
      · simp [hn, hn.symm]
    rw [hm, opJet1, sum_monomial_index _ _ (by simp [locJet1]), hj, ← C_mul_X_pow_eq_monomial,
      pow_one]

/-- The two allocation indices are the integers `-1` and `0`. -/
theorem locFactored_nodeIndex :
    locNodeIndex 1 1 1 (opJet1 locFactoredOp) (locToyBlock 0) (locToyBlock 1)
        (locCofactor locToyBlock 0 1) 1 1 = -1 ∧
      locNodeIndex 1 1 1 (opJet1 locFactoredOp) (locToyBlock 1) (locToyBlock 0)
        (locCofactor locToyBlock 1 0) 1 1 = 0 := by
  obtain ⟨d0, d1, i0, i1⟩ := evalPoint_derivative_locToyBlock_one
  obtain ⟨hT, hT'⟩ := locCofactor_locToyBlock
  rw [opJet_locFactoredOp.2, hT, hT', locNodeIndex, locNodeIndex, d0, d1, i0, i1]
  simp [evalPoint]
  norm_num

end AJConjecture
