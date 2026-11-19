import Mathlib
import AJConjecture.QAlgNodeJetBasic
import AJHandoff.TorusKnot.PairKMirrorRobust
import AJPaper.Divisor.PpLAdjoint

/-!
# The symbol of the adjoint of `P_0` (Unit PpL, node `PpL_Symbol`)

Source: Section 3.4 of the paper (`transfer.tex`), the symbol `(L - 1) E` of `P_0`, and
Section 5.1 (`operators.tex`), eq. (Eb): "At `a = 0` the monic symbol in `u` is
`(u - 1) E_back`". At `t = -1` the shift is the identity, so the symbol of the adjoint
`∑_k σ^k(p_(3-k)) L^k` is the symbol of `P_0` with the order of the coefficients reversed.

For the adjoint `pplAdjOp` of the explicit operator of `a = 0`:

* `coeff_pplAdjOp_explicit`: its four coefficients `b_k(t⁴, t^(12 + 4k) M²)` in factored form;
* `natDegree_pplAdjOp`: it has order `3`;
* `specialize_pplAdjOp`: its symbol is `-(M² - 1)² (L - 1) E^∨`, with
  `E^∨ = extraFactorMirror = M⁴ L² - (M⁴ - 4M² + 1) L + 1`, the reverse of `E`;
* `specialize_pplAdjOp_ne_zero`.

Checked by exact computation (scratch `py/d01_adjoint.py`; for the explicit operator itself the
same script gives `(M² - 1)² (L - 1) E`).

This file has no `sorry`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The four coefficients of the adjoint, in the variable `M`. -/
theorem coeff_pplAdjOp_explicit :
    pplAdjOp.coeff 0 = C (X ^ 28) * (C (X ^ 4) * X ^ 2 - 1) * (C (X ^ 12) * X ^ 2 - 1) ∧
      pplAdjOp.coeff 1 = -(C (X ^ 32) * (C (X ^ 12) * X ^ 2 - 1) ^ 2 *
        (C (X ^ 20) * X ^ 4 - C (X ^ 12) * X ^ 2 - 3 * C (X ^ 8) * X ^ 2 + 2)) ∧
      pplAdjOp.coeff 2 = C (X ^ 36) * (C (X ^ 12) * X ^ 2 - 1) ^ 2 *
        (2 * C (X ^ 28) * X ^ 4 - C (X ^ 16) * X ^ 2 - 3 * C (X ^ 12) * X ^ 2 + 1) ∧
      pplAdjOp.coeff 3 =
        -(C (X ^ 68) * X ^ 4 * (C (X ^ 12) * X ^ 2 - 1) * (C (X ^ 20) * X ^ 2 - 1)) := by
  obtain ⟨h0, h1, h2, h3⟩ := coeff_pplAdjOpX_explicit
  have hsq : ∀ c : Coeff, twfSq c = c.comp (X ^ 2) := fun _ ↦ rfl
  rw [← map_twfSq_pplAdjOpX]
  simp only [coeff_map, h0, h1, h2, h3, hsq, twfLin, mul_comp, sub_comp, add_comp, neg_comp,
    pow_comp, C_comp, X_comp, one_comp, ofNat_comp, Nat.cast_ofNat]
  refine ⟨trivial, ?_, ?_, ?_⟩ <;> ring

/-- The value at `t = -1` of the leading coefficient of the adjoint is not zero. -/
private theorem map_coeff_three_ne_zero_pplSymbol :
    (pplAdjOp.coeff 3).map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0 := by
  have hx : (X ^ 2 - 1 : ℤ[X]) ≠ 0 := by
    have := (monic_X_pow_sub_C (1 : ℤ) (two_ne_zero)).ne_zero
    rwa [map_one] at this
  have hm : (pplAdjOp.coeff 3).map (Polynomial.evalRingHom (-1 : ℤ)) =
      -(X ^ 4 * (X ^ 2 - 1) ^ 2) := by
    rw [coeff_pplAdjOp_explicit.2.2.2]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_neg, Polynomial.map_one, map_C, map_X, coe_evalRingHom, eval_pow, eval_X]
    norm_num
    ring
  rw [hm]
  exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 4 X_ne_zero) (pow_ne_zero 2 hx))

/-- The adjoint of the explicit operator of `a = 0` has order `3`. -/
theorem natDegree_pplAdjOp : pplAdjOp.natDegree = 3 := by
  refine le_antisymm (natDegree_pplOreAdjoint_le _ _ _) (le_natDegree_of_ne_zero fun h ↦ ?_)
  exact map_coeff_three_ne_zero_pplSymbol (by rw [h, Polynomial.map_zero])

/-- The symbol of the adjoint: `-(M² - 1)² (L - 1) E^∨`. -/
theorem specialize_pplAdjOp :
    specialize pplAdjOp = -(C ((X ^ 2 - 1) ^ 2) * ((X - 1) * extraFactorMirror)) := by
  obtain ⟨h0, h1, h2, h3⟩ := coeff_pplAdjOp_explicit
  have hdeg : (specialize pplAdjOp).natDegree < 4 := by
    have h : (specialize pplAdjOp).natDegree ≤ pplAdjOp.natDegree := by
      rw [specialize, coe_mapRingHom]
      exact natDegree_map_le
    exact Nat.lt_succ_of_le (h.trans (natDegree_pplOreAdjoint_le _ _ _))
  rw [(specialize pplAdjOp).as_sum_range' 4 hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, coeff_specialize, h0, h1,
    h2, h3]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_neg, Polynomial.map_one, Polynomial.map_ofNat, map_C, map_X,
    coe_evalRingHom, eval_pow, eval_X]
  norm_num
  simp only [extraFactorMirror, ← C_mul_X_pow_eq_monomial, C_mul, C_pow, C_sub, C_add, C_1,
    C_ofNat]
  ring

/-- The symbol of the adjoint is not zero. -/
theorem specialize_pplAdjOp_ne_zero : specialize pplAdjOp ≠ 0 := by
  intro h
  have h3 := congrArg (fun p : ℤ[X][X] ↦ p.coeff 3) h
  simp only [coeff_specialize, coeff_zero] at h3
  exact map_coeff_three_ne_zero_pplSymbol h3

end AJConjecture
