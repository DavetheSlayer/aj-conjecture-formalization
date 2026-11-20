import Mathlib
import AJTwist.Factor.TwFRankOneJet
import AJPaper.Divisor.PpLJetRules
import AJPaper.Divisor.PpLSymbol

/-!
# The first jet of a right factor of order one of the adjoint of `P_0` (Unit PpL, node
`PpL_Jet`)

Source: Section 5.6 of the paper (`operators.tex`): "Now set `q = e^ε` and
`r_0 = 1 + ε f(x) + ⋯` … Thus `f(x) = (x + 1)/(2(x - 1))`" for a right factor `u - r_0` of
`P_0`; Section 5.5: "If a left factor is `u - 1 + ε s_1 + ⋯`, the same product formula yields
`s_1 = (Ṗ(x, 1) - δ H_0(x, 1))/H_0(x, 1)`". For `P_0` the left exponent is
`(3x - 1)/(2(x - 1))`, with limit `3/2` at infinity against `1/2` for the right factor: both are
half-integers.

In the library's forward convention, with the first jet `∂_t` at `t = -1`, for the adjoint
`pplAdjOp` (mirror of `AJTwist/Factor/TwFZeroJet.lean`):

* `eval_one_derivative_specialize_pplAdjOp`: `(∂_L P†₀)(M, 1) = -4 M² (M² - 1)²`;
* `eval_one_specializeJet_pplAdjOp`: `P†₁(M, 1) = 8 M² (M² - 1)(5 M² - 3)`;
* `nodeNumer_mul_of_rightFactor_pplAdjOp`: for a right pseudo-factor `R` of degree one with
  `R₀(M, 1) = 0`: `N_R (M² - 1) = Δ_R · 2 (5 M² - 3)`, i.e. the logarithmic first jet of
  `r₀/r₁` is `2 (5 M² - 3)/(M² - 1)`, with limit `10 ≡ 2 mod 4` at infinity (for `P_0` itself:
  `2 (M² + 1)/(M² - 1)`, limit `2`).

Route: as in the template, from `coeff_pplAdjOp_explicit`, the jet rules of
`AJPaper/Divisor/PpLJetRules.lean` and `nodeNumer_mul_of_rankOne_right`.
Checked by exact computation (scratch `py/d01_adjoint.py`, which reproduces the library's
values `4 M² (M² - 1)²` and `-8 M² (M² - 1)(M² + 1)` for the explicit operator).

This file has no `sorry`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `(∂_L P†₀)(M, 1) = -4 M² (M² - 1)²` for the adjoint of the explicit operator of `a = 0`. -/
theorem eval_one_derivative_specialize_pplAdjOp :
    (derivative (specialize pplAdjOp)).eval 1 = -(4 * X ^ 2 * (X ^ 2 - 1) ^ 2) := by
  rw [specialize_pplAdjOp]
  simp only [extraFactorMirror, derivative_neg, derivative_mul, derivative_C, derivative_sub,
    derivative_add, derivative_X, derivative_one, derivative_X_pow, eval_neg, eval_mul,
    eval_add, eval_sub, eval_C, eval_X, eval_one, eval_pow, eval_zero]
  norm_num
  ring

/-- `P†₁(M, 1) = 8 M² (M² - 1)(5 M² - 3)` for the adjoint of the explicit operator of
`a = 0`. -/
theorem eval_one_specializeJet_pplAdjOp :
    (specializeJet pplAdjOp).eval 1 = 8 * X ^ 2 * (X ^ 2 - 1) * (5 * X ^ 2 - 3) := by
  have hdeg : (specializeJet pplAdjOp).natDegree < 4 := by
    refine Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ ?_)
    rw [coeff_specializeJet, coeff_eq_zero_of_natDegree_lt
      (natDegree_pplAdjOp.le.trans_lt hk), coeffJet_zero]
  obtain ⟨h0, h1, h2, h3⟩ := coeff_pplAdjOp_explicit
  have hj2 : coeffJet (2 : Coeff) = 0 := ppl_coeffJet_ofNat 2
  have hj3 : coeffJet (3 : Coeff) = 0 := ppl_coeffJet_ofNat 3
  rw [eval_eq_sum_range' hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeff_specializeJet, one_pow,
    mul_one, zero_add]
  rw [h0, h1, h2, h3]
  simp only [ppl_coeffJet_neg, ppl_coeffJet_add, ppl_coeffJet_sub, ppl_coeffJet_mul,
    ppl_coeffJet_sq, ppl_coeffJet_C, ppl_coeffJet_X_pow, hj2, hj3, ppl_coeffJet_one]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_one, Polynomial.map_ofNat, map_C, map_X, coe_evalRingHom, eval_pow, eval_X,
    derivative_pow, derivative_X, eval_mul, eval_C]
  norm_num
  ring

/-- The logarithmic first jet of a right pseudo-factor of degree one of the adjoint of the
explicit operator of `a = 0` is `2 (5 M² - 3)/(M² - 1)`. -/
theorem nodeNumer_mul_of_rightFactor_pplAdjOp {β : Coeff}
    (hβ : β.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0) {S R : RecOp}
    (h : C β * pplAdjOp = oreMul coeffShift S R) (hR : R.natDegree = 1)
    (hR1 : (specialize R).eval 1 = 0) :
    nodeNumer R * (X ^ 2 - 1) = nodeDenom R * (2 * (5 * X ^ 2 - 3)) := by
  have hkey := nodeNumer_mul_of_rankOne_right hβ h hR hR1
  rw [eval_one_derivative_specialize_pplAdjOp, eval_one_specializeJet_pplAdjOp] at hkey
  have h2 : (X ^ 2 - 1 : ℤ[X]) ≠ 0 := by
    have := (monic_X_pow_sub_C (1 : ℤ) (two_ne_zero)).ne_zero
    rwa [map_one] at this
  have h4 : (4 : ℤ[X]) ≠ 0 := by
    rw [← C_ofNat]
    exact C_ne_zero.mpr (by norm_num)
  have hc : (4 * X ^ 2 * (X ^ 2 - 1) : ℤ[X]) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h4 (pow_ne_zero 2 X_ne_zero)) h2
  refine mul_left_cancel₀ hc ?_
  linear_combination -hkey

end AJConjecture
