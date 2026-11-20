import Mathlib
import AJPaper.Divisor.PpLIntegral
import AJPaper.Divisor.PpLJetRules

/-!
# The normal form of the adjoint at `t = -1` (Unit PpL, node `PpL_Reduce`)

Source: Section 5.6 of the paper (`operators.tex`): "Since `r̄_0 = 1` and `σ(g)/g` reduces to
`1`, eq. (riccati-normal) gives `μ = 0`, `∑ n_k = 0` and `c(1) = 1`." Mirror of
`AJTwist/Factor/TwFZeroReduce.lean`.

For the adjoint the leading coefficient `p†_3 = -t⁶⁸ x² ℓ₃ ℓ₅` carries the factor `x²` (for
`P_0` it is the trailing coefficient that does), so in the integral normal form

`e₀ · c_d · t⁶⁸ x² ℓ₃ ℓ₅ · τ(g) = c_n · x^μ ∏_{j<4} ℓ_{pplIdx j}^{ε_j} · τ²(e₁) · g`

the reduction at `t = -1` (`ē₀ = -ē₁`, `ℓ_j ↦ x - 1`, the shift becomes the identity) reads
`-c_d(-1) x² (x - 1)² = c_n(-1) x^μ (x - 1)^{∑ ε_j}`:

`ppl_adjoint_reduce`: `μ = 2`, `∑_j ε_j = 2` and `c_n(-1) = -c_d(-1)`.

So `ρ = -e₀/e₁` has neither a zero nor a pole at `x = 0`: this excludes the degenerate branch
`ρ ∼ q⁻⁴ x⁻²` of the Riccati equation at `x = 0` (a double pole; for `P_0` the degenerate branch
is a double zero, excluded by `μ = 0`).

Route: as in the template: `congrArg (Polynomial.map (evalRingHom (-1)))` of the identity,
`map_evalRingHom_twfShiftX`, `ppl_map_evalRingHom_twfLin`, `Finset.prod_pow_eq_pow_sum`, cancel
`ē₁ ḡ ≠ 0`; then the order at `x = 0` (evaluate at `0` after cancelling the common power of `x`,
or compare `Polynomial.natTrailingDegree`), the degree, and the leading coefficient.

This file has no `sorry`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The integral normal form of the adjoint at `t = -1`: `μ = 2`, `∑ ε_j = 2` and
`c_n(-1) = -c_d(-1)`. -/
theorem ppl_adjoint_reduce {e₀ e₁ g : Coeff} {cn cd : ℤ[X]} {μ : ℕ} {ε : Fin 4 → ℕ}
    (h₁ : e₁.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0)
    (h₀₁ : e₀.map (Polynomial.evalRingHom (-1 : ℤ)) = -e₁.map (Polynomial.evalRingHom (-1 : ℤ)))
    (hg : g.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0)
    (hcn : cn.eval (-1) ≠ 0) (hcd : cd.eval (-1) ≠ 0)
    (hI : e₀ * C cd * (C (X ^ 68) * X ^ 2 * twfLin 3 * twfLin 5) * twfShiftX g =
      C cn * X ^ μ * (∏ j : Fin 4, twfLin (pplIdx j) ^ ε j) * twfShiftX (twfShiftX e₁) * g) :
    μ = 2 ∧ ∑ j : Fin 4, ε j = 2 ∧ cn.eval (-1) = -cd.eval (-1) := by
  have hx1 : (X - 1 : ℤ[X]) ≠ 0 := X_sub_C_ne_zero 1
  have hX1 : (X - 1 : ℤ[X]) = X - C 1 := by rw [C_1]
  have h68 : (X ^ 68 : ℤ[X]).eval (-1) = 1 := by
    rw [eval_pow, eval_X]
    norm_num
  have hcd' : (C (cd.eval (-1)) : ℤ[X]) ≠ 0 := C_ne_zero.mpr hcd
  have hcn' : (C (cn.eval (-1)) : ℤ[X]) ≠ 0 := C_ne_zero.mpr hcn
  have hXp : ∀ n : ℕ, (X ^ n : ℤ[X]) ≠ 0 := fun n ↦ pow_ne_zero n X_ne_zero
  have hmap := congrArg (Polynomial.map (Polynomial.evalRingHom (-1 : ℤ))) hI
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_prod, map_C, map_X,
    coe_evalRingHom, map_evalRingHom_twfShiftX, ppl_map_evalRingHom_twfLin,
    Finset.prod_pow_eq_pow_sum, h₀₁, h68, C_1, one_mul] at hmap
  have hkey : -(C (cd.eval (-1)) * (X ^ 2 * (X - 1) ^ 2)) =
      C (cn.eval (-1)) * X ^ μ * (X - 1) ^ (∑ j : Fin 4, ε j) := by
    refine mul_right_cancel₀ (mul_ne_zero h₁ hg) ?_
    linear_combination hmap
  have htr : ∀ n : ℕ, ((X - 1 : ℤ[X]) ^ n).natTrailingDegree = 0 := by
    intro n
    refine natTrailingDegree_eq_zero.mpr (Or.inr ?_)
    rw [coeff_zero_eq_eval_zero, eval_pow, eval_sub, eval_X, eval_one]
    exact pow_ne_zero _ (by norm_num)
  have hμ : μ = 2 := by
    have h := congrArg natTrailingDegree hkey
    rw [natTrailingDegree_neg, natTrailingDegree_mul hcd' (mul_ne_zero (hXp 2) (pow_ne_zero 2 hx1)),
      natTrailingDegree_C, natTrailingDegree_mul (hXp 2) (pow_ne_zero 2 hx1),
      natTrailingDegree_X_pow, htr,
      natTrailingDegree_mul (mul_ne_zero hcn' (hXp μ)) (pow_ne_zero _ hx1),
      natTrailingDegree_mul hcn' (hXp μ), natTrailingDegree_C, natTrailingDegree_X_pow, htr]
      at h
    omega
  subst hμ
  have hkey' : -(C (cd.eval (-1)) * (X - 1) ^ 2) =
      C (cn.eval (-1)) * (X - 1) ^ (∑ j : Fin 4, ε j) := by
    refine mul_left_cancel₀ (hXp 2) ?_
    linear_combination hkey
  have hdeg := congrArg natDegree hkey'
  rw [natDegree_neg, natDegree_C_mul hcd, natDegree_C_mul hcn, natDegree_pow, natDegree_pow,
    hX1, natDegree_X_sub_C, mul_one, mul_one] at hdeg
  refine ⟨rfl, hdeg.symm, ?_⟩
  rw [← hdeg, ← neg_mul, ← C_neg] at hkey'
  have h := C_injective (mul_right_cancel₀ (pow_ne_zero 2 hx1) hkey')
  linarith

end AJConjecture
