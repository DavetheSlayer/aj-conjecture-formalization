import Mathlib
import AJTwist.Factor.TwFZeroIntegral

/-!
# The normal form at `t = -1` (TwF, unit F4)

Source: revision 5, Section 5.6 (`operators.tex`): "Since `r̄_0 = 1` and `σ(g)/g` reduces to `1`,
eq. (riccati-normal) gives `μ = 0`, `∑ n_k = 0` and `c(1) = 1`. Put `d_0 = ord_{x=0} g`,
`s = ∑ k n_k`. At `x = 0`, the right side is `c(q) q^{s - d_0}`. The coefficients of the Riccati
equation there are `(q⁷, -2q⁸, q⁹, 0)`, giving `r_0(q, 0) = q⁻¹`. Hence `c(q) = q^κ` with
`κ = -1 - s + d_0 ∈ ℤ`."

In the forward convention the Riccati equation at `x = 0` is `q⁷ ρ (q - ρ)² = 0`
(`p_k(q, 0) = (0, q⁹, -2q⁸, q⁷)`), so `ρ(0) = q`. With the integral normal form

`-e₀ · c_d · t²⁸ ℓ₁ ℓ₃ · τ(g) = c_n · x^μ ∏_{j<4} ℓ_j^{ε_j} · τ²(e₁) · g`     (I)

and `ē₀ = -ē₁ ≠ 0`, `ḡ ≠ 0`, `c_n(-1), c_d(-1) ≠ 0`:

* `twf_zero_reduce`: applying `t = -1` to (I) (`ℓ_j ↦ x - 1`, the shift becomes the identity):
  `c_d(-1) (x - 1)² = c_n(-1) x^μ (x - 1)^{∑ ε_j}`, hence `μ = 0`, `∑_j ε_j = 2`,
  `c_n(-1) = c_d(-1)`.
The value at `x = 0` is in `AJTwist/Factor/TwFZeroAtZero.lean`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- At `t = -1` the linear forms `ℓ_j` become `x - 1`. -/
private theorem map_evalRingHom_twfLin_twfZeroReduce (j : ℕ) :
    (twfLin j).map (Polynomial.evalRingHom (-1 : ℤ)) = X - 1 := by
  rw [twfLin, Polynomial.map_sub, Polynomial.map_mul, map_C, map_X, Polynomial.map_one,
    coe_evalRingHom, eval_pow, eval_X, pow_mul]
  norm_num

/-- The integral normal form at `t = -1`: `μ = 0`, `∑ ε_j = 2` and `c_n(-1) = c_d(-1)`. -/
theorem twf_zero_reduce {e₀ e₁ g : Coeff} {cn cd : ℤ[X]} {μ : ℕ} {ε : Fin 4 → ℕ}
    (h₁ : e₁.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0)
    (h₀₁ : e₀.map (Polynomial.evalRingHom (-1 : ℤ)) = -e₁.map (Polynomial.evalRingHom (-1 : ℤ)))
    (hg : g.map (Polynomial.evalRingHom (-1 : ℤ)) ≠ 0)
    (hcn : cn.eval (-1) ≠ 0) (hcd : cd.eval (-1) ≠ 0)
    (hI : -e₀ * C cd * (C (X ^ 28) * twfLin 1 * twfLin 3) * twfShiftX g =
      C cn * X ^ μ * (∏ j : Fin 4, twfLin j ^ ε j) * twfShiftX (twfShiftX e₁) * g) :
    μ = 0 ∧ ∑ j : Fin 4, ε j = 2 ∧ cn.eval (-1) = cd.eval (-1) := by
  have hx1 : (X - 1 : ℤ[X]) ≠ 0 := X_sub_C_ne_zero 1
  have hX1 : (X - 1 : ℤ[X]) = X - C 1 := by rw [C_1]
  have h28 : (X ^ 28 : ℤ[X]).eval (-1) = 1 := by
    rw [eval_pow, eval_X]
    norm_num
  have hmap := congrArg (Polynomial.map (Polynomial.evalRingHom (-1 : ℤ))) hI
  simp only [Polynomial.map_mul, Polynomial.map_neg, Polynomial.map_pow, Polynomial.map_prod,
    map_C, map_X, coe_evalRingHom, map_evalRingHom_twfShiftX,
    map_evalRingHom_twfLin_twfZeroReduce, Finset.prod_pow_eq_pow_sum, h₀₁, neg_neg, h28, C_1,
    one_mul] at hmap
  have hkey : C (cd.eval (-1)) * (X - 1) ^ 2 =
      C (cn.eval (-1)) * X ^ μ * (X - 1) ^ (∑ j : Fin 4, ε j) := by
    refine mul_right_cancel₀ (mul_ne_zero h₁ hg) ?_
    linear_combination hmap
  have hμ : μ = 0 := by
    by_contra hμ
    have h0 := congrArg (Polynomial.eval 0) hkey
    simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_one, zero_pow hμ, mul_zero,
      zero_mul] at h0
    norm_num at h0
    exact hcd h0
  subst hμ
  rw [pow_zero, mul_one] at hkey
  have hdeg := congrArg natDegree hkey
  rw [natDegree_C_mul hcd, natDegree_C_mul hcn, natDegree_pow, natDegree_pow, hX1,
    natDegree_X_sub_C, mul_one, mul_one] at hdeg
  refine ⟨rfl, hdeg.symm, ?_⟩
  rw [← hdeg] at hkey
  exact (C_injective (mul_right_cancel₀ (pow_ne_zero 2 hx1) hkey)).symm

end AJConjecture
