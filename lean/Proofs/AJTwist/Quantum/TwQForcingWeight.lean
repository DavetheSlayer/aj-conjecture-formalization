import Mathlib
import AJTwist.Quantum.TwQInputRec

/-!
# The forcing weight `ℛ_η` and the inner forcing on the half interval (Unit Q4)

Source: revision 5, Section 3.2, eq. (innerforcing):
`e_j = ∑_{n=0}^{j} K_{jn} g(n) ℛ_η(Q, J)`, `ℛ_η(Q, J) = -q^(ηm+ℓ) (A(Q, J) - A(\hat Q, J))`,
`A(Q, J) = (Q - J) Q^(ηm+ℓ-1) H_η(q, Q)`, `H_η(q, Q) = ∑_i c_i(q^η) Q^(η β_i)`; Section 6.3:
"Put `p_i = ℓ + η λ_i` … the `Q`-terms are precisely `Q^(p_i) - J Q^(p_i - 1)`".

* `twLambda r s = (s + r, r - s, s - r, -s - r)`, `twExp η r s ℓ i = p_i = ℓ ± λ_i`;
* `twCoef η r s i = c_i(q^{±1})`,
  `(c_1, …, c_4) = (q^(β_1+1), -q^(β_2), -q^(β_3), q^(β_4+1))/(q-1)`,
  `β_i = -rs + λ_i`;
* `twForcingWeight η r s ℓ n j = ℛ_η(q^n, q^j)
    = -q^(±rs+ℓ) ∑_i c_i [(Q^(p_i) - \hat Q^(p_i)) - J (Q^(p_i - 1) - \hat Q^(p_i - 1))]`,
  `\hat Q = q^(-(n+1))`.

`twForcing_eq_sum` expands the forcing of the twisted input in the four monomials. The inner
equation itself is in `AJTwist.Quantum.TwQInnerForcing`.
-/

noncomputable section

namespace AJConjecture

/-- The exponents `(λ_1, …, λ_4) = (s + r, r - s, s - r, -s - r)`. -/
def twLambda (r s : ℕ) : Fin 4 → ℤ :=
  ![(s : ℤ) + r, (r : ℤ) - s, (s : ℤ) - r, -(s : ℤ) - r]

/-- The exponents `p_i = ℓ + η λ_i` of the forcing. -/
def twExp (η : Bool) (r s : ℕ) (ℓ : ℤ) (i : Fin 4) : ℤ :=
  ℓ + (if η then 1 else -1) * twLambda r s i

/-- The coefficients `c_i(q^η)`:
`(c_1, …, c_4)(q) = (q^(β_1+1), -q^(β_2), -q^(β_3), q^(β_4+1))/(q - 1)`, `β_i = -rs + λ_i`. -/
def twCoef (η : Bool) (r s : ℕ) (i : Fin 4) : RatFunc ℚ :=
  (![1, -1, -1, 1] i : RatFunc ℚ) *
    qParam ^ ((if η then 1 else -1) *
      (twLambda r s i - (r : ℤ) * s + (![1, 0, 0, 1] i : ℤ))) /
      (qParam ^ (if η then (1 : ℤ) else -1) - 1)

/-- The forcing weight `ℛ_η(q^n, q^j)` of eq. (innerforcing). -/
def twForcingWeight (η : Bool) (r s : ℕ) (ℓ : ℤ) (n : ℤ) (j : ℕ) : RatFunc ℚ :=
  -(qParam ^ ((if η then 1 else -1) * ((r : ℤ) * s) + ℓ)) *
    ∑ i : Fin 4, twCoef η r s i *
      ((qParam ^ (twExp η r s ℓ i * n) - qParam ^ (-(twExp η r s ℓ i * (n + 1)))) -
        qParam ^ j * (qParam ^ ((twExp η r s ℓ i - 1) * n) -
          qParam ^ (-((twExp η r s ℓ i - 1) * (n + 1)))))

/-- The denominator `q^η - 1` of the coefficients `c_i(q^η)` does not vanish. -/
private theorem twCoefDen_ne_zero_twQForcingWeight (η : Bool) :
    qParam ^ (if η then (1 : ℤ) else -1) - 1 ≠ 0 := by
  have h := one_sub_qParam_zpow_ne_zero (n := if η then (1 : ℤ) else -1) (by cases η <;> simp)
  intro h0
  exact h (by rw [← neg_sub, h0, neg_zero])

/-- `(q^η - 1) c_i(q^η)` is a signed power of `q`. -/
theorem twCoef_mul (η : Bool) (r s : ℕ) (i : Fin 4) :
    (qParam ^ (if η then (1 : ℤ) else -1) - 1) * twCoef η r s i =
      (![1, -1, -1, 1] i : RatFunc ℚ) *
        qParam ^ ((if η then 1 else -1) *
          (twLambda r s i - (r : ℤ) * s + (![1, 0, 0, 1] i : ℤ))) := by
  rw [twCoef, mul_div_assoc', mul_div_cancel_left₀ _ (twCoefDen_ne_zero_twQForcingWeight η)]

/-- A monomial of `X² · (numerator of H)` as a product of two powers of `q`. -/
private theorem ratFuncX_zpow_mul_eq_qParam_twQForcingWeight (c e a b : ℤ)
    (h : c + e = 4 * a + 4 * b) :
    (RatFunc.X : RatFunc ℚ) ^ c * RatFunc.X ^ e = qParam ^ a * qParam ^ b := by
  rw [qParam_zpow_eq_ratFuncX_zpow, qParam_zpow_eq_ratFuncX_zpow,
    ← zpow_add₀ RatFunc.X_ne_zero, ← zpow_add₀ RatFunc.X_ne_zero, h]

/-- `(q - 1) H_+(q, q^n)` in the four monomials. -/
private theorem qParam_sub_one_mul_pairQForcing_twQForcingWeight (r s : ℕ) (n : ℤ) :
    (qParam ^ (1 : ℤ) - 1) * pairQForcing r s n =
      1 * qParam ^ (1 * ((s : ℤ) + r - (r : ℤ) * s + 1)) *
          qParam ^ (n * (1 * ((s : ℤ) + r - (r : ℤ) * s))) +
        -1 * qParam ^ (1 * ((r : ℤ) - s - (r : ℤ) * s + 0)) *
          qParam ^ (n * (1 * ((r : ℤ) - s - (r : ℤ) * s))) +
        -1 * qParam ^ (1 * ((s : ℤ) - r - (r : ℤ) * s + 0)) *
          qParam ^ (n * (1 * ((s : ℤ) - r - (r : ℤ) * s))) +
        1 * qParam ^ (1 * (-(s : ℤ) - r - (r : ℤ) * s + 1)) *
          qParam ^ (n * (1 * (-(s : ℤ) - r - (r : ℤ) * s))) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hD := ratFuncX_sq_sub_inv_sq_ne_zero
  have hq1 : qParam ^ (1 : ℤ) - 1 = (RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) *
      (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) := by
    rw [qParam_zpow_eq_ratFuncX_zpow, mul_sub, ← zpow_add₀ hX, ← zpow_add₀ hX]
    norm_num
  have t1 := ratFuncX_zpow_mul_eq_qParam_twQForcingWeight 2
    (4 * ((r : ℤ) + s - r * s) * (n + 1) + 2) (1 * ((s : ℤ) + r - (r : ℤ) * s + 1))
    (n * (1 * ((s : ℤ) + r - (r : ℤ) * s))) (by ring)
  have t2 := ratFuncX_zpow_mul_eq_qParam_twQForcingWeight 2
    (4 * ((r : ℤ) - s - r * s) * (n + 1) - 2) (1 * ((r : ℤ) - s - (r : ℤ) * s + 0))
    (n * (1 * ((r : ℤ) - s - (r : ℤ) * s))) (by ring)
  have t3 := ratFuncX_zpow_mul_eq_qParam_twQForcingWeight 2
    (4 * ((s : ℤ) - r - r * s) * (n + 1) - 2) (1 * ((s : ℤ) - r - (r : ℤ) * s + 0))
    (n * (1 * ((s : ℤ) - r - (r : ℤ) * s))) (by ring)
  have t4 := ratFuncX_zpow_mul_eq_qParam_twQForcingWeight 2
    (-4 * ((r : ℤ) + s + r * s) * (n + 1) + 2) (1 * (-(s : ℤ) - r - (r : ℤ) * s + 1))
    (n * (1 * (-(s : ℤ) - r - (r : ℤ) * s))) (by ring)
  rw [hq1, pairQForcing, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ hD]
  linear_combination t1 - t2 - t3 + t4

/-- `(q⁻¹ - 1) H_-(q, q^n)` in the four monomials. -/
private theorem qParam_inv_sub_one_mul_bar_pairQForcing_twQForcingWeight (r s : ℕ) (n : ℤ) :
    (qParam ^ (-1 : ℤ) - 1) * twQBar (pairQForcing r s n) =
      1 * qParam ^ (-1 * ((s : ℤ) + r - (r : ℤ) * s + 1)) *
          qParam ^ (n * (-1 * ((s : ℤ) + r - (r : ℤ) * s))) +
        -1 * qParam ^ (-1 * ((r : ℤ) - s - (r : ℤ) * s + 0)) *
          qParam ^ (n * (-1 * ((r : ℤ) - s - (r : ℤ) * s))) +
        -1 * qParam ^ (-1 * ((s : ℤ) - r - (r : ℤ) * s + 0)) *
          qParam ^ (n * (-1 * ((s : ℤ) - r - (r : ℤ) * s))) +
        1 * qParam ^ (-1 * (-(s : ℤ) - r - (r : ℤ) * s + 1)) *
          qParam ^ (n * (-1 * (-(s : ℤ) - r - (r : ℤ) * s))) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hD : (RatFunc.X : RatFunc ℚ) ^ (-2 : ℤ) - RatFunc.X ^ (-(-2 : ℤ)) ≠ 0 := by
    intro h
    rw [neg_neg] at h
    exact ratFuncX_sq_sub_inv_sq_ne_zero (by linear_combination -h)
  have hq1 : qParam ^ (-1 : ℤ) - 1 = (RatFunc.X : RatFunc ℚ) ^ (-2 : ℤ) *
      (RatFunc.X ^ (-2 : ℤ) - RatFunc.X ^ (-(-2 : ℤ))) := by
    rw [qParam_zpow_eq_ratFuncX_zpow, mul_sub, ← zpow_add₀ hX, ← zpow_add₀ hX]
    norm_num
  have t1 := ratFuncX_zpow_mul_eq_qParam_twQForcingWeight (-2)
    (-(4 * ((r : ℤ) + s - r * s) * (n + 1) + 2)) (-1 * ((s : ℤ) + r - (r : ℤ) * s + 1))
    (n * (-1 * ((s : ℤ) + r - (r : ℤ) * s))) (by ring)
  have t2 := ratFuncX_zpow_mul_eq_qParam_twQForcingWeight (-2)
    (-(4 * ((r : ℤ) - s - r * s) * (n + 1) - 2)) (-1 * ((r : ℤ) - s - (r : ℤ) * s + 0))
    (n * (-1 * ((r : ℤ) - s - (r : ℤ) * s))) (by ring)
  have t3 := ratFuncX_zpow_mul_eq_qParam_twQForcingWeight (-2)
    (-(4 * ((s : ℤ) - r - r * s) * (n + 1) - 2)) (-1 * ((s : ℤ) - r - (r : ℤ) * s + 0))
    (n * (-1 * ((s : ℤ) - r - (r : ℤ) * s))) (by ring)
  have t4 := ratFuncX_zpow_mul_eq_qParam_twQForcingWeight (-2)
    (-(-4 * ((r : ℤ) + s + r * s) * (n + 1) + 2)) (-1 * (-(s : ℤ) - r - (r : ℤ) * s + 1))
    (n * (-1 * (-(s : ℤ) - r - (r : ℤ) * s))) (by ring)
  rw [hq1, pairQForcing]
  simp only [map_div₀, map_sub, map_add, twQBar_X_zpow]
  rw [mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ hD]
  linear_combination t1 - t2 - t3 + t4

/-- The forcing of the input in the four monomials: `H_η(q, q^n) = ∑_i c_i(q^η) q^(n η β_i)`. -/
theorem twForcing_eq_sum (η : Bool) (r s : ℕ) (ℓ : ℤ) (n : ℤ) :
    twForcing η r s ℓ n =
      qParam ^ (ℓ * (n + 1) * (n + 2)) *
        ∑ i : Fin 4, twCoef η r s i *
          qParam ^ (n * ((if η then 1 else -1) * (twLambda r s i - (r : ℤ) * s))) := by
  rw [twForcing]
  congr 1
  apply mul_left_cancel₀ (twCoefDen_ne_zero_twQForcingWeight η)
  rw [Finset.mul_sum]
  simp only [← mul_assoc (qParam ^ (if η then (1 : ℤ) else -1) - 1), twCoef_mul]
  rw [Fin.sum_univ_four]
  cases η
  · exact qParam_inv_sub_one_mul_bar_pairQForcing_twQForcingWeight r s n
  · exact qParam_sub_one_mul_pairQForcing_twQForcingWeight r s n

end AJConjecture
