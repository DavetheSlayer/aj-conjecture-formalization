import Mathlib
import AJFamily.Skein.TorusOddColorOne
import AJFamily.Skein.TorusReducedFormulaTwo

/-!
# The colour-2 formula separates the torus knots

`torusWhiteheadFormula_two_injective`: for `a, b ≥ 3`, equal values of `torusWhiteheadFormula` at
`2` force `a = b`. The value at `2` determines the first odd colour `u_1` of `T(2, a)`, and
`q^(4a) u_1` is a polynomial in `X` with constant term `1`. If `u_1` agreed for `a < b`, then
`q^(4(b-a))` times the polynomial for `a` would equal the polynomial for `b`, which fails at
`X = 0`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- `q` is the image of the polynomial `X⁴` under `ℚ[X] → ℚ(X)`. -/
private theorem algebraMap_X_pow_four_eq_qParam :
    algebraMap ℚ[X] (RatFunc ℚ) ((Polynomial.X : ℚ[X]) ^ 4) = qParam := by
  rw [map_pow, RatFunc.algebraMap_X, qParam]

/-- `[3] q = 1 + q + q²`. -/
private theorem quantumInt_three_mul_qParam :
    quantumInt 3 * qParam = 1 + qParam + qParam ^ 2 := by
  have h := claspAlg_quantumInt_mul_one_sub_qParam 3
  rw [zpow_ofNat] at h
  have hX : (RatFunc.X : RatFunc ℚ) ^ (2 - 2 * (3 : ℤ)) * qParam = 1 := by
    rw [← zpow_one qParam, claspAlg_qParam_zpow, ← zpow_add₀ RatFunc.X_ne_zero]
    norm_num
  have h1 := claspAlg_one_sub_qParam_ne_zero
  apply mul_right_cancel₀ h1
  linear_combination qParam * h + (1 - qParam ^ 3) * hX

/-- `[5] q² = 1 + q + q² + q³ + q⁴`. -/
private theorem quantumInt_five_mul_qParam_sq :
    quantumInt 5 * qParam ^ 2 = 1 + qParam + qParam ^ 2 + qParam ^ 3 + qParam ^ 4 := by
  have h := claspAlg_quantumInt_mul_one_sub_qParam 5
  rw [zpow_ofNat] at h
  have hX : (RatFunc.X : RatFunc ℚ) ^ (2 - 2 * (5 : ℤ)) * qParam ^ 2 = 1 := by
    rw [← zpow_natCast qParam 2, claspAlg_qParam_zpow, ← zpow_add₀ RatFunc.X_ne_zero]
    norm_num
  have h1 := claspAlg_one_sub_qParam_ne_zero
  apply mul_right_cancel₀ h1
  linear_combination qParam ^ 2 * h + (1 - qParam ^ 5) * hX

/-- The polynomial `q^(4c) u₁(c)` for `c = d + 2`, written in the variable `X` with `q = X⁴`. -/
private def torusOddColorOnePoly (d : ℕ) : ℚ[X] :=
  1 - (X ^ 4) ^ (d + 1) - (X ^ 4) ^ (d + 2) - (X ^ 4) ^ (d + 3) + (X ^ 4) ^ (3 * d + 4) +
    (X ^ 4) ^ (3 * d + 5) + (X ^ 4) ^ (3 * d + 6) + (X ^ 4) ^ (3 * d + 7) + (X ^ 4) ^ (3 * d + 8)

/-- The constant term of `torusOddColorOnePoly d` is `1`. -/
private theorem eval_zero_torusOddColorOnePoly (d : ℕ) :
    (torusOddColorOnePoly d).eval 0 = 1 := by
  simp [torusOddColorOnePoly]

/-- `q^(4c) u₁(c)` is the image of `torusOddColorOnePoly (c - 2)`. -/
private theorem qParam_pow_mul_torusOddColor_one (d : ℕ) :
    qParam ^ (4 * (d + 2)) * torusOddColor (d + 2) 1 =
      algebraMap ℚ[X] (RatFunc ℚ) (torusOddColorOnePoly d) := by
  have hq : qParam ≠ 0 := pow_ne_zero 4 RatFunc.X_ne_zero
  have e1 : qParam ^ (-(4 * (((d + 2 : ℕ)) : ℤ))) = (qParam ^ (4 * (d + 2)))⁻¹ := by
    rw [zpow_neg, ← zpow_natCast]
    push_cast
    rfl
  have e2 : qParam ^ (((d + 2 : ℕ)) : ℤ) = qParam ^ (d + 2) := zpow_natCast _ _
  have e3 : qParam ^ (3 * (((d + 2 : ℕ)) : ℤ)) = qParam ^ (3 * d + 6) := by
    rw [← zpow_natCast]
    push_cast
    ring_nf
  rw [torusOddColor_one, e1, e2, e3, mul_inv_cancel_left₀ (pow_ne_zero _ hq)]
  have hφ (n : ℕ) : algebraMap ℚ[X] (RatFunc ℚ) (((X : ℚ[X]) ^ 4) ^ n) = qParam ^ n := by
    rw [map_pow, algebraMap_X_pow_four_eq_qParam]
  simp only [torusOddColorOnePoly, map_add, map_sub, map_one, hφ]
  linear_combination (-qParam ^ (d + 1)) * quantumInt_three_mul_qParam +
    qParam ^ (3 * d + 4) * quantumInt_five_mul_qParam_sq

/-- The first odd colour separates the torus knots `T(2, c)` with `c ≥ 2`. -/
private theorem torusOddColor_one_ne_of_lt {d e : ℕ} (hde : d < e) :
    torusOddColor (d + 2) 1 ≠ torusOddColor (e + 2) 1 := by
  intro h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hde
  have hφ : algebraMap ℚ[X] (RatFunc ℚ) (((X : ℚ[X]) ^ 4) ^ (4 * (k + 1))) =
      qParam ^ (4 * (k + 1)) := by
    rw [map_pow, algebraMap_X_pow_four_eq_qParam]
  have key : algebraMap ℚ[X] (RatFunc ℚ)
      (((X : ℚ[X]) ^ 4) ^ (4 * (k + 1)) * torusOddColorOnePoly d) =
        algebraMap ℚ[X] (RatFunc ℚ) (torusOddColorOnePoly (d + k + 1)) := by
    rw [map_mul, hφ, ← qParam_pow_mul_torusOddColor_one, ← qParam_pow_mul_torusOddColor_one, h,
      ← mul_assoc, ← pow_add]
    ring_nf
  have h0 := congrArg (Polynomial.eval 0) (RatFunc.algebraMap_injective ℚ key)
  simp [eval_zero_torusOddColorOnePoly] at h0

/-- `1 + q ≠ 0`. -/
private theorem one_add_qParam_ne_zero_torusJones : 1 + qParam ≠ 0 := by
  rw [← algebraMap_X_pow_four_eq_qParam, ← map_one (algebraMap ℚ[X] (RatFunc ℚ)), ← map_add]
  refine (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).mpr fun h0 ↦ ?_
  have h1 := congrArg (Polynomial.eval 0) h0
  simp at h1

/-- The unreduced formula at `n = 2` determines the torus knot `T(2, a)`, `a ≥ 3`. -/
theorem torusWhiteheadFormula_two_injective (a b : ℕ) (ha : 3 ≤ a) (hb : 3 ≤ b)
    (h : torusWhiteheadFormula a 2 = torusWhiteheadFormula b 2) : a = b := by
  have hq : qParam ≠ 0 := pow_ne_zero 4 RatFunc.X_ne_zero
  have hF : torusReducedFormula a 2 = torusReducedFormula b 2 := by
    have h2 : quantumInt 2 ≠ 0 := claspAlg_quantumInt_ne_zero (by norm_num)
    have ht : (2 : ℤ).toNat = 2 := rfl
    simp only [torusWhiteheadFormula, show (0 : ℤ) < 2 by norm_num, ite_true, ht] at h
    exact mul_left_cancel₀ h2 h
  rw [torusReducedFormula_two, torusReducedFormula_two,
    div_left_inj₀ one_add_qParam_ne_zero_torusJones] at hF
  have hu : torusOddColor a 1 = torusOddColor b 1 :=
    mul_left_cancel₀ claspAlg_one_sub_qParam_ne_zero (add_left_cancel (mul_left_cancel₀ hq hF))
  obtain ⟨d, rfl⟩ : ∃ d, a = d + 2 := ⟨a - 2, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, b = e + 2 := ⟨b - 2, by omega⟩
  rcases lt_trichotomy d e with hde | hde | hde
  · exact absurd hu (torusOddColor_one_ne_of_lt hde)
  · rw [hde]
  · exact absurd hu.symm (torusOddColor_one_ne_of_lt hde)

end AJConjecture
