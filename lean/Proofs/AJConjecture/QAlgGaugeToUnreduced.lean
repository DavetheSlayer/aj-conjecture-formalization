import Mathlib
import AJConjecture.QAlgOpApplyFieldBasic

/-!
# Gauge from a sequence `g` to the sequence `[n] g(n)`

Multiplying the coefficient of `L^k` of an operator of degree `r` by
`t^(2k) ∏_{l ≤ r, l ≠ k} (t^(4l) M² - 1)` turns an annihilator of `g` into an annihilator of
`n ↦ [n] g(n)`: `[n + k] (t^(4k) M² - 1)⁻¹` is, up to `t^(-2k)`, independent of `k` at
`M = t^(2n)`.
-/

open Polynomial

namespace AJConjecture

/-- The weight `t^(2k) ∏_{l ≤ r, l ≠ k} (t^(4l) M² - 1)` multiplying the coefficient of `L^k`. -/
private noncomputable def quantumGaugeWeight (r k : ℕ) : Coeff :=
  C (X ^ (2 * k)) * ∏ l ∈ (Finset.range (r + 1)).erase k, (C (X ^ (4 * l)) * X ^ 2 - 1)

/-- The value of `t^(4l) M² - 1` at the colour `n`. -/
private theorem evalAtField_quantumGaugeFactor (n : ℤ) (l : ℕ) :
    evalAtField n (C (X ^ (4 * l)) * X ^ 2 - 1 : Coeff) =
      RatFunc.X ^ (4 * l) * (RatFunc.X ^ (2 * n)) ^ 2 - 1 := by
  simp only [evalAtField, coe_eval₂RingHom, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow,
    eval₂_one]

/-- The factor `t^(4l) M² - 1` is not zero. -/
private theorem quantumGaugeFactor_ne_zero (l : ℕ) :
    (C (X ^ (4 * l)) * X ^ 2 - 1 : Coeff) ≠ 0 := by
  intro h0
  have h1 := congrArg (fun p : Coeff ↦ p.coeff 2) h0
  simp only [coeff_sub, coeff_C_mul, coeff_X_pow, coeff_one, coeff_zero] at h1
  norm_num at h1

/-- The gauge weight is not zero. -/
private theorem quantumGaugeWeight_ne_zero (r k : ℕ) : quantumGaugeWeight r k ≠ 0 :=
  mul_ne_zero (C_ne_zero.mpr (pow_ne_zero _ X_ne_zero))
    (Finset.prod_ne_zero_iff.mpr fun l _ ↦ quantumGaugeFactor_ne_zero l)

/-- `t^(2k) [n + k] = t^(-2n) (t² - t⁻²)⁻¹ (t^(4k) M² - 1)` at `M = t^(2n)`. -/
private theorem ratFuncX_pow_mul_quantumInt_add (n : ℤ) (k : ℕ) :
    (RatFunc.X : RatFunc ℚ) ^ (2 * k) * quantumInt (n + k) =
      RatFunc.X ^ (-(2 * n)) * (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))⁻¹ *
        (RatFunc.X ^ (4 * k) * (RatFunc.X ^ (2 * n)) ^ 2 - 1) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have e1 : (RatFunc.X : RatFunc ℚ) ^ (2 * (n + k)) =
      RatFunc.X ^ n * RatFunc.X ^ n * (RatFunc.X ^ k * RatFunc.X ^ k) := by
    have h2 : (2 * (n + k) : ℤ) = n + n + (k + k) := by ring
    rw [h2, zpow_add₀ hX, zpow_add₀ hX, zpow_add₀ hX, zpow_natCast]
  have e2 : (RatFunc.X : RatFunc ℚ) ^ (2 * n) = RatFunc.X ^ n * RatFunc.X ^ n := by
    rw [two_mul, zpow_add₀ hX]
  have e3 : (RatFunc.X : RatFunc ℚ) ^ (2 * k) = RatFunc.X ^ k * RatFunc.X ^ k := by
    rw [two_mul, pow_add]
  have e4 : (RatFunc.X : RatFunc ℚ) ^ (4 * k) =
      RatFunc.X ^ k * RatFunc.X ^ k * (RatFunc.X ^ k * RatFunc.X ^ k) := by
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  have hT : (RatFunc.X : RatFunc ℚ) ^ n ≠ 0 := zpow_ne_zero _ hX
  have hS : (RatFunc.X : RatFunc ℚ) ^ k ≠ 0 := pow_ne_zero _ hX
  rw [quantumInt, zpow_neg, zpow_neg, zpow_neg, e1, e2, e3, e4, div_eq_mul_inv]
  generalize ((RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - (RatFunc.X ^ (2 : ℤ))⁻¹)⁻¹ = c
  generalize (RatFunc.X : RatFunc ℚ) ^ n = T at hT ⊢
  generalize (RatFunc.X : RatFunc ℚ) ^ k = S at hS ⊢
  field_simp

/-- The value of the gauge weight at the colour `n`, times `[n + k]`, does not depend on `k`. -/
private theorem evalAtField_quantumGaugeWeight_mul_quantumInt (r : ℕ) (n : ℤ) {k : ℕ}
    (hk : k ∈ Finset.range (r + 1)) :
    evalAtField n (quantumGaugeWeight r k) * quantumInt (n + k) =
      RatFunc.X ^ (-(2 * n)) * (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))⁻¹ *
        ∏ l ∈ Finset.range (r + 1), (RatFunc.X ^ (4 * l) * (RatFunc.X ^ (2 * n)) ^ 2 - 1) := by
  have hC : evalAtField n (C (X ^ (2 * k)) : Coeff) = RatFunc.X ^ (2 * k) := by
    simp only [evalAtField, coe_eval₂RingHom, eval₂_C, eval₂_X, eval₂_pow]
  rw [quantumGaugeWeight, map_mul, map_prod, hC, ← Finset.mul_prod_erase _ _ hk,
    Finset.prod_congr rfl fun l _ ↦ evalAtField_quantumGaugeFactor n l,
    mul_right_comm, ratFuncX_pow_mul_quantumInt_add, mul_assoc]

/-- The action of an operator given by its coefficients up to a degree. -/
private theorem opApplyField_sum_range_monomial_mul (N : ℕ) (c : ℕ → Coeff) (f : ℤ → RatFunc ℚ)
    (n : ℤ) :
    opApplyField (∑ k ∈ Finset.range N, monomial k (c k)) f n =
      ∑ k ∈ Finset.range N, evalAtField n (c k) * f (n + k) := by
  induction N with
  | zero => simp [opApplyField]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, opApplyField_add_left, ih,
      opApplyField_monomial]

/-- Every operator `Q₀` has a gauge transform `Q`, nonzero when `Q₀` is, that annihilates
`n ↦ [n] g(n)` at every colour where `Q₀` annihilates `g`. -/
theorem exists_gauge_quantumInt_mul (Q₀ : RecOp) :
    ∃ Q : RecOp, (Q₀ ≠ 0 → Q ≠ 0) ∧ ∀ (g : ℤ → RatFunc ℚ) (n : ℤ),
      opApplyField Q₀ g n = 0 → opApplyField Q (fun m ↦ quantumInt m * g m) n = 0 := by
  set r : ℕ := Q₀.natDegree with hr
  refine ⟨∑ k ∈ Finset.range (r + 1), monomial k (Q₀.coeff k * quantumGaugeWeight r k),
    fun hQ₀ hzero ↦ ?_, fun g n hann ↦ ?_⟩
  · have h0 : (∑ k ∈ Finset.range (r + 1),
        monomial k (Q₀.coeff k * quantumGaugeWeight r k)).coeff r = 0 := by
      rw [hzero, coeff_zero]
    rw [finsetSum_coeff, Finset.sum_eq_single r
      (fun k _ hk ↦ coeff_monomial_of_ne _ (Ne.symm hk))
      (fun h ↦ absurd (Finset.mem_range.mpr (Nat.lt_succ_self r)) h), coeff_monomial_same] at h0
    exact mul_ne_zero (by rw [hr, coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hQ₀)
      (quantumGaugeWeight_ne_zero r r) h0
  · rw [opApplyField_eq_sum_range, ← hr] at hann
    rw [opApplyField_sum_range_monomial_mul]
    have hmul := congrArg (fun x ↦ RatFunc.X ^ (-(2 * n)) *
      (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))⁻¹ *
        (∏ l ∈ Finset.range (r + 1), (RatFunc.X ^ (4 * l) * (RatFunc.X ^ (2 * n)) ^ 2 - 1)) *
          x) hann
    simp only [mul_zero, Finset.mul_sum] at hmul
    rw [← hmul]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [← evalAtField_quantumGaugeWeight_mul_quantumInt r n hk, map_mul]
    ring

end AJConjecture
