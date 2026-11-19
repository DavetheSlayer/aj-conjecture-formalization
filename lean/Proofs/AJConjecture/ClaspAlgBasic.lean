import Mathlib
import AJConjecture.QAlgQParamBasic

/-!
# Basic facts on powers of `q = t⁴` and on quantum integers

Conversions between the two languages of the clasp computation: powers of `q` are powers of `t`,
`[−m] = −[m]`, and `[m] (1 - q) = t^(2 - 2m) (1 - q^m)`, so that products of quantum integers are
`q`-Pochhammer symbols up to an explicit power of `t`; and `(q; q)_a (q^(a+1); q)_k = (q; q)_(a+k)`.
-/

namespace AJConjecture

/-- An integer power of `q` is an integer power of `t`: `q^e = t^(4e)`. -/
theorem claspAlg_qParam_zpow (e : ℤ) : qParam ^ e = (RatFunc.X : RatFunc ℚ) ^ (4 * e) := by
  rw [qParam, ← zpow_natCast, ← zpow_mul]
  rfl

/-- A natural power of `q` is an integer power of `t`: `q^e = t^(4e)`. -/
theorem claspAlg_qParam_pow (e : ℕ) : qParam ^ e = (RatFunc.X : RatFunc ℚ) ^ (4 * (e : ℤ)) := by
  rw [← zpow_natCast, claspAlg_qParam_zpow]

/-- The quantum integers are odd: `[-m] = -[m]`. -/
theorem claspAlg_quantumInt_neg (m : ℤ) : quantumInt (-m) = -quantumInt m := by
  simp only [quantumInt, mul_neg, neg_neg]
  ring

/-- The denominator `t² - t⁻²` of the quantum integers is not zero. -/
theorem claspAlg_ratFuncX_sq_sub_ne_zero :
    (RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ) ≠ 0 := by
  intro h
  have h2 : (2 : ℤ) = -2 := ratFuncX_zpow_injective (sub_eq_zero.mp h)
  omega

/-- `1 - q ≠ 0`. -/
theorem claspAlg_one_sub_qParam_ne_zero : 1 - qParam ≠ 0 := by
  have h := one_sub_qParam_zpow_ne_zero (n := 1) (by norm_num)
  rwa [zpow_one] at h

/-- The quantum integer in the variable `q`: `[m] (1 - q) = t^(2 - 2m) (1 - q^m)`. -/
theorem claspAlg_quantumInt_mul_one_sub_qParam (m : ℤ) :
    quantumInt m * (1 - qParam) = (RatFunc.X : RatFunc ℚ) ^ (2 - 2 * m) * (1 - qParam ^ m) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hD := claspAlg_ratFuncX_sq_sub_ne_zero
  have hq1 : (1 : RatFunc ℚ) - qParam = -(RatFunc.X ^ (2 : ℤ) * (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))) := by
    have h4 : qParam = (RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) * RatFunc.X ^ (2 : ℤ) := by
      rw [← zpow_add₀ hX, qParam, ← zpow_natCast]
      rfl
    have h0 : (RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) * RatFunc.X ^ (-2 : ℤ) = 1 := by
      rw [← zpow_add₀ hX]
      norm_num
    rw [h4, mul_sub, h0]
    ring
  have hqm : (RatFunc.X : RatFunc ℚ) ^ (2 - 2 * m) * (1 - qParam ^ m) =
      -(RatFunc.X ^ (2 : ℤ) * (RatFunc.X ^ (2 * m) - RatFunc.X ^ (-(2 * m)))) := by
    have ha : (RatFunc.X : RatFunc ℚ) ^ (2 - 2 * m) = RatFunc.X ^ (2 : ℤ) * RatFunc.X ^ (-(2 * m)) := by
      rw [← zpow_add₀ hX]
      congr 1
    have hb : (RatFunc.X : RatFunc ℚ) ^ (-(2 * m)) * qParam ^ m = RatFunc.X ^ (2 * m) := by
      rw [claspAlg_qParam_zpow, ← zpow_add₀ hX]
      congr 1
      ring
    rw [ha, mul_sub, mul_one, mul_assoc, hb]
    ring
  rw [hqm, hq1, quantumInt, div_mul_eq_mul_div, div_eq_iff hD]
  ring

/-- A quantum integer with a nonzero argument is not zero. -/
theorem claspAlg_quantumInt_ne_zero {m : ℤ} (hm : m ≠ 0) : quantumInt m ≠ 0 := by
  intro h
  have h1 := claspAlg_quantumInt_mul_one_sub_qParam m
  rw [h, zero_mul] at h1
  rcases mul_eq_zero.mp h1.symm with h2 | h2
  · exact zpow_ne_zero _ RatFunc.X_ne_zero h2
  · exact one_sub_qParam_zpow_ne_zero hm h2

/-- `(q; q)_a (q^(a+1); q)_k = (q; q)_(a+k)`. -/
theorem claspAlg_qPochhammer_mul_shift (a k : ℕ) :
    qPochhammer qParam a * qPochhammer (qParam ^ (a + 1)) k = qPochhammer qParam (a + k) := by
  induction k with
  | zero =>
    have h0 : qPochhammer (qParam ^ (a + 1)) 0 = 1 := Finset.prod_range_zero _
    rw [h0, mul_one, Nat.add_zero]
  | succ k ih =>
    have h1 : qPochhammer (qParam ^ (a + 1)) (k + 1) =
        qPochhammer (qParam ^ (a + 1)) k * (1 - qParam ^ (a + 1) * qParam ^ k) :=
      Finset.prod_range_succ _ _
    have h2 : qPochhammer qParam (a + k + 1) =
        qPochhammer qParam (a + k) * (1 - qParam * qParam ^ (a + k)) :=
      Finset.prod_range_succ _ _
    rw [h1, ← Nat.add_assoc, h2, ← ih]
    ring

end AJConjecture
