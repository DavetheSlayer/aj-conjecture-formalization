import Mathlib
import AJConjecture.ClaspAlgBasic
import AJConjecture.ClaspAlgScalars

/-!
# The scalars of the clasp computation as `q`-Pochhammer symbols

With `P_m = (q; q)_m`, `q = t⁴`, the identity `[m] (1 - q) = t^(2-2m) (1 - q^m)`
(`claspAlg_quantumInt_mul_one_sub_qParam`) turns products of quantum integers into quotients of
`q`-Pochhammer symbols:

* `[k]! = t^(-k(k-1)) P_k / (1 - q)^k`;
* `[c choose k] = t^(-2k(c-k)) P_c / (P_k P_(c-k))` for `k ≤ c`;
* `s_k = (-1)^k t^(2c²-8ck+4k²-2k) P_c² / (P_(c-k)² P_k)` for `k ≤ c`;
* `d_{j,n} = (-1)^j t^(-2j) P_(c-n) P_(c+n+1) P_(c-j)² / (P_(c-n-j) P_(c+n+1-j) P_c²)` for `j + n ≤ c`,
  and `d_{j,n} = 0` for `n ≤ c < j + n` (the factor `[0]`).

Each is an induction on the length of the product; `P_(m+1) = P_m (1 - q q^m)`.
-/

namespace AJConjecture

/-- The quantum factorial cleared of its denominator:
`[k]! (1 - q)^k = t^(-k(k-1)) (q; q)_k`. -/
private theorem claspAlgQFactorial_mul_one_sub_pow_pochForms (k : ℕ) :
    claspAlgQFactorial k * (1 - qParam) ^ k =
      (RatFunc.X : RatFunc ℚ) ^ (-((k : ℤ) * ((k : ℤ) - 1))) * qPochhammer qParam k := by
  induction k with
  | zero =>
    have h1 : claspAlgQFactorial 0 = 1 := Finset.prod_range_zero _
    have h2 : qPochhammer qParam 0 = 1 := Finset.prod_range_zero _
    rw [h1, h2]
    simp
  | succ k ih =>
    have h1 : claspAlgQFactorial (k + 1) = claspAlgQFactorial k * quantumInt ((k : ℤ) + 1) :=
      Finset.prod_range_succ _ _
    have h2 : qPochhammer qParam (k + 1) = qPochhammer qParam k * (1 - qParam * qParam ^ k) :=
      Finset.prod_range_succ _ _
    have h3 := claspAlg_quantumInt_mul_one_sub_qParam ((k : ℤ) + 1)
    have h4 : qParam ^ ((k : ℤ) + 1) = qParam * qParam ^ k := by
      rw [zpow_add_one₀ qParam_ne_zero, zpow_natCast, mul_comm]
    have h5 : (RatFunc.X : RatFunc ℚ) ^ (-(((k + 1 : ℕ) : ℤ) * (((k + 1 : ℕ) : ℤ) - 1))) =
        RatFunc.X ^ (-((k : ℤ) * ((k : ℤ) - 1))) * RatFunc.X ^ (2 - 2 * ((k : ℤ) + 1)) := by
      rw [← zpow_add₀ RatFunc.X_ne_zero]
      congr 1
      push_cast
      ring
    rw [h1, h2, h5, pow_succ, ← h4]
    calc claspAlgQFactorial k * quantumInt ((k : ℤ) + 1) * ((1 - qParam) ^ k * (1 - qParam))
        = claspAlgQFactorial k * (1 - qParam) ^ k *
            (quantumInt ((k : ℤ) + 1) * (1 - qParam)) := by ring
      _ = _ := by
        rw [ih, h3]
        ring

/-- The quantum factorial as a `q`-Pochhammer symbol, with the exponent of `t` an integer
expression. -/
private theorem claspAlgQFactorial_eq_div_pochForms (k : ℕ) :
    claspAlgQFactorial k =
      (RatFunc.X : RatFunc ℚ) ^ (-((k : ℤ) * ((k : ℤ) - 1))) * qPochhammer qParam k /
        (1 - qParam) ^ k := by
  rw [eq_div_iff (pow_ne_zero k claspAlg_one_sub_qParam_ne_zero)]
  exact claspAlgQFactorial_mul_one_sub_pow_pochForms k

/-- `t² - t⁻² = -(1 - q) t⁻²`. -/
private theorem claspAlg_ratFuncX_sq_sub_eq_pochForms :
    (RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ) =
      -((1 - qParam) * RatFunc.X ^ (-2 : ℤ)) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h4 : qParam * (RatFunc.X : RatFunc ℚ) ^ (-2 : ℤ) = RatFunc.X ^ (2 : ℤ) := by
    rw [qParam, ← zpow_natCast, ← zpow_add₀ hX]
    rfl
  rw [sub_mul, one_mul, h4]
  ring

/-- The rational identity behind the closed form of the full-twist coefficient. -/
private theorem claspAlg_fullTwistCoeff_algebra_pochForms
    (s T0 T2 Xc Xr Xk Pc Pr Pk Dk Dr : RatFunc ℚ)
    (hXr : Xr ≠ 0) (hXk : Xk ≠ 0) (hPr : Pr ≠ 0) (hPk : Pk ≠ 0) (hDk : Dk ≠ 0) (hDr : Dr ≠ 0) :
    T0 * (s * (Dk * T2)) * (Xc * Pc / (Dk * Dr)) ^ 2 / ((Xr * Pr / Dr) ^ 2 * (Xk * Pk / Dk)) =
      s * (T0 * T2 * Xc ^ 2 / (Xr ^ 2 * Xk)) * Pc ^ 2 / (Pr ^ 2 * Pk) := by
  field_simp

/-- The full-twist coefficient as a quotient of `q`-Pochhammer symbols:
`s_k = (-1)^k t^(2c²-8ck+4k²-2k) (q; q)_c² / ((q; q)_(c-k)² (q; q)_k)` for `k ≤ c`. -/
theorem claspAlgFullTwistCoeff_eq_qPochhammer (c k : ℕ) (hk : k ≤ c) :
    claspAlgFullTwistCoeff c k =
      (-1) ^ k *
        (RatFunc.X : RatFunc ℚ) ^
          (2 * (c : ℤ) ^ 2 - 8 * (c : ℤ) * (k : ℤ) + 4 * (k : ℤ) ^ 2 - 2 * (k : ℤ)) *
        qPochhammer qParam c ^ 2 / (qPochhammer qParam (c - k) ^ 2 * qPochhammer qParam k) := by
  obtain ⟨r, rfl⟩ : ∃ r, c = k + r := ⟨c - k, by omega⟩
  have e1 : k + r - k = r := by omega
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hD : (1 : RatFunc ℚ) - qParam ≠ 0 := claspAlg_one_sub_qParam_ne_zero
  have hY : ((RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) ^ k =
      (-1) ^ k * ((1 - qParam) ^ k * RatFunc.X ^ (-(2 * (k : ℤ)))) := by
    have hz : ((RatFunc.X : RatFunc ℚ) ^ (-2 : ℤ)) ^ k = RatFunc.X ^ (-(2 * (k : ℤ))) := by
      rw [show -(2 * (k : ℤ)) = (-2 : ℤ) * (k : ℤ) by ring, zpow_mul, zpow_natCast]
    rw [claspAlg_ratFuncX_sq_sub_eq_pochForms, neg_eq_neg_one_mul, mul_pow, mul_pow, hz]
  have hT : (RatFunc.X : RatFunc ℚ) ^ (2 * ((k + r : ℕ) : ℤ) ^ 2 -
        8 * ((k + r : ℕ) : ℤ) * (k : ℤ) + 4 * (k : ℤ) ^ 2 - 2 * (k : ℤ)) =
      RatFunc.X ^ (2 * ((k + r : ℕ) : ℤ) ^ 2 - 4 * ((k + r : ℕ) : ℤ) * (k : ℤ) + (k : ℤ) ^ 2 -
          (k : ℤ)) * RatFunc.X ^ (-(2 * (k : ℤ))) *
        (RatFunc.X ^ (-(((k + r : ℕ) : ℤ) * (((k + r : ℕ) : ℤ) - 1)))) ^ 2 /
        ((RatFunc.X ^ (-((r : ℤ) * ((r : ℤ) - 1)))) ^ 2 *
          RatFunc.X ^ (-((k : ℤ) * ((k : ℤ) - 1)))) := by
    rw [← zpow_natCast (RatFunc.X ^ (-(((k + r : ℕ) : ℤ) * (((k + r : ℕ) : ℤ) - 1)))) 2,
      ← zpow_natCast (RatFunc.X ^ (-((r : ℤ) * ((r : ℤ) - 1)))) 2, ← zpow_mul, ← zpow_mul,
      ← zpow_add₀ hX, ← zpow_add₀ hX, ← zpow_add₀ hX, ← zpow_sub₀ hX]
    congr 1
    push_cast
    ring
  rw [claspAlgFullTwistCoeff, e1, claspAlgQFactorial_eq_div_pochForms (k + r),
    claspAlgQFactorial_eq_div_pochForms k, claspAlgQFactorial_eq_div_pochForms r, hT, hY,
    pow_add]
  exact claspAlg_fullTwistCoeff_algebra_pochForms _ _ _ _ _ _ _ _ _ _ _ (zpow_ne_zero _ hX)
    (zpow_ne_zero _ hX) (qPochhammer_qParam_ne_zero r) (qPochhammer_qParam_ne_zero k)
    (pow_ne_zero k hD) (pow_ne_zero r hD)

/-- The rational identity behind the induction step for the turnback eigenvalue. -/
private theorem claspAlg_turnbackEigen_step_algebra_pochForms
    (s T Ta Tb Tc F1 F2 F3 D Pm Pc1 Pa Pb Pd Pc : RatFunc ℚ)
    (hTc : Tc ≠ 0) (hF1 : F1 ≠ 0) (hF2 : F2 ≠ 0) (hF3 : F3 ≠ 0) (hD : D ≠ 0) (hPa : Pa ≠ 0)
    (hPb : Pb ≠ 0) (hPc : Pc ≠ 0) :
    s * T * Pm * Pc1 * (Pd * F3) ^ 2 / (Pa * F1 * (Pb * F2) * Pc ^ 2) *
        (-(Ta * F1 / D * (Tb * F2 / D)) / (Tc * F3 / D) ^ 2) =
      s * -1 * (T * Ta * Tb / Tc ^ 2) * Pm * Pc1 * Pd ^ 2 / (Pa * Pb * Pc ^ 2) := by
  field_simp

/-- The turnback eigenvalue as a quotient of `q`-Pochhammer symbols, for `j + n ≤ c`. -/
theorem claspAlgTurnbackEigen_eq_qPochhammer (c j n : ℕ) (hj : j + n ≤ c) :
    claspAlgTurnbackEigen c j n =
      (-1) ^ j * (RatFunc.X : RatFunc ℚ) ^ (-(2 * (j : ℤ))) * qPochhammer qParam (c - n) *
        qPochhammer qParam (c + n + 1) * qPochhammer qParam (c - j) ^ 2 /
        (qPochhammer qParam (c - n - j) * qPochhammer qParam (c + n + 1 - j) *
          qPochhammer qParam c ^ 2) := by
  induction j with
  | zero =>
    have h1 : claspAlgTurnbackEigen c 0 n = 1 := Finset.prod_range_zero _
    rw [h1, pow_zero, Nat.cast_zero, mul_zero, neg_zero, zpow_zero, Nat.sub_zero, Nat.sub_zero,
      Nat.sub_zero, one_mul, one_mul]
    have h2 := qPochhammer_qParam_ne_zero (c - n)
    have h3 := qPochhammer_qParam_ne_zero (c + n + 1)
    have h4 := qPochhammer_qParam_ne_zero c
    field_simp
  | succ j ih =>
    have ih' := ih (by omega)
    obtain ⟨r, rfl⟩ : ∃ r, c = j + 1 + n + r := ⟨c - (j + 1 + n), by omega⟩
    have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
    have hD : (1 : RatFunc ℚ) - qParam ≠ 0 := claspAlg_one_sub_qParam_ne_zero
    have hstep : claspAlgTurnbackEigen (j + 1 + n + r) (j + 1) n =
        claspAlgTurnbackEigen (j + 1 + n + r) j n *
          (-(quantumInt (((j + 1 + n + r : ℕ) : ℤ) - n - j) *
              quantumInt (((j + 1 + n + r : ℕ) : ℤ) + n + 1 - j)) /
            quantumInt (((j + 1 + n + r : ℕ) : ℤ) - j) ^ 2) :=
      Finset.prod_range_succ _ _
    -- the three quantum integers
    have hA : quantumInt (((j + 1 + n + r : ℕ) : ℤ) - n - j) =
        RatFunc.X ^ (2 - 2 * (((j + 1 + n + r : ℕ) : ℤ) - n - j)) *
          (1 - qParam * qParam ^ r) / (1 - qParam) := by
      rw [eq_div_iff hD, claspAlg_quantumInt_mul_one_sub_qParam]
      congr 2
      rw [← zpow_natCast, ← zpow_one_add₀ qParam_ne_zero]
      congr 1
      push_cast
      ring
    have hB : quantumInt (((j + 1 + n + r : ℕ) : ℤ) + n + 1 - j) =
        RatFunc.X ^ (2 - 2 * (((j + 1 + n + r : ℕ) : ℤ) + n + 1 - j)) *
          (1 - qParam * qParam ^ (n + n + 1 + r)) / (1 - qParam) := by
      rw [eq_div_iff hD, claspAlg_quantumInt_mul_one_sub_qParam]
      congr 2
      rw [← zpow_natCast, ← zpow_one_add₀ qParam_ne_zero]
      congr 1
      push_cast
      ring
    have hC : quantumInt (((j + 1 + n + r : ℕ) : ℤ) - j) =
        RatFunc.X ^ (2 - 2 * (((j + 1 + n + r : ℕ) : ℤ) - j)) *
          (1 - qParam * qParam ^ (n + r)) / (1 - qParam) := by
      rw [eq_div_iff hD, claspAlg_quantumInt_mul_one_sub_qParam]
      congr 2
      rw [← zpow_natCast, ← zpow_one_add₀ qParam_ne_zero]
      congr 1
      push_cast
      ring
    -- the index arithmetic
    have e1 : j + 1 + n + r - n - j = r + 1 := by omega
    have e2 : j + 1 + n + r + n + 1 - j = n + n + 1 + r + 1 := by omega
    have e3 : j + 1 + n + r - j = n + r + 1 := by omega
    have e4 : j + 1 + n + r - n - (j + 1) = r := by omega
    have e5 : j + 1 + n + r + n + 1 - (j + 1) = n + n + 1 + r := by omega
    have e6 : j + 1 + n + r - (j + 1) = n + r := by omega
    have hP1 : qPochhammer qParam (r + 1) = qPochhammer qParam r * (1 - qParam * qParam ^ r) :=
      Finset.prod_range_succ _ _
    have hP2 : qPochhammer qParam (n + n + 1 + r + 1) =
        qPochhammer qParam (n + n + 1 + r) * (1 - qParam * qParam ^ (n + n + 1 + r)) :=
      Finset.prod_range_succ _ _
    have hP3 : qPochhammer qParam (n + r + 1) =
        qPochhammer qParam (n + r) * (1 - qParam * qParam ^ (n + r)) :=
      Finset.prod_range_succ _ _
    have hT : (RatFunc.X : RatFunc ℚ) ^ (-(2 * ((j + 1 : ℕ) : ℤ))) =
        RatFunc.X ^ (-(2 * (j : ℤ))) *
          RatFunc.X ^ (2 - 2 * (((j + 1 + n + r : ℕ) : ℤ) - n - j)) *
          RatFunc.X ^ (2 - 2 * (((j + 1 + n + r : ℕ) : ℤ) + n + 1 - j)) /
          (RatFunc.X ^ (2 - 2 * (((j + 1 + n + r : ℕ) : ℤ) - j))) ^ 2 := by
      rw [← zpow_natCast (RatFunc.X ^ (2 - 2 * (((j + 1 + n + r : ℕ) : ℤ) - j))) 2, ← zpow_mul,
        ← zpow_add₀ hX, ← zpow_add₀ hX, ← zpow_sub₀ hX]
      congr 1
      push_cast
      ring
    have hF : ∀ s : ℕ, (1 : RatFunc ℚ) - qParam * qParam ^ s ≠ 0 := by
      intro s
      have h := one_sub_qParam_zpow_ne_zero (n := (s : ℤ) + 1) (by omega)
      rwa [zpow_add_one₀ qParam_ne_zero, zpow_natCast, mul_comm] at h
    rw [hstep, ih', hA, hB, hC, e1, e2, e3, e4, e5, e6, hP1, hP2, hP3, hT, pow_succ]
    exact claspAlg_turnbackEigen_step_algebra_pochForms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (zpow_ne_zero _ hX) (hF _) (hF _) (hF _) hD (qPochhammer_qParam_ne_zero _)
      (qPochhammer_qParam_ne_zero _) (qPochhammer_qParam_ne_zero _)

/-- The turnback eigenvalue `d_{j,n}` vanishes for `j > c - n`: the product contains `[0]`. -/
theorem claspAlgTurnbackEigen_eq_zero (c j n : ℕ) (hn : n ≤ c) (hj : c < j + n) :
    claspAlgTurnbackEigen c j n = 0 := by
  unfold claspAlgTurnbackEigen
  refine Finset.prod_eq_zero (i := c - n) (Finset.mem_range.mpr (by omega)) ?_
  have h0 : (c : ℤ) - (n : ℤ) - ((c - n : ℕ) : ℤ) = 0 := by omega
  have hq0 : quantumInt 0 = 0 := by simp [quantumInt]
  rw [h0, hq0, zero_mul, neg_zero, zero_div]

end AJConjecture
