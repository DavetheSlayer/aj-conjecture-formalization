import Mathlib
import AJConjecture.QAlgCycloBilateralKernel
import AJConjecture.QAlgQBinomial

/-!
# Vanishing moments of the bilateral kernel

`∑_n K_(j,n) q^(nk) = 0` for `|k| ≤ j`: with `m = n + j + 1` the sum is a multiple of
`(q^(k-j); q)_(2j+1)` by the finite `q`-binomial theorem, and one of the factors
`1 - q^(k-j+i)`, `0 ≤ i ≤ 2j`, vanishes.
-/

namespace AJConjecture

/-- The exponent of `q` in the `m`-th term of the moment sum, with `n = m - j - 1`:
`n(n+1)/2 + nk = m(m-1)/2 + (k-j)m + (j(j+1)/2 - (j+1)k)`. -/
private theorem kernel_moment_exponent (j m : ℕ) (k : ℤ) :
    ((m : ℤ) - ((j : ℤ) + 1)) * ((m : ℤ) - ((j : ℤ) + 1) + 1) / 2 + ((m : ℤ) - ((j : ℤ) + 1)) * k =
      ((m * (m - 1) / 2 : ℕ) : ℤ) + (k - j) * m +
        (((j * (j + 1) / 2 : ℕ) : ℤ) - ((j : ℤ) + 1) * k) := by
  have he : 2 * (((m : ℤ) - ((j : ℤ) + 1)) * ((m : ℤ) - ((j : ℤ) + 1) + 1) / 2) =
      ((m : ℤ) - ((j : ℤ) + 1)) * ((m : ℤ) - ((j : ℤ) + 1) + 1) :=
    Int.mul_ediv_cancel' (Int.even_mul_succ_self _).two_dvd
  have ha : 2 * ((m * (m - 1) / 2 : ℕ) : ℤ) = (m : ℤ) * ((m : ℤ) - 1) := by
    have h := Nat.mul_div_cancel' (Nat.even_mul_pred_self m).two_dvd
    have h' : (2 : ℤ) * ((m * (m - 1) / 2 : ℕ) : ℤ) = ((m * (m - 1) : ℕ) : ℤ) := by
      exact_mod_cast h
    rw [h']
    cases m with
    | zero => simp
    | succ m =>
      push_cast
      simp
  have hb : 2 * ((j * (j + 1) / 2 : ℕ) : ℤ) = (j : ℤ) * ((j : ℤ) + 1) := by
    have h := Nat.mul_div_cancel' (Nat.even_mul_succ_self j).two_dvd
    exact_mod_cast h
  refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
  linear_combination he - ha - hb

/-- The sign `(-1)^(m - i)` for natural numbers `m`, `i`. -/
private theorem neg_one_zpow_natCast_sub (m i : ℕ) :
    (-1 : RatFunc ℚ) ^ ((m : ℤ) - (i : ℤ)) = (-1) ^ m * (-1) ^ i := by
  have h1 : ((-1 : RatFunc ℚ) ^ i) * (-1) ^ i = 1 := by
    rw [← mul_pow]
    simp
  rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast,
    div_eq_iff (pow_ne_zero _ (by norm_num)), mul_assoc, h1, mul_one]

/-- The rational identity that puts a term of the moment sum in the form of a term of the
`q`-binomial sum. -/
private theorem kernel_moment_term_algebra (c sm sj E R qa zm Cq PN Pm Pr : RatFunc ℚ)
    (hPN : PN ≠ 0) (hPm : Pm ≠ 0) (hPr : Pr ≠ 0) (h : E * R = qa * zm * Cq) :
    c * (sm * sj) * E / (Pr * Pm) * R =
      c * sj * Cq / PN * (sm * qa * zm * (PN / (Pm * Pr))) := by
  have h1 : c * (sm * sj) * E / (Pr * Pm) * R = c * (sm * sj) * (E * R) / (Pr * Pm) := by ring
  rw [h1, h]
  field_simp

/-- A term of the moment sum, indexed by `m = n + j + 1`, is a constant multiple of a term of
the `q`-binomial sum with `N = 2j + 1` and `z = q^(k-j)`. -/
private theorem kernel_moment_term (j m : ℕ) (k : ℤ) (hm : m ≤ 2 * j + 1) :
    cycloBilateralKernel j ((m : ℤ) - ((j : ℤ) + 1)) * qParam ^ (((m : ℤ) - ((j : ℤ) + 1)) * k) =
      qParam ^ j * (1 - qParam) * qPochhammer qParam j * (-1) ^ (j + 1) *
          qParam ^ (((j * (j + 1) / 2 : ℕ) : ℤ) - ((j : ℤ) + 1) * k) /
          qPochhammer qParam (2 * j + 1) *
        ((-1) ^ m * qParam ^ (m * (m - 1) / 2) * (qParam ^ (k - j)) ^ m *
          (qPochhammer qParam (2 * j + 1) /
            (qPochhammer qParam m * qPochhammer qParam (2 * j + 1 - m)))) := by
  have hq := qParam_ne_zero
  have hc : -((j : ℤ) + 1) ≤ (m : ℤ) - ((j : ℤ) + 1) ∧ (m : ℤ) - ((j : ℤ) + 1) ≤ j := by omega
  have e1 : ((j : ℤ) - ((m : ℤ) - ((j : ℤ) + 1))).toNat = 2 * j + 1 - m := by omega
  have e2 : ((j : ℤ) + ((m : ℤ) - ((j : ℤ) + 1)) + 1).toNat = m := by omega
  have hs : (-1 : RatFunc ℚ) ^ ((m : ℤ) - ((j : ℤ) + 1)) = (-1) ^ m * (-1) ^ (j + 1) := by
    rw [← neg_one_zpow_natCast_sub]
    push_cast
    rfl
  have hpow : qParam ^ (((m : ℤ) - ((j : ℤ) + 1)) * ((m : ℤ) - ((j : ℤ) + 1) + 1) / 2) *
      qParam ^ (((m : ℤ) - ((j : ℤ) + 1)) * k) =
        qParam ^ (m * (m - 1) / 2) * (qParam ^ (k - j)) ^ m *
          qParam ^ (((j * (j + 1) / 2 : ℕ) : ℤ) - ((j : ℤ) + 1) * k) := by
    rw [← zpow_add₀ hq, kernel_moment_exponent, zpow_add₀ hq, zpow_add₀ hq, zpow_natCast,
      zpow_mul, zpow_natCast]
  rw [cycloBilateralKernel, ite_eq_left hc, e1, e2, hs]
  exact kernel_moment_term_algebra _ _ _ _ _ _ _ _ _ _ _ (qPochhammer_qParam_ne_zero _)
    (qPochhammer_qParam_ne_zero _) (qPochhammer_qParam_ne_zero _) hpow

/-- `(q^(k-j); q)_(2j+1) = 0` for `|k| ≤ j`: the factor of index `j - k` vanishes. -/
private theorem qPochhammer_zpow_eq_zero_of_abs_le {j : ℕ} {k : ℤ} (hk : |k| ≤ j) :
    qPochhammer (qParam ^ (k - j)) (2 * j + 1) = 0 := by
  have hk' := abs_le.mp hk
  refine Finset.prod_eq_zero (i := ((j : ℤ) - k).toNat) (Finset.mem_range.mpr (by omega)) ?_
  rw [← zpow_natCast qParam, ← zpow_add₀ qParam_ne_zero,
    show k - j + (((j : ℤ) - k).toNat : ℤ) = 0 by omega, zpow_zero, sub_self]

/-- The moments of degree `|k| ≤ j` of the bilateral kernel vanish. -/
theorem cycloBilateralSum_zpow_eq_zero {j : ℕ} {k : ℤ} (hk : |k| ≤ j) :
    cycloBilateralSum (fun n ↦ qParam ^ (n * k)) j = 0 := by
  have hre : ∑ n ∈ Finset.Icc (-((j : ℤ) + 1)) (j : ℤ),
      cycloBilateralKernel j n * qParam ^ (n * k) =
        ∑ m ∈ Finset.range (2 * j + 1 + 1), cycloBilateralKernel j ((m : ℤ) - ((j : ℤ) + 1)) *
          qParam ^ (((m : ℤ) - ((j : ℤ) + 1)) * k) := by
    symm
    refine Finset.sum_nbij' (fun m ↦ (m : ℤ) - ((j : ℤ) + 1)) (fun n ↦ (n + ((j : ℤ) + 1)).toNat)
      ?_ ?_ ?_ ?_ ?_
    · intro m hm
      have := Finset.mem_range.mp hm
      exact Finset.mem_Icc.mpr (by omega)
    · intro n hn
      have := Finset.mem_Icc.mp hn
      exact Finset.mem_range.mpr (by omega)
    · intro m _
      omega
    · intro n hn
      have := Finset.mem_Icc.mp hn
      change (((n + ((j : ℤ) + 1)).toNat : ℕ) : ℤ) - ((j : ℤ) + 1) = n
      omega
    · intro m _
      rfl
  rw [cycloBilateralSum, hre, Finset.sum_congr rfl fun m hm ↦
    kernel_moment_term j m k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)), ← Finset.mul_sum,
    sum_qBinomial_eq_qPochhammer, qPochhammer_zpow_eq_zero_of_abs_le hk, mul_zero]

end AJConjecture
