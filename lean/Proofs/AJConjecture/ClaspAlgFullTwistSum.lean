import Mathlib
import AJConjecture.ClaspAlgPochForms
import AJConjecture.ClaspAlgQVandermonde

/-!
# The eigenvalues of the cabled full twist from the turnback expansion (identity J1′)

`∑_{k=0}^{c} s_k d_{k,n} = λ_{c,n}²` for `0 ≤ n ≤ c`.

Route: the summand vanishes for `k > c - n`, and for `k ≤ c - n` the ratio of consecutive
summands is `q (1 - q^(k-(c-n))) (1 - q^(k-(c+n+1))) / (1 - q^(k+1))`. So the sum is the terminating
`₂φ₁(q^(-(c-n)), q^(-(c+n+1)); 0; q, q)`, the case `C = 0` of the `q`-Chu–Vandermonde sum
(the expansion of a monomial `b^m` in the basis `(b; q)_k`). The hypothesis `n ≤ c` is needed.

In detail, with `P_m = (q; q)_m` and `m = c - n`: the summands with `k > m` vanish
(`claspAlgTurnbackEigen_eq_zero`); for `k ≤ m`, by `claspAlgFullTwistCoeff_eq_qPochhammer` and
`claspAlgTurnbackEigen_eq_qPochhammer`, the summand is
`t^(2c²-8ck+4k²-4k) P_(c-n) P_(c+n+1) / (P_k P_(c-n-k) P_(c+n+1-k))`.
Apply `claspAlg_qVandermonde m b 0` with `b = q^(-(c+n+1))`, where
`(b; q)_k = (-1)^k q^(k(k-1)/2 - (c+n+1)k) P_(c+n+1) / P_(c+n+1-k)` and
`∏_{s<m} q^s b = q^(m(m-1)/2 - (c+n+1)m)`; the powers of `t` agree because
`2c² - 4(c+n+1)(c-n) = 4n(n+1) - 2c(c+2)`.
-/

namespace AJConjecture

/-- `q^(j(j-1)/2) = t^(2j(j-1))`. -/
private theorem claspAlg_qParam_pow_triangle_fullTwistSum (j : ℕ) :
    qParam ^ (j * (j - 1) / 2) = (RatFunc.X : RatFunc ℚ) ^ (2 * (j : ℤ) * ((j : ℤ) - 1)) := by
  have h : 2 * (j * (j - 1) / 2) = j * (j - 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self j)
  generalize j * (j - 1) / 2 = T at h ⊢
  rw [claspAlg_qParam_pow]
  congr 1
  cases j with
  | zero =>
    have hT : T = 0 := by omega
    subst hT
    simp
  | succ j =>
    rw [Nat.add_sub_cancel] at h
    have h' : 2 * (T : ℤ) = ((j : ℤ) + 1) * j := by exact_mod_cast h
    push_cast
    linarith

/-- `(q^(-e); q)_k (q; q)_(e-k) = (-1)^k t^(2k(k-1) - 4ek) (q; q)_e` for `k ≤ e`. -/
private theorem claspAlg_qPochhammer_neg_pow_mul_fullTwistSum (e k : ℕ) (hk : k ≤ e) :
    qPochhammer (qParam ^ (-(e : ℤ))) k * qPochhammer qParam (e - k) =
      (-1) ^ k * (RatFunc.X : RatFunc ℚ) ^ (2 * (k : ℤ) * ((k : ℤ) - 1) - 4 * (e : ℤ) * (k : ℤ)) *
        qPochhammer qParam e := by
  induction k with
  | zero =>
    have h0 : qPochhammer (qParam ^ (-(e : ℤ))) 0 = 1 := Finset.prod_range_zero _
    rw [h0]
    simp
  | succ k ih =>
    have ih' := ih (by omega)
    obtain ⟨r, rfl⟩ : ∃ r, e = k + 1 + r := ⟨e - (k + 1), by omega⟩
    have e1 : k + 1 + r - k = r + 1 := by omega
    have e2 : k + 1 + r - (k + 1) = r := by omega
    have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
    have h1 : qPochhammer (qParam ^ (-((k + 1 + r : ℕ) : ℤ))) (k + 1) =
        qPochhammer (qParam ^ (-((k + 1 + r : ℕ) : ℤ))) k *
          (1 - qParam ^ (-((k + 1 + r : ℕ) : ℤ)) * qParam ^ k) :=
      Finset.prod_range_succ _ _
    have h2 : qPochhammer qParam (r + 1) = qPochhammer qParam r * (1 - qParam * qParam ^ r) :=
      Finset.prod_range_succ _ _
    have h3 : 1 - qParam ^ (-((k + 1 + r : ℕ) : ℤ)) * qParam ^ k =
        -((RatFunc.X : RatFunc ℚ) ^ (-(4 * ((r : ℤ) + 1))) * (1 - qParam * qParam ^ r)) := by
      have ha : qParam ^ (-((k + 1 + r : ℕ) : ℤ)) * qParam ^ k =
          (RatFunc.X : RatFunc ℚ) ^ (-(4 * ((r : ℤ) + 1))) := by
        rw [claspAlg_qParam_zpow, claspAlg_qParam_pow, ← zpow_add₀ hX]
        congr 1
        push_cast
        ring
      have hb : (RatFunc.X : RatFunc ℚ) ^ (-(4 * ((r : ℤ) + 1))) * (qParam * qParam ^ r) = 1 := by
        have h0 : -(4 * ((r : ℤ) + 1)) + 4 * ((r + 1 : ℕ) : ℤ) = 0 := by
          push_cast
          ring
        rw [← pow_succ', claspAlg_qParam_pow, ← zpow_add₀ hX, h0, zpow_zero]
      rw [ha, mul_sub, mul_one, hb]
      ring
    have h4 : (RatFunc.X : RatFunc ℚ) ^ (2 * ((k + 1 : ℕ) : ℤ) * (((k + 1 : ℕ) : ℤ) - 1) -
          4 * ((k + 1 + r : ℕ) : ℤ) * ((k + 1 : ℕ) : ℤ)) =
        RatFunc.X ^ (2 * (k : ℤ) * ((k : ℤ) - 1) - 4 * ((k + 1 + r : ℕ) : ℤ) * (k : ℤ)) *
          RatFunc.X ^ (-(4 * ((r : ℤ) + 1))) := by
      rw [← zpow_add₀ hX]
      congr 1
      push_cast
      ring
    rw [e1, h2] at ih'
    rw [e2, h1, h3, h4, pow_succ]
    linear_combination (-((RatFunc.X : RatFunc ℚ) ^ (-(4 * ((r : ℤ) + 1))))) * ih'

/-- The product side of the `q`-Chu–Vandermonde sum at `b = q^(-e)`, `C = 0`. -/
private theorem claspAlg_prod_qVandermonde_fullTwistSum (e m : ℕ) :
    ∏ s ∈ Finset.range m, qParam ^ s * (qParam ^ (-(e : ℤ)) - 0 * qParam ^ s) =
      (RatFunc.X : RatFunc ℚ) ^ (2 * (m : ℤ) * ((m : ℤ) - 1) - 4 * (e : ℤ) * (m : ℤ)) := by
  induction m with
  | zero =>
    rw [Finset.prod_range_zero]
    simp
  | succ m ih =>
    have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
    have hT : (RatFunc.X : RatFunc ℚ) ^ (2 * ((m + 1 : ℕ) : ℤ) * (((m + 1 : ℕ) : ℤ) - 1) -
          4 * (e : ℤ) * ((m + 1 : ℕ) : ℤ)) =
        RatFunc.X ^ (2 * (m : ℤ) * ((m : ℤ) - 1) - 4 * (e : ℤ) * (m : ℤ)) *
          (RatFunc.X ^ (4 * (m : ℤ)) * RatFunc.X ^ (4 * -(e : ℤ))) := by
      rw [← zpow_add₀ hX, ← zpow_add₀ hX]
      congr 1
      push_cast
      ring
    rw [Finset.prod_range_succ, ih, zero_mul, sub_zero, claspAlg_qParam_pow, claspAlg_qParam_zpow,
      hT]

/-- The rational identity that compares a summand of J1′ with a summand of the
`q`-Chu–Vandermonde sum. -/
private theorem claspAlg_fullTwistSum_term_algebra
    (sk T1 T3 T5 Q1 Pc Pk Pr Pm Pnr Pc1 Pc1k B : RatFunc ℚ)
    (hsk : sk = 1 ∨ sk = -1) (hT5 : T5 ≠ 0) (hQ1 : Q1 ≠ 0) (hPc : Pc ≠ 0) (hPk : Pk ≠ 0)
    (hPr : Pr ≠ 0) (hPnr : Pnr ≠ 0) (hPc1k : Pc1k ≠ 0) (hB : B * Pc1k = sk * T5 * Pc1) :
    sk * T1 * Pc ^ 2 / (Pnr ^ 2 * Pk) * (sk * T3 * Pm * Pc1 * Pnr ^ 2 / (Pr * Pc1k * Pc ^ 2)) =
      T1 * T3 / (Q1 * T5) * (sk * Q1 * (Pm / (Pk * Pr)) * 1 * B) := by
  obtain rfl : B = sk * T5 * Pc1 / Pc1k := eq_div_of_mul_eq hPc1k hB
  rcases hsk with rfl | rfl <;> field_simp

/-- A summand of J1′ is a constant multiple of a summand of the `q`-Chu–Vandermonde sum. -/
private theorem claspAlg_fullTwistSum_term (n m k : ℕ) (hk : k ≤ m) :
    claspAlgFullTwistCoeff (n + m) k * claspAlgTurnbackEigen (n + m) k n =
      (RatFunc.X : RatFunc ℚ) ^ (2 * ((n + m : ℕ) : ℤ) ^ 2 - 2 * (m : ℤ) * ((m : ℤ) - 1)) *
        ((-1) ^ k * qParam ^ ((m - k) * (m - k - 1) / 2) *
          (qPochhammer qParam m / (qPochhammer qParam k * qPochhammer qParam (m - k))) *
          qPochhammer (0 * qParam ^ k) (m - k) *
          qPochhammer (qParam ^ (-((n + m + n + 1 : ℕ) : ℤ))) k) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = k + r := ⟨m - k, by omega⟩
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have e1 : k + r - k = r := by omega
  have e2 : n + (k + r) - k = n + r := by omega
  have e3 : n + (k + r) - n = k + r := by omega
  have e5 : n + (k + r) + n + 1 - k = n + r + n + 1 := by omega
  have hFt := claspAlgFullTwistCoeff_eq_qPochhammer (n + (k + r)) k (by omega)
  have hTb := claspAlgTurnbackEigen_eq_qPochhammer (n + (k + r)) k n (by omega)
  rw [e2] at hFt
  rw [e3, e1, e5, e2] at hTb
  have hW : qPochhammer (0 * qParam ^ k) r = 1 := by
    rw [qPochhammer]
    refine Finset.prod_eq_one fun s _ ↦ ?_
    rw [zero_mul, zero_mul, sub_zero]
  have hB := claspAlg_qPochhammer_neg_pow_mul_fullTwistSum (n + (k + r) + n + 1) k (by omega)
  rw [e5] at hB
  have hE : (RatFunc.X : RatFunc ℚ) ^
        (2 * ((n + (k + r) : ℕ) : ℤ) ^ 2 - 2 * ((k + r : ℕ) : ℤ) * (((k + r : ℕ) : ℤ) - 1)) =
      RatFunc.X ^ (2 * ((n + (k + r) : ℕ) : ℤ) ^ 2 - 8 * ((n + (k + r) : ℕ) : ℤ) * (k : ℤ) +
            4 * (k : ℤ) ^ 2 - 2 * (k : ℤ)) *
          RatFunc.X ^ (-(2 * (k : ℤ))) /
        (RatFunc.X ^ (2 * (r : ℤ) * ((r : ℤ) - 1)) *
          RatFunc.X ^ (2 * (k : ℤ) * ((k : ℤ) - 1) -
            4 * ((n + (k + r) + n + 1 : ℕ) : ℤ) * (k : ℤ))) := by
    rw [← zpow_add₀ hX, ← zpow_add₀ hX, ← zpow_sub₀ hX]
    congr 1
    push_cast
    ring
  rw [hFt, hTb, e1, claspAlg_qParam_pow_triangle_fullTwistSum r, hE, hW]
  exact claspAlg_fullTwistSum_term_algebra _ _ _ _ _ _ _ _ _ _ _ _ _
    (neg_one_pow_eq_or _ k) (zpow_ne_zero _ hX) (zpow_ne_zero _ hX)
    (qPochhammer_qParam_ne_zero _) (qPochhammer_qParam_ne_zero _) (qPochhammer_qParam_ne_zero _)
    (qPochhammer_qParam_ne_zero _) (qPochhammer_qParam_ne_zero _) hB

/-- Identity J1′: the square of the eigenvalue of the cabled half twist is the turnback expansion
of the cabled full twist evaluated on the eigenvalues of the turnback elements. -/
theorem claspAlg_sum_fullTwistCoeff_mul_turnbackEigen (c n : ℕ) (hn : n ≤ c) :
    ∑ k ∈ Finset.range (c + 1), claspAlgFullTwistCoeff c k * claspAlgTurnbackEigen c k n =
      claspAlgHalfTwistEigen c n ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, c = n + m := ⟨c - n, by omega⟩
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  refine Eq.trans (Finset.sum_subset (Finset.range_mono (show m + 1 ≤ n + m + 1 by omega))
    fun k _ hk ↦ ?_).symm ?_
  · have hk' : m + 1 ≤ k := Nat.le_of_not_lt (Finset.mem_range.not.mp hk)
    rw [claspAlgTurnbackEigen_eq_zero (n + m) k n (by omega) (by omega), mul_zero]
  have hterm := fun k (hk : k ∈ Finset.range (m + 1)) ↦
    claspAlg_fullTwistSum_term n m k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have hs : ((-1 : RatFunc ℚ) ^ (n + m + n)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hT : (RatFunc.X : RatFunc ℚ) ^
        (2 * ((n + m : ℕ) : ℤ) ^ 2 - 2 * (m : ℤ) * ((m : ℤ) - 1)) *
        RatFunc.X ^ (2 * (m : ℤ) * ((m : ℤ) - 1) - 4 * ((n + m + n + 1 : ℕ) : ℤ) * (m : ℤ)) =
      (RatFunc.X ^ (2 * (n : ℤ) * ((n : ℤ) + 1) -
        ((n + m : ℕ) : ℤ) * (((n + m : ℕ) : ℤ) + 2))) ^ 2 := by
    rw [← zpow_add₀ hX, ← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, claspAlg_qVandermonde,
    claspAlg_prod_qVandermonde_fullTwistSum, claspAlgHalfTwistEigen, mul_pow, hs, one_mul, hT]

end AJConjecture
