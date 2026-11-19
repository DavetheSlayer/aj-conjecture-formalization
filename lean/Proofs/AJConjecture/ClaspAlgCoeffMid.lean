import Mathlib
import AJConjecture.ClaspAlgScalars
import AJConjecture.ClaspAlgSearsRight

/-!
# The clasp coefficient as the middle term of the Sears transformation

`claspAlgCoeff (c+1) n = t^(4c²+6c) Mid(n, c-n)` for `n ≤ c`.

Route: with `P_m = (q; q)_m` and `N = c + 1`, for `n ≤ j ≤ c`:
`C_j(N) = (q^(N+1); q)_j (q^(1-N); q)_j = (-1)^j q^(j(j+1)/2 - Nj) P_(N+j) P_(N-1) / (P_N P_(N-1-j))`,
`[N] = t^(-2c) (1 - q^N) / (1 - q)` and the definition of the bilateral kernel give
`[N] C_j(N) K_{j,n} = t^(-2c) (-1)^(n+j) q^(n(n+1)/2 + j(j+1)/2 - cj) P_(c+1+j) P_j / (P_(c-j) P_(j-n) P_(j+n+1))`.
Reindex `j = n + m` and apply `claspAlg_searsRight` with `M = c - n`; `t^(-2c) q^(c²+2c) = t^(4c²+6c)`.
-/

namespace AJConjecture

/-- The bilateral kernel at a natural index `0 ≤ n ≤ j`. -/
private theorem claspAlg_coeffMid_kernel (j n : ℕ) (hn : n ≤ j) :
    cycloBilateralKernel j (n : ℤ) =
      qParam ^ j * (1 - qParam) * qPochhammer qParam j * (-1) ^ n * qParam ^ (n * (n + 1) / 2) /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1)) := by
  have hE : (n : ℤ) * ((n : ℤ) + 1) / 2 = ((n * (n + 1) / 2 : ℕ) : ℤ) := by norm_cast
  rw [cycloBilateralKernel, ite_eq_left (by omega),
    show ((j : ℤ) - (n : ℤ)).toNat = j - n by omega,
    show ((j : ℤ) + (n : ℤ) + 1).toNat = j + n + 1 by omega, hE, zpow_natCast, zpow_natCast]

/-- The cyclotomic kernel at the colour `c + 1` in terms of `(q; q)_m`, for `j ≤ c`:
`C_j(c+1) P_(c+1) P_(c-j) = (-1)^j q^(j(j+1)/2 - (c+1)j) P_(c+1+j) P_c`. -/
private theorem claspAlg_coeffMid_cyclotomicKernel (c j : ℕ) (hj : j ≤ c) :
    cyclotomicKernel j ((c + 1 : ℕ) : ℤ) *
        (qPochhammer qParam (c + 1) * qPochhammer qParam (c - j)) =
      (-1) ^ j * qParam ^ (((j * (j + 1) / 2 : ℕ) : ℤ) - ((c + 1 : ℕ) : ℤ) * (j : ℤ)) *
        qPochhammer qParam (c + 1 + j) * qPochhammer qParam c := by
  induction j with
  | zero => simp [cyclotomicKernel]
  | succ j ih =>
    obtain ⟨r, rfl⟩ : ∃ r, c = j + 1 + r := ⟨c - (j + 1), by omega⟩
    have ih' := ih (by omega)
    have hq := qParam_ne_zero
    have hQ : qParam * qParam ^ r ≠ 0 := mul_ne_zero hq (pow_ne_zero r hq)
    have e1 : j + 1 + r - j = r + 1 := by omega
    have e2 : j + 1 + r - (j + 1) = r := by omega
    have hPr : qPochhammer qParam (r + 1) = qPochhammer qParam r * (1 - qParam * qParam ^ r) :=
      Finset.prod_range_succ _ _
    have hPt : qPochhammer qParam (j + 1 + r + 1 + (j + 1)) =
        qPochhammer qParam (j + 1 + r + 1 + j) * (1 - qParam * qParam ^ (j + 1 + r + 1 + j)) :=
      Finset.prod_range_succ _ _
    have hK : cyclotomicKernel (j + 1) ((j + 1 + r + 1 : ℕ) : ℤ) =
        cyclotomicKernel j ((j + 1 + r + 1 : ℕ) : ℤ) *
          ((1 - qParam ^ (((j + 1 : ℕ) : ℤ) + ((j + 1 + r + 1 : ℕ) : ℤ))) *
            (1 - qParam ^ (((j + 1 : ℕ) : ℤ) - ((j + 1 + r + 1 : ℕ) : ℤ)))) := by
      unfold cyclotomicKernel
      rw [Finset.prod_Icc_succ_top (by omega)]
    have hA : qParam ^ (((j + 1 : ℕ) : ℤ) + ((j + 1 + r + 1 : ℕ) : ℤ)) =
        qParam * qParam ^ (j + 1 + r + 1 + j) := by
      rw [← pow_succ', ← zpow_natCast]
      congr 1
      push_cast
      ring
    have hB : qParam ^ (((j + 1 : ℕ) : ℤ) - ((j + 1 + r + 1 : ℕ) : ℤ)) =
        (qParam * qParam ^ r)⁻¹ := by
      rw [← pow_succ', ← zpow_natCast, ← zpow_neg]
      congr 1
      push_cast
      ring
    have hE : qParam ^ ((((j + 1) * (j + 1 + 1) / 2 : ℕ) : ℤ) -
          ((j + 1 + r + 1 : ℕ) : ℤ) * ((j + 1 : ℕ) : ℤ)) =
        qParam ^ (((j * (j + 1) / 2 : ℕ) : ℤ) - ((j + 1 + r + 1 : ℕ) : ℤ) * (j : ℤ)) *
          (qParam * qParam ^ r)⁻¹ := by
      have g1 := claspAlg (j + 1)
      have g2 := claspAlg j
      rw [← pow_succ', ← zpow_natCast qParam (r + 1), ← zpow_neg, ← zpow_add₀ hq]
      congr 1
      simp only [Nat.cast_add, Nat.cast_one] at g1 ⊢
      refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
      linear_combination g1 - g2
    have hQinv : 1 - (qParam * qParam ^ r)⁻¹ =
        -(qParam * qParam ^ r)⁻¹ * (1 - qParam * qParam ^ r) := by
      field_simp
      ring
    rw [e1, hPr] at ih'
    rw [hK, hA, hB, hE, e2, hPt, pow_succ (-1 : RatFunc ℚ) j, hQinv]
    linear_combination
      (-(qParam * qParam ^ r)⁻¹ * (1 - qParam * qParam ^ (j + 1 + r + 1 + j))) * ih'

/-- The rational identity behind the termwise closed form of the clasp coefficient. -/
private theorem claspAlg_coeffMid_term_algebra
    (QN CK q qc Xc sj sn Ej E Qj Tn Pc1 Pc Pr Pcj Pj Pm PAm : RatFunc ℚ)
    (hQ : QN * (1 - q) = Xc * (1 - q * qc))
    (hC : CK * (Pc1 * Pr) = sj * Ej * Pcj * Pc)
    (hPc1 : Pc1 = Pc * (1 - q * qc)) (hE : Ej * Qj = E)
    (h1q : 1 - q ≠ 0) (hPc : Pc ≠ 0) (hqc : 1 - q * qc ≠ 0) (hPr : Pr ≠ 0) :
    QN * (CK * (Qj * (1 - q) * Pj * sn * Tn / (Pm * PAm))) =
      Xc * (sn * Tn * (sj * E * Pcj * Pj / (Pr * Pm * PAm))) := by
  have hQN : QN = Xc * (1 - q * qc) / (1 - q) := by
    rw [eq_div_iff h1q]
    exact hQ
  have hCK : CK = sj * Ej * Pcj * Pc / (Pc1 * Pr) := by
    rw [eq_div_iff (mul_ne_zero (hPc1 ▸ mul_ne_zero hPc hqc) hPr)]
    exact hC
  rw [hQN, hCK, hPc1, ← hE]
  field_simp

/-- The summand of index `j = n + m` of the clasp coefficient at the colour `c + 1`,
`c = n + (m + r)`, as a term of the cyclotomic side of the Sears transformation. -/
private theorem claspAlg_coeffMid_term (n m r : ℕ) :
    quantumInt ((n + (m + r) + 1 : ℕ) : ℤ) *
        (cyclotomicKernel (n + m) ((n + (m + r) + 1 : ℕ) : ℤ) *
          cycloBilateralKernel (n + m) (n : ℤ)) =
      (RatFunc.X : RatFunc ℚ) ^ (-(2 * ((n + (m + r) : ℕ) : ℤ))) *
        ((-1) ^ n * qParam ^ (n * (n + 1) / 2) *
          ((-1) ^ (n + m) *
            qParam ^ ((((n + m) * (n + m + 1) / 2 : ℕ) : ℤ) -
              ((n + (m + r) : ℕ) : ℤ) * ((n + m : ℕ) : ℤ)) *
            qPochhammer qParam (2 * n + (m + r) + 1 + m) * qPochhammer qParam (n + m) /
            (qPochhammer qParam (m + r - m) * qPochhammer qParam m *
              qPochhammer qParam (2 * n + 1 + m)))) := by
  have hq := qParam_ne_zero
  have hQ : quantumInt ((n + (m + r) + 1 : ℕ) : ℤ) * (1 - qParam) =
      (RatFunc.X : RatFunc ℚ) ^ (-(2 * ((n + (m + r) : ℕ) : ℤ))) *
        (1 - qParam * qParam ^ (n + (m + r))) := by
    rw [claspAlg_quantumInt_mul_one_sub_qParam, zpow_natCast, pow_succ']
    congr 2
    push_cast
    ring
  have hC := claspAlg_coeffMid_cyclotomicKernel (n + (m + r)) (n + m) (by omega)
  have hPc1 : qPochhammer qParam (n + (m + r) + 1) =
      qPochhammer qParam (n + (m + r)) * (1 - qParam * qParam ^ (n + (m + r))) :=
    Finset.prod_range_succ _ _
  have hE : qParam ^ ((((n + m) * (n + m + 1) / 2 : ℕ) : ℤ) -
        ((n + (m + r) + 1 : ℕ) : ℤ) * ((n + m : ℕ) : ℤ)) * qParam ^ (n + m) =
      qParam ^ ((((n + m) * (n + m + 1) / 2 : ℕ) : ℤ) -
        ((n + (m + r) : ℕ) : ℤ) * ((n + m : ℕ) : ℤ)) := by
    rw [← zpow_natCast qParam (n + m), ← zpow_add₀ hq]
    congr 1
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hqc : 1 - qParam * qParam ^ (n + (m + r)) ≠ 0 := by
    have h := one_sub_qParam_zpow_ne_zero (n := ((n + (m + r) : ℕ) : ℤ) + 1) (by omega)
    rwa [zpow_add_one₀ hq, zpow_natCast, mul_comm] at h
  rw [show n + (m + r) - (n + m) = r by omega,
    show n + (m + r) + 1 + (n + m) = 2 * n + (m + r) + 1 + m by omega] at hC
  rw [claspAlg_coeffMid_kernel (n + m) n (by omega), show n + m - n = m by omega,
    show n + m + n + 1 = 2 * n + 1 + m by omega, show m + r - m = r by omega]
  exact claspAlg_coeffMid_term_algebra _ _ qParam (qParam ^ (n + (m + r))) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hQ hC hPc1 hE claspAlg_one_sub_qParam_ne_zero (qPochhammer_qParam_ne_zero _) hqc
    (qPochhammer_qParam_ne_zero _)

/-- The clasp coefficient at the colour `c + 1` is `t^(4c²+6c)` times the middle term of the Sears
transformation. -/
theorem claspAlgCoeff_eq_searsMid (c n : ℕ) (hn : n ≤ c) :
    claspAlgCoeff (c + 1) n =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (c : ℤ) ^ 2 + 6 * (c : ℤ)) * claspAlgSearsMid n (c - n) := by
  obtain ⟨M, rfl⟩ : ∃ M, c = n + M := ⟨c - n, by omega⟩
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hterm : ∀ m ∈ Finset.range (M + 1),
      quantumInt ((n + M + 1 : ℕ) : ℤ) *
          (cyclotomicKernel (n + m) ((n + M + 1 : ℕ) : ℤ) * cycloBilateralKernel (n + m) (n : ℤ)) =
        (RatFunc.X : RatFunc ℚ) ^ (-(2 * ((n + M : ℕ) : ℤ))) *
          ((-1) ^ n * qParam ^ (n * (n + 1) / 2) *
            ((-1) ^ (n + m) *
              qParam ^ ((((n + m) * (n + m + 1) / 2 : ℕ) : ℤ) -
                ((n + M : ℕ) : ℤ) * ((n + m : ℕ) : ℤ)) *
              qPochhammer qParam (2 * n + M + 1 + m) * qPochhammer qParam (n + m) /
              (qPochhammer qParam (M - m) * qPochhammer qParam m *
                qPochhammer qParam (2 * n + 1 + m)))) := by
    intro m hm
    obtain ⟨r, rfl⟩ : ∃ r, M = m + r := ⟨M - m, by have := Finset.mem_range.mp hm; omega⟩
    exact claspAlg_coeffMid_term n m r
  have hpow : (RatFunc.X : RatFunc ℚ) ^ (-(2 * ((n + M : ℕ) : ℤ))) *
      qParam ^ ((n + M) ^ 2 + 2 * (n + M)) =
        RatFunc.X ^ (4 * ((n + M : ℕ) : ℤ) ^ 2 + 6 * ((n + M : ℕ) : ℤ)) := by
    rw [claspAlg_qParam_pow, ← zpow_add₀ hX]
    congr 1
    push_cast
    ring
  rw [claspAlgCoeff, Finset.sum_Ico_eq_sum_range, show n + M + 1 - n = M + 1 by omega,
    Finset.mul_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.mul_sum,
    claspAlg_searsRight n M, show n + M - n = M by omega, ← hpow]
  ring

end AJConjecture
