import Mathlib
import AJConjecture.ClaspAlgPochForms
import AJConjecture.ClaspAlgSearsLeft

/-!
# The clasp eigenvalue as the middle term of the Sears transformation

`(-1)^c θ_c² ξ_{c,n} = t^(4c²+6c) Mid(n, c-n)` for `n ≤ c`, with `θ_c² = t^(2c(c+2))`.

Route: with `P_m = (q; q)_m`, the closed forms
`s_k = (-1)^k t^(2c²-8ck+4k²-2k) P_c² / (P_(c-k)² P_k)` for `k ≤ c`
(`claspAlgFullTwistCoeff_eq_qPochhammer`),
`d_{j,n} = (-1)^j t^(-2j) P_(c-n) P_(c+n+1) P_(c-j)² / (P_(c-n-j) P_(c+n+1-j) P_c²)` for `j ≤ c - n`
(`claspAlgTurnbackEigen_eq_qPochhammer`) and `d_{j,n} = 0` for `c - n < j`
(`claspAlgTurnbackEigen_eq_zero`). Hence the summand of `ξ_{c,n}` vanishes for
`k < n` and, for `n ≤ k ≤ c`,
`(-1)^c t^(2c(c+2)) s_k d_{c-k,n} = t^(4c²+2c) q^(k²-2ck) P_(c-n) P_(c+n+1) P_k / (P_(c-k)² P_(k-n) P_(k+n+1))`.
Reindex `k = n + m` and apply `claspAlg_searsLeft` with `M = c - n`; `t^(4c²+2c) q^c = t^(4c²+6c)`.
-/

namespace AJConjecture

/-- The rational identity behind the termwise closed form of the normalised clasp eigenvalue:
`sk`, `sr` are signs, `Xa`, `Xb`, `Xd`, `Xg`, `E` powers of `t`, and the `P`'s are `q`-Pochhammer
symbols. -/
private theorem claspAlg_claspEigen_term_algebra
    (sk sr Xa Xb Xd Xg E Pc Pr Pk PM PN Pm PAm : RatFunc ℚ)
    (hsk : sk * sk = 1) (hsr : sr * sr = 1) (hpow : Xa * Xb * Xd = Xg * E)
    (hPc : Pc ≠ 0) (hPk : Pk ≠ 0) (hPr : Pr ≠ 0) (hPm : Pm ≠ 0) (hPAm : PAm ≠ 0) :
    sk * sr * Xa * (sk * Xb * Pc ^ 2 / (Pr ^ 2 * Pk) *
        (sr * Xd * PM * PN * Pk ^ 2 / (Pm * PAm * Pc ^ 2))) =
      Xg * (PM * PN * (E * Pk / (Pr ^ 2 * Pm * PAm))) := by
  have h1 : Pc ^ 2 / (Pr ^ 2 * Pk) * (Pk ^ 2 / (Pm * PAm * Pc ^ 2)) = Pk / (Pr ^ 2 * Pm * PAm) := by
    field_simp
  have key : sk * sr * Xa * (sk * Xb * Pc ^ 2 / (Pr ^ 2 * Pk) *
      (sr * Xd * PM * PN * Pk ^ 2 / (Pm * PAm * Pc ^ 2))) =
      (sk * sk) * (sr * sr) * (Xa * Xb * Xd) * (PM * PN) *
        (Pc ^ 2 / (Pr ^ 2 * Pk) * (Pk ^ 2 / (Pm * PAm * Pc ^ 2))) := by
    ring
  rw [key, h1, hsk, hsr, hpow]
  ring

/-- The summand of index `k = n + m` of the normalised clasp eigenvalue at `c = n + (m + r)`, as
a term of the turnback side of the Sears transformation. -/
private theorem claspAlg_claspEigen_term (n m r : ℕ) :
    (-1) ^ (n + (m + r)) *
        (RatFunc.X : RatFunc ℚ) ^ (2 * ((n + (m + r) : ℕ) : ℤ) * (((n + (m + r) : ℕ) : ℤ) + 2)) *
        (claspAlgFullTwistCoeff (n + (m + r)) (n + m) *
          claspAlgTurnbackEigen (n + (m + r)) (n + (m + r) - (n + m)) n) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * ((n + (m + r) : ℕ) : ℤ) ^ 2 + 2 * ((n + (m + r) : ℕ) : ℤ)) *
        (qPochhammer qParam (m + r) * qPochhammer qParam (2 * n + (m + r) + 1) *
          (qParam ^ (((n + m : ℕ) : ℤ) ^ 2 - 2 * ((n + (m + r) : ℕ) : ℤ) * ((n + m : ℕ) : ℤ)) *
            qPochhammer qParam (n + m) /
            (qPochhammer qParam (m + r - m) ^ 2 * qPochhammer qParam m *
              qPochhammer qParam (2 * n + 1 + m)))) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hsk : (-1 : RatFunc ℚ) ^ (n + m) * (-1) ^ (n + m) = 1 := by
    rw [← mul_pow]
    norm_num
  have hsr : (-1 : RatFunc ℚ) ^ r * (-1) ^ r = 1 := by
    rw [← mul_pow]
    norm_num
  have hsgn : (-1 : RatFunc ℚ) ^ (n + (m + r)) = (-1) ^ (n + m) * (-1) ^ r := by
    rw [← pow_add, Nat.add_assoc]
  have hpow : (RatFunc.X : RatFunc ℚ) ^ (2 * ((n + (m + r) : ℕ) : ℤ) * (((n + (m + r) : ℕ) : ℤ) + 2)) *
      RatFunc.X ^ (2 * ((n + (m + r) : ℕ) : ℤ) ^ 2 - 8 * ((n + (m + r) : ℕ) : ℤ) * ((n + m : ℕ) : ℤ) +
        4 * ((n + m : ℕ) : ℤ) ^ 2 - 2 * ((n + m : ℕ) : ℤ)) *
      RatFunc.X ^ (-(2 * (r : ℤ))) =
      RatFunc.X ^ (4 * ((n + (m + r) : ℕ) : ℤ) ^ 2 + 2 * ((n + (m + r) : ℕ) : ℤ)) *
        qParam ^ (((n + m : ℕ) : ℤ) ^ 2 - 2 * ((n + (m + r) : ℕ) : ℤ) * ((n + m : ℕ) : ℤ)) := by
    rw [claspAlg_qParam_zpow, ← zpow_add₀ hX, ← zpow_add₀ hX, ← zpow_add₀ hX]
    congr 1
    push_cast
    ring
  rw [show n + (m + r) - (n + m) = r by omega,
    claspAlgFullTwistCoeff_eq_qPochhammer (n + (m + r)) (n + m) (by omega),
    claspAlgTurnbackEigen_eq_qPochhammer (n + (m + r)) r n (by omega),
    show n + (m + r) - (n + m) = r by omega, show n + (m + r) - n = m + r by omega,
    show n + (m + r) + n + 1 = 2 * n + (m + r) + 1 by omega, show n + (m + r) - r = n + m by omega,
    show m + r - r = m by omega, show 2 * n + (m + r) + 1 - r = 2 * n + 1 + m by omega,
    show m + r - m = r by omega, hsgn]
  exact claspAlg_claspEigen_term_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsk hsr hpow
    (qPochhammer_qParam_ne_zero _) (qPochhammer_qParam_ne_zero _) (qPochhammer_qParam_ne_zero _)
    (qPochhammer_qParam_ne_zero _) (qPochhammer_qParam_ne_zero _)

/-- The normalised clasp eigenvalue is `t^(4c²+6c)` times the middle term of the Sears
transformation. -/
theorem claspAlgClaspEigen_eq_searsMid (c n : ℕ) (hn : n ≤ c) :
    (-1) ^ c * (RatFunc.X : RatFunc ℚ) ^ (2 * (c : ℤ) * ((c : ℤ) + 2)) * claspAlgClaspEigen c n =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (c : ℤ) ^ 2 + 6 * (c : ℤ)) * claspAlgSearsMid n (c - n) := by
  obtain ⟨M, rfl⟩ : ∃ M, c = n + M := ⟨c - n, by omega⟩
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hzero : ∑ k ∈ Finset.range n,
      claspAlgFullTwistCoeff (n + M) k * claspAlgTurnbackEigen (n + M) (n + M - k) n = 0 := by
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    have hk' := Finset.mem_range.mp hk
    rw [claspAlgTurnbackEigen_eq_zero (n + M) (n + M - k) n (by omega) (by omega), mul_zero]
  have hterm : ∀ m ∈ Finset.range (M + 1),
      (-1) ^ (n + M) *
          (RatFunc.X : RatFunc ℚ) ^ (2 * ((n + M : ℕ) : ℤ) * (((n + M : ℕ) : ℤ) + 2)) *
          (claspAlgFullTwistCoeff (n + M) (n + m) *
            claspAlgTurnbackEigen (n + M) (n + M - (n + m)) n) =
        (RatFunc.X : RatFunc ℚ) ^ (4 * ((n + M : ℕ) : ℤ) ^ 2 + 2 * ((n + M : ℕ) : ℤ)) *
          (qPochhammer qParam M * qPochhammer qParam (2 * n + M + 1) *
            (qParam ^ (((n + m : ℕ) : ℤ) ^ 2 - 2 * ((n + M : ℕ) : ℤ) * ((n + m : ℕ) : ℤ)) *
              qPochhammer qParam (n + m) /
              (qPochhammer qParam (M - m) ^ 2 * qPochhammer qParam m *
                qPochhammer qParam (2 * n + 1 + m)))) := by
    intro m hm
    obtain ⟨r, rfl⟩ : ∃ r, M = m + r := ⟨M - m, by have := Finset.mem_range.mp hm; omega⟩
    exact claspAlg_claspEigen_term n m r
  have hpow : (RatFunc.X : RatFunc ℚ) ^ (4 * ((n + M : ℕ) : ℤ) ^ 2 + 2 * ((n + M : ℕ) : ℤ)) *
      qParam ^ (n + M) =
        RatFunc.X ^ (4 * ((n + M : ℕ) : ℤ) ^ 2 + 6 * ((n + M : ℕ) : ℤ)) := by
    rw [claspAlg_qParam_pow, ← zpow_add₀ hX]
    congr 1
    ring
  rw [claspAlgClaspEigen, show n + M + 1 = n + (M + 1) by omega, Finset.sum_range_add, hzero,
    zero_add, Finset.mul_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.mul_sum,
    claspAlg_searsLeft n M, show n + M - n = M by omega, ← hpow]
  ring

end AJConjecture
