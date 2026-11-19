import Mathlib
import AJConjecture.QAlgQParamBasic

/-!
# The `q`-Chu–Vandermonde sum

For arbitrary `b`, `C` in `ℚ(t)` and `q = t⁴`:
`∑_{k=0}^{m} (-1)^k q^((m-k)(m-k-1)/2) [m choose k]_q (C q^k; q)_(m-k) (b; q)_k = ∏_{s<m} q^s (b - C q^s)`,
with the Gaussian binomial coefficient written as `(q;q)_m / ((q;q)_k (q;q)_(m-k))`. After division
by `q^(m(m-1)/2)` this is `₂φ₁(q^(-m), b; C; q, q) = (C/b; q)_m b^m / (C; q)_m`; for `C = 0` it is the
expansion of `q^(m(m-1)/2) b^m` in the basis `(b; q)_k`.

Proof: induction on `m`. Multiplication of `(b; q)_k` by `q^m (b - C q^m)` is
`(q^(m-k) - C q^(2m)) (b; q)_k - q^(m-k) (b; q)_(k+1)`, and the coefficients satisfy the corresponding
three-term relation (the `q`-Pascal rule).
-/

namespace AJConjecture

/-- The coefficient of `(b; q)_k` in the `q`-Chu–Vandermonde sum of length `m + 1`. -/
private noncomputable def claspAlgVdmCoeff (C : RatFunc ℚ) (m k : ℕ) : RatFunc ℚ :=
  (-1) ^ k * qParam ^ ((m - k) * (m - k - 1) / 2) *
    (qPochhammer qParam m / (qPochhammer qParam k * qPochhammer qParam (m - k))) *
    qPochhammer (C * qParam ^ k) (m - k)

/-- The first factor of a `q`-Pochhammer symbol: `(a; q)_(r+1) = (1 - a) (a q; q)_r`. -/
theorem claspAlg_qPochhammer_succ_left (a : RatFunc ℚ) (r : ℕ) :
    qPochhammer a (r + 1) = (1 - a) * qPochhammer (a * qParam) r := by
  unfold qPochhammer
  rw [Finset.prod_range_succ', pow_zero, mul_one, mul_comm (1 - a)]
  congr 1
  refine Finset.prod_congr rfl fun s _ ↦ ?_
  ring

/-- `1 - q q^s ≠ 0`, the last factor of `(q; q)_(s+1)`. -/
theorem claspAlg_one_sub_qParam_mul_pow_ne_zero (s : ℕ) : 1 - qParam * qParam ^ s ≠ 0 := by
  have h := one_sub_qParam_zpow_ne_zero (n := (s : ℤ) + 1) (by omega)
  rwa [zpow_add_one₀ qParam_ne_zero, zpow_natCast, mul_comm] at h

/-- The rational identity behind the three-term relation of the coefficients: `K = q^k`,
`R = q^r` with `m = k + 1 + r`, `E = q^(r(r-1)/2)`, `W = (C q^(k+1); q)_r`, and `s`, `Pk`, `Pr`,
`Pm` stand for the common factors. -/
private theorem claspAlg_vdmCoeff_interior_algebra (q K R C E W s Pk Pr Pm : RatFunc ℚ)
    (hPk : Pk ≠ 0) (hPr : Pr ≠ 0) (hK : 1 - q * K ≠ 0) (hR : 1 - q * R ≠ 0) :
    s * -1 * (E * R) * (Pm * (1 - q * (K * q * R)) / (Pk * (1 - q * K) * (Pr * (1 - q * R)))) *
        (W * (1 - C * (K * q) * R)) =
      s * -1 * E * (Pm / (Pk * (1 - q * K) * Pr)) * W * (R - C * (K * q * R) ^ 2) -
        s * (E * R) * (Pm / (Pk * (Pr * (1 - q * R)))) * ((1 - C * K) * W) * (R * q) := by
  have hK' : 1 - K * q ≠ 0 := by rwa [mul_comm]
  have hR' : 1 - R * q ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

/-- The coefficient of `(b; q)_0`. -/
private theorem claspAlgVdmCoeff_succ_zero (C : RatFunc ℚ) (m : ℕ) :
    claspAlgVdmCoeff C (m + 1) 0 =
      claspAlgVdmCoeff C m 0 * (qParam ^ m - C * qParam ^ (2 * m)) := by
  have h0 : qPochhammer qParam 0 = 1 := Finset.prod_range_zero _
  have hC : qPochhammer C (m + 1) = qPochhammer C m * (1 - C * qParam ^ m) :=
    Finset.prod_range_succ _ _
  simp only [claspAlgVdmCoeff, Nat.sub_zero, pow_zero, mul_one, one_mul, h0,
    div_self (qPochhammer_qParam_ne_zero _), Nat.triangle_succ, pow_add, hC]
  ring

/-- The coefficient of `(b; q)_(m+1)`. -/
private theorem claspAlgVdmCoeff_succ_self (C : RatFunc ℚ) (m : ℕ) :
    claspAlgVdmCoeff C (m + 1) (m + 1) = -claspAlgVdmCoeff C m m := by
  have h0 : ∀ a : RatFunc ℚ, qPochhammer a 0 = 1 := fun a ↦ Finset.prod_range_zero _
  simp only [claspAlgVdmCoeff, Nat.sub_self, Nat.zero_mul, Nat.zero_div, pow_zero, mul_one, h0,
    div_self (qPochhammer_qParam_ne_zero _), pow_succ]
  ring

/-- The three-term relation of the coefficients (the `q`-Pascal rule). -/
private theorem claspAlgVdmCoeff_succ_succ (C : RatFunc ℚ) (m k : ℕ) (hk : k < m) :
    claspAlgVdmCoeff C (m + 1) (k + 1) =
      claspAlgVdmCoeff C m (k + 1) * (qParam ^ (m - (k + 1)) - C * qParam ^ (2 * m)) -
        claspAlgVdmCoeff C m k * qParam ^ (m - k) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = k + 1 + r := ⟨m - (k + 1), by omega⟩
  have e1 : k + 1 + r + 1 - (k + 1) = r + 1 := by omega
  have e2 : k + 1 + r - (k + 1) = r := by omega
  have e3 : k + 1 + r - k = r + 1 := by omega
  have hPm : qPochhammer qParam (k + 1 + r + 1) =
      qPochhammer qParam (k + 1 + r) * (1 - qParam * qParam ^ (k + 1 + r)) :=
    Finset.prod_range_succ _ _
  have hPk : qPochhammer qParam (k + 1) = qPochhammer qParam k * (1 - qParam * qParam ^ k) :=
    Finset.prod_range_succ _ _
  have hPr : qPochhammer qParam (r + 1) = qPochhammer qParam r * (1 - qParam * qParam ^ r) :=
    Finset.prod_range_succ _ _
  have hW1 : qPochhammer (C * qParam ^ (k + 1)) (r + 1) =
      qPochhammer (C * qParam ^ (k + 1)) r * (1 - C * qParam ^ (k + 1) * qParam ^ r) :=
    Finset.prod_range_succ _ _
  have hW0 : qPochhammer (C * qParam ^ k) (r + 1) =
      (1 - C * qParam ^ k) * qPochhammer (C * qParam ^ (k + 1)) r := by
    rw [claspAlg_qPochhammer_succ_left, mul_assoc, ← pow_succ]
  have hE : (r + 1) * (r + 1 - 1) / 2 = r * (r - 1) / 2 + r := Nat.triangle_succ r
  have hqm : qParam ^ (k + 1 + r) = qParam ^ k * qParam * qParam ^ r := by
    rw [pow_add, pow_succ]
  have hq2m : qParam ^ (2 * (k + 1 + r)) = (qParam ^ k * qParam * qParam ^ r) ^ 2 := by
    rw [← hqm, ← pow_mul, mul_comm]
  unfold claspAlgVdmCoeff
  rw [e1, e2, e3, hPm, hPk, hPr, hW1, hW0, hE, hq2m, hqm, pow_add qParam (r * (r - 1) / 2) r,
    pow_succ (-1 : RatFunc ℚ) k, pow_succ qParam k, pow_succ qParam r]
  exact claspAlg_vdmCoeff_interior_algebra qParam (qParam ^ k) (qParam ^ r) C _ _ _ _ _ _
    (qPochhammer_qParam_ne_zero k) (qPochhammer_qParam_ne_zero r)
    (claspAlg_one_sub_qParam_mul_pow_ne_zero k) (claspAlg_one_sub_qParam_mul_pow_ne_zero r)

/-- Multiplication of `(b; q)_k` by `q^m (b - C q^m)` in the basis `(b; q)_k`. -/
private theorem claspAlg_qPochhammer_mul_linear (b C : RatFunc ℚ) (m k : ℕ) (hk : k ≤ m) :
    qPochhammer b k * (qParam ^ m * (b - C * qParam ^ m)) =
      (qParam ^ (m - k) - C * qParam ^ (2 * m)) * qPochhammer b k -
        qParam ^ (m - k) * qPochhammer b (k + 1) := by
  have hb : qPochhammer b (k + 1) = qPochhammer b k * (1 - b * qParam ^ k) :=
    Finset.prod_range_succ _ _
  have hq : qParam ^ m = qParam ^ (m - k) * qParam ^ k := by
    rw [← pow_add]
    congr 1
    omega
  have hq2 : qParam ^ (2 * m) = (qParam ^ (m - k) * qParam ^ k) ^ 2 := by
    rw [← hq]
    ring
  rw [hb, hq2, hq]
  ring

/-- The `q`-Chu–Vandermonde sum, for arbitrary `b` and `C`. -/
theorem claspAlg_qVandermonde (m : ℕ) (b C : RatFunc ℚ) :
    ∑ k ∈ Finset.range (m + 1),
        (-1) ^ k * qParam ^ ((m - k) * (m - k - 1) / 2) *
          (qPochhammer qParam m / (qPochhammer qParam k * qPochhammer qParam (m - k))) *
          qPochhammer (C * qParam ^ k) (m - k) * qPochhammer b k =
      ∏ s ∈ Finset.range m, qParam ^ s * (b - C * qParam ^ s) := by
  change ∑ k ∈ Finset.range (m + 1), claspAlgVdmCoeff C m k * qPochhammer b k = _
  induction m with
  | zero =>
    have h0 : ∀ a : RatFunc ℚ, qPochhammer a 0 = 1 := fun a ↦ Finset.prod_range_zero _
    simp [claspAlgVdmCoeff, h0]
  | succ m ih =>
    have hstep : ∀ k ∈ Finset.range (m + 1),
        claspAlgVdmCoeff C m k * qPochhammer b k * (qParam ^ m * (b - C * qParam ^ m)) =
          claspAlgVdmCoeff C m k * (qParam ^ (m - k) - C * qParam ^ (2 * m)) * qPochhammer b k -
            claspAlgVdmCoeff C m k * qParam ^ (m - k) * qPochhammer b (k + 1) := by
      intro k hk
      rw [mul_assoc, claspAlg_qPochhammer_mul_linear b C m k
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
      ring
    have hL : ∑ k ∈ Finset.range (m + 1 + 1), claspAlgVdmCoeff C (m + 1) k * qPochhammer b k =
        ∑ k ∈ Finset.range m, claspAlgVdmCoeff C (m + 1) (k + 1) * qPochhammer b (k + 1) +
          claspAlgVdmCoeff C (m + 1) (m + 1) * qPochhammer b (m + 1) +
          claspAlgVdmCoeff C (m + 1) 0 * qPochhammer b 0 := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
    have hA : ∑ k ∈ Finset.range (m + 1),
        claspAlgVdmCoeff C m k * (qParam ^ (m - k) - C * qParam ^ (2 * m)) * qPochhammer b k =
        ∑ k ∈ Finset.range m, claspAlgVdmCoeff C m (k + 1) *
            (qParam ^ (m - (k + 1)) - C * qParam ^ (2 * m)) * qPochhammer b (k + 1) +
          claspAlgVdmCoeff C m 0 * (qParam ^ (m - 0) - C * qParam ^ (2 * m)) * qPochhammer b 0 :=
      Finset.sum_range_succ' _ _
    have hB : ∑ k ∈ Finset.range (m + 1),
        claspAlgVdmCoeff C m k * qParam ^ (m - k) * qPochhammer b (k + 1) =
        ∑ k ∈ Finset.range m, claspAlgVdmCoeff C m k * qParam ^ (m - k) * qPochhammer b (k + 1) +
          claspAlgVdmCoeff C m m * qParam ^ (m - m) * qPochhammer b (m + 1) :=
      Finset.sum_range_succ _ _
    have hint : ∑ k ∈ Finset.range m, claspAlgVdmCoeff C (m + 1) (k + 1) * qPochhammer b (k + 1) =
        ∑ k ∈ Finset.range m, claspAlgVdmCoeff C m (k + 1) *
            (qParam ^ (m - (k + 1)) - C * qParam ^ (2 * m)) * qPochhammer b (k + 1) -
          ∑ k ∈ Finset.range m,
            claspAlgVdmCoeff C m k * qParam ^ (m - k) * qPochhammer b (k + 1) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [claspAlgVdmCoeff_succ_succ C m k (Finset.mem_range.mp hk)]
      ring
    rw [Finset.prod_range_succ, ← ih, Finset.sum_mul, Finset.sum_congr rfl hstep,
      Finset.sum_sub_distrib, hL, hA, hB, hint, claspAlgVdmCoeff_succ_zero,
      claspAlgVdmCoeff_succ_self, Nat.sub_zero, Nat.sub_self, pow_zero]
    ring

end AJConjecture
