import Mathlib
import AJConjecture.ClaspAlgQVandermonde
import AJConjecture.QAlgQParamBasic

/-!
# The `q`-Chu–Vandermonde sum, dual form

For arbitrary `x`, `y` in `ℚ(t)` and `q = t⁴`:
`∑_{i=0}^{m} (-1)^i q^(i(i-1)/2) [m choose i]_q (y q^i; q)_(m-i) y^i (x; q)_i x^(m-i) = ∏_{s<m} (x - y q^s)`,
with the Gaussian binomial coefficient written as `(q;q)_m / ((q;q)_i (q;q)_(m-i))`. After division
by `x^m (y; q)_m` this is `₂φ₁(q^(-m), x; y; q, y q^m / x) = (y/x; q)_m / (y; q)_m`.

Proof: induction on `m`. With `g_(m,i) = (x; q)_i x^(m-i)`,
`(x - y q^m) g_(m,i) = (1 - y q^(m+i)) g_(m+1,i) - y q^m g_(m+1,i+1)`, and the coefficients satisfy
the corresponding three-term relation (the `q`-Pascal rule).
-/

namespace AJConjecture

/-- The coefficient of `(x; q)_i x^(m-i)` in the dual `q`-Chu–Vandermonde sum of length `m + 1`. -/
private noncomputable def claspAlgVdmDualCoeff (y : RatFunc ℚ) (m i : ℕ) : RatFunc ℚ :=
  (-1) ^ i * qParam ^ (i * (i - 1) / 2) *
    (qPochhammer qParam m / (qPochhammer qParam i * qPochhammer qParam (m - i))) *
    qPochhammer (y * qParam ^ i) (m - i) * y ^ i

/-- The rational identity behind the three-term relation of the coefficients: `K = q^i`,
`R = q^r` with `m = i + 1 + r`, `E = q^(i(i-1)/2)`, `Y = y^i`, `W = (y q^(i+1); q)_r`, and `s`,
`Pi`, `Pr`, `Pm` stand for the common factors. -/
private theorem claspAlg_vdmDualCoeff_interior_algebra (q K R y E Y W s Pi Pr Pm : RatFunc ℚ)
    (hPi : Pi ≠ 0) (hPr : Pr ≠ 0) (hK : 1 - q * K ≠ 0) (hR : 1 - q * R ≠ 0) :
    s * -1 * (E * K) * (Pm * (1 - q * (K * q * R)) / (Pi * (1 - q * K) * (Pr * (1 - q * R)))) *
        (W * (1 - y * (K * q) * R)) * (Y * y) =
      s * -1 * (E * K) * (Pm / (Pi * (1 - q * K) * Pr)) * W * (Y * y) *
          (1 - y * (K * q * R) * (K * q)) -
        s * E * (Pm / (Pi * (Pr * (1 - q * R)))) * ((1 - y * K) * W) * Y * (y * (K * q * R)) := by
  have hK' : 1 - K * q ≠ 0 := by rwa [mul_comm]
  have hR' : 1 - R * q ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

/-- The coefficient of `x^(m+1)`. -/
private theorem claspAlgVdmDualCoeff_succ_zero (y : RatFunc ℚ) (m : ℕ) :
    claspAlgVdmDualCoeff y (m + 1) 0 =
      claspAlgVdmDualCoeff y m 0 * (1 - y * qParam ^ m * qParam ^ 0) := by
  have h0 : qPochhammer qParam 0 = 1 := Finset.prod_range_zero _
  have hy : qPochhammer y (m + 1) = qPochhammer y m * (1 - y * qParam ^ m) :=
    Finset.prod_range_succ _ _
  simp only [claspAlgVdmDualCoeff, Nat.sub_zero, pow_zero, mul_one, one_mul, h0,
    div_self (qPochhammer_qParam_ne_zero _), Nat.zero_mul, Nat.zero_div, hy]

/-- The coefficient of `(x; q)_(m+1)`. -/
private theorem claspAlgVdmDualCoeff_succ_self (y : RatFunc ℚ) (m : ℕ) :
    claspAlgVdmDualCoeff y (m + 1) (m + 1) =
      -(claspAlgVdmDualCoeff y m m * (y * qParam ^ m)) := by
  have h0 : ∀ a : RatFunc ℚ, qPochhammer a 0 = 1 := fun a ↦ Finset.prod_range_zero _
  simp only [claspAlgVdmDualCoeff, Nat.sub_self, mul_one, h0,
    div_self (qPochhammer_qParam_ne_zero _), pow_succ, Nat.triangle_succ, pow_add]
  ring

/-- The three-term relation of the coefficients (the `q`-Pascal rule). -/
private theorem claspAlgVdmDualCoeff_succ_succ (y : RatFunc ℚ) (m i : ℕ) (hi : i < m) :
    claspAlgVdmDualCoeff y (m + 1) (i + 1) =
      claspAlgVdmDualCoeff y m (i + 1) * (1 - y * qParam ^ m * qParam ^ (i + 1)) -
        claspAlgVdmDualCoeff y m i * (y * qParam ^ m) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = i + 1 + r := ⟨m - (i + 1), by omega⟩
  have e1 : i + 1 + r + 1 - (i + 1) = r + 1 := by omega
  have e2 : i + 1 + r - (i + 1) = r := by omega
  have e3 : i + 1 + r - i = r + 1 := by omega
  have hPm : qPochhammer qParam (i + 1 + r + 1) =
      qPochhammer qParam (i + 1 + r) * (1 - qParam * qParam ^ (i + 1 + r)) :=
    Finset.prod_range_succ _ _
  have hPi : qPochhammer qParam (i + 1) = qPochhammer qParam i * (1 - qParam * qParam ^ i) :=
    Finset.prod_range_succ _ _
  have hPr : qPochhammer qParam (r + 1) = qPochhammer qParam r * (1 - qParam * qParam ^ r) :=
    Finset.prod_range_succ _ _
  have hW1 : qPochhammer (y * qParam ^ (i + 1)) (r + 1) =
      qPochhammer (y * qParam ^ (i + 1)) r * (1 - y * qParam ^ (i + 1) * qParam ^ r) :=
    Finset.prod_range_succ _ _
  have hW0 : qPochhammer (y * qParam ^ i) (r + 1) =
      (1 - y * qParam ^ i) * qPochhammer (y * qParam ^ (i + 1)) r := by
    rw [claspAlg_qPochhammer_succ_left, mul_assoc, ← pow_succ]
  have hE : (i + 1) * (i + 1 - 1) / 2 = i * (i - 1) / 2 + i := Nat.triangle_succ i
  have hqm : qParam ^ (i + 1 + r) = qParam ^ i * qParam * qParam ^ r := by
    rw [pow_add, pow_succ]
  unfold claspAlgVdmDualCoeff
  rw [e1, e2, e3, hPm, hPi, hPr, hW1, hW0, hE, hqm, pow_add qParam (i * (i - 1) / 2) i,
    pow_succ (-1 : RatFunc ℚ) i, pow_succ qParam i, pow_succ y i]
  exact claspAlg_vdmDualCoeff_interior_algebra qParam (qParam ^ i) (qParam ^ r) y _ _ _ _ _ _ _
    (qPochhammer_qParam_ne_zero i) (qPochhammer_qParam_ne_zero r)
    (claspAlg_one_sub_qParam_mul_pow_ne_zero i)
    (claspAlg_one_sub_qParam_mul_pow_ne_zero r)

/-- Multiplication of `(x; q)_i x^(m-i)` by `x - y q^m`. -/
private theorem claspAlg_qPochhammer_mul_pow_mul_linear (x y : RatFunc ℚ) (m i : ℕ) (hi : i ≤ m) :
    qPochhammer x i * x ^ (m - i) * (x - y * qParam ^ m) =
      (1 - y * qParam ^ m * qParam ^ i) * (qPochhammer x i * x ^ (m + 1 - i)) -
        y * qParam ^ m * (qPochhammer x (i + 1) * x ^ (m + 1 - (i + 1))) := by
  have hx : qPochhammer x (i + 1) = qPochhammer x i * (1 - x * qParam ^ i) :=
    Finset.prod_range_succ _ _
  have e1 : m + 1 - i = m - i + 1 := by omega
  have e2 : m + 1 - (i + 1) = m - i := by omega
  rw [hx, e1, e2, pow_succ]
  ring

/-- The `q`-Chu–Vandermonde sum in its dual form, for arbitrary `x` and `y`. -/
theorem claspAlg_qVandermonde_dual (m : ℕ) (x y : RatFunc ℚ) :
    ∑ i ∈ Finset.range (m + 1),
        (-1) ^ i * qParam ^ (i * (i - 1) / 2) *
          (qPochhammer qParam m / (qPochhammer qParam i * qPochhammer qParam (m - i))) *
          qPochhammer (y * qParam ^ i) (m - i) * y ^ i * (qPochhammer x i * x ^ (m - i)) =
      ∏ s ∈ Finset.range m, (x - y * qParam ^ s) := by
  change ∑ i ∈ Finset.range (m + 1),
    claspAlgVdmDualCoeff y m i * (qPochhammer x i * x ^ (m - i)) = _
  induction m with
  | zero =>
    have h0 : ∀ a : RatFunc ℚ, qPochhammer a 0 = 1 := fun a ↦ Finset.prod_range_zero _
    simp [claspAlgVdmDualCoeff, h0]
  | succ m ih =>
    have hstep : ∀ i ∈ Finset.range (m + 1),
        claspAlgVdmDualCoeff y m i * (qPochhammer x i * x ^ (m - i)) * (x - y * qParam ^ m) =
          claspAlgVdmDualCoeff y m i * (1 - y * qParam ^ m * qParam ^ i) *
              (qPochhammer x i * x ^ (m + 1 - i)) -
            claspAlgVdmDualCoeff y m i * (y * qParam ^ m) *
              (qPochhammer x (i + 1) * x ^ (m + 1 - (i + 1))) := by
      intro i hi
      rw [mul_assoc, claspAlg_qPochhammer_mul_pow_mul_linear x y m i
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
      ring
    have hL : ∑ i ∈ Finset.range (m + 1 + 1),
        claspAlgVdmDualCoeff y (m + 1) i * (qPochhammer x i * x ^ (m + 1 - i)) =
        ∑ i ∈ Finset.range m, claspAlgVdmDualCoeff y (m + 1) (i + 1) *
            (qPochhammer x (i + 1) * x ^ (m + 1 - (i + 1))) +
          claspAlgVdmDualCoeff y (m + 1) (m + 1) *
            (qPochhammer x (m + 1) * x ^ (m + 1 - (m + 1))) +
          claspAlgVdmDualCoeff y (m + 1) 0 * (qPochhammer x 0 * x ^ (m + 1 - 0)) := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
    have hA : ∑ i ∈ Finset.range (m + 1),
        claspAlgVdmDualCoeff y m i * (1 - y * qParam ^ m * qParam ^ i) *
          (qPochhammer x i * x ^ (m + 1 - i)) =
        ∑ i ∈ Finset.range m, claspAlgVdmDualCoeff y m (i + 1) *
            (1 - y * qParam ^ m * qParam ^ (i + 1)) *
            (qPochhammer x (i + 1) * x ^ (m + 1 - (i + 1))) +
          claspAlgVdmDualCoeff y m 0 * (1 - y * qParam ^ m * qParam ^ 0) *
            (qPochhammer x 0 * x ^ (m + 1 - 0)) :=
      Finset.sum_range_succ' _ _
    have hB : ∑ i ∈ Finset.range (m + 1),
        claspAlgVdmDualCoeff y m i * (y * qParam ^ m) *
          (qPochhammer x (i + 1) * x ^ (m + 1 - (i + 1))) =
        ∑ i ∈ Finset.range m, claspAlgVdmDualCoeff y m i * (y * qParam ^ m) *
            (qPochhammer x (i + 1) * x ^ (m + 1 - (i + 1))) +
          claspAlgVdmDualCoeff y m m * (y * qParam ^ m) *
            (qPochhammer x (m + 1) * x ^ (m + 1 - (m + 1))) :=
      Finset.sum_range_succ _ _
    have hint : ∑ i ∈ Finset.range m, claspAlgVdmDualCoeff y (m + 1) (i + 1) *
          (qPochhammer x (i + 1) * x ^ (m + 1 - (i + 1))) =
        ∑ i ∈ Finset.range m, claspAlgVdmDualCoeff y m (i + 1) *
            (1 - y * qParam ^ m * qParam ^ (i + 1)) *
            (qPochhammer x (i + 1) * x ^ (m + 1 - (i + 1))) -
          ∑ i ∈ Finset.range m, claspAlgVdmDualCoeff y m i * (y * qParam ^ m) *
            (qPochhammer x (i + 1) * x ^ (m + 1 - (i + 1))) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [claspAlgVdmDualCoeff_succ_succ y m i (Finset.mem_range.mp hi)]
      ring
    rw [Finset.prod_range_succ, ← ih, Finset.sum_mul, Finset.sum_congr rfl hstep,
      Finset.sum_sub_distrib, hL, hA, hB, hint, claspAlgVdmDualCoeff_succ_zero,
      claspAlgVdmDualCoeff_succ_self]
    ring

end AJConjecture
