import Mathlib
import AJConjecture.WhiteheadFormula
import AJConjecture.ClaspAlgQVandermonde
import AJConjecture.ClaspAlgBasic

/-!
# The coefficient-extraction generating function of the clasp (G-KERNEL)

Zheng's clasp coefficient is a coefficient of the generating function
`F_n(z, z/x) = (z/x)ⁿ (q;q)_n / ((z;q)_{n+1} (z/x;q)_{n+1})`, `x = q^N`, expanded at `z = 0`
(`geoClaspGen`; `1/(1 - cz)` is the geometric series `geoGeomSeries c`). Its coefficient of
`z^{N-1}` is the finite convolution
`x^{-n} (q;q)_n ∑_{i+j = N-1-n} x^{-i} [n+i choose n]_q [n+j choose n]_q`, it vanishes for
`n ≥ N`, and each convolution term is Zheng's product
`∏_{r=1}^{n} (1 - q^{i+r})(1 - q^{N-i-r})/(1 - q^r)` (Zheng (2.7)).

Route. `[z^i] ∏_{s=0}^{n} 1/(1 - c q^s z) = cⁱ [n+i choose n]_q` (q-binomial theorem; induction on
`n` with `(1 - c q^{n+1} z)`, or the library's q-Pascal machinery); multiply the two series
(`PowerSeries.coeff_mul`) and shift by `zⁿ`. The product form is
`(q;q)_{n+i}/(q;q)_i = ∏_{r=1}^{n}(1 - q^{i+r})` and the reversal `r ↦ n + 1 - r`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The geometric series `1/(1 - c z) = ∑ cᵏ zᵏ`. -/
def geoGeomSeries (c : RatFunc ℚ) : PowerSeries (RatFunc ℚ) :=
  PowerSeries.mk fun k ↦ c ^ k

/-- `geoGeomSeries c` is the inverse of `1 - c z`. -/
theorem geoGeomSeries_mul (c : RatFunc ℚ) :
    geoGeomSeries c * (1 - PowerSeries.C c * PowerSeries.X) = 1 := by
  ext m
  rcases m with _ | m
  · simp [geoGeomSeries, mul_sub]
  · simp [geoGeomSeries, mul_sub, ← mul_assoc, PowerSeries.coeff_succ_mul_X, pow_succ]

/-- The generating function `F_n(z, z/x) = (z/x)ⁿ (q;q)_n / ((z;q)_{n+1} (z/x;q)_{n+1})`,
`x = q^N`, as a power series in `z`. -/
def geoClaspGen (N n : ℕ) : PowerSeries (RatFunc ℚ) :=
  PowerSeries.C (((qParam ^ N)⁻¹) ^ n * qPochhammer qParam n) * PowerSeries.X ^ n *
    ∏ s ∈ Finset.range (n + 1),
      (geoGeomSeries (qParam ^ s) * geoGeomSeries (qParam ^ s / qParam ^ N))

/-- The Gaussian binomial `[a choose b]_q = (q;q)_a / ((q;q)_b (q;q)_{a-b})`. -/
def geoQBinom (a b : ℕ) : RatFunc ℚ :=
  qPochhammer qParam a / (qPochhammer qParam b * qPochhammer qParam (a - b))

/-- The `q`-Pascal rule `[n+m+2, m+1] = [n+m+1, m+1] + q^{n+1} [n+m+1, m]`, written with
`P_k = (q; q)_k`. -/
private theorem geo_qBinom_pascal_series (n m : ℕ) :
    qPochhammer qParam (n + 1 + (m + 1)) /
        (qPochhammer qParam (n + 1) * qPochhammer qParam (m + 1)) =
      qPochhammer qParam (n + (m + 1)) / (qPochhammer qParam n * qPochhammer qParam (m + 1)) +
        qParam ^ (n + 1) * (qPochhammer qParam (n + 1 + m) /
          (qPochhammer qParam (n + 1) * qPochhammer qParam m)) := by
  have hm : qPochhammer qParam (n + 1 + (m + 1)) =
      qPochhammer qParam (n + 1 + m) * (1 - qParam * qParam ^ (n + 1 + m)) :=
    Finset.prod_range_succ _ _
  have hm' : qPochhammer qParam (n + (m + 1)) = qPochhammer qParam (n + 1 + m) := by
    rw [show n + (m + 1) = n + 1 + m by ring]
  have hn : qPochhammer qParam (n + 1) = qPochhammer qParam n * (1 - qParam * qParam ^ n) :=
    Finset.prod_range_succ _ _
  have hr : qPochhammer qParam (m + 1) = qPochhammer qParam m * (1 - qParam * qParam ^ m) :=
    Finset.prod_range_succ _ _
  have h1 := qPochhammer_qParam_ne_zero n
  have h2 := qPochhammer_qParam_ne_zero m
  have h3 := claspAlg_one_sub_qParam_mul_pow_ne_zero n
  have h4 := claspAlg_one_sub_qParam_mul_pow_ne_zero m
  rw [hm, hm', hn, hr]
  field_simp
  ring

/-- The `q`-binomial theorem for the product of geometric series:
`∏_{s=0}^{n} 1/(1 - c q^s z) = ∑_m c^m [n+m, n]_q z^m`. -/
private theorem geo_prod_geomSeries (c : RatFunc ℚ) (n : ℕ) :
    ∏ s ∈ Finset.range (n + 1), geoGeomSeries (c * qParam ^ s) =
      PowerSeries.mk fun m ↦
        c ^ m * (qPochhammer qParam (n + m) / (qPochhammer qParam n * qPochhammer qParam m)) := by
  induction n with
  | zero =>
    ext m
    have h0 : qPochhammer qParam 0 = 1 := Finset.prod_range_zero _
    simp [geoGeomSeries, h0, div_self (qPochhammer_qParam_ne_zero m)]
  | succ n ih =>
    have hrec : (PowerSeries.mk fun m ↦ c ^ m * (qPochhammer qParam (n + 1 + m) /
          (qPochhammer qParam (n + 1) * qPochhammer qParam m))) *
          (1 - PowerSeries.C (c * qParam ^ (n + 1)) * PowerSeries.X) =
        PowerSeries.mk fun m ↦
          c ^ m * (qPochhammer qParam (n + m) / (qPochhammer qParam n * qPochhammer qParam m)) := by
      ext m
      rcases m with _ | m
      · have h0 : qPochhammer qParam 0 = 1 := Finset.prod_range_zero _
        simp [mul_sub, h0, div_self (qPochhammer_qParam_ne_zero _)]
      · simp only [mul_sub, mul_one, map_sub, PowerSeries.coeff_mk, ← mul_assoc,
          PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
        rw [geo_qBinom_pascal_series n m]
        ring
    rw [Finset.prod_range_succ, ih, ← hrec, mul_assoc, mul_comm _ (geoGeomSeries _),
      geoGeomSeries_mul, mul_one]

/-- The coefficient of `z^{N-1}`: the finite convolution. -/
theorem geo_coeff_claspGen {N n : ℕ} (hn : n < N) :
    PowerSeries.coeff (N - 1) (geoClaspGen N n) =
      ((qParam ^ N)⁻¹) ^ n * qPochhammer qParam n *
        ∑ i ∈ Finset.range (N - n),
          ((qParam ^ N)⁻¹) ^ i * geoQBinom (n + i) n * geoQBinom (N - 1 - i) n := by
  have hprod : ∏ s ∈ Finset.range (n + 1),
      (geoGeomSeries (qParam ^ s) * geoGeomSeries (qParam ^ s / qParam ^ N)) =
        (∏ s ∈ Finset.range (n + 1), geoGeomSeries ((qParam ^ N)⁻¹ * qParam ^ s)) *
          ∏ s ∈ Finset.range (n + 1), geoGeomSeries (1 * qParam ^ s) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ ↦ ?_
    rw [one_mul, div_eq_inv_mul, mul_comm]
  obtain ⟨M, hM⟩ : ∃ M, N - 1 = M + n := ⟨N - 1 - n, by omega⟩
  rw [geoClaspGen, hprod, geo_prod_geomSeries, geo_prod_geomSeries, mul_assoc, hM,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, show N - n = M + 1 by omega]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [PowerSeries.coeff_mk, one_pow, one_mul, geoQBinom]
  rw [show n + i - n = i by omega, show M + n - i = n + (M - i) by omega,
    show n + (M - i) - n = M - i by omega]

/-- Coefficient extraction makes the sum over `n` finite: the coefficient vanishes for `n ≥ N`. -/
theorem geo_coeff_claspGen_eq_zero {N n : ℕ} (hN : 1 ≤ N) (hn : N ≤ n) :
    PowerSeries.coeff (N - 1) (geoClaspGen N n) = 0 := by
  rw [geoClaspGen, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · omega
  · rw [mul_zero]

/-- Each convolution term is Zheng's product
`∏_{r=1}^{n} (1 - q^{i+r})(1 - q^{N-i-r})/(1 - q^r)`. -/
theorem geo_qBinom_mul_eq_zhengProduct {N n i : ℕ} (h : n + i < N) :
    qPochhammer qParam n * geoQBinom (n + i) n * geoQBinom (N - 1 - i) n =
      ∏ r ∈ Finset.Icc 1 n,
        (1 - qParam ^ (i + r)) * (1 - qParam ^ (N - i - r)) / (1 - qParam ^ r) := by
  obtain ⟨K, rfl⟩ : ∃ K, N = n + i + K + 1 := ⟨N - (n + i + 1), by omega⟩
  have hA : ∏ k ∈ Finset.range n, (1 - qParam ^ (i + (1 + k))) =
      qPochhammer qParam (i + n) / qPochhammer qParam i := by
    rw [← claspAlg_qPochhammer_mul_shift i n, mul_div_cancel_left₀ _
      (qPochhammer_qParam_ne_zero i), qPochhammer]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [← pow_add]
    congr 2
    ring
  have hB : ∏ k ∈ Finset.range n, (1 - qParam ^ (n + i + K + 1 - i - (1 + k))) =
      qPochhammer qParam (K + n) / qPochhammer qParam K := by
    rw [← claspAlg_qPochhammer_mul_shift K n, mul_div_cancel_left₀ _
      (qPochhammer_qParam_ne_zero K), qPochhammer, ← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun k hk ↦ ?_
    have hk' := Finset.mem_range.mp hk
    rw [← pow_add]
    congr 2
    omega
  have hC : ∏ k ∈ Finset.range n, (1 - qParam ^ (1 + k)) = qPochhammer qParam n := by
    rw [qPochhammer]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [pow_add, pow_one]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, show n + 1 - 1 = n by omega,
    Finset.prod_div_distrib, Finset.prod_mul_distrib, hA, hB, hC, geoQBinom, geoQBinom,
    show n + i - n = i by omega, show n + i + K + 1 - 1 - i = K + n by omega,
    show K + n - n = K by omega, add_comm i n]
  have := qPochhammer_qParam_ne_zero n
  have := qPochhammer_qParam_ne_zero i
  have := qPochhammer_qParam_ne_zero K
  field_simp

end AJConjecture
