import Mathlib
import AJConjecture.ClaspAlgCoeffMid
import AJFamily.Skein.TorusReducedFormulaSum
import AJFamily.Skein.TorusSequenceIdentity
import AJHandoff.Geometry.GeoKernelSeries
import AJHandoff.Geometry.GeoKernelSears

/-!
# The coefficient-extraction formula for the actual clasp kernel (G-KERNEL)

The library's clasp coefficient `claspAlgCoeff N n = [N] ∑_{j=n}^{N-1} C_j(N) K_{j,n}` (which equals
the skein-theoretic clasp eigenvalue, `claspAlgClaspEigen_eq_claspAlgCoeff`) is
`q^{N² - (N+1)/2} [z^{N-1}] F_n(z, z/x)` (`q^{1/2} = t²`, so the prefactor is `t^{4N² - 2N - 2}`).
Hence the coloured Jones function of `whiteheadTorusKnot k` (`a = 2k + 1`) has the
coefficient-extraction form

  `J(N) = q^{N² - (N+1)/2} [z^{N-1}] ∑_{n ≥ 0} F_n(z, z/x) u_n`, `x = q^N`,

where the sum is finite in each colour (every `n ≥ N` contributes `0`). This is the source's
starting kernel (stationary_bridge, CLASP_SYSTEM) certified against the library's skein
derivation. Checked exactly at `t = 2`, `t = 3/2` for `N ≤ 5`.

Route. `geo_coeff_claspGen`, then with `M = N - 1 - n`, `c = N - 1`:
`t^{4N²-2N-2} x^{-n} P_n ∑_i x^{-i} [n+i, n][N-1-i, n] = t^{4c²+6c} ∑_i (…) = t^{4c²+6c} Mid(n, M)`
(`geo_claspConv_eq_searsMid`) `= claspAlgCoeff N n` (`claspAlgCoeff_eq_searsMid`). The formula
follows from `claspAlg_quantumInt_mul_torusReducedFormula`, `torusWhiteheadFormula` and
`laurentToField_coloredJones_whiteheadTorusKnot`.
-/

noncomputable section

namespace AJConjecture

/-- The clasp coefficient is a coefficient of the generating function. -/
theorem geo_claspAlgCoeff_eq_coeff {N n : ℕ} (hn : n < N) :
    claspAlgCoeff N n =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (N : ℤ) ^ 2 - 2 * N - 2) *
        PowerSeries.coeff (N - 1) (geoClaspGen N n) := by
  obtain ⟨c, rfl⟩ : ∃ c, N = c + 1 := ⟨N - 1, by omega⟩
  obtain ⟨M, rfl⟩ : ∃ M, c = n + M := ⟨c - n, by omega⟩
  rw [geo_coeff_claspGen hn, claspAlgCoeff_eq_searsMid _ _ (by omega),
    show n + M - n = M by omega, ← geo_claspConv_eq_searsMid,
    show (4 * (((n + M + 1 : ℕ) : ℤ)) ^ 2 - 2 * ((n + M + 1 : ℕ) : ℤ) - 2) =
      4 * ((n + M : ℕ) : ℤ) ^ 2 + 6 * ((n + M : ℕ) : ℤ) by push_cast; ring,
    show n + M + 1 - n = M + 1 by omega]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hpow : qParam ^ (-(((n + M + 1) * (n + i) : ℕ) : ℤ)) =
      ((qParam ^ (n + M + 1))⁻¹) ^ n * ((qParam ^ (n + M + 1))⁻¹) ^ i := by
    rw [← pow_add, inv_pow, ← pow_mul, zpow_neg, zpow_natCast]
  rw [hpow, geoQBinom, geoQBinom, show n + i - n = i by omega,
    show n + M + 1 - 1 - i = n + M - i by omega, show n + M - i - n = M - i by omega]
  have := qPochhammer_qParam_ne_zero n
  have := qPochhammer_qParam_ne_zero i
  have := qPochhammer_qParam_ne_zero (M - i)
  field_simp

/-- The unreduced formula of `T(2, a)` in coefficient-extraction form, for every bound `B ≥ N` on
the companion colours. -/
theorem geo_torusWhiteheadFormula_eq_extract (a N B : ℕ) (hN : 1 ≤ N) (hB : N ≤ B) :
    torusWhiteheadFormula a N =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (N : ℤ) ^ 2 - 2 * N - 2) *
        PowerSeries.coeff (N - 1)
          (∑ n ∈ Finset.range B, PowerSeries.C (torusOddColor a n) * geoClaspGen N n) := by
  have hpos : (0 : ℤ) < (N : ℤ) := by omega
  simp only [torusWhiteheadFormula, hpos, ↓reduceIte, Int.toNat_natCast]
  rw [claspAlg_quantumInt_mul_torusReducedFormula, map_sum, Finset.mul_sum,
    ← Finset.sum_range_add_sum_Ico _ hB]
  have hzero : ∑ n ∈ Finset.Ico N B, (RatFunc.X : RatFunc ℚ) ^ (4 * (N : ℤ) ^ 2 - 2 * N - 2) *
      PowerSeries.coeff (N - 1) (PowerSeries.C (torusOddColor a n) * geoClaspGen N n) = 0 := by
    refine Finset.sum_eq_zero fun n hn ↦ ?_
    rw [PowerSeries.coeff_C_mul,
      geo_coeff_claspGen_eq_zero hN (Finset.mem_Ico.mp hn).1, mul_zero, mul_zero]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [PowerSeries.coeff_C_mul, geo_claspAlgCoeff_eq_coeff (Finset.mem_range.mp hn)]
  ring

/-- G-KERNEL, the kernel: the coloured Jones function of the actual knot `whiteheadTorusKnot k`
has the coefficient-extraction formula. -/
theorem geo_coloredJones_eq_extract (k : ℕ) (hk : 1 ≤ k) (N B : ℕ) (hN : 1 ≤ N) (hB : N ≤ B) :
    laurentToField (coloredJones (whiteheadTorusKnot k hk) N) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (N : ℤ) ^ 2 - 2 * N - 2) *
        PowerSeries.coeff (N - 1)
          (∑ n ∈ Finset.range B,
            PowerSeries.C (torusOddColor (2 * k + 1) n) * geoClaspGen N n) := by
  rw [laurentToField_coloredJones_whiteheadTorusKnot k hk N,
    geo_torusWhiteheadFormula_eq_extract (2 * k + 1) N B hN hB]

end AJConjecture
