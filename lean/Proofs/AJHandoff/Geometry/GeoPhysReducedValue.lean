import Mathlib
import AJHandoff.Geometry.GeoPhysReducedDeriv

/-!
# Zheng's clasp summand at `t_N = e^{πi/(2N)}` (G-PHYS)

At `t_N` (so `t_N² = s = e^{πi/N}`, `t_N⁴ = q_N`): the summand `c_{n,i}(t_N)` equals
`-s⁻¹ a_n^{-1} S_{n,i}` (`geo_claspSummand_quarterRoot`), from
`1 - e^{2iθ} = e^{i(θ - π/2)} · 2 sin θ`; and its scaled logarithmic derivative is
`N² - N/2 - 1/2 + b_{n,i}` (`geo_logDeriv_claspSummand_quarterRoot`).
-/

open Real

noncomputable section

namespace AJConjecture

/-- `t_N = e^{πi/(2N)}`. -/
def geoQuarterRoot (N : ℕ) : ℂ := Complex.exp (Real.pi * Complex.I / (2 * N))

/-- Integer powers of `t_N`. -/
theorem geoQuarterRoot_zpow (N : ℕ) (m : ℤ) :
    geoQuarterRoot N ^ m = Complex.exp (m * (Real.pi * Complex.I / (2 * N))) := by
  rw [geoQuarterRoot, Complex.exp_int_mul]

/-- Natural powers of `t_N`. -/
theorem geoQuarterRoot_pow (N m : ℕ) :
    geoQuarterRoot N ^ m = Complex.exp (m * (Real.pi * Complex.I / (2 * N))) := by
  rw [geoQuarterRoot, Complex.exp_nat_mul]

/-- `t_N ≠ 0`. -/
theorem geoQuarterRoot_ne_zero (N : ℕ) : geoQuarterRoot N ≠ 0 := Complex.exp_ne_zero _

/-- `t_N² = s`. -/
theorem geoQuarterRoot_sq {N : ℕ} (hN : 1 ≤ N) : geoQuarterRoot N ^ 2 = geoHalfRoot N := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [geoQuarterRoot_pow, geoHalfRoot]
  congr 1
  push_cast
  field_simp

/-- `t_N⁴ = q_N`. -/
theorem geoQuarterRoot_pow_four {N : ℕ} (hN : 1 ≤ N) : geoQuarterRoot N ^ 4 = geoRootQ N := by
  rw [geoRootQ, ← geoQuarterRoot_sq hN, ← pow_mul]

/-- `t_N^{4k} = e^{2iθ}`, `θ = kπ/N`. -/
theorem geoQuarterRoot_pow_four_mul {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    geoQuarterRoot N ^ (4 * k) = Complex.exp (2 * ((k * Real.pi / N : ℝ) : ℂ) * Complex.I) := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [geoQuarterRoot_pow]
  congr 1
  push_cast
  field_simp
  ring

/-- `q_N^k ≠ 1` for `1 ≤ k < N`. -/
theorem geoQuarterRoot_pow_four_pow_ne_one {N : ℕ} (hN : 1 ≤ N) {k : ℕ}
    (hk : k ∈ Finset.Icc 1 (N - 1)) : (geoQuarterRoot N ^ 4) ^ k ≠ 1 := by
  have hk' := Finset.mem_Icc.mp hk
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [← pow_mul, geoQuarterRoot_pow]
  intro hexp
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexp
  have h1 : ((k : ℤ) : ℂ) = ((m * N : ℤ) : ℂ) := by
    have h2 : ((4 * k : ℕ) : ℂ) * (Real.pi * Complex.I / (2 * N)) * N =
        m * (2 * Real.pi * Complex.I) * N := by rw [hm]
    push_cast at h2 ⊢
    field_simp at h2
    linear_combination h2 / 4
  have h5 : (k : ℤ) = m * N := by exact_mod_cast h1
  have hkN : (k : ℤ) ≤ N - 1 := by omega
  have hk1 : (1 : ℤ) ≤ k := by omega
  rcases lt_trichotomy m 0 with hm0 | hm0 | hm0
  · nlinarith
  · subst hm0
    omega
  · nlinarith

/-- `1 - e^{2iθ} = e^{i(θ - π/2)} · 2 sin θ`. -/
theorem geo_one_sub_exp_two_mul_I (θ : ℝ) :
    1 - Complex.exp (2 * (θ : ℂ) * Complex.I) =
      Complex.exp (((θ : ℂ) - Real.pi / 2) * Complex.I) * ((2 * Real.sin θ : ℝ) : ℂ) := by
  have hE : Complex.exp (θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have h2 : Complex.exp (2 * (θ : ℂ) * Complex.I) = Complex.exp (θ * Complex.I) ^ 2 := by
    rw [← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have h3 : Complex.exp (((θ : ℂ) - Real.pi / 2) * Complex.I) =
      Complex.exp (θ * Complex.I) * (-Complex.I) := by
    rw [sub_mul, Complex.exp_sub, Complex.exp_pi_div_two_mul_I]
    field_simp
    rw [Complex.I_sq]
    ring
  have h4 : Complex.exp (-(θ : ℂ) * Complex.I) = (Complex.exp (θ * Complex.I))⁻¹ := by
    rw [neg_mul, Complex.exp_neg]
  push_cast
  rw [Complex.sin, h2, h3, h4]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- One factor of Zheng's product at `t_N`. -/
theorem geo_claspFactor_quarterRoot {N i r : ℕ} (hN : 1 ≤ N) (h : i + r ≤ N) :
    (1 - geoQuarterRoot N ^ (4 * (i + r))) * (1 - geoQuarterRoot N ^ (4 * (N - i - r))) /
        (1 - geoQuarterRoot N ^ (4 * r)) =
      ((4 * Real.sin (((i : ℝ) + r) * Real.pi / N) ^ 2 /
          (2 * Real.sin ((r : ℝ) * Real.pi / N)) : ℝ) : ℂ) *
        Complex.exp (-((((r : ℝ) * Real.pi / N : ℝ) : ℂ) - Real.pi / 2) * Complex.I) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  set θa : ℝ := ((i + r : ℕ) : ℝ) * Real.pi / N with hθa
  set θb : ℝ := ((N - i - r : ℕ) : ℝ) * Real.pi / N with hθb
  have hsum : θa + θb = Real.pi := by
    rw [hθa, hθb, Nat.cast_sub (by omega : r ≤ N - i), Nat.cast_sub (by omega : i ≤ N)]
    push_cast
    field_simp
    ring
  have hsin : Real.sin θb = Real.sin θa := by
    rw [show θb = Real.pi - θa by linarith, Real.sin_pi_sub]
  have hab : Complex.exp (((θa : ℂ) - Real.pi / 2) * Complex.I) *
      Complex.exp (((θb : ℂ) - Real.pi / 2) * Complex.I) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    have : (θa : ℂ) + θb = Real.pi := by exact_mod_cast hsum
    linear_combination Complex.I * this
  rw [geoQuarterRoot_pow_four_mul hN, geoQuarterRoot_pow_four_mul hN,
    geoQuarterRoot_pow_four_mul hN, geo_one_sub_exp_two_mul_I, geo_one_sub_exp_two_mul_I,
    geo_one_sub_exp_two_mul_I, ← hθa, ← hθb, hsin, neg_mul, Complex.exp_neg]
  have hθa' : θa = ((i : ℝ) + r) * Real.pi / N := by rw [hθa]; push_cast; ring
  rw [← hθa']
  set θr : ℝ := (r : ℝ) * Real.pi / N with hθr
  set Ea := Complex.exp (((θa : ℂ) - Real.pi / 2) * Complex.I)
  set Eb := Complex.exp (((θb : ℂ) - Real.pi / 2) * Complex.I)
  set Er := Complex.exp (((θr : ℂ) - Real.pi / 2) * Complex.I)
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv]
  linear_combination (4 * (Real.sin θa : ℂ) ^ 2 *
    Er⁻¹ *
    (2 * (Real.sin θr : ℂ))⁻¹) * hab

/-- Zheng's product at `t_N` is `a_n^{-1} S_{n,i}`. -/
theorem geo_claspProd_quarterRoot {N : ℕ} (hN : 1 ≤ N) (i : ℕ) :
    ∀ n : ℕ, n + i < N →
      ∏ r ∈ Finset.Icc 1 n,
          ((1 - geoQuarterRoot N ^ (4 * (i + r))) * (1 - geoQuarterRoot N ^ (4 * (N - i - r))) /
            (1 - geoQuarterRoot N ^ (4 * r))) =
        geoPhasePow N n (-1) * geoNormFactor N n i := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [geoPhasePow, geoPhaseArg, geoNormFactor]
  | succ n ih =>
    intro h
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hS : geoNormFactor N (n + 1) i = geoNormFactor N n i *
        (4 * Real.sin (((i : ℝ) + ((n + 1 : ℕ) : ℝ)) * Real.pi / N) ^ 2 /
          (2 * Real.sin (((n + 1 : ℕ) : ℝ) * Real.pi / N))) := by
      simp only [geoNormFactor]
      rw [Finset.prod_Icc_succ_top (by omega)]
    have hP : geoPhasePow N (n + 1) (-1) = geoPhasePow N n (-1) *
        Complex.exp (-(((((n + 1 : ℕ) : ℝ) * Real.pi / N : ℝ) : ℂ) - Real.pi / 2) *
          Complex.I) := by
      have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      simp only [geoPhasePow, geoPhaseArg]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    rw [Finset.prod_Icc_succ_top (by omega), ih (by omega),
      geo_claspFactor_quarterRoot hN (by omega), hS, hP]
    push_cast
    ring

/-- The prefactor `t_N^{4N² - 2N - 2 - 4N(n+i)} = -s⁻¹`. -/
theorem geoQuarterRoot_zpow_prefactor {N : ℕ} (hN : 1 ≤ N) (n i : ℕ) :
    geoQuarterRoot N ^ (4 * (N : ℤ) ^ 2 - 2 * N - 2 - 4 * N * (n + i)) = -(geoHalfRoot N)⁻¹ := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have harg : (((4 * (N : ℤ) ^ 2 - 2 * N - 2 - 4 * N * (n + i) : ℤ)) : ℂ) *
      (Real.pi * Complex.I / (2 * N)) =
        (((N : ℤ) - n - i : ℤ) : ℂ) * (2 * Real.pi * Complex.I) + -(Real.pi * Complex.I) +
          -(Real.pi * Complex.I / N) := by
    push_cast
    field_simp
    ring
  rw [geoQuarterRoot_zpow, harg, Complex.exp_add, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, Complex.exp_neg, Complex.exp_neg, Complex.exp_pi_mul_I,
    geoHalfRoot]
  ring

/-- Zheng's clasp summand at `t_N` is `-s⁻¹ a_n^{-1} S_{n,i}`. -/
theorem geo_claspSummand_quarterRoot {N n i : ℕ} (hN : 1 ≤ N) (h : n + i < N) :
    geoClaspSummand N n i (geoQuarterRoot N) =
      -(geoHalfRoot N)⁻¹ * geoPhasePow N n (-1) * geoNormFactor N n i := by
  rw [geoClaspSummand, geoQuarterRoot_zpow_prefactor hN, geo_claspProd_quarterRoot hN i n h]
  ring

/-- The scaled logarithmic derivative of the summand at `t_N` is `N² - N/2 - 1/2 + b_{n,i}`. -/
theorem geo_logDeriv_claspSummand_quarterRoot {N n i : ℕ} (hN : 1 ≤ N) (h : n + i < N) :
    (((4 * (N : ℤ) ^ 2 - 2 * N - 2 - 4 * N * (n + i) : ℤ)) : ℂ) / 4 +
        ∑ r ∈ Finset.Icc 1 n,
          (geoBeta (geoQuarterRoot N ^ 4) (i + r) + geoBeta (geoQuarterRoot N ^ 4) (N - i - r) -
            geoBeta (geoQuarterRoot N ^ 4) r) =
      ((N : ℂ) ^ 2 - N / 2 - 1 / 2) + geoZhengB N n i := by
  rw [geoQuarterRoot_pow_four hN, geoZhengB]
  have hsum : ∑ r ∈ Finset.Icc 1 n,
      (geoBeta (geoRootQ N) (i + r) + geoBeta (geoRootQ N) (N - i - r) -
        geoBeta (geoRootQ N) r) =
      ∑ j ∈ Finset.Icc 1 n,
        (((N : ℂ) - i - j) / (1 - geoRootQ N ^ (-(N : ℤ) + i + j)) +
          ((i : ℂ) + j) / (1 - geoRootQ N ^ (-((i : ℤ) + j))) -
          (j : ℂ) / (1 - geoRootQ N ^ (-(j : ℤ)))) := by
    refine Finset.sum_congr rfl fun r hr ↦ ?_
    have hr' := Finset.mem_Icc.mp hr
    have hexp : -(((N - i - r : ℕ) : ℤ)) = -(N : ℤ) + i + r := by omega
    simp only [geoBeta]
    rw [hexp, Nat.cast_sub (by omega : r ≤ N - i), Nat.cast_sub (by omega : i ≤ N)]
    push_cast
    ring
  rw [hsum]
  push_cast
  ring

end AJConjecture
