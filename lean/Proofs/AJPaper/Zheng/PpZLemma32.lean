import Mathlib
import AJHandoff.Geometry.GeoPhysUncond
import AJPaper.Zheng.PpZNormGlobal

/-!
# Zheng's Lemma 3.2 (Unit PpZ, node `PpZ_Lemma32`)

Source: H. Zheng, arXiv:math/0508138v4, Lemma 3.2, (3.25): for `1/2 < δ < 1` there are `ε, C > 0`
with `S_{n,i} < C e^{-ε N^{2δ-1}} S_{[N/2],[N/4]}` whenever `|n - N/2| + |i - N/4| ≥ N^δ`.

Route. From `ppZ_normFactor_gaussian_bound` with constants `c, C₀`: if `d ≥ N^δ` then
`d²/N ≥ N^{2δ-1}` (`Real.rpow_natCast`, `Real.rpow_add`), so
`S ≤ C₀ e^{-c N^{2δ-1}} S₀ < (max C₀ 0 + 1) e^{-c N^{2δ-1}} S₀`, using `S₀ > 0`
(`geo_normFactor0_pos`). Take `ε = c`, `C = max C₀ 0 + 1`; the same `ε, C` serve every `δ`.
-/

noncomputable section

namespace AJConjecture

/-- **Zheng, Lemma 3.2**: the norm factor is exponentially small outside the window. -/
theorem zhengLemma32_holds : ZhengLemma32 := by
  obtain ⟨c, hc, C₀, hG⟩ := ppZ_normFactor_gaussian_bound
  unfold ZhengLemma32
  intro δ _ _
  refine ⟨c, hc, max C₀ 0 + 1, by positivity, fun N n i hN h hd ↦ ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hS0 := geo_normFactor0_pos N hN
  have hG' := hG N n i hN h
  have hpow0 : 0 ≤ (N : ℝ) ^ δ := Real.rpow_nonneg hNr.le δ
  have h1 : (N : ℝ) ^ (2 * δ - 1) ≤ (|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2 / N := by
    rw [Real.rpow_sub_one hNr.ne', div_le_div_iff_of_pos_right hNr]
    have e : (N : ℝ) ^ (2 * δ) = ((N : ℝ) ^ δ) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
      congr 1
      push_cast
      ring
    rw [e]
    exact pow_le_pow_left₀ hpow0 hd 2
  have hexp : Real.exp (-(c / N) * (|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2) ≤
      Real.exp (-c * (N : ℝ) ^ (2 * δ - 1)) := by
    apply Real.exp_le_exp.mpr
    have e : -(c / N) * (|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2 =
        -(c * ((|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2 / N)) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h1 hc.le
    linarith
  have hM : 0 ≤ max C₀ 0 := le_max_right _ _
  have hpos : 0 < Real.exp (-c * (N : ℝ) ^ (2 * δ - 1)) * geoNormFactor0 N :=
    mul_pos (Real.exp_pos _) hS0
  calc geoNormFactor N n i
      ≤ C₀ * Real.exp (-(c / N) * (|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2) *
          geoNormFactor0 N := hG'
    _ ≤ max C₀ 0 * Real.exp (-(c / N) * (|(n : ℝ) - N / 2| + |(i : ℝ) - N / 4|) ^ 2) *
          geoNormFactor0 N :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le) hS0.le
    _ ≤ max C₀ 0 * Real.exp (-c * (N : ℝ) ^ (2 * δ - 1)) * geoNormFactor0 N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hM) hS0.le
    _ < (max C₀ 0 + 1) * Real.exp (-c * (N : ℝ) ^ (2 * δ - 1)) * geoNormFactor0 N := by
        linarith

end AJConjecture
