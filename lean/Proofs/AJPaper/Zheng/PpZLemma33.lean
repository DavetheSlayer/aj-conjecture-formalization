import Mathlib
import AJHandoff.Geometry.GeoPhysGaussian
import AJHandoff.Geometry.GeoPhysUncond
import AJPaper.Zheng.PpZWindowCompare
import AJPaper.Zheng.PpZFinite

/-!
# Zheng's Lemma 3.3 (`α = 0`) with the constant (3.34) (Unit PpZ, node `PpZ_Lemma33`)

Source: H. Zheng, arXiv:math/0508138v4, Lemma 3.3, (3.29), (3.34): for `1/2 < δ < 2/3`

  `∑_{|n-N/2| + |i-N/4| < N^δ} a_n^β S_{n,i} = C_β N e^{-βNπi/8} S₀ (1 + O(N^{3δ-2}))`,
  `C_β = e^{βπi/4} ∫_{ℝ²} e^{-π(x² + 2xy + 2y²) + βπi x²/2} dx dy`.

Route. `geoGaussConst β = e^{βπi/4} (1 - iβ)^{-1/2}` (`geo_gaussConst_eq`), hence
`C_β N e^{-βNπi/8} S₀ = e^{iβπ(1/4 - N/8)} S₀ · N (1 - iβ)^{-1/2}`. For `N ≥ max N₁ 65`:
`‖W - main‖ ≤ ‖W - e^{iβπ(1/4-N/8)} S₀ M‖ + S₀ ‖M - N(1 - iβ)^{-1/2}‖` with
`M = ppZModelWindowSum N δ β` (`ppZ_windowSum_compare`, `ppZ_modelWindowSum`, the unit modulus of
the phase, `S₀ > 0` from `geo_normFactor0_pos`). The finitely many smaller `N`:
`ppZ_exists_bound_of_eventually` with `g N = N^{3δ-2} · (N S₀)`, which is positive.
-/

noncomputable section

namespace AJConjecture

/-- The main term of Lemma 3.3 in the form used by the model:
`C_β N e^{-βNπi/8} S₀ = e^{iβπ(1/4 - N/8)} S₀ · N (1 - iβ)^{-1/2}`. -/
private theorem mainTerm_eq_lemma33 (β : ℝ) (N : ℕ) :
    geoGaussConst β * N * Complex.exp (-(β : ℂ) * N * Real.pi * Complex.I / 8) *
        geoNormFactor0 N =
      Complex.exp (((β * Real.pi * (1 / 4 - (N : ℝ) / 8) : ℝ) : ℂ) * Complex.I) *
        (geoNormFactor0 N : ℂ) * ((N : ℂ) * (1 - β * Complex.I) ^ (-(1 / 2 : ℂ))) := by
  have hP : Complex.exp (((β * Real.pi * (1 / 4 - (N : ℝ) / 8) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (β * Real.pi * Complex.I / 4) *
        Complex.exp (-(β : ℂ) * N * Real.pi * Complex.I / 8) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [(geo_gaussConst_eq β).1, hP]
  ring

/-- **Zheng, Lemma 3.3** (`α = 0`) with the explicit constant (3.34), for every real `β`. -/
theorem zhengLemma33_holds (β : ℝ) {δ : ℝ} (hδ : 1 / 2 < δ) (hδ' : δ < 2 / 3) :
    ZhengLemma33 β δ := by
  obtain ⟨K₁, N₁, h₁⟩ := ppZ_windowSum_compare β hδ hδ'
  obtain ⟨K₂, h₂⟩ := ppZ_modelWindowSum β hδ hδ'
  have hg : ∀ N : ℕ, 1 ≤ N → 0 < (N : ℝ) ^ (3 * δ - 2) * (N * geoNormFactor0 N) :=
    fun N hN ↦ by
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    exact mul_pos (Real.rpow_pos_of_pos hN' _) (mul_pos hN' (geo_normFactor0_pos N hN))
  obtain ⟨K, hK⟩ := ppZ_exists_bound_of_eventually
    (f := fun N : ℕ ↦ ‖geoWindowSum N δ β -
      geoGaussConst β * N * Complex.exp (-(β : ℂ) * N * Real.pi * Complex.I / 8) *
        geoNormFactor0 N‖) hg (K₁ + K₂) (max N₁ 65) fun N hN ↦ by
    have hN1 : 1 ≤ N := by omega
    have hS0 := geo_normFactor0_pos N hN1
    have a1 := h₁ N (by omega)
    have a2 := h₂ N (by omega)
    set P : ℂ := Complex.exp (((β * Real.pi * (1 / 4 - (N : ℝ) / 8) : ℝ) : ℂ) * Complex.I)
      with hP
    have hPn : ‖P‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have e : geoWindowSum N δ β - P * (geoNormFactor0 N : ℂ) *
        ((N : ℂ) * (1 - β * Complex.I) ^ (-(1 / 2 : ℂ))) =
        (geoWindowSum N δ β - P * (geoNormFactor0 N : ℂ) * ppZModelWindowSum N δ β) +
          P * (geoNormFactor0 N : ℂ) *
            (ppZModelWindowSum N δ β - (N : ℂ) * (1 - β * Complex.I) ^ (-(1 / 2 : ℂ))) := by
      ring
    have a3 : ‖P * (geoNormFactor0 N : ℂ) *
        (ppZModelWindowSum N δ β - (N : ℂ) * (1 - β * Complex.I) ^ (-(1 / 2 : ℂ)))‖ ≤
        geoNormFactor0 N * (K₂ * (N : ℝ) ^ (3 * δ - 2) * N) := by
      rw [norm_mul, norm_mul, hPn, one_mul, Complex.norm_real, Real.norm_of_nonneg hS0.le]
      exact mul_le_mul_of_nonneg_left a2 hS0.le
    rw [mainTerm_eq_lemma33, e]
    refine (norm_add_le _ _).trans ((add_le_add a1 a3).trans (le_of_eq ?_))
    ring
  exact ⟨K, fun N hN ↦ (hK N hN).trans (le_of_eq (by ring))⟩

end AJConjecture
