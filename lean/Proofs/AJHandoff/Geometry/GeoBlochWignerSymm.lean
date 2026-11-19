import Mathlib
import AJFamily.Volume.BlochWignerI
import AJHandoff.Geometry.GeoBlochWignerCont

/-!
# Symmetries of the Bloch–Wigner dilogarithm and the regulator primitive

`D(conj z) = -D(z)`, `D(1/z) = -D(z)`, `D` vanishes on the real line, and `D(-i) = -G`. The
regulator primitive of the extra curve is `U(r) = D(r) - D(-r)` (`geoRegPrimitive`); it is
continuous on `ℂ`, tends to `0` at infinity, vanishes at `r = 0, 1, -1` and takes the values
`U(±i) = ±2G`.

Route. On the closed disc, `Im Li₂(conj z) = -Im Li₂(z)` termwise and
`arg(1 - conj z) = -arg(1 - z)` because `1 - z` is never on the negative real axis there; outside
the disc use the definition. For `D(1/z)`: by definition when `|z| ≠ 1`, and by the conjugation
symmetry when `|z| = 1` (then `1/z = conj z`). On the real line the series is real and
`arg(1 - x) = 0` for `x < 1`, while `log |x| = 0` at `x = ±1`. `D(-i) = D(conj i) = -G` by
`blochWigner_I`.
-/

open Filter Topology

noncomputable section

namespace AJConjecture

/-- The regulator primitive `U(r) = D(r) - D(-r)` of the extra curve, `D` the Bloch–Wigner
dilogarithm. -/
def geoRegPrimitive (z : ℂ) : ℝ :=
  blochWigner z - blochWigner (-z)

/-- The disc formula `Im Li₂(z) + arg(1 - z) log ‖z‖` of the Bloch–Wigner function. -/
private def bwDiscTerm (z : ℂ) : ℝ :=
  (dilogSeries z).im + Complex.arg (1 - z) * Real.log ‖z‖

/-- `blochWigner` in terms of the disc formula. -/
private theorem blochWigner_eq_ite_disc (z : ℂ) :
    blochWigner z = if ‖z‖ ≤ 1 then bwDiscTerm z else -bwDiscTerm z⁻¹ := rfl

/-- `Li₂(conj z) = conj Li₂(z)`. -/
private theorem dilogSeries_conj (z : ℂ) :
    dilogSeries (starRingEnd ℂ z) = starRingEnd ℂ (dilogSeries z) := by
  unfold dilogSeries
  rw [Complex.conj_tsum]
  congr 1
  ext n
  simp [map_div₀, map_pow]

/-- The disc formula is odd under conjugation on the closed disc. -/
private theorem bwDiscTerm_conj {z : ℂ} (hz : ‖z‖ ≤ 1) :
    bwDiscTerm (starRingEnd ℂ z) = -bwDiscTerm z := by
  have harg : Complex.arg (1 - z) ≠ Real.pi := by
    rw [Ne, Complex.arg_eq_pi_iff, Complex.sub_re, Complex.one_re]
    intro h
    linarith [h.1, Complex.re_le_norm z]
  have e : 1 - starRingEnd ℂ z = starRingEnd ℂ (1 - z) := by simp
  unfold bwDiscTerm
  rw [dilogSeries_conj, Complex.conj_im, Complex.norm_conj, e, Complex.arg_conj, ite_eq_right harg]
  ring

/-- `D(conj z) = -D(z)`. -/
theorem geo_blochWigner_conj (z : ℂ) : blochWigner (starRingEnd ℂ z) = -blochWigner z := by
  by_cases hz : ‖z‖ ≤ 1
  · rw [blochWigner_eq_ite_disc, blochWigner_eq_ite_disc, ite_eq_left (by rwa [Complex.norm_conj]),
      ite_eq_left hz, bwDiscTerm_conj hz]
  · have hz' : ‖z⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hz))
    rw [blochWigner_eq_ite_disc, blochWigner_eq_ite_disc, ite_eq_right (by rwa [Complex.norm_conj]),
      ite_eq_right hz, ← map_inv₀, bwDiscTerm_conj hz']

/-- `D(1/z) = -D(z)`. -/
theorem geo_blochWigner_inv {z : ℂ} (hz : z ≠ 0) : blochWigner z⁻¹ = -blochWigner z := by
  rcases lt_trichotomy ‖z‖ 1 with h | h | h
  · have h' : ¬ ‖z⁻¹‖ ≤ 1 := by
      rw [norm_inv, not_le]
      exact one_lt_inv₀ (norm_pos_iff.2 hz) |>.2 h
    rw [blochWigner_eq_ite_disc, blochWigner_eq_ite_disc, ite_eq_right h', ite_eq_left h.le,
      inv_inv]
  · rw [Complex.inv_eq_conj h, geo_blochWigner_conj]
  · have h' : ‖z⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ h.le
    rw [blochWigner_eq_ite_disc, blochWigner_eq_ite_disc, ite_eq_left h', ite_eq_right (not_le.2 h),
      neg_neg]

/-- `D` vanishes on the real line. -/
theorem geo_blochWigner_ofReal (x : ℝ) : blochWigner x = 0 := by
  have h := geo_blochWigner_conj (x : ℂ)
  rw [Complex.conj_ofReal] at h
  linarith

/-- `D(-i) = -G`. -/
theorem geo_blochWigner_neg_I : blochWigner (-Complex.I) = -catalanConstant := by
  rw [← Complex.conj_I, geo_blochWigner_conj, blochWigner_I]

/-- `U` is continuous on `ℂ`. -/
theorem geo_continuous_regPrimitive : Continuous geoRegPrimitive :=
  geo_continuous_blochWigner.sub (geo_continuous_blochWigner.comp continuous_neg)

/-- `U(r) → 0` as `r → ∞`. -/
theorem geo_tendsto_regPrimitive_cocompact :
    Tendsto geoRegPrimitive (cocompact ℂ) (𝓝 0) := by
  have hneg : Tendsto (fun z : ℂ ↦ -z) (cocompact ℂ) (cocompact ℂ) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact Filter.tendsto_neg_cobounded
  have h := geo_tendsto_blochWigner_cocompact.sub (geo_tendsto_blochWigner_cocompact.comp hneg)
  rw [sub_zero] at h
  exact h

/-- The values of `U` at the four punctures `r = 0, 1, -1` (and `∞`, by the limit above) and at
the two branches `r = ±i` over the nodes: `U(0) = U(1) = U(-1) = 0`, `U(i) = 2G`,
`U(-i) = -2G`. -/
theorem geo_regPrimitive_values :
    geoRegPrimitive 0 = 0 ∧ geoRegPrimitive 1 = 0 ∧ geoRegPrimitive (-1) = 0 ∧
      geoRegPrimitive Complex.I = 2 * catalanConstant ∧
      geoRegPrimitive (-Complex.I) = -(2 * catalanConstant) := by
  have h1 : blochWigner 1 = 0 := by exact_mod_cast geo_blochWigner_ofReal 1
  have hm1 : blochWigner (-1) = 0 := by exact_mod_cast geo_blochWigner_ofReal (-1)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [geoRegPrimitive, neg_zero, neg_neg, h1, hm1,
    geo_blochWigner_zero, blochWigner_I, geo_blochWigner_neg_I] <;> ring

end AJConjecture
