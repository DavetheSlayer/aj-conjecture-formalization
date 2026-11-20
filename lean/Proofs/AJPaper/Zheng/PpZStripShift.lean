import Mathlib

/-!
# Shifting a horizontal line of integration: the holomorphic case
(Unit PpZ, node `PpZ_StripShift`)

Source: Zheng, Lemma 5.1 (the contour `C` is moved to `C + z₀`); this is the pole-free part.

If `f` is complex differentiable on the closed strip `Y₁ ≤ Im w ≤ Y₂` and
`‖f(x + iy)‖ ≤ M/(1 + x²)` there for `|x| ≥ R`, then
`∫_ℝ f(x + iY₁) dx = ∫_ℝ f(x + iY₂) dx` (`ppZ_strip_shift`), both integrals being absolutely
convergent (`ppZ_strip_integrable`).

Route (as in Mathlib's `GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I`). For `T ≥ R`
apply `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` to the rectangle with corners
`-T + iY₁`, `T + iY₂` (a subset of the strip). The two vertical integrals are bounded by
`(Y₂ - Y₁) M/(1 + T²) → 0` (`intervalIntegral.norm_integral_le_of_norm_le_const`). The horizontal
ones converge to the improper integrals (`MeasureTheory.intervalIntegral_tendsto_integral`), once
`x ↦ f(x + iy)` is integrable: it is continuous (`hf.continuousOn` composed with a continuous map
into the strip), bounded on `[-R', R']`, and dominated by `M/(1 + x²)` outside
(`integrable_inv_one_add_sq`). Uniqueness of limits (`tendsto_nhds_unique`).
-/

noncomputable section

namespace AJConjecture

open MeasureTheory Filter Topology Set in
/-- The restriction of a function continuous on a closed strip to a horizontal line of the
strip is continuous. -/
private theorem continuous_line_ppZStripShift {f : ℂ → ℂ} {Y₁ Y₂ : ℝ}
    (hf : DifferentiableOn ℂ f {w : ℂ | Y₁ ≤ w.im ∧ w.im ≤ Y₂})
    {y : ℝ} (hy1 : Y₁ ≤ y) (hy2 : y ≤ Y₂) :
    Continuous fun x : ℝ ↦ f (x + y * Complex.I) := by
  rw [← continuousOn_univ]
  refine hf.continuousOn.comp (by fun_prop) fun x _ ↦ ?_
  simp [hy1, hy2]

open MeasureTheory Filter Topology Set in
/-- On a strip of holomorphy with decay `M/(1 + x²)` every horizontal line integral converges. -/
theorem ppZ_strip_integrable {f : ℂ → ℂ} {Y₁ Y₂ M R : ℝ}
    (hf : DifferentiableOn ℂ f {w : ℂ | Y₁ ≤ w.im ∧ w.im ≤ Y₂})
    (hdec : ∀ x y : ℝ, Y₁ ≤ y → y ≤ Y₂ → R ≤ |x| →
      ‖f (x + y * Complex.I)‖ ≤ M / (1 + x ^ 2))
    {y : ℝ} (hy1 : Y₁ ≤ y) (hy2 : y ≤ Y₂) :
    MeasureTheory.Integrable fun x : ℝ ↦ f (x + y * Complex.I) := by
  have hc := continuous_line_ppZStripShift hf hy1 hy2
  rw [← integrableOn_univ, ← union_compl_self (Icc (-R) R)]
  refine IntegrableOn.union hc.integrableOn_Icc ?_
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul M).integrableOn)
    hc.aestronglyMeasurable.restrict ?_
  refine ae_restrict_of_forall_mem measurableSet_Icc.compl fun x hx ↦ ?_
  rw [← div_eq_mul_inv]
  refine hdec x y hy1 hy2 ?_
  by_contra h
  exact hx ⟨(abs_lt.mp (not_le.mp h)).1.le, (abs_lt.mp (not_le.mp h)).2.le⟩

open MeasureTheory Filter Topology Set in
/-- The integral over a vertical side of the rectangle tends to `0`. -/
private theorem tendsto_vertical_ppZStripShift {f : ℂ → ℂ} {Y₁ Y₂ M R : ℝ} (hY : Y₁ ≤ Y₂)
    (hdec : ∀ x y : ℝ, Y₁ ≤ y → y ≤ Y₂ → R ≤ |x| →
      ‖f (x + y * Complex.I)‖ ≤ M / (1 + x ^ 2)) (s : ℝ) (hs : |s| = 1) :
    Tendsto (fun T : ℝ ↦ ∫ y : ℝ in Y₁..Y₂, f ((s * T : ℝ) + y * Complex.I)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun T : ℝ ↦ M / (1 + T ^ 2) * |Y₂ - Y₁|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ ↦ 1 + T ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
    simpa [div_eq_mul_inv] using (h1.inv_tendsto_atTop.const_mul M).mul_const |Y₂ - Y₁|
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
  filter_upwards [eventually_ge_atTop R, eventually_ge_atTop 0] with T hT hT0
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy ↦ ?_
  rw [uIoc_of_le hY] at hy
  have h := hdec (s * T) y hy.1.le hy.2
    (by rw [abs_mul, hs, one_mul, abs_of_nonneg hT0]; exact hT)
  have h2 : (s * T) ^ 2 = T ^ 2 := by
    rw [mul_pow, ← sq_abs s, hs]; ring
  rwa [h2] at h

open MeasureTheory Filter Topology Set in
/-- **Strip shift** for a holomorphic function with decay `M/(1 + x²)`. -/
theorem ppZ_strip_shift {f : ℂ → ℂ} {Y₁ Y₂ M R : ℝ} (hY : Y₁ ≤ Y₂)
    (hf : DifferentiableOn ℂ f {w : ℂ | Y₁ ≤ w.im ∧ w.im ≤ Y₂})
    (hdec : ∀ x y : ℝ, Y₁ ≤ y → y ≤ Y₂ → R ≤ |x| →
      ‖f (x + y * Complex.I)‖ ≤ M / (1 + x ^ 2)) :
    ∫ x : ℝ, f (x + Y₁ * Complex.I) = ∫ x : ℝ, f (x + Y₂ * Complex.I) := by
  have h1 := intervalIntegral_tendsto_integral (ppZ_strip_integrable hf hdec le_rfl hY)
    tendsto_neg_atTop_atBot tendsto_id
  have h2 := intervalIntegral_tendsto_integral (ppZ_strip_integrable hf hdec hY le_rfl)
    tendsto_neg_atTop_atBot tendsto_id
  have hv1 := tendsto_vertical_ppZStripShift hY hdec 1 (by simp)
  have hv2 := tendsto_vertical_ppZStripShift hY hdec (-1) (by simp)
  have hC : ∀ T : ℝ, (∫ x : ℝ in -T..T, f (x + Y₁ * Complex.I)) -
      (∫ x : ℝ in -T..T, f (x + Y₂ * Complex.I)) =
      Complex.I * (∫ y : ℝ in Y₁..Y₂, f (((-1 : ℝ) * T : ℝ) + y * Complex.I)) -
      Complex.I * (∫ y : ℝ in Y₁..Y₂, f (((1 : ℝ) * T : ℝ) + y * Complex.I)) := by
    intro T
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      (-T + Y₁ * Complex.I) (T + Y₂ * Complex.I) (hf.mono fun w hw ↦ by
        have := hw.2
        simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, neg_zero, zero_add,
          add_zero, mem_preimage, uIcc_of_le hY, mem_Icc] at this
        exact this)
    simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, neg_zero, zero_add,
      add_zero, Complex.add_re, Complex.neg_re, Complex.mul_re, sub_zero, smul_eq_mul,
      Complex.ofReal_neg] at h
    simp only [neg_mul, one_mul, Complex.ofReal_neg]
    linear_combination h
  have h3 := h1.sub h2
  simp only [id] at h3
  have h4 := (hv2.const_mul Complex.I).sub (hv1.const_mul Complex.I)
  simp only [mul_zero, sub_zero] at h4
  have h5 : (fun T : ℝ ↦ (∫ x : ℝ in -T..T, f (x + Y₁ * Complex.I)) -
      ∫ x : ℝ in -T..T, f (x + Y₂ * Complex.I)) = fun T : ℝ ↦
      Complex.I * (∫ y : ℝ in Y₁..Y₂, f (((-1 : ℝ) * T : ℝ) + y * Complex.I)) -
      Complex.I * (∫ y : ℝ in Y₁..Y₂, f (((1 : ℝ) * T : ℝ) + y * Complex.I)) := funext hC
  rw [h5] at h3
  exact sub_eq_zero.mp (tendsto_nhds_unique h3 h4)

end AJConjecture
