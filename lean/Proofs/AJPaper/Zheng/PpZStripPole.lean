import Mathlib
import AJPaper.Zheng.PpZStripShift
import AJPaper.Zheng.PpZPolePair

/-!
# Shifting a line of integration across one simple pole (Unit PpZ, node `PpZ_StripPole`)

Source: Zheng, (5.10) ("counting the residues of the integrand"). Mathlib has the Cauchy–Goursat
theorem on rectangles but no residue theorem; this node supplies the case needed.

`ppZ_strip_shift_simple_pole`: let `P, Q` be entire, `w₀` a point of the open strip
`Y₁ < Im w < Y₂` with `Q(w₀) = 0`, `Q'(w₀) ≠ 0`, `Q ≠ 0` elsewhere on the closed strip, and
`‖P/Q‖ ≤ M/(1 + x²)` on the strip for `|x| ≥ R`. Then

  `∫_ℝ (P/Q)(x + iY₁) dx - ∫_ℝ (P/Q)(x + iY₂) dx = 2πi · P(w₀)/Q'(w₀)`.

Route. `D = dslope Q w₀` is entire (`Complex.differentiableOn_dslope`, or
`differentiable_dslope…`), `D(w₀) = Q'(w₀) ≠ 0` (`dslope_same`), `D(w) = Q(w)/(w - w₀) ≠ 0` for
`w ≠ w₀` in the strip (`dslope_of_ne`); so `H = P/D` is differentiable on the strip and
`P/Q = H/(w - w₀)` off `w₀`. Let `w₁ = w₀ - (Im w₀ - Y₁ + 1) i` (below the strip) and
`G(w) = H(w) - H(w₀)(w₀ - w₁)/(w - w₁)`: differentiable on the strip, `G(w₀) = 0`. Then
`g = dslope G w₀` is differentiable on the strip (the strip is a neighbourhood of `w₀`), and for
`w ≠ w₀`: `g(w) = (P/Q)(w) - H(w₀)((w - w₀)⁻¹ - (w - w₁)⁻¹)`. Decay of `g`: `M/(1+x²)` for `P/Q`
and `|(w - w₀)⁻¹ - (w - w₁)⁻¹| = |w₀ - w₁|/(|w - w₀||w - w₁|) ≤ M'/(1 + x²)` for `|x|` large.
Apply `ppZ_strip_shift` to `g`, and split the two line integrals (`ppZ_strip_integrable`,
`ppZ_integrable_inv_sub_inv`): on `Im = Y₁` the pole pair gives `2πi`
(`ppZ_integral_inv_sub_inv_opposite` with `p = w₀ - iY₁`, `p' = w₁ - iY₁`), on `Im = Y₂` it gives
`0` (`ppZ_integral_inv_sub_inv_same`). `H(w₀) = P(w₀)/Q'(w₀)`.
-/

noncomputable section

namespace AJConjecture

open MeasureTheory Filter Topology Set in
/-- The function whose divided slope at `w₀` is the regular part of `P/Q`. -/
private theorem differentiableOn_numerator_ppZStripPole {P Q : ℂ → ℂ} {S : Set ℂ} {w₀ w₁ c : ℂ}
    (hP : Differentiable ℂ P) (hQ : Differentiable ℂ Q)
    (hDne : ∀ w ∈ S, dslope Q w₀ w ≠ 0) (hne₁ : ∀ w ∈ S, w - w₁ ≠ 0) :
    DifferentiableOn ℂ (fun w ↦ P w / dslope Q w₀ w - c * (w₀ - w₁) / (w - w₁)) S := by
  have hD : Differentiable ℂ (dslope Q w₀) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope univ_mem).mpr hQ.differentiableOn
  have h1 : DifferentiableOn ℂ (fun w : ℂ ↦ w - w₁) S := differentiableOn_id.sub_const w₁
  exact (hP.differentiableOn.div hD.differentiableOn hDne).sub
    ((differentiableOn_const (c * (w₀ - w₁))).div h1 hne₁)

open MeasureTheory Filter Topology Set in
/-- Removing a simple pole of `P/Q` at `w₀` by a pair of simple poles at `w₀` and at a point
`w₁` outside the set leaves a function differentiable on the set. -/
private theorem exists_regular_part_ppZStripPole {P Q : ℂ → ℂ} {S : Set ℂ} {w₀ w₁ : ℂ}
    (hP : Differentiable ℂ P) (hQ : Differentiable ℂ Q) (hS : S ∈ 𝓝 w₀) (hQ0 : Q w₀ = 0)
    (hQ' : deriv Q w₀ ≠ 0) (hQne : ∀ w ∈ S, w ≠ w₀ → Q w ≠ 0) (hw₁ : w₁ ∉ S) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g S ∧ ∀ w ∈ S, w ≠ w₀ →
      g w = P w / Q w - P w₀ / deriv Q w₀ * ((w - w₀)⁻¹ - (w - w₁)⁻¹) := by
  have hDeq : ∀ w, w ≠ w₀ → dslope Q w₀ w = Q w / (w - w₀) := fun w hw ↦ by
    rw [dslope_of_ne _ hw, slope_def_field, hQ0, sub_zero]
  have hDne : ∀ w ∈ S, dslope Q w₀ w ≠ 0 := fun w hw ↦ by
    by_cases h : w = w₀
    · rw [h, dslope_same]
      exact hQ'
    · rw [hDeq w h]
      exact div_ne_zero (hQne w hw h) (sub_ne_zero.mpr h)
  have hne₁ : ∀ w ∈ S, w - w₁ ≠ 0 := fun w hw h ↦ hw₁ (by rwa [← sub_eq_zero.mp h])
  have h₀ : w₀ ∈ S := mem_of_mem_nhds hS
  have hG := differentiableOn_numerator_ppZStripPole (c := P w₀ / deriv Q w₀) hP hQ hDne hne₁
  refine ⟨dslope (fun w ↦ P w / dslope Q w₀ w - P w₀ / deriv Q w₀ * (w₀ - w₁) / (w - w₁)) w₀,
    (Complex.differentiableOn_dslope hS).mpr hG, fun w hw hne ↦ ?_⟩
  have h1 := hne₁ w hw
  have h2 := sub_ne_zero.mpr hne
  have h3 := hQne w hw hne
  have h4 := hne₁ w₀ h₀
  rw [dslope_of_ne _ hne, slope_def_field]
  simp only [dslope_same, hDeq w hne]
  field_simp
  ring

open MeasureTheory Filter Topology Set in
/-- The elementary inequality behind the decay of a pair of poles with the same real part. -/
private theorem one_add_sq_le_ppZStripPole {u x : ℝ} (hx : |u| + 1 ≤ |x|) :
    1 + x ^ 2 ≤ (1 + (1 + |u|) ^ 2) * |x - u| ^ 2 := by
  have h1 : 1 ≤ |x - u| := by
    have := abs_sub_abs_le_abs_sub x u
    linarith
  have h2 : |x| ≤ (1 + |u|) * |x - u| := by
    have := abs_sub_abs_le_abs_sub x u
    nlinarith [abs_nonneg u]
  have h3 : x ^ 2 ≤ ((1 + |u|) * |x - u|) ^ 2 := by
    rw [← sq_abs x]
    exact pow_le_pow_left₀ (abs_nonneg x) h2 2
  nlinarith

open MeasureTheory Filter Topology Set in
/-- A pair of simple poles with the same real part decays like `1/(1 + x²)`. -/
private theorem norm_inv_sub_inv_le_ppZStripPole {w w₀ w₁ : ℂ} (h₁ : w₁.re = w₀.re)
    (hw : |w₀.re| + 1 ≤ |w.re|) :
    ‖(w - w₀)⁻¹ - (w - w₁)⁻¹‖ ≤ ‖w₀ - w₁‖ * (1 + (1 + |w₀.re|) ^ 2) / (1 + w.re ^ 2) := by
  have hd : 1 ≤ |w.re - w₀.re| := by
    have := abs_sub_abs_le_abs_sub w.re w₀.re
    linarith
  have hd0 : |w.re - w₀.re| ≤ ‖w - w₀‖ := by simpa using Complex.abs_re_le_norm (w - w₀)
  have hd1 : |w.re - w₀.re| ≤ ‖w - w₁‖ := by simpa [h₁] using Complex.abs_re_le_norm (w - w₁)
  have hn0 : w - w₀ ≠ 0 := norm_pos_iff.mp (by linarith)
  have hn1 : w - w₁ ≠ 0 := norm_pos_iff.mp (by linarith)
  have heq : (w - w₀)⁻¹ - (w - w₁)⁻¹ = (w₀ - w₁) / ((w - w₀) * (w - w₁)) := by
    field_simp
    ring
  rw [heq, norm_div, norm_mul, div_le_div_iff₀ (by positivity) (by positivity), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h4 := one_add_sq_le_ppZStripPole hw
  have h5 : |w.re - w₀.re| ^ 2 ≤ ‖w - w₀‖ * ‖w - w₁‖ := by
    rw [sq]
    exact mul_le_mul hd0 hd1 (abs_nonneg _) (norm_nonneg _)
  nlinarith [abs_nonneg w₀.re]

open MeasureTheory Filter Topology Set in
/-- On a horizontal line avoiding both poles, the integral of `P/Q` is the integral of its regular
part plus the integral of the pair of poles. -/
private theorem integral_line_ppZStripPole {P Q g : ℂ → ℂ} {c w₀ w₁ : ℂ} {y : ℝ}
    (hg : Integrable fun x : ℝ ↦ g (x + y * Complex.I)) (h0 : w₀.im ≠ y) (h1 : w₁.im ≠ y)
    (hform : ∀ x : ℝ, g (x + y * Complex.I) =
      P (x + y * Complex.I) / Q (x + y * Complex.I) -
        c * ((x + y * Complex.I - w₀)⁻¹ - (x + y * Complex.I - w₁)⁻¹)) :
    ∫ x : ℝ, P (x + y * Complex.I) / Q (x + y * Complex.I) =
      (∫ x : ℝ, g (x + y * Complex.I)) + c * ∫ x : ℝ,
        (((x : ℂ) - (w₀ - y * Complex.I))⁻¹ - ((x : ℂ) - (w₁ - y * Complex.I))⁻¹) := by
  have hpair : Integrable fun x : ℝ ↦
      c * (((x : ℂ) - (w₀ - y * Complex.I))⁻¹ - ((x : ℂ) - (w₁ - y * Complex.I))⁻¹) :=
    (ppZ_integrable_inv_sub_inv (p := w₀ - y * Complex.I) (p' := w₁ - y * Complex.I)
      (by simpa [sub_eq_zero] using h0) (by simpa [sub_eq_zero] using h1)).const_mul c
  rw [← integral_const_mul, ← integral_add hg hpair]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [hform x]
  ring

open MeasureTheory Filter Topology Set in
/-- **Strip shift across one simple pole**: the difference of the two line integrals of `P/Q` is
`2πi` times the residue `P(w₀)/Q'(w₀)`. -/
theorem ppZ_strip_shift_simple_pole {P Q : ℂ → ℂ} {Y₁ Y₂ M R : ℝ} {w₀ : ℂ}
    (hP : Differentiable ℂ P) (hQ : Differentiable ℂ Q)
    (h1 : Y₁ < w₀.im) (h2 : w₀.im < Y₂) (hQ0 : Q w₀ = 0) (hQ' : deriv Q w₀ ≠ 0)
    (hQne : ∀ w : ℂ, Y₁ ≤ w.im → w.im ≤ Y₂ → w ≠ w₀ → Q w ≠ 0)
    (hdec : ∀ x y : ℝ, Y₁ ≤ y → y ≤ Y₂ → R ≤ |x| →
      ‖P (x + y * Complex.I) / Q (x + y * Complex.I)‖ ≤ M / (1 + x ^ 2)) :
    (∫ x : ℝ, P (x + Y₁ * Complex.I) / Q (x + Y₁ * Complex.I)) -
        ∫ x : ℝ, P (x + Y₂ * Complex.I) / Q (x + Y₂ * Complex.I) =
      2 * Real.pi * Complex.I * (P w₀ / deriv Q w₀) := by
  set w₁ : ℂ := w₀ - ((w₀.im - Y₁ + 1 : ℝ) : ℂ) * Complex.I with hw₁
  have hre : w₁.re = w₀.re := by simp [hw₁]
  have him : w₁.im = Y₁ - 1 := by
    simp only [hw₁, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    ring
  have hS : {w : ℂ | Y₁ ≤ w.im ∧ w.im ≤ Y₂} ∈ 𝓝 w₀ :=
    Complex.continuous_im.continuousAt.preimage_mem_nhds (Icc_mem_nhds h1 h2)
  obtain ⟨g, hg, hform⟩ := exists_regular_part_ppZStripPole hP hQ hS hQ0 hQ'
    (fun w hw ↦ hQne w hw.1 hw.2) (w₁ := w₁)
    (fun h ↦ by have := h.1; rw [him] at this; linarith)
  set c : ℂ := P w₀ / deriv Q w₀ with hc
  have hmem : ∀ x y : ℝ, Y₁ ≤ y → y ≤ Y₂ →
      (x + y * Complex.I : ℂ) ∈ {w : ℂ | Y₁ ≤ w.im ∧ w.im ≤ Y₂} := fun x y hy1 hy2 ↦ by
    simp [hy1, hy2]
  have hdecg : ∀ x y : ℝ, Y₁ ≤ y → y ≤ Y₂ → max R (|w₀.re| + 1) ≤ |x| →
      ‖g (x + y * Complex.I)‖ ≤
        (M + ‖c‖ * (‖w₀ - w₁‖ * (1 + (1 + |w₀.re|) ^ 2))) / (1 + x ^ 2) := by
    intro x y hy1 hy2 hx
    have hx1 : |w₀.re| + 1 ≤ |(x + y * Complex.I : ℂ).re| := by
      simpa using (le_max_right _ _).trans hx
    have hne : (x + y * Complex.I : ℂ) ≠ w₀ := fun h ↦ by
      rw [h] at hx1
      linarith
    rw [hform _ (hmem x y hy1 hy2) hne, add_div]
    refine (norm_sub_le _ _).trans (add_le_add (hdec x y hy1 hy2 ((le_max_left _ _).trans hx)) ?_)
    rw [norm_mul, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    simpa using norm_inv_sub_inv_le_ppZStripPole hre hx1
  have hshift := ppZ_strip_shift (h1.le.trans h2.le) hg hdecg
  have hline : ∀ y : ℝ, Y₁ ≤ y → y ≤ Y₂ → w₀.im ≠ y →
      ∫ x : ℝ, P (x + y * Complex.I) / Q (x + y * Complex.I) =
      (∫ x : ℝ, g (x + y * Complex.I)) + c * ∫ x : ℝ,
        (((x : ℂ) - (w₀ - y * Complex.I))⁻¹ - ((x : ℂ) - (w₁ - y * Complex.I))⁻¹) :=
    fun y hy1 hy2 hy ↦ integral_line_ppZStripPole (ppZ_strip_integrable hg hdecg hy1 hy2) hy
      (by rw [him]; linarith) fun x ↦ hform _ (hmem x y hy1 hy2) fun h ↦ hy (by simp [← h])
  rw [hline Y₁ le_rfl (h1.le.trans h2.le) h1.ne', hline Y₂ (h1.le.trans h2.le) le_rfl h2.ne,
    ppZ_integral_inv_sub_inv_opposite (by simpa using h1) (by simp [him]),
    ppZ_integral_inv_sub_inv_same (by simpa using h2) (by simp [him]; linarith), hshift]
  ring

end AJConjecture
