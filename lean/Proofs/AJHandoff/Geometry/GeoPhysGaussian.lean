import Mathlib
import AJHandoff.Geometry.GeoPhysDefs

/-!
# Zheng's Gaussian constant is nonzero (G-PHYS, unconditional)

`C_β = e^{βπi/4} ∫_{ℝ²} exp(-π(x² + 2xy + 2y²) + βπi x²/2) dx dy = e^{βπi/4} (1 - βi)^{-1/2}`;
in particular `C_β ≠ 0` for every real `β`. (Lemma 3.3 asserts a nonzero constant; here it is
computed.)

Route. Complete the square: `x² + 2xy + 2y² = x²/2 + 2(y + x/2)²`. The real quadratic part is
positive definite, so the integrand is integrable on `ℝ²`; Fubini, then
`integral_gaussian_complex` (`∫ exp(-b t²) = (π/b)^{1/2}` for `Re b > 0`) twice:
`∫ dy = (1/2)^{1/2}`, `∫ dx = (2/(1 - βi))^{1/2}`.
-/

noncomputable section

namespace AJConjecture

open MeasureTheory

/-- The integrand of Zheng's Gaussian constant (3.34) at `α = 0`. -/
private def gaussIntegrand (β : ℝ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * (p.1 ^ 2 + 2 * p.1 * p.2 + 2 * p.2 ^ 2) +
    β * Real.pi * Complex.I * p.1 ^ 2 / 2)

/-- The integrand of (3.34) is integrable on `ℝ²`: it is dominated by `e^{-π(x² + y²)/4}`. -/
private theorem integrable_gaussIntegrand (β : ℝ) :
    Integrable (gaussIntegrand β) (volume.prod volume) := by
  have hg : Integrable (fun x : ℝ ↦ Real.exp (-(Real.pi / 4) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  refine (hg.mul_prod hg).mono' ?_ (Filter.Eventually.of_forall fun p ↦ ?_)
  · exact (Continuous.aestronglyMeasurable (by unfold gaussIntegrand; fun_prop))
  · have harg : -(Real.pi : ℂ) * (p.1 ^ 2 + 2 * p.1 * p.2 + 2 * p.2 ^ 2) +
        β * Real.pi * Complex.I * p.1 ^ 2 / 2 =
        ((-Real.pi * (p.1 ^ 2 + 2 * p.1 * p.2 + 2 * p.2 ^ 2) : ℝ) : ℂ) +
          ((β * Real.pi * p.1 ^ 2 / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [gaussIntegrand, harg, Complex.exp_add, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_exp_ofReal, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hq : 0 ≤ 3 / 4 * (p.1 + 4 / 3 * p.2) ^ 2 + 5 / 12 * p.2 ^ 2 := by positivity
    nlinarith [mul_nonneg Real.pi_pos.le hq]

/-- The inner integral: `∫ e^{-π(x² + 2xy + 2y²)} dy = 2^{-1/2} e^{-πx²/2}`. -/
private theorem integral_gaussIntegrand_inner (β x : ℝ) :
    ∫ y : ℝ, gaussIntegrand β (x, y) =
      (1 / 2 : ℂ) ^ (1 / 2 : ℂ) *
        Complex.exp (-((Real.pi : ℂ) / 2 * (1 - β * Complex.I)) * (x : ℂ) ^ 2) := by
  have hb : (-2 * (Real.pi : ℂ)).re < 0 := by
    simp [Real.pi_pos]
  have hfun : ∀ y : ℝ, gaussIntegrand β (x, y) =
      Complex.exp (-2 * (Real.pi : ℂ) * (y : ℂ) ^ 2 + (-2 * Real.pi * x) * y +
        (-(Real.pi : ℂ) * x ^ 2 + β * Real.pi * Complex.I * x ^ 2 / 2)) := by
    intro y
    rw [gaussIntegrand]
    congr 1
    ring
  simp_rw [hfun]
  rw [integral_cexp_quadratic hb]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  congr 2
  · field_simp
  · field_simp
    ring

/-- The Gaussian constant of Lemma 3.3 in closed form, and its nonvanishing. -/
theorem geo_gaussConst_eq (β : ℝ) :
    geoGaussConst β =
        Complex.exp (β * Real.pi * Complex.I / 4) * (1 - β * Complex.I) ^ (-(1 / 2 : ℂ)) ∧
      geoGaussConst β ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hre : (1 - β * Complex.I).re = 1 := by simp
  have hw : 1 - (β : ℂ) * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this
  have harg : (1 - (β : ℂ) * Complex.I).arg ≠ Real.pi := by
    have h := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hre]; norm_num))
    intro h'
    rw [h', abs_of_pos Real.pi_pos] at h
    linarith [Real.pi_pos]
  have hbre : 0 < ((Real.pi : ℂ) / 2 * (1 - β * Complex.I)).re := by
    simp [Real.pi_pos]
  have hint : ∫ p : ℝ × ℝ, gaussIntegrand β p = (1 - β * Complex.I) ^ (-(1 / 2 : ℂ)) := by
    rw [Measure.volume_eq_prod, integral_prod _ (integrable_gaussIntegrand β)]
    simp_rw [integral_gaussIntegrand_inner]
    rw [integral_const_mul, integral_gaussian_complex hbre]
    have h2 : (Real.pi : ℂ) / ((Real.pi : ℂ) / 2 * (1 - β * Complex.I)) =
        2 * (1 - β * Complex.I)⁻¹ := by
      field_simp
    have hmem : (1 / 2 : ℂ).arg + (2 * (1 - β * Complex.I)⁻¹).arg ∈
        Set.Ioc (-Real.pi) Real.pi := by
      have h0 : (1 / 2 : ℂ).arg = 0 := by
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
        exact Complex.arg_ofReal_of_nonneg (by norm_num)
      rw [h0, zero_add]
      exact Complex.arg_mem_Ioc _
    rw [h2, ← Complex.mul_cpow hmem, ← mul_assoc, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_mul,
      Complex.inv_cpow _ _ harg, Complex.cpow_neg]
  have hval : geoGaussConst β =
      Complex.exp (β * Real.pi * Complex.I / 4) * (1 - β * Complex.I) ^ (-(1 / 2 : ℂ)) := by
    rw [← hint]
    rfl
  refine ⟨hval, ?_⟩
  rw [hval]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h ↦ hw h.1

end AJConjecture
