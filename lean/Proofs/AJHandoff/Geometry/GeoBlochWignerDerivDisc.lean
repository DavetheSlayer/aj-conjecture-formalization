import Mathlib
import AJFamily.VolumeDefs

/-!
# The differential of the Bloch–Wigner dilogarithm inside the unit disc

The real differential of `D` is the regulator form `η(z, 1 - z)`:
`dD = log |z| d arg(1 - z) - log |1 - z| d arg z`, i.e. on a tangent vector `h`,
`dD(z)(h) = log‖z‖ Im(-h/(1 - z)) - log‖1 - z‖ Im(h/z)` (`geoBWDeriv`). This file proves it on the
punctured open disc `0 < |z| < 1`, together with the complex derivative
`Li₂'(v) = -log(1 - v)/v` of the dilogarithm series.

Route. `dilogSeries` is a power series of radius `1`; differentiate termwise
(`hasDerivAt_tsum_of_isPreconnected` or the `HasFPowerSeriesOnBall` API) and compare with
`-log(1 - v) = ∑ vⁿ/n` (`Complex.hasSum_taylorSeries_neg_log`). Then
`D = Im ∘ Li₂ + (arg ∘ (1 - ·)) · (log ∘ ‖·‖)`: `Im Li₂` has real differential `Im(Li₂'(z) h)`,
`arg(1 - z) = Im log(1 - z)` is differentiable since `Re(1 - z) > 0`, and `log ‖z‖` has differential
`Re(h/z)`. The terms `Im(-log(1-z) h / z)` and `arg(1 - z) Re(h/z)` combine with
`log|1 - z| = Re log(1 - z)` to the stated form.
-/

open Filter Topology

noncomputable section

namespace AJConjecture

/-- The differential of the Bloch–Wigner function at `z`, the regulator form `η(z, 1 - z)`:
`h ↦ log‖z‖ Im(-h/(1 - z)) - log‖1 - z‖ Im(h/z)`. -/
def geoBWDeriv (z : ℂ) : ℂ →L[ℝ] ℝ :=
  Real.log ‖z‖ • (Complex.imCLM.comp ((-(1 - z)⁻¹ : ℂ) • ContinuousLinearMap.id ℝ ℂ)) -
    Real.log ‖1 - z‖ • (Complex.imCLM.comp (z⁻¹ • ContinuousLinearMap.id ℝ ℂ))

theorem geoBWDeriv_apply (z h : ℂ) :
    geoBWDeriv z h = Real.log ‖z‖ * (-h / (1 - z)).im - Real.log ‖1 - z‖ * (h / z).im := by
  simp only [geoBWDeriv, sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, Complex.imCLM_apply,
    smul_eq_mul]
  rw [show -(1 - z)⁻¹ * h = -h / (1 - z) by ring, show z⁻¹ * h = h / z by ring]

/-- The dilogarithm series has complex derivative `-log(1 - v)/v` on the punctured open disc. -/
theorem geo_hasDerivAt_dilogSeries {v : ℂ} (hv0 : v ≠ 0) (hv1 : ‖v‖ < 1) :
    HasDerivAt dilogSeries (-Complex.log (1 - v) / v) v := by
  obtain ⟨ρ, hvρ, hρ1⟩ := exists_between hv1
  have hρ0 : 0 ≤ ρ := (norm_nonneg v).trans hvρ.le
  have hsum : HasSum (fun n : ℕ ↦ v ^ n / ((n : ℂ) + 1)) (-Complex.log (1 - v) / v) := by
    have h := (Complex.hasSum_taylorSeries_neg_log' hv1).div_const v
    have e : (fun n : ℕ ↦ v ^ (n + 1) / ((n : ℂ) + 1) / v) = fun n : ℕ ↦ v ^ n / ((n : ℂ) + 1) := by
      ext n
      rw [pow_succ]
      field_simp
    rwa [e] at h
  have hderiv : ∀ (n : ℕ) (y : ℂ), y ∈ Metric.ball (0 : ℂ) ρ →
      HasDerivAt (fun y ↦ y ^ (n + 1) / ((n : ℂ) + 1) ^ 2) (y ^ n / ((n : ℂ) + 1)) y := by
    intro n y _
    have h := (hasDerivAt_pow (n + 1) y).div_const (((n : ℂ) + 1) ^ 2)
    convert h using 1
    have : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
    rw [Nat.add_sub_cancel]
    push_cast
    field_simp
  have hbound : ∀ (n : ℕ) (y : ℂ), y ∈ Metric.ball (0 : ℂ) ρ → ‖y ^ n / ((n : ℂ) + 1)‖ ≤ ρ ^ n := by
    intro n y hy
    rw [mem_ball_zero_iff] at hy
    have hn : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
      rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast
      ring
    rw [norm_div, norm_pow, hn]
    calc ‖y‖ ^ n / ((n : ℝ) + 1) ≤ ‖y‖ ^ n :=
          div_le_self (pow_nonneg (norm_nonneg _) _) (by linarith [n.cast_nonneg (α := ℝ)])
      _ ≤ ρ ^ n := pow_le_pow_left₀ (norm_nonneg _) hy.le n
  have h := hasDerivAt_tsum_of_isPreconnected (summable_geometric_of_lt_one hρ0 hρ1)
    Metric.isOpen_ball (convex_ball (0 : ℂ) ρ).isPreconnected hderiv hbound
    (Metric.mem_ball_self ((norm_nonneg v).trans_lt hvρ))
    (by simp) (mem_ball_zero_iff.2 hvρ)
  rw [hsum.tsum_eq] at h
  exact h

/-- `log ‖w‖` is real differentiable away from `0`, with differential `h ↦ Re(h/z)`. -/
private theorem hasFDerivAt_log_norm {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun w : ℂ ↦ Real.log ‖w‖)
      (Complex.reCLM.comp
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) z⁻¹).restrictScalars ℝ)) z := by
  obtain ⟨L, hL, hre⟩ : ∃ L : ℂ → ℂ, HasDerivAt L z⁻¹ z ∧ ∀ w, (L w).re = Real.log ‖w‖ := by
    rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hz with hs | hs
    · exact ⟨Complex.log, Complex.hasDerivAt_log hs, fun w ↦ Complex.log_re w⟩
    · refine ⟨fun w ↦ Complex.log (-w), ?_, fun w ↦ by rw [Complex.log_re, norm_neg]⟩
      have h : HasDerivAt (fun w ↦ Complex.log (-w)) ((-z)⁻¹ * -1) z :=
        (Complex.hasDerivAt_log hs).comp z (hasDerivAt_neg z)
      exact h.congr_deriv (by rw [inv_neg, neg_mul_neg, mul_one])
  have e : (fun w : ℂ ↦ Real.log ‖w‖) = fun w ↦ (L w).re := funext fun w ↦ (hre w).symm
  rw [e]
  exact Complex.reCLM.hasFDerivAt.comp z (hL.hasFDerivAt.restrictScalars ℝ)

/-- `arg (1 - w)` is real differentiable where `1 - w` lies in the slit plane. -/
private theorem hasFDerivAt_arg_one_sub {z : ℂ} (hs : 1 - z ∈ Complex.slitPlane) :
    HasFDerivAt (fun w : ℂ ↦ Complex.arg (1 - w))
      (Complex.imCLM.comp
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(1 - z)⁻¹)).restrictScalars ℝ)) z := by
  have hlog : HasDerivAt (fun w : ℂ ↦ Complex.log (1 - w)) (-(1 - z)⁻¹) z := by
    have h : HasDerivAt (fun w : ℂ ↦ Complex.log (1 - w)) ((1 - z)⁻¹ * -1) z :=
      (Complex.hasDerivAt_log hs).comp z ((hasDerivAt_id z).const_sub 1)
    exact h.congr_deriv (by ring)
  have e : (fun w : ℂ ↦ Complex.arg (1 - w)) = fun w ↦ (Complex.log (1 - w)).im :=
    funext fun w ↦ (Complex.log_im _).symm
  rw [e]
  exact Complex.imCLM.hasFDerivAt.comp z (hlog.hasFDerivAt.restrictScalars ℝ)

/-- `dD = η(z, 1 - z)` on the punctured open unit disc. -/
theorem geo_hasFDerivAt_blochWigner_of_norm_lt_one {z : ℂ} (hz0 : z ≠ 0) (hz1 : ‖z‖ < 1) :
    HasFDerivAt blochWigner (geoBWDeriv z) z := by
  have hslit : 1 - z ∈ Complex.slitPlane := by
    left
    rw [Complex.sub_re, Complex.one_re]
    linarith [Complex.re_le_norm z]
  have h1 : HasFDerivAt (fun w ↦ (dilogSeries w).im)
      (Complex.imCLM.comp ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        (-Complex.log (1 - z) / z)).restrictScalars ℝ)) z :=
    Complex.imCLM.hasFDerivAt.comp z
      ((geo_hasDerivAt_dilogSeries hz0 hz1).hasFDerivAt.restrictScalars ℝ)
  have hF := h1.add ((hasFDerivAt_arg_one_sub hslit).mul (hasFDerivAt_log_norm hz0))
  have heq : blochWigner =ᶠ[𝓝 z]
      fun w ↦ (dilogSeries w).im + Complex.arg (1 - w) * Real.log ‖w‖ := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz1)] with w hw
    rw [mem_ball_zero_iff] at hw
    exact ite_eq_left hw.le
  refine (hF.congr_fderiv ?_).congr_of_eventuallyEq heq
  refine ContinuousLinearMap.ext fun h ↦ ?_
  rw [geoBWDeriv_apply]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, Complex.reCLM_apply,
    Complex.imCLM_apply, smul_eq_mul]
  rw [show h * (-Complex.log (1 - z) / z) = -(Complex.log (1 - z) * (h / z)) by ring,
    show h * -(1 - z)⁻¹ = -h / (1 - z) by ring, show h * z⁻¹ = h / z by ring, Complex.neg_im,
    Complex.mul_im, Complex.log_re, Complex.log_im]
  ring

end AJConjecture
