import Mathlib
import AJFamily.Volume.ArctanCatalan

/-!
# `∫₀^{π/2} arsinh(sin θ) dθ = G`

`arsinh s = ∫₀¹ s/√(1 + a²s²) da` (derivative of `a ↦ arsinh(as)`); exchange the order of
integration (continuous nonnegative integrand on a rectangle); the inner integral is
`∫₀^{π/2} sin θ/√(1 + a² sin²θ) dθ = arctan(a)/a`, with antiderivative
`θ ↦ -(1/a) arcsin(a cos θ/√(1 + a²))` for `a > 0`; conclude with
`integral_arctan_div_self`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The kernel `(θ, a) ↦ sin θ / √(1 + (a sin θ)²)` is continuous. -/
private lemma continuous_sin_div_sqrt_kernel :
    Continuous fun p : ℝ × ℝ ↦ Real.sin p.1 / √(1 + (p.2 * Real.sin p.1) ^ 2) := by
  refine Continuous.div (by fun_prop) (by fun_prop) fun p ↦ ?_
  positivity

/-- `arsinh s = ∫₀¹ s / √(1 + (a s)²) da`. -/
private lemma arsinh_eq_integral_div_sqrt (s : ℝ) :
    Real.arsinh s = ∫ a in (0 : ℝ)..1, s / √(1 + (a * s) ^ 2) := by
  have hc : Continuous fun a : ℝ ↦ s / √(1 + (a * s) ^ 2) :=
    Continuous.div (by fun_prop) (by fun_prop) fun a ↦ by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun a ↦ Real.arsinh (a * s))
    (fun a _ ↦ ?_) (hc.intervalIntegrable _ _)]
  · simp
  · have h := (Real.hasDerivAt_arsinh (a * s)).comp a ((hasDerivAt_id a).mul_const s)
    exact h.congr_deriv (by rw [div_eq_inv_mul, one_mul])

/-- For `a ≠ 0`, `∫₀^{π/2} sin θ / √(1 + (a sin θ)²) dθ = arctan a / a`. -/
private lemma integral_sin_div_sqrt_eq_arctan_div {a : ℝ} (ha : a ≠ 0) :
    ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ / √(1 + (a * Real.sin θ) ^ 2) =
      Real.arctan a / a := by
  have hc : Continuous fun θ : ℝ ↦ Real.sin θ / √(1 + (a * Real.sin θ) ^ 2) :=
    Continuous.div (by fun_prop) (by fun_prop) fun θ ↦ by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun θ ↦ -(1 / a) * Real.arctan (a * Real.cos θ / √(1 + (a * Real.sin θ) ^ 2)))
    (fun θ _ ↦ ?_) (hc.intervalIntegrable _ _)]
  · simp
    field_simp
  · have hpos : 0 < 1 + (a * Real.sin θ) ^ 2 := by positivity
    have hS : (√(1 + (a * Real.sin θ) ^ 2)) ^ 2 = 1 + (a * Real.sin θ) ^ 2 :=
      Real.sq_sqrt hpos.le
    have hSpos : 0 < √(1 + (a * Real.sin θ) ^ 2) := Real.sqrt_pos.2 hpos
    have hq : HasDerivAt (fun θ ↦ 1 + (a * Real.sin θ) ^ 2)
        (2 * (a * Real.sin θ) * (a * Real.cos θ)) θ := by
      have := (((Real.hasDerivAt_sin θ).const_mul a).pow 2).const_add 1
      convert this using 1
      push_cast
      ring
    have hsq := hq.sqrt hpos.ne'
    have hg := ((Real.hasDerivAt_cos θ).const_mul a).div hsq hSpos.ne'
    have h := (hg.arctan).const_mul (-(1 / a))
    convert h using 1
    simp only [Pi.div_apply, div_pow, hS]
    field_simp
    rw [Real.sq_sqrt (by positivity)]
    ring

open MeasureTheory Set in
/-- `∫₀^{π/2} arsinh(sin θ) dθ` is Catalan's constant. -/
theorem integral_arsinh_sin :
    ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.arsinh (Real.sin θ) = catalanConstant := by
  simp_rw [arsinh_eq_integral_div_sqrt]
  rw [intervalIntegral_intervalIntegral_swap, ← integral_arctan_div_self]
  · refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun a ha ↦ ?_)
    rw [uIoc_of_le zero_le_one] at ha
    exact integral_sin_div_sqrt_eq_arctan_div ha.1.ne'
  · exact (continuous_sin_div_sqrt_kernel.continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

end AJConjecture
