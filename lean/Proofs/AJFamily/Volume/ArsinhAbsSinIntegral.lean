import Mathlib
import AJFamily.Volume.ArsinhSinCatalan

/-!
# `∫₀^{2π} 2 arsinh|sin θ| dθ = 8G`

`|sin|` has period `π` and is symmetric about `π/2` on `[0, π]`, so the integral is
`8 ∫₀^{π/2} arsinh(sin θ) dθ`; conclude with `integral_arsinh_sin`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `∫₀^{2π} 2 arsinh|sin θ| dθ = 8G`. -/
theorem integral_two_arsinh_abs_sin :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), 2 * Real.arsinh |Real.sin θ| = 8 * catalanConstant := by
  set g : ℝ → ℝ := fun θ ↦ Real.arsinh |Real.sin θ| with hg
  have hcont : Continuous g := Real.continuous_arsinh.comp (continuous_abs.comp Real.continuous_sin)
  have hper : Function.Periodic g Real.pi := fun θ ↦ by simp [hg, Real.sin_add_pi, abs_neg]
  have hint : ∀ a b : ℝ, IntervalIntegrable g MeasureTheory.volume a b :=
    fun a b ↦ hcont.intervalIntegrable a b
  have h1 : ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ = 2 * ∫ θ in (0 : ℝ)..Real.pi, g θ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 Real.pi)
      (hint Real.pi (2 * Real.pi))]
    have := hper.intervalIntegral_add_eq Real.pi 0
    rw [zero_add, show Real.pi + Real.pi = 2 * Real.pi by ring] at this
    rw [this]
    ring
  have h2 : ∫ θ in (0 : ℝ)..Real.pi, g θ = ∫ θ in (0 : ℝ)..Real.pi, Real.arsinh (Real.sin θ) := by
    refine intervalIntegral.integral_congr fun θ hθ ↦ ?_
    rw [Set.uIcc_of_le Real.pi_pos.le] at hθ
    simp only [hg, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)]
  have hc2 : Continuous fun θ ↦ Real.arsinh (Real.sin θ) :=
    Real.continuous_arsinh.comp Real.continuous_sin
  have h3 : ∫ θ in (0 : ℝ)..Real.pi, Real.arsinh (Real.sin θ) =
      2 * ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.arsinh (Real.sin θ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hc2.intervalIntegrable 0 (Real.pi / 2))
      (hc2.intervalIntegrable (Real.pi / 2) Real.pi)]
    have : ∫ θ in (Real.pi / 2)..Real.pi, Real.arsinh (Real.sin θ) =
        ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.arsinh (Real.sin θ) := by
      have h := intervalIntegral.integral_comp_sub_left (fun θ ↦ Real.arsinh (Real.sin θ))
        (a := 0) (b := Real.pi / 2) Real.pi
      simp only [Real.sin_pi_sub, sub_zero, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at h
      exact h.symm
    rw [this]
    ring
  rw [intervalIntegral.integral_const_mul, h1, h2, h3, integral_arsinh_sin]
  ring

end AJConjecture
