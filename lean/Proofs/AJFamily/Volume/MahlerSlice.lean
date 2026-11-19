import Mathlib
import AJFamily.VolumeDefs

/-!
# The Mahler measure of one slice of `E` (Jensen)

For `M = e^{iθ}`, `E(M, L) = L² - bL + M⁴` with `b = M⁴ - 4M² + 1 = -2M²(2 - cos 2θ)`; its
roots are `L = -M² e^{±h}` with `cosh h = 2 - cos 2θ = 1 + 2 sin²θ`, i.e. `h = 2 arsinh|sin θ|`.
By Jensen's formula (`Polynomial.logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots`) the
one-variable logarithmic Mahler measure of `E(M, ·)` is `log⁺ e^h + log⁺ e^{-h} = h`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The slice `E(M, ·)` of the extra factor as a quadratic in `L`. -/
private lemma extraFactorℂ_map_eval_slice (M : ℂ) :
    extraFactorℂ.map (Polynomial.evalRingHom M) =
      X ^ 2 - C (M ^ 4 - 4 * M ^ 2 + 1) * X + C (M ^ 4) := by
  simp [extraFactorℂ, extraFactor]

/-- `cosh (2 arsinh |sin θ|) = 1 + 2 sin² θ`. -/
private lemma cosh_two_arsinh_abs_sin (θ : ℝ) :
    Real.cosh (2 * Real.arsinh |Real.sin θ|) = 1 + 2 * Real.sin θ ^ 2 := by
  rw [Real.cosh_two_mul, Real.cosh_sq, Real.sinh_arsinh, sq_abs]
  ring

/-- For `M = e^{iθ}`, `M⁴ - 4M² + 1 = -M² (e^h + e^{-h})` with `h = 2 arsinh |sin θ|`. -/
private lemma extraFactor_slice_coeff_eq (θ : ℝ) :
    Complex.exp (θ * Complex.I) ^ 4 - 4 * Complex.exp (θ * Complex.I) ^ 2 + 1 =
      -(Complex.exp (θ * Complex.I) ^ 2 *
        ((Real.exp (2 * Real.arsinh |Real.sin θ|) : ℂ) +
          (Real.exp (-(2 * Real.arsinh |Real.sin θ|)) : ℂ))) := by
  have hc : (Real.exp (2 * Real.arsinh |Real.sin θ|) : ℂ) +
      (Real.exp (-(2 * Real.arsinh |Real.sin θ|)) : ℂ) = 2 * (1 + 2 * Complex.sin θ ^ 2) := by
    have := cosh_two_arsinh_abs_sin θ
    rw [Real.cosh_eq] at this
    have h2 : ((Real.exp (2 * Real.arsinh |Real.sin θ|) +
        Real.exp (-(2 * Real.arsinh |Real.sin θ|)) : ℝ) : ℂ) =
        ((2 * (1 + 2 * Real.sin θ ^ 2) : ℝ) : ℂ) := by
      congr 1; linarith
    exact_mod_cast h2
  rw [hc, Complex.exp_mul_I]
  have h1 := Complex.sin_sq_add_cos_sq (θ : ℂ)
  linear_combination (norm := skip) (2 * (Complex.cos θ + Complex.sin θ * Complex.I) ^ 2 - 1 -
    (Complex.sin θ ^ 2 + Complex.cos θ ^ 2)) * h1
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_four, hI3]
  ring

/-- The logarithmic Mahler measure of `L ↦ E(e^{iθ}, L)` is `2 arsinh|sin θ|`. -/
theorem logMahlerMeasure_extraFactor_slice (θ : ℝ) :
    (extraFactorℂ.map (Polynomial.evalRingHom (Complex.exp (θ * Complex.I)))).logMahlerMeasure =
      2 * Real.arsinh |Real.sin θ| := by
  set h : ℝ := 2 * Real.arsinh |Real.sin θ| with hh
  set M : ℂ := Complex.exp (θ * Complex.I) with hM
  have hMn : ‖M‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have h0 : 0 ≤ h := by
    have := Real.arsinh_nonneg_iff.mpr (abs_nonneg (Real.sin θ))
    linarith
  have hfac : extraFactorℂ.map (Polynomial.evalRingHom M) =
      (X - C (-(M ^ 2 * (Real.exp h : ℂ)))) * (X - C (-(M ^ 2 * (Real.exp (-h) : ℂ)))) := by
    rw [extraFactorℂ_map_eval_slice, extraFactor_slice_coeff_eq, ← hh, ← hM]
    have he : C (Real.exp h : ℂ) * C (Real.exp (-h) : ℂ) = (1 : ℂ[X]) := by
      rw [← map_mul, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
        Complex.ofReal_one, map_one]
    simp only [map_neg, map_mul, map_add, map_pow]
    linear_combination -(C M) ^ 4 * he
  rw [hfac, logMahlerMeasure_mul_eq_add_logMahlerMeasure
    (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), logMahlerMeasure_X_sub_C,
    logMahlerMeasure_X_sub_C]
  simp only [norm_neg, norm_mul, norm_pow, hMn, one_pow, one_mul, Complex.norm_real,
    Real.norm_eq_abs, Real.abs_exp]
  rw [Real.posLog_eq_log (by rw [Real.abs_exp]; exact Real.one_le_exp h0),
    (Real.posLog_eq_zero_iff _).mpr
      (by rw [Real.abs_exp]; exact Real.exp_le_one_iff.mpr (by linarith)),
    Real.log_exp, add_zero]

end AJConjecture
