import Mathlib
import AJPaper.Zheng.PpZTauDefs

/-!
# Gaussian linearisation of a quadratic phase (Unit PpZ, node `PpZ_GaussLin`)

Source: the Gaussian integral behind Zheng's (5.5) (Kashaev–Tirkkonen): for `A > 0` and `m ∈ ℂ`,
with `ω = e^{πi/4}` (`ω² = i`),

* `ppZ_gauss_lin`: `∫_ℝ e^{-Ax² + mωx} dx = √(π/A) e^{i m²/(4A)}`;
* `ppZ_gauss_lin_sq`: `∫_ℝ x² e^{-Ax² + mωx} dx = √(π/A) e^{i m²/(4A)} (1/(2A) + i m²/(4A²))`;
* `ppZ_gauss_lin_integrable`: both integrands are integrable.

Route. First: `integral_cexp_quadratic` with `b = -A`, `c = mω`, `d = 0`:
`(π/A)^{1/2} e^{(mω)²/(4A)}`, `(mω)² = i m²` (`ppZOmega_sq`); the complex power of the positive
real `π/A` is the real square root (`Complex.ofReal_cpow`, `Real.sqrt_eq_rpow`). Second: with
`g(x) = e^{-Ax² + bx}`, `g'' = (4A²x² - 4Abx + b² - 2A) g`; integrate `g''` and `(x g)'` over `ℝ`
to `0` (`MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable`, decay from
`integrable_cexp_quadratic`-type bounds), which gives `∫ x g = (b/(2A)) ∫ g` and
`∫ x² g = (1/(2A) + b²/(4A²)) ∫ g`; here `b² = i m²`. (Alternatively differentiate the first
formula in `m` under the integral sign.) Both checked numerically to `10⁻¹⁵` (`strip.py`).
-/

noncomputable section

namespace AJConjecture

/-- `|x|^p ≤ p! (e^x + e^{-x})`. -/
private theorem abs_pow_le_ppZGaussLin (p : ℕ) (x : ℝ) :
    |x| ^ p ≤ p.factorial * (Real.exp x + Real.exp (-x)) := by
  have h1 := Real.pow_div_factorial_le_exp (x := |x|) (abs_nonneg x) p
  rw [div_le_iff₀' (by positivity)] at h1
  have h2 : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
      linarith [Real.exp_pos x, Real.exp_pos (-x)]
  exact h1.trans (by gcongr)

set_option linter.unusedVariables false in
/-- `x ↦ x^p e^{-Ax² + bx}` is integrable for `p ≤ 2`. -/
theorem ppZ_gauss_lin_integrable {A : ℝ} (hA : 0 < A) (b : ℂ) (p : ℕ) (hp : p ≤ 2) :
    MeasureTheory.Integrable fun x : ℝ ↦
      (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x) := by
  have hre : (-(A : ℂ)).re < 0 := by simpa using hA
  have h1 := integrable_cexp_quadratic' hre (b + 1) 0
  have h2 := integrable_cexp_quadratic' hre (b - 1) 0
  refine ((h1.norm.add h2.norm).const_mul (p.factorial : ℝ)).mono'
    (Continuous.aestronglyMeasurable (by fun_prop)) (Filter.Eventually.of_forall fun x ↦ ?_)
  have e1 : Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + (b + 1) * x + 0) =
      Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x) * Complex.exp (x : ℂ) := by
    rw [← Complex.exp_add]
    ring_nf
  have e2 : Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + (b - 1) * x + 0) =
      Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x) * Complex.exp ((-x : ℝ) : ℂ) := by
    rw [← Complex.exp_add]
    push_cast
    ring_nf
  rw [Pi.add_apply, e1, e2, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_exp_ofReal, Complex.norm_exp_ofReal]
  calc |x| ^ p * ‖Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x)‖
      ≤ p.factorial * (Real.exp x + Real.exp (-x)) *
          ‖Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x)‖ := by
        gcongr
        exact abs_pow_le_ppZGaussLin p x
    _ = _ := by ring

/-- `∫_ℝ e^{-Ax² + mωx} dx = √(π/A) e^{i m²/(4A)}`. -/
theorem ppZ_gauss_lin {A : ℝ} (hA : 0 < A) (m : ℂ) :
    ∫ x : ℝ, Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + m * ppZOmega * x) =
      (Real.sqrt (Real.pi / A) : ℂ) * Complex.exp (Complex.I * m ^ 2 / (4 * A)) := by
  have hre : (-(A : ℂ)).re < 0 := by simpa using hA
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have h := integral_cexp_quadratic hre (m * ppZOmega) 0
  simp only [add_zero] at h
  rw [h]
  congr 1
  · rw [neg_neg, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  · congr 1
    field_simp
    linear_combination (m ^ 2) * ppZOmega_sq

/-- The first two moments of `e^{-Ax² + bx}` by integration by parts. -/
private theorem gauss_second_moment_ppZGaussLin {A : ℝ} (hA : 0 < A) (b : ℂ) :
    ∫ x : ℝ, (x : ℂ) ^ 2 * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x) =
      (1 / (2 * A) + b ^ 2 / (4 * (A : ℂ) ^ 2)) *
        ∫ x : ℝ, Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x) := by
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hi0 : MeasureTheory.Integrable fun x : ℝ ↦
      Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x) := by
    simpa using ppZ_gauss_lin_integrable hA b 0 (by norm_num)
  have hi1 : MeasureTheory.Integrable fun x : ℝ ↦
      (x : ℂ) * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x) := by
    simpa using ppZ_gauss_lin_integrable hA b 1 (by norm_num)
  have hi2 := ppZ_gauss_lin_integrable hA b 2 le_rfl
  have hd0 : ∀ x : ℝ, HasDerivAt (fun x : ℝ ↦ Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x))
      (-(2 * A : ℂ) * ((x : ℂ) * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x)) +
        b * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x)) x := fun x ↦ by
    have h1 : HasDerivAt (fun z : ℂ ↦ -(A : ℂ) * z ^ 2 + b * z)
        (-(A : ℂ) * (2 * (x : ℂ)) + b) (x : ℂ) := by
      refine HasDerivAt.congr_deriv (((hasDerivAt_pow 2 (x : ℂ)).const_mul (-(A : ℂ))).add
        ((hasDerivAt_id (x : ℂ)).const_mul b)) ?_
      simp
    have h2 := h1.cexp.comp_ofReal
    convert h2 using 1
    ring
  have hd1 : ∀ x : ℝ,
      HasDerivAt (fun x : ℝ ↦ (x : ℂ) * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x))
      (Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x) +
        (-(2 * A : ℂ) * ((x : ℂ) ^ 2 * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x)) +
          b * ((x : ℂ) * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x)))) x := fun x ↦ by
    have h1 : HasDerivAt (fun x : ℝ ↦ (x : ℂ)) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    convert h1.mul (hd0 x) using 1
    ring
  have z0 := MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable hd0
    ((hi1.const_mul _).add (hi0.const_mul _)) hi0
  have z1 := MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable hd1
    (hi0.add ((hi2.const_mul _).add (hi1.const_mul _))) hi1
  rw [MeasureTheory.integral_add (hi1.const_mul _) (hi0.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at z0
  have hi3 : MeasureTheory.Integrable fun x : ℝ ↦
      -(2 * A : ℂ) * ((x : ℂ) ^ 2 * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x)) +
        b * ((x : ℂ) * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x)) :=
    (hi2.const_mul _).add (hi1.const_mul _)
  rw [MeasureTheory.integral_add hi0 hi3,
    MeasureTheory.integral_add (hi2.const_mul _) (hi1.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at z1
  generalize (∫ x : ℝ, Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x)) = J₀ at z0 z1 ⊢
  generalize (∫ x : ℝ, (x : ℂ) * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x)) = J₁ at z0 z1
  generalize (∫ x : ℝ, (x : ℂ) ^ 2 * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * x)) = J₂ at z1 ⊢
  field_simp
  linear_combination (-4 * (A : ℂ)) * z1 - 2 * b * z0

/-- `∫_ℝ x² e^{-Ax² + mωx} dx = √(π/A) e^{i m²/(4A)} (1/(2A) + i m²/(4A²))`. -/
theorem ppZ_gauss_lin_sq {A : ℝ} (hA : 0 < A) (m : ℂ) :
    ∫ x : ℝ, (x : ℂ) ^ 2 * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + m * ppZOmega * x) =
      (Real.sqrt (Real.pi / A) : ℂ) * Complex.exp (Complex.I * m ^ 2 / (4 * A)) *
        (1 / (2 * A) + Complex.I * m ^ 2 / (4 * (A : ℂ) ^ 2)) := by
  rw [gauss_second_moment_ppZGaussLin hA (m * ppZOmega), ppZ_gauss_lin hA m, mul_pow,
    ppZOmega_sq]
  ring

end AJConjecture
