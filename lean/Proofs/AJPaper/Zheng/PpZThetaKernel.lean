import Mathlib
import AJPaper.Zheng.PpZThetaIntegral
import AJPaper.Zheng.PpZKernelPole

/-!
# The theta sums as kernel integrals (Unit PpZ, node `PpZ_ThetaKernel`)

Source: Zheng, (5.5) in the form `∫_C e^{pq(nz - z²/h)} z^{2k} τ(z) dz`, after completing the
square. `A = aN/π`, `c = 2n + 1`, `x₀ = (πc/N)ω`.

* `ppZ_theta_eq_kernel`: `Θ = (√(aN)/π) e^{iπac²/N} ∫_ℝ ppZKernel a 0 A x₀ x dx`;
* `ppZ_thetaTwo_eq_kernel`:
  `i Θ₂ = 4A² (√(aN)/π) e^{iπac²/N} ∫_ℝ ppZKernel a 1 A x₀ x dx - 2A Θ`.

Route. `τ(ωx)` is odd in `x` and `x^{2k} e^{-Ax²}` is even, so in `ppZ_theta_eq_integral` and
`ppZ_thetaTwo_eq_integral` the function `sinh(2acωx) = (e^{2acωx} - e^{-2acωx})/2` may be
replaced by `e^{2acωx}` (substitute `x ↦ -x` in the second half:
`MeasureTheory.integral_comp_neg`; integrability of each half: `|τ(ωx)| ≤ cosh(√2 x)` because
`|cosh(aωx)| ≥ 1`, against the Gaussian). Then `-Ax² + 2acωx = -A(x - x₀)² + A x₀²` with
`x₀ = acω/A = (πc/N)ω` and `A x₀² = iπac²/N` (`ppZOmega_sq`).
-/

noncomputable section

namespace AJConjecture

/-- `|cosh(aωx)| ≥ 1` for real `x`. -/
private theorem one_le_norm_cosh_ppZThetaKernel (a : ℕ) (x : ℝ) :
    1 ≤ ‖Complex.cosh (a * (ppZOmega * x))‖ := by
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by simp
  have h1 : (a * (ppZOmega * x) : ℂ) = ((a * x / Real.sqrt 2 : ℝ) : ℂ) +
      ((a * x / Real.sqrt 2 : ℝ) : ℂ) * Complex.I := by
    rw [ppZOmega_eq]
    push_cast
    field_simp
  have h2 := ppZ_normSq_cosh (a * x / Real.sqrt 2) (a * x / Real.sqrt 2)
  rw [← h1, Complex.normSq_eq_norm_sq] at h2
  generalize a * x / Real.sqrt 2 = u at h2
  have h3 : Real.sin u ^ 2 ≤ Real.sinh u ^ 2 := by
    refine Real.sin_sq_le_sq.trans (sq_le_sq.mpr ?_)
    rw [Real.abs_sinh]
    exact Real.self_le_sinh_iff.mpr (abs_nonneg u)
  have h4 := Real.sin_sq_add_cos_sq u
  nlinarith [norm_nonneg (Complex.cosh (a * (ppZOmega * x)))]

/-- `τ(ω(-x)) = -τ(ωx)`. -/
private theorem tau_neg_ppZThetaKernel (a : ℕ) (x : ℂ) :
    ppZTau a (ppZOmega * -x) = -ppZTau a (ppZOmega * x) := by
  rw [ppZTau, ppZTau, mul_neg, mul_neg, mul_neg, Complex.sinh_neg, Complex.cosh_neg, neg_div]

/-- `x ↦ x^p e^{-Ax² + bωx} τ(ωx)` is integrable for `p ≤ 2`. -/
private theorem integrable_exp_tau_ppZThetaKernel (a : ℕ) {A : ℝ} (hA : 0 < A) (b : ℂ) (p : ℕ)
    (hp : p ≤ 2) :
    MeasureTheory.Integrable fun x : ℝ ↦
      (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * ppZOmega * x) *
        ppZTau a (ppZOmega * x) := by
  have hne : ∀ x : ℝ, Complex.cosh (a * (ppZOmega * x)) ≠ 0 := fun x h ↦ by
    have := one_le_norm_cosh_ppZThetaKernel a x
    rw [h, norm_zero] at this
    linarith
  have hF : MeasureTheory.Integrable fun x : ℝ ↦
      (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * ppZOmega * x) *
        Complex.sinh (2 * (ppZOmega * x)) := by
    have h := ((ppZ_gauss_lin_integrable hA (b * ppZOmega + 2 * ppZOmega) p hp).sub
      (ppZ_gauss_lin_integrable hA (b * ppZOmega - 2 * ppZOmega) p hp)).div_const 2
    refine h.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    have e1 : -(A : ℂ) * (x : ℂ) ^ 2 + (b * ppZOmega + 2 * ppZOmega) * x =
        -(A : ℂ) * (x : ℂ) ^ 2 + b * ppZOmega * x + 2 * (ppZOmega * x) := by ring
    have e2 : -(A : ℂ) * (x : ℂ) ^ 2 + (b * ppZOmega - 2 * ppZOmega) * x =
        -(A : ℂ) * (x : ℂ) ^ 2 + b * ppZOmega * x + -(2 * (ppZOmega * x)) := by ring
    simp only [Pi.sub_apply]
    rw [e1, e2, Complex.sinh]
    simp only [Complex.exp_add]
    ring
  have hc : Continuous fun x : ℝ ↦
      (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * ppZOmega * x) *
        ppZTau a (ppZOmega * x) :=
    ((Complex.continuous_ofReal.pow p).mul (Complex.continuous_exp.comp (by fun_prop))).mul
      ((Complex.continuous_sinh.comp (by fun_prop)).div
        (Complex.continuous_cosh.comp (by fun_prop)) hne)
  refine hF.mono hc.aestronglyMeasurable (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [ppZTau, ← mul_div_assoc, norm_div]
  exact div_le_self (norm_nonneg _) (one_le_norm_cosh_ppZThetaKernel a x)

/-- Since `x^p e^{-Ax²} τ(ωx)` is odd for even `p`, `sinh(bωx)` may be replaced by `e^{bωx}`. -/
private theorem integral_sinh_eq_exp_ppZThetaKernel (a : ℕ) {A : ℝ} (hA : 0 < A) (b : ℂ) (p : ℕ)
    (hp : p ≤ 2) (hpe : Even p) :
    ∫ x : ℝ, (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2) *
        Complex.sinh (b * (ppZOmega * x)) * ppZTau a (ppZOmega * x) =
      ∫ x : ℝ, (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * ppZOmega * x) *
        ppZTau a (ppZOmega * x) := by
  have h1 := integrable_exp_tau_ppZThetaKernel a hA b p hp
  have h2 := integrable_exp_tau_ppZThetaKernel a hA (-b) p hp
  have hneg : ∫ x : ℝ, (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + -b * ppZOmega * x) *
      ppZTau a (ppZOmega * x) =
      -∫ x : ℝ, (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * ppZOmega * x) *
        ppZTau a (ppZOmega * x) := by
    rw [← MeasureTheory.integral_neg_eq_self (fun x : ℝ ↦
      (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * ppZOmega * x) *
        ppZTau a (ppZOmega * x)) MeasureTheory.volume, ← MeasureTheory.integral_neg]
    congr 1
    ext x
    have e : -(A : ℂ) * (x : ℂ) ^ 2 + -b * ppZOmega * x =
        -(A : ℂ) * (-(x : ℂ)) ^ 2 + b * ppZOmega * (-(x : ℂ)) := by ring
    rw [Complex.ofReal_neg, tau_neg_ppZThetaKernel, hpe.neg_pow, e]
    ring
  have hsplit : ∀ x : ℝ, (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2) *
      Complex.sinh (b * (ppZOmega * x)) * ppZTau a (ppZOmega * x) =
      ((x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + b * ppZOmega * x) *
          ppZTau a (ppZOmega * x) -
        (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + -b * ppZOmega * x) *
          ppZTau a (ppZOmega * x)) / 2 := fun x ↦ by
    have e1 : b * ppZOmega * x = b * (ppZOmega * x) := by ring
    have e2 : -b * ppZOmega * x = -(b * (ppZOmega * x)) := by ring
    rw [Complex.sinh, Complex.exp_add, Complex.exp_add, e1, e2]
    ring
  simp only [hsplit]
  rw [MeasureTheory.integral_div, MeasureTheory.integral_sub h1 h2, hneg]
  ring

/-- Completing the square: `e^{iπac²/N} F_k(x) = x^{2k} e^{-Ax² + 2acωx} τ(ωx)`. -/
private theorem exp_mul_kernel_ppZThetaKernel (a k N n : ℕ) (ha : 1 ≤ a) (hN : 1 ≤ N) (x : ℝ) :
    Complex.exp (Real.pi * Complex.I * a * (2 * n + 1) ^ 2 / N) *
        ppZKernel a k (a * N / Real.pi)
          (((Real.pi * (2 * n + 1) / N : ℝ) : ℂ) * ppZOmega) x =
      (x : ℂ) ^ (2 * k) * Complex.exp (-((a * N / Real.pi : ℝ) : ℂ) * (x : ℂ) ^ 2 +
        2 * a * (2 * n + 1) * ppZOmega * x) * ppZTau a (ppZOmega * x) := by
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have he : Complex.exp (Real.pi * Complex.I * a * (2 * n + 1) ^ 2 / N) *
      Complex.exp (-((a * N / Real.pi : ℝ) : ℂ) *
        ((x : ℂ) - ((Real.pi * (2 * n + 1) / N : ℝ) : ℂ) * ppZOmega) ^ 2) =
      Complex.exp (-((a * N / Real.pi : ℝ) : ℂ) * (x : ℂ) ^ 2 +
        2 * a * (2 * n + 1) * ppZOmega * x) := by
    rw [← Complex.exp_add, ← ppZOmega_sq]
    congr 1
    push_cast
    field_simp
    ring
  rw [ppZKernel, ← he]
  ring

/-- `Θ = (√(aN)/π) e^{iπac²/N} ∫ ppZKernel a 0 A x₀`, `A = aN/π`, `c = 2n+1`, `x₀ = (πc/N)ω`. -/
theorem ppZ_theta_eq_kernel (a N n : ℕ) (ha : 1 ≤ a) (hN : 1 ≤ N) :
    ppZTheta a N n =
      ((Real.sqrt (a * N) / Real.pi : ℝ) : ℂ) *
        Complex.exp (Real.pi * Complex.I * a * (2 * n + 1) ^ 2 / N) *
        ∫ x : ℝ, ppZKernel a 0 (a * N / Real.pi)
          (((Real.pi * (2 * n + 1) / N : ℝ) : ℂ) * ppZOmega) x := by
  have hA : (0 : ℝ) < a * N / Real.pi := by
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have h := integral_sinh_eq_exp_ppZThetaKernel a hA (2 * a * (2 * n + 1)) 0 (by norm_num)
    (by decide)
  simp only [pow_zero, one_mul] at h
  rw [ppZ_theta_eq_integral a N n ha hN, h, mul_assoc _ (Complex.exp _)]
  congr 1
  rw [← MeasureTheory.integral_const_mul]
  simp only [exp_mul_kernel_ppZThetaKernel a 0 N n ha hN, mul_zero, pow_zero, one_mul]

/-- `i Θ₂ = 4A² (√(aN)/π) e^{iπac²/N} ∫ ppZKernel a 1 A x₀ - 2A Θ`. -/
theorem ppZ_thetaTwo_eq_kernel (a N n : ℕ) (ha : 1 ≤ a) (hN : 1 ≤ N) :
    Complex.I * ppZThetaTwo a N n =
      4 * ((a * N / Real.pi : ℝ) : ℂ) ^ 2 * ((Real.sqrt (a * N) / Real.pi : ℝ) : ℂ) *
          Complex.exp (Real.pi * Complex.I * a * (2 * n + 1) ^ 2 / N) *
          (∫ x : ℝ, ppZKernel a 1 (a * N / Real.pi)
            (((Real.pi * (2 * n + 1) / N : ℝ) : ℂ) * ppZOmega) x) -
        2 * ((a * N / Real.pi : ℝ) : ℂ) * ppZTheta a N n := by
  have hA : (0 : ℝ) < a * N / Real.pi := by
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have h := integral_sinh_eq_exp_ppZThetaKernel a hA (2 * a * (2 * n + 1)) 2 le_rfl
    (by decide)
  rw [ppZ_thetaTwo_eq_integral a N n ha hN, h, mul_assoc _ (Complex.exp _)]
  congr 2
  rw [← MeasureTheory.integral_const_mul]
  simp only [exp_mul_kernel_ppZThetaKernel a 1 N n ha hN, mul_one]

end AJConjecture
