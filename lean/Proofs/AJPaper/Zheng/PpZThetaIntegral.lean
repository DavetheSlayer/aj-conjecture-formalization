import Mathlib
import AJPaper.Zheng.PpZGaussLin
import AJPaper.Zheng.PpZThetaSum

/-!
# The theta sums as Gaussian integrals of `τ` (Unit PpZ, node `PpZ_ThetaIntegral`)

Source: Zheng, (5.5) (the integral formula of Kashaev–Tirkkonen), for `(p, q) = (a, 2)` and odd
colour `c = 2n + 1`, written before the contour is moved. `A = aN/π`, `√(A/π) = √(aN)/π`.

* `ppZ_theta_eq_integral`:
  `Θ = (√(aN)/π) ∫_ℝ e^{-Ax²} sinh(2a(2n+1)ωx) τ(ωx) dx`;
* `ppZ_thetaTwo_eq_integral`:
  `i Θ₂ = 4A² (√(aN)/π) ∫_ℝ x² e^{-Ax²} sinh(2a(2n+1)ωx) τ(ωx) dx - 2A Θ`.

Route. `G(m) = e^{i m²/(4A)} = √(A/π) ∫ e^{-Ax² + mωx} dx` (`ppZ_gauss_lin`), and
`i m² G(m) = √(A/π) · 4A² ∫ x² e^{-Ax² + mωx} dx - 2A G(m)` (`ppZ_gauss_lin_sq`). Sum over the
`2(2n+1)` values of `m` (finite sums of integrable functions, `ppZ_gauss_lin_integrable`,
`MeasureTheory.integral_finset_sum`). Since `G(m) = G(-m)`, replace `e^{mωx}` by
`cosh(mωx)` (average of the formulas for `m` and `-m`, or the substitution `x ↦ -x`). Then
`∑_{|k|≤n} (cosh((4ak+a+2)z) - cosh((4ak+a-2)z)) = sinh(2z) sinh(2a(2n+1)z)/cosh(az)` at `z = ωx`
(`ppZ_cosh_mul_sum`; `cosh(aωx) ≠ 0` for real `x`: `|cosh(aωx)|² = sinh² u + cos² u ≥ 1`,
`u = ax/√2`, by `ppZ_normSq_cosh`).
Checked numerically through the final formulas (`kt.py`).
-/

noncomputable section

namespace AJConjecture

/-- `cosh(aωx) ≠ 0` for real `x`. -/
private theorem cosh_omega_ne_zero_ppZThetaIntegral (a : ℕ) (x : ℝ) :
    Complex.cosh (a * (ppZOmega * x)) ≠ 0 := by
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by simp
  have h1 : (a * (ppZOmega * x) : ℂ) = ((a * x / Real.sqrt 2 : ℝ) : ℂ) +
      ((a * x / Real.sqrt 2 : ℝ) : ℂ) * Complex.I := by
    rw [ppZOmega_eq]
    push_cast
    field_simp
  intro h
  have h2 := ppZ_normSq_cosh (a * x / Real.sqrt 2) (a * x / Real.sqrt 2)
  rw [← h1, h, map_zero] at h2
  have h3 : Real.sinh (a * x / Real.sqrt 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (Real.sinh (a * x / Real.sqrt 2)),
      sq_nonneg (Real.cos (a * x / Real.sqrt 2))]
  have h4 : a * x / Real.sqrt 2 = 0 := Real.sinh_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
  rw [h4] at h2
  simp at h2

/-- `∑_{|k|≤n} (cosh((4ak+a+2)ωx) - cosh((4ak+a-2)ωx)) = sinh(2a(2n+1)ωx) τ(ωx)`. -/
private theorem cosh_sum_eq_ppZThetaIntegral (a n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
        (Complex.cosh (((4 * a * k + a + 2 : ℤ) : ℂ) * (ppZOmega * x)) -
          Complex.cosh (((4 * a * k + a - 2 : ℤ) : ℂ) * (ppZOmega * x))) =
      Complex.sinh (2 * a * (2 * n + 1) * (ppZOmega * x)) * ppZTau a (ppZOmega * x) := by
  have h := ppZ_cosh_mul_sum a n (ppZOmega * x)
  have h0 := cosh_omega_ne_zero_ppZThetaIntegral a x
  rw [ppZTau, eq_comm, mul_div_assoc', div_eq_iff h0, mul_comm _ (Complex.cosh _), h, mul_comm]

/-- `x^p e^{-Ax²} cosh(mωx)` as the average of two Gaussians with a linear term. -/
private theorem cosh_split_ppZThetaIntegral (A : ℝ) (m : ℂ) (p : ℕ) (x : ℝ) :
    (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2) * Complex.cosh (m * (ppZOmega * x)) =
      ((x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + m * ppZOmega * x) +
        (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + -m * ppZOmega * x)) / 2 := by
  have e1 : m * ppZOmega * x = m * (ppZOmega * x) := by ring
  have e2 : -m * ppZOmega * x = -(m * (ppZOmega * x)) := by ring
  rw [Complex.cosh, Complex.exp_add, Complex.exp_add, e1, e2]
  ring

/-- `x ↦ x^p e^{-Ax²} cosh(mωx)` is integrable for `p ≤ 2`. -/
private theorem integrable_cosh_ppZThetaIntegral {A : ℝ} (hA : 0 < A) (m : ℂ) (p : ℕ)
    (hp : p ≤ 2) :
    MeasureTheory.Integrable fun x : ℝ ↦
      (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2) * Complex.cosh (m * (ppZOmega * x)) := by
  simp only [cosh_split_ppZThetaIntegral]
  exact ((ppZ_gauss_lin_integrable hA (m * ppZOmega) p hp).add
    (ppZ_gauss_lin_integrable hA (-m * ppZOmega) p hp)).div_const 2

/-- `∫ x^p e^{-Ax²} cosh(mωx)` as the average of the integrals for `m` and `-m`. -/
private theorem integral_cosh_ppZThetaIntegral {A : ℝ} (hA : 0 < A) (m : ℂ) (p : ℕ)
    (hp : p ≤ 2) :
    ∫ x : ℝ, (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2) *
        Complex.cosh (m * (ppZOmega * x)) =
      ((∫ x : ℝ, (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + m * ppZOmega * x)) +
        ∫ x : ℝ, (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2 + -m * ppZOmega * x)) / 2 := by
  simp only [cosh_split_ppZThetaIntegral]
  rw [MeasureTheory.integral_div, MeasureTheory.integral_add
    (ppZ_gauss_lin_integrable hA (m * ppZOmega) p hp)
    (ppZ_gauss_lin_integrable hA (-m * ppZOmega) p hp)]

/-- `∫ e^{-Ax²} cosh(mωx) dx = √(π/A) e^{i m²/(4A)}`. -/
private theorem integral_cosh_zero_ppZThetaIntegral {A : ℝ} (hA : 0 < A) (m : ℂ) :
    ∫ x : ℝ, Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2) * Complex.cosh (m * (ppZOmega * x)) =
      (Real.sqrt (Real.pi / A) : ℂ) * Complex.exp (Complex.I * m ^ 2 / (4 * A)) := by
  have h := integral_cosh_ppZThetaIntegral hA m 0 (by norm_num)
  simp only [pow_zero, one_mul] at h
  rw [h, ppZ_gauss_lin hA m, ppZ_gauss_lin hA (-m), neg_sq]
  ring

/-- `∫ x² e^{-Ax²} cosh(mωx) dx = √(π/A) e^{i m²/(4A)} (1/(2A) + i m²/(4A²))`. -/
private theorem integral_cosh_two_ppZThetaIntegral {A : ℝ} (hA : 0 < A) (m : ℂ) :
    ∫ x : ℝ, (x : ℂ) ^ 2 * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2) *
        Complex.cosh (m * (ppZOmega * x)) =
      (Real.sqrt (Real.pi / A) : ℂ) * Complex.exp (Complex.I * m ^ 2 / (4 * A)) *
        (1 / (2 * A) + Complex.I * m ^ 2 / (4 * (A : ℂ) ^ 2)) := by
  rw [integral_cosh_ppZThetaIntegral hA m 2 le_rfl, ppZ_gauss_lin_sq hA m,
    ppZ_gauss_lin_sq hA (-m), neg_sq]
  ring

/-- The integral of `x^p e^{-Ax²} sinh(2a(2n+1)ωx) τ(ωx)` as a finite sum of `cosh`-integrals. -/
private theorem integral_sinh_tau_ppZThetaIntegral (a n : ℕ) {A : ℝ} (hA : 0 < A) (p : ℕ)
    (hp : p ≤ 2) :
    ∫ x : ℝ, (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2) *
        Complex.sinh (2 * a * (2 * n + 1) * (ppZOmega * x)) * ppZTau a (ppZOmega * x) =
      ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
        ((∫ x : ℝ, (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2) *
            Complex.cosh (((4 * a * k + a + 2 : ℤ) : ℂ) * (ppZOmega * x))) -
          ∫ x : ℝ, (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2) *
            Complex.cosh (((4 * a * k + a - 2 : ℤ) : ℂ) * (ppZOmega * x))) := by
  have hi := fun m : ℂ ↦ integrable_cosh_ppZThetaIntegral hA m p hp
  symm
  calc _ = ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
        ∫ x : ℝ, ((x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2) *
            Complex.cosh (((4 * a * k + a + 2 : ℤ) : ℂ) * (ppZOmega * x)) -
          (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2) *
            Complex.cosh (((4 * a * k + a - 2 : ℤ) : ℂ) * (ppZOmega * x))) :=
        Finset.sum_congr rfl fun k _ ↦ (MeasureTheory.integral_sub (hi _) (hi _)).symm
    _ = ∫ x : ℝ, ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
          ((x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2) *
            Complex.cosh (((4 * a * k + a + 2 : ℤ) : ℂ) * (ppZOmega * x)) -
          (x : ℂ) ^ p * Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2) *
            Complex.cosh (((4 * a * k + a - 2 : ℤ) : ℂ) * (ppZOmega * x))) :=
        (MeasureTheory.integral_finsetSum _ fun k _ ↦ (hi _).sub (hi _)).symm
    _ = _ := by
        congr 1
        ext x
        rw [mul_assoc, ← cosh_sum_eq_ppZThetaIntegral, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ ↦ (mul_sub _ _ _).symm

/-- `G(m) = (√(aN)/π) · √(π/A) e^{i m²/(4A)}`, `A = aN/π`. -/
private theorem ppZG_eq_ppZThetaIntegral (a N : ℕ) (ha : 1 ≤ a) (hN : 1 ≤ N) (m : ℤ) :
    ppZG a N m = ((Real.sqrt (a * N) / Real.pi : ℝ) : ℂ) *
      ((Real.sqrt (Real.pi / (a * N / Real.pi)) : ℂ) *
        Complex.exp (Complex.I * (m : ℂ) ^ 2 / (4 * ((a * N / Real.pi : ℝ) : ℂ)))) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha'.ne'
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN'.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs : Real.sqrt (Real.pi / (a * N / Real.pi)) = Real.pi / Real.sqrt (a * N) := by
    rw [show Real.pi / (a * N / Real.pi) = Real.pi ^ 2 / (a * N) by field_simp,
      Real.sqrt_div (sq_nonneg _), Real.sqrt_sq Real.pi_pos.le]
  have hc : Real.sqrt (a * N) / Real.pi * Real.sqrt (Real.pi / (a * N / Real.pi)) = 1 := by
    rw [hs]
    have : Real.sqrt (a * N) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp
  rw [← mul_assoc, ← Complex.ofReal_mul, hc, Complex.ofReal_one, one_mul, ppZG]
  congr 1
  push_cast
  field_simp

/-- `Θ = (√(aN)/π) ∫ e^{-Ax²} sinh(2a(2n+1)ωx) τ(ωx) dx`, `A = aN/π`. -/
theorem ppZ_theta_eq_integral (a N n : ℕ) (ha : 1 ≤ a) (hN : 1 ≤ N) :
    ppZTheta a N n =
      ((Real.sqrt (a * N) / Real.pi : ℝ) : ℂ) *
        ∫ x : ℝ, Complex.exp (-((a * N / Real.pi : ℝ) : ℂ) * (x : ℂ) ^ 2) *
          Complex.sinh (2 * a * (2 * n + 1) * (ppZOmega * x)) * ppZTau a (ppZOmega * x) := by
  have hA : (0 : ℝ) < a * N / Real.pi := by
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have h := integral_sinh_tau_ppZThetaIntegral a n hA 0 (by norm_num)
  simp only [pow_zero, one_mul] at h
  rw [h, ppZTheta, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_cosh_zero_ppZThetaIntegral hA, integral_cosh_zero_ppZThetaIntegral hA,
    ppZG_eq_ppZThetaIntegral a N ha hN, ppZG_eq_ppZThetaIntegral a N ha hN]
  ring

/-- `i Θ₂ = 4A² (√(aN)/π) ∫ x² e^{-Ax²} sinh(2a(2n+1)ωx) τ(ωx) dx - 2A Θ`, `A = aN/π`. -/
theorem ppZ_thetaTwo_eq_integral (a N n : ℕ) (ha : 1 ≤ a) (hN : 1 ≤ N) :
    Complex.I * ppZThetaTwo a N n =
      4 * ((a * N / Real.pi : ℝ) : ℂ) ^ 2 * ((Real.sqrt (a * N) / Real.pi : ℝ) : ℂ) *
          (∫ x : ℝ, (x : ℂ) ^ 2 * Complex.exp (-((a * N / Real.pi : ℝ) : ℂ) * (x : ℂ) ^ 2) *
            Complex.sinh (2 * a * (2 * n + 1) * (ppZOmega * x)) * ppZTau a (ppZOmega * x)) -
        2 * ((a * N / Real.pi : ℝ) : ℂ) * ppZTheta a N n := by
  have hA : (0 : ℝ) < a * N / Real.pi := by
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hA' : ((a * N / Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  rw [integral_sinh_tau_ppZThetaIntegral a n hA 2 le_rfl, ppZTheta, ppZThetaTwo, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_cosh_two_ppZThetaIntegral hA, integral_cosh_two_ppZThetaIntegral hA,
    ppZG_eq_ppZThetaIntegral a N ha hN, ppZG_eq_ppZThetaIntegral a N ha hN]
  field_simp
  ring

end AJConjecture
