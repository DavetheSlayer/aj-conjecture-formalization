import Mathlib
import AJPaper.Zheng.PpZTauDefs

/-!
# The integral over the shifted contour is `O(A^{-1/2})` (Unit PpZ, node `PpZ_ShiftBound`)

Source: Zheng, (5.8): `∫_C e^{-pq z²/h} (z + z₀)^{2k} τ(z + z₀) dz = O(N^{-1/2})` uniformly on
`|n - N| < N/(2pq)`, "since `z^{2k} τ(z)` is bounded on the region (5.9)".

`ppZ_shifted_integral_bound`: for `k ≤ 1` there is `K` (depending on `a`, `k`) such that for all
`A ≥ 1` and all `ρ` with `a|ρ - π| ≤ 5π/16`:

  `‖∫_ℝ e^{-Ax²} (x + ρω)^{2k} τ(ωx + iρ) dx‖ ≤ K/√A`.

Route. `‖τ(ωx + iρ)‖ ≤ 6 e^{√2|x|}` (`ppZ_tau_shift_bound`), `|ρ| ≤ 2π`, `|x + ρω| ≤ |x| + 2π`,
so the integrand is bounded by `6 (|x| + 2π)^{2k} e^{-Ax² + √2|x|}`
(`MeasureTheory.norm_integral_le_of_norm_le`). With `-Ax² + √2|x| ≤ -Ax²/2 + 1/A ≤ -Ax²/2 + 1`:
`∫ e^{-Ax²/2} dx = √(2π/A)` (`integral_gaussian`) and
`∫ x² e^{-Ax²/2} dx = √(2π) A^{-3/2} ≤ √(2π/A)` for `A ≥ 1` (`integral_rpow_mul_exp_neg_mul_sq`
or `integral_gaussian` after integration by parts); `(|x| + 2π)² ≤ 2x² + 8π²`. Unlike Zheng's
argument this does not use boundedness of `z² τ(z)` (false for `a ≤ 2`), only its exponential
growth, so it covers every `a ≥ 1`.
-/

noncomputable section

namespace AJConjecture

/-- The Gaussian absorbs the exponential growth of `τ` and the polynomial factor. -/
private theorem gauss_bound_ppZShiftBound {A : ℝ} (hA : 1 ≤ A) (x : ℝ) :
    Real.exp (-A * x ^ 2) * (2 * x ^ 2 + 8 * Real.pi ^ 2) * (6 * Real.exp (Real.sqrt 2 * |x|)) ≤
      6 * Real.exp 1 * (8 + 8 * Real.pi ^ 2) * Real.exp (-(A / 4) * x ^ 2) := by
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hAx : 0 ≤ (A - 1) * x ^ 2 := mul_nonneg (by linarith) (sq_nonneg x)
  have h1 : Real.exp (-A * x ^ 2) * Real.exp (Real.sqrt 2 * |x|) ≤
      Real.exp 1 * Real.exp (-(A / 2) * x ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [sq_nonneg (|x| - Real.sqrt 2)]
  have hE := Real.exp_pos (-(A / 4) * x ^ 2)
  have h2 : x ^ 2 * Real.exp (-(A / 4) * x ^ 2) ≤ 4 := by
    have h3 := Real.add_one_le_exp (A / 4 * x ^ 2)
    have h4 : Real.exp (-(A / 4) * x ^ 2) * Real.exp (A / 4 * x ^ 2) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    have h5 : 0 ≤ (4 * Real.exp (A / 4 * x ^ 2) - 4 - x ^ 2) * Real.exp (-(A / 4) * x ^ 2) :=
      mul_nonneg (by linarith) hE.le
    nlinarith
  have h6 : Real.exp (-(A / 2) * x ^ 2) =
      Real.exp (-(A / 4) * x ^ 2) * Real.exp (-(A / 4) * x ^ 2) := by
    rw [← Real.exp_add]
    ring_nf
  have h7 : Real.exp (-(A / 4) * x ^ 2) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
  have h8 : (2 * x ^ 2 + 8 * Real.pi ^ 2) * Real.exp (-(A / 2) * x ^ 2) ≤
      (8 + 8 * Real.pi ^ 2) * Real.exp (-(A / 4) * x ^ 2) := by
    rw [h6]
    nlinarith [mul_le_mul_of_nonneg_right h2 hE.le, mul_le_mul_of_nonneg_right h7 hE.le,
      sq_nonneg Real.pi, mul_nonneg (sq_nonneg Real.pi) hE.le,
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h7 hE.le) (sq_nonneg Real.pi)]
  calc Real.exp (-A * x ^ 2) * (2 * x ^ 2 + 8 * Real.pi ^ 2) *
        (6 * Real.exp (Real.sqrt 2 * |x|))
      = 6 * (Real.exp (-A * x ^ 2) * Real.exp (Real.sqrt 2 * |x|)) *
          (2 * x ^ 2 + 8 * Real.pi ^ 2) := by ring
    _ ≤ 6 * (Real.exp 1 * Real.exp (-(A / 2) * x ^ 2)) * (2 * x ^ 2 + 8 * Real.pi ^ 2) := by
        gcongr
    _ = 6 * Real.exp 1 * ((2 * x ^ 2 + 8 * Real.pi ^ 2) * Real.exp (-(A / 2) * x ^ 2)) := by
        ring
    _ ≤ 6 * Real.exp 1 * ((8 + 8 * Real.pi ^ 2) * Real.exp (-(A / 4) * x ^ 2)) := by gcongr
    _ = _ := by ring

/-- Pointwise bound of the integrand on the shifted contour by a Gaussian. -/
private theorem norm_integrand_le_ppZShiftBound (a k : ℕ) (ha : 1 ≤ a) (hk : k ≤ 1) {A ρ : ℝ}
    (hA : 1 ≤ A) (hρ : a * |ρ - Real.pi| ≤ 5 * Real.pi / 16) (x : ℝ) :
    ‖Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2) * ((x : ℂ) + ρ * ppZOmega) ^ (2 * k) *
        ppZTau a (ppZOmega * x + ρ * Complex.I)‖ ≤
      6 * Real.exp 1 * (8 + 8 * Real.pi ^ 2) * Real.exp (-(A / 4) * x ^ 2) := by
  have hpi := Real.pi_gt_three
  have hω : ‖ppZOmega‖ = 1 := by
    rw [ppZOmega, Complex.norm_exp]
    simp
  have he : ‖Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2)‖ = Real.exp (-A * x ^ 2) := by
    rw [show -(A : ℂ) * (x : ℂ) ^ 2 = ((-A * x ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_ofReal]
  have hρ2 : |ρ| ≤ 2 * Real.pi := by
    have h1 : |ρ - Real.pi| ≤ a * |ρ - Real.pi| :=
      le_mul_of_one_le_left (abs_nonneg _) (by exact_mod_cast ha)
    have h2 : |ρ| ≤ |ρ - Real.pi| + |Real.pi| := by
      simpa using abs_add_le (ρ - Real.pi) Real.pi
    rw [abs_of_pos Real.pi_pos] at h2
    linarith
  have hw : ‖(x : ℂ) + ρ * ppZOmega‖ ≤ |x| + 2 * Real.pi := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hω, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    linarith
  have hp : ‖((x : ℂ) + ρ * ppZOmega) ^ (2 * k)‖ ≤ 2 * x ^ 2 + 8 * Real.pi ^ 2 := by
    rw [norm_pow]
    refine (pow_le_pow_left₀ (norm_nonneg _) hw _).trans ?_
    have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    interval_cases k
    · rw [mul_zero, pow_zero]
      nlinarith [sq_nonneg x]
    · rw [mul_one]
      nlinarith [sq_nonneg (|x| - 2 * Real.pi)]
  have hτ := ppZ_tau_shift_bound a ha hρ x
  rw [norm_mul, norm_mul, he]
  refine le_trans ?_ (gauss_bound_ppZShiftBound hA x)
  gcongr

/-- The shifted-contour integrals are `O(A^{-1/2})`, uniformly in the admissible shifts. -/
theorem ppZ_shifted_integral_bound (a k : ℕ) (ha : 1 ≤ a) (hk : k ≤ 1) :
    ∃ K : ℝ, ∀ A ρ : ℝ, 1 ≤ A → a * |ρ - Real.pi| ≤ 5 * Real.pi / 16 →
      ‖∫ x : ℝ, Complex.exp (-(A : ℂ) * (x : ℂ) ^ 2) * ((x : ℂ) + ρ * ppZOmega) ^ (2 * k) *
          ppZTau a (ppZOmega * x + ρ * Complex.I)‖ ≤ K / Real.sqrt A := by
  refine ⟨6 * Real.exp 1 * (8 + 8 * Real.pi ^ 2) * Real.sqrt (4 * Real.pi),
    fun A ρ hA hρ ↦ ?_⟩
  have hA0 : 0 < A := by linarith
  have hint : MeasureTheory.Integrable fun x : ℝ ↦
      6 * Real.exp 1 * (8 + 8 * Real.pi ^ 2) * Real.exp (-(A / 4) * x ^ 2) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  refine (MeasureTheory.norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall
    fun x ↦ norm_integrand_le_ppZShiftBound a k ha hk hA hρ x)).trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_gaussian,
    show Real.pi / (A / 4) = 4 * Real.pi / A by field_simp,
    Real.sqrt_div (by positivity)]
  ring

end AJConjecture
