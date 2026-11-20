import Mathlib

/-!
# The kernel `τ(z) = sinh 2z / cosh az` of the torus knot `T(a, 2)`
(Unit PpZ, node `PpZ_TauDefs`)

Source: Zheng, (5.6): `τ(z) = (e^{pz} - e^{-pz})(e^{qz} - e^{-qz})/(e^{pqz} - e^{-pqz})`; for
`(p, q) = (a, 2)` this is `sinh 2z / cosh az`. The contour is `C = e^{πi/4} ℝ`; we write
`ω = e^{πi/4}` (`ppZOmega`) and integrate over `x ∈ ℝ`, `z = ωx`.

* `ppZOmega_sq`, `ppZOmega_eq`: `ω² = i`, `ω = (1 + i)/√2`.
* `ppZ_normSq_cosh`: `|cosh(u + iv)|² = sinh² u + cos² v`.
* `ppZ_cosh_omega_eq_zero_iff`: `cosh(aωw) = 0 ↔ w = ω(2j+1)π/(2a)` for some `j ∈ ℤ`
  (`Complex.cosh z = Complex.cos (z * I)`, `Complex.cos_eq_zero_iff`, `1/ω = ω̄`, `ω̄ i = ω`).
* `ppZ_tau_shift_bound`: on the shifted lines `z = ωx + iρ` with `a|ρ - π| ≤ 5π/16`,
  `‖τ(z)‖ ≤ 6 e^{√2|x|}`. Indeed `‖sinh 2z‖ ≤ cosh(2 Re z) ≤ e^{√2|x|}` (`Re z = x/√2`), and with
  `u = ax/√2`, `aρ = aπ + φ`, `|φ| ≤ 5π/16`: `|cosh az|² = sinh² u + cos²(u + φ)` (shift by `aπ`
  only changes a sign); if `|u| ≤ π/8` then `|u + φ| ≤ 7π/16` and `cos² ≥ cos²(7π/16) > 1/36`;
  otherwise `sinh² u ≥ sinh²(π/8) > 1/36`. (This is the place where Zheng's colour window
  `|n - N| < N/(2pq)` enters: the line stays away from the poles of `τ`.)
  Numerically `sup ‖τ‖ e^{-√2|x|} = 1.83` (`scaf.py`).
-/

noncomputable section

namespace AJConjecture

/-- `ω = e^{πi/4}`, the direction of Zheng's contour `C`. -/
def ppZOmega : ℂ := Complex.exp (Real.pi * Complex.I / 4)

/-- `τ(z) = sinh 2z / cosh az`: Zheng's (5.6) for `(p, q) = (a, 2)`. -/
def ppZTau (a : ℕ) (z : ℂ) : ℂ := Complex.sinh (2 * z) / Complex.cosh (a * z)

/-- `ω² = i`. -/
theorem ppZOmega_sq : ppZOmega ^ 2 = Complex.I := by
  have h : ((2 : ℕ) : ℂ) * (Real.pi * Complex.I / 4) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [ppZOmega, ← Complex.exp_nat_mul, h, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- `ω = (1 + i)/√2`. -/
theorem ppZOmega_eq : ppZOmega = (1 + Complex.I) / (Real.sqrt 2 : ℂ) := by
  have h : (Real.pi * Complex.I / 4 : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by simp
  have h3 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    simp
  rw [ppZOmega, h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast
  field_simp
  linear_combination (1 + Complex.I) * h3

/-- `|cosh(u + iv)|² = sinh² u + cos² v`. -/
theorem ppZ_normSq_cosh (u v : ℝ) :
    Complex.normSq (Complex.cosh (u + v * Complex.I)) = Real.sinh u ^ 2 + Real.cos v ^ 2 := by
  have h : Complex.cosh (u + v * Complex.I) = ((Real.cosh u * Real.cos v : ℝ) : ℂ) +
      ((Real.sinh u * Real.sin v : ℝ) : ℂ) * Complex.I := by
    rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
    push_cast
    ring
  rw [h, Complex.normSq_add_mul_I, mul_pow, mul_pow, Real.cosh_sq, Real.sin_sq]
  ring

/-- The zeros of `w ↦ cosh(aωw)` are `w = ω(2j+1)π/(2a)`, `j ∈ ℤ`. -/
theorem ppZ_cosh_omega_eq_zero_iff (a : ℕ) (ha : 1 ≤ a) (w : ℂ) :
    Complex.cosh (a * (ppZOmega * w)) = 0 ↔
      ∃ j : ℤ, w = ppZOmega * ((2 * (j : ℂ) + 1) * Real.pi / (2 * a)) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hω := ppZOmega_sq
  rw [← Complex.cos_mul_I, Complex.cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k - 1, ?_⟩
    push_cast
    field_simp
    linear_combination (-2 * ppZOmega) * hk + (2 * a * w * Complex.I) * hω +
      (2 * a * w) * Complex.I_sq
  · rintro ⟨j, rfl⟩
    refine ⟨-j - 1, ?_⟩
    push_cast
    field_simp
    linear_combination ((2 * (j : ℂ) + 1) * Complex.I) * hω + (2 * (j : ℂ) + 1) * Complex.I_sq

/-- `‖sinh z‖ ≤ cosh (Re z)`. -/
private theorem norm_sinh_le_ppZTauDefs (z : ℂ) : ‖Complex.sinh z‖ ≤ Real.cosh z.re := by
  rw [Complex.sinh, Real.cosh_eq, norm_div]
  have h := norm_sub_le (Complex.exp z) (Complex.exp (-z))
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at h
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  linarith

/-- `cosh t ≤ e^{|t|}`. -/
private theorem cosh_le_exp_abs_ppZTauDefs (t : ℝ) : Real.cosh t ≤ Real.exp |t| := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have h : Real.exp (-|t|) ≤ Real.exp |t| :=
    Real.exp_le_exp.mpr (by linarith [abs_nonneg t])
  linarith

/-- `sinh² u + cos²(u + φ) ≥ 1/36` when `|φ| ≤ 5π/16`. -/
private theorem sinh_sq_add_cos_sq_ge_ppZTauDefs {u φ : ℝ} (hφ : |φ| ≤ 5 * Real.pi / 16) :
    1 / 36 ≤ Real.sinh u ^ 2 + Real.cos (u + φ) ^ 2 := by
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  by_cases hu : |u| ≤ Real.pi / 8
  · have h1 : |u + φ| ≤ 7 * Real.pi / 16 := (abs_add_le u φ).trans (by linarith)
    have h2 : Real.cos (7 * Real.pi / 16) ≤ Real.cos (u + φ) := by
      rw [← Real.cos_abs (u + φ)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) h1
    have h3 : Real.cos (7 * Real.pi / 16) = Real.sin (Real.pi / 16) := by
      rw [← Real.sin_pi_div_two_sub]
      congr 1
      ring
    have h4 : Real.sin (3 / 16) ≤ Real.sin (Real.pi / 16) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
    have h5 := Real.sin_gt_sub_cube (x := 3 / 16) (by norm_num)
    have h6 : (1 : ℝ) / 6 ≤ Real.cos (u + φ) := by
      rw [h3] at h2
      norm_num at h5
      linarith
    nlinarith [sq_nonneg (Real.sinh u)]
  · have h1 : (3 : ℝ) / 8 ≤ |Real.sinh u| := by
      rw [Real.abs_sinh]
      have := Real.self_le_sinh_iff.mpr (abs_nonneg u)
      linarith
    have h2 : Real.sinh u ^ 2 = |Real.sinh u| ^ 2 := (sq_abs _).symm
    nlinarith [sq_nonneg (Real.cos (u + φ))]

set_option linter.unusedVariables false in
/-- `‖τ(ωx + iρ)‖ ≤ 6 e^{√2|x|}` when `a|ρ - π| ≤ 5π/16`. -/
theorem ppZ_tau_shift_bound (a : ℕ) (ha : 1 ≤ a) {ρ : ℝ}
    (hρ : a * |ρ - Real.pi| ≤ 5 * Real.pi / 16) (x : ℝ) :
    ‖ppZTau a (ppZOmega * x + ρ * Complex.I)‖ ≤ 6 * Real.exp (Real.sqrt 2 * |x|) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2' : (Real.sqrt 2 : ℂ) ≠ 0 := by simp
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hz : (ppZOmega * x + ρ * Complex.I : ℂ) =
      ((x / Real.sqrt 2 : ℝ) : ℂ) + ((x / Real.sqrt 2 + ρ : ℝ) : ℂ) * Complex.I := by
    rw [ppZOmega_eq]
    push_cast
    field_simp
    ring
  have hnum : ‖Complex.sinh (2 * (ppZOmega * x + ρ * Complex.I))‖ ≤
      Real.exp (Real.sqrt 2 * |x|) := by
    refine (norm_sinh_le_ppZTauDefs _).trans ((cosh_le_exp_abs_ppZTauDefs _).trans ?_)
    refine Real.exp_le_exp.mpr (le_of_eq ?_)
    have hre : (2 * (ppZOmega * x + ρ * Complex.I)).re = Real.sqrt 2 * x := by
      rw [hz]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im,
        Complex.mul_im]
      field_simp
      linear_combination -x * hss
    rw [hre, abs_mul, abs_of_pos hs2]
  have hden : 1 / 6 ≤ ‖Complex.cosh (a * (ppZOmega * x + ρ * Complex.I))‖ := by
    have h1 : (a * (ppZOmega * x + ρ * Complex.I) : ℂ) = ((a * (x / Real.sqrt 2) : ℝ) : ℂ) +
        ((a * (x / Real.sqrt 2) + a * (ρ - Real.pi) + a * Real.pi : ℝ) : ℂ) * Complex.I := by
      rw [hz]
      push_cast
      ring
    have h2 := sinh_sq_add_cos_sq_ge_ppZTauDefs (u := a * (x / Real.sqrt 2))
      (φ := a * (ρ - Real.pi)) (by rwa [abs_mul, Nat.abs_cast])
    have h3 : Complex.normSq (Complex.cosh (a * (ppZOmega * x + ρ * Complex.I))) =
        Real.sinh (a * (x / Real.sqrt 2)) ^ 2 +
          Real.cos (a * (x / Real.sqrt 2) + a * (ρ - Real.pi)) ^ 2 := by
      rw [h1, ppZ_normSq_cosh, Real.cos_add_nat_mul_pi, mul_pow, ← pow_mul, mul_comm a 2,
        pow_mul, neg_one_sq, one_pow, one_mul]
    rw [Complex.normSq_eq_norm_sq] at h3
    nlinarith [norm_nonneg (Complex.cosh (a * (ppZOmega * x + ρ * Complex.I)))]
  rw [ppZTau, norm_div, div_le_iff₀ (by linarith)]
  nlinarith [Real.exp_pos (Real.sqrt 2 * |x|)]

end AJConjecture
