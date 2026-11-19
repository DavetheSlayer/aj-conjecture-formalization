import Mathlib
import AJPaper.Zheng.PpZEq512

/-!
# The weighted theta sum: main term `N^{5/2} A⁺_{a,2}(N, 1)` (Unit PpZ, node `PpZ_ThetaTwoMain`)

Source: Zheng, Lemma 5.1 with `k = 1` and (5.13).

* `ppZ_thetaTwo_shifted`: the exact formula. For `N ≥ 4a`, `|c - N| < N/(4a) + 1` (`c = 2n+1`),
  `A = aN/π`, `ρ = πc/N`:
  `Θ₂ = -2ω (N^{5/2}/√a) A⁺_{a,2}(N,1) - 4i A² (√(aN)/π) e^{iπac²/N} J₁ + 2iA Θ`,
  `J₁ = ∫_ℝ e^{-Ax²} (x + ρω)² τ(ωx + iρ) dx`.
  Route: `ppZ_thetaTwo_eq_kernel`, `ppZ_kernel_shift` (`k = 1`), `ppZ_kernelRes_sum` (`k = 1`):
  `4A² (√(aN)/π) e^{iπac²/N} · 2πi · (-e^{-iπac²/N} (ωπ/(2a))²/(aω)) A⁺ = -2iω a^{-1/2} N^{5/2} A⁺`
  because `A² √(aN)/π = a^{5/2} N^{5/2}/π³` (`Real.sqrt_eq_rpow`, `Real.rpow_natCast`,
  `← Real.rpow_add`) and `ω²/ω = ω`; then divide by `i`.
* `ppZ_thetaTwo_main`: `‖Θ₂ + 2ω (N^{5/2}/√a) A⁺_{a,2}(N,1)‖ ≤ K N²` for `N ≥ 16a` on the window:
  `‖J₁‖ ≤ K₁/√A` (`ppZ_shifted_integral_bound`, `k = 1`), so the second term is
  `≤ 4A² (√(aN)/π) K₁/√A = 4K₁ A²/√π = O(N²)`, and `2A‖Θ‖ = O(N)` (`ppZ_theta_bound`).

The exact formula was checked numerically to `10⁻¹⁰ N^{5/2}` (`kt.py`).
-/

noncomputable section

namespace AJConjecture

/-- `x^{5/2} = x² √x` for `x ≥ 0`. -/
private theorem rpow_five_halves_ppZThetaTwoMain {x : ℝ} (hx : 0 ≤ x) :
    x ^ (5 / 2 : ℝ) = x ^ 2 * Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x 2, ← Real.rpow_add' hx (by norm_num)]
  norm_num

/-- `A² √(aN)/π · π³ = (N^{5/2}/√a) a³` for `A = aN/π`. -/
private theorem coef_ppZThetaTwoMain {a N : ℝ} (ha : 0 < a) (hN : 0 < N) :
    (a * N / Real.pi) ^ 2 * (Real.sqrt (a * N) / Real.pi) * Real.pi ^ 3 =
      N ^ (5 / 2 : ℝ) / Real.sqrt a * a ^ 3 := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hpi := Real.pi_pos
  rw [rpow_five_halves_ppZThetaTwoMain hN.le, Real.sqrt_mul ha.le]
  field_simp
  linear_combination h1

/-- On the colour window `ρ = π(2n+1)/N` lies strictly between the poles `a - 1` and `a`. -/
private theorem window_rho_ppZThetaTwoMain (a N n : ℕ) (ha : 1 ≤ a) (hN : 4 * a ≤ N)
    (hw : |(2 * (n : ℝ) + 1) - N| < N / (4 * a) + 1) :
    (2 * (a : ℝ) - 1) * Real.pi / (2 * a) < Real.pi * (2 * n + 1) / N ∧
      Real.pi * (2 * n + 1) / N < (2 * (a : ℝ) + 1) * Real.pi / (2 * a) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpi := Real.pi_pos
  have h4 : (4 * a : ℝ) ≤ N := by exact_mod_cast hN
  have h5 : (1 : ℝ) ≤ N / (4 * a) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h6 : (N : ℝ) / (2 * a) = 2 * (N / (4 * a)) := by
    field_simp
    ring
  have hd : (N : ℝ) / (2 * a) * (2 * a) = N := div_mul_cancel₀ _ (by positivity)
  obtain ⟨hw1, hw2⟩ := abs_lt.mp (hw.trans_le (by linarith : (N : ℝ) / (4 * a) + 1 ≤ N / (2 * a)))
  constructor
  · rw [div_lt_div_iff₀ (by positivity) hNR]
    nlinarith [mul_pos hpi (mul_pos haR (by linarith :
      (0 : ℝ) < 2 * n + 1 - N + N / (2 * a)))]
  · rw [div_lt_div_iff₀ hNR (by positivity)]
    nlinarith [mul_pos hpi (mul_pos haR (by linarith :
      (0 : ℝ) < N / (2 * a) - (2 * n + 1 - N)))]

/-- On the colour window with `N ≥ 16a`, `a|ρ - π| ≤ 5π/16` for `ρ = π(2n+1)/N`. -/
private theorem window_shift_ppZThetaTwoMain (a N n : ℕ) (ha : 1 ≤ a) (hN : 16 * a ≤ N)
    (hw : |(2 * (n : ℝ) + 1) - N| < N / (4 * a) + 1) :
    a * |Real.pi * (2 * n + 1) / N - Real.pi| ≤ 5 * Real.pi / 16 := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hNR : (16 * a : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hpi := Real.pi_pos
  have e : Real.pi * (2 * n + 1) / N - Real.pi = Real.pi / N * ((2 * n + 1) - N) := by
    field_simp
  have e1 : (a : ℝ) * (Real.pi / N * |(2 * (n : ℝ) + 1) - N|) ≤
      a * (Real.pi / N * (N / (4 * a) + 1)) := by
    gcongr
  have e2 : (a : ℝ) * (Real.pi / N * (N / (4 * a) + 1)) =
      Real.pi / 4 + Real.pi * (a / N) := by
    field_simp
  have e3 : (a : ℝ) / N ≤ 1 / 16 := by
    rw [div_le_div_iff₀ hN0 (by norm_num)]
    linarith
  rw [e, abs_mul, abs_of_pos (by positivity)]
  nlinarith

/-- The exact shifted-contour formula for `Θ₂` on the colour window. -/
theorem ppZ_thetaTwo_shifted (a N n : ℕ) (hodd : Odd a) (hN : 4 * a ≤ N)
    (hw : |(2 * (n : ℝ) + 1) - N| < N / (4 * a) + 1) :
    ppZThetaTwo a N n =
      -(2 * ppZOmega * (((N : ℝ) ^ (5 / 2 : ℝ) / Real.sqrt a : ℝ) : ℂ) * geoZhengA a N 1) -
        4 * Complex.I * ((a * N / Real.pi : ℝ) : ℂ) ^ 2 *
          ((Real.sqrt (a * N) / Real.pi : ℝ) : ℂ) *
          Complex.exp (Real.pi * Complex.I * a * (2 * n + 1) ^ 2 / N) *
          (∫ x : ℝ, Complex.exp (-((a * N / Real.pi : ℝ) : ℂ) * (x : ℂ) ^ 2) *
            ((x : ℂ) + ((Real.pi * (2 * n + 1) / N : ℝ) : ℂ) * ppZOmega) ^ 2 *
            ppZTau a (ppZOmega * x + ((Real.pi * (2 * n + 1) / N : ℝ) : ℂ) * Complex.I)) +
        2 * Complex.I * ((a * N / Real.pi : ℝ) : ℂ) * ppZTheta a N n := by
  have ha : 1 ≤ a := hodd.pos
  have hN1 : 1 ≤ N := by omega
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hA : (0 : ℝ) < a * N / Real.pi := by positivity
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast haR.ne'
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hω : ppZOmega ≠ 0 := by
    intro h
    have h0 := ppZOmega_sq
    rw [h, zero_pow two_ne_zero] at h0
    exact Complex.I_ne_zero h0.symm
  obtain ⟨h1, h2⟩ := window_rho_ppZThetaTwoMain a N n ha hN hw
  have hks := ppZ_kernel_shift a 1 ha (A := a * N / Real.pi)
    (ρ := Real.pi * (2 * n + 1) / N) hA h1 h2
  have hres := ppZ_kernelRes_sum a 1 N (2 * n + 1) ha hN1 (odd_two_mul_add_one n)
  rw [show ((2 * n + 1 : ℕ) : ℝ) = 2 * (n : ℝ) + 1 by push_cast; ring,
    show ((2 * n + 1 : ℕ) : ℂ) = 2 * (n : ℂ) + 1 by push_cast; ring] at hres
  have hK := ppZ_thetaTwo_eq_kernel a N n ha hN1
  rw [hks, hres] at hK
  simp only [mul_one] at hK
  have hEE : Complex.exp (Real.pi * Complex.I * a * (2 * n + 1) ^ 2 / N) *
      Complex.exp (-(Real.pi * Complex.I * a * (2 * (n : ℂ) + 1) ^ 2 / N)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hcoef : ((a * N / Real.pi : ℝ) : ℂ) ^ 2 * ((Real.sqrt (a * N) / Real.pi : ℝ) : ℂ) *
      (Real.pi : ℂ) ^ 3 = (((N : ℝ) ^ (5 / 2 : ℝ) / Real.sqrt a : ℝ) : ℂ) * (a : ℂ) ^ 3 := by
    exact_mod_cast coef_ppZThetaTwoMain haR hNR
  have hP : (((N : ℝ) ^ (5 / 2 : ℝ) / Real.sqrt a : ℝ) : ℂ) =
      ((a * N / Real.pi : ℝ) : ℂ) ^ 2 * ((Real.sqrt (a * N) / Real.pi : ℝ) : ℂ) *
        (Real.pi : ℂ) ^ 3 / (a : ℂ) ^ 3 := by
    rw [eq_div_iff (pow_ne_zero 3 haC)]
    exact hcoef.symm
  have h3 : ∀ e : ℂ, e * (ppZOmega * Real.pi / (2 * a)) ^ 2 / (a * ppZOmega) =
      e * (ppZOmega * (Real.pi : ℂ) ^ 2 / (4 * (a : ℂ) ^ 3)) := fun e ↦ by
    field_simp
    ring
  have hI : ppZThetaTwo a N n = -Complex.I * (Complex.I * ppZThetaTwo a N n) := by
    linear_combination ppZThetaTwo a N n * Complex.I_sq
  rw [hI, hK, h3, hP]
  generalize ((a * N / Real.pi : ℝ) : ℂ) = Ac at *
  generalize ((Real.sqrt (a * N) / Real.pi : ℝ) : ℂ) = S at *
  generalize Complex.exp (Real.pi * Complex.I * a * (2 * n + 1) ^ 2 / N) = E at *
  generalize Complex.exp (-(Real.pi * Complex.I * a * (2 * (n : ℂ) + 1) ^ 2 / N)) = E' at *
  linear_combination
    (2 * Ac ^ 2 * S * (Real.pi : ℂ) ^ 3 * ppZOmega * geoZhengA a N 1 / (a : ℂ) ^ 3 *
      Complex.I ^ 2) * hEE +
    (2 * Ac ^ 2 * S * (Real.pi : ℂ) ^ 3 * ppZOmega * geoZhengA a N 1 / (a : ℂ) ^ 3) *
      Complex.I_sq

/-- `Θ₂ = -2ω (N^{5/2}/√a) A⁺_{a,2}(N, 1) + O(N²)` on the colour window, `N ≥ 16a`. -/
theorem ppZ_thetaTwo_main (a : ℕ) (hodd : Odd a) :
    ∃ K : ℝ, ∀ N n : ℕ, 16 * a ≤ N → |(2 * (n : ℝ) + 1) - N| < N / (4 * a) + 1 →
      ‖ppZThetaTwo a N n +
          2 * ppZOmega * (((N : ℝ) ^ (5 / 2 : ℝ) / Real.sqrt a : ℝ) : ℂ) * geoZhengA a N 1‖ ≤
        K * (N : ℝ) ^ 2 := by
  have ha : 1 ≤ a := hodd.pos
  obtain ⟨K₁, hK₁⟩ := ppZ_shifted_integral_bound a 1 ha le_rfl
  obtain ⟨K₀, hK₀⟩ := ppZ_theta_bound a hodd
  refine ⟨4 * (a / Real.pi) ^ 2 / Real.sqrt Real.pi * |K₁| + 2 * (a / Real.pi) * |K₀|,
    fun N n hN hw ↦ ?_⟩
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hNR : (16 * a : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hpi := Real.pi_pos
  have hA1 : 1 ≤ (a * N / Real.pi : ℝ) := by
    rw [le_div_iff₀ hpi]
    nlinarith [Real.pi_le_four]
  have hJ := hK₁ (a * N / Real.pi) (Real.pi * (2 * n + 1) / N) hA1
    (window_shift_ppZThetaTwoMain a N n ha hN hw)
  simp only [mul_one] at hJ
  have hΘ := (hK₀ N n hN hw).trans (le_abs_self K₀)
  have hE : ‖Complex.exp (Real.pi * Complex.I * a * (2 * n + 1) ^ 2 / N)‖ = 1 := by
    have e : (Real.pi * Complex.I * a * (2 * n + 1) ^ 2 / N : ℂ) =
        ((Real.pi * a * (2 * n + 1) ^ 2 / N : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [e, Complex.norm_exp_ofReal_mul_I]
  have hs : 0 < Real.sqrt (a * N) := Real.sqrt_pos.mpr (by positivity)
  have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hpp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt hpi.le
  have hsA : Real.sqrt (a * N) / Real.pi / Real.sqrt (a * N / Real.pi) =
      1 / Real.sqrt Real.pi := by
    rw [Real.sqrt_div (by positivity)]
    field_simp
    linear_combination hpp
  rw [ppZ_thetaTwo_shifted a N n hodd (by omega) hw]
  generalize (∫ x : ℝ, Complex.exp (-((a * N / Real.pi : ℝ) : ℂ) * (x : ℂ) ^ 2) *
    ((x : ℂ) + ((Real.pi * (2 * n + 1) / N : ℝ) : ℂ) * ppZOmega) ^ 2 *
    ppZTau a (ppZOmega * x + ((Real.pi * (2 * n + 1) / N : ℝ) : ℂ) * Complex.I)) = J at hJ ⊢
  have hJ' : ‖J‖ ≤ |K₁| / Real.sqrt (a * N / Real.pi) :=
    hJ.trans (div_le_div_of_nonneg_right (le_abs_self K₁) (Real.sqrt_nonneg _))
  have e1 : ‖4 * Complex.I * ((a * N / Real.pi : ℝ) : ℂ) ^ 2 *
      ((Real.sqrt (a * N) / Real.pi : ℝ) : ℂ) *
      Complex.exp (Real.pi * Complex.I * a * (2 * n + 1) ^ 2 / N) * J‖ =
      4 * (a * N / Real.pi) ^ 2 * (Real.sqrt (a * N) / Real.pi) * ‖J‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hE, norm_pow, Complex.norm_real,
      Complex.norm_real, Complex.norm_I, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by positivity)]
    norm_num
  have e2 : ‖2 * Complex.I * ((a * N / Real.pi : ℝ) : ℂ) * ppZTheta a N n‖ =
      2 * (a * N / Real.pi) * ‖ppZTheta a N n‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I,
      Real.norm_of_nonneg (by positivity)]
    norm_num
  have e3 : ∀ X T1 T2 : ℂ, -X - T1 + T2 + X = T2 - T1 := fun X T1 T2 ↦ by ring
  rw [e3]
  refine (norm_sub_le _ _).trans ?_
  rw [e1, e2]
  have b1 : 4 * ((a : ℝ) * N / Real.pi) ^ 2 * (Real.sqrt (a * N) / Real.pi) * ‖J‖ ≤
      4 * (a / Real.pi) ^ 2 / Real.sqrt Real.pi * |K₁| * (N : ℝ) ^ 2 := by
    calc 4 * ((a : ℝ) * N / Real.pi) ^ 2 * (Real.sqrt (a * N) / Real.pi) * ‖J‖
        ≤ 4 * ((a : ℝ) * N / Real.pi) ^ 2 * (Real.sqrt (a * N) / Real.pi) *
          (|K₁| / Real.sqrt (a * N / Real.pi)) := by gcongr
      _ = 4 * ((a : ℝ) * N / Real.pi) ^ 2 * |K₁| *
          (Real.sqrt (a * N) / Real.pi / Real.sqrt (a * N / Real.pi)) := by ring
      _ = 4 * (a / Real.pi) ^ 2 / Real.sqrt Real.pi * |K₁| * (N : ℝ) ^ 2 := by
          rw [hsA]
          ring
  have b2 : 2 * ((a : ℝ) * N / Real.pi) * ‖ppZTheta a N n‖ ≤
      2 * (a / Real.pi) * |K₀| * (N : ℝ) ^ 2 := by
    calc 2 * ((a : ℝ) * N / Real.pi) * ‖ppZTheta a N n‖
        ≤ 2 * ((a : ℝ) * N / Real.pi) * |K₀| := by gcongr
      _ = 2 * (a / Real.pi) * |K₀| * N := by ring
      _ ≤ 2 * (a / Real.pi) * |K₀| * (N : ℝ) ^ 2 := by
          gcongr
          nlinarith
  linarith

end AJConjecture
