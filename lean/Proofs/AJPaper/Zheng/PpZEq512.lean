import Mathlib
import AJHandoff.Geometry.GeoZhEq519
import AJPaper.Zheng.PpZHatTheta
import AJPaper.Zheng.PpZThetaKernel
import AJPaper.Zheng.PpZKernelShift
import AJPaper.Zheng.PpZZhengAZero
import AJPaper.Zheng.PpZShiftBound

/-!
# Zheng's (5.12): `Ĥ_n = O(1)` on the colour window (Unit PpZ, node `PpZ_Eq512`)

Source: H. Zheng, arXiv:math/0508138v4, Lemma 5.2, (5.12): `Ĵ_{T(p,q),n}(e^{2πi/N}) = O(1)`
uniformly on `|n - N| < N/(2pq)`; here `(p, q) = (a, 2)`, odd colour `c = 2n + 1`.

* `ppZ_theta_shifted`: the exact formula. For `N ≥ 4a` and `|c - N| < N/(4a) + 1`, with
  `A = aN/π`, `ρ = πc/N`,
  `Θ = (√(aN)/π) e^{iπac²/N} ∫_ℝ e^{-Ax²} τ(ωx + iρ) dx`
  (`ppZ_theta_eq_kernel`, `ppZ_kernel_shift` with `k = 0`: its hypothesis on `ρ` is
  `|c - N| < N/(2a)`, which follows from `N/(4a) + 1 ≤ N/(2a)`; the residue sum is a multiple of
  `A⁺_{a,2}(N, 0) = 0` by `ppZ_kernelRes_sum` and `ppZ_zhengA_zero`).
* `ppZ_theta_bound`: `‖Θ‖ ≤ K` for `N ≥ 16a` on that window: `a|ρ - π| = πa|c - N|/N <
  π/4 + πa/N ≤ 5π/16`, so `ppZ_shifted_integral_bound` (`k = 0`, `A = aN/π ≥ 1`) gives
  `‖Θ‖ ≤ (√(aN)/π) · K₀/√A = K₀/√π`.
* `zhengEq512_holds`: `ZhengEq512 a` with `N₀ = 16a`; `‖Ĥ_n‖ = ‖Θ‖` by `ppZ_hatInput_eq_theta`
  (the prefactor has modulus `1`: `Complex.norm_exp` of a purely imaginary number).

Numerically `sup ‖Ĥ_n‖ = 1.41, 0.70, 0.44` for `a = 1, 3, 5` (`range_a.py`); the exact formula
holds to `10⁻¹⁰` (`kt.py`). The statement is false for `a = 2` (`A⁺_{2,2}(N, 0) ≠ 0`).
-/

noncomputable section

namespace AJConjecture

/-- The exact shifted-contour formula for `Θ` on the colour window. -/
theorem ppZ_theta_shifted (a N n : ℕ) (hodd : Odd a) (hN : 4 * a ≤ N)
    (hw : |(2 * (n : ℝ) + 1) - N| < N / (4 * a) + 1) :
    ppZTheta a N n =
      ((Real.sqrt (a * N) / Real.pi : ℝ) : ℂ) *
        Complex.exp (Real.pi * Complex.I * a * (2 * n + 1) ^ 2 / N) *
        ∫ x : ℝ, Complex.exp (-((a * N / Real.pi : ℝ) : ℂ) * (x : ℂ) ^ 2) *
          ppZTau a (ppZOmega * x + ((Real.pi * (2 * n + 1) / N : ℝ) : ℂ) * Complex.I) := by
  have ha : 1 ≤ a := hodd.pos
  have hN1 : 1 ≤ N := by omega
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpi := Real.pi_pos
  have hA : (0 : ℝ) < a * N / Real.pi := by positivity
  have h4 : (4 * a : ℝ) ≤ N := by exact_mod_cast hN
  have h5 : (1 : ℝ) ≤ N / (4 * a) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h6 : (N : ℝ) / (2 * a) = 2 * (N / (4 * a)) := by
    field_simp
    ring
  have hd : (N : ℝ) / (2 * a) * (2 * a) = N := div_mul_cancel₀ _ (by positivity)
  obtain ⟨hw1, hw2⟩ := abs_lt.mp (hw.trans_le (by linarith : (N : ℝ) / (4 * a) + 1 ≤ N / (2 * a)))
  have h1 : (2 * (a : ℝ) - 1) * Real.pi / (2 * a) < Real.pi * (2 * n + 1) / N := by
    rw [div_lt_div_iff₀ (by positivity) hNR]
    nlinarith [mul_pos hpi (mul_pos haR (by linarith :
      (0 : ℝ) < 2 * n + 1 - N + N / (2 * a)))]
  have h2 : Real.pi * (2 * n + 1) / N < (2 * (a : ℝ) + 1) * Real.pi / (2 * a) := by
    rw [div_lt_div_iff₀ hNR (by positivity)]
    nlinarith [mul_pos hpi (mul_pos haR (by linarith :
      (0 : ℝ) < N / (2 * a) - (2 * n + 1 - N)))]
  have hks := ppZ_kernel_shift a 0 ha (A := a * N / Real.pi)
    (ρ := Real.pi * (2 * n + 1) / N) hA h1 h2
  have hres := ppZ_kernelRes_sum a 0 N (2 * n + 1) ha hN1 (odd_two_mul_add_one n)
  rw [ppZ_zhengA_zero a hodd, mul_zero,
    show ((2 * n + 1 : ℕ) : ℝ) = 2 * (n : ℝ) + 1 by push_cast; ring] at hres
  rw [ppZ_theta_eq_kernel a N n ha hN1, hks, hres]
  simp only [mul_zero, pow_zero, mul_one, add_zero]

/-- `Θ = O(1)` on the colour window `|2n + 1 - N| < N/(4a) + 1`, `N ≥ 16a`. -/
theorem ppZ_theta_bound (a : ℕ) (hodd : Odd a) :
    ∃ K : ℝ, ∀ N n : ℕ, 16 * a ≤ N →
      |(2 * (n : ℝ) + 1) - N| < N / (4 * a) + 1 → ‖ppZTheta a N n‖ ≤ K := by
  have ha : 1 ≤ a := hodd.pos
  obtain ⟨K₀, hK⟩ := ppZ_shifted_integral_bound a 0 ha (by norm_num)
  refine ⟨K₀ / Real.sqrt Real.pi, fun N n hN hw ↦ ?_⟩
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hNR : (16 * a : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hpi := Real.pi_pos
  have hA1 : 1 ≤ (a * N / Real.pi : ℝ) := by
    rw [le_div_iff₀ hpi]
    nlinarith [Real.pi_le_four]
  have hρ : a * |Real.pi * (2 * n + 1) / N - Real.pi| ≤ 5 * Real.pi / 16 := by
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
  have hb := hK (a * N / Real.pi) (Real.pi * (2 * n + 1) / N) hA1 hρ
  simp only [mul_zero, pow_zero, mul_one] at hb
  have hE : ‖Complex.exp (Real.pi * Complex.I * a * (2 * n + 1) ^ 2 / N)‖ = 1 := by
    have e : (Real.pi * Complex.I * a * (2 * n + 1) ^ 2 / N : ℂ) =
        ((Real.pi * a * (2 * n + 1) ^ 2 / N : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [e, Complex.norm_exp_ofReal_mul_I]
  have hs : 0 < Real.sqrt (a * N) := Real.sqrt_pos.mpr (by positivity)
  have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hpp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt hpi.le
  rw [ppZ_theta_shifted a N n hodd (by omega) hw, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), hE, mul_one]
  calc Real.sqrt (a * N) / Real.pi * ‖_‖
      ≤ Real.sqrt (a * N) / Real.pi * (K₀ / Real.sqrt (a * N / Real.pi)) := by gcongr
    _ = K₀ / Real.sqrt Real.pi := by
        rw [Real.sqrt_div (by positivity)]
        field_simp
        linear_combination K₀ * hpp

/-- **Zheng (5.12)** for the odd colours of `T(a, 2)`, `a` odd. -/
theorem zhengEq512_holds (a : ℕ) (hodd : Odd a) : ZhengEq512 a := by
  obtain ⟨K, hK⟩ := ppZ_theta_bound a hodd
  refine ⟨K, 16 * a, fun N n hN _ hw ↦ ?_⟩
  have ha : 1 ≤ a := hodd.pos
  have hv : (Real.pi * Complex.I *
      (-(4 * (a : ℂ) * n * (n + 1)) - ((a : ℂ) ^ 2 + 4) / (4 * a)) / N : ℂ) =
      ((Real.pi * (-(4 * (a : ℝ) * n * (n + 1)) - ((a : ℝ) ^ 2 + 4) / (4 * a)) / N : ℝ) : ℂ) *
        Complex.I := by
    push_cast
    ring
  rw [ppZ_hatInput_eq_theta a N n ha (by omega), hv, norm_mul, Complex.norm_exp_ofReal_mul_I,
    one_mul]
  exact hK N n hN (by linarith)

end AJConjecture
