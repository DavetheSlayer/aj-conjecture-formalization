import Mathlib
import AJPaper.Zheng.PpZThetaTwoMain

/-!
# Zheng's (5.20) on the colour window (Unit PpZ, node `PpZ_Eq520Main`)

Source: Zheng, Lemma 5.2, (5.13), and (5.20).

* `ppZ_zhengC_mul_phase`: the leading term of (5.20) is the leading term of the theta formula:
  `C_{a,N} a_n^{-8a} = ½ e^{πi v_n/N} · (-2ω (N^{5/2}/√a) A⁺_{a,2}(N,1))/(4a)`,
  `v_n = -4an(n+1) - (a²+4)/(4a)`.
  Route: `geoZhengC`, `geoPhasePow`, `geoPhaseArg` unfolded; `(4a)^{3/2} = 8 a √a`
  (`Real.rpow_natCast`, `Real.sqrt_eq_rpow`, `Real.mul_rpow`); `e^{πi/4} = ω`;
  `-(a/2 + 2/a)πi/(2N) = -πi(a²+4)/(4aN)`; and
  `-8a · πn(n+1-N)/(2N) = -4aπ n(n+1)/N + 2π · 2an`, the last term giving `e^{2πi·2an} = 1`
  (`Complex.exp_int_mul_two_pi_mul_I` / `Complex.exp_nat_mul_two_pi_mul_I`).
* `ppZ_hatInputDeriv_main`: for `N ≥ 16a`, `n < N`, `|2n + 1 - N| < N/(4a) + 1`:
  `‖q∂_q Ĥ_n - C_{a,N} a_n^{-8a}‖ ≤ K N²`.
  Route: `ppZ_hatInputDeriv_eq_theta` minus `ppZ_zhengC_mul_phase` is
  `½ e^{πi v_n/N} (v_n Θ + (Θ₂ + 2ω (N^{5/2}/√a) A⁺)/(4a))`; `|v_n| ≤ 4aN² + a` for `n < N`,
  `‖Θ‖ ≤ K₀` (`ppZ_theta_bound`), `ppZ_thetaTwo_main`.

Numerically `‖D_n - C a_n^{-8a}‖/N² ≈ 2.4/N` (`range_a.py`).
-/

noncomputable section

namespace AJConjecture

/-- `(4a)^{3/2} = 8a√a`. -/
private theorem four_mul_rpow_ppZEq520Main {a : ℝ} (ha : 0 ≤ a) :
    (4 * a) ^ (3 / 2 : ℝ) = 8 * a * Real.sqrt a := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h : (4 * a) ^ (3 / 2 : ℝ) = (4 * a) ^ (1 : ℕ) * Real.sqrt (4 * a) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (4 * a) 1,
      ← Real.rpow_add' (by positivity) (by norm_num)]
    norm_num
  rw [h, Real.sqrt_mul (by norm_num), h4]
  ring

/-- The phases agree: `e^{-(a/2+2/a)πi/(2N) + πi/4} a_n^{-8a} = e^{πi v_n/N} ω`. -/
private theorem exp_mul_phase_ppZEq520Main (a N n : ℕ) (ha : 1 ≤ a) (hN : 1 ≤ N) :
    Complex.exp (-((a : ℂ) / 2 + 2 / a) * Real.pi * Complex.I / (2 * N) +
        Real.pi * Complex.I / 4) * geoPhasePow N n (-(8 * a : ℝ)) =
      Complex.exp (Real.pi * Complex.I *
        (-(4 * (a : ℂ) * n * (n + 1)) - ((a : ℂ) ^ 2 + 4) / (4 * a)) / N) * ppZOmega := by
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have e : -((a : ℂ) / 2 + 2 / a) * Real.pi * Complex.I / (2 * N) + Real.pi * Complex.I / 4 +
      ((-(8 * a : ℝ) * geoPhaseArg N n : ℝ) : ℂ) * Complex.I =
      Real.pi * Complex.I * (-(4 * (a : ℂ) * n * (n + 1)) - ((a : ℂ) ^ 2 + 4) / (4 * a)) / N +
        Real.pi * Complex.I / 4 + ((2 * a * n : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [geoPhaseArg]
    push_cast
    field_simp
    ring
  rw [geoPhasePow, ppZOmega, ← Complex.exp_add, ← Complex.exp_add, e, Complex.exp_add _ (_ * _),
    Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- `C_{a,N} a_n^{-8a} = ½ e^{πi v_n/N} (-2ω (N^{5/2}/√a) A⁺_{a,2}(N,1))/(4a)`. -/
theorem ppZ_zhengC_mul_phase (a N n : ℕ) (ha : 1 ≤ a) (hN : 1 ≤ N) :
    geoZhengC a N * geoPhasePow N n (-(8 * a : ℝ)) =
      1 / 2 * Complex.exp (Real.pi * Complex.I *
          (-(4 * (a : ℂ) * n * (n + 1)) - ((a : ℂ) ^ 2 + 4) / (4 * a)) / N) *
        (-(2 * ppZOmega * (((N : ℝ) ^ (5 / 2 : ℝ) / Real.sqrt a : ℝ) : ℂ) * geoZhengA a N 1) /
          (4 * a)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hR : (((N : ℝ) ^ (5 / 2 : ℝ) / (4 * (a : ℝ)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) =
      (((N : ℝ) ^ (5 / 2 : ℝ) / Real.sqrt a : ℝ) : ℂ) / (8 * a) := by
    rw [four_mul_rpow_ppZEq520Main haR.le]
    push_cast
    rw [div_div]
    congr 1
    ring
  have hexp := exp_mul_phase_ppZEq520Main a N n ha hN
  rw [geoZhengC]
  linear_combination
    (-2 * (((N : ℝ) ^ (5 / 2 : ℝ) / (4 * (a : ℝ)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * geoZhengA a N 1) *
      hexp +
    (-2 * geoZhengA a N 1 * Complex.exp (Real.pi * Complex.I *
      (-(4 * (a : ℂ) * n * (n + 1)) - ((a : ℂ) ^ 2 + 4) / (4 * a)) / N) * ppZOmega) * hR

/-- (5.20) on the colour window `|2n + 1 - N| < N/(4a) + 1`, `N ≥ 16a`. -/
theorem ppZ_hatInputDeriv_main (a : ℕ) (hodd : Odd a) :
    ∃ K : ℝ, ∀ N n : ℕ, 16 * a ≤ N → n < N → |(2 * (n : ℝ) + 1) - N| < N / (4 * a) + 1 →
      ‖geoHatInputDeriv a n N - geoZhengC a N * geoPhasePow N n (-(8 * a : ℝ))‖ ≤
        K * (N : ℝ) ^ 2 := by
  have ha : 1 ≤ a := hodd.pos
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  obtain ⟨K₀, hK₀⟩ := ppZ_theta_bound a hodd
  obtain ⟨K₂, hK₂⟩ := ppZ_thetaTwo_main a hodd
  refine ⟨1 / 2 * ((4 * a + ((a : ℝ) ^ 2 + 4) / (4 * a)) * |K₀| + |K₂| / (4 * a)),
    fun N n hN hn hw ↦ ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hnR : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hΘ := (hK₀ N n hN hw).trans (le_abs_self K₀)
  have hW := (hK₂ N n hN hw).trans
    (mul_le_mul_of_nonneg_right (le_abs_self K₂) (sq_nonneg (N : ℝ)))
  have hv : (Real.pi * Complex.I *
      (-(4 * (a : ℂ) * n * (n + 1)) - ((a : ℂ) ^ 2 + 4) / (4 * a)) / N : ℂ) =
      ((Real.pi * (-(4 * (a : ℝ) * n * (n + 1)) - ((a : ℝ) ^ 2 + 4) / (4 * a)) / N : ℝ) : ℂ) *
        Complex.I := by
    push_cast
    ring
  have hvv : (-(4 * (a : ℂ) * n * (n + 1)) - ((a : ℂ) ^ 2 + 4) / (4 * a)) =
      ((-(4 * (a : ℝ) * n * (n + 1)) - ((a : ℝ) ^ 2 + 4) / (4 * a) : ℝ) : ℂ) := by
    push_cast
    ring
  have hvabs : |(-(4 * (a : ℝ) * n * (n + 1)) - ((a : ℝ) ^ 2 + 4) / (4 * a))| ≤
      (4 * a + ((a : ℝ) ^ 2 + 4) / (4 * a)) * (N : ℝ) ^ 2 := by
    have hq : (0 : ℝ) ≤ ((a : ℝ) ^ 2 + 4) / (4 * a) := by positivity
    have hp : (0 : ℝ) ≤ 4 * a * n * (n + 1) := by positivity
    rw [abs_of_nonpos (by linarith)]
    have h1 : (n : ℝ) * (n + 1) ≤ (N : ℝ) ^ 2 := by nlinarith
    have h2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 4 * a),
      mul_le_mul_of_nonneg_left h2 hq]
  have ediff : geoHatInputDeriv a n N - geoZhengC a N * geoPhasePow N n (-(8 * a : ℝ)) =
      1 / 2 * Complex.exp (Real.pi * Complex.I *
          (-(4 * (a : ℂ) * n * (n + 1)) - ((a : ℂ) ^ 2 + 4) / (4 * a)) / N) *
        ((-(4 * (a : ℂ) * n * (n + 1)) - ((a : ℂ) ^ 2 + 4) / (4 * a)) * ppZTheta a N n +
          (ppZThetaTwo a N n + 2 * ppZOmega *
            (((N : ℝ) ^ (5 / 2 : ℝ) / Real.sqrt a : ℝ) : ℂ) * geoZhengA a N 1) / (4 * a)) := by
    rw [ppZ_hatInputDeriv_eq_theta a N n ha hN1, ppZ_zhengC_mul_phase a N n ha hN1]
    ring
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [ediff, norm_mul, norm_mul, hv, Complex.norm_exp_ofReal_mul_I, hvv, h12, mul_one]
  refine le_trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)) ?_
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs]
  have h4a : ‖(4 * a : ℂ)‖ = 4 * a := by
    rw [show (4 * a : ℂ) = ((4 * a : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [h4a]
  have b1 : |(-(4 * (a : ℝ) * n * (n + 1)) - ((a : ℝ) ^ 2 + 4) / (4 * a))| * ‖ppZTheta a N n‖ ≤
      (4 * a + ((a : ℝ) ^ 2 + 4) / (4 * a)) * (N : ℝ) ^ 2 * |K₀| := by
    gcongr
  have b2 : ‖ppZThetaTwo a N n + 2 * ppZOmega *
      (((N : ℝ) ^ (5 / 2 : ℝ) / Real.sqrt a : ℝ) : ℂ) * geoZhengA a N 1‖ / (4 * a) ≤
      |K₂| * (N : ℝ) ^ 2 / (4 * a) := by
    gcongr
  refine (mul_le_mul_of_nonneg_left (add_le_add b1 b2) (by norm_num)).trans (le_of_eq ?_)
  ring

end AJConjecture
