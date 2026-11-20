import Mathlib
import AJPaper.Zheng.PpZNormSteps
import AJPaper.Zheng.PpZLogSin

/-!
# The one-step log-ratios of `S` against the quadratic potential
(Unit PpZ, node `PpZ_NormLocalStep`)

Source: Zheng, (3.31): `log S_{n,i} - log S₀ = -(π/N)(n'² + 2n'i' + 2i'²) + O(N^{3δ-2})`,
`n' = n - N/2`, `i' = i - N/4`; here the statement for one step.

`ppZPot N x y = -(π/N) Q(x - N/2, y - N/4)`, `Q(x, y) = x² + 2xy + 2y²`. On the box
`|n'| ≤ r`, `|i'| ≤ r`, `1 ≤ r ≤ N/40`:

* `ppZ_log_normFactor_step_left`:
  `|log S_{n+1,i} - log S_{n,i} - (V(n+1,i) - V(n,i))| ≤ 1000 (r² + N)/N²`;
* `ppZ_log_normFactor_step_right`: the same for the step `i → i + 1`.

Route. Left (`ppZ_normFactor_succ_left`): the ratio is `2 sin²(3π/4 + ε₁)/sin(π/2 + ε₃)` with
`ε₁ = (n' + i' + 1)π/N`, `ε₃ = (n' + 1)π/N`; `2 sin²(3π/4) = 1`, `sin(π/2 + ε₃) = cos ε₃`. By
`ppZ_log_sin_three_quarter` and `ppZ_log_cos` its logarithm is `-2ε₁ + θ`, `|θ| ≤ 4ε₁² + ε₃²`,
and `V(n+1,i) - V(n,i) = -(π/N)(2n' + 2i' + 1) = -2ε₁ + π/N`. With `|ε₁| ≤ 3πr/N ≤ 1/4`,
`|ε₃| ≤ 2πr/N`: total `≤ π/N + 40π² r²/N²`.
Right (`ppZ_normFactor_succ_right`): the ratio is `(sin(3π/4 + ε₁)/sin(π/4 + ε₂))²`,
`ε₂ = (i' + 1)π/N`, `sin(3π/4) = sin(π/4)`; its logarithm is `-2ε₁ - 2ε₂ + θ`,
`|θ| ≤ 4ε₁² + 4ε₂²`, and `V(n,i+1) - V(n,i) = -(π/N)(2n' + 4i' + 2) = -2ε₁ - 2ε₂ + 2π/N`.
Positivity of the three values of `S` (`ppZ_normFactor_pos`): `n + i + 1 < N` since
`n + i ≤ 3N/4 + 2r ≤ 4N/5`.
-/

noncomputable section

namespace AJConjecture

/-- The quadratic potential `V(x, y) = -(π/N)((x-N/2)² + 2(x-N/2)(y-N/4) + 2(y-N/4)²)`. -/
def ppZPot (N : ℕ) (x y : ℝ) : ℝ :=
  -(Real.pi / N) * ((x - N / 2) ^ 2 + 2 * (x - N / 2) * (y - N / 4) + 2 * (y - N / 4) ^ 2)

/-- An angle `aπ/N` with `|a| ≤ 3r`, `40r ≤ N` is at most `1/4`, and its square is
`≤ 100 r²/N²`. -/
private theorem abs_angle_le_normLocalStep {N r a : ℝ} (hr1 : 1 ≤ r) (hr : 40 * r ≤ N)
    (ha : |a| ≤ 3 * r) :
    |a * Real.pi / N| ≤ 1 / 4 ∧ (a * Real.pi / N) ^ 2 ≤ 100 * (r ^ 2 / N ^ 2) := by
  have hN : (0 : ℝ) < N := by linarith
  have hπ : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
  have h1 : |a * Real.pi / N| ≤ 10 * r / N := by
    rw [abs_div, abs_mul, abs_of_pos hN, abs_of_pos Real.pi_pos]
    have h0 : |a| * Real.pi ≤ 3 * r * 3.15 :=
      mul_le_mul ha hπ Real.pi_pos.le (by linarith)
    exact div_le_div_of_nonneg_right (by linarith) hN.le
  have h2 : 10 * r / N ≤ 1 / 4 := by
    rw [div_le_iff₀ hN]; linarith
  refine ⟨h1.trans h2, ?_⟩
  have h3 : (a * Real.pi / N) ^ 2 ≤ (10 * r / N) ^ 2 :=
    sq_le_sq' (by linarith [abs_le.mp h1]) (abs_le.mp h1).2
  calc (a * Real.pi / N) ^ 2 ≤ (10 * r / N) ^ 2 := h3
    _ = 100 * (r ^ 2 / N ^ 2) := by ring

/-- `log sin(3π/4) = -(log 2)/2`. -/
private theorem log_sin_three_quarter_normLocalStep :
    Real.log (Real.sin (3 * Real.pi / 4)) = -(Real.log 2) / 2 := by
  have e2 : Real.sin (3 * Real.pi / 4) = Real.sin (Real.pi / 4) := by
    rw [← Real.sin_pi_sub]; congr 1; ring
  rw [e2, Real.sin_pi_div_four, Real.log_div (by positivity) (by norm_num),
    Real.log_sqrt (by norm_num)]
  ring

/-- `sin(3π/4 + ε) > 0` for `|ε| ≤ 1/4`. -/
private theorem sin_three_quarter_add_pos_normLocalStep {ε : ℝ} (h : |ε| ≤ 1 / 4) :
    0 < Real.sin (3 * Real.pi / 4 + ε) := by
  have h' := abs_le.mp h
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_gt_three])
    (by linarith [Real.pi_gt_three])

/-- `π/N ≤ 4 N/N²`. -/
private theorem pi_div_le_normLocalStep {N : ℝ} (hN : 0 < N) :
    Real.pi / N ≤ 4 * (N / N ^ 2) := by
  have e : N / N ^ 2 = 1 / N := by field_simp
  rw [e, mul_one_div]
  gcongr
  exact Real.pi_le_four

/-- One step in `n` on the box of radius `r ≤ N/40`. -/
theorem ppZ_log_normFactor_step_left {N n i : ℕ} {r : ℝ} (hr1 : 1 ≤ r) (hr : 40 * r ≤ N)
    (hn : |(n : ℝ) - N / 2| ≤ r) (hi : |(i : ℝ) - N / 4| ≤ r) :
    |Real.log (geoNormFactor N (n + 1) i) - Real.log (geoNormFactor N n i) -
        (ppZPot N ((n : ℝ) + 1) i - ppZPot N n i)| ≤ 1000 * (r ^ 2 + N) / (N : ℝ) ^ 2 := by
  have hN : (0 : ℝ) < N := by linarith
  have hNne : (N : ℝ) ≠ 0 := hN.ne'
  obtain ⟨hn1, hn2⟩ := abs_le.mp hn
  obtain ⟨hi1, hi2⟩ := abs_le.mp hi
  have hlt : n + i + 1 < N := by
    have : (n : ℝ) + i + 1 < N := by linarith
    exact_mod_cast this
  have hS := ppZ_normFactor_pos (N := N) (n := n) (i := i) (by omega)
  obtain ⟨c1, d1⟩ := abs_angle_le_normLocalStep (a := (n : ℝ) - N / 2 + ((i : ℝ) - N / 4) + 1)
    hr1 hr (by rw [abs_le]; constructor <;> linarith)
  have a1 : ((i : ℝ) + n + 1) * Real.pi / N =
      3 * Real.pi / 4 + ((n : ℝ) - N / 2 + ((i : ℝ) - N / 4) + 1) * Real.pi / N := by
    field_simp; ring
  have L1 := abs_le.mp (ppZ_log_sin_three_quarter c1)
  have hsin1 := sin_three_quarter_add_pos_normLocalStep c1
  have hπN := pi_div_le_normLocalStep hN
  have hπN0 : 0 < Real.pi / N := by positivity
  have hrN : 0 ≤ r ^ 2 / (N : ℝ) ^ 2 := by positivity
  have hNN : 0 ≤ (N : ℝ) / (N : ℝ) ^ 2 := by positivity
  have hrhs : 1000 * (r ^ 2 + N) / (N : ℝ) ^ 2 =
      1000 * (r ^ 2 / (N : ℝ) ^ 2) + 1000 * ((N : ℝ) / (N : ℝ) ^ 2) := by ring
  obtain ⟨c3, d3⟩ := abs_angle_le_normLocalStep (a := (n : ℝ) - N / 2 + 1)
    hr1 hr (by rw [abs_le]; constructor <;> linarith)
  have a3 : ((n : ℝ) + 1) * Real.pi / N =
      ((n : ℝ) - N / 2 + 1) * Real.pi / N + Real.pi / 2 := by
    field_simp; ring
  have L3 := abs_le.mp (ppZ_log_cos c3)
  have hcos3 : 0 < Real.cos (((n : ℝ) - N / 2 + 1) * Real.pi / N) := by
    have h' := abs_le.mp c3
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  have hV : ppZPot N ((n : ℝ) + 1) i - ppZPot N n i =
      -2 * (((n : ℝ) - N / 2 + ((i : ℝ) - N / 4) + 1) * Real.pi / N) + Real.pi / N := by
    unfold ppZPot; field_simp; ring
  rw [ppZ_normFactor_succ_left, a1, a3, Real.sin_add_pi_div_two, hV,
    Real.log_mul hS.ne' (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) hcos3.ne',
    Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, hrhs]
  rw [log_sin_three_quarter_normLocalStep] at L1
  push_cast
  rw [abs_le]
  constructor <;> linarith

/-- One step in `i` on the box of radius `r ≤ N/40`. -/
theorem ppZ_log_normFactor_step_right {N n i : ℕ} {r : ℝ} (hr1 : 1 ≤ r) (hr : 40 * r ≤ N)
    (hn : |(n : ℝ) - N / 2| ≤ r) (hi : |(i : ℝ) - N / 4| ≤ r) :
    |Real.log (geoNormFactor N n (i + 1)) - Real.log (geoNormFactor N n i) -
        (ppZPot N n ((i : ℝ) + 1) - ppZPot N n i)| ≤ 1000 * (r ^ 2 + N) / (N : ℝ) ^ 2 := by
  have hN : (0 : ℝ) < N := by linarith
  have hNne : (N : ℝ) ≠ 0 := hN.ne'
  obtain ⟨hn1, hn2⟩ := abs_le.mp hn
  obtain ⟨hi1, hi2⟩ := abs_le.mp hi
  have hlt : n + i + 1 < N := by
    have : (n : ℝ) + i + 1 < N := by linarith
    exact_mod_cast this
  have hS := ppZ_normFactor_pos (N := N) (n := n) (i := i) (by omega)
  obtain ⟨c1, d1⟩ := abs_angle_le_normLocalStep (a := (n : ℝ) - N / 2 + ((i : ℝ) - N / 4) + 1)
    hr1 hr (by rw [abs_le]; constructor <;> linarith)
  have a1 : ((i : ℝ) + n + 1) * Real.pi / N =
      3 * Real.pi / 4 + ((n : ℝ) - N / 2 + ((i : ℝ) - N / 4) + 1) * Real.pi / N := by
    field_simp; ring
  have L1 := abs_le.mp (ppZ_log_sin_three_quarter c1)
  have hsin1 := sin_three_quarter_add_pos_normLocalStep c1
  have hπN := pi_div_le_normLocalStep hN
  have hπN0 : 0 < Real.pi / N := by positivity
  have hrN : 0 ≤ r ^ 2 / (N : ℝ) ^ 2 := by positivity
  have hNN : 0 ≤ (N : ℝ) / (N : ℝ) ^ 2 := by positivity
  have hrhs : 1000 * (r ^ 2 + N) / (N : ℝ) ^ 2 =
      1000 * (r ^ 2 / (N : ℝ) ^ 2) + 1000 * ((N : ℝ) / (N : ℝ) ^ 2) := by ring
  obtain ⟨c2, d2⟩ := abs_angle_le_normLocalStep (a := (i : ℝ) - N / 4 + 1)
    hr1 hr (by rw [abs_le]; constructor <;> linarith)
  have a2 : ((i : ℝ) + 1) * Real.pi / N =
      Real.pi / 4 + ((i : ℝ) - N / 4 + 1) * Real.pi / N := by
    field_simp; ring
  have L2 := abs_le.mp (ppZ_log_sin_quarter c2)
  have hsin2 : 0 < Real.sin (Real.pi / 4 + ((i : ℝ) - N / 4 + 1) * Real.pi / N) := by
    have h' := abs_le.mp c2
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_gt_three])
      (by linarith [Real.pi_gt_three])
  have hS' := ppZ_normFactor_pos (N := N) (n := n) (i := i + 1) (by omega)
  have hV : ppZPot N n ((i : ℝ) + 1) - ppZPot N n i =
      -2 * (((n : ℝ) - N / 2 + ((i : ℝ) - N / 4) + 1) * Real.pi / N) -
        2 * (((i : ℝ) - N / 4 + 1) * Real.pi / N) + 2 * (Real.pi / N) := by
    unfold ppZPot; field_simp; ring
  have key := congrArg Real.log (ppZ_normFactor_succ_right N n i)
  rw [a1, a2, Real.log_mul hS'.ne' (by positivity), Real.log_mul hS.ne' (by positivity),
    Real.log_pow, Real.log_pow] at key
  have e34 : Real.log (Real.sin (Real.pi / 4)) = -(Real.log 2) / 2 := by
    rw [← log_sin_three_quarter_normLocalStep, ← Real.sin_pi_sub]; congr 2; ring
  rw [log_sin_three_quarter_normLocalStep] at L1
  rw [e34] at L2
  push_cast at key
  rw [hV, hrhs, abs_le]
  constructor <;> linarith

end AJConjecture
