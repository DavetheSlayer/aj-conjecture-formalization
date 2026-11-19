import Mathlib
import AJPaper.Zheng.PpZRidgeRatio

/-!
# Two-sided bounds for the ridge steps (Unit PpZ, node `PpZ_RidgeStep`)

With `φ_k = kπ/(2N)`: `cot φ_{n+1} ≤ T_{n+1}/T_n ≤ cot φ_{n-2}`, in product form.

* `ppZ_ridge_step_ge`: `T_n cos φ_{n+1} ≤ T_{n+1} sin φ_{n+1}`. Odd case: equality. Even case:
  `T_{n+1}/T_n = cot φ_{n+1} · (cos φ_n / cos φ_{n+1})² ≥ cot φ_{n+1}`.
* `ppZ_ridge_step_le` (`3 ≤ n`): `T_{n+1} sin φ_{n-2} ≤ T_n cos φ_{n-2}`. Odd case:
  `cot φ_{n+1} ≤ cot φ_{n-2}`. Even case: with `φ = φ_n`, `x = π/(2N)` the claim is
  `2 cos²φ sin(φ - 2x) ≤ sin(2φ + 2x) cos(φ - 2x)`; the difference of the two sides is
  `2 cos φ sin 2x + 2 cos(2φ + x) sin x cos(φ - 2x)`, which is `≥ 0` because
  `2 cos φ cos x ≥ cos(φ - 2x)` when `φ + x ≤ π/2 - x` (write `φ = π/2 - kx`, `k = N - n ≥ 2`:
  `sin((k+1)x) + sin((k-1)x) ≥ sin((k+2)x)`).

Both checked numerically for all `n`, `N ≤ 79` and `N ∈ {100, …, 2047}` (`ridge.py`).
-/

noncomputable section

namespace AJConjecture

/-- The identity behind the even ridge step:
`2 sin(φ+x) cos(φ+x) cos(φ-2x) - 2 cos²φ sin(φ-2x)`
`= 2 cos φ sin 2x + 2 cos(2φ+x) sin x cos(φ-2x)`. -/
private theorem even_step_identity_ridgeStep (φ x : ℝ) :
    2 * (Real.sin (φ + x) * Real.cos (φ + x) * Real.cos (φ - 2 * x)) -
        2 * (Real.cos φ ^ 2 * Real.sin (φ - 2 * x)) =
      2 * Real.cos φ * Real.sin (2 * x) +
        2 * Real.cos (2 * φ + x) * Real.sin x * Real.cos (φ - 2 * x) := by
  have J1 : 2 * Real.sin (φ + x) * Real.cos (φ + x) * Real.cos (φ - 2 * x) -
      (2 * Real.cos φ ^ 2 - 1) * Real.sin (φ - 2 * x) =
      Real.sin (2 * φ + x) * Real.cos (φ - x) - Real.cos (2 * φ + x) * Real.sin (φ - 3 * x) := by
    have h : Real.sin (2 * φ + x + x) * Real.cos (φ - 2 * x) -
        Real.cos (2 * φ + x - x) * Real.sin (φ - 2 * x) =
        Real.sin (2 * φ + x) * Real.cos (x + (φ - 2 * x)) -
          Real.cos (2 * φ + x) * Real.sin (φ - 2 * x - x) := by
      rw [Real.sin_add (2 * φ + x) x, Real.cos_sub (2 * φ + x) x, Real.cos_add x,
        Real.sin_sub (φ - 2 * x) x]
      ring
    rw [show 2 * φ + x + x = 2 * (φ + x) by ring, show 2 * φ + x - x = 2 * φ by ring,
      show x + (φ - 2 * x) = φ - x by ring, show φ - 2 * x - x = φ - 3 * x by ring,
      Real.sin_two_mul, Real.cos_two_mul] at h
    linear_combination h
  have J2 : 2 * Real.sin x * Real.cos (φ - 2 * x) =
      Real.sin (φ - x) - Real.sin (φ - 3 * x) := by
    have h : 2 * Real.sin x * Real.cos (φ - 2 * x) =
        Real.sin (φ - 2 * x + x) - Real.sin (φ - 2 * x - x) := by
      rw [Real.sin_add (φ - 2 * x) x, Real.sin_sub (φ - 2 * x) x]
      ring
    rw [show φ - 2 * x + x = φ - x by ring, show φ - 2 * x - x = φ - 3 * x by ring] at h
    exact h
  have J3 : Real.sin (2 * φ + x) * Real.cos (φ - x) - Real.cos (2 * φ + x) * Real.sin (φ - x) =
      Real.sin (φ + 2 * x) := by
    rw [← Real.sin_sub]
    congr 1
    ring
  have J4 : Real.sin (φ + 2 * x) - Real.sin (φ - 2 * x) = 2 * Real.cos φ * Real.sin (2 * x) := by
    rw [Real.sin_add, Real.sin_sub]
    ring
  linear_combination J1 + J4 - Real.cos (2 * φ + x) * J2 + J3

/-- The trigonometric inequality of the even ridge step:
`cos²φ sin(φ-2x) ≤ sin(φ+x) cos(φ+x) cos(φ-2x)` for `0 ≤ x`, `2x ≤ φ`, `φ + 2x ≤ π/2`. -/
private theorem even_step_trig_ridgeStep {φ x : ℝ} (hx0 : 0 ≤ x) (hφ : 2 * x ≤ φ)
    (hφ2 : φ + 2 * x ≤ Real.pi / 2) :
    Real.cos φ ^ 2 * Real.sin (φ - 2 * x) ≤
      Real.sin (φ + x) * Real.cos (φ + x) * Real.cos (φ - 2 * x) := by
  have hπ := Real.pi_pos
  have hsx : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith)
  have hcB : 0 ≤ Real.cos (φ - 2 * x) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hcp : 0 ≤ Real.cos (φ - x) := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have h1 : Real.sin x ≤ Real.cos (φ + x) := by
    rw [← Real.sin_pi_div_two_sub]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have h2 : Real.cos (φ - 2 * x) ≤ Real.cos (φ - x) + Real.sin x := by
    have e : Real.cos (φ - 2 * x) =
        Real.cos (φ - x) * Real.cos x + Real.sin (φ - x) * Real.sin x := by
      rw [← Real.cos_sub]
      congr 1
      ring
    rw [e]
    nlinarith [Real.cos_le_one x, Real.sin_le_one (φ - x)]
  have h3 : 2 * Real.cos φ * Real.cos x = Real.cos (φ - x) + Real.cos (φ + x) := by
    rw [Real.cos_sub, Real.cos_add]
    ring
  have h4 : Real.cos (φ - 2 * x) ≤ 2 * Real.cos φ * Real.cos x := by linarith
  have key := even_step_identity_ridgeStep φ x
  rw [Real.sin_two_mul] at key
  have h5 : 0 ≤ Real.sin x * (2 * Real.cos φ * Real.cos x - Real.cos (φ - 2 * x)) :=
    mul_nonneg hsx (sub_nonneg.mpr h4)
  have h6 : 0 ≤ Real.sin x * Real.cos (φ - 2 * x) * (1 + Real.cos (2 * φ + x)) :=
    mul_nonneg (mul_nonneg hsx hcB) (by linarith [Real.neg_one_le_cos (2 * φ + x)])
  linarith

/-- The ridge value is nonnegative for `n < N`. -/
private theorem ridge_nonneg_ridgeStep {N n : ℕ} (hn : n < N) : 0 ≤ ppZRidge N n := by
  refine (ppZ_normFactor_pos ?_).le
  unfold ppZRidgeIdx
  omega

/-- `0 < φ_{n+1} < π/2` for `n + 1 < N`, hence `sin φ_{n+1} > 0` and `cos φ_{n+1} > 0`. -/
private theorem half_angle_succ_ridgeStep {N n : ℕ} (h : n + 1 < N) :
    0 < Real.sin (((n : ℝ) + 1) * Real.pi / (2 * N)) ∧
      0 < Real.cos (((n : ℝ) + 1) * Real.pi / (2 * N)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlt : (n : ℝ) + 1 < N := by exact_mod_cast h
  have hπ := Real.pi_pos
  have h0 : 0 < ((n : ℝ) + 1) * Real.pi / (2 * N) := by positivity
  have h1 : ((n : ℝ) + 1) * Real.pi / (2 * N) < Real.pi / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  exact ⟨Real.sin_pos_of_pos_of_lt_pi h0 (by linarith),
    Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩⟩

/-- Lower bound for a ridge step: `T_n cos φ_{n+1} ≤ T_{n+1} sin φ_{n+1}`. -/
theorem ppZ_ridge_step_ge {N n : ℕ} (h : n + 1 < N) :
    ppZRidge N n * Real.cos (((n : ℝ) + 1) * Real.pi / (2 * N)) ≤
      ppZRidge N (n + 1) * Real.sin (((n : ℝ) + 1) * Real.pi / (2 * N)) := by
  rcases Nat.mod_two_eq_zero_or_one (N - n) with hp | hp
  · have he := ppZ_ridge_succ_even h hp
    obtain ⟨-, hc⟩ := half_angle_succ_ridgeStep h
    have hT := ridge_nonneg_ridgeStep (by omega : n < N)
    have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hlt : (n : ℝ) + 1 < N := by exact_mod_cast h
    have hπ := Real.pi_pos
    have hcc : Real.cos (((n : ℝ) + 1) * Real.pi / (2 * N)) ≤
        Real.cos ((n : ℝ) * Real.pi / (2 * N)) := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
      · rw [div_le_iff₀ (by positivity)]
        nlinarith
      · gcongr
        linarith
    refine le_of_mul_le_mul_right ?_ hc
    rw [mul_assoc (ppZRidge N (n + 1)), he, mul_assoc, ← sq]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc.le hcc 2) hT
  · exact (ppZ_ridge_succ_odd h hp).ge

/-- Upper bound for a ridge step: `T_{n+1} sin φ_{n-2} ≤ T_n cos φ_{n-2}` for `3 ≤ n`. -/
theorem ppZ_ridge_step_le {N n : ℕ} (hn : 3 ≤ n) (h : n + 1 < N) :
    ppZRidge N (n + 1) * Real.sin (((n : ℝ) - 2) * Real.pi / (2 * N)) ≤
      ppZRidge N n * Real.cos (((n : ℝ) - 2) * Real.pi / (2 * N)) := by
  obtain ⟨hs, hc⟩ := half_angle_succ_ridgeStep h
  have hT := ridge_nonneg_ridgeStep (by omega : n < N)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlt : (n : ℝ) + 2 ≤ N := by exact_mod_cast (by omega : n + 2 ≤ N)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hπ := Real.pi_pos
  rcases Nat.mod_two_eq_zero_or_one (N - n) with hp | hp
  · have he := ppZ_ridge_succ_even h hp
    have hx0 : 0 ≤ Real.pi / (2 * N) := by positivity
    have h2x : 2 * (Real.pi / (2 * N)) ≤ (n : ℝ) * Real.pi / (2 * N) := by
      rw [← mul_div_assoc]
      gcongr
      nlinarith
    have hφ2 : (n : ℝ) * Real.pi / (2 * N) + 2 * (Real.pi / (2 * N)) ≤ Real.pi / 2 := by
      rw [← mul_div_assoc, ← add_div, div_le_iff₀ (by positivity)]
      nlinarith
    have key := even_step_trig_ridgeStep hx0 h2x hφ2
    rw [show (n : ℝ) * Real.pi / (2 * N) - 2 * (Real.pi / (2 * N)) =
        ((n : ℝ) - 2) * Real.pi / (2 * N) by ring,
      show (n : ℝ) * Real.pi / (2 * N) + Real.pi / (2 * N) =
        ((n : ℝ) + 1) * Real.pi / (2 * N) by ring] at key
    refine le_of_mul_le_mul_right ?_ (mul_pos hs hc)
    rw [mul_right_comm, he, mul_assoc, mul_right_comm, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hT
    linarith
  · have ho := ppZ_ridge_succ_odd h hp
    have hsub : 0 ≤ Real.sin (((n : ℝ) + 1) * Real.pi / (2 * N) -
        ((n : ℝ) - 2) * Real.pi / (2 * N)) := by
      have e : ((n : ℝ) + 1) * Real.pi / (2 * N) - ((n : ℝ) - 2) * Real.pi / (2 * N) =
          3 * Real.pi / (2 * N) := by ring
      rw [e]
      apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    rw [Real.sin_sub] at hsub
    refine le_of_mul_le_mul_right ?_ hs
    rw [mul_right_comm, ho, mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hT
    linarith

end AJConjecture
