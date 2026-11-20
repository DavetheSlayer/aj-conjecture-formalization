import Mathlib

/-!
# Second-order bounds for `log sin` at `π/4`, `3π/4`, `π/2` (Unit PpZ, node `PpZ_LogSin`)

Source: Zheng, (3.24) (the quadratic expansion of `f` at its critical point), in the form needed
for the exact one-step ratios of `S_{n,i}`.

For `|ε| ≤ 1/4`:
* `|log sin(π/4 + ε) - log sin(π/4) - ε| ≤ 2ε²`   (`sin(π/4+ε)/sin(π/4) = cos ε + sin ε`);
* `|log sin(3π/4 + ε) - log sin(3π/4) + ε| ≤ 2ε²` (`= cos ε - sin ε`; the first with `-ε`);
* `|log cos ε| ≤ ε²`.

Route. `|cos ε + sin ε - 1 - ε| ≤ ε²` (`Real.cos_bound`/`Real.sin_bound`, or
`1 - ε²/2 ≤ cos ε ≤ 1`, `|sin ε - ε| ≤ |ε|³/6`), so `u = cos ε + sin ε - 1` has `|u| ≤ 5/16` and
`|log(1+u) - u| ≤ u²` for `|u| ≤ 1/2` (`Real.abs_log_sub_add_sum_range_le` with `n = 1`, or
`Real.log_le_sub_one_of_pos` and `Real.one_sub_inv_le_log_of_pos`). Numerically the best constants
on `|ε| ≤ 1/4` are `1.23`, `1.23`, `0.51` (`scaf.py`).
-/

noncomputable section

namespace AJConjecture

/-- `|log(1 + u) - u| ≤ u²` for `|u| ≤ 3/10`. -/
private theorem abs_log_one_add_sub_le_sq_logSin {u : ℝ} (hu : |u| ≤ 3 / 10) :
    |Real.log (1 + u) - u| ≤ u ^ 2 := by
  have h1 : |-u| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg] at h
  norm_num at h
  have h0 : 0 ≤ |u| := abs_nonneg u
  have h2 : |u| ^ 3 / (1 - |u|) ≤ u ^ 2 / 2 := by
    rw [div_le_iff₀ (by linarith), ← sq_abs u]
    nlinarith [sq_nonneg |u|, mul_nonneg h0 (sq_nonneg |u|)]
  have h3 := abs_le.mp (h.trans h2)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg u]

/-- `|log(cos ε + sin ε) - ε| ≤ 2ε²` for `|ε| ≤ 1/4`. -/
private theorem abs_log_cos_add_sin_sub_le_logSin {ε : ℝ} (h : |ε| ≤ 1 / 4) :
    |Real.log (Real.cos ε + Real.sin ε) - ε| ≤ 2 * ε ^ 2 := by
  have h0 : 0 ≤ |ε| := abs_nonneg ε
  have hsq : ε ^ 2 = |ε| ^ 2 := (sq_abs ε).symm
  have hs := abs_le.mp (Real.sin_bound (x := ε) (by linarith))
  have hc1 := Real.one_sub_sq_div_two_le_cos (x := ε)
  have hc2 := Real.cos_le_one ε
  have hcube : |ε ^ 3| ≤ |ε| ^ 2 / 4 := by
    rw [abs_pow]; nlinarith [sq_nonneg |ε|]
  have hcube' := abs_le.mp hcube
  have hthree : |ε| ^ 3 ≤ 1 / 64 := (pow_le_pow_left₀ h0 h 3).trans (by norm_num)
  have hfive : |ε| ^ 5 ≤ |ε| ^ 2 / 64 := by nlinarith [sq_nonneg |ε|]
  have hu : |Real.cos ε + Real.sin ε - 1 - ε| ≤ 3 / 5 * |ε| ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg |ε|]
  have hu' := abs_le.mp hu
  have hε := abs_le.mp h
  have hle := le_abs_self ε
  have hge := neg_abs_le ε
  have hub : |Real.cos ε + Real.sin ε - 1| ≤ 23 / 20 * |ε| := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg |ε|]
  have hlog := abs_log_one_add_sub_le_sq_logSin
    (u := Real.cos ε + Real.sin ε - 1) (by linarith)
  rw [show 1 + (Real.cos ε + Real.sin ε - 1) = Real.cos ε + Real.sin ε by ring] at hlog
  have husq : (Real.cos ε + Real.sin ε - 1) ^ 2 ≤ (23 / 20 * |ε|) ^ 2 :=
    sq_le_sq' (by linarith [abs_le.mp hub]) (abs_le.mp hub).2
  have hlog' := abs_le.mp hlog
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg |ε|]

/-- `|log sin(π/4 + ε) - log sin(π/4) - ε| ≤ 2ε²` for `|ε| ≤ 1/4`. -/
theorem ppZ_log_sin_quarter {ε : ℝ} (h : |ε| ≤ 1 / 4) :
    |Real.log (Real.sin (Real.pi / 4 + ε)) - Real.log (Real.sin (Real.pi / 4)) - ε| ≤
      2 * ε ^ 2 := by
  have hpos : 0 < Real.cos ε + Real.sin ε := by
    have hs := abs_le.mp (Real.sin_bound (x := ε) (by linarith))
    have hc1 := Real.one_sub_sq_div_two_le_cos (x := ε)
    have hε := abs_le.mp h
    have h0 : 0 ≤ |ε| := abs_nonneg ε
    have hcube : |ε ^ 3| ≤ 1 / 64 := by
      rw [abs_pow]; nlinarith [sq_nonneg |ε|]
    have hcube' := abs_le.mp hcube
    have hfive : |ε| ^ 5 ≤ 1 / 1024 := (pow_le_pow_left₀ h0 h 5).trans (by norm_num)
    nlinarith [sq_nonneg ε, sq_abs ε]
  have hq : 0 < Real.sin (Real.pi / 4) := by
    rw [Real.sin_pi_div_four]; positivity
  have e : Real.sin (Real.pi / 4 + ε) = Real.sin (Real.pi / 4) * (Real.cos ε + Real.sin ε) := by
    rw [Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]; ring
  rw [e, Real.log_mul hq.ne' hpos.ne', add_sub_cancel_left]
  exact abs_log_cos_add_sin_sub_le_logSin h

/-- `|log sin(3π/4 + ε) - log sin(3π/4) + ε| ≤ 2ε²` for `|ε| ≤ 1/4`. -/
theorem ppZ_log_sin_three_quarter {ε : ℝ} (h : |ε| ≤ 1 / 4) :
    |Real.log (Real.sin (3 * Real.pi / 4 + ε)) - Real.log (Real.sin (3 * Real.pi / 4)) + ε| ≤
      2 * ε ^ 2 := by
  have e1 : Real.sin (3 * Real.pi / 4 + ε) = Real.sin (Real.pi / 4 + -ε) := by
    rw [← Real.sin_pi_sub]; congr 1; ring
  have e2 : Real.sin (3 * Real.pi / 4) = Real.sin (Real.pi / 4) := by
    rw [← Real.sin_pi_sub]; congr 1; ring
  have := ppZ_log_sin_quarter (ε := -ε) (by rwa [abs_neg])
  rw [e1, e2]
  simpa only [sub_neg_eq_add, neg_pow_two] using this

/-- `|log cos ε| ≤ ε²` for `|ε| ≤ 1/4`. -/
theorem ppZ_log_cos {ε : ℝ} (h : |ε| ≤ 1 / 4) : |Real.log (Real.cos ε)| ≤ ε ^ 2 := by
  have hc1 := Real.one_sub_sq_div_two_le_cos (x := ε)
  have hc2 := Real.cos_le_one ε
  have hε : ε ^ 2 ≤ 1 / 16 := by
    rw [← sq_abs ε]; nlinarith [abs_nonneg ε]
  have hpos : 0 < Real.cos ε := by linarith
  have hlow := Real.one_sub_inv_le_log_of_pos hpos
  have hup := Real.log_le_sub_one_of_pos hpos
  have hinv : (Real.cos ε)⁻¹ ≤ 1 + ε ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith [sq_nonneg ε]
  rw [abs_le]
  constructor <;> linarith

end AJConjecture
