import Mathlib
import AJFamily.VolumeDefs

/-!
# Continuity of the Bloch–Wigner dilogarithm

The library defines `blochWigner z = Im Li₂(z) + arg(1 - z) log |z|` for `|z| ≤ 1` (with the
dilogarithm series) and `blochWigner z = -blochWigner(1/z)` for `|z| > 1`. This file proves that
this piecewise definition is a continuous function on `ℂ` vanishing at `0`, `1` and at infinity,
so that it extends continuously to `ℙ¹(ℂ)` with `D(∞) = 0`.

Route. The series `∑ zⁿ/n²` converges uniformly on the closed unit disc (Weierstrass M-test with
`∑ 1/n²`), so `Im Li₂` is continuous there. The product `arg(1 - z) log |z|` is continuous on the
closed disc minus `{0, 1}`: `1 - z` stays off the negative real axis; at `z = 1` it tends to `0`
since `arg` is bounded by `π` and `log |z| → 0`; at `z = 0` it tends to `0` since `arg(1 - z) → 0`
faster than `log |z|` grows (`|arg(1 - z)| ≤ C |z|`). On `|z| = 1` the two branches agree by the
conjugation symmetry of the disc formula (`1/z = conj z`). Outside the disc use `z ↦ 1/z`.
-/

open Filter Topology

noncomputable section

namespace AJConjecture

/-- The disc formula `Im Li₂(z) + arg(1 - z) log ‖z‖` of the Bloch–Wigner function. -/
private def bwDiscFormula (z : ℂ) : ℝ :=
  (dilogSeries z).im + Complex.arg (1 - z) * Real.log ‖z‖

/-- `blochWigner` in terms of the disc formula. -/
private theorem blochWigner_eq_ite (z : ℂ) :
    blochWigner z = if ‖z‖ ≤ 1 then bwDiscFormula z else -bwDiscFormula z⁻¹ := rfl

/-- `‖(n : ℂ) + 1‖ = n + 1`. -/
private theorem norm_natCast_add_one (n : ℕ) : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
  rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
  push_cast
  ring

/-- The terms of the dilogarithm series are bounded by `1/(n+1)²` on the closed disc. -/
private theorem norm_dilog_term_le {z : ℂ} (hz : ‖z‖ ≤ 1) (n : ℕ) :
    ‖z ^ (n + 1) / ((n : ℂ) + 1) ^ 2‖ ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
  rw [norm_div, norm_pow, norm_pow, norm_natCast_add_one]
  gcongr
  exact pow_le_one₀ (norm_nonneg _) hz

/-- `∑ 1/(n+1)²` converges. -/
private theorem summable_one_div_succ_sq : Summable fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  exact this.congr fun n ↦ by push_cast; ring_nf

/-- The dilogarithm series is continuous on the closed unit disc (M-test). -/
private theorem continuousOn_dilogSeries : ContinuousOn dilogSeries (Metric.closedBall 0 1) := by
  unfold dilogSeries
  refine continuousOn_tsum (fun n ↦ ((continuous_pow _).div_const _).continuousOn)
    summable_one_div_succ_sq fun n z hz ↦ ?_
  exact norm_dilog_term_le (by simpa using hz) n

/-- On the closed disc, `Re z < 1` unless `z = 1`. -/
private theorem re_lt_one_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) (h1 : z ≠ 1) : z.re < 1 := by
  by_contra! h
  apply h1
  have h2 : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have := Complex.sq_norm z
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg z]
  have hre : z.re = 1 := by nlinarith [Complex.re_le_norm z]
  have him : z.im = 0 := by nlinarith
  exact Complex.ext hre him

/-- `arg(1 - z) log ‖z‖ → 0` as `z → 0`. -/
private theorem continuousAt_arg_mul_log_zero :
    ContinuousAt (fun z : ℂ ↦ Complex.arg (1 - z) * Real.log ‖z‖) 0 := by
  have hlim : Tendsto (fun z : ℂ ↦ 3 / 2 * |‖z‖ * Real.log ‖z‖|) (𝓝 0) (𝓝 0) := by
    have : Continuous (fun z : ℂ ↦ 3 / 2 * |‖z‖ * Real.log ‖z‖|) :=
      continuous_const.mul ((Real.continuous_mul_log.comp continuous_norm).abs)
    simpa using this.tendsto 0
  show Tendsto _ (𝓝 0) (𝓝 (Complex.arg (1 - 0) * Real.log ‖(0 : ℂ)‖))
  simp only [sub_zero, Complex.arg_one, zero_mul]
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  have harg : |Complex.arg (1 - z)| ≤ 3 / 2 * ‖z‖ := by
    have h := Complex.norm_log_one_add_half_le_self (z := -z) (by rwa [norm_neg])
    rw [norm_neg, ← sub_eq_add_neg] at h
    rw [← Complex.log_im]
    exact (Complex.abs_im_le_norm _).trans h
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_norm, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right harg (abs_nonneg _)

/-- `arg(1 - z) log ‖z‖ → 0` as `z → 1`. -/
private theorem continuousAt_arg_mul_log_one :
    ContinuousAt (fun z : ℂ ↦ Complex.arg (1 - z) * Real.log ‖z‖) 1 := by
  have hlim : Tendsto (fun z : ℂ ↦ Real.pi * |Real.log ‖z‖|) (𝓝 1) (𝓝 0) := by
    have : ContinuousAt (fun z : ℂ ↦ Real.pi * |Real.log ‖z‖|) 1 :=
      continuousAt_const.mul ((Real.continuousAt_log (by simp)).comp
        continuous_norm.continuousAt).abs
    simpa using this.tendsto
  show Tendsto _ (𝓝 1) (𝓝 (Complex.arg (1 - 1) * Real.log ‖(1 : ℂ)‖))
  simp only [norm_one, Real.log_one, mul_zero]
  refine squeeze_zero_norm (fun z ↦ ?_) hlim
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (Complex.abs_arg_le_pi _) (abs_nonneg _)

/-- The logarithmic term is continuous on the closed disc. -/
private theorem continuousOn_arg_mul_log :
    ContinuousOn (fun z : ℂ ↦ Complex.arg (1 - z) * Real.log ‖z‖) (Metric.closedBall 0 1) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  rcases eq_or_ne z 0 with rfl | h0
  · exact continuousAt_arg_mul_log_zero.continuousWithinAt
  rcases eq_or_ne z 1 with rfl | h1
  · exact continuousAt_arg_mul_log_one.continuousWithinAt
  have hslit : 1 - z ∈ Complex.slitPlane := by
    left
    rw [Complex.sub_re, Complex.one_re]
    linarith [re_lt_one_of_norm_le_one hz h1]
  refine ContinuousAt.continuousWithinAt ?_
  exact ((Complex.continuousAt_arg hslit).comp (by fun_prop)).mul
    ((Real.continuousAt_log (norm_ne_zero_iff.2 h0)).comp continuous_norm.continuousAt)

/-- The disc formula is continuous on the closed disc. -/
private theorem continuousOn_bwDiscFormula :
    ContinuousOn bwDiscFormula (Metric.closedBall 0 1) :=
  (Complex.continuous_im.comp_continuousOn continuousOn_dilogSeries).add continuousOn_arg_mul_log

/-- `Li₂(conj z) = conj Li₂(z)`. -/
private theorem dilogSeries_conj_cont (z : ℂ) :
    dilogSeries (starRingEnd ℂ z) = starRingEnd ℂ (dilogSeries z) := by
  unfold dilogSeries
  rw [Complex.conj_tsum]
  congr 1
  ext n
  simp [map_div₀, map_pow]

/-- On the unit circle the two branches agree. -/
private theorem bwDiscFormula_inv_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    bwDiscFormula z = -bwDiscFormula z⁻¹ := by
  have hinv : ‖z⁻¹‖ = 1 := by rw [norm_inv, hz, inv_one]
  unfold bwDiscFormula
  rw [hz, hinv, Complex.inv_eq_conj hz, dilogSeries_conj_cont, Complex.conj_im]
  simp

/-- `D(0) = 0`. -/
theorem geo_blochWigner_zero : blochWigner 0 = 0 := by
  simp [blochWigner, dilogSeries]

/-- `D(1) = 0`. -/
theorem geo_blochWigner_one : blochWigner 1 = 0 := by
  rw [blochWigner_eq_ite, ite_eq_left (by simp), bwDiscFormula, norm_one, Real.log_one,
    mul_zero, add_zero]
  unfold dilogSeries
  rw [Complex.im_tsum]
  · refine (tsum_congr fun n ↦ ?_).trans tsum_zero
    rw [one_pow, show ((n : ℂ) + 1) ^ 2 = (((n : ℝ) + 1) ^ 2 : ℝ) by push_cast; ring,
      ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_im]
  · refine Summable.of_norm_bounded summable_one_div_succ_sq fun n ↦ ?_
    exact norm_dilog_term_le (by simp) n

/-- The Bloch–Wigner dilogarithm is continuous on `ℂ`. -/
theorem geo_continuous_blochWigner : Continuous blochWigner := by
  have hset : {z : ℂ | ‖z‖ ≤ 1} = Metric.closedBall 0 1 := by ext; simp
  have hF : ContinuousOn bwDiscFormula {z : ℂ | ‖z‖ ≤ 1} := hset ▸ continuousOn_bwDiscFormula
  have hG : ContinuousOn (fun z ↦ -bwDiscFormula z⁻¹) {z : ℂ | 1 ≤ ‖z‖} := by
    refine (hF.comp (continuousOn_inv₀.mono fun z hz ↦ ?_) fun z hz ↦ ?_).neg
    · simp only [Set.mem_ofPred_eq] at hz
      simpa using (one_pos.trans_le hz).ne'
    · simp only [Set.mem_ofPred_eq, norm_inv] at hz ⊢
      exact inv_le_one_of_one_le₀ hz
  have h := continuous_if_le continuous_norm continuous_const hF hG
    fun z hz ↦ bwDiscFormula_inv_of_norm_eq_one hz
  exact h.congr fun z ↦ (blochWigner_eq_ite z).symm

/-- `D(z) → 0` as `z → ∞`: with `D(∞) = 0` the function is continuous on `ℙ¹(ℂ)`. -/
theorem geo_tendsto_blochWigner_cocompact :
    Tendsto blochWigner (cocompact ℂ) (𝓝 0) := by
  rw [← Metric.cobounded_eq_cocompact]
  have h1 : Tendsto (fun z : ℂ ↦ -blochWigner z⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := by
    have := (geo_continuous_blochWigner.tendsto 0).comp (tendsto_inv₀_cobounded (α := ℂ))
    rw [geo_blochWigner_zero] at this
    simpa using this.neg
  refine h1.congr' ?_
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 1] with z hz
  have hz' : ‖z⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hz.le
  rw [blochWigner_eq_ite, blochWigner_eq_ite, ite_eq_left hz', ite_eq_right (not_le.2 hz)]

end AJConjecture
