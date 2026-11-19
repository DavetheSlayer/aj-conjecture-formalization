import Mathlib
import AJFamily.VolumeDefs

/-!
# `log |E|` is integrable on the torus

Tonelli (`MeasureTheory.integrable_prod_iff`): the integrand is measurable, and for each `θ`
the inner integral `∫₀^{2π} |log |E(e^{iθ}, e^{iφ})|| dφ` is bounded uniformly in `θ`. The
fibre `p = E(e^{iθ}, ·)` is a monic polynomial with `|p| ≤ 8` on the unit circle, so writing
`|log x| = 2 log⁺ x - log x` and using `∫₀^{2π} log |p(e^{iφ})| dφ = 2π m(p) ≥ 0` (Jensen, in the
form `one_le_mahlerMeasure_of_one_le_norm_leadingCoeff`) gives the bound `4π log 8`.
-/

open Polynomial Real

noncomputable section

namespace AJConjecture

/-- Explicit value of `E(M, L)`. -/
private lemma evalPoint_extraFactorℂ_eq (M L : ℂ) :
    evalPoint extraFactorℂ (M, L) = L ^ 2 - (M ^ 4 - 4 * M ^ 2 + 1) * L + M ^ 4 := by
  simp [evalPoint, extraFactorℂ, extraFactor, eval₂_pow, eval₂_C]

/-- The fibre `E(M, ·)` of the extra factor at a fixed meridian value `M`. -/
private def extraFactorFiber (M : ℂ) : ℂ[X] :=
  X ^ 2 - C (M ^ 4 - 4 * M ^ 2 + 1) * X + C (M ^ 4)

/-- Evaluating the fibre `E(M, ·)` at `L`. -/
private lemma eval_extraFactorFiber (M L : ℂ) :
    (extraFactorFiber M).eval L = L ^ 2 - (M ^ 4 - 4 * M ^ 2 + 1) * L + M ^ 4 := by
  simp [extraFactorFiber]

/-- The fibre `E(M, ·)` is monic. -/
private lemma monic_extraFactorFiber (M : ℂ) : (extraFactorFiber M).Monic := by
  unfold extraFactorFiber
  monicity!

/-- On the unit torus, `|E(M, L)| ≤ 8`. -/
private lemma norm_eval_extraFactorFiber_le {M L : ℂ} (hM : ‖M‖ = 1) (hL : ‖L‖ = 1) :
    ‖(extraFactorFiber M).eval L‖ ≤ 8 := by
  have hB : ‖M ^ 4 - 4 * M ^ 2 + 1‖ ≤ 6 := by
    calc ‖M ^ 4 - 4 * M ^ 2 + 1‖ ≤ ‖M ^ 4‖ + ‖4 * M ^ 2‖ + ‖(1 : ℂ)‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ = 6 := by simp [norm_pow, hM]; norm_num
  rw [eval_extraFactorFiber]
  calc ‖L ^ 2 - (M ^ 4 - 4 * M ^ 2 + 1) * L + M ^ 4‖
        ≤ ‖L ^ 2‖ + ‖(M ^ 4 - 4 * M ^ 2 + 1) * L‖ + ‖M ^ 4‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ 1 + 6 + 1 := by
          rw [norm_mul, norm_pow, norm_pow, hM, hL]
          gcongr <;> norm_num [hB]
    _ = 8 := by norm_num

/-- For a monic `p` bounded by `B ≥ 1` on the unit circle,
`∫₀^{2π} |log |p(e^{iφ})|| dφ ≤ 4π log B`, by Jensen (`m(p) ≥ 0`). -/
private lemma intervalIntegral_abs_log_norm_eval_circleMap_le {p : ℂ[X]} (hp : p.Monic)
    {B : ℝ} (hB : 1 ≤ B) (hpB : ∀ φ : ℝ, ‖p.eval (circleMap 0 1 φ)‖ ≤ B) :
    ∫ φ in 0..2 * π, |Real.log ‖p.eval (circleMap 0 1 φ)‖| ≤
      2 * (2 * π) * Real.log B := by
  have hint := p.intervalIntegrable_mahlerMeasure
  have hpos : IntervalIntegrable (fun φ ↦ log⁺ ‖p.eval (circleMap 0 1 φ)‖)
      MeasureTheory.volume 0 (2 * π) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have habs : ∀ φ : ℝ, |Real.log ‖p.eval (circleMap 0 1 φ)‖| =
      2 * log⁺ ‖p.eval (circleMap 0 1 φ)‖ - Real.log ‖p.eval (circleMap 0 1 φ)‖ := by
    intro φ
    have := Real.half_mul_log_add_log_abs (x := ‖p.eval (circleMap 0 1 φ)‖)
    linarith
  have hmahler : 0 ≤ ∫ φ in 0..2 * π, Real.log ‖p.eval (circleMap 0 1 φ)‖ := by
    have h1 : 0 ≤ p.logMahlerMeasure := by
      rw [logMahlerMeasure_eq_log_MahlerMeasure]
      exact Real.log_nonneg
        (one_le_mahlerMeasure_of_one_le_norm_leadingCoeff (by simp [hp.leadingCoeff]))
    rw [logMahlerMeasure_def, circleAverage_def, smul_eq_mul] at h1
    exact nonneg_of_mul_nonneg_right h1 (by positivity)
  have hle : ∫ φ in 0..2 * π, log⁺ ‖p.eval (circleMap 0 1 φ)‖ ≤
      ∫ _ in 0..2 * π, Real.log B := by
    refine intervalIntegral.integral_mono_on (by positivity) hpos (by simp) fun φ _ ↦ ?_
    rw [← Real.posLog_eq_log (by rw [abs_of_nonneg (by linarith)]; exact hB)]
    exact Real.posLog_le_posLog (by linarith [norm_nonneg (p.eval (circleMap 0 1 φ))]) (hpB φ)
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hle
  have hsplit : ∫ φ in 0..2 * π, |Real.log ‖p.eval (circleMap 0 1 φ)‖| =
      2 * (∫ φ in 0..2 * π, log⁺ ‖p.eval (circleMap 0 1 φ)‖) -
        ∫ φ in 0..2 * π, Real.log ‖p.eval (circleMap 0 1 φ)‖ := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hpos.const_mul 2) hint]
    exact intervalIntegral.integral_congr fun φ _ ↦ habs φ
  rw [hsplit]
  linarith

/-- `log |E(e^{iθ}, e^{iφ})|` is integrable on `[0, 2π]²`. -/
theorem integrableOn_torusLogAbs_extraFactor :
    MeasureTheory.IntegrableOn (torusLogAbs extraFactorℂ) torusBox := by
  have hf : ∀ θ : ℝ × ℝ, torusLogAbs extraFactorℂ θ =
      Real.log
        ‖(extraFactorFiber (Complex.exp (θ.1 * Complex.I))).eval (circleMap 0 1 θ.2)‖ := by
    intro θ
    simp [torusLogAbs, torusPoint, evalPoint_extraFactorℂ_eq, eval_extraFactorFiber, circleMap]
  have hmeas : Measurable (torusLogAbs extraFactorℂ) := by
    have : torusLogAbs extraFactorℂ = fun θ : ℝ × ℝ ↦
        Real.log ‖Complex.exp (θ.2 * Complex.I) ^ 2 -
        (Complex.exp (θ.1 * Complex.I) ^ 4 - 4 * Complex.exp (θ.1 * Complex.I) ^ 2 + 1) *
          Complex.exp (θ.2 * Complex.I) + Complex.exp (θ.1 * Complex.I) ^ 4‖ := by
      funext θ
      simp [torusLogAbs, torusPoint, evalPoint_extraFactorℂ_eq]
    rw [this]
    exact Real.measurable_log.comp (by fun_prop : Continuous _).measurable
  unfold MeasureTheory.IntegrableOn torusBox
  rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
    MeasureTheory.integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun x ↦ ?_, ?_⟩
  · have := (extraFactorFiber (Complex.exp (x * Complex.I))).intervalIntegrable_mahlerMeasure
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity),
      ← integrableOn_Icc_iff_integrableOn_Ioc] at this
    simp only [hf]
    exact this
  · refine MeasureTheory.Integrable.of_bound
      hmeas.aestronglyMeasurable.norm.integral_prod_right' (2 * (2 * π) * Real.log 8)
      (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun _ ↦ norm_nonneg _),
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity)]
    simp only [hf, Real.norm_eq_abs]
    exact intervalIntegral_abs_log_norm_eval_circleMap_le (monic_extraFactorFiber _)
      (by norm_num) fun φ ↦ norm_eval_extraFactorFiber_le
        (by simp [Complex.norm_exp_ofReal_mul_I]) (by simp [circleMap])

end AJConjecture
