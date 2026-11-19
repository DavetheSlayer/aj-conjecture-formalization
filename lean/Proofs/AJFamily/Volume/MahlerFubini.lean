import Mathlib
import AJFamily.VolumeDefs

/-!
# The Mahler measure of two variables as an iterated circle average

For an integrand integrable on `[0, 2π]²`, Fubini turns the normalised double integral into the
average over `θ` of the one-variable logarithmic Mahler measures of `L ↦ P(e^{iθ}, L)`
(`Polynomial.logMahlerMeasure` is `circleAverage (log ‖eval · p‖) 0 1`, and
`circleMap 0 1 φ = e^{iφ}`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Fubini for the two-variable Mahler measure. -/
theorem logMahlerMeasure₂_eq_integral (P : ℂ[X][X])
    (hP : MeasureTheory.IntegrableOn (torusLogAbs P) torusBox) :
    logMahlerMeasure₂ P = (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (P.map (Polynomial.evalRingHom (Complex.exp (θ * Complex.I)))).logMahlerMeasure := by
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  unfold logMahlerMeasure₂
  unfold torusBox at hP ⊢
  rw [MeasureTheory.Measure.volume_eq_prod] at hP ⊢
  rw [MeasureTheory.setIntegral_prod _ hP]
  have inner : ∀ θ : ℝ, ∫ φ in Set.Icc (0 : ℝ) (2 * Real.pi), torusLogAbs P (θ, φ) =
      2 * Real.pi *
        (P.map (Polynomial.evalRingHom (Complex.exp (θ * Complex.I)))).logMahlerMeasure := by
    intro θ
    rw [Polynomial.logMahlerMeasure_def, Real.circleAverage_def, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hπ, one_mul, intervalIntegral.integral_of_le h2π,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
    congr 1
    funext φ
    simp [torusLogAbs, torusPoint, evalPoint, circleMap_zero, Polynomial.eval_map]
  simp_rw [inner]
  rw [MeasureTheory.integral_const_mul, intervalIntegral.integral_of_le h2π,
    MeasureTheory.integral_Icc_eq_integral_Ioc]
  field_simp
  simp_rw [mul_comm Complex.I]

end AJConjecture
