import Mathlib
import AJFamily.Volume.ArsinhAbsSinIntegral
import AJFamily.Volume.MahlerFubini
import AJFamily.Volume.MahlerIntegrable
import AJFamily.Volume.MahlerSlice

/-!
# The Mahler measure of the extra factor is `4G/π`

`m(E) = (2π)⁻¹ ∫₀^{2π} 2 arsinh|sin θ| dθ = (2π)⁻¹ · 8G = 4G/π`: Fubini
(`logMahlerMeasure₂_eq_integral`, with `integrableOn_torusLogAbs_extraFactor`), Jensen on each
slice (`logMahlerMeasure_extraFactor_slice`) and `integral_two_arsinh_abs_sin`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `log |E|` is integrable on the torus and `m(E) = 4G/π`. -/
theorem mahlerMeasure_extraFactor :
    MeasureTheory.IntegrableOn (torusLogAbs extraFactorℂ) torusBox ∧
      logMahlerMeasure₂ extraFactorℂ = 4 * catalanConstant / Real.pi := by
  refine ⟨integrableOn_torusLogAbs_extraFactor, ?_⟩
  rw [logMahlerMeasure₂_eq_integral _ integrableOn_torusLogAbs_extraFactor]
  simp_rw [logMahlerMeasure_extraFactor_slice]
  rw [integral_two_arsinh_abs_sin]
  field_simp
  ring

end AJConjecture
