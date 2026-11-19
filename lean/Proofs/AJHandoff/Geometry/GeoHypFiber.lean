import Mathlib

/-!
# The vertical fibre of the ideal tetrahedron of shape `i`

Over a point `p` at squared distance `s < 1/2` from the centre `(1 + i)/2`, the ideal tetrahedron
contains the heights `t ≥ h` with `h² = 1/2 - s`, and `∫_h^∞ t⁻³ dt = 1/(2h²) = 1/(1 - 2s)`.
-/

open MeasureTheory Set

noncomputable section

namespace AJConjecture

/-- The hyperbolic length element `t⁻³ dt` integrated over the heights above the hemisphere of
squared radius `1/2` at a point at squared distance `s < 1/2` from its centre. -/
theorem hypFiber_lintegral {s : ℝ} (hs : s < 1 / 2) :
    ∫⁻ t in {t : ℝ | 0 < t ∧ 1 / 2 ≤ s + t ^ 2}, ENNReal.ofReal (t ^ (-3 : ℤ)) =
      ENNReal.ofReal (1 / (1 - 2 * s)) := by
  set h := √(1 / 2 - s) with hh
  have hpos : 0 < h := Real.sqrt_pos.2 (by linarith)
  have hsq : h ^ 2 = 1 / 2 - s := Real.sq_sqrt (by linarith)
  have hset : {t : ℝ | 0 < t ∧ 1 / 2 ≤ s + t ^ 2} = Ici h := by
    ext t
    simp only [mem_ofPred_eq, mem_Ici]
    constructor
    · rintro ⟨ht, h2⟩
      exact (Real.sqrt_le_left ht.le).2 (by linarith)
    · intro ht
      refine ⟨hpos.trans_le ht, ?_⟩
      nlinarith
  have hrpow : ∀ t : ℝ, t ^ (-3 : ℤ) = t ^ (-3 : ℝ) := fun t ↦ by
    rw [← Real.rpow_intCast]
    norm_num
  simp_rw [hset, hrpow]
  rw [setLIntegral_congr Ioi_ae_eq_Ici.symm, ← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hpos), integral_Ioi_rpow_of_lt (by norm_num) hpos]
  · congr 1
    rw [show (-3 : ℝ) + 1 = -2 by norm_num, Real.rpow_neg hpos.le,
      Real.rpow_two, hsq]
    have : 1 - 2 * s ≠ 0 := by linarith
    have : 1 / 2 - s ≠ 0 := by linarith
    field_simp
  · exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦
      Real.rpow_nonneg (hpos.trans ht).le _

end AJConjecture
