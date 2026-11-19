import Mathlib
import AJFamily.Volume.ExtraFactorEval

/-!
# The completed Whitehead slice lies on the extra factor

If the first cusp is complete in the sense `meridian₀² = 1`, `longitude₀ = -1`, the shapes are
`(w, -1/w, w, -1/w)` with `w ∉ {0, ±1}`, the second cusp has `meridian₁² = (1 + w)/(w(1 - w))`
and `longitude₁ = w²`, and `B₊(u, v) = u⁴v² - (u⁴ - 4u² + 1)v + 1 = v² E(u, v⁻¹)` vanishes for
`u² = meridian₁²`, `v = w²`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The completed slice maps into `E = 0` with `M = u`, `L = longitude₁⁻¹`. -/
theorem whitehead_slice_mem_extraFactor (z : Fin 4 → ℂ) (hz : WhiteheadGluing z)
    (h0 : (whiteheadPeripheral z).1 = 1) (h1 : (whiteheadPeripheral z).2.1 = -1) (u : ℂ)
    (hu : u ^ 2 = (whiteheadPeripheral z).2.2.1) :
    evalPoint extraFactorℂ (u, ((whiteheadPeripheral z).2.2.2)⁻¹) = 0 := by
  obtain ⟨hnd, hprod, -⟩ := hz
  obtain ⟨w0, w1⟩ := hnd 0
  obtain ⟨a0, a1⟩ := hnd 1
  obtain ⟨b0, b1⟩ := hnd 2
  obtain ⟨c0, c1⟩ := hnd 3
  simp only [whiteheadPeripheral, shapePrime, shapeDoublePrime] at h0 h1 hu ⊢
  rw [evalPoint_extraFactorℂ]
  simp only
  have ha1 : (1 : ℂ) - z 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm a1)
  have hw1 : (1 : ℂ) - z 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm w1)
  -- b = -1/a
  have hb : z 2 = -1 / z 1 := by field_simp; linear_combination h1
  -- a = c from h0
  have hac : z 3 = z 1 := by
    rw [hb] at h0
    field_simp at h0
    linear_combination -h0
  -- w = b
  have hw : z 0 = z 2 := by
    rw [hac, hb] at hprod
    rw [hb]
    field_simp at hprod ⊢
    linear_combination -hprod
  have hu2 : u ^ 2 = (1 + z 0) / (z 0 * (1 - z 0)) := by
    rw [hu, hac]
    have : z 1 = -1 / z 0 := by rw [hw, hb]; field_simp
    rw [this, hw]
    field_simp
    ring
  have h4 : u ^ 4 = ((1 + z 0) / (z 0 * (1 - z 0))) ^ 2 := by rw [← hu2]; ring
  rw [show u ^ 4 = ((1 + z 0) / (z 0 * (1 - z 0))) ^ 2 from h4, hu2, hw]
  rw [hw] at w0 w1 hw1
  field_simp
  ring

end AJConjecture
