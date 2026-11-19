import Mathlib
import AJFamily.Volume.ExtraFactorEval
import AJFamily.Volume.WhiteheadComplete

/-!
# Every point of the extra factor with `M ≠ 0` comes from the completed slice

For `(u, L)` on `E` with `u ≠ 0`, `u² ≠ 1`: `L ≠ 0`; put `v = L⁻¹` and
`w = (u²v + 1)/(u² - 1)`. Then `w ∉ {0, ±1}` (the resultants of `w - c`, `c ∈ {0, ±1}`, with
`B₊(u, v)` are `u²(u² - 1)²` up to units and powers of `u`), the shapes `(w, -1/w, w, -1/w)`
satisfy the gluing equations, and `(1 + w)/(w(1 - w)) = u²`, `w² = v` modulo `B₊`. If
`u² = 1` then `E(u, L) = (L + 1)²`, so `L = -1`, and the complete solution `(i, i, i, i)`, with
holonomy coordinates `(1, -1, 1, -1)`, realises the point.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The tuple `(w, -1/w, w, -1/w)` of the completed slice. -/
private noncomputable def sliceShapes (w : ℂ) : Fin 4 → ℂ :=
  fun j ↦ if (j : ℕ) % 2 = 0 then w else -1 / w

private theorem sliceShapes_zero (w : ℂ) : sliceShapes w 0 = w := rfl
private theorem sliceShapes_one (w : ℂ) : sliceShapes w 1 = -1 / w := rfl
private theorem sliceShapes_two (w : ℂ) : sliceShapes w 2 = w := rfl
private theorem sliceShapes_three (w : ℂ) : sliceShapes w 3 = -1 / w := rfl

/-- The slice shapes satisfy the gluing equations. -/
private theorem sliceShapes_gluing (w : ℂ) (w0 : w ≠ 0) (w1 : w ≠ 1) (wm1 : w ≠ -1) :
    WhiteheadGluing (sliceShapes w) := by
  have hb0 : -1 / w ≠ 0 := by simpa using w0
  have hb1 : -1 / w ≠ 1 := by
    intro h
    field_simp at h
    exact wm1 (by linear_combination -h)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact ⟨w0, w1⟩
    · exact ⟨hb0, hb1⟩
    · exact ⟨w0, w1⟩
    · exact ⟨hb0, hb1⟩
  · rw [sliceShapes_zero, sliceShapes_one, sliceShapes_two, sliceShapes_three]
    field_simp
  · rw [sliceShapes_zero, sliceShapes_one, sliceShapes_two, sliceShapes_three]
    field_simp

/-- The holonomy coordinates of the slice shapes. -/
private theorem sliceShapes_peripheral (w : ℂ) (w0 : w ≠ 0) (w1 : w ≠ 1) (wm1 : w ≠ -1) :
    whiteheadPeripheral (sliceShapes w) = (1, -1, (1 + w) / (w * (1 - w)), w ^ 2) := by
  have w1' : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm w1)
  have wp1 : w + 1 ≠ 0 := by intro h; exact wm1 (by linear_combination h)
  simp only [whiteheadPeripheral, shapePrime, shapeDoublePrime, sliceShapes_zero,
    sliceShapes_one, sliceShapes_two, sliceShapes_three, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
  · field_simp
    ring
  · ring

/-- The completed slice covers `E = 0` away from `M = 0`. -/
theorem exists_whitehead_slice_of_extraFactor (p : ℂ × ℂ) (hp : evalPoint extraFactorℂ p = 0)
    (h0 : p.1 ≠ 0) :
    ∃ z : Fin 4 → ℂ, WhiteheadGluing z ∧ (whiteheadPeripheral z).1 = 1 ∧
      (whiteheadPeripheral z).2.1 = -1 ∧ (whiteheadPeripheral z).2.2.1 = p.1 ^ 2 ∧
      (whiteheadPeripheral z).2.2.2 = p.2⁻¹ := by
  obtain ⟨u, L⟩ := p
  simp only at h0 ⊢
  rw [evalPoint_extraFactorℂ] at hp
  simp only at hp
  by_cases hu1 : u ^ 2 = 1
  · have h4 : u ^ 4 = 1 := by rw [show u ^ 4 = (u ^ 2) ^ 2 by ring, hu1]; norm_num
    have hL : L = -1 := by
      have hsq : (L + 1) ^ 2 = 0 := by rw [h4, hu1] at hp; linear_combination hp
      linear_combination pow_eq_zero_iff two_ne_zero |>.1 hsq
    obtain ⟨hg, hc1, -, hc3, hc4⟩ :=
      (whiteheadGluing_complete_iff (fun _ ↦ Complex.I)).2 (Or.inl rfl)
    refine ⟨fun _ ↦ Complex.I, hg, hc1, ?_, ?_, ?_⟩
    · simp [whiteheadPeripheral]
    · rw [hc3, hu1]
    · simp [whiteheadPeripheral, hL]
  · have hL0 : L ≠ 0 := by
      rintro rfl
      apply h0
      exact pow_eq_zero_iff (n := 4) (by norm_num) |>.1 (by linear_combination hp)
    obtain ⟨x, hx⟩ : ∃ x, x = u ^ 2 := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v, v = L⁻¹ := ⟨_, rfl⟩
    have hx1 : x - 1 ≠ 0 := by rw [hx]; exact sub_ne_zero.mpr hu1
    have hx0 : x ≠ 0 := by rw [hx]; exact pow_ne_zero 2 h0
    have hB : x ^ 2 * v ^ 2 - (x ^ 2 - 4 * x + 1) * v + 1 = 0 := by
      rw [hx, hv]
      field_simp
      linear_combination hp
    obtain ⟨w, hw⟩ : ∃ w, w = (x * v + 1) / (x - 1) := ⟨_, rfl⟩
    have hw' : w * (x - 1) = x * v + 1 := by rw [hw]; field_simp
    have w0 : w ≠ 0 := by
      intro h
      have h' : x * v + 1 = 0 := by rw [← hw', h, zero_mul]
      have : (x - 1) ^ 2 = 0 := by
        linear_combination x * hB + (1 - 3 * x + x ^ 2 - x ^ 2 * v) * h'
      exact hx1 (pow_eq_zero_iff two_ne_zero |>.1 this)
    have w1 : w ≠ 1 := by
      intro h
      have h' : x * v - x + 2 = 0 := by rw [h] at hw'; linear_combination -hw'
      have : (x - 1) ^ 2 = 0 := by
        linear_combination (1 / 2 : ℂ) * x * hB + (1 / 2 - x - (1 / 2) * x ^ 2 * v) * h'
      exact hx1 (pow_eq_zero_iff two_ne_zero |>.1 this)
    have wm1 : w ≠ -1 := by
      intro h
      have h' : v + 1 = 0 := by
        rw [h] at hw'
        have : x * (v + 1) = 0 := by linear_combination -hw'
        exact (mul_eq_zero.1 this).resolve_left hx0
      have : 2 * (x - 1) ^ 2 = 0 := by
        linear_combination hB - (x ^ 2 * (v - 1) - x ^ 2 + 4 * x - 1) * h'
      exact hx1 (pow_eq_zero_iff two_ne_zero |>.1
        ((mul_eq_zero.1 this).resolve_left two_ne_zero))
    have w1' : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm w1)
    have ht : (x - 1) ^ 2 * ((1 + w) - x * w * (1 - w)) = 0 := by
      linear_combination x * hB +
        ((x - 1) - x * (x - 1) + x * (w * (x - 1) + (x * v + 1))) * hw'
    have ht' : (1 + w) / (w * (1 - w)) = x := by
      have := (mul_eq_zero.1 ht).resolve_left (pow_ne_zero 2 hx1)
      field_simp
      linear_combination this
    have hv' : (x - 1) ^ 2 * (w ^ 2 - v) = 0 := by
      linear_combination hB + (w * (x - 1) + (x * v + 1)) * hw'
    have hv'' : w ^ 2 = v := by
      linear_combination (mul_eq_zero.1 hv').resolve_left (pow_ne_zero 2 hx1)
    refine ⟨sliceShapes w, sliceShapes_gluing w w0 w1 wm1, ?_⟩
    rw [sliceShapes_peripheral w w0 w1 wm1]
    exact ⟨rfl, rfl, by rw [ht', hx], by rw [hv'', hv]⟩
end AJConjecture
