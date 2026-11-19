import Mathlib
import AJFamily.VolumeDefs

/-!
# The complete solutions of the Whitehead gluing equations

The nondegenerate solutions of the gluing equations with both cusps complete are exactly the two
constant tuples `(i, i, i, i)` and `(-i, -i, -i, -i)`. From `longitude₀² = 1` and
`meridian₀² = 1`: the sign `longitude₀ = 1` forces `w = 1`, and `longitude₀ = -1` gives
`(w, -1/w, w, -1/w)`; then `meridian₁² = (1 + w)/(w(1 - w)) = 1` gives `w² = -1`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A constant tuple `(c, c, c, c)` with `c² = -1` is a complete solution. -/
private theorem complete_const (c : ℂ) (hc : c ^ 2 = -1) :
    WhiteheadGluing (fun _ ↦ c) ∧ WhiteheadComplete (fun _ ↦ c) := by
  have c0 : c ≠ 0 := by rintro rfl; norm_num at hc
  have c1 : c ≠ 1 := by rintro rfl; norm_num at hc
  have c1' : (1 : ℂ) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm c1)
  refine ⟨⟨fun _ ↦ ⟨c0, c1⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · linear_combination (c ^ 2 - 1) * hc
  · ring
  · simp only [whiteheadPeripheral, shapePrime, shapeDoublePrime]
    field_simp
    linear_combination (c - 1) * hc
  · simp only [whiteheadPeripheral]
    linear_combination (c ^ 2 - 1) * hc
  · simp only [whiteheadPeripheral, shapePrime, shapeDoublePrime]
    field_simp
    linear_combination (c - 1) * hc
  · simp only [whiteheadPeripheral]
    linear_combination (c ^ 2 - 1) * hc

/-- The complete nondegenerate solutions are `(i, i, i, i)` and `(-i, -i, -i, -i)`. -/
theorem whiteheadGluing_complete_iff (z : Fin 4 → ℂ) :
    WhiteheadGluing z ∧ WhiteheadComplete z ↔
      z = (fun _ ↦ Complex.I) ∨ z = (fun _ ↦ -Complex.I) := by
  constructor
  · rintro ⟨⟨hnd, hprod, hglue⟩, h0, ht, hu, -⟩
    obtain ⟨w0, w1⟩ := hnd 0
    obtain ⟨a0, a1⟩ := hnd 1
    obtain ⟨b0, b1⟩ := hnd 2
    obtain ⟨c0, c1⟩ := hnd 3
    simp only [whiteheadPeripheral, shapePrime, shapeDoublePrime] at h0 ht hu
    have ha1 : (1 : ℂ) - z 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm a1)
    have hw1 : (1 : ℂ) - z 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm w1)
    have h0' : z 3 - 1 = (1 - z 1) * z 3 * z 2 := by
      field_simp at h0
      linear_combination h0
    have hu' : z 3 - 1 = (1 - z 0) * z 3 * z 2 := by
      field_simp at hu
      linear_combination hu
    have ht' : z 1 * z 2 = 1 ∨ z 1 * z 2 = -1 := by
      have : (z 1 * z 2 - 1) * (z 1 * z 2 + 1) = 0 := by linear_combination ht
      rcases mul_eq_zero.1 this with h | h
      · left; linear_combination h
      · right; linear_combination h
    rcases ht' with h1 | h1
    · exfalso
      have hwc : z 0 * z 3 = 1 := by linear_combination hprod - z 0 * z 3 * h1
      have k1 : z 1 * (z 1 - 1) * (1 - z 3) = (z 3 - 1) * (1 - z 1) * z 3 := by
        linear_combination (z 1 * z 3) * hglue +
          ((1 - z 3) * z 1 + (z 3 - 1) * (1 - z 1) * z 3) * h1 +
          (-(z 1) ^ 2 * (1 - z 2) * (1 - z 3) - (1 - z 1) * z 3 * z 1 * z 2) * hwc
      have hfac : (z 1 - 1) * (1 - z 3) * (z 1 - z 3) = 0 := by linear_combination k1
      have hz13 : z 1 = z 3 := by
        rcases mul_eq_zero.1 hfac with h | h
        · rcases mul_eq_zero.1 h with h | h
          · exact absurd (sub_eq_zero.1 h) a1
          · exact absurd (sub_eq_zero.1 h).symm c1
        · exact sub_eq_zero.1 h
      have : 2 * (z 1 - 1) = 0 := by
        linear_combination h0' + (1 - (1 - z 1) * z 2) * hz13 - (z 1 - 1) * h1
      exact a1 (by linear_combination this / 2)
    · have h23 : z 2 * z 3 = -1 := by linear_combination -h0' + z 3 * h1
      have hz13 : z 1 = z 3 := by
        have : z 2 * (z 1 - z 3) = 0 := by linear_combination h1 - h23
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left b0)
      have hz02 : z 0 = z 2 := by
        have : z 3 * (z 0 - z 2) = 0 := by
          linear_combination z 0 * z 3 * h1 - hprod - h23
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left c0)
      have hz30 : z 3 = z 0 := by linear_combination hu' + (1 - z 0) * h23
      have hz10 : z 1 = z 0 := hz13.trans hz30
      have hsq : z 0 ^ 2 = -1 := by
        rw [hz10, ← hz02] at h1
        linear_combination h1
      have hall : z = fun _ ↦ z 0 := by
        funext j
        fin_cases j
        · rfl
        · exact hz10
        · exact hz02.symm
        · exact hz30
      have hroot : (z 0 - Complex.I) * (z 0 + Complex.I) = 0 := by
        linear_combination hsq - Complex.I_sq
      rcases mul_eq_zero.1 hroot with h | h
      · left
        rw [hall, sub_eq_zero.1 h]
      · right
        rw [hall, eq_neg_of_add_eq_zero_left h]
  · rintro (h | h) <;> subst h
    · exact complete_const _ Complex.I_sq
    · exact complete_const _ (by rw [neg_sq, Complex.I_sq])
end AJConjecture
