import Mathlib
import AJFamily.VolumeDefs
import AJHandoff.Geometry.GeoShapeRep

/-!
# G-SHAPE: on the completed chart all shapes are `(w, -1/w, w, -1/w)`

A solution of the gluing equations of the four-tetrahedron Whitehead triangulation whose first
cusp is complete (meridian derivative `1`, longitude eigenvalue `-1`) has shapes
`(w, -1/w, w, -1/w)` for some `w ∉ {0, 1, -1}`. This is the converse half of the slice description
(the forward half is `geo_sliceShapes_gluing`).
-/

namespace AJConjecture

/-- With the first cusp completed, all shapes are `(w, -1/w, w, -1/w)`. -/
theorem geo_sliceShapes_of_complete (z : Fin 4 → ℂ) (hz : WhiteheadGluing z)
    (h1 : (whiteheadPeripheral z).1 = 1) (h2 : (whiteheadPeripheral z).2.1 = -1) :
    ∃ w : ℂ, w ≠ 0 ∧ w ≠ 1 ∧ w ≠ -1 ∧ z = geoSliceShapes w := by
  obtain ⟨hnd, hprod, -⟩ := hz
  obtain ⟨w0, w1⟩ := hnd 0
  obtain ⟨a0, a1⟩ := hnd 1
  obtain ⟨c0, c1⟩ := hnd 3
  simp only [whiteheadPeripheral, shapePrime, shapeDoublePrime] at h1 h2
  have ha1 : (1 : ℂ) - z 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm a1)
  have hc1 : (1 : ℂ) - z 3 ≠ 0 := sub_ne_zero.mpr (Ne.symm c1)
  have hb : z 2 = -1 / z 1 := by field_simp; linear_combination h2
  have hac : z 3 = z 1 := by
    rw [hb] at h1
    field_simp at h1
    linear_combination -h1
  have hw : z 0 = z 2 := by
    rw [hac, hb] at hprod
    rw [hb]
    field_simp at hprod ⊢
    linear_combination -hprod
  have h1' : z 1 = -1 / z 0 := by rw [hw, hb]; field_simp
  refine ⟨z 0, w0, w1, fun h ↦ a1 (by rw [h1', h]; norm_num), ?_⟩
  funext j
  fin_cases j
  · rfl
  · exact h1'
  · exact hw.symm
  · exact hac.trans h1'

end AJConjecture
