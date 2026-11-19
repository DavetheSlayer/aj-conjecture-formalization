import Mathlib
import AJFamily.VolumeDefs
import AJHandoff.Geometry.GeoMarkGroups

/-!
# The holonomy representation of the completed Whitehead slice (G-SHAPE)

For `w ∉ {0, 1, -1}` the shapes `(w, -1/w, w, -1/w)` (`geoSliceShapes`) solve Tillmann's gluing
equations with the axis cusp completed, `meridian₀² = 1`, `longitude₀ = -1`. For a square root `u`
of `meridian₁² = (1 + w)/(w(1 - w))` the matrices

  `A₀ = [[1, -(1 + w)/w], [0, 1]]`, `B₀/u = [[u, 0], [u⁻¹, u⁻¹]]`

(Tillmann's `GL₂` model `B₀ = [[ū, 0], [1, 1]]` divided by `u`, an `SL₂` lift) satisfy the relation
of `GeoTillmannGroup`, giving `geoShapeRep w u : GeoTillmannGroup →* SL₂(ℂ)`. The longitudes map
to triangular matrices: `λ₀ ↦ [[-1, 2(w² - 2w - 1)/(w(1 - w))], [0, -1]]`,
`λ₁ ↦ [[w², 0], [*, w⁻²]]`. Hence the eigenvalue coordinates of the representation,
`((A₀)₀₀², ρ(λ₀)₀₀, ρ(b)₀₀², ρ(λ₁)₀₀) = (1, -1, (1 + w)/(w(1 - w)), w²)`, are exactly Tillmann's
holonomy coordinates `whiteheadPeripheral` of the shapes: the library's triangulation coordinates
are the eigenvalues of an actual representation. The axis meridian is nontrivially parabolic
(`-(1 + w)/w ≠ 0`).

What stays interpretation: that `geoShapeRep` is the holonomy of the hyperbolic structure built from
these ideal tetrahedra (the developing map), and that the triangulation is one of the `W⁺`
complement.

Route. All statements are identities of `2 × 2` matrices with entries in `ℚ(w, u)` subject to
`u² = (1 + w)/(w(1 - w))`: expand the words (`Matrix.mul_fin_two`), `field_simp`,
`linear_combination` with `hu` (checked numerically at three values of `w`).
-/

open Matrix

noncomputable section

namespace AJConjecture

/-- The completed slice shapes `(w, -1/w, w, -1/w)`. -/
def geoSliceShapes (w : ℂ) : Fin 4 → ℂ := ![w, -1 / w, w, -1 / w]

/-- The slice shapes solve the gluing equations with the axis cusp completed. -/
theorem geo_sliceShapes_gluing {w : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1) :
    WhiteheadGluing (geoSliceShapes w) ∧
      whiteheadPeripheral (geoSliceShapes w) = (1, -1, (1 + w) / (w * (1 - w)), w ^ 2) := by
  have hb0 : -1 / w ≠ 0 := by simpa using hw0
  have hb1 : -1 / w ≠ 1 := by
    intro h
    field_simp at h
    exact hwm1 (by linear_combination -h)
  have w1' : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have wp1 : w + 1 ≠ 0 := fun h ↦ hwm1 (by linear_combination h)
  refine ⟨⟨fun j ↦ ?_, ?_, ?_⟩, ?_⟩
  · fin_cases j
    · exact ⟨hw0, hw1⟩
    · exact ⟨hb0, hb1⟩
    · exact ⟨hw0, hw1⟩
    · exact ⟨hb0, hb1⟩
  · simp only [geoSliceShapes, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    field_simp
  · simp only [geoSliceShapes, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    field_simp
  · simp only [whiteheadPeripheral, shapePrime, shapeDoublePrime, geoSliceShapes,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · field_simp
      ring
    · field_simp
    · field_simp
      ring
    · ring

/-- `u ≠ 0` for a square root of `(1 + w)/(w(1 - w))`, `w ∉ {0, 1, -1}`. -/
theorem geo_shape_u_ne_zero {w u : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1)
    (hu : u ^ 2 = (1 + w) / (w * (1 - w))) : u ≠ 0 := by
  rintro rfl
  have w1' : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have wp1 : 1 + w ≠ 0 := fun h ↦ hwm1 (by linear_combination h)
  have h0 : (1 + w) / (w * (1 - w)) ≠ 0 := div_ne_zero wp1 (mul_ne_zero hw0 w1')
  exact h0 (by rw [← hu]; ring)

/-- The axis meridian matrix `A₀ = [[1, -(1 + w)/w], [0, 1]]`. -/
def geoShapeA (w : ℂ) : SpecialLinearGroup (Fin 2) ℂ :=
  ⟨!![1, -(1 + w) / w; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- The outer meridian matrix `B₀/u = [[u, 0], [u⁻¹, u⁻¹]]`. -/
def geoShapeB (u : ℂ) (hu : u ≠ 0) : SpecialLinearGroup (Fin 2) ℂ :=
  ⟨!![u, 0; u⁻¹, u⁻¹], by simp [Matrix.det_fin_two, hu]⟩

/-- The matrix of `A₀`. -/
private theorem geo_shapeA_coe (w : ℂ) :
    ((geoShapeA w : SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1, -(1 + w) / w; 0, 1] := rfl

/-- The matrix of `A₀⁻¹`. -/
private theorem geo_shapeA_inv_coe (w : ℂ) :
    (((geoShapeA w)⁻¹ : SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1, (1 + w) / w; 0, 1] := by
  change Matrix.adjugate !![1, -(1 + w) / w; 0, 1] = _
  rw [Matrix.adjugate_fin_two_of]
  simp only [neg_div, neg_neg, neg_zero]

/-- The matrix of `B₀/u`. -/
private theorem geo_shapeB_coe (u : ℂ) (hu : u ≠ 0) :
    ((geoShapeB u hu : SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![u, 0; u⁻¹, u⁻¹] := rfl

/-- The matrix of `(B₀/u)⁻¹`. -/
private theorem geo_shapeB_inv_coe (u : ℂ) (hu : u ≠ 0) :
    (((geoShapeB u hu)⁻¹ : SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![u⁻¹, 0; -u⁻¹, u] := by
  change Matrix.adjugate !![u, 0; u⁻¹, u⁻¹] = _
  rw [Matrix.adjugate_fin_two_of]
  simp only [neg_zero]

/-- The matrices satisfy Tillmann's relation. -/
theorem geo_shapeRep_rel {w u : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1)
    (hu : u ^ 2 = (1 + w) / (w * (1 - w))) :
    FreeGroup.lift (![geoShapeA w, geoShapeB u (geo_shape_u_ne_zero hw0 hw1 hwm1 hu)] :
      Fin 2 → SpecialLinearGroup (Fin 2) ℂ) geoTilRel = 1 := by
  have hu0 := geo_shape_u_ne_zero hw0 hw1 hwm1 hu
  simp only [geoTilRel, map_mul, map_inv, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [mul_inv_eq_one]
  have w1' : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hu' : u ^ 2 * (w * (1 - w)) = 1 + w := by rw [hu]; field_simp
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, geo_shapeA_coe, geo_shapeA_inv_coe,
    geo_shapeB_coe, geo_shapeB_inv_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp
    field_simp
    linear_combination (-w^2 - 2*w - 1) * hu'
  · simp
    field_simp
    linear_combination (u^2*w^2 + 2*u^2*w + u^2 - w^2 - 2*w - 1) * hu'
  · simp
    field_simp
    ring
  · simp
    field_simp
    linear_combination (w^2 + 2*w + 1) * hu'

/-- The holonomy representation of the completed slice point `(w, u)`. -/
def geoShapeRep (w u : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1)
    (hu : u ^ 2 = (1 + w) / (w * (1 - w))) :
    GeoTillmannGroup →* SpecialLinearGroup (Fin 2) ℂ :=
  PresentedGroup.toGroup (by rintro r rfl; exact geo_shapeRep_rel hw0 hw1 hwm1 hu)

/-- The peripheral images: `λ₀` upper triangular with diagonal `(-1, -1)`, `λ₁` lower triangular
with diagonal `(w², w⁻²)`. -/
theorem geo_shapeRep_peripheral {w u : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1)
    (hu : u ^ 2 = (1 + w) / (w * (1 - w))) :
    let ρ := geoShapeRep w u hw0 hw1 hwm1 hu
    (ρ geoTilA : Matrix (Fin 2) (Fin 2) ℂ) = !![1, -(1 + w) / w; 0, 1] ∧
      (ρ geoTilB : Matrix (Fin 2) (Fin 2) ℂ) = !![u, 0; u⁻¹, u⁻¹] ∧
      (ρ geoTilLong0 : Matrix (Fin 2) (Fin 2) ℂ) =
        !![-1, 2 * (w ^ 2 - 2 * w - 1) / (w * (1 - w)); 0, -1] ∧
      (ρ geoTilLong1 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 ∧
      (ρ geoTilLong1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = w ^ 2 ∧
      (ρ geoTilLong1 : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = (w ^ 2)⁻¹ := by
  intro ρ
  have hu0 := geo_shape_u_ne_zero hw0 hw1 hwm1 hu
  have w1' : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hu' : u ^ 2 * (w * (1 - w)) = 1 + w := by rw [hu]; field_simp
  have hA : ρ geoTilA = geoShapeA w := PresentedGroup.toGroup.of _
  have hB : ρ geoTilB = geoShapeB u hu0 := PresentedGroup.toGroup.of _
  have hL0 : (ρ geoTilLong0 : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1, (1 + w) / w; 0, 1] * !![u, 0; u⁻¹, u⁻¹] * !![1, -(1 + w) / w; 0, 1] *
        !![u⁻¹, 0; -u⁻¹, u] * !![1, (1 + w) / w; 0, 1] * !![u⁻¹, 0; -u⁻¹, u] *
        !![1, -(1 + w) / w; 0, 1] * !![u, 0; u⁻¹, u⁻¹] := by
    simp only [geoTilLong0, map_mul, map_inv, hA, hB, Matrix.SpecialLinearGroup.coe_mul,
      geo_shapeA_coe, geo_shapeA_inv_coe, geo_shapeB_coe, geo_shapeB_inv_coe]
  have hL1 : (ρ geoTilLong1 : Matrix (Fin 2) (Fin 2) ℂ) =
      !![u⁻¹, 0; -u⁻¹, u] * !![1, -(1 + w) / w; 0, 1] * !![u, 0; u⁻¹, u⁻¹] *
        !![1, (1 + w) / w; 0, 1] * !![u⁻¹, 0; -u⁻¹, u] * !![1, (1 + w) / w; 0, 1] *
        !![u, 0; u⁻¹, u⁻¹] * !![1, -(1 + w) / w; 0, 1] := by
    simp only [geoTilLong1, map_mul, map_inv, hA, hB, Matrix.SpecialLinearGroup.coe_mul,
      geo_shapeA_coe, geo_shapeA_inv_coe, geo_shapeB_coe, geo_shapeB_inv_coe]
  refine ⟨by rw [hA]; rfl, by rw [hB]; rfl, ?_, ?_, ?_, ?_⟩
  · rw [hL0]
    simp only [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · simp
      field_simp
      linear_combination (-2*u^2*w^2 - u^2*w - w^2 - 2*w - 1) * hu'
    · simp
      field_simp
      linear_combination
        (-u^4*w^3 - u^4*w^2 + 3*u^2*w^3 - u^2*w^2 - 2*u^2*w + w^3 + w^2 - w - 1) * hu'
    · simp
      field_simp
      linear_combination (-w - 1) * hu'
    · simp
      field_simp
      linear_combination (-u^2*w - w - 1) * hu'
  · rw [hL1]
    simp only [Matrix.mul_fin_two]
    simp
    field_simp
    linear_combination (w^2 + 2*w + 1) * hu'
  · rw [hL1]
    simp only [Matrix.mul_fin_two]
    simp
    field_simp
    linear_combination (u^2*w^3 + u^2*w^2 - w^2 - 2*w - 1) * hu'
  · rw [hL1]
    simp only [Matrix.mul_fin_two]
    simp
    field_simp
    linear_combination (-u^2*w^2 - u^2*w - w^2 - 2*w - 1) * hu'

/-- The library's holonomy coordinates of the slice shapes are the eigenvalue coordinates of the
representation. -/
theorem geo_shapeRep_holonomy {w u : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1)
    (hu : u ^ 2 = (1 + w) / (w * (1 - w))) :
    let ρ := geoShapeRep w u hw0 hw1 hwm1 hu
    whiteheadPeripheral (geoSliceShapes w) =
      ((ρ geoTilA : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^ 2,
        (ρ geoTilLong0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0,
        (ρ geoTilB : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^ 2,
        (ρ geoTilLong1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
  intro ρ
  obtain ⟨h1, h2, h3, -, h5, -⟩ := geo_shapeRep_peripheral hw0 hw1 hwm1 hu
  simp only [ρ, (geo_sliceShapes_gluing hw0 hw1 hwm1).2, h1, h2, h3, h5]
  simp [hu]

end AJConjecture
