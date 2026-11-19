import Mathlib
import AJFamily.Volume.WhiteheadSlice
import AJFamily.Volume.WhiteheadSliceConverse
import AJHandoff.Geometry.GeoMarkPattern
import AJHandoff.Geometry.GeoShapeRep
import AJHandoff.Geometry.GeoSliceShapes

/-!
# `M = u`, `L = v⁻¹` derived from the marking (G-SHAPE, marking part; MARK geometric part)

Pull the holonomy representation of the completed slice back to the library's pattern group,
`ρ_{w,u} = geoShapeRep w u ∘ geoPatToTil` (`geoPatternShapeRep`). Then:

* the axis is completed: the axis meridian `m` and axis longitude `c` have a common eigenvector
  with eigenvalues `ε` (`ε² = 1`) and `-1`, the meridian nontrivially parabolic;
* the pattern meridian `p` and the pattern's preferred longitude `l` (the library knot's
  meridian and longitude, `geo_pattern_to_knotGroup`) have common eigenvectors with eigenvalue
  pairs `(u, w⁻²)` and `(u⁻¹, w²)`, i.e. `(M, L) = (u, v⁻¹)` or `(u⁻¹, v)` with `v = w²` the
  Tillmann longitude coordinate — the identification the source obtained by correcting the
  unchanged longitude, here forced by the library's own peripheral words;
* the set of all such eigenvalue pairs over the chart is exactly `E ∩ {M ≠ 0}`;
* over each node `(ε, -1)` there are exactly the two lifts `w = ±i` (with `u = ε`): the four lifts
  at the two nodes, one per normalized branch;
* the unchanged identification fails: at `w = 2`, `u² = -3/2`, `E(u, v) = E(u, 4) = -75/4 ≠ 0`.

Route. `geo_pattern_tillmann` and `geo_shapeRep_peripheral` give `ρ(p) = B₀/u` (lower triangular)
and `ρ(l) = ρ(b)² ρ(λ₁)⁻¹ ρ(b)⁻²` (lower triangular, diagonal `(w⁻², w²)`): the vector `e₂` is a
common eigenvector (conjugate by `[[0, 1], [-1, 0]]`); for `u² ≠ 1` the `u`-eigenvector
`(u² - 1, 1)` of `B₀/u` is a second one (conjugate by `[[u² - 1, 0], [1, (u² - 1)⁻¹]]`), and
`ρ(l)` preserves it since it commutes with `ρ(p)`. If `u² = 1` then `w² = -1` and both pairs
coincide. The image: `whitehead_slice_mem_extraFactor` and `exists_whitehead_slice_of_extraFactor`
(with `geo_sliceShapes_gluing`). Nodes: `(u, w⁻²) = (ε, -1)` or `(u⁻¹, w²) = (ε, -1)` forces
`w² = -1`, `u = ε`.
-/

open Matrix

noncomputable section

namespace AJConjecture

/-- The holonomy representation of the completed slice, pulled back to the pattern group. -/
def geoPatternShapeRep (w u : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1)
    (hu : u ^ 2 = (1 + w) / (w * (1 - w))) :
    GeoPatternGroup →* SpecialLinearGroup (Fin 2) ℂ :=
  (geoShapeRep w u hw0 hw1 hwm1 hu).comp geoPatToTil

/-- `(M, L)` is an eigenvalue pair of the pattern meridian and longitude on a common eigenvector:
after conjugation both are upper triangular with diagonal entries `M`, `L` in position `(0, 0)`
(the convention of `eigenvalueSet`). -/
def GeoPatternEigenPair (ρ : GeoPatternGroup →* SpecialLinearGroup (Fin 2) ℂ) (p : ℂ × ℂ) :
    Prop :=
  ∃ g : SpecialLinearGroup (Fin 2) ℂ,
    ((g⁻¹ * ρ geoPatMer * g : SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 ∧
    ((g⁻¹ * ρ geoPatLong * g : SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 ∧
    ((g⁻¹ * ρ geoPatMer * g : SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = p.1 ∧
    ((g⁻¹ * ρ geoPatLong * g : SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = p.2

/-- The axis cusp is completed: a common eigenvector of the axis meridian and axis longitude with
eigenvalues `ε` (`ε² = 1`) and `-1`, the meridian nontrivially parabolic. -/
def GeoAxisCompleted (ρ : GeoPatternGroup →* SpecialLinearGroup (Fin 2) ℂ) : Prop :=
  ∃ g : SpecialLinearGroup (Fin 2) ℂ,
    let A := ((g⁻¹ * ρ geoPatAxisMer * g : SpecialLinearGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ)
    let C := ((g⁻¹ * ρ geoPatAxisLong * g : SpecialLinearGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ)
    A 1 0 = 0 ∧ C 1 0 = 0 ∧ A 0 0 ^ 2 = 1 ∧ C 0 0 = -1 ∧ A 0 1 ≠ 0

/-- The `(1, 0)` and `(0, 0)` entries of a conjugate `g⁻¹ X g` in `SL₂(ℂ)`. -/
private theorem geo_sl_conj_entries (g X : SpecialLinearGroup (Fin 2) ℂ) :
    ((g⁻¹ * X * g : SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
        -(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 *
            ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 +
              (X : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) +
          (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 *
            ((X : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 +
              (X : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ∧
      ((g⁻¹ * X * g : SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
        (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 *
            ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 +
              (X : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) -
          (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 *
            ((X : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 +
              (X : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  constructor <;> simp <;> ring

/-- The pattern meridian goes to `B₀/u`. -/
private theorem geo_patternShapeRep_mer {w u : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1)
    (hu : u ^ 2 = (1 + w) / (w * (1 - w))) :
    ((geoPatternShapeRep w u hw0 hw1 hwm1 hu geoPatMer : SpecialLinearGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = !![u, 0; u⁻¹, u⁻¹] := by
  rw [geoPatternShapeRep, MonoidHom.comp_apply, geo_pattern_tillmann.2.2.1]
  exact (geo_shapeRep_peripheral hw0 hw1 hwm1 hu).2.1

/-- The pattern longitude goes to `ρ(λ₁)⁻¹`. -/
private theorem geo_patternShapeRep_long {w u : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1)
    (hwm1 : w ≠ -1) (hu : u ^ 2 = (1 + w) / (w * (1 - w))) :
    geoPatternShapeRep w u hw0 hw1 hwm1 hu geoPatLong =
      (geoShapeRep w u hw0 hw1 hwm1 hu geoTilLong1)⁻¹ := by
  have hc : geoTilB ^ 2 * geoTilLong1⁻¹ = geoTilLong1⁻¹ * geoTilB ^ 2 :=
    ((geo_tillmann_peripheral.2.pow_left 2).inv_right).eq
  rw [geoPatternShapeRep, MonoidHom.comp_apply, geo_pattern_tillmann.2.2.2.2.1, hc,
    mul_inv_cancel_right, map_inv]

/-- The axis meridian goes to `A₀⁻¹`, the axis longitude to `A₀ ρ(λ₀) A₀⁻¹`. -/
private theorem geo_patternShapeRep_axis {w u : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1)
    (hwm1 : w ≠ -1) (hu : u ^ 2 = (1 + w) / (w * (1 - w))) :
    geoPatternShapeRep w u hw0 hw1 hwm1 hu geoPatAxisMer =
        (geoShapeRep w u hw0 hw1 hwm1 hu geoTilA)⁻¹ ∧
      geoPatternShapeRep w u hw0 hw1 hwm1 hu geoPatAxisLong =
        geoShapeRep w u hw0 hw1 hwm1 hu geoTilA * geoShapeRep w u hw0 hw1 hwm1 hu geoTilLong0 *
          (geoShapeRep w u hw0 hw1 hwm1 hu geoTilA)⁻¹ := by
  simp only [geoPatternShapeRep, MonoidHom.comp_apply, geo_pattern_tillmann.2.2.2.1,
    geo_pattern_tillmann.2.2.2.2.2, map_mul, map_inv, and_self]

/-- The eigenvalue pairs of the pattern representation are exactly `(u, w⁻²)` and `(u⁻¹, w²)`. -/
private theorem geo_patternEigenPair_iff {w u : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1)
    (hu : u ^ 2 = (1 + w) / (w * (1 - w))) (p : ℂ × ℂ) :
    GeoPatternEigenPair (geoPatternShapeRep w u hw0 hw1 hwm1 hu) p ↔
      p = (u, (w ^ 2)⁻¹) ∨ p = (u⁻¹, w ^ 2) := by
  have hu0 := geo_shape_u_ne_zero hw0 hw1 hwm1 hu
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw0
  obtain ⟨-, hB, -, hL01, hL00, hL11⟩ := geo_shapeRep_peripheral hw0 hw1 hwm1 hu
  have hX := geo_patternShapeRep_mer hw0 hw1 hwm1 hu
  have hY : ((geoPatternShapeRep w u hw0 hw1 hwm1 hu geoPatLong : SpecialLinearGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) =
        !![(w ^ 2)⁻¹, 0; -((geoShapeRep w u hw0 hw1 hwm1 hu geoTilLong1 :
          SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0, w ^ 2] := by
    rw [geo_patternShapeRep_long]
    change Matrix.adjugate _ = _
    rw [Matrix.adjugate_fin_two, hL01, hL00, hL11, neg_zero]
  have hc := congrArg (fun x : SpecialLinearGroup (Fin 2) ℂ ↦ (x : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
    ((geo_tillmann_peripheral.2).map (geoShapeRep w u hw0 hw1 hwm1 hu)).eq
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hB,
    hL00, hL11] at hc
  generalize ((geoShapeRep w u hw0 hw1 hwm1 hu geoTilLong1 : SpecialLinearGroup (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ) 1 0 = t at hY hc
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at hc
  obtain ⟨g0, hg0⟩ : ∃ g0 : SpecialLinearGroup (Fin 2) ℂ,
      (g0 : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0] :=
    ⟨⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩, rfl⟩
  have hswap : GeoPatternEigenPair (geoPatternShapeRep w u hw0 hw1 hwm1 hu) (u⁻¹, w ^ 2) := by
    refine ⟨g0, ?_⟩
    simp only [(geo_sl_conj_entries _ _).1, (geo_sl_conj_entries _ _).2, hX, hY, hg0]
    simp
  constructor
  · rintro ⟨g, h1, h2, h3, h4⟩
    simp only [(geo_sl_conj_entries _ _).1, (geo_sl_conj_entries _ _).2, hX, hY] at h1 h2 h3 h4
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at h1 h2 h3 h4
    have hdet : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 -
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 1 := by
      rw [← Matrix.det_fin_two]
      exact g.prop
    generalize (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = a at *
    generalize (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = b at *
    generalize (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = c at *
    generalize (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = d at *
    by_cases ha : a = 0
    · subst ha
      right
      refine Prod.ext ?_ ?_
      · linear_combination -h3 + u⁻¹ * hdet
      · linear_combination -h4 + w ^ 2 * hdet
    · left
      have hX' : -c * u + u⁻¹ * a + u⁻¹ * c = 0 :=
        (mul_eq_zero.1 (by linear_combination h1 :
          a * (-c * u + u⁻¹ * a + u⁻¹ * c) = 0)).resolve_left ha
      have hY' : -c * (w ^ 2)⁻¹ - t * a + w ^ 2 * c = 0 :=
        (mul_eq_zero.1 (by linear_combination h2 :
          a * (-c * (w ^ 2)⁻¹ - t * a + w ^ 2 * c) = 0)).resolve_left ha
      refine Prod.ext ?_ ?_
      · linear_combination -h3 + u * hdet - b * hX'
      · linear_combination -h4 + (w ^ 2)⁻¹ * hdet - b * hY'
  · rintro (rfl | rfl)
    · by_cases hu1 : u ^ 2 = 1
      · have w1' : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
        have hwsq : w ^ 2 = -1 := by
          rw [hu1] at hu
          field_simp at hu
          linear_combination -hu
        have e1 : u⁻¹ = u := by
          field_simp
          linear_combination -hu1
        have e : (u, (w ^ 2)⁻¹) = (u⁻¹, w ^ 2) := by
          rw [e1, hwsq]
          norm_num
        rw [e]
        exact hswap
      · have hs : u ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hu1
        obtain ⟨g1, hg1⟩ : ∃ g1 : SpecialLinearGroup (Fin 2) ℂ,
            (g1 : Matrix (Fin 2) (Fin 2) ℂ) = !![u ^ 2 - 1, 0; 1, (u ^ 2 - 1)⁻¹] :=
          ⟨⟨!![u ^ 2 - 1, 0; 1, (u ^ 2 - 1)⁻¹], by simp [Matrix.det_fin_two, hs]⟩, rfl⟩
        refine ⟨g1, ?_⟩
        simp only [(geo_sl_conj_entries _ _).1, (geo_sl_conj_entries _ _).2, hX, hY, hg1]
        have hinv : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one]
        refine ⟨?_, ?_, ?_, ?_⟩
        · linear_combination (u ^ 2 - 1) * u * hinv
        · linear_combination (u ^ 2 - 1) * u * hc - (u ^ 2 - 1) * (w ^ 2 + t - (w ^ 2)⁻¹) * hinv
        · field_simp
          ring
        · field_simp
          ring
    · exact hswap

/-- G-SHAPE marking: completed axis, the two eigenvalue pairs `(u, v⁻¹)`, `(u⁻¹, v)` with
`v = w²`, and `E(u, v⁻¹) = 0`. -/
theorem geo_shape_marking {w u : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1)
    (hu : u ^ 2 = (1 + w) / (w * (1 - w))) :
    GeoAxisCompleted (geoPatternShapeRep w u hw0 hw1 hwm1 hu) ∧
      GeoPatternEigenPair (geoPatternShapeRep w u hw0 hw1 hwm1 hu) (u, (w ^ 2)⁻¹) ∧
      GeoPatternEigenPair (geoPatternShapeRep w u hw0 hw1 hwm1 hu) (u⁻¹, w ^ 2) ∧
      evalPoint extraFactorℂ (u, (w ^ 2)⁻¹) = 0 := by
  obtain ⟨hA, -, hL0, -⟩ := geo_shapeRep_peripheral hw0 hw1 hwm1 hu
  obtain ⟨hm, hc⟩ := geo_patternShapeRep_axis hw0 hw1 hwm1 hu
  obtain ⟨hg, hper⟩ := geo_sliceShapes_gluing hw0 hw1 hwm1
  have hwp : (1 : ℂ) + w ≠ 0 := fun h ↦ hwm1 (by linear_combination h)
  refine ⟨⟨1, ?_⟩, (geo_patternEigenPair_iff hw0 hw1 hwm1 hu _).2 (Or.inl rfl),
    (geo_patternEigenPair_iff hw0 hw1 hwm1 hu _).2 (Or.inr rfl), ?_⟩
  · have hAinv : (((geoShapeRep w u hw0 hw1 hwm1 hu geoTilA)⁻¹ : SpecialLinearGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = !![1, (1 + w) / w; 0, 1] := by
      change Matrix.adjugate _ = _
      rw [hA, Matrix.adjugate_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, neg_div, neg_neg, neg_zero]
    simp only [inv_one, one_mul, mul_one, hm, hc, Matrix.SpecialLinearGroup.coe_mul, hAinv, hA,
      hL0, Matrix.mul_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    exact ⟨trivial, by ring, by ring, by ring, div_ne_zero hwp hw0⟩
  · have h := whitehead_slice_mem_extraFactor (geoSliceShapes w) hg (by rw [hper])
      (by rw [hper]) u (by rw [hper]; exact hu)
    rwa [hper] at h

/-- The eigenvalue pairs of the pattern over the whole completed chart are exactly the points of
`E` with `M ≠ 0`. -/
theorem geo_shape_marking_image :
    {p : ℂ × ℂ | ∃ (w u : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1)
        (hu : u ^ 2 = (1 + w) / (w * (1 - w))),
        GeoPatternEigenPair (geoPatternShapeRep w u hw0 hw1 hwm1 hu) p} =
      {p : ℂ × ℂ | evalPoint extraFactorℂ p = 0 ∧ p.1 ≠ 0} := by
  ext ⟨M, L⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, u, hw0, hw1, hwm1, hu, hp⟩
    have hu0 := geo_shape_u_ne_zero hw0 hw1 hwm1 hu
    have hE := (geo_shape_marking hw0 hw1 hwm1 hu).2.2.2
    rcases (geo_patternEigenPair_iff hw0 hw1 hwm1 hu _).1 hp with h | h <;>
      simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
      refine ⟨?_, by simpa using hu0⟩
    · exact hE
    · rw [evalPoint_extraFactorℂ] at hE ⊢
      simp only at hE ⊢
      have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw0
      have key : ((w ^ 2) ^ 2 - ((u⁻¹) ^ 4 - 4 * (u⁻¹) ^ 2 + 1) * w ^ 2 + (u⁻¹) ^ 4) *
          (u ^ 4 * ((w ^ 2)⁻¹) ^ 2) =
          ((w ^ 2)⁻¹) ^ 2 - (u ^ 4 - 4 * u ^ 2 + 1) * (w ^ 2)⁻¹ + u ^ 4 := by
        field_simp
        ring
      rw [hE] at key
      exact (mul_eq_zero.1 key).resolve_right (by positivity)
  · rintro ⟨hE, h0⟩
    obtain ⟨z, hz, h1, h2, h3, h4⟩ := exists_whitehead_slice_of_extraFactor (M, L) hE h0
    obtain ⟨w, hw0, hw1, hwm1, rfl⟩ := geo_sliceShapes_of_complete z hz h1 h2
    rw [(geo_sliceShapes_gluing hw0 hw1 hwm1).2] at h3 h4
    simp only at h3 h4
    refine ⟨w, M, hw0, hw1, hwm1, h3.symm, (geo_patternEigenPair_iff _ _ _ _ _).2 (Or.inl ?_)⟩
    rw [h4, inv_inv]

/-- The lifts at a node `(ε, -1)`: exactly `(w, u) = (i, ε)` and `(-i, ε)`. -/
theorem geo_shape_node_lifts (ε : ℂ) (hε : ε = 1 ∨ ε = -1) :
    {q : ℂ × ℂ | ∃ (hw0 : q.1 ≠ 0) (hw1 : q.1 ≠ 1) (hwm1 : q.1 ≠ -1)
        (hu : q.2 ^ 2 = (1 + q.1) / (q.1 * (1 - q.1))),
        GeoPatternEigenPair (geoPatternShapeRep q.1 q.2 hw0 hw1 hwm1 hu) (ε, -1)} =
      {(Complex.I, ε), (-Complex.I, ε)} := by
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  ext ⟨w, u⟩
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hw0, hw1, hwm1, hu, hp⟩
    have hu0 := geo_shape_u_ne_zero hw0 hw1 hwm1 hu
    have key : w ^ 2 = -1 ∧ u = ε := by
      rcases (geo_patternEigenPair_iff hw0 hw1 hwm1 hu _).1 hp with h | h <;>
        simp only [Prod.mk.injEq] at h <;> obtain ⟨h1, h2⟩ := h
      · refine ⟨?_, h1.symm⟩
        rw [← inv_inv (w ^ 2), ← h2]
        norm_num
      · refine ⟨h2.symm, ?_⟩
        have : u * ε = 1 := by rw [h1, mul_inv_cancel₀ hu0]
        linear_combination ε * this - u * hε2
    obtain ⟨hw, rfl⟩ := key
    have : (w - Complex.I) * (w + Complex.I) = 0 := by
      linear_combination hw - Complex.I_sq
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl ⟨by linear_combination h, rfl⟩
    · exact Or.inr ⟨by linear_combination h, rfl⟩
  · have hI : (1 : ℂ) + Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
    have hI' : (1 : ℂ) - Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨Complex.I_ne_zero, ?_, ?_, ?_, ?_⟩
      · intro h
        have := congrArg Complex.im h
        simp at this
      · intro h
        have := congrArg Complex.im h
        simp at this
      · rw [hε2, eq_div_iff (mul_ne_zero Complex.I_ne_zero hI')]
        linear_combination -Complex.I_sq
      · refine (geo_patternEigenPair_iff _ _ _ _ _).2 (Or.inl ?_)
        simp
    · refine ⟨neg_ne_zero.2 Complex.I_ne_zero, ?_, ?_, ?_, ?_⟩
      · intro h
        have := congrArg Complex.im h
        simp at this
      · intro h
        have := congrArg Complex.im h
        simp at this
      · rw [hε2, eq_div_iff (mul_ne_zero (neg_ne_zero.2 Complex.I_ne_zero) (by
          rw [sub_neg_eq_add]; exact hI))]
        linear_combination -Complex.I_sq
      · refine (geo_patternEigenPair_iff _ _ _ _ _).2 (Or.inl ?_)
        simp

/-- The unchanged-longitude identification fails: at `w = 2`, `u² = -3/2`, `v = 4`,
`E(u, v) = -75/4`. -/
theorem geo_unchanged_marking_fails {u : ℂ} (hu : u ^ 2 = -3 / 2) :
    evalPoint extraFactorℂ (u, 4) = -75 / 4 := by
  rw [evalPoint_extraFactorℂ]
  linear_combination (-3 * (u ^ 2 - 3 / 2) + 16) * hu

end AJConjecture
