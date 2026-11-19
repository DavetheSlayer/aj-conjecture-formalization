import Mathlib
import AJFamily.Volume.ArctanCatalan
import AJFamily.Volume.WhiteheadComplete
import AJHandoff.Geometry.GeoBlochWignerInvolution
import AJHandoff.Geometry.GeoShapeRep

/-!
# Signed, mirror and unsigned volumes of the Whitehead slice (G-VOL)

The signed shape volume of the four-tetrahedron structure is `∑ D(z_j)`. Along the completed slice
`(w, -1/w, w, -1/w)` it is `2D(w) + 2D(-1/w) = 2[D(w) - D(-w)] = 2U(w)`; with
`w = (1 - r)/(1 + r)` (geometry_v2 (9), the shape parameter of the point with normalization
parameter `r`) it equals `-2U(r)`, the normalized critical action `V_S` of `GeoAction`. For
`Im w > 0` all four shapes are positively oriented; at `w = i` they are four right-isosceles
tetrahedra and the volume is `4G`, at `w = -i` it is `-4G`.

Orientation reversal replaces each oriented shape `z` by `1/z` (an odd permutation of the vertices,
`GeoVolumeOriented`), so the mirror-oriented pullback of a shape assignment has signed volume
`∑ D(1/z_j) = -∑ D(z_j)`: `-4G` for the pullback of the `w = i` structure to the source mirror
orientation, while the positive structure of the mirror is the conjugate branch `w = -i`. The
unsigned volume of every complete structure is `|∑ D(z_j)| = 4G`.

What stays interpretation: that the triangulation with these gluing equations is an ideal
triangulation of the two-cusped Whitehead link exterior, that the complete positive solution is its
hyperbolic structure (Thurston, Tillmann), and that the volume of an ideal tetrahedron of shape `z`
is `D(z)` (for shape `i` this is `GeoVolumeHyperbolic`). The satellite exterior has a further
(companion) piece; no volume is asserted for it. The square-weave value `8G` is the difference
`4G - (-4G)` of the normalized primitive `-2U` between the two branches over a node, not the
Whitehead volume.

Route. `geo_blochWigner_inv` (`D(-1/w) = -D(-w)`); `geo_regPrimitive_cayley`;
`whiteheadGluing_complete_iff` and `blochWigner_I`, `geo_blochWigner_neg_I`.
-/

noncomputable section

namespace AJConjecture

/-- The signed shape volume along the completed slice is `2U(w) = 2[D(w) - D(-w)]`. -/
theorem geo_slice_signedVolume {w : ℂ} (hw0 : w ≠ 0) :
    ∑ j, blochWigner (geoSliceShapes w j) = 2 * geoRegPrimitive w := by
  have h : blochWigner (-1 / w) = -blochWigner (-w) := by
    rw [show -1 / w = (-w)⁻¹ by rw [inv_neg, neg_div, one_div]]
    exact geo_blochWigner_inv (neg_ne_zero.2 hw0)
  simp only [Fin.sum_univ_four, geoSliceShapes, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, h,
    geoRegPrimitive]
  ring

/-- With `w = (1 - r)/(1 + r)`, the signed volume is `-2U(r) = V_S`. -/
theorem geo_slice_signedVolume_eq_action {r : ℂ} (hr : r ≠ -1) (hr1 : r ≠ 1) :
    ∑ j, blochWigner (geoSliceShapes ((1 - r) / (1 + r)) j) = -2 * geoRegPrimitive r := by
  have hr' : (1 : ℂ) + r ≠ 0 := fun h ↦ hr (by linear_combination h)
  have hr1' : (1 : ℂ) - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
  rw [geo_slice_signedVolume (div_ne_zero hr1' hr'), geo_regPrimitive_cayley hr]
  ring

/-- For `Im w > 0` all four slice shapes are positively oriented. -/
theorem geo_slice_positive {w : ℂ} (hw : 0 < w.im) : ∀ j, 0 < (geoSliceShapes w j).im := by
  have hw0 : w ≠ 0 := fun h ↦ by simp [h] at hw
  have h : 0 < (-1 / w).im := by
    rw [neg_div, Complex.neg_im, one_div, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hw (Complex.normSq_pos.2 hw0)
  intro j
  fin_cases j
  · exact hw
  · exact h
  · exact hw
  · exact h

/-- The complete branches: signed volume `4G` at `w = i` and `-4G` at `w = -i`. -/
theorem geo_slice_complete_volumes :
    ∑ j, blochWigner (geoSliceShapes Complex.I j) = 4 * catalanConstant ∧
      ∑ j, blochWigner (geoSliceShapes (-Complex.I) j) = -(4 * catalanConstant) := by
  rw [geo_slice_signedVolume Complex.I_ne_zero,
    geo_slice_signedVolume (neg_ne_zero.2 Complex.I_ne_zero)]
  simp only [geoRegPrimitive, neg_neg, blochWigner_I, geo_blochWigner_neg_I]
  constructor <;> ring

/-- The mirror-oriented pullback: reversing the orientation of every tetrahedron (shape `z ↦ 1/z`)
negates the signed volume; for the complete positive structure it is `-4G`. -/
theorem geo_mirror_signedVolume (z : Fin 4 → ℂ) (hz : ∀ j, z j ≠ 0) :
    ∑ j, blochWigner (z j)⁻¹ = -∑ j, blochWigner (z j) ∧
      ∑ j, blochWigner (geoSliceShapes Complex.I j)⁻¹ = -(4 * catalanConstant) := by
  have hmirror : ∀ z : Fin 4 → ℂ, (∀ j, z j ≠ 0) →
      ∑ j, blochWigner (z j)⁻¹ = -∑ j, blochWigner (z j) := by
    intro z hz
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ geo_blochWigner_inv (hz j)
  refine ⟨hmirror z hz, ?_⟩
  rw [hmirror _ fun j ↦ ?_, geo_slice_complete_volumes.1]
  fin_cases j
  · exact Complex.I_ne_zero
  · simp [geoSliceShapes]
  · exact Complex.I_ne_zero
  · simp [geoSliceShapes]

/-- The unsigned volume of every complete structure is `4G`. -/
theorem geo_unsigned_volume (z : Fin 4 → ℂ) (hg : WhiteheadGluing z) (hc : WhiteheadComplete z) :
    |∑ j, blochWigner (z j)| = 4 * catalanConstant := by
  have hG : 0 ≤ catalanConstant := by
    rw [← integral_arctan_div_self]
    exact intervalIntegral.integral_nonneg zero_le_one fun a ha ↦
      div_nonneg (Real.arctan_nonneg.2 ha.1) ha.1
  rcases (whiteheadGluing_complete_iff z).1 ⟨hg, hc⟩ with rfl | rfl
  · simp only [Fin.sum_const, blochWigner_I, nsmul_eq_mul]
    rw [abs_of_nonneg (by positivity)]
    norm_num
  · simp only [Fin.sum_const, geo_blochWigner_neg_I,
      nsmul_eq_mul]
    rw [abs_of_nonpos (by push_cast; linarith)]
    norm_num

end AJConjecture
