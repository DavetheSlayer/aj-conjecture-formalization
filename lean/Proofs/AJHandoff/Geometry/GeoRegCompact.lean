import Mathlib
import AJHandoff.Geometry.GeoRegulator
import AJHandoff.Geometry.GeoNormMap

/-!
# The regulator primitive on the compact normalization (G-REG-COMPACT)

`U = D(r) - D(-r)` extends continuously to `ℙ¹(ℂ)` (`geoRegPrimitiveP1`, value `0` at `∞`). Its
pullback `Ũ ∘ π` along the double cover `π : (X, Y) ↦ -X` is a continuous function on the compact
smooth projective model `GeoEllipticPoints`. On the punctured model off the four points over the
nodes it is `U ∘ r ∘ ν`, the primitive of `η(M, L)` on the smooth torus locus (`r(ν(X, Y)) = -X`).
It vanishes above the four punctures `r = 0, 1, -1, ∞` and equals `±2G` above `r = ±i`; each node
`(±1, -1)` has one preimage over `r = i` and one over `r = -i`, so `U ∘ r` has no limit at a node
along `E`: no single value is assigned at either singular affine point.

Route. Continuity: `OnePoint` continuity at `∞` from `geo_tendsto_regPrimitive_cocompact`, and
`geo_continuous_coverR`. Agreement: `geoCurveR (geoNormMap (X, Y)) = -X` on the punctured model
with `X² ≠ -1` (algebra). Values: `geo_regPrimitive_values`. No limit at the node: approach
`(1, -1)` along the images of the two branches `r → i` and `r → -i`
(`geo_mem_smoothTorusLocus_of_param`), where `U` tends to `2G ≠ -2G`.
-/

open Filter Topology

noncomputable section

namespace AJConjecture

/-- The continuous extension of `U` to `ℙ¹(ℂ)`, with `U(∞) = 0`. -/
def geoRegPrimitiveP1 (z : OnePoint ℂ) : ℝ :=
  Option.elim z 0 geoRegPrimitive

/-- `Ũ` is continuous on `ℙ¹(ℂ)`. -/
theorem geo_continuous_regPrimitiveP1 : Continuous geoRegPrimitiveP1 := by
  rw [OnePoint.continuous_iff, coclosedCompact_eq_cocompact]
  exact ⟨geo_tendsto_regPrimitive_cocompact, geo_continuous_regPrimitive⟩

/-- On the punctured model off the node fibres, `ν` lands in the smooth torus locus with
parameter `r = -X`. -/
private theorem geo_normMap_mem_smooth {q : ℂ × ℂ} (hq : q ∈ GeoPuncturedModel)
    (hX : q.1 ^ 2 ≠ -1) :
    geoNormMap q ∈ GeoSmoothTorusLocus ∧ geoCurveR (geoNormMap q) = -q.1 := by
  obtain ⟨hbij, hinv⟩ := geo_weierstrass_birational
  have hw : q ∈ GeoWeierstrassOpen := ⟨hq.1, hq.2, hX⟩
  obtain ⟨p, hp, rfl⟩ := hbij.surjOn hw
  have hpq : geoNormMap (geoToWeierstrass p) = p := hinv.1 hp
  rw [hpq]
  exact ⟨hp, by simp [geoToWeierstrass]⟩

/-- G-REG-COMPACT: `Ũ ∘ π` is continuous on the compact model, agrees with `U ∘ r ∘ ν` on the
punctured model off the fibres over the nodes, vanishes over the four punctures and takes the
values `±2G` over `r = ±i`. -/
theorem geo_regCompact :
    Continuous (geoRegPrimitiveP1 ∘ geoCoverR) ∧
      (∀ q ∈ GeoPuncturedModel, q.1 ^ 2 ≠ -1 →
        geoNormMap q ∈ GeoSmoothTorusLocus ∧
          geoRegPrimitive (geoCurveR (geoNormMap q)) = geoRegPrimitiveP1 (-q.1 : ℂ)) ∧
      (∀ P : GeoEllipticPoints, (geoCoverR P = ((0 : ℂ) : OnePoint ℂ) ∨
          geoCoverR P = ((1 : ℂ) : OnePoint ℂ) ∨ geoCoverR P = ((-1 : ℂ) : OnePoint ℂ) ∨
          geoCoverR P = OnePoint.infty) → geoRegPrimitiveP1 (geoCoverR P) = 0) ∧
      (∀ P : GeoEllipticPoints, geoCoverR P = (Complex.I : OnePoint ℂ) →
        geoRegPrimitiveP1 (geoCoverR P) = 2 * catalanConstant) ∧
      (∀ P : GeoEllipticPoints, geoCoverR P = ((-Complex.I : ℂ) : OnePoint ℂ) →
        geoRegPrimitiveP1 (geoCoverR P) = -(2 * catalanConstant)) := by
  obtain ⟨h0, h1, hm1, hI, hmI⟩ := geo_regPrimitive_values
  refine ⟨geo_continuous_regPrimitiveP1.comp geo_continuous_coverR, fun q hq hX ↦ ?_,
    fun P hP ↦ ?_, fun P hP ↦ ?_, fun P hP ↦ ?_⟩
  · obtain ⟨hs, hr⟩ := geo_normMap_mem_smooth hq hX
    exact ⟨hs, by rw [hr]; rfl⟩
  · rcases hP with hP | hP | hP | hP <;> rw [hP]
    · exact h0
    · exact h1
    · exact hm1
    · rfl
  · rw [hP]; exact hI
  · rw [hP]; exact hmI

/-- `x(r)` is continuous off `r = 0, 1`. -/
private theorem geo_continuousAt_geoX {r₀ : ℂ} (h0 : r₀ ≠ 0) (h1 : 1 - r₀ ≠ 0) :
    ContinuousAt geoX r₀ := by
  have h01 : r₀ * (1 - r₀) ≠ 0 := mul_ne_zero h0 h1
  have h : ContinuousAt (fun r : ℂ ↦ (1 + r) / (r * (1 - r))) r₀ := by
    fun_prop (disch := exact h01)
  unfold geoX
  exact h

/-- `L(r)` is continuous off `r = 1`. -/
private theorem geo_continuousAt_geoL {r₀ : ℂ} (h1 : 1 - r₀ ≠ 0) : ContinuousAt geoL r₀ := by
  have h : ContinuousAt (fun r : ℂ ↦ ((1 + r) / (1 - r)) ^ 2) r₀ := by
    fun_prop (disch := exact h1)
  unfold geoL geoF
  exact h

/-- A limit of `U ∘ r` at the node `(ε, -1)` along the smooth torus locus must equal the value
`U(r₀)` of the branch `r → r₀ ∈ {i, -i}`, approached by `r ↦ (ε √x(r), L(r))`. -/
private theorem geo_limit_eq_branch_value (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (r₀ : ℂ)
    (hr₀ : r₀ = Complex.I ∨ r₀ = -Complex.I) (c : ℝ)
    (h : Tendsto (fun p ↦ geoRegPrimitive (geoCurveR p)) (𝓝[GeoSmoothTorusLocus] (ε, -1))
      (𝓝 c)) :
    c = geoRegPrimitive r₀ := by
  obtain ⟨hXI, hXmI, hLI, hLmI⟩ := geo_node_branches
  have hX1 : geoX r₀ = 1 := by rcases hr₀ with rfl | rfl; exacts [hXI, hXmI]
  have hL1 : geoL r₀ = -1 := by rcases hr₀ with rfl | rfl; exacts [hLI, hLmI]
  have hsq : r₀ ^ 2 = -1 := by
    rcases hr₀ with rfl | rfl <;> simp [Complex.I_sq]
  have hr0 : r₀ ≠ 0 := by rintro rfl; norm_num at hsq
  have hr1 : r₀ ≠ 1 := by rintro rfl; norm_num at hsq
  have hrm1 : r₀ ≠ -1 := by rintro rfl; norm_num at hsq
  have hr1' : 1 - r₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  set p : ℂ → ℂ × ℂ := fun r ↦ (ε * geoX r ^ (2 : ℂ)⁻¹, geoL r) with hpdef
  have hXc : ContinuousAt geoX r₀ := geo_continuousAt_geoX hr0 hr1'
  have hLc : ContinuousAt geoL r₀ := geo_continuousAt_geoL hr1'
  have hpc : Tendsto p (𝓝 r₀) (𝓝 (ε, -1)) := by
    have hsqrt : ContinuousAt (fun r ↦ geoX r ^ (2 : ℂ)⁻¹) r₀ :=
      (continuousAt_cpow_const (by rw [hX1]; exact Complex.one_mem_slitPlane)).comp hXc
    have hfst : ContinuousAt (fun r ↦ ε * geoX r ^ (2 : ℂ)⁻¹) r₀ := continuousAt_const.mul hsqrt
    have h1 := hfst.tendsto.prodMk_nhds hLc.tendsto
    simpa only [hX1, hL1, Complex.one_cpow, mul_one] using h1
  have hev : ∀ᶠ r in 𝓝[≠] r₀, p r ∈ GeoSmoothTorusLocus ∧ geoCurveR (p r) = r := by
    have hne : ∀ᶠ r in 𝓝[≠] r₀, r ≠ 0 ∧ r ≠ 1 ∧ r ≠ -1 ∧ r ≠ -r₀ := by
      have hn : r₀ ≠ -r₀ := by
        intro h
        have : r₀ = 0 := by linear_combination h / 2
        exact hr0 this
      exact ((eventually_ne_nhds hr0).and ((eventually_ne_nhds hr1).and
        ((eventually_ne_nhds hrm1).and (eventually_ne_nhds hn)))).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hne, self_mem_nhdsWithin] with r ⟨h0, h1, hm1, hn⟩ (hr : r ≠ r₀)
    have hi : r ^ 2 ≠ -1 := by
      intro hi
      have h' : (r - r₀) * (r + r₀) = 0 := by linear_combination hi - hsq
      rcases mul_eq_zero.mp h' with h' | h'
      · exact hr (sub_eq_zero.mp h')
      · exact hn (eq_neg_of_add_eq_zero_left h')
    have hM : (ε * geoX r ^ (2 : ℂ)⁻¹) ^ 2 = geoX r := by
      rw [mul_pow, hε2, one_mul, Complex.cpow_ofNat_inv_pow]
    exact geo_mem_smoothTorusLocus_of_param h0 h1 hm1 hi hM
  have hp : Tendsto p (𝓝[≠] r₀) (𝓝[GeoSmoothTorusLocus] (ε, -1)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpc.mono_left nhdsWithin_le_nhds, hev.mono fun r hr ↦ hr.1⟩
  have h1 := h.comp hp
  have h2 : Tendsto ((fun q ↦ geoRegPrimitive (geoCurveR q)) ∘ p) (𝓝[≠] r₀)
      (𝓝 (geoRegPrimitive r₀)) := by
    refine ((geo_continuous_regPrimitive.tendsto r₀).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hev] with r hr
    simp only [Function.comp_apply, hr.2]
  exact tendsto_nhds_unique h1 h2

/-- No single value at a node: `U ∘ r` has no limit at `(1, -1)` along the smooth torus locus
(the two normalized branches carry `2G` and `-2G`); the same holds at `(-1, -1)`. -/
theorem geo_regPrimitive_no_limit_at_node (ε : ℂ) (hε : ε = 1 ∨ ε = -1) :
    ¬ ∃ c : ℝ, Tendsto (fun p ↦ geoRegPrimitive (geoCurveR p))
      (𝓝[GeoSmoothTorusLocus] (ε, -1)) (𝓝 c) := by
  rintro ⟨c, hc⟩
  have h1 := geo_limit_eq_branch_value ε hε _ (Or.inl rfl) c hc
  have h2 := geo_limit_eq_branch_value ε hε _ (Or.inr rfl) c hc
  exact geo_reg_primitive.2.2.2.2.2.2.2 (h1.symm.trans h2)

end AJConjecture
