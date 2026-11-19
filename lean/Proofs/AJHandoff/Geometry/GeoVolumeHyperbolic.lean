import Mathlib
import AJFamily.VolumeDefs
import AJHandoff.Geometry.GeoHypFiber
import AJHandoff.Geometry.GeoHypPlanar

/-!
# Hyperbolic volume of the ideal tetrahedron of shape `i` (G-VOL, metric volume; optional crux)

Hyperbolic volume on the upper half-space `ℍ³ = ℂ × (0, ∞)` is the measure with density `t⁻³`
against Lebesgue measure (`geoHypMeasure`). The ideal tetrahedron with vertices `∞, 0, 1, i` is the
region over the triangle `0, 1, i` above the hemisphere through `0, 1, i` (centre `(1 + i)/2`,
radius `1/√2`): its faces are the three vertical half-planes over the edges and that hemisphere
(`geoIdealTetI`). Its volume is Catalan's constant `G`, so the four tetrahedra of shape `i` of the
complete Whitehead structure have total volume `4G`. This defines volume through the metric, as the
G-VOL acceptance asks, and checks the Bloch–Wigner value `D(i) = G` against it.

What stays interpretation: that the four tetrahedra glue (up to measure zero) to the Whitehead link
exterior with its complete hyperbolic metric.

Route. Integrate `t` first (`hypFiber_lintegral`): `∫_{h}^{∞} t⁻³ dt = 1/(2h²)` with
`h² = 1/2 - |p - c|²`, so the volume is `∫_Δ dA/(1 - 2|p - c|²)` and
`1 - 2|p - c|² = 2(x(1 - x) + y(1 - y))` (`geo_hypVolume_eq_planar`, by Tonelli on
`ℂ × ℝ ≃ ℝ × ℝ × ℝ`). Substituting `y = a x` and integrating `x` leaves
`∫₀^∞ log((1 + a)²/(2a)) / (2(1 + a²)) da` (`hypVol_lintegral_planar`), which is `G` by
`a ↦ 1/a`, Tonelli against `∫₀¹ arctan b / b db = G` and a Serret-type substitution
(`hypVol_lintegral_profile`).
-/

open MeasureTheory

noncomputable section

namespace AJConjecture

/-- The hyperbolic volume measure on the upper half-space: density `t⁻³` on `t > 0`. -/
def geoHypMeasure : Measure (ℂ × ℝ) :=
  (volume.restrict {p : ℂ × ℝ | 0 < p.2}).withDensity fun p ↦ ENNReal.ofReal (p.2 ^ (-3 : ℤ))

/-- The ideal tetrahedron with vertices `∞, 0, 1, i`. -/
def geoIdealTetI : Set (ℂ × ℝ) :=
  {p | 0 ≤ p.1.re ∧ 0 ≤ p.1.im ∧ p.1.re + p.1.im ≤ 1 ∧ 0 < p.2 ∧
    1 / 2 ≤ ‖p.1 - (1 + Complex.I) / 2‖ ^ 2 + p.2 ^ 2}

open Set

/-- The ideal tetrahedron of shape `i` is a measurable set. -/
lemma geoIdealTetI_measurableSet : MeasurableSet geoIdealTetI := by
  have h1 : Measurable fun p : ℂ × ℝ ↦ p.1.re := by fun_prop
  have h2 : Measurable fun p : ℂ × ℝ ↦ p.1.im := by fun_prop
  have h3 : Measurable fun p : ℂ × ℝ ↦ p.1.re + p.1.im := by fun_prop
  have h4 : Measurable fun p : ℂ × ℝ ↦ ‖p.1 - (1 + Complex.I) / 2‖ ^ 2 + p.2 ^ 2 := by fun_prop
  have hc : ∀ r : ℝ, Measurable fun _ : ℂ × ℝ ↦ r := fun r ↦ measurable_const
  exact (measurableSet_le (hc 0) h1).inter
    ((measurableSet_le (hc 0) h2).inter
    ((measurableSet_le h3 (hc 1)).inter
    ((measurableSet_lt (hc 0) measurable_snd).inter
    (measurableSet_le (hc (1 / 2)) h4))))

/-- The squared distance from `z` to the centre `(1 + i)/2`. -/
lemma geo_norm_sub_center_sq (z : ℂ) :
    ‖z - (1 + Complex.I) / 2‖ ^ 2 = (z.re - 1 / 2) ^ 2 + (z.im - 1 / 2) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im, Complex.add_re,
    Complex.add_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  norm_num
  ring

/-- The vertical fibre of the tetrahedron over `z`, as an indicator. -/
lemma geoIdealTetI_indicator_fibre (z : ℂ) :
    (fun t : ℝ ↦ geoIdealTetI.indicator
      (fun p : ℂ × ℝ ↦ ENNReal.ofReal (p.2 ^ (-3 : ℤ))) (z, t)) =
    if 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re + z.im ≤ 1 then
      {t : ℝ | 0 < t ∧ 1 / 2 ≤ ‖z - (1 + Complex.I) / 2‖ ^ 2 + t ^ 2}.indicator
        fun t ↦ ENNReal.ofReal (t ^ (-3 : ℤ))
    else 0 := by
  funext t
  by_cases h : 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re + z.im ≤ 1
  · simp only [h, and_self, ↓reduceIte, indicator_apply, geoIdealTetI, mem_ofPred_eq, true_and]
  · simp only [h, ↓reduceIte, indicator_apply, geoIdealTetI, mem_ofPred_eq, Pi.zero_apply]
    rw [ite_eq_right_iff]
    intro h'
    exact absurd ⟨h'.1, h'.2.1, h'.2.2.1⟩ h

/-- Over a point with positive coordinates, the fibre integral is the planar density. -/
lemma geoIdealTetI_lintegral_fibre {z : ℂ} (hx : 0 < z.re) (hy : 0 < z.im) :
    ∫⁻ t, geoIdealTetI.indicator (fun p : ℂ × ℝ ↦ ENNReal.ofReal (p.2 ^ (-3 : ℤ))) (z, t) =
      hypPlanarDensity z.re z.im := by
  rw [geoIdealTetI_indicator_fibre]
  by_cases h : z.re + z.im ≤ 1
  · simp only [hx.le, hy.le, h, and_self, ↓reduceIte, hypPlanarDensity]
    have hs : ‖z - (1 + Complex.I) / 2‖ ^ 2 < 1 / 2 := by
      rw [geo_norm_sub_center_sq]
      nlinarith
    have hS : MeasurableSet
        {t : ℝ | 0 < t ∧ 1 / 2 ≤ ‖z - (1 + Complex.I) / 2‖ ^ 2 + t ^ 2} := by
      rw [ofPred_and]
      exact measurableSet_Ioi.inter (measurableSet_le measurable_const (by fun_prop))
    rw [lintegral_indicator hS, hypFiber_lintegral hs, geo_norm_sub_center_sq]
    congr 2
    ring
  · simp only [h, and_false, ↓reduceIte, hypPlanarDensity, lintegral_zero_fun]

/-- Over a point with a negative coordinate, the fibre integral vanishes. -/
lemma geoIdealTetI_lintegral_fibre_zero {z : ℂ} (h : z.re < 0 ∨ z.im < 0) :
    ∫⁻ t, geoIdealTetI.indicator (fun p : ℂ × ℝ ↦ ENNReal.ofReal (p.2 ^ (-3 : ℤ))) (z, t) = 0 := by
  have h' : ¬(0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re + z.im ≤ 1) := by
    rintro ⟨h1, h2, -⟩
    rcases h with h | h <;> linarith
  rw [geoIdealTetI_indicator_fibre]
  simp only [h', ↓reduceIte, lintegral_zero_fun]

/-- Tonelli: the hyperbolic volume of the tetrahedron is the planar integral over the triangle. -/
lemma geo_hypVolume_eq_planar : geoHypMeasure geoIdealTetI =
    ∫⁻ x in Ioi (0 : ℝ), ∫⁻ y in Ioi (0 : ℝ), hypPlanarDensity x y := by
  set ρ : ℂ × ℝ → ENNReal := fun p ↦ ENNReal.ofReal (p.2 ^ (-3 : ℤ)) with hρ
  have hT := geoIdealTetI_measurableSet
  have hρm : Measurable (geoIdealTetI.indicator ρ) := by
    refine Measurable.indicator ?_ hT
    fun_prop
  set F : ℂ → ENNReal := fun z ↦ ∫⁻ t, geoIdealTetI.indicator ρ (z, t) with hF
  have hFm : Measurable F := hρm.lintegral_prod_right'
  have hsub : geoIdealTetI ∩ {p : ℂ × ℝ | 0 < p.2} = geoIdealTetI :=
    inter_eq_left.2 fun p hp ↦ hp.2.2.2.1
  rw [geoHypMeasure, withDensity_apply _ hT, Measure.restrict_restrict hT, hsub,
    ← lintegral_indicator hT, Measure.volume_eq_prod, lintegral_prod _ hρm.aemeasurable]
  change ∫⁻ z, F z = _
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding, Measure.volume_eq_prod,
    lintegral_prod (fun a ↦ F (Complex.measurableEquivRealProd.symm a))
      (hFm.comp Complex.measurableEquivRealProd.symm.measurable).aemeasurable]
  simp only [Complex.measurableEquivRealProd_symm_apply]
  have hneg : ∀ x y : ℝ, x < 0 ∨ y < 0 → F ⟨x, y⟩ = 0 := fun x y h ↦
    geoIdealTetI_lintegral_fibre_zero h
  have hinner : ∀ x : ℝ, ∫⁻ y, F ⟨x, y⟩ = ∫⁻ y in Ioi 0, F ⟨x, y⟩ := by
    intro x
    rw [setLIntegral_congr Ioi_ae_eq_Ici, setLIntegral_eq_of_support_subset]
    intro y hy
    by_contra hy'
    exact hy (hneg x y (Or.inr (not_le.1 hy')))
  simp_rw [hinner]
  rw [← setLIntegral_eq_of_support_subset (s := Ici 0), ← setLIntegral_congr Ioi_ae_eq_Ici]
  · refine setLIntegral_congr_fun measurableSet_Ioi fun x hx ↦
      setLIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    exact geoIdealTetI_lintegral_fibre (z := ⟨x, y⟩) hx hy
  · intro x hx
    by_contra hx'
    refine hx ?_
    simp only
    refine setLIntegral_eq_zero measurableSet_Ioi fun y _ ↦ hneg x y (Or.inl (not_le.1 hx'))

/-- The hyperbolic volume of the ideal tetrahedron of shape `i` is Catalan's constant. -/
theorem geo_hypVolume_idealTetI : geoHypMeasure geoIdealTetI = ENNReal.ofReal catalanConstant :=
  geo_hypVolume_eq_planar.trans hypVol_lintegral_planar

end AJConjecture
