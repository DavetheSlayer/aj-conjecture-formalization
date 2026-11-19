import Mathlib
import AJHandoff.Geometry.GeoHypCatalanLog

/-!
# The planar integral for the ideal tetrahedron of shape `i`

After integrating out the height, the hyperbolic volume of the ideal tetrahedron with vertices
`∞, 0, 1, i` is `∫_Δ dA / (1 - 2|p - c|²)` over the triangle `Δ = (0, 1, i)`, `c = (1 + i)/2`.
In coordinates `p = x + iy`, `1 - 2|p - c|² = 2(x(1 - x) + y(1 - y))` (`hypPlanarDensity`).
We substitute `y = a x` (rays from the vertex `0`), exchange the order of integration, and
integrate `x` explicitly: what remains is `∫₀^∞ hypVolProfile a da = G`.
-/

open MeasureTheory Set

noncomputable section

namespace AJConjecture

/-- The planar density `1 / (2(x(1 - x) + y(1 - y))) = 1/(1 - 2|p - c|²)` on the half-plane
`x + y ≤ 1`, and `0` beyond it. -/
def hypPlanarDensity (x y : ℝ) : ENNReal :=
  if x + y ≤ 1 then ENNReal.ofReal (1 / (2 * (x * (1 - x) + y * (1 - y)))) else 0

/-- The planar density along the ray of slope `a` from `0`, after the substitution `y = a x`. -/
def hypRayDensity (a x : ℝ) : ENNReal :=
  if x * (1 + a) ≤ 1 then ENNReal.ofReal (1 / (2 * ((1 + a) - x * (1 + a ^ 2)))) else 0

/-- Inside the triangle, the denominator `(1 + a) - x(1 + a²)` along the ray of slope `a > 0` is
positive. -/
lemma hypRay_denom_pos {a x : ℝ} (ha : 0 < a) (hx : x * (1 + a) ≤ 1) :
    0 < (1 + a) - x * (1 + a ^ 2) := by
  have h1 : x * (1 + a) * (1 + a ^ 2) ≤ 1 + a ^ 2 :=
    by nlinarith [mul_le_mul_of_nonneg_right hx (by positivity : (0 : ℝ) ≤ 1 + a ^ 2)]
  have h2 : 0 < ((1 + a) - x * (1 + a ^ 2)) * (1 + a) := by nlinarith
  exact pos_of_mul_pos_left h2 (by linarith)

/-- The substitution `y = a x` in the inner integral. -/
lemma hypPlanar_lintegral_ray {x : ℝ} (hx : 0 < x) :
    ∫⁻ y in Ioi (0 : ℝ), hypPlanarDensity x y = ∫⁻ a in Ioi (0 : ℝ), hypRayDensity a x := by
  conv_lhs => rw [← image_const_mul_Ioi_zero hx]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (f' := fun _ ↦ x) (fun a _ ↦ by simpa using ((hasDerivAt_id a).const_mul x).hasDerivWithinAt)
    (mul_right_injective₀ hx.ne').injOn]
  refine setLIntegral_congr_fun measurableSet_Ioi fun a ha ↦ ?_
  have ha : 0 < a := ha
  simp only [hypPlanarDensity, hypRayDensity, abs_of_pos hx]
  have hc : x + x * a ≤ 1 ↔ x * (1 + a) ≤ 1 := by rw [mul_add, mul_one]
  by_cases h : x * (1 + a) ≤ 1
  · simp only [hc, h, ↓reduceIte]
    rw [← ENNReal.ofReal_mul hx.le]
    congr 1
    have hQ := hypRay_denom_pos ha h
    rw [show x * (1 - x) + x * a * (1 - x * a) = x * ((1 + a) - x * (1 + a ^ 2)) by ring]
    field_simp
  · simp only [hc, h, ↓reduceIte, mul_zero]

/-- The integral along the ray of slope `a > 0` is the profile `hypVolProfile a`. -/
lemma hypRay_lintegral {a : ℝ} (ha : 0 < a) :
    ∫⁻ x in Ioi (0 : ℝ), hypRayDensity a x = ENNReal.ofReal (hypVolProfile a) := by
  have h1a : 0 < 1 + a := by linarith
  have e : ∀ x, hypRayDensity a x = (Iic (1 / (1 + a))).indicator
      (fun x ↦ ENNReal.ofReal (1 / (2 * ((1 + a) - x * (1 + a ^ 2))))) x := by
    intro x
    simp only [hypRayDensity, indicator_apply, mem_Iic, le_div_iff₀ h1a]
  have hQ : ∀ x ∈ Icc 0 (1 / (1 + a)), 0 < (1 + a) - x * (1 + a ^ 2) := fun x hx ↦
    hypRay_denom_pos ha ((le_div_iff₀ h1a).1 hx.2)
  have hc : Continuous fun x : ℝ ↦ 2 * ((1 + a) - x * (1 + a ^ 2)) := by fun_prop
  simp_rw [e]
  rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    Iic_inter_Ioi, hypVol_lintegral_Ioc_ofReal (by positivity)]
  · congr 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x ↦ -Real.log ((1 + a) - x * (1 + a ^ 2)) / (2 * (1 + a ^ 2)))]
    · have e1 : (1 + a) - 1 / (1 + a) * (1 + a ^ 2) = 2 * a / (1 + a) := by
        field_simp
        ring
      have e2 : Real.log ((1 + a) ^ 2 / (2 * a)) = 2 * Real.log (1 + a) - Real.log (2 * a) := by
        rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
        push_cast
        ring
      have e3 : Real.log (2 * a / (1 + a)) = Real.log (2 * a) - Real.log (1 + a) :=
        Real.log_div (by positivity) (by positivity)
      simp only [hypVolProfile, e1, zero_mul, sub_zero, e2, e3]
      field_simp
      ring
    · intro x hx
      rw [uIcc_of_le (by positivity)] at hx
      have hq := hQ x hx
      have hd : HasDerivAt (fun x ↦ (1 + a) - x * (1 + a ^ 2)) (-(1 + a ^ 2)) x := by
        convert ((hasDerivAt_id' x).mul_const (1 + a ^ 2)).const_sub (1 + a) using 1
        ring
      have := ((hd.log hq.ne').neg).div_const (2 * (1 + a ^ 2))
      convert this using 1
      field_simp
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le (by positivity)]
      exact ContinuousOn.div continuousOn_const hc.continuousOn fun x hx ↦ by
        have := hQ x hx
        exact (by positivity : 2 * ((1 + a) - x * (1 + a ^ 2)) ≠ 0)
  · exact ContinuousOn.div continuousOn_const hc.continuousOn fun x hx ↦ by
      have := hQ x hx
      exact (by positivity : 2 * ((1 + a) - x * (1 + a ^ 2)) ≠ 0)
  · intro x hx
    have := hQ x (Ioc_subset_Icc_self hx)
    positivity

/-- The planar integral `∫_Δ dA / (1 - 2|p - c|²)` over the triangle `(0, 1, i)` is `G`. -/
theorem hypVol_lintegral_planar :
    ∫⁻ x in Ioi (0 : ℝ), ∫⁻ y in Ioi (0 : ℝ), hypPlanarDensity x y =
      ENNReal.ofReal catalanConstant := by
  have hm : Measurable (Function.uncurry fun x a ↦ hypRayDensity a x) := by
    refine Measurable.ite (measurableSet_le (by fun_prop) measurable_const) ?_ measurable_const
    fun_prop
  rw [setLIntegral_congr_fun measurableSet_Ioi fun x hx ↦ hypPlanar_lintegral_ray hx,
    lintegral_lintegral_swap hm.aemeasurable,
    setLIntegral_congr_fun measurableSet_Ioi fun a ha ↦ hypRay_lintegral ha]
  exact hypVol_lintegral_profile

end AJConjecture
