import Mathlib

/-!
# The line integral of a pair of simple poles (Unit PpZ, node `PpZ_PolePair`)

Source: the residue count in Zheng's (5.10), reduced to an elementary real integral.

For `p, p' ∈ ℂ \ ℝ` the function `x ↦ (x - p)⁻¹ - (x - p')⁻¹` is integrable on `ℝ`
(it is `(p - p')/((x - p)(x - p'))`, continuous and `O(x⁻²)`), and
`∫_ℝ ((x - p)⁻¹ - (x - p')⁻¹) dx = πi (sgn Im p - sgn Im p')`:
* `= 2πi` if `Im p > 0 > Im p'` (`ppZ_integral_inv_sub_inv_opposite`);
* `= 0` if `Im p < 0` and `Im p' < 0` (`ppZ_integral_inv_sub_inv_same`).

Route. With `p = u + iv`: `(x - p)⁻¹ = ((x - u) + iv)/((x - u)² + v²)`. On `[-T, T]`:
imaginary part `∫ v/((x-u)² + v²) dx = arctan((T-u)/v) + arctan((T+u)/v) → π sgn v`
(`integral_inv_one_add_sq`/`integral_one_div_one_add_sq` after `x = u + vt`,
`Real.tendsto_arctan_atTop`); real part `½ log(((T-u)² + v²)/((T+u)² + v²)) → 0`. Apply
`MeasureTheory.intervalIntegral_tendsto_integral` to the integrable difference. (Alternatively:
the real parts of the two terms combine to an integrable function whose integral is computed the
same way; no principal values are needed for the difference.)
Numerically: `6.28318i` and `0` for `p = 0.3 ± 0.7i`, `p' = -1.2 - 0.4i` (`strip.py`).
-/

noncomputable section

namespace AJConjecture

open MeasureTheory Filter Topology Set in
/-- A real number minus a non-real number is not zero. -/
private theorem ofReal_sub_ne_zero_ppZPolePair {p : ℂ} (hp : p.im ≠ 0) (x : ℝ) :
    (x : ℂ) - p ≠ 0 := fun h ↦ hp <| by
  have := congrArg Complex.im h
  simpa using this

open MeasureTheory Filter Topology Set in
/-- `x ↦ ‖x - p‖⁻²` is integrable on `ℝ` for `p ∉ ℝ`. -/
private theorem integrable_inv_norm_sq_ppZPolePair {p : ℂ} (hp : p.im ≠ 0) :
    Integrable fun x : ℝ ↦ (‖(x : ℂ) - p‖ ^ 2)⁻¹ := by
  have h := (((integrable_inv_one_add_sq.comp_div hp).comp_sub_right p.re).const_mul
    ((p.im ^ 2)⁻¹))
  refine h.congr (Eventually.of_forall fun x ↦ ?_)
  have h1 : ‖(x : ℂ) - p‖ ^ 2 = (x - p.re) ^ 2 + p.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
    ring
  simp only [h1]
  have h2 : (0 : ℝ) < p.im ^ 2 := by positivity
  have h3 : (0 : ℝ) < (x - p.re) ^ 2 + p.im ^ 2 := by positivity
  field_simp
  ring

open MeasureTheory Filter Topology Set in
/-- `x ↦ (x - p)⁻¹ - (x - p')⁻¹` is integrable on `ℝ` for `p, p' ∉ ℝ`. -/
theorem ppZ_integrable_inv_sub_inv {p p' : ℂ} (hp : p.im ≠ 0) (hp' : p'.im ≠ 0) :
    MeasureTheory.Integrable fun x : ℝ ↦ ((x : ℂ) - p)⁻¹ - ((x : ℂ) - p')⁻¹ := by
  have hc : Continuous fun x : ℝ ↦ ((x : ℂ) - p)⁻¹ - ((x : ℂ) - p')⁻¹ :=
    (Continuous.inv₀ (by fun_prop) (ofReal_sub_ne_zero_ppZPolePair hp)).sub
      (Continuous.inv₀ (by fun_prop) (ofReal_sub_ne_zero_ppZPolePair hp'))
  refine Integrable.mono' (((integrable_inv_norm_sq_ppZPolePair hp).add
    (integrable_inv_norm_sq_ppZPolePair hp')).const_mul ‖p - p'‖) hc.aestronglyMeasurable
    (Eventually.of_forall fun x ↦ ?_)
  have h1 := ofReal_sub_ne_zero_ppZPolePair hp x
  have h2 := ofReal_sub_ne_zero_ppZPolePair hp' x
  have h3 : ((x : ℂ) - p)⁻¹ - ((x : ℂ) - p')⁻¹ =
      (p - p') * (((x : ℂ) - p)⁻¹ * ((x : ℂ) - p')⁻¹) := by
    field_simp
    ring
  rw [h3, norm_mul, norm_mul, norm_inv, norm_inv]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  simp only [Pi.add_apply, ← inv_pow]
  nlinarith [sq_nonneg (‖(x : ℂ) - p‖⁻¹ - ‖(x : ℂ) - p'‖⁻¹), sq_nonneg (‖(x : ℂ) - p‖⁻¹),
    sq_nonneg (‖(x : ℂ) - p'‖⁻¹)]

open MeasureTheory Filter Topology Set in
/-- The antiderivative `log (x - p)` of `(x - p)⁻¹` along the real line. -/
private theorem hasDerivAt_log_sub_ppZPolePair {p : ℂ} (hp : p.im ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Complex.log ((t : ℂ) - p)) (((x : ℂ) - p)⁻¹) x := by
  have h1 : HasDerivAt (fun t : ℝ ↦ (t : ℂ) - p) 1 x :=
    ((hasDerivAt_id x).ofReal_comp).sub_const p
  have h2 : (x : ℂ) - p ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    simpa using hp
  simpa using h1.clog_real h2

open MeasureTheory Filter Topology Set in
/-- `‖x - p‖ → ∞` as `|x| → ∞`. -/
private theorem tendsto_norm_sub_ppZPolePair (p : ℂ) :
    Tendsto (fun x : ℝ ↦ ‖(x : ℂ) - p‖) (cocompact ℝ) atTop := by
  have h : Tendsto (fun x : ℝ ↦ ‖x‖ - ‖p‖) (cocompact ℝ) atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_norm_cocompact_atTop
  refine tendsto_atTop_mono (fun x ↦ ?_) h
  have := norm_sub_norm_le (x : ℂ) p
  simpa using this

open MeasureTheory Filter Topology Set in
/-- `c / ‖x - p‖ → 0` as `|x| → ∞`. -/
private theorem tendsto_div_norm_sub_ppZPolePair (c : ℝ) (p : ℂ) :
    Tendsto (fun x : ℝ ↦ c / ‖(x : ℂ) - p‖) (cocompact ℝ) (𝓝 0) :=
  (tendsto_norm_sub_ppZPolePair p).const_div_atTop c

open MeasureTheory Filter Topology Set in
/-- The real part of `log (x - p) - log (x - p')` tends to `0` as `|x| → ∞`. -/
private theorem tendsto_log_norm_sub_ppZPolePair {p p' : ℂ} (hp : p.im ≠ 0) (hp' : p'.im ≠ 0) :
    Tendsto (fun x : ℝ ↦ Real.log ‖(x : ℂ) - p‖ - Real.log ‖(x : ℂ) - p'‖) (cocompact ℝ)
      (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ ↦ (p' - p) / ((x : ℂ) - p')) (cocompact ℝ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [norm_div] using tendsto_div_norm_sub_ppZPolePair ‖p' - p‖ p'
  have h2 : Tendsto (fun x : ℝ ↦ ‖1 + (p' - p) / ((x : ℂ) - p')‖) (cocompact ℝ) (𝓝 1) := by
    simpa using (h1.const_add 1).norm
  have h3 := (Real.continuousAt_log one_ne_zero).tendsto.comp h2
  rw [Real.log_one] at h3
  refine h3.congr fun x ↦ ?_
  have hx := ofReal_sub_ne_zero_ppZPolePair hp x
  have hx' := ofReal_sub_ne_zero_ppZPolePair hp' x
  have h4 : 1 + (p' - p) / ((x : ℂ) - p') = ((x : ℂ) - p) / ((x : ℂ) - p') := by
    field_simp
    ring
  simp only [Function.comp_apply, h4, norm_div]
  rw [Real.log_div (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hx')]

open MeasureTheory Filter Topology Set in
/-- `arg (x - p) → 0` as `x → +∞`. -/
private theorem tendsto_arg_atTop_ppZPolePair (p : ℂ) :
    Tendsto (fun x : ℝ ↦ Complex.arg ((x : ℂ) - p)) atTop (𝓝 0) := by
  have h := (Real.continuous_arcsin.tendsto 0).comp
    ((tendsto_div_norm_sub_ppZPolePair (-p.im) p).mono_left atTop_le_cocompact)
  rw [Real.arcsin_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop p.re] with x hx
  rw [Complex.arg_of_re_nonneg (by simpa using hx)]
  simp

open MeasureTheory Filter Topology Set in
/-- `arg (x - p) → π` as `x → -∞`, for `p` in the lower half plane. -/
private theorem tendsto_arg_atBot_of_neg_ppZPolePair {p : ℂ} (hp : p.im < 0) :
    Tendsto (fun x : ℝ ↦ Complex.arg ((x : ℂ) - p)) atBot (𝓝 Real.pi) := by
  have h := ((Real.continuous_arcsin.tendsto 0).comp
    ((tendsto_div_norm_sub_ppZPolePair p.im p).mono_left atBot_le_cocompact)).add_const Real.pi
  rw [Real.arcsin_zero, zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_lt_atBot p.re] with x hx
  rw [Complex.arg_of_re_neg_of_im_nonneg (by simpa using hx) (by simpa using hp.le)]
  simp

open MeasureTheory Filter Topology Set in
/-- `arg (x - p) → -π` as `x → -∞`, for `p` in the upper half plane. -/
private theorem tendsto_arg_atBot_of_pos_ppZPolePair {p : ℂ} (hp : 0 < p.im) :
    Tendsto (fun x : ℝ ↦ Complex.arg ((x : ℂ) - p)) atBot (𝓝 (-Real.pi)) := by
  have h := ((Real.continuous_arcsin.tendsto 0).comp
    ((tendsto_div_norm_sub_ppZPolePair p.im p).mono_left atBot_le_cocompact)).sub_const Real.pi
  rw [Real.arcsin_zero, zero_sub] at h
  refine h.congr' ?_
  filter_upwards [eventually_lt_atBot p.re] with x hx
  rw [Complex.arg_of_re_neg_of_im_neg (by simpa using hx) (by simpa using hp)]
  simp

open MeasureTheory Filter Topology Set in
/-- The limit of `log (x - p) - log (x - p')` along a filter going to infinity, given the limits
of the two arguments. -/
private theorem tendsto_log_sub_log_ppZPolePair {p p' : ℂ} (hp : p.im ≠ 0) (hp' : p'.im ≠ 0)
    {l : Filter ℝ} (hl : l ≤ cocompact ℝ) {a a' : ℝ}
    (ha : Tendsto (fun x : ℝ ↦ Complex.arg ((x : ℂ) - p)) l (𝓝 a))
    (ha' : Tendsto (fun x : ℝ ↦ Complex.arg ((x : ℂ) - p')) l (𝓝 a')) :
    Tendsto (fun x : ℝ ↦ Complex.log ((x : ℂ) - p) - Complex.log ((x : ℂ) - p')) l
      (𝓝 (((a - a' : ℝ) : ℂ) * Complex.I)) := by
  have h1 := (Complex.continuous_ofReal.tendsto _).comp
    ((tendsto_log_norm_sub_ppZPolePair hp hp').mono_left hl)
  have h2 := ((Complex.continuous_ofReal.tendsto _).comp (ha.sub ha')).mul_const Complex.I
  have h3 := h1.add h2
  simp only [Complex.ofReal_zero, zero_add] at h3
  refine h3.congr fun x ↦ ?_
  simp only [Function.comp_apply, Complex.log, Complex.ofReal_sub]
  ring

open MeasureTheory Filter Topology Set in
/-- A pole above and a pole below the real line: the integral is `2πi`. -/
theorem ppZ_integral_inv_sub_inv_opposite {p p' : ℂ} (hp : 0 < p.im) (hp' : p'.im < 0) :
    ∫ x : ℝ, (((x : ℂ) - p)⁻¹ - ((x : ℂ) - p')⁻¹) = 2 * Real.pi * Complex.I := by
  rw [integral_of_hasDerivAt_of_tendsto
    (fun x ↦ (hasDerivAt_log_sub_ppZPolePair hp.ne' x).sub
      (hasDerivAt_log_sub_ppZPolePair hp'.ne x))
    (ppZ_integrable_inv_sub_inv hp.ne' hp'.ne)
    (tendsto_log_sub_log_ppZPolePair hp.ne' hp'.ne atBot_le_cocompact
      (tendsto_arg_atBot_of_pos_ppZPolePair hp) (tendsto_arg_atBot_of_neg_ppZPolePair hp'))
    (tendsto_log_sub_log_ppZPolePair hp.ne' hp'.ne atTop_le_cocompact
      (tendsto_arg_atTop_ppZPolePair p) (tendsto_arg_atTop_ppZPolePair p'))]
  push_cast
  ring

open MeasureTheory Filter Topology Set in
/-- Both poles below the real line: the integral is `0`. -/
theorem ppZ_integral_inv_sub_inv_same {p p' : ℂ} (hp : p.im < 0) (hp' : p'.im < 0) :
    ∫ x : ℝ, (((x : ℂ) - p)⁻¹ - ((x : ℂ) - p')⁻¹) = 0 := by
  rw [integral_of_hasDerivAt_of_tendsto
    (fun x ↦ (hasDerivAt_log_sub_ppZPolePair hp.ne x).sub
      (hasDerivAt_log_sub_ppZPolePair hp'.ne x))
    (ppZ_integrable_inv_sub_inv hp.ne hp'.ne)
    (tendsto_log_sub_log_ppZPolePair hp.ne hp'.ne atBot_le_cocompact
      (tendsto_arg_atBot_of_neg_ppZPolePair hp) (tendsto_arg_atBot_of_neg_ppZPolePair hp'))
    (tendsto_log_sub_log_ppZPolePair hp.ne hp'.ne atTop_le_cocompact
      (tendsto_arg_atTop_ppZPolePair p) (tendsto_arg_atTop_ppZPolePair p'))]
  simp

end AJConjecture
