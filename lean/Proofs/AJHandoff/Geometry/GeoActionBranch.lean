import Mathlib
import AJHandoff.Geometry.GeoAction
import AJHandoff.Geometry.GeoBlochWignerDerivDisc

/-!
# The displayed dilogarithmic action is a channel branch (G-ACTION, nonvacuity)

The source's formal action, restricted to the channel `Q = -1` with `log Q = πi`:

  `S_a(ℓx, ℓz) = πi(ℓz - ℓx) + Li₂(1) - Li₂(-1) - Li₂(z) + Li₂(-z) - Li₂(z/x) + Li₂(-z/x)
               - 2a(πi)² - ℓx ℓz + ℓx²`, `x = e^{ℓx}`, `z = e^{ℓz}`,

with `Li₂` the library's `dilogSeries`, is a `GeoChannelActionBranch` on the domain
`|z| < 1`, `|z/x| < 1`. Near `r = 2` (`x = -3/2`, `z = -1/2`, `z/x = 1/3`) the principal lift
`ℓ(r) = (log x(r), log(-1/r))` lies in this domain and is admissible (`∂S/∂ℓz = 0` exactly), so
the hypotheses of `geo_action_envelope` are satisfiable.

Route. `geo_hasDerivAt_dilogSeries`: `∂/∂ℓ Li₂(±e^{ℓ}) = -log(1 ∓ e^{ℓ})`; then
`exp(∂S/∂ℓz) = -(1 - z)(1 - z/x)/((1 + z)(1 + z/x) x) = R_z` and
`exp(∂S/∂ℓx) = -x²(1 + z/x)/(z(1 - z/x)) = R_x` at `Q = -1`. Analyticity: power series inside the
disc composed with `exp`. At `r = 2` the real parts cancel (`log 3 + log ½ - log(3/2) = 0`) and the
imaginary parts are `πi - πi`; `∂S/∂ℓz` is continuous with values in `2πiℤ` along the lift, hence
zero near `2`.
-/

open Filter Topology

noncomputable section

namespace AJConjecture

/-- The formal action on the channel `Q = -1` (with `log Q = πi`). -/
def geoChannelAction (a : ℕ) (ℓ : ℂ × ℂ) : ℂ :=
  Complex.I * Real.pi * (ℓ.2 - ℓ.1) + dilogSeries 1 - dilogSeries (-1)
    - dilogSeries (Complex.exp ℓ.2) + dilogSeries (-Complex.exp ℓ.2)
    - dilogSeries (Complex.exp (ℓ.2 - ℓ.1)) + dilogSeries (-Complex.exp (ℓ.2 - ℓ.1))
    - 2 * a * (Complex.I * Real.pi) ^ 2 - ℓ.1 * ℓ.2 + ℓ.1 ^ 2

/-- The domain of the series: `|z| < 1`, `|z/x| < 1`. -/
def geoChannelActionDomain : Set (ℂ × ℂ) :=
  {ℓ | ‖Complex.exp ℓ.2‖ < 1 ∧ ‖Complex.exp (ℓ.2 - ℓ.1)‖ < 1}

/-- `Li₂` is analytic at every nonzero point of the open unit disc. -/
private theorem geo_analyticAt_dilogSeries {v : ℂ} (hv0 : v ≠ 0) (hv1 : ‖v‖ < 1) :
    AnalyticAt ℂ dilogSeries v := by
  have hopen : IsOpen {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1} :=
    isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)
  exact DifferentiableOn.analyticAt (s := {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1})
    (fun u (hu : u ≠ 0 ∧ ‖u‖ < 1) ↦
      (geo_hasDerivAt_dilogSeries hu.1 hu.2).differentiableAt.differentiableWithinAt)
    (hopen.mem_nhds ⟨hv0, hv1⟩)

/-- A point of the open unit disc is neither `1` nor `-1`. -/
private theorem geo_one_add_ne_zero_of_norm_lt {w : ℂ} (hw : ‖w‖ < 1) :
    1 - w ≠ 0 ∧ 1 + w ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [show w = 1 by linear_combination -h, norm_one] at hw
    exact lt_irrefl _ hw
  · rw [show w = -1 by linear_combination h, norm_neg, norm_one] at hw
    exact lt_irrefl _ hw

/-- The partial derivative of the action in `ℓx`. -/
private theorem geo_channelAction_hasDerivAt_fst (n : ℕ) {a b : ℂ}
    (hw : ‖Complex.exp (b - a)‖ < 1) :
    HasDerivAt (fun t ↦ geoChannelAction n (t, b))
      (-(Complex.I * Real.pi) - Complex.log (1 - Complex.exp (b - a)) +
        Complex.log (1 + Complex.exp (b - a)) - b + 2 * a) a := by
  have hw0 : Complex.exp (b - a) ≠ 0 := Complex.exp_ne_zero _
  have hnw1 : ‖-Complex.exp (b - a)‖ < 1 := by rwa [norm_neg]
  have he : HasDerivAt (fun t ↦ Complex.exp (b - t)) (Complex.exp (b - a) * -1) a :=
    ((hasDerivAt_id' a).const_sub b).cexp
  have hD1 := (geo_hasDerivAt_dilogSeries hw0 hw).comp a he
  have hD2 := (geo_hasDerivAt_dilogSeries (neg_ne_zero.2 hw0) hnw1).comp a he.neg
  have hπ := ((hasDerivAt_id' a).const_sub b).const_mul (Complex.I * Real.pi)
  have h := (((((((((hπ.add_const (dilogSeries 1)).sub_const (dilogSeries (-1))).sub_const
    (dilogSeries (Complex.exp b))).add_const (dilogSeries (-Complex.exp b))).sub hD1).add
    hD2).sub_const (2 * n * (Complex.I * Real.pi) ^ 2)).sub
    ((hasDerivAt_id' a).mul_const b)).add (hasDerivAt_pow 2 a))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
  · simp only [geoChannelAction, Pi.add_apply, Pi.sub_apply, Function.comp_apply, Pi.neg_apply]
  · simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, sub_neg_eq_add]
    field_simp

/-- The partial derivative of the action in `ℓz`. -/
private theorem geo_channelAction_hasDerivAt_snd (n : ℕ) {a b : ℂ} (hz : ‖Complex.exp b‖ < 1)
    (hw : ‖Complex.exp (b - a)‖ < 1) :
    HasDerivAt (fun t ↦ geoChannelAction n (a, t))
      (Complex.I * Real.pi + Complex.log (1 - Complex.exp b) - Complex.log (1 + Complex.exp b) +
        Complex.log (1 - Complex.exp (b - a)) - Complex.log (1 + Complex.exp (b - a)) - a) b := by
  have hz0 : Complex.exp b ≠ 0 := Complex.exp_ne_zero _
  have hw0 : Complex.exp (b - a) ≠ 0 := Complex.exp_ne_zero _
  have hnz1 : ‖-Complex.exp b‖ < 1 := by rwa [norm_neg]
  have hnw1 : ‖-Complex.exp (b - a)‖ < 1 := by rwa [norm_neg]
  have he : HasDerivAt (fun t ↦ Complex.exp (t - a)) (Complex.exp (b - a) * 1) b :=
    ((hasDerivAt_id' b).sub_const a).cexp
  have hexp := Complex.hasDerivAt_exp b
  have hexpn := hexp.neg
  have hen := he.neg
  have hL1 := geo_hasDerivAt_dilogSeries hz0 hz
  have hL2 := geo_hasDerivAt_dilogSeries (neg_ne_zero.2 hz0) hnz1
  have hL3 := geo_hasDerivAt_dilogSeries hw0 hw
  have hL4 := geo_hasDerivAt_dilogSeries (neg_ne_zero.2 hw0) hnw1
  have hD1 := hL1.comp b hexp
  have hD2 := hL2.comp b hexpn
  have hD3 := hL3.comp b he
  have hD4 := hL4.comp_of_eq b hen (by rw [Pi.neg_apply])
  have hπ := ((hasDerivAt_id' b).sub_const a).const_mul (Complex.I * Real.pi)
  have h := (((((((((hπ.add_const (dilogSeries 1)).sub_const (dilogSeries (-1))).sub hD1).add
    hD2).sub hD3).add hD4).sub_const (2 * n * (Complex.I * Real.pi) ^ 2)).sub
    ((hasDerivAt_id' b).const_mul a)).add_const (a ^ 2))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
  · simp only [geoChannelAction, Pi.add_apply, Pi.sub_apply, Function.comp_apply, Pi.neg_apply]
  · field_simp
    ring_nf

/-- The displayed action is analytic on its domain. -/
private theorem geo_channelAction_analyticAt (n : ℕ) {ℓ : ℂ × ℂ}
    (hℓ : ℓ ∈ geoChannelActionDomain) : AnalyticAt ℂ (geoChannelAction n) ℓ := by
  obtain ⟨hz, hw⟩ := hℓ
  have hz0 : Complex.exp ℓ.2 ≠ 0 := Complex.exp_ne_zero _
  have hw0 : Complex.exp (ℓ.2 - ℓ.1) ≠ 0 := Complex.exp_ne_zero _
  have hnz : ‖-Complex.exp ℓ.2‖ < 1 := by rwa [norm_neg]
  have hnw : ‖-Complex.exp (ℓ.2 - ℓ.1)‖ < 1 := by rwa [norm_neg]
  have he1 : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ Complex.exp p.2) ℓ := analyticAt_snd.cexp'
  have he2 : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ -Complex.exp p.2) ℓ := he1.fun_neg
  have he3 : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ Complex.exp (p.2 - p.1)) ℓ :=
    (analyticAt_snd.fun_sub analyticAt_fst).cexp'
  have he4 : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ -Complex.exp (p.2 - p.1)) ℓ := he3.fun_neg
  have h1 : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ dilogSeries (Complex.exp p.2)) ℓ :=
    (geo_analyticAt_dilogSeries hz0 hz).comp_of_eq he1 rfl
  have h2 : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ dilogSeries (-Complex.exp p.2)) ℓ :=
    (geo_analyticAt_dilogSeries (neg_ne_zero.2 hz0) hnz).comp_of_eq he2 rfl
  have h3 : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ dilogSeries (Complex.exp (p.2 - p.1))) ℓ :=
    (geo_analyticAt_dilogSeries hw0 hw).comp_of_eq he3 rfl
  have h4 : AnalyticAt ℂ (fun p : ℂ × ℂ ↦ dilogSeries (-Complex.exp (p.2 - p.1))) ℓ :=
    (geo_analyticAt_dilogSeries (neg_ne_zero.2 hw0) hnw).comp_of_eq he4 rfl
  unfold geoChannelAction
  exact (((((((((analyticAt_const.fun_mul (analyticAt_snd.fun_sub analyticAt_fst)).fun_add
    analyticAt_const).fun_sub analyticAt_const).fun_sub h1).fun_add h2).fun_sub h3).fun_add
    h4).fun_sub analyticAt_const).fun_sub (analyticAt_fst.fun_mul analyticAt_snd)).fun_add
    (analyticAt_fst.fun_pow 2)

/-- The internal derivative `∂S/∂ℓz` of the action at a point of its domain. -/
private theorem geo_channelAction_fderiv_snd (n : ℕ) {ℓ : ℂ × ℂ}
    (hℓ : ℓ ∈ geoChannelActionDomain) :
    fderiv ℂ (geoChannelAction n) ℓ (0, 1) =
      Complex.I * Real.pi + Complex.log (1 - Complex.exp ℓ.2) -
        Complex.log (1 + Complex.exp ℓ.2) + Complex.log (1 - Complex.exp (ℓ.2 - ℓ.1)) -
        Complex.log (1 + Complex.exp (ℓ.2 - ℓ.1)) - ℓ.1 := by
  have hS : HasFDerivAt (geoChannelAction n) (fderiv ℂ (geoChannelAction n) ℓ) ℓ :=
    (geo_channelAction_analyticAt n hℓ).differentiableAt.hasFDerivAt
  obtain ⟨p, q⟩ := ℓ
  obtain ⟨hz, hw⟩ := hℓ
  dsimp only at hz hw ⊢
  have hl2 : HasDerivAt (fun t : ℂ ↦ (p, t)) ((0 : ℂ), (1 : ℂ)) q :=
    (hasDerivAt_const q p).prodMk (hasDerivAt_id q)
  have hc2 := hS.comp_hasDerivAt q hl2
  rw [Function.comp_def] at hc2
  exact hc2.unique (geo_channelAction_hasDerivAt_snd n hz hw)

/-- The internal derivative along the continuous lift, as a function of `r`. -/
private def geoLiftDeriv (r : ℂ) : ℂ :=
  Complex.log (1 - -1 / r) - Complex.log (1 + -1 / r) + Complex.log (1 - (r - 1) / (r + 1)) -
    Complex.log (1 + (r - 1) / (r + 1)) - Complex.log (-geoX r)

/-- `geoLiftDeriv` is continuous at `r = 2`. -/
private theorem geoLiftDeriv_continuousAt : ContinuousAt geoLiftDeriv 2 := by
  have hm : ∀ t : ℝ, 0 < t → ∀ c : ℂ, c = t → c ∈ Complex.slitPlane := fun t ht c hc ↦ by
    rw [hc]
    exact Complex.ofReal_mem_slitPlane.2 ht
  have h1 : ContinuousAt (fun r : ℂ ↦ Complex.log (1 - -1 / r)) 2 :=
    ContinuousAt.clog (by fun_prop (disch := norm_num))
      (hm (3 / 2) (by norm_num) _ (by push_cast; norm_num))
  have h2 : ContinuousAt (fun r : ℂ ↦ Complex.log (1 + -1 / r)) 2 :=
    ContinuousAt.clog (by fun_prop (disch := norm_num))
      (hm (1 / 2) (by norm_num) _ (by push_cast; norm_num))
  have h3 : ContinuousAt (fun r : ℂ ↦ Complex.log (1 - (r - 1) / (r + 1))) 2 :=
    ContinuousAt.clog (by fun_prop (disch := norm_num))
      (hm (2 / 3) (by norm_num) _ (by push_cast; norm_num))
  have h4 : ContinuousAt (fun r : ℂ ↦ Complex.log (1 + (r - 1) / (r + 1))) 2 :=
    ContinuousAt.clog (by fun_prop (disch := norm_num))
      (hm (4 / 3) (by norm_num) _ (by push_cast; norm_num))
  have h5 : ContinuousAt (fun r : ℂ ↦ Complex.log (-geoX r)) 2 := by
    unfold geoX
    exact ContinuousAt.clog (by fun_prop (disch := norm_num))
      (hm (3 / 2) (by norm_num) _ (by push_cast; norm_num))
  exact ((((h1.sub h2).add h3).sub h4).sub h5)

/-- `geoLiftDeriv 2 = log(3/2) - log(1/2) + log(2/3) - log(4/3) - log(3/2) = 0`. -/
private theorem geoLiftDeriv_two : geoLiftDeriv 2 = 0 := by
  have e : geoLiftDeriv 2 = ((Real.log (3 / 2) - Real.log (1 / 2) + Real.log (2 / 3) -
      Real.log (4 / 3) - Real.log (3 / 2) : ℝ) : ℂ) := by
    rw [geoLiftDeriv, geoX, show (1 - -1 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; norm_num,
      show (1 + -1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; norm_num,
      show (1 - (2 - 1) / (2 + 1) : ℂ) = ((2 / 3 : ℝ) : ℂ) by push_cast; norm_num,
      show (1 + (2 - 1) / (2 + 1) : ℂ) = ((4 / 3 : ℝ) : ℂ) by push_cast; norm_num,
      show (-((1 + 2) / (2 * (1 - 2))) : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; norm_num,
      ← Complex.ofReal_log (by norm_num), ← Complex.ofReal_log (by norm_num),
      ← Complex.ofReal_log (by norm_num), ← Complex.ofReal_log (by norm_num)]
    push_cast
    ring
  rw [e, Complex.ofReal_eq_zero]
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, Real.log_one]
  push_cast
  ring

/-- The displayed action is a branch of the formal action on the channel. -/
theorem geo_channelAction_branch (a : ℕ) :
    GeoChannelActionBranch (geoChannelAction a) geoChannelActionDomain := by
  have hopen : IsOpen geoChannelActionDomain := by
    have h1 : Continuous fun ℓ : ℂ × ℂ ↦ ‖Complex.exp ℓ.2‖ := by fun_prop
    have h2 : Continuous fun ℓ : ℂ × ℂ ↦ ‖Complex.exp (ℓ.2 - ℓ.1)‖ := by fun_prop
    exact (isOpen_lt h1 continuous_const).inter (isOpen_lt h2 continuous_const)
  refine ⟨hopen, fun ℓ hℓ ↦ geo_channelAction_analyticAt a hℓ, fun ℓ hℓ ↦ ?_⟩
  have hS : HasFDerivAt (geoChannelAction a) (fderiv ℂ (geoChannelAction a) ℓ) ℓ :=
    (geo_channelAction_analyticAt a hℓ).differentiableAt.hasFDerivAt
  obtain ⟨p, q⟩ := ℓ
  obtain ⟨hz, hw⟩ := hℓ
  dsimp only at hz hw ⊢
  have hz' := geo_one_add_ne_zero_of_norm_lt hz
  have hw' := geo_one_add_ne_zero_of_norm_lt hw
  have hl1 : HasDerivAt (fun t : ℂ ↦ (t, q)) ((1 : ℂ), (0 : ℂ)) p :=
    (hasDerivAt_id p).prodMk (hasDerivAt_const p q)
  have hl2 : HasDerivAt (fun t : ℂ ↦ (p, t)) ((0 : ℂ), (1 : ℂ)) q :=
    (hasDerivAt_const q p).prodMk (hasDerivAt_id q)
  have hc1 := hS.comp_hasDerivAt p hl1
  have hc2 := hS.comp_hasDerivAt q hl2
  rw [Function.comp_def] at hc1 hc2
  have hd1 := hc1.unique (geo_channelAction_hasDerivAt_fst a hw)
  have hd2 := hc2.unique (geo_channelAction_hasDerivAt_snd a hz hw)
  have hx0 : Complex.exp p ≠ 0 := Complex.exp_ne_zero _
  have hz0 : Complex.exp q ≠ 0 := Complex.exp_ne_zero _
  have hwq : Complex.exp (q - p) = Complex.exp q / Complex.exp p := Complex.exp_sub _ _
  rw [hwq] at hw'
  refine ⟨?_, ?_⟩
  · rw [hd1, show -(Complex.I * Real.pi) - Complex.log (1 - Complex.exp (q - p)) +
        Complex.log (1 + Complex.exp (q - p)) - q + 2 * p =
        Complex.log (1 + Complex.exp (q - p)) + (p + p) -
          (Complex.log (1 - Complex.exp (q - p)) + q + Real.pi * Complex.I) by ring,
      Complex.exp_sub, Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add,
      hwq, Complex.exp_log hw'.2, Complex.exp_log hw'.1, Complex.exp_pi_mul_I, geoRatioX]
    field_simp
    ring
  · rw [hd2, show Complex.I * Real.pi + Complex.log (1 - Complex.exp q) -
        Complex.log (1 + Complex.exp q) + Complex.log (1 - Complex.exp (q - p)) -
        Complex.log (1 + Complex.exp (q - p)) - p =
        Real.pi * Complex.I + Complex.log (1 - Complex.exp q) +
          Complex.log (1 - Complex.exp (q - p)) -
          (Complex.log (1 + Complex.exp q) + Complex.log (1 + Complex.exp (q - p)) + p) by ring,
      Complex.exp_sub, Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add,
      hwq, Complex.exp_log hw'.2, Complex.exp_log hw'.1, Complex.exp_log hz'.1,
      Complex.exp_log hz'.2, Complex.exp_pi_mul_I, geoRatioZ]
    field_simp
    ring

/-- Near `r = 2` the continuous lift `ℓ(r) = (log(-x(r)) + πi, log(1/r) + πi)` of the critical
curve lies in the domain and is admissible (`∂S/∂ℓz = 0`) on a whole complex ball. (The principal
lift of `geo_channelAction_admissible_near_two` crosses the branch cut of `log` at `x(2) = -3/2`:
for `r = 2 - iδ`, `δ > 0` small, its internal derivative is `2πi`.) -/
theorem geo_channelAction_admissible_near_two_lift (a : ℕ) :
    ∃ ε > 0, ∀ r ∈ Metric.ball (2 : ℂ) ε,
      (Complex.log (-geoX r) + Real.pi * Complex.I,
          Complex.log (1 / r) + Real.pi * Complex.I) ∈ geoChannelActionDomain ∧
        fderiv ℂ (geoChannelAction a)
          (Complex.log (-geoX r) + Real.pi * Complex.I,
            Complex.log (1 / r) + Real.pi * Complex.I) (0, 1) = 0 := by
  have hev : ∀ᶠ r in 𝓝 (2 : ℂ), r ≠ 0 ∧ r ≠ 1 ∧ r ≠ -1 ∧ ‖-1 / r‖ < 1 ∧
      ‖(r - 1) / (r + 1)‖ < 1 ∧ ‖geoLiftDeriv r‖ < 2 * Real.pi := by
    have h1 : ∀ᶠ r in 𝓝 (2 : ℂ), r ≠ 0 := eventually_ne_nhds (by norm_num)
    have h2 : ∀ᶠ r in 𝓝 (2 : ℂ), r ≠ 1 := eventually_ne_nhds (by norm_num)
    have h3 : ∀ᶠ r in 𝓝 (2 : ℂ), r ≠ -1 := eventually_ne_nhds (by norm_num)
    have h4 : ∀ᶠ r in 𝓝 (2 : ℂ), ‖-1 / r‖ < 1 :=
      ContinuousAt.eventually_lt (by fun_prop (disch := norm_num)) continuousAt_const
        (by norm_num)
    have h5 : ∀ᶠ r in 𝓝 (2 : ℂ), ‖(r - 1) / (r + 1)‖ < 1 :=
      ContinuousAt.eventually_lt (by fun_prop (disch := norm_num)) continuousAt_const
        (by norm_num)
    have h6 : ∀ᶠ r in 𝓝 (2 : ℂ), ‖geoLiftDeriv r‖ < 2 * Real.pi :=
      ContinuousAt.eventually_lt geoLiftDeriv_continuousAt.norm continuousAt_const
        (by rw [geoLiftDeriv_two, norm_zero]; positivity)
    filter_upwards [h1, h2, h3, h4, h5, h6] with r a b c d e f using ⟨a, b, c, d, e, f⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨ε, hε, fun r hr ↦ ?_⟩
  obtain ⟨hr0, hr1, hrm1, hz, hw, hg⟩ := hball r hr
  have hp : r + 1 ≠ 0 := fun h ↦ hrm1 (by linear_combination h)
  have hm : 1 - r ≠ 0 := fun h ↦ hr1 (by linear_combination -h)
  have hm' : r - 1 ≠ 0 := sub_ne_zero.2 hr1
  have hp' : 1 + r ≠ 0 := by rwa [add_comm]
  have hX : -geoX r ≠ 0 := neg_ne_zero.2 (div_ne_zero (by rwa [add_comm]) (mul_ne_zero hr0 hm))
  have hexp2 : Complex.exp (Complex.log (1 / r) + Real.pi * Complex.I) = -1 / r := by
    rw [Complex.exp_add, Complex.exp_log (one_div_ne_zero hr0), Complex.exp_pi_mul_I]
    ring
  have hexp1 : Complex.exp (Complex.log (-geoX r) + Real.pi * Complex.I) = geoX r := by
    rw [Complex.exp_add, Complex.exp_log hX, Complex.exp_pi_mul_I]
    ring
  have hexp21 : Complex.exp ((Complex.log (1 / r) + Real.pi * Complex.I) -
      (Complex.log (-geoX r) + Real.pi * Complex.I)) = (r - 1) / (r + 1) := by
    rw [Complex.exp_sub, hexp1, hexp2, geoX]
    field_simp
    ring
  have hdom : (Complex.log (-geoX r) + Real.pi * Complex.I,
      Complex.log (1 / r) + Real.pi * Complex.I) ∈ geoChannelActionDomain :=
    ⟨by dsimp only; rwa [hexp2], by dsimp only; rwa [hexp21]⟩
  refine ⟨hdom, ?_⟩
  have e1 : 1 - -1 / r = (r + 1) / r := by field_simp; ring
  have e2 : 1 + -1 / r = (r - 1) / r := by field_simp; ring
  have e3 : 1 - (r - 1) / (r + 1) = 2 / (r + 1) := by field_simp; ring
  have e4 : 1 + (r - 1) / (r + 1) = 2 * r / (r + 1) := by field_simp; ring
  have e5 : -geoX r = (r + 1) / (r * (r - 1)) := by
    rw [geoX]
    field_simp
    ring
  have hexpg : Complex.exp (geoLiftDeriv r) = 1 := by
    rw [geoLiftDeriv, Complex.exp_sub, Complex.exp_sub, Complex.exp_add, Complex.exp_sub, e1, e2,
      e3, e4, e5, Complex.exp_log (div_ne_zero hp hr0), Complex.exp_log (div_ne_zero hm' hr0),
      Complex.exp_log (div_ne_zero two_ne_zero hp),
      Complex.exp_log (div_ne_zero (mul_ne_zero two_ne_zero hr0) hp),
      Complex.exp_log (div_ne_zero hp (mul_ne_zero hr0 hm'))]
    field_simp
  have hg0 : geoLiftDeriv r = 0 := by
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hexpg
    rw [hn] at hg
    have hnorm : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ = |(n : ℝ)| * (2 * Real.pi) := by
      rw [norm_mul, Complex.norm_intCast, norm_mul, Complex.norm_I, mul_one, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat]
    rw [hnorm] at hg
    have hn1 : |(n : ℝ)| < 1 := by nlinarith [Real.pi_pos]
    have hn0 : n = 0 := by
      rw [abs_lt] at hn1
      obtain ⟨h1, h2⟩ := hn1
      have h1' : (-1 : ℤ) < n := by exact_mod_cast h1
      have h2' : n < (1 : ℤ) := by exact_mod_cast h2
      omega
    rw [hn, hn0]
    simp
  rw [geo_channelAction_fderiv_snd a hdom]
  dsimp only
  rw [hexp2, hexp21, ← hg0, geoLiftDeriv]
  ring

end AJConjecture
