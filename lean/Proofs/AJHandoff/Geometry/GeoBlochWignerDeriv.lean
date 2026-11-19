import Mathlib
import AJHandoff.Geometry.GeoBlochWignerSymm
import AJHandoff.Geometry.GeoBlochWignerDerivDisc

/-!
# The differential of the Bloch–Wigner dilogarithm on `ℂ ∖ {0, 1}` (crux)

`dD = η(z, 1 - z)` at every `z ≠ 0, 1`, including the unit circle, where the library's definition
switches formula.

Route. Inside the disc: `geo_hasFDerivAt_blochWigner_of_norm_lt_one`. Outside: `D(z) = -D(1/z)`
(`geo_blochWigner_inv`) and the chain rule with `z ↦ 1/z`; the form is invariant:
`-η(1/z, 1 - 1/z) = η(z, 1 - z)` because `1 - 1/z = -(1 - z)/z` and `η(-1, ·) = 0`.
On `|z₀| = 1`, `z₀ ≠ 1`: take a small ball `B` around `z₀` avoiding `0, 1`. The convex open set
`B ∩ {|z| < 1}` carries the derivative `geoBWDeriv`, which is continuous at `z₀`, and `D` is
continuous (`geo_continuous_blochWigner`); `hasFDerivWithinAt_closure_of_tendsto_fderiv` gives the
derivative within its closure. The outer part is the image of an inner part near `conj z₀` under
`z ↦ 1/z`; compose. The two closures cover a neighbourhood of `z₀`
(`HasFDerivWithinAt.union`, `hasFDerivWithinAt_of_mem_nhds`).
-/

open Filter Topology

noncomputable section

namespace AJConjecture

/-- The regulator form `geoBWDeriv z` depends continuously on `z ≠ 0, 1`. -/
private theorem continuousAt_geoBWDeriv {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    ContinuousAt geoBWDeriv z := by
  have h1 : ContinuousAt (fun w : ℂ ↦ Real.log ‖w‖) z :=
    (Real.continuousAt_log (norm_ne_zero_iff.2 hz0)).comp continuous_norm.continuousAt
  have h2 : ContinuousAt (fun w : ℂ ↦ Real.log ‖1 - w‖) z :=
    (Real.continuousAt_log (norm_ne_zero_iff.2 (sub_ne_zero.2 hz1.symm))).comp
      (f := fun w : ℂ ↦ ‖1 - w‖) (by fun_prop)
  have h3 : ContinuousAt (fun w : ℂ ↦ (-(1 - w)⁻¹ : ℂ)) z :=
    ((continuousAt_const.sub continuousAt_id).inv₀ (sub_ne_zero.2 hz1.symm)).neg
  have h4 : ContinuousAt (fun w : ℂ ↦ w⁻¹) z := continuousAt_inv₀ hz0
  have hL : Continuous fun c : ℂ ↦ Complex.imCLM.comp (c • ContinuousLinearMap.id ℝ ℂ) :=
    (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.imCLM).continuous.comp
      (continuous_id.smul continuous_const)
  have h3' : ContinuousAt (fun w : ℂ ↦
      Complex.imCLM.comp ((-(1 - w)⁻¹ : ℂ) • ContinuousLinearMap.id ℝ ℂ)) z :=
    hL.continuousAt.comp (f := fun w : ℂ ↦ (-(1 - w)⁻¹ : ℂ)) h3
  have h4' : ContinuousAt (fun w : ℂ ↦
      Complex.imCLM.comp (w⁻¹ • ContinuousLinearMap.id ℝ ℂ)) z :=
    hL.continuousAt.comp (f := fun w : ℂ ↦ w⁻¹) h4
  have e : geoBWDeriv = fun w ↦
      Real.log ‖w‖ • (Complex.imCLM.comp ((-(1 - w)⁻¹ : ℂ) • ContinuousLinearMap.id ℝ ℂ)) -
      Real.log ‖1 - w‖ • (Complex.imCLM.comp (w⁻¹ • ContinuousLinearMap.id ℝ ℂ)) := rfl
  rw [e]
  exact (h1.smul h3').sub (h2.smul h4')

/-- `D` has derivative `η(z, 1 - z)` within the closed unit disc at each `z ≠ 0, 1` of the
closed disc. On the circle this is the extension of the derivative from the open disc. -/
private theorem hasFDerivWithinAt_blochWigner_closedBall {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hz : ‖z‖ ≤ 1) :
    HasFDerivWithinAt blochWigner (geoBWDeriv z) (Metric.closedBall 0 1) z := by
  rcases hz.lt_or_eq with hlt | heq
  · exact (geo_hasFDerivAt_blochWigner_of_norm_lt_one hz0 hlt).hasFDerivWithinAt
  have hr : (0 : ℝ) < 1 := one_pos
  set s : Set ℂ := Metric.ball z 1 ∩ Metric.ball 0 1 with hs_def
  have hs : ∀ w ∈ s, w ≠ 0 ∧ ‖w‖ < 1 := by
    intro w hw
    refine ⟨?_, mem_ball_zero_iff.1 hw.2⟩
    rintro rfl
    have := hw.1
    rw [Metric.mem_ball, dist_comm, dist_zero_right, heq] at this
    exact lt_irrefl _ this
  have hdiff : DifferentiableOn ℝ blochWigner s := fun w hw ↦
    (geo_hasFDerivAt_blochWigner_of_norm_lt_one (hs w hw).1
      (hs w hw).2).differentiableAt.differentiableWithinAt
  have hlim : Tendsto (fun y ↦ fderiv ℝ blochWigner y) (𝓝[s] z) (𝓝 (geoBWDeriv z)) := by
    refine ((continuousAt_geoBWDeriv hz0 hz1).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (geo_hasFDerivAt_blochWigner_of_norm_lt_one (hs w hw).1 (hs w hw).2).fderiv.symm
  have h := hasFDerivWithinAt_closure_of_tendsto_fderiv hdiff
    ((convex_ball _ _).inter (convex_ball _ _)) (Metric.isOpen_ball.inter Metric.isOpen_ball)
    (fun y _ ↦ geo_continuous_blochWigner.continuousWithinAt) hlim
  have hsub : Metric.closedBall (0 : ℂ) 1 ∩ Metric.ball z 1 ⊆ closure s := by
    rw [Set.inter_comm, ← closure_ball (0 : ℂ) one_ne_zero]
    exact Metric.isOpen_ball.inter_closure
  exact (hasFDerivWithinAt_inter (Metric.ball_mem_nhds z hr)).1 (h.mono hsub)

/-- The regulator form is invariant under `z ↦ 1/z` up to sign:
`-η(1/z, 1 - 1/z) ∘ d(1/z) = η(z, 1 - z)`. -/
private theorem neg_geoBWDeriv_inv_comp {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    -((geoBWDeriv z⁻¹).comp ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
      (-(z ^ 2)⁻¹)).restrictScalars ℝ)) = geoBWDeriv z := by
  have hz1' : 1 - z ≠ 0 := sub_ne_zero.2 hz1.symm
  have hz1'' : z - 1 ≠ 0 := sub_ne_zero.2 hz1
  refine ContinuousLinearMap.ext fun h ↦ ?_
  simp only [neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, smul_eq_mul]
  rw [geoBWDeriv_apply, geoBWDeriv_apply]
  have e1 : Real.log ‖z⁻¹‖ = -Real.log ‖z‖ := by rw [norm_inv, Real.log_inv]
  have e2 : Real.log ‖1 - z⁻¹‖ = Real.log ‖1 - z‖ - Real.log ‖z‖ := by
    rw [show 1 - z⁻¹ = -(1 - z) / z by field_simp; ring, norm_div, norm_neg,
      Real.log_div (norm_ne_zero_iff.2 hz1') (norm_ne_zero_iff.2 hz0)]
  have e3 : -(h * -(z ^ 2)⁻¹) / (1 - z⁻¹) = -h / (1 - z) - h / z := by
    field_simp
    ring
  have e4 : h * -(z ^ 2)⁻¹ / z⁻¹ = -(h / z) := by
    field_simp
  rw [e1, e2, e3, e4, Complex.sub_im, Complex.neg_im]
  ring

/-- `D` has derivative `η(z, 1 - z)` within `{|w| ≥ 1}` at each `z ≠ 0, 1` with `|z| ≥ 1`. -/
private theorem hasFDerivWithinAt_blochWigner_outer {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hz : 1 ≤ ‖z‖) :
    HasFDerivWithinAt blochWigner (geoBWDeriv z) {w : ℂ | 1 ≤ ‖w‖} z := by
  have hz0' : z⁻¹ ≠ 0 := inv_ne_zero hz0
  have hz1' : z⁻¹ ≠ 1 := fun h ↦ hz1 (by rw [← inv_inv z, h, inv_one])
  have hn : ‖z⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hz
  have hinv : HasFDerivAt (fun w : ℂ ↦ w⁻¹) ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
      (-(z ^ 2)⁻¹)).restrictScalars ℝ) z :=
    (hasDerivAt_inv hz0).hasFDerivAt.restrictScalars ℝ
  have hmaps : Set.MapsTo (fun w : ℂ ↦ w⁻¹) {w : ℂ | 1 ≤ ‖w‖} (Metric.closedBall 0 1) := by
    intro w hw
    rw [Set.mem_ofPred_eq] at hw
    rw [mem_closedBall_zero_iff, norm_inv]
    exact inv_le_one_of_one_le₀ hw
  have hc := ((hasFDerivWithinAt_blochWigner_closedBall hz0' hz1' hn).comp z
    hinv.hasFDerivWithinAt hmaps).neg
  rw [neg_geoBWDeriv_inv_comp hz0 hz1] at hc
  have hD : ∀ w : ℂ, w ≠ 0 → blochWigner w = -blochWigner w⁻¹ := fun w hw ↦ by
    rw [geo_blochWigner_inv hw, neg_neg]
  refine hc.congr (fun w hw ↦ ?_) (hD z hz0)
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [Set.mem_ofPred_eq, norm_zero] at hw
    linarith
  exact hD w hw0

/-- `dD = η(z, 1 - z)` at every `z ≠ 0, 1`. -/
theorem geo_hasFDerivAt_blochWigner {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    HasFDerivAt blochWigner (geoBWDeriv z) z := by
  rcases lt_trichotomy ‖z‖ 1 with h | h | h
  · exact geo_hasFDerivAt_blochWigner_of_norm_lt_one hz0 h
  · have hu := (hasFDerivWithinAt_blochWigner_closedBall hz0 hz1 h.le).union
      (hasFDerivWithinAt_blochWigner_outer hz0 hz1 h.ge)
    refine hu.hasFDerivAt (Filter.univ_mem' fun w ↦ ?_)
    rcases le_total ‖w‖ 1 with hw | hw
    · exact Or.inl (mem_closedBall_zero_iff.2 hw)
    · exact Or.inr hw
  · refine (hasFDerivWithinAt_blochWigner_outer hz0 hz1 h.le).hasFDerivAt ?_
    have hopen : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
    exact Filter.mem_of_superset (hopen.mem_nhds h) fun w (hw : 1 < ‖w‖) ↦ (le_of_lt hw)

/-- Along a differentiable path avoiding `0, 1`: `(D ∘ γ)' = η(γ, 1 - γ)(γ')`. -/
theorem geo_hasDerivAt_blochWigner_comp {γ : ℝ → ℂ} {γ' : ℂ} {t : ℝ}
    (hγ : HasDerivAt γ γ' t) (h0 : γ t ≠ 0) (h1 : γ t ≠ 1) :
    HasDerivAt (fun s ↦ blochWigner (γ s)) (geoBWDeriv (γ t) γ') t :=
  (geo_hasFDerivAt_blochWigner h0 h1).comp_hasDerivAt t hγ

end AJConjecture
