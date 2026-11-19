import Mathlib
import AJHandoff.Geometry.GeoRegulator
import AJHandoff.Geometry.GeoKernelChannel

/-!
# The normalized critical action is `V_S = -2U` (G-ACTION)

Local branches of the formal action on the channel `Q = -1` are functions `S(ℓx, ℓz)` of the
logarithmic coordinates `ℓx = log x`, `ℓz = log z`, analytic on an open set, whose exponentiated
partial derivatives are the formal critical ratios: `exp(∂S/∂ℓx) = R_x`, `exp(∂S/∂ℓz) = R_z`
(`GeoChannelActionBranch`; any two branches differ locally by a constant plus integral multiples of
`2πi ℓx` and `2πi ℓz`). The critical curve of the channel is parametrized by `r`:
`x = x(r)`, `y = 1/r`, `z = -1/r` (`T(x(r), 1/r) = 0`). A lift `ℓ(r)` of it is admissible when
the internal derivative vanishes exactly, `∂S/∂ℓz(ℓ(r)) = 0` (the integral branch slope of `ℓz`
removed).

* Envelope (`geo_action_envelope`): `d S(ℓ(r))/dr = λ(r) ℓx'(r)` with `λ = ∂S/∂ℓx(ℓ(r))` a branch of
  `log L(r)`, i.e. `dS_crit = log L dlog x`.
* Normalization (`geo_action_normalized`): for holomorphic branches `ℓx` of `log x(r)`, `λ` of
  `log L(r)` and a primitive `s` of `λ ℓx'` on a preconnected open `Ω ⊆ ℂ ∖ {0, ±1}`, the real
  primitive `V = Im s - Im λ · Re ℓx` (that is `Im S_crit - arg L log|x|`) satisfies
  `dV = -2η(M, L)` along the curve, `V + 2U` is constant on `Ω`, and `V(1/2) = 0` forces
  `V = -2U` on `Ω`. The values of `-2U`: `0` at the punctures, `-4G` at `r = i`, `+4G` at `r = -i`
  (`y = i`, the positive complete branch).

The local derivatives choose no physical contour, additive constant or dominant sequence; the
basepoint `r = 1/2` fixes the constant.

Route. Envelope: chain rule (`HasFDerivAt.comp_hasDerivAt`) and `geo_channel_critical_iff` with
`x = x(r)`, `y = 1/r` (`T = 0` by the `r`-quadratic). Normalization: `V` is real differentiable with
`dV = log|L| d arg x - log|x| d arg L = -η(x, L) = -2η(M, L)` (Im/Re of `λ ℓx'`, with
`Re ℓx = log|x|`, `Im λ` a continuous argument of `L`); `geo_reg_hasDerivAt` gives
`d(2U) = 2η(M, L)`; so `V + 2U` has zero differential on the preconnected open `Ω`
(`IsOpen.is_const_of_fderiv_eq_zero`). At `r = 1/2`, `U = 0` (`geo_blochWigner_ofReal`).
-/

open Filter Topology

noncomputable section

namespace AJConjecture

/-- A local branch of the formal action on the channel `Q = -1` over an open set `Ω` of
logarithmic coordinates `(ℓx, ℓz)`. -/
def GeoChannelActionBranch (S : ℂ × ℂ → ℂ) (Ω : Set (ℂ × ℂ)) : Prop :=
  IsOpen Ω ∧ AnalyticOnNhd ℂ S Ω ∧ ∀ ℓ ∈ Ω,
    Complex.exp (fderiv ℂ S ℓ (1, 0)) =
        geoRatioX 1 (Complex.exp ℓ.1) (-1) (Complex.exp ℓ.2) ∧
      Complex.exp (fderiv ℂ S ℓ (0, 1)) =
        geoRatioZ 1 (Complex.exp ℓ.1) (-1) (Complex.exp ℓ.2)

/-- The outer shift on the critical curve: `R_x(x(r), -1, -1/r) = L(r)`. -/
private theorem geo_ratioX_channel_param {r : ℂ} (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hrm1 : r ≠ -1) :
    geoRatioX 1 (geoX r) (-1) (-1 / r) = geoL r := by
  have hp : 1 + r ≠ 0 := fun h ↦ hrm1 (by linear_combination h)
  have hm : 1 - r ≠ 0 := fun h ↦ hr1 (by linear_combination -h)
  have e1 : -1 / r * -1 / geoX r = (1 - r) / (1 + r) := by
    unfold geoX
    field_simp
  have e2 : -1 / r / (1 ^ 2 * geoX r) = -((1 - r) / (1 + r)) := by
    unfold geoX
    field_simp
  have e3 : 1 - (1 - r) / (1 + r) = 2 * r / (1 + r) := by
    field_simp
    ring
  have e4 : 1 - -((1 - r) / (1 + r)) = 2 / (1 + r) := by
    field_simp
    ring
  rw [geoRatioX, e1, e2, e3, e4, geoL, geoF, geoX]
  field_simp

/-- Envelope identity `dS_crit = log L dlog x` along an admissible lift of the critical curve. -/
theorem geo_action_envelope {S : ℂ × ℂ → ℂ} {Ω : Set (ℂ × ℂ)} (hS : GeoChannelActionBranch S Ω)
    {ℓ : ℂ → ℂ × ℂ} {r : ℂ} (hr : r ≠ 0 ∧ r ≠ 1 ∧ r ≠ -1 ∧ r ^ 2 ≠ -1)
    (hℓ : DifferentiableAt ℂ ℓ r) (hℓΩ : ℓ r ∈ Ω)
    (hexp : Complex.exp (ℓ r).1 = geoX r ∧ Complex.exp (ℓ r).2 = -1 / r)
    (hadm : fderiv ℂ S (ℓ r) (0, 1) = 0) :
    HasDerivAt (fun ρ ↦ S (ℓ ρ)) (fderiv ℂ S (ℓ r) (1, 0) * deriv (fun ρ ↦ (ℓ ρ).1) r) r ∧
      Complex.exp (fderiv ℂ S (ℓ r) (1, 0)) = geoL r := by
  obtain ⟨hr0, hr1, hrm1, -⟩ := hr
  have hS' : HasFDerivAt S (fderiv ℂ S (ℓ r)) (ℓ r) :=
    (hS.2.1 (ℓ r) hℓΩ).differentiableAt.hasFDerivAt
  have hcomp := hS'.comp_hasDerivAt r hℓ.hasDerivAt
  have hfst : deriv (fun ρ ↦ (ℓ ρ).1) r = (deriv ℓ r).1 :=
    ((hasFDerivAt_fst (𝕜 := ℂ) (p := ℓ r)).comp_hasDerivAt r hℓ.hasDerivAt).deriv
  refine ⟨?_, ?_⟩
  · have hval : fderiv ℂ S (ℓ r) (deriv ℓ r) =
        fderiv ℂ S (ℓ r) (1, 0) * deriv (fun ρ ↦ (ℓ ρ).1) r := by
      have hsplit : deriv ℓ r =
          (deriv ℓ r).1 • ((1 : ℂ), (0 : ℂ)) + (deriv ℓ r).2 • ((0 : ℂ), (1 : ℂ)) := by
        ext <;> simp
      rw [hsplit, map_add, map_smul, map_smul, hadm, smul_zero, add_zero, smul_eq_mul, hfst]
      ring
    rw [hval] at hcomp
    exact hcomp
  · rw [(hS.2.2 (ℓ r) hℓΩ).1, hexp.1, hexp.2]
    exact geo_ratioX_channel_param hr0 hr1 hrm1

/-- The differential of `U` at `z ≠ 0, ±1`: `dU(z)(h) = η(z, 1 - z)(h) - η(-z, 1 + z)(-h)`. -/
private theorem geo_action_hasFDerivAt_regPrimitive {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1)
    (hm1 : z ≠ -1) :
    HasFDerivAt geoRegPrimitive
      (geoBWDeriv z - (geoBWDeriv (-z)).comp (-ContinuousLinearMap.id ℝ ℂ)) z := by
  have hn1 : -z ≠ 1 := fun e ↦ hm1 (by rw [← e, neg_neg])
  exact (geo_hasFDerivAt_blochWigner h0 h1).sub
    ((geo_hasFDerivAt_blochWigner (neg_ne_zero.2 h0) hn1).comp z (hasFDerivAt_id z).neg)

/-- A holomorphic branch of `log g` on an open set has derivative `g'/g`. -/
private theorem geo_hasDerivAt_log_branch {g lg : ℂ → ℂ} {Ω : Set ℂ} {r c : ℂ} (hΩ : IsOpen Ω)
    (hr : r ∈ Ω) (hlg : DifferentiableOn ℂ lg Ω) (hexp : ∀ ρ ∈ Ω, Complex.exp (lg ρ) = g ρ)
    (hg : HasDerivAt g (g r * c) r) (hg0 : g r ≠ 0) : HasDerivAt lg c r := by
  have hd : HasDerivAt lg (deriv lg r) r :=
    ((hlg r hr).differentiableAt (hΩ.mem_nhds hr)).hasDerivAt
  have he' : HasDerivAt g (Complex.exp (lg r) * deriv lg r) r :=
    hd.cexp.congr_of_eventuallyEq
      (Filter.eventually_of_mem (hΩ.mem_nhds hr) fun ρ hρ ↦ (hexp ρ hρ).symm)
  have h := he'.unique hg
  rw [hexp r hr] at h
  rwa [mul_left_cancel₀ hg0 h] at hd

/-- The logarithmic derivative of `x(r) = (1 + r)/(r(1 - r))`. -/
private theorem geo_hasDerivAt_geoX {r : ℂ} (hr0 : r ≠ 0) (hp : 1 + r ≠ 0) (hm : 1 - r ≠ 0) :
    HasDerivAt geoX (geoX r * (1 / (1 + r) - 1 / r + 1 / (1 - r))) r := by
  have h := ((hasDerivAt_id' r).const_add 1).div
    ((hasDerivAt_id' r).mul ((hasDerivAt_id' r).const_sub 1)) (mul_ne_zero hr0 hm)
  show HasDerivAt (fun x ↦ (1 + x) / (x * (1 - x))) _ r
  convert h using 1
  rw [geoX]
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- The logarithmic derivative of `L(r) = ((1 + r)/(1 - r))²`. -/
private theorem geo_hasDerivAt_geoL {r : ℂ} (hp : 1 + r ≠ 0) (hm : 1 - r ≠ 0) :
    HasDerivAt geoL (geoL r * (1 / (1 + r) + 1 / (1 + r) + 1 / (1 - r) + 1 / (1 - r))) r := by
  have h := (((hasDerivAt_id' r).const_add 1).div ((hasDerivAt_id' r).const_sub 1) hm).pow 2
  show HasDerivAt (fun x ↦ ((1 + x) / (1 - x)) ^ 2) _ r
  convert h using 1
  rw [geoL, geoF]
  simp only [Pi.div_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp
  ring

/-- `V + 2U` has zero differential at every point of `Ω`. -/
private theorem geo_action_hasFDerivAt_zero {Ω : Set ℂ} (hΩ : IsOpen Ω) {lx lL s : ℂ → ℂ}
    (hlx : DifferentiableOn ℂ lx Ω) (hlL : DifferentiableOn ℂ lL Ω)
    (hexpx : ∀ r ∈ Ω, Complex.exp (lx r) = geoX r)
    (hexpL : ∀ r ∈ Ω, Complex.exp (lL r) = geoL r)
    (hs : ∀ r ∈ Ω, HasDerivAt s (lL r * deriv lx r) r) {r : ℂ} (hr : r ∈ Ω) (hr0 : r ≠ 0)
    (hr1 : r ≠ 1) (hrm1 : r ≠ -1) :
    HasFDerivAt (fun r ↦ (s r).im - (lL r).im * (lx r).re + 2 * geoRegPrimitive r)
      (0 : ℂ →L[ℝ] ℝ) r := by
  have hp : 1 + r ≠ 0 := fun h ↦ hrm1 (by linear_combination h)
  have hm : 1 - r ≠ 0 := fun h ↦ hr1 (by linear_combination -h)
  have hX0 : geoX r ≠ 0 := div_ne_zero hp (mul_ne_zero hr0 hm)
  have hL0 : geoL r ≠ 0 := pow_ne_zero 2 (div_ne_zero hp hm)
  have hdx := geo_hasDerivAt_log_branch hΩ hr hlx hexpx (geo_hasDerivAt_geoX hr0 hp hm) hX0
  have hdL := geo_hasDerivAt_log_branch hΩ hr hlL hexpL (geo_hasDerivAt_geoL hp hm) hL0
  have hds := hs r hr
  rw [hdx.deriv] at hds
  have hreX : (lx r).re = Real.log ‖1 + r‖ - Real.log ‖r‖ - Real.log ‖1 - r‖ := by
    rw [← Real.log_exp (lx r).re, ← Complex.norm_exp, hexpx r hr, geoX, norm_div, norm_mul,
      Real.log_div (norm_ne_zero_iff.2 hp) (mul_ne_zero (norm_ne_zero_iff.2 hr0)
        (norm_ne_zero_iff.2 hm)),
      Real.log_mul (norm_ne_zero_iff.2 hr0) (norm_ne_zero_iff.2 hm)]
    ring
  have hreL : (lL r).re = 2 * (Real.log ‖1 + r‖ - Real.log ‖1 - r‖) := by
    rw [← Real.log_exp (lL r).re, ← Complex.norm_exp, hexpL r hr, geoL, geoF, norm_pow,
      Real.log_pow, norm_div, Real.log_div (norm_ne_zero_iff.2 hp) (norm_ne_zero_iff.2 hm)]
    push_cast
    ring
  have h1 := Complex.imCLM.hasFDerivAt.comp r (hds.hasFDerivAt.restrictScalars ℝ)
  have h2 := Complex.imCLM.hasFDerivAt.comp r (hdL.hasFDerivAt.restrictScalars ℝ)
  have h3 := Complex.reCLM.hasFDerivAt.comp r (hdx.hasFDerivAt.restrictScalars ℝ)
  have h4 := geo_action_hasFDerivAt_regPrimitive hr0 hr1 hrm1
  refine ((h1.sub (h2.mul h3)).add (h4.const_mul 2)).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun h ↦ ?_
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    neg_apply, ContinuousLinearMap.id_apply, Complex.imCLM_apply, Complex.reCLM_apply,
    smul_eq_mul, geoBWDeriv_apply, zero_apply, Function.comp_apply]
  have e1 : h * (lL r * (1 / (1 + r) - 1 / r + 1 / (1 - r))) =
      lL r * (h / (1 + r) - h / r + h / (1 - r)) := by ring
  have e2 : h * (1 / (1 + r) + 1 / (1 + r) + 1 / (1 - r) + 1 / (1 - r)) =
      h / (1 + r) + h / (1 + r) + h / (1 - r) + h / (1 - r) := by ring
  have e3 : h * (1 / (1 + r) - 1 / r + 1 / (1 - r)) = h / (1 + r) - h / r + h / (1 - r) := by
    ring
  have e4 : -h / (1 - r) = -(h / (1 - r)) := neg_div _ _
  have e5 : - -h / (1 - -r) = h / (1 + r) := by
    rw [neg_neg, sub_neg_eq_add]
  have e6 : -h / -r = h / r := neg_div_neg_eq _ _
  rw [e1, e2, e3, e4, e5, e6, norm_neg, sub_neg_eq_add, Complex.mul_im, hreX, hreL]
  simp only [Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.add_re, Complex.sub_re]
  ring

/-- The real primitive of a normalized critical action: `dV = -2η(M, L)`, `V + 2U` is constant,
and the basepoint `V(1/2) = 0` gives `V = -2U`. -/
theorem geo_action_normalized {Ω : Set ℂ} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hsing : ∀ r ∈ Ω, r ≠ 0 ∧ r ≠ 1 ∧ r ≠ -1) {lx lL s : ℂ → ℂ}
    (hlx : DifferentiableOn ℂ lx Ω) (hlL : DifferentiableOn ℂ lL Ω)
    (hexpx : ∀ r ∈ Ω, Complex.exp (lx r) = geoX r)
    (hexpL : ∀ r ∈ Ω, Complex.exp (lL r) = geoL r)
    (hs : ∀ r ∈ Ω, HasDerivAt s (lL r * deriv lx r) r) :
    (∀ {γ : ℝ → ℂ × ℂ} {γ' : ℂ × ℂ} {t : ℝ}, HasDerivAt γ γ' t →
        (∀ᶠ τ in 𝓝 t, γ τ ∈ GeoSmoothTorusLocus ∧ geoCurveR (γ τ) ∈ Ω) →
        HasDerivAt (fun τ ↦ (s (geoCurveR (γ τ))).im -
            (lL (geoCurveR (γ τ))).im * (lx (geoCurveR (γ τ))).re)
          (-2 * geoEta (γ t).1 (γ t).2 γ'.1 γ'.2) t) ∧
      (∃ c : ℝ, ∀ r ∈ Ω, (s r).im - (lL r).im * (lx r).re + 2 * geoRegPrimitive r = c) ∧
      ((1 / 2 : ℂ) ∈ Ω → (s (1 / 2)).im - (lL (1 / 2)).im * (lx (1 / 2)).re = 0 →
        ∀ r ∈ Ω, (s r).im - (lL r).im * (lx r).re = -2 * geoRegPrimitive r) := by
  have hW : ∀ r ∈ Ω, HasFDerivAt
      (fun r ↦ (s r).im - (lL r).im * (lx r).re + 2 * geoRegPrimitive r) (0 : ℂ →L[ℝ] ℝ) r :=
    fun r hr ↦ geo_action_hasFDerivAt_zero hΩ hlx hlL hexpx hexpL hs hr (hsing r hr).1
      (hsing r hr).2.1 (hsing r hr).2.2
  obtain ⟨c, hc⟩ := hΩ.exists_is_const_of_fderiv_eq_zero hconn
    (fun r hr ↦ (hW r hr).differentiableAt.differentiableWithinAt)
    (fun r hr ↦ (hW r hr).fderiv)
  refine ⟨fun {γ γ' t} hγ hev ↦ ?_, ⟨c, hc⟩, fun hhalf hV r hr ↦ ?_⟩
  · have hU := (geo_reg_hasDerivAt hγ (hev.mono fun τ h ↦ h.1)).const_mul (-2 : ℝ)
    have hU' := hU.const_add c
    refine (hU'.congr_of_eventuallyEq (hev.mono fun τ h ↦ ?_)).congr_deriv (by ring)
    have := hc _ h.2
    simp only
    linarith
  · have hU : geoRegPrimitive (1 / 2) = 0 := by
      have h := geo_blochWigner_ofReal (1 / 2)
      have h' := geo_blochWigner_ofReal (-(1 / 2))
      push_cast at h h'
      rw [geoRegPrimitive, h, h', sub_zero]
    have hc0 := hc _ hhalf
    rw [hV, hU, mul_zero, add_zero] at hc0
    have := hc r hr
    linarith

/-- The normalized primitive `-2U` at the punctures and on the two branches over the nodes:
`0` at `r = 0, ±1` (and `∞`), `-4G` at `r = i`, `+4G` at `r = -i` (`y = 1/r = i`). -/
theorem geo_action_values :
    -2 * geoRegPrimitive 0 = 0 ∧ -2 * geoRegPrimitive 1 = 0 ∧
      -2 * geoRegPrimitive (-1) = 0 ∧
      -2 * geoRegPrimitive Complex.I = -(4 * catalanConstant) ∧
      -2 * geoRegPrimitive (-Complex.I) = 4 * catalanConstant := by
  obtain ⟨h0, h1, hm1, hI, hmI⟩ := geo_regPrimitive_values
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h0, mul_zero]
  · rw [h1, mul_zero]
  · rw [hm1, mul_zero]
  · rw [hI]
    ring
  · rw [hmI]
    ring

end AJConjecture
