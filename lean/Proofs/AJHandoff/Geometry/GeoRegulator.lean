import Mathlib
import AJHandoff.Geometry.GeoBlochWignerDeriv
import AJHandoff.Geometry.GeoCurveParam

/-!
# The regulator of the extra curve is exact: `η(M, L) = dU` (G-REG)

With `η(a, b) = log|a| d arg b - log|b| d arg a` (`geoEta`, evaluated on a tangent vector
`(a', b')` at `(a, b)` as `log‖a‖ Im(b'/b) - log‖b‖ Im(a'/a)`), and `U(r) = D(r) - D(-r)`
(`geoRegPrimitive`), the function `U ∘ r` on the smooth torus locus has differential `η(M, L)`:
along every differentiable path that stays on the locus near `t`,
`(U ∘ r ∘ γ)'(t) = η(M, L)(γ'(t))`.
The primitive is continuous in the parameter, has limits `0` at `r = 0, 1, -1, ∞` and the values
`U(±i) = ±2G` on the two branches over each node, which therefore differ.

Sign convention: this `η` is the one of the source (geometry_v2 §1); Guilloux–Marché use `-η`, so
their volume function for this normalization is `-U`.

Route. Put `ρ = r ∘ γ` (differentiable: rational in `γ` with nonzero denominator on the locus).
Near `t`, `M² = x(ρ)` and `L = f(ρ)²` (`geo_curveR_spec`), so `η(M, L) = ½ η(x, L)` and, by
`x = f/ρ`, `L = f²`, bilinearity and `η(f, f) = 0`, `η(x, L) = -2 η(ρ, f)`. On the other side,
`dU(ρ) = η(ρ, 1 - ρ) - η(-ρ, 1 + ρ) = -η(ρ, f)` by `geo_hasDerivAt_blochWigner_comp`
(`ρ ≠ 0, ±1`) and `η(-1, ·) = 0`. All identities of `η` are pointwise identities of
`log‖·‖` and logarithmic derivatives.
-/

open Filter Topology

noncomputable section

namespace AJConjecture

/-- The regulator form `η(a, b) = log|a| d arg b - log|b| d arg a` on the tangent vector
`(a', b')` at `(a, b)`: `log‖a‖ Im(b'/b) - log‖b‖ Im(a'/a)`. -/
def geoEta (a b a' b' : ℂ) : ℝ :=
  Real.log ‖a‖ * (b' / b).im - Real.log ‖b‖ * (a' / a).im

/-- On the smooth torus locus: `log‖M‖ = (log‖1 + r‖ - log‖r‖ - log‖1 - r‖)/2` and
`log‖L‖ = 2 (log‖1 + r‖ - log‖1 - r‖)`. -/
private theorem geo_log_norm_of_param {M L r : ℂ} (hr0 : r ≠ 0) (hr1 : 1 - r ≠ 0)
    (hrm1 : 1 + r ≠ 0) (hM : M ^ 2 = geoX r) (hL : L = geoL r) :
    Real.log ‖M‖ = (Real.log ‖1 + r‖ - Real.log ‖r‖ - Real.log ‖1 - r‖) / 2 ∧
      Real.log ‖L‖ = 2 * (Real.log ‖1 + r‖ - Real.log ‖1 - r‖) := by
  have n0 : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr hr0
  have n1 : ‖1 - r‖ ≠ 0 := norm_ne_zero_iff.mpr hr1
  have n2 : ‖1 + r‖ ≠ 0 := norm_ne_zero_iff.mpr hrm1
  constructor
  · have h := congrArg (fun z : ℂ ↦ Real.log ‖z‖) hM
    simp only [norm_pow, Real.log_pow, geoX, norm_div, norm_mul] at h
    rw [Real.log_div n2 (mul_ne_zero n0 n1), Real.log_mul n0 n1] at h
    push_cast at h
    linarith
  · rw [hL, geoL, geoF, norm_pow, Real.log_pow, norm_div, Real.log_div n2 n1]
    push_cast
    ring

/-- The pointwise identity behind G-REG: `η(r, 1 - r) - η(-r, 1 + r) = η(M, L)` once
`M'/M = (r'/(1 + r) - r'/r + r'/(1 - r))/2` and `L'/L = 2 r'/(1 + r) + 2 r'/(1 - r)`. -/
private theorem geo_bwDeriv_sub_eq_eta {M L M' L' r r' : ℂ} (hr0 : r ≠ 0) (hr1 : 1 - r ≠ 0)
    (hrm1 : 1 + r ≠ 0) (hM : M ^ 2 = geoX r) (hL : L = geoL r)
    (hA : M' / M = (r' / (1 + r) - r' / r + r' / (1 - r)) / 2)
    (hB : L' / L = 2 * (r' / (1 + r)) + 2 * (r' / (1 - r))) :
    geoBWDeriv r r' - geoBWDeriv (-r) (-r') = geoEta M L M' L' := by
  obtain ⟨hlM, hlL⟩ := geo_log_norm_of_param hr0 hr1 hrm1 hM hL
  rw [geoBWDeriv_apply, geoBWDeriv_apply, geoEta, hlM, hlL, hA, hB, norm_neg,
    sub_neg_eq_add, neg_neg, neg_div_neg_eq, neg_div]
  simp only [Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.div_ofNat_im,
    Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero]
  ring

/-- The derivative of `x(ρ(s))` along a differentiable path `ρ` avoiding `0, 1`. -/
private theorem geo_hasDerivAt_geoX_comp {ρ : ℝ → ℂ} {ρ' : ℂ} {t : ℝ} (hρ : HasDerivAt ρ ρ' t)
    (h0 : ρ t ≠ 0) (h1 : 1 - ρ t ≠ 0) :
    HasDerivAt (fun s ↦ geoX (ρ s))
      ((ρ' * (ρ t * (1 - ρ t)) - (1 + ρ t) * (ρ' * (1 - ρ t) + ρ t * -ρ')) /
        (ρ t * (1 - ρ t)) ^ 2) t :=
  (hρ.const_add 1).div (hρ.mul (hρ.const_sub 1)) (mul_ne_zero h0 h1)

/-- The derivative of `L(ρ(s))` along a differentiable path `ρ` avoiding `1`. -/
private theorem geo_hasDerivAt_geoL_comp {ρ : ℝ → ℂ} {ρ' : ℂ} {t : ℝ} (hρ : HasDerivAt ρ ρ' t)
    (h1 : 1 - ρ t ≠ 0) :
    HasDerivAt (fun s ↦ geoL (ρ s))
      (((2 : ℕ) : ℂ) * ((1 + ρ t) / (1 - ρ t)) ^ (2 - 1) *
        ((ρ' * (1 - ρ t) - (1 + ρ t) * -ρ') / (1 - ρ t) ^ 2)) t :=
  ((hρ.const_add 1).div (hρ.const_sub 1) h1).pow 2

/-- The logarithmic derivative of `M` along the curve, from `2 M M' = (x ∘ r)'`. -/
private theorem geo_logDeriv_M {M M' r r' : ℂ} (hM0 : M ≠ 0) (hr0 : r ≠ 0) (hr1 : 1 - r ≠ 0)
    (hrm1 : 1 + r ≠ 0) (hX : M ^ 2 = geoX r)
    (h : ((2 : ℕ) : ℂ) * M ^ (2 - 1) * M' =
      (r' * (r * (1 - r)) - (1 + r) * (r' * (1 - r) + r * -r')) / (r * (1 - r)) ^ 2) :
    M' / M = (r' / (1 + r) - r' / r + r' / (1 - r)) / 2 := by
  rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one, Nat.cast_ofNat] at h
  have key : M' / M = (2 * M * M') / (2 * M ^ 2) := by field_simp
  rw [key, h, hX, geoX]
  field_simp
  ring

/-- The logarithmic derivative of `L` along the curve, from `L' = (L ∘ r)'`. -/
private theorem geo_logDeriv_L {L L' r r' : ℂ} (hr1 : 1 - r ≠ 0) (hrm1 : 1 + r ≠ 0)
    (hL : L = geoL r)
    (h : L' = ((2 : ℕ) : ℂ) * ((1 + r) / (1 - r)) ^ (2 - 1) *
        ((r' * (1 - r) - (1 + r) * -r') / (1 - r) ^ 2)) :
    L' / L = 2 * (r' / (1 + r)) + 2 * (r' / (1 - r)) := by
  rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one, Nat.cast_ofNat] at h
  rw [h, hL, geoL, geoF]
  field_simp
  ring

/-- G-REG, the differential: `d(U ∘ r) = η(M, L)` along every differentiable path on the smooth
torus locus. -/
theorem geo_reg_hasDerivAt {γ : ℝ → ℂ × ℂ} {γ' : ℂ × ℂ} {t : ℝ} (hγ : HasDerivAt γ γ' t)
    (hE : ∀ᶠ s in 𝓝 t, γ s ∈ GeoSmoothTorusLocus) :
    HasDerivAt (fun s ↦ geoRegPrimitive (geoCurveR (γ s)))
      (geoEta (γ t).1 (γ t).2 γ'.1 γ'.2) t := by
  have hmem : γ t ∈ GeoSmoothTorusLocus := hE.self_of_nhds
  obtain ⟨hr0, hr1, hrm1, -, hX, hL⟩ := geo_curveR_spec hmem
  have hM0 : (γ t).1 ≠ 0 := hmem.2.1
  have hM1 : (γ t).1 ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hmem.2.2
  have hr1' : 1 - geoCurveR (γ t) ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
  have hrm1' : 1 + geoCurveR (γ t) ≠ 0 := fun h ↦ hrm1 (eq_neg_of_add_eq_zero_right h)
  have hrm1'' : -geoCurveR (γ t) ≠ 1 := fun h ↦ hrm1 (by rw [← h, neg_neg])
  have hMd : HasDerivAt (fun s ↦ (γ s).1) γ'.1 t :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t hγ
  have hLd : HasDerivAt (fun s ↦ (γ s).2) γ'.2 t :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t hγ
  have hM2 := hMd.pow 2
  obtain ⟨ρ', hρ⟩ : ∃ ρ', HasDerivAt (fun s ↦ geoCurveR (γ s)) ρ' t :=
    ⟨_, (hM2.add hLd).div (hM2.mul (hM2.sub_const 1)) (mul_ne_zero (pow_ne_zero 2 hM0) hM1)⟩
  have hU : HasDerivAt (fun s ↦ geoRegPrimitive (geoCurveR (γ s)))
      (geoBWDeriv (geoCurveR (γ t)) ρ' - geoBWDeriv (-geoCurveR (γ t)) (-ρ')) t :=
    (geo_hasDerivAt_blochWigner_comp hρ hr0 hr1).sub
      (geo_hasDerivAt_blochWigner_comp hρ.neg (neg_ne_zero.mpr hr0) hrm1'')
  have hXe : (fun s ↦ (γ s).1 ^ 2) =ᶠ[𝓝 t] fun s ↦ geoX (geoCurveR (γ s)) :=
    hE.mono fun s hs ↦ (geo_curveR_spec hs).2.2.2.2.1
  have hLe : (fun s ↦ (γ s).2) =ᶠ[𝓝 t] fun s ↦ geoL (geoCurveR (γ s)) :=
    hE.mono fun s hs ↦ (geo_curveR_spec hs).2.2.2.2.2
  have h1 := hM2.unique ((geo_hasDerivAt_geoX_comp hρ hr0 hr1').congr_of_eventuallyEq hXe)
  have h2 := hLd.unique ((geo_hasDerivAt_geoL_comp hρ hr1').congr_of_eventuallyEq hLe)
  convert hU using 1
  exact (geo_bwDeriv_sub_eq_eta hr0 hr1' hrm1' hX hL
    (geo_logDeriv_M hM0 hr0 hr1' hrm1' hX h1) (geo_logDeriv_L hr1' hrm1' hL h2)).symm

/-- Catalan's constant is positive: `G ≥ 1 - 1/9`, by the alternating series bound. -/
private theorem geo_catalanConstant_pos : 0 < catalanConstant := by
  have hsum : Summable fun n : ℕ ↦ (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2 := by
    refine Summable.of_norm_bounded (g := fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 2) ?_ fun n ↦ ?_
    · exact (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr one_lt_two) |>.congr fun n ↦ by push_cast; rfl
    · rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_pow, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      gcongr
      linarith [n.cast_nonneg (α := ℝ)]
  have hfl : Tendsto (fun n ↦ ∑ i ∈ Finset.range n,
      (-1 : ℝ) ^ i * (fun k : ℕ ↦ 1 / (2 * (k : ℝ) + 1) ^ 2) i) atTop (𝓝 catalanConstant) := by
    simp only [mul_one_div]
    exact hsum.hasSum.tendsto_sum_nat
  have hanti : Antitone fun k : ℕ ↦ 1 / (2 * (k : ℝ) + 1) ^ 2 := by
    intro a b hab
    have : (a : ℝ) ≤ b := Nat.cast_le.mpr hab
    simp only
    gcongr
  have h := hanti.alternating_series_le_tendsto hfl 1
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- G-REG, the primitive in the parameter: continuous, with limits `0` at `r = 0, 1, -1, ∞` and
values `U(±i) = ±2G`; the two branches over a node carry different values. -/
theorem geo_reg_primitive :
    Continuous geoRegPrimitive ∧ Tendsto geoRegPrimitive (cocompact ℂ) (𝓝 0) ∧
      geoRegPrimitive 0 = 0 ∧ geoRegPrimitive 1 = 0 ∧ geoRegPrimitive (-1) = 0 ∧
      geoRegPrimitive Complex.I = 2 * catalanConstant ∧
      geoRegPrimitive (-Complex.I) = -(2 * catalanConstant) ∧
      geoRegPrimitive Complex.I ≠ geoRegPrimitive (-Complex.I) := by
  obtain ⟨h0, h1, hm1, hI, hmI⟩ := geo_regPrimitive_values
  refine ⟨geo_continuous_regPrimitive, geo_tendsto_regPrimitive_cocompact, h0, h1, hm1, hI, hmI,
    ?_⟩
  rw [hI, hmI]
  have := geo_catalanConstant_pos
  intro h
  linarith

end AJConjecture
