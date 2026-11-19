import Mathlib
import AJHandoff.Geometry.GeoBlochWignerDeriv

/-!
# Two functional equations proved by differentiation

* `D(1 - z) = -D(z)` for all `z`;
* `U((1 - r)/(1 + r)) = -U(r)` for all `r ≠ -1`, where `U(r) = D(r) - D(-r)`. This is the identity
  behind `V_Wh(w) = 2U(w) = -2U(r)` for `w = (1 - r)/(1 + r)` (G-VOL), proved, as in the source,
  by differentiation and a real basepoint.

Route. `dU(z) = η(z, 1 - z) - η(-z, 1 + z) = η(z, φ(z))` with `φ(z) = (1 - z)/(1 + z)`, using
bilinearity and `η(-1, ·) = 0`. Since `φ` is an involution, `dU(φ(r)) = η(φ(r), r) = -η(r, φ(r))`,
so `r ↦ U(φ(r)) + U(r)` has zero real differential on `ℂ ∖ {0, ±1}`. That set is connected
(complement of a countable set in `ℂ`, `Set.Countable.isConnected_compl_of_one_lt_rank`), so the
function is constant there (`IsOpen.is_const_of_fderiv_eq_zero` style); it vanishes at `r = 1/2`
(`D` is zero on `ℝ`) and extends by continuity to `r ∈ {0, 1}`. The same argument with
`d[D(z) + D(1 - z)] = η(z, 1 - z) + η(1 - z, z) = 0` gives the first identity on `ℂ ∖ {0, 1}`, and
`D(0) = D(1) = 0` covers the rest.
-/

open Filter Topology

noncomputable section

namespace AJConjecture

/-- A function with zero real differential off a finite subset of `ℂ` takes equal values at any
two points outside it (the complement is open and connected). -/
private theorem eq_of_hasFDerivAt_zero_off_finite {f : ℂ → ℝ} {S : Set ℂ} (hS : S.Finite)
    (hf : ∀ z ∉ S, HasFDerivAt f (0 : ℂ →L[ℝ] ℝ) z) {a b : ℂ} (ha : a ∉ S) (hb : b ∉ S) :
    f a = f b := by
  have hconn : IsConnected Sᶜ := hS.countable.isConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)
  exact hS.isClosed.isOpen_compl.is_const_of_fderiv_eq_zero hconn.isPreconnected
    (fun z hz ↦ (hf z hz).differentiableAt.differentiableWithinAt)
    (fun z hz ↦ (hf z hz).fderiv) ha hb

/-- `η(z, 1 - z) + η(1 - z, z) = 0`: the differential of `D(z) + D(1 - z)` vanishes. -/
private theorem geoBWDeriv_add_one_sub (w h : ℂ) :
    geoBWDeriv w h + geoBWDeriv (1 - w) (-h) = 0 := by
  rw [geoBWDeriv_apply, geoBWDeriv_apply, sub_sub_cancel, neg_neg]
  ring

/-- `D(1 - z) = -D(z)`. -/
theorem geo_blochWigner_one_sub (z : ℂ) : blochWigner (1 - z) = -blochWigner z := by
  have hfin : ({0, 1} : Set ℂ).Finite := Set.toFinite _
  have hhalf : (1 / 2 : ℂ) ∉ ({0, 1} : Set ℂ) := by norm_num
  have hderiv : ∀ w ∉ ({0, 1} : Set ℂ),
      HasFDerivAt (fun w ↦ blochWigner w + blochWigner (1 - w)) (0 : ℂ →L[ℝ] ℝ) w := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hw
    have h1 := geo_hasFDerivAt_blochWigner hw.1 hw.2
    have h2 := (geo_hasFDerivAt_blochWigner (sub_ne_zero.2 (Ne.symm hw.2))
      (by rw [Ne, sub_eq_self]; exact hw.1)).comp w ((hasFDerivAt_id w).const_sub 1)
    refine (h1.add h2).congr_fderiv (ContinuousLinearMap.ext fun h ↦ ?_)
    rw [add_apply, ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply,
      zero_apply]
    exact geoBWDeriv_add_one_sub w h
  by_cases hz : z ∈ ({0, 1} : Set ℂ)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [sub_zero, geo_blochWigner_zero, geo_blochWigner_one, neg_zero]
    · rw [sub_self, geo_blochWigner_zero, geo_blochWigner_one, neg_zero]
  · have h := eq_of_hasFDerivAt_zero_off_finite hfin hderiv hz hhalf
    have hr : blochWigner (1 / 2 : ℂ) = 0 := by
      have := geo_blochWigner_ofReal (1 / 2)
      push_cast at this
      exact this
    rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, hr, add_zero] at h
    linarith

/-- `U` vanishes on the real line. -/
private theorem geoRegPrimitive_ofReal (x : ℝ) : geoRegPrimitive x = 0 := by
  rw [geoRegPrimitive, ← Complex.ofReal_neg, geo_blochWigner_ofReal, geo_blochWigner_ofReal,
    sub_zero]

/-- The differential of `U` at `z ≠ 0, ±1`: `dU(z)(h) = η(z, 1 - z)(h) - η(-z, 1 + z)(-h)`. -/
private theorem hasFDerivAt_geoRegPrimitive {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) (hm1 : z ≠ -1) :
    HasFDerivAt geoRegPrimitive
      (geoBWDeriv z - (geoBWDeriv (-z)).comp (-ContinuousLinearMap.id ℝ ℂ)) z := by
  have hn1 : -z ≠ 1 := fun e ↦ hm1 (by rw [← e, neg_neg])
  exact (geo_hasFDerivAt_blochWigner h0 h1).sub
    ((geo_hasFDerivAt_blochWigner (neg_ne_zero.2 h0) hn1).comp z (hasFDerivAt_id z).neg)

/-- The algebraic identity behind the Cayley symmetry: with `φ(r) = (1 - r)/(1 + r)` and
`φ'(r) = -2/(1 + r)²`, `dU(φ(r))(φ'(r) h) + dU(r)(h) = 0`. -/
private theorem cayley_deriv_identity {r : ℂ} (h0 : r ≠ 0) (h1 : r ≠ 1) (hm1 : r ≠ -1) (h : ℂ) :
    geoBWDeriv ((1 - r) / (1 + r)) (h * (-2 / (1 + r) ^ 2)) -
        geoBWDeriv (-((1 - r) / (1 + r))) (-(h * (-2 / (1 + r) ^ 2))) +
      (geoBWDeriv r h - geoBWDeriv (-r) (-h)) = 0 := by
  have hp : 1 + r ≠ 0 := fun e ↦ hm1 (by linear_combination e)
  have hm : 1 - r ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have hpn : ‖1 + r‖ ≠ 0 := norm_ne_zero_iff.2 hp
  have hmn : ‖1 - r‖ ≠ 0 := norm_ne_zero_iff.2 hm
  have h0n : ‖r‖ ≠ 0 := norm_ne_zero_iff.2 h0
  have l1 : Real.log ‖(1 - r) / (1 + r)‖ = Real.log ‖1 - r‖ - Real.log ‖1 + r‖ := by
    rw [norm_div, Real.log_div hmn hpn]
  have l2 : Real.log ‖-((1 - r) / (1 + r))‖ = Real.log ‖1 - r‖ - Real.log ‖1 + r‖ := by
    rw [norm_neg, l1]
  have l3 : Real.log ‖1 - (1 - r) / (1 + r)‖ =
      Real.log 2 + Real.log ‖r‖ - Real.log ‖1 + r‖ := by
    rw [show 1 - (1 - r) / (1 + r) = 2 * r / (1 + r) by field_simp; ring, norm_div, norm_mul,
      Complex.norm_two, Real.log_div (mul_ne_zero two_ne_zero h0n) hpn,
      Real.log_mul two_ne_zero h0n]
  have l4 : Real.log ‖1 - -((1 - r) / (1 + r))‖ = Real.log 2 - Real.log ‖1 + r‖ := by
    rw [show 1 - -((1 - r) / (1 + r)) = 2 / (1 + r) by field_simp; ring, norm_div,
      Complex.norm_two, Real.log_div two_ne_zero hpn]
  have l5 : Real.log ‖-r‖ = Real.log ‖r‖ := by rw [norm_neg]
  have l6 : Real.log ‖1 - -r‖ = Real.log ‖1 + r‖ := by rw [sub_neg_eq_add]
  rw [geoBWDeriv_apply, geoBWDeriv_apply, geoBWDeriv_apply, geoBWDeriv_apply, l1, l2, l3, l4,
    l5, l6]
  have c1 : -(h * (-2 / (1 + r) ^ 2)) / (1 - (1 - r) / (1 + r)) = h / r - h / (1 + r) := by
    rw [show 1 - (1 - r) / (1 + r) = 2 * r / (1 + r) by field_simp; ring]
    field_simp
    ring
  have c2 : h * (-2 / (1 + r) ^ 2) / ((1 - r) / (1 + r)) = -(h / (1 - r)) - h / (1 + r) := by
    field_simp
    ring
  have c3 : -(-(h * (-2 / (1 + r) ^ 2))) / (1 - -((1 - r) / (1 + r))) = -(h / (1 + r)) := by
    field_simp
    ring
  have c4 : -(h * (-2 / (1 + r) ^ 2)) / -((1 - r) / (1 + r)) =
      -(h / (1 - r)) - h / (1 + r) := by
    field_simp
    ring
  have c5 : -h / (1 - r) = -(h / (1 - r)) := by ring
  have c6 : -(-h) / (1 - -r) = h / (1 + r) := by ring
  have c7 : -h / -r = h / r := by ring
  rw [c1, c2, c3, c4, c5, c6, c7]
  simp only [Complex.sub_im, Complex.neg_im]
  ring

/-- `U((1 - r)/(1 + r)) = -U(r)` for `r ≠ -1`. -/
theorem geo_regPrimitive_cayley {r : ℂ} (hr : r ≠ -1) :
    geoRegPrimitive ((1 - r) / (1 + r)) = -geoRegPrimitive r := by
  have hfin : ({0, 1, -1} : Set ℂ).Finite := Set.toFinite _
  have hderiv : ∀ w ∉ ({0, 1, -1} : Set ℂ), HasFDerivAt
      (fun w ↦ geoRegPrimitive ((1 - w) / (1 + w)) + geoRegPrimitive w) (0 : ℂ →L[ℝ] ℝ) w := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hw
    obtain ⟨h0, h1, hm1⟩ := hw
    have hp : 1 + w ≠ 0 := fun e ↦ hm1 (by linear_combination e)
    have hφ0 : (1 - w) / (1 + w) ≠ 0 := div_ne_zero (sub_ne_zero.2 (Ne.symm h1)) hp
    have hφ1 : (1 - w) / (1 + w) ≠ 1 := by
      rw [Ne, div_eq_one_iff_eq hp]
      intro e
      exact h0 (by linear_combination -e / 2)
    have hφm1 : (1 - w) / (1 + w) ≠ -1 := by
      rw [Ne, div_eq_iff hp]
      intro e
      have : (2 : ℂ) = 0 := by linear_combination e
      exact two_ne_zero this
    have hφ : HasDerivAt (fun w : ℂ ↦ (1 - w) / (1 + w)) (-2 / (1 + w) ^ 2) w := by
      have := ((hasDerivAt_id w).const_sub 1).div ((hasDerivAt_id w).const_add 1) hp
      refine this.congr_deriv ?_
      simp only [id]
      field_simp
      ring
    have hc := (hasFDerivAt_geoRegPrimitive hφ0 hφ1 hφm1).comp w
      (hφ.hasFDerivAt.restrictScalars ℝ)
    refine (hc.add (hasFDerivAt_geoRegPrimitive h0 h1 hm1)).congr_fderiv
      (ContinuousLinearMap.ext fun h ↦ ?_)
    simp only [add_apply, sub_apply, neg_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.id_apply,
      zero_apply]
    exact cayley_deriv_identity h0 h1 hm1 h
  have hU := geo_regPrimitive_values
  by_cases hz : r ∈ ({0, 1, -1} : Set ℂ)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · rw [sub_zero, add_zero, div_one, hU.1, hU.2.1, neg_zero]
    · rw [sub_self, zero_div, hU.1, hU.2.1, neg_zero]
    · exact absurd rfl hr
  · have hhalf : ((1 / 2 : ℝ) : ℂ) ∉ ({0, 1, -1} : Set ℂ) := by norm_num
    have h := eq_of_hasFDerivAt_zero_off_finite hfin hderiv hz hhalf
    have e : (1 - ((1 / 2 : ℝ) : ℂ)) / (1 + ((1 / 2 : ℝ) : ℂ)) =
        (((1 - 1 / 2) / (1 + 1 / 2) : ℝ) : ℂ) := by push_cast; ring
    rw [e, geoRegPrimitive_ofReal, geoRegPrimitive_ofReal, add_zero] at h
    linarith

end AJConjecture
