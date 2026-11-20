import Mathlib
import AJTwist.Main.TwMMirrorSurvival
import AJPaper.Sharp.PpSMInv

/-!
# The recurrence polynomial of the mirror image (Unit PpF, node `PpF_RecInv`)

Source: Section 8.2 of the paper (`conclusion.tex`): the Ore map `Θ(t, M, L) = (t⁻¹, M⁻¹, L)`
"identifies the saturated annihilator ideals. Under `t⁻¹ + 1 = (t + 1)/t` the primitive
parameter order is preserved. Thus `f_{S^*}(M, L) ≐ f_S(M⁻¹, L)`."

`ppf_recurrencePolynomial_bar`: let `J'(n) = \overline{J(n)}`. For every recurrence polynomial
`α'` of `J'` there is a recurrence polynomial `α` of `J` with
`f_{α'} ≐ f_α(M⁻¹, L)` in `R = ℚ(M)[L, L⁻¹]`.

Route: `α = (Θ(α')).primPart` with `Θ = twmBarOp`. `Θ(α')` is nonzero (`twmBarOp_ne_zero`), has
the order of `α'` (`natDegree_twmBarOp`) and lies in the localized annihilator of `J`
(`twm_inLocalizedAnnihilator_barOp`); so does its primitive part (as in `pps_mirror_dvd`).
Minimality: for `Q ≠ 0` in the localized annihilator of `J`, `Θ(Q)` is a nonzero element of the
localized annihilator of `J'` of the same order (the bar is an involution, `twQBar_twQBar`), so
`ord α' ≤ ord Q`. Finally `Θ(α') = content · α` gives, with `specialize_twmBarOp` and
`toComparison_twmMReflect`, `± M^B f_{α'}(M⁻¹, L) = c(M) f_α` with `c(M) ≠ 0` because
`f_{α'} ≠ 0` (`specialize_ne_zero_of_isPrimitive`); apply the involution `ppsMInv`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `toComparison` is injective. -/
private theorem toComparison_injective_ppfRecInv : Function.Injective toComparison :=
  Polynomial.toLaurent_injective.comp
    (Polynomial.map_injective _ ((RatFunc.algebraMap_injective ℚ).comp
      (Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)))

/-- The primitive part of a nonzero element of the localized annihilator lies in it. -/
private theorem inLocalizedAnnihilator_primPart_ppfRecInv {J : ℤ → LaurentPolynomial ℤ}
    {Q : RecOp} (h0 : Q ≠ 0) (hQ : InLocalizedAnnihilator J Q) :
    InLocalizedAnnihilator J Q.primPart := by
  obtain ⟨c, hc, hann⟩ := hQ
  refine ⟨c * Q.content, mul_ne_zero hc (mt Polynomial.content_eq_zero_iff.mp h0), ?_⟩
  rwa [Polynomial.C_mul, mul_assoc, ← Polynomial.eq_C_content_mul_primPart]

/-- The image in the comparison ring of the specialization of a constant operator whose
specialization is not zero is a unit. -/
private theorem isUnit_toComparison_specialize_C_ppfRecInv {c : Coeff}
    (hc : specialize (Polynomial.C c) ≠ 0) :
    IsUnit (toComparison (specialize (Polynomial.C c))) := by
  have h1 : specialize (Polynomial.C c) =
      Polynomial.C (c.map (Polynomial.evalRingHom (-1 : ℤ))) := by
    rw [specialize, coe_mapRingHom, Polynomial.map_C, coe_mapRingHom]
  rw [h1] at hc ⊢
  have h2 : toComparison (Polynomial.C (c.map (Polynomial.evalRingHom (-1 : ℤ)))) =
      LaurentPolynomial.C (((algebraMap ℚ[X] (RatFunc ℚ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℚ)))
          (c.map (Polynomial.evalRingHom (-1 : ℤ)))) := by
    rw [toComparison, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_C,
      Polynomial.toLaurent_C]
  have h3 : toComparison (Polynomial.C (c.map (Polynomial.evalRingHom (-1 : ℤ)))) ≠ 0 :=
    fun h ↦ hc (toComparison_injective_ppfRecInv (h.trans (map_zero toComparison).symm))
  rw [h2] at h3 ⊢
  exact (IsUnit.mk0 _ fun h ↦ h3 (by rw [h, map_zero])).map LaurentPolynomial.C

/-- **The recurrence polynomial under the bar involution**: if `J'` is the bar of `J`, every
recurrence polynomial `α'` of `J'` has specialization associated, in `ℚ(M)[L, L⁻¹]`, to the
meridian inversion of the specialization of a recurrence polynomial `α` of `J`. -/
theorem ppf_recurrencePolynomial_bar {J J' : ℤ → LaurentPolynomial ℤ}
    (hbar : ∀ n : ℤ, laurentToField (J' n) = twQBar (laurentToField (J n))) {α' : RecOp}
    (hα' : IsRecurrencePolynomial J' α') :
    ∃ α : RecOp, IsRecurrencePolynomial J α ∧
      Associated (toComparison (specialize α')) (ppsMInv (toComparison (specialize α))) := by
  obtain ⟨hα0, hαin, hαmin, hαprim⟩ := hα'
  have hbar' : ∀ n : ℤ, laurentToField (J n) = twQBar (laurentToField (J' n)) := fun n ↦ by
    rw [hbar, twQBar_twQBar]
  have hΘ0 : twmBarOp α' ≠ 0 := twmBarOp_ne_zero hα0
  refine ⟨(twmBarOp α').primPart, ⟨(twmBarOp α').primPart_ne_zero,
    inLocalizedAnnihilator_primPart_ppfRecInv hΘ0 (twm_inLocalizedAnnihilator_barOp hbar hαin),
    fun Q hQ0 hQ ↦ ?_, (twmBarOp α').isPrimitive_primPart⟩, ?_⟩
  · rw [Polynomial.natDegree_primPart, natDegree_twmBarOp, ← natDegree_twmBarOp Q]
    exact hαmin _ (twmBarOp_ne_zero hQ0) (twm_inLocalizedAnnihilator_barOp hbar' hQ)
  · have hf0 : toComparison (specialize α') ≠ 0 := fun h ↦
      specialize_ne_zero_of_isPrimitive hαprim
        (toComparison_injective_ppfRecInv (h.trans (map_zero toComparison).symm))
    have hu : IsUnit (toComparison (Polynomial.C (Polynomial.C ((-1 : ℤ) ^ twmTDeg α')))) :=
      (((isUnit_neg_one (α := ℤ)).pow _).map Polynomial.C |>.map Polynomial.C).map toComparison
    have hX : IsUnit (LaurentPolynomial.C ((RatFunc.X : RatFunc ℚ) ^ twmMDeg α')) :=
      (IsUnit.mk0 _ (pow_ne_zero _ RatFunc.X_ne_zero)).map LaurentPolynomial.C
    have hM0 : ppsMInv (toComparison (specialize α')) ≠ 0 := fun h ↦ hf0 <| by
      rw [← ppsMInv_ppsMInv (toComparison (specialize α')), h, map_zero]
    have key : toComparison (Polynomial.C (Polynomial.C ((-1 : ℤ) ^ twmTDeg α'))) *
        (LaurentPolynomial.C ((RatFunc.X : RatFunc ℚ) ^ twmMDeg α') *
          ppsMInv (toComparison (specialize α'))) =
        toComparison (specialize (Polynomial.C (twmBarOp α').content)) *
          toComparison (specialize (twmBarOp α').primPart) := by
      rw [← toComparison_twmMReflect _ _ (natDegree_coeff_specialize_le_twmMDeg α'), ← map_mul,
        ← specialize_twmBarOp, ← map_mul, ← map_mul, ← Polynomial.eq_C_content_mul_primPart]
    have hc0 : specialize (Polynomial.C (twmBarOp α').content) ≠ 0 := fun h ↦ by
      rw [h, map_zero, zero_mul] at key
      exact mul_ne_zero hu.ne_zero (mul_ne_zero hX.ne_zero hM0) key
    have hc := isUnit_toComparison_specialize_C_ppfRecInv hc0
    have h1 := (associated_isUnit_mul_left_iff hu).mpr
      ((associated_isUnit_mul_left_iff hX).mpr
        (Associated.refl (ppsMInv (toComparison (specialize α')))))
    have h2 := (associated_isUnit_mul_left_iff hc).mpr
      (Associated.refl (toComparison (specialize (twmBarOp α').primPart)))
    have h4 := ((h1.symm.trans (Associated.of_eq key)).trans h2).map
      (ppsMInv : ComparisonRing →* ComparisonRing)
    rwa [MonoidHom.coe_ofClass, ppsMInv_ppsMInv] at h4

end AJConjecture
