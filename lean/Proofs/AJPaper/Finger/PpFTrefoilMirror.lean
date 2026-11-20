import Mathlib
import AJPaper.Sharp.PpSSymbolMirror
import AJPaper.Finger.PpFTrefoil
import AJPaper.Finger.PpFRecInv
import AJPaper.Finger.PpFAPolyInv

/-!
# The mirror trefoil test: `Δ ≐ E^∨` (Unit PpF, node `PpF_TrefoilMirror`)

Source: Section 9 of the paper: "reflection of a knot inverts `M` on both sides of the AJ
comparison. The involution `ρ` of `R` given by `ρ g = g(M⁻¹, L)` therefore gives
`Δ_{K^*} ≐ ρ(Δ_K)`"; proof of Corollary 9.2: "The mirror identity gives the positive-clasp
formula since `ρ(E) ≐ E^∨`."

The test knot for `W_+` is the mirror image `S^* = W_(+,0)(T(2, -3))` of `S = Z(T(2, 3))`:
`twFamilyKnot 2 3 h false false 0 = (twFamilyKnot 2 3 h true true 0).inv`
(`ppf_trefoilMirror_eq_inv`).

* `ppf_trefoilMirror_specialize`: every recurrence polynomial of `S^*` has
  `f ≐ ρ((L - 1)² E B_6)` (`ppf_recurrencePolynomial_bar` with
  `twm_laurentToField_coloredJones_mirror`, and `ppf_trefoil_specialize`).
* `ppf_trefoilMirror_aPolynomial`: every A-polynomial of `S^*` has `A ≐ ρ((L - 1) B_6)`:
  `ppf_aPolynomial_inv` gives the image of `(L - 1) B_6` under `L ↦ L⁻¹`
  (`ppf_trefoil_aPolynomial`), and this is `ρ((L - 1) B_6)` up to a unit because
  `B_6(M⁻¹, L⁻¹) ≐ B_6` (`pps_twistPoly_inv`) and `L⁻¹ - 1 = -L⁻¹ (L - 1)`.
* `ppf_isExtraSupportOf_trefoilMirror`: `E^∨` is an extra support of `S^*`: transport the model
  `ppf_isExtraSupport_trefoil_model` along `ρ = ppsMInv`
  (`isExtraSupport_map_of_involutive`, `ppsMInv_ppsMInv`) and use
  `pps_extraFactor_mInv_associated` (`ρ(E) ≐ E^∨`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The positive-clasp untwisted double of the left-handed trefoil is the mirror image (the
closure of the inverse braid) of the negative-clasp untwisted double of the right-handed
trefoil. -/
theorem ppf_trefoilMirror_eq_inv (h : IsTorusPair 2 3) :
    twFamilyKnot 2 3 h false false 0 = (twFamilyKnot 2 3 h true true 0).inv := by
  rw [twFamilyKnot_false, twFamilyKnot_true, neg_zero, Bool.not_false]

/-- The specialized recurrence polynomial of the mirror test knot. -/
theorem ppf_trefoilMirror_specialize (h : IsTorusPair 2 3) {α : RecOp}
    (hα : IsRecurrencePolynomial (coloredJones (twFamilyKnot 2 3 h false false 0)) α) :
    Associated (toComparison (specialize α))
      (ppsMInv (toComparison ((X - 1) ^ 2 * extraFactor * twistPoly 6))) := by
  have hbar : ∀ n : ℤ, laurentToField (coloredJones (twFamilyKnot 2 3 h false false 0) n) =
      twQBar (laurentToField (coloredJones (twFamilyKnot 2 3 h true true 0) n)) := fun n ↦ by
    have hm := twm_laurentToField_coloredJones_mirror h true true 0 n
    rwa [Bool.not_true, neg_zero] at hm
  obtain ⟨α₀, hα₀, hassoc⟩ := ppf_recurrencePolynomial_bar hbar hα
  exact hassoc.trans ((ppf_trefoil_specialize h hα₀).map ppsMInv)

/-- The image of `L - 1` in the comparison ring. -/
private theorem toComparison_X_sub_one_ppfTrefoilMirror :
    toComparison (X - 1 : ℤ[X][X]) = LaurentPolynomial.T 1 - 1 := by
  rw [map_sub, map_one, toComparison, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_X,
    Polynomial.toLaurent_X]

/-- The longitude inversion and the meridian inversion of `L - 1` are associated. -/
private theorem invert_X_sub_one_associated_ppfTrefoilMirror :
    Associated (LaurentPolynomial.invert (toComparison (X - 1 : ℤ[X][X])))
      (ppsMInv (toComparison (X - 1 : ℤ[X][X]))) := by
  have hu : IsUnit (-LaurentPolynomial.T (-1) : ComparisonRing) :=
    (LaurentPolynomial.isUnit_T (-1)).neg
  have he : LaurentPolynomial.invert (toComparison (X - 1 : ℤ[X][X])) =
      -LaurentPolynomial.T (-1) * ppsMInv (toComparison (X - 1 : ℤ[X][X])) := by
    have hT : (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1 : ComparisonRing) = 1 := by
      rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]
    rw [toComparison_X_sub_one_ppfTrefoilMirror, map_sub, map_one, map_sub, map_one,
      LaurentPolynomial.invert_T, ppsMInv_T]
    linear_combination hT
  rw [he, associated_isUnit_mul_left_iff hu]
  exact Associated.refl _

/-- The longitude inversion and the meridian inversion of `B_6` are associated. -/
private theorem invert_twistPoly_six_associated_ppfTrefoilMirror :
    Associated (LaurentPolynomial.invert (toComparison (twistPoly 6)))
      (ppsMInv (toComparison (twistPoly 6))) := by
  have h' := congrArg LaurentPolynomial.invert (pps_twistPoly_inv 6)
  rw [map_mul, map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
    LaurentPolynomial.involutive_invert (ppsMInv (toComparison (twistPoly 6)))] at h'
  have hu : IsUnit (LaurentPolynomial.C ((RatFunc.X : RatFunc ℚ) ^ (8 * 6)) *
      LaurentPolynomial.T (-((2 * 6 : ℕ) : ℤ)) : ComparisonRing) :=
    ((IsUnit.mk0 _ (pow_ne_zero _ RatFunc.X_ne_zero)).map LaurentPolynomial.C).mul
      (LaurentPolynomial.isUnit_T _)
  rw [h', associated_isUnit_mul_left_iff hu]
  exact Associated.refl _

/-- The A-polynomial of the mirror test knot. -/
theorem ppf_trefoilMirror_aPolynomial (h : IsTorusPair 2 3) {A : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet (twFamilyKnot 2 3 h false false 0)) A) :
    Associated (toComparison A) (ppsMInv (toComparison ((X - 1) * twistPoly 6))) := by
  rw [ppf_trefoilMirror_eq_inv] at hA
  obtain ⟨A₀, hA₀⟩ := (twFamilyClauses_negClasp h true 0).2.2.2.1
  refine (ppf_aPolynomial_inv hA₀ hA).trans
    (((ppf_trefoil_aPolynomial h hA₀).map LaurentPolynomial.invert).trans ?_)
  rw [map_mul, map_mul, map_mul]
  exact invert_X_sub_one_associated_ppfTrefoilMirror.mul_mul
    invert_twistPoly_six_associated_ppfTrefoilMirror

/-- **The mirror trefoil test**: `Δ ≐ E^∨` for the mirror image of `Z(T(2, 3))`. -/
theorem ppf_isExtraSupportOf_trefoilMirror (h : IsTorusPair 2 3) :
    IsExtraSupportOf (twFamilyKnot 2 3 h false false 0) (toComparison extraFactorMirror) := by
  have hc := twFamilyClauses_posClasp h false 0
  obtain ⟨α, hα⟩ := hc.2.1
  obtain ⟨A, hA⟩ := hc.2.2.2.1
  exact ⟨α, A, hα, hA, isExtraSupport_congr (ppf_trefoilMirror_specialize h hα).symm
    (ppf_trefoilMirror_aPolynomial h hA).symm pps_extraFactor_mInv_associated
    (isExtraSupport_map_of_involutive ppsMInv ppsMInv_ppsMInv ppf_isExtraSupport_trefoil_model)⟩

end AJConjecture
