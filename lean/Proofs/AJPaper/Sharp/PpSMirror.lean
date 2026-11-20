import Mathlib
import AJTwist.Main.TwMMirrorSurvival
import AJPaper.Sharp.PpSMInv

/-!
# Mirror transport of a divisibility by an arbitrary factor (Unit PpS, node `PpS_Mirror`)

Source: Section 8.2 of the paper (`conclusion.tex`): the Ore map `Θ(t, M, L) = (t⁻¹, M⁻¹, L)`
identifies the saturated annihilator ideals of a sequence and of its bar, and
`f_{S^*}(M, L) ≐ f_S(M⁻¹, L)`: "this transports both divisibility and coprimality".

The library's `twm_mirror_survival` (`AJTwist.Main.TwMMirrorSurvival`) does this for the factor
`E` only. `pps_mirror_dvd` is the same argument for an arbitrary element `F` of
`R = ℚ(M)[L, L⁻¹]`: if `J'(n) = \overline{J(n)}` and `F` divides the specialization of every
nonzero primitive element of the localized annihilator of `J`, then the meridian inversion
`F(M⁻¹, L) = ppsMInv F` divides the specialization of every nonzero primitive element of the
localized annihilator of `J'`.

Proof: for `Q` primitive in the localized annihilator of `J'`, `Θ(Q) = twmBarOp Q` lies in the
localized annihilator of `J`; `F` divides the specialization of its primitive part, hence of
`Θ(Q)`, which is `± M^B f_Q(M⁻¹, L)` (`specialize_twmBarOp`, `toComparison_twmMReflect`); apply
the involution `ppsMInv`.

This file has no `sorry`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- **Mirror transport of a divisibility** (Section 8.2): if `J'` is the bar of `J` and `F`
divides the specialization of every nonzero primitive element of the localized annihilator of
`J`, then `F(M⁻¹, L)` divides the specialization of every nonzero primitive element of the
localized annihilator of `J'`, in `ℚ(M)[L, L⁻¹]`. -/
theorem pps_mirror_dvd {J J' : ℤ → LaurentPolynomial ℤ}
    (hbar : ∀ n : ℤ, laurentToField (J' n) = twQBar (laurentToField (J n)))
    {F : ComparisonRing}
    (hJ : ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator J Q →
      F ∣ toComparison (specialize Q)) :
    ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator J' Q →
      ppsMInv F ∣ toComparison (specialize Q) := by
  intro Q _ _ hQ
  have hΘ : InLocalizedAnnihilator J (twmBarOp Q) := twm_inLocalizedAnnihilator_barOp hbar hQ
  have hE : F ∣ toComparison (specialize (twmBarOp Q)) := by
    by_cases h0 : twmBarOp Q = 0
    · rw [h0, map_zero, map_zero]
      exact dvd_zero _
    · obtain ⟨c, hc, hann⟩ := hΘ
      have hpp : InLocalizedAnnihilator J (twmBarOp Q).primPart := by
        refine ⟨c * (twmBarOp Q).content,
          mul_ne_zero hc (mt Polynomial.content_eq_zero_iff.mp h0), ?_⟩
        rwa [Polynomial.C_mul, mul_assoc, ← Polynomial.eq_C_content_mul_primPart]
      have h1 := hJ _ (twmBarOp Q).primPart_ne_zero (twmBarOp Q).isPrimitive_primPart hpp
      have h2 : specialize (twmBarOp Q).primPart ∣ specialize (twmBarOp Q) := by
        conv_rhs => rw [(twmBarOp Q).eq_C_content_mul_primPart, map_mul]
        exact dvd_mul_left _ _
      exact h1.trans (map_dvd toComparison h2)
  rw [specialize_twmBarOp, map_mul,
    toComparison_twmMReflect _ _ (natDegree_coeff_specialize_le_twmMDeg Q)] at hE
  have hu : IsUnit (toComparison (Polynomial.C (Polynomial.C ((-1 : ℤ) ^ twmTDeg Q)))) :=
    (((isUnit_neg_one (α := ℤ)).pow _).map Polynomial.C |>.map Polynomial.C).map toComparison
  have hX : IsUnit (LaurentPolynomial.C ((RatFunc.X : RatFunc ℚ) ^ twmMDeg Q)) :=
    (IsUnit.mk0 _ (pow_ne_zero _ RatFunc.X_ne_zero)).map LaurentPolynomial.C
  have h3 : F ∣ ppsMInv (toComparison (specialize Q)) :=
    hX.dvd_mul_left.mp (hu.dvd_mul_left.mp hE)
  have h4 := map_dvd ppsMInv h3
  rwa [ppsMInv_ppsMInv] at h4

end AJConjecture
