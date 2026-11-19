import Mathlib
import AJConjecture.QAlgSpecializeNeZero
import AJTwist.Main.TwMBarAction
import AJTwist.Main.TwMBarSpecialize
import AJTwist.Main.TwMReflectComparison

/-!
# Mirror transport of the survival of the factor (Unit M2, conclusion)

Source: revision 5, Section 8.2 (`conclusion.tex`, "Transport under the satellite mirror"):
the Ore map `Θ(t, M, L) = (t⁻¹, M⁻¹, L)` identifies the saturated annihilator ideals of a
sequence and of its bar, `f_{S^*}(M, L) ≐ f_S(M⁻¹, L)`, and the obstruction polynomial becomes
`E^∨ = M⁴ E(M⁻¹, L)`.

`twm_mirror_exists`: if `J'(n) = \overline{J(n)}` and the localized annihilator of `J` is
nonzero, so is that of `J'`.

`twm_mirror_survival`: let `J`, `J' : ℤ → ℤ[t, t⁻¹]` with `J'(n) = \overline{J(n)}`
(`t ↦ t⁻¹`). If every nonzero primitive element of the localized annihilator of `J` has nonzero
specialization divisible by `E` in `ℚ(M)[L, L⁻¹]`, then every nonzero primitive element of the
localized annihilator of `J'` has nonzero specialization divisible by `E^∨`
(`extraFactorMirror`).

Proof. For `Q` primitive in the localized annihilator of `J'`, the mirror operator
`Θ(Q) = twmBarOp Q` lies in the localized annihilator of `J`
(`twm_inLocalizedAnnihilator_barOp`). It need not be primitive in `ℤ[t][M][L]`, and this is not
needed: `Θ(Q) = content · primPart`, the primitive part lies in the localized annihilator of `J`
(the content is a nonzero coefficient), so `E` divides its specialization and hence that of
`Θ(Q)`, which is `± M^B f_Q(M⁻¹, L)` (`specialize_twmBarOp`). The meridian inversion turns this
into `E^∨ ∣ f_Q` (`twm_extraFactorMirror_dvd_of_dvd_mReflect`). The specialization of a
primitive operator is nonzero by `specialize_ne_zero_of_isPrimitive`.

The paper argues through "`Θ` preserves the primitive parameter order" (primitivity over
`ℤ[t^{±1}, M^{±1}]`); the statement here quantifies over all primitive elements, so neither the
primitivity nor the minimality of `Θ(Q)` is used. (`Θ` with the exact degrees `A`, `B` does
preserve primitivity in `ℤ[t][M][L]`, and with larger bounds it does not: design notes of the
package, `SCR/M/DESIGN.md`, Section 3.4.)

This file has no `sorry` of its own.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- **Mirror transport of the existence clause**: if `J'` is the bar of `J` and the localized
annihilator of `J` contains a nonzero operator `Q`, then the localized annihilator of `J'`
contains the nonzero operator `Θ(Q)`. -/
theorem twm_mirror_exists {J J' : ℤ → ℤ[T;T⁻¹]}
    (hbar : ∀ n : ℤ, laurentToField (J' n) = twQBar (laurentToField (J n)))
    (h : ∃ Q : RecOp, Q ≠ 0 ∧ InLocalizedAnnihilator J Q) :
    ∃ Q : RecOp, Q ≠ 0 ∧ InLocalizedAnnihilator J' Q := by
  obtain ⟨Q, hQ0, hQ⟩ := h
  have hbar' : ∀ n : ℤ, laurentToField (J n) = twQBar (laurentToField (J' n)) := fun n ↦ by
    rw [hbar, twQBar_twQBar]
  exact ⟨twmBarOp Q, twmBarOp_ne_zero hQ0, twm_inLocalizedAnnihilator_barOp hbar' hQ⟩

/-- **Mirror transport of the survival clause** (Section 8.2): if `J'` is the bar of `J` and `E`
divides the nonzero specialization of every nonzero primitive element of the localized
annihilator of `J`, then `E^∨ = M⁴ E(M⁻¹, L)` divides the nonzero specialization of every
nonzero primitive element of the localized annihilator of `J'`, in `ℚ(M)[L, L⁻¹]`. -/
theorem twm_mirror_survival {J J' : ℤ → ℤ[T;T⁻¹]}
    (hbar : ∀ n : ℤ, laurentToField (J' n) = twQBar (laurentToField (J n)))
    (hJ : ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator J Q →
      specialize Q ≠ 0 ∧ toComparison extraFactor ∣ toComparison (specialize Q)) :
    ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator J' Q →
      specialize Q ≠ 0 ∧ toComparison extraFactorMirror ∣ toComparison (specialize Q) := by
  intro Q _ hprim hQ
  refine ⟨specialize_ne_zero_of_isPrimitive hprim, ?_⟩
  have hΘ : InLocalizedAnnihilator J (twmBarOp Q) := twm_inLocalizedAnnihilator_barOp hbar hQ
  have hE : toComparison extraFactor ∣ toComparison (specialize (twmBarOp Q)) := by
    by_cases h0 : twmBarOp Q = 0
    · rw [h0, map_zero, map_zero]
      exact dvd_zero _
    · obtain ⟨c, hc, hann⟩ := hΘ
      have hpp : InLocalizedAnnihilator J (twmBarOp Q).primPart := by
        refine ⟨c * (twmBarOp Q).content,
          mul_ne_zero hc (mt Polynomial.content_eq_zero_iff.mp h0), ?_⟩
        rwa [Polynomial.C_mul, mul_assoc, ← Polynomial.eq_C_content_mul_primPart]
      have h1 := (hJ _ (twmBarOp Q).primPart_ne_zero (twmBarOp Q).isPrimitive_primPart hpp).2
      have h2 : specialize (twmBarOp Q).primPart ∣ specialize (twmBarOp Q) := by
        conv_rhs => rw [(twmBarOp Q).eq_C_content_mul_primPart, map_mul]
        exact dvd_mul_left _ _
      exact h1.trans (map_dvd toComparison h2)
  rw [specialize_twmBarOp, map_mul] at hE
  have hu : IsUnit (toComparison (Polynomial.C (Polynomial.C ((-1 : ℤ) ^ twmTDeg Q)))) :=
    (((isUnit_neg_one (α := ℤ)).pow _).map Polynomial.C |>.map Polynomial.C).map toComparison
  exact twm_extraFactorMirror_dvd_of_dvd_mReflect (natDegree_coeff_specialize_le_twmMDeg Q)
    (hu.dvd_mul_left.mp hE)

end AJConjecture
