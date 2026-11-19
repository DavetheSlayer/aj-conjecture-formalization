import Mathlib
import AJTwist.Main.TwMTheorem

/-!
# Every integral annihilator, primitive or not (Unit PpI, node `PpI_Integer`)

Source: Section 8.5 of the paper (`conclusion.tex`): "For each nonzero rational row, clear
numerical denominators and divide by its Laurent-polynomial content. The resulting primitive row
lies in the rational saturation … Sections 8.1 and its mirror give a nonzero specialization
divisible by `G` … Multiplying the content back … A content factor may itself specialize to
zero."

* `extraFactorMirror_dvd_of_toComparison_dvd`: divisibility by `E^∨` in `ℚ(M)[L, L⁻¹]` descends
  to `ℤ[M][L]` (the companion of the library's `extraFactor_dvd_of_toComparison_dvd`; route:
  `E^∨ = E.reverse`, `toComparison_reverse`, `Polynomial.reverse_mul_of_domain`, and
  `A = L^k · A.reverse.reverse`).
* `ppi_dvd_specialize_of_primitive`: if `G` divides the specialization of every nonzero
  primitive element of the localized annihilator of a sequence, it divides the specialization
  of every element (`Q = content · primPart`, and the primitive part stays in the localized
  annihilator).
* `ppi_factor_dvd_specialize`: for the four families, the obstruction factor `G` (`E` or `E^∨`)
  divides `Q(-1, M, L)` in `ℤ[M][L]` for every `Q` in the localized annihilator; in particular
  (`ppi_factor_dvd_specialize_of_annihilates`) for every operator with coefficients in
  `ℤ[t][M]` annihilating the coloured Jones function at all integers, primitive or not.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Divisibility by `E^∨` in the comparison ring descends to `ℤ[M][L]`. -/
theorem extraFactorMirror_dvd_of_toComparison_dvd {A : ℤ[X][X]}
    (h : toComparison extraFactorMirror ∣ toComparison A) : extraFactorMirror ∣ A := by
  have hmir : extraFactor.mirror = extraFactorMirror := by
    have h0 : extraFactor.natTrailingDegree = 0 := by
      refine natTrailingDegree_eq_zero.mpr (Or.inr ?_)
      rw [extraFactor_coeff_zero]
      exact pow_ne_zero 4 X_ne_zero
    rw [mirror, h0, pow_zero, mul_one, extraFactor_reverse]
  have hA : toComparison A.mirror = LaurentPolynomial.invert (toComparison A) *
      LaurentPolynomial.T ((A.natDegree : ℤ) + (A.natTrailingDegree : ℤ)) := by
    rw [mirror, map_mul, toComparison_reverse, LaurentPolynomial.T_add, mul_assoc]
    congr 2
    simp only [toComparison, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_X, map_pow,
      toLaurent_X, LaurentPolynomial.T_pow, mul_one]
  have hE : toComparison extraFactor ∣ toComparison A.mirror := by
    rw [hA]
    have h1 := map_dvd LaurentPolynomial.invert h
    rw [toComparison_extraFactorMirror, map_mul, LaurentPolynomial.invert_T,
      LaurentPolynomial.involutive_invert] at h1
    exact (dvd_of_mul_left_dvd h1).mul_right _
  obtain ⟨B, hB⟩ := extraFactor_dvd_of_toComparison_dvd hE
  have hmm := congrArg mirror hB
  rw [mirror_mirror, mirror_mul_of_domain, hmir] at hmm
  exact ⟨_, hmm⟩

/-- From the primitive elements of a localized annihilator to all its elements. -/
theorem ppi_dvd_specialize_of_primitive {f : ℤ → LaurentPolynomial ℤ} {G : ℤ[X][X]}
    (hG : ∀ Q : RecOp, Q ≠ 0 → Q.IsPrimitive → InLocalizedAnnihilator f Q → G ∣ specialize Q) :
    ∀ Q : RecOp, InLocalizedAnnihilator f Q → G ∣ specialize Q := by
  intro Q hQ
  by_cases h0 : Q = 0
  · rw [h0, map_zero]
    exact dvd_zero _
  · obtain ⟨c, hc, hann⟩ := hQ
    have hpp : InLocalizedAnnihilator f Q.primPart := by
      refine ⟨c * Q.content, mul_ne_zero hc (mt Polynomial.content_eq_zero_iff.mp h0), ?_⟩
      rwa [Polynomial.C_mul, mul_assoc, ← Polynomial.eq_C_content_mul_primPart]
    have h1 := hG _ Q.primPart_ne_zero Q.isPrimitive_primPart hpp
    have h2 : specialize Q.primPart ∣ specialize Q := by
      conv_rhs => rw [Q.eq_C_content_mul_primPart, map_mul]
      exact dvd_mul_left _ _
    exact h1.trans h2

/-- **Every element of the localized annihilator** of the coloured Jones function of
`W_(ε,ℓ)(T_η)`, primitive or not, has specialization divisible by the obstruction factor
(`E` for the negative clasp, `E^∨` for the positive clasp) in `ℤ[M][L]`. -/
theorem ppi_factor_dvd_specialize {r s : ℕ} (h : IsTorusPair r s) (σ η : Bool) (ℓ : ℤ) :
    ∀ Q : RecOp, InLocalizedAnnihilator (coloredJones (twFamilyKnot r s h σ η ℓ)) Q →
      twFamilyFactor σ ∣ specialize Q := by
  refine ppi_dvd_specialize_of_primitive fun Q hQ0 hprim hQ ↦ ?_
  have h3 := ((twFamilyClauses_twFamilyKnot h σ η ℓ).2.2.1 Q hQ0 hprim hQ).2
  cases σ
  · exact extraFactorMirror_dvd_of_toComparison_dvd h3
  · exact extraFactor_dvd_of_toComparison_dvd h3

/-- **Every integral annihilator**: an operator with coefficients in `ℤ[t][M]` annihilating the
coloured Jones function of `W_(ε,ℓ)(T_η)` at all integers has specialization divisible by the
obstruction factor in `ℤ[M][L]`. -/
theorem ppi_factor_dvd_specialize_of_annihilates {r s : ℕ} (h : IsTorusPair r s) (σ η : Bool)
    (ℓ : ℤ) :
    ∀ Q : RecOp, Annihilates Q (coloredJones (twFamilyKnot r s h σ η ℓ)) →
      twFamilyFactor σ ∣ specialize Q := by
  intro Q hQ
  refine ppi_factor_dvd_specialize h σ η ℓ Q ⟨1, one_ne_zero, ?_⟩
  rwa [Polynomial.C_1, one_mul]

end AJConjecture
