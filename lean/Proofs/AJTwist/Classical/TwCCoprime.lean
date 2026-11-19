import Mathlib
import AJConjecture.ComparisonDvdDescent
import AJConjecture.ExtraFactorPrime
import AJTwist.Classical.TwCReverse
import AJTwist.Classical.TwCWitness

/-!
# `E` and `E^∨` are coprime to the bounds (Unit C3, the resultants)

Source: revision 5, Section 7.3 (`classical.tex`, eqs. (allbresultant), (allcresultant)):
the resultants `Res_L(E, B_k)`, `Res_L(E, C_k)` are nonzero and `E(M, 1) = 4 M²`, so
`gcd_R(E, (L - 1) 𝒫_(k₁) 𝒫_(k₂)) = 1` in `R = ℚ(M)[L, L⁻¹]` for all signed indices; Section 8.2
(`conclusion.tex`) for `E^∨ = M⁴ E(M⁻¹, L)` and the mirrored bound.

The formal proof does not compute resultants: `E` is prime in `R`
(`prime_toComparison_extraFactor`), and if it divided the bound in `R` it would divide it in
`ℤ[M][L]` (`extraFactor_dvd_of_toComparison_dvd`), so the bound would vanish at the zero
`(2, L)`, `L² - L + 16 = 0`, of `E`, against `evalPoint_twBound_witness_ne_zero`. (The two
resultant formulas and `E(M, 1) = 4 M²` were checked symbolically for `k ≤ 4`,
`SCR/C/py/v7_resultants.py`; they are not needed.)

* `isCoprime_extraFactor_twBound`: `gcd_R(E, twBound k₁ k₂) = 1`. Route: as
  `isCoprime_extraFactor_pair` (`AJHandoff.TorusKnot.PairKAPolyHorizontal`), with the
  principal-ideal-ring instance of `ℚ(M)[L, L⁻¹]` restated (it is private there).
* `isCoprime_extraFactorMirror_twBound_reverse`: `gcd_R(E^∨, (twBound k₁ k₂).reverse) = 1`.
  Route: apply the ring automorphism `LaurentPolynomial.invert` to the first statement and
  remove the units `T 2`, `T deg` (`toComparison_extraFactorMirror`, `toComparison_reverse`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The Laurent polynomial ring over a field is a principal ideal ring: it is the localisation
of the principal ideal domain `F[X]` at the powers of `X`. -/
private theorem isPrincipalIdealRing_laurentPolynomial_twCCoprime (F : Type) [Field F] :
    IsPrincipalIdealRing (LaurentPolynomial F) := by
  refine ⟨fun J ↦ ?_⟩
  rw [← IsLocalization.map_under (Submonoid.powers (X : F[X])) (LaurentPolynomial F) J]
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal (J.under F[X])
  refine ⟨algebraMap F[X] (LaurentPolynomial F) g, ?_⟩
  rw [hg, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]

/-- `E` is coprime to every bound `(L - 1) 𝒫_(k₁) 𝒫_(k₂)` in the comparison ring. -/
theorem isCoprime_extraFactor_twBound (k₁ k₂ : ℤ) :
    IsCoprime (toComparison extraFactor) (toComparison (twBound k₁ k₂)) := by
  have hnd : ¬ toComparison extraFactor ∣ toComparison (twBound k₁ k₂) := by
    intro hdvd
    obtain ⟨G, hG⟩ := extraFactor_dvd_of_toComparison_dvd hdvd
    obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = -63 := IsAlgClosed.exists_pow_nat_eq (-63) (by norm_num)
    have hL : ((1 + s) / 2) ^ 2 - (1 + s) / 2 + 16 = 0 := by linear_combination (1 / 4 : ℂ) * hs
    apply evalPoint_twBound_witness_ne_zero _ hL k₁ k₂
    rw [hG, mapC, Polynomial.map_mul, evalPoint, eval₂_mul, ← evalPoint,
      evalPoint_extraFactor_witness _ hL, zero_mul]
  have := isPrincipalIdealRing_laurentPolynomial_twCCoprime (RatFunc ℚ)
  exact (prime_toComparison_extraFactor.coprime_iff_not_dvd).mpr hnd

/-- `E^∨` is coprime to the reverse of every bound in the comparison ring. -/
theorem isCoprime_extraFactorMirror_twBound_reverse (k₁ k₂ : ℤ) :
    IsCoprime (toComparison extraFactorMirror) (toComparison (twBound k₁ k₂).reverse) := by
  have h := (isCoprime_extraFactor_twBound k₁ k₂).map
    (LaurentPolynomial.invert (R := RatFunc ℚ) : ComparisonRing →+* ComparisonRing)
  rw [toComparison_extraFactorMirror, toComparison_reverse,
    isCoprime_mul_unit_left_left (LaurentPolynomial.isUnit_T 2),
    isCoprime_mul_unit_right_right (LaurentPolynomial.isUnit_T _)]
  exact h

/-- The reversed bounds are nonzero polynomials. -/
theorem twBound_reverse_ne_zero (k₁ k₂ : ℤ) : (twBound k₁ k₂).reverse ≠ 0 :=
  fun h ↦ twBound_ne_zero k₁ k₂ (reverse_eq_zero.mp h)

end AJConjecture
