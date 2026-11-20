import Mathlib
import AJTwist.Classical.TwCFourFamilies
import AJPaper.Filling.PpAFilling

/-!
# What is now known about the A-polynomial of the twisted doubles (PpA, unit B)

Source: arXiv:2611.24826v1, Section 7.6 (`classical.tex`), last sentences: "This extension
concerns the companion-abelian filling. Equation (classicalcontainment) is the general bound for
the full satellite curve." The paper does not claim that the second filling factor `𝒫_a`
occurs, and neither does this file.

Combining the bound `A ∣ (L - 1) 𝒫_(-ℓ) 𝒫_a` (`twClassClauses_twFamilyKnot_neg`,
`a = twIndex η r s ℓ = η r s - ℓ`) with `(L - 1) 𝒫_(-ℓ) ∣ A` (`ppa_fillingFactor_dvd_neg`), in
`R = ℚ(M)[L, L⁻¹]` every A-polynomial `A` of `W_(-,ℓ)(T_η)` is one of two polynomials up to a
unit:

* `ppa_aPolynomial_cases_neg`: `A ≐ (L - 1) 𝒫_(-ℓ)` or `A ≐ (L - 1) 𝒫_(-ℓ) 𝒫_a`;
* `ppa_aPolynomial_cases_pos`: the same for the positive clasp, with the reversed polynomials
  `(L - 1) 𝒫_ℓ` and `(L - 1) 𝒫_ℓ 𝒫_(-a)`;
* `ppa_aPolynomial_of_index_zero_neg`, `_pos`: for `a = 0`, i.e. `ℓ = η r s`, the A-polynomial
  is determined: `A ≐ (L - 1) 𝒫_(-ℓ)` (resp. the reverse of `(L - 1) 𝒫_ℓ`).

So the factors `L - 1` and `𝒫_(-ℓ)` of `twBound (-ℓ) a` are known to occur for all four
families; whether `𝒫_a` occurs (`a ≠ 0`) is open here, except for `ℓ = 0`, `η = +`, negative
clasp, where `aPolynomial_pair_associated_famBound` (`AJHandoff.TorusKnot.PairKReverse`) shows
that it does. Deciding it in general needs the reverse inclusion for nonabelian companion
representations of the twisted block lists (the analogue of
`exists_pairRevEdge_annulus` with a twisted head band for an arbitrary tuple `y`).

Route. `R` is a domain. Write `F` for the image of `(L - 1) 𝒫_(-ℓ)`; then
`toComparison (twBound (-ℓ) a) = F * toComparison (twP a)` (`twBound`, `map_mul`), `F ∣ A` and
`A ∣ F * toComparison (twP a)`. With `A = F D`, cancel `F ≠ 0` (it is a product of two primes,
or of a prime and `1`): `D ∣ toComparison (twP a)`. If `a = 0`, `twP 0 = 1` and `D` is a unit. If
`a ≠ 0`, `toComparison (twP a)` is prime (`ppa_prime_toComparison_twP`), hence irreducible, so
`D` is a unit or associated to it. The positive clasp is the same with
`Polynomial.reverse_mul_of_domain` and `ppa_prime_toComparison_twP_reverse`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `toComparison` is injective. -/
private theorem toComparison_injective_ppaDichotomy : Function.Injective toComparison :=
  Polynomial.toLaurent_injective.comp (Polynomial.map_injective _ intPolyToRatFunc_injective)

/-- `(L - 1) 𝒫_k` is not zero. -/
private theorem sub_one_mul_twP_ne_zero_ppaDichotomy (k : ℤ) :
    ((X - 1) * twP k : ℤ[X][X]) ≠ 0 := by
  refine mul_ne_zero ?_ fun h0 ↦ ppa_coeff_zero_twP_ne_zero k (by rw [h0, coeff_zero])
  rw [← C_1]
  exact X_sub_C_ne_zero 1

/-- In a domain, an element between `F` and `F Q`, `Q` prime, is associated to one of them. -/
private theorem associated_or_of_dvd_mul_prime_ppaDichotomy {R : Type*} [CommRing R]
    [IsDomain R] {F A Q : R} (hF : F ≠ 0) (hFA : F ∣ A) (hAQ : A ∣ F * Q) (hQ : Prime Q) :
    Associated A F ∨ Associated A (F * Q) := by
  obtain ⟨D, rfl⟩ := hFA
  rcases hQ.irreducible.dvd_iff.1 ((mul_dvd_mul_iff_left hF).1 hAQ) with hu | hD
  · exact Or.inl (associated_mul_unit_left F D hu)
  · exact Or.inr (hD.symm.mul_left F)

/-- Negative clasp: every A-polynomial of `W_(-,ℓ)(T_η)` is `(L - 1) 𝒫_(-ℓ)` or the full bound
`(L - 1) 𝒫_(-ℓ) 𝒫_a`, up to a unit of `ℚ(M)[L, L⁻¹]`. -/
theorem ppa_aPolynomial_cases_neg {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ)
    {A : ℤ[X][X]} (hA : IsAPolynomialOf (eigenvalueSet (twFamilyKnot r s h true η ℓ)) A) :
    Associated (toComparison A) (toComparison ((X - 1) * twP (-ℓ))) ∨
      Associated (toComparison A) (toComparison (twBound (-ℓ) (twIndex η r s ℓ))) := by
  have hb := ((twClassClauses_twFamilyKnot_neg h η ℓ).2 A hA).1
  have hd := ppa_fillingFactor_dvd_neg h η ℓ hA
  by_cases ha : twIndex η r s ℓ = 0
  · rw [ha, twBound, twP_zero, mul_one] at hb
    exact Or.inl (associated_of_dvd_dvd hb hd)
  · have he : toComparison (twBound (-ℓ) (twIndex η r s ℓ)) =
        toComparison ((X - 1) * twP (-ℓ)) * toComparison (twP (twIndex η r s ℓ)) := by
      rw [twBound, map_mul]
    rw [he] at hb ⊢
    exact associated_or_of_dvd_mul_prime_ppaDichotomy
      ((map_ne_zero_iff _ toComparison_injective_ppaDichotomy).2
        (sub_one_mul_twP_ne_zero_ppaDichotomy (-ℓ))) hd hb (ppa_prime_toComparison_twP _ ha)

/-- Positive clasp: every A-polynomial of `W_(+,ℓ)(T_η)` is the reverse of `(L - 1) 𝒫_ℓ` or of
the full bound `(L - 1) 𝒫_ℓ 𝒫_(-a)`, up to a unit of `ℚ(M)[L, L⁻¹]`. -/
theorem ppa_aPolynomial_cases_pos {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ)
    {A : ℤ[X][X]} (hA : IsAPolynomialOf (eigenvalueSet (twFamilyKnot r s h false η ℓ)) A) :
    Associated (toComparison A) (toComparison ((X - 1) * twP ℓ).reverse) ∨
      Associated (toComparison A)
        (toComparison (twBound ℓ (-(twIndex η r s ℓ))).reverse) := by
  have hb := ((twClassClauses_twFamilyKnot_pos h η ℓ).2 A hA).1
  have hd := ppa_fillingFactor_dvd_pos h η ℓ hA
  by_cases ha : twIndex η r s ℓ = 0
  · rw [ha, neg_zero, twBound, twP_zero, mul_one] at hb
    exact Or.inl (associated_of_dvd_dvd hb hd)
  · have he : toComparison (twBound ℓ (-(twIndex η r s ℓ))).reverse =
        toComparison ((X - 1) * twP ℓ).reverse *
          toComparison (twP (-(twIndex η r s ℓ))).reverse := by
      rw [twBound, reverse_mul_of_domain, map_mul]
    rw [he] at hb ⊢
    exact associated_or_of_dvd_mul_prime_ppaDichotomy
      ((map_ne_zero_iff _ toComparison_injective_ppaDichotomy).2
        (reverse_eq_zero.not.2 (sub_one_mul_twP_ne_zero_ppaDichotomy ℓ))) hd hb
      (ppa_prime_toComparison_twP_reverse _ (neg_ne_zero.2 ha))

/-- Negative clasp with index `a = 0` (`ℓ = η r s`): the A-polynomial is `(L - 1) 𝒫_(-ℓ)`. -/
theorem ppa_aPolynomial_of_index_zero_neg {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ)
    (ha : twIndex η r s ℓ = 0) {A : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet (twFamilyKnot r s h true η ℓ)) A) :
    Associated (toComparison A) (toComparison ((X - 1) * twP (-ℓ))) := by
  have hb := ((twClassClauses_twFamilyKnot_neg h η ℓ).2 A hA).1
  rw [ha, twBound, twP_zero, mul_one] at hb
  exact associated_of_dvd_dvd hb (ppa_fillingFactor_dvd_neg h η ℓ hA)

/-- Positive clasp with index `a = 0`: the A-polynomial is the reverse of `(L - 1) 𝒫_ℓ`. -/
theorem ppa_aPolynomial_of_index_zero_pos {r s : ℕ} (h : IsTorusPair r s) (η : Bool) (ℓ : ℤ)
    (ha : twIndex η r s ℓ = 0) {A : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet (twFamilyKnot r s h false η ℓ)) A) :
    Associated (toComparison A) (toComparison ((X - 1) * twP ℓ).reverse) := by
  have hb := ((twClassClauses_twFamilyKnot_pos h η ℓ).2 A hA).1
  rw [ha, neg_zero, twBound, twP_zero, mul_one] at hb
  exact associated_of_dvd_dvd hb (ppa_fillingFactor_dvd_pos h η ℓ hA)

end AJConjecture
