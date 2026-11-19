import Mathlib
import AJHandoff.TorusKnot.PairKAPolyHorizontal
import AJTwist.Classical.TwCReverse
import AJPaper.Filling.PpAPolyFacts

/-!
# The abelian line and a prime factor: `(L - 1) P ∣ A` (PpA)

Source: arXiv:2611.24826v1, Lemma 7.1 (`boundary.tex`): "For a knot in `S³` this equation
includes `L - 1`", and Section 7.6: "`𝒫_k` is reduced, distinct from `L - 1`".

* `ppa_toComparison_sub_one_dvd`: `L - 1` divides every A-polynomial of a knot in
  `R = ℚ(M)[L, L⁻¹]` (`sub_one_dvd_aPolynomial` over `ℂ`, descended as in the private
  `toComparison_dvd_of_mapC_dvd_twCClauses` of `AJTwist.Classical.TwCClauses`);
* `ppa_sub_one_mul_dvd`: if moreover a prime `P` of `R`, not divisible by `L - 1`, divides the
  A-polynomial, so does `(L - 1) P` (write `A = (L - 1) A'`; `P ∣ (L - 1) A'` and `P ∤ L - 1`,
  since both are prime (`prime_toComparison_X_sub_one`) and `L - 1 ∤ P`);
* `ppa_toComparison_reverse_sub_one_mul`: in `R` the reverse of `(L - 1) P` is associated to
  `(L - 1) · P.reverse` (`Polynomial.reverse_mul_of_domain`; the reverse of `L - 1` is `1 - L`);
* `ppa_prime_toComparison_twP_reverse`: the reverse in `L` of `𝒫_k`, `k ≠ 0`, is prime in `R`
  (`toComparison_reverse`: it is the image of `𝒫_k` under the automorphism
  `LaurentPolynomial.invert`, `L ↦ L⁻¹`, times the unit `L^deg`; `ppa_prime_toComparison_twP`);
* `ppa_not_sub_one_dvd_twP_reverse`: `L - 1` does not divide the reverse of `𝒫_k`, `k ≠ 0`
  (apply the same automorphism, which sends `L - 1` to `-L⁻¹ (L - 1)`, to
  `ppa_not_sub_one_dvd_twP`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The reverse of `L - 1` is `-(L - 1)`. -/
private theorem reverse_X_sub_one_ppaSubOne : (X - 1 : ℤ[X][X]).reverse = -(X - 1) := by
  have hdeg : (X - 1 : ℤ[X][X]).natDegree = 1 := by compute_degree!
  have hE : (X - 1 : ℤ[X][X]) = X ^ 1 - C 1 := by simp
  rw [reverse, hdeg, hE, reflect_sub, reflect_monomial, reflect_C, revAt_le le_rfl]
  simp

/-- The automorphism `L ↦ L⁻¹` sends `L - 1` to `-L⁻¹ (L - 1)`. -/
private theorem invert_toComparison_X_sub_one_ppaSubOne :
    LaurentPolynomial.invert (toComparison (X - 1)) =
      toComparison (X - 1) * (-LaurentPolynomial.T (-1)) := by
  have h : toComparison (X - 1) = LaurentPolynomial.T 1 - 1 := by simp [toComparison]
  rw [h, map_sub, map_one, LaurentPolynomial.invert_T, mul_neg, sub_mul,
    ← LaurentPolynomial.T_add]
  simp

/-- If `L - 1` divides the reverse of `P` in the comparison ring, it divides `P`. -/
private theorem sub_one_dvd_of_dvd_reverse_ppaSubOne (P : ℤ[X][X])
    (h : toComparison (X - 1) ∣ toComparison P.reverse) :
    toComparison (X - 1) ∣ toComparison P := by
  rw [toComparison_reverse, (LaurentPolynomial.isUnit_T _).dvd_mul_right] at h
  have h1 := map_dvd (LaurentPolynomial.invert (R := RatFunc ℚ)) h
  rw [LaurentPolynomial.involutive_invert (toComparison P)] at h1
  refine dvd_trans ?_ h1
  rw [invert_toComparison_X_sub_one_ppaSubOne]
  exact (IsUnit.dvd_mul_right (LaurentPolynomial.isUnit_T (R := RatFunc ℚ) (-1)).neg).2 dvd_rfl

/-- `L - 1` divides every A-polynomial of a knot in the comparison ring. -/
theorem ppa_toComparison_sub_one_dvd (K : BraidKnot) {A : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet K) A) : toComparison (X - 1) ∣ toComparison A := by
  have hroot : (mapC A).IsRoot 1 := by
    rw [← dvd_iff_isRoot, C_1]
    exact sub_one_dvd_aPolynomial K hA
  rw [IsRoot, mapC, eval_one_map] at hroot
  have h0 : A.eval 1 = 0 :=
    Polynomial.map_injective _ (Int.cast_injective (α := ℂ)) (by simpa using hroot)
  have hd : (X - C 1 : ℤ[X][X]) ∣ A := dvd_iff_isRoot.2 h0
  rw [C_1] at hd
  exact map_dvd toComparison hd

/-- A prime of the comparison ring that divides an A-polynomial of a knot and is not divisible
by `L - 1` divides it together with `L - 1`. -/
theorem ppa_sub_one_mul_dvd (K : BraidKnot) {A P : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet K) A) (hP : Prime (toComparison P))
    (hne : ¬ toComparison (X - 1) ∣ toComparison P) (hPA : toComparison P ∣ toComparison A) :
    toComparison ((X - 1) * P) ∣ toComparison A := by
  obtain ⟨A', hA'⟩ := ppa_toComparison_sub_one_dvd K hA
  rw [hA'] at hPA ⊢
  rw [map_mul]
  rcases hP.dvd_or_dvd hPA with h1 | h1
  · exact absurd
      (hP.irreducible.dvd_symm prime_toComparison_X_sub_one.irreducible h1) hne
  · exact mul_dvd_mul_left _ h1

/-- The reverse in `L` of `(L - 1) P` is `(L - 1) · P.reverse` up to a unit. -/
theorem ppa_toComparison_reverse_sub_one_mul (P : ℤ[X][X]) :
    Associated (toComparison ((X - 1) * P).reverse) (toComparison ((X - 1) * P.reverse)) := by
  have h : ((X - 1) * P).reverse = -((X - 1) * P.reverse) := by
    rw [reverse_mul_of_domain, reverse_X_sub_one_ppaSubOne]
    ring
  rw [h, map_neg]
  exact ⟨-1, by simp⟩

/-- The reverse in `L` of `𝒫_k` is prime in the comparison ring for `k ≠ 0`. -/
theorem ppa_prime_toComparison_twP_reverse (k : ℤ) (hk : k ≠ 0) :
    Prime (toComparison (twP k).reverse) := by
  rw [toComparison_reverse]
  have h1 : Prime (LaurentPolynomial.invert (toComparison (twP k))) :=
    (MulEquiv.prime_iff (LaurentPolynomial.invert (R := RatFunc ℚ)).toMulEquiv).2
      (ppa_prime_toComparison_twP k hk)
  exact (associated_mul_unit_right _ _ (LaurentPolynomial.isUnit_T _)).prime h1

/-- `L - 1` does not divide the reverse of `𝒫_k` in the comparison ring for `k ≠ 0`. -/
theorem ppa_not_sub_one_dvd_twP_reverse (k : ℤ) (hk : k ≠ 0) :
    ¬ toComparison (X - 1) ∣ toComparison (twP k).reverse := fun h ↦
  ppa_not_sub_one_dvd_twP k hk (sub_one_dvd_of_dvd_reverse_ppaSubOne _ h)

end AJConjecture
