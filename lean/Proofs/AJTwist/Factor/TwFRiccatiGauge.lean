import Mathlib
import AJTwist.Factor.TwFRiccati

/-!
# Two solutions of the Riccati equation give a solution for the cofactor (TwF, unit F4)

Source: revision 5, Section 5.6: "Two distinct such divisors would have a monic degree-two least
common left multiple right-dividing `P`, by the right Euclidean algorithm."

Instead of the least common left multiple we use the gauge transformation: if
`β P = S ⋆ (r₁ L + r₀)` and `(r₀', r₁')` is another solution of the Riccati equation of `P`, put
`θ = r₀ r₁' - r₁ r₀'` (the value of `r₁ L + r₀` on the second solution, cleared). Then
`(r₀' σ(θ), σ(r₁') θ)` is a solution of the Riccati equation of the cofactor `S`
(`α = ρ' σ(θ̃)/θ̃` with `θ̃ = θ/r₁'`), so if `θ ≠ 0` the cofactor has a right pseudo-factor of
degree one, and `P` is a product of three factors of degree one.

* `oreRiccati_cofactor_three`: the polynomial identity for operators of order three:
  `oreRiccati σ 2 S (r₀' σθ) (σ r₁' · θ) = σ(θ) · oreRiccati σ 3 (S ⋆ (r₁ L + r₀)) r₀' r₁'`
  for `S` of degree at most `2`. Proof: write `S = s₂ L² + s₁ L + s₀`, compute the Ore product
  (`oreMul_add_left`, `oreMul_monomial_monomial`), unfold the two finite sums and `ring`
  (`σ` is a ring homomorphism; the atoms are `σ^i` of `r₀, r₁, r₀', r₁'`).
* `exists_cofactor_pseudoFactor_of_two_solutions`: the consequence, by
  `oreRiccati_C_mul`, `exists_pseudoFactor_of_oreRiccati_eq_zero`.

Checked on random examples (scratch `check_zero2.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The gauge identity for the cofactor of a right factor of degree one, order three. -/
theorem oreRiccati_cofactor_three {A : Type*} [CommRing A] (σ : A →+* A) (S : A[X])
    (hS : S.natDegree ≤ 2) (r₀ r₁ r₀' r₁' : A) :
    oreRiccati σ 2 S (r₀' * σ (r₀ * r₁' - r₁ * r₀')) (σ r₁' * (r₀ * r₁' - r₁ * r₀')) =
      σ (r₀ * r₁' - r₁ * r₀') *
        oreRiccati σ 3 (oreMul σ S (C r₁ * X + C r₀)) r₀' r₁' := by
  have hS3 : oreMul σ S (C r₁ * X + C r₀) =
      monomial 3 (S.coeff 2 * σ (σ r₁)) +
        monomial 2 (S.coeff 1 * σ r₁ + S.coeff 2 * σ (σ r₀)) +
        monomial 1 (S.coeff 0 * r₁ + S.coeff 1 * σ r₀) + monomial 0 (S.coeff 0 * r₀) := by
    conv_lhs => rw [S.as_sum_range' 3 (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, oreMul_add_left,
      C_mul_X_eq_monomial, ← monomial_zero_left (a := r₀), oreMul_add_right,
      oreMul_monomial_monomial, Function.iterate_succ, Function.iterate_zero, Function.comp,
      id, map_add]
    abel
  have c0 : (oreMul σ S (C r₁ * X + C r₀)).coeff 0 = S.coeff 0 * r₀ := by
    rw [hS3]
    simp [coeff_monomial]
  have c1 : (oreMul σ S (C r₁ * X + C r₀)).coeff 1 = S.coeff 0 * r₁ + S.coeff 1 * σ r₀ := by
    rw [hS3]
    simp [coeff_monomial]
  have c2 : (oreMul σ S (C r₁ * X + C r₀)).coeff 2 =
      S.coeff 1 * σ r₁ + S.coeff 2 * σ (σ r₀) := by
    rw [hS3]
    simp [coeff_monomial]
  have c3 : (oreMul σ S (C r₁ * X + C r₀)).coeff 3 = S.coeff 2 * σ (σ r₁) := by
    rw [hS3]
    simp [coeff_monomial]
  simp only [oreRiccati, Finset.sum_range_succ, Finset.sum_range_zero, Finset.prod_range_succ,
    Finset.prod_range_zero, Finset.prod_Ico_eq_prod_range, c0, c1, c2, c3, Nat.sub_self,
    Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceSub, Function.iterate_succ_apply,
    Function.iterate_zero_apply, map_neg, map_mul, map_sub]
  ring

set_option linter.unusedVariables false in
/-- If an operator of order at most three has the right pseudo-factor `r₁ L + r₀` and a second,
non-proportional solution of its Riccati equation, then the cofactor has a right pseudo-factor of
degree one. -/
theorem exists_cofactor_pseudoFactor_of_two_solutions {A : Type*} [CommRing A] [IsDomain A]
    {σ : A →+* A} (hσ : Function.Injective σ) {P S : A[X]} {β : A} (hβ : β ≠ 0)
    (hP : P.natDegree ≤ 3) {r₀ r₁ r₀' r₁' : A}
    (h : C β * P = oreMul σ S (C r₁ * X + C r₀)) (hr₁ : r₁ ≠ 0) (hr₁' : r₁' ≠ 0)
    (h' : oreRiccati σ 3 P r₀' r₁' = 0) (hne : r₀ * r₁' - r₁ * r₀' ≠ 0) :
    ∃ β₂ : A, β₂ ≠ 0 ∧ ∃ S₂ R₂ : A[X], R₂.natDegree = 1 ∧ C β₂ * S = oreMul σ S₂ R₂ := by
  by_cases hS0 : S = 0
  · refine ⟨1, one_ne_zero, 0, X, natDegree_X, ?_⟩
    rw [hS0, mul_zero]
    unfold oreMul
    exact (Polynomial.sum_zero_index _).symm
  have hGdeg : (C r₁ * X + C r₀ : A[X]).natDegree = 1 := natDegree_linear hr₁
  have hG : (C r₁ * X + C r₀ : A[X]) ≠ 0 := fun h0 ↦ by
    rw [h0, natDegree_zero] at hGdeg
    exact zero_ne_one hGdeg
  have hS : S.natDegree ≤ 2 := by
    have hdeg := congrArg natDegree h
    rw [natDegree_oreMul hσ hS0 hG, hGdeg] at hdeg
    have := (natDegree_C_mul_le β P).trans hP
    omega
  have hθ : σ (r₀ * r₁' - r₁ * r₀') ≠ 0 := (map_ne_zero_iff σ hσ).mpr hne
  have hlead : σ r₁' * (r₀ * r₁' - r₁ * r₀') ≠ 0 :=
    mul_ne_zero ((map_ne_zero_iff σ hσ).mpr hr₁') hne
  have hric : oreRiccati σ 2 S (r₀' * σ (r₀ * r₁' - r₁ * r₀'))
      (σ r₁' * (r₀ * r₁' - r₁ * r₀')) = 0 := by
    rw [oreRiccati_cofactor_three σ S hS, ← h, oreRiccati_C_mul, h', mul_zero, mul_zero]
  obtain ⟨β₂, hβ₂, S₂, hS₂⟩ := exists_pseudoFactor_of_oreRiccati_eq_zero hσ hS hlead hric
  exact ⟨β₂, hβ₂, S₂, _, natDegree_linear hlead, hS₂⟩

end AJConjecture
