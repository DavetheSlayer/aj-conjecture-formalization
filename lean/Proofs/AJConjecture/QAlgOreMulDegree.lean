import Mathlib
import AJConjecture.QAlgOreMul

/-!
# Degrees in the Ore product

The degree of an Ore product is at most the sum of the degrees, the coefficient in that degree
is `lc(P) σ^(deg P)(lc(Q))`, and over a domain with an injective endomorphism degrees add: the
skew polynomial ring is a domain.
-/

open Polynomial

namespace AJConjecture

/-- The degree of an Ore product is at most the sum of the degrees. -/
theorem natDegree_oreMul_le {A : Type*} [Semiring A] (σ : A →+* A) (P Q : A[X]) :
    (oreMul σ P Q).natDegree ≤ P.natDegree + Q.natDegree := by
  unfold oreMul
  simp only [Polynomial.sum_def]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk ↦ ?_
  exact (Polynomial.natDegree_monomial_le _).trans
    (Nat.add_le_add (Polynomial.le_natDegree_of_mem_supp i hi)
      (Polynomial.le_natDegree_of_mem_supp k hk))

/-- The top-degree coefficient of an Ore product, as a double sum over ranges. -/
private theorem coeff_oreMul_eq_sum_range {A : Type*} [Semiring A] (σ : A →+* A) (P Q : A[X])
    (n : ℕ) :
    (oreMul σ P Q).coeff n = ∑ i ∈ Finset.range (P.natDegree + 1),
      ∑ k ∈ Finset.range (Q.natDegree + 1),
        if i + k = n then P.coeff i * σ^[i] (Q.coeff k) else 0 := by
  unfold oreMul
  rw [Polynomial.sum_over_range]
  · rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Polynomial.sum_over_range]
    · rw [Polynomial.finsetSum_coeff]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Polynomial.coeff_monomial_apply]
    · intro k
      simp [iterate_map_zero]
  · intro i
    simp [Polynomial.sum_def]

/-- The coefficient of an Ore product in the top degree. -/
theorem coeff_oreMul_natDegree_add {A : Type*} [Semiring A] (σ : A →+* A) (P Q : A[X]) :
    (oreMul σ P Q).coeff (P.natDegree + Q.natDegree) =
      P.leadingCoeff * σ^[P.natDegree] Q.leadingCoeff := by
  rw [coeff_oreMul_eq_sum_range, Finset.sum_eq_single P.natDegree]
  · rw [Finset.sum_eq_single Q.natDegree]
    · rw [ite_eq_left rfl]
      rfl
    · intro k _ hk
      rw [ite_eq_right (by omega)]
    · intro h
      exact absurd (Finset.self_mem_range_succ _) h
  · intro i hi hne
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    rw [Finset.mem_range] at hi hk
    rw [ite_eq_right (by omega)]
  · intro h
    exact absurd (Finset.self_mem_range_succ _) h

/-- Over a domain with an injective endomorphism, the top coefficient of an Ore product of
nonzero polynomials is nonzero. -/
private theorem coeff_oreMul_natDegree_add_ne_zero {A : Type*} [CommRing A] [IsDomain A]
    {σ : A →+* A} (hσ : Function.Injective σ) {P Q : A[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (oreMul σ P Q).coeff (P.natDegree + Q.natDegree) ≠ 0 := by
  rw [coeff_oreMul_natDegree_add]
  refine mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP) fun h ↦ ?_
  rw [← iterate_map_zero σ P.natDegree] at h
  exact Polynomial.leadingCoeff_ne_zero.mpr hQ (hσ.iterate _ h)

/-- Over a domain with an injective endomorphism, degrees add in an Ore product. -/
theorem natDegree_oreMul {A : Type*} [CommRing A] [IsDomain A] {σ : A →+* A}
    (hσ : Function.Injective σ) {P Q : A[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (oreMul σ P Q).natDegree = P.natDegree + Q.natDegree :=
  le_antisymm (natDegree_oreMul_le σ P Q)
    (Polynomial.le_natDegree_of_ne_zero (coeff_oreMul_natDegree_add_ne_zero hσ hP hQ))

/-- Over a domain with an injective endomorphism, the Ore product has no zero divisors. -/
theorem oreMul_ne_zero {A : Type*} [CommRing A] [IsDomain A] {σ : A →+* A}
    (hσ : Function.Injective σ) {P Q : A[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    oreMul σ P Q ≠ 0 := fun h ↦
  coeff_oreMul_natDegree_add_ne_zero hσ hP hQ (by rw [h, Polynomial.coeff_zero])

end AJConjecture
