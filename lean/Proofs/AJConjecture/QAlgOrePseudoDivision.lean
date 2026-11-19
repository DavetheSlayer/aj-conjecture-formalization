import Mathlib
import AJConjecture.QAlgOreMulAssoc
import AJConjecture.QAlgOreMulDegree

/-!
# Right pseudo-division in the Ore product

Over a commutative domain `A` with an injective endomorphism, every `P` can be divided on the
right by a nonzero `G` after multiplication by a nonzero constant: `β P = S ⋆ G + R` with
`deg R < deg G`. This is right Euclidean division in `Frac(A)[L; σ]` with denominators cleared.
-/

open Polynomial

namespace AJConjecture

/-- The Ore product with `0` on the left is `0`. -/
private theorem oreMul_zero_left_pseudoDivision {A : Type*} [Semiring A] (σ : A →+* A)
    (Q : A[X]) : oreMul σ 0 Q = 0 := by
  unfold oreMul
  exact Polynomial.sum_zero_index _

/-- A constant factor moves into the left argument of an Ore product. -/
private theorem C_mul_oreMul_pseudoDivision {A : Type*} [Semiring A] (σ : A →+* A) (c : A)
    (P Q : A[X]) : C c * oreMul σ P Q = oreMul σ (C c * P) Q := by
  rw [← oreMul_C_left σ c (oreMul σ P Q), ← oreMul_assoc, oreMul_C_left]

/-- The leading-term cancellation step of right pseudo-division: multiplying `P` by the
constant `σ^[deg P - deg G] (lc G)` and subtracting a monomial left multiple of `G` lowers the
degree. -/
private theorem degree_C_mul_sub_oreMul_monomial_lt {A : Type*} [CommRing A] [IsDomain A]
    {σ : A →+* A} (hσ : Function.Injective σ) {P G : A[X]} (hG : G ≠ 0)
    (hPG : G.degree ≤ P.degree) :
    (C (σ^[P.natDegree - G.natDegree] G.leadingCoeff) * P -
      oreMul σ (monomial (P.natDegree - G.natDegree) P.leadingCoeff) G).degree < P.degree := by
  have hP : P ≠ 0 := fun h ↦ hG (by simpa [h] using hPG)
  have hdeg : G.natDegree ≤ P.natDegree := Polynomial.natDegree_le_natDegree hPG
  have hg : σ^[P.natDegree - G.natDegree] G.leadingCoeff ≠ 0 := fun h ↦ by
    rw [← iterate_map_zero σ (P.natDegree - G.natDegree)] at h
    exact Polynomial.leadingCoeff_ne_zero.mpr hG (hσ.iterate _ h)
  have hlcP : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hM : monomial (P.natDegree - G.natDegree) P.leadingCoeff ≠ 0 :=
    (Polynomial.monomial_eq_zero_iff _ _).not.mpr hlcP
  have hMdeg : (monomial (P.natDegree - G.natDegree) P.leadingCoeff).natDegree =
      P.natDegree - G.natDegree := Polynomial.natDegree_monomial_eq _ hlcP
  have hnat : (oreMul σ (monomial (P.natDegree - G.natDegree) P.leadingCoeff) G).natDegree =
      P.natDegree := by
    rw [natDegree_oreMul hσ hM hG, hMdeg]
    omega
  have hCP : (C (σ^[P.natDegree - G.natDegree] G.leadingCoeff) * P).degree = P.degree :=
    Polynomial.degree_C_mul hg
  have hlc : (oreMul σ (monomial (P.natDegree - G.natDegree) P.leadingCoeff) G).leadingCoeff =
      P.leadingCoeff * σ^[P.natDegree - G.natDegree] G.leadingCoeff := by
    have h := coeff_oreMul_natDegree_add σ (monomial (P.natDegree - G.natDegree) P.leadingCoeff) G
    rw [hMdeg, Nat.sub_add_cancel hdeg, Polynomial.leadingCoeff_monomial] at h
    rw [← h, Polynomial.leadingCoeff, hnat]
  rw [← hCP]
  refine Polynomial.degree_sub_lt_left ?_ (mul_ne_zero (Polynomial.C_ne_zero.mpr hg) hP) ?_
  · rw [hCP, Polynomial.degree_eq_natDegree hP,
      Polynomial.degree_eq_natDegree (oreMul_ne_zero hσ hM hG), hnat]
  · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hlc, mul_comm]

/-- Right pseudo-division: `C β * P = S ⋆ G + R` with `β ≠ 0` and `deg R < deg G`. -/
theorem exists_C_mul_eq_oreMul_add {A : Type*} [CommRing A] [IsDomain A] {σ : A →+* A}
    (hσ : Function.Injective σ) (P : A[X]) {G : A[X]} (hG : G ≠ 0) :
    ∃ β : A, β ≠ 0 ∧ ∃ S R : A[X], C β * P = oreMul σ S G + R ∧ R.degree < G.degree := by
  induction P using Polynomial.degree_lt_wf.induction with
  | _ P ih =>
    by_cases hPG : P.degree < G.degree
    · exact ⟨1, one_ne_zero, 0, P, by
        rw [Polynomial.C_1, one_mul, oreMul_zero_left_pseudoDivision, zero_add], hPG⟩
    · have hg : σ^[P.natDegree - G.natDegree] G.leadingCoeff ≠ 0 := fun h ↦ by
        rw [← iterate_map_zero σ (P.natDegree - G.natDegree)] at h
        exact Polynomial.leadingCoeff_ne_zero.mpr hG (hσ.iterate _ h)
      obtain ⟨β, hβ, S, R, hSR, hR⟩ :=
        ih _ (degree_C_mul_sub_oreMul_monomial_lt hσ hG (not_lt.mp hPG))
      refine ⟨β * σ^[P.natDegree - G.natDegree] G.leadingCoeff, mul_ne_zero hβ hg,
        S + C β * monomial (P.natDegree - G.natDegree) P.leadingCoeff, R, ?_, hR⟩
      rw [oreMul_add_left, ← C_mul_oreMul_pseudoDivision, Polynomial.C_mul, mul_assoc,
        add_right_comm, ← hSR]
      ring

end AJConjecture
