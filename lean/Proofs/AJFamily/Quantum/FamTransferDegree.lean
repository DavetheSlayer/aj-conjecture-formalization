import Mathlib
import AJFamily.Quantum.FamTransferPoly

/-!
# Degree bounds in `J`

The family basis polynomials and target polynomial have degree at most `2m + 3` in `J`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The basis polynomials have degree at most `2m + 3` in `J`. -/
theorem natDegree_famBasisPoly_le {R : Type*} [CommRing R] (m : ℕ) (q : R) {i : ℕ}
    (hi : i ≤ 2 * m + 3) : (famBasisPoly m q i).natDegree ≤ 2 * m + 3 := by
  unfold famBasisPoly
  have h1 : (∏ r ∈ Finset.range i,
      (C (C (q ^ r) - X) * (C X - C (C (q ^ (r + 1))) * X) : R[X][X])).natDegree ≤ i := by
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ 1 fun r _ ↦ ?_).trans (by simp)
    compute_degree
  have h2 : (∏ r ∈ Finset.Ico i (2 * m + 3),
      (C (X - C (q ^ (r + 1))) * (C (C (q ^ r)) - C X * X) : R[X][X])).natDegree ≤
        2 * m + 3 - i := by
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ 1 fun r _ ↦ ?_).trans (by simp)
    compute_degree
  exact natDegree_mul_le.trans (by omega)

/-- The cubic factor `(1 - qJ)(x - qJ)(q^(2m+2) - xJ)` of the family adjoint has degree at
most `3` in `J`. -/
private theorem natDegree_famAdjointCubic_le {R : Type*} [CommRing R] (m : ℕ) (q : R) :
    ((1 - C (C q) * X) * (C X - C (C q) * X) * (C (C (q ^ (2 * m + 2))) - C X * X) :
      R[X][X]).natDegree ≤ 3 := by
  compute_degree

/-- The substitution `J ↦ qJ` does not raise the degree in `J`. -/
private theorem natDegree_comp_famScaling_le {R : Type*} [CommRing R] (q : R)
    (n : R[X][X]) : (n.comp (C (C q) * X)).natDegree ≤ n.natDegree := by
  have hs : (C (C q) * X : R[X][X]).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans natDegree_X_le
  refine natDegree_comp_le.trans ?_
  exact (Nat.mul_le_mul_left _ hs).trans (by omega)

/-- The family adjoint operator raises the degree in `J` by at most two. -/
private theorem natDegree_famAdjoint_le {R : Type*} [CommRing R] (m : ℕ) (q : R)
    (n : R[X][X]) : (famAdjoint m q n).natDegree ≤ n.natDegree + 2 := by
  unfold famAdjoint
  refine natDegree_add_le_of_degree_le ?_ ?_
  · have hX : (C (C (q ^ (2 * m + 3)) * X) * X : R[X][X]).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans natDegree_X_le
    exact (natDegree_mul_le_of_le hX le_rfl).trans (by omega)
  · rw [natDegree_divX_eq_natDegree_tsub_one]
    have hcomp := natDegree_comp_famScaling_le q n
    have h : (C (C (q ^ (2 * m + 2)) * X) * n -
        (1 - C (C q) * X) * (C X - C (C q) * X) * (C (C (q ^ (2 * m + 2))) - C X * X) *
          n.comp (C (C q) * X)).natDegree ≤ n.natDegree + 3 := by
      refine (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans (by omega)) ?_)
      exact (natDegree_mul_le_of_le (natDegree_famAdjointCubic_le m q) hcomp).trans (by omega)
    omega

/-- The `d`-th family adjoint Chebyshev operator raises the degree in `J` by at most `2 d`. -/
private theorem natDegree_famCheb_le {R : Type*} [CommRing R] (m : ℕ) (q : R) :
    ∀ (d : ℕ) (n : R[X][X]), (famCheb m q d n).natDegree ≤ n.natDegree + 2 * d
  | 0, n => by
    rw [famCheb, two_mul]
    exact natDegree_add_le_of_degree_le (by omega) (by omega)
  | 1, n => by
    rw [famCheb]
    exact natDegree_famAdjoint_le m q n
  | d + 2, n => by
    rw [famCheb]
    have h1 := natDegree_famCheb_le m q (d + 1) (famAdjoint m q n)
    have h2 := natDegree_famCheb_le m q d n
    have h3 := natDegree_famAdjoint_le m q n
    exact (natDegree_sub_le _ _).trans
      (max_le (by omega) ((natDegree_C_mul_le _ _).trans (by omega)))

set_option linter.unusedVariables false in
/-- The family target polynomial has degree at most `2m + 3` in `J`. -/
theorem natDegree_famTarget_le {R : Type*} [CommRing R] (m : ℕ) (hm : 1 ≤ m) (q : R) :
    (famTarget m q).natDegree ≤ 2 * m + 3 := by
  unfold famTarget
  have h5 := natDegree_famCheb_le m q (m - 1) 1
  have h6 := natDegree_famCheb_le m q m (1 - C (C q) * X)
  have h7 := natDegree_famCheb_le m q (m + 1) (C (C q) * X)
  have hlin : (1 - C (C q) * X : R[X][X]).natDegree ≤ 1 := by compute_degree
  have hmon : (C (C q) * X : R[X][X]).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans natDegree_X_le
  rw [natDegree_one] at h5
  refine (natDegree_sub_le _ _).trans (max_le (natDegree_add_le_of_degree_le ?_ ?_) (by omega))
  · exact (natDegree_C_mul_le _ _).trans (by omega)
  · exact (natDegree_C_mul_le _ _).trans (by omega)

end AJConjecture
