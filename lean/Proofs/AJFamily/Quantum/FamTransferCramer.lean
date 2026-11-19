import Mathlib
import AJFamily.Quantum.FamTransferCoeff
import AJFamily.Quantum.FamTransferDegree

/-!
# The Cramer identity

`sum_famCoeff_mul_famBasisPoly`, Cramer's rule for the family in the monomial basis of `J`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The Cramer identity `∑_i A_i P_i = famDet m q · famTarget m q`. -/
theorem sum_famCoeff_mul_famBasisPoly {R : Type*} [CommRing R] (m : ℕ) (hm : 1 ≤ m) (q : R) :
    ∑ i : Fin (2 * m + 4), C (famCoeff m q i) * famBasisPoly m q i =
      C (famDet m q) * famTarget m q := by
  refine AddMonoidAlgebra.ext (Finsupp.ext fun k ↦ ?_)
  rw [finsetSum_coeff, coeff_C_mul]
  simp only [coeff_C_mul]
  by_cases hk : k < 2 * m + 4
  · have h := congrFun (Matrix.mulVec_cramer (famMatrix m q)
      (fun k : Fin (2 * m + 4) ↦ (famTarget m q).coeff k)) ⟨k, hk⟩
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [famDet, ← h]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [famCoeff, mul_comm]
    rfl
  · have hbasis : ∀ i : Fin (2 * m + 4), (famBasisPoly m q i).coeff k = 0 := fun i ↦
      coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_famBasisPoly_le m q (by omega)) (by omega))
    have htarget : (famTarget m q).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_famTarget_le m hm q) (by omega))
    simp only [hbasis, htarget, mul_zero, Finset.sum_const_zero]

end AJConjecture
