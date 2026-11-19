import Mathlib
import AJTwist.Quantum.TwQWindowPoly

/-!
# The Cramer identity and naturality for an arbitrary pole window (Unit Q3)

Source: revision 5, Section 3.3, eq. (physicalrow): the unique solution of
`𝒩 = ∑_i a_i Δ R_i`. Here without division: for every target `T` of degree at most `d` in `J`,
`∑_i c_i P_i = twDet d q · T` with the Cramer numerators `c_i = twCoeff d q T i`
(`sum_twCoeff_mul_twBasisPoly`; the case `d = 2m + 3`, `T = famTarget m q` is the library's
`sum_famCoeff_mul_famBasisPoly`). The identity holds over every commutative ring, in particular
over the dual numbers, where the factor theory reads the first-order jets.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The Cramer identity `∑_i c_i P_i = twDet d q · T` for a target of degree at most `d`. -/
theorem sum_twCoeff_mul_twBasisPoly {R : Type*} [CommRing R] (d : ℕ) (q : R) (T : R[X][X])
    (hT : T.natDegree ≤ d) :
    ∑ i : Fin (d + 1), C (twCoeff d q T i) * twBasisPoly d q i = C (twDet d q) * T := by
  refine AddMonoidAlgebra.ext (Finsupp.ext fun k ↦ ?_)
  rw [finsetSum_coeff, coeff_C_mul]
  simp only [coeff_C_mul]
  by_cases hk : k < d + 1
  · have h := congrFun (Matrix.mulVec_cramer (twMatrix d q)
      (fun k : Fin (d + 1) ↦ T.coeff k)) ⟨k, hk⟩
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [twDet, ← h]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [twCoeff, mul_comm]
    rfl
  · have hbasis : ∀ i : Fin (d + 1), (twBasisPoly d q i).coeff k = 0 := fun i ↦
      coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_twBasisPoly_le d q (by omega)) (by omega))
    have htarget : T.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hT (by omega))
    simp only [hbasis, htarget, mul_zero, Finset.sum_const_zero]

end AJConjecture
