import Mathlib
import AJConjecture.QAlgSymbolMoebiusExtra
import AJFamily.Quantum.FamBasisAtOne
import AJFamily.Quantum.FamSpecialize
import AJFamily.Quantum.FamTargetAtOne
import AJFamily.Quantum.FamTransferCramer
import AJFamily.Quantum.TwistPolyMoebius

/-!
# The symbol of the family transfer operator

`specialize_famTransferOp_mul_eq`: up to nonzero polynomials in `M`, the symbol of
`famTransferOp m` at `t = -1` is `(L - 1) · E · B_m`. It follows from the Cramer identity at
`q = 1` by the stationary substitution.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The stationary substitution of degree one of `1 - J`. -/
private theorem moebiusSubst_one_sub_X_famSymbol :
    moebiusSubst 1 (1 - X) = -(C (X - 1) * (X - 1)) := by
  rw [moebiusSubst_sub, moebiusSubst_one, show (1 : ℕ) = 0 + 1 from rfl, moebiusSubst_X]
  simp only [C_sub, C_1]
  ring

/-- `(1 - J)(ζ + 2x)` has degree at most three in `J`. -/
private theorem natDegree_one_sub_X_mul_symbolZeta_add_le :
    ((1 - X) * (symbolZeta + C (2 * X)) : ℤ[X][X]).natDegree ≤ 3 := by
  unfold symbolZeta
  compute_degree

/-- The stationary substitution of the family target polynomial at `q = 1`. -/
private theorem moebiusSubst_famTarget_one (m : ℕ) (hm : 1 ≤ m) :
    moebiusSubst (2 * m + 3) (famTarget m (1 : ℤ)) =
      -(C (X - 1) * (X - 1)) * moebiusSubst 2 (symbolZeta + C (2 * X)) *
        moebiusSubst (2 * m) (symbolTwist m) := by
  have hz : (symbolZeta + C (2 * X) : ℤ[X][X]).natDegree ≤ 2 := by
    unfold symbolZeta
    compute_degree
  have h1 : (1 - X : ℤ[X][X]).natDegree ≤ 1 := by compute_degree
  rw [famTarget_one_eq m hm, show 2 * m + 3 = 3 + 2 * m by ring,
    moebiusSubst_mul natDegree_one_sub_X_mul_symbolZeta_add_le (natDegree_symbolTwist_le m),
    show (3 : ℕ) = 1 + 2 from rfl, moebiusSubst_mul h1 hz, moebiusSubst_one_sub_X_famSymbol]

/-- The stationary substitution of the left-hand side of the family Cramer identity at
`q = 1`. -/
private theorem moebiusSubst_famCramerSum_one (m : ℕ) :
    moebiusSubst (2 * m + 3)
        (∑ i : Fin (2 * m + 4), C (famCoeff m (1 : ℤ) i) * famBasisPoly m (1 : ℤ) i) =
      -(C ((X - 1) ^ (2 * m + 3) * (X ^ 2 - 1) ^ (2 * m + 3)) *
        ∑ i : Fin (2 * m + 4), C (famCoeff m (1 : ℤ) i) * X ^ (2 * m + 3 - (i : ℕ))) := by
  rw [moebiusSubst_finsetSum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [moebiusSubst_C_mul, moebiusSubst_famBasisPoly_one m (by omega)]
  ring

/-- The specialisation of the family transfer operator, with the sum reversed. -/
private theorem sum_rev_famCoeff_one (m : ℕ) :
    ∑ i : Fin (2 * m + 4), C ((famCoeff m (1 : ℤ) i).comp (X ^ 2)) *
        (X : ℤ[X][X]) ^ (2 * m + 3 - (i : ℕ)) =
      specialize (famTransferOp m) := by
  rw [specialize_famTransferOp_eq_sum, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Fin.revPerm_apply, Fin.val_rev]
  congr 2
  omega

/-- The symbol at `t = -1` of the family transfer operator is `(L - 1) · E · B_m` up to
nonzero polynomials in `M`. -/
theorem specialize_famTransferOp_mul_eq (m : ℕ) (hm : 1 ≤ m) :
    C ((X ^ 2 - 1) ^ (2 * m + 3) * (X ^ 4 - 1) ^ (2 * m + 3)) * specialize (famTransferOp m) =
      C ((famDet m (1 : ℤ)).comp (X ^ 2) * ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1))) *
        ((X - 1) * extraFactor * twistPoly m) := by
  have h := congrArg (moebiusSubst (2 * m + 3)) (sum_famCoeff_mul_famBasisPoly m hm (1 : ℤ))
  rw [moebiusSubst_famCramerSum_one, moebiusSubst_C_mul, moebiusSubst_famTarget_one m hm] at h
  have h' := congrArg (Polynomial.map (Polynomial.compRingHom (X ^ 2 : ℤ[X]))) h
  have hc : ((X - 1 : ℤ[X]) ^ (2 * m + 3) * (X ^ 2 - 1) ^ (2 * m + 3)).comp (X ^ 2) =
      (X ^ 2 - 1) ^ (2 * m + 3) * (X ^ 4 - 1) ^ (2 * m + 3) := by
    simp only [mul_comp, pow_comp, sub_comp, X_comp, one_comp]
    rw [← pow_mul]
  simp only [Polynomial.map_neg, Polynomial.map_mul, Polynomial.map_sum, Polynomial.map_pow,
    Polynomial.map_sub, map_C, map_X, Polynomial.map_one, coe_compRingHom_apply,
    map_moebiusSubst_symbolZeta_add, map_moebiusSubst_symbolTwist, hc, sum_rev_famCoeff_one,
    sub_comp, X_comp, one_comp] at h'
  have hC : (C ((famDet m (1 : ℤ)).comp (X ^ 2) * ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1))) :
      ℤ[X][X]) = C ((famDet m (1 : ℤ)).comp (X ^ 2)) * (C ((X ^ 2 + 1) ^ 2) * C (X ^ 2 - 1)) := by
    rw [C_mul, C_mul]
  rw [hC]
  linear_combination (-1 : ℤ[X][X]) * h'

end AJConjecture
