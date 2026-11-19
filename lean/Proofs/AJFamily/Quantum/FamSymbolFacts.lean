import Mathlib
import AJConjecture.QAlgToComparisonUnit
import AJFamily.Quantum.FamDetAtOne
import AJFamily.Quantum.FamSymbol
import AJFamily.Quantum.TwistPolyBasic

/-!
# Consequences of the symbol identity

The symbol of `famTransferOp m` is nonzero of degree `2m + 3` in `L`, so `famTransferOp m` has
order `2m + 3`, and `E` divides the symbol in the comparison ring.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The extra factor has degree `2` in `L`. -/
theorem natDegree_extraFactor : extraFactor.natDegree = 2 := by
  have h2 : extraFactor.coeff 2 = 1 := by
    simp only [extraFactor, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    simp
  have hle : extraFactor.natDegree ≤ 2 := by
    unfold extraFactor
    compute_degree
  exact le_antisymm hle (le_natDegree_of_ne_zero (by rw [h2]; exact one_ne_zero))

/-- `L - 1` has degree `1` in `L`. -/
theorem natDegree_X_sub_one : (X - 1 : ℤ[X][X]).natDegree = 1 := by
  rw [← C_1, natDegree_X_sub_C]

/-- The product `(L - 1) E B_m` has degree `2m + 3` in `L`. -/
private theorem natDegree_symbolProduct_famSymbolFacts (m : ℕ) :
    ((X - 1) * extraFactor * twistPoly m : ℤ[X][X]).natDegree = 2 * m + 3 := by
  have h1 : (X - 1 : ℤ[X][X]) ≠ 0 :=
    ne_zero_of_natDegree_gt (n := 0) (by rw [natDegree_X_sub_one]; norm_num)
  have h2 : extraFactor ≠ 0 :=
    ne_zero_of_natDegree_gt (n := 0) (by rw [natDegree_extraFactor]; norm_num)
  have h3 : twistPoly m ≠ 0 := by
    intro h
    have h' := leadingCoeff_twistPoly m
    rw [h, leadingCoeff_zero] at h'
    exact pow_ne_zero (4 * m) X_ne_zero h'.symm
  rw [natDegree_mul (mul_ne_zero h1 h2) h3, natDegree_mul h1 h2,
    natDegree_X_sub_one, natDegree_extraFactor,
    natDegree_twistPoly]
  ring

/-- The polynomial in `M` on the left of the family symbol identity is not zero. -/
private theorem symbolLeft_ne_zero_famSymbolFacts (m : ℕ) :
    ((X ^ 2 - 1) ^ (2 * m + 3) * (X ^ 4 - 1) ^ (2 * m + 3) : ℤ[X]) ≠ 0 := by
  intro h
  have h0 := congrArg (Polynomial.eval 0) h
  simp at h0

/-- The polynomial in `M` on the right of the family symbol identity is not zero. -/
private theorem symbolRight_ne_zero_famSymbolFacts (m : ℕ) :
    ((famDet m (1 : ℤ)).comp (X ^ 2) * ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1)) : ℤ[X]) ≠ 0 := by
  intro h
  have h0 := famDet_one_eval_ne_zero m (x₀ := 0) (by norm_num) (by norm_num)
  have h1 := congrArg (fun p : ℤ[X] ↦ (p.map (Int.castRingHom ℂ)).eval 0) h
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_one, Polynomial.map_comp, map_X, eval_mul, eval_pow, eval_sub, eval_add,
    eval_X, eval_one, eval_comp, Polynomial.map_zero, eval_zero] at h1
  rw [zero_pow two_ne_zero] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact h0 h2
  · norm_num at h2

/-- The specialisation of the family transfer operator is not zero. -/
theorem specialize_famTransferOp_ne_zero (m : ℕ) (hm : 1 ≤ m) :
    specialize (famTransferOp m) ≠ 0 := by
  intro h
  have h1 := specialize_famTransferOp_mul_eq m hm
  rw [h, mul_zero] at h1
  have h2 : ((X - 1) * extraFactor * twistPoly m : ℤ[X][X]) ≠ 0 :=
    ne_zero_of_natDegree_gt (n := 0) (by rw [natDegree_symbolProduct_famSymbolFacts]; omega)
  exact mul_ne_zero (C_ne_zero.mpr (symbolRight_ne_zero_famSymbolFacts m)) h2 h1.symm

/-- The specialisation of the family transfer operator has degree `2m + 3` in `L`. -/
theorem natDegree_specialize_famTransferOp (m : ℕ) (hm : 1 ≤ m) :
    (specialize (famTransferOp m)).natDegree = 2 * m + 3 := by
  have h := congrArg natDegree (specialize_famTransferOp_mul_eq m hm)
  rwa [natDegree_C_mul (symbolLeft_ne_zero_famSymbolFacts m),
    natDegree_C_mul (symbolRight_ne_zero_famSymbolFacts m),
    natDegree_symbolProduct_famSymbolFacts] at h

/-- The family transfer operator has degree `2m + 3` in `L`. -/
theorem natDegree_famTransferOp (m : ℕ) (hm : 1 ≤ m) : (famTransferOp m).natDegree = 2 * m + 3 := by
  refine le_antisymm ?_ ?_
  · unfold famTransferOp
    refine natDegree_sum_le_of_forall_le _ _ fun k _ ↦ ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · have h : (specialize (famTransferOp m)).natDegree ≤ (famTransferOp m).natDegree := by
      rw [specialize, coe_mapRingHom]
      exact natDegree_map_le
    rwa [natDegree_specialize_famTransferOp m hm] at h

/-- The extra factor divides the symbol of the family transfer operator in the comparison
ring. -/
theorem extraFactor_dvd_specialize_famTransferOp (m : ℕ) (hm : 1 ≤ m) :
    toComparison extraFactor ∣ toComparison (specialize (famTransferOp m)) := by
  refine (isUnit_toComparison_coeff_of_ne_zero
    (symbolLeft_ne_zero_famSymbolFacts m)).dvd_mul_left.mp ?_
  rw [← map_mul, specialize_famTransferOp_mul_eq m hm]
  exact map_dvd toComparison (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _)

end AJConjecture
