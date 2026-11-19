import Mathlib
import AJConjecture.ClaspAlgScalars
import AJFamily.Quantum.TorusFormula

/-!
# The unreduced formula as a sum of odd colours

`claspAlg_quantumInt_mul_torusReducedFormula`: `[N] F_N` for `T(2, a)` is the sum of the odd colours
`u_n`, `n < N`, weighted by the clasp coefficients.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The cyclotomic coefficient of `T(2, a)` is the sum of its odd colours against the
bilateral kernel at the natural indices `0 ≤ n ≤ j`. -/
private theorem torusCyclotomicCoeff_eq_sum_range_kernel (a j : ℕ) :
    torusCyclotomicCoeff a j =
      ∑ n ∈ Finset.range (j + 1), cycloBilateralKernel j n * torusOddColor a n := by
  rw [torusCyclotomicCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn' : n ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hE : (n : ℤ) * ((n : ℤ) + 1) / 2 = ((n * (n + 1) / 2 : ℕ) : ℤ) := by norm_cast
  rw [cycloBilateralKernel, ite_eq_left (by omega),
    show ((j : ℤ) - (n : ℤ)).toNat = j - n by omega,
    show ((j : ℤ) + (n : ℤ) + 1).toNat = j + n + 1 by omega, hE, zpow_natCast, zpow_natCast]
  ring

/-- The unreduced formula of `T(2, a)` is the sum of its odd colours weighted by the clasp
coefficients. -/
theorem claspAlg_quantumInt_mul_torusReducedFormula (a N : ℕ) :
    quantumInt N * torusReducedFormula a N =
      ∑ n ∈ Finset.range N, claspAlgCoeff N n * torusOddColor a n := by
  have hswap : ∑ j ∈ Finset.range N, ∑ n ∈ Finset.range (j + 1),
      cyclotomicKernel j N * (cycloBilateralKernel j n * torusOddColor a n) =
        ∑ n ∈ Finset.range N, ∑ j ∈ Finset.Ico n N,
          cyclotomicKernel j N * (cycloBilateralKernel j n * torusOddColor a n) := by
    simp only [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_Ico_comm 0 N _).symm
  calc quantumInt N * torusReducedFormula a N
      = quantumInt N * ∑ j ∈ Finset.range N, ∑ n ∈ Finset.range (j + 1),
          cyclotomicKernel j N * (cycloBilateralKernel j n * torusOddColor a n) := by
        rw [torusReducedFormula]
        congr 1
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [torusCyclotomicCoeff_eq_sum_range_kernel, Finset.mul_sum]
    _ = quantumInt N * ∑ n ∈ Finset.range N, ∑ j ∈ Finset.Ico n N,
          cyclotomicKernel j N * (cycloBilateralKernel j n * torusOddColor a n) := by
        rw [hswap]
    _ = ∑ n ∈ Finset.range N, claspAlgCoeff N n * torusOddColor a n := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        rw [claspAlgCoeff, mul_assoc, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        ring

end AJConjecture
