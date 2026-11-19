import Mathlib
import AJConjecture.ClaspAlgClaspEigenCoeff
import AJConjecture.QAlgCycloBilateralKernel
import AJHandoff.TorusQuantum.PairQFormula

/-!
# Basic identities of the closed formula of an input sequence

For an arbitrary input `u`: the unreduced formula is `[n] F_|n|`; `[N] F_N` is the sum of the
inputs `u_n`, `n < N`, against the clasp coefficients; and the channel sum of the clasp
eigenvalues against the inputs, with its framing factor, is the formula at the colour `c + 1`.
These are the identities `torusWhiteheadFormula_eq_quantumInt_mul`,
`claspAlg_quantumInt_mul_torusReducedFormula` and `claspAlg_sum_claspEigen_mul_torusOddColor`
of the library with `torusOddColor a` replaced by `u`; their proofs never use the form of `u`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The even extension of the reduced formula is even. -/
theorem pairQReducedFormulaEven_neg (u : ℕ → RatFunc ℚ) (n : ℤ) :
    pairQReducedFormulaEven u (-n) = pairQReducedFormulaEven u n := by
  rw [pairQReducedFormulaEven, pairQReducedFormulaEven, Int.natAbs_neg]

/-- `pairQFormula u n = [n] F_|n|` at every integer. -/
theorem pairQFormula_eq_quantumInt_mul (u : ℕ → RatFunc ℚ) (n : ℤ) :
    pairQFormula u n = quantumInt n * pairQReducedFormulaEven u n := by
  have hneg : quantumInt (-n) = -quantumInt n := by
    simp only [quantumInt, mul_neg, neg_neg]
    ring
  rcases lt_trichotomy 0 n with hn | hn | hn
  · have h1 : n.toNat = n.natAbs := by omega
    rw [pairQFormula, ite_eq_left hn, pairQReducedFormulaEven, h1]
  · subst hn
    have h0 : quantumInt 0 = 0 := by simp [quantumInt]
    rw [pairQFormula, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _), h0, zero_mul]
  · have h1 : (-n).toNat = n.natAbs := by omega
    rw [pairQFormula, ite_eq_right (by omega), ite_eq_left hn, pairQReducedFormulaEven, h1, hneg]
    ring

/-- The cyclotomic coefficient of `u` is the sum of the inputs against the bilateral kernel at
the natural indices `0 ≤ n ≤ j`. -/
private theorem pairQCycloCoeff_eq_sum_range_kernel (u : ℕ → RatFunc ℚ) (j : ℕ) :
    pairQCycloCoeff u j =
      ∑ n ∈ Finset.range (j + 1), cycloBilateralKernel j n * u n := by
  rw [pairQCycloCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn' : n ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hE : (n : ℤ) * ((n : ℤ) + 1) / 2 = ((n * (n + 1) / 2 : ℕ) : ℤ) := by norm_cast
  rw [cycloBilateralKernel, ite_eq_left (by omega),
    show ((j : ℤ) - (n : ℤ)).toNat = j - n by omega,
    show ((j : ℤ) + (n : ℤ) + 1).toNat = j + n + 1 by omega, hE, zpow_natCast, zpow_natCast]
  ring

/-- `[N] F_N` is the sum of the inputs `u_n`, `n < N`, weighted by the clasp coefficients. -/
theorem pairQ_quantumInt_mul_reducedFormula (u : ℕ → RatFunc ℚ) (N : ℕ) :
    quantumInt N * pairQReducedFormula u N =
      ∑ n ∈ Finset.range N, claspAlgCoeff N n * u n := by
  have hswap : ∑ j ∈ Finset.range N, ∑ n ∈ Finset.range (j + 1),
      cyclotomicKernel j N * (cycloBilateralKernel j n * u n) =
        ∑ n ∈ Finset.range N, ∑ j ∈ Finset.Ico n N,
          cyclotomicKernel j N * (cycloBilateralKernel j n * u n) := by
    simp only [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_Ico_comm 0 N _).symm
  calc quantumInt N * pairQReducedFormula u N
      = quantumInt N * ∑ j ∈ Finset.range N, ∑ n ∈ Finset.range (j + 1),
          cyclotomicKernel j N * (cycloBilateralKernel j n * u n) := by
        rw [pairQReducedFormula]
        congr 1
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [pairQCycloCoeff_eq_sum_range_kernel, Finset.mul_sum]
    _ = quantumInt N * ∑ n ∈ Finset.range N, ∑ j ∈ Finset.Ico n N,
          cyclotomicKernel j N * (cycloBilateralKernel j n * u n) := by
        rw [hswap]
    _ = ∑ n ∈ Finset.range N, claspAlgCoeff N n * u n := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        rw [claspAlgCoeff, mul_assoc, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        ring

/-- The channel sum of the clasp eigenvalues against the inputs, with the framing factor
`(-1)^c t^(2c(c+2))`, is the unreduced formula at the colour `c + 1`. -/
theorem pairQ_sum_claspEigen_mul (u : ℕ → RatFunc ℚ) (c : ℕ) :
    (-1) ^ c * (RatFunc.X : RatFunc ℚ) ^ (2 * (c : ℤ) * ((c : ℤ) + 2)) *
        ∑ n ∈ Finset.range (c + 1), claspAlgClaspEigen c n * u n =
      pairQFormula u ((c : ℤ) + 1) := by
  have hpos : (0 : ℤ) < (c : ℤ) + 1 := by omega
  have htoNat : ((c : ℤ) + 1).toNat = c + 1 := by omega
  have hcast : (((c + 1 : ℕ) : ℤ)) = (c : ℤ) + 1 := by push_cast; ring
  rw [pairQFormula, ite_eq_left hpos, htoNat, ← hcast,
    pairQ_quantumInt_mul_reducedFormula, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [← claspAlgClaspEigen_eq_claspAlgCoeff c n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]
  ring

end AJConjecture
