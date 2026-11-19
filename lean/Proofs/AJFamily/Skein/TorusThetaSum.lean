import Mathlib
import AJConjecture.ClaspAlgBasic

/-!
# A reindexed theta sum

`claspAlg_alternating_theta_sum_torus`: the alternating sum over `j ≤ 2n` of
`X^(2a j(j+1)) [2j+1]` is the sum over `|s| ≤ n` of `q^(a s(2s+1)) [4s+1]`, the sum in
`torusOddColor a n`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The alternating theta sum over `0 ≤ j ≤ 2n` with exponent `a` is the theta sum over
`-n ≤ s ≤ n`. -/
theorem claspAlg_alternating_theta_sum_torus (a n : ℕ) :
    ∑ j ∈ Finset.range (2 * n + 1),
        (-1 : RatFunc ℚ) ^ j * RatFunc.X ^ (2 * (a : ℤ) * (j : ℤ) * ((j : ℤ) + 1)) *
          quantumInt (2 * (j : ℤ) + 1) =
      ∑ s ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), qParam ^ ((a : ℤ) * s * (2 * s + 1)) * quantumInt (4 * s + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hIcc : Finset.Icc (-(((n + 1 : ℕ) : ℤ))) ((n + 1 : ℕ) : ℤ) =
        insert ((n : ℤ) + 1) (insert (-((n : ℤ) + 1)) (Finset.Icc (-(n : ℤ)) n)) := by
      ext s
      simp only [Finset.mem_insert, Finset.mem_Icc, Nat.cast_add, Nat.cast_one]
      omega
    have h1 : (n : ℤ) + 1 ∉ insert (-((n : ℤ) + 1)) (Finset.Icc (-(n : ℤ)) n) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have h2 : -((n : ℤ) + 1) ∉ Finset.Icc (-(n : ℤ)) n := by
      simp only [Finset.mem_Icc]
      omega
    have e1 : (-1 : RatFunc ℚ) ^ (2 * n + 1) = -1 := by
      rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
    have e2 : (-1 : RatFunc ℚ) ^ (2 * n + 1 + 1) = 1 := by
      rw [pow_succ, e1]
      ring
    have q1 : qParam ^ ((a : ℤ) * ((n : ℤ) + 1) * (2 * ((n : ℤ) + 1) + 1)) =
        RatFunc.X ^ (2 * (a : ℤ) * ((2 * n + 1 + 1 : ℕ) : ℤ) *
          (((2 * n + 1 + 1 : ℕ) : ℤ) + 1)) := by
      rw [claspAlg_qParam_zpow]
      congr 1
      push_cast
      ring
    have q2 : qParam ^ ((a : ℤ) * (-((n : ℤ) + 1)) * (2 * (-((n : ℤ) + 1)) + 1)) =
        RatFunc.X ^ (2 * (a : ℤ) * ((2 * n + 1 : ℕ) : ℤ) * (((2 * n + 1 : ℕ) : ℤ) + 1)) := by
      rw [claspAlg_qParam_zpow]
      congr 1
      push_cast
      ring
    have i1 : quantumInt (4 * ((n : ℤ) + 1) + 1) =
        quantumInt (2 * ((2 * n + 1 + 1 : ℕ) : ℤ) + 1) := by
      congr 1
      push_cast
      ring
    have i2 : quantumInt (4 * (-((n : ℤ) + 1)) + 1) =
        -quantumInt (2 * ((2 * n + 1 : ℕ) : ℤ) + 1) := by
      rw [← claspAlg_quantumInt_neg]
      congr 1
      push_cast
      ring
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, hIcc, Finset.sum_insert h1, Finset.sum_insert h2, e1, e2, q1, q2,
      i1, i2]
    ring

end AJConjecture
