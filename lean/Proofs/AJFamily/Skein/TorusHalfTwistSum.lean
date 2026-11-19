import Mathlib
import AJConjecture.ClaspAlgScalars
import AJFamily.Quantum.TorusFormula
import AJFamily.Skein.TorusThetaSum

/-!
# The half-twist sum of `T(2, 2k+1)`

`claspAlg_sum_halfTwistEigen_pow_torus`: the sum over `j ≤ 2n` of `λ_{2n,j}^(2k+1) [2j+1]`, where
`λ_{2n,j}` are the half-twist eigenvalues at colour `2n`, is
`X^(4(2k+1) n(n+1)) · torusOddColor (2k+1) n`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

theorem claspAlg_sum_halfTwistEigen_pow_torus (k n : ℕ) :
    ∑ j ∈ Finset.range (2 * n + 1),
        claspAlgHalfTwistEigen (2 * n) j ^ (2 * k + 1) * quantumInt (2 * (j : ℤ) + 1) =
      (RatFunc.X : RatFunc ℚ) ^ (4 * (2 * (k : ℤ) + 1) * (n : ℤ) * ((n : ℤ) + 1)) *
        torusOddColor (2 * k + 1) n := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hlam : ∀ j : ℕ, claspAlgHalfTwistEigen (2 * n) j ^ (2 * k + 1) =
      RatFunc.X ^ (-(4 * (2 * (k : ℤ) + 1) * (n : ℤ) * ((n : ℤ) + 1))) *
        ((-1) ^ j * RatFunc.X ^ (2 * ((2 * k + 1 : ℕ) : ℤ) * (j : ℤ) * ((j : ℤ) + 1))) := by
    intro j
    have h1 : ((-1 : RatFunc ℚ) ^ (2 * n + j)) ^ (2 * k + 1) = (-1) ^ j := by
      rw [← pow_mul, show (2 * n + j) * (2 * k + 1) = 2 * (n * (2 * k + 1) + j * k) + j by ring,
        pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
    have h2 : ((RatFunc.X : RatFunc ℚ) ^
        (2 * (j : ℤ) * ((j : ℤ) + 1) - ((2 * n : ℕ) : ℤ) * (((2 * n : ℕ) : ℤ) + 2))) ^
          (2 * k + 1) =
        RatFunc.X ^ (-(4 * (2 * (k : ℤ) + 1) * (n : ℤ) * ((n : ℤ) + 1))) *
          RatFunc.X ^ (2 * ((2 * k + 1 : ℕ) : ℤ) * (j : ℤ) * ((j : ℤ) + 1)) := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hX]
      congr 1
      push_cast
      ring
    rw [claspAlgHalfTwistEigen, mul_pow, h1, h2]
    ring
  have hq : qParam ^ (-(2 * ((2 * k + 1 : ℕ) : ℤ) * (n : ℤ) * ((n : ℤ) + 1))) =
      (RatFunc.X : RatFunc ℚ) ^ (-(8 * (2 * (k : ℤ) + 1) * (n : ℤ) * ((n : ℤ) + 1))) := by
    rw [claspAlg_qParam_zpow]
    congr 1
    push_cast
    ring
  have hXX : (RatFunc.X : RatFunc ℚ) ^ (4 * (2 * (k : ℤ) + 1) * (n : ℤ) * ((n : ℤ) + 1)) *
      RatFunc.X ^ (-(8 * (2 * (k : ℤ) + 1) * (n : ℤ) * ((n : ℤ) + 1))) =
        RatFunc.X ^ (-(4 * (2 * (k : ℤ) + 1) * (n : ℤ) * ((n : ℤ) + 1))) := by
    rw [← zpow_add₀ hX]
    congr 1
    ring
  rw [torusOddColor, hq, ← mul_assoc, hXX, ← claspAlg_alternating_theta_sum_torus,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hlam]
  ring

end AJConjecture
