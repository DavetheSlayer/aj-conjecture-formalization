import Mathlib
import AJConjecture.FieldActionBridge
import AJConjecture.SkeinChebyshevRecursion
import AJConjecture.SkeinKnotTraceJwStep
import AJConjecture.SkeinScalars

/-!
# Chebyshev cabling is the insertion of the Jones–Wenzl projector

`⟨K(S_k)⟩ = Tr_{K,k}(f_k)` (Lickorish, Ch. 13–14: the closure of `f_k` in the annulus is `S_k(z)`).
With `a_{i,j} = Tr_{K,i+j}(f_j ⊗ 1_i)` and `b_i = ⟨K^{(i)}⟩`, the recursion
`a_{i,j+2} = a_{i+1,j+1} - a_{i,j}` (`AJConjecture.knotTrace_jwAt_succ_succ`), `a_{i,0} = b_i` and
`a_{i,1} = b_{i+1}` give `a_{i,k} = ∑_j (-1)^j (k-j choose j) b_{i+k-2j}`
(`AJConjecture.chebyshev_recursion_solution`), and `b_i` is the image of the bracket of the
`i`-cable (`AJConjecture.knotTrace_one`). The second
statement rewrites the coloured Jones polynomial: the prefactor of
`AJConjecture.coloredJonesPos` is `(-1)^k θ_k^(-writhe)`.
-/

open LaurentPolynomial

namespace AJConjecture

/-- The knot trace of `f_j` on the first `j` of `n` strands, as a function of two numbers. -/
private noncomputable def jwKnotTraceChebProj (K : BraidKnot) (n j : ℕ) : RatFunc ℚ :=
  knotTrace K n (jwAt n 0 j)

/-- The sign of the framing correction. -/
private theorem neg_one_pow_zpow_chebProj (k : ℕ) (w : ℤ) :
    ((-1 : RatFunc ℚ) ^ k) ^ (-w) = (-1) ^ (k * w.natAbs) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg w
  · rw [zpow_neg, zpow_natCast, Int.natAbs_natCast, ← pow_mul, ← inv_pow, inv_neg_one]
  · rw [neg_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, ← pow_mul]

/-- The bracket of the Chebyshev cable is the knot trace of the Jones–Wenzl projector. -/
theorem laurentToField_chebyshevBracket (K : BraidKnot) (k : ℕ) :
    laurentToField (chebyshevBracket K.strands K.word k) = knotTrace K k (jwAt k 0 k) := by
  have key := chebyshev_recursion_solution (fun i j ↦ jwKnotTraceChebProj K (i + j) j)
    (fun i ↦ knotTrace K i 1) (fun i ↦ rfl) (fun i ↦ rfl) (fun i j ↦ ?_) 0 k
  · rw [Nat.zero_add] at key
    rw [← jwKnotTraceChebProj, key, chebyshevBracket, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_zsmul, Nat.zero_add, knotTrace_one]
  · have h := knotTrace_jwAt_succ_succ K (i + j) j (Nat.le_add_left j i)
    have e : i + 1 + (j + 1) = i + j + 2 := by omega
    simp only [e]
    exact h

/-- The coloured Jones polynomial at the colour `k + 1` is the framing-corrected knot trace of
`f_k`. -/
theorem laurentToField_coloredJonesPos (K : BraidKnot) (k : ℕ) :
    laurentToField (coloredJonesPos K k) =
      (-1) ^ k * kinkScalar k ^ (-(writhe K.word)) * knotTrace K k (jwAt k 0 k) := by
  rw [coloredJonesPos, map_zsmul, map_mul, laurentToField_chebyshevBracket,
    laurentToField_T, kinkScalar, mul_zpow, neg_one_pow_zpow_chebProj, ← zpow_mul,
    zsmul_eq_mul, mul_add, mul_one, pow_add]
  have e : -writhe K.word * (((k : ℤ) + 1) ^ 2 - 1) = (k : ℤ) * ((k : ℤ) + 2) * -writhe K.word := by
    ring
  rw [e]
  push_cast
  ring

end AJConjecture
