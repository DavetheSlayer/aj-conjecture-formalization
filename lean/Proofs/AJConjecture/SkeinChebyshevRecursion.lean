import Mathlib

/-!
# The solution of the Chebyshev recursion

A double sequence with `a_{i,0} = b_i`, `a_{i,1} = b_{i+1}` and
`a_{i,j+2} = a_{i+1,j+1} - a_{i,j}` is
`a_{i,k} = ∑_j (-1)^j (k-j choose j) b_{i+k-2j}`: these are the coefficients of the Chebyshev
polynomial `S_k(z) = ∑_j (-1)^j (k-j choose j) z^(k-2j)`, with `S_{k+2} = z S_{k+1} - S_k`. Strong
induction on `k`, with Pascal's rule
`(k+2-j choose j) = (k+1-j choose j) + (k+1-j choose j-1)` and a shift of the index in the
second sum.
-/

namespace AJConjecture

/-- The Chebyshev sum can be extended to a longer range: the extra binomials vanish. -/
private theorem chebyshevSum_range_extend {R : Type*} [CommRing R] (b : ℕ → R) (i k N : ℕ)
    (hN : k / 2 + 1 ≤ N) :
    ∑ j ∈ Finset.range (k / 2 + 1),
        ((-1 : ℤ) ^ j * ((k - j).choose j : ℤ)) • b (i + (k - 2 * j)) =
      ∑ j ∈ Finset.range N, ((-1 : ℤ) ^ j * ((k - j).choose j : ℤ)) • b (i + (k - 2 * j)) := by
  apply Finset.sum_subset
  · intro x
    simp only [Finset.mem_range]
    omega
  · intro j hj hj'
    simp only [Finset.mem_range] at hj hj'
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- One term of the Chebyshev recursion: Pascal's rule. -/
private theorem chebyshevSum_term_pascal {R : Type*} [CommRing R] (b : ℕ → R) (i k j : ℕ) :
    ((-1 : ℤ) ^ (j + 1) * ((k + 2 - (j + 1)).choose (j + 1) : ℤ)) •
        b (i + (k + 2 - 2 * (j + 1))) =
      ((-1 : ℤ) ^ (j + 1) * ((k + 1 - (j + 1)).choose (j + 1) : ℤ)) •
          b (i + 1 + (k + 1 - 2 * (j + 1))) -
        ((-1 : ℤ) ^ j * ((k - j).choose j : ℤ)) • b (i + (k - 2 * j)) := by
  have e1 : k + 2 - 2 * (j + 1) = k - 2 * j := by omega
  have e2 : k + 1 - (j + 1) = k - j := by omega
  rw [e1, e2]
  by_cases hjk : 2 * j + 1 ≤ k
  · have e3 : i + 1 + (k + 1 - 2 * (j + 1)) = i + (k - 2 * j) := by omega
    have e4 : k + 2 - (j + 1) = (k - j) + 1 := by omega
    rw [e3, e4, ← sub_smul, Nat.choose_succ_succ]
    congr 1
    push_cast
    ring
  · have z1 : (k - j).choose (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [z1]
    by_cases hj : j ≤ k
    · have e4 : k + 2 - (j + 1) = (k - j) + 1 := by omega
      rw [e4, Nat.choose_succ_succ, z1]
      simp only [Nat.cast_zero, mul_zero, zero_smul, zero_sub, add_zero, ← neg_smul]
      congr 1
      ring
    · have z2 : (k + 2 - (j + 1)).choose (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have z3 : (k - j).choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [z2, z3]
      simp

/-- The Chebyshev recursion determines the sequence. -/
theorem chebyshev_recursion_solution {R : Type*} [CommRing R] (a : ℕ → ℕ → R) (b : ℕ → R)
    (h0 : ∀ i, a i 0 = b i) (h1 : ∀ i, a i 1 = b (i + 1))
    (h2 : ∀ i j, a i (j + 2) = a (i + 1) (j + 1) - a i j) (i k : ℕ) :
    a i k = ∑ j ∈ Finset.range (k / 2 + 1),
      ((-1 : ℤ) ^ j * ((k - j).choose j : ℤ)) • b (i + (k - 2 * j)) := by
  induction k using Nat.twoStepInduction generalizing i with
  | zero => simp [h0]
  | one => simp [h1]
  | more k ih0 ih1 =>
    rw [h2, ih1 (i + 1), ih0 i, chebyshevSum_range_extend b i (k + 2) (k + 3) (by omega),
      chebyshevSum_range_extend b (i + 1) (k + 1) (k + 3) (by omega),
      chebyshevSum_range_extend b i k (k + 2) (by omega),
      Finset.sum_range_succ' _ (k + 2), Finset.sum_range_succ' _ (k + 2), add_sub_right_comm,
      ← Finset.sum_sub_distrib]
    congr 1
    · exact (Finset.sum_congr rfl fun j _ ↦ chebyshevSum_term_pascal b i k j).symm
    · simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_smul,
        mul_zero]
      congr 1
      omega

end AJConjecture
