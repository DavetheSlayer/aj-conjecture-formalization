import Mathlib
import AJConjecture.ColoredJones
import AJConjecture.Unknot

/-!
# The coloured Jones function of the unknot

For the unknot the coloured Jones function is the quantum integer
`[n] = (t^(2n) - t^(-2n)) / (t² - t⁻²)`, for every integer `n`; the statement is written without
division.
-/

open LaurentPolynomial

namespace AJConjecture

/-- The value at `x` of the Chebyshev polynomial `S_k(z) = ∑_j (-1)^j (k-j choose j) z^(k-2j)`. -/
private noncomputable def chebyshevSum {R : Type*} [CommRing R] (x : R) (k : ℕ) : R :=
  ∑ j ∈ Finset.range (k / 2 + 1), ((-1 : R) ^ j * ((k - j).choose j : R)) * x ^ (k - 2 * j)

/-- The Chebyshev sum may be taken over any longer range: the extra binomials vanish. -/
private theorem chebyshevSum_eq_sum_range {R : Type*} [CommRing R] (x : R) (k N : ℕ)
    (hN : k / 2 + 1 ≤ N) :
    chebyshevSum x k =
      ∑ j ∈ Finset.range N, ((-1 : R) ^ j * ((k - j).choose j : R)) * x ^ (k - 2 * j) := by
  refine Finset.sum_subset (Finset.range_mono hN) fun j _ hj ↦ ?_
  have hlt : k - j < j := by
    have hj' := Finset.mem_range.not.mp hj
    omega
  rw [Nat.choose_eq_zero_of_lt hlt]
  simp

/-- Pascal's rule on one term of the Chebyshev sum. -/
private theorem chebyshevSum_term_succ_succ {R : Type*} [CommRing R] (x : R) (k i : ℕ)
    (hi : 2 * i ≤ k) :
    ((-1 : R) ^ (i + 1) * ((k + 2 - (i + 1)).choose (i + 1) : R)) * x ^ (k + 2 - 2 * (i + 1)) =
      x * (((-1 : R) ^ (i + 1) * ((k + 1 - (i + 1)).choose (i + 1) : R)) *
        x ^ (k + 1 - 2 * (i + 1))) -
      ((-1 : R) ^ i * ((k - i).choose i : R)) * x ^ (k - 2 * i) := by
  have h1 : k + 2 - (i + 1) = k - i + 1 := by omega
  have h2 : k + 1 - (i + 1) = k - i := by omega
  have h3 : k + 2 - 2 * (i + 1) = k - 2 * i := by omega
  rw [h1, h2, h3, Nat.choose_succ_succ, Nat.cast_add]
  rcases hi.eq_or_lt with h | h
  · have hlt : k - i < i + 1 := by omega
    rw [Nat.choose_eq_zero_of_lt hlt]
    simp only [Nat.cast_zero, add_zero, mul_zero, zero_mul]
    ring
  · have h4 : k - 2 * i = k + 1 - 2 * (i + 1) + 1 := by omega
    rw [h4]
    ring

/-- The three-term recurrence `S_{k+2}(x) = x S_{k+1}(x) - S_k(x)`. -/
private theorem chebyshevSum_add_two {R : Type*} [CommRing R] (x : R) (k : ℕ) :
    chebyshevSum x (k + 2) = x * chebyshevSum x (k + 1) - chebyshevSum x k := by
  rw [chebyshevSum_eq_sum_range x (k + 2) (k / 2 + 1 + 1) (by omega),
    chebyshevSum_eq_sum_range x (k + 1) (k / 2 + 1 + 1) (by omega),
    chebyshevSum_eq_sum_range x k (k / 2 + 1) le_rfl,
    Finset.sum_range_succ' _ (k / 2 + 1), Finset.sum_range_succ' _ (k / 2 + 1), mul_add,
    Finset.mul_sum, add_sub_right_comm, ← Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i hi ↦ chebyshevSum_term_succ_succ x k i ?_
    have hi' := Finset.mem_range.mp hi
    omega
  · simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul,
      mul_zero]
    rw [← pow_succ']

/-- The closed form of the signed Chebyshev sum at `-t² - t⁻²`: it is a quantum integer. -/
private theorem chebyshevSum_quantumInteger (k : ℕ) :
    ((T 2 : ℤ[T;T⁻¹]) - T (-2)) * ((-1) ^ k * chebyshevSum (-T 2 - T (-2) : ℤ[T;T⁻¹]) k) =
      T (2 * ((k : ℤ) + 1)) - T (-(2 * ((k : ℤ) + 1))) := by
  have huv : (T 2 : ℤ[T;T⁻¹]) * T (-2) = 1 := by rw [← T_add]; simp
  induction k using Nat.twoStepInduction with
  | zero =>
    simp [chebyshevSum]
  | one =>
    have h4 : (T (2 * ((1 : ℕ) + 1 : ℤ)) : ℤ[T;T⁻¹]) = T 2 * T 2 := by rw [← T_add]; norm_num
    have h4' : (T (-(2 * ((1 : ℕ) + 1 : ℤ))) : ℤ[T;T⁻¹]) = T (-2) * T (-2) := by
      rw [← T_add]; norm_num
    rw [h4, h4']
    simp only [chebyshevSum]
    simp
    ring
  | more k h0 h1 =>
    have hA : (T (2 * (((k + 2 : ℕ) : ℤ) + 1)) : ℤ[T;T⁻¹]) =
        T 2 * T (2 * (((k + 1 : ℕ) : ℤ) + 1)) := by
      rw [← T_add]; exact congrArg T (by push_cast; ring)
    have hB : (T (-(2 * (((k + 2 : ℕ) : ℤ) + 1))) : ℤ[T;T⁻¹]) =
        T (-2) * T (-(2 * (((k + 1 : ℕ) : ℤ) + 1))) := by
      rw [← T_add]; exact congrArg T (by push_cast; ring)
    have hC : (T (2 * ((k : ℤ) + 1)) : ℤ[T;T⁻¹]) =
        T (-2) * T (2 * (((k + 1 : ℕ) : ℤ) + 1)) := by
      rw [← T_add]; exact congrArg T (by push_cast; ring)
    have hD : (T (-(2 * ((k : ℤ) + 1))) : ℤ[T;T⁻¹]) =
        T 2 * T (-(2 * (((k + 1 : ℕ) : ℤ) + 1))) := by
      rw [← T_add]; exact congrArg T (by push_cast; ring)
    rw [hC, hD] at h0
    rw [hA, hB, chebyshevSum_add_two]
    linear_combination (T 2 + T (-2)) * h1 - h0

/-- The bracket of the closure of the empty braid on `c` strands: `c` disjoint circles. -/
private theorem bracket_nil_eq_pow (c : ℕ) :
    bracket c [] = (-T 2 - T (-2) : ℤ[T;T⁻¹]) ^ c := by
  have hsum : (∑ b : Bool, if b then -T (-2) else -T 2 : ℤ[T;T⁻¹]) = -T 2 - T (-2) := by
    simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
    ring
  simp only [bracket, List.map_nil, List.prod_nil, mul_one, Matrix.trace_diagonal]
  rw [← hsum, ← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- The positive coloured Jones polynomial of the unknot is a signed Chebyshev sum. -/
private theorem coloredJonesPos_unknot_eq_chebyshevSum (k : ℕ) :
    coloredJonesPos unknot k = (-1) ^ k * chebyshevSum (-T 2 - T (-2) : ℤ[T;T⁻¹]) k := by
  have hw : writhe unknot.word = 0 := by simp [unknot, writhe]
  have hc : ∀ c : ℕ, cable c unknot.word = [] := fun c ↦ by simp [unknot, cable]
  have hs : unknot.strands = 1 := rfl
  simp only [coloredJonesPos, chebyshevBracket, hw, hc, hs, bracket_nil_eq_pow, chebyshevSum,
    neg_zero, zero_mul, T_zero, one_mul, Int.natAbs_zero, add_zero, mul_one, zsmul_eq_mul]
  push_cast
  rfl

/-- The quantum-integer formula at the positive colour `k + 1`. -/
private theorem coloredJonesPos_unknot_quantumInteger (k : ℕ) :
    ((T 2 : ℤ[T;T⁻¹]) - T (-2)) * coloredJonesPos unknot k =
      T (2 * ((k : ℤ) + 1)) - T (-(2 * ((k : ℤ) + 1))) := by
  rw [coloredJonesPos_unknot_eq_chebyshevSum, chebyshevSum_quantumInteger]

/-- The coloured Jones function of the unknot is `[n]`: `(t² - t⁻²) J(n) = t^(2n) - t^(-2n)`. -/
theorem coloredJones_unknot (n : ℤ) :
    ((T 2 : ℤ[T;T⁻¹]) - T (-2)) * coloredJones unknot n = T (2 * n) - T (-(2 * n)) := by
  rcases lt_trichotomy 0 n with hn | hn | hn
  · have hk : ((n.toNat - 1 : ℕ) : ℤ) + 1 = n := by omega
    simp only [coloredJones, hn, ↓reduceIte]
    rw [coloredJonesPos_unknot_quantumInteger, hk]
  · subst hn
    simp [coloredJones]
  · have hk : (((-n).toNat - 1 : ℕ) : ℤ) + 1 = -n := by omega
    simp only [coloredJones, not_lt.mpr hn.le, hn, ↓reduceIte]
    rw [mul_neg, coloredJonesPos_unknot_quantumInteger, hk]
    simp

end AJConjecture
