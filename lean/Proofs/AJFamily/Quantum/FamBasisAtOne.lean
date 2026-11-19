import Mathlib
import AJConjecture.QAlgMoebiusSubstMul
import AJFamily.Quantum.FamTransferPoly

/-!
# The family basis polynomials at `q = 1`

The stationary substitution of the family basis polynomials at `q = 1`, used for the symbol
identity of `famTransferOp m`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The stationary substitution of degree `0` fixes `1`. -/
theorem famMoebiusSubst_zero_one : moebiusSubst 0 (1 : ℤ[X][X]) = 1 := by
  simp [moebiusSubst]

/-- The stationary substitution commutes with powers of polynomials of bounded degree. -/
theorem famMoebiusSubst_pow_of_natDegree_le {d : ℕ} {p : ℤ[X][X]}
    (hp : p.natDegree ≤ d) (k : ℕ) : moebiusSubst (k * d) (p ^ k) = moebiusSubst d p ^ k := by
  induction k with
  | zero => rw [zero_mul, pow_zero, pow_zero, famMoebiusSubst_zero_one]
  | succ k ih =>
    rw [Nat.succ_mul, pow_succ, pow_succ, moebiusSubst_mul (natDegree_pow_le_of_le k hp) hp, ih]

/-- At `q = 1` the family basis polynomial is a product of two powers. -/
theorem famBasisPoly_one_eq_pow (m i : ℕ) :
    famBasisPoly m (1 : ℤ) i =
      (C (1 - X) * (C X - X)) ^ i * (C (X - 1) * (1 - C X * X)) ^ (2 * m + 3 - i) := by
  have hc : (Finset.Ico i (2 * m + 3)).card = 2 * m + 3 - i := Nat.card_Ico i (2 * m + 3)
  simp only [famBasisPoly, one_pow, C_1, one_mul, Finset.prod_const, Finset.card_range, hc]

/-- The stationary substitution of a polynomial of degree at most one in `J`. -/
theorem famMoebiusSubst_one_linear (a b : ℤ[X]) :
    moebiusSubst 1 (C a + C b * X) = C a * (C X + X) + C b * (C X * X + 1) := by
  simp [moebiusSubst, Finset.sum_range_succ]

/-- The stationary substitution of `(1 - x)(x - J)`. -/
theorem famMoebiusSubst_one_basisFactor_left :
    moebiusSubst 1 (C (1 - X) * (C X - X)) = -(C (X - 1) * C (X ^ 2 - 1)) := by
  have h : (C X - X : ℤ[X][X]) = C X + C (-1) * X := by
    rw [C_neg, C_1]
    ring
  rw [moebiusSubst_C_mul, h, famMoebiusSubst_one_linear]
  simp only [C_neg, C_1, C_sub, C_pow]
  ring

/-- The stationary substitution of `(x - 1)(1 - xJ)`. -/
theorem famMoebiusSubst_one_basisFactor_right :
    moebiusSubst 1 (C (X - 1) * (1 - C X * X)) = -(C (X - 1) * C (X ^ 2 - 1) * X) := by
  have h : (1 - C X * X : ℤ[X][X]) = C 1 + C (-X) * X := by
    rw [C_neg, C_1]
    ring
  rw [moebiusSubst_C_mul, h, famMoebiusSubst_one_linear]
  simp only [C_neg, C_1, C_sub, C_pow]
  ring

/-- The sign bookkeeping of the product of the two powers, for an odd total exponent. -/
private theorem famBasisAtOne_sign_identity {A : Type*} [CommRing A] (a L : A) (m : ℕ)
    {i j : ℕ} (h : i + j = 2 * m + 3) :
    (-a) ^ i * (-(a * L)) ^ j = -(a ^ (2 * m + 3) * L ^ j) := by
  have hodd : (-1 : A) ^ (2 * m + 3) = -1 := Odd.neg_one_pow ⟨m + 1, by ring⟩
  rw [← h] at hodd ⊢
  rw [neg_eq_neg_one_mul a, neg_eq_neg_one_mul (a * L), mul_pow, mul_pow, pow_add]
  linear_combination (a ^ i * (a * L) ^ j) * hodd

/-- At `q = 1`, the stationary substitution sends the `i`-th family basis polynomial to
`-(x - 1)^(2m+3) (x² - 1)^(2m+3) L^(2m+3-i)`. -/
theorem moebiusSubst_famBasisPoly_one (m : ℕ) {i : ℕ} (hi : i ≤ 2 * m + 3) :
    moebiusSubst (2 * m + 3) (famBasisPoly m (1 : ℤ) i) =
      -(C ((X - 1) ^ (2 * m + 3) * (X ^ 2 - 1) ^ (2 * m + 3)) * X ^ (2 * m + 3 - i)) := by
  have hl : (C (1 - X) * (C X - X) : ℤ[X][X]).natDegree ≤ 1 := by compute_degree
  have hr : (C (X - 1) * (1 - C X * X) : ℤ[X][X]).natDegree ≤ 1 := by compute_degree
  have h := moebiusSubst_mul (natDegree_pow_le_of_le i hl)
    (natDegree_pow_le_of_le (2 * m + 3 - i) hr)
  have hij : i + (2 * m + 3 - i) = 2 * m + 3 := by omega
  rw [show i * 1 + (2 * m + 3 - i) * 1 = 2 * m + 3 by omega,
    famMoebiusSubst_pow_of_natDegree_le hl, famMoebiusSubst_pow_of_natDegree_le hr,
    famMoebiusSubst_one_basisFactor_left, famMoebiusSubst_one_basisFactor_right] at h
  rw [famBasisPoly_one_eq_pow m i, h, famBasisAtOne_sign_identity _ _ m hij, C_mul, C_pow, C_pow,
    mul_pow]

end AJConjecture
