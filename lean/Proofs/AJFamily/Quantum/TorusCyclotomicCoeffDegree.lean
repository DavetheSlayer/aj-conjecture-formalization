import Mathlib
import AJFamily.Quantum.TorusOddColorDegree

/-!
# Degree of the cyclotomic coefficients

For `a ≥ 2`, `D_j` is nonzero of `t`-degree `-2j(j+1)`; the term `n = 0` of its sum dominates.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- A natural power of `q` is nonzero of degree `4k` in `t`. -/
private theorem intDegree_qParam_pow_torusCyclo (k : ℕ) :
    qParam ^ k ≠ 0 ∧ (qParam ^ k).intDegree = 4 * (k : ℤ) :=
  ⟨pow_ne_zero k qParam_ne_zero, by rw [← zpow_natCast, intDegree_qParam_zpow]⟩

/-- `1 - q^k`, `k ≥ 1`, is nonzero of degree `4k` in `t`. -/
private theorem intDegree_one_sub_qParam_pow_torusCyclo {k : ℕ} (hk : 1 ≤ k) :
    1 - qParam ^ k ≠ 0 ∧ (1 - qParam ^ k).intDegree = 4 * (k : ℤ) := by
  rw [sub_eq_neg_add]
  refine intDegree_add_eq_of_lt
    ⟨neg_ne_zero.mpr (intDegree_qParam_pow_torusCyclo k).1, ?_⟩ (Or.inr ?_)
  · rw [RatFunc.intDegree_neg, (intDegree_qParam_pow_torusCyclo k).2]
  · rw [RatFunc.intDegree_one]
    omega

/-- The `q`-Pochhammer symbol `(q; q)_k` is nonzero of degree `2k(k+1)` in `t`. -/
private theorem intDegree_qPochhammer_qParam_torusCyclo (k : ℕ) :
    qPochhammer qParam k ≠ 0 ∧
      (qPochhammer qParam k).intDegree = 2 * (k : ℤ) * ((k : ℤ) + 1) := by
  induction k with
  | zero =>
    rw [qPochhammer, Finset.prod_range_zero]
    exact ⟨one_ne_zero, by rw [RatFunc.intDegree_one]; simp⟩
  | succ k ih =>
    have h1 := intDegree_one_sub_qParam_pow_torusCyclo (k := k + 1) (by omega)
    rw [pow_succ'] at h1
    have h2 := intDegree_mul_eq ih h1
    rw [qPochhammer, Finset.prod_range_succ]
    refine ⟨h2.1, h2.2.trans ?_⟩
    push_cast
    ring

/-- A power of `-1` is nonzero of degree `0`. -/
private theorem intDegree_neg_one_pow_torusCyclo (n : ℕ) :
    (-1 : RatFunc ℚ) ^ n ≠ 0 ∧ ((-1 : RatFunc ℚ) ^ n).intDegree = 0 := by
  refine ⟨pow_ne_zero n (neg_ne_zero.mpr one_ne_zero), ?_⟩
  rcases neg_one_pow_eq_or (RatFunc ℚ) n with h | h
  · rw [h, RatFunc.intDegree_one]
  · rw [h, RatFunc.intDegree_neg, RatFunc.intDegree_one]

/-- The `n`-th term of the sum defining `D_j` is nonzero of degree
`-2n² + (6 - 4a)n - 4j² - 8j - 4` in `t`. -/
private theorem intDegree_torusCyclotomicCoeff_term {a : ℕ} (ha : 2 ≤ a) {j n : ℕ}
    (hn : n ≤ j) :
    (-1) ^ n * qParam ^ (n * (n + 1) / 2) * torusOddColor a n /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1)) ≠ 0 ∧
      ((-1) ^ n * qParam ^ (n * (n + 1) / 2) * torusOddColor a n /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1))).intDegree =
        -2 * (n : ℤ) ^ 2 + (6 - 4 * (a : ℤ)) * n - 4 * (j : ℤ) ^ 2 - 8 * j - 4 := by
  have h := intDegree_div_eq
    (intDegree_mul_eq
      (intDegree_mul_eq (intDegree_neg_one_pow_torusCyclo n)
        (intDegree_qParam_pow_torusCyclo (n * (n + 1) / 2))) (intDegree_torusOddColor a ha n))
    (intDegree_mul_eq (intDegree_qPochhammer_qParam_torusCyclo (j - n))
      (intDegree_qPochhammer_qParam_torusCyclo (j + n + 1)))
  refine ⟨h.1, h.2.trans ?_⟩
  have h2 : ((n * (n + 1) / 2 : ℕ) : ℤ) * 2 = (n : ℤ) * ((n : ℤ) + 1) := by
    exact_mod_cast Nat.div_two_mul_two_of_even (Nat.even_mul_succ_self n)
  rw [Nat.cast_sub hn, Nat.cast_add, Nat.cast_add, Nat.cast_one]
  linear_combination 2 * h2

/-- The cyclotomic coefficient `D_j` of `T(2, a)`, `a ≥ 2`, is nonzero of degree `-2j(j+1)` in
`t`. -/
theorem intDegree_torusCyclotomicCoeff (a : ℕ) (ha : 2 ≤ a) (j : ℕ) :
    torusCyclotomicCoeff a j ≠ 0 ∧
      (torusCyclotomicCoeff a j).intDegree = -2 * (j : ℤ) * ((j : ℤ) + 1) := by
  have hsum : ∑ n ∈ Finset.range (j + 1), (-1) ^ n * qParam ^ (n * (n + 1) / 2) *
        torusOddColor a n / (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1)) ≠ 0 ∧
      (∑ n ∈ Finset.range (j + 1), (-1) ^ n * qParam ^ (n * (n + 1) / 2) *
        torusOddColor a n /
          (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1))).intDegree =
        -4 * (j : ℤ) ^ 2 - 8 * j - 4 := by
    refine intDegree_sum_eq_of_lt (a := 0) (Finset.mem_range.mpr (by omega))
      ⟨(intDegree_torusCyclotomicCoeff_term ha (Nat.zero_le j)).1, ?_⟩
      fun n hn hn0 ↦ Or.inr ?_
    · rw [(intDegree_torusCyclotomicCoeff_term ha (Nat.zero_le j)).2]
      push_cast
      ring
    · rw [(intDegree_torusCyclotomicCoeff_term ha
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))).2]
      have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have ha2 : (2 : ℤ) ≤ a := by exact_mod_cast ha
      nlinarith
  have h1 := intDegree_one_sub_qParam_pow_torusCyclo (k := 1) le_rfl
  rw [pow_one] at h1
  have h := intDegree_mul_eq (intDegree_mul_eq
    (intDegree_mul_eq (intDegree_qParam_pow_torusCyclo j) h1)
    (intDegree_qPochhammer_qParam_torusCyclo j)) hsum
  refine ⟨h.1, h.2.trans ?_⟩
  push_cast
  ring

end AJConjecture
