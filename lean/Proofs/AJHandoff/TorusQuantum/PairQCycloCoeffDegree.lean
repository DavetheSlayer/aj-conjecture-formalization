import Mathlib
import AJFamily.Quantum.TorusOddColorDegree
import AJHandoff.TorusQuantum.PairQFormula

/-!
# The degree in `t` of the cyclotomic coefficients

If `u_0 = 1` and `u_n = 0` or `deg_t u_n ≤ 0` for `n ≥ 1`, then `D_j ≠ 0` and
`deg_t D_j = -2j(j+1)`. The term `n` of the sum defining `D_j` has degree at most
`-2n² - 2n - 4(j+1)²`, strictly below the degree `-4(j+1)²` of the term `n = 0`
(`intDegree_sum_eq_of_lt`); the prefactor `q^j (1 - q) (q;q)_j` has degree `4j + 4 + 2j(j+1)`.
As `intDegree_torusCyclotomicCoeff`, with the hypothesis on `u` in place of the explicit degree
of `torusOddColor`.
-/

noncomputable section

namespace AJConjecture

/-- A natural power of `q` is nonzero of degree `4k` in `t`. -/
private theorem intDegree_qParam_pow_pairQCyclo (k : ℕ) :
    qParam ^ k ≠ 0 ∧ (qParam ^ k).intDegree = 4 * (k : ℤ) :=
  ⟨pow_ne_zero k qParam_ne_zero, by rw [← zpow_natCast, intDegree_qParam_zpow]⟩

/-- `1 - q^k`, `k ≥ 1`, is nonzero of degree `4k` in `t`. -/
private theorem intDegree_one_sub_qParam_pow_pairQCyclo {k : ℕ} (hk : 1 ≤ k) :
    1 - qParam ^ k ≠ 0 ∧ (1 - qParam ^ k).intDegree = 4 * (k : ℤ) := by
  rw [sub_eq_neg_add]
  refine intDegree_add_eq_of_lt
    ⟨neg_ne_zero.mpr (intDegree_qParam_pow_pairQCyclo k).1, ?_⟩ (Or.inr ?_)
  · rw [RatFunc.intDegree_neg, (intDegree_qParam_pow_pairQCyclo k).2]
  · rw [RatFunc.intDegree_one]
    omega

/-- The `q`-Pochhammer symbol `(q; q)_k` is nonzero of degree `2k(k+1)` in `t`. -/
private theorem intDegree_qPochhammer_qParam_pairQCyclo (k : ℕ) :
    qPochhammer qParam k ≠ 0 ∧
      (qPochhammer qParam k).intDegree = 2 * (k : ℤ) * ((k : ℤ) + 1) := by
  induction k with
  | zero =>
    rw [qPochhammer, Finset.prod_range_zero]
    exact ⟨one_ne_zero, by rw [RatFunc.intDegree_one]; simp⟩
  | succ k ih =>
    have h1 := intDegree_one_sub_qParam_pow_pairQCyclo (k := k + 1) (by omega)
    rw [pow_succ'] at h1
    have h2 := intDegree_mul_eq ih h1
    rw [qPochhammer, Finset.prod_range_succ]
    refine ⟨h2.1, h2.2.trans ?_⟩
    push_cast
    ring

/-- A power of `-1` is nonzero of degree `0`. -/
private theorem intDegree_neg_one_pow_pairQCyclo (n : ℕ) :
    (-1 : RatFunc ℚ) ^ n ≠ 0 ∧ ((-1 : RatFunc ℚ) ^ n).intDegree = 0 := by
  refine ⟨pow_ne_zero n (neg_ne_zero.mpr one_ne_zero), ?_⟩
  rcases neg_one_pow_eq_or (RatFunc ℚ) n with h | h
  · rw [h, RatFunc.intDegree_one]
  · rw [h, RatFunc.intDegree_neg, RatFunc.intDegree_one]

/-- The weight of `u_n` in the term `n` of the sum defining `D_j` is nonzero of degree
`-2n² - 2n - 4j² - 8j - 4` in `t`. -/
private theorem intDegree_pairQCycloCoeff_weight {j n : ℕ} (hn : n ≤ j) :
    (-1) ^ n * qParam ^ (n * (n + 1) / 2) /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1)) ≠ 0 ∧
      ((-1) ^ n * qParam ^ (n * (n + 1) / 2) /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1))).intDegree =
        -2 * (n : ℤ) ^ 2 - 2 * n - 4 * (j : ℤ) ^ 2 - 8 * j - 4 := by
  have h := intDegree_div_eq
    (intDegree_mul_eq (intDegree_neg_one_pow_pairQCyclo n)
      (intDegree_qParam_pow_pairQCyclo (n * (n + 1) / 2)))
    (intDegree_mul_eq (intDegree_qPochhammer_qParam_pairQCyclo (j - n))
      (intDegree_qPochhammer_qParam_pairQCyclo (j + n + 1)))
  refine ⟨h.1, h.2.trans ?_⟩
  have h2 : ((n * (n + 1) / 2 : ℕ) : ℤ) * 2 = (n : ℤ) * ((n : ℤ) + 1) := by
    exact_mod_cast Nat.div_two_mul_two_of_even (Nat.even_mul_succ_self n)
  rw [Nat.cast_sub hn, Nat.cast_add, Nat.cast_add, Nat.cast_one]
  linear_combination 2 * h2

/-- The sum defining `D_j` is nonzero of degree `-4(j+1)²`: its term `n = 0` dominates. -/
private theorem intDegree_pairQCycloCoeff_sum (u : ℕ → RatFunc ℚ) (h0 : u 0 = 1)
    (hdeg : ∀ n : ℕ, 1 ≤ n → u n = 0 ∨ (u n).intDegree ≤ 0) (j : ℕ) :
    ∑ n ∈ Finset.range (j + 1), (-1) ^ n * qParam ^ (n * (n + 1) / 2) * u n /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1)) ≠ 0 ∧
      (∑ n ∈ Finset.range (j + 1), (-1) ^ n * qParam ^ (n * (n + 1) / 2) * u n /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1))).intDegree =
        -4 * (j : ℤ) ^ 2 - 8 * j - 4 := by
  have hterm : ∀ n : ℕ, (-1) ^ n * qParam ^ (n * (n + 1) / 2) * u n /
      (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1)) =
      (-1) ^ n * qParam ^ (n * (n + 1) / 2) /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1)) * u n := fun n ↦ by
    rw [mul_div_right_comm]
  simp only [hterm]
  have hw0 := intDegree_pairQCycloCoeff_weight (Nat.zero_le j)
  refine intDegree_sum_eq_of_lt (a := 0) (Finset.mem_range.mpr (by omega))
    ⟨?_, ?_⟩ fun n hn hn0 ↦ ?_
  · rw [h0, mul_one]
    exact hw0.1
  · rw [h0, mul_one, hw0.2]
    push_cast
    ring
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hw := intDegree_pairQCycloCoeff_weight (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
    by_cases hu0 : u n = 0
    · left
      rw [hu0, mul_zero]
    · right
      have hu := (hdeg n hn1).resolve_left hu0
      rw [RatFunc.intDegree_mul hw.1 hu0, hw.2]
      have hn2 : (1 : ℤ) ≤ n := by exact_mod_cast hn1
      nlinarith

theorem pairQ_intDegree_cycloCoeff (u : ℕ → RatFunc ℚ) (h0 : u 0 = 1)
    (hdeg : ∀ n : ℕ, 1 ≤ n → u n = 0 ∨ (u n).intDegree ≤ 0) (j : ℕ) :
    pairQCycloCoeff u j ≠ 0 ∧
      (pairQCycloCoeff u j).intDegree = -2 * (j : ℤ) * ((j : ℤ) + 1) := by
  have h1 := intDegree_one_sub_qParam_pow_pairQCyclo (k := 1) le_rfl
  rw [pow_one] at h1
  have h := intDegree_mul_eq (intDegree_mul_eq
    (intDegree_mul_eq (intDegree_qParam_pow_pairQCyclo j) h1)
    (intDegree_qPochhammer_qParam_pairQCyclo j)) (intDegree_pairQCycloCoeff_sum u h0 hdeg j)
  refine ⟨h.1, h.2.trans ?_⟩
  push_cast
  ring

end AJConjecture
