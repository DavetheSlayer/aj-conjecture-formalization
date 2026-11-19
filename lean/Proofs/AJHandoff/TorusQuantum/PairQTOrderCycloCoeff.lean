import Mathlib
import AJHandoff.TorusQuantum.PairQTOrderOddColor

/-!
# The `t`-valuation of the cyclotomic coefficients of `T(r, s)`

For `r, s ≥ 2`: `D_j ≠ 0` and `ord_t D_j = 4j - 2(2rs - 1) j(j+1)` (source §5). Every Pochhammer
factor `(q;q)_k` has order `0`; the term `n` of the sum defining `D_j` has order
`2n(n+1) - 4rs n(n+1)`, strictly decreasing in `n` (`rs ≥ 1`), so the term `n = j` is the unique
term of least order (`pairQTOrder_sum_eq_of_lt`); the prefactor `q^j (1 - q)` has order `4j`.
-/

noncomputable section

namespace AJConjecture

/-- A power of `-1` is nonzero of order `0`. -/
private theorem pairQTOrder_neg_one_pow_cyclo (n : ℕ) :
    (-1 : RatFunc ℚ) ^ n ≠ 0 ∧ pairQTOrder ((-1 : RatFunc ℚ) ^ n) = 0 := by
  have h1 : pairQTOrder (1 : RatFunc ℚ) = 0 := by simpa using pairQTOrder_X_zpow 0
  refine ⟨pow_ne_zero n (neg_ne_zero.mpr one_ne_zero), ?_⟩
  rcases neg_one_pow_eq_or (RatFunc ℚ) n with h | h
  · rw [h, h1]
  · rw [h, pairQTOrder_neg, h1]

/-- The term `n ≤ j` of the sum defining `D_j` is nonzero of order `2n(n+1) - 4rs n(n+1)`. -/
private theorem pairQTOrder_pairQCycloCoeff_term (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s)
    (j n : ℕ) :
    (-1) ^ n * qParam ^ (n * (n + 1) / 2) * pairQOddColor r s n /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1)) ≠ 0 ∧
      pairQTOrder ((-1) ^ n * qParam ^ (n * (n + 1) / 2) * pairQOddColor r s n /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1))) =
        2 * (n : ℤ) * ((n : ℤ) + 1) - 4 * ((r : ℤ) * s) * n * ((n : ℤ) + 1) := by
  have h := pairQTOrder_div_eq
    (pairQTOrder_mul_eq (pairQTOrder_mul_eq (pairQTOrder_neg_one_pow_cyclo n)
      (pairQTOrder_qParam_pow_eq (n * (n + 1) / 2))) (pairQ_tOrder_oddColor r s hr hs n))
    (pairQTOrder_mul_eq (pairQTOrder_qPochhammer_qParam (j - n))
      (pairQTOrder_qPochhammer_qParam (j + n + 1)))
  refine ⟨h.1, h.2.trans ?_⟩
  have h2 : ((n * (n + 1) / 2 : ℕ) : ℤ) * 2 = (n : ℤ) * ((n : ℤ) + 1) := by
    exact_mod_cast Nat.div_two_mul_two_of_even (Nat.even_mul_succ_self n)
  linear_combination 2 * h2

/-- The sum defining `D_j` is nonzero of order `2j(j+1) - 4rs j(j+1)`: its term `n = j` has the
least order. -/
private theorem pairQTOrder_pairQCycloCoeff_sum (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (j : ℕ) :
    ∑ n ∈ Finset.range (j + 1), (-1) ^ n * qParam ^ (n * (n + 1) / 2) * pairQOddColor r s n /
        (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1)) ≠ 0 ∧
      pairQTOrder (∑ n ∈ Finset.range (j + 1),
        (-1) ^ n * qParam ^ (n * (n + 1) / 2) * pairQOddColor r s n /
          (qPochhammer qParam (j - n) * qPochhammer qParam (j + n + 1))) =
        2 * (j : ℤ) * ((j : ℤ) + 1) - 4 * ((r : ℤ) * s) * j * ((j : ℤ) + 1) := by
  have hr0 : (2 : ℤ) ≤ r := by exact_mod_cast hr
  have hs0 : (2 : ℤ) ≤ s := by exact_mod_cast hs
  have hrs : (4 : ℤ) ≤ r * s := by nlinarith
  refine pairQTOrder_sum_eq_of_lt (a := j) (Finset.mem_range.mpr (by omega))
    (pairQTOrder_pairQCycloCoeff_term r s hr hs j j) fun n hn hnj ↦ Or.inr ?_
  rw [(pairQTOrder_pairQCycloCoeff_term r s hr hs j n).2]
  have hn' : (n : ℤ) + 1 ≤ j := by
    have := Finset.mem_range.mp hn
    omega
  have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have h1 : (n : ℤ) * ((n : ℤ) + 1) < (j : ℤ) * ((j : ℤ) + 1) := by nlinarith
  nlinarith

theorem pairQ_tOrder_cycloCoeff (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (j : ℕ) :
    pairQCycloCoeff (pairQOddColor r s) j ≠ 0 ∧
      pairQTOrder (pairQCycloCoeff (pairQOddColor r s) j) =
        4 * (j : ℤ) - 2 * (2 * ((r : ℤ) * s) - 1) * j * ((j : ℤ) + 1) := by
  have h1 := pairQTOrder_one_sub_qParam_zpow_of_pos (k := 1) one_pos
  rw [zpow_one] at h1
  have h := pairQTOrder_mul_eq (pairQTOrder_mul_eq
    (pairQTOrder_mul_eq (pairQTOrder_qParam_pow_eq j) h1)
    (pairQTOrder_qPochhammer_qParam j)) (pairQTOrder_pairQCycloCoeff_sum r s hr hs j)
  refine ⟨h.1, h.2.trans ?_⟩
  ring

end AJConjecture
