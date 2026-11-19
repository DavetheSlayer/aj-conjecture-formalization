import Mathlib
import AJHandoff.TorusQuantum.PairQTOrder
import AJHandoff.TorusQuantum.PairQFormula

/-!
# The `t`-valuation of the odd colours of `T(r, s)`

For `r, s ≥ 2`: `u_n ≠ 0` and `ord_t u_n = -4rs n(n+1)` (source §5). In the sum defining
`pairQOddColor`, the term `k = 0` is `1`; the term `k = a > 0` has order `4a(rsa + r - s) > 0` and
the term `k = -a < 0` has order `4(ra - 1)(sa - 1) > 0` (with `ord_t [l] = 2 - 2|l|` and
`ord_t q^e = 4e`), so the sum has order `0` (`pairQTOrder_sum_eq_of_lt`); the prefactor gives
`-4rs n(n+1)`.
-/

noncomputable section

namespace AJConjecture

/-- The term of index `k` of the sum defining `pairQOddColor r s` is nonzero of order
`4rk(sk+1) + 2 - 2|2sk+1|`. -/
private theorem pairQTOrder_pairQOddColor_term (r s : ℕ) (k : ℤ) :
    qParam ^ ((r : ℤ) * k * ((s : ℤ) * k + 1)) * quantumInt (2 * (s : ℤ) * k + 1) ≠ 0 ∧
      pairQTOrder (qParam ^ ((r : ℤ) * k * ((s : ℤ) * k + 1)) *
        quantumInt (2 * (s : ℤ) * k + 1)) =
        4 * ((r : ℤ) * k * ((s : ℤ) * k + 1)) +
          (min (2 * (2 * (s : ℤ) * k + 1)) (-(2 * (2 * (s : ℤ) * k + 1))) + 2) := by
  have hne : 2 * (s : ℤ) * k + 1 ≠ 0 := by
    rw [mul_assoc]
    omega
  exact pairQTOrder_mul_eq (pairQTOrder_qParam_zpow_eq _) (pairQTOrder_quantumInt hne)

/-- The sum defining `pairQOddColor r s n` is nonzero of order `0`: its term `k = 0`, equal to
`1`, has the least order. -/
private theorem pairQTOrder_pairQOddColor_sum (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (n : ℕ) :
    ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
        qParam ^ ((r : ℤ) * k * ((s : ℤ) * k + 1)) * quantumInt (2 * (s : ℤ) * k + 1) ≠ 0 ∧
      pairQTOrder (∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
        qParam ^ ((r : ℤ) * k * ((s : ℤ) * k + 1)) *
          quantumInt (2 * (s : ℤ) * k + 1)) = 0 := by
  have hr0 : (2 : ℤ) ≤ r := by exact_mod_cast hr
  have hs0 : (2 : ℤ) ≤ s := by exact_mod_cast hs
  refine pairQTOrder_sum_eq_of_lt (a := (0 : ℤ)) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    ⟨(pairQTOrder_pairQOddColor_term r s 0).1, ?_⟩ fun k _ hk0 ↦ Or.inr ?_
  · rw [(pairQTOrder_pairQOddColor_term r s 0).2]
    simp
  · rw [(pairQTOrder_pairQOddColor_term r s k).2, mul_assoc 2 (s : ℤ) k]
    rcases lt_or_gt_of_ne hk0 with h0 | h0
    · have h1 : (s : ℤ) * k < 0 := by nlinarith
      have h2 : (1 : ℤ) ≤ -((r : ℤ) * k) - 1 := by nlinarith
      have h3 : (1 : ℤ) ≤ -((s : ℤ) * k) - 1 := by nlinarith
      have h4 := one_le_mul_of_one_le_of_one_le h2 h3
      rw [min_eq_left (by omega)]
      nlinarith
    · have h1 : 0 < (s : ℤ) * k := by nlinarith
      have h2 : (2 : ℤ) * k ≤ r * k := by nlinarith
      rw [min_eq_right (by omega)]
      nlinarith

theorem pairQ_tOrder_oddColor (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) (n : ℕ) :
    pairQOddColor r s n ≠ 0 ∧
      pairQTOrder (pairQOddColor r s n) = -4 * ((r : ℤ) * s) * n * ((n : ℤ) + 1) := by
  have h := pairQTOrder_mul_eq (pairQTOrder_qParam_zpow_eq (-((r : ℤ) * s * n * ((n : ℤ) + 1))))
    (pairQTOrder_pairQOddColor_sum r s hr hs n)
  refine ⟨h.1, h.2.trans ?_⟩
  ring

end AJConjecture
