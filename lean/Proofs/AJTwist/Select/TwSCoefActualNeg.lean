import Mathlib
import AJTwist.Select.TwSCoefDefs

/-!
# The exact orders of the coefficients of the actual sequence, `θ = 1`

Source: eq. (negative-companion-coeff) of `selection.tex` (revision 5), for the cleared
coefficients `A'_d`.

With `n = j + l` the term `τ(n, d - j, j)` of `A'_d` has order (in units of `q`), for
`ord w_n = a n(n+1)`, `(a + 1) j² + (a - d) j + 2 a j l + (a + 1/2) l (l + 1)`; at
`d = 2 (a+1) k` the `j`-part exceeds its value at `j = k` by `(j-k)² + a (j-k)(j-k+1) > 0`, so
`(n, j) = (k, k)` is the unique minimum, of value `-(a+1) k² + a k`. The statement is for an
arbitrary input of the stated exact orders.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A finite sum of series of order greater than `g` has order greater than `g`. -/
private theorem lt_orderTop_sum_twsCoefActualNeg {ι : Type*} (s : Finset ι)
    (f : ι → LaurentSeries ℚ) (g : ℤ) (h : ∀ i ∈ s, (g : WithTop ℤ) < (f i).orderTop) :
    (g : WithTop ℤ) < (∑ i ∈ s, f i).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, HahnSeries.orderTop_zero]
    exact WithTop.coe_lt_top g
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact lt_of_lt_of_le (lt_min (h a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))) HahnSeries.min_orderTop_le_orderTop_add

/-- The excess of the exponent of `τ(n, d - j, j)` over its value at `n = j = k` is positive
away from `(k, k)`: with `e = j - k`, `l = n - j` it is
`4 e² + 4 a e (e + 1) + 8 a j l + (4 a + 2) l (l + 1)`. -/
private theorem excess_pos_twsCoefActualNeg {a n j k : ℤ} (ha : 0 ≤ a) (hj : 0 ≤ j)
    (hjn : j ≤ n) (hne : ¬ (n = k ∧ j = k)) :
    0 < 4 * (j - k) ^ 2 + 4 * a * ((j - k) * (j - k + 1)) + 8 * a * (j * (n - j)) +
      (4 * a + 2) * ((n - j) * (n - j + 1)) := by
  have h1 : 0 ≤ (j - k) * (j - k + 1) := by
    rcases le_or_gt 0 (j - k) with h | h
    · exact mul_nonneg h (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have h2 : 0 ≤ j * (n - j) := mul_nonneg hj (by omega)
  have h3 : 0 ≤ (n - j) * (n - j + 1) := mul_nonneg (by omega) (by omega)
  have h4 := mul_nonneg ha h1
  have h5 := mul_nonneg ha h2
  have h6 := mul_nonneg ha h3
  by_cases hjk : j = k
  · have hl : 1 ≤ n - j := by omega
    have h7 : 1 ≤ (n - j) * (n - j + 1) := by nlinarith
    nlinarith [sq_nonneg (j - k)]
  · have h7 : 0 < (j - k) ^ 2 := by positivity
    nlinarith

/-- The order of the term `τ(n, d - j, j)`, `d = 2 (a+1) k`, of the coefficient of an input of
exact order `4 a n(n+1)`. -/
private theorem tOrder_term_twsCoefActualNeg {u : ℕ → RatFunc ℚ} {a : ℕ}
    (hu : ∀ n : ℕ, u n ≠ 0 ∧ pairQTOrder (u n) = 4 * (a : ℤ) * n * ((n : ℤ) + 1)) (k : ℕ)
    {n j : ℕ} (hjn : j ≤ n) (hjd : j ≤ 2 * (a + 1) * k) :
    twsTerm true u n (2 * (a + 1) * k - j) j ≠ 0 ∧
      pairQTOrder (twsTerm true u n (2 * (a + 1) * k - j) j) =
        4 * (-((a : ℤ) + 1) * (k : ℤ) ^ 2 + (a : ℤ) * k) +
          (4 * ((j : ℤ) - k) ^ 2 + 4 * (a : ℤ) * (((j : ℤ) - k) * ((j : ℤ) - k + 1)) +
            8 * (a : ℤ) * ((j : ℤ) * ((n : ℤ) - j)) +
            (4 * (a : ℤ) + 2) * (((n : ℤ) - j) * ((n : ℤ) - j + 1))) := by
  have h := tws_tOrder_twsTerm true (hu n).1 (2 * (a + 1) * k - j) hjn
  refine ⟨h.1, h.2.trans ?_⟩
  rw [(hu n).2, Nat.cast_sub hjd]
  simp only [↓reduceIte]
  push_cast
  ring

/-- **Eq. (negative-companion-coeff).** For an input of exact order `4 a n(n+1)` at `t = 0`,
`a ≥ 0`, the coefficient `A'_{2(a+1)k}` (`θ = 1`) is nonzero of order `4 (-(a+1) k² + a k)`. -/
theorem tws_order_coef_one_of_input {u : ℕ → RatFunc ℚ} {a : ℕ}
    (hu : ∀ n : ℕ, u n ≠ 0 ∧ pairQTOrder (u n) = 4 * (a : ℤ) * n * ((n : ℤ) + 1)) (k : ℕ) :
    twsCoef true u (2 * (a + 1) * k) ≠ 0 ∧
      (twsCoef true u (2 * (a + 1) * k)).order =
        4 * (-((a : ℤ) + 1) * (k : ℤ) ^ 2 + (a : ℤ) * k) := by
  have ha0 : (0 : ℤ) ≤ a := Int.natCast_nonneg a
  have hsum : TwsSummable fun n ↦ twsSeries (twsCoefSummand true u (2 * (a + 1) * k) n) :=
    tws_summable_coef_one (C := 0) (fun n ↦ Or.inr (by
      rw [(hu n).2]
      have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
      have := mul_nonneg (mul_nonneg ha0 hn0) (by omega : (0 : ℤ) ≤ (n : ℤ) + 1)
      linarith)) _
  have h1q : (1 - qParam : RatFunc ℚ) ≠ 0 ∧ pairQTOrder (1 - qParam) = 0 := by
    have h := pairQTOrder_one_sub_qParam_zpow_of_pos (k := 1) one_pos
    rwa [zpow_one] at h
  have hkd : k ≤ 2 * (a + 1) * k := by nlinarith
  have hk : twsCoefSummand true u (2 * (a + 1) * k) k ≠ 0 ∧
      pairQTOrder (twsCoefSummand true u (2 * (a + 1) * k) k) =
        4 * (-((a : ℤ) + 1) * (k : ℤ) ^ 2 + (a : ℤ) * k) := by
    have hterm := tOrder_term_twsCoefActualNeg hu k (n := k) (j := k) le_rfl hkd
    have hterm' : twsTerm true u k (2 * (a + 1) * k - k) k ≠ 0 ∧
        pairQTOrder (twsTerm true u k (2 * (a + 1) * k - k) k) =
          4 * (-((a : ℤ) + 1) * (k : ℤ) ^ 2 + (a : ℤ) * k) :=
      ⟨hterm.1, hterm.2.trans (by ring)⟩
    have hs := pairQTOrder_sum_eq_of_lt (s := Finset.range (min k (2 * (a + 1) * k) + 1))
      (f := fun j ↦ twsTerm true u k (2 * (a + 1) * k - j) j) (a := k)
      (Finset.mem_range.mpr (by omega)) hterm' fun j hj hjk ↦ Or.inr (by
        have hj' := Finset.mem_range.mp hj
        rw [(tOrder_term_twsCoefActualNeg hu k (n := k) (j := j) (by omega) (by omega)).2]
        have := excess_pos_twsCoefActualNeg (a := a) (n := k) (j := j) (k := k) ha0
          (by omega) (by omega) (by omega)
        linarith)
    have hm := pairQTOrder_mul_eq h1q hs
    rw [zero_add] at hm
    exact hm
  have hsk := (map_ne_zero twsSeries).mpr hk.1
  have hordk := tws_order_twsSeries hk.1
  have hres := order_twsSum_eq hsum (n₀ := k) hsk fun n hn ↦ by
    by_cases hz : twsSeries (twsCoefSummand true u (2 * (a + 1) * k) n) = 0
    · exact Or.inl hz
    refine Or.inr ?_
    have hlt : ((4 * (-((a : ℤ) + 1) * (k : ℤ) ^ 2 + (a : ℤ) * k) : ℤ) : WithTop ℤ) <
        (twsSeries (twsCoefSummand true u (2 * (a + 1) * k) n)).orderTop := by
      rw [twsCoefSummand, Finset.mul_sum, map_sum]
      refine lt_orderTop_sum_twsCoefActualNeg _ _ _ fun j hj ↦ ?_
      have hj' := Finset.mem_range.mp hj
      have ht := tOrder_term_twsCoefActualNeg hu k (n := n) (j := j) (by omega) (by omega)
      have hm := pairQTOrder_mul_eq h1q ht
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero twsSeries).mpr hm.1),
        tws_order_twsSeries hm.1, hm.2, zero_add, WithTop.coe_lt_coe]
      have := excess_pos_twsCoefActualNeg (a := a) (n := n) (j := j) (k := k) ha0
        (by omega) (by omega) (by omega)
      linarith
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hz, WithTop.coe_lt_coe] at hlt
    rw [hordk, hk.2]
    exact hlt
  exact ⟨hres.1, by rw [twsCoef, hres.2, hordk, hk.2]⟩

end AJConjecture
