import Mathlib
import AJTwist.Select.TwSCoefDefs

/-!
# The exact orders of the coefficients of the actual sequence, `θ = 0`

Source: eq. (positive-companion-coeff) of `selection.tex` (revision 5), for the cleared
coefficients `A'_d` (the minimal term has geometric degree `0`, so the orders are those of `A_d`).

With `n = j + l` the term `τ(n, d - j, j)` of `A'_d` has order (in units of `q`), for
`ord w_n = b n(n+1)`,
`(b + 1/2) j² + (b - 1/2 - d) j + (2b - 1) j l + b l² + b l`; at `d = (2b+1) k`, `k ≥ 1`, the
`j`-part exceeds its value at `j = k` by `h ((2b+1) h + 2b - 1) / 2 > 0`, `h = j - k ≠ 0`, so
`(n, j) = (k, k)` is the unique minimum, of value `-((2b+1) k² - (2b-1) k) / 2`. The statement is
for an arbitrary input of the stated exact orders (`tws_tOrder_twsTerm`, `order_twsSum_eq`,
`pairQTOrder_sum_eq_of_lt`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A finite sum of series of order greater than `g` has order greater than `g`. -/
private theorem lt_orderTop_sum_coefActualPos {ι : Type*} (s : Finset ι)
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

/-- The excess `h ((2b+1) h + 2b - 1)` of the `j`-part over its value at `j = k`, `h = j - k`,
is positive for `h ≠ 0`. -/
private theorem gap_pos_coefActualPos {b h : ℤ} (hb : 1 ≤ b) (hh : h ≠ 0) :
    0 < h * ((2 * b + 1) * h + 2 * b - 1) := by
  rcases lt_or_gt_of_ne hh with h1 | h1
  · have h2 : 0 ≤ (2 * b + 1) * (-(h + 1)) := mul_nonneg (by linarith) (by linarith)
    exact mul_pos_of_neg_of_neg h1 (by linarith)
  · have h2 : 0 < (2 * b + 1) * h := mul_pos (by linarith) h1
    exact mul_pos h1 (by linarith)

/-- The term `(n, j) = (k, k)` of `A'_{(2b+1)k}` is the unique term of least order. -/
private theorem order_gap_coefActualPos {b k n j : ℕ} (hb : 1 ≤ b) (hj : j ≤ n)
    (hjd : j ≤ (2 * b + 1) * k) (hne : ¬ (n = k ∧ j = k)) :
    -2 * ((2 * (b : ℤ) + 1) * (k : ℤ) ^ 2 - (2 * (b : ℤ) - 1) * k) <
      4 * (b : ℤ) * n * ((n : ℤ) + 1) + 2 * (j : ℤ) * ((j : ℤ) - 1) -
        4 * (j : ℤ) * ((((2 * b + 1) * k - j : ℕ) : ℤ) + n) := by
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
  have hjn : (j : ℤ) ≤ n := by exact_mod_cast hj
  rw [Nat.cast_sub hjd]
  push_cast
  have e : 4 * (b : ℤ) * n * ((n : ℤ) + 1) + 2 * (j : ℤ) * ((j : ℤ) - 1) -
      4 * (j : ℤ) * ((2 * (b : ℤ) + 1) * k - j + n) =
      -2 * ((2 * (b : ℤ) + 1) * (k : ℤ) ^ 2 - (2 * (b : ℤ) - 1) * k) +
        (2 * (((j : ℤ) - k) * ((2 * (b : ℤ) + 1) * ((j : ℤ) - k) + 2 * b - 1)) +
          4 * ((2 * (b : ℤ) - 1) * j * ((n : ℤ) - j)) + 4 * (b : ℤ) * ((n : ℤ) - j) ^ 2 +
          4 * (b : ℤ) * ((n : ℤ) - j)) := by
    ring
  rw [e]
  have h1 : (0 : ℤ) ≤ (2 * (b : ℤ) - 1) * j * ((n : ℤ) - j) :=
    mul_nonneg (mul_nonneg (by linarith) hj0) (by linarith)
  have h2 : (0 : ℤ) ≤ (b : ℤ) * ((n : ℤ) - j) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : (0 : ℤ) ≤ (b : ℤ) * ((n : ℤ) - j) := mul_nonneg (by linarith) (by linarith)
  by_cases hjk : j = k
  · have hnj : n ≠ j := fun h ↦ hne ⟨h.trans hjk, hjk⟩
    have h4 : (1 : ℤ) ≤ (n : ℤ) - j := by lia
    have h5 : (1 : ℤ) * 1 ≤ (b : ℤ) * ((n : ℤ) - j) := mul_le_mul hb' h4 zero_le_one (by linarith)
    rw [hjk] at h1 h2 h5 ⊢
    rw [sub_self, zero_mul]
    linarith
  · have h4 := gap_pos_coefActualPos hb' (h := (j : ℤ) - k) (by lia)
    linarith

set_option linter.unusedVariables false in
/-- **Eq. (positive-companion-coeff).** For an input of exact order `4 b n(n+1)` at `t = 0`,
`b ≥ 1`, the coefficient `A'_{(2b+1)k}` (`θ = 0`, `k ≥ 1`) is nonzero of order
`-2 ((2b+1) k² - (2b-1) k)`. -/
theorem tws_order_coef_zero_of_input {u : ℕ → RatFunc ℚ} {b : ℕ} (hb : 1 ≤ b)
    (hu : ∀ n : ℕ, u n ≠ 0 ∧ pairQTOrder (u n) = 4 * (b : ℤ) * n * ((n : ℤ) + 1)) {k : ℕ}
    (hk : 1 ≤ k) :
    twsCoef false u ((2 * b + 1) * k) ≠ 0 ∧
      (twsCoef false u ((2 * b + 1) * k)).order =
        -2 * ((2 * (b : ℤ) + 1) * (k : ℤ) ^ 2 - (2 * (b : ℤ) - 1) * k) := by
  have hkd : k ≤ (2 * b + 1) * k := Nat.le_mul_of_pos_left k (by omega)
  have hsum : TwsSummable fun n ↦ twsSeries (twsCoefSummand false u ((2 * b + 1) * k) n) := by
    refine tws_summable_coef_zero (B := 0) (C := 0) (fun n ↦ Or.inr ?_) _
    rw [(hu n).2]
    have h1 : (1 : ℤ) ≤ b := by exact_mod_cast hb
    have h2 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    nlinarith [mul_nonneg h2 h2, mul_nonneg (sub_nonneg.mpr h1) (mul_nonneg h2 h2),
      mul_nonneg (le_trans zero_le_one h1) h2]
  have hterm : ∀ n j : ℕ, j ≤ n → twsTerm false u n ((2 * b + 1) * k - j) j ≠ 0 ∧
      pairQTOrder (twsTerm false u n ((2 * b + 1) * k - j) j) =
        4 * (b : ℤ) * n * ((n : ℤ) + 1) + 2 * (j : ℤ) * ((j : ℤ) - 1) -
          4 * (j : ℤ) * ((((2 * b + 1) * k - j : ℕ) : ℤ) + n) := by
    intro n j hj
    have h := tws_tOrder_twsTerm false (hu n).1 ((2 * b + 1) * k - j) hj
    refine ⟨h.1, h.2.trans ?_⟩
    rw [(hu n).2]
    simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  have h1q : (1 - qParam : RatFunc ℚ) ≠ 0 ∧ pairQTOrder (1 - qParam) = 0 := by
    have h := pairQTOrder_one_sub_qParam_zpow_of_pos (k := 1) one_pos
    rwa [zpow_one] at h
  have hk0 : twsCoefSummand false u ((2 * b + 1) * k) k ≠ 0 ∧
      pairQTOrder (twsCoefSummand false u ((2 * b + 1) * k) k) =
        -2 * ((2 * (b : ℤ) + 1) * (k : ℤ) ^ 2 - (2 * (b : ℤ) - 1) * k) := by
    have hin := pairQTOrder_sum_eq_of_lt (s := Finset.range (min k ((2 * b + 1) * k) + 1))
      (f := fun j ↦ twsTerm false u k ((2 * b + 1) * k - j) j) (a := k)
      (d := -2 * ((2 * (b : ℤ) + 1) * (k : ℤ) ^ 2 - (2 * (b : ℤ) - 1) * k))
      (Finset.mem_range.mpr (by omega))
      ⟨(hterm k k le_rfl).1, (hterm k k le_rfl).2.trans (by
        rw [Nat.cast_sub hkd]
        push_cast
        ring)⟩
      fun j hj hjk ↦ Or.inr (by
        rw [Finset.mem_range] at hj
        rw [(hterm k j (by omega)).2]
        exact order_gap_coefActualPos hb (by omega) (by omega) fun h ↦ hjk h.2)
    have h := pairQTOrder_mul_eq h1q hin
    rwa [zero_add] at h
  have hs0 : twsSeries (twsCoefSummand false u ((2 * b + 1) * k) k) ≠ 0 :=
    (map_ne_zero twsSeries).mpr hk0.1
  have hso : (twsSeries (twsCoefSummand false u ((2 * b + 1) * k) k)).order =
      -2 * ((2 * (b : ℤ) + 1) * (k : ℤ) ^ 2 - (2 * (b : ℤ) - 1) * k) := by
    rw [tws_order_twsSeries hk0.1, hk0.2]
  have h := order_twsSum_eq hsum (n₀ := k) hs0 fun n hn ↦ by
    rw [hso]
    have hlt : ((-2 * ((2 * (b : ℤ) + 1) * (k : ℤ) ^ 2 - (2 * (b : ℤ) - 1) * k) : ℤ) :
        WithTop ℤ) < (twsSeries (twsCoefSummand false u ((2 * b + 1) * k) n)).orderTop := by
      rw [twsCoefSummand, Finset.mul_sum, map_sum]
      refine lt_orderTop_sum_coefActualPos _ _ _ fun j hj ↦ ?_
      rw [Finset.mem_range] at hj
      have hm := pairQTOrder_mul_eq h1q (hterm n j (by omega))
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero twsSeries).mpr hm.1),
        tws_order_twsSeries hm.1, hm.2, zero_add]
      exact WithTop.coe_lt_coe.mpr
        (order_gap_coefActualPos hb (by omega) (by omega) fun h ↦ hn h.1)
    by_cases hz : twsSeries (twsCoefSummand false u ((2 * b + 1) * k) n) = 0
    · exact Or.inl hz
    · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hz] at hlt
      exact Or.inr (WithTop.coe_lt_coe.mp hlt)
  rw [hso] at h
  exact h

end AJConjecture
