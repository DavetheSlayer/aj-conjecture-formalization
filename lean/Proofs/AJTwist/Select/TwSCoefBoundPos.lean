import Mathlib
import AJTwist.Select.TwSCoefDefs

/-!
# Lower bounds for the coefficients of the Gaussian periods, `θ = 0`

Source: Section 6.5 of `selection.tex` (revision 5): the bound
`ν A_{0,d}(w^{(ℓ,c)}) ≥ -(d + c)² / (2 (2γ + 1)) - O(1)`, here for every input of order at least
`γ n(n+1) - B (n+1)` (in units of `q`) and for the cleared coefficients `A'_d`.

With `n = j + l`, the order of the term `τ(n, d - j, j)` is at least
`(γ + 1/2) j² + (γ - 1/2 - d - B) j + (2γ - 1) j l + γ l² + (γ - B) l - B`, which is at least
`-(d + B + 1/2 - γ)² / (2 (2γ + 1)) - (B - γ)² / (4γ) - B` (complete the squares in `j` and in
`l`). In the `M`-degree `j_M = 2d` and in units of `t` this is `D · ord ≥ -(j_M² + O(j_M))` with
`D = 2 (2γ + 1)`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A finite sum of series of order at least `g` has order at least `g`. -/
private theorem le_orderTop_sum_coefBoundPos {ι : Type*} (s : Finset ι)
    (f : ι → LaurentSeries ℚ) (g : WithTop ℤ) (h : ∀ i ∈ s, g ≤ (f i).orderTop) :
    g ≤ (∑ i ∈ s, f i).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, HahnSeries.orderTop_zero]
    exact le_top
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (le_min (h a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))) HahnSeries.min_orderTop_le_orderTop_add

/-- A lower bound for the order at `t = 0` is one for the order of the expansion. -/
private theorem le_orderTop_twsSeries_coefBoundPos {x : RatFunc ℚ} {b : ℤ}
    (h : x = 0 ∨ b ≤ pairQTOrder x) : (b : WithTop ℤ) ≤ (twsSeries x).orderTop := by
  by_cases h0 : x = 0
  · rw [h0, map_zero, HahnSeries.orderTop_zero]
    exact le_top
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero twsSeries).mpr h0),
    tws_order_twsSeries h0]
  exact WithTop.coe_le_coe.mpr (h.resolve_left h0)

/-- Multiplication by `1 - q` does not lower the order of the expansion. -/
private theorem le_orderTop_one_sub_mul_coefBoundPos {x : RatFunc ℚ} {b : WithTop ℤ}
    (h : b ≤ (twsSeries x).orderTop) : b ≤ (twsSeries ((1 - qParam) * x)).orderTop := by
  have h1q : (1 - qParam : RatFunc ℚ) ≠ 0 ∧ pairQTOrder (1 - qParam) = 0 := by
    have h := pairQTOrder_one_sub_qParam_zpow_of_pos (k := 1) one_pos
    rwa [zpow_one] at h
  rw [map_mul, HahnSeries.orderTop_mul,
    ← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero twsSeries).mpr h1q.1),
    tws_order_twsSeries h1q.1, h1q.2, WithTop.coe_zero, zero_add]
  exact h

/-- Completing the squares in `j` and in `l = n - j`: the order of every term `τ(n, d - j, j)` of
`A'_d`, times `2 (2γ + 1)`, is at least `-((2d)² + C (2d) + C)`. -/
private theorem term_ineq_coefBoundPos {γ B C : ℤ} (hγ : 1 ≤ γ)
    (hC : C = 2 * |2 * B + 1 - 2 * γ| + (2 * B + 1 - 2 * γ) ^ 2 +
      8 * (2 * γ + 1) * ((B - γ) ^ 2 + |B|)) {n j d : ℕ} (hjn : j ≤ n) (hjd : j ≤ d) :
    -((2 * (d : ℤ)) ^ 2 + C * (2 * (d : ℤ)) + C) ≤
      2 * (2 * γ + 1) * (4 * (γ * n * ((n : ℤ) + 1) - B * ((n : ℤ) + 1)) +
        2 * (j : ℤ) * ((j : ℤ) - 1) - 4 * (j : ℤ) * (((d - j : ℕ) : ℤ) + n)) := by
  have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg j
  have hd0 : (0 : ℤ) ≤ d := Int.natCast_nonneg d
  have hjn' : (j : ℤ) ≤ n := by exact_mod_cast hjn
  rw [Nat.cast_sub hjd]
  have e : 2 * (2 * γ + 1) * (4 * (γ * n * ((n : ℤ) + 1) - B * ((n : ℤ) + 1)) +
      2 * (j : ℤ) * ((j : ℤ) - 1) - 4 * (j : ℤ) * ((d : ℤ) - j + n)) =
      (2 * (2 * γ + 1) * j + (2 * γ - 1 - 2 * d - 2 * B)) ^ 2 -
        (2 * (d : ℤ) + (2 * B + 1 - 2 * γ)) ^ 2 +
        8 * (2 * γ + 1) * ((2 * γ - 1) * j * ((n : ℤ) - j) + γ * ((n : ℤ) - j) ^ 2 +
          (γ - B) * ((n : ℤ) - j) - B) := by
    ring
  rw [e]
  have h0 := sq_nonneg (2 * (2 * γ + 1) * j + (2 * γ - 1 - 2 * d - 2 * B))
  have h1 : (0 : ℤ) ≤ (2 * γ - 1) * j * ((n : ℤ) - j) :=
    mul_nonneg (mul_nonneg (by linarith) hj0) (by linarith)
  have h2 : (0 : ℤ) ≤ (γ - 1) * ((n : ℤ) - j) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : (0 : ℤ) ≤ (2 * ((n : ℤ) - j) - (B - γ)) ^ 2 + 3 * (B - γ) ^ 2 := by positivity
  have h4 := le_abs_self B
  have h5 : (0 : ℤ) ≤ 8 * (2 * γ + 1) * ((2 * γ - 1) * j * ((n : ℤ) - j) +
      γ * ((n : ℤ) - j) ^ 2 + (γ - B) * ((n : ℤ) - j) - B + ((B - γ) ^ 2 + |B|)) :=
    mul_nonneg (by linarith) (by nlinarith)
  have h6 : (0 : ℤ) ≤ (d : ℤ) * (|2 * B + 1 - 2 * γ| - (2 * B + 1 - 2 * γ)) :=
    mul_nonneg hd0 (sub_nonneg.mpr (le_abs_self _))
  have h7 : (0 : ℤ) ≤ (d : ℤ) * ((2 * B + 1 - 2 * γ) ^ 2 +
      8 * (2 * γ + 1) * ((B - γ) ^ 2 + |B|)) :=
    mul_nonneg hd0 (add_nonneg (sq_nonneg _)
      (mul_nonneg (by linarith) (add_nonneg (sq_nonneg _) (abs_nonneg _))))
  have h8 := abs_nonneg (2 * B + 1 - 2 * γ)
  rw [hC]
  linarith

/-- An input of order at least `4 (γ n(n+1) - B (n+1))`, `γ ≥ 1`, has order at least
`4 (n² - |B| n - |B|)`. -/
private theorem input_bound_coefBoundPos {w : ℕ → RatFunc ℚ} {γ B : ℤ} (hγ : 1 ≤ γ)
    (hw : ∀ n : ℕ, w n = 0 ∨
      4 * (γ * n * ((n : ℤ) + 1) - B * ((n : ℤ) + 1)) ≤ pairQTOrder (w n)) (n : ℕ) :
    w n = 0 ∨ 4 * ((n : ℤ) ^ 2 - |B| * n - |B|) ≤ pairQTOrder (w n) := by
  refine (hw n).imp_right fun h ↦ le_trans ?_ h
  have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have h1 : (0 : ℤ) ≤ (γ - 1) * ((n : ℤ) * n) := mul_nonneg (by linarith) (mul_nonneg hn0 hn0)
  have h2 : (0 : ℤ) ≤ γ * n := mul_nonneg (by linarith) hn0
  have h3 : (0 : ℤ) ≤ (|B| - B) * ((n : ℤ) + 1) :=
    mul_nonneg (sub_nonneg.mpr (le_abs_self B)) (by linarith)
  nlinarith

/-- Lower bound for the coefficients `A'_d`, `θ = 0`, of an input of order at least
`4 (γ n(n+1) - B (n+1))`, `γ ≥ 1`. -/
theorem tws_bound_coef_zero_of_input {w : ℕ → RatFunc ℚ} {γ B : ℤ} (hγ : 1 ≤ γ)
    (hw : ∀ n : ℕ, w n = 0 ∨
      4 * (γ * n * ((n : ℤ) + 1) - B * ((n : ℤ) + 1)) ≤ pairQTOrder (w n)) :
    ∃ C : ℤ, ∀ d : ℕ, twsCoef false w d = 0 ∨
      -((2 * (d : ℤ)) ^ 2 + C * (2 * (d : ℤ)) + C) ≤
        2 * (2 * γ + 1) * (twsCoef false w d).order := by
  obtain ⟨C, hC⟩ : ∃ C : ℤ, C = 2 * |2 * B + 1 - 2 * γ| + (2 * B + 1 - 2 * γ) ^ 2 +
      8 * (2 * γ + 1) * ((B - γ) ^ 2 + |B|) := ⟨_, rfl⟩
  refine ⟨C, fun d ↦ ?_⟩
  by_cases h0 : twsCoef false w d = 0
  · exact Or.inl h0
  refine Or.inr ?_
  have hD : (0 : ℤ) < 2 * (2 * γ + 1) := by linarith
  have hsum := tws_summable_coef_zero (input_bound_coefBoundPos hγ hw) d
  have hle : ((-(((2 * (d : ℤ)) ^ 2 + C * (2 * (d : ℤ)) + C) / (2 * (2 * γ + 1))) : ℤ) :
      WithTop ℤ) ≤ (twsCoef false w d).orderTop := by
    refine le_orderTop_twsSum hsum fun n ↦ ?_
    rw [twsCoefSummand]
    refine le_orderTop_one_sub_mul_coefBoundPos ?_
    rw [map_sum]
    refine le_orderTop_sum_coefBoundPos _ _ _ fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    have hjn : j ≤ n := by omega
    refine le_orderTop_twsSeries_coefBoundPos ?_
    by_cases hw0 : w n = 0
    · exact Or.inl (by simp [twsTerm, hw0])
    refine Or.inr ?_
    rw [(tws_tOrder_twsTerm false hw0 (d - j) hjn).2]
    simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
    have h1 := term_ineq_coefBoundPos hγ hC hjn (by omega : j ≤ d)
    have h2 := (hw n).resolve_left hw0
    rw [neg_le]
    refine Int.le_ediv_of_mul_le hD ?_
    nlinarith
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero h0, WithTop.coe_le_coe] at hle
  have h3 := Int.ediv_mul_le ((2 * (d : ℤ)) ^ 2 + C * (2 * (d : ℤ)) + C) hD.ne'
  nlinarith

end AJConjecture
