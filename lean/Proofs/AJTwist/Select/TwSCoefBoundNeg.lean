import Mathlib
import AJTwist.Select.TwSCoefDefs

/-!
# Lower bounds for the coefficients of the Gaussian periods, `θ = 1`

Source: Section 6.6 of `selection.tex` (revision 5): the bound
`ν A_{1,d}(w^{(c)}) ≥ -(d + γ)² / (4 (γ + 1))`, here for every input of order at least
`γ n(n+1) - B (n+1)` (in units of `q`) and for the cleared coefficients `A'_d`.

With `n = j + l`, the order of the term `τ(n, d - j, j)` is at least
`(γ + 1) j² + (γ - d - B) j + 2γ j l + (γ + 1/2) l² + (γ + 1/2 - B) l - B`, at least
`-(d + B - γ)² / (4 (γ + 1)) - O(1)`. In the `M`-degree `j_M = 2d` and in units of `t` this is
`D · ord ≥ -(j_M² + O(j_M))` with `D = 4 (γ + 1)`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A finite sum of series of order at least `g` has order at least `g`. -/
private theorem le_orderTop_sum_twsCoefBoundNeg {ι : Type*} (s : Finset ι)
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

/-- The quadratic lower bound for the exponent of `τ(n, d - j, j)`: completing the squares in
`j` and in `l = n - j`. -/
private theorem exponent_quadratic_twsCoefBoundNeg {γ B d n j : ℤ} (hγ : 0 ≤ γ) (hj : 0 ≤ j)
    (hjn : j ≤ n) :
    -(4 * (d + B - γ) ^ 2 + 2 * (γ + 1) * (2 * B + 1) ^ 2) ≤
      4 * (γ + 1) * (2 * n * (n + 1) + 4 * (γ * n * (n + 1) - B * (n + 1)) +
        2 * j * (j - 1) - 4 * j * ((d - j) + n)) := by
  have hid : 4 * (γ + 1) * (2 * n * (n + 1) + 4 * (γ * n * (n + 1) - B * (n + 1)) +
      2 * j * (j - 1) - 4 * j * ((d - j) + n)) +
        (4 * (d + B - γ) ^ 2 + 2 * (γ + 1) * (2 * B + 1) ^ 2) =
      4 * (2 * (γ + 1) * j - (d + B - γ)) ^ 2 +
        16 * (γ + 1) * (2 * γ * (j * (n - j)) + γ * ((n - j) * (n - j + 1))) +
        2 * (γ + 1) * (2 * (n - j) + 1 - 2 * B) ^ 2 := by
    ring
  have h1 : 0 ≤ j * (n - j) := mul_nonneg hj (by omega)
  have h2 : 0 ≤ (n - j) * (n - j + 1) := mul_nonneg (by omega) (by omega)
  have h3 : 0 ≤ 16 * (γ + 1) * (2 * γ * (j * (n - j)) + γ * ((n - j) * (n - j + 1))) := by
    positivity
  have h4 : 0 ≤ 2 * (γ + 1) * (2 * (n - j) + 1 - 2 * B) ^ 2 := by positivity
  have h5 : 0 ≤ 4 * (2 * (γ + 1) * j - (d + B - γ)) ^ 2 := by positivity
  linarith

/-- For a fixed degree `d` the exponent of `τ(n, d - j, j)` tends to infinity with `n`. -/
private theorem exponent_tendsto_twsCoefBoundNeg {γ B d n j g : ℤ} (hγ : 0 ≤ γ) (hj : 0 ≤ j)
    (hjn : j ≤ n) (hjd : j ≤ d) (hn : 6 * |B| + 2 * d + 4 * d ^ 2 + |g| + 1 ≤ n) :
    g < 2 * n * (n + 1) + 4 * (γ * n * (n + 1) - B * (n + 1)) +
      2 * j * (j - 1) - 4 * j * ((d - j) + n) := by
  have hB := le_abs_self B
  have hB0 := abs_nonneg B
  have hg := le_abs_self g
  have hg0 := abs_nonneg g
  have hd0 : 0 ≤ d := le_trans hj hjd
  have hn0 : 0 ≤ n := le_trans hj hjn
  have h1 : 0 ≤ j * (j - 1) := by
    rcases hj.eq_or_lt with rfl | hpos
    · simp
    · exact mul_nonneg hj (by omega)
  have h2 : j * ((d - j) + n) ≤ d * (d + n) :=
    mul_le_mul hjd (by omega) (by omega) hd0
  have h3 : 0 ≤ γ * n * (n + 1) := mul_nonneg (mul_nonneg hγ hn0) (by omega)
  have h4 : B * (n + 1) ≤ |B| * (n + 1) := mul_le_mul_of_nonneg_right hB (by omega)
  have h5 : n ≤ n * (n - 2 * |B| - 2 * d) := by
    have := mul_nonneg hn0 (by nlinarith [sq_nonneg d] : (0 : ℤ) ≤ n - 2 * |B| - 2 * d - 1)
    nlinarith
  nlinarith [sq_nonneg d]

/-- The order of a term `τ(n, d - j, j)` for an input of order at least
`4 (γ n(n+1) - B (n+1))`. -/
private theorem le_tOrder_term_twsCoefBoundNeg {w : ℕ → RatFunc ℚ} {γ B : ℤ}
    (hw : ∀ n : ℕ, w n = 0 ∨
      4 * (γ * n * ((n : ℤ) + 1) - B * ((n : ℤ) + 1)) ≤ pairQTOrder (w n))
    {n d j : ℕ} (hjn : j ≤ n) (hjd : j ≤ d) (h0 : w n ≠ 0) :
    (1 - qParam) * twsTerm true w n (d - j) j ≠ 0 ∧
      2 * (n : ℤ) * ((n : ℤ) + 1) + 4 * (γ * n * ((n : ℤ) + 1) - B * ((n : ℤ) + 1)) +
        2 * (j : ℤ) * ((j : ℤ) - 1) - 4 * (j : ℤ) * (((d : ℤ) - j) + n) ≤
          pairQTOrder ((1 - qParam) * twsTerm true w n (d - j) j) := by
  have h1q : (1 - qParam : RatFunc ℚ) ≠ 0 ∧ pairQTOrder (1 - qParam) = 0 := by
    have h := pairQTOrder_one_sub_qParam_zpow_of_pos (k := 1) one_pos
    rwa [zpow_one] at h
  have hord := (hw n).resolve_left h0
  have hm := pairQTOrder_mul_eq h1q (tws_tOrder_twsTerm true h0 (d - j) hjn)
  refine ⟨hm.1, ?_⟩
  rw [hm.2, Nat.cast_sub hjd]
  simp only [↓reduceIte]
  linarith

/-- A lower bound for the orders of all the terms `(1 - q) τ(n, d - j, j)` of `A'_d`. -/
private theorem le_orderTop_term_twsCoefBoundNeg {w : ℕ → RatFunc ℚ} {γ B : ℤ} (hγ : 0 ≤ γ)
    (hw : ∀ n : ℕ, w n = 0 ∨
      4 * (γ * n * ((n : ℤ) + 1) - B * ((n : ℤ) + 1)) ≤ pairQTOrder (w n))
    {n d j : ℕ} (hjn : j ≤ n) (hjd : j ≤ d) {G : ℤ}
    (hG : ∀ x : ℤ, -(4 * ((d : ℤ) + B - γ) ^ 2 + 2 * (γ + 1) * (2 * B + 1) ^ 2) ≤
      4 * (γ + 1) * x → G ≤ x) :
    (G : WithTop ℤ) ≤ (twsSeries ((1 - qParam) * twsTerm true w n (d - j) j)).orderTop := by
  by_cases h0 : w n = 0
  · have hz : twsTerm true w n (d - j) j = 0 := by simp [twsTerm, h0]
    rw [hz, mul_zero, map_zero, HahnSeries.orderTop_zero]
    exact le_top
  have ht := le_tOrder_term_twsCoefBoundNeg hw hjn hjd h0
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero twsSeries).mpr ht.1),
    tws_order_twsSeries ht.1, WithTop.coe_le_coe]
  refine le_trans (hG _ ?_) ht.2
  exact exponent_quadratic_twsCoefBoundNeg hγ (Int.natCast_nonneg j) (by omega)

/-- The sum defining `A'_d`, `θ = 1`, converges for an input of order at least
`4 (γ n(n+1) - B (n+1))`, `γ ≥ 0`. -/
private theorem twsSummable_coefSummand_twsCoefBoundNeg {w : ℕ → RatFunc ℚ} {γ B : ℤ}
    (hγ : 0 ≤ γ)
    (hw : ∀ n : ℕ, w n = 0 ∨
      4 * (γ * n * ((n : ℤ) + 1) - B * ((n : ℤ) + 1)) ≤ pairQTOrder (w n)) (d : ℕ) :
    TwsSummable fun n ↦ twsSeries (twsCoefSummand true w d n) := by
  intro g
  refine ⟨(6 * |B| + 2 * (d : ℤ) + 4 * (d : ℤ) ^ 2 + |g| + 1).toNat, fun n hn ↦ ?_⟩
  have hn' : 6 * |B| + 2 * (d : ℤ) + 4 * (d : ℤ) ^ 2 + |g| + 1 ≤ n := Int.toNat_le.mp hn
  by_cases hz : twsSeries (twsCoefSummand true w d n) = 0
  · exact Or.inl hz
  refine Or.inr ?_
  have hle : ((g + 1 : ℤ) : WithTop ℤ) ≤ (twsSeries (twsCoefSummand true w d n)).orderTop := by
    rw [twsCoefSummand, Finset.mul_sum, map_sum]
    refine le_orderTop_sum_twsCoefBoundNeg _ _ _ fun j hj ↦ ?_
    have hj' := Finset.mem_range.mp hj
    by_cases h0 : w n = 0
    · have hz' : twsTerm true w n (d - j) j = 0 := by simp [twsTerm, h0]
      rw [hz', mul_zero, map_zero, HahnSeries.orderTop_zero]
      exact le_top
    have ht := le_tOrder_term_twsCoefBoundNeg hw (n := n) (d := d) (j := j) (by omega)
      (by omega) h0
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero twsSeries).mpr ht.1),
      tws_order_twsSeries ht.1, WithTop.coe_le_coe]
    have := exponent_tendsto_twsCoefBoundNeg (γ := γ) (B := B) (d := d) (n := n) (j := j)
      (g := g) hγ (by omega) (by omega) (by omega) hn'
    linarith [ht.2]
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero hz, WithTop.coe_le_coe] at hle
  exact Int.lt_of_add_one_le hle

/-- Lower bound for the coefficients `A'_d`, `θ = 1`, of an input of order at least
`4 (γ n(n+1) - B (n+1))`, `γ ≥ 0`. -/
theorem tws_bound_coef_one_of_input {w : ℕ → RatFunc ℚ} {γ B : ℤ} (hγ : 0 ≤ γ)
    (hw : ∀ n : ℕ, w n = 0 ∨
      4 * (γ * n * ((n : ℤ) + 1) - B * ((n : ℤ) + 1)) ≤ pairQTOrder (w n)) :
    ∃ C : ℤ, ∀ d : ℕ, twsCoef true w d = 0 ∨
      -((2 * (d : ℤ)) ^ 2 + C * (2 * (d : ℤ)) + C) ≤
        4 * (γ + 1) * (twsCoef true w d).order := by
  refine ⟨4 * (B - γ) ^ 2 + 4 + 2 * (γ + 1) * (2 * B + 1) ^ 2, fun d ↦ ?_⟩
  by_cases hz : twsCoef true w d = 0
  · exact Or.inl hz
  refine Or.inr ?_
  have hD : (0 : ℤ) < 4 * (γ + 1) := by omega
  set K : ℤ := 4 * ((d : ℤ) + B - γ) ^ 2 + 2 * (γ + 1) * (2 * B + 1) ^ 2 with hK
  have hle : ((-(K / (4 * (γ + 1))) : ℤ) : WithTop ℤ) ≤ (twsCoef true w d).orderTop := by
    refine le_orderTop_twsSum (twsSummable_coefSummand_twsCoefBoundNeg hγ hw d) fun n ↦ ?_
    rw [twsCoefSummand, Finset.mul_sum, map_sum]
    refine le_orderTop_sum_twsCoefBoundNeg _ _ _ fun j hj ↦ ?_
    have hj' := Finset.mem_range.mp hj
    refine le_orderTop_term_twsCoefBoundNeg hγ hw (by omega) (by omega) fun x hx ↦ ?_
    have h1 : -x ≤ K / (4 * (γ + 1)) := Int.le_ediv_of_mul_le hD (by linarith)
    omega
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero hz, WithTop.coe_le_coe] at hle
  have h2 : K / (4 * (γ + 1)) * (4 * (γ + 1)) ≤ K := Int.ediv_mul_le K hD.ne'
  have h3 : -K ≤ 4 * (γ + 1) * (twsCoef true w d).order := by nlinarith
  have hd0 : (0 : ℤ) ≤ d := Int.natCast_nonneg d
  have h4 : 0 ≤ (d : ℤ) * ((2 * (B - γ) - 1) ^ 2 + 3 + 2 * (γ + 1) * (2 * B + 1) ^ 2) := by
    positivity
  have h5 : 0 ≤ 2 * (γ + 1) * (2 * B + 1) ^ 2 := by positivity
  rw [hK] at h3
  nlinarith

end AJConjecture
