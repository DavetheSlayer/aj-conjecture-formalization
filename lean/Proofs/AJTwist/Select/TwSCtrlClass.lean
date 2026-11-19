import Mathlib
import AJTwist.Select.TwSCtrlClosure

/-!
# The classes of controlled expansions are growth classes

Source: Section 6.4 of `selection.tex` (revision 5), "Bounds after rational multiplication":
fixed shifts incur a linear loss in the coefficient orders, finite sums can only raise the
minimum order, and multiplication by a monomial moves the index by a constant; so the quadratic
coefficient `1 / D` of the bound `D · ord_t c_j ≥ -(j² + O(j))` is preserved.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The expansion of a sequence vanishing on a tail. -/
private theorem twsCtrl_series_zero_tail_ctrlClass {g : ℤ → RatFunc ℚ} {n₀ : ℤ}
    (h : ∀ n : ℤ, n₀ ≤ n → g n = 0) : TwsCtrl (fun _ ↦ 0) fun n ↦ twsSeries (g n) :=
  twsCtrl_zero_tail (n₀ := n₀) fun n hn ↦ by simp only [h n hn, map_zero]

/-- The expansion of a difference of sequences of rational functions. -/
private theorem twsCtrl_series_sub_ctrlClass {c₁ c₂ : ℤ → LaurentSeries ℚ}
    {g₁ g₂ : ℤ → RatFunc ℚ} (h₁ : TwsCtrl c₁ fun n ↦ twsSeries (g₁ n))
    (h₂ : TwsCtrl c₂ fun n ↦ twsSeries (g₂ n)) :
    TwsCtrl (fun j ↦ c₁ j - c₂ j) fun n ↦ twsSeries (g₁ n - g₂ n) := by
  have e : (fun n ↦ twsSeries (g₁ n - g₂ n)) = fun n ↦ twsSeries (g₁ n) - twsSeries (g₂ n) :=
    funext fun n ↦ map_sub _ _ _
  rw [e]
  exact twsCtrl_sub h₁ h₂

/-- The expansion of a monomial multiple of a sequence of rational functions. -/
private theorem twsCtrl_series_monomial_ctrlClass {c : ℤ → LaurentSeries ℚ}
    {g : ℤ → RatFunc ℚ} (h : TwsCtrl c fun n ↦ twsSeries (g n)) (i j : ℤ) :
    TwsCtrl (fun k ↦ twsT i * c (k - j))
      fun n ↦ twsSeries ((RatFunc.X : RatFunc ℚ) ^ (i + 2 * n * j) * g n) := by
  have e : (fun n ↦ twsSeries ((RatFunc.X : RatFunc ℚ) ^ (i + 2 * n * j) * g n)) =
      fun n ↦ twsT (i + 2 * n * j) * twsSeries (g n) :=
    funext fun n ↦ by rw [map_mul, twsSeries_X_zpow]
  rw [e]
  exact twsCtrl_monomial h i j

/-- The order of a monomial multiple. -/
private theorem order_twsT_mul_ctrlClass (k : ℤ) {x : LaurentSeries ℚ} (hx : x ≠ 0) :
    (twsT k * x).order = k + x.order := by
  have hT : twsT k ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  rw [HahnSeries.order_mul hT hx, twsT, HahnSeries.order_single one_ne_zero]

/-- A lower bound for the orders of two series is one for their difference. -/
private theorem order_sub_bound_ctrlClass {x y : LaurentSeries ℚ} {b : ℤ} (D : ℕ)
    (hx : x = 0 ∨ b ≤ (D : ℤ) * x.order) (hy : y = 0 ∨ b ≤ (D : ℤ) * y.order) :
    x - y = 0 ∨ b ≤ (D : ℤ) * (x - y).order := by
  by_cases hxy : x - y = 0
  · exact Or.inl hxy
  refine Or.inr ?_
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · exact absurd (sub_zero _) hxy
    · rwa [zero_sub, HahnSeries.order_neg]
  rcases hy with rfl | hy
  · rwa [sub_zero]
  have hm := HahnSeries.min_order_le_order_add (x := x) (y := -y) (by rwa [← sub_eq_add_neg])
  rw [HahnSeries.order_neg, ← sub_eq_add_neg] at hm
  have hD : (0 : ℤ) ≤ D := Nat.cast_nonneg D
  rcases min_le_iff.mp hm with h | h
  · exact le_trans hx (mul_le_mul_of_nonneg_left h hD)
  · exact le_trans hy (mul_le_mul_of_nonneg_left h hD)

/-- The coefficient bound is weaker for a larger constant. -/
private theorem coeff_bound_mono_ctrlClass {x : LaurentSeries ℚ} {D : ℕ} {C C' j : ℤ}
    (hC : C ≤ C') (h : x = 0 ∨ -(j ^ 2 + C * |j| + C) ≤ (D : ℤ) * x.order) :
    x = 0 ∨ -(j ^ 2 + C' * |j| + C') ≤ (D : ℤ) * x.order := by
  refine h.imp_right fun h ↦ le_trans ?_ h
  have h1 := mul_le_mul_of_nonneg_right hC (abs_nonneg j)
  linarith

/-- The coefficient bounds of a difference. -/
private theorem coeff_bound_sub_ctrlClass {c₁ c₂ : ℤ → LaurentSeries ℚ} {D : ℕ}
    (h₁ : ∃ C : ℤ, ∀ j : ℤ, c₁ j = 0 ∨ -(j ^ 2 + C * |j| + C) ≤ (D : ℤ) * (c₁ j).order)
    (h₂ : ∃ C : ℤ, ∀ j : ℤ, c₂ j = 0 ∨ -(j ^ 2 + C * |j| + C) ≤ (D : ℤ) * (c₂ j).order) :
    ∃ C : ℤ, ∀ j : ℤ, c₁ j - c₂ j = 0 ∨
      -(j ^ 2 + C * |j| + C) ≤ (D : ℤ) * (c₁ j - c₂ j).order := by
  obtain ⟨C₁, h₁⟩ := h₁
  obtain ⟨C₂, h₂⟩ := h₂
  exact ⟨max C₁ C₂, fun j ↦ order_sub_bound_ctrlClass D
    (coeff_bound_mono_ctrlClass (le_max_left _ _) (h₁ j))
    (coeff_bound_mono_ctrlClass (le_max_right _ _) (h₂ j))⟩

/-- The coefficient bounds of a monomial multiple. -/
private theorem coeff_bound_monomial_ctrlClass {c : ℤ → LaurentSeries ℚ} {D : ℕ}
    (h : ∃ C : ℤ, ∀ j : ℤ, c j = 0 ∨ -(j ^ 2 + C * |j| + C) ≤ (D : ℤ) * (c j).order)
    (i j : ℤ) :
    ∃ C : ℤ, ∀ k : ℤ, twsT i * c (k - j) = 0 ∨
      -(k ^ 2 + C * |k| + C) ≤ (D : ℤ) * (twsT i * c (k - j)).order := by
  obtain ⟨C, h⟩ := h
  refine ⟨2 * |j| + |C| + j ^ 2 + |C| * |j| + D * |i|, fun k ↦ ?_⟩
  rcases h (k - j) with h0 | hb
  · exact Or.inl (by rw [h0, mul_zero])
  by_cases h0 : c (k - j) = 0
  · exact Or.inl (by rw [h0, mul_zero])
  refine Or.inr ?_
  rw [order_twsT_mul_ctrlClass i h0]
  have hD : (0 : ℤ) ≤ D := Nat.cast_nonneg D
  have ha := abs_nonneg k
  have hb' := abs_nonneg j
  have he := abs_nonneg C
  have hf := abs_nonneg i
  have h1 : (k - j) ^ 2 ≤ k ^ 2 + 2 * |k| * |j| + j ^ 2 := by
    have := neg_abs_le (k * j)
    rw [abs_mul] at this
    nlinarith
  have h2 : C * |k - j| ≤ |C| * (|k| + |j|) :=
    mul_le_mul (le_abs_self C) (abs_sub k j) (abs_nonneg _) he
  have h3 : -((D : ℤ) * |i|) ≤ D * i := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le i) hD
    linarith
  have h4 := le_abs_self C
  have h5 : 0 ≤ j ^ 2 * |k| := mul_nonneg (sq_nonneg j) ha
  have h6 : 0 ≤ |C| * |j| * |k| := mul_nonneg (mul_nonneg he hb') ha
  have h7 : 0 ≤ (D : ℤ) * |i| * |k| := mul_nonneg (mul_nonneg hD hf) ha
  linarith

/-- The coefficient bounds after a shift of the colour. -/
private theorem coeff_bound_shift_ctrlClass {c : ℤ → LaurentSeries ℚ} {D : ℕ}
    (h : ∃ C : ℤ, ∀ j : ℤ, c j = 0 ∨ -(j ^ 2 + C * |j| + C) ≤ (D : ℤ) * (c j).order) :
    ∃ C : ℤ, ∀ j : ℤ, twsT (2 * j) * c j = 0 ∨
      -(j ^ 2 + C * |j| + C) ≤ (D : ℤ) * (twsT (2 * j) * c j).order := by
  obtain ⟨C, h⟩ := h
  refine ⟨C + 2 * D, fun j ↦ ?_⟩
  rcases h j with h0 | hb
  · exact Or.inl (by rw [h0, mul_zero])
  by_cases h0 : c j = 0
  · exact Or.inl (by rw [h0, mul_zero])
  refine Or.inr ?_
  rw [order_twsT_mul_ctrlClass (2 * j) h0]
  have hD : (0 : ℤ) ≤ D := Nat.cast_nonneg D
  have h3 := mul_le_mul_of_nonneg_left (neg_abs_le j) hD
  have ha := abs_nonneg j
  nlinarith

/-- The sequences with a controlled expansion form a growth class. -/
theorem twsCtrlAll_growthClass : TwsGrowthClass TwsCtrlAll where
  zero_tail h := ⟨_, twsCtrl_series_zero_tail_ctrlClass h⟩
  sub := fun ⟨_, h₁⟩ ⟨_, h₂⟩ ↦ ⟨_, twsCtrl_series_sub_ctrlClass h₁ h₂⟩
  monomial i j := fun ⟨_, h⟩ ↦ ⟨_, twsCtrl_series_monomial_ctrlClass h i j⟩
  shift := fun ⟨_, h⟩ ↦ ⟨_, twsCtrl_shift h⟩

/-- The sequences with a controlled expansion whose coefficients have order at least
`-(j² + O(j)) / D` form a growth class. -/
theorem twsCtrlB_growthClass (D : ℕ) : TwsGrowthClass (TwsCtrlB D) where
  zero_tail h := ⟨_, twsCtrl_series_zero_tail_ctrlClass h, 0, fun _ ↦ Or.inl rfl⟩
  sub := fun ⟨_, h₁, b₁⟩ ⟨_, h₂, b₂⟩ ↦
    ⟨_, twsCtrl_series_sub_ctrlClass h₁ h₂, coeff_bound_sub_ctrlClass b₁ b₂⟩
  monomial i j := fun ⟨_, h, b⟩ ↦
    ⟨_, twsCtrl_series_monomial_ctrlClass h i j, coeff_bound_monomial_ctrlClass b i j⟩
  shift := fun ⟨_, h, b⟩ ↦ ⟨_, twsCtrl_shift h, coeff_bound_shift_ctrlClass b⟩

end AJConjecture
