import Mathlib
import AJTwist.Select.TwSCtrlDefs

/-!
# Closure of controlled expansions under the Ore operations

Source: Section 6.4 of `selection.tex` (revision 5), "Rational coefficients and shifts": a fixed
shift multiplies the coefficient of `M^j` by a power of `t`, and multiplication by a monomial
`t^i M^j` shifts the coefficients. Here the operations are those of a growth class
(`TwsGrowthClass`), with the explicit coefficients of the image.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The product of two monomials. -/
private theorem twsT_mul_twsT_ctrlClosure (a b : ℤ) : twsT a * twsT b = twsT (a + b) := by
  rw [twsT, twsT, twsT, HahnSeries.single_mul_single, mul_one]

/-- A lower bound for the order of a product with a monomial. -/
private theorem le_orderTop_twsT_mul_ctrlClosure {x : LaurentSeries ℚ} {a : ℤ}
    (h : (a : WithTop ℤ) ≤ x.orderTop) (k : ℤ) :
    ((k + a : ℤ) : WithTop ℤ) ≤ (twsT k * x).orderTop := by
  rw [HahnSeries.orderTop_mul, twsT, HahnSeries.orderTop_single one_ne_zero, WithTop.coe_add]
  exact add_le_add le_rfl h

/-- The lower end of a truncated sum may be moved down. -/
private theorem sum_Ico_eq_of_le_ctrlClosure {c : ℤ → LaurentSeries ℚ} {j₀ j₁ : ℤ}
    (h₀ : ∀ j : ℤ, j < j₀ → c j = 0) (hle : j₁ ≤ j₀) (J : ℤ) (x : ℤ → LaurentSeries ℚ) :
    ∑ j ∈ Finset.Ico j₀ J, c j * x j = ∑ j ∈ Finset.Ico j₁ J, c j * x j := by
  refine Finset.sum_subset (Finset.Ico_subset_Ico_left hle) fun j hj hj' ↦ ?_
  rw [Finset.mem_Ico] at hj hj'
  rw [h₀ j (by lia), zero_mul]

/-- The truncated sums do not depend on the degree below which the coefficients vanish. -/
private theorem sum_Ico_rebase_ctrlClosure {c : ℤ → LaurentSeries ℚ} {j₀ j₁ : ℤ}
    (h₀ : ∀ j : ℤ, j < j₀ → c j = 0) (h₁ : ∀ j : ℤ, j < j₁ → c j = 0) (J : ℤ)
    (x : ℤ → LaurentSeries ℚ) :
    ∑ j ∈ Finset.Ico j₀ J, c j * x j = ∑ j ∈ Finset.Ico j₁ J, c j * x j := by
  rw [sum_Ico_eq_of_le_ctrlClosure h₀ (min_le_left j₀ j₁),
    sum_Ico_eq_of_le_ctrlClosure h₁ (min_le_right j₀ j₁)]

/-- The remainder estimates of a controlled expansion, with the truncated sums starting at any
degree below which the coefficients vanish. -/
private theorem twsCtrl_bound_of_vanish_ctrlClosure {c : ℤ → LaurentSeries ℚ}
    {g : ℤ → LaurentSeries ℚ} (h : TwsCtrl c g) {j₁ : ℤ} (h₁ : ∀ j : ℤ, j < j₁ → c j = 0)
    (J : ℤ) :
    ∃ C n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ((2 * J * n - C : ℤ) : WithTop ℤ) ≤
      (g n - ∑ j ∈ Finset.Ico j₁ J, c j * twsT (2 * n * j)).orderTop := by
  obtain ⟨j₀, h₀, hJ⟩ := h
  obtain ⟨C, n₀, hC⟩ := hJ J
  refine ⟨C, n₀, fun n hn ↦ ?_⟩
  rw [sum_Ico_rebase_ctrlClosure h₁ h₀]
  exact hC n hn

/-- A sequence vanishing on a tail has the zero expansion. -/
theorem twsCtrl_zero_tail {g : ℤ → LaurentSeries ℚ} {n₀ : ℤ} (h : ∀ n : ℤ, n₀ ≤ n → g n = 0) :
    TwsCtrl (fun _ ↦ 0) g := by
  refine ⟨0, fun _ _ ↦ rfl, fun J ↦ ⟨0, n₀, fun n hn ↦ ?_⟩⟩
  rw [h n hn]
  simp

/-- A controlled expansion of a sequence is one of every sequence equal to it on a tail. -/
theorem twsCtrl_congr_tail {c : ℤ → LaurentSeries ℚ} {g₁ g₂ : ℤ → LaurentSeries ℚ}
    (h : TwsCtrl c g₁) {n₀ : ℤ} (heq : ∀ n : ℤ, n₀ ≤ n → g₁ n = g₂ n) : TwsCtrl c g₂ := by
  obtain ⟨j₀, h₀, hJ⟩ := h
  refine ⟨j₀, h₀, fun J ↦ ?_⟩
  obtain ⟨C, n₁, hC⟩ := hJ J
  refine ⟨C, max n₀ n₁, fun n hn ↦ ?_⟩
  rw [← heq n (le_trans (le_max_left _ _) hn)]
  exact hC n (le_trans (le_max_right _ _) hn)

/-- The difference of two controlled expansions. -/
theorem twsCtrl_sub {c₁ c₂ : ℤ → LaurentSeries ℚ} {g₁ g₂ : ℤ → LaurentSeries ℚ}
    (h₁ : TwsCtrl c₁ g₁) (h₂ : TwsCtrl c₂ g₂) :
    TwsCtrl (fun j ↦ c₁ j - c₂ j) (fun n ↦ g₁ n - g₂ n) := by
  obtain ⟨j₁, hj₁, -⟩ := id h₁
  obtain ⟨j₂, hj₂, -⟩ := id h₂
  have hm₁ : ∀ j : ℤ, j < min j₁ j₂ → c₁ j = 0 := fun j hj ↦
    hj₁ j (lt_of_lt_of_le hj (min_le_left _ _))
  have hm₂ : ∀ j : ℤ, j < min j₁ j₂ → c₂ j = 0 := fun j hj ↦
    hj₂ j (lt_of_lt_of_le hj (min_le_right _ _))
  refine ⟨min j₁ j₂, fun j hj ↦ by simp only [hm₁ j hj, hm₂ j hj, sub_zero],
    fun J ↦ ?_⟩
  obtain ⟨C₁, n₁, hC₁⟩ := twsCtrl_bound_of_vanish_ctrlClosure h₁ hm₁ J
  obtain ⟨C₂, n₂, hC₂⟩ := twsCtrl_bound_of_vanish_ctrlClosure h₂ hm₂ J
  refine ⟨max C₁ C₂, max n₁ n₂, fun n hn ↦ ?_⟩
  have e : g₁ n - g₂ n - ∑ j ∈ Finset.Ico (min j₁ j₂) J, (c₁ j - c₂ j) * twsT (2 * n * j) =
      (g₁ n - ∑ j ∈ Finset.Ico (min j₁ j₂) J, c₁ j * twsT (2 * n * j)) -
        (g₂ n - ∑ j ∈ Finset.Ico (min j₁ j₂) J, c₂ j * twsT (2 * n * j)) := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    abel
  rw [e]
  refine le_trans (le_min ?_ ?_) HahnSeries.min_orderTop_le_orderTop_sub
  · exact le_trans (WithTop.coe_le_coe.mpr (by have := le_max_left C₁ C₂; lia))
      (hC₁ n (le_trans (le_max_left _ _) hn))
  · exact le_trans (WithTop.coe_le_coe.mpr (by have := le_max_right C₁ C₂; lia))
      (hC₂ n (le_trans (le_max_right _ _) hn))

/-- Multiplication by `t^i M^j` at `M = t^(2n)`: the coefficients are shifted by `j` and
multiplied by `t^i`. -/
theorem twsCtrl_monomial {c : ℤ → LaurentSeries ℚ} {g : ℤ → LaurentSeries ℚ} (h : TwsCtrl c g)
    (i j : ℤ) :
    TwsCtrl (fun k ↦ twsT i * c (k - j)) (fun n ↦ twsT (i + 2 * n * j) * g n) := by
  obtain ⟨j₀, h₀, hJ⟩ := h
  refine ⟨j₀ + j, fun k hk ↦ by simp only [h₀ (k - j) (by lia), mul_zero], fun J ↦ ?_⟩
  obtain ⟨C, n₀, hC⟩ := hJ (J - j)
  refine ⟨C - i, n₀, fun n hn ↦ ?_⟩
  have e : twsT (i + 2 * n * j) * g n -
      ∑ k ∈ Finset.Ico (j₀ + j) J, twsT i * c (k - j) * twsT (2 * n * k) =
      twsT (i + 2 * n * j) *
        (g n - ∑ k ∈ Finset.Ico j₀ (J - j), c k * twsT (2 * n * k)) := by
    have hJ' : J = J - j + j := by ring
    rw [mul_sub, Finset.mul_sum]
    conv_lhs => rw [hJ', ← Finset.sum_Ico_add']
    refine congrArg _ (Finset.sum_congr rfl fun k _ ↦ ?_)
    rw [add_sub_cancel_right, ← twsT_mul_twsT_ctrlClosure i (2 * n * j), mul_add,
      ← twsT_mul_twsT_ctrlClosure (2 * n * k) (2 * n * j)]
    ring
  rw [e]
  have h2 := le_orderTop_twsT_mul_ctrlClosure (hC n hn) (i + 2 * n * j)
  have h3 : 2 * J * n - (C - i) = i + 2 * n * j + (2 * (J - j) * n - C) := by ring
  rw [h3]
  exact h2

/-- The shift of the colour multiplies the coefficient of `M^j` by `t^(2j)`. -/
theorem twsCtrl_shift {c : ℤ → LaurentSeries ℚ} {g : ℤ → LaurentSeries ℚ} (h : TwsCtrl c g) :
    TwsCtrl (fun j ↦ twsT (2 * j) * c j) (fun n ↦ g (n + 1)) := by
  obtain ⟨j₀, h₀, hJ⟩ := h
  refine ⟨j₀, fun k hk ↦ by simp only [h₀ k hk, mul_zero], fun J ↦ ?_⟩
  obtain ⟨C, n₀, hC⟩ := hJ J
  refine ⟨C - 2 * J, n₀, fun n hn ↦ ?_⟩
  have e : ∑ k ∈ Finset.Ico j₀ J, twsT (2 * k) * c k * twsT (2 * n * k) =
      ∑ k ∈ Finset.Ico j₀ J, c k * twsT (2 * (n + 1) * k) := by
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hk : 2 * (n + 1) * k = 2 * k + 2 * n * k := by ring
    rw [hk, ← twsT_mul_twsT_ctrlClosure]
    ring
  have h3 : 2 * J * n - (C - 2 * J) = 2 * J * (n + 1) - C := by ring
  rw [e, h3]
  exact hC (n + 1) (by lia)

end AJConjecture
