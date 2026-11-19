import Mathlib
import AJTwist.Select.TwSCtrlClosure

/-!
# Controlled expansions: multiplication by a coefficient

Source: Section 6.4 of `selection.tex` (revision 5), "Rational coefficients and shifts". For a
polynomial coefficient `κ(t, M) = ∑_j κ_j(t) M^j` the product of `κ(t, t^(2n))` with a sequence
having the controlled expansion `∑ c_k M^k` has the controlled expansion with the convolution
coefficients `∑_j κ_j c_(k-j)` (a finite sum; no Taylor remainder is needed for polynomial
coefficients, and division is handled by `tws_bound_of_twsConv`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The expansion in `ℚ((t))` of the coefficient of `M^j` of `κ ∈ ℤ[t][M]`. -/
def twsCoeffT (κ : Coeff) (j : ℕ) : LaurentSeries ℚ :=
  twsSeries (Polynomial.eval₂ (Int.castRingHom (RatFunc ℚ)) RatFunc.X (κ.coeff j))

/-- The convolution coefficients `∑_j κ_j c_(k-j)` of the product of `κ(t, M)` with the expansion
`∑ c_k M^k`. -/
def twsConv (κ : Coeff) (c : ℤ → LaurentSeries ℚ) (k : ℤ) : LaurentSeries ℚ :=
  ∑ j ∈ Finset.range (κ.natDegree + 1), twsCoeffT κ j * c (k - j)

/-- The evaluated coefficient is the finite sum of its monomials. -/
theorem twsSeries_evalAtField_ctrlMul (κ : Coeff) (n : ℤ) :
    twsSeries (evalAtField n κ) =
      ∑ j ∈ Finset.range (κ.natDegree + 1), twsCoeffT κ j * twsT (2 * n * j) := by
  have h : evalAtField n κ = ∑ j ∈ Finset.range (κ.natDegree + 1),
      Polynomial.eval₂ (Int.castRingHom (RatFunc ℚ)) RatFunc.X (κ.coeff j) *
        (RatFunc.X : RatFunc ℚ) ^ (2 * n * j) := by
    rw [evalAtField, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Polynomial.coe_eval₂RingHom, ← zpow_natCast, ← zpow_mul]
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, twsSeries_X_zpow, twsCoeffT]

/-- Multiplication of a controlled expansion by a fixed series. -/
theorem twsCtrl_const_mul_ctrlMul {c : ℤ → LaurentSeries ℚ} {g : ℤ → LaurentSeries ℚ}
    (h : TwsCtrl c g) (a : LaurentSeries ℚ) :
    TwsCtrl (fun k ↦ a * c k) (fun n ↦ a * g n) := by
  obtain ⟨j₀, h₀, hJ⟩ := h
  refine ⟨j₀, fun k hk ↦ by simp only [h₀ k hk, mul_zero], fun J ↦ ?_⟩
  obtain ⟨C, n₀, hC⟩ := hJ J
  refine ⟨C - a.order, n₀, fun n hn ↦ ?_⟩
  have e : a * g n - ∑ k ∈ Finset.Ico j₀ J, a * c k * twsT (2 * n * k) =
      a * (g n - ∑ k ∈ Finset.Ico j₀ J, c k * twsT (2 * n * k)) := by
    rw [mul_sub, Finset.mul_sum]
    simp only [mul_assoc]
  rw [e]
  by_cases ha : a = 0
  · rw [ha, zero_mul, HahnSeries.orderTop_zero]
    exact le_top
  rw [HahnSeries.orderTop_mul, ← HahnSeries.order_eq_orderTop_of_ne_zero ha]
  have h3 : 2 * J * n - (C - a.order) = a.order + (2 * J * n - C) := by ring
  rw [h3, WithTop.coe_add]
  exact add_le_add le_rfl (hC n hn)

/-- The sum of two controlled expansions. -/
theorem twsCtrl_add_ctrlMul {c₁ c₂ : ℤ → LaurentSeries ℚ} {g₁ g₂ : ℤ → LaurentSeries ℚ}
    (h₁ : TwsCtrl c₁ g₁) (h₂ : TwsCtrl c₂ g₂) :
    TwsCtrl (fun j ↦ c₁ j + c₂ j) (fun n ↦ g₁ n + g₂ n) := by
  have h0 : TwsCtrl (fun _ ↦ 0) (fun _ : ℤ ↦ (0 : LaurentSeries ℚ)) :=
    twsCtrl_zero_tail (n₀ := 0) fun _ _ ↦ rfl
  have h := twsCtrl_sub h₁ (twsCtrl_sub h0 h₂)
  simp only [zero_sub, sub_neg_eq_add] at h
  exact h

/-- A finite sum of controlled expansions. -/
theorem twsCtrl_sum_ctrlMul {ι : Type*} (S : Finset ι) {c : ι → ℤ → LaurentSeries ℚ}
    {g : ι → ℤ → LaurentSeries ℚ} (h : ∀ i ∈ S, TwsCtrl (c i) (g i)) :
    TwsCtrl (fun k ↦ ∑ i ∈ S, c i k) (fun n ↦ ∑ i ∈ S, g i n) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact twsCtrl_zero_tail (n₀ := 0) fun _ _ ↦ rfl
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact twsCtrl_add_ctrlMul (h a (Finset.mem_insert_self a S))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- The product of an evaluated coefficient with a sequence having a controlled expansion has
the convolution expansion. -/
theorem twsCtrl_coeff_mul {c : ℤ → LaurentSeries ℚ} {g : ℤ → LaurentSeries ℚ} (h : TwsCtrl c g)
    (κ : Coeff) : TwsCtrl (twsConv κ c) (fun n ↦ twsSeries (evalAtField n κ) * g n) := by
  have hT : twsT 0 = 1 := rfl
  have hs := twsCtrl_sum_ctrlMul (Finset.range (κ.natDegree + 1))
    (c := fun (j : ℕ) (k : ℤ) ↦ twsCoeffT κ j * (twsT 0 * c (k - j)))
    (g := fun (j : ℕ) (n : ℤ) ↦ twsCoeffT κ j * (twsT (0 + 2 * n * j) * g n))
    fun j _ ↦ twsCtrl_const_mul_ctrlMul (twsCtrl_monomial h 0 j) (twsCoeffT κ j)
  have e₁ : (fun k : ℤ ↦ ∑ j ∈ Finset.range (κ.natDegree + 1),
      twsCoeffT κ j * (twsT 0 * c (k - j))) = twsConv κ c := by
    funext k
    simp only [hT, one_mul, twsConv]
  have e₂ : (fun n : ℤ ↦ ∑ j ∈ Finset.range (κ.natDegree + 1),
      twsCoeffT κ j * (twsT (0 + 2 * n * j) * g n)) =
      fun n ↦ twsSeries (evalAtField n κ) * g n := by
    funext n
    rw [twsSeries_evalAtField_ctrlMul, Finset.sum_mul]
    simp only [zero_add, mul_assoc]
  rw [e₁, e₂] at hs
  exact hs

end AJConjecture
