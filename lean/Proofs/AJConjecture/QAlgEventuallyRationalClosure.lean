import Mathlib
import AJConjecture.QAlgEventuallyRational
import AJConjecture.QAlgOpApplyFieldOreMul

/-!
# The operators with eventually rational image form a left ideal

For a fixed sequence `f`, the set of operators `Q` such that `Q f` is eventually rational
contains the annihilators of the tail of `f` and is stable under subtraction, left
multiplication by a coefficient, and left Ore multiplication by any operator.
-/

open Polynomial

namespace AJConjecture

/-- A sequence that vanishes at all large colours is eventually rational. -/
theorem eventuallyRational_of_forall_ge_eq_zero {g : ℤ → RatFunc ℚ} {n₀ : ℤ}
    (h : ∀ n : ℤ, n₀ ≤ n → g n = 0) : EventuallyRational g :=
  ⟨0, 1, one_ne_zero, n₀, fun n hn ↦ by rw [h n hn, mul_zero, map_zero]⟩

/-- The sum of two eventually rational sequences is eventually rational. -/
private theorem eventuallyRational_add_seq {g₁ g₂ : ℤ → RatFunc ℚ} (h₁ : EventuallyRational g₁)
    (h₂ : EventuallyRational g₂) : EventuallyRational fun n ↦ g₁ n + g₂ n := by
  obtain ⟨a₁, b₁, hb₁, n₁, h₁⟩ := h₁
  obtain ⟨a₂, b₂, hb₂, n₂, h₂⟩ := h₂
  refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, mul_ne_zero hb₁ hb₂, max n₁ n₂, fun n hn ↦ ?_⟩
  have e₁ := h₁ n ((le_max_left n₁ n₂).trans hn)
  have e₂ := h₂ n ((le_max_right n₁ n₂).trans hn)
  rw [map_mul, map_add, map_mul, map_mul, ← e₁, ← e₂]
  ring

/-- The difference of two eventually rational sequences is eventually rational. -/
private theorem eventuallyRational_sub_seq {g₁ g₂ : ℤ → RatFunc ℚ} (h₁ : EventuallyRational g₁)
    (h₂ : EventuallyRational g₂) : EventuallyRational fun n ↦ g₁ n - g₂ n := by
  obtain ⟨a₁, b₁, hb₁, n₁, h₁⟩ := h₁
  obtain ⟨a₂, b₂, hb₂, n₂, h₂⟩ := h₂
  refine ⟨a₁ * b₂ - a₂ * b₁, b₁ * b₂, mul_ne_zero hb₁ hb₂, max n₁ n₂, fun n hn ↦ ?_⟩
  have e₁ := h₁ n ((le_max_left n₁ n₂).trans hn)
  have e₂ := h₂ n ((le_max_right n₁ n₂).trans hn)
  rw [map_mul, map_sub, map_mul, map_mul, ← e₁, ← e₂]
  ring

/-- The image of an eventually rational sequence under a monomial `c L ^ i` is eventually
rational. -/
private theorem eventuallyRational_opApplyField_monomial_seq {g : ℤ → RatFunc ℚ}
    (hg : EventuallyRational g) (i : ℕ) (c : Coeff) :
    EventuallyRational fun n ↦ opApplyField (monomial i c) g n := by
  obtain ⟨a, b, hb, n₀, h⟩ := hg
  have hb' : coeffShift^[i] b ≠ 0 := fun h0 ↦
    hb (coeffShift_injective.iterate i (h0.trans (iterate_map_zero coeffShift i).symm))
  refine ⟨c * coeffShift^[i] a, coeffShift^[i] b, hb', n₀, fun n hn ↦ ?_⟩
  have e := h (n + i) (by omega)
  beta_reduce
  rw [opApplyField_monomial, map_mul, evalAtField_iterate_coeffShift,
    evalAtField_iterate_coeffShift, ← e]
  ring

/-- The image of an eventually rational sequence under a recurrence operator is eventually
rational. -/
private theorem eventuallyRational_opApplyField_seq {g : ℤ → RatFunc ℚ}
    (hg : EventuallyRational g) (S : RecOp) :
    EventuallyRational fun n ↦ opApplyField S g n := by
  induction S using Polynomial.induction_on' with
  | add P P' hP hP' =>
    simp only [opApplyField_add_left]
    exact eventuallyRational_add_seq hP hP'
  | monomial i c => exact eventuallyRational_opApplyField_monomial_seq hg i c

/-- Eventual rationality of the image is stable under subtraction of operators. -/
theorem eventuallyRational_opApplyField_sub {f : ℤ → RatFunc ℚ} {P Q : RecOp}
    (hP : EventuallyRational fun n ↦ opApplyField P f n)
    (hQ : EventuallyRational fun n ↦ opApplyField Q f n) :
    EventuallyRational fun n ↦ opApplyField (P - Q) f n := by
  simp only [opApplyField_sub_left]
  exact eventuallyRational_sub_seq hP hQ

/-- Eventual rationality of the image is stable under left multiplication by a coefficient. -/
theorem eventuallyRational_opApplyField_C_mul {f : ℤ → RatFunc ℚ} {Q : RecOp}
    (hQ : EventuallyRational fun n ↦ opApplyField Q f n) (c : Coeff) :
    EventuallyRational fun n ↦ opApplyField (C c * Q) f n := by
  obtain ⟨a, b, hb, n₀, h⟩ := hQ
  refine ⟨c * a, b, hb, n₀, fun n hn ↦ ?_⟩
  have e := h n hn
  beta_reduce at e ⊢
  rw [opApplyField_C_mul_left, map_mul, ← e]
  ring

/-- Eventual rationality of the image is stable under left Ore multiplication. -/
theorem eventuallyRational_opApplyField_oreMul {f : ℤ → RatFunc ℚ} {Q : RecOp}
    (hQ : EventuallyRational fun n ↦ opApplyField Q f n) (S : RecOp) :
    EventuallyRational fun n ↦ opApplyField (oreMul coeffShift S Q) f n := by
  simp only [opApplyField_oreMul]
  exact eventuallyRational_opApplyField_seq hQ S

end AJConjecture
