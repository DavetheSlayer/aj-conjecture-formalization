import Mathlib
import AJConjecture.QAlgOreMul

/-!
# The Ore product: monomials, additivity, constants

The Ore product is biadditive, multiplies monomials by the twisted rule, has `1` as a two-sided
unit, and left multiplication by a constant is the ordinary product by that constant.
-/

open Polynomial

namespace AJConjecture

/-- The Ore product of two monomials. -/
theorem oreMul_monomial_monomial {A : Type*} [Semiring A] (σ : A →+* A) (i k : ℕ) (a b : A) :
    oreMul σ (monomial i a) (monomial k b) = monomial (i + k) (a * σ^[i] b) := by
  unfold oreMul
  rw [Polynomial.sum_monomial_index, Polynomial.sum_monomial_index]
  · simp [iterate_map_zero]
  · simp [Polynomial.sum_def]

/-- The Ore product is additive in its left argument. -/
theorem oreMul_add_left {A : Type*} [Semiring A] (σ : A →+* A) (P P' Q : A[X]) :
    oreMul σ (P + P') Q = oreMul σ P Q + oreMul σ P' Q := by
  unfold oreMul
  refine Polynomial.sum_add_index P P' _ (fun i ↦ ?_) (fun i a a' ↦ ?_)
  · simp [Polynomial.sum_def]
  · simp only [add_mul, map_add, Polynomial.sum_def, Finset.sum_add_distrib]

/-- The Ore product is additive in its right argument. -/
theorem oreMul_add_right {A : Type*} [Semiring A] (σ : A →+* A) (P Q Q' : A[X]) :
    oreMul σ P (Q + Q') = oreMul σ P Q + oreMul σ P Q' := by
  unfold oreMul
  rw [← Polynomial.sum_add]
  congr 1
  funext i a
  refine Polynomial.sum_add_index Q Q' _ (fun k ↦ ?_) (fun k b b' ↦ ?_)
  · simp [iterate_map_zero]
  · simp only [iterate_map_add, mul_add, map_add]

/-- Left Ore multiplication by a constant is the ordinary product by that constant. -/
theorem oreMul_C_left {A : Type*} [Semiring A] (σ : A →+* A) (c : A) (P : A[X]) :
    oreMul σ (C c) P = C c * P := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [oreMul_add_right, hp, hq, mul_add]
  | monomial n a =>
    rw [← Polynomial.monomial_zero_left, oreMul_monomial_monomial, Function.iterate_zero, id,
      Polynomial.monomial_mul_monomial]

/-- `1` is a left unit of the Ore product. -/
theorem oreMul_one_left {A : Type*} [Semiring A] (σ : A →+* A) (P : A[X]) :
    oreMul σ 1 P = P := by
  rw [← Polynomial.C_1, oreMul_C_left, Polynomial.C_1, one_mul]

end AJConjecture
