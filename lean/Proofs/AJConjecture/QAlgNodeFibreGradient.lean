import Mathlib
import AJConjecture.QAlgInnerDerivativeBasic

/-!
# The gradient of a multiple at a zero of the divisor

Let `u L^n F = G Q` in `k[M][L]` with `u(m₀) ≠ 0`, `l₀ ≠ 0` and `G(m₀, l₀) = 0`. Then
`F(m₀, l₀) = 0` and the gradient of `F` at `(m₀, l₀)` is `λ` times the gradient of `G`, with
`λ = Q(m₀, l₀) / (u(m₀) l₀^n)`.

Proof. The value at `(m₀, l₀)` of `p ∈ k[M][L]` is `(p.map (evalRingHom m₀)).eval l₀`, a ring
homomorphism in `p`. Evaluate the equation, its `L`-derivative (`Polynomial.derivative_mul`,
`Polynomial.derivative_map`) and its `M`-derivative (`innerDerivative_mul`,
`innerDerivative_C`, `innerDerivative (X^n) = 0`): the terms containing `F(m₀, l₀)` or
`G(m₀, l₀)` vanish and `u(m₀) l₀^n ≠ 0` can be divided out.
-/

open Polynomial

namespace AJConjecture

/-- The inner derivative of a power of the outer variable vanishes. -/
private theorem innerDerivative_X_pow_fibreGradient {A : Type*} [CommSemiring A] (n : ℕ) :
    innerDerivative (X ^ n : A[X][X]) = 0 := by
  rw [← monomial_one_right_eq_X_pow, innerDerivative, sum_monomial_index]
  · rw [derivative_one, monomial_zero_right]
  · rw [derivative_zero, monomial_zero_right]

/-- If `u L^n F = G Q` with `u(m₀) l₀ ≠ 0` and `G(m₀, l₀) = 0`, then `F(m₀, l₀) = 0` and the
gradient of `F` at `(m₀, l₀)` is proportional to that of `G`. -/
theorem exists_gradient_eq_mul_of_local_dvd {k : Type*} [Field k] {m₀ l₀ : k} {u : k[X]}
    {n : ℕ} {F G Q : k[X][X]} (hu : u.eval m₀ ≠ 0) (hl₀ : l₀ ≠ 0)
    (h : C u * X ^ n * F = G * Q) (hG : (G.map (Polynomial.evalRingHom m₀)).eval l₀ = 0) :
    ∃ lam : k, (F.map (Polynomial.evalRingHom m₀)).eval l₀ = 0 ∧
      (derivative (F.map (Polynomial.evalRingHom m₀))).eval l₀ =
        lam * (derivative (G.map (Polynomial.evalRingHom m₀))).eval l₀ ∧
      ((innerDerivative F).map (Polynomial.evalRingHom m₀)).eval l₀ =
        lam * ((innerDerivative G).map (Polynomial.evalRingHom m₀)).eval l₀ := by
  set ev : k[X][X] →+* k :=
    (Polynomial.evalRingHom l₀).comp (Polynomial.mapRingHom (Polynomial.evalRingHom m₀))
  have hevdef : ∀ p : k[X][X], (p.map (Polynomial.evalRingHom m₀)).eval l₀ = ev p := fun p ↦ rfl
  have hC : ∀ c : k[X], ev (C c) = c.eval m₀ := fun c ↦ by
    rw [← hevdef, Polynomial.map_C, eval_C, coe_evalRingHom]
  have hX : ev X = l₀ := by rw [← hevdef, Polynomial.map_X, eval_X]
  rw [derivative_map, derivative_map]
  simp only [hevdef] at hG ⊢
  have hne : u.eval m₀ * l₀ ^ n ≠ 0 := mul_ne_zero hu (pow_ne_zero n hl₀)
  have h0 := congrArg ev h
  simp only [map_mul, map_pow, hC, hX, hG, zero_mul] at h0
  have hF0 : ev F = 0 := (mul_eq_zero.mp h0).resolve_left hne
  have h1 := congrArg (fun p ↦ ev (derivative p)) h
  simp only [derivative_mul, map_add, map_mul, map_pow, hC, hX, hG, hF0, zero_mul, mul_zero,
    zero_add, add_zero] at h1
  have h2 := congrArg (fun p ↦ ev (innerDerivative p)) h
  simp only [innerDerivative_mul, innerDerivative_C, innerDerivative_X_pow_fibreGradient,
    map_add, map_mul, map_pow, hC, hX, hG, hF0, zero_mul, mul_zero, zero_add,
    add_zero] at h2
  refine ⟨ev Q / (u.eval m₀ * l₀ ^ n), hF0, ?_, ?_⟩
  · field_simp
    linear_combination h1
  · field_simp
    linear_combination h2

end AJConjecture
