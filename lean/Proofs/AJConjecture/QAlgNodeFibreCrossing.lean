import Mathlib

/-!
# One-variable facts at a double root of a product (fibre fact 3)

* If `u B A = v G D T` in `k[L]` and `l₀` is a root of `A, B, G, D`, then
  `u B'(l₀) A'(l₀) = v G'(l₀) D'(l₀) T(l₀)`: write each of the four as `(L - l₀)` times a
  cofactor whose value at `l₀` is the derivative (`Polynomial.mul_divByMonic_eq_iff_isRoot`,
  `Polynomial.derivative_mul`), cancel `(L - l₀)²` and evaluate at `l₀`.
* If `c p = B A` over `ℂ` with `c ≠ 0`, `l₀` a simple root of `A`, and `l₀` the only multiple
  root of `p`, then `A = (L - l₀) A^c` with `A^c` coprime to `B`. Over an algebraically closed
  field coprimality means no common root
  (`Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed`). A common root `l` of `A^c` and `B`
  is a root of `p` and of `p'` (`c p' = B' A + B A'`, `A(l) = 0 = B(l)`), so `l = l₀`; but
  `A^c(l₀) = A'(l₀) ≠ 0`.
-/

open Polynomial

namespace AJConjecture

/-- The product of the slopes at a common root: if `u B A = v G D T` and `l₀` is a root of
`A, B, G, D`, then `u B'(l₀) A'(l₀) = v G'(l₀) D'(l₀) T(l₀)`. -/
theorem eval_derivative_mul_eq_of_mul_eq {k : Type*} [Field k] {u v l₀ : k}
    {A B G D T : k[X]} (h : C u * (B * A) = C v * (G * D * T)) (hA : A.eval l₀ = 0)
    (hB : B.eval l₀ = 0) (hG : G.eval l₀ = 0) (hD : D.eval l₀ = 0) :
    u * ((derivative B).eval l₀ * (derivative A).eval l₀) =
      v * ((derivative G).eval l₀ * (derivative D).eval l₀ * T.eval l₀) := by
  obtain ⟨A₁, rfl⟩ := dvd_iff_isRoot.mpr hA
  obtain ⟨B₁, rfl⟩ := dvd_iff_isRoot.mpr hB
  obtain ⟨G₁, rfl⟩ := dvd_iff_isRoot.mpr hG
  obtain ⟨D₁, rfl⟩ := dvd_iff_isRoot.mpr hD
  have key : C u * (B₁ * A₁) = C v * (G₁ * D₁ * T) := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (X_sub_C_ne_zero l₀))
    linear_combination h
  have hk := congrArg (eval l₀) key
  simp only [eval_mul, eval_C] at hk
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, eval_add, eval_mul,
    eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, sub_zero, one_mul]
  linear_combination hk

end AJConjecture
