import Mathlib
import AJConjecture.QAlgWeylSymbol

/-!
# Derivatives of a symbol `κ₁ P₀ = κ₂ G D T` at a common zero of `G` and `D`

At a point `(m₀, l₀)` with `G = D = 0` and `κ₁(m₀) ≠ 0`:
`P₀ = 0`, `∂_L P₀ = 0`, `κ₁ ∂_L² P₀ = 2 κ₂ ∂_L G ∂_L D · T` and
`κ₁ (L ∂_L)(M ∂_M) P₀ = κ₂ l₀ m₀ (∂_L G ∂_M D + ∂_M G ∂_L D) T`.
Proof: `evalIntPoint` is a ring homomorphism in its polynomial argument and commutes with the
Leibniz rules for `derivative`, `coeffDerivative` and `eulerEuler = (L ∂_L)(M ∂_M)`; every term
with an undifferentiated `G` or `D` vanishes.
-/

open Polynomial

namespace AJConjecture

/-- Evaluation at a complex point `(m, l)`, as a ring homomorphism. -/
private noncomputable def evalIntHomSymbolNode (m l : ℂ) : ℤ[X][X] →+* ℂ :=
  (Polynomial.eval₂RingHom (Polynomial.evalRingHom m) l).comp
    (Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom ℂ)))

/-- `evalIntPoint` is the evaluation homomorphism. -/
private theorem evalIntPoint_eq_evalIntHomSymbolNode (p : ℤ[X][X]) (m l : ℂ) :
    evalIntPoint p m l = evalIntHomSymbolNode m l p :=
  rfl

/-- The value of a polynomial constant in `L`. -/
private theorem evalIntHomSymbolNode_C (m l : ℂ) (κ : ℤ[X]) :
    evalIntHomSymbolNode m l (C κ) = (κ.map (Int.castRingHom ℂ)).eval m := by
  simp [evalIntHomSymbolNode]

/-- The value of `L`. -/
private theorem evalIntHomSymbolNode_X (m l : ℂ) : evalIntHomSymbolNode m l X = l := by
  simp [evalIntHomSymbolNode]

/-- The coefficients of `∂p/∂M` are the derivatives of the coefficients. -/
theorem coeff_coeffDerivative (p : ℤ[X][X]) (k : ℕ) :
    (coeffDerivative p).coeff k = derivative (p.coeff k) := by
  rw [coeffDerivative, sum_def, finsetSum_coeff]
  simp only [coeff_monomial, Finsupp.single_apply]
  rw [Finset.sum_ite_eq' p.support k]
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, derivative_zero]

/-- The Leibniz rule for `∂/∂M`. -/
private theorem coeffDerivative_mul_symbolNode (p q : ℤ[X][X]) :
    coeffDerivative (p * q) = coeffDerivative p * q + p * coeffDerivative q := by
  ext k : 2
  simp only [coeff_coeffDerivative, coeff_add, coeff_mul, derivative_sum,
    derivative_mul, Finset.sum_add_distrib]

/-- The derivative `∂/∂M` of a polynomial constant in `L`. -/
private theorem coeffDerivative_C_symbolNode (κ : ℤ[X]) :
    coeffDerivative (C κ) = C (derivative κ) := by
  ext k : 2
  rw [coeff_coeffDerivative, coeff_C, coeff_C]
  split_ifs
  · rfl
  · rw [derivative_zero]

/-- The coefficients of `(L ∂_L)(M ∂_M) p`. -/
theorem coeff_eulerEuler (p : ℤ[X][X]) (k : ℕ) :
    (eulerEuler p).coeff k = (k : ℤ[X]) * (X * derivative (p.coeff k)) := by
  have hmon : ∀ c : ℤ[X], (c.sum fun e a ↦ monomial e (((k * e : ℕ) : ℤ) * a)) =
      (k : ℤ[X]) * (X * derivative c) := by
    intro c
    ext e
    rw [sum_def, finsetSum_coeff, ← C_eq_natCast, coeff_C_mul]
    simp only [coeff_monomial, Finsupp.single_apply]
    rw [Finset.sum_ite_eq' c.support e]
    rcases e with _ | e
    · simp
    · rw [coeff_X_mul, coeff_derivative]
      split_ifs with h
      · push_cast
        ring
      · rw [notMem_support_iff.mp h]
        simp
  rw [eulerEuler, sum_def, finsetSum_coeff]
  simp only [coeff_monomial, Finsupp.single_apply]
  rw [Finset.sum_ite_eq' p.support k]
  split_ifs with h
  · exact hmon _
  · rw [notMem_support_iff.mp h, derivative_zero, mul_zero, mul_zero]

/-- `(L ∂_L)(M ∂_M) p = M L ∂_L ∂_M p`. -/
theorem eulerEuler_eq (p : ℤ[X][X]) :
    eulerEuler p = C X * (X * derivative (coeffDerivative p)) := by
  ext k : 2
  rw [coeff_eulerEuler, coeff_C_mul]
  rcases k with _ | k
  · simp
  · rw [coeff_X_mul, coeff_derivative, coeff_coeffDerivative]
    push_cast
    ring

/-- Values at a common zero of `G` and `D` of the derivatives of `P₀` with
`κ₁ P₀ = κ₂ G D T`. -/
theorem evalIntPoint_derivatives_of_symbol_node {P₀ G D T : ℤ[X][X]} {κ₁ κ₂ : ℤ[X]}
    (hsym : C κ₁ * P₀ = C κ₂ * (G * D * T)) {m₀ l₀ : ℂ}
    (hκ₁ : (κ₁.map (Int.castRingHom ℂ)).eval m₀ ≠ 0)
    (hG : evalIntPoint G m₀ l₀ = 0) (hD : evalIntPoint D m₀ l₀ = 0) :
    evalIntPoint P₀ m₀ l₀ = 0 ∧ evalIntPoint (derivative P₀) m₀ l₀ = 0 ∧
      (κ₁.map (Int.castRingHom ℂ)).eval m₀ * evalIntPoint (derivative (derivative P₀)) m₀ l₀ =
        2 * (κ₂.map (Int.castRingHom ℂ)).eval m₀ *
          (evalIntPoint (derivative G) m₀ l₀ * evalIntPoint (derivative D) m₀ l₀) *
          evalIntPoint T m₀ l₀ ∧
      (κ₁.map (Int.castRingHom ℂ)).eval m₀ * evalIntPoint (eulerEuler P₀) m₀ l₀ =
        (κ₂.map (Int.castRingHom ℂ)).eval m₀ * (l₀ * m₀) *
          (evalIntPoint (derivative G) m₀ l₀ * evalIntPoint (coeffDerivative D) m₀ l₀ +
            evalIntPoint (coeffDerivative G) m₀ l₀ * evalIntPoint (derivative D) m₀ l₀) *
          evalIntPoint T m₀ l₀ := by
  simp only [evalIntPoint_eq_evalIntHomSymbolNode] at hG hD ⊢
  rw [← evalIntHomSymbolNode_C m₀ l₀ κ₁] at hκ₁ ⊢
  rw [← evalIntHomSymbolNode_C m₀ l₀ κ₂]
  have e0 := congrArg (evalIntHomSymbolNode m₀ l₀) hsym
  simp only [map_mul, hG, hD] at e0
  have hP : evalIntHomSymbolNode m₀ l₀ P₀ = 0 :=
    mul_left_cancel₀ hκ₁ (by rw [e0]; ring)
  have e1 := congrArg (fun p ↦ evalIntHomSymbolNode m₀ l₀ (derivative p)) hsym
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, map_add, map_mul, hG, hD] at e1
  have hP' : evalIntHomSymbolNode m₀ l₀ (derivative P₀) = 0 :=
    mul_left_cancel₀ hκ₁ (by rw [e1]; ring)
  have e2 := congrArg (fun p ↦ evalIntHomSymbolNode m₀ l₀ (derivative (derivative p))) hsym
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, map_add, map_mul, hG, hD] at e2
  have e3 := congrArg (fun p ↦ evalIntHomSymbolNode m₀ l₀ (derivative (coeffDerivative p))) hsym
  simp only [coeffDerivative_mul_symbolNode, coeffDerivative_C_symbolNode, derivative_mul,
    derivative_C, zero_mul, zero_add, map_add, map_mul, hG, hD, hP'] at e3
  refine ⟨hP, hP', ?_, ?_⟩
  · linear_combination e2
  · have hX : evalIntHomSymbolNode m₀ l₀ (C X) = m₀ := by
      rw [evalIntHomSymbolNode_C, map_X, eval_X]
    rw [eulerEuler_eq, map_mul, map_mul, hX, evalIntHomSymbolNode_X]
    linear_combination (l₀ * m₀) * e3

end AJConjecture
