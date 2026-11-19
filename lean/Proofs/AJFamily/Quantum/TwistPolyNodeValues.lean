import Mathlib
import AJConjecture.QAlgInnerDerivativeBasic
import AJFamily.Quantum.DoubleRootRecurrence
import AJFamily.Quantum.TwistPoly

/-!
# The twist polynomial at a double point

Closed forms of `B_k`, `∂B_k/∂L` and `∂B_k/∂M` at a point where the recursion of `B_k` has a double
characteristic root.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- Evaluation at a complex point `(m, l)`, as a ring homomorphism. -/
def evalIntHomTwistNode (m l : ℂ) : ℤ[X][X] →+* ℂ :=
  (Polynomial.eval₂RingHom (Polynomial.evalRingHom m) l).comp
    (Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom ℂ)))

/-- `evalIntPoint` is the evaluation homomorphism. -/
theorem evalIntPoint_eq (p : ℤ[X][X]) (m l : ℂ) :
    evalIntPoint p m l = evalIntHomTwistNode m l p :=
  rfl

/-- The inner derivative is subtractive. -/
theorem innerDerivative_sub (p q : ℤ[X][X]) :
    innerDerivative (p - q) = innerDerivative p - innerDerivative q := by
  rw [eq_sub_iff_add_eq, ← innerDerivative_add, sub_add_cancel]

/-- The inner derivative of `1` vanishes. -/
private theorem innerDerivative_one_twistNode : innerDerivative (1 : ℤ[X][X]) = 0 := by
  rw [← C_1, innerDerivative_C, derivative_one, C_0]

/-- The value of the coefficient `x² (L + x)⁴` of the twist recursion. -/
private theorem evalIntPoint_twistCoeff (m l : ℂ) :
    evalIntPoint (C (X ^ 4) * (C (X ^ 2) + X) ^ 4 : ℤ[X][X]) m l =
      (m ^ 2) ^ 2 * (l + m ^ 2) ^ 4 := by
  rw [evalIntPoint_eq]
  simp only [evalIntHomTwistNode, RingHom.comp_apply, coe_mapRingHom, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X, coe_eval₂RingHom,
    eval₂_mul, eval₂_pow, eval₂_add, eval₂_C, eval₂_X, coe_evalRingHom, eval_pow, eval_X]
  ring

theorem twistPoly_node_values {m₀ l₀ : ℂ}
    (hdbl : evalIntPoint zetaMoebiusM m₀ l₀ ^ 2 = 4 * ((m₀ ^ 2) ^ 2 * (l₀ + m₀ ^ 2) ^ 4))
    (hw : evalIntPoint zetaMoebiusM m₀ l₀ ≠ 0) (k : ℕ) :
    evalIntPoint (twistPoly k) m₀ l₀ =
        (evalIntPoint zetaMoebiusM m₀ l₀ / 2) ^ k + k * (evalIntPoint zetaMoebiusM m₀ l₀ / 2) ^ (k - 1) *
          (evalIntPoint (twistPoly 1) m₀ l₀ - evalIntPoint zetaMoebiusM m₀ l₀ / 2) ∧
      evalIntPoint (derivative (twistPoly k)) m₀ l₀ =
        dblRootDeriv (evalIntPoint zetaMoebiusM m₀ l₀ / 2)
          (evalIntPoint (twistPoly 1) m₀ l₀ - evalIntPoint zetaMoebiusM m₀ l₀ / 2)
          (evalIntPoint (derivative (twistPoly 1)) m₀ l₀)
          (evalIntPoint (derivative zetaMoebiusM) m₀ l₀)
          (evalIntPoint (derivative (C (X ^ 4) * (C (X ^ 2) + X) ^ 4 : ℤ[X][X])) m₀ l₀) k ∧
      evalIntPoint (coeffDerivative (twistPoly k)) m₀ l₀ =
        dblRootDeriv (evalIntPoint zetaMoebiusM m₀ l₀ / 2)
          (evalIntPoint (twistPoly 1) m₀ l₀ - evalIntPoint zetaMoebiusM m₀ l₀ / 2)
          (evalIntPoint (coeffDerivative (twistPoly 1)) m₀ l₀)
          (evalIntPoint (coeffDerivative zetaMoebiusM) m₀ l₀)
          (evalIntPoint (coeffDerivative (C (X ^ 4) * (C (X ^ 2) + X) ^ 4 : ℤ[X][X])) m₀ l₀) k := by
  set w : ℂ := evalIntPoint zetaMoebiusM m₀ l₀ / 2 with hwdef
  set Q : ℤ[X][X] := C (X ^ 4) * (C (X ^ 2) + X) ^ 4 with hQ
  have hw0 : w ≠ 0 := div_ne_zero hw two_ne_zero
  have h2w : evalIntPoint zetaMoebiusM m₀ l₀ = 2 * w := by rw [hwdef]; ring
  have hQw : evalIntPoint Q m₀ l₀ = w ^ 2 := by
    rw [hQ, evalIntPoint_twistCoeff, hwdef, div_pow, hdbl]
    ring
  have hrec : ∀ k, twistPoly (k + 2) = zetaMoebiusM * twistPoly (k + 1) - Q * twistPoly k :=
    fun k ↦ rfl
  have hy : ∀ k, evalIntPoint (twistPoly (k + 2)) m₀ l₀ =
      2 * w * evalIntPoint (twistPoly (k + 1)) m₀ l₀ -
        w ^ 2 * evalIntPoint (twistPoly k) m₀ l₀ := by
    intro k
    rw [hrec, ← h2w, ← hQw]
    simp only [evalIntPoint_eq, map_sub, map_mul]
  have hy0 : evalIntPoint (twistPoly 0) m₀ l₀ = 1 := by
    rw [evalIntPoint_eq, twistPoly, map_one]
  have hy1 : evalIntPoint (twistPoly 1) m₀ l₀ =
      w + (evalIntPoint (twistPoly 1) m₀ l₀ - w) := by
    ring
  have key := fun (z₁ α β : ℂ) (z : ℕ → ℂ) ↦
    dblRoot_closed (z₁ := z₁) (α := α) (β := β)
      (y := fun k ↦ evalIntPoint (twistPoly k) m₀ l₀) (z := z) hw0 hy0 hy1 hy
  have hE := h2w
  have hF := hQw
  simp only [evalIntPoint_eq] at hE hF
  refine ⟨(key 0 0 0 (fun _ ↦ 0) rfl rfl (fun _ ↦ by ring) k).1,
    (key _ (evalIntPoint (derivative zetaMoebiusM) m₀ l₀)
      (evalIntPoint (derivative Q) m₀ l₀)
      (fun k ↦ evalIntPoint (derivative (twistPoly k)) m₀ l₀) ?_ rfl ?_ k).2,
    (key _ (evalIntPoint (coeffDerivative zetaMoebiusM) m₀ l₀)
      (evalIntPoint (coeffDerivative Q) m₀ l₀)
      (fun k ↦ evalIntPoint (coeffDerivative (twistPoly k)) m₀ l₀) ?_ rfl ?_ k).2⟩
  · simp only [twistPoly, derivative_one, evalIntPoint_eq, map_zero]
  · intro k
    simp only [hrec, derivative_mul, evalIntPoint_eq, map_sub,
      map_add, map_mul, hE, hF]
    ring
  · simp only [twistPoly, coeffDerivative_eq_innerDerivative, innerDerivative_one_twistNode,
      evalIntPoint_eq, map_zero]
  · intro k
    simp only [hrec, coeffDerivative_eq_innerDerivative, innerDerivative_sub,
      innerDerivative_mul, evalIntPoint_eq, map_sub, map_add, map_mul, hE,
      hF]
    ring

end AJConjecture
