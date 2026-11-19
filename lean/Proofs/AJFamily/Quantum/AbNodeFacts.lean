import Mathlib
import AJFamily.Quantum.AbNodeCertificateIdentity
import AJConjecture.WitnessPolynomials
import AJFamily.Quantum.TwistPolyBasic
import AJFamily.Quantum.TwistPolyNodeValues

/-!
# Abelian node: values and derivatives

`abNode_facts`: at the abelian node `(m₀, 1)`, where `x₀ = m₀²` solves
`m x₀² - (2m + 1) x₀ + m = 0`, `B_m` vanishes, `E` does not, and both partial derivatives of
`B_m` are nonzero.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- `Ẑ(m, 1) = 2x(1 + x)²`, `x = m²`. -/
private theorem evalIntPoint_zetaMoebiusM_one_abNode (m : ℂ) :
    evalIntPoint zetaMoebiusM m 1 = 2 * m ^ 2 * (1 + m ^ 2) ^ 2 := by
  rw [evalIntPoint_eq, zetaMoebiusM_eq_explicit]
  simp [evalIntHomTwistNode]
  ring

/-- `∂_L Ẑ(m, 1)`. -/
private theorem evalIntPoint_derivative_zetaMoebiusM_one_abNode (m : ℂ) :
    evalIntPoint (derivative zetaMoebiusM) m 1 =
      -((1 + m ^ 2) * ((m ^ 2) ^ 3 - 3 * (m ^ 2) ^ 2 - m ^ 2 - 1)) := by
  rw [evalIntPoint_eq, zetaMoebiusM_eq_explicit]
  simp [evalIntHomTwistNode, derivative_pow, derivative_mul]
  ring

/-- `∂_L B_1(m, 1)`. -/
private theorem evalIntPoint_derivative_twistPoly_one_one_abNode (m : ℂ) :
    evalIntPoint (derivative (twistPoly 1)) m 1 =
      -((1 + m ^ 2) ^ 2 * ((m ^ 2) ^ 2 - 3 * m ^ 2 + 1)) := by
  rw [evalIntPoint_eq, twistPoly, zetaMoebiusM_eq_explicit]
  simp [evalIntHomTwistNode, derivative_pow, derivative_mul]
  ring

/-- `∂_L (x²(L + x)⁴)` at `(m, 1)`. -/
private theorem evalIntPoint_derivative_twistCoeff_one_abNode (m : ℂ) :
    evalIntPoint (derivative (C (X ^ 4) * (C (X ^ 2) + X) ^ 4 : ℤ[X][X])) m 1 =
      4 * (m ^ 2) ^ 2 * (1 + m ^ 2) ^ 3 := by
  rw [evalIntPoint_eq]
  simp [evalIntHomTwistNode, derivative_pow, derivative_mul]
  ring

/-- `B_k(m, 1)` in closed form. -/
private theorem evalIntPoint_twistPoly_one_abNode {k : ℕ} (hk : 1 ≤ k) (m : ℂ) :
    evalIntPoint (twistPoly k) m 1 = -(m ^ (2 * (k - 1)) * (1 + m ^ 2) ^ (2 * k) *
      ((k : ℂ) * m ^ 4 - (2 * (k : ℂ) + 1) * m ^ 2 + k)) := by
  rw [evalIntPoint_at_one, eval_one_twistPoly hk]
  simp

/-- `B_1(m, 1) = -(1 + x)²(x² - 3x + 1)`. -/
private theorem evalIntPoint_twistPoly_one_one_abNode (m : ℂ) :
    evalIntPoint (twistPoly 1) m 1 = -((1 + m ^ 2) ^ 2 * ((m ^ 2) ^ 2 - 3 * m ^ 2 + 1)) := by
  rw [evalIntPoint_twistPoly_one_abNode le_rfl, Nat.sub_self, mul_zero, pow_zero, Nat.cast_one]
  ring

/-- The double-root closed form at the abelian node `L = 1`, with the denominators cleared. -/
private theorem dblRootDeriv_abNode (x : ℂ) (k : ℕ) (hx0 : x ≠ 0) (hx1 : 1 + x ≠ 0) :
    dblRootDeriv (2 * x * (1 + x) ^ 2 / 2)
        (-((1 + x) ^ 2 * (x ^ 2 - 3 * x + 1)) - 2 * x * (1 + x) ^ 2 / 2)
        (-((1 + x) ^ 2 * (x ^ 2 - 3 * x + 1))) (-((1 + x) * (x ^ 3 - 3 * x ^ 2 - x - 1)))
        (4 * x ^ 2 * (1 + x) ^ 3) k =
      (x * (1 + x) ^ 2) ^ k * ((k : ℂ) * ((k : ℂ) ^ 2 * (x - 1) ^ 5 - 3 * k * x ^ 4
        - 3 * k * x ^ 3 + 15 * k * x ^ 2 - 9 * k * x - x ^ 5 + 2 * x ^ 4 + 5 * x ^ 3
        + 7 * x ^ 2 - 2 * x + 1) / (6 * x ^ 2 * (1 + x))) := by
  have hw : 2 * x * (1 + x) ^ 2 / 2 = x * (1 + x) ^ 2 := by ring
  rw [dblRootDeriv, hw]
  refine congrArg (fun t ↦ (x * (1 + x) ^ 2) ^ k * t) ?_
  field_simp
  ring

/-- The values and derivatives at the abelian node used by the index criterion. -/
theorem abNode_facts (m : ℕ) (hm : 2 ≤ m) {m₀ : ℂ}
    (hab : (m : ℂ) * (m₀ ^ 2) ^ 2 - (2 * m + 1) * m₀ ^ 2 + m = 0) :
    m₀ ≠ 0 ∧ m₀ ^ 2 ≠ 1 ∧ m₀ ^ 2 ≠ -1 ∧
      evalIntPoint (twistPoly m) m₀ 1 = 0 ∧ evalIntPoint extraFactor m₀ 1 ≠ 0 ∧
      evalIntPoint (derivative (twistPoly m)) m₀ 1 ≠ 0 ∧
      evalIntPoint (coeffDerivative (twistPoly m)) m₀ 1 ≠ 0 := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have h4m : (4 * (m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (4 * m)
  have h0 : m₀ ≠ 0 := by
    intro h
    rw [h] at hab
    exact hmC (by linear_combination hab)
  have hx0 : m₀ ^ 2 ≠ 0 := pow_ne_zero 2 h0
  have h1 : m₀ ^ 2 ≠ 1 := by
    intro h
    rw [h] at hab
    exact one_ne_zero (by linear_combination -hab : (1 : ℂ) = 0)
  have h2 : m₀ ^ 2 ≠ -1 := by
    intro h
    rw [h] at hab
    exact h4m (by linear_combination hab)
  have hx1 : 1 + m₀ ^ 2 ≠ 0 := fun h ↦ h2 (by linear_combination h)
  refine ⟨h0, h1, h2, ?_, ?_, ?_, ?_⟩
  · rw [evalIntPoint_twistPoly_one_abNode (by omega)]
    linear_combination (-(m₀ ^ (2 * (m - 1)) * (1 + m₀ ^ 2) ^ (2 * m))) * hab
  · rw [evalIntPoint_extraFactor_one]
    exact mul_ne_zero (by norm_num) hx0
  · have hZ := evalIntPoint_zetaMoebiusM_one_abNode m₀
    have hw : evalIntPoint zetaMoebiusM m₀ 1 ≠ 0 := by
      rw [hZ]
      exact mul_ne_zero (mul_ne_zero two_ne_zero hx0) (pow_ne_zero 2 hx1)
    have hdbl : evalIntPoint zetaMoebiusM m₀ 1 ^ 2 =
        4 * ((m₀ ^ 2) ^ 2 * (1 + m₀ ^ 2) ^ 4) := by
      rw [hZ]
      ring
    rw [(twistPoly_node_values hdbl hw m).2.1, hZ, evalIntPoint_twistPoly_one_one_abNode,
      evalIntPoint_derivative_twistPoly_one_one_abNode,
      evalIntPoint_derivative_zetaMoebiusM_one_abNode,
      evalIntPoint_derivative_twistCoeff_one_abNode, dblRootDeriv_abNode _ _ hx0 hx1]
    refine mul_ne_zero (pow_ne_zero _ (mul_ne_zero hx0 (pow_ne_zero 2 hx1)))
      (div_ne_zero (mul_ne_zero hmC ?_) (mul_ne_zero (mul_ne_zero (by norm_num)
        (pow_ne_zero 2 hx0)) hx1))
    intro hP
    have hprod : m₀ ^ 2 * (1 + m₀ ^ 2) ^ 2 * ((m₀ ^ 2) ^ 2 - 3 * m₀ ^ 2 + 1) = 0 := by
      linear_combination ((m : ℂ) ^ 2 * (m₀ ^ 2 - 1) ^ 4 - 2 * m * (m₀ ^ 2) ^ 3
        - 8 * m * (m₀ ^ 2) ^ 2 + 10 * m * m₀ ^ 2 - (m₀ ^ 2) ^ 4 + (m₀ ^ 2) ^ 3
        + 4 * (m₀ ^ 2) ^ 2 + m₀ ^ 2 - 1) * hab - (m₀ ^ 2 - 1) * m * hP
    have hq : (m₀ ^ 2) ^ 2 - 3 * m₀ ^ 2 + 1 = 0 := by
      rcases mul_eq_zero.1 hprod with h | h
      · exact absurd h (mul_ne_zero hx0 (pow_ne_zero 2 hx1))
      · exact h
    have hm1 : ((m : ℂ) - 1) * m₀ ^ 2 = 0 := by linear_combination hab - (m : ℂ) * hq
    have hm1' : (m : ℂ) = 1 := by
      linear_combination (mul_eq_zero.1 hm1).resolve_right hx0
    have : m = 1 := by exact_mod_cast hm1'
    omega
  · rw [evalIntPoint_at_one, eval_one_coeffDerivative, eval_one_twistPoly (by omega),
      ← derivative_map]
    have hmap : (-(X ^ (2 * (m - 1)) * (1 + X ^ 2) ^ (2 * m) * (C (m : ℤ) * X ^ 4 -
        C (2 * (m : ℤ) + 1) * X ^ 2 + C (m : ℤ))) : ℤ[X]).map (Int.castRingHom ℂ) =
        -(X ^ (2 * (m - 1)) * (1 + X ^ 2) ^ (2 * m)) *
          (C (m : ℂ) * X ^ 4 - C (2 * (m : ℂ) + 1) * X ^ 2 + C (m : ℂ)) := by
      simp only [Polynomial.map_neg, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add,
        Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, Polynomial.map_C]
      simp
    have hC0 :
        (C (m : ℂ) * X ^ 4 - C (2 * (m : ℂ) + 1) * X ^ 2 + C (m : ℂ)).eval m₀ = 0 := by
      simp only [eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
      linear_combination hab
    rw [hmap, derivative_mul, eval_add, eval_mul, eval_mul, hC0, mul_zero, zero_add]
    refine mul_ne_zero ?_ ?_
    · simp only [eval_neg, eval_mul, eval_pow, eval_X, eval_add, eval_one, neg_ne_zero]
      exact mul_ne_zero (pow_ne_zero _ h0) (pow_ne_zero _ hx1)
    · simp only [derivative_add, derivative_sub, derivative_C_mul_X_pow, derivative_C]
      simp only [eval_sub, eval_C, eval_mul, eval_pow, eval_X, add_zero]
      intro h
      have ht : 2 * (m : ℂ) * m₀ ^ 2 - (2 * m + 1) = 0 := by
        have h' : m₀ * (2 * (2 * (m : ℂ) * m₀ ^ 2 - (2 * m + 1))) = 0 := by
          linear_combination h
        exact (mul_eq_zero.1 ((mul_eq_zero.1 h').resolve_left h0)).resolve_left two_ne_zero
      exact h4m (by
        linear_combination (2 * (m : ℂ) * m₀ ^ 2 - (2 * m + 1)) * ht - 4 * m * hab)

end AJConjecture
