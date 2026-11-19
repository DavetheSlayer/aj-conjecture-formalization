import Mathlib
import AJFamily.Quantum.TwistPolyNodeValues
import AJConjecture.QAlgInnerDerivativeBasic
import AJConjecture.WitnessPolynomials
import AJFamily.Quantum.NodeClosedForms
import AJFamily.Quantum.TwistPolyBasic

/-!
# Abelian node: the certificate identity

`abNode_certificate_identity` is the numerical identity of
`evalIntPoint_weylSymbol_famTransferOp_of_certificate` for `G = L - 1`, `D = B_m`, `T = E` at the
abelian node `(m₀, 1)`, where `x₀ = m₀²` solves `m x₀² - (2m + 1) x₀ + m = 0`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The value at `L = 1` is the value of the specialisation `p(M, 1) ∈ ℤ[M]`. -/
theorem evalIntPoint_at_one (p : ℤ[X][X]) (m : ℂ) :
    evalIntPoint p m 1 = ((p.eval 1).map (Int.castRingHom ℂ)).eval m := by
  rw [evalIntPoint, evalPoint, eval₂_at_one, eval_one_map]
  rfl

/-- At `L = 1` the `M`-derivative commutes with specialisation. -/
theorem eval_one_coeffDerivative (p : ℤ[X][X]) :
    (coeffDerivative p).eval 1 = derivative (p.eval 1) := by
  rw [coeffDerivative, eval_sum, eval_eq_sum (p := p), Polynomial.sum, Polynomial.sum,
    derivative_sum]
  simp only [eval_monomial, one_pow, mul_one]

/-- `E(m, 1) = 4m²`. -/
theorem evalIntPoint_extraFactor_one (m : ℂ) :
    evalIntPoint extraFactor m 1 = 4 * m ^ 2 := by
  rw [evalIntPoint_eq, extraFactor]
  simp [evalIntHomTwistNode]

/-- The `L`-derivative of `L - 1` is `1`. -/
theorem evalIntPoint_derivative_X_sub_one (m l : ℂ) :
    evalIntPoint (derivative (X - 1 : ℤ[X][X])) m l = 1 := by
  rw [evalIntPoint_eq]
  simp

/-- The `M`-derivative of `L - 1` vanishes. -/
private theorem evalIntPoint_coeffDerivative_X_sub_one_abCert (m l : ℂ) :
    evalIntPoint (coeffDerivative (X - 1 : ℤ[X][X])) m l = 0 := by
  have h : coeffDerivative (X - 1 : ℤ[X][X]) = 0 := by
    have hX : innerDerivative (X : ℤ[X][X]) = 0 := by
      rw [← monomial_one_one_eq_X]
      simp [innerDerivative]
    rw [coeffDerivative_eq_innerDerivative, sub_eq_add_neg, ← C_1, ← C_neg, innerDerivative_add,
      innerDerivative_C, hX]
    simp
  rw [h, evalIntPoint_eq, map_zero]

/-- The basis-jet coefficient `c` vanishes at `J₀ = 1`. -/
private theorem famBasisJetC_one_abCert (x : ℂ) : famBasisJetC x 1 = 0 := by
  rw [famBasisJetC, mul_one, mul_one, ← neg_sub x 1, div_neg]
  ring

/-- `∂_M B_m(m₀, 1)` in closed form at a root of the abelian node quadratic. -/
private theorem evalIntPoint_coeffDerivative_twistPoly_abCert (m : ℕ) (hm : 1 ≤ m) {m₀ : ℂ}
    (hab : (m : ℂ) * (m₀ ^ 2) ^ 2 - (2 * m + 1) * m₀ ^ 2 + m = 0) :
    evalIntPoint (coeffDerivative (twistPoly m)) m₀ 1 =
      -(m₀ ^ (2 * (m - 1)) * (1 + m₀ ^ 2) ^ (2 * m)) *
        (4 * m * m₀ ^ 3 - 2 * (2 * m + 1) * m₀) := by
  rw [evalIntPoint_at_one, eval_one_coeffDerivative, eval_one_twistPoly hm,
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
  simp only [derivative_add, derivative_sub, derivative_C_mul_X_pow, derivative_C]
  simp only [eval_neg, eval_mul, eval_pow, eval_X, eval_add, eval_one, eval_sub, eval_C, add_zero]
  push_cast
  ring

/-- The target jet at the abelian node `J₀ = 1`, `w = x₀`, in closed form. -/
private theorem famTargetJet_abNode_closed (k : ℕ) (x : ℂ) :
    famTargetJet (k + 2) x 1 x =
      -8 * x ^ (k + 2) * (2 * ((k : ℂ) + 2) * x ^ 2 - 4 * ((k : ℂ) + 2) * x +
        2 * ((k : ℂ) + 2) - x) := by
  rcases k with _ | j
  · simp only [famTargetJet]
    norm_num
    ring
  · simp only [famTargetJet]
    simp only [show j + 1 + 2 - 1 = j + 2 by omega, show j + 1 + 2 - 2 = j + 1 by omega,
      show j + 1 + 2 + 1 - 1 = j + 3 by omega, show j + 1 + 2 + 1 - 2 = j + 2 by omega]
    push_cast
    ring

/-- The certificate identity at the abelian node. -/
theorem abNode_certificate_identity (m : ℕ) (hm : 2 ≤ m) {m₀ : ℂ}
    (hab : (m : ℂ) * (m₀ ^ 2) ^ 2 - (2 * m + 1) * m₀ ^ 2 + m = 0) :
    famTargetJet m (m₀ ^ 2) 1 (m₀ ^ 2) *
        ((m₀ ^ 2 - 1) ^ (2 * m + 3) * ((m₀ ^ 2) ^ 2 - 1) ^ (2 * m + 3)) =
      famBasisGamma m (m₀ ^ 2) 1 * ((m₀ ^ 2 + 1) ^ 2 * (m₀ ^ 2 - 1)) * evalIntPoint extraFactor m₀ 1 *
        (2 * famBasisJetC (m₀ ^ 2) 1 * 1 ^ 2 *
            (evalIntPoint (derivative (X - 1)) m₀ 1 * evalIntPoint (derivative (twistPoly m)) m₀ 1) -
          1 * m₀ *
            (evalIntPoint (derivative (X - 1)) m₀ 1 * evalIntPoint (coeffDerivative (twistPoly m)) m₀ 1 +
              evalIntPoint (coeffDerivative (X - 1)) m₀ 1 * evalIntPoint (derivative (twistPoly m)) m₀ 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [famBasisJetC_one_abCert, evalIntPoint_derivative_X_sub_one,
    evalIntPoint_coeffDerivative_X_sub_one_abCert, evalIntPoint_extraFactor_one,
    evalIntPoint_coeffDerivative_twistPoly_abCert _ (by omega) hab, famTargetJet_abNode_closed,
    famBasisGamma, show k + 2 - 1 = k + 1 by omega, pow_mul]
  have hodd : ((1 - m₀ ^ 2) * (m₀ ^ 2 - 1)) ^ (2 * (k + 2) + 3) =
      -((m₀ ^ 2 - 1) ^ (2 * (k + 2) + 3)) ^ 2 := by
    rw [show (1 - m₀ ^ 2) * (m₀ ^ 2 - 1) = -1 * ((m₀ ^ 2 - 1) * (m₀ ^ 2 - 1)) by ring, mul_pow,
      mul_pow, Odd.neg_one_pow ⟨k + 3, by ring⟩]
    ring
  have hsq : ((m₀ ^ 2) ^ 2 - 1) ^ (2 * (k + 2) + 3) =
      (m₀ ^ 2 - 1) ^ (2 * (k + 2) + 3) * ((1 + m₀ ^ 2) ^ (2 * (k + 2)) * (1 + m₀ ^ 2) ^ 3) := by
    rw [← pow_add, ← mul_pow]
    ring
  rw [hodd, hsq]
  generalize (m₀ ^ 2 - 1) ^ (2 * (k + 2) + 3) = P
  generalize (1 + m₀ ^ 2) ^ (2 * (k + 2)) = R
  push_cast at hab ⊢
  linear_combination (-16 * P ^ 2 * R * (1 + m₀ ^ 2) ^ 2 * (m₀ ^ 2) ^ (k + 2)) * hab

end AJConjecture
