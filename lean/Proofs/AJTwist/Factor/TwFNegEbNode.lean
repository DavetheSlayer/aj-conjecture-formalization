import Mathlib
import AJTwist.Quantum.TwQTargetAtOne
import AJFamily.Quantum.NodeClosedForms
import AJTwist.Factor.TwFNegSymbolValues
import AJFamily.Quantum.TwistPolyNodeValues

/-!
# The crossing `E/C_b` in the coordinates `(x, J)` (TwF, unit F2)

Source: revision 5, Section 5.4 (`operators.tex`), "The `E/C_b` crossing": at `Z = -2`, with
`h_b = 2b - 1`, `s_b = (-1)^b`: `A_* = 1/(b h_b)`, `D_*² = (8b² - 4b + 1)/(b² h_b²)`,
`Z_J = -(4b - 1)/(b h_b)`, `ω = -4/h_b²`, `p_Z = 0`, `p_{ZJ} = s_b h_b`,
`p_{ZZ} = -2 s_b b(2b + 1)/3`, `Ṅ_(-b) = -s_b (56b² - 16b + 2)/(3 h_b³)`,
`s_G = -4b/(4b - 1)`, `s_H = -(24b³ - 8b² + 2b)/(10b² - 5b + 1)`, `ρ = 4b²/h_b`,
`κ = (s_G + s_H)/2`: both indices are `-1/2`. Eq. (enode) with `a = -b`:
`J = -(2b + 1)/(2b - 1)`, `K = -2 - 1/(b(2b - 1))`.

The node is `(m₀, twNegNodeL b m₀)` with `x₀ = m₀²` a root of
`b(2b - 1) x² + (4b² - 2b + 1) x + b(2b - 1)`; in the coordinates `(x, J)` it is
`(x₀, J₀)`, `J₀ = twNegNodeJ b = -(2b + 1)/(2b - 1)`, on the double locus `ζ = -2x` (`w = -x₀`),
where `T̂_(-b) = (-x₀)^(b-1) (-x₀ + b (x₀² + x₀ + 1 - x₀ J₀)) = 0`.

* `twNeg_ebNode_zeta`: `ζ(x₀, J₀) = -2 x₀` and `T̂_(-b)(x₀, J₀) = 0` at the node.
* `twNegTarget_one_derivatives_ebNode`: `p = (1 - J)(ζ + 2x) T̂_(-b)` has a double point there and
  `∂_x∂_J p = (1 - J₀)(∂_J ζ · ∂_x T̂_(-b) + (∂_x ζ + 2) ∂_J T̂_(-b))`.
The certificate identity and the vanishing of the Weyl symbol are in
`AJTwist/Factor/TwFNegEbCert.lean`, `TwFNegEbWeyl.lean`.

Checked: Weyl symbol, certificate and all the constants quoted above for `1 ≤ b ≤ 8` (scratch
`check_weyl.py`, `check_paper5.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `J₀ = -(2b + 1)/(2b - 1)` at the `E/C_b` node. -/
def twNegNodeJ (b : ℕ) : ℂ := -(2 * (b : ℂ) + 1) / (2 * b - 1)

/-- `L₀` at the `E/C_b` node over `M = m₀`. -/
def twNegNodeL (b : ℕ) (m₀ : ℂ) : ℂ := famNodeL (m₀ ^ 2) (twNegNodeJ b)

/-- The inner derivative of `1` vanishes. -/
private theorem innerDerivative_one_twfNegEbNode : innerDerivative (1 : ℤ[X][X]) = 0 := by
  rw [← C_1, innerDerivative_C, derivative_one, C_0]

/-- The inner derivative of the outer variable vanishes. -/
private theorem innerDerivative_X_twfNegEbNode : innerDerivative (X : ℤ[X][X]) = 0 := by
  rw [innerDerivative, sum_X_index] <;> simp

/-- The derivatives of `ζ + 2x`. -/
private theorem derivative_symbolZeta_add_twfNegEbNode :
    derivative (symbolZeta + C (2 * X) : ℤ[X][X]) = C (2 * X) * X - C (X ^ 2 + 1) ∧
      innerDerivative (symbolZeta + C (2 * X) : ℤ[X][X]) =
        X ^ 2 - C (2 * X) * X + C (2 * X + 1) + 2 ∧
      derivative (X ^ 2 - C (2 * X) * X + C (2 * X + 1) + 2 : ℤ[X][X]) = 2 * X - C (2 * X) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [symbolZeta, sq (X : ℤ[X][X]), derivative_add, derivative_sub, derivative_mul,
      derivative_C, derivative_X]
    simp only [C_mul, C_add, C_pow, C_1, C_ofNat]
    ring
  · simp only [symbolZeta, sq (X : ℤ[X][X]), innerDerivative_sub, innerDerivative_add,
      innerDerivative_mul, innerDerivative_C, innerDerivative_X_twfNegEbNode,
      sq (X : ℤ[X]), derivative_add, derivative_mul, derivative_X, derivative_one,
      derivative_ofNat]
    simp only [C_mul, C_add, C_1, C_0, C_ofNat]
    ring
  · simp only [sq (X : ℤ[X][X]), derivative_add, derivative_sub, derivative_mul,
      derivative_C, derivative_X, derivative_ofNat]
    ring

/-- The first derivatives and the mixed derivative of `(1 - J)(ζ + 2x) T` at a point. -/
private theorem evalIntPoint_derivatives_target_twfNegEbNode (T : ℤ[X][X]) (x₀ J₀ : ℂ) :
    evalIntPoint (derivative ((1 - X) * (symbolZeta + C (2 * X)) * T)) x₀ J₀ =
        -((evalIntPoint symbolZeta x₀ J₀ + 2 * x₀) * evalIntPoint T x₀ J₀) +
          (1 - J₀) * ((2 * x₀ * J₀ - (x₀ ^ 2 + 1)) * evalIntPoint T x₀ J₀ +
            (evalIntPoint symbolZeta x₀ J₀ + 2 * x₀) * evalIntPoint (derivative T) x₀ J₀) ∧
      evalIntPoint (coeffDerivative ((1 - X) * (symbolZeta + C (2 * X)) * T)) x₀ J₀ =
        (1 - J₀) * ((J₀ ^ 2 - 2 * x₀ * J₀ + 2 * x₀ + 1 + 2) * evalIntPoint T x₀ J₀ +
          (evalIntPoint symbolZeta x₀ J₀ + 2 * x₀) *
            evalIntPoint (coeffDerivative T) x₀ J₀) ∧
      evalIntPoint (derivative (coeffDerivative ((1 - X) * (symbolZeta + C (2 * X)) * T)))
          x₀ J₀ =
        -((J₀ ^ 2 - 2 * x₀ * J₀ + 2 * x₀ + 1 + 2) * evalIntPoint T x₀ J₀ +
          (evalIntPoint symbolZeta x₀ J₀ + 2 * x₀) * evalIntPoint (coeffDerivative T) x₀ J₀) +
        (1 - J₀) * ((2 * J₀ - 2 * x₀) * evalIntPoint T x₀ J₀ +
          (J₀ ^ 2 - 2 * x₀ * J₀ + 2 * x₀ + 1 + 2) * evalIntPoint (derivative T) x₀ J₀ +
          (2 * x₀ * J₀ - (x₀ ^ 2 + 1)) * evalIntPoint (coeffDerivative T) x₀ J₀ +
          (evalIntPoint symbolZeta x₀ J₀ + 2 * x₀) *
            evalIntPoint (derivative (coeffDerivative T)) x₀ J₀) := by
  obtain ⟨hdB, hiB, hdiB⟩ := derivative_symbolZeta_add_twfNegEbNode
  have hd : derivative ((1 - X) * (symbolZeta + C (2 * X)) * T) =
      -((symbolZeta + C (2 * X)) * T) + (1 - X) * ((C (2 * X) * X - C (X ^ 2 + 1)) * T +
        (symbolZeta + C (2 * X)) * derivative T) := by
    simp only [derivative_mul, derivative_sub, derivative_one, derivative_X, hdB]
    ring
  have hi : innerDerivative ((1 - X) * (symbolZeta + C (2 * X)) * T) =
      (1 - X) * ((X ^ 2 - C (2 * X) * X + C (2 * X + 1) + 2) * T +
        (symbolZeta + C (2 * X)) * innerDerivative T) := by
    simp only [innerDerivative_mul, innerDerivative_sub, innerDerivative_one_twfNegEbNode,
      innerDerivative_X_twfNegEbNode, hiB]
    ring
  have hdi : derivative (innerDerivative ((1 - X) * (symbolZeta + C (2 * X)) * T)) =
      -((X ^ 2 - C (2 * X) * X + C (2 * X + 1) + 2) * T +
        (symbolZeta + C (2 * X)) * innerDerivative T) +
      (1 - X) * ((2 * X - C (2 * X)) * T +
        (X ^ 2 - C (2 * X) * X + C (2 * X + 1) + 2) * derivative T +
        (C (2 * X) * X - C (X ^ 2 + 1)) * innerDerivative T +
        (symbolZeta + C (2 * X)) * derivative (innerDerivative T)) := by
    rw [hi]
    simp only [derivative_mul, derivative_add, derivative_sub, derivative_one, derivative_X,
      hdB, hdiB]
    ring
  have hX : evalIntHomTwistNode x₀ J₀ X = J₀ := by
    simp [evalIntHomTwistNode]
  have hCX : evalIntHomTwistNode x₀ J₀ (C X) = x₀ := by
    simp [evalIntHomTwistNode]
  simp only [coeffDerivative_eq_innerDerivative, evalIntPoint_eq]
  rw [hdi, hd, hi]
  simp only [map_add, map_sub, map_mul, map_neg, map_one, map_pow, map_ofNat, hX, hCX]
  refine ⟨trivial, ?_, ?_⟩ <;> ring

/-- At the `E/C_b` node, `ζ = -2x` and `T̂_(-b) = 0`. -/
theorem twNeg_ebNode_zeta (b : ℕ) (hb : 1 ≤ b) {m₀ : ℂ}
    (heb : (b : ℂ) * (2 * b - 1) * (m₀ ^ 2) ^ 2 + (4 * b ^ 2 - 2 * b + 1) * m₀ ^ 2 +
      b * (2 * b - 1) = 0) :
    evalIntPoint symbolZeta (m₀ ^ 2) (twNegNodeJ b) = 2 * -(m₀ ^ 2) ∧
      evalIntPoint (symbolTwistNeg b) (m₀ ^ 2) (twNegNodeJ b) = 0 := by
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have h2b : 2 * (b : ℂ) - 1 ≠ 0 := by
    intro h
    have h' : ((2 * b : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
      push_cast
      linear_combination h
    have := Nat.cast_injective h'
    omega
  have hx0 : m₀ ^ 2 ≠ 0 := by
    intro h
    rw [h] at heb
    exact mul_ne_zero hb0 h2b (by linear_combination heb)
  have hζ : evalIntPoint symbolZeta (m₀ ^ 2) (twNegNodeJ b) = 2 * -(m₀ ^ 2) := by
    rw [evalIntPoint_symbolZeta, twNegNodeJ]
    field_simp
    linear_combination 4 * heb
  refine ⟨hζ, ?_⟩
  rw [(symbolTwistNeg_node_values hζ (by ring) (neg_ne_zero.2 hx0) b).1]
  have hcrit : -(m₀ ^ 2) + b * ((m₀ ^ 2) ^ 2 + 1 - m₀ ^ 2 * twNegNodeJ b - -(m₀ ^ 2)) = 0 := by
    have hJ : twNegNodeJ b * (2 * b - 1) = -(2 * b + 1) := by
      rw [twNegNodeJ]
      field_simp
    refine mul_left_cancel₀ h2b ?_
    linear_combination heb - b * m₀ ^ 2 * hJ
  rw [← pow_sub_one_mul (show b ≠ 0 by omega) (-(m₀ ^ 2))]
  linear_combination (-(m₀ ^ 2)) ^ (b - 1) * hcrit

/-- On the curve `ζ = -2x`, at a zero of `T̂_(-b)`, the target `p = twNegTarget b 1` has a double
point, and `∂_x∂_J p = (1 - J₀)(∂_J ζ ∂_x T̂_(-b) + (∂_x ζ + 2) ∂_J T̂_(-b))`. -/
theorem twNegTarget_one_derivatives_ebNode (b : ℕ) (hb : 1 ≤ b) {x₀ J₀ : ℂ}
    (hζ : evalIntPoint symbolZeta x₀ J₀ = 2 * -x₀)
    (hT : evalIntPoint (symbolTwistNeg b) x₀ J₀ = 0) :
    evalIntPoint (derivative (twNegTarget b (1 : ℤ))) x₀ J₀ = 0 ∧
      evalIntPoint (coeffDerivative (twNegTarget b (1 : ℤ))) x₀ J₀ = 0 ∧
      evalIntPoint (derivative (coeffDerivative (twNegTarget b (1 : ℤ)))) x₀ J₀ =
        (1 - J₀) * ((2 * x₀ * J₀ - (x₀ ^ 2 + 1)) *
            evalIntPoint (coeffDerivative (symbolTwistNeg b)) x₀ J₀ +
          (J₀ ^ 2 - 2 * x₀ * J₀ + 2 * x₀ + 1 + 2) *
            evalIntPoint (derivative (symbolTwistNeg b)) x₀ J₀) := by
  obtain ⟨h1, h2, h3⟩ := evalIntPoint_derivatives_target_twfNegEbNode (symbolTwistNeg b) x₀ J₀
  rw [twNegTarget_one_eq b hb, h1, h2, h3, hT, hζ]
  refine ⟨?_, ?_, ?_⟩ <;> ring

end AJConjecture
