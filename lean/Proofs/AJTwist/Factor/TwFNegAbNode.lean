import Mathlib
import AJTwist.Quantum.TwQTargetAtOne
import AJTwist.Factor.TwFTargetBridge
import AJTwist.Factor.TwFNegTargetJet
import AJTwist.Factor.TwFNegSymbolValues
import AJFamily.Quantum.TwistPolyNodeValues

/-!
# The crossing `(L - 1)/C_b`: the Weyl symbol vanishes (TwF, unit F2)

Source: revision 5, Section 5.4 (`operators.tex`), "The `(L - 1)/C_b` crossing": at `J = 1`,
`K = 2 - 1/b`, one has `ω = ρ = 0`, `Ṅ_(-b) = 2`,
`(D_u G)(D_u H) = -2(b+1)/(3b)`, `s_G = 0`, `s_H = -6b/(b+1)`, `κ = -3b/(b+1)`: both indices
are `-1/2`.

The node is `(m₀, 1)` with `x₀ = m₀²` a root of `b x² - (2b - 1) x + b` (`K = x + 1/x = 2 - 1/b`);
in the coordinates `(x, J)` it is `(x₀, 1)`, on the double locus `ζ = 2x` (`w = x₀`), where
`T̂_(-b) = x₀^(b-1) (x₀ + b (x₀ - 1)²) = 0`.

* `twNegTarget_one_derivatives_abNode`: `p = (1 - J)(ζ + 2x) T̂_(-b)` has a double point there and
  `∂_x∂_J p = -4 x₀ ∂_x T̂_(-b)`.
* `twNeg_abNode_cert`: the certificate
  `h₁ (x₀² - 1) = 2 x₀ (1 - x₀)(x₀ - 1) ∂_x∂_J p` for `h₁ = twNegTargetJet b x₀ 1 x₀`.
  With the closed forms (`symbolTwistNeg_node_values`, `dblRootDeriv_mul_of_crit`) both sides are
  `x₀^(b-2)` times polynomials in `(b, x₀)`, and their difference is
  `-8 x₀² (x₀ - 1)(b x₀ - b - x₀ - 1) · (b x₀² - (2b - 1) x₀ + b)` (computed symbolically in `b`,
  scratch `node_closed_neg.py`); the cases `b = 1, 2` have truncated exponents and are done
  separately.
* `evalIntPoint_weylSymbol_twTransferOp_neg_abNode`: the Weyl subprincipal symbol of `P_(-b)`
  vanishes at `(m₀, 1)`. From `evalIntPoint_weylSymbol_twTransferOp_eq_zero` with `a = -b`,
  `J₀ = 1` (`famNodeL x₀ 1 = 1`), `twTarget_neg_natCast`, `twWindow_neg_natCast`,
  `evalEval_twNegTarget_dual_node` (`w = x₀`).

Checked: Weyl symbol, certificate and the paper's constants for `1 ≤ b ≤ 8` (scratch
`check_weyl.py`, `check_paper5.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The inner derivative of `1` vanishes. -/
private theorem innerDerivative_one_twfNegAbNode : innerDerivative (1 : ℤ[X][X]) = 0 := by
  rw [← C_1, innerDerivative_C, derivative_one, C_0]

/-- The inner derivative of the outer variable vanishes. -/
private theorem innerDerivative_X_twfNegAbNode : innerDerivative (X : ℤ[X][X]) = 0 := by
  rw [innerDerivative, sum_X_index] <;> simp

/-- The derivatives of `ζ + 2x`. -/
private theorem derivative_symbolZeta_add_twfNegAbNode :
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
      innerDerivative_mul, innerDerivative_C, innerDerivative_X_twfNegAbNode,
      sq (X : ℤ[X]), derivative_add, derivative_mul, derivative_X, derivative_one,
      derivative_ofNat]
    simp only [C_mul, C_add, C_1, C_0, C_ofNat]
    ring
  · simp only [sq (X : ℤ[X][X]), derivative_add, derivative_sub, derivative_mul,
      derivative_C, derivative_X, derivative_ofNat]
    ring

/-- The first derivatives and the mixed derivative of `(1 - J)(ζ + 2x) T` at a point. -/
private theorem evalIntPoint_derivatives_target_twfNegAbNode (T : ℤ[X][X]) (x₀ J₀ : ℂ) :
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
  obtain ⟨hdB, hiB, hdiB⟩ := derivative_symbolZeta_add_twfNegAbNode
  have hd : derivative ((1 - X) * (symbolZeta + C (2 * X)) * T) =
      -((symbolZeta + C (2 * X)) * T) + (1 - X) * ((C (2 * X) * X - C (X ^ 2 + 1)) * T +
        (symbolZeta + C (2 * X)) * derivative T) := by
    simp only [derivative_mul, derivative_sub, derivative_one, derivative_X, hdB]
    ring
  have hi : innerDerivative ((1 - X) * (symbolZeta + C (2 * X)) * T) =
      (1 - X) * ((X ^ 2 - C (2 * X) * X + C (2 * X + 1) + 2) * T +
        (symbolZeta + C (2 * X)) * innerDerivative T) := by
    simp only [innerDerivative_mul, innerDerivative_sub, innerDerivative_one_twfNegAbNode,
      innerDerivative_X_twfNegAbNode, hiB]
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

/-- At the abelian node the target `p = twNegTarget b 1` has a double point, and
`∂_x∂_J p = -4 x₀ ∂_x T̂_(-b)`. -/
theorem twNegTarget_one_derivatives_abNode (b : ℕ) (hb : 1 ≤ b) {x₀ : ℂ}
    (hT : evalIntPoint (symbolTwistNeg b) x₀ 1 = 0) :
    evalIntPoint (derivative (twNegTarget b (1 : ℤ))) x₀ 1 = 0 ∧
      evalIntPoint (coeffDerivative (twNegTarget b (1 : ℤ))) x₀ 1 = 0 ∧
      evalIntPoint (derivative (coeffDerivative (twNegTarget b (1 : ℤ)))) x₀ 1 =
        -4 * x₀ * evalIntPoint (coeffDerivative (symbolTwistNeg b)) x₀ 1 := by
  obtain ⟨h1, h2, h3⟩ := evalIntPoint_derivatives_target_twfNegAbNode (symbolTwistNeg b) x₀ 1
  rw [twNegTarget_one_eq b hb, h1, h2, h3, hT, evalIntPoint_symbolZeta]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- The certificate identity at the abelian node of `P_(-b)`. -/
theorem twNeg_abNode_cert (b : ℕ) (hb : 1 ≤ b) {m₀ : ℂ}
    (hab : (b : ℂ) * (m₀ ^ 2) ^ 2 - (2 * b - 1) * m₀ ^ 2 + b = 0) :
    twNegTargetJet b (m₀ ^ 2) 1 (m₀ ^ 2) * ((m₀ ^ 2) ^ 2 - 1) =
      2 * m₀ ^ 2 * ((1 - m₀ ^ 2 * 1) * (m₀ ^ 2 - 1)) *
        evalIntPoint (derivative (coeffDerivative (twNegTarget b (1 : ℤ)))) (m₀ ^ 2) 1 := by
  generalize m₀ ^ 2 = x at hab ⊢
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb0 (by linear_combination hab)
  have hζ : evalIntPoint symbolZeta x 1 = 2 * x := by
    rw [evalIntPoint_symbolZeta]
    ring
  obtain ⟨hT, -, hTx⟩ := symbolTwistNeg_node_values hζ rfl hx0 b
  have hcrit : x + b * (x ^ 2 + 1 - x * 1 - x) = 0 := by linear_combination hab
  have hT0 : evalIntPoint (symbolTwistNeg b) x 1 = 0 := by
    rw [hT]
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    linear_combination x ^ n * hcrit
  have hD := dblRootDeriv_mul_of_crit (z₁ := 2 * x - 1) (α := 1 ^ 2 - 2 * x * 1 + 2 * x + 1)
    (β := 2 * x) hb hx0 hcrit
  rw [(twNegTarget_one_derivatives_abNode b hb hT0).2.2, hTx]
  refine mul_left_cancel₀ (mul_ne_zero (show (6 : ℂ) ≠ 0 by norm_num) hx0) ?_
  generalize dblRootDeriv x (x ^ 2 + 1 - x * 1 - x) (2 * x - 1) (1 ^ 2 - 2 * x * 1 + 2 * x + 1)
    (2 * x) b = D at hD ⊢
  obtain rfl | rfl | ⟨n, rfl⟩ : b = 1 ∨ b = 2 ∨ ∃ n, b = n + 3 := by
    rcases b with _ | _ | _ | n
    · omega
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨n, rfl⟩)
  · simp only [Nat.cast_one, one_mul, Nat.sub_self, pow_zero, sub_self, zero_mul, mul_zero,
      sub_zero, add_zero] at hD hab
    simp [twNegTargetJet]
    linear_combination (2 * x * ((1 - x) * (x - 1)) * (4 * x)) * hD +
      (96 * x ^ 2 * (x - 1)) * hab
  · simp [twNegTargetJet] at hD hab ⊢
    linear_combination (2 * x * ((1 - x) * (x - 1)) * (4 * x)) * hD +
      (96 * x ^ 3 * (x - 1)) * hab
  · simp [twNegTargetJet] at hD hab ⊢
    linear_combination (2 * x * ((1 - x) * (x - 1)) * (4 * x)) * hD +
      (96 * x ^ (n + 4) * (x - 1)) * hab

/-- The Weyl subprincipal symbol of `P_(-b)` vanishes at the abelian node `(m₀, 1)`, where
`b (m₀²)² - (2b - 1) m₀² + b = 0`. -/
theorem evalIntPoint_weylSymbol_twTransferOp_neg_abNode (b : ℕ) (hb : 1 ≤ b) {m₀ : ℂ}
    (hab : (b : ℂ) * (m₀ ^ 2) ^ 2 - (2 * b - 1) * m₀ ^ 2 + b = 0) :
    evalIntPoint (weylSymbol (twTransferOp (-(b : ℤ)))) m₀ 1 = 0 := by
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hx0 : m₀ ^ 2 ≠ 0 := by
    intro h
    rw [h] at hab
    exact hb0 (by linear_combination hab)
  have h1 : m₀ ^ 2 ≠ 1 := by
    intro h
    rw [h] at hab
    exact one_ne_zero (α := ℂ) (by linear_combination hab)
  have h2 : m₀ ^ 2 ≠ -1 := by
    intro h
    rw [h] at hab
    have h4 : (4 * b : ℂ) = 1 := by linear_combination hab
    have h4' : 4 * b = 1 := by exact_mod_cast h4
    omega
  have hζ : evalIntPoint symbolZeta (m₀ ^ 2) 1 = 2 * m₀ ^ 2 := by
    rw [evalIntPoint_symbolZeta]
    ring
  have hT0 : evalIntPoint (symbolTwistNeg b) (m₀ ^ 2) 1 = 0 := by
    rw [(symbolTwistNeg_node_values hζ rfl hx0 b).1]
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    push_cast at hab ⊢
    linear_combination (m₀ ^ 2) ^ n * hab
  obtain ⟨hpJ, hpx, -⟩ := twNegTarget_one_derivatives_abNode b hb hT0
  have hL : famNodeL (m₀ ^ 2) 1 = 1 := by
    rw [famNodeL, mul_one]
    exact div_self (sub_ne_zero.mpr (Ne.symm h1))
  have key := evalIntPoint_weylSymbol_twTransferOp_eq_zero (-(b : ℤ)) (m₀ := m₀) (J₀ := 1)
    (h₁ := twNegTargetJet b (m₀ ^ 2) 1 (m₀ ^ 2)) h1 h2 h1 (by rwa [mul_one])
  rw [twTarget_neg_natCast b hb, twTarget_neg_natCast b hb, twWindow_neg_natCast b hb, hL] at key
  refine key hpJ hpx (evalEval_twNegTarget_dual_node b hb ?_ rfl ?_) (twNeg_abNode_cert b hb hab)
  · simp only [twJetZeta]
    ring
  · ring

end AJConjecture
