import Mathlib
import AJFamily.Quantum.FamDualTransferOp
import AJFamily.Quantum.EbNodeFacts
import AJTwist.Factor.TwFOneEbNode
import AJTwist.Factor.TwFOneTargetJet

/-!
# The Weyl symbol of `P_1` vanishes at its two nodes (TwF, unit F3)

Source: revision 5, Section 5.3 ("the same simple crossing binds `E` to `B_1`") and Section 5.5
("The raw jet is `2 (1 - x₀)^(-5)` by the abelian crossing calculation").

* `evalIntPoint_weylSymbol_famTransferOp_one_ebNode`: at the `E/B_1` node
  `(m₀, ebNodeL 1 m₀)`, `3 (m₀²)² + 7 m₀² + 3 = 0`.
* `evalIntPoint_weylSymbol_famTransferOp_one_abNode`: at the degenerate abelian node `(m₀, 1)`,
  `(m₀²)² - 3 m₀² + 1 = 0` (`K = 3`), where `L = 1` is a triple root of the symbol on the fibre.
  The generic certificate needs only a double point of the target in `(x, J)`, which holds
  (`p = ∂_J p = ∂_x p = 0`; here also `∂_J² p = 0`).

Route: `evalIntPoint_weylSymbol_twTransferOp_eq_zero` with `a = 1`
(`twTransferOp_natCast 1`, `twTarget_natCast 1`, `twWindow_natCast 1`; `twDualX 5 m₀` is
`famDualX 1 m₀` by `rfl`), `evalEval_famTarget_one_dual_node` (`w = -m₀²` resp. `w = m₀²`), the
vanishing of `∂_J p`, `∂_x p` from `famTarget_one_eq` (two of the three factors
`1 - J`, `ζ + 2x`, `T̂_1` vanish; at `K = 3`, `T̂_1(x₀, J) = x₀ (J - 1)²`), and the certificates
`famOne_ebNode_cert`, `famOne_abNode_cert`. The node conditions `m₀² ≠ ± 1`, `m₀² ≠ J₀`,
`m₀² J₀ ≠ 1` follow from the node quadratics. `famNodeL m₀² 1 = 1`.
Checked directly from the definition of the operator (scratch `check_weyl.py`, `a = 1`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The derivative `∂_J p` of `p = famTarget 1 1 = (1 - J)(ζ + 2x) T̂_1`. -/
private theorem evalIntPoint_derivative_famTarget_one_twfOneWeyl (x J : ℂ) :
    evalIntPoint (derivative (famTarget 1 (1 : ℤ))) x J =
      (-5 * x ^ 2) * J ^ 4 + (8 * x ^ 3 + 8 * x) * J ^ 3 +
        (-3 * x ^ 4 - 6 * x ^ 3 - 15 * x ^ 2 - 6 * x - 3) * J ^ 2 +
        (4 * x ^ 4 + 6 * x ^ 3 + 10 * x ^ 2 + 6 * x + 4) * J +
        (-x ^ 4 - 4 * x ^ 3 - 2 * x ^ 2 - 4 * x - 1) := by
  rw [evalIntPoint_eq, famTarget_one_eq 1 le_rfl, symbolTwist, symbolZeta]
  simp [evalIntHomTwistNode, eval₂_pow, derivative_pow, derivative_mul]
  ring

/-- The derivative `∂_x p` of `p = famTarget 1 1 = (1 - J)(ζ + 2x) T̂_1`. -/
private theorem evalIntPoint_coeffDerivative_famTarget_one_twfOneWeyl (x J : ℂ) :
    evalIntPoint (coeffDerivative (famTarget 1 (1 : ℤ))) x J =
      (-2 * x) * J ^ 5 + (6 * x ^ 2 + 2) * J ^ 4 + (-4 * x ^ 3 - 6 * x ^ 2 - 10 * x - 2) * J ^ 3 +
        (8 * x ^ 3 + 9 * x ^ 2 + 10 * x + 3) * J ^ 2 + (-4 * x ^ 3 - 12 * x ^ 2 - 4 * x - 4) * J +
        (3 * x ^ 2 + 6 * x + 1) := by
  have h1 : innerDerivative (1 : ℤ[X][X]) = 0 := by
    rw [← C_1, innerDerivative_C, derivative_one, C_0]
  rw [evalIntPoint_eq, famTarget_one_eq 1 le_rfl, symbolTwist, symbolZeta,
    coeffDerivative_eq_innerDerivative]
  simp only [innerDerivative_add, innerDerivative_sub, innerDerivative_mul, innerDerivative_C,
    innerDerivative_X, h1, pow_succ, pow_zero, one_mul]
  simp [evalIntHomTwistNode, derivative_mul]
  ring

/-- The Weyl certificate for `P_1 = famTransferOp 1` in the form of the generic certificate for
`twTransferOp 1`. -/
private theorem evalIntPoint_weylSymbol_famTransferOp_one_twfOneWeyl {m₀ J₀ w : ℂ}
    (h1 : m₀ ^ 2 ≠ 1) (h2 : m₀ ^ 2 ≠ -1) (hJ : m₀ ^ 2 ≠ J₀) (hJ' : m₀ ^ 2 * J₀ ≠ 1)
    (hpJ : evalIntPoint (derivative (famTarget 1 (1 : ℤ))) (m₀ ^ 2) J₀ = 0)
    (hpx : evalIntPoint (coeffDerivative (famTarget 1 (1 : ℤ))) (m₀ ^ 2) J₀ = 0)
    (hw : 2 * w = famJetZeta 1 (1 : ℂ) (m₀ ^ 2) J₀) (hw2 : w ^ 2 = (m₀ ^ 2) ^ 2)
    (hval : (m₀ ^ 2) ^ 2 + m₀ ^ 2 * (1 - J₀) * w - J₀ * w ^ 2 = 0)
    (hcert : famTargetJet 1 (m₀ ^ 2) J₀ w * ((m₀ ^ 2) ^ 2 - 1) =
      2 * m₀ ^ 2 * ((1 - m₀ ^ 2 * J₀) * (m₀ ^ 2 - J₀)) *
        evalIntPoint (derivative (coeffDerivative (famTarget 1 (1 : ℤ)))) (m₀ ^ 2) J₀) :
    evalIntPoint (weylSymbol (famTransferOp 1)) m₀ (famNodeL (m₀ ^ 2) J₀) = 0 := by
  have key := evalIntPoint_weylSymbol_twTransferOp_eq_zero ((1 : ℕ) : ℤ) (m₀ := m₀) (J₀ := J₀)
    (h₁ := famTargetJet 1 (m₀ ^ 2) J₀ w) h1 h2 hJ hJ'
  rw [twTransferOp_natCast 1 le_rfl, twTarget_natCast 1 le_rfl, twTarget_natCast 1 le_rfl,
    twWindow_natCast] at key
  exact key hpJ hpx (evalEval_famTarget_one_dual_node hw hw2 hval) hcert

/-- The Weyl subprincipal symbol of `P_1` vanishes at the `E/B_1` node. -/
theorem evalIntPoint_weylSymbol_famTransferOp_one_ebNode {m₀ : ℂ}
    (heb : 3 * (m₀ ^ 2) ^ 2 + 7 * m₀ ^ 2 + 3 = 0) :
    evalIntPoint (weylSymbol (famTransferOp 1)) m₀ (ebNodeL 1 m₀) = 0 := by
  obtain ⟨-, h1, h2, hJ, hJ', -⟩ := famOne_ebNode_facts heb
  have hJ0 : ebNodeJ 1 = -1 / 3 := by
    rw [ebNodeJ]
    norm_num
  refine evalIntPoint_weylSymbol_famTransferOp_one_twfOneWeyl (w := -(m₀ ^ 2)) h1 h2 hJ hJ'
    ?_ ?_ ?_ (by ring) ?_ (famOne_ebNode_cert heb)
  · rw [evalIntPoint_derivative_famTarget_one_twfOneWeyl, hJ0]
    linear_combination (-8 * (m₀ ^ 2) ^ 2 / 9 - 20 * (m₀ ^ 2) / 81 - 8 / 9) * heb
  · rw [evalIntPoint_coeffDerivative_famTarget_one_twfOneWeyl, hJ0]
    linear_combination (64 * (m₀ ^ 2) / 81 + 224 / 243) * heb
  · rw [famJetZeta, hJ0]
    linear_combination (-4 / 9 : ℂ) * heb
  · rw [hJ0]
    ring

/-- The Weyl subprincipal symbol of `P_1` vanishes at the degenerate abelian node `(m₀, 1)`,
`K = 3`. -/
theorem evalIntPoint_weylSymbol_famTransferOp_one_abNode {m₀ : ℂ}
    (hab : (m₀ ^ 2) ^ 2 - 3 * m₀ ^ 2 + 1 = 0) :
    evalIntPoint (weylSymbol (famTransferOp 1)) m₀ 1 = 0 := by
  have h1 : m₀ ^ 2 ≠ 1 := by
    intro h
    rw [h] at hab
    norm_num at hab
  have h2 : m₀ ^ 2 ≠ -1 := by
    intro h
    rw [h] at hab
    norm_num at hab
  have hL : famNodeL (m₀ ^ 2) 1 = 1 := by
    rw [famNodeL, mul_one]
    exact div_self (sub_ne_zero.mpr (Ne.symm h1))
  rw [← hL]
  refine evalIntPoint_weylSymbol_famTransferOp_one_twfOneWeyl (w := m₀ ^ 2) h1 h2 h1
    (by rwa [mul_one]) ?_ ?_ ?_ rfl (by ring) (famOne_abNode_cert hab)
  · rw [evalIntPoint_derivative_famTarget_one_twfOneWeyl]
    linear_combination 4 * (m₀ ^ 2) * hab
  · rw [evalIntPoint_coeffDerivative_famTarget_one_twfOneWeyl]
    ring
  · rw [famJetZeta]
    ring

end AJConjecture
